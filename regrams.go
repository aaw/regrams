// regrams parses regular expressions into trigram queries in conjunctive
// normal form. To build a search engine that accepts regular expression
// queries, index all text documents by trigrams, then use the MakeQuery method
// provided in this package to transform any regular expression query into a
// query over the indexed trigrams.
//
// For example, MakeQuery("abc+(d|e)") returns [["abc"], ["bcc","bcd","bce"]],
// which represents the trigram query "(abc) AND (bcc OR bcd OR bce)"
package regrams

import (
	"bytes"
	"errors"
	"fmt"
	"regexp/syntax"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

// If we see a single character class with at least this many characters, we'll
// give up on trying to expand ngrams for character class.
const maxCharClassSize = 10

// We'll never analyze a set of ngrams larger than this.
const maxNgramSetSize = 100

// We won't try to create a query from any NFAs with at least this many nodes.
const maxNFANodes = 10000

// A very large weight. Used during computation of a minimum-weight cut on the
// NFA for any node that we don't want to be part of a cut.
const infinity = maxNgramSetSize * maxNFANodes

// Analyzing a single query involves multiple traversals over the NFA. Each
// traversal needs to keep track of which nodes have and haven't been seen at
// any given point to avoid loops. Instead of allocating a map[*nFANode]bool
// to keep track of this for each traversal, each nFANode has a WhenSeen field
// and each time we want to traverse the NFA, we'll increment a global Epoch
// counter. When we visit an nFANode, we'll set WhenSeen to the current epoch,
// so testing whether a node has been visited for a traversal is just a check to
// see if WhenSeen is equal to the current epoch.
var epoch = 0

func newEpoch() int {
	epoch++
	return epoch
}

type regexpOp int

const (
	kleeneStar regexpOp = iota
	concatenate
	alternate
	literal
	emptyString
	noMatch
)

// A textbook regular expression. If Op is literal, this represents the
// character class [LitBegin-LitEnd]. If Op is kleeneStar, concatenate, or
// alternate, Sub is populated with subexpressions.
type regexp struct {
	Op       regexpOp
	Sub      []*regexp
	LitBegin rune
	LitEnd   rune
}

// Parse a regexp, given as a string, into a regrams.Regexp.
func parseRegexpString(expr string) (*regexp, error) {
	re, err := syntax.Parse(expr, syntax.Perl)
	if err != nil {
		return nil, err
	}
	sre := re.Simplify()
	return normalizeRegexp(sre), nil
}

// Convert a simplified golang syntax.Regexp into a more general regular expression.
// The normalized regular expression may match more than the syntax.Regexp would.
func normalizeRegexp(re *syntax.Regexp) *regexp {
	switch re.Op {
	case syntax.OpNoMatch:
		return &regexp{Op: noMatch}
	case syntax.OpEmptyMatch,
		syntax.OpBeginLine,
		syntax.OpEndLine,
		syntax.OpBeginText,
		syntax.OpEndText,
		syntax.OpWordBoundary,
		syntax.OpNoWordBoundary:
		return &regexp{Op: emptyString}
	case syntax.OpLiteral:
		lits := make([]*regexp, len(re.Rune))
		for i, r := range re.Rune {
			if re.Flags&syntax.FoldCase != 0 {
				folds := []*regexp{&regexp{Op: literal, LitBegin: r, LitEnd: r}}
				for f := unicode.SimpleFold(r); f != r; f = unicode.SimpleFold(f) {
					folds = append(folds, &regexp{Op: literal, LitBegin: f, LitEnd: f})
				}
				lits[i] = &regexp{Op: alternate, Sub: folds}
			} else {
				lits[i] = &regexp{Op: literal, LitBegin: r, LitEnd: r}
			}
		}
		return &regexp{Op: concatenate, Sub: lits}
	case syntax.OpAnyCharNotNL:
		beforeNL := &regexp{Op: literal, LitBegin: 0, LitEnd: '\n'}
		afterNL := &regexp{Op: literal, LitBegin: '\n', LitEnd: utf8.MaxRune}
		return &regexp{Op: alternate, Sub: []*regexp{beforeNL, afterNL}}
	case syntax.OpAnyChar:
		return &regexp{Op: literal, LitBegin: 0, LitEnd: utf8.MaxRune}
	case syntax.OpCapture:
		return normalizeRegexp(re.Sub[0])
	case syntax.OpConcat:
		args := make([]*regexp, len(re.Sub))
		for i, s := range re.Sub {
			args[i] = normalizeRegexp(s)
		}
		return &regexp{Op: concatenate, Sub: args}
	case syntax.OpAlternate:
		args := make([]*regexp, len(re.Sub))
		for i, s := range re.Sub {
			args[i] = normalizeRegexp(s)
		}
		return &regexp{Op: alternate, Sub: args}
	case syntax.OpQuest:
		return &regexp{Op: alternate, Sub: []*regexp{normalizeRegexp(re.Sub[0]), &regexp{Op: emptyString}}}
	case syntax.OpStar:
		return &regexp{Op: kleeneStar, Sub: []*regexp{normalizeRegexp(re.Sub[0])}}
	case syntax.OpRepeat:
		args := make([]*regexp, re.Max)
		sub := normalizeRegexp(re.Sub[0])
		for i := 0; i < re.Min; i++ {
			args[i] = sub
		}
		for i := re.Min; i < re.Max; i++ {
			args[i] = &regexp{Op: alternate, Sub: []*regexp{sub, &regexp{Op: emptyString}}}
		}
		return &regexp{Op: concatenate, Sub: args}
	case syntax.OpPlus:
		parsed := normalizeRegexp(re.Sub[0])
		return &regexp{Op: concatenate, Sub: []*regexp{parsed, &regexp{Op: kleeneStar, Sub: []*regexp{parsed}}}}
	case syntax.OpCharClass:
		args := make([]*regexp, len(re.Rune)/2)
		for i := 0; i < len(re.Rune)-1; i += 2 {
			args[i/2] = &regexp{Op: literal, LitBegin: re.Rune[i], LitEnd: re.Rune[i+1]}
		}
		return &regexp{Op: alternate, Sub: args}
	}
	panic(fmt.Sprintf("Unknown regexp operation: %v (%v)", re.Op, re))
}

type nFA struct {
	Start  *nFANode
	Accept *nFANode
}

// Visit the node, return true if the node has already been visited this
// epoch and false otherwise.
func seen(node *nFANode, epoch int) bool {
	if node.WhenSeen == epoch {
		return true
	}
	node.WhenSeen = epoch
	return false
}

// An nFANode has zero or more epsilon-transitions but only at most one
// character class transition ([LitBegin-LitEnd] -> LitOut). If the node has no
// character class transition, LitOut is nil. EpsilonClosure is populated by
// calling populateEpsilonClosure and Trigrams is populated by calling
// populateTrigrams. WhenSeen is the last epoch this node was visited and
// Capacity is used by findCut (and populated in that method by calling
// populateCapacities).
type nFANode struct {
	LitOut         *nFANode
	LitBegin       rune
	LitEnd         rune
	Epsilons       []*nFANode
	EpsilonClosure []*nFANode
	Trigrams       []string
	WhenSeen       int
	Capacity       int
}

// Thompson's construction of an NFA from a regular expression.
func buildNFA(re *regexp) *nFA {
	switch re.Op {
	case kleeneStar:
		sub := buildNFA(re.Sub[0])
		accept := &nFANode{}
		start := &nFANode{Epsilons: []*nFANode{sub.Start, accept}}
		sub.Accept.Epsilons = append(sub.Accept.Epsilons, sub.Start, accept)
		return &nFA{Start: start, Accept: accept}
	case concatenate:
		var next, curr *nFA
		var accept *nFANode
		for i := len(re.Sub) - 1; i >= 0; i-- {
			curr = buildNFA(re.Sub[i])
			if next != nil {
				curr.Accept.Epsilons = append(curr.Accept.Epsilons, next.Start)
			} else {
				accept = curr.Accept
			}
			next = curr
		}
		return &nFA{Start: curr.Start, Accept: accept}
	case alternate:
		subStarts := make([]*nFANode, len(re.Sub))
		accept := &nFANode{}
		for i, sub := range re.Sub {
			nfa := buildNFA(sub)
			nfa.Accept.Epsilons = append(nfa.Accept.Epsilons, accept)
			subStarts[i] = nfa.Start
		}
		start := &nFANode{Epsilons: subStarts}
		return &nFA{Start: start, Accept: accept}
	case literal:
		accept := &nFANode{}
		start := &nFANode{LitBegin: re.LitBegin, LitEnd: re.LitEnd, LitOut: accept}
		return &nFA{Start: start, Accept: accept}
	case emptyString:
		accept := &nFANode{}
		start := &nFANode{Epsilons: []*nFANode{accept}}
		return &nFA{Start: start, Accept: accept}
	case noMatch:
		return &nFA{Start: &nFANode{}}
	}
	panic(fmt.Sprintf("Unknown regexp Op: %s (%v)", re.Op, re))
}

// A trigram query. These are always in conjunctive normal form: an AND of a
// bunch of ORs. The Query [["abc", "xbc"], ["xxx"]], for example, represents
// the trigram query (abc OR xbc) AND (xxx).
type Query [][]string

func (q Query) String() string {
	var buffer bytes.Buffer
	for i, dis := range q {
		if i > 0 {
			buffer.WriteString(" ")
		}
		buffer.WriteString("(")
		buffer.WriteString(strings.Join(dis, "|"))
		buffer.WriteString(")")
	}
	return buffer.String()
}

// Make a regrams.Query from a string representation of a regexp.
func MakeQuery(r string) (Query, error) {
	re, err := parseRegexpString(r)
	if err != nil {
		return Query{}, err
	}
	nfa := buildNFA(re)
	if countReachableNodes(nfa) > maxNFANodes {
		return Query{}, errors.New("Too many nodes in NFA, refusing to build query.")
	}
	populateEpsilonClosure(nfa)
	populateTrigrams(nfa)
	return makeQueryHelper(nfa), nil
}

// Count the number of nodes in an NFA. We only do this to make sure that we
// don't start computing a min cut on a graph that's too big.
func countReachableNodes(nfa *nFA) int {
	return countReachableNodesHelper(nfa.Start, newEpoch())
}

func countReachableNodesHelper(node *nFANode, epoch int) int {
	if seen(node, epoch) {
		return 0
	}
	count := 1
	if node.LitOut != nil {
		count += countReachableNodesHelper(node.LitOut, epoch)
	}
	for _, e := range node.Epsilons {
		count += countReachableNodesHelper(e, epoch)
	}
	return count
}

// Compute the epsilon closure of each node in the NFA, populate the
// EpsilonClosure field of each node with that value. The epsilon closure of
// a node is the set of all nodes that can be reached via zero or more epsilon
// transitions.
func populateEpsilonClosure(nfa *nFA) {
	populateEpsilonClosureHelper(nfa.Start, newEpoch())
}

func populateEpsilonClosureHelper(node *nFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	closure := []*nFANode{node}
	for _, e := range node.Epsilons {
		populateEpsilonClosureHelper(e, epoch)
		closure = append(closure, e.EpsilonClosure...)
	}
	node.EpsilonClosure = uniqNodes(closure)
	if node.LitOut != nil {
		populateEpsilonClosureHelper(node.LitOut, epoch)
	}
}

type byNFANodePtr []*nFANode
func (a byNFANodePtr) Len() int      { return len(a) }
func (a byNFANodePtr) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a byNFANodePtr) Less(i, j int) bool {
	return uintptr(unsafe.Pointer(a[i])) < uintptr(unsafe.Pointer(a[j]))
}

func uniqNodes(nodes []*nFANode) []*nFANode {
	sort.Sort(byNFANodePtr(nodes))
	i := 0
	for _, s := range nodes {
		if i == 0 || nodes[i-1] != s {
			nodes[i] = s
			i++
		}
	}
	return nodes[:i]
}

// Build the trigram set for all nodes in the NFA. Nodes with trigram sets that
// are deemed too large during expansion or that can't be computed because the
// accept state is reachable in 2 or fewer steps are given an empty trigram
// set. There's a faster way to compute the trigram sets than what we do here:
// we're essentially running a separate sub-traversal to compute trigrams
// at each node (the call to "trigrams" in populateTrigramsHelper), when we
// could be computing the trigram set with three passes over the graph,
// accumulating intermediate suffixes to build up the trigrams at each step.
func populateTrigrams(nfa *nFA) {
	populateTrigramsHelper(nfa.Start, nfa.Accept, newEpoch())
}

func populateTrigramsHelper(node *nFANode, accept *nFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	if node.LitOut != nil {
		node.Trigrams = trigrams(node, accept)
		populateTrigramsHelper(node.LitOut, accept, epoch)
	}
	for _, e := range node.Epsilons {
		populateTrigramsHelper(e, accept, epoch)
	}
}

// Compute the trigram set for an individual node.
func trigrams(root *nFANode, accept *nFANode) []string {
	return uniq(ngramSearch(root, accept, 3))
}

func ngramSearch(node *nFANode, accept *nFANode, limit int) []string {
	if limit == 0 {
		return []string{""}
	}
	results := []string{}
	for _, cnode := range node.EpsilonClosure {
		if cnode == accept {
			// Bail out, we can reach the accept state before we've consumed
			// enough characters for a full n-gram.
			return []string{}
		}
		if cnode.LitOut == nil {
			continue
		}
		begin := int(cnode.LitBegin)
		end := int(cnode.LitEnd)
		if end-begin > maxCharClassSize {
			// Bail out, the ngram set might be too large.
			return []string{}
		}
		subresults := ngramSearch(cnode.LitOut, accept, limit-1)
		if len(subresults) == 0 {
			// A subresult has bailed out, so short-circuit here as well.
			return []string{}
		}
		if len(subresults)*(end-begin+1) > maxNgramSetSize {
			// Bail out, the ngram set is going to be too large.
			return []string{}
		}
		suffixes := make([]string, len(subresults))
		for i := begin; i <= end; i++ {
			copy(suffixes, subresults)
			crossProduct(i, suffixes)
			results = append(results, suffixes...)
		}
	}
	return results
}

// Prefix each string in y with the string at codepoint x.
func crossProduct(x int, y []string) {
	s := string(rune(x))
	for i, yy := range y {
		y[i] = s + yy
	}
}

// Once the trigram set is populated on each node, all that's left is to
// generate the query. We find a minimum weight vertex cut in the NFA based on
// weights computed from the size of the trigram sets of each node, then
// recursively continue on both sides of the cut to identify disjunctions that
// we can AND together to make a complete query.
func makeQueryHelper(nfa *nFA) Query {
	s, t, cut := findCut(nfa)
	if len(cut) > 0 {
		sq := makeQueryHelper(s)
		tq := makeQueryHelper(t)
		return Query(append(append(sq, uniq(cut)), tq...))
	} else {
		return Query{}
	}
}

func uniq(x []string) []string {
	sort.Strings(x)
	i := 0
	for _, s := range x {
		if i == 0 || x[i-1] != s {
			x[i] = s
			i++
		}
	}
	return x[:i]
}

// Find a minimum-weight vertex cut in the NFA by repeatedly pushing flow
// through a path of positive capacity until no such path exists. This is
// essentially the (depth-first) Ford-Fulkerson algorithm. After no more flow
// can be pushed through, identify the cut and do a little surgery on the NFA
// so that it's actually two NFAs: one on each side of the cut. We'll pass those
// two NFAs back along with the cut and continue extracting queries from each.
func findCut(nfa *nFA) (*nFA, *nFA, []string) {
	populateCapacities(nfa)
	for path := []*nFANode{}; path != nil; path = findAugmentingPath(nfa) {
		minCap := infinity
		for _, node := range path {
			if node.Capacity < minCap {
				minCap = node.Capacity
			}
		}
		for _, node := range path {
			node.Capacity -= minCap
		}
	}
	cut, cutEpoch := isolateCut(nfa)
	accept := &nFANode{}
	start := &nFANode{}
	orClause := []string{}
	for _, node := range cut {
		frontier := false
		for i, e := range node.Epsilons {
			if e.WhenSeen != cutEpoch {
				frontier = true
				start.Epsilons = append(start.Epsilons, e)
				node.Epsilons[i] = accept
			}
		}
		if node.LitOut != nil && node.LitOut.WhenSeen != cutEpoch {
			frontier = true
			start.Epsilons = append(start.Epsilons, node.LitOut)
			node.LitOut = accept
		}
		if frontier && node.LitOut != nil {
			orClause = append(orClause, node.Trigrams...)
			// This is a hack, we're clearing the trigram set on a
			// node when it's used so that they aren't continually
			// reused when the graph is decomposed and cut again.
			node.Trigrams = []string{}
		}
	}
	return &nFA{Start: nfa.Start, Accept: accept}, &nFA{Start: start, Accept: nfa.Accept}, orClause
}

// Once capacities have been decremented by pushing flow through a graph, we
// can identify the cut by figuring out which nodes are reachable without
// crossing any zero-capacity nodes.
func isolateCut(nfa *nFA) ([]*nFANode, int) {
	epoch := newEpoch()
	return isolateCutHelper(nfa.Start, epoch), epoch
}

func isolateCutHelper(node *nFANode, epoch int) []*nFANode {
	if seen(node, epoch) {
		return nil
	}
	result := []*nFANode{node}
	if node.Capacity == 0 {
		return result
	}
	if node.LitOut != nil {
		result = append(result, isolateCutHelper(node.LitOut, epoch)...)
	}
	for _, e := range node.Epsilons {
		result = append(result, isolateCutHelper(e, epoch)...)
	}
	return result
}

// Find a path from nfa.Start to nfa.Accept through vertices of positive
// capacity. The path is returned in reverse order from accept to start.
func findAugmentingPath(nfa *nFA) []*nFANode {
	return findAugmentingPathHelper(nfa.Start, nfa.Accept, newEpoch())
}

func findAugmentingPathHelper(node *nFANode, accept *nFANode, epoch int) []*nFANode {
	if seen(node, epoch) || node.Capacity == 0 {
		return nil
	}
	if node == accept {
		return []*nFANode{node}
	}
	if node.LitOut != nil {
		path := findAugmentingPathHelper(node.LitOut, accept, epoch)
		if path != nil {
			return append(path, node)
		}
	}
	for _, v := range node.Epsilons {
		path := findAugmentingPathHelper(v, accept, epoch)
		if path != nil {
			return append(path, node)
		}
	}
	return nil
}

// Calculate capacities for all nodes in the NFA.
func populateCapacities(nfa *nFA) {
	populateCapacitiesHelper(nfa.Start, newEpoch())
}

// * Any node with LitOut = nil has capacity infinity.
// * Any node with LitOut != nil && empty trigram set has capacity infinity.
// * Any node with LitOut != nil && non-empty trigram set has capacity == len(trigram set).
func populateCapacitiesHelper(node *nFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	if node.LitOut != nil {
		nt := len(node.Trigrams)
		if nt > 0 {
			node.Capacity = nt
		} else {
			node.Capacity = infinity
		}
		populateCapacitiesHelper(node.LitOut, epoch)
	} else {
		node.Capacity = infinity
	}
	for _, e := range node.Epsilons {
		populateCapacitiesHelper(e, epoch)
	}
}
