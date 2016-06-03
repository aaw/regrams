package regrams

import (
	"bytes"
	"fmt"
	"regexp/syntax"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"
	"unsafe"
)

// If we see a single character class with at least this many characters, we'll
// give up on trying to expand ngrams for that path.
const MaxCharClassSize = 10

// While expanding a set of ngrams, if the set ever becomes this large, we'll give up
// on trying to expand ngrams for that path.
const MaxNgramSetSize = 100

// We won't try to create a query from any NFAs with at least this many nodes.
const MaxNFANodes = 1000

// A very large capacity. Used on any node that we don't want to be part of a cut, since
// we'll be able to push as much flow as we want through that node.
const Infinity = MaxNgramSetSize * MaxNFANodes

type RegexpOp int

const (
	KleeneStar RegexpOp = iota
	Concatenate
	Alternate
	Literal
	EmptyString
	NoMatch
)

type Regexp struct {
	Op       RegexpOp
	Sub      []*Regexp
	LitBegin rune
	LitEnd   rune
}

func Parse(expr string) *Regexp {
	re, err := syntax.Parse(expr, syntax.Perl)
	if err != nil {
		panic(err)
	}
	sre := re.Simplify()
	return NormalizeRegexp(sre)
}

type NFA struct {
	Start  *NFANode
	Accept *NFANode
}

var Epoch = 0

func getEpoch() int {
	Epoch++
	return Epoch
}

// Visits the node, returns true if the node has already been visited this
// epoch and false otherwise.
func seen(node *NFANode, epoch int) bool {
	if node.WhenSeen == epoch {
		return true
	}
	node.WhenSeen = epoch
	return false
}

// An NFANode has zero or more epsilon-transitions but only at most one
// character class transition ([LitBegin-LitEnd] -> LitOut). If the node
// has no character class transition, LitOut is nil.
type NFANode struct {
	LitOut         *NFANode
	LitBegin       rune
	LitEnd         rune
	Epsilons       []*NFANode
	EpsilonClosure []*NFANode
	Trigrams       []string
	WhenSeen       int
	Capacity       int
}

func CalculateEpsilonClosure(nfa *NFA) {
	calculateEpsilonClosureHelper(nfa.Start, getEpoch())
}

func calculateEpsilonClosureHelper(node *NFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	closure := []*NFANode{node}
	for _, e := range node.Epsilons {
		calculateEpsilonClosureHelper(e, epoch)
		closure = append(closure, e.EpsilonClosure...)
	}
	node.EpsilonClosure = uniqNodes(closure)
	if node.LitOut != nil {
		calculateEpsilonClosureHelper(node.LitOut, epoch)
	}
}

type ByNFANodePtr []*NFANode

func (a ByNFANodePtr) Len() int      { return len(a) }
func (a ByNFANodePtr) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a ByNFANodePtr) Less(i, j int) bool {
	return uintptr(unsafe.Pointer(a[i])) < uintptr(unsafe.Pointer(a[j]))
}
func uniqNodes(nodes []*NFANode) []*NFANode {
	sort.Sort(ByNFANodePtr(nodes))
	i := 0
	for _, s := range nodes {
		if i == 0 || nodes[i-1] != s {
			nodes[i] = s
			i++
		}
	}
	return nodes[:i]
}

func Trigrams(root *NFANode, accept *NFANode) []string {
	return uniq(ngramSearch(root, accept, 3))
}

func ngramSearch(node *NFANode, accept *NFANode, limit int) []string {
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
		if end-begin > MaxCharClassSize {
			// Bail out, the ngram set might be too large.
			return []string{}
		}
		subresults := ngramSearch(cnode.LitOut, accept, limit-1)
		if len(subresults) == 0 {
			// A subresult has bailed out, so short-circuit here as well.
			return []string{}
		}
		if len(subresults)*(end-begin+1) > MaxNgramSetSize {
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

// Thompson's construction of an NFA from a regular expression.
func BuildNFA(re *Regexp) *NFA {
	switch re.Op {
	case KleeneStar:
		sub := BuildNFA(re.Sub[0])
		accept := &NFANode{}
		start := &NFANode{Epsilons: []*NFANode{sub.Start, accept}}
		sub.Accept.Epsilons = append(sub.Accept.Epsilons, sub.Start, accept)
		return &NFA{Start: start, Accept: accept}
	case Concatenate:
		var next, curr *NFA
		var accept *NFANode
		for i := len(re.Sub) - 1; i >= 0; i-- {
			curr = BuildNFA(re.Sub[i])
			if next != nil {
				curr.Accept.Epsilons = append(curr.Accept.Epsilons, next.Start)
			} else {
				accept = curr.Accept
			}
			next = curr
		}
		return &NFA{Start: curr.Start, Accept: accept}
	case Alternate:
		subStarts := make([]*NFANode, len(re.Sub))
		accept := &NFANode{}
		for i, sub := range re.Sub {
			nfa := BuildNFA(sub)
			nfa.Accept.Epsilons = append(nfa.Accept.Epsilons, accept)
			subStarts[i] = nfa.Start
		}
		start := &NFANode{Epsilons: subStarts}
		return &NFA{Start: start, Accept: accept}
	case Literal:
		accept := &NFANode{}
		start := &NFANode{LitBegin: re.LitBegin, LitEnd: re.LitEnd, LitOut: accept}
		return &NFA{Start: start, Accept: accept}
	case EmptyString:
		accept := &NFANode{}
		start := &NFANode{Epsilons: []*NFANode{accept}}
		return &NFA{Start: start, Accept: accept}
	case NoMatch:
		return &NFA{Start: &NFANode{}}
	}
	return nil
}

// Convert a simplified golang syntax.Regexp into a more general regular expression.
// The normalized regular expression may match more than the syntax.Regexp would.
func NormalizeRegexp(re *syntax.Regexp) *Regexp {
	switch re.Op {
	case syntax.OpNoMatch:
		return &Regexp{Op: NoMatch}
	case syntax.OpEmptyMatch,
		syntax.OpBeginLine,
		syntax.OpEndLine,
		syntax.OpBeginText,
		syntax.OpEndText,
		syntax.OpWordBoundary,
		syntax.OpNoWordBoundary:
		return &Regexp{Op: EmptyString}
	case syntax.OpLiteral:
		lits := make([]*Regexp, len(re.Rune))
		for i, r := range re.Rune {
			if re.Flags&syntax.FoldCase != 0 {
				folds := []*Regexp{&Regexp{Op: Literal, LitBegin: r, LitEnd: r}}
				for f := unicode.SimpleFold(r); f != r; f = unicode.SimpleFold(f) {
					folds = append(folds, &Regexp{Op: Literal, LitBegin: f, LitEnd: f})
				}
				lits[i] = &Regexp{Op: Alternate, Sub: folds}
			} else {
				lits[i] = &Regexp{Op: Literal, LitBegin: r, LitEnd: r}
			}
		}
		return &Regexp{Op: Concatenate, Sub: lits}
	case syntax.OpAnyCharNotNL:
		beforeNL := &Regexp{Op: Literal, LitBegin: 0, LitEnd: '\n'}
		afterNL := &Regexp{Op: Literal, LitBegin: '\n', LitEnd: utf8.MaxRune}
		return &Regexp{Op: Alternate, Sub: []*Regexp{beforeNL, afterNL}}
	case syntax.OpAnyChar:
		return &Regexp{Op: Literal, LitBegin: 0, LitEnd: utf8.MaxRune}
	case syntax.OpCapture:
		return NormalizeRegexp(re.Sub[0])
	case syntax.OpConcat:
		args := make([]*Regexp, len(re.Sub))
		for i, s := range re.Sub {
			args[i] = NormalizeRegexp(s)
		}
		return &Regexp{Op: Concatenate, Sub: args}
	case syntax.OpAlternate:
		args := make([]*Regexp, len(re.Sub))
		for i, s := range re.Sub {
			args[i] = NormalizeRegexp(s)
		}
		return &Regexp{Op: Alternate, Sub: args}
	case syntax.OpQuest:
		return &Regexp{Op: Alternate, Sub: []*Regexp{NormalizeRegexp(re.Sub[0]), &Regexp{Op: EmptyString}}}
	case syntax.OpStar:
		return &Regexp{Op: KleeneStar, Sub: []*Regexp{NormalizeRegexp(re.Sub[0])}}
	case syntax.OpRepeat:
		args := make([]*Regexp, re.Max)
		sub := NormalizeRegexp(re.Sub[0])
		for i := 0; i < re.Min; i++ {
			args[i] = sub
		}
		for i := re.Min; i < re.Max; i++ {
			args[i] = &Regexp{Op: Alternate, Sub: []*Regexp{sub, &Regexp{Op: EmptyString}}}
		}
		return &Regexp{Op: Concatenate, Sub: args}
	case syntax.OpPlus:
		parsed := NormalizeRegexp(re.Sub[0])
		return &Regexp{Op: Concatenate, Sub: []*Regexp{parsed, &Regexp{Op: KleeneStar, Sub: []*Regexp{parsed}}}}
	case syntax.OpCharClass:
		args := make([]*Regexp, len(re.Rune)/2)
		for i := 0; i < len(re.Rune)-1; i += 2 {
			args[i/2] = &Regexp{Op: Literal, LitBegin: re.Rune[i], LitEnd: re.Rune[i+1]}
		}
		return &Regexp{Op: Alternate, Sub: args}
	}
	panic(fmt.Sprintf("Unknown regexp operation: %v (%v)", re.Op, re))
}

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

func MakeQuery(nfa *NFA) Query {
	if countReachableNodes(nfa) > MaxNFANodes {
		return Query{}
	}
	CalculateEpsilonClosure(nfa)
	PopulateTrigrams(nfa)
	return makeQueryHelper(nfa)
}

func countReachableNodes(nfa *NFA) int {
	return countReachableNodesHelper(nfa.Start, getEpoch())
}

func countReachableNodesHelper(node *NFANode, epoch int) int {
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

func makeQueryHelper(nfa *NFA) Query {
	s, t, cut := FindCut(nfa)
	if len(cut) > 0 {
		sq := makeQueryHelper(s)
		tq := makeQueryHelper(t)
		return Query(append(append(sq, uniq(cut)), tq...))
	} else {
		return Query{}
	}
}

func FindCut(nfa *NFA) (*NFA, *NFA, []string) {
	PopulateCapacities(nfa)
	for path := []*NFANode{}; path != nil; path = FindAugmentingPath(nfa) {
		minCap := Infinity
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
	accept := &NFANode{}
	start := &NFANode{}
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
			node.Trigrams = []string{} // reset so that they aren't continually reused in a cut...
		}
	}
	return &NFA{Start: nfa.Start, Accept: accept}, &NFA{Start: start, Accept: nfa.Accept}, orClause
}

func isolateCut(nfa *NFA) ([]*NFANode, int) {
	epoch := getEpoch()
	return isolateCutHelper(nfa.Start, epoch), epoch
}

func isolateCutHelper(node *NFANode, epoch int) []*NFANode {
	if seen(node, epoch) {
		return nil
	}
	result := []*NFANode{node}
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

// Find path from nfa.Start to nfa.Accept through vertices of positive capacity.
func FindAugmentingPath(nfa *NFA) []*NFANode {
	return findAugmentingPathHelper(nfa.Start, nfa.Accept, getEpoch())
}

func findAugmentingPathHelper(node *NFANode, accept *NFANode, epoch int) []*NFANode {
	if seen(node, epoch) || node.Capacity == 0 {
		return nil
	}
	if node == accept {
		return []*NFANode{node}
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

// Build the trigram set for all nodes in the NFA.
func PopulateTrigrams(nfa *NFA) {
	populateTrigramsHelper(nfa.Start, nfa.Accept, getEpoch())
}

func populateTrigramsHelper(node *NFANode, accept *NFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	if node.LitOut != nil {
		node.Trigrams = Trigrams(node, accept)
		populateTrigramsHelper(node.LitOut, accept, epoch)
	}
	for _, e := range node.Epsilons {
		populateTrigramsHelper(e, accept, epoch)
	}
}

// Calculate capacities for all nodes in the NFA.
func PopulateCapacities(nfa *NFA) {
	populateCapacitiesHelper(nfa.Start, getEpoch())
}

func populateCapacitiesHelper(node *NFANode, epoch int) {
	if seen(node, epoch) {
		return
	}
	// - Any node with LitOut = nil has capacity infinity
	// - Any node with LitOut != nil && empty trigram set has capacity infinity
	// - Any node with LitOut != nil && non-empty trigram set has capacity == len(trigram set)
	if node.LitOut != nil {
		nt := len(node.Trigrams)
		if nt > 0 {
			node.Capacity = nt
		} else {
			node.Capacity = Infinity
		}
		populateCapacitiesHelper(node.LitOut, epoch)
	} else {
		node.Capacity = Infinity
	}
	for _, e := range node.Epsilons {
		populateCapacitiesHelper(e, epoch)
	}
}
