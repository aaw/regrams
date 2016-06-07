package regrams

import (
	"bytes"
	"fmt"
	"regexp/syntax"
	"sort"
	"testing"
)

var parseExamples = []struct {
	r string
	p string
}{
	{`[a-ce-z]`, `([a-c]|[e-z])`},
	{`\\b[ab]{0,3}\\b`, `\b(([a-b])(([a-b])(([a-b])|ε)|ε)|ε)\b`},
	{`BBB([^BD]*)EEE{2,3}`, "BBB(([\x00-A]|C|[E-\U0010FFFF]))*EEEE(E|ε)"},
	{`[0-9a-zA-Z]{3}|123`, `(([0-9]|[A-Z]|[a-z])([0-9]|[A-Z]|[a-z])([0-9]|[A-Z]|[a-z])|123)`},
	{`[^t]abc[59][^5](xxx|yyy)z`, "([\x00-s]|[u-\U0010FFFF])abc(5|9)([\x00-4]|[6-\U0010FFFF])(xxx|yyy)z"},
	{`abc{3,7}`, `abccc(c(c(c(c|ε)|ε)|ε)|ε)`},
	{`(abc[a-z]{3}|[a-z]{2}xyz)`, `(abc([a-z])([a-z])([a-z])|([a-z])([a-z])xyz)`},
	{`abc?`, `ab(c|ε)`},
}

func (s regexp) String() string {
	var buffer bytes.Buffer
	regexpStringHelper(s, &buffer)
	return buffer.String()
}

func regexpStringHelper(s regexp, buf *bytes.Buffer) {
	switch s.Op {
	case kleeneStar:
		buf.WriteString("(")
		regexpStringHelper(*s.Sub[0], buf)
		buf.WriteString(")*")
	case concatenate:
		for _, x := range s.Sub {
			regexpStringHelper(*x, buf)
		}
	case alternate:
		buf.WriteString("(")
		for i, x := range s.Sub {
			regexpStringHelper(*x, buf)
			if i < len(s.Sub)-1 && len(s.Sub) > 1 {
				buf.WriteString("|")
			}
		}
		buf.WriteString(")")
	case literal:
		if s.LitBegin == s.LitEnd {
			buf.WriteString(fmt.Sprintf("%c", s.LitBegin))
		} else {
			buf.WriteString(fmt.Sprintf("[%c-%c]", s.LitBegin, s.LitEnd))
		}
	case emptyString:
		buf.WriteString("ε")
	case noMatch:
		buf.WriteString("∅")
	}
}

func TestParse(t *testing.T) {
	for _, ex := range parseExamples {
		p, _ := parseRegexpString(ex.r)
		if p.String() != ex.p {
			t.Errorf("Got %v, want %v", p, ex.p)
		}
	}
}

func assertNodeSetEqual(t *testing.T, want []*nFANode, got []*nFANode) {
	if len(want) != len(got) {
		t.Fatalf("Wanted length %v, got length %v", len(want), len(got))
	}
	swant := make([]string, len(want))
	for i := range want {
		swant[i] = fmt.Sprintf("%v", want[i])
	}
	sgot := make([]string, len(got))
	for i := range got {
		sgot[i] = fmt.Sprintf("%v", got[i])
	}
	sort.Strings(swant)
	sort.Strings(sgot)
	for i, x := range swant {
		if x != sgot[i] {
			t.Errorf("In position %v, want %v but got %v", i, x, sgot[i])
		}
	}
}

func TestEpsilonClosure(t *testing.T) {
	n1 := &nFANode{}
	n2 := &nFANode{}
	n3 := &nFANode{}
	n4 := &nFANode{Epsilons: []*nFANode{n1, n2}}
	n5 := &nFANode{Epsilons: []*nFANode{n3}}
	n6 := &nFANode{Epsilons: []*nFANode{n4, n1}}
	n7 := &nFANode{Epsilons: []*nFANode{n4, n5}}
	n8 := &nFANode{Epsilons: []*nFANode{n1, n3, n7}}
	n9 := &nFANode{Epsilons: []*nFANode{n8, n6}}
	n10 := &nFANode{Epsilons: []*nFANode{n9}}
	n10.Epsilons = append(n10.Epsilons, n10)
	n1.Epsilons = append(n1.Epsilons, n8)
	populateEpsilonClosure(&nFA{Start: n10, Accept: n1})
	assertNodeSetEqual(t, []*nFANode{n2}, n2.EpsilonClosure)
	assertNodeSetEqual(t, []*nFANode{n1, n2, n3, n4, n5, n6, n7, n8, n9}, n9.EpsilonClosure)
	assertNodeSetEqual(t, []*nFANode{n1, n2, n3, n4, n5, n6, n7, n8, n9, n10}, n10.EpsilonClosure)
}

func TestTrigrams1(t *testing.T) {
	s := "[a-c]b[v-z]"
	r, err := parseRegexpString(s)
	if err != nil {
		t.Fatalf("Error parsing regex: %s", err)
	}
	nfa := buildNFA(r)
	populateEpsilonClosure(nfa)
	e := NewEngine(10, 100, 1000)
	trigrams := e.trigrams(nfa.Start, nfa.Accept)
	want := "[abv abw abx aby abz bbv bbw bbx bby bbz cbv cbw cbx cby cbz]"
	if fmt.Sprintf("%v", trigrams) != fmt.Sprintf("%v", want) {
		t.Errorf("Got %v, want %v", trigrams, want)
	}
}

func TestTrigrams2(t *testing.T) {
	s := "(abc)|(xyz)|(afc)|(a[b-f]c)"
	r, err := parseRegexpString(s)
	if err != nil {
		t.Fatalf("Error parsing regex: %s", err)
	}
	nfa := buildNFA(r)
	populateEpsilonClosure(nfa)
	e := NewEngine(10, 100, 1000)
	trigrams := e.trigrams(nfa.Start, nfa.Accept)
	want := "[abc acc adc aec afc xyz]"
	if fmt.Sprintf("%v", trigrams) != fmt.Sprintf("%v", want) {
		t.Errorf("Got %v, want %v", trigrams, want)
	}
}

func TestTrigrams3(t *testing.T) {
	s := "(a|b){3,5}"
	r, err := parseRegexpString(s)
	if err != nil {
		t.Fatalf("Error parsing regex: %s", err)
	}
	nfa := buildNFA(r)
	populateEpsilonClosure(nfa)
	e := NewEngine(10, 100, 1000)
	trigrams := e.trigrams(nfa.Start, nfa.Accept)
	want := "[aaa aab aba abb baa bab bba bbb]"
	if fmt.Sprintf("%v", trigrams) != fmt.Sprintf("%v", want) {
		t.Errorf("Got %v, want %v", trigrams, want)
	}
}

func TestTrigrams4(t *testing.T) {
	s := "abc?"
	r, err := parseRegexpString(s)
	if err != nil {
		t.Fatalf("Error parsing regex: %s", err)
	}
	nfa := buildNFA(r)
	populateEpsilonClosure(nfa)
	e := NewEngine(10, 100, 1000)
	trigrams := e.trigrams(nfa.Start, nfa.Accept)
	want := "[]"
	if fmt.Sprintf("%v", trigrams) != fmt.Sprintf("%v", want) {
		t.Errorf("Got %v, want %v", trigrams, want)
	}
}

var queryExamples = []struct {
	r string
	q string
}{
	{`[a-ce-z]`, ``},
	{`[^t]abc[59][^5](xxx|yyy)z`, `(abc) (bc5|bc9) (xxx|yyy) (xxz|yyz)`},
	{`[a-c][0-3]zz`, `(a0z|a1z|a2z|a3z|b0z|b1z|b2z|b3z|c0z|c1z|c2z|c3z) (0zz|1zz|2zz|3zz)`},
	{`[a-z]ab[a-z]def[a-z]gh[a-z]`, `(def)`},

	// Examples from codesearch tests
	{`Abcdef`, `(Abc) (bcd) (cde) (def)`},
	{`(abc)(def)`, `(abc) (bcd) (cde) (def)`},
	{`abc.*(def|ghi)`, `(abc) (def|ghi)`},
	// Note: codesearch parses the next query into "abc (bcd cde def)|(bcg cgh ghi)", but
	// we don't attempt any such simplifications.
	{`abc(def|ghi)`, `(abc) (bcd|bcg) (cde|cgh) (def|ghi)`},
	// Note: codesearch parses the next two queries as "ahe ell hel llo" and
	// "(ahe ell hel llo)|(bwo orl rld wor)", respectively.
	{`a+hello`, `(aaa|aah|ahe) (hel) (ell) (llo)`},
	{`(a+hello|b+world)`, `(aaa|aah|ahe|bbb|bbw|bwo) (hel|wor) (ell|orl) (llo|rld)`},
	{`a*bbb`, `(bbb)`},
	{`a?bb`, ``},
	// Note: codesearch only parses the next query into "bbb".
	{`a?bbb`, `(abb|bbb)`},
	{`(bbb)a?`, `(bbb)`},
	{`(bbb)a*`, `(bbb)`},
	{`^abc`, `(abc)`},
	{`abc$`, `(abc)`},
	// Note: codesearch parses next query into "(abc bcf)|(abd bdf)|(abe bef)"
	{`ab[cde]f`, `(abc|abd|abe) (bcf|bdf|bef)`},
	// Note: codesearch parses next query into "cde (abc bcd)|(acd bac)"
	{`(abc|bac)de`, `(abc|bac) (acd|bcd) (cde)`},
	{`ab[^cde]f`, ``},
	{`ab.f`, ``},
	{`.`, ``},
	{`()`, ``},
	{`(?s).`, ``},
	// Query below has no match, but we don't distinguish all/no matches. If we can't
	// figure out a trigram query, we return the empty query.
	{`[^\s\S]`, ``},

	// Interesting Factoring examples.
	{`(abc|abc)`, `(abc)`},
	{`(ab|ab)c`, `(abc)`},
	{`ab(cab|cat)`, `(abc) (bca) (cab|cat)`},
	// codesearch returns (abc|def) for the query below.
	{`(z*(abc|def)z*)(z*(abc|def)z*)`,
		`(abc|def) (bca|bcd|bcz|efa|efd|efz) (cab|cde|cza|czd|czz|fab|fde|fza|fzd|fzz) (abc|def)`},
	{`(z*abcz*defz*)|(z*abcz*defz*)`,
		`(abc) (bcd|bcz) (cde|czd|czz) (def)`},
	// codesearch returns (abc) (def) (ghi|jkl|mno|prs) for the query below.
	{`(z*abcz*defz*(ghi|jkl)z*)|(z*abcz*defz*(mno|prs)z*)`,
		`(abc) (bcd|bcz) (cde|czd|czz) (def) (efg|efj|efm|efp|efz) (fgh|fjk|fmn|fpr|fzg|fzj|fzm|fzp|fzz) (ghi|jkl|mno|prs)`},
	// codesearch returns (abc def)|(ghi jkl)|(mno prs)|(tuv wxy) for the query below.
	{`(z*(abcz*def)|(ghiz*jkl)z*)|(z*(mnoz*prs)|(tuvz*wxy)z*)`,
		`(abc|ghi|mno|tuv) (bcd|bcz|hij|hiz|nop|noz|uvw|uvz) (cde|czd|czz|ijk|izj|izz|opr|ozp|ozz|vwx|vzw|vzz) (def|jkl|prs|wxy)`},
	// codesearch returns (abc) (def) (ghi|jkl) for the query below.
	{`(z*abcz*defz*)(z*(ghi|jkl)z*)`,
		`(abc) (bcd|bcz) (cde|czd|czz) (def) (efg|efj|efz) (fgh|fjk|fzg|fzj|fzz) (ghi|jkl)`},
	// codesearch returns (ghi|jkl)|(abc def)
	{`(z*abcz*defz*)|(z*(ghi|jkl)z*)`, `(abc|ghi|jkl)`},
	{`[ab][cd][ef]`, `(ace|acf|ade|adf|bce|bcf|bde|bdf)`},
	{`ab[cd]e`, `(abc|abd) (bce|bde)`},
	{`(a|ab)cde`, `(abc|acd) (cde)`},
	{`(a|b|c|d)(ef|g|hi|j)`, ``},
	{`(a|b|c|d)(ef|g|hi|j)*`, ``},
	{`(a|b|c|d)(ef|g|hi|j)+`, ``},

	// Expanding case.
	{`(?i)a~~`, `(A~~|a~~)`},
	{`(?i)ab~`, `(AB~|Ab~|aB~|ab~)`},
	{`(?i)abc`, `(ABC|ABc|AbC|Abc|aBC|aBc|abC|abc)`},
	{`(?i)abc|def`, `(ABC|ABc|AbC|Abc|DEF|DEf|DeF|Def|aBC|aBc|abC|abc|dEF|dEf|deF|def)`},
	{`(?i)abcd`, `(ABC|ABc|AbC|Abc|aBC|aBc|abC|abc) (BCD|BCd|BcD|Bcd|bCD|bCd|bcD|bcd)`},
	{`(?i)abc|abc`, `(ABC|ABc|AbC|Abc|aBC|aBc|abC|abc)`},

	// Word boundary.
	{`\b`, ``},
	{`\B`, ``},
	{`\babc`, `(abc)`},
	{`\Babc`, `(abc)`},
	{`abc\b`, `(abc)`},
	{`abc\B`, `(abc)`},
	{`ab\bc`, `(abc)`},
	{`ab\Bc`, `(abc)`},

	// Short examples that test trigram expansion near accept states.
	{`a+bc`, `(aaa|aab|abc)`},
	{`(bc)+d`, `(bcb|bcd)`},
	{`a(bc)+d`, `(abc) (bcb|bcd)`},
	{`abc+de`, `(abc) (bcc|bcd) (ccc|ccd|cde)`},
	{`(abc*)+de`, `(aba|abc|abd) (bab|bca|bcc|bcd|bde)`},
	{`ab(cd)*ef`, `(abc|abe) (bcd|bef)`},
	{`ab*cd`, `(abb|abc|acd)`},
	{`a+b+c+`, `(aaa|aab|abb|abc)`},

	// Our "trigrams" are three runes.
	{`プログラミング`, `(プログ) (ログラ) (グラミ) (ラミン) (ミング)`},
	{`(?i)Füße`, `(FÜß|FÜẞ|Füß|Füẞ|fÜß|fÜẞ|füß|füẞ) (ÜßE|Üße|ÜẞE|Üẞe|üßE|üße|üẞE|üẞe)`},
}

func TestQueries(t *testing.T) {
	for _, ex := range queryExamples {
		query, err := MakeQuery(ex.r)
		if err != nil {
			t.Fatalf("Error creating query: %v", err)
		}
		if query.String() != ex.q {
			t.Errorf("For query %v: got %v, want %v", ex.r, query, ex.q)
		}
	}
}

// Benchmarks

var benchmarkRegexps = []string{
	"(abc|def|ghi)",
	"[a-c]{0,8}",
	"[0-9]{1,5} ms",
	"(z*(abcz*def)|(ghiz*jkl)z*)|(z*(mnoz*prs)|(tuvz*wxy)z*)",
	"(a?){10}",
	"abcdefghijklmnopqrstuvwxyz",
	"a(b|c)+defg?hijk(lm|no)+pqrs(t|u|v|w)xyz",
	"abc|defg|hijkl|mno+pqr|stu+vwx*yz12+345+6+789",
	"(?i)abc|def",
	"ab[cd]e",
	"(a|ab)cde",
	"(a|b|c|d)(ef|g|hi|j)",
}

func BenchmarkQueryTestSuite(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for _, r := range benchmarkRegexps {
			MakeQuery(r)
		}
	}
}

func BenchmarkQueryBigNFA(b *testing.B) {
	r := "(a?){20}a{20}"
	for i := 0; i < b.N; i++ {
		MakeQuery(r)
	}
}

func BenchmarkGoParseAndSimplify(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for _, r := range benchmarkRegexps {
			re, err := syntax.Parse(r, syntax.Perl)
			if err != nil {
				panic(err)
			}
			re.Simplify()
		}
	}
}

func BenchmarkParseRegexpString(b *testing.B) {
	for i := 0; i < b.N; i++ {
		for _, r := range benchmarkRegexps {
			parseRegexpString(r)
		}
	}
}

func BenchmarkBuildNFA(b *testing.B) {
	parsed := []*regexp{}
	for _, r := range benchmarkRegexps {
		re, _ := parseRegexpString(r)
		parsed = append(parsed, re)
	}
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for _, p := range parsed {
			buildNFA(p)
		}
	}
}
