# regrams

regrams is a go package that implements an engine for regular expression
queries. Given a collection of documents that are indexed by trigrams (for
example, an index for a file containing "Hello, world!" would contain entries
for the substrings "Hel", "ell", "llo", "lo,", "o, ", ", w", " wo", "wor",
"orl", "rld", and "ld!", all pointing to that file) and a regular expression,
regrams can generate a boolean query for the trigram index that retrieves
candidates that might match the regular expression. The candidates that come
back can then be matched exhaustively against the regular expression.

For example, `regrams.MakeQuery("a(bc)+d")` returns "(abc) (bcb|bcd)", which
means that any document that matches the regular expression "a(bc)+d" must
contain the trigram "abc" as well as one of "bcb" or "bcd".

regrams is inspired by Google's [codesearch](https://github.com/google/codesearch)
repo and Russ Cox's corresponding [blog post](https://swtch.com/~rsc/regexp/regexp4.html)
explaining the implementation. Instead of using the structure of the parsed
regular expression to generate queries, however, regrams creates an NFA from
the query with nodes weighted by the size of the reachable trigram sets and
repeatedly extracts disjunctions from the NFA by identifying and removing
minimum-weight graph cuts. See [this post](LINK TBD) on regular expression
search via graph cuts for more background on the techinque.

The easiest way to try out this package is to build the command-line wrapper
included in this repo:

```
go get github.com/aaw/regrams
go build -o regrams github.com/aaw/regrams
```

Then you can use the command-line tool to start playing around with queries:

```
$ regrams abcd
(abc) (bcd)
./regrams 'Time: [0-9]+ ms'
( ms) (: 0|: 1|: 2|: 3|: 4|: 5|: 6|: 7|: 8|: 9) (Tim) (e: ) (ime) (me:)
$ regrams '(abc*)+de'
(aba|abc|abd) (bab|bca|bcc|bcd|bde)
$ regrams '(?i)abc'
(ABC|ABc|AbC|Abc|aBC|aBc|abC|abc)
```

Running `regrams --help` will give you more options.

To use regrams as a package, import `github.com/aaw/regrams`, then call
`regrams.MakeQuery` in your code to generate a trigram query from a string
representing a regular expression. `MakeQuery` returns a slice-of-slices of
strings, which should be interpreted as a boolean query in conjunctive
normal form: the slice `[["abc"], ["xyz","xyw"], ["xxx", "yyy", "zzz"]]`
represents the query "abc AND (xyz OR xyw) AND (xxx OR yyy OR zzz)".