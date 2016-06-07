package main

import (
	"flag"
	"fmt"
	"os"
	"github.com/aaw/regrams"
)

var maxCharClassSize = flag.Int("maxCharClassSize", 10,
	"Maximum size of a character class regrams considers expanding. " +
	"If 5, [1-5] can be expanded to trigrams but [1-6] won't.")

var maxTrigramSetSize = flag.Int("maxTrigramSetSize", 100,
	"Maximum size of a trigram disjunction allowed in a query.")

var maxNFANodes = flag.Int("maxNFANodes", 1000,
	"Maximum size of an NFA that will be considered for generating a query.")

func main() {
	flag.Parse()
	e := regrams.NewEngine(*maxCharClassSize, *maxTrigramSetSize, *maxNFANodes)
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "Usage: regrams <regular expression>")
		os.Exit(1)
	}
	query, err := e.MakeQuery(flag.Arg(0))
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println(query)
}
