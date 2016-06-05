package main

import (
	"fmt"
	"os"
	"github.com/aaw/regrams"
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "Usage: regrams <regular expression>")
		os.Exit(1)
	}
	query, err := regrams.MakeQuery(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println(query)
}
