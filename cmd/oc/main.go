package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/fzipp/oberon-compiler/orp"
)

func usage() {
	printVersion()
	fail(`
Compiles the source code of one or more Oberon modules (.Mod)
to object files for RISC-5 (.rsc) and accompanying symbol files (.smb).

Usage:
    oc [-s] modfile...

Flags:
    -s  Overwrites existing symbol file on changes.

Examples:
    oc Hello.Mod
    oc -s Hello.Mod
    oc A.Mod B.Mod C.Mod
    oc *.Mod`)
}

func main() {
	newSF := flag.Bool("s", false, "overwrites existing symbol file on changes")
	flag.Usage = usage
	flag.Parse()

	if flag.NArg() < 1 {
		usage()
	}

	printVersion()
	for _, arg := range flag.Args() {
		err := orp.CompileFile(arg, *newSF)
		check(err)
	}
}

func printVersion() {
	fmt.Println("OR Compiler  8.3.2020; ported to Go")
}

func check(err error) {
	if err != nil {
		fail(err)
	}
}

func fail(msg interface{}) {
	_, _ = fmt.Fprintln(os.Stderr, msg)
	os.Exit(1)
}
