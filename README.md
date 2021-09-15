# oberon-compiler

This is a port of the
[Project Oberon](https://people.inf.ethz.ch/wirth/ProjectOberon/index.html)
compiler for RISC-5 (not to be confused with RISC-V) from Oberon to Go.
The compiled binaries can be run  in a Project Oberon RISC emulator like
Peter de Wachter's [oberon-risc-emu](https://github.com/pdewacht/oberon-risc-emu)
or on my [port of it to Go](https://github.com/fzipp/oberon) —
or on real Project Oberon FPGA hardware, of course.

The source code of the original compiler by Niklaus Wirth can be found on
the website linked above.

## Installation

```
$ go install github.com/fzipp/oberon-compiler/cmd/oc@latest
```

## Usage

```
$ oc Hello.Mod
```

## Motivation

My motivation was the same as
<a href="https://github.com/arnobastenhof">@arnobastenhof</a>'s motivation to
[port a subset](https://github.com/arnobastenhof/oberon) of Wirth's
reference implementation for the Oberon-07 language to C:

> "It was written primarily for self-educational purposes as a kind of
> intensive code reading exercise."

Having a compiler available outside the target system also turned out to be
useful in practice. One can develop code in a familiar environment before
transferring it to the target system.

## Porting Notes

- I resisted the temptation to remove limits like the maximum
  length of strings or identifiers in order to keep source code 
  written for this compiler compatible with the original compiler.
  These restrictions can also have an educational value as Hanspeter
  Mössenböck points out in
  [Compiler Construction - The Art of Niklaus Wirth](ftp://ftp.ssw.uni-linz.ac.at/pub/Papers/Moe00b.pdf).
- `REPEAT...UNTIL x;` was translated to Go as `for {...; if x { break } }`.
  I did not rewrite these loops as loops with the condition at the start
  (which would be idiomatic Go) in order to preserve the original
  control flow.
- I kept the "single return" style of Oberon and did not translate it to the
  "early return" style that is idiomatic in Go.
- I kept the short names, but I changed the capitalization of many variables
  and struct fields consistently to "camel case". I had to slightly adjust the
  names of some functions and variables that would otherwise clash with Go
  keywords, specifically `import` and `type`.
- I introduced the types `ors.Sym`, `orb.Form` and `orb.Class`, and prefixed
  the names of their enumeration-like constants, as it is customary in Go.
  The original code uses raw integer types for them, but I found the additional 
  type safety helpful.
- The functionality is implemented in Go as methods on types (`ors.Scanner`,
  `orp.Parser`, `orb.Base`, `org.Generator`), not as free functions in
  "flat" packages with package scoped variables. This is a deviation from the
  original implementation, but it allows the creation of multiple compiler
  instances, for example to compile multiple modules in parallel with
  goroutines.
- I used a map for `ors.keyTab` instead of an array-based lookup table, and a
  slice for `orp.Parser.pbsList` instead of a linked list.
- I extracted two instances of duplicated code fragments in the scanner
  as two new methods: `ors.Scanner.hexDigit` and `ors.Scanner.decimalInteger`.
- Non-compilation errors like I/O errors are propagated as panics,
  with `orp.Compile` acting as the boundary where they are recovered
  and transformed back into a regular error return value.
- `DIV` and `MOD` in Oberon are defined differently than `/` and `%` in Go
  (floored division vs. truncated division). In Oberon `(-15) DIV 4 = -4` and
  `(-15) MOD 4 = 1`, whereas in Go `(-15) / 4 == -3` and `(-15) % 4 == -3`.
  The original code frequently uses `DIV` and `MOD` for bit shifting and
  masking. The translated code uses bitwise operators such as `<<`, `>>`
  and `&` instead where appropriate.

## License

This project is free and open source software licensed under the
[ISC License](LICENSE).
