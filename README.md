# Acid Synchrone

This project is a compiler for Acid Synchrone, an experimental first-order
functional programming language. It is a domain-specific language designed to
ease the implementation of high-performance reactive systems.

Acid Synchrone programs handle infinite streams of values. The compiler employs
a dedicated static analysis (the clock calculus) to reject ill-behaved
programs and generate efficient code for well-behaved ones.

The compiler and related tools are released under GPLv3.

# Examples

See the examples/ directory.

# Building the compiler

The Acid Synchrone compiler is written in OCaml. To compile it, you need:
* the OCaml compiler and run-time system: http://caml.inria.fr
* the OCamlGraph library: http://ocamlgraph.lri.fr
* the Menhir parser generator: http://pauillac.inria.fr/~fpottier/menhir/

(I strongly recommend the use of FindLib to handle OCamlGraph and Menhir. Note
that "opam install menhir ocamlgraph" should do the trick.)

To compile, just run "make" in the top-level directory, and add this directory
to your path.

# Running the compiler

To use the compiler to its full extent, you need a linear programming
solver. Currently, only the GNU Linear Programming Kit is supported.

# Architecture

The directory layout of Acid Synchrone is as follows:

- base/ holds a library of basic modules used in the project

- resolution/ holds a library dedicated to the resolution of sampling problems
  on ultimately periodic integer words.

- quicksolve/ holds a small stand-alone utility using the abovementioned
  library, see tests/sys/ its the textual input format.

- compiler/ holds the... compiler (doh!)
  - frontend/ is mainly dedicated to clock type inference
    - asts/ holds the various asts of the front-end. The main AST is a functor,
      enabling reuse and type-safety through the front-end
    - parsing/ holds the parser and lexer
    - typing/ holds the various type-like analysis, from data typing to clock
      typing.
    - misc_passes/ holds miscellaneous passes.

  - middleend/ is responsible on optimizations of the NIR language, an n-ary IR
    with only three-address code.This part handles scheduling and (one day)
    data-flow optimizations.

  - backend/ is responsible for the translation to imperative code. Currently,
    this may generate (poor and ugly) C code for a subset of well-typed AcidS
    programs.

# Limitations

The following features are *not* supported, and will only be available once the
second version of the compiler is done:

- Hardware (VHDL) generation
- Integrated clocking and productivity analysis (the current compiler may infer
  clock types that make programs non-productive!)
- Higher-order functions
- Code generation for data-type polymorphic functions
- Any optimization whatsoever

More generally, you can expect the compiler to be buggy and unpredictable.

# Acknowledgments

This project relies on numerous tools, libraries and ideas. Some
acknowledgments:

- F. Pottier and Y. Régis-Gianas for Menhir

- S. Conchon, J.-C. Filliâtre and J. Signoles for OcamlGraph

- F. Pottier, D. Rémy and Y. Régis-Gianas for their UnionFind implementation
  (see base/UnionFind.ml{,i} in the source)

- L. Mandel and F. Plateau for Lucy-n in general and its testing infrastructure
  in particular (see test/tools).

- P. Caspi, N. Halbwachs, M. Pouzet, P. Raymond and others for their general
  work on the design and implementation of synchronous functional languages.

-- Adrien Guatto <adrien.guatto@laposte.net>