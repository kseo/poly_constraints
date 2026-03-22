# Poly

A small ML-like language with **constraint-based Hindley-Milner type inference**, let polymorphism, and a fixpoint operator. Unlike traditional syntax-directed HM inference, this implementation uses a **constraint generation and solving** approach that cleanly separates constraint collection from unification.

## Build & Run

```shell
$ cabal run
```

Or load a source file directly:

```shell
$ cabal run poly -- test.ml
```

## Language Features

- **Let polymorphism** with generalization
- **Lambda abstractions** (`\x -> ...`)
- **Recursive definitions** via `let rec` (desugared to `fix`)
- **Integer and boolean literals** with built-in operators (`+`, `-`, `*`, `==`)
- **Conditionals** (`if ... then ... else ...`)

## REPL

The interactive REPL supports defining values, evaluating expressions, and inspecting types:

```
Poly> let i x = x;
i : forall a. a -> a

Poly> i 3
3 : Int

Poly> :type let k x y = x;
k : forall a b. a -> b -> a

Poly> :type let s f g x = f x (g x)
s : forall a b c. ((a -> b) -> c -> a) -> (a -> b) -> c -> b

Poly> :type let on g f = \x y -> g (f x) (f y)
on : forall a b c. (a -> a -> b) -> (c -> a) -> c -> c -> b

Poly> :type let compose f g = \x -> f (g x)
compose : forall a b c. (a -> b) -> (c -> a) -> c -> b

Poly> let rec factorial n =
  if (n == 0)
  then 1
  else (n * (factorial (n-1)));
```

### REPL Commands

| Command           | Description                        |
|-------------------|------------------------------------|
| `:load <file>`    | Load and execute a source file     |
| `:type <expr>`    | Display the inferred type          |
| `:browse`         | List all definitions and types     |
| `:quit`           | Exit the REPL                      |

## Architecture

```
Input Text
  → Lexer.hs      (tokenization via Parsec)
  → Parser.hs     (AST construction)
  → Infer.hs      (constraint generation & solving)
  → Eval.hs       (interpretation)
  → Pretty.hs     (output formatting)
```

### Type Inference

The core of this project is the **constraint-based** type inference engine in `Infer.hs`. Instead of performing unification inline during AST traversal, it:

1. **Generates constraints** from the AST — three kinds:
   - `EqConst` — equality constraints between two types (standard unification)
   - `ExpInstConst` — explicit instantiation of a polymorphic scheme
   - `ImpInstConst` — implicit instantiation with a monomorphic variable set
2. **Solves constraints** iteratively, picking the next solvable constraint and applying substitutions until all constraints are resolved.

This separation makes the algorithm easier to reason about and extend compared to Algorithm W.

### Modules

| Module           | Role                                              |
|------------------|---------------------------------------------------|
| `Syntax.hs`      | AST definition (`Expr`, `Lit`, `Binop`, `Decl`)   |
| `Type.hs`        | Type representations (`Type`, `TVar`, `Scheme`)    |
| `Lexer.hs`       | Lexical analysis (reserved words, operators)       |
| `Parser.hs`      | Parser producing the AST from source text          |
| `Infer.hs`       | Constraint generation, unification, and solving    |
| `Assumption.hs`  | Intermediate type assumptions during inference     |
| `Env.hs`         | Final type environment (name → type scheme)        |
| `Eval.hs`        | Tree-walking interpreter with closures             |
| `Pretty.hs`      | Pretty-printing for types, expressions, constraints|
| `Main.hs`        | REPL built on the `repline` library                |

## Syntactic Sugar

Top-level `let` declarations with multiple arguments desugar to nested lambdas:

```ocaml
let add x y = x + y;
(* equivalent to *)
let add = \x -> \y -> x + y;
```

`let rec` declarations desugar to use of the `fix` operator:

```ocaml
let rec factorial n = if (n == 0) then 1 else (n * (factorial (n-1)));
(* equivalent to *)
let factorial = fix (\factorial n -> if (n == 0) then 1 else (n * (factorial (n-1))));
```

## References

- Heeren, B., Hage, J., & Swierstra, S. D. (2002). *Generalizing Hindley-Milner Type Inference Algorithms*.
- Damas, L., & Milner, R. (1982). *Principal type-schemes for functional programs*.

## License

Released under the MIT license.
