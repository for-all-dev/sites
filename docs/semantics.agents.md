# Future work: deep embedding with a full operational semantics

Status: **planned, not started.** Decided 2026-09-25.

## Decision

The first cut of the generator verifies its pipeline with the stock
`Std.Do` Hoare-triple library and the `mvcgen` tactic, and verifies the pure
parts (HTML/CSS printers, escaping, routing) with ordinary theorems.

The second phase, which the owner explicitly wants, is a *deep embedding* of
the page/template language with a *full operational semantics*, and a custom
verification-condition generator for it written in `SymM`.

## What that means concretely

1. **Deep-embed the page language.** Today a page is a Lean term of the typed
   HTML DSL (`Sites.Html`), i.e. a shallow embedding: the host language does
   sequencing, binding and abstraction. The deep embedding adds an inductive
   syntax `Sites.Lang.Expr` / `Sites.Lang.Cmd` for the *template* language
   (variables, layouts as functions, loops over collections, conditionals,
   includes) so that page programs are data we can reason about.
2. **Give it an operational semantics.** An inductive predicate
   `Sites.Lang.Step : Config → Config → Prop` (small-step) plus the derived
   big-step relation, following the omnisemantics style used by the `Std.WP`
   deep-embedding example in Lean core (`tests/elab/vcgenImp.lean` in the
   lean4 repository is the reference template). Provide a `WP Cmd Unit Pred
   EStack⟨⟩` instance from `Std.WP` so the deep language plugs into the same
   Hoare-triple machinery as the shallow pipeline.
3. **Write a VCGen in `SymM`.** `Lean.Meta.Sym.SymM` (Lean ≥ 4.28) is the
   monad Leo de Moura built for symbolic simulators and VC generators; it is
   orders of magnitude faster than `MetaM`-based `apply`/`intro` loops. The
   generator walks a page program symbolically, emits verification conditions
   (e.g. "every emitted `href` targets a declared route", "every `li` lands
   inside a list", "no unescaped user text reaches the output"), and hands the
   residue to `grind` via `Lean.Meta.Sym.Grind`. Entry points to study:
   `Lean/Meta/Sym/SymM.lean`, `Lean/Meta/Sym/Grind.lean`,
   `Lean/Elab/Tactic/Grind/Sym.lean` in the toolchain sources.
4. **Compile to the shallow DSL.** A verified compiler
   `Sites.Lang.compile : Cmd → Sites.Html` with a theorem that the compiled
   page's rendering equals the semantics' output. This keeps the existing
   printer round-trip theorems as the trusted base.

## Why later, not now

- The shallow embedding already gets the four properties the owner asked for
  (printer round-trip, typed CSS, no dead links, pipeline Hoare specs).
- `SymM` is still moving fast on nightly and has no user-facing docs; the
  reference implementation is `grind`'s own use of it.
- The deep embedding is only valuable once there is a template language
  worth reasoning about. Phase one establishes what that language needs.

## Constraints that carry over

Same escape-hatch policy as the rest of the project: no `partial`,
`noncomputable`, `unsafe`, `implemented_by`, `sorry`, `native_decide`, or
`axiom`. The semantics must be an inductive predicate, not a fuelled
interpreter, so that theorems are about *all* executions.
