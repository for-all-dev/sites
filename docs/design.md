# Design

## What "verified" means here

Four theorems carry the claim; everything else exists to state them.

1. `Sites.Html.parseDocument_render_norm` (`Sites/Html/Norm.lean`).
   For any document `d` and any site whose `route?`/`url` pair satisfies `RouteInverse` and
   `RouteSection`, `parseDocument route? (d.render url) = some (d.norm route?)`. The parser
   accepts only the printer's canonical output, so this is a specification of the printer:
   escaping is correct, every tag is closed, nesting is preserved, attribute values survive.
2. `Sites.Css.Stylesheet.render_grammar` (`Sites/Css/Grammar.lean`).
   The rendered stylesheet is derivable in `Css.Grammar.Stylesheet`, an inductive predicate
   that follows the CSS Syntax Level 3 token grammar for the constructs the printer emits.
3. `Sites.writeAllModel.spec` (`Sites/Build.lean`).
   The build loop, at the model file system `StateM FS`, writes exactly the listed files and
   touches nothing else. Proven by `vcgen` from the intrinsic contract on the definition.
   `writeAllModel_eq` shows this is definitionally the generic `writeAll` the IO build runs.
4. `Sites.Site.build_pages` (`Sites/Build.lean`).
   After a build on the model, every route's file holds its rendered page and parsing it
   gives the route's normalised document. This composes 1, 3 and the route lemmas.

Two facts are enforced by types rather than theorems:

- Internal links are `Link.route r` with `r : ρ`, the site's route type. There is no way to
  write a dangling internal link in the DSL. Markdown links are strings, so `Markdown.md`
  takes a `decide` proof that every `/…` link resolves; a bad link fails elaboration.
- Content categories are indices of `Node`. Placement is witnessed by `Fits`, found by a
  default tactic, so `ul [] [p [] ["x"]]` is rejected at the use site.

## What is trusted

- Lean's kernel and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
  `Test.lean` pins each headline theorem to exactly those.
- The compiler and runtime: the theorems are about the Lean definitions, and the executable is
  produced by the (unverified) Lean compiler. `scripts/check.sh` re-checks the `.olean` files
  with `leanchecker`, so the proofs do not depend on the elaborator either.
- `IO.FS.writeFile` and `Std.Http`: the build contract is proven on a file-system model, and
  the server is not specified. The IO instance of `MonadFS` is eleven lines.
- The CSS grammar itself: it is a hand-written subset of the standard.

## Why the parser has fuel

`parseNode`/`parseNodes` recurse on an explicit fuel argument rather than on the input's
length through well-founded recursion. Two reasons: structural recursion keeps the round-trip
proof a plain mutual induction, and fuel-based definitions reduce in the kernel, which the
Markdown link check relies on (`decide +kernel` evaluates the parser at elaboration time).
The default fuel is `input.length + 1`; `Nodes.size_le_render` shows it always suffices.

One practical wrinkle: the kernel decodes a `String` literal into characters very slowly
(about 40 s for 700 bytes on this toolchain), while it evaluates the parser on a character
list in about a second. `chars!"..."` therefore expands a string literal into a `List Char`
literal at elaboration time, and `Markdown.md` takes that list.

## Canonical form

The round-trip theorem holds for canonical trees: no empty text, no two adjacent text nodes,
`Link.url` only for URLs that are not routes. `Document.norm` produces a canonical tree with
the same rendering (`Document.render_norm`, `Document.norm_canonical`), and `Site.html`
renders `norm d`, so the theorem applies to every file written.

## Verso

Verso (Lean FRO's documentation framework) was considered and set aside for the core. Its
`Html` type is untyped (`text` takes an `escape : Bool` flag; `tag` takes any name and any
children) and its rendering path is `partial`, so nothing can be proven about its output.
Its authoring syntax is separable: an adapter lowering `Verso.Doc` into `Sites.Html.Node`
would reuse it without touching the verified part. Not started.

## Dev server

Plain HTTP/1.1 via `Std.Http`, serving from memory. No TLS: the standard library has none and
linking OpenSSL would put unverified C under the generator. Use a reverse proxy for HTTPS.
There is no file watcher: content is Lean, so a change means recompiling; restart `serve`.
