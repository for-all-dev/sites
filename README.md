# sites

A static site generator written in Lean 4, with the parts that matter proven.

- **Typed HTML.** Pages are Lean terms. The document tree is an inductive family indexed by
  content category, so a `li` outside a list or a `p` inside a `span` is a type error.
- **Verified printer.** There is a parser for the printer's output and a theorem that parsing
  a rendered document gives back the document (`Sites.Html.parseDocument_render_norm`).
- **Typed links.** Internal links are values of the site's route type. A dead link does not
  compile. Markdown pages get the same check through a `decide` proof at elaboration time.
- **Typed CSS.** A stylesheet DSL with units, colours and selectors, plus a theorem that its
  output is derivable in a CSS grammar (`Sites.Css.Stylesheet.render_grammar`).
- **Verified build loop.** The build has a Hoare-triple contract, proven with Lean's `vcgen`,
  and an end-to-end theorem: after a build, every route's file parses back to its document
  (`Sites.Site.build_pages`).
- **No escape hatches.** No `partial`, `noncomputable`, `unsafe`, `implemented_by`,
  `native_decide`, `sorry` or custom axioms anywhere. `scripts/check.sh` enforces it and
  re-checks the compiled proofs with the toolchain's independent `leanchecker`.

Everything targets a Lean nightly (see `lean-toolchain`) and uses the module system, the
`Std.WP` program logic and `Std.Http`. See `docs/` for the design and the verification story.

## Use

```sh
lake build            # build the library, the example site and the CLI
lake build Test       # run the executable checks and the axiom audit
.lake/build/bin/sites build [dist]   # write the example site
.lake/build/bin/sites serve [8080]   # serve it from memory over HTTP
scripts/check.sh      # everything above plus the escape-hatch audit and leanchecker
```

With Nix: `nix develop` provides `elan`, which picks up `lean-toolchain`.

## Writing a site

Look at `Example/Site.lean`. In short:

```lean
inductive Route | home | about deriving DecidableEq

def path : Route → Path
  | .home => []
  | .about => [seg "about"]

def site : Site Route :=
  { name := "My site"
    routes := [.home, .about]
    routes_complete := by intro r; cases r <;> decide
    path
    urls_nodup := by decide
    page := fun
      | .home => { title := "Home", body := [p [] ["Hello, ", a [.href (.route .about)] ["about"]]] }
      | .about => { title := "About", body := md chars!"Markdown with [links](/)." }
    nav := [(.home, "Home"), (.about, "About")]
    stylesheet := [rule (.tag .p) [.color (.hex 0x33 0x33 0x33)]] }
```

Elements are functions named after their tags. Strings coerce to text where text is allowed.
An element used in the wrong place fails with a `Fits` error at the use site. Markdown goes
through `chars!"..."` so that the link check runs in the kernel in about a second; a dead
`/link/` is reported as `decide proved that the proposition ... is false`.

## Layout of the code

| Module | What it is |
| --- | --- |
| `Sites/Html/Syntax.lean` | Content categories, tags, attributes, the `Node`/`Nodes` family, smart constructors. |
| `Sites/Html/Escape.lean` | Escaping and its inverse, with proofs. |
| `Sites/Html/Render.lean` | The canonical printer. |
| `Sites/Html/Parse.lean` | The fuel-bounded parser for the printer's output. |
| `Sites/Html/RoundTrip.lean` | `parseDocument_render`: parsing a rendered canonical document gives it back. |
| `Sites/Html/Norm.lean` | `norm` makes any tree canonical without changing its rendering. |
| `Sites/Css.lean`, `Sites/Css/Grammar.lean` | The CSS DSL, its printer, the grammar and the validity theorem. |
| `Sites/Site.lean` | Routes, paths, pages, layouts; `RouteInverse`/`RouteSection` for a site. |
| `Sites/Markdown.lean` | The total Markdown subset and its lowering to typed HTML. |
| `Sites/Build.lean` | `writeAll` over an abstract file system, the model contract, `Site.build_pages`. |
| `Sites/Serve.lean` | The `Std.Http` development server. |
| `Example/Site.lean` | The example site. |
| `Test.lean` | Executable checks and the axiom audit. |
| `docs/` | Design notes, including planned future work. |
