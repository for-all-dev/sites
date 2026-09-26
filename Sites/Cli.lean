module
public import Sites.Site
public import Sites.Build
public import Sites.Serve

/-!
# Command-line interface

`Cli.run site args` is the whole `main` of a site executable: `build [DIR]` and `serve [PORT]`.
`Cli.new args` scaffolds a fresh site project that depends on this library, the equivalent of
`create docusaurus`.
-/

namespace Sites.Cli

/-- Usage text for a site executable. -/
public def usage (exe : String) : String :=
  s!"usage: {exe} build [OUT_DIR]   write the site (default: dist)\n" ++
  s!"       {exe} serve [PORT]      serve it over HTTP (default: 8080)"

/-- The `main` of a site executable. -/
public def run {ρ : Type} [DecidableEq ρ] (site : Site ρ) (args : List String)
    (exe : String := "site") : IO UInt32 := do
  match args with
  | ["build"] => site.build "dist"; IO.println "wrote dist/"; return 0
  | ["build", out] => site.build out; IO.println s!"wrote {out}/"; return 0
  | ["serve"] => site.serve 8080; return 0
  | ["serve", port] =>
    match port.toNat? with
    | some p => site.serve p.toUInt16; return 0
    | none => IO.eprintln (usage exe); return 1
  | _ => IO.eprintln (usage exe); return 1

/-! ## Scaffolding -/

/-- Valid project names: lowercase letters, digits and dashes, starting with a letter. -/
public def validName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isLower && cs.all fun d => d.isLower || d.isDigit || d = '-'

/-- `my-site` becomes `MySite`. -/
public def moduleName (s : String) : String :=
  String.join ((s.splitOn "-").map String.capitalize)

/-- Where the library is fetched from. -/
public def libraryUrl : String := "https://github.com/for-all-dev/sites.git"

/-- The toolchain line, in the form `elan` expects for nightlies. -/
public def toolchainLine : String :=
  if Lean.toolchain.startsWith "leanprover/lean4:nightly-" then
    "leanprover/lean4-nightly:" ++ (Lean.toolchain.drop "leanprover/lean4:".length)
  else Lean.toolchain

/-- `lakefile.toml` for a new site. -/
public def lakefile (name : String) : String :=
  let m := moduleName name
  s!"name = \"{name}\"\nversion = \"0.1.0\"\ndefaultTargets = [\"{name}\"]\n\n" ++
  "[leanOptions]\nautoImplicit = false\n\n" ++
  s!"[[require]]\nname = \"sites\"\ngit = \"{libraryUrl}\"\nrev = \"master\"\n\n" ++
  s!"[[lean_lib]]\nname = \"{m}\"\n\n" ++
  s!"[[lean_exe]]\nname = \"{name}\"\nroot = \"Main\"\n"

/-- `Main.lean` for a new site. -/
public def mainFile (name : String) : String :=
  let m := moduleName name
  s!"import Sites\nimport {m}\n\n" ++
  s!"/-- `build [DIR]` or `serve [PORT]`. -/\n" ++
  s!"def main (args : List String) : IO UInt32 := Sites.Cli.run {m}.site args \"{name}\"\n"

/-- The site module for a new site: two pages, one in the DSL and one in Markdown. -/
public def siteFile (name : String) : String :=
  let m := moduleName name
  s!"module\npublic import Sites\n\n" ++
  s!"/-! # {name}\n\nThe routes are an enumeration: every internal link is a value of `Route`, so a dead link\n" ++
  "does not compile. `routes_complete` and `urls_nodup` are proven by `decide`. -/\n\n" ++
  s!"namespace {m}\n\nopen Sites Sites.Html\n\n@[expose] public section\n\n" ++
  "/-- The routes. -/\ninductive Route where\n  | home\n  | about\n  deriving DecidableEq, Repr\n\n" ++
  "/-- All routes, in navigation order. -/\ndef routes : List Route := [.home, .about]\n\n" ++
  "/-- Where each route lives. -/\ndef path : Route → Path\n  | .home => []\n  | .about => [seg \"about\"]\n\n" ++
  "/-- Route lookup, shared with the Markdown link checker. -/\n" ++
  "def route? : List Char → Option Route := routeOfChars routes path\n\n" ++
  "/-- Markdown with compile-time link checking. Write content as `chars!\"...\"`. -/\n" ++
  "abbrev md (cs : List Char)\n" ++
  "    (h : (Markdown.parseChars cs).linksOk route? = true := by decide +kernel) :\n" ++
  "    List (Node Route .flow) :=\n  Markdown.md route? cs h\n\n" ++
  "/-- The stylesheet, in the typed CSS DSL. -/\ndef stylesheet : Css.Stylesheet :=\n  open Css in\n" ++
  "  [ rule .body [.fontFamily [.systemUi, .sansSerif], .lineHeight (.tenths 16),\n" ++
  "      .maxWidth (.rem 40), .margin .auto, .padding (.rem 1)],\n" ++
  "    rule (.desc (.tag .nav) (.ofTag .ul)) [.listStyle .none, .display .flex, .gap (.rem 1),\n" ++
  "      .padding .zero],\n" ++
  "    rule (.tag .a) [.color (.hex 0x0b 0x57 0xd0)],\n" ++
  "    rule (Selector.tag .a).hover [.textDecoration .underline] ]\n\n" ++
  "/-- Home page, in the HTML DSL. -/\ndef home : Page Route :=\n  { title := \"Home\"\n    body :=\n" ++
  s!"      [ p [] [\"Hello from \", strong [] [\"{name}\"], \". Edit \", code [] [\"{m}.lean\"],\n" ++
  "             \" to change this page.\"],\n" ++
  "        p [] [a [.href (.route .about)] [\"About this site\"]] ] }\n\n" ++
  "/-- About page, in Markdown. -/\ndef about : Page Route :=\n  { title := \"About\"\n" ++
  "    body := md chars!\"\nWritten in **Markdown**. Links like [home](/) are checked when this file compiles:\n" ++
  "point one at a route that does not exist and the build fails.\n\" }\n\n" ++
  s!"/-- The site. -/\ndef site : Site Route :=\n  \{ name := \"{name}\"\n    routes\n" ++
  "    routes_complete := by intro r; cases r <;> decide\n    path\n    urls_nodup := by decide\n" ++
  "    page := fun\n      | .home => home\n      | .about => about\n" ++
  "    nav := [(.home, \"Home\"), (.about, \"About\")]\n    stylesheet }\n\nend\n\n" ++
  s!"end {m}\n"

/-- `README.md` for a new site. -/
public def readme (name : String) : String :=
  s!"# {name}\n\nA site built with [sites](https://github.com/for-all-dev/sites), a verified static site\n" ++
  s!"generator in Lean 4.\n\n```sh\nlake build\n.lake/build/bin/{name} serve   # http://127.0.0.1:8080/\n" ++
  s!".lake/build/bin/{name} build   # writes dist/\n```\n\nEdit `{moduleName name}.lean`.\n"

/-- Writes the project. Refuses to overwrite an existing directory. -/
public def scaffold (name : String) (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then
    throw (IO.userError s!"{dir} already exists")
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "lakefile.toml") (lakefile name)
  IO.FS.writeFile (dir / "lean-toolchain") (toolchainLine ++ "\n")
  IO.FS.writeFile (dir / "Main.lean") (mainFile name)
  IO.FS.writeFile (dir / (moduleName name ++ ".lean")) (siteFile name)
  IO.FS.writeFile (dir / "README.md") (readme name)
  IO.FS.writeFile (dir / ".gitignore") "/.lake\n/dist\n"

/-- `new NAME [DIR]`: scaffolds a site project. -/
public def new (args : List String) : IO UInt32 := do
  let (name, dir) ← match args with
    | [name] => pure (name, (name : System.FilePath))
    | [name, dir] => pure (name, (dir : System.FilePath))
    | _ =>
      IO.eprintln "usage: sites new NAME [DIR]"
      return 1
  unless validName name do
    IO.eprintln s!"invalid name {name}: use lowercase letters, digits and dashes"
    return 1
  scaffold name dir
  IO.println s!"created {dir}/\n\n  cd {dir}\n  lake build\n  .lake/build/bin/{name} serve\n"
  return 0

end Sites.Cli
