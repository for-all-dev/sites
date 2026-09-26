import Sites
import Example

/-- Command-line usage. -/
def usage : String :=
  "usage: sites build [OUT_DIR]   write the site (default: dist)\n" ++
  "       sites serve [PORT]      serve it over HTTP (default: 8080)"

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["build"] => Example.site.build "dist"; IO.println "wrote dist/"; return 0
  | ["build", out] => Example.site.build out; IO.println s!"wrote {out}/"; return 0
  | ["serve"] => Example.site.serve 8080; return 0
  | ["serve", port] =>
    match port.toNat? with
    | some p => Example.site.serve p.toUInt16; return 0
    | none => IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
