import Sites
import Example

/-- `sites new NAME [DIR]` scaffolds a site; the other commands act on the example site. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "new" :: rest => Sites.Cli.new rest
  | _ => Sites.Cli.run Example.site args "sites"
