module
public import Std.Http
public import Sites.Site
public import Sites.Build

/-!
# Development server

Serves the site from memory over plain HTTP/1.1 using the asynchronous server in `Std.Http`.
Nothing is written to disk; every request renders the page from the same `Site` value the
build uses, so what you see is what `build` writes.

There is no TLS: the standard library has none, and linking OpenSSL would put unverified C
under a verified generator. Put a reverse proxy in front if you need HTTPS.
-/

namespace Sites

open Std Std.Http Std.Async

variable {ρ : Type} [DecidableEq ρ]

/-- The 404 page, built with the typed DSL like everything else. -/
public def notFoundDoc : Html.Document ρ :=
  { head := .ofList [Html.«meta» [.charset "utf-8"], Html.title "Not found"]
    body := .ofList [Html.h1 [] [Html.text "404 Not Found"]] }

/-- What to serve for a request path: `(content, content type)`. -/
public def Site.lookup (site : Site ρ) (path : String) : Option (String × String) :=
  if path = stylesheetUrl then some (site.stylesheet.render, "text/css; charset=utf-8")
  else
    let p := if path.endsWith "/" then path else path ++ "/"
    match site.route? p with
    | some r => some (site.html r, "text/html; charset=utf-8")
    | none => none

/-- Handles one request. -/
public def Site.respond (site : Site ρ) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let target := toString req.line.uri
  let path := (target.splitOn "?").headD "/"
  let (builder, content, ctype) :=
    match site.lookup path with
    | some (c, t) => (Response.ok, c, t)
    | none =>
      (Response.notFound, (notFoundDoc (ρ := ρ)).toString site.url, "text/html; charset=utf-8")
  let resp ← (builder.header! "Content-Type" ctype).fromBytes content.toUTF8
  return { resp with body := .ofBody resp.body }

/-- Serves the site on `127.0.0.1:port` until the process is stopped. -/
public def Site.serve (site : Site ρ) (port : UInt16) : IO Unit := do
  IO.println s!"Serving {site.name} at http://127.0.0.1:{port}/"
  Async.block do
    let server ← Server.serve (.v4 { addr := .ofParts 127 0 0 1, port })
      (Server.Handler.ofFn site.respond)
    server.waitShutdown

end Sites
