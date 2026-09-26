module
public meta import Sites
public meta import Example
import Sites
import Example

/-!
# Tests and audit

`#guard` lines run the compiled code on concrete inputs. `#guard_msgs` lines pin the axioms
each headline theorem depends on: exactly the three standard axioms of Lean's logic and no
`sorryAx`. `lake build Test` fails if either kind of check breaks.
-/

open Sites Sites.Html

/-! ## Escaping -/

#guard escape "a<b&c\"d>e".toList = "a&lt;b&amp;c&quot;d&gt;e".toList
#guard unescape (escape "x<y&z".toList) = some "x<y&z".toList
#guard unescape "<".toList = none

/-! ## Rendering and parsing, executed on the example site -/

#guard Example.routes.all fun r =>
  (parseDocument Example.site.route? (Example.site.html r).toList).isSome

#guard (Example.site.html .home).startsWith "<!DOCTYPE html><html lang=\"en\"><head>"

#guard Example.site.url .blogHello = "/blog/hello-world/"
#guard Example.site.route? "/blog/hello-world/" = some .blogHello
#guard Example.site.route? "/nope/" = none

/-! ## CSS -/

#guard (Css.Stylesheet.render Example.stylesheet).startsWith "*{box-sizing:border-box;}"
#guard (Css.Decimal.render (Css.Decimal.tenths 15)) = "1.5".toList
#guard (Css.Decimal.render ⟨-25, 2⟩) = "-0.25".toList
#guard (Css.Length.render (.rem 2)) = "2rem".toList
#guard (Css.Color.render (.hex 0x0b 0x57 0xd0)) = "#0b57d0".toList

/-! ## Markdown -/

#guard (Markdown.parse "# Hi\n\nSome *em* and **strong** text.\n").length = 2
#guard (Markdown.parse "- a\n- b\n").length = 1
#guard (Markdown.parse "[x](/about/) and [y](/nope/)").links = ["/about/".toList, "/nope/".toList]
#guard (Markdown.parse "[x](/about/)").linksOk Example.route? = true
#guard (Markdown.parse "[y](/nope/)").linksOk Example.route? = false
#guard (Markdown.parse "[ext](https://lean-lang.org)").linksOk Example.route? = true

/-! ## Axiom audit -/

/-- info: 'Sites.Html.parseDocument_render' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.Html.parseDocument_render

/-- info: 'Sites.Html.parseDocument_render_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.Html.parseDocument_render_norm

/-- info: 'Sites.Site.parse_html' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.Site.parse_html

/-- info: 'Sites.Css.Stylesheet.render_grammar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.Css.Stylesheet.render_grammar

/-- info: 'Sites.writeAllModel.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.writeAllModel.spec

/-- info: 'Sites.Site.build_pages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sites.Site.build_pages

/-- info: 'Example.site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Example.site

/-! ## Negative cases, at the type level

Misplaced elements are rejected because no `Fits` witness exists; a dead Markdown link makes
`linksOk` false, which the `decide +kernel` proof in `md` then refuses. -/

example : Fits Tag.p.ctx Tag.ul.childCtx → False := fun h => nomatch h
example : Fits Tag.li.ctx Ctx.flow → False := fun h => nomatch h
example : Fits Tag.td.ctx Tag.ul.childCtx → False := fun h => nomatch h
#guard (Markdown.parseChars chars!"See [this](/nope/).").linksOk Example.route? = false
#guard (Markdown.parseChars chars!"See [this](/blog/hello-world/).").linksOk Example.route? = true

/-! ## Scaffolder helpers -/

#guard Sites.Cli.moduleName "my-site" = "MySite"
#guard Sites.Cli.moduleName "blog" = "Blog"
#guard Sites.Cli.validName "my-site-2" = true
#guard Sites.Cli.validName "My Site" = false
#guard Sites.Cli.validName "" = false
#guard Sites.Cli.toolchainLine.startsWith "leanprover/lean4"

/-! ## Inline SVG

`a` names two tags; lookup is by category. A document with an SVG map inside round-trips. -/

#guard Tag.ofNameIn? .svg "a" = some .svgA
#guard Tag.ofNameIn? .flow "a" = some .a
#guard Tag.ofNameIn? .phrasing "a" = some .a
#guard Tag.ofNameIn? .svg "circle" = some .circle

/-- A small map: one category circle, one linked organisation dot with its label. -/
def svgDoc : Document Example.Route :=
  { head := Nodes.ofList [title "svg"]
    body := Nodes.ofList
      [ div [.cls "map"]
          [ svg [.viewBox "0 0 100 100"]
              [ circle [.cls "circle", .cx "50", .cy "50", .r "40", .fill "#6366f1"],
                svgText [.x "50", .y "5"] ["Mathematics"],
                svgA [.href (.url "https://axiommath.ai/"), .target "_blank"]
                  [ circle [.cx "50", .cy "50", .r "5"], svgText [.x "50", .y "70"] ["Axiom"] ] ] ] ] }

#guard (svgDoc.toString Example.site.url).endsWith
  "<a href=\"https://axiommath.ai/\" target=\"_blank\"><circle cx=\"50\" cy=\"50\" r=\"5\"></circle><text x=\"50\" y=\"70\">Axiom</text></a></svg></div></body></html>"
#guard (parseDocument Example.site.route? (svgDoc.toString Example.site.url).toList).isSome

/-- Text is not SVG content, and an SVG `a` is not phrasing content. -/
example : Fits Tag.svgA.ctx Ctx.flow → False := fun h => nomatch h
example : TextCtx Ctx.svg → False := fun ⟨h⟩ => nomatch h
