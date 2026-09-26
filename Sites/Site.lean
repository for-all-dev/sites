module
public import Sites.Html.Syntax
public import Sites.Html.Render
public import Sites.Html.Norm
public import Sites.Css

/-!
# Sites, routes and pages

A `Site ρ` is indexed by its route type `ρ`. Every internal link in the HTML is a value of `ρ`
(see `Sites.Html.Link.route`), so a dead internal link is a type error. The route table must
be complete (`routes_complete`) and produce distinct URLs (`urls_nodup`); both are discharged
by `decide` for enumerated route types.

From those two facts this module derives `RouteInverse` and `RouteSection` for the site's
`url`/`route?` pair, which is what the HTML round-trip theorem needs.
-/

namespace Sites

open Html

@[expose] public section

/-! ## URL path segments -/

/-- Characters allowed in a URL path segment: lowercase ASCII letters, digits and `-`. -/
def isSegmentChar (c : Char) : Bool :=
  c.isLower || c.isDigit || c = '-'

/-- A validated path segment. -/
structure Segment where
  /-- The segment text. -/
  name : String
  /-- Nonempty and made of `isSegmentChar` characters. -/
  valid : name.toList ≠ [] ∧ (name.toList.all isSegmentChar) = true
  deriving DecidableEq

instance : Repr Segment := ⟨fun s _ => repr s.name⟩

/-- Builds a segment; the proof is found by `decide` for literals. -/
def seg (s : String) (h : s.toList ≠ [] ∧ (s.toList.all isSegmentChar) = true := by decide) :
    Segment := ⟨s, h⟩

/-- A URL path: the root is `[]`, `/blog/hello/` is `[seg "blog", seg "hello"]`. -/
abbrev Path := List Segment

/-- The URL of a path as characters, always with a trailing slash: `/`, `/about/`,
`/blog/hello/`. Character lists rather than strings so that `decide` can compute with them. -/
def Path.urlChars (p : Path) : List Char :=
  '/' :: (p.map fun s => s.name.toList ++ ['/']).flatten

/-- The URL of a path. -/
def Path.url (p : Path) : String := String.ofList p.urlChars

/-- The output file for a path, as components: `["about", "index.html"]`. -/
def Path.file (p : Path) : List String :=
  p.map Segment.name ++ ["index.html"]

/-! ## Pages -/

/-- A page: metadata plus body content. The layout supplies the chrome. -/
structure Page (ρ : Type) where
  /-- Shown in `<title>` and used by the layout. -/
  title : String
  /-- `<meta name="description">`; empty means none. -/
  description : String := ""
  /-- The page body. -/
  body : List (Node ρ .flow)

/-- What a layout gets to work with. -/
structure LayoutInput (ρ : Type) where
  /-- The site name. -/
  siteName : String
  /-- Navigation entries: route and label. -/
  nav : List (ρ × String)
  /-- The route being rendered. -/
  route : ρ
  /-- The page being rendered. -/
  page : Page ρ
  /-- Where the stylesheet lives. -/
  stylesheet : Link ρ

/-- A layout turns a page into a full document. -/
abbrev Layout (ρ : Type) := LayoutInput ρ → Document ρ

/-- The default layout: header with navigation, main content, footer. -/
def defaultLayout {ρ : Type} : Layout ρ := fun input =>
  { lang := "en"
    head := Nodes.ofList <|
      [ «meta» [.charset "utf-8"],
        «meta» [.name "viewport", .content "width=device-width, initial-scale=1"],
        title (input.page.title ++ " · " ++ input.siteName),
        link [.rel "stylesheet", .href input.stylesheet] ] ++
      (if input.page.description = "" then []
       else [«meta» [.name "description", .content input.page.description]])
    body := Nodes.ofList
      [ header [.cls "site-header"]
          [ nav [.ariaLabel "Main"]
              [ ul [] (input.nav.map fun (r, label) =>
                  li [] [a [.href (.route r)] [text label]]) ] ],
        main [.cls "site-main"] (h1 [] [text input.page.title] :: input.page.body),
        footer [.cls "site-footer"] [small [] [text input.siteName]] ] }

/-! ## Sites -/

/-- A site over route type `ρ`. -/
structure Site (ρ : Type) [DecidableEq ρ] where
  /-- Human-readable name. -/
  name : String
  /-- Every route, in navigation order. -/
  routes : List ρ
  /-- The route table is complete. Prove with `by intro r; cases r <;> decide`. -/
  routes_complete : ∀ r, r ∈ routes
  /-- Where each route lives. -/
  path : ρ → Path
  /-- No two routes share a URL. Prove with `by decide`. -/
  urls_nodup : (routes.map fun r => (path r).urlChars).Nodup
  /-- The content of each route. -/
  page : ρ → Page ρ
  /-- Navigation entries. -/
  nav : List (ρ × String) := []
  /-- The stylesheet. -/
  stylesheet : Css.Stylesheet := []
  /-- The layout. -/
  layout : Layout ρ := defaultLayout

variable {ρ : Type} [DecidableEq ρ]

/-- The URL of a route. -/
def Site.url (site : Site ρ) (r : ρ) : String := (site.path r).url

/-- The route with a given URL, if any, from a route list and path function. Sites use this,
and page content can use it too (for Markdown link checks) before the site is assembled. -/
def routeOfChars (routes : List ρ) (path : ρ → Path) (cs : List Char) : Option ρ :=
  routes.find? fun r => (path r).urlChars == cs

/-- `routeOfChars` on a string. -/
def routeOf (routes : List ρ) (path : ρ → Path) (s : String) : Option ρ :=
  routeOfChars routes path s.toList

/-- The route with a given URL, if any. -/
def Site.route? (site : Site ρ) (s : String) : Option ρ :=
  routeOf site.routes site.path s

/-- Where the stylesheet is served. This is never a route URL because route URLs end in `/`. -/
def stylesheetUrl : String := "/style.css"

/-- The file for the stylesheet. -/
def stylesheetFile : List String := ["style.css"]

/-- The full document for a route (before normalisation). -/
def Site.document (site : Site ρ) (r : ρ) : Document ρ :=
  site.layout
    { siteName := site.name, nav := site.nav, route := r, page := site.page r,
      stylesheet := .url stylesheetUrl }

/-- The HTML written for a route: the normalised document, rendered. -/
def Site.html (site : Site ρ) (r : ρ) : String :=
  ((site.document r).norm site.route?).toString site.url

/-- Every file the site produces, as `(path components, content)`. -/
def Site.files (site : Site ρ) : List (List String × String) :=
  (stylesheetFile, site.stylesheet.render) ::
    site.routes.map fun r => ((site.path r).file, site.html r)

end

variable {ρ : Type} [DecidableEq ρ]

/-! ## Route lemmas -/

theorem List.eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hf : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hf.symm⟩ h.1
    · exact absurd ⟨a, ha, hf⟩ h.1
    · exact ih h.2 ha hb

/-- `route?` only returns routes whose URL is the query. -/
public theorem Site.routeInverse (site : Site ρ) : RouteInverse site.route? site.url := by
  intro s r h
  unfold Site.route? routeOf routeOfChars at h
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  simp [Site.url, Path.url, this]

/-- Every route's URL resolves to that route. -/
public theorem Site.routeSection (site : Site ρ) : RouteSection site.route? site.url := by
  intro r
  have hmem := site.routes_complete r
  unfold Site.route? routeOf routeOfChars
  simp only [Site.url, Path.url, String.toList_ofList]
  have hex : ∃ x, site.routes.find? (fun x => (site.path x).urlChars == (site.path r).urlChars) =
      some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨r, hmem, by simp⟩
  obtain ⟨x, hx⟩ := hex
  have hxmem : x ∈ site.routes := List.mem_of_find?_eq_some hx
  have hurl : (site.path x).urlChars = (site.path r).urlChars := by
    have := List.find?_some hx
    simpa using this
  rw [hx]
  congr
  exact List.eq_of_nodup_map site.urls_nodup hxmem hmem hurl

/-- **Every page round-trips.** Parsing the HTML the site writes for a route gives back the
route's normalised document. -/
public theorem Site.parse_html (site : Site ρ) (r : ρ) :
    parseDocument site.route? (site.html r).toList =
      some ((site.document r).norm site.route?) := by
  unfold Site.html Document.toString
  rw [String.toList_ofList]
  exact parseDocument_render _ _ _ (Document.norm_canonical site.routeSection _)

end Sites
