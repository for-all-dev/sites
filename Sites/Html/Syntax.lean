module

/-!
# Typed HTML syntax

The document tree is an inductive family indexed by a *content category* (`Ctx`). Each tag
lives in exactly one category and accepts children of exactly one category, so ill-nested
markup (a `li` outside a list, a `p` inside a `span`, text inside a `ul`) is a type error.

Links are typed by the site's route type `ρ`: `Link.route r` can only be built from a real
route, which is how "no dead internal links" is enforced (see `Sites.Site`).

Every constructor that fixes its category carries an equation proof (`h : c = .phrasing`)
instead of targeting a specific index. That keeps pattern matching on `Node ρ c` total for
arbitrary `c`, which the renderer, parser and proofs all rely on. The smart constructors at
the end of this file supply those proofs with `rfl`.
-/

namespace Sites.Html

@[expose] public section

/-- HTML content categories, simplified from the WHATWG content model. -/
inductive Ctx where
  /-- Block-level content: children of `body`, `div`, `li`, `blockquote`, ... -/
  | flow
  /-- Inline content: text, `em`, `a`, `code`, ... and children of `p`, `h1`, ... -/
  | phrasing
  /-- Children of `ul` and `ol`: only `li`. -/
  | listItem
  /-- Children of `table`: only `tr`. -/
  | tableRow
  /-- Children of `tr`: only `td` and `th`. -/
  | tableCell
  /-- Children of `head`: `title`, `meta`, `link`. -/
  | head
  /-- Children of inline `svg`, `g` and SVG `a`: shapes, text, groups and links. -/
  | svg
  deriving DecidableEq, Repr

set_option linter.missingDocs false in
/-- Non-void tags. SVG elements are never void: in an HTML document a `<circle>` without a
closing tag would swallow its siblings, so they are rendered with explicit closing tags.
`svgText` and `svgA` are SVG's `text` and `a`; the latter shares its name with HTML's `a`, which
is why `Tag.ofNameIn?` takes the surrounding category. -/
inductive Tag where
  | div | «section» | article | nav | header | footer | main | aside | blockquote
  | figure | figcaption | iframe
  | p | h1 | h2 | h3 | h4 | h5 | h6 | pre
  | ul | ol | table
  | span | a | em | strong | code | b | i | small | kbd | sup | sub | mark
  | li | tr | td | th
  | svg | g | circle | svgText | svgA
  deriving DecidableEq, Repr

set_option linter.missingDocs false in
/-- Void tags: no children and no closing tag. -/
inductive VoidTag where
  | br | hr | img | «meta» | link
  deriving DecidableEq, Repr

/-- The category a tag belongs to. -/
abbrev Tag.ctx : Tag → Ctx
  | .li => .listItem
  | .tr => .tableRow
  | .td | .th => .tableCell
  | .span | .a | .em | .strong | .code | .b | .i | .small | .kbd | .sup | .sub | .mark => .phrasing
  | .g | .circle | .svgText | .svgA => .svg
  | _ => .flow

/-- The category of a tag's children. -/
abbrev Tag.childCtx : Tag → Ctx
  | .p | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .pre | .iframe => .phrasing
  | .ul | .ol => .listItem
  | .table => .tableRow
  | .tr => .tableCell
  | .span | .a | .em | .strong | .code | .b | .i | .small | .kbd | .sup | .sub | .mark => .phrasing
  | .svg | .g | .circle | .svgA => .svg
  | .svgText => .phrasing
  | _ => .flow

/-- The category a void tag belongs to. -/
abbrev VoidTag.ctx : VoidTag → Ctx
  | .br | .img => .phrasing
  | .hr => .flow
  | .«meta» | .link => .head

/-- The tag's name as it appears in markup. -/
def Tag.name : Tag → String
  | .div => "div" | .«section» => "section" | .article => "article" | .nav => "nav"
  | .header => "header" | .footer => "footer" | .main => "main" | .aside => "aside"
  | .blockquote => "blockquote" | .figure => "figure" | .figcaption => "figcaption"
  | .iframe => "iframe"
  | .p => "p" | .h1 => "h1" | .h2 => "h2" | .h3 => "h3" | .h4 => "h4" | .h5 => "h5" | .h6 => "h6"
  | .pre => "pre" | .ul => "ul" | .ol => "ol" | .table => "table"
  | .span => "span" | .a => "a" | .em => "em" | .strong => "strong" | .code => "code"
  | .b => "b" | .i => "i" | .small => "small" | .kbd => "kbd" | .sup => "sup" | .sub => "sub"
  | .mark => "mark"
  | .li => "li" | .tr => "tr" | .td => "td" | .th => "th"
  | .svg => "svg" | .g => "g" | .circle => "circle" | .svgText => "text" | .svgA => "a"

/-- Inverse of `Tag.name` outside SVG content (where `a` is HTML's `a`). -/
def Tag.ofName? : String → Option Tag
  | "div" => some .div | "section" => some .«section» | "article" => some .article
  | "nav" => some .nav | "header" => some .header | "footer" => some .footer
  | "main" => some .main | "aside" => some .aside | "blockquote" => some .blockquote
  | "figure" => some .figure | "figcaption" => some .figcaption | "iframe" => some .iframe
  | "p" => some .p | "h1" => some .h1 | "h2" => some .h2 | "h3" => some .h3
  | "h4" => some .h4 | "h5" => some .h5 | "h6" => some .h6 | "pre" => some .pre
  | "ul" => some .ul | "ol" => some .ol | "table" => some .table
  | "span" => some .span | "a" => some .a | "em" => some .em | "strong" => some .strong
  | "code" => some .code | "b" => some .b | "i" => some .i | "small" => some .small
  | "kbd" => some .kbd | "sup" => some .sup | "sub" => some .sub | "mark" => some .mark
  | "li" => some .li | "tr" => some .tr | "td" => some .td | "th" => some .th
  | "svg" => some .svg | "g" => some .g | "circle" => some .circle | "text" => some .svgText
  | _ => none

/-- Inverse of `Tag.name` in category `c`: the tag named `s` that can be placed in `c`. Only
`a` depends on the category, since HTML and SVG both have one. -/
def Tag.ofNameIn? (c : Ctx) (s : String) : Option Tag :=
  if c = .svg ∧ s = "a" then some .svgA else Tag.ofName? s

/-- The void tag's name as it appears in markup. -/
def VoidTag.name : VoidTag → String
  | .br => "br" | .hr => "hr" | .img => "img" | .«meta» => "meta" | .link => "link"

/-- Inverse of `VoidTag.name`. -/
def VoidTag.ofName? : String → Option VoidTag
  | "br" => some .br | "hr" => some .hr | "img" => some .img | "meta" => some .«meta»
  | "link" => some .link
  | _ => none

/-- Characters allowed in tag and attribute names. -/
def isNameChar (c : Char) : Bool :=
  c.isLower || c.isDigit || c = '-'

/-- A link target: either a route of the site (checked) or an arbitrary URL (unchecked). -/
inductive Link (ρ : Type) where
  /-- An internal link. It can only be built from a value of the route type. -/
  | route (r : ρ)
  /-- Any other URL: external, `mailto:`, fragment, ... -/
  | url (s : String)
  deriving Repr

set_option linter.missingDocs false in
/-- Attributes. Every value is a string except `href`, which is a typed link. -/
inductive Attr (ρ : Type) where
  | id (v : String)
  | cls (v : String)
  | href (l : Link ρ)
  | src (v : String)
  | alt (v : String)
  | title (v : String)
  | lang (v : String)
  | rel (v : String)
  | type (v : String)
  | name (v : String)
  | content (v : String)
  | charset (v : String)
  | role (v : String)
  | ariaLabel (v : String)
  | target (v : String)
  | width (v : String)
  | height (v : String)
  | loading (v : String)
  | crossorigin (v : String)
  /-- SVG `viewBox`. Emitted lowercase, as attribute names here are; the HTML parser's
  SVG attribute adjustment restores the case. -/
  | viewBox (v : String)
  | cx (v : String)
  | cy (v : String)
  | r (v : String)
  | x (v : String)
  | y (v : String)
  | fill (v : String)
  | stroke (v : String)
  deriving Repr

/-- The attribute's name as it appears in markup. -/
def Attr.key {ρ : Type} : Attr ρ → String
  | .id _ => "id" | .cls _ => "class" | .href _ => "href" | .src _ => "src" | .alt _ => "alt"
  | .title _ => "title" | .lang _ => "lang" | .rel _ => "rel" | .type _ => "type"
  | .name _ => "name" | .content _ => "content" | .charset _ => "charset" | .role _ => "role"
  | .ariaLabel _ => "aria-label" | .target _ => "target" | .width _ => "width"
  | .height _ => "height" | .loading _ => "loading" | .crossorigin _ => "crossorigin"
  | .viewBox _ => "viewbox" | .cx _ => "cx" | .cy _ => "cy" | .r _ => "r" | .x _ => "x"
  | .y _ => "y" | .fill _ => "fill" | .stroke _ => "stroke"

/-- Rebuilds an attribute from its key and (already unescaped) value.
`route?` resolves internal links; when it fails the value becomes a plain `Link.url`. -/
def Attr.ofKey? {ρ : Type} (route? : String → Option ρ) (key value : String) :
    Option (Attr ρ) :=
  match key with
  | "id" => some (.id value) | "class" => some (.cls value)
  | "href" => some (.href (match route? value with | some rt => .route rt | none => .url value))
  | "src" => some (.src value) | "alt" => some (.alt value) | "title" => some (.title value)
  | "lang" => some (.lang value) | "rel" => some (.rel value) | "type" => some (.type value)
  | "name" => some (.name value) | "content" => some (.content value)
  | "charset" => some (.charset value) | "role" => some (.role value)
  | "aria-label" => some (.ariaLabel value) | "target" => some (.target value)
  | "width" => some (.width value) | "height" => some (.height value)
  | "loading" => some (.loading value) | "crossorigin" => some (.crossorigin value)
  | "viewbox" => some (.viewBox value) | "cx" => some (.cx value) | "cy" => some (.cy value)
  | "r" => some (.r value) | "x" => some (.x value) | "y" => some (.y value)
  | "fill" => some (.fill value) | "stroke" => some (.stroke value)
  | _ => none

mutual
  /-- A node in category `c`. -/
  inductive Node (ρ : Type) : Ctx → Type where
    /-- A text node. Only phrasing content may contain raw text. -/
    | text {c : Ctx} (h : c = .phrasing) (s : String) : Node ρ c
    /-- Phrasing content is also flow content. -/
    | inline {c : Ctx} (h : c = .flow) (n : Node ρ .phrasing) : Node ρ c
    /-- An element. Its children live in the tag's child category. -/
    | el {c : Ctx} (t : Tag) (h : t.ctx = c) (attrs : List (Attr ρ)) (children : Nodes ρ t.childCtx) :
        Node ρ c
    /-- A void element. -/
    | void {c : Ctx} (t : VoidTag) (h : t.ctx = c) (attrs : List (Attr ρ)) : Node ρ c
    /-- The document title; only text, only in `head`. -/
    | title {c : Ctx} (h : c = .head) (s : String) : Node ρ c
  /-- A sequence of nodes in category `c`. -/
  inductive Nodes (ρ : Type) : Ctx → Type where
    /-- The empty sequence. -/
    | nil {c : Ctx} : Nodes ρ c
    /-- Prepends a node. -/
    | cons {c : Ctx} (n : Node ρ c) (ns : Nodes ρ c) : Nodes ρ c
end

/-- A whole HTML document. -/
structure Document (ρ : Type) where
  /-- The `lang` attribute of the root element. -/
  lang : String := "en"
  /-- Children of `<head>`. -/
  head : Nodes ρ .head
  /-- Children of `<body>`. -/
  body : Nodes ρ .flow

variable {ρ : Type}

/-- Converts a list of nodes into a `Nodes` sequence. -/
def Nodes.ofList {c : Ctx} : List (Node ρ c) → Nodes ρ c
  | [] => .nil
  | n :: ns => .cons n (Nodes.ofList ns)

/-- Converts a `Nodes` sequence into a list. -/
def Nodes.toList {c : Ctx} : Nodes ρ c → List (Node ρ c)
  | .nil => []
  | .cons n ns => n :: ns.toList

/-- Appends two sequences. -/
def Nodes.append {c : Ctx} : Nodes ρ c → Nodes ρ c → Nodes ρ c
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

instance {c : Ctx} : Append (Nodes ρ c) := ⟨Nodes.append⟩

/-! ## Smart constructors

These are what site code uses. Each element constructor is polymorphic in the category it is
placed in: `em [] ["x"]` is phrasing content inside a `p` and flow content inside a `li`. The
placement witness `Fits` is found by a default tactic, so a misplaced element is a type error
at the use site with no proof to write. -/

/-- Evidence that content of category `a` may be placed where category `b` is expected:
either the same category, or phrasing content used as flow content. -/
inductive Fits : Ctx → Ctx → Type where
  /-- Same category. -/
  | refl (c : Ctx) : Fits c c
  /-- Phrasing content is flow content. -/
  | phrasingFlow : Fits .phrasing .flow

/-- Finds the placement witness. -/
macro "fits" : tactic => `(tactic| first | exact Fits.refl _ | exact Fits.phrasingFlow)

/-- Places a node according to a `Fits` witness. -/
def Node.place {a b : Ctx} : Fits a b → Node ρ a → Node ρ b
  | .refl _, n => n
  | .phrasingFlow, n => .inline rfl n

/-- Categories that may contain text. -/
class TextCtx (c : Ctx) where
  /-- The witness. -/
  fits : Fits .phrasing c

instance : TextCtx .phrasing := ⟨.refl _⟩
instance : TextCtx .flow := ⟨.phrasingFlow⟩

/-- A text node, placed where text is allowed. -/
def text {c : Ctx} [TextCtx c] (s : String) : Node ρ c := Node.place TextCtx.fits (.text rfl s)

instance {c : Ctx} [TextCtx c] : Coe String (Node ρ c) := ⟨text⟩

/-- The document title. -/
def title (s : String) : Node ρ .head := .title rfl s

/-- Builds an element from a list of children and places it. -/
def el {c : Ctx} (t : Tag) (attrs : List (Attr ρ) := []) (children : List (Node ρ t.childCtx) := [])
    (h : Fits t.ctx c := by fits) : Node ρ c :=
  Node.place h (.el t rfl attrs (Nodes.ofList children))

/-- Builds a void element and places it. -/
def void {c : Ctx} (t : VoidTag) (attrs : List (Attr ρ) := []) (h : Fits t.ctx c := by fits) :
    Node ρ c :=
  Node.place h (.void t rfl attrs)

/-- Elements are named after their tags: `div`, `p`, `h1`, ... -/
macro "def_el" name:ident tag:ident : command =>
  `(/-- Element constructor. -/
    def $name {c : Ctx} (attrs : List (Attr ρ) := [])
        (children : List (Node ρ (Tag.childCtx $tag)) := [])
        (h : Fits (Tag.ctx $tag) c := by fits) : Node ρ c :=
      el $tag attrs children h)

def_el div Tag.div
def_el «section» Tag.«section»
def_el article Tag.article
def_el nav Tag.nav
def_el header Tag.header
def_el footer Tag.footer
def_el main Tag.main
def_el aside Tag.aside
def_el blockquote Tag.blockquote
def_el figure Tag.figure
def_el figcaption Tag.figcaption
def_el p Tag.p
def_el h1 Tag.h1
def_el h2 Tag.h2
def_el h3 Tag.h3
def_el h4 Tag.h4
def_el h5 Tag.h5
def_el h6 Tag.h6
def_el pre Tag.pre
def_el ul Tag.ul
def_el ol Tag.ol
def_el table Tag.table
def_el span Tag.span
def_el a Tag.a
def_el em Tag.em
def_el strong Tag.strong
def_el code Tag.code
def_el b Tag.b
def_el i Tag.i
def_el small Tag.small
def_el kbd Tag.kbd
def_el sup Tag.sup
def_el sub Tag.sub
def_el mark Tag.mark
def_el li Tag.li
def_el tr Tag.tr
def_el td Tag.td
def_el th Tag.th
def_el iframe Tag.iframe
def_el svg Tag.svg
def_el svgGroup Tag.g
def_el circle Tag.circle
def_el svgText Tag.svgText
def_el svgA Tag.svgA

/-- `<br>` -/
def br {c : Ctx} (h : Fits .phrasing c := by fits) : Node ρ c := void .br [] h
/-- `<hr>` -/
def hr (attrs : List (Attr ρ) := []) : Node ρ .flow := void .hr attrs
/-- `<img>` -/
def img {c : Ctx} (attrs : List (Attr ρ) := []) (h : Fits .phrasing c := by fits) : Node ρ c :=
  void .img attrs h
/-- `<meta>` -/
def «meta» (attrs : List (Attr ρ) := []) : Node ρ .head := void .«meta» attrs
/-- Evidence that a tag may be placed in category `c`: its own category, or phrasing content
placed as flow content. This is exactly what `Fits` witnesses. -/
def Tag.PlacesIn (t : Tag) (c : Ctx) : Prop := t.ctx = c ∨ (t.ctx = .phrasing ∧ c = .flow)

/-- `<link>` -/
def link (attrs : List (Attr ρ) := []) : Node ρ .head := void .link attrs

end

/-! ## Name lemmas -/

/-- Looking a tag's name up in any category it can be placed in gives the tag back. -/
public theorem Tag.ofNameIn?_name (t : Tag) (c : Ctx) (h : t.PlacesIn c) :
    Tag.ofNameIn? c t.name = some t := by
  revert h; unfold Tag.PlacesIn; cases t <;> cases c <;> decide

public theorem VoidTag.ofName?_name (t : VoidTag) : VoidTag.ofName? t.name = some t := by
  cases t <;> rfl

/-- Void and non-void tag names are disjoint. -/
public theorem Tag.ofNameIn?_voidName (t : VoidTag) (c : Ctx) : Tag.ofNameIn? c t.name = none := by
  cases t <;> cases c <;> rfl

public theorem Tag.ofNameIn?_title (c : Ctx) : Tag.ofNameIn? c "title" = none := by
  cases c <;> rfl
public theorem VoidTag.ofName?_title : VoidTag.ofName? "title" = none := rfl

public theorem Tag.name_chars (t : Tag) : ∀ c ∈ t.name.toList, isNameChar c = true := by
  cases t <;> decide

public theorem VoidTag.name_chars (t : VoidTag) : ∀ c ∈ t.name.toList, isNameChar c = true := by
  cases t <;> decide

public theorem Attr.key_chars {ρ : Type} (a : Attr ρ) : ∀ c ∈ a.key.toList, isNameChar c = true := by
  cases a <;> simp only [Attr.key] <;> decide

public theorem isNameChar_space : isNameChar ' ' = false := by decide
public theorem isNameChar_gt : isNameChar '>' = false := by decide
public theorem isNameChar_eq : isNameChar '=' = false := by decide
public theorem isNameChar_slash : isNameChar '/' = false := by decide

public theorem Nodes.toList_ofList {ρ : Type} {c : Ctx} (l : List (Node ρ c)) :
    (Nodes.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons n ns ih => simp [Nodes.ofList, Nodes.toList, ih]


/-! ## Mutual induction -/

/-- Simultaneous induction over `Node` and `Nodes`. -/
public theorem Node.induction {ρ : Type}
    {motive_1 : (c : Ctx) → Node ρ c → Prop} {motive_2 : (c : Ctx) → Nodes ρ c → Prop}
    (text : ∀ {c : Ctx} (h : c = .phrasing) (s : String), motive_1 c (.text h s))
    (inline : ∀ {c : Ctx} (h : c = .flow) (n : Node ρ .phrasing),
      motive_1 .phrasing n → motive_1 c (.inline h n))
    (el : ∀ {c : Ctx} (t : Tag) (h : t.ctx = c) (attrs : List (Attr ρ))
      (children : Nodes ρ t.childCtx), motive_2 t.childCtx children →
      motive_1 c (.el t h attrs children))
    (void : ∀ {c : Ctx} (t : VoidTag) (h : t.ctx = c) (attrs : List (Attr ρ)),
      motive_1 c (.void t h attrs))
    (title : ∀ {c : Ctx} (h : c = .head) (s : String), motive_1 c (.title h s))
    (nil : ∀ {c : Ctx}, motive_2 c .nil)
    (cons : ∀ {c : Ctx} (n : Node ρ c) (ns : Nodes ρ c),
      motive_1 c n → motive_2 c ns → motive_2 c (.cons n ns)) :
    (∀ {c : Ctx} (n : Node ρ c), motive_1 c n) ∧ (∀ {c : Ctx} (ns : Nodes ρ c), motive_2 c ns) :=
  ⟨fun n => Node.rec text inline el void title nil cons n,
   fun ns => Nodes.rec text inline el void title nil cons ns⟩

end Sites.Html
