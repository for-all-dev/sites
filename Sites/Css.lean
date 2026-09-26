module
public import Sites.Html.Syntax

/-!
# Typed CSS

A small typed subset of CSS: lengths carry units, colours are structured, selectors are
trees, and properties only accept values of the right type. `Stylesheet.render` prints it, and
`render_grammar` proves the output is derivable in the token-level grammar `Css.Grammar`,
a simplification of CSS Syntax Module Level 3 restricted to what this printer emits.

Identifiers (class names, ids) are validated at construction time with a `decide` proof, so
`Selector.cls "my-class"` type-checks and `Selector.cls "my class"` does not.
-/

namespace Sites.Css

-- The keyword enumerations below are self-describing.
set_option linter.missingDocs false

@[expose] public section

/-! ## Characters and identifiers -/

/-- Characters allowed anywhere in a CSS identifier. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c = '-' || c = '_'

/-- A validated CSS identifier. -/
def IsIdent (s : String) : Prop :=
  s.toList ≠ [] ∧ (s.toList.all isIdentChar) = true ∧ (s.toList.head?.all fun c => !c.isDigit) = true

instance (s : String) : Decidable (IsIdent s) := by unfold IsIdent; infer_instance

/-- A CSS identifier with its validity proof. -/
structure Ident where
  /-- The identifier text. -/
  name : String
  /-- Validity: nonempty, identifier characters only, no leading digit. -/
  valid : IsIdent name

instance : Repr Ident := ⟨fun i _ => repr i.name⟩

/-- Builds an identifier; the proof is found by `decide` for literals. -/
def ident (s : String) (h : IsIdent s := by decide) : Ident := ⟨s, h⟩

/-! ## Numbers -/

/-- A decimal number `mantissa / 10^scale`, e.g. `1.5 = ⟨15, 1⟩`, `-0.25 = ⟨-25, 2⟩`. -/
structure Decimal where
  /-- Signed mantissa. -/
  mantissa : Int
  /-- Digits after the decimal point. -/
  scale : Nat := 0
  deriving Repr, DecidableEq

instance (n : Nat) : OfNat Decimal n := ⟨⟨n, 0⟩⟩

/-- `d.tenths 15 = 1.5` -/
def Decimal.tenths (n : Int) : Decimal := ⟨n, 1⟩
/-- `d.hundredths 125 = 1.25` -/
def Decimal.hundredths (n : Int) : Decimal := ⟨n, 2⟩

/-- The digit character for `d % 10`. -/
def digitChar (d : Nat) : Char :=
  match d % 10 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- Decimal digits of a natural number, most significant first. -/
def natDigits (n : Nat) : List Char :=
  if h : n < 10 then [digitChar n]
  else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

/-- Exactly `k` digits, zero-padded on the left. -/
def natDigitsPad (k : Nat) (n : Nat) : List Char :=
  match k with
  | 0 => []
  | k + 1 => natDigitsPad k (n / 10) ++ [digitChar (n % 10)]

/-- Renders a decimal: `-12.50`. -/
def Decimal.render (d : Decimal) : List Char :=
  let sign : List Char := if d.mantissa < 0 then ['-'] else []
  let m := d.mantissa.natAbs
  let intPart := natDigits (m / 10 ^ d.scale)
  let fracPart := if d.scale = 0 then [] else '.' :: natDigitsPad d.scale (m % 10 ^ d.scale)
  sign ++ intPart ++ fracPart

/-! ## Values -/

/-- Lengths with units, plus the `auto` keyword where a length is expected. -/
inductive Length where
  | px (v : Decimal) | rem (v : Decimal) | em (v : Decimal) | pct (v : Decimal)
  | vw (v : Decimal) | vh (v : Decimal)
  /-- Unitless zero. -/
  | zero
  /-- The `auto` keyword. -/
  | auto
  deriving Repr

/-- Named colours (a useful subset). -/
inductive NamedColor where
  | black | white | red | green | blue | gray | silver | transparent | currentColor | inherit
  deriving Repr

/-- Colours. -/
inductive Color where
  /-- `#rrggbb` -/
  | hex (r g b : UInt8)
  /-- `rgba(r, g, b, a)` -/
  | rgba (r g b : UInt8) (a : Decimal)
  | named (n : NamedColor)
  deriving Repr

/-- `display` values. -/
inductive Display where
  | block | inline | inlineBlock | flex | grid | none
  deriving Repr

/-- `flex-direction` values. -/
inductive FlexDirection where
  | row | column | rowReverse | columnReverse
  deriving Repr

/-- `justify-content` / `align-items` values. -/
inductive Align where
  | flexStart | flexEnd | center | spaceBetween | spaceAround | stretch | baseline
  deriving Repr

/-- `text-align` values. -/
inductive TextAlign where
  | left | right | center | justify
  deriving Repr

/-- `font-weight` values. -/
inductive FontWeight where
  | normal | bold | w100 | w200 | w300 | w400 | w500 | w600 | w700 | w800 | w900
  deriving Repr

/-- `border-style` values. -/
inductive BorderStyle where
  | none | solid | dashed | dotted | double
  deriving Repr

/-- `text-decoration` values. -/
inductive TextDecoration where
  | none | underline | lineThrough
  deriving Repr

/-- `white-space` values. -/
inductive WhiteSpace where
  | normal | nowrap | pre | preWrap
  deriving Repr

/-- `overflow` values. -/
inductive Overflow where
  | visible | hidden | scroll | auto
  deriving Repr

/-- `text-transform` values. -/
inductive TextTransform where
  | none | uppercase | lowercase | capitalize
  deriving Repr

/-- `box-sizing` values. -/
inductive BoxSizing where
  | contentBox | borderBox
  deriving Repr

/-- `cursor` values. -/
inductive Cursor where
  | auto | pointer | default | text
  deriving Repr

/-- `list-style` values. -/
inductive ListStyle where
  | none | disc | decimal | circle | square
  deriving Repr

/-- A side, for `margin-top` and friends. -/
inductive Side where
  | top | right | bottom | left
  deriving Repr

/-- A font family: a quoted family name or a generic keyword. -/
inductive FontFamily where
  /-- A quoted name such as `"Helvetica Neue"`. Quotes and backslashes are not allowed;
  the proof `h` is found by `decide`. -/
  | named (name : String) (h : (name.toList.all fun c => c ≠ '"' && c ≠ '\\' && c ≠ '\n') = true := by decide)
  | serif | sansSerif | monospace | systemUi
  deriving Repr

/-- Typed declarations. -/
inductive Decl where
  | color (c : Color)
  | backgroundColor (c : Color)
  | margin (l : Length)
  | marginSide (s : Side) (l : Length)
  /-- `margin: v h` -/
  | marginVH (v h : Length)
  | padding (l : Length)
  | paddingSide (s : Side) (l : Length)
  /-- `padding: v h` -/
  | paddingVH (v h : Length)
  | width (l : Length)
  | maxWidth (l : Length)
  | minWidth (l : Length)
  | height (l : Length)
  | minHeight (l : Length)
  | fontSize (l : Length)
  | fontFamily (fs : List FontFamily) (h : fs ≠ [] := by decide)
  | fontWeight (w : FontWeight)
  | fontStyleItalic
  | lineHeight (v : Decimal)
  | letterSpacing (l : Length)
  | textAlign (a : TextAlign)
  | textDecoration (d : TextDecoration)
  | textTransform (t : TextTransform)
  | whiteSpace (w : WhiteSpace)
  | display (d : Display)
  | flexDirection (d : FlexDirection)
  | flexWrap
  | justifyContent (a : Align)
  | alignItems (a : Align)
  | gap (l : Length)
  | border (w : Length) (s : BorderStyle) (c : Color)
  | borderSide (side : Side) (w : Length) (s : BorderStyle) (c : Color)
  | borderRadius (l : Length)
  | listStyle (s : ListStyle)
  | overflowX (o : Overflow)
  | overflowY (o : Overflow)
  | opacity (v : Decimal)
  | boxSizing (b : BoxSizing)
  | cursor (c : Cursor)
  deriving Repr

/-! ## Selectors -/

/-- Pseudo-classes. -/
inductive Pseudo where
  | hover | focus | active | visited | firstChild | lastChild | focusVisible
  deriving Repr

/-- A type selector: any element name, including the document-level `html` and `body`. -/
inductive TypeSel where
  | html | body
  | tag (t : Html.Tag)
  | void (v : Html.VoidTag)
  deriving Repr

/-- The element name. -/
def TypeSel.render : TypeSel → List Char
  | .html => "html".toList
  | .body => "body".toList
  | .tag t => t.name.toList
  | .void v => v.name.toList

/-- A compound selector: optional type, then classes, id and pseudo-classes. -/
structure Compound where
  /-- Element type. -/
  tag : Option TypeSel := none
  /-- `.class` parts. -/
  classes : List Ident := []
  /-- `#id` part. -/
  id : Option Ident := none
  /-- `:pseudo` parts. -/
  pseudos : List Pseudo := []
  deriving Repr

/-- Combinators between compounds. -/
inductive Combinator where
  /-- `a b` -/
  | descendant
  /-- `a > b` -/
  | child
  deriving Repr

/-- A complex selector: compounds joined by combinators. -/
inductive Selector where
  | simple (c : Compound)
  | combine (a : Selector) (comb : Combinator) (b : Compound)
  deriving Repr

/-- `tag` -/
def Selector.tag (t : Html.Tag) : Selector := .simple { tag := some (.tag t) }
/-- `html` -/
def Selector.html : Selector := .simple { tag := some .html }
/-- `body` -/
def Selector.body : Selector := .simple { tag := some .body }
/-- A void tag such as `img` or `hr`. -/
def Selector.void (v : Html.VoidTag) : Selector := .simple { tag := some (.void v) }
/-- `.name` -/
def Selector.cls (s : String) (h : IsIdent s := by decide) : Selector :=
  .simple { classes := [⟨s, h⟩] }
/-- `#name` -/
def Selector.id (s : String) (h : IsIdent s := by decide) : Selector :=
  .simple { id := some ⟨s, h⟩ }
/-- `*` -/
def Selector.universal : Selector := .simple {}
/-- `tag.name` -/
def Selector.tagCls (t : Html.Tag) (s : String) (h : IsIdent s := by decide) : Selector :=
  .simple { tag := some (.tag t), classes := [⟨s, h⟩] }
/-- Adds a pseudo-class to the last compound. -/
def Selector.pseudo (s : Selector) (p : Pseudo) : Selector :=
  match s with
  | .simple c => .simple { c with pseudos := c.pseudos ++ [p] }
  | .combine a comb b => .combine a comb { b with pseudos := b.pseudos ++ [p] }
/-- `a b` -/
def Selector.desc (a : Selector) (b : Compound) : Selector := .combine a .descendant b
/-- `a > b` -/
def Selector.child (a : Selector) (b : Compound) : Selector := .combine a .child b

/-- Sugar: `sel.hover` -/
abbrev Selector.hover (s : Selector) : Selector := s.pseudo .hover
/-- Sugar: `sel.focus` -/
abbrev Selector.focus (s : Selector) : Selector := s.pseudo .focus

/-- `tag` as a compound, for the right-hand side of combinators. -/
def Compound.ofTag (t : Html.Tag) : Compound := { tag := some (.tag t) }
/-- `.name` as a compound. -/
def Compound.ofCls (s : String) (h : IsIdent s := by decide) : Compound := { classes := [⟨s, h⟩] }

/-! ## Rules and stylesheets -/

/-- A rule set or a media query. -/
inductive Rule where
  /-- `sel, sel { decl; decl }` -/
  | style (selectors : List Selector) (decls : List Decl) (h : selectors ≠ [] := by decide)
  /-- `@media (max-width: L) { rules }` -/
  | mediaMaxWidth (l : Length) (rules : List Rule)
  /-- `@media (prefers-color-scheme: dark) { rules }` -/
  | mediaDark (rules : List Rule)
  deriving Repr

/-- A stylesheet. -/
abbrev Stylesheet := List Rule

/-- `sel { decls }` -/
def rule (sel : Selector) (decls : List Decl) : Rule := .style [sel] decls (by simp)

/-- `sel₁, sel₂, … { decls }` -/
def rules (sels : List Selector) (decls : List Decl) (h : sels ≠ [] := by decide) : Rule :=
  .style sels decls h

/-! ## Rendering -/

/-- Two hex digits. -/
def hexByte (v : UInt8) : List Char :=
  [hexDigit (v.toNat / 16), hexDigit (v.toNat % 16)]
where
  /-- One hex digit for `d % 16`. -/
  hexDigit (d : Nat) : Char :=
    match d % 16 with
    | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
    | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- Renders a length. -/
def Length.render : Length → List Char
  | .px v => v.render ++ ['p', 'x']
  | .rem v => v.render ++ ['r', 'e', 'm']
  | .em v => v.render ++ ['e', 'm']
  | .pct v => v.render ++ ['%']
  | .vw v => v.render ++ ['v', 'w']
  | .vh v => v.render ++ ['v', 'h']
  | .zero => ['0']
  | .auto => "auto".toList

/-- Keyword text of a named colour. -/
def NamedColor.render : NamedColor → List Char
  | .black => "black".toList | .white => "white".toList | .red => "red".toList
  | .green => "green".toList | .blue => "blue".toList | .gray => "gray".toList
  | .silver => "silver".toList | .transparent => "transparent".toList
  | .currentColor => "currentColor".toList | .inherit => "inherit".toList

/-- Renders a colour. -/
def Color.render : Color → List Char
  | .hex r g b => '#' :: (hexByte r ++ hexByte g ++ hexByte b)
  | .rgba r g b a =>
    "rgba(".toList ++ natDigits r.toNat ++ [','] ++ natDigits g.toNat ++ [','] ++
      natDigits b.toNat ++ [','] ++ a.render ++ [')']
  | .named n => n.render

/-- Keyword text. -/
def Display.render : Display → List Char
  | .block => "block".toList | .inline => "inline".toList | .inlineBlock => "inline-block".toList
  | .flex => "flex".toList | .grid => "grid".toList | .none => "none".toList

/-- Keyword text. -/
def FlexDirection.render : FlexDirection → List Char
  | .row => "row".toList | .column => "column".toList
  | .rowReverse => "row-reverse".toList | .columnReverse => "column-reverse".toList

/-- Keyword text. -/
def Align.render : Align → List Char
  | .flexStart => "flex-start".toList | .flexEnd => "flex-end".toList | .center => "center".toList
  | .spaceBetween => "space-between".toList | .spaceAround => "space-around".toList
  | .stretch => "stretch".toList | .baseline => "baseline".toList

/-- Keyword text. -/
def TextAlign.render : TextAlign → List Char
  | .left => "left".toList | .right => "right".toList | .center => "center".toList
  | .justify => "justify".toList

/-- Keyword text. -/
def FontWeight.render : FontWeight → List Char
  | .normal => "normal".toList | .bold => "bold".toList
  | .w100 => "100".toList | .w200 => "200".toList | .w300 => "300".toList | .w400 => "400".toList
  | .w500 => "500".toList | .w600 => "600".toList | .w700 => "700".toList | .w800 => "800".toList
  | .w900 => "900".toList

/-- Keyword text. -/
def BorderStyle.render : BorderStyle → List Char
  | .none => "none".toList | .solid => "solid".toList | .dashed => "dashed".toList
  | .dotted => "dotted".toList | .double => "double".toList

/-- Keyword text. -/
def TextDecoration.render : TextDecoration → List Char
  | .none => "none".toList | .underline => "underline".toList
  | .lineThrough => "line-through".toList

/-- Keyword text. -/
def WhiteSpace.render : WhiteSpace → List Char
  | .normal => "normal".toList | .nowrap => "nowrap".toList | .pre => "pre".toList
  | .preWrap => "pre-wrap".toList

/-- Keyword text. -/
def Overflow.render : Overflow → List Char
  | .visible => "visible".toList | .hidden => "hidden".toList | .scroll => "scroll".toList
  | .auto => "auto".toList

/-- Keyword text. -/
def TextTransform.render : TextTransform → List Char
  | .none => "none".toList | .uppercase => "uppercase".toList
  | .lowercase => "lowercase".toList | .capitalize => "capitalize".toList

/-- Keyword text. -/
def BoxSizing.render : BoxSizing → List Char
  | .contentBox => "content-box".toList | .borderBox => "border-box".toList

/-- Keyword text. -/
def Cursor.render : Cursor → List Char
  | .auto => "auto".toList | .pointer => "pointer".toList | .default => "default".toList
  | .text => "text".toList

/-- Keyword text. -/
def ListStyle.render : ListStyle → List Char
  | .none => "none".toList | .disc => "disc".toList | .decimal => "decimal".toList
  | .circle => "circle".toList | .square => "square".toList

/-- Keyword text. -/
def Side.render : Side → List Char
  | .top => "top".toList | .right => "right".toList | .bottom => "bottom".toList
  | .left => "left".toList

/-- Renders a font family. -/
def FontFamily.render : FontFamily → List Char
  | .named n _ => '"' :: n.toList ++ ['"']
  | .serif => "serif".toList | .sansSerif => "sans-serif".toList
  | .monospace => "monospace".toList | .systemUi => "system-ui".toList

/-- Renders a comma-separated font family list. -/
def renderFamilies : List FontFamily → List Char
  | [] => []
  | [f] => f.render
  | f :: fs => f.render ++ ',' :: renderFamilies fs

/-- Property name and rendered value of a declaration. -/
def Decl.parts : Decl → List Char × List Char
  | .color c => ("color".toList, c.render)
  | .backgroundColor c => ("background-color".toList, c.render)
  | .margin l => ("margin".toList, l.render)
  | .marginSide s l => ("margin-".toList ++ s.render, l.render)
  | .marginVH v h => ("margin".toList, v.render ++ ' ' :: h.render)
  | .padding l => ("padding".toList, l.render)
  | .paddingSide s l => ("padding-".toList ++ s.render, l.render)
  | .paddingVH v h => ("padding".toList, v.render ++ ' ' :: h.render)
  | .width l => ("width".toList, l.render)
  | .maxWidth l => ("max-width".toList, l.render)
  | .minWidth l => ("min-width".toList, l.render)
  | .height l => ("height".toList, l.render)
  | .minHeight l => ("min-height".toList, l.render)
  | .fontSize l => ("font-size".toList, l.render)
  | .fontFamily fs _ => ("font-family".toList, renderFamilies fs)
  | .fontWeight w => ("font-weight".toList, w.render)
  | .fontStyleItalic => ("font-style".toList, "italic".toList)
  | .lineHeight v => ("line-height".toList, v.render)
  | .letterSpacing l => ("letter-spacing".toList, l.render)
  | .textAlign a => ("text-align".toList, a.render)
  | .textDecoration d => ("text-decoration".toList, d.render)
  | .textTransform t => ("text-transform".toList, t.render)
  | .whiteSpace w => ("white-space".toList, w.render)
  | .display d => ("display".toList, d.render)
  | .flexDirection d => ("flex-direction".toList, d.render)
  | .flexWrap => ("flex-wrap".toList, "wrap".toList)
  | .justifyContent a => ("justify-content".toList, a.render)
  | .alignItems a => ("align-items".toList, a.render)
  | .gap l => ("gap".toList, l.render)
  | .border w s c => ("border".toList, w.render ++ ' ' :: s.render ++ ' ' :: c.render)
  | .borderSide side w s c =>
    ("border-".toList ++ side.render, w.render ++ ' ' :: s.render ++ ' ' :: c.render)
  | .borderRadius l => ("border-radius".toList, l.render)
  | .listStyle s => ("list-style".toList, s.render)
  | .overflowX o => ("overflow-x".toList, o.render)
  | .overflowY o => ("overflow-y".toList, o.render)
  | .opacity v => ("opacity".toList, v.render)
  | .boxSizing b => ("box-sizing".toList, b.render)
  | .cursor c => ("cursor".toList, c.render)

/-- `name:value;` -/
def Decl.render (d : Decl) : List Char :=
  d.parts.1 ++ ':' :: d.parts.2 ++ [';']

/-- Renders a declaration block body. -/
def renderDecls : List Decl → List Char
  | [] => []
  | d :: ds => d.render ++ renderDecls ds

/-- Keyword text. -/
def Pseudo.render : Pseudo → List Char
  | .hover => "hover".toList | .focus => "focus".toList | .active => "active".toList
  | .visited => "visited".toList | .firstChild => "first-child".toList
  | .lastChild => "last-child".toList | .focusVisible => "focus-visible".toList

/-- Renders `.a.b` -/
def renderClasses : List Ident → List Char
  | [] => []
  | c :: cs => '.' :: c.name.toList ++ renderClasses cs

/-- Renders `:p:q` -/
def renderPseudos : List Pseudo → List Char
  | [] => []
  | p :: ps => ':' :: p.render ++ renderPseudos ps

/-- Renders a compound selector; an empty compound is `*`. -/
def Compound.render (c : Compound) : List Char :=
  let tagPart : List Char :=
    match c.tag with
    | some t => t.render
    | none => if c.classes.isEmpty && c.id.isNone && c.pseudos.isEmpty then ['*'] else []
  let idPart : List Char :=
    match c.id with
    | some i => '#' :: i.name.toList
    | none => []
  tagPart ++ renderClasses c.classes ++ idPart ++ renderPseudos c.pseudos

/-- Renders a selector. -/
def Selector.render : Selector → List Char
  | .simple c => c.render
  | .combine a .descendant b => a.render ++ ' ' :: b.render
  | .combine a .child b => a.render ++ '>' :: b.render

/-- Renders a comma-separated selector list. -/
def renderSelectors : List Selector → List Char
  | [] => []
  | [s] => s.render
  | s :: ss => s.render ++ ',' :: renderSelectors ss

mutual
  /-- Renders a rule. -/
  def Rule.render : Rule → List Char
    | .style sels decls _ => renderSelectors sels ++ '{' :: renderDecls decls ++ ['}']
    | .mediaMaxWidth l rs =>
      "@media (max-width:".toList ++ l.render ++ "){".toList ++ renderRules rs ++ ['}']
    | .mediaDark rs =>
      "@media (prefers-color-scheme:dark){".toList ++ renderRules rs ++ ['}']
  /-- Renders a rule list. -/
  def renderRules : List Rule → List Char
    | [] => []
    | r :: rs => r.render ++ renderRules rs
end

/-- Renders a stylesheet to a string. -/
def Stylesheet.render (s : Stylesheet) : String := String.ofList (renderRules s)

end

end Sites.Css
