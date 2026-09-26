module
public import Sites.Html.Syntax

/-!
# A total Markdown subset

Blocks: ATX headings (`#` to `######`), paragraphs, fenced code blocks, bullet lists (`- `),
numbered lists (`1. `), block quotes (`> `) and thematic breaks (`---`).
Inlines: `**strong**`, `*emphasis*`, `` `code` `` and `[text](url)`.

Both parsers are structurally recursive on an explicit fuel (the input length), so they are
total, need no `partial`, and reduce inside the kernel. That last property is what lets
`Doc.linksOk` be checked with `decide` at compile time: a Markdown page whose internal link
does not resolve to a route fails to elaborate.
-/

namespace Sites.Markdown

open Html

@[expose] public section

/-- Inline content. -/
inductive Inline where
  | text (s : String)
  | emph (xs : List Inline)
  | strong (xs : List Inline)
  | code (s : String)
  | link (xs : List Inline) (url : List Char)
  deriving Repr

/-- Block content. -/
inductive Block where
  | heading (level : Nat) (xs : List Inline)
  | para (xs : List Inline)
  | code (lang : String) (body : String)
  | bullets (items : List (List Inline))
  | numbered (items : List (List Inline))
  | quote (xs : List Inline)
  | rule
  deriving Repr

/-- A parsed document. -/
abbrev Doc := List Block

/-! ## Inline parsing -/

/-- Splits at the first occurrence of `delim`: `splitAt "**" "a**b" = some ("a", "b")`. -/
def splitAt (delim : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if (c :: cs).take delim.length = delim then some ([], (c :: cs).drop delim.length)
    else match splitAt delim cs with
      | some (before, after) => some (c :: before, after)
      | none => none

/-- Characters that start inline syntax. -/
def isInlineSpecial (c : Char) : Bool := c = '*' || c = '`' || c = '['

/-- Prepends text, merging with a leading text node. -/
def pushText (s : String) : List Inline → List Inline
  | .text t :: rest => .text (s ++ t) :: rest
  | rest => if s = "" then rest else .text s :: rest

/-- Parses inline content with the given fuel. -/
def parseInlinesWith : Nat → List Char → List Inline
  | 0, cs => if cs = [] then [] else [.text (String.ofList cs)]
  | fuel + 1, cs =>
    match cs with
    | [] => []
    | '*' :: '*' :: rest =>
      match splitAt ['*', '*'] rest with
      | some (inner, after) =>
        .strong (parseInlinesWith fuel inner) :: parseInlinesWith fuel after
      | none => pushText "**" (parseInlinesWith fuel rest)
    | '*' :: rest =>
      match splitAt ['*'] rest with
      | some (inner, after) => .emph (parseInlinesWith fuel inner) :: parseInlinesWith fuel after
      | none => pushText "*" (parseInlinesWith fuel rest)
    | '`' :: rest =>
      match splitAt ['`'] rest with
      | some (inner, after) => .code (String.ofList inner) :: parseInlinesWith fuel after
      | none => pushText "`" (parseInlinesWith fuel rest)
    | '[' :: rest =>
      match splitAt [']'] rest with
      | some (txt, '(' :: after) =>
        match splitAt [')'] after with
        | some (url, after') =>
          .link (parseInlinesWith fuel txt) url :: parseInlinesWith fuel after'
        | none => pushText "[" (parseInlinesWith fuel rest)
      | _ => pushText "[" (parseInlinesWith fuel rest)
    | c :: rest =>
      let run := (c :: rest).takeWhile fun d => !isInlineSpecial d
      let rest' := (c :: rest).dropWhile fun d => !isInlineSpecial d
      pushText (String.ofList run) (parseInlinesWith fuel rest')

/-- Parses inline content. -/
def parseInlines (cs : List Char) : List Inline := parseInlinesWith (cs.length + 1) cs

/-! ## Block parsing -/

/-- A line of input. -/
abbrev Line := List Char

/-- Whitespace-only line. -/
def isBlank (l : Line) : Bool := l.all fun c => c = ' ' || c = '\t' || c = '\r'

/-- Does `l` start with `pre`? -/
def startsWith (pre : List Char) (l : Line) : Bool := l.take pre.length = pre

/-- Is this a fenced-code delimiter line? -/
def isFence (l : Line) : Bool := startsWith "```".toList l

/-- Is this a bullet item line? -/
def isBullet (l : Line) : Bool := startsWith "- ".toList l || startsWith "* ".toList l

/-- Is this a numbered item line (`1. `)? -/
def isNumbered (l : Line) : Bool :=
  let digits := l.takeWhile Char.isDigit
  !digits.isEmpty && startsWith ". ".toList (l.drop digits.length)

/-- Strips the numbered-item prefix. -/
def stripNumbered (l : Line) : Line :=
  let digits := l.takeWhile Char.isDigit
  (l.drop digits.length).drop 2

/-- Is this a block-quote line? -/
def isQuote (l : Line) : Bool := startsWith "> ".toList l || l = ['>']

/-- Strips the quote prefix. -/
def stripQuote (l : Line) : Line := if l = ['>'] then [] else l.drop 2

/-- Number of leading `#` characters. -/
def headingLevel (l : Line) : Nat := (l.takeWhile (· = '#')).length

/-- Is this an ATX heading line? -/
def isHeading (l : Line) : Bool :=
  let n := headingLevel l
  0 < n && n ≤ 6 && startsWith [' '] (l.drop n)

/-- Is this a thematic break? -/
def isRule (l : Line) : Bool := l = "---".toList || l = "***".toList

/-- A line that continues a paragraph. -/
def isParaLine (l : Line) : Bool :=
  !isBlank l && !isFence l && !isBullet l && !isNumbered l && !isQuote l && !isHeading l &&
    !isRule l

/-- Joins lines with a separator. -/
def joinLines (sep : List Char) : List Line → List Char
  | [] => []
  | [l] => l
  | l :: ls => l ++ sep ++ joinLines sep ls

/-- Trims leading and trailing spaces. -/
def trim (l : Line) : Line :=
  ((l.dropWhile (· = ' ')).reverse.dropWhile (· = ' ')).reverse

/-- Parses blocks with the given fuel. -/
def parseBlocksWith : Nat → List Line → List Block
  | 0, _ => []
  | fuel + 1, lines =>
    match lines with
    | [] => []
    | l :: rest =>
      if isBlank l then parseBlocksWith fuel rest
      else if isFence l then
        let lang := String.ofList (trim (l.drop 3))
        let body := rest.takeWhile fun x => !isFence x
        let rest' := (rest.dropWhile fun x => !isFence x).drop 1
        .code lang (String.ofList (joinLines ['\n'] body)) :: parseBlocksWith fuel rest'
      else if isHeading l then
        let n := headingLevel l
        .heading n (parseInlines (trim (l.drop n))) :: parseBlocksWith fuel rest
      else if isRule l then .rule :: parseBlocksWith fuel rest
      else if isQuote l then
        let ls := (l :: rest).takeWhile isQuote
        let rest' := (l :: rest).dropWhile isQuote
        .quote (parseInlines (joinLines [' '] (ls.map stripQuote))) :: parseBlocksWith fuel rest'
      else if isBullet l then
        let ls := (l :: rest).takeWhile isBullet
        let rest' := (l :: rest).dropWhile isBullet
        .bullets (ls.map fun x => parseInlines (trim (x.drop 2))) :: parseBlocksWith fuel rest'
      else if isNumbered l then
        let ls := (l :: rest).takeWhile isNumbered
        let rest' := (l :: rest).dropWhile isNumbered
        .numbered (ls.map fun x => parseInlines (trim (stripNumbered x))) ::
          parseBlocksWith fuel rest'
      else
        let ls := (l :: rest).takeWhile isParaLine
        let rest' := (l :: rest).dropWhile isParaLine
        .para (parseInlines (joinLines [' '] (ls.map trim))) :: parseBlocksWith fuel rest'

/-- Splits input into lines. -/
def splitLines : List Char → List Line
  | [] => [[]]
  | '\n' :: cs => [] :: splitLines cs
  | c :: cs =>
    match splitLines cs with
    | l :: ls => (c :: l) :: ls
    | [] => [[c]]

/-- Parses a Markdown document given as characters. This is the form that reduces quickly in
the kernel; see `chars!`. -/
def parseChars (cs : List Char) : Doc :=
  let lines := splitLines cs
  parseBlocksWith (lines.length + 1) lines

/-- Parses a Markdown document. -/
def parse (s : String) : Doc := parseChars s.toList

/-! ## Links -/

mutual
  /-- All link targets in an inline. -/
  def Inline.links : Inline → List (List Char)
    | .text _ => []
    | .code _ => []
    | .emph xs => Inline.linksOf xs
    | .strong xs => Inline.linksOf xs
    | .link xs url => url :: Inline.linksOf xs
  /-- All link targets in a list of inlines. -/
  def Inline.linksOf : List Inline → List (List Char)
    | [] => []
    | x :: xs => x.links ++ Inline.linksOf xs
end

/-- All link targets in a block. -/
def Block.links : Block → List (List Char)
  | .heading _ xs => Inline.linksOf xs
  | .para xs => Inline.linksOf xs
  | .quote xs => Inline.linksOf xs
  | .bullets items => (items.map Inline.linksOf).flatten
  | .numbered items => (items.map Inline.linksOf).flatten
  | .code _ _ => []
  | .rule => []

/-- All link targets in a document. -/
def Doc.links (d : Doc) : List (List Char) := (d.map Block.links).flatten

/-- Internal links (starting with `/`) all resolve to routes. -/
def Doc.linksOk {ρ : Type} (route? : List Char → Option ρ) (d : Doc) : Bool :=
  d.links.all fun u => !(startsWith ['/'] u) || (route? u).isSome

/-! ## Lowering to HTML -/

variable {ρ : Type}

mutual
  /-- Lowers an inline. -/
  def Inline.toHtml (resolve : String → Link ρ) : Inline → Node ρ .phrasing
    | .text s => Html.text s
    | .code s => Html.code [] [Html.text s]
    | .emph xs => .el .em rfl [] (Inline.toHtmlList resolve xs)
    | .strong xs => .el .strong rfl [] (Inline.toHtmlList resolve xs)
    | .link xs url => .el .a rfl [.href (resolve (String.ofList url))] (Inline.toHtmlList resolve xs)
  /-- Lowers a list of inlines. -/
  def Inline.toHtmlList (resolve : String → Link ρ) : List Inline → Nodes ρ .phrasing
    | [] => .nil
    | x :: xs => .cons (x.toHtml resolve) (Inline.toHtmlList resolve xs)
end

/-- Phrasing content as flow content, one node per inline. -/
def inlinesAsFlow (resolve : String → Link ρ) (xs : List Inline) : Nodes ρ .flow :=
  go (Inline.toHtmlList resolve xs)
where
  /-- Wraps each node. -/
  go : Nodes ρ .phrasing → Nodes ρ .flow
    | .nil => .nil
    | .cons n ns => .cons (.inline rfl n) (go ns)

/-- Heading tag for a level. -/
def headingTag : Nat → Tag
  | 1 => .h1 | 2 => .h2 | 3 => .h3 | 4 => .h4 | 5 => .h5 | _ => .h6

theorem headingTag_ctx (n : Nat) : (headingTag n).ctx = .flow := by
  unfold headingTag; split <;> rfl

theorem headingTag_childCtx (n : Nat) : (headingTag n).childCtx = .phrasing := by
  unfold headingTag; split <;> rfl

/-- Lowers a list of items to `li`s. -/
def itemsToHtml (resolve : String → Link ρ) : List (List Inline) → Nodes ρ .listItem
  | [] => .nil
  | item :: items => .cons (.el .li rfl [] (inlinesAsFlow resolve item)) (itemsToHtml resolve items)

/-- Lowers a block. -/
def Block.toHtml (resolve : String → Link ρ) : Block → Node ρ .flow
  | .heading n xs =>
    .el (headingTag n) (headingTag_ctx n) []
      (headingTag_childCtx n ▸ Inline.toHtmlList resolve xs)
  | .para xs => .el .p rfl [] (Inline.toHtmlList resolve xs)
  | .code lang body =>
    .el .pre rfl [] (.cons (.el .code rfl
      (if lang = "" then [] else [.cls ("language-" ++ lang)]) (.cons (text body) .nil)) .nil)
  | .bullets items => .el .ul rfl [] (itemsToHtml resolve items)
  | .numbered items => .el .ol rfl [] (itemsToHtml resolve items)
  | .quote xs => .el .blockquote rfl [] (.cons (.el .p rfl [] (Inline.toHtmlList resolve xs)) .nil)
  | .rule => .void .hr rfl []

/-- Lowers a document. -/
def Doc.toHtml (resolve : String → Link ρ) (d : Doc) : List (Node ρ .flow) :=
  d.map (Block.toHtml resolve)

/-- Resolves a URL against a route lookup: routes become typed links. -/
def resolveWith (route? : List Char → Option ρ) (u : String) : Link ρ :=
  match route? u.toList with
  | some r => .route r
  | none => .url u

/-- Parses Markdown given as characters (use `chars!"..."`) into page content. Internal links
must resolve: the proof obligation is discharged by `decide +kernel`, so an unresolved
`/path/` is a compile-time error. Kernel evaluation of the parser on a page takes about a
second; decoding a `String` literal in the kernel would take far longer, hence `chars!`. -/
def md (route? : List Char → Option ρ) (cs : List Char)
    (h : (parseChars cs).linksOk route? = true := by decide +kernel) : List (Node ρ .flow) :=
  have _ := h
  (parseChars cs).toHtml (resolveWith route?)

/-- Parses Markdown from a string with no link check. -/
def mdUnchecked (route? : List Char → Option ρ) (s : String) : List (Node ρ .flow) :=
  (parse s).toHtml (resolveWith route?)

end

end Sites.Markdown

namespace Sites.Markdown

public section

/-- `chars!"text"` is the character list of the literal, spelled out as a list literal so
that the kernel can compute with it directly. -/
macro:max "chars!" s:str : term => do
  let lits := s.getString.toList.toArray.map fun c => Lean.Syntax.mkCharLit c
  `([$lits,*])

end

end Sites.Markdown
