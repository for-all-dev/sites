module
public import Sites.Html.Syntax
public import Sites.Html.Escape
public import Sites.Html.Render

/-!
# Parsing

A parser for exactly the canonical form produced by `Sites.Html.Render`. It exists so that the
printer can be *specified*: `Sites.Html.RoundTrip` proves that parsing a rendered tree gives
the tree back. It is not a general HTML parser and rejects anything non-canonical.

Recursion is bounded by an explicit fuel argument; `parseDocument` supplies
`input.length + 1`, which the round-trip proof shows is always enough.
-/

namespace Sites.Html

@[expose] public section

variable {ρ : Type}

/-- Drops `</name>` from the front of the input. -/
def dropClose (name : List Char) (input : List Char) : Option (List Char) :=
  match input with
  | '<' :: '/' :: rest =>
    if rest.take name.length = name then
      match rest.drop name.length with
      | '>' :: rest => some rest
      | _ => none
    else none
  | _ => none

/-- Drops a literal prefix. -/
def dropPrefix (pre : List Char) (input : List Char) : Option (List Char) :=
  if input.take pre.length = pre then some (input.drop pre.length) else none

/-- Does the input start with `</`? -/
def startsClose : List Char → Bool
  | '<' :: '/' :: _ => true
  | _ => false

/-- Parses ` key="value"` pairs until something that is not a space. -/
def parseAttrs (route? : String → Option ρ) : Nat → List Char → Option (List (Attr ρ) × List Char)
  | 0, _ => none
  | fuel + 1, input =>
    match input with
    | [] => some ([], [])
    | d :: rest =>
      if d = ' ' then
        let key := rest.takeWhile isNameChar
        let rest := rest.dropWhile isNameChar
        match rest with
        | '=' :: '"' :: rest =>
          let raw := rest.takeWhile (· ≠ '"')
          match rest.dropWhile (· ≠ '"') with
          | '"' :: rest =>
            match unescape raw with
            | some v =>
              match Attr.ofKey? route? (String.ofList key) (String.ofList v) with
              | some a =>
                match parseAttrs route? fuel rest with
                | some (as, rest) => some (a :: as, rest)
                | none => none
              | none => none
            | none => none
          | _ => none
        | _ => none
      else some ([], d :: rest)

/-- Places a parsed element of category `t` into the requested category `c`, wrapping
phrasing content in `inline` when flow content is expected. -/
def placeEl (c : Ctx) (t : Tag) (attrs : List (Attr ρ)) (children : Nodes ρ t.childCtx) :
    Option (Node ρ c) :=
  if h : t.ctx = c then some (.el t h attrs children)
  else if h' : t.ctx = .phrasing ∧ c = .flow then some (.inline h'.2 (.el t h'.1 attrs children))
  else none

/-- Same as `placeEl`, for void elements. -/
def placeVoid (c : Ctx) (t : VoidTag) (attrs : List (Attr ρ)) : Option (Node ρ c) :=
  if h : t.ctx = c then some (.void t h attrs)
  else if h' : t.ctx = .phrasing ∧ c = .flow then some (.inline h'.2 (.void t h'.1 attrs))
  else none

/-- Places parsed text into the requested category. -/
def placeText (c : Ctx) (s : String) : Option (Node ρ c) :=
  if h : c = .phrasing then some (.text h s)
  else if h' : c = .flow then some (.inline h' (.text rfl s))
  else none

/-- Parses a run of text up to the next `<`. -/
def parseText (c : Ctx) (input : List Char) : Option (Node ρ c × List Char) :=
  let raw := input.takeWhile (· ≠ '<')
  let rest := input.dropWhile (· ≠ '<')
  match unescape raw with
  | some s =>
    match placeText c (String.ofList s) with
    | some n => some (n, rest)
    | none => none
  | none => none

/-- Parses `<title>text</title>`; `rest` is what follows the tag name. -/
def parseTitle (c : Ctx) (rest : List Char) : Option (Node ρ c × List Char) :=
  match rest with
  | '>' :: rest =>
    let raw := rest.takeWhile (· ≠ '<')
    let rest := rest.dropWhile (· ≠ '<')
    match unescape raw with
    | some s =>
      match dropClose "title".toList rest with
      | some rest =>
        if h : c = .head then some (.title h (String.ofList s), rest) else none
      | none => none
    | none => none
  | _ => none

mutual
  /-- Parses one node in category `c`. -/
  def parseNode (route? : String → Option ρ) : Nat → (c : Ctx) → List Char →
      Option (Node ρ c × List Char)
    | 0, _, _ => none
    | fuel + 1, c, input =>
      match input with
      | [] => none
      | d :: rest =>
        if d = '<' then
          let name := rest.takeWhile isNameChar
          let rest := rest.dropWhile isNameChar
          let nameS := String.ofList name
          match Tag.ofNameIn? c nameS with
          | some t =>
            match parseAttrs route? (fuel + 1) rest with
            | some (attrs, '>' :: rest) =>
              match parseNodes route? fuel t.childCtx rest with
              | some (children, rest) =>
                match dropClose t.name.toList rest with
                | some rest =>
                  match placeEl c t attrs children with
                  | some n => some (n, rest)
                  | none => none
                | none => none
              | none => none
            | _ => none
          | none =>
            match VoidTag.ofName? nameS with
            | some t =>
              match parseAttrs route? (fuel + 1) rest with
              | some (attrs, '>' :: rest) =>
                match placeVoid c t attrs with
                | some n => some (n, rest)
                | none => none
              | _ => none
            | none =>
              if nameS = "title" then parseTitle c rest else none
        else parseText c (d :: rest)
  /-- Parses nodes until the input is exhausted or a closing tag starts. -/
  def parseNodes (route? : String → Option ρ) : Nat → (c : Ctx) → List Char →
      Option (Nodes ρ c × List Char)
    | 0, _, _ => none
    | fuel + 1, c, input =>
      if input.isEmpty then some (.nil, [])
      else if startsClose input then some (.nil, input)
      else
        match parseNode route? fuel c input with
        | some (n, rest) =>
          match parseNodes route? fuel c rest with
          | some (ns, rest) => some (.cons n ns, rest)
          | none => none
        | none => none
end

/-- Parses a canonical document with the given fuel. -/
def parseDocumentWith (route? : String → Option ρ) (fuel : Nat) (input : List Char) :
    Option (Document ρ) :=
  match dropPrefix docPrefix input with
  | some rest =>
    let rawLang := rest.takeWhile (· ≠ '"')
    let rest := rest.dropWhile (· ≠ '"')
    match unescape rawLang with
    | some lang =>
      match dropPrefix headOpen rest with
      | some rest =>
        match parseNodes route? fuel .head rest with
        | some (head, rest) =>
          match dropPrefix bodyOpen rest with
          | some rest =>
            match parseNodes route? fuel .flow rest with
            | some (body, rest) =>
              match dropPrefix docSuffix rest with
              | some [] => some { lang := String.ofList lang, head, body }
              | _ => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

/-- Parses a canonical document. -/
def parseDocument (route? : String → Option ρ) (input : List Char) : Option (Document ρ) :=
  parseDocumentWith route? (input.length + 1) input

end

/-! ## Reduction lemmas -/

public theorem startsClose_cons_of_ne {d : Char} (ds : List Char) (hd : d ≠ '<') :
    startsClose (d :: ds) = false := by
  unfold startsClose; split <;> simp_all

public theorem startsClose_lt_cons_of_ne {e : Char} (es : List Char) (he : e ≠ '/') :
    startsClose ('<' :: e :: es) = false := by
  unfold startsClose; split <;> simp_all

end Sites.Html
