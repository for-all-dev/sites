module
public import Sites.Html.Syntax
public import Sites.Html.Escape

/-!
# Rendering

A canonical printer: no whitespace between tags, every attribute double-quoted, every text
and attribute value escaped. Canonicity is what makes the parser in `Sites.Html.Parse` an
exact inverse.

Rendering is parameterised by `url : ρ → String`, the site's route-to-URL function.
-/

namespace Sites.Html

@[expose] public section

variable {ρ : Type}

/-- The URL an attribute value refers to. -/
def Link.render (url : ρ → String) : Link ρ → String
  | .route r => url r
  | .url s => s

/-- The attribute's value before escaping. -/
def Attr.value (url : ρ → String) : Attr ρ → String
  | .id v | .cls v | .src v | .alt v | .title v | .lang v | .rel v | .type v | .name v
  | .content v | .charset v | .role v | .ariaLabel v | .target v | .width v | .height v
  | .loading v | .crossorigin v | .viewBox v | .cx v | .cy v | .r v | .x v | .y v | .fill v
  | .stroke v => v
  | .href l => l.render url

/-- ` key="escaped value"` -/
def Attr.render (url : ρ → String) (a : Attr ρ) : List Char :=
  ' ' :: (a.key.toList ++ '=' :: '"' :: escape (a.value url).toList ++ ['"'])

/-- Renders an attribute list, each preceded by a space. -/
def renderAttrs (url : ρ → String) : List (Attr ρ) → List Char
  | [] => []
  | a :: as => a.render url ++ renderAttrs url as

mutual
  /-- Renders a node. -/
  def Node.render (url : ρ → String) : {c : Ctx} → Node ρ c → List Char
    | _, .text _ s => escape s.toList
    | _, .inline _ n => n.render url
    | _, .el t _ attrs children =>
      '<' :: t.name.toList ++ renderAttrs url attrs ++ '>' :: children.render url ++
        '<' :: '/' :: t.name.toList ++ ['>']
    | _, .void t _ attrs => '<' :: t.name.toList ++ renderAttrs url attrs ++ ['>']
    | _, .title _ s =>
      '<' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: escape s.toList ++
        ['<', '/', 't', 'i', 't', 'l', 'e', '>']
  /-- Renders a sequence of nodes. -/
  def Nodes.render (url : ρ → String) : {c : Ctx} → Nodes ρ c → List Char
    | _, .nil => []
    | _, .cons n ns => n.render url ++ ns.render url
end

/-- `<!DOCTYPE html><html lang="` -/
def docPrefix : List Char := "<!DOCTYPE html><html lang=\"".toList
/-- `><head>` -/
def headOpenTail : List Char := "><head>".toList
/-- `"><head>` -/
def headOpen : List Char := '"' :: headOpenTail
/-- `</head><body>` -/
def bodyOpen : List Char := "</head><body>".toList
/-- `</body></html>` -/
def docSuffix : List Char := "</body></html>".toList

/-- Renders a full document. -/
def Document.render (url : ρ → String) (d : Document ρ) : List Char :=
  docPrefix ++ escape d.lang.toList ++ headOpen ++ d.head.render url ++ bodyOpen ++
    d.body.render url ++ docSuffix

/-- Renders a full document to a `String`. -/
def Document.toString (url : ρ → String) (d : Document ρ) : String :=
  String.ofList (d.render url)

end

end Sites.Html
