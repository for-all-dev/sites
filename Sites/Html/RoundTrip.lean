module
public import Sites.Html.Syntax
public import Sites.Html.Escape
public import Sites.Html.Render
public import Sites.Html.Parse

/-!
# The printer round-trip theorem

`parseDocument route? (d.render url) = some d` for every *canonical* document `d`.

Canonical means: no empty text nodes, no two adjacent text nodes, and every `Link.url` is one
that `route?` does not recognise (otherwise it should have been a `Link.route`). Any tree can
be made canonical without changing its rendering; see `Sites.Html.Norm`.

The proof is a mutual induction over `Node`/`Nodes`, generalised over the unparsed suffix
`rest` and the fuel.
-/

namespace Sites.Html

variable {ρ : Type}

@[expose] public section

/-- A link is canonical when `route?` agrees with `url` on it. -/
def Link.Canonical (route? : String → Option ρ) (url : ρ → String) : Link ρ → Prop
  | .route r => route? (url r) = some r
  | .url s => route? s = none

/-- An attribute is canonical when its link (if any) is. -/
def Attr.Canonical (route? : String → Option ρ) (url : ρ → String) : Attr ρ → Prop
  | .href l => l.Canonical route? url
  | _ => True

/-- Whether a node renders as bare text. -/
def Node.isText : {c : Ctx} → Node ρ c → Bool
  | _, .text _ _ => true
  | _, .inline _ n => n.isText
  | _, _ => false

/-- Whether the first node of a sequence renders as bare text. -/
def Nodes.headIsText : {c : Ctx} → Nodes ρ c → Bool
  | _, .nil => false
  | _, .cons n _ => n.isText

mutual
  /-- Canonical nodes: nonempty text, canonical links, canonical children. -/
  def Node.Canonical (route? : String → Option ρ) (url : ρ → String) :
      {c : Ctx} → Node ρ c → Prop
    | _, .text _ s => s.toList ≠ []
    | _, .inline _ n => n.Canonical route? url
    | _, .el _ _ attrs children =>
      (∀ a ∈ attrs, a.Canonical route? url) ∧ children.Canonical route? url
    | _, .void _ _ attrs => ∀ a ∈ attrs, a.Canonical route? url
    | _, .title _ _ => True
  /-- Canonical sequences: canonical nodes, never two texts in a row. -/
  def Nodes.Canonical (route? : String → Option ρ) (url : ρ → String) :
      {c : Ctx} → Nodes ρ c → Prop
    | _, .nil => True
    | _, .cons n ns =>
      n.Canonical route? url ∧ ns.Canonical route? url ∧ (n.isText = true → ns.headIsText = false)
end

/-- A document is canonical when its head and body are. -/
def Document.Canonical (route? : String → Option ρ) (url : ρ → String) (d : Document ρ) : Prop :=
  d.head.Canonical route? url ∧ d.body.Canonical route? url

mutual
  /-- The fuel the parser needs for this node. -/
  def Node.size : {c : Ctx} → Node ρ c → Nat
    | _, .text _ _ => 1
    | _, .inline _ n => n.size
    | _, .el _ _ attrs children => children.size + attrs.length + 1
    | _, .void _ _ attrs => attrs.length + 1
    | _, .title _ _ => 1
  /-- The fuel the parser needs for this sequence. -/
  def Nodes.size : {c : Ctx} → Nodes ρ c → Nat
    | _, .nil => 1
    | _, .cons n ns => n.size + ns.size
end

end

/-! ## List helpers -/

theorem take_length_append {α : Type} (l r : List α) : (l ++ r).take l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem drop_length_append {α : Type} (l r : List α) : (l ++ r).drop l.length = r := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem dropPrefix_append (pre r : List Char) : dropPrefix pre (pre ++ r) = some r := by
  simp [dropPrefix, take_length_append, drop_length_append]

theorem dropClose_append (name r : List Char) :
    dropClose name ('<' :: '/' :: (name ++ '>' :: r)) = some r := by
  simp [dropClose, take_length_append, drop_length_append]

theorem dropClose_title (rest : List Char) :
    dropClose ['t', 'i', 't', 'l', 'e']
      ('<' :: '/' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: rest) = some rest := by
  simp [dropClose]

theorem ofList_title : String.ofList ['t', 'i', 't', 'l', 'e'] = "title" := by decide
theorem title_toList : "title".toList = ['t', 'i', 't', 'l', 'e'] := by decide
theorem title_chars : ∀ c ∈ ['t', 'i', 't', 'l', 'e'], isNameChar c = true := by decide

/-! ## Sizes are positive -/

mutual
  theorem Node.size_pos {c : Ctx} (n : Node ρ c) : 0 < n.size := by
    cases n with
    | text _ _ => simp [Node.size]
    | inline _ n => exact Node.size_pos n
    | el _ _ attrs children => simp [Node.size]
    | void _ _ attrs => simp [Node.size]
    | title _ _ => simp [Node.size]
  theorem Nodes.size_pos {c : Ctx} (ns : Nodes ρ c) : 0 < ns.size := by
    cases ns with
    | nil => simp [Nodes.size]
    | cons n ns => simp [Nodes.size]; have := Node.size_pos n; omega
end

/-! ## Attributes -/

theorem Attr.ofKey?_key_value (route? : String → Option ρ) (url : ρ → String) (a : Attr ρ)
    (h : a.Canonical route? url) : Attr.ofKey? route? a.key (a.value url) = some a := by
  cases a with
  | href l =>
    cases l with
    | route r =>
      simp [Attr.Canonical, Link.Canonical] at h
      simp [Attr.ofKey?, Attr.key, Attr.value, Link.render, h]
    | url s =>
      simp [Attr.Canonical, Link.Canonical] at h
      simp [Attr.ofKey?, Attr.key, Attr.value, Link.render, h]
  | _ => rfl

theorem Attr.render_head (url : ρ → String) (a : Attr ρ) (r : List Char) :
    a.render url ++ r =
      ' ' :: (a.key.toList ++ '=' :: '"' :: (escape (a.value url).toList ++ '"' :: r)) := by
  simp [Attr.render]

/-- After an attribute list comes either a space (another attribute) or the `>`; never a name
character. -/
theorem renderAttrs_gt_head (url : ρ → String) (attrs : List (Attr ρ)) (r : List Char) :
    ∃ c r', renderAttrs url attrs ++ '>' :: r = c :: r' ∧ isNameChar c = false := by
  cases attrs with
  | nil => exact ⟨'>', r, rfl, isNameChar_gt⟩
  | cons a as =>
    refine ⟨' ', a.key.toList ++ '=' :: '"' :: (escape (a.value url).toList ++
      '"' :: (renderAttrs url as ++ '>' :: r)), ?_, isNameChar_space⟩
    simp [renderAttrs, Attr.render]

theorem parseAttrs_render (route? : String → Option ρ) (url : ρ → String)
    (attrs : List (Attr ρ)) (hc : ∀ a ∈ attrs, a.Canonical route? url) (r : List Char) :
    ∀ fuel, attrs.length + 1 ≤ fuel →
      parseAttrs route? fuel (renderAttrs url attrs ++ '>' :: r) = some (attrs, '>' :: r) := by
  induction attrs with
  | nil =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp [renderAttrs, parseAttrs]
  | cons a as ih =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hca : a.Canonical route? url := hc a (by simp)
    have hcas : ∀ b ∈ as, b.Canonical route? url := fun b hb => hc b (by simp [hb])
    have step := ih hcas k (by simp at hf; omega)
    rw [renderAttrs, List.append_assoc, Attr.render_head, parseAttrs]
    simp only [ite_true, takeWhile_append_cons_of_all isNameChar _ (Attr.key_chars a) isNameChar_eq,
      dropWhile_append_cons_of_all isNameChar _ (Attr.key_chars a) isNameChar_eq]
    rw [takeWhile_append_cons_of_all (fun c => decide (c ≠ '"')) _ (escape_all_ne_quot _) (by decide),
      dropWhile_append_cons_of_all (fun c => decide (c ≠ '"')) _ (escape_all_ne_quot _) (by decide)]
    simp only [unescape_escape, String.ofList_toList, Attr.ofKey?_key_value route? url a hca, step]

theorem length_le_renderAttrs (url : ρ → String) (attrs : List (Attr ρ)) :
    attrs.length ≤ (renderAttrs url attrs).length := by
  induction attrs with
  | nil => simp [renderAttrs]
  | cons a as ih => simp [renderAttrs, Attr.render]; omega

/-! ## Shapes of rendered nodes -/

theorem escapeChar_head (c : Char) : ∃ d ds, escapeChar c = d :: ds ∧ d ≠ '<' := by
  unfold escapeChar
  split
  · exact ⟨_, _, rfl, by decide⟩
  split
  · exact ⟨_, _, rfl, by decide⟩
  split
  · exact ⟨_, _, rfl, by decide⟩
  split
  · exact ⟨_, _, rfl, by decide⟩
  · rename_i h1 h2 h3 h4; exact ⟨c, [], rfl, h2⟩

theorem escape_head {s : List Char} (hs : s ≠ []) (r : List Char) :
    ∃ d ds, escape s ++ r = d :: ds ∧ d ≠ '<' := by
  cases s with
  | nil => exact absurd rfl hs
  | cons c cs =>
    obtain ⟨d, ds, hd, hne⟩ := escapeChar_head c
    exact ⟨d, ds ++ (escape cs ++ r), by simp [escape_cons, hd], hne⟩

theorem Tag.name_ne_nil (t : Tag) : t.name.toList ≠ [] := by cases t <;> decide
theorem VoidTag.name_ne_nil (t : VoidTag) : t.name.toList ≠ [] := by cases t <;> decide

theorem name_head_ne_slash {name : List Char} (hne : name ≠ [])
    (hchars : ∀ c ∈ name, isNameChar c = true) (r : List Char) :
    ∃ e es, name ++ r = e :: es ∧ e ≠ '/' := by
  cases name with
  | nil => exact absurd rfl hne
  | cons e es =>
    refine ⟨e, es ++ r, rfl, ?_⟩
    intro h; subst h
    have := hchars '/' (by simp)
    simp [isNameChar_slash] at this

/-- Every canonical node renders either as text (not starting with `<`) or as a tag
(`<` followed by a name character). In particular, never as `</`, never empty. -/
theorem Node.render_shape (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
    (n : Node ρ c) (hc : n.Canonical route? url) (r : List Char) :
    (n.isText = true ∧ ∃ d ds, n.render url ++ r = d :: ds ∧ d ≠ '<') ∨
    (n.isText = false ∧ ∃ e es, n.render url ++ r = '<' :: e :: es ∧ e ≠ '/') := by
  cases n with
  | text h s =>
    left
    exact ⟨rfl, escape_head hc r⟩
  | inline h n =>
    cases n with
    | text h' s => left; exact ⟨rfl, escape_head hc r⟩
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el t h' attrs children =>
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨e, es, he, hne⟩ := name_head_ne_slash (Tag.name_ne_nil t) (Tag.name_chars t)
        (renderAttrs url attrs ++ '>' :: (children.render url ++
          ('<' :: '/' :: t.name.toList ++ ['>']) ++ r))
      refine ⟨e, es, ?_, hne⟩
      simp only [Node.render, Node.isText, Nodes.render, List.cons_append, List.append_assoc] at he ⊢
      rw [he]
    | void t h' attrs =>
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨e, es, he, hne⟩ := name_head_ne_slash (VoidTag.name_ne_nil t) (VoidTag.name_chars t)
        (renderAttrs url attrs ++ '>' :: r)
      refine ⟨e, es, ?_, hne⟩
      simp only [Node.render, Node.isText, List.cons_append, List.append_assoc, List.nil_append] at he ⊢
      rw [he]
  | el t h attrs children =>
    right
    refine ⟨rfl, ?_⟩
    obtain ⟨e, es, he, hne⟩ := name_head_ne_slash (Tag.name_ne_nil t) (Tag.name_chars t)
      (renderAttrs url attrs ++ '>' :: (children.render url ++
        ('<' :: '/' :: t.name.toList ++ ['>']) ++ r))
    refine ⟨e, es, ?_, hne⟩
    simp only [Node.render, List.cons_append, List.append_assoc, List.nil_append] at he ⊢
    rw [he]
  | void t h attrs =>
    right
    refine ⟨rfl, ?_⟩
    obtain ⟨e, es, he, hne⟩ := name_head_ne_slash (VoidTag.name_ne_nil t) (VoidTag.name_chars t)
      (renderAttrs url attrs ++ '>' :: r)
    refine ⟨e, es, ?_, hne⟩
    simp only [Node.render, List.cons_append, List.append_assoc, List.nil_append] at he ⊢
    rw [he]
  | title h s =>
    right
    exact ⟨rfl, 't', 'i' :: 't' :: 'l' :: 'e' :: '>' :: (escape s.toList ++ '<' :: '/' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: r),
      by simp [Node.render], by decide⟩

end Sites.Html

namespace Sites.Html

variable {ρ : Type}

/-! ## Placement lemmas -/

theorem placeText_phrasing (s : String) :
    placeText (ρ := ρ) .phrasing s = some (.text rfl s) := by
  simp [placeText]

theorem placeText_flow (s : String) :
    placeText (ρ := ρ) .flow s = some (.inline rfl (.text rfl s)) := by
  simp [placeText]

theorem placeEl_self (t : Tag) (attrs : List (Attr ρ)) (children : Nodes ρ t.childCtx) :
    placeEl t.ctx t attrs children = some (.el t rfl attrs children) := by
  simp [placeEl]

theorem placeEl_inline (t : Tag) (h : t.ctx = .phrasing) (attrs : List (Attr ρ))
    (children : Nodes ρ t.childCtx) :
    placeEl .flow t attrs children = some (.inline rfl (.el t h attrs children)) := by
  simp [placeEl, h]

/-- A successful placement witnesses `Tag.PlacesIn`. -/
theorem placeEl_placesIn {c : Ctx} {t : Tag} {attrs : List (Attr ρ)} {children : Nodes ρ t.childCtx}
    {n : Node ρ c} (h : placeEl c t attrs children = some n) : t.PlacesIn c := by
  unfold placeEl at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · exact absurd h (by simp)

theorem placeVoid_self (t : VoidTag) (attrs : List (Attr ρ)) :
    placeVoid t.ctx t attrs = some (.void t rfl attrs) := by
  simp [placeVoid]

theorem placeVoid_inline (t : VoidTag) (h : t.ctx = .phrasing) (attrs : List (Attr ρ)) :
    placeVoid .flow t attrs = some (.inline rfl (.void t h attrs)) := by
  simp [placeVoid, h]

/-! ## Per-constructor parsing lemmas -/

theorem takeWhile_escape (s : String) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r, rest = '<' :: r) :
    (escape s.toList ++ rest).takeWhile (fun c => decide (c ≠ '<')) = escape s.toList := by
  rcases hrest with rfl | ⟨r, rfl⟩
  · rw [List.append_nil]; exact takeWhile_of_all _ (escape_all_ne_lt _)
  · exact takeWhile_append_cons_of_all _ _ (escape_all_ne_lt _) (by decide)

theorem dropWhile_escape (s : String) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r, rest = '<' :: r) :
    (escape s.toList ++ rest).dropWhile (fun c => decide (c ≠ '<')) = rest := by
  rcases hrest with rfl | ⟨r, rfl⟩
  · rw [List.append_nil]; exact dropWhile_of_all _ (escape_all_ne_lt _)
  · exact dropWhile_append_cons_of_all _ _ (escape_all_ne_lt _) (by decide)

theorem parseText_render (c : Ctx) (s : String) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r, rest = '<' :: r) (n : Node ρ c) (hn : placeText c s = some n) :
    parseText c (escape s.toList ++ rest) = some (n, rest) := by
  unfold parseText
  simp only [takeWhile_escape s rest hrest, dropWhile_escape s rest hrest, unescape_escape,
    String.ofList_toList, hn]

/-- The text case of `parseNode`. -/
theorem parseNode_text (route? : String → Option ρ) (c : Ctx) (s : String)
    (hs : s.toList ≠ []) (rest : List Char) (hrest : rest = [] ∨ ∃ r, rest = '<' :: r)
    (n : Node ρ c) (hn : placeText c s = some n) (k : Nat) :
    parseNode route? (k + 1) c (escape s.toList ++ rest) = some (n, rest) := by
  obtain ⟨d, ds, hd, hne⟩ := escape_head hs rest
  rw [hd, parseNode]
  simp only [hne, ite_false]
  rw [← hd]
  exact parseText_render c s rest hrest n hn

/-- The element case of `parseNode`, given the children's round trip. -/
theorem parseNode_el (route? : String → Option ρ) (url : ρ → String) (c : Ctx) (t : Tag)
    (attrs : List (Attr ρ)) (children : Nodes ρ t.childCtx)
    (hattrs : ∀ a ∈ attrs, a.Canonical route? url)
    (n : Node ρ c) (hplace : placeEl c t attrs children = some n)
    (rest : List Char) (k : Nat) (hk : attrs.length ≤ k)
    (ih : parseNodes route? k t.childCtx
      (children.render url ++ '<' :: '/' :: (t.name.toList ++ '>' :: rest)) =
        some (children, '<' :: '/' :: (t.name.toList ++ '>' :: rest))) :
    parseNode route? (k + 1) c
      (('<' :: t.name.toList ++ renderAttrs url attrs ++ '>' :: children.render url ++
        '<' :: '/' :: t.name.toList ++ ['>']) ++ rest) = some (n, rest) := by
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  rw [parseNode]
  simp only [ite_true]
  obtain ⟨e, es, he, hne⟩ := renderAttrs_gt_head url attrs
    (children.render url ++ '<' :: '/' :: (t.name.toList ++ '>' :: rest))
  rw [he, takeWhile_append_cons_of_all isNameChar _ (Tag.name_chars t) hne,
    dropWhile_append_cons_of_all isNameChar _ (Tag.name_chars t) hne, ← he]
  simp only [String.ofList_toList, Tag.ofNameIn?_name t c (placeEl_placesIn hplace)]
  rw [parseAttrs_render route? url attrs hattrs _ (k + 1) (by omega)]
  simp only [ih, dropClose_append, hplace]

/-- The void-element case of `parseNode`. -/
theorem parseNode_void (route? : String → Option ρ) (url : ρ → String) (c : Ctx) (t : VoidTag)
    (attrs : List (Attr ρ)) (hattrs : ∀ a ∈ attrs, a.Canonical route? url)
    (n : Node ρ c) (hplace : placeVoid c t attrs = some n)
    (rest : List Char) (k : Nat) (hk : attrs.length ≤ k) :
    parseNode route? (k + 1) c (('<' :: t.name.toList ++ renderAttrs url attrs ++ ['>']) ++ rest) =
      some (n, rest) := by
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  rw [parseNode]
  simp only [ite_true]
  obtain ⟨e, es, he, hne⟩ := renderAttrs_gt_head url attrs rest
  rw [he, takeWhile_append_cons_of_all isNameChar _ (VoidTag.name_chars t) hne,
    dropWhile_append_cons_of_all isNameChar _ (VoidTag.name_chars t) hne, ← he]
  simp only [String.ofList_toList, Tag.ofNameIn?_voidName, VoidTag.ofName?_name]
  rw [parseAttrs_render route? url attrs hattrs _ (k + 1) (by omega)]
  simp only [hplace]

/-- The title case of `parseNode`. -/
theorem parseNode_title (route? : String → Option ρ) (s : String) (rest : List Char) (k : Nat) :
    parseNode route? (k + 1) .head
      (('<' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: escape s.toList ++
        ['<', '/', 't', 'i', 't', 'l', 'e', '>']) ++ rest) = some (.title rfl s, rest) := by
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  rw [parseNode]
  simp only [ite_true]
  have h1 : ('t' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: (escape s.toList ++
      '<' :: '/' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: rest)) =
      ['t', 'i', 't', 'l', 'e'] ++ '>' :: (escape s.toList ++
      '<' :: '/' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: rest) := rfl
  rw [h1, takeWhile_append_cons_of_all isNameChar _ title_chars isNameChar_gt,
    dropWhile_append_cons_of_all isNameChar _ title_chars isNameChar_gt, ofList_title,
    Tag.ofNameIn?_title, VoidTag.ofName?_title]
  simp only [ite_true, parseTitle]
  have h2 : escape s.toList ++ '<' :: '/' :: 't' :: 'i' :: 't' :: 'l' :: 'e' :: '>' :: rest =
      escape s.toList ++ '<' :: '/' :: ("title".toList ++ '>' :: rest) := by
    rw [title_toList]; rfl
  rw [h2, takeWhile_escape s _ (Or.inr ⟨_, rfl⟩), dropWhile_escape s _ (Or.inr ⟨_, rfl⟩)]
  simp only [unescape_escape, String.ofList_toList]
  simp [dropClose]

/-! ## The main theorem -/

mutual
  theorem parseNode_render (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
      (n : Node ρ c) (hc : n.Canonical route? url) (rest : List Char)
      (hrest : n.isText = true → rest = [] ∨ ∃ r, rest = '<' :: r)
      (fuel : Nat) (hf : n.size ≤ fuel) :
      parseNode route? fuel c (n.render url ++ rest) = some (n, rest) := by
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by have := Node.size_pos n; omega⟩
    cases n with
    | text h s =>
      subst h
      exact parseNode_text route? _ s hc rest (hrest rfl) _ (placeText_phrasing s) k
    | inline h n =>
      subst h
      cases n with
      | text h' s =>
        exact parseNode_text route? _ s hc rest (hrest rfl) _ (placeText_flow s) k
      | inline h' _ => exact absurd h' (by decide)
      | title h' _ => exact absurd h' (by decide)
      | el t h' attrs children =>
        have hsz : children.size + attrs.length ≤ k := by
          simp only [Node.size] at hf; omega
        have ih := parseNodes_render route? url children hc.2
          ('<' :: '/' :: (t.name.toList ++ '>' :: rest)) (Or.inr ⟨_, rfl⟩) k
          (by have := Nodes.size_pos children; omega)
        exact parseNode_el route? url _ t attrs children hc.1 _ (placeEl_inline t h' attrs children)
          rest k (by omega) ih
      | void t h' attrs =>
        have hsz : attrs.length ≤ k := by simp only [Node.size] at hf; omega
        exact parseNode_void route? url _ t attrs hc _ (placeVoid_inline t h' attrs) rest k hsz
    | el t h attrs children =>
      subst h
      have hsz : children.size + attrs.length ≤ k := by
        simp only [Node.size] at hf; omega
      have ih := parseNodes_render route? url children hc.2
        ('<' :: '/' :: (t.name.toList ++ '>' :: rest)) (Or.inr ⟨_, rfl⟩) k
        (by have := Nodes.size_pos children; omega)
      exact parseNode_el route? url _ t attrs children hc.1 _ (placeEl_self t attrs children)
        rest k (by omega) ih
    | void t h attrs =>
      subst h
      have hsz : attrs.length ≤ k := by simp only [Node.size] at hf; omega
      exact parseNode_void route? url _ t attrs hc _ (placeVoid_self t attrs) rest k hsz
    | title h s =>
      subst h
      exact parseNode_title route? s rest k

  theorem parseNodes_render (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
      (ns : Nodes ρ c) (hc : ns.Canonical route? url) (rest : List Char)
      (hrest : rest = [] ∨ ∃ r, rest = '<' :: '/' :: r)
      (fuel : Nat) (hf : ns.size ≤ fuel) :
      parseNodes route? fuel c (ns.render url ++ rest) = some (ns, rest) := by
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by have := Nodes.size_pos ns; omega⟩
    cases ns with
    | nil =>
      rcases hrest with rfl | ⟨r, rfl⟩
      · simp [Nodes.render, parseNodes]
      · simp [Nodes.render, parseNodes, startsClose]
    | cons n ns =>
      have hcn : n.Canonical route? url := hc.1
      have hcns : ns.Canonical route? url := hc.2.1
      have htext : n.isText = true → ns.headIsText = false := hc.2.2
      have hsz := Node.size_pos n
      have hsz' := Nodes.size_pos ns
      have hf' : n.size + ns.size ≤ k + 1 := hf
      have hrest' : n.isText = true →
          ns.render url ++ rest = [] ∨ ∃ r, ns.render url ++ rest = '<' :: r := by
        intro ht
        have hh := htext ht
        cases ns with
        | nil =>
          rcases hrest with rfl | ⟨r, rfl⟩
          · left; rfl
          · right; exact ⟨_, rfl⟩
        | cons m ms =>
          simp only [Nodes.headIsText] at hh
          rcases Node.render_shape route? url m hcns.1 (ms.render url ++ rest) with
            ⟨h1, _⟩ | ⟨_, e, es, he, _⟩
          · rw [h1] at hh; exact absurd hh (by decide)
          · right
            refine ⟨e :: es, ?_⟩
            simp only [Nodes.render, List.append_assoc]
            exact he
      have h1 := parseNode_render route? url n hcn (ns.render url ++ rest) hrest' k (by omega)
      have h2 := parseNodes_render route? url ns hcns rest hrest k (by omega)
      rw [parseNodes]
      simp only [Nodes.render, List.append_assoc]
      rcases Node.render_shape route? url n hcn (ns.render url ++ rest) with
        ⟨_, d, ds, hd, hne⟩ | ⟨_, e, es, he, hne⟩
      · rw [hd]
        simp only [List.isEmpty_cons, startsClose_cons_of_ne ds hne, Bool.false_eq_true, ite_false]
        rw [← hd]
        simp only [h1, h2]
      · rw [he]
        simp only [List.isEmpty_cons, startsClose_lt_cons_of_ne es hne, Bool.false_eq_true,
          ite_false]
        rw [← he]
        simp only [h1, h2]
end

end Sites.Html

namespace Sites.Html

variable {ρ : Type}

/-! ## Fuel bounds: the parser's default fuel always suffices -/

theorem length_pos_of_ne_nil' {s : List Char} (h : s ≠ []) : 0 < (escape s).length := by
  cases s with
  | nil => exact absurd rfl h
  | cons c cs =>
    have := escape_ne_nil (c := c) (cs := cs)
    cases h : escape (c :: cs) with
    | nil => exact absurd h this
    | cons _ _ => simp

mutual
  theorem Node.size_le_render (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
      (n : Node ρ c) (hc : n.Canonical route? url) : n.size ≤ (n.render url).length := by
    cases n with
    | text h s =>
      simp only [Node.size, Node.render]
      exact length_pos_of_ne_nil' hc
    | inline h n => exact Node.size_le_render route? url n hc
    | el t h attrs children =>
      have h1 := Nodes.size_le_render route? url children hc.2
      have h2 := length_le_renderAttrs url attrs
      simp only [Node.size, Node.render, List.length_append, List.length_cons]
      omega
    | void t h attrs =>
      have h2 := length_le_renderAttrs url attrs
      simp only [Node.size, Node.render, List.length_append, List.length_cons]
      omega
    | title h s =>
      simp only [Node.size, Node.render, List.length_append, List.length_cons]
      omega
  theorem Nodes.size_le_render (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
      (ns : Nodes ρ c) (hc : ns.Canonical route? url) : ns.size ≤ (ns.render url).length + 1 := by
    cases ns with
    | nil => simp [Nodes.size, Nodes.render]
    | cons n ns =>
      have h1 := Node.size_le_render route? url n hc.1
      have h2 := Nodes.size_le_render route? url ns hc.2.1
      simp only [Nodes.size, Nodes.render, List.length_append]
      omega
end

theorem bodyOpen_close : bodyOpen = '<' :: '/' :: "head><body>".toList := by decide
theorem docSuffix_close : docSuffix = '<' :: '/' :: "body></html>".toList := by decide

theorem dropPrefix_self (pre : List Char) : dropPrefix pre pre = some [] := by
  simpa using dropPrefix_append pre []

/-- **The round-trip theorem.** Parsing the rendering of a canonical document gives it back. -/
public theorem parseDocument_render (route? : String → Option ρ) (url : ρ → String)
    (d : Document ρ) (hc : d.Canonical route? url) :
    parseDocument route? (d.render url) = some d := by
  have hhead := Nodes.size_le_render route? url d.head hc.1
  have hbody := Nodes.size_le_render route? url d.body hc.2
  have hlen : (d.head.render url).length ≤ (d.render url).length ∧
      (d.body.render url).length ≤ (d.render url).length := by
    simp only [Document.render, List.length_append]; omega
  unfold parseDocument
  generalize hfuel : (d.render url).length + 1 = fuel
  unfold parseDocumentWith
  simp only [Document.render, List.append_assoc]
  rw [dropPrefix_append]
  simp only [headOpen, List.cons_append]
  rw [takeWhile_append_cons_of_all _ _ (escape_all_ne_quot _) (by decide),
    dropWhile_append_cons_of_all _ _ (escape_all_ne_quot _) (by decide)]
  simp only [unescape_escape]
  rw [← List.cons_append, dropPrefix_append]
  simp only []
  rw [parseNodes_render route? url d.head hc.1 _
    (Or.inr ⟨"head><body>".toList ++ (d.body.render url ++ docSuffix), by rw [bodyOpen_close]; rfl⟩)
    fuel (by omega)]
  simp only []
  rw [dropPrefix_append]
  simp only []
  rw [parseNodes_render route? url d.body hc.2 docSuffix
    (Or.inr ⟨"body></html>".toList, by rw [docSuffix_close]⟩) fuel (by omega)]
  simp only [dropPrefix_self, String.ofList_toList]

end Sites.Html
