module
public import Sites.Html.Syntax
public import Sites.Html.Render
public import Sites.Html.RoundTrip

/-!
# Normalisation

`norm` turns any tree into a canonical one (see `Sites.Html.RoundTrip`) without changing what
it renders to: empty text nodes are dropped, adjacent text nodes are merged, and `Link.url`s
that name a real route become `Link.route`s.

The build pipeline renders `norm d`, so the round-trip theorem applies to every file it writes.
-/

namespace Sites.Html

variable {ρ : Type}

@[expose] public section

/-- Canonicalises a link: a URL that resolves to a route becomes that route. -/
def Link.norm (route? : String → Option ρ) : Link ρ → Link ρ
  | .url s => match route? s with | some r => .route r | none => .url s
  | .route r => .route r

/-- Canonicalises an attribute's link. -/
def Attr.norm (route? : String → Option ρ) : Attr ρ → Attr ρ
  | .href l => .href (l.norm route?)
  | a => a

/-- The text of a text node (possibly wrapped in `inline`). -/
def Node.textContent? : {c : Ctx} → Node ρ c → Option String
  | _, .text _ s => some s
  | _, .inline _ n => n.textContent?
  | _, _ => none

/-- Replaces the text of a text node; identity on other nodes. -/
def Node.setText : {c : Ctx} → Node ρ c → String → Node ρ c
  | _, .text h _, s => .text h s
  | _, .inline h n, s => .inline h (n.setText s)
  | _, n, _ => n

/-- Prepends a node to a canonical sequence, keeping it canonical: empty text is dropped and
text is merged into a following text node. -/
def Nodes.push {c : Ctx} (n : Node ρ c) (ns : Nodes ρ c) : Nodes ρ c :=
  match n.textContent? with
  | some s =>
    if s.toList = [] then ns
    else
      match ns with
      | .cons m ms =>
        match m.textContent? with
        | some t => .cons (n.setText (s ++ t)) ms
        | none => .cons n ns
      | .nil => .cons n ns
  | none => .cons n ns

mutual
  /-- Canonicalises a node. -/
  def Node.norm (route? : String → Option ρ) : {c : Ctx} → Node ρ c → Node ρ c
    | _, .text h s => .text h s
    | _, .inline h n => .inline h (n.norm route?)
    | _, .el t h attrs children => .el t h (attrs.map (Attr.norm route?)) (children.norm route?)
    | _, .void t h attrs => .void t h (attrs.map (Attr.norm route?))
    | _, .title h s => .title h s
  /-- Canonicalises a sequence. -/
  def Nodes.norm (route? : String → Option ρ) : {c : Ctx} → Nodes ρ c → Nodes ρ c
    | _, .nil => .nil
    | _, .cons n ns => Nodes.push (n.norm route?) (ns.norm route?)
end

/-- Canonicalises a document. -/
def Document.norm (route? : String → Option ρ) (d : Document ρ) : Document ρ :=
  { d with head := d.head.norm route?, body := d.body.norm route? }

/-- `route?` only ever returns a route whose URL is the queried string. -/
def RouteInverse (route? : String → Option ρ) (url : ρ → String) : Prop :=
  ∀ s r, route? s = some r → url r = s

/-- Every route's URL is recognised as that route. -/
def RouteSection (route? : String → Option ρ) (url : ρ → String) : Prop :=
  ∀ r, route? (url r) = some r

end

/-! ## `norm` preserves rendering

This needs `route?` to be a partial inverse of `url`: whenever it recognises a string, the
string is that route's URL. -/

theorem Link.render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) (l : Link ρ) : (l.norm route?).render url = l.render url := by
  cases l with
  | route r => rfl
  | url s =>
    simp only [Link.norm]
    split
    · rename_i r hr; simp [Link.render, hinv s r hr]
    · rfl

theorem Attr.render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) (a : Attr ρ) : (a.norm route?).render url = a.render url := by
  cases a with
  | href l => simp [Attr.norm, Attr.render, Attr.key, Attr.value, Link.render_norm hinv]
  | _ => rfl

theorem renderAttrs_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) (attrs : List (Attr ρ)) :
    renderAttrs url (attrs.map (Attr.norm route?)) = renderAttrs url attrs := by
  induction attrs with
  | nil => rfl
  | cons a as ih => simp [renderAttrs, Attr.render_norm hinv, ih]

theorem Node.render_setText (url : ρ → String) {c : Ctx} (n : Node ρ c) (s t : String)
    (h : n.textContent? = some s) : (n.setText t).render url = escape t.toList := by
  cases n with
  | text _ _ => rfl
  | inline _ n =>
    cases n with
    | text _ _ => rfl
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.textContent?] at h
    | void _ _ _ => simp [Node.textContent?] at h
  | el _ _ _ _ => simp [Node.textContent?] at h
  | void _ _ _ => simp [Node.textContent?] at h
  | title _ _ => simp [Node.textContent?] at h

theorem Node.render_of_textContent (url : ρ → String) {c : Ctx} (n : Node ρ c) (s : String)
    (h : n.textContent? = some s) : n.render url = escape s.toList := by
  cases n with
  | text _ _ => simp [Node.textContent?] at h; subst h; rfl
  | inline _ n =>
    cases n with
    | text _ _ => simp [Node.textContent?] at h; subst h; rfl
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.textContent?] at h
    | void _ _ _ => simp [Node.textContent?] at h
  | el _ _ _ _ => simp [Node.textContent?] at h
  | void _ _ _ => simp [Node.textContent?] at h
  | title _ _ => simp [Node.textContent?] at h

theorem Nodes.render_push (url : ρ → String) {c : Ctx} (n : Node ρ c) (ns : Nodes ρ c) :
    (Nodes.push n ns).render url = n.render url ++ ns.render url := by
  unfold Nodes.push
  split
  · rename_i s hs
    split
    · rename_i hempty
      rw [Node.render_of_textContent url n s hs, hempty]; rfl
    · split
      · rename_i m ms
        split
        · rename_i t ht
          simp only [Nodes.render, Node.render_setText url n s (s ++ t) hs,
            Node.render_of_textContent url n s hs, Node.render_of_textContent url m t ht,
            String.toList_append, escape_append, List.append_assoc]
        · rfl
      · rfl
  · rfl

theorem render_norm_both {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) :
    (∀ {c : Ctx} (n : Node ρ c), (n.norm route?).render url = n.render url) ∧
    (∀ {c : Ctx} (ns : Nodes ρ c), (ns.norm route?).render url = ns.render url) := by
  refine Node.induction ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c h s; rfl
  · intro c h n ih; exact ih
  · intro c t h attrs children ih
    simp only [Node.norm, Node.render, renderAttrs_norm hinv, ih]
  · intro c t h attrs; simp only [Node.norm, Node.render, renderAttrs_norm hinv]
  · intro c h s; rfl
  · intro c; rfl
  · intro c n ns ih1 ih2
    simp only [Nodes.norm, Nodes.render, Nodes.render_push, ih1, ih2]

theorem Node.render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) {c : Ctx} (n : Node ρ c) :
    (n.norm route?).render url = n.render url := (render_norm_both hinv).1 n

theorem Nodes.render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) {c : Ctx} (ns : Nodes ρ c) :
    (ns.norm route?).render url = ns.render url := (render_norm_both hinv).2 ns

public theorem Document.render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) (d : Document ρ) :
    (d.norm route?).render url = d.render url := by
  simp only [Document.norm, Document.render, Nodes.render_norm hinv]

/-! ## `norm` produces canonical trees

This needs `url` to be a section of `route?`: every route's URL resolves to that route. -/

theorem Link.norm_canonical {route? : String → Option ρ} {url : ρ → String}
    (hsec : RouteSection route? url) (l : Link ρ) : (l.norm route?).Canonical route? url := by
  cases l with
  | route r => exact hsec r
  | url s =>
    simp only [Link.norm]
    split
    · rename_i r hr; exact hsec r
    · rename_i hr; exact hr

theorem Attr.norm_canonical {route? : String → Option ρ} {url : ρ → String}
    (hsec : RouteSection route? url) (a : Attr ρ) : (a.norm route?).Canonical route? url := by
  cases a with
  | href l => exact Link.norm_canonical hsec l
  | _ => trivial

theorem Node.isText_norm (route? : String → Option ρ) {c : Ctx} (n : Node ρ c) :
    (n.norm route?).isText = n.isText := by
  cases n with
  | inline h n => simp only [Node.norm, Node.isText]; exact Node.isText_norm route? n
  | _ => rfl

theorem Node.isText_of_textContent {c : Ctx} (n : Node ρ c) (s : String)
    (h : n.textContent? = some s) : n.isText = true := by
  cases n with
  | text _ _ => rfl
  | inline _ n =>
    cases n with
    | text _ _ => rfl
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.textContent?] at h
    | void _ _ _ => simp [Node.textContent?] at h
  | el _ _ _ _ => simp [Node.textContent?] at h
  | void _ _ _ => simp [Node.textContent?] at h
  | title _ _ => simp [Node.textContent?] at h

theorem Node.textContent?_of_isText {c : Ctx} (n : Node ρ c) (h : n.isText = true) :
    ∃ s, n.textContent? = some s := by
  cases n with
  | text _ s => exact ⟨s, rfl⟩
  | inline _ n =>
    cases n with
    | text _ s => exact ⟨s, rfl⟩
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.isText] at h
    | void _ _ _ => simp [Node.isText] at h
  | el _ _ _ _ => simp [Node.isText] at h
  | void _ _ _ => simp [Node.isText] at h
  | title _ _ => simp [Node.isText] at h

theorem Node.setText_canonical (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
    (n : Node ρ c) (s t : String) (h : n.textContent? = some s) (ht : t.toList ≠ []) :
    (n.setText t).Canonical route? url := by
  cases n with
  | text _ _ => exact ht
  | inline _ n =>
    cases n with
    | text _ _ => exact ht
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.textContent?] at h
    | void _ _ _ => simp [Node.textContent?] at h
  | el _ _ _ _ => simp [Node.textContent?] at h
  | void _ _ _ => simp [Node.textContent?] at h
  | title _ _ => simp [Node.textContent?] at h

/-- A text node with nonempty content is canonical. -/
theorem Node.canonical_of_textContent (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
    (n : Node ρ c) (s : String) (h : n.textContent? = some s) (hs : s.toList ≠ []) :
    n.Canonical route? url := by
  cases n with
  | text _ _ => simp [Node.textContent?] at h; subst h; exact hs
  | inline _ n =>
    cases n with
    | text _ _ => simp [Node.textContent?] at h; subst h; exact hs
    | inline h' _ => exact absurd h' (by decide)
    | title h' _ => exact absurd h' (by decide)
    | el _ _ _ _ => simp [Node.textContent?] at h
    | void _ _ _ => simp [Node.textContent?] at h
  | el _ _ _ _ => simp [Node.textContent?] at h
  | void _ _ _ => simp [Node.textContent?] at h
  | title _ _ => simp [Node.textContent?] at h

theorem Nodes.push_canonical (route? : String → Option ρ) (url : ρ → String) {c : Ctx}
    (n : Node ρ c) (ns : Nodes ρ c)
    (hn : n.isText = false → n.Canonical route? url)
    (hns : ns.Canonical route? url) : (Nodes.push n ns).Canonical route? url := by
  unfold Nodes.push
  split
  · rename_i s hs
    split
    · exact hns
    · rename_i hne
      split
      · rename_i m ms
        split
        · rename_i t ht
          refine ⟨Node.setText_canonical route? url n s (s ++ t) hs ?_, hns.2.1, ?_⟩
          · intro h; apply hne
            have := congrArg List.length h
            simp only [String.toList_append, List.length_append, List.length_nil] at this
            exact List.eq_nil_of_length_eq_zero (by omega)
          · intro _; exact hns.2.2 (Node.isText_of_textContent m t ht)
        · rename_i hmt
          refine ⟨Node.canonical_of_textContent route? url n s hs hne, hns, ?_⟩
          intro _
          simp only [Nodes.headIsText]
          cases hm : m.isText with
          | false => rfl
          | true => obtain ⟨t, ht⟩ := Node.textContent?_of_isText m hm; simp [ht] at hmt
      · exact ⟨Node.canonical_of_textContent route? url n s hs hne, trivial, fun _ => rfl⟩
  · rename_i hs
    have hnt : n.isText = false := by
      cases h : n.isText with
      | false => rfl
      | true => obtain ⟨t, ht⟩ := Node.textContent?_of_isText n h; simp [ht] at hs
    exact ⟨hn hnt, hns, fun h => by simp [hnt] at h⟩

theorem norm_canonical_both {route? : String → Option ρ} {url : ρ → String}
    (hsec : RouteSection route? url) :
    (∀ {c : Ctx} (n : Node ρ c), n.isText = false → (n.norm route?).Canonical route? url) ∧
    (∀ {c : Ctx} (ns : Nodes ρ c), (ns.norm route?).Canonical route? url) := by
  refine Node.induction ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c h s hnt; simp [Node.isText] at hnt
  · intro c h n ih hnt
    simp only [Node.isText] at hnt
    exact ih hnt
  · intro c t h attrs children ih _
    refine ⟨?_, ih⟩
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact Attr.norm_canonical hsec b
  · intro c t h attrs _
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact Attr.norm_canonical hsec b
  · intro c h s _; trivial
  · intro c; trivial
  · intro c n ns ih1 ih2
    simp only [Nodes.norm]
    apply Nodes.push_canonical route? url
    · intro h
      rw [Node.isText_norm] at h
      exact ih1 h
    · exact ih2

theorem Nodes.norm_canonical {route? : String → Option ρ} {url : ρ → String}
    (hsec : RouteSection route? url) {c : Ctx} (ns : Nodes ρ c) :
    (ns.norm route?).Canonical route? url := (norm_canonical_both hsec).2 ns

public theorem Document.norm_canonical {route? : String → Option ρ} {url : ρ → String}
    (hsec : RouteSection route? url) (d : Document ρ) :
    (d.norm route?).Canonical route? url :=
  ⟨Nodes.norm_canonical hsec d.head, Nodes.norm_canonical hsec d.body⟩

/-- **Round trip for arbitrary documents.** Parsing the rendering of any document yields its
normal form. -/
public theorem parseDocument_render_norm {route? : String → Option ρ} {url : ρ → String}
    (hinv : RouteInverse route? url) (hsec : RouteSection route? url) (d : Document ρ) :
    parseDocument route? (d.render url) = some (d.norm route?) := by
  rw [← Document.render_norm hinv d]
  exact parseDocument_render route? url _ (Document.norm_canonical hsec d)

end Sites.Html
