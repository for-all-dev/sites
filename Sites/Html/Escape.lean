module

/-!
# HTML escaping

Text and attribute values are escaped so that the printed document can never contain a stray
`<`, `>`, `&` or `"`. `unescape` is the exact inverse on the image of `escape`, which is what
the round-trip theorem for the printer needs (`Sites.Html.RoundTrip`).

All functions work on `List Char`; the `String` boundary is handled by the caller.
-/

namespace Sites.Html

@[expose] public section

/-- Escapes one character. Only the four characters that can break markup are rewritten. -/
def escapeChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else [c]

/-- Escapes a character list for use as HTML text or as a double-quoted attribute value. -/
def escape : List Char → List Char
  | [] => []
  | c :: cs => escapeChar c ++ escape cs

/--
Inverse of `escape`. Accepts exactly the four entities `escape` emits and rejects every raw
`&`, `<`, `>` and `"`, so it only succeeds on strings that `escape` could have produced.
-/
def unescape : List Char → Option (List Char)
  | [] => some []
  | c :: cs =>
    if c = '&' then
      match cs with
      | 'a' :: 'm' :: 'p' :: ';' :: cs' => ('&' :: ·) <$> unescape cs'
      | 'l' :: 't' :: ';' :: cs' => ('<' :: ·) <$> unescape cs'
      | 'g' :: 't' :: ';' :: cs' => ('>' :: ·) <$> unescape cs'
      | 'q' :: 'u' :: 'o' :: 't' :: ';' :: cs' => ('"' :: ·) <$> unescape cs'
      | _ => none
    else if c = '<' ∨ c = '>' ∨ c = '"' then none
    else (c :: ·) <$> unescape cs

/-- `true` iff the character is one of the four that `escape` rewrites. -/
def isSpecial (c : Char) : Bool :=
  c = '&' || c = '<' || c = '>' || c = '"'

end

/-! ## Lemmas -/

public theorem escape_nil : escape [] = [] := rfl

public theorem escape_cons (c : Char) (cs : List Char) :
    escape (c :: cs) = escapeChar c ++ escape cs := rfl

public theorem escape_append (a b : List Char) : escape (a ++ b) = escape a ++ escape b := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp [escape_cons, ih]

public theorem escapeChar_of_not_special {c : Char} (h : isSpecial c = false) :
    escapeChar c = [c] := by
  simp [isSpecial] at h
  simp [escapeChar, h]

/-- Every character emitted by `escapeChar` is safe: never `<`, `>` or `"`. -/
public theorem mem_escapeChar {c d : Char} (h : d ∈ escapeChar c) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  by_cases h1 : c = '&'
  · subst h1; simp [escapeChar] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases h2 : c = '<'
  · subst h2; simp [escapeChar] at h; rcases h with rfl | rfl | rfl | rfl <;> decide
  by_cases h3 : c = '>'
  · subst h3; simp [escapeChar] at h; rcases h with rfl | rfl | rfl | rfl <;> decide
  by_cases h4 : c = '"'
  · subst h4; simp [escapeChar] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp [escapeChar, h1, h2, h3, h4] at h; subst h; exact ⟨h2, h3, h4⟩

/-- No `<`, `>` or `"` survives escaping. -/
public theorem mem_escape {s : List Char} {d : Char} (h : d ∈ escape s) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  induction s with
  | nil => simp [escape] at h
  | cons c cs ih =>
    simp only [escape_cons, List.mem_append] at h
    rcases h with h | h
    · exact mem_escapeChar h
    · exact ih h

public theorem not_lt_mem_escape {s : List Char} : '<' ∉ escape s :=
  fun h => (mem_escape h).1 rfl

public theorem not_quot_mem_escape {s : List Char} : '"' ∉ escape s :=
  fun h => (mem_escape h).2.2 rfl

/-- Every character of an escaped string satisfies `· ≠ '<'`, in `Bool` form for `takeWhile`. -/
public theorem escape_all_ne_lt (s : List Char) : ∀ x ∈ escape s, (x ≠ '<' : Bool) = true := by
  intro x hx
  have := (mem_escape hx).1
  simp [this]

/-- Every character of an escaped string satisfies `· ≠ '"'`, in `Bool` form for `takeWhile`. -/
public theorem escape_all_ne_quot (s : List Char) : ∀ x ∈ escape s, (x ≠ '"' : Bool) = true := by
  intro x hx
  have := (mem_escape hx).2.2
  simp [this]

public theorem escapeChar_length_pos (c : Char) : 0 < (escapeChar c).length := by
  unfold escapeChar
  split
  · simp
  split
  · simp
  split
  · simp
  split <;> simp

public theorem escape_ne_nil {c : Char} {cs : List Char} : escape (c :: cs) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [escape_cons, List.length_append, List.length_nil] at this
  have := escapeChar_length_pos c
  omega

public theorem escape_eq_nil_iff {s : List Char} : escape s = [] ↔ s = [] := by
  cases s with
  | nil => simp [escape_nil]
  | cons c cs => simp [escape_ne_nil]

/-- `unescape` undoes `escape`, character by character. -/
public theorem unescape_escape (s : List Char) : unescape (escape s) = some s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    rw [escape_cons]
    by_cases h1 : c = '&'
    · subst h1; simp [escapeChar, unescape, ih]
    by_cases h2 : c = '<'
    · subst h2; simp [escapeChar, unescape, ih]
    by_cases h3 : c = '>'
    · subst h3; simp [escapeChar, unescape, ih]
    by_cases h4 : c = '"'
    · subst h4; simp [escapeChar, unescape, ih]
    · rw [escapeChar_of_not_special (by simp [isSpecial, h1, h2, h3, h4]), List.singleton_append,
        unescape.eq_def]
      simp [h1, h2, h3, h4, ih]

/-- `escape` is injective, as a corollary of `unescape_escape`. -/
public theorem escape_injective : Function.Injective escape := by
  intro a b h
  have := congrArg unescape h
  rw [unescape_escape, unescape_escape] at this
  exact Option.some.inj this

/-! ## Splitting an escaped prefix off a stream

The parser reads text with `takeWhile (· ≠ '<')`. Because `escape` never emits `<`, the
following lemmas let it recover exactly the escaped segment. -/

public theorem takeWhile_append_cons_of_all {α : Type} (p : α → Bool) {l : List α} {c : α}
    (r : List α) (hl : ∀ x ∈ l, p x = true) (hc : p c = false) :
    (l ++ c :: r).takeWhile p = l := by
  induction l with
  | nil => simp [hc]
  | cons x xs ih =>
    have hx : p x = true := hl x (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    simp [hx, this]

public theorem dropWhile_append_cons_of_all {α : Type} (p : α → Bool) {l : List α} {c : α}
    (r : List α) (hl : ∀ x ∈ l, p x = true) (hc : p c = false) :
    (l ++ c :: r).dropWhile p = c :: r := by
  induction l with
  | nil => simp [hc]
  | cons x xs ih =>
    have hx : p x = true := hl x (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    simp [hx, this]

public theorem takeWhile_of_all {α : Type} (p : α → Bool) {l : List α}
    (hl : ∀ x ∈ l, p x = true) : l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := hl x (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    simp [hx, this]

public theorem dropWhile_of_all {α : Type} (p : α → Bool) {l : List α}
    (hl : ∀ x ∈ l, p x = true) : l.dropWhile p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := hl x (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    simp [hx, this]

end Sites.Html
