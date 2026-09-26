module
public import Sites.Css

/-!
# CSS grammar and the printer's validity theorem

`Grammar.Stylesheet cs` is an inductive predicate describing well-formed CSS text at the
token level: a simplification of the CSS Syntax Module Level 3 core grammar covering the
constructs the printer in `Sites.Css` emits (identifiers, numbers, dimensions, percentages,
hash colours, strings, functions, parenthesised blocks; qualified rules and at-rules).

`Stylesheet.render_grammar` proves that every rendered stylesheet is derivable.
-/

namespace Sites.Css

namespace Grammar

@[expose] public section

/-- Hex digits as the printer emits them (lowercase). -/
def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A nonempty run of decimal digits. -/
inductive Digits : List Char → Prop
  | one (c : Char) (h : c.isDigit = true) : Digits [c]
  | cons (c : Char) (h : c.isDigit = true) (cs : List Char) (hcs : Digits cs) : Digits (c :: cs)

/-- A signed decimal number. -/
inductive Number : List Char → Prop
  | int (ds : List Char) (h : Digits ds) : Number ds
  | neg (ds : List Char) (h : Digits ds) : Number ('-' :: ds)
  | frac (i f : List Char) (hi : Digits i) (hf : Digits f) : Number (i ++ '.' :: f)
  | negFrac (i f : List Char) (hi : Digits i) (hf : Digits f) : Number ('-' :: i ++ '.' :: f)

/-- An identifier token: identifier characters, not starting with a digit. -/
inductive IdentTok : List Char → Prop
  | mk (c : Char) (cs : List Char) (hc : isIdentChar c = true) (hd : c.isDigit = false)
      (hcs : ∀ d ∈ cs, isIdentChar d = true) : IdentTok (c :: cs)

mutual
  /-- A component value. -/
  inductive Token : List Char → Prop
    | ident (s : List Char) (h : IdentTok s) : Token s
    | number (s : List Char) (h : Number s) : Token s
    | dimension (n u : List Char) (hn : Number n) (hu : IdentTok u) : Token (n ++ u)
    | percentage (n : List Char) (hn : Number n) : Token (n ++ ['%'])
    | hash (hs : List Char) (h : ∀ c ∈ hs, isHex c = true) (hne : hs ≠ []) : Token ('#' :: hs)
    | string (s : List Char) (h : ∀ c ∈ s, c ≠ '"' ∧ c ≠ '\\' ∧ c ≠ '\n') :
        Token ('"' :: s ++ ['"'])
    | function (name args : List Char) (hn : IdentTok name) (hargs : Values args) :
        Token (name ++ '(' :: args ++ [')'])
    | block (inner : List Char) (h : Values inner) : Token ('(' :: inner ++ [')'])
    | comma : Token [',']
    | colon : Token [':']
    | space : Token [' ']
  /-- A sequence of component values. -/
  inductive Values : List Char → Prop
    | nil : Values []
    | cons (t ts : List Char) (ht : Token t) (hts : Values ts) : Values (t ++ ts)
end

/-- `name:values;` with a nonempty value. -/
inductive Declaration : List Char → Prop
  | mk (name vals : List Char) (hn : IdentTok name) (hv : Values vals) (hne : vals ≠ []) :
      Declaration (name ++ ':' :: vals ++ [';'])

/-- A sequence of declarations. -/
inductive Declarations : List Char → Prop
  | nil : Declarations []
  | cons (d ds : List Char) (hd : Declaration d) (hds : Declarations ds) : Declarations (d ++ ds)

/-- Subclass selectors: `.c`, `#i`, `:p`, repeated. -/
inductive Subclasses : List Char → Prop
  | nil : Subclasses []
  | cls (i rest : List Char) (hi : IdentTok i) (hr : Subclasses rest) : Subclasses ('.' :: i ++ rest)
  | id (i rest : List Char) (hi : IdentTok i) (hr : Subclasses rest) : Subclasses ('#' :: i ++ rest)
  | pseudo (i rest : List Char) (hi : IdentTok i) (hr : Subclasses rest) :
      Subclasses (':' :: i ++ rest)

/-- A compound selector: optional type or `*`, then subclasses; nonempty overall. -/
inductive Compound : List Char → Prop
  | universal (subs : List Char) (hs : Subclasses subs) : Compound ('*' :: subs)
  | typed (t subs : List Char) (ht : IdentTok t) (hs : Subclasses subs) : Compound (t ++ subs)
  | bare (subs : List Char) (hs : Subclasses subs) (hne : subs ≠ []) : Compound subs

/-- A complex selector: compounds joined by combinators. -/
inductive Complex : List Char → Prop
  | simple (s : List Char) (h : Compound s) : Complex s
  | desc (a b : List Char) (ha : Complex a) (hb : Compound b) : Complex (a ++ ' ' :: b)
  | child (a b : List Char) (ha : Complex a) (hb : Compound b) : Complex (a ++ '>' :: b)

/-- A comma-separated, nonempty selector list. -/
inductive SelectorList : List Char → Prop
  | one (s : List Char) (h : Complex s) : SelectorList s
  | cons (s rest : List Char) (hs : Complex s) (hr : SelectorList rest) :
      SelectorList (s ++ ',' :: rest)

mutual
  /-- A qualified rule or an at-rule. -/
  inductive Rule : List Char → Prop
    | style (sels decls : List Char) (hs : SelectorList sels) (hd : Declarations decls) :
        Rule (sels ++ '{' :: decls ++ ['}'])
    | atRule (name prelude body : List Char) (hn : IdentTok name) (hp : Values prelude)
        (hb : Stylesheet body) : Rule ('@' :: name ++ ' ' :: prelude ++ '{' :: body ++ ['}'])
  /-- A sequence of rules. -/
  inductive Stylesheet : List Char → Prop
    | nil : Stylesheet []
    | cons (r rs : List Char) (hr : Rule r) (hrs : Stylesheet rs) : Stylesheet (r ++ rs)
end

/-- Decidable check for `IdentTok`. -/
def isIdentTok : List Char → Bool
  | [] => false
  | c :: cs => isIdentChar c && !c.isDigit && cs.all isIdentChar

/-- Decidable check for `Digits`. -/
def isDigits (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

end

/-! ## Helpers -/

theorem identTok_of_isIdentTok {s : List Char} (h : isIdentTok s = true) : IdentTok s := by
  cases s with
  | nil => simp [isIdentTok] at h
  | cons c cs =>
    simp only [isIdentTok, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    exact IdentTok.mk c cs h.1.1 h.1.2 h.2

theorem digits_of_isDigits {s : List Char} (h : isDigits s = true) : Digits s := by
  induction s with
  | nil => simp [isDigits] at h
  | cons c cs ih =>
    simp only [isDigits, List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_cons,
      Bool.and_eq_true] at h
    cases cs with
    | nil => exact Digits.one c h.1
    | cons d ds => exact Digits.cons c h.1 _ (ih (by simp [isDigits, h.2]))

theorem Digits.snoc {ds : List Char} (h : Digits ds) {c : Char} (hc : c.isDigit = true) :
    Digits (ds ++ [c]) := by
  induction h with
  | one d hd => exact Digits.cons d hd _ (Digits.one c hc)
  | cons d hd _ _ ih => exact Digits.cons d hd _ ih

theorem Values.single {t : List Char} (h : Token t) : Values t := by
  have := Values.cons t [] h Values.nil
  simpa using this

theorem Values.append {a b : List Char} (ha : Values a) (hb : Values b) : Values (a ++ b) :=
  match ha with
  | .nil => by simpa using hb
  | .cons t ts ht hts => by
    rw [List.append_assoc]; exact Values.cons t _ ht (Values.append hts hb)

theorem Values.spaced {a b : List Char} (ha : Values a) (hb : Values b) :
    Values (a ++ ' ' :: b) :=
  Values.append ha (Values.cons [' '] b Token.space hb)

theorem Number.ne_nil {a : List Char} (h : Number a) : a ≠ [] := by
  cases h with
  | int ds hd => cases hd <;> simp
  | neg => simp
  | frac i f hi => cases hi <;> simp
  | negFrac => simp

/-- A keyword is an identifier token, checked by `decide` on the concrete string. -/
theorem identTok_lit (s : String) (h : isIdentTok s.toList = true) : IdentTok s.toList :=
  identTok_of_isIdentTok h

theorem token_of_ident_lit (s : String) (h : isIdentTok s.toList = true) : Token s.toList :=
  Token.ident _ (identTok_lit s h)

theorem token_of_digits_lit (s : String) (h : isDigits s.toList = true) : Token s.toList :=
  Token.number _ (Number.int _ (digits_of_isDigits h))

theorem keyword_values (s : String) (h : isIdentTok s.toList = true) : Values s.toList :=
  Values.single (token_of_ident_lit s h)

theorem keyword_ne_nil (s : String) (h : isIdentTok s.toList = true) : s.toList ≠ [] := by
  cases hs : s.toList with
  | nil => rw [hs] at h; simp [isIdentTok] at h
  | cons => simp

end Grammar

open Grammar in
theorem digitChar_isDigit (d : Nat) : (digitChar d).isDigit = true := by
  unfold digitChar; split <;> decide

open Grammar in
theorem natDigits_digits (n : Nat) : Digits (natDigits n) := by
  induction n using natDigits.induct with
  | case1 n h => rw [natDigits]; simp only [h, ↓reduceDIte]; exact Digits.one _ (digitChar_isDigit n)
  | case2 n h ih => rw [natDigits]; simp only [h, ↓reduceDIte]; exact ih.snoc (digitChar_isDigit _)

open Grammar in
theorem natDigitsPad_digits (k n : Nat) : Digits (natDigitsPad (k + 1) n) := by
  induction k generalizing n with
  | zero => simp only [natDigitsPad]; exact Digits.one _ (digitChar_isDigit _)
  | succ k ih => rw [natDigitsPad]; exact (ih (n / 10)).snoc (digitChar_isDigit _)

open Grammar in
theorem Decimal.render_number (d : Decimal) : Number d.render := by
  unfold Decimal.render
  simp only []
  by_cases hneg : d.mantissa < 0 <;> by_cases hs : d.scale = 0
  · simp only [hneg, hs, ↓reduceIte, List.nil_append, List.append_nil]
    exact Number.neg _ (natDigits_digits _)
  · simp only [hneg, hs, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k, d.scale = k + 1 := ⟨d.scale - 1, by omega⟩
    rw [hk]
    exact Number.negFrac _ _ (natDigits_digits _) (natDigitsPad_digits _ _)
  · simp only [hneg, hs, ↓reduceIte, List.nil_append, List.append_nil]
    exact Number.int _ (natDigits_digits _)
  · simp only [hneg, hs, ↓reduceIte, List.nil_append]
    obtain ⟨k, hk⟩ : ∃ k, d.scale = k + 1 := ⟨d.scale - 1, by omega⟩
    rw [hk]
    exact Number.frac _ _ (natDigits_digits _) (natDigitsPad_digits _ _)

/-! ## Values -/

open Grammar in
theorem Length.render_token (l : Length) : Token l.render := by
  cases l with
  | px v => exact Token.dimension _ _ v.render_number (identTok_lit "px" (by decide))
  | rem v => exact Token.dimension _ _ v.render_number (identTok_lit "rem" (by decide))
  | em v => exact Token.dimension _ _ v.render_number (identTok_lit "em" (by decide))
  | pct v => exact Token.percentage _ v.render_number
  | vw v => exact Token.dimension _ _ v.render_number (identTok_lit "vw" (by decide))
  | vh v => exact Token.dimension _ _ v.render_number (identTok_lit "vh" (by decide))
  | zero => exact Token.number _ (Number.int _ (Digits.one '0' (by decide)))
  | auto => exact token_of_ident_lit "auto" (by decide)

theorem Length.render_ne_nil (l : Length) : l.render ≠ [] := by
  cases l with
  | px v | rem v | em v | pct v | vw v | vh v =>
    simp only [Length.render, ne_eq, List.append_eq_nil_iff, not_and]; intro; simp
  | zero => simp [Length.render]
  | auto => simp [Length.render]

open Grammar in
theorem hexDigit_isHex (d : Nat) : isHex (hexByte.hexDigit d) = true := by
  unfold hexByte.hexDigit; split <;> decide

open Grammar in
theorem hexByte_hex (v : UInt8) : ∀ c ∈ hexByte v, isHex c = true := by
  intro c hc
  simp only [hexByte, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact hexDigit_isHex _

open Grammar in
theorem NamedColor.render_ident (n : NamedColor) : IdentTok n.render := by
  cases n <;> exact identTok_lit _ (by decide)

open Grammar in
theorem Color.render_values (c : Color) : Values c.render := by
  cases c with
  | hex r g b =>
    apply Values.single
    apply Token.hash
    · intro d hd
      simp only [List.mem_append] at hd
      rcases hd with (hd | hd) | hd <;> exact hexByte_hex _ _ hd
    · simp [hexByte]
  | rgba r g b a =>
    apply Values.single
    have : "rgba(".toList ++ natDigits r.toNat ++ [','] ++ natDigits g.toNat ++ [','] ++
        natDigits b.toNat ++ [','] ++ a.render ++ [')'] =
        "rgba".toList ++ '(' :: (natDigits r.toNat ++ [','] ++ natDigits g.toNat ++ [','] ++
        natDigits b.toNat ++ [','] ++ a.render) ++ [')'] := by simp
    rw [Color.render, this]
    apply Token.function _ _ (identTok_lit "rgba" (by decide))
    refine Values.append (Values.append (Values.append (Values.append (Values.append
      (Values.append (Values.single (Token.number _ (Number.int _ (natDigits_digits _))))
      (Values.single Token.comma))
      (Values.single (Token.number _ (Number.int _ (natDigits_digits _)))))
      (Values.single Token.comma))
      (Values.single (Token.number _ (Number.int _ (natDigits_digits _)))))
      (Values.single Token.comma))
      (Values.single (Token.number _ a.render_number))
  | named n => exact Values.single (Token.ident _ n.render_ident)

theorem Color.render_ne_nil (c : Color) : c.render ≠ [] := by
  cases c with
  | hex => simp [Color.render]
  | rgba => simp [Color.render]
  | named n => cases n <;> simp [Color.render, NamedColor.render]

open Grammar in
theorem FontFamily.render_token (f : FontFamily) : Token f.render := by
  cases f with
  | named n h =>
    apply Token.string
    intro c hc
    have := List.all_eq_true.mp h c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  | _ => exact token_of_ident_lit _ (by decide)

open Grammar in
theorem renderFamilies_values (fs : List FontFamily) : Values (renderFamilies fs) := by
  induction fs with
  | nil => exact Values.nil
  | cons f fs ih =>
    cases fs with
    | nil => exact Values.single f.render_token
    | cons g gs =>
      simp only [renderFamilies]
      exact Values.append (Values.single f.render_token) (Values.cons [','] _ Token.comma ih)

theorem renderFamilies_ne_nil (fs : List FontFamily) (h : fs ≠ []) : renderFamilies fs ≠ [] := by
  cases fs with
  | nil => exact absurd rfl h
  | cons f fs =>
    cases fs with
    | nil =>
      simp only [renderFamilies]
      cases f <;> simp [FontFamily.render]
    | cons g gs => simp only [renderFamilies]; cases f <;> simp [FontFamily.render]

theorem Side.render_all (s : Side) : ∀ c ∈ s.render, isIdentChar c = true := by
  cases s <;> decide

open Grammar in
/-- Property names of the form `prefix-side` are identifiers. -/
theorem identTok_prefix_side (pre : String) (hpre : isIdentTok pre.toList = true) (s : Side) :
    IdentTok (pre.toList ++ s.render) := by
  cases hp : pre.toList with
  | nil => rw [hp] at hpre; simp [isIdentTok] at hpre
  | cons c cs =>
    rw [hp] at hpre
    simp only [isIdentTok, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at hpre
    rw [List.cons_append]
    refine IdentTok.mk c _ hpre.1.1 hpre.1.2 ?_
    intro d hd
    simp only [List.mem_append] at hd
    rcases hd with hd | hd
    · exact hpre.2 d hd
    · exact Side.render_all s d hd

open Grammar in
theorem BorderStyle.render_ident (s : BorderStyle) : IdentTok s.render := by
  cases s <;> exact identTok_lit _ (by decide)

open Grammar in
/-- Every declaration renders to a grammatical declaration. -/
theorem Decl.render_grammar (d : Decl) : Declaration d.render := by
  unfold Decl.render
  cases d with
  | color c | backgroundColor c =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide)) c.render_values c.render_ne_nil
  | margin l | padding l | width l | maxWidth l | minWidth l | height l | minHeight l
  | fontSize l | letterSpacing l | gap l | borderRadius l =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide)) (Values.single l.render_token)
      l.render_ne_nil
  | marginSide s l | paddingSide s l =>
    exact Declaration.mk _ _ (identTok_prefix_side _ (by decide) s) (Values.single l.render_token)
      l.render_ne_nil
  | marginVH v h | paddingVH v h =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (Values.spaced (Values.single v.render_token) (Values.single h.render_token))
      (by simp [Decl.parts])
  | fontFamily fs h =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide)) (renderFamilies_values fs)
      (renderFamilies_ne_nil fs h)
  | fontWeight w =>
    cases w with
    | normal | bold =>
      exact Declaration.mk _ _ (identTok_lit "font-weight" (by decide))
        (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
    | w100 | w200 | w300 | w400 | w500 | w600 | w700 | w800 | w900 =>
      exact Declaration.mk _ _ (identTok_lit "font-weight" (by decide))
        (Values.single (token_of_digits_lit _ (by decide))) (by decide)
  | fontStyleItalic | flexWrap =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide)) (keyword_values _ (by decide))
      (keyword_ne_nil _ (by decide))
  | lineHeight v | opacity v =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (Values.single (Token.number _ v.render_number)) v.render_number.ne_nil
  | textAlign a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | textDecoration a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | textTransform a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | whiteSpace a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | display a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | flexDirection a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | justifyContent a | alignItems a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | listStyle a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | overflowX a | overflowY a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | boxSizing a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | cursor a =>
    cases a <;> exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (keyword_values _ (by decide)) (keyword_ne_nil _ (by decide))
  | border w s c =>
    exact Declaration.mk _ _ (identTok_lit _ (by decide))
      (Values.spaced (Values.spaced (Values.single w.render_token)
        (Values.single (Token.ident _ s.render_ident))) c.render_values)
      (by simp [Decl.parts])
  | borderSide side w s c =>
    exact Declaration.mk _ _ (identTok_prefix_side _ (by decide) side)
      (Values.spaced (Values.spaced (Values.single w.render_token)
        (Values.single (Token.ident _ s.render_ident))) c.render_values)
      (by simp [Decl.parts])

open Grammar in
theorem renderDecls_grammar (ds : List Decl) : Declarations (renderDecls ds) := by
  induction ds with
  | nil => exact Declarations.nil
  | cons d ds ih => exact Declarations.cons _ _ d.render_grammar ih

/-! ## Selectors -/

open Grammar in
theorem Ident.identTok (i : Ident) : IdentTok i.name.toList := by
  obtain ⟨hne, hall, hhead⟩ := i.valid
  cases h : i.name.toList with
  | nil => exact absurd h hne
  | cons c cs =>
    rw [h] at hall hhead
    simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hall
    simp only [List.head?_cons, Option.all_some, Bool.not_eq_eq_eq_not, Bool.not_true] at hhead
    exact IdentTok.mk c cs hall.1 hhead hall.2

open Grammar in
theorem Pseudo.render_ident (p : Pseudo) : IdentTok p.render := by
  cases p <;> exact identTok_lit _ (by decide)

open Grammar in
theorem renderClasses_subclasses (cs : List Ident) (rest : List Char) (hr : Subclasses rest) :
    Subclasses (renderClasses cs ++ rest) := by
  induction cs with
  | nil => simp only [renderClasses, List.nil_append]; exact hr
  | cons c cs ih =>
    simp only [renderClasses, List.cons_append, List.append_assoc]
    exact Subclasses.cls _ _ c.identTok ih

open Grammar in
theorem renderPseudos_subclasses (ps : List Pseudo) : Subclasses (renderPseudos ps) := by
  induction ps with
  | nil => exact Subclasses.nil
  | cons p ps ih =>
    simp only [renderPseudos, List.cons_append]
    exact Subclasses.pseudo _ _ p.render_ident ih

open Grammar in
theorem idPart_subclasses (id : Option Ident) (rest : List Char) (hr : Subclasses rest) :
    Subclasses ((match id with | some i => '#' :: i.name.toList | none => []) ++ rest) := by
  cases id with
  | none => simpa using hr
  | some i => exact Subclasses.id _ _ i.identTok hr

open Grammar in
theorem TypeSel.isIdentTok : ∀ t : TypeSel, isIdentTok t.render = true
  | .html => by decide
  | .body => by decide
  | .tag t => by cases t <;> decide
  | .void v => by cases v <;> decide

open Grammar in
theorem Compound.render_grammar (c : Compound) : Grammar.Compound c.render := by
  have hsubs := renderClasses_subclasses c.classes _
    (idPart_subclasses c.id _ (renderPseudos_subclasses c.pseudos))
  unfold Compound.render
  simp only [List.append_assoc] at hsubs ⊢
  cases ht : c.tag with
  | some t =>
    simp only []
    exact Grammar.Compound.typed _ _ (identTok_of_isIdentTok (TypeSel.isIdentTok t)) hsubs
  | none =>
    simp only []
    split
    · rename_i hempty
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hempty
      obtain ⟨⟨h1, h2⟩, h3⟩ := hempty
      simp only [h1, h2, h3, renderClasses, renderPseudos, List.append_nil, List.cons_append,
        List.nil_append]
      exact Grammar.Compound.universal _ Subclasses.nil
    · rename_i hne
      simp only [List.nil_append]
      apply Grammar.Compound.bare _ hsubs
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none, not_and] at hne
      intro h
      simp only [List.append_eq_nil_iff] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hc : c.classes = [] := by
        cases hc : c.classes with
        | nil => rfl
        | cons x xs => rw [hc] at h1; simp [renderClasses] at h1
      have hi : c.id = none := by
        cases hi : c.id with
        | none => rfl
        | some i => rw [hi] at h2; simp at h2
      have hp : c.pseudos = [] := by
        cases hp : c.pseudos with
        | nil => rfl
        | cons x xs => rw [hp] at h3; simp [renderPseudos] at h3
      exact hne ⟨hc, hi⟩ hp

open Grammar in
theorem Selector.render_grammar (s : Selector) : Complex s.render := by
  induction s with
  | simple c => exact Complex.simple _ c.render_grammar
  | combine a comb b ih =>
    cases comb with
    | descendant => exact Complex.desc _ _ ih b.render_grammar
    | child => exact Complex.child _ _ ih b.render_grammar

open Grammar in
theorem renderSelectors_grammar (ss : List Selector) (h : ss ≠ []) :
    SelectorList (renderSelectors ss) := by
  induction ss with
  | nil => exact absurd rfl h
  | cons s ss ih =>
    cases ss with
    | nil => exact SelectorList.one _ s.render_grammar
    | cons t ts =>
      simp only [renderSelectors]
      exact SelectorList.cons _ _ s.render_grammar (ih (by simp))

/-! ## Rules -/

open Grammar in
theorem maxWidthPrelude (l : Length) :
    Values ('(' :: ("max-width".toList ++ ':' :: l.render) ++ [')']) :=
  Values.single (Token.block _ (Values.append (keyword_values "max-width" (by decide))
    (Values.cons [':'] _ Token.colon (Values.single l.render_token))))

open Grammar in
theorem darkPrelude :
    Values ('(' :: ("prefers-color-scheme".toList ++ ':' :: "dark".toList) ++ [')']) :=
  Values.single (Token.block _ (Values.append (keyword_values "prefers-color-scheme" (by decide))
    (Values.cons [':'] _ Token.colon (keyword_values "dark" (by decide)))))

open Grammar in
theorem mediaMaxWidth_render (l : Length) (rs : List Rule) :
    Rule.render (.mediaMaxWidth l rs) =
      '@' :: "media".toList ++ ' ' :: ('(' :: ("max-width".toList ++ ':' :: l.render) ++ [')']) ++
        '{' :: renderRules rs ++ ['}'] := by
  simp [Rule.render]

open Grammar in
theorem mediaDark_render (rs : List Rule) :
    Rule.render (.mediaDark rs) =
      '@' :: "media".toList ++ ' ' ::
        ('(' :: ("prefers-color-scheme".toList ++ ':' :: "dark".toList) ++ [')']) ++
        '{' :: renderRules rs ++ ['}'] := by
  simp [Rule.render]

open Grammar in
mutual
  theorem Rule.render_grammar (r : Rule) : Grammar.Rule r.render := by
    cases r with
    | style sels decls h =>
      exact Grammar.Rule.style _ _ (renderSelectors_grammar sels h) (renderDecls_grammar decls)
    | mediaMaxWidth l rs =>
      have ih := renderRules_grammar rs
      rw [mediaMaxWidth_render]
      exact Grammar.Rule.atRule _ _ _ (identTok_lit "media" (by decide)) (maxWidthPrelude l) ih
    | mediaDark rs =>
      have ih := renderRules_grammar rs
      rw [mediaDark_render]
      exact Grammar.Rule.atRule _ _ _ (identTok_lit "media" (by decide)) darkPrelude ih
  theorem renderRules_grammar (rs : List Rule) : Grammar.Stylesheet (renderRules rs) := by
    cases rs with
    | nil => exact Grammar.Stylesheet.nil
    | cons r rs =>
      have ih1 := Rule.render_grammar r
      have ih2 := renderRules_grammar rs
      exact Grammar.Stylesheet.cons _ _ ih1 ih2
end

/-- **Every rendered stylesheet is grammatical.** -/
public theorem Stylesheet.render_grammar (s : Stylesheet) :
    Grammar.Stylesheet (s.render.toList) := by
  unfold Stylesheet.render
  rw [String.toList_ofList]
  exact renderRules_grammar s

end Sites.Css
