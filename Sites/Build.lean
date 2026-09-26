module
public import Std.WP
public import Sites.Site

/-!
# The build pipeline, specified

`writeAll` writes every `(path, content)` pair through an abstract `MonadFS`. Instantiated at
`StateM FS` it is a pure model of the file system, and that model carries a Hoare-triple
specification proven with `vcgen`:

* every listed file ends up on disk with exactly its listed content;
* no other path is touched.

Instantiated at `IO` it is the real build. The two share one definition, so the specification
is about the code that runs.

`Site.build_pages` combines the specification with the HTML round-trip theorem: after a
build, parsing the file written for any route yields that route's normalised document.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace Sites

open Std.WP Lean.Order

@[expose] public section

/-- The file-system operations the build needs. -/
class MonadFS (m : Type → Type) where
  /-- Writes a file at the given path components (relative to the output directory). -/
  writeFile : List String → String → m Unit

/-- A model file system: path components to content. -/
abbrev FS := List String → Option String

/-- The model instance. -/
instance : MonadFS (StateM FS) where
  writeFile p s := modify fun fs q => if q = p then some s else fs q

/-- The real instance, relative to an output directory. -/
instance : MonadFS (ReaderT System.FilePath IO) where
  writeFile p s := do
    let out ← read
    let file := p.foldl (fun acc c => acc / c) out
    if let some parent := file.parent then IO.FS.createDirAll parent
    IO.FS.writeFile file s

/-- Writes every file. -/
def writeAll {m : Type → Type} [Monad m] [MonadFS m] (files : List (List String × String)) :
    m Unit := do
  for f in files do
    MonadFS.writeFile f.1 f.2

/-- The model build, with its contract. `fs₀` names the initial file system and is only used
in the specification. -/
def writeAllModel (fs₀ : FS) (files : List (List String × String)) : StateM FS Unit
    requires fs => fs = fs₀ ∧ (files.map Prod.fst).Nodup
    ensures _ fs =>
      (∀ p s, (p, s) ∈ files → fs p = some s) ∧
      (∀ p, p ∉ files.map Prod.fst → fs p = fs₀ p)
  := do
  for f in files
      invariant pref suff fs =>
        pref ++ suff = files ∧ (files.map Prod.fst).Nodup ∧
        (∀ p s, (p, s) ∈ pref → fs p = some s) ∧
        (∀ p, p ∉ pref.map Prod.fst → fs p = fs₀ p)
    do
    modify fun fs q => if q = f.1 then some f.2 else fs q
where finally
  | spec =>
    all_goals simp_all
    all_goals grind

end

end Sites

namespace Sites

variable {ρ : Type} [DecidableEq ρ]

/-- The annotated model is, definitionally, the generic loop at the model monad. -/
public theorem writeAllModel_eq (fs₀ : FS) (files : List (List String × String)) :
    writeAllModel fs₀ files = (writeAll files : StateM FS Unit) := rfl

/-- The real build: writes every file of the site below `outDir`. -/
public def Site.build (site : Site ρ) (outDir : System.FilePath) : IO Unit :=
  (writeAll site.files : ReaderT System.FilePath IO Unit).run outDir

/-! ## The site's files have distinct paths -/

theorem nodup_map_of_nodup_map {α β γ : Type} {f : α → β} {g : α → γ} {l : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l, f a = f b → g a = g b) (hg : (l.map g).Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hg ⊢
    refine ⟨?_, ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) hg.2⟩
    rintro ⟨a, ha, hfa⟩
    exact hg.1 ⟨a, ha, h a (by simp [ha]) x (by simp) hfa⟩

theorem Path.urlChars_eq_of_file_eq {p q : Path} (h : p.file = q.file) :
    p.urlChars = q.urlChars := by
  simp only [Path.file, List.append_cancel_right_eq] at h
  simp only [Path.urlChars]
  have : ∀ (l : Path), l.map (fun s => s.name.toList ++ ['/']) =
      (l.map Segment.name).map (fun n => n.toList ++ ['/']) := by
    intro l; simp [List.map_map, Function.comp_def]
  rw [this p, this q, h]

theorem Site.files_nodup (site : Site ρ) : (site.files.map Prod.fst).Nodup := by
  simp only [Site.files, List.map_cons, List.map_map, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨r, _, hr⟩ := List.mem_map.mp h
    have := congrArg List.getLast? hr
    simp [Path.file, stylesheetFile] at this
  · refine nodup_map_of_nodup_map ?_ site.urls_nodup
    intro a _ b _ hab
    simp only [Function.comp] at hab
    exact Path.urlChars_eq_of_file_eq hab

/-! ## The end-to-end theorem -/

open Std.WP in
/-- **Building a site writes every page, and every page parses back to its document.**
Stated on the file-system model; the IO build runs the same `writeAll`. -/
public theorem Site.build_pages (site : Site ρ) (fs₀ : FS) :
    ⦃fun fs => fs = fs₀⦄
    writeAllModel fs₀ site.files
    ⦃fun _ fs => ∀ r, fs (site.path r).file = some (site.html r) ∧
      Html.parseDocument site.route? (site.html r).toList =
        some ((site.document r).norm site.route?)⦄ := by
  vcgen
  · exact ⟨‹_›, site.files_nodup⟩
  · rename_i fs h r
    refine ⟨h.1 _ _ ?_, site.parse_html r⟩
    simp only [Site.files, List.mem_cons, List.mem_map]
    exact Or.inr ⟨r, site.routes_complete r, rfl⟩

end Sites
