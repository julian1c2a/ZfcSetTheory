import Init.Classical

/-!
  Preliminary definitions and theorems for ZFC Set Theory.
  This module provides fundamental structures and lemmas needed for
  Set Theory development without external dependencies.
-/
open Classical
universe u

/-! ### Definition of Unique Existence ### -/
/-! A proposition p has a unique witness when there exists x satisfying p,
    and any y satisfying p must equal x -/
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ### Notation for Unique Existence ### -/
/-! We define the notation ∃! x, p to match the standard Lean notation
    but mapping to our local definition of ExistsUnique -/
syntax "∃! " ident ", " term : term
macro_rules
  | `(∃! $x, $p) => `(ExistsUnique fun $x => $p)

/-! ### Constructor for unique existence ### -/
theorem ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α)
    (hw : p w) (h : ∀ y, p y → y = w) : ExistsUnique p :=
  ⟨w, hw, h⟩

/-! ### Extract existence from unique existence ### -/
theorem ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
  ∃ x, p x := by
  obtain ⟨x, hx, _⟩ := h
  exact ⟨x, hx⟩
/-! ### Extract the unique witness from unique existence ### -/
noncomputable def ExistsUnique.choose {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : α :=
  Classical.choose (ExistsUnique.exists h)

/-! ### The witness satisfies the property ### -/
theorem ExistsUnique.choose_spec {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
  p (h.choose) := by
  obtain ⟨x, hx, _⟩ := h
  exact Classical.choose_spec ⟨x, hx⟩

/-! ### Uniqueness of the witness ### -/
theorem ExistsUnique.unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
  ∀ y, p y → y = h.choose
  := by
  intro y hy
  unfold choose
  have h_exists := ExistsUnique.exists h
  have h_spec := Classical.choose_spec h_exists
  obtain ⟨x, _, hunique⟩ := h
  have h_choose_eq_x : Classical.choose h_exists = x := hunique _ h_spec
  rw [h_choose_eq_x]
  exact hunique y hy
