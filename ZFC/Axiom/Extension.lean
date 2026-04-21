/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZFC.Core.Prelim

namespace ZFC
  open Classical
  universe u
  variable {U : Type u}

  /-! ### Introducción de la pertenencia a un conjunto como símbolo primitivo ### -/
  -- Definición axiomática de pertenencia: x pertenece a y
  axiom mem (x y : U) : Prop

  /-! ### Notación estándar de la pertenecia a conjuntos ### -/
  notation:50 lhs:51 " ∈ " rhs:51 => mem lhs rhs

  notation:50 lhs:51 " ∉ " rhs:51 => ¬(lhs ∈ rhs)

  namespace Axiom.Extension
    /-! ### Axioma de Extensionalidad de Conjuntos ### -/
    /-! ### ExtSet : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y ### -/
    @[simp] axiom ExtSet (x y : U): (∀ (z: U), z ∈ x ↔ z ∈ y) → (x = y) --

    @[simp] theorem ExtSetReverse (x y : U) :
      (x = y) → (∀ (z: U), z ∈ x ↔ z ∈ y)
        := by
      intro h_eq
      intro z
      constructor
      · -- Dirección ->
        intro hz_in_x
        rw [h_eq] at hz_in_x
        exact hz_in_x
      · -- Dirección <-
        intro hz_in_y
        rw [← h_eq] at hz_in_y
        exact hz_in_y

    @[simp]
    theorem eq_of_subset_of_subset {x y : U}
      (h_x_subs_y: ∀ (z: U), z ∈ x → z ∈ y)
      (h_y_subs_x: ∀ (z: U), z ∈ y → z ∈ x) :
        (x = y)
          := by
        apply ExtSet
        intro z
        constructor
        · -- Dirección ->
          apply h_x_subs_y
        · -- Dirección <-
          apply h_y_subs_x

    /-! ### Subconjunto (no estricto) ### -/
    @[simp]
    def subset (x y : U) : Prop :=
      ∀ (z: U), z ∈ x → z ∈ y

    /-! ### Notación estándar de subconjunto (no estricto) ### -/
    notation:50 lhs:51 " ⊆ " rhs:51 => subset lhs rhs

    /-! ### Subconjunto propio ### -/
    /-! ### Subset : x ⊆ y ∧ x ≠ y ### -/
    @[simp]
    def ssubset (x y : U) : Prop :=
      (x  ⊆  y) ∧ (x ≠ y)

    /-! ### Notación estándar de subconjunto propio ### -/
    notation:50 lhs:51 " ⊂ " rhs:51 => ssubset lhs rhs

    /-! ### Notación estándar de superconjunto y superconjunto propio ### -/
    notation:50 lhs:51 " ⊇ " rhs:51 => subset rhs lhs

    notation:50 lhs:51 " ⊃ " rhs:51 => ssubset rhs lhs

    /-! ### Teorema de igualdad de conjuntos a través de ser subconjunto uno de otro ### -/
    @[simp]
    theorem subset_antisymm (x y : U) :
      (x ⊆ y) → (y ⊆ x) → (x = y)
        := by
      intro h_xy h_yx
      apply (ExtSet x y)
      intro z
      constructor
      · apply h_xy
      · apply h_yx

    /-! ### 'U' es un Orden Parcial por '⊆' ### -/
    @[simp]
    theorem subset_refl :
      ∀ (x : U), x ⊆ x
        := by
      intro x z h_mem
      exact h_mem

    @[simp]
    theorem subset_trans :
      ∀ (x y z : U), x ⊆ y → y ⊆ z → x ⊆ z
        := by
      intro x y z h_xy h_yz
      intro w h_w_in_x
      apply h_yz
      apply h_xy
      exact h_w_in_x

    @[simp]
    theorem ssubset_asymm :
      ∀ (x y : U), x ⊂ y → ¬(y ⊂ x)
        := by
      intro x y h_subs
      intro h_subs_reverse
      apply h_subs.2
      apply subset_antisymm
      exact h_subs.1
      exact h_subs_reverse.1

    @[simp]
    theorem ssubset_irrefl :
      ∀ (x : U), ¬(x ⊂ x)
        := by
      intro x h_subs
      apply h_subs.2
      rfl

    @[simp] theorem ssubset_trans :
      ∀ (x y z : U), x ⊂ y → y ⊂ z → x ⊂ z
        := by
      intro x y z h_subs_xy h_subs_yz
      constructor
      · apply subset_trans
        exact h_subs_xy.1
        exact h_subs_yz.1
      · intro h_eq
        apply h_subs_xy.2
        apply subset_antisymm
        exact h_subs_xy.1
        rw [h_eq]
        exact h_subs_yz.1

    /-! ### Definición de Conjuntos Disjuntos ### -/
    @[simp]
    def disjoint (x y : U) : Prop :=
      ∀ z, z ∈ x → z ∉ y

    /-! ### Notación estándar de conjuntos disjuntos ### -/
    notation:50 lhs:51 " ⟂ " rhs:51 => disjoint lhs rhs

    /-! ### Simetría de los Conjuntos Disjuntos ### -/
    @[simp]
    theorem disjoint_comm (x y : U) :
      (x ⟂ y) → (y ⟂ x)
        := by
      intro h_disj z h_z_in_y h_z_in_x
      apply h_disj z h_z_in_x
      exact h_z_in_y

    /-! ### Teorema de conjuntos disjuntos (todavía sin notación estándar) ### -/
    @[simp]
    theorem disjoint_elim (x y : U) :
      (x ⟂ y) → (∃ z : U, z ∈ x ∧ z ∈ y) → False
        := by
      intro h_disj h_exists
      cases h_exists with
      | intro z h_z_both =>
        apply h_disj
        exact h_z_both.1
        exact h_z_both.2

    @[simp]
    theorem not_disjoint_of_exists_mem {x y : U} (h_exists :  ∃ (z : U), z ∈ x ∧ z ∈ y) :
      ¬(x ⟂ y)
        := by
      intro h_disj
      apply disjoint_elim
      exact h_disj
      exact h_exists

    @[simp]
    noncomputable def IsTransitive (x : U) : Prop :=
      ∀ (y : U), (y ∈ x) → (y ⊂ x)

    @[simp]
    noncomputable def isEmpty (x : U) : Prop :=
      ∀ y, y ∉ x

    @[simp]
    noncomputable def isNonEmpty (x : U) : Prop :=
      ∃ y, y ∈ x

    @[simp]
    noncomputable def isSingleton (x : U) : Prop :=
      ∃ y, ∀ z, z ∈ x → z = y

    @[simp]
    noncomputable def isPair (x : U) : Prop :=
      ∃ y z, ∀ w, w ∈ x → (w = y ∨ w = z)

    @[simp]
    noncomputable def isBinInter (x y s: U) : Prop :=
      ∀ z, z ∈ x ↔ (z ∈ y ∧ z ∈ s)

    @[simp]
    noncomputable def isBinUnion (x y s: U) : Prop :=
      ∀ z, z ∈ x ↔ (∃ t, t ∈ y ∧ z ∈ t) ∧ (z ∈ s)

    @[simp]
    noncomputable def isBinDiff (x y s: U) : Prop :=
      ∀ z, z ∈ x ↔ (z ∈ y ∧ ¬(z ∈ s))

    @[simp]
    noncomputable def isBinSymDiff (x y s: U) : Prop :=
      ∀ z, z ∈ x ↔ (z ∈ y ∧ z ∉ s) ∨ (z ∉ y ∧ z ∈ s)

    @[simp]
    noncomputable def isUnion (x X: U) : Prop :=
      ∀ (z : U), z ∈ X ↔ ∃ (y : U), z ∈ y ∧ y ∈ x

    @[simp]
    noncomputable def isinter (x X: U) : Prop :=
      ∀ (z: U), z ∈ X ↔ ∀ (y: U), y ∈ x → z ∈ y

  end Axiom.Extension
end ZFC

export ZFC (mem)
export ZFC.Axiom.Extension (
    ExtSet ExtSetReverse eq_of_subset_of_subset subset_antisymm
    subset subset_refl subset_trans
    disjoint disjoint_comm disjoint_elim not_disjoint_of_exists_mem
    ssubset_irrefl ssubset_asymm ssubset_trans
    IsTransitive isEmpty isNonEmpty isSingleton isPair
    isBinInter isBinUnion isBinDiff isBinSymDiff
    isUnion isinter ssubset
)
