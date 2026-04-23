/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import Init.Classical
import ZFC.Core.Prelim
import ZFC.Axiom.Extension
import ZFC.Axiom.Existence

namespace ZFC
  open Classical
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Extension
  universe u
  variable {U : Type u}

  namespace Axiom.Specification


    /-! ### Axioma de Especificación, Separación o Comprehensión ### -/
    /-! ### Specification : existe algún conjunto en el universo U que cumple que es subconjunto de otro y que cumple la proposición P ### -/
    @[simp]
    axiom Specification (x : U) (P : U → Prop) :
      ∃ (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)

    /-! ### Teorema de Existencia Única para el Axioma de Especificación ### -/
    /-! ### SpecificationUnique : existe un único conjunto que cumple la especificación P ### -/
    @[simp]
    theorem SpecificationUnique (x : U) (P : U → Prop) :
      ∃! y, ∀ z : U, z ∈ y ↔ (z ∈ x ∧ P z)
        := by
      obtain ⟨y, hy⟩ := Specification x P
      apply ExistsUnique.intro y
      · exact hy
      · -- Unicidad del conjunto especificado
        intro z hz_spec
        apply (ExtSet z y)
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_w_in_y : w ∈ y := by
            apply (hy w).2
            exact (hz_spec w).mp hw_in_z
          exact h_w_in_y
        · -- Dirección <-
          intro hw_in_y
          have h := (hy w).mp hw_in_y
          have h_w_in_x : w ∈ x := h.1
          have h_P_w : P w := h.2
          have h_w_in_z : w ∈ z := by
            apply (hz_spec w).mpr
            exact ⟨h_w_in_x, h_P_w⟩
          exact h_w_in_z

    /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
    @[simp]
    noncomputable def sep (x : U) (P : U → Prop) : U :=
      (SpecificationUnique x P).choose

    @[simp]
    theorem mem_sep_iff (x z : U) (P : U → Prop) :
      z ∈ sep x P ↔ (z ∈ x ∧ P z)
        := by
      exact (SpecificationUnique x P).choose_spec z

    notation " { " x " | " P " } " => sep x P

    /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
    @[simp]
    noncomputable def inter (x y : U) : U :=
      (SpecificationUnique x fun z => z ∈ y).choose

    @[simp]
    theorem mem_inter_iff (x y z : U) :
      z ∈ inter x y ↔ (z ∈ x ∧ z ∈ y)
        := by
      have h := (SpecificationUnique x fun z => z ∈ y).choose_spec
      exact h z

    @[simp]
    theorem inter_unique (x y : U) :
      ∃! z, ∀ w : U, w ∈ z ↔ (w ∈ x ∧ w ∈ y)
        := by
      apply ExistsUnique.intro (inter x y)
      · exact mem_inter_iff x y
      · -- Unicidad del conjunto de intersección binaria
        intro z hz_inter
        apply (ExtSet z (inter x y))
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_both := (hz_inter w).mp hw_in_z
          have h_w_in_x : w ∈ x := h_both.1
          have h_w_in_y : w ∈ y := h_both.2
          exact (mem_inter_iff x y w).mpr ⟨h_w_in_x, h_w_in_y⟩
        · -- Dirección <-
          intro hw_in_bin_inter
          have h_both := (mem_inter_iff x y w).mp hw_in_bin_inter
          exact (hz_inter w).mpr h_both

    /-! ### Notación estándar de conjuntos de la Intersección Binaria ### -/
    notation:50 lhs:51 " ∩ " rhs:51 => inter lhs rhs

    /-! ### Teorema de la Intersección es Subconjunto ### -/
    @[simp]
    theorem inter_subset (x y : U) :
      (x ∩ y) ⊆ x ∧ (x ∩ y) ⊆ y
        := by
      constructor
      · -- Subconjunto de x
        intro z h_z_in_bin_inter
        have h := mem_inter_iff x y z
        exact (h.1 h_z_in_bin_inter).1
      · -- Subconjunto de y
        intro z h_z_in_bin_inter
        have h := mem_inter_iff x y z
        exact (h.1 h_z_in_bin_inter).2

    /-! ### Teorema de la Intersección de Conjuntos Disjuntos es Vacía ### -/
    @[simp]
    theorem inter_eq_empty_iff_disjoint (x y : U) :
      (x ∩ y) = ∅ ↔ (x ⟂ y)
        := by
      constructor
      · -- Dirección ->
        intro h_bin_inter_empty z h_z_in_x h_z_in_y
        have h_bin_inter := mem_inter_iff x y z
        have h_z_in_bin_inter : z ∈ (x ∩ y) := by
          apply h_bin_inter.mpr
          exact ⟨h_z_in_x, h_z_in_y⟩
        apply EmptySet_is_empty z
        rw [← h_bin_inter_empty]
        exact h_z_in_bin_inter
      · -- Dirección <-
        intro h_disj
        apply ExtSet (x ∩ y) ∅
        intro z
        constructor
        · -- Dirección ->
          intro h_z_in_bin_inter
          have h_bin_inter := mem_inter_iff x y z
          have h_both := h_bin_inter.mp h_z_in_bin_inter
          have h_false := h_disj z h_both.1 h_both.2
          exact False.elim h_false
        · -- Dirección <-
          intro h_z_in_empty
          exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem disjoint_of_inter_eq_empty {x y : U} (h_empty : (x ∩ y) = ∅) :
      x ⟂ y
        := by
      exact (inter_eq_empty_iff_disjoint x y).mp h_empty

    @[simp]
    theorem inter_eq_empty_of_disjoint {x y : U} (h_perp : x ⟂ y) :
      (x ∩ y) = ∅
        := by
      exact (inter_eq_empty_iff_disjoint x y).mpr h_perp

    @[simp]
    theorem inter_comm (x y : U) :
      (x ∩ y) = (y ∩ x)
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h := mem_inter_iff x y z
        have h_both := h.mp h_z_in_bin_inter
        exact (mem_inter_iff y x z).mpr ⟨h_both.2, h_both.1⟩
      · -- Dirección <-
        intro h_z_in_bin_inter
        have h := mem_inter_iff y x z
        have h_both := h.mp h_z_in_bin_inter
        exact (mem_inter_iff x y z).mpr ⟨h_both.2, h_both.1⟩

    @[simp]
    theorem inter_assoc (x y z : U) :
      ((x ∩ y) ∩ z) = (x ∩ (y ∩ z))
        := by
      apply ExtSet
      intro w
      constructor
      · -- Dirección ->
        intro h_w_in_bin_inter
        have h_bin_inter := mem_inter_iff (x ∩ y) z w
        have h_both := h_bin_inter.mp h_w_in_bin_inter
        have h_w_in_xy := (mem_inter_iff x y w).mp h_both.1
        have h_w_in_y_inter_z : w ∈ (y ∩ z) := by
          apply (mem_inter_iff y z w).mpr
          exact ⟨h_w_in_xy.2, h_both.2⟩
        have h_w_in_x_inter_yz : w ∈ (x ∩ (y ∩ z)) := by
          apply (mem_inter_iff x (y ∩ z) w).mpr
          exact ⟨h_w_in_xy.1, h_w_in_y_inter_z⟩
        exact h_w_in_x_inter_yz
      · -- Dirección <-
        intro h_w_in_x_inter_yz
        have h_bin_inter := mem_inter_iff x (y ∩ z) w
        have h_both := h_bin_inter.mp h_w_in_x_inter_yz
        have h_w_in_yz : w ∈ (y ∩ z) := h_both.2
        have h_w_in_yz_components := (mem_inter_iff y z w).mp h_w_in_yz
        have h_w_in_x_inter_y : w ∈ (x ∩ y) := by
          apply (mem_inter_iff x y w).mpr
          exact ⟨h_both.1, h_w_in_yz_components.1⟩
        have h_w_in_bin_inter : w ∈ ((x ∩ y) ∩ z) := by
          apply (mem_inter_iff (x ∩ y) z w).mpr
          exact ⟨h_w_in_x_inter_y, h_w_in_yz_components.2⟩
        exact h_w_in_bin_inter

    @[simp]
      theorem inter_empty (x : U) :
      (x ∩ ∅) = ∅
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h_bin_inter := mem_inter_iff x ∅ z
        have h_both := h_bin_inter.mp h_z_in_bin_inter
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_in_empty : z ∈ ∅ := h_both.2
        exact h_z_in_empty
      · -- Dirección <-
        intro h_z_in_empty
        exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem inter_subset_of_subset (x y : U) :
      x ⊆ y → (x ∩ y) ⊆ x
        := by
      intro h_subset z h_z_in_bin_inter
      have h_bin_inter := mem_inter_iff x y z
      have h_both := h_bin_inter.mp h_z_in_bin_inter
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_in_y : z ∈ y := h_both.2
      exact h_z_in_x

    @[simp]
    theorem subset_iff_inter_eq (x y : U) :
      x ⊆ y ↔ (x ∩ y) = x
        := by
      constructor
      · -- Direction: x ⊆ y → (x ∩ y) = x
        intro h_subset
        apply ExtSet
        intro z
        constructor
        · -- z ∈ (x ∩ y) → z ∈ x
          intro h_z_in_inter
          have h_bin_inter := mem_inter_iff x y z
          have h_both := h_bin_inter.mp h_z_in_inter
          exact h_both.1
        · -- z ∈ x → z ∈ (x ∩ y)
          intro h_z_in_x
          have h_z_in_y := h_subset z h_z_in_x
          exact (mem_inter_iff x y z).mpr ⟨h_z_in_x, h_z_in_y⟩
      · -- Direction: (x ∩ y) = x → x ⊆ y
        intro h_eq z h_z_in_x
        have h_z_in_inter : z ∈ (x ∩ y) := by
          rw [h_eq]
          exact h_z_in_x
        have h_bin_inter := mem_inter_iff x y z
        have h_both := h_bin_inter.mp h_z_in_inter
        exact h_both.2

    @[simp]
    theorem inter_empty_right (x : U) :
      (x ∩ ∅) = ∅
        := by
      exact inter_empty x

    @[simp]
    theorem inter_self (x : U) :
      (x ∩ x) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h_bin_inter := mem_inter_iff x x z
        have h_both := h_bin_inter.mp h_z_in_bin_inter
        exact h_both.1
      · -- Dirección <-
        intro h_z_in_x
        exact (mem_inter_iff x x z).mpr ⟨h_z_in_x, h_z_in_x⟩

    /-! ### Definición de la Diferencia de Conjuntos ### -/
    @[simp]
    noncomputable def sdiff (x y : U) : U :=
      (SpecificationUnique x (fun z => z ∉ y)).choose

    /-! ### Notación estándar de la Diferencia de Conjuntos ### -/
    notation:50 lhs:51 " \\ " rhs:51 => sdiff lhs rhs

    @[simp]
    theorem mem_sdiff_iff (x y z : U) :
      z ∈ (x \ y) ↔ (z ∈ x ∧ z ∉ y)
        := by
      have h := (SpecificationUnique x fun z => z ∉ y).choose_spec
      exact h z

    @[simp]
    theorem sdiff_unique (x y : U) :
      ∃! z, ∀ w : U, w ∈ z ↔ (w ∈ x ∧ w ∉ y)
        := by
      apply ExistsUnique.intro (sdiff x y)
      · exact mem_sdiff_iff x y
      · -- Unicidad de la diferencia binaria
        intro z hz_difference
        apply (ExtSet z (sdiff x y))
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_both := (hz_difference w).mp hw_in_z
          have h_w_in_x : w ∈ x := h_both.1
          have h_w_not_in_y : w ∉ y := h_both.2
          exact (mem_sdiff_iff x y w).mpr ⟨h_w_in_x, h_w_not_in_y⟩
        · -- Dirección <-
          intro hw_in_difference
          have h_both := (mem_sdiff_iff x y w).mp hw_in_difference
          exact (hz_difference w).mpr h_both

    @[simp]
    theorem sdiff_subset_left (x y : U) :
      (x \ y) ⊆ x
        := by
      intro z h_z_in_difference
      have h_difference := mem_sdiff_iff x y z
      have h_both := h_difference.mp h_z_in_difference
      exact h_both.1

    @[simp]
    theorem sdiff_eq_empty_iff_subset (x y : U) :
      (x \ y) = ∅ ↔ x ⊆ y := by
      constructor
      · -- Dirección: (x \ y) = ∅ → x ⊆ y
        intro h_empty_diff z h_z_in_x
        -- Queremos demostrar z ∈ y. Usaremos una prueba por contradicción.
        -- Esto es el equivalente en Lean 4 puro de `by_contra h_z_notin_y`.
        apply Classical.byContradiction
        intro h_z_notin_y
        -- Ahora tenemos `h_z_notin_y : z ∉ y` y el objetivo es `False`.
        have h_in_diff : z ∈ (x \ y) := (mem_sdiff_iff x y z).mpr ⟨h_z_in_x, h_z_notin_y⟩
        rw [h_empty_diff] at h_in_diff
        exact EmptySet_is_empty z h_in_diff
      · -- Dirección <-
        intro h_subset
        apply ExtSet
        intro z
        rw [mem_sdiff_iff]
        -- Membership in the empty set is always false
        have h_empty : ∀ x, x ∈ (∅ : U) → False := EmptySet_is_empty
        constructor
        · intro h_in_diff
          have h_z_in_y := h_subset z h_in_diff.left
          -- h_in_diff.right h_z_in_y is False, so z ∈ ∅ is impossible
          exact False.elim (h_in_diff.right h_z_in_y)
        · intro h_false
          exact False.elim (EmptySet_is_empty z h_false)

    @[simp]
    theorem sdiff_empty (x : U) :
      (x \ ∅) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := mem_sdiff_iff x ∅ z
        have h_both := h_difference.mp h_z_in_difference
        exact h_both.1
      · -- Dirección <-
        intro h_z_in_x
        exact (mem_sdiff_iff x ∅ z).mpr ⟨h_z_in_x, fun h_z_in_y => EmptySet_is_empty z h_z_in_y⟩

    @[simp]
    theorem sdiff_self (x : U) :
      (x \ x) = ∅
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := mem_sdiff_iff x x z
        have h_both := h_difference.mp h_z_in_difference
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_not_in_x : z ∉ x := h_both.2
        exact False.elim (h_z_not_in_x h_z_in_x)
      · -- Dirección <-
        intro h_z_in_empty
        exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem sdiff_eq_self_of_disjoint (x : U) {y: U} (h_disjoint : x ⟂ y) :
      (x \ y) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := mem_sdiff_iff x y z
        have h_both := h_difference.mp h_z_in_difference
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_not_in_y : z ∉ y := h_both.2
        exact h_z_in_x
      · -- Dirección <-
        intro h_z_in_x
        have h_z_not_in_y : z ∉ y := h_disjoint z h_z_in_x
        exact (mem_sdiff_iff x y z).mpr ⟨h_z_in_x, h_z_not_in_y⟩

    @[simp]
    theorem sdiff_eq_empty_subset (A B : U) :
      ((A \ B) = (∅ : U)) → ∀ x, x ∈ A → x ∈ B
        := by
    intro h_empty x hx_in_A
    rw [sdiff_eq_empty_iff_subset] at h_empty
    -- Since A \ B = ∅, every x ∈ A must be in B, otherwise x ∈ A \ B ≠ ∅
    have h_sub : ∀ x, x ∈ A → x ∈ B := h_empty
    exact h_sub x hx_in_A

    @[simp]
    theorem subset_of_sdiff_eq_empty (A B : U) (h_empty : (A \ B) = ∅) :
      ∀ x, x ∈ A → x ∈ B
        := by
      intro x hx_in_A
      -- We can use the previous theorem to show this
      exact sdiff_eq_empty_subset A B h_empty x hx_in_A

    @[simp]
    theorem sdiff_eq_empty_of_mem_subset (A B : U) :
      (∀ x, x ∈ A → x ∈ B) → ((A \ B) = (∅ : U))
        := by
      intro h
      apply ExtSet
      intro x
      constructor
      · intro hx
        -- x ∈ A \ B means x ∈ A and x ∉ B
        rw [mem_sdiff_iff] at hx
        have hxA := hx.left
        have hxB := hx.right
        have hAB := h x hxA
        -- But hAB: x ∈ B, contradiction
        exfalso
        exact hxB hAB
      · intro hx_empty
        -- x ∈ ∅ is impossible
        exfalso
        exact EmptySet_is_empty x hx_empty

    @[simp]
    theorem sdiff_eq_empty_of_subset (A B : U) (h_subseteq : ∀ x, x ∈ A → x ∈ B) :
      (A \ B) = (∅ : U)
        := by
      exact sdiff_eq_empty_of_mem_subset A B h_subseteq

  end Axiom.Specification
end ZFC

export ZFC.Axiom.Specification (
    Specification SpecificationUnique sep mem_sep_iff
    inter mem_inter_iff inter_unique
    inter_subset inter_eq_empty_iff_disjoint disjoint_of_inter_eq_empty
    inter_eq_empty_of_disjoint inter_comm
    inter_assoc inter_empty
    inter_subset_of_subset subset_iff_inter_eq
    inter_empty_right inter_self
    sdiff mem_sdiff_iff sdiff_unique
    sdiff_subset_left sdiff_empty
    sdiff_self sdiff_eq_self_of_disjoint
    sdiff_eq_empty_iff_subset
    sdiff_eq_empty_subset subset_of_sdiff_eq_empty sdiff_eq_empty_of_mem_subset sdiff_eq_empty_of_subset
)
