/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.SetOrder

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.SetOrder
  universe u
  variable {U : Type u}

  namespace SetStrictOrder

    /-! ### Propiedades del Orden Estricto Completas ### -/

    @[simp]
    theorem subset_subseteq (x y : U) :
      x ⊂ y → x ⊆ y := by
      intro h_subs
      exact h_subs.1

    @[simp]
    theorem subseteq_subset_or_eq (x y : U) :
      x ⊆ y → (x ⊂ y ∨ x = y) := by
      intro h_subs
      by_cases h_eq : x = y
      · right; exact h_eq
      · left; exact ⟨h_subs, h_eq⟩

    /-! ### Propiedades de Relación de Orden Estricto ### -/
    @[simp]
    theorem strict_order_irreflexive (x : U) : ¬(x ⊂ x) := by
      intro h_subs
      exact h_subs.2 rfl

    @[simp]
    theorem strict_order_asymmetric (x y : U) : x ⊂ y → ¬(y ⊂ x) := by
      intro h_subs h_subs_reverse
      apply h_subs.2
      apply EqualityOfSubset
      exact h_subs.1
      exact h_subs_reverse.1

    @[simp]
    theorem strict_order_transitive (x y z : U) : x ⊂ y → y ⊂ z → x ⊂ z := by
      intro h_subs_xy h_subs_yz
      constructor
      · apply order_transitive
        exact h_subs_xy.1
        exact h_subs_yz.1
      · intro h_eq
        apply h_subs_xy.2
        apply EqualityOfSubset
        exact h_subs_xy.1
        rw [h_eq]
        exact h_subs_yz.1

    /-! ### Transitividad mixta ### -/
    @[simp]
    theorem subset_transitive_mixed_left (x y z : U) :
      (x ⊆ y) → (y ⊂ z) → (x ⊂ z) := by
      intro h_subs_xy h_subs_yz
      constructor
      · apply order_transitive
        exact h_subs_xy
        exact h_subs_yz.1
      · intro h_eq
        apply h_subs_yz.2
        apply EqualityOfSubset
        exact h_subs_yz.1
        rw [← h_eq]
        exact h_subs_xy

    @[simp]
    theorem subset_transitive_mixed_right (x y z : U) :
      (x ⊂ y) → (y ⊆ z) → (x ⊂ z) := by
      intro h_subs_xy h_subs_yz
      constructor
      · apply order_transitive
        exact h_subs_xy.1
        exact h_subs_yz
      · intro h_eq
        apply h_subs_xy.2
        apply EqualityOfSubset
        exact h_subs_xy.1
        rw [h_eq]
        exact h_subs_yz

    /-! ### Relación entre Orden Parcial y Orden Estricto ### -/
    @[simp]
    theorem partial_to_strict_order (x y : U) :
      (( x ⊆ y ) ∧ ( x ≠ y )) ↔ x ⊂ y
        := by
      constructor
      · intro h
        exact ⟨h.1, h.2⟩
      · intro h_strict
        exact ⟨h_strict.1, h_strict.2⟩

    @[simp]
    theorem strict_implies_partial (x y : U) :
      x ⊂ y → x ⊆ y := subset_subseteq x y

    /-! ### Propiedades adicionales del orden estricto ### -/
    @[simp]
    theorem strict_order_trichotomy_partial (x y : U) :
      x ⊂ y ∨ x = y ∨ y ⊂ x ∨ (¬(x ⊆ y) ∧ ¬(y ⊆ x)) := by
      by_cases h1 : x ⊆ y
      · by_cases h2 : x = y
        · right; left; exact h2
        · left; exact ⟨h1, h2⟩
      · by_cases h3 : y ⊆ x
        · by_cases h4 : y = x
          · right; left; exact h4.symm
          · right; right; left; exact ⟨h3, h4⟩
        · right; right; right; exact ⟨h1, h3⟩

    @[simp]
    theorem empty_strict_subset_nonempty (x : U) :
      x ≠ ∅ → ∅ ⊂ x := by
      intro h_neq
      constructor
      · exact empty_is_minimum x
      · exact h_neq.symm

    @[simp]
    theorem strict_subset_nonempty (x y : U) :
      x ⊂ y → ∃ z, z ∈ y ∧ z ∉ x := by
      intro h_strict
      -- Por contradicción: si no existe tal z, entonces y ⊆ x
      apply Classical.byContradiction
      intro h_not_exists
      -- h_not_exists : ¬∃ z, z ∈ y ∧ z ∉ x
      -- Esto equivale a: ∀ z, z ∈ y → z ∈ x, es decir, y ⊆ x
      have h_y_sub_x : y ⊆ x := by
        intro z hz_in_y
        apply Classical.byContradiction
        intro hz_not_in_x
        exact h_not_exists ⟨z, hz_in_y, hz_not_in_x⟩
      -- Pero entonces x = y por antisimetría, contradiciendo x ⊂ y
      have h_eq := order_antisymmetric x y h_strict.1 h_y_sub_x
      exact h_strict.2 h_eq

  end SetStrictOrder

end SetUniverse

export SetUniverse.SetStrictOrder (
    subset_subseteq subseteq_subset_or_eq
    strict_order_irreflexive strict_order_asymmetric strict_order_transitive
    subset_transitive_mixed_left subset_transitive_mixed_right
    partial_to_strict_order strict_implies_partial
    strict_order_trichotomy_partial empty_strict_subset_nonempty
    strict_subset_nonempty
)
