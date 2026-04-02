/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZfcSetTheory.Core.Prelim
import ZfcSetTheory.Axiom.Extension
import ZfcSetTheory.Axiom.Existence
import ZfcSetTheory.Axiom.Specification
import ZfcSetTheory.Axiom.Pairing
import ZfcSetTheory.Axiom.Union
import ZfcSetTheory.Axiom.PowerSet
import ZfcSetTheory.BoolAlg.PowerSetAlgebra

/-!
# Generalized De Morgan Laws

This file establishes the generalized De Morgan laws for arbitrary families of sets.

## Main Definitions

* `ComplementFamily A F` - The set of complements: { A \ X | X ∈ F }

## Main Theorems

For a family F of subsets of A:
* `inter_complement_eq_complement_union` - ⋂(A∖∖F) = A \ ⋃F
* `union_complement_eq_complement_inter` - ⋃(A∖∖F) = A \ ⋂F (for F ≠ ∅)
-/

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.BoolAlg.PowerSetAlgebra
  universe u
  variable {U : Type u}

  namespace BoolAlg.GenDeMorgan

    /-! ### The Complement Family Operation -/

    /-- The family of complements: { A \ X | X ∈ F } -/
    noncomputable def ComplementFamily (A F : U) : U :=
      sep (𝒫 A) (fun Y => ∃ X, X ∈ F ∧ Y = sdiff A X)

    /-- Specification for ComplementFamily -/
    theorem ComplementFamily_is_specified (A F Y : U) :
        Y ∈ ComplementFamily A F ↔ Y ⊆ A ∧ ∃ X, X ∈ F ∧ Y = sdiff A X := by
      unfold ComplementFamily
      rw [mem_sep_iff, mem_powerset_iff]

    /-- A \ X is in ComplementFamily A F when X ∈ F -/
    theorem complement_mem_ComplementFamily (A F X : U) (hX : X ∈ F) :
        sdiff A X ∈ ComplementFamily A F := by
      rw [ComplementFamily_is_specified]
      constructor
      · intro z hz
        rw [mem_sdiff_iff] at hz
        exact hz.1
      · exact ⟨X, hX, rfl⟩

    /-! ### Characterization of interSet membership -/

    /-- For nonempty F: z ∈ ⋂F iff z is in every member of F -/
    theorem interSet_mem_iff (F z : U) (hF : F ≠ ∅) :
        z ∈ (⋂ F) ↔ ∀ X, X ∈ F → z ∈ X := by
      have h_exists := (nonempty_iff_exists_mem F).mp hF
      unfold interSet
      simp only [dif_pos h_exists]
      rw [mem_sep_iff]
      constructor
      · intro h
        exact h.2
      · intro h_all
        constructor
        · have hy₀ := choose_spec h_exists
          exact h_all (choose h_exists) hy₀
        · exact h_all

    /-! ### First Generalized De Morgan Law -/

    /-- First De Morgan: ⋂(ComplementFamily A F) = A \ ⋃F -/
    theorem inter_complement_eq_complement_union (A F : U)
        (hF_nonempty : F ≠ ∅) (_hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        (⋂ (ComplementFamily A F)) = sdiff A (⋃ F)
        := by
      -- ComplementFamily A F is nonempty
      have hCF_nonempty : ComplementFamily A F ≠ ∅ := by
        have h_ex := (nonempty_iff_exists_mem F).mp hF_nonempty
        let X := choose h_ex
        have hX : X ∈ F := choose_spec h_ex
        intro h_empty
        have h_mem : sdiff A X ∈ ComplementFamily A F := complement_mem_ComplementFamily A F X hX
        rw [h_empty] at h_mem
        exact EmptySet_is_empty (sdiff A X) h_mem
      -- Forward direction: z ∈ ⋂(ComplementFamily A F) → z ∈ A \ ⋃F
      have forward : ∀ z, z ∈ (⋂ (ComplementFamily A F)) → z ∈ sdiff A (⋃ F) := by
        intro z hz
        rw [interSet_mem_iff (ComplementFamily A F) z hCF_nonempty] at hz
        rw [mem_sdiff_iff]
        constructor
        · have h_ex := (nonempty_iff_exists_mem F).mp hF_nonempty
          let X := choose h_ex
          have hX : X ∈ F := choose_spec h_ex
          have h_AX_mem := complement_mem_ComplementFamily A F X hX
          have hz_in_AX := hz (sdiff A X) h_AX_mem
          rw [mem_sdiff_iff] at hz_in_AX
          exact hz_in_AX.1
        · rw [mem_sUnion_iff]
          intro h_ex
          let S := choose h_ex
          have hS : S ∈ F ∧ z ∈ S := choose_spec h_ex
          have h_AS_mem := complement_mem_ComplementFamily A F S hS.1
          have hz_in_AS := hz (sdiff A S) h_AS_mem
          rw [mem_sdiff_iff] at hz_in_AS
          exact hz_in_AS.2 hS.2
      -- Backward direction: z ∈ A \ ⋃F → z ∈ ⋂(ComplementFamily A F)
      have backward : ∀ z, z ∈ sdiff A (⋃ F) → z ∈ (⋂ (ComplementFamily A F)) := by
        intro z hz
        rw [mem_sdiff_iff] at hz
        have hz_in_A := hz.1
        have hz_not_union := hz.2
        rw [interSet_mem_iff (ComplementFamily A F) z hCF_nonempty]
        intro Y hY
        rw [ComplementFamily_is_specified] at hY
        let h_ex := choose hY.2
        have hX_spec : h_ex ∈ F ∧ Y = sdiff A h_ex := choose_spec hY.2
        rw [hX_spec.2, mem_sdiff_iff]
        constructor
        · exact hz_in_A
        · intro hz_in_X
          rw [mem_sUnion_iff] at hz_not_union
          exact hz_not_union ⟨h_ex, hX_spec.1, hz_in_X⟩
      have h_iff : ∀ z, z ∈ (⋂ (ComplementFamily A F)) ↔ z ∈ sdiff A (⋃ F) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (⋂ (ComplementFamily A F)) (sdiff A (⋃ F)) h_iff

    /-! ### Second Generalized De Morgan Law -/

    /-- Second De Morgan: ⋃(ComplementFamily A F) = A \ ⋂F -/
    theorem union_complement_eq_complement_inter (A F : U)
        (hF_nonempty : F ≠ ∅) (_hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        (⋃ (ComplementFamily A F)) = sdiff A (⋂ F) := by
      -- Forward: z ∈ ⋃(ComplementFamily A F) → z ∈ A \ ⋂F
      have forward : ∀ z, z ∈ (⋃ (ComplementFamily A F)) → z ∈ sdiff A (⋂ F) := by
        intro z hz
        rw [mem_sUnion_iff] at hz
        let Y := choose hz
        have hY_spec : Y ∈ ComplementFamily A F ∧ z ∈ Y := choose_spec hz
        rw [ComplementFamily_is_specified] at hY_spec
        let h_ex2 := choose hY_spec.1.2
        have hX_spec : h_ex2 ∈ F ∧ Y = sdiff A h_ex2 := choose_spec hY_spec.1.2
        have hz_in_Y := hY_spec.2
        rw [hX_spec.2, mem_sdiff_iff] at hz_in_Y
        rw [mem_sdiff_iff]
        constructor
        · exact hz_in_Y.1
        · rw [interSet_mem_iff F z hF_nonempty]
          intro h_all
          exact hz_in_Y.2 (h_all h_ex2 hX_spec.1)
      -- Backward: z ∈ A \ ⋂F → z ∈ ⋃(ComplementFamily A F)
      have backward : ∀ z, z ∈ sdiff A (⋂ F) → z ∈ (⋃ (ComplementFamily A F)) := by
        intro z hz
        rw [mem_sdiff_iff] at hz
        have hz_in_A := hz.1
        have hz_not_inter := hz.2
        rw [interSet_mem_iff F z hF_nonempty] at hz_not_inter
        have h_exists : ∃ X, X ∈ F ∧ z ∉ X := by
          apply Classical.byContradiction
          intro h_neg
          apply hz_not_inter
          intro X hX
          apply Classical.byContradiction
          intro hz_not_X
          exact h_neg ⟨X, hX, hz_not_X⟩
        let X := choose h_exists
        have hX_spec : X ∈ F ∧ z ∉ X := choose_spec h_exists
        rw [mem_sUnion_iff]
        exact ⟨sdiff A X, complement_mem_ComplementFamily A F X hX_spec.1,
               (mem_sdiff_iff A X z).mpr ⟨hz_in_A, hX_spec.2⟩⟩
      have h_iff : ∀ z, z ∈ (⋃ (ComplementFamily A F)) ↔ z ∈ sdiff A (⋂ F) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (⋃ (ComplementFamily A F)) (sdiff A (⋂ F)) h_iff

    /-! ### Double Complement Variants -/

    /-- Helper: A \ (A \ B) = B when B ⊆ A -/
    theorem double_complement (A B : U) (hB_sub : B ⊆ A) :
        sdiff A (sdiff A B) = B := by
      have forward : ∀ z, z ∈ sdiff A (sdiff A B) → z ∈ B := by
        intro z hz
        rw [mem_sdiff_iff, mem_sdiff_iff] at hz
        apply Classical.byContradiction
        intro hz_not_B
        exact hz.2 ⟨hz.1, hz_not_B⟩
      have backward : ∀ z, z ∈ B → z ∈ sdiff A (sdiff A B) := by
        intro z hz
        rw [mem_sdiff_iff, mem_sdiff_iff]
        constructor
        · exact hB_sub z hz
        · intro h_diff
          exact h_diff.2 hz
      have h_iff : ∀ z, z ∈ sdiff A (sdiff A B) ↔ z ∈ B :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (sdiff A (sdiff A B)) B h_iff

    /-- Union of subsets is a subset -/
    theorem union_subsets (F A : U) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        (⋃ F) ⊆ A := by
      intro z hz
      rw [mem_sUnion_iff] at hz
      let X := choose hz
      have hX : X ∈ F ∧ z ∈ X := choose_spec hz
      exact hF_subsets X hX.1 z hX.2

    /-- Double complement: A \ ⋂(ComplementFamily A F) = ⋃F -/
    theorem complement_inter_complement_eq_union (A F : U)
        (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        sdiff A (⋂ (ComplementFamily A F)) = ⋃ F := by
      have h_eq := inter_complement_eq_complement_union A F hF_nonempty hF_subsets
      have hUF_sub : ⋃ F ⊆ A := union_subsets F A hF_subsets
      calc sdiff A (⋂ (ComplementFamily A F))
          = sdiff A (sdiff A (⋃ F)) := by rw [h_eq]
        _ = ⋃ F := double_complement A (⋃ F) hUF_sub

    /-- Intersection of subsets of A is a subset of A when F ≠ ∅ -/
    theorem inter_subsets (F A : U) (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        (⋂ F) ⊆ A := by
      intro z hz
      rw [interSet_mem_iff F z hF_nonempty] at hz
      have h_ex := (nonempty_iff_exists_mem F).mp hF_nonempty
      let X := choose h_ex
      have hX : X ∈ F := choose_spec h_ex
      exact hF_subsets X hX z (hz X hX)

    /-- Double complement: A \ ⋃(ComplementFamily A F) = ⋂F -/
    theorem complement_union_complement_eq_inter (A F : U)
        (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
        sdiff A (⋃ (ComplementFamily A F)) = (⋂ F) := by
      have h_eq := union_complement_eq_complement_inter A F hF_nonempty hF_subsets
      have hIF_sub : (⋂ F) ⊆ A := inter_subsets F A hF_nonempty hF_subsets
      calc sdiff A (⋃ (ComplementFamily A F))
          = sdiff A (sdiff A (⋂ F)) := by rw [h_eq]
        _ = (⋂ F) := double_complement A (⋂ F) hIF_sub

  end BoolAlg.GenDeMorgan

  -- Export key theorems
  export BoolAlg.GenDeMorgan (ComplementFamily ComplementFamily_is_specified
    complement_mem_ComplementFamily interSet_mem_iff
    inter_complement_eq_complement_union union_complement_eq_complement_inter
    complement_inter_complement_eq_union complement_union_complement_eq_inter)

end ZFC
