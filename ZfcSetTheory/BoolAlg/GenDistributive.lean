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
import ZfcSetTheory.BoolAlg.GenDeMorgan

/-!
# Generalized Distributive Laws

This file establishes the generalized distributive laws for arbitrary families of sets.

## Main Definitions

* `IntersectFamily A F` - The set of intersections: { A ∩ X | X ∈ F }
* `UnionFamily A F` - The set of unions: { A ∪ X | X ∈ F }

## Main Theorems

* `inter_distrib_union` - A ∩ (⋃F) = ⋃{A ∩ X | X ∈ F}
* `union_distrib_inter` - A ∪ (⋂F) = ⋂{A ∪ X | X ∈ F} (for F ≠ ∅)
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
  open ZFC.BoolAlg.GenDeMorgan
  universe u
  variable {U : Type u}

  namespace BoolAlg.GenDistributive

    /-! ### The Intersection Family Operation -/

    /-- The family of intersections: { A ∩ X | X ∈ F } -/
    noncomputable def IntersectFamily (A F : U) : U :=
      sep (𝒫 A) (fun Y => ∃ X, X ∈ F ∧ Y = inter A X)

    /-- Specification for IntersectFamily -/
    theorem IntersectFamily_is_specified (A F Y : U) :
        Y ∈ IntersectFamily A F ↔ Y ⊆ A ∧ ∃ X, X ∈ F ∧ Y = inter A X := by
      unfold IntersectFamily
      rw [mem_sep_iff, mem_powerset_iff]

    /-- A ∩ X is in IntersectFamily A F when X ∈ F -/
    theorem intersect_mem_IntersectFamily (A F X : U) (hX : X ∈ F) :
        inter A X ∈ IntersectFamily A F := by
      rw [IntersectFamily_is_specified]
      constructor
      · intro z hz
        rw [mem_inter_iff] at hz
        exact hz.1
      · exact ⟨X, hX, rfl⟩

    /-! ### The Union Family Operation -/

    /-- The family of unions: { A ∪ X | X ∈ F } -/
    noncomputable def UnionFamily (A F : U) : U :=
      sep (𝒫 (A ∪ (⋃ F))) (fun Y => ∃ X, X ∈ F ∧ Y = union A X)

    /-- Specification for UnionFamily -/
    theorem UnionFamily_is_specified (A F Y : U) :
        Y ∈ UnionFamily A F ↔ Y ⊆ union A (⋃ F) ∧ ∃ X, X ∈ F ∧ Y = union A X := by
      unfold UnionFamily
      rw [mem_sep_iff, mem_powerset_iff]

    /-- A ∪ X is in UnionFamily A F when X ∈ F -/
    theorem union_mem_UnionFamily (A F X : U) (hX : X ∈ F) :
        union A X ∈ UnionFamily A F := by
      rw [UnionFamily_is_specified]
      constructor
      · intro z hz
        rw [mem_union_iff] at hz
        rw [mem_union_iff]
        cases hz with
        | inl h => left; exact h
        | inr h =>
          right
          rw [mem_sUnion_iff]
          exact ⟨X, hX, h⟩
      · exact ⟨X, hX, rfl⟩

    /-! ### First Generalized Distributive Law -/

    /-- First Distributive Law: A ∩ (⋃F) = ⋃{A ∩ X | X ∈ F} -/
    theorem inter_distrib_union (A F : U) :
        inter A (⋃ F) = (⋃ (IntersectFamily A F)) := by
      -- Forward: z ∈ A ∩ (⋃F) → z ∈ ⋃{A ∩ X | X ∈ F}
      have forward : ∀ z, z ∈ inter A (⋃ F) → z ∈ (⋃ (IntersectFamily A F)) := by
        intro z hz
        rw [mem_inter_iff] at hz
        have hz_A := hz.1
        have hz_UF := hz.2
        rw [mem_sUnion_iff] at hz_UF
        let X := choose hz_UF
        have hX_spec : X ∈ F ∧ z ∈ X := choose_spec hz_UF
        rw [mem_sUnion_iff]
        exact ⟨inter A X, intersect_mem_IntersectFamily A F X hX_spec.1,
               (mem_inter_iff A X z).mpr ⟨hz_A, hX_spec.2⟩⟩
      -- Backward: z ∈ ⋃{A ∩ X | X ∈ F} → z ∈ A ∩ (⋃F)
      have backward : ∀ z, z ∈ (⋃ (IntersectFamily A F)) → z ∈ inter A (⋃ F) := by
        intro z hz
        rw [mem_sUnion_iff] at hz
        let Y := choose hz
        have hY_spec : Y ∈ IntersectFamily A F ∧ z ∈ Y := choose_spec hz
        rw [IntersectFamily_is_specified] at hY_spec
        let h_ex := choose hY_spec.1.2
        have hX_spec : h_ex ∈ F ∧ Y = inter A h_ex := choose_spec hY_spec.1.2
        have hz_in_Y := hY_spec.2
        rw [hX_spec.2, mem_inter_iff] at hz_in_Y
        rw [mem_inter_iff]
        constructor
        · exact hz_in_Y.1
        · rw [mem_sUnion_iff]
          exact ⟨h_ex, hX_spec.1, hz_in_Y.2⟩
      have h_iff : ∀ z, z ∈ inter A (⋃ F) ↔ z ∈ (⋃ (IntersectFamily A F)) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (inter A (⋃ F)) (⋃ (IntersectFamily A F)) h_iff

    /-! ### IntersectFamily Nonempty When F Nonempty -/

    /-- IntersectFamily A F is nonempty when F is nonempty -/
    theorem IntersectFamily_nonempty (A F : U) (hF : F ≠ ∅) :
        IntersectFamily A F ≠ ∅ := by
      have h_ex := (nonempty_iff_exists_mem F).mp hF
      let X := choose h_ex
      have hX : X ∈ F := choose_spec h_ex
      intro h_empty
      have h_mem : inter A X ∈ IntersectFamily A F := intersect_mem_IntersectFamily A F X hX
      rw [h_empty] at h_mem
      exact EmptySet_is_empty (inter A X) h_mem

    /-- UnionFamily A F is nonempty when F is nonempty -/
    theorem UnionFamily_nonempty (A F : U) (hF : F ≠ ∅) :
        UnionFamily A F ≠ ∅ := by
      have h_ex := (nonempty_iff_exists_mem F).mp hF
      let X := choose h_ex
      have hX : X ∈ F := choose_spec h_ex
      intro h_empty
      have h_mem : union A X ∈ UnionFamily A F := union_mem_UnionFamily A F X hX
      rw [h_empty] at h_mem
      exact EmptySet_is_empty (union A X) h_mem

    /-! ### Second Generalized Distributive Law -/

    /-- Second Distributive Law: A ∪ (⋂F) = ⋂{A ∪ X | X ∈ F} (for F ≠ ∅) -/
    theorem union_distrib_inter (A F : U) (hF : F ≠ ∅) :
        union A (⋂ F) = (⋂ (UnionFamily A F)) := by
      -- UnionFamily A F is nonempty
      have hUF_nonempty : UnionFamily A F ≠ ∅ := UnionFamily_nonempty A F hF
      -- Forward: z ∈ A ∪ (⋂F) → z ∈ ⋂{A ∪ X | X ∈ F}
      have forward : ∀ z, z ∈ union A (⋂ F) → z ∈ (⋂ (UnionFamily A F)) := by
        intro z hz
        rw [mem_union_iff] at hz
        rw [interSet_mem_iff (UnionFamily A F) z hUF_nonempty]
        intro Y hY
        rw [UnionFamily_is_specified] at hY
        let X := choose hY.2
        have hX_spec : X ∈ F ∧ Y = union A X := choose_spec hY.2
        rw [hX_spec.2, mem_union_iff]
        cases hz with
        | inl hz_A => left; exact hz_A
        | inr hz_IF =>
          right
          rw [interSet_mem_iff F z hF] at hz_IF
          exact hz_IF X hX_spec.1
      -- Backward: z ∈ ⋂{A ∪ X | X ∈ F} → z ∈ A ∪ (⋂F)
      have backward : ∀ z, z ∈ (⋂ (UnionFamily A F)) → z ∈ union A (⋂ F) := by
        intro z hz
        rw [interSet_mem_iff (UnionFamily A F) z hUF_nonempty] at hz
        rw [mem_union_iff]
        -- Either z ∈ A, or z is in every member of F
        by_cases h_zA : z ∈ A
        · left; exact h_zA
        · right
          rw [interSet_mem_iff F z hF]
          intro X hX
          have h_AX_mem : union A X ∈ UnionFamily A F := union_mem_UnionFamily A F X hX
          have hz_AX := hz (union A X) h_AX_mem
          rw [mem_union_iff] at hz_AX
          cases hz_AX with
          | inl h => exact absurd h h_zA
          | inr h => exact h
      have h_iff : ∀ z, z ∈ union A (⋂ F) ↔ z ∈ (⋂ (UnionFamily A F)) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (union A (⋂ F)) (⋂ (UnionFamily A F)) h_iff

    /-! ### Alternative Forms with Original Family -/

    /-- Alternative: (⋃F) ∩ A = ⋃{X ∩ A | X ∈ F} using commutativity -/
    theorem union_inter_distrib (A F : U) :
        inter (⋃ F) A = (⋃ (IntersectFamily A F)) := by
      have h := inter_distrib_union A F
      calc inter (⋃ F) A = inter A (⋃ F) := inter_comm (⋃ F) A
        _ = (⋃ (IntersectFamily A F)) := h

    /-- Alternative: (⋂F) ∪ A = ⋂{X ∪ A | X ∈ F} using commutativity -/
    theorem inter_union_distrib (A F : U) (hF : F ≠ ∅) :
        union (⋂ F) A = (⋂ (UnionFamily A F)) := by
      have h := union_distrib_inter A F hF
      calc union (⋂ F) A = union A (⋂ F) := union_comm (⋂ F) A
        _ = (⋂ (UnionFamily A F)) := h

  end BoolAlg.GenDistributive

  -- Export key theorems
  export BoolAlg.GenDistributive (IntersectFamily IntersectFamily_is_specified
    intersect_mem_IntersectFamily UnionFamily UnionFamily_is_specified
    union_mem_UnionFamily IntersectFamily_nonempty UnionFamily_nonempty
    inter_distrib_union union_distrib_inter union_inter_distrib inter_union_distrib)

end ZFC
