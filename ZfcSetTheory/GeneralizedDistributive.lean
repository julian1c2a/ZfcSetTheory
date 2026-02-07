/-
Copyright (c) 2025. All rights reserved.
Author: ZfcSetTheory project
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.PowerSet
import ZfcSetTheory.PowerSetAlgebra
import ZfcSetTheory.GeneralizedDeMorgan

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

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.PowerSetAlgebra
  open SetUniverse.GeneralizedDeMorgan
  universe u
  variable {U : Type u}

  namespace GeneralizedDistributive

    /-! ### The Intersection Family Operation -/

    /-- The family of intersections: { A ∩ X | X ∈ F } -/
    noncomputable def IntersectFamily (A F : U) : U :=
      SpecSet (𝒫 A) (fun Y => ∃ X, X ∈ F ∧ Y = BinInter A X)

    /-- Specification for IntersectFamily -/
    theorem IntersectFamily_is_specified (A F Y : U) :
        Y ∈ IntersectFamily A F ↔ Y ⊆ A ∧ ∃ X, X ∈ F ∧ Y = BinInter A X := by
      unfold IntersectFamily
      rw [SpecSet_is_specified, PowerSet_is_specified]

    /-- A ∩ X is in IntersectFamily A F when X ∈ F -/
    theorem intersect_mem_IntersectFamily (A F X : U) (hX : X ∈ F) :
        BinInter A X ∈ IntersectFamily A F := by
      rw [IntersectFamily_is_specified]
      constructor
      · intro z hz
        rw [BinInter_is_specified] at hz
        exact hz.1
      · exact ⟨X, hX, rfl⟩

    /-! ### The Union Family Operation -/

    /-- The family of unions: { A ∪ X | X ∈ F } -/
    noncomputable def UnionFamily (A F : U) : U :=
      SpecSet (𝒫 (A ∪ (⋃ F))) (fun Y => ∃ X, X ∈ F ∧ Y = BinUnion A X)

    /-- Specification for UnionFamily -/
    theorem UnionFamily_is_specified (A F Y : U) :
        Y ∈ UnionFamily A F ↔ Y ⊆ BinUnion A (⋃ F) ∧ ∃ X, X ∈ F ∧ Y = BinUnion A X := by
      unfold UnionFamily
      rw [SpecSet_is_specified, PowerSet_is_specified]

    /-- A ∪ X is in UnionFamily A F when X ∈ F -/
    theorem union_mem_UnionFamily (A F X : U) (hX : X ∈ F) :
        BinUnion A X ∈ UnionFamily A F := by
      rw [UnionFamily_is_specified]
      constructor
      · intro z hz
        rw [BinUnion_is_specified] at hz
        rw [BinUnion_is_specified]
        cases hz with
        | inl h => left; exact h
        | inr h =>
          right
          rw [UnionSet_is_specified]
          exact ⟨X, hX, h⟩
      · exact ⟨X, hX, rfl⟩

    /-! ### First Generalized Distributive Law -/

    /-- First Distributive Law: A ∩ (⋃F) = ⋃{A ∩ X | X ∈ F} -/
    theorem inter_distrib_union (A F : U) :
        BinInter A (⋃ F) = (⋃ (IntersectFamily A F)) := by
      -- Forward: z ∈ A ∩ (⋃F) → z ∈ ⋃{A ∩ X | X ∈ F}
      have forward : ∀ z, z ∈ BinInter A (⋃ F) → z ∈ (⋃ (IntersectFamily A F)) := by
        intro z hz
        rw [BinInter_is_specified] at hz
        have hz_A := hz.1
        have hz_UF := hz.2
        rw [UnionSet_is_specified] at hz_UF
        let X := choose hz_UF
        have hX_spec : X ∈ F ∧ z ∈ X := choose_spec hz_UF
        rw [UnionSet_is_specified]
        exact ⟨BinInter A X, intersect_mem_IntersectFamily A F X hX_spec.1,
               (BinInter_is_specified A X z).mpr ⟨hz_A, hX_spec.2⟩⟩
      -- Backward: z ∈ ⋃{A ∩ X | X ∈ F} → z ∈ A ∩ (⋃F)
      have backward : ∀ z, z ∈ (⋃ (IntersectFamily A F)) → z ∈ BinInter A (⋃ F) := by
        intro z hz
        rw [UnionSet_is_specified] at hz
        let Y := choose hz
        have hY_spec : Y ∈ IntersectFamily A F ∧ z ∈ Y := choose_spec hz
        rw [IntersectFamily_is_specified] at hY_spec
        let h_ex := choose hY_spec.1.2
        have hX_spec : h_ex ∈ F ∧ Y = BinInter A h_ex := choose_spec hY_spec.1.2
        have hz_in_Y := hY_spec.2
        rw [hX_spec.2, BinInter_is_specified] at hz_in_Y
        rw [BinInter_is_specified]
        constructor
        · exact hz_in_Y.1
        · rw [UnionSet_is_specified]
          exact ⟨h_ex, hX_spec.1, hz_in_Y.2⟩
      have h_iff : ∀ z, z ∈ BinInter A (⋃ F) ↔ z ∈ (⋃ (IntersectFamily A F)) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (BinInter A (⋃ F)) (⋃ (IntersectFamily A F)) h_iff

    /-! ### IntersectFamily Nonempty When F Nonempty -/

    /-- IntersectFamily A F is nonempty when F is nonempty -/
    theorem IntersectFamily_nonempty (A F : U) (hF : F ≠ ∅) :
        IntersectFamily A F ≠ ∅ := by
      have h_ex := (nonempty_iff_exists_mem F).mp hF
      let X := choose h_ex
      have hX : X ∈ F := choose_spec h_ex
      intro h_empty
      have h_mem : BinInter A X ∈ IntersectFamily A F := intersect_mem_IntersectFamily A F X hX
      rw [h_empty] at h_mem
      exact EmptySet_is_empty (BinInter A X) h_mem

    /-- UnionFamily A F is nonempty when F is nonempty -/
    theorem UnionFamily_nonempty (A F : U) (hF : F ≠ ∅) :
        UnionFamily A F ≠ ∅ := by
      have h_ex := (nonempty_iff_exists_mem F).mp hF
      let X := choose h_ex
      have hX : X ∈ F := choose_spec h_ex
      intro h_empty
      have h_mem : BinUnion A X ∈ UnionFamily A F := union_mem_UnionFamily A F X hX
      rw [h_empty] at h_mem
      exact EmptySet_is_empty (BinUnion A X) h_mem

    /-! ### Second Generalized Distributive Law -/

    /-- Second Distributive Law: A ∪ (⋂F) = ⋂{A ∪ X | X ∈ F} (for F ≠ ∅) -/
    theorem union_distrib_inter (A F : U) (hF : F ≠ ∅) :
        BinUnion A (⋂ F) = (⋂ (UnionFamily A F)) := by
      -- UnionFamily A F is nonempty
      have hUF_nonempty : UnionFamily A F ≠ ∅ := UnionFamily_nonempty A F hF
      -- Forward: z ∈ A ∪ (⋂F) → z ∈ ⋂{A ∪ X | X ∈ F}
      have forward : ∀ z, z ∈ BinUnion A (⋂ F) → z ∈ (⋂ (UnionFamily A F)) := by
        intro z hz
        rw [BinUnion_is_specified] at hz
        rw [interSet_mem_iff (UnionFamily A F) z hUF_nonempty]
        intro Y hY
        rw [UnionFamily_is_specified] at hY
        let X := choose hY.2
        have hX_spec : X ∈ F ∧ Y = BinUnion A X := choose_spec hY.2
        rw [hX_spec.2, BinUnion_is_specified]
        cases hz with
        | inl hz_A => left; exact hz_A
        | inr hz_IF =>
          right
          rw [interSet_mem_iff F z hF] at hz_IF
          exact hz_IF X hX_spec.1
      -- Backward: z ∈ ⋂{A ∪ X | X ∈ F} → z ∈ A ∪ (⋂F)
      have backward : ∀ z, z ∈ (⋂ (UnionFamily A F)) → z ∈ BinUnion A (⋂ F) := by
        intro z hz
        rw [interSet_mem_iff (UnionFamily A F) z hUF_nonempty] at hz
        rw [BinUnion_is_specified]
        -- Either z ∈ A, or z is in every member of F
        by_cases h_zA : z ∈ A
        · left; exact h_zA
        · right
          rw [interSet_mem_iff F z hF]
          intro X hX
          have h_AX_mem : BinUnion A X ∈ UnionFamily A F := union_mem_UnionFamily A F X hX
          have hz_AX := hz (BinUnion A X) h_AX_mem
          rw [BinUnion_is_specified] at hz_AX
          cases hz_AX with
          | inl h => exact absurd h h_zA
          | inr h => exact h
      have h_iff : ∀ z, z ∈ BinUnion A (⋂ F) ↔ z ∈ (⋂ (UnionFamily A F)) :=
        fun z => ⟨forward z, backward z⟩
      exact ExtSet (BinUnion A (⋂ F)) (⋂ (UnionFamily A F)) h_iff

    /-! ### Alternative Forms with Original Family -/

    /-- Alternative: (⋃F) ∩ A = ⋃{X ∩ A | X ∈ F} using commutativity -/
    theorem union_inter_distrib (A F : U) :
        BinInter (⋃ F) A = (⋃ (IntersectFamily A F)) := by
      have h := inter_distrib_union A F
      calc BinInter (⋃ F) A = BinInter A (⋃ F) := BinInter_commutative (⋃ F) A
        _ = (⋃ (IntersectFamily A F)) := h

    /-- Alternative: (⋂F) ∪ A = ⋂{X ∪ A | X ∈ F} using commutativity -/
    theorem inter_union_distrib (A F : U) (hF : F ≠ ∅) :
        BinUnion (⋂ F) A = (⋂ (UnionFamily A F)) := by
      have h := union_distrib_inter A F hF
      calc BinUnion (⋂ F) A = BinUnion A (⋂ F) := BinUnion_comm (⋂ F) A
        _ = (⋂ (UnionFamily A F)) := h

  end GeneralizedDistributive

  -- Export key theorems
  export GeneralizedDistributive (IntersectFamily IntersectFamily_is_specified
    intersect_mem_IntersectFamily UnionFamily UnionFamily_is_specified
    union_mem_UnionFamily IntersectFamily_nonempty UnionFamily_nonempty
    inter_distrib_union union_distrib_inter union_inter_distrib inter_union_distrib)

end SetUniverse
