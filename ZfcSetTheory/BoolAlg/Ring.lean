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
# Boolean Ring Structure on Power Sets

This file establishes that the power set forms a Boolean ring with:
- Addition: symmetric difference (SymDiff)
- Multiplication: intersection

## Main Theorems

### Ring Axioms
* `SymDiff_assoc` - associativity of SymDiff
* `SymDiff_is_comm` - commutativity of SymDiff
* `SymDiff_empty_identity` - SymDiff with empty set
* `SymDiff_inverse` - X SymDiff X = empty

### Boolean Ring Properties
* `SymDiff_inter_distrib` - distributivity of inter over SymDiff
* `inter_idempotent` - X inter X = X

### Formulas
* `SymDiff_eq_union_diff` - SymDiff as union of differences
* `SymDiff_as_complement` - SymDiff using complement (for subsets)
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
  universe u
  variable {U : Type u}

  namespace BooleanRing

    /-! ### Basic SymDiff Properties -/

    /-- SymDiff is commutative -/
    theorem SymDiff_is_comm (X Y : U) :
      SymDiff X Y = SymDiff Y X
      := SymDiff_comm X Y

    /-- SymDiff identity: empty SymDiff X = X -/
    theorem SymDiff_identity_empty (X : U) :
      SymDiff ∅ X = X
      := SymDiff_empty_left X

    /-- SymDiff identity: X SymDiff empty = X -/
    theorem SymDiff_empty_identity (X : U) :
      SymDiff X ∅ = X
      := by
      rw [SymDiff_comm]
      exact SymDiff_empty_left X

    /-- SymDiff inverse -/
    theorem SymDiff_inverse (X : U) :
      SymDiff X X = ∅
      := SymDiff_self X

    /-! ### SymDiff Associativity -/

    /-- SymDiff is associative -/
    theorem SymDiff_assoc (X Y Z : U) :
      SymDiff (SymDiff X Y) Z = SymDiff X (SymDiff Y Z)
      := by
      apply ExtSet
      intro z
      simp only [SymDiff_is_specified]
      constructor
      · intro h
        cases h with
        | inl hXYnotZ =>
          cases hXYnotZ.1 with
          | inl hXnotY =>
            left
            constructor
            · exact hXnotY.1
            · intro hYZ
              cases hYZ with
              | inl hYnotZ => exact hXnotY.2 hYnotZ.1
              | inr hZnotY => exact hXYnotZ.2 hZnotY.1
          | inr hYnotX =>
            right
            constructor
            · left
              exact ⟨hYnotX.1, hXYnotZ.2⟩
            · exact hYnotX.2
        | inr hZnotXY =>
          have hZinZ := hZnotXY.1
          have hNotXY := hZnotXY.2
          by_cases hzX : z ∈ X
          · have hzY : z ∈ Y := Classical.byContradiction fun hzNotY =>
              hNotXY (Or.inl ⟨hzX, hzNotY⟩)
            left
            constructor
            · exact hzX
            · intro hYZ
              cases hYZ with
              | inl hYnotZ => exact hYnotZ.2 hZinZ
              | inr hZnotY => exact hZnotY.2 hzY
          · by_cases hzY : z ∈ Y
            · exact absurd (Or.inr ⟨hzY, hzX⟩) hNotXY
            · right
              constructor
              · right
                exact ⟨hZinZ, hzY⟩
              · exact hzX
      · intro h
        cases h with
        | inl hXnotYZ =>
          have hzX := hXnotYZ.1
          have hNotYZ := hXnotYZ.2
          by_cases hzY : z ∈ Y
          · have hzZ : z ∈ Z := Classical.byContradiction fun hzNotZ =>
              hNotYZ (Or.inl ⟨hzY, hzNotZ⟩)
            right
            constructor
            · exact hzZ
            · intro hXY
              cases hXY with
              | inl hXnotY => exact hXnotY.2 hzY
              | inr hYnotX => exact hYnotX.2 hzX
          · by_cases hzZ : z ∈ Z
            · exact absurd (Or.inr ⟨hzZ, hzY⟩) hNotYZ
            · left
              constructor
              · left
                exact ⟨hzX, hzY⟩
              · exact hzZ
        | inr hYZnotX =>
          have hzNotX := hYZnotX.2
          cases hYZnotX.1 with
          | inl hYnotZ =>
            left
            constructor
            · right
              exact ⟨hYnotZ.1, hzNotX⟩
            · exact hYnotZ.2
          | inr hZnotY =>
            right
            constructor
            · exact hZnotY.1
            · intro hXY
              cases hXY with
              | inl hXnotY => exact hzNotX hXnotY.1
              | inr hYnotX => exact hZnotY.2 hYnotX.1

    /-! ### Distributivity of Intersection over SymDiff -/

    /-- Distributivity of inter over SymDiff -/
    theorem SymDiff_inter_distrib (X Y Z : U) :
        BinInter X (SymDiff Y Z) = SymDiff (BinInter X Y) (BinInter X Z)
        := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [BinInter_is_specified] at hw
        have hwX := hw.1
        have hwYZ := hw.2
        rw [SymDiff_is_specified] at hwYZ
        rw [SymDiff_is_specified]
        cases hwYZ with
        | inl hYnotZ =>
          left
          rw [BinInter_is_specified, BinInter_is_specified]
          constructor
          · exact ⟨hwX, hYnotZ.1⟩
          · intro hXZ
            exact hYnotZ.2 hXZ.2
        | inr hZnotY =>
          right
          rw [BinInter_is_specified, BinInter_is_specified]
          constructor
          · exact ⟨hwX, hZnotY.1⟩
          · intro hXY
            exact hZnotY.2 hXY.2
      · intro hw
        rw [SymDiff_is_specified] at hw
        rw [BinInter_is_specified, SymDiff_is_specified]
        cases hw with
        | inl hXYnotXZ =>
          rw [BinInter_is_specified] at hXYnotXZ
          have hwXY := hXYnotXZ.1
          have hwX := hwXY.1
          have hwY := hwXY.2
          have hNotXZ := hXYnotXZ.2
          constructor
          · exact hwX
          · left
            constructor
            · exact hwY
            · intro hwZ
              rw [BinInter_is_specified] at hNotXZ
              exact hNotXZ ⟨hwX, hwZ⟩
        | inr hXZnotXY =>
          rw [BinInter_is_specified] at hXZnotXY
          have hwXZ := hXZnotXY.1
          have hwX := hwXZ.1
          have hwZ := hwXZ.2
          have hNotXY := hXZnotXY.2
          constructor
          · exact hwX
          · right
            constructor
            · exact hwZ
            · intro hwY
              rw [BinInter_is_specified] at hNotXY
              exact hNotXY ⟨hwX, hwY⟩

    /-- Right distributivity of inter over SymDiff -/
    theorem SymDiff_inter_distrib_right (X Y Z : U) :
        BinInter (SymDiff Y Z) X = SymDiff (BinInter Y X) (BinInter Z X)
        := by
      rw [BinInter_commutative, BinInter_commutative Y, BinInter_commutative Z]
      exact SymDiff_inter_distrib X Y Z

    /-! ### SymDiff Closure in PowerSet -/

    /-- SymDiff of subsets is a subset -/
    theorem SymDiff_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
        SymDiff X Y ∈ 𝒫 A
        := by
      rw [PowerSet_is_specified] at hX hY ⊢
      intro z hz
      rw [SymDiff_is_specified] at hz
      cases hz with
      | inl hXnotY => exact hX z hXnotY.1
      | inr hYnotX => exact hY z hYnotX.1

    /-! ### Alternative Characterizations -/

    /-- SymDiff as union of differences -/
    theorem SymDiff_eq_union_diff (X Y : U) :
      SymDiff X Y = BinUnion (X \ Y) (Y \ X)
      := by
      apply ExtSet
      intro z
      simp only [SymDiff_is_specified, BinUnion_is_specified, Difference_is_specified]

    /-- For subsets of A: SymDiff expressed using complement -/
    theorem SymDiff_as_complement (A X Y : U) (hX : X ⊆ A) (hY : Y ⊆ A) :
        SymDiff X Y = BinInter (BinUnion X Y) ((BinInter X Y)^∁[ A ])
        := by
      apply ExtSet
      intro z
      constructor
      · intro h
        rw [SymDiff_is_specified] at h
        rw [BinInter_is_specified, BinUnion_is_specified, Complement_is_specified,
            BinInter_is_specified]
        cases h with
        | inl hXnotY =>
          constructor
          · left; exact hXnotY.1
          · constructor
            · exact hX z hXnotY.1
            · intro hXY
              exact hXnotY.2 hXY.2
        | inr hYnotX =>
          constructor
          · right; exact hYnotX.1
          · constructor
            · exact hY z hYnotX.1
            · intro hXY
              exact hYnotX.2 hXY.1
      · intro h
        rw [BinInter_is_specified, BinUnion_is_specified, Complement_is_specified,
            BinInter_is_specified] at h
        have hUnion := h.1
        have hzA := h.2.1
        have hNotInter := h.2.2
        rw [SymDiff_is_specified]
        cases hUnion with
        | inl hzX =>
          by_cases hzY : z ∈ Y
          · exact absurd ⟨hzX, hzY⟩ hNotInter
          · left; exact ⟨hzX, hzY⟩
        | inr hzY =>
          by_cases hzX : z ∈ X
          · exact absurd ⟨hzX, hzY⟩ hNotInter
          · right; exact ⟨hzY, hzX⟩

    /-! ### Additional Properties -/

    /-- SymDiff X Y = X is equivalent to Y = empty -/
    theorem SymDiff_eq_self_iff_empty (X Y : U) : SymDiff X Y = X ↔ Y = ∅ := by
      constructor
      · intro h
        apply ExtSet
        intro z
        constructor
        · intro hzY
          by_cases hzX : z ∈ X
          · have hNotSymDiff : z ∉ SymDiff X Y := by
              rw [SymDiff_is_specified]
              intro hSymDiff
              cases hSymDiff with
              | inl hXnotY => exact hXnotY.2 hzY
              | inr hYnotX => exact hYnotX.2 hzX
            rw [h] at hNotSymDiff
            exact absurd hzX hNotSymDiff
          · have hInSymDiff : z ∈ SymDiff X Y := by
              rw [SymDiff_is_specified]
              right
              exact ⟨hzY, hzX⟩
            rw [h] at hInSymDiff
            exact absurd hInSymDiff hzX
        · intro hz
          exact absurd hz (EmptySet_is_empty z)
      · intro hY
        rw [hY]
        exact SymDiff_empty_identity X

  end BooleanRing

end SetUniverse

export SetUniverse.BooleanRing (
    SymDiff_is_comm
    SymDiff_empty_identity
    SymDiff_identity_empty
    SymDiff_inverse
    SymDiff_assoc
    SymDiff_inter_distrib
    SymDiff_inter_distrib_right
    SymDiff_mem_PowerSet
    SymDiff_eq_union_diff
    SymDiff_as_complement
    SymDiff_eq_self_iff_empty
)
