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
import ZFC.Axiom.Specification
import ZFC.Axiom.Pairing
import ZFC.Axiom.Union
import ZFC.Axiom.PowerSet
import ZFC.BoolAlg.PowerSetAlgebra

/-!
# Boolean Ring Structure on Power Sets

This file establishes that the power set forms a Boolean ring with:
- Addition: symmetric difference (symmDiff)
- Multiplication: intersection

## Main Theorems

### Ring Axioms
* `symmDiff_assoc` - associativity of symmDiff
* `symmDiff_is_comm` - commutativity of symmDiff
* `symmDiff_empty_identity` - symmDiff with empty set
* `symmDiff_inverse` - X symmDiff X = empty

### Boolean Ring Properties
* `symmDiff_inter_distrib` - distributivity of inter over symmDiff
* `inter_idempotent` - X inter X = X

### Formulas
* `symmDiff_eq_union_diff` - symmDiff as union of differences
* `symmDiff_as_complement` - symmDiff using complement (for subsets)
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

  namespace BoolAlg.Ring

    /-! ### Basic symmDiff Properties -/

    /-- symmDiff is commutative -/
    theorem symmDiff_is_comm (X Y : U) :
      symmDiff X Y = symmDiff Y X
      := symmDiff_comm X Y

    /-- symmDiff identity: empty symmDiff X = X -/
    theorem symmDiff_identity_empty (X : U) :
      symmDiff ∅ X = X
      := empty_symmDiff X

    /-- symmDiff identity: X symmDiff empty = X -/
    theorem symmDiff_empty_identity (X : U) :
      symmDiff X ∅ = X
      := by
      rw [symmDiff_comm]
      exact empty_symmDiff X

    /-- symmDiff inverse -/
    theorem symmDiff_inverse (X : U) :
      symmDiff X X = ∅
      := symmDiff_self X

    /-! ### symmDiff Associativity -/

    /-- symmDiff is associative -/
    theorem symmDiff_assoc (X Y Z : U) :
      symmDiff (symmDiff X Y) Z = symmDiff X (symmDiff Y Z)
      := by
      apply ExtSet
      intro z
      simp only [mem_symmDiff_iff]
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

    /-! ### Distributivity of Intersection over symmDiff -/

    /-- Distributivity of inter over symmDiff -/
    theorem symmDiff_inter_distrib (X Y Z : U) :
        inter X (symmDiff Y Z) = symmDiff (inter X Y) (inter X Z)
        := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [mem_inter_iff] at hw
        have hwX := hw.1
        have hwYZ := hw.2
        rw [mem_symmDiff_iff] at hwYZ
        rw [mem_symmDiff_iff]
        cases hwYZ with
        | inl hYnotZ =>
          left
          rw [mem_inter_iff, mem_inter_iff]
          constructor
          · exact ⟨hwX, hYnotZ.1⟩
          · intro hXZ
            exact hYnotZ.2 hXZ.2
        | inr hZnotY =>
          right
          rw [mem_inter_iff, mem_inter_iff]
          constructor
          · exact ⟨hwX, hZnotY.1⟩
          · intro hXY
            exact hZnotY.2 hXY.2
      · intro hw
        rw [mem_symmDiff_iff] at hw
        rw [mem_inter_iff, mem_symmDiff_iff]
        cases hw with
        | inl hXYnotXZ =>
          rw [mem_inter_iff] at hXYnotXZ
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
              rw [mem_inter_iff] at hNotXZ
              exact hNotXZ ⟨hwX, hwZ⟩
        | inr hXZnotXY =>
          rw [mem_inter_iff] at hXZnotXY
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
              rw [mem_inter_iff] at hNotXY
              exact hNotXY ⟨hwX, hwY⟩

    /-- Right distributivity of inter over symmDiff -/
    theorem symmDiff_inter_distrib_right (X Y Z : U) :
        inter (symmDiff Y Z) X = symmDiff (inter Y X) (inter Z X)
        := by
      rw [inter_comm, inter_comm Y, inter_comm Z]
      exact symmDiff_inter_distrib X Y Z

    /-! ### symmDiff Closure in PowerSet -/

    /-- symmDiff of subsets is a subset -/
    theorem symmDiff_mem_powerset (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
        symmDiff X Y ∈ 𝒫 A
        := by
      rw [mem_powerset_iff] at hX hY ⊢
      intro z hz
      rw [mem_symmDiff_iff] at hz
      cases hz with
      | inl hXnotY => exact hX z hXnotY.1
      | inr hYnotX => exact hY z hYnotX.1

    /-! ### Alternative Characterizations -/

    /-- symmDiff as union of differences -/
    theorem symmDiff_eq_union_diff (X Y : U) :
      symmDiff X Y = union (X \ Y) (Y \ X)
      := by
      apply ExtSet
      intro z
      simp only [mem_symmDiff_iff, mem_union_iff, mem_sdiff_iff]

    /-- For subsets of A: symmDiff expressed using complement -/
    theorem symmDiff_as_complement (A X Y : U) (hX : X ⊆ A) (hY : Y ⊆ A) :
        symmDiff X Y = inter (union X Y) ((inter X Y)^∁[ A ])
        := by
      apply ExtSet
      intro z
      constructor
      · intro h
        rw [mem_symmDiff_iff] at h
        rw [mem_inter_iff, mem_union_iff, Complement_is_specified,
            mem_inter_iff]
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
        rw [mem_inter_iff, mem_union_iff, Complement_is_specified,
            mem_inter_iff] at h
        have hUnion := h.1
        have hzA := h.2.1
        have hNotInter := h.2.2
        rw [mem_symmDiff_iff]
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

    /-- symmDiff X Y = X is equivalent to Y = empty -/
    theorem symmDiff_eq_self_iff_empty (X Y : U) : symmDiff X Y = X ↔ Y = ∅ := by
      constructor
      · intro h
        apply ExtSet
        intro z
        constructor
        · intro hzY
          by_cases hzX : z ∈ X
          · have hNotSymDiff : z ∉ symmDiff X Y := by
              rw [mem_symmDiff_iff]
              intro hSymDiff
              cases hSymDiff with
              | inl hXnotY => exact hXnotY.2 hzY
              | inr hYnotX => exact hYnotX.2 hzX
            rw [h] at hNotSymDiff
            exact absurd hzX hNotSymDiff
          · have hInSymDiff : z ∈ symmDiff X Y := by
              rw [mem_symmDiff_iff]
              right
              exact ⟨hzY, hzX⟩
            rw [h] at hInSymDiff
            exact absurd hInSymDiff hzX
        · intro hz
          exact absurd hz (EmptySet_is_empty z)
      · intro hY
        rw [hY]
        exact symmDiff_empty_identity X

  end BoolAlg.Ring

end ZFC

export ZFC.BoolAlg.Ring (
    symmDiff_is_comm
    symmDiff_empty_identity
    symmDiff_identity_empty
    symmDiff_inverse
    symmDiff_assoc
    symmDiff_inter_distrib
    symmDiff_inter_distrib_right
    symmDiff_mem_powerset
    symmDiff_eq_union_diff
    symmDiff_as_complement
    symmDiff_eq_self_iff_empty
)
