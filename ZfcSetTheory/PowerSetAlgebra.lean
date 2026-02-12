/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.PowerSet
import ZfcSetTheory.BooleanAlgebra

/-!
# Boolean Algebra on Power Sets

This file establishes that the power set forms a Boolean algebra.

## Main Definitions

* `Complement A X` - The complement of X relative to A: A \ X
* Notation `X ^∁[ A ]` for `Complement A X`

## Main Theorems

### Identity Laws
* `PowerSet_union_empty` - X ∪ ∅ = X
* `PowerSet_inter_universe` - X ∩ A = X (for X ⊆ A)

### Complement Laws
* `PowerSet_union_complement` - X ∪ X^∁[A] = A (for X ⊆ A)
* `PowerSet_inter_complement` - X ∩ X^∁[A] = ∅

### Distributive Laws
* `PowerSet_union_distrib_inter` - X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)
* `PowerSet_inter_distrib_union` - X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z)

### De Morgan Laws
* `PowerSet_DeMorgan_union` - (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A]
* `PowerSet_DeMorgan_inter` - (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A]

### Double Complement
* `PowerSet_double_complement` - (X^∁[A])^∁[A] = X (for X ⊆ A)
-/

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.BooleanAlgebra
  universe u
  variable {U : Type u}

  namespace PowerSetAlgebra

    /-! ### The Complement Operation -/

    /-- The complement of X relative to universe A -/
    noncomputable def Complement (A X : U) : U := A \ X

    /-- Notation: X ^∁[ A ] denotes the complement of X relative to A -/
    notation:max X:max " ^∁[ " A:max " ]" => Complement A X

    /-- Specification for complement -/
    theorem Complement_is_specified (A X z : U) : z ∈ (X ^∁[ A ]) ↔ z ∈ A ∧ z ∉ X := by
      unfold Complement
      rw [Difference_is_specified]

    /-! ### Closure Properties -/

    /-- Union of subsets is a subset -/
    theorem union_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
        BinUnion X Y ∈ 𝒫 A := by
      rw [PowerSet_is_specified] at hX hY ⊢
      intro z hz
      rw [BinUnion_is_specified] at hz
      cases hz with
      | inl hzX => exact hX z hzX
      | inr hzY => exact hY z hzY

    /-- Intersection of subsets is a subset -/
    theorem inter_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        BinInter X Y ∈ 𝒫 A := by
      rw [PowerSet_is_specified] at hX ⊢
      intro z hz
      rw [BinInter_is_specified] at hz
      exact hX z hz.1

    /-- Complement of a subset is a subset -/
    theorem complement_mem_PowerSet (A X : U) (_hX : X ∈ 𝒫 A) :
        (X ^∁[ A ]) ∈ 𝒫 A := by
      rw [PowerSet_is_specified]
      intro z hz
      rw [Complement_is_specified] at hz
      exact hz.1

    /-- Empty set is in power set -/
    theorem empty_in_PowerSet (A : U) : ∅ ∈ 𝒫 A := empty_mem_PowerSet A

    /-- Universe is in its own power set -/
    theorem universe_in_PowerSet (A : U) : A ∈ 𝒫 A := self_mem_PowerSet A

    /-! ### Identity Laws -/

    /-- Union identity: X ∪ ∅ = X -/
    theorem PowerSet_union_empty (X : U) : BinUnion X ∅ = X := BinUnion_empty_right X

    /-- Union identity: ∅ ∪ X = X -/
    theorem PowerSet_empty_union (X : U) : BinUnion ∅ X = X := BinUnion_empty_left X

    /-- Intersection with universe: X ∩ A = X for X ⊆ A -/
    theorem PowerSet_inter_universe (A X : U) (hX : X ⊆ A) : BinInter X A = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [BinInter_is_specified] at hz
        exact hz.1
      · intro hz
        rw [BinInter_is_specified]
        exact ⟨hz, hX z hz⟩

    /-- Intersection with universe: A ∩ X = X for X ⊆ A -/
    theorem PowerSet_universe_inter (A X : U) (hX : X ⊆ A) : BinInter A X = X := by
      rw [BinInter_commutative]
      exact PowerSet_inter_universe A X hX

    /-! ### Complement Laws -/

    /-- Union complement: X ∪ X^∁[A] = A for X ⊆ A -/
    theorem PowerSet_union_complement (A X : U) (hX : X ⊆ A) : BinUnion X (X ^∁[ A ]) = A := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [BinUnion_is_specified] at hz
        cases hz with
        | inl hzX => exact hX z hzX
        | inr hzComp =>
          rw [Complement_is_specified] at hzComp
          exact hzComp.1
      · intro hzA
        rw [BinUnion_is_specified]
        by_cases hzX : z ∈ X
        · left; exact hzX
        · right
          rw [Complement_is_specified]
          exact ⟨hzA, hzX⟩

    /-- Intersection complement: X ∩ X^∁[A] = ∅ -/
    theorem PowerSet_inter_complement (A X : U) : BinInter X (X ^∁[ A ]) = ∅ := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [BinInter_is_specified] at hz
        rw [Complement_is_specified] at hz
        exact absurd hz.1 hz.2.2
      · intro hz
        exact absurd hz (EmptySet_is_empty z)

    /-! ### Distributive Laws -/

    /-- Distributive: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) -/
    theorem PowerSet_union_distrib_inter (X Y Z : U) :
        BinUnion X (BinInter Y Z) = BinInter (BinUnion X Y) (BinUnion X Z) := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [BinUnion_is_specified] at hw
        rw [BinInter_is_specified]
        cases hw with
        | inl hwX =>
          constructor
          · rw [BinUnion_is_specified]; left; exact hwX
          · rw [BinUnion_is_specified]; left; exact hwX
        | inr hwYZ =>
          rw [BinInter_is_specified] at hwYZ
          constructor
          · rw [BinUnion_is_specified]; right; exact hwYZ.1
          · rw [BinUnion_is_specified]; right; exact hwYZ.2
      · intro hw
        rw [BinInter_is_specified] at hw
        rw [BinUnion_is_specified] at hw
        rw [BinUnion_is_specified]
        cases hw.1 with
        | inl hwX => left; exact hwX
        | inr hwY =>
          rw [BinUnion_is_specified] at hw
          cases hw.2 with
          | inl hwX => left; exact hwX
          | inr hwZ =>
            right
            rw [BinInter_is_specified]
            exact ⟨hwY, hwZ⟩

    /-- Distributive: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) -/
    theorem PowerSet_inter_distrib_union (X Y Z : U) :
        BinInter X (BinUnion Y Z) = BinUnion (BinInter X Y) (BinInter X Z) := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [BinInter_is_specified] at hw
        rw [BinUnion_is_specified] at hw
        rw [BinUnion_is_specified]
        cases hw.2 with
        | inl hwY =>
          left
          rw [BinInter_is_specified]
          exact ⟨hw.1, hwY⟩
        | inr hwZ =>
          right
          rw [BinInter_is_specified]
          exact ⟨hw.1, hwZ⟩
      · intro hw
        rw [BinUnion_is_specified] at hw
        rw [BinInter_is_specified]
        cases hw with
        | inl hwXY =>
          rw [BinInter_is_specified] at hwXY
          constructor
          · exact hwXY.1
          · rw [BinUnion_is_specified]; left; exact hwXY.2
        | inr hwXZ =>
          rw [BinInter_is_specified] at hwXZ
          constructor
          · exact hwXZ.1
          · rw [BinUnion_is_specified]; right; exact hwXZ.2

    /-! ### De Morgan Laws -/

    /-- De Morgan: (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A] -/
    theorem PowerSet_DeMorgan_union (A X Y : U) :
        (BinUnion X Y) ^∁[ A ] = BinInter (X ^∁[ A ]) (Y ^∁[ A ]) := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [Complement_is_specified] at hz
        rw [BinInter_is_specified]
        have hzNotUnion := hz.2
        rw [BinUnion_is_specified] at hzNotUnion
        -- Manually handle push_neg: ¬(z ∈ X ∨ z ∈ Y) ↔ z ∉ X ∧ z ∉ Y
        have hzNotX : z ∉ X := fun hzX => hzNotUnion (Or.inl hzX)
        have hzNotY : z ∉ Y := fun hzY => hzNotUnion (Or.inr hzY)
        constructor
        · rw [Complement_is_specified]
          exact ⟨hz.1, hzNotX⟩
        · rw [Complement_is_specified]
          exact ⟨hz.1, hzNotY⟩
      · intro hz
        rw [BinInter_is_specified] at hz
        -- hz : z ∈ (X ^∁[ A ]) ∧ z ∈ (Y ^∁[ A ])
        have hzAX := (Complement_is_specified A X z).mp hz.1
        have hzAY := (Complement_is_specified A Y z).mp hz.2
        rw [Complement_is_specified]
        constructor
        · exact hzAX.1
        · intro hzUnion
          rw [BinUnion_is_specified] at hzUnion
          cases hzUnion with
          | inl hzX => exact hzAX.2 hzX
          | inr hzY => exact hzAY.2 hzY

    /-- De Morgan: (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A] -/
    theorem PowerSet_DeMorgan_inter (A X Y : U) :
        (BinInter X Y) ^∁[ A ] = BinUnion (X ^∁[ A ]) (Y ^∁[ A ]) := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [Complement_is_specified] at hz
        rw [BinUnion_is_specified]
        have hzNotInter := hz.2
        rw [BinInter_is_specified] at hzNotInter
        -- Manually handle ¬(z ∈ X ∧ z ∈ Y) with case split
        by_cases hzX : z ∈ X
        · -- z ∈ X, so z ∉ Y (from ¬(z ∈ X ∧ z ∈ Y) and z ∈ X)
          have hzNotY : z ∉ Y := fun hzY => hzNotInter ⟨hzX, hzY⟩
          right
          rw [Complement_is_specified]
          exact ⟨hz.1, hzNotY⟩
        · -- z ∉ X
          left
          rw [Complement_is_specified]
          exact ⟨hz.1, hzX⟩
      · intro hz
        rw [BinUnion_is_specified] at hz
        rw [Complement_is_specified]
        cases hz with
        | inl hzAX =>
          rw [Complement_is_specified] at hzAX
          constructor
          · exact hzAX.1
          · intro hzInter
            rw [BinInter_is_specified] at hzInter
            exact hzAX.2 hzInter.1
        | inr hzAY =>
          rw [Complement_is_specified] at hzAY
          constructor
          · exact hzAY.1
          · intro hzInter
            rw [BinInter_is_specified] at hzInter
            exact hzAY.2 hzInter.2

    /-! ### Absorption Laws -/

    /-- Absorption: X ∪ (X ∩ Y) = X -/
    theorem PowerSet_absorb_union_inter (X Y : U) : BinUnion X (BinInter X Y) = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [BinUnion_is_specified] at hz
        cases hz with
        | inl hzX => exact hzX
        | inr hzXY =>
          rw [BinInter_is_specified] at hzXY
          exact hzXY.1
      · intro hz
        rw [BinUnion_is_specified]
        left
        exact hz

    /-- Absorption: X ∩ (X ∪ Y) = X -/
    theorem PowerSet_absorb_inter_union (X Y : U) : BinInter X (BinUnion X Y) = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [BinInter_is_specified] at hz
        exact hz.1
      · intro hz
        rw [BinInter_is_specified]
        constructor
        · exact hz
        · rw [BinUnion_is_specified]; left; exact hz

    /-! ### Double Complement -/

    /-- Double complement: (X^∁[A])^∁[A] = X for X ⊆ A -/
    theorem PowerSet_double_complement (A X : U) (hX : X ⊆ A) :
        (X ^∁[ A ]) ^∁[ A ] = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [Complement_is_specified] at hz
        -- hz : z ∈ A ∧ ¬(z ∈ (X ^∁[ A ]))
        -- Need to show z ∈ X
        -- ¬(z ∈ (X ^∁[ A ])) means ¬(z ∈ A ∧ z ∉ X)
        have hNotComp := hz.2
        apply Classical.byContradiction
        intro hzNotX
        have hzComp : z ∈ (X ^∁[ A ]) := (Complement_is_specified A X z).mpr ⟨hz.1, hzNotX⟩
        exact hNotComp hzComp
      · intro hz
        rw [Complement_is_specified]
        constructor
        · exact hX z hz
        · intro hzComp
          have hzNotX := (Complement_is_specified A X z).mp hzComp
          exact hzNotX.2 hz

    /-! ### Idempotence Laws -/

    /-- Idempotent: X ∪ X = X -/
    theorem PowerSet_union_idempotent (X : U) : BinUnion X X = X := BinUnion_idem X

    /-- Idempotent: X ∩ X = X -/
    theorem PowerSet_inter_idempotent (X : U) : BinInter X X = X := BinInter_idempotence X

    /-! ### Commutativity -/

    /-- Commutative: X ∪ Y = Y ∪ X -/
    theorem PowerSet_union_comm (X Y : U) : BinUnion X Y = BinUnion Y X := BinUnion_comm X Y

    /-- Commutative: X ∩ Y = Y ∩ X -/
    theorem PowerSet_inter_comm (X Y : U) : BinInter X Y = BinInter Y X := BinInter_commutative X Y

    /-! ### Associativity -/

    /-- Associative: X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z -/
    theorem PowerSet_union_assoc (X Y Z : U) : BinUnion X (BinUnion Y Z) = BinUnion (BinUnion X Y) Z :=
      (BinUnion_assoc X Y Z).symm

    /-- Associative: X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z -/
    theorem PowerSet_inter_assoc (X Y Z : U) : BinInter X (BinInter Y Z) = BinInter (BinInter X Y) Z :=
      (BinInter_associative X Y Z).symm

    /-! ### Bounded Lattice Properties -/

    /-- Annihilation: X ∩ ∅ = ∅ -/
    theorem PowerSet_inter_empty (X : U) : BinInter X ∅ = ∅ := BinInter_absorbent_elem X

    /-- Annihilation: ∅ ∩ X = ∅ -/
    theorem PowerSet_empty_inter (X : U) : BinInter ∅ X = ∅ := by
      rw [BinInter_commutative]
      exact BinInter_absorbent_elem X

    /-! ### Complement of Extremes -/

    /-- Complement of empty: ∅^∁[A] = A -/
    theorem PowerSet_complement_empty (A : U) : (∅ ^∁[ A ]) = A := by
      unfold Complement
      exact Difference_with_empty A

    /-- Complement of universe: A^∁[A] = ∅ -/
    theorem PowerSet_complement_universe (A : U) : (A ^∁[ A ]) = ∅ := by
      unfold Complement
      exact Difference_self_empty A

  end PowerSetAlgebra

end SetUniverse

export SetUniverse.PowerSetAlgebra (
    Complement
    Complement_is_specified
    union_mem_PowerSet
    inter_mem_PowerSet
    complement_mem_PowerSet
    empty_in_PowerSet
    universe_in_PowerSet
    PowerSet_union_empty
    PowerSet_empty_union
    PowerSet_inter_universe
    PowerSet_universe_inter
    PowerSet_union_complement
    PowerSet_inter_complement
    PowerSet_union_distrib_inter
    PowerSet_inter_distrib_union
    PowerSet_DeMorgan_union
    PowerSet_DeMorgan_inter
    PowerSet_absorb_union_inter
    PowerSet_absorb_inter_union
    PowerSet_double_complement
    PowerSet_union_idempotent
    PowerSet_inter_idempotent
    PowerSet_union_comm
    PowerSet_inter_comm
    PowerSet_union_assoc
    PowerSet_inter_assoc
    PowerSet_inter_empty
    PowerSet_empty_inter
    PowerSet_complement_empty
    PowerSet_complement_universe
)
