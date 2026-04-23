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
import ZFC.BoolAlg.Basic

/-!
# Boolean Algebra on Power Sets

This file establishes that the power set forms a Boolean algebra.

## Main Definitions

* `Complement A X` - The complement of X relative to A: A \ X
* Notation `X ^∁[ A ]` for `Complement A X`

## Main Theorems

### Identity Laws
* `powerset_union_empty` - X ∪ ∅ = X
* `powerset_inter_universe` - X ∩ A = X (for X ⊆ A)

### Complement Laws
* `powerset_union_complement` - X ∪ X^∁[A] = A (for X ⊆ A)
* `powerset_inter_complement` - X ∩ X^∁[A] = ∅

### Distributive Laws
* `powerset_union_distrib_inter` - X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)
* `powerset_inter_distrib_union` - X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z)

### De Morgan Laws
* `powerset_compl_union` - (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A]
* `powerset_compl_inter` - (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A]

### Double Complement
* `powerset_double_complement` - (X^∁[A])^∁[A] = X (for X ⊆ A)
-/

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.BoolAlg.Basic
  universe u
  variable {U : Type u}

  namespace BoolAlg.PowerSetAlgebra

    /-! ### The Complement Operation -/

    /-- The complement of X relative to universe A -/
    noncomputable def Complement (A X : U) : U := A \ X

    /-- Notation: X ^∁[ A ] denotes the complement of X relative to A -/
    notation:max X:max " ^∁[ " A:max " ]" => Complement A X

    /-- Specification for complement -/
    theorem Complement_is_specified (A X z : U) : z ∈ (X ^∁[ A ]) ↔ z ∈ A ∧ z ∉ X := by
      unfold Complement
      rw [mem_sdiff_iff]

    /-! ### Closure Properties -/

    /-- Union of subsets is a subset -/
    theorem union_mem_powerset (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
        union X Y ∈ 𝒫 A := by
      rw [mem_powerset_iff] at hX hY ⊢
      intro z hz
      rw [mem_union_iff] at hz
      cases hz with
      | inl hzX => exact hX z hzX
      | inr hzY => exact hY z hzY

    /-- Intersection of subsets is a subset -/
    theorem inter_mem_powerset (A X Y : U) (hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        inter X Y ∈ 𝒫 A := by
      rw [mem_powerset_iff] at hX ⊢
      intro z hz
      rw [mem_inter_iff] at hz
      exact hX z hz.1

    /-- Complement of a subset is a subset -/
    theorem complement_mem_powerset (A X : U) (_hX : X ∈ 𝒫 A) :
        (X ^∁[ A ]) ∈ 𝒫 A := by
      rw [mem_powerset_iff]
      intro z hz
      rw [Complement_is_specified] at hz
      exact hz.1

    /-- Empty set is in power set -/
    theorem empty_in_powerset (A : U) : ∅ ∈ 𝒫 A := empty_mem_powerset A

    /-- Universe is in its own power set -/
    theorem universe_in_powerset (A : U) : A ∈ 𝒫 A := self_mem_powerset A

    /-! ### Identity Laws -/

    /-- Union identity: X ∪ ∅ = X -/
    theorem powerset_union_empty (X : U) : union X ∅ = X := union_empty X

    /-- Union identity: ∅ ∪ X = X -/
    theorem powerset_empty_union (X : U) : union ∅ X = X := empty_union X

    /-- Intersection with universe: X ∩ A = X for X ⊆ A -/
    theorem powerset_inter_universe (A X : U) (hX : X ⊆ A) : inter X A = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [mem_inter_iff] at hz
        exact hz.1
      · intro hz
        rw [mem_inter_iff]
        exact ⟨hz, hX z hz⟩

    /-- Intersection with universe: A ∩ X = X for X ⊆ A -/
    theorem powerset_universe_inter (A X : U) (hX : X ⊆ A) : inter A X = X := by
      rw [inter_comm]
      exact powerset_inter_universe A X hX

    /-! ### Complement Laws -/

    /-- Union complement: X ∪ X^∁[A] = A for X ⊆ A -/
    theorem powerset_union_complement (A X : U) (hX : X ⊆ A) : union X (X ^∁[ A ]) = A := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [mem_union_iff] at hz
        cases hz with
        | inl hzX => exact hX z hzX
        | inr hzComp =>
          rw [Complement_is_specified] at hzComp
          exact hzComp.1
      · intro hzA
        rw [mem_union_iff]
        by_cases hzX : z ∈ X
        · left; exact hzX
        · right
          rw [Complement_is_specified]
          exact ⟨hzA, hzX⟩

    /-- Intersection complement: X ∩ X^∁[A] = ∅ -/
    theorem powerset_inter_complement (A X : U) : inter X (X ^∁[ A ]) = ∅ := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [mem_inter_iff] at hz
        rw [Complement_is_specified] at hz
        exact absurd hz.1 hz.2.2
      · intro hz
        exact absurd hz (EmptySet_is_empty z)

    /-! ### Distributive Laws -/

    /-- Distributive: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) -/
    theorem powerset_union_distrib_inter (X Y Z : U) :
        union X (inter Y Z) = inter (union X Y) (union X Z) := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [mem_union_iff] at hw
        rw [mem_inter_iff]
        cases hw with
        | inl hwX =>
          constructor
          · rw [mem_union_iff]; left; exact hwX
          · rw [mem_union_iff]; left; exact hwX
        | inr hwYZ =>
          rw [mem_inter_iff] at hwYZ
          constructor
          · rw [mem_union_iff]; right; exact hwYZ.1
          · rw [mem_union_iff]; right; exact hwYZ.2
      · intro hw
        rw [mem_inter_iff] at hw
        rw [mem_union_iff] at hw
        rw [mem_union_iff]
        cases hw.1 with
        | inl hwX => left; exact hwX
        | inr hwY =>
          rw [mem_union_iff] at hw
          cases hw.2 with
          | inl hwX => left; exact hwX
          | inr hwZ =>
            right
            rw [mem_inter_iff]
            exact ⟨hwY, hwZ⟩

    /-- Distributive: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) -/
    theorem powerset_inter_distrib_union (X Y Z : U) :
        inter X (union Y Z) = union (inter X Y) (inter X Z) := by
      apply ExtSet
      intro w
      constructor
      · intro hw
        rw [mem_inter_iff] at hw
        rw [mem_union_iff] at hw
        rw [mem_union_iff]
        cases hw.2 with
        | inl hwY =>
          left
          rw [mem_inter_iff]
          exact ⟨hw.1, hwY⟩
        | inr hwZ =>
          right
          rw [mem_inter_iff]
          exact ⟨hw.1, hwZ⟩
      · intro hw
        rw [mem_union_iff] at hw
        rw [mem_inter_iff]
        cases hw with
        | inl hwXY =>
          rw [mem_inter_iff] at hwXY
          constructor
          · exact hwXY.1
          · rw [mem_union_iff]; left; exact hwXY.2
        | inr hwXZ =>
          rw [mem_inter_iff] at hwXZ
          constructor
          · exact hwXZ.1
          · rw [mem_union_iff]; right; exact hwXZ.2

    /-! ### De Morgan Laws -/

    /-- De Morgan: (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A] -/
    theorem powerset_compl_union (A X Y : U) :
        (union X Y) ^∁[ A ] = inter (X ^∁[ A ]) (Y ^∁[ A ]) := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [Complement_is_specified] at hz
        rw [mem_inter_iff]
        have hzNotUnion := hz.2
        rw [mem_union_iff] at hzNotUnion
        -- Manually handle push_neg: ¬(z ∈ X ∨ z ∈ Y) ↔ z ∉ X ∧ z ∉ Y
        have hzNotX : z ∉ X := fun hzX => hzNotUnion (Or.inl hzX)
        have hzNotY : z ∉ Y := fun hzY => hzNotUnion (Or.inr hzY)
        constructor
        · rw [Complement_is_specified]
          exact ⟨hz.1, hzNotX⟩
        · rw [Complement_is_specified]
          exact ⟨hz.1, hzNotY⟩
      · intro hz
        rw [mem_inter_iff] at hz
        -- hz : z ∈ (X ^∁[ A ]) ∧ z ∈ (Y ^∁[ A ])
        have hzAX := (Complement_is_specified A X z).mp hz.1
        have hzAY := (Complement_is_specified A Y z).mp hz.2
        rw [Complement_is_specified]
        constructor
        · exact hzAX.1
        · intro hzUnion
          rw [mem_union_iff] at hzUnion
          cases hzUnion with
          | inl hzX => exact hzAX.2 hzX
          | inr hzY => exact hzAY.2 hzY

    /-- De Morgan: (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A] -/
    theorem powerset_compl_inter (A X Y : U) :
        (inter X Y) ^∁[ A ] = union (X ^∁[ A ]) (Y ^∁[ A ]) := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [Complement_is_specified] at hz
        rw [mem_union_iff]
        have hzNotInter := hz.2
        rw [mem_inter_iff] at hzNotInter
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
        rw [mem_union_iff] at hz
        rw [Complement_is_specified]
        cases hz with
        | inl hzAX =>
          rw [Complement_is_specified] at hzAX
          constructor
          · exact hzAX.1
          · intro hzInter
            rw [mem_inter_iff] at hzInter
            exact hzAX.2 hzInter.1
        | inr hzAY =>
          rw [Complement_is_specified] at hzAY
          constructor
          · exact hzAY.1
          · intro hzInter
            rw [mem_inter_iff] at hzInter
            exact hzAY.2 hzInter.2

    /-! ### Absorption Laws -/

    /-- Absorption: X ∪ (X ∩ Y) = X -/
    theorem powerset_absorb_union_inter (X Y : U) : union X (inter X Y) = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [mem_union_iff] at hz
        cases hz with
        | inl hzX => exact hzX
        | inr hzXY =>
          rw [mem_inter_iff] at hzXY
          exact hzXY.1
      · intro hz
        rw [mem_union_iff]
        left
        exact hz

    /-- Absorption: X ∩ (X ∪ Y) = X -/
    theorem powerset_absorb_inter_union (X Y : U) : inter X (union X Y) = X := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [mem_inter_iff] at hz
        exact hz.1
      · intro hz
        rw [mem_inter_iff]
        constructor
        · exact hz
        · rw [mem_union_iff]; left; exact hz

    /-! ### Double Complement -/

    /-- Double complement: (X^∁[A])^∁[A] = X for X ⊆ A -/
    theorem powerset_double_complement (A X : U) (hX : X ⊆ A) :
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
    theorem powerset_union_idempotent (X : U) : union X X = X := union_self X

    /-- Idempotent: X ∩ X = X -/
    theorem powerset_inter_idempotent (X : U) : inter X X = X := inter_self X

    /-! ### Commutativity -/

    /-- Commutative: X ∪ Y = Y ∪ X -/
    theorem powerset_union_comm (X Y : U) : union X Y = union Y X := union_comm X Y

    /-- Commutative: X ∩ Y = Y ∩ X -/
    theorem powerset_inter_comm (X Y : U) : inter X Y = inter Y X := inter_comm X Y

    /-! ### Associativity -/

    /-- Associative: X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z -/
    theorem powerset_union_assoc (X Y Z : U) : union X (union Y Z) = union (union X Y) Z :=
      (union_assoc X Y Z).symm

    /-- Associative: X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z -/
    theorem powerset_inter_assoc (X Y Z : U) : inter X (inter Y Z) = inter (inter X Y) Z :=
      (inter_assoc X Y Z).symm

    /-! ### Bounded Lattice Properties -/

    /-- Annihilation: X ∩ ∅ = ∅ -/
    theorem powerset_inter_empty (X : U) : inter X ∅ = ∅ := inter_empty X

    /-- Annihilation: ∅ ∩ X = ∅ -/
    theorem powerset_empty_inter (X : U) : inter ∅ X = ∅ := by
      rw [inter_comm]
      exact inter_empty X

    /-! ### Complement of Extremes -/

    /-- Complement of empty: ∅^∁[A] = A -/
    theorem powerset_complement_empty (A : U) : (∅ ^∁[ A ]) = A := by
      unfold Complement
      exact sdiff_empty A

    /-- Complement of universe: A^∁[A] = ∅ -/
    theorem powerset_complement_universe (A : U) : (A ^∁[ A ]) = ∅ := by
      unfold Complement
      exact sdiff_self A

  end BoolAlg.PowerSetAlgebra

end ZFC

export ZFC.BoolAlg.PowerSetAlgebra (
    Complement
    Complement_is_specified
    union_mem_powerset
    inter_mem_powerset
    complement_mem_powerset
    empty_in_powerset
    universe_in_powerset
    powerset_union_empty
    powerset_empty_union
    powerset_inter_universe
    powerset_universe_inter
    powerset_union_complement
    powerset_inter_complement
    powerset_union_distrib_inter
    powerset_inter_distrib_union
    powerset_compl_union
    powerset_compl_inter
    powerset_absorb_union_inter
    powerset_absorb_inter_union
    powerset_double_complement
    powerset_union_idempotent
    powerset_inter_idempotent
    powerset_union_comm
    powerset_inter_comm
    powerset_union_assoc
    powerset_inter_assoc
    powerset_inter_empty
    powerset_empty_inter
    powerset_complement_empty
    powerset_complement_universe
)
