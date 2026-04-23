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
import ZFC.BoolAlg.GenDeMorgan
import ZFC.SetOps.SetOrder
import ZFC.BoolAlg.Atomic

/-!
# Complete Boolean Algebra on Power Sets

This file proves that the power set 𝒫(A) forms a **complete atomic Boolean algebra**:
every subfamily of 𝒫(A) has a supremum and infimum within 𝒫(A).

Combined with `powerset_is_atomic` from `BoolAlg.Atomic`, this yields the
full structure theorem: 𝒫(A) is a complete atomic Boolean algebra.

## Main Definitions

* `isSupremumIn L S x` - x is the supremum of S within lattice L (ordered by ⊆)
* `isInfimumIn L S x` - x is the infimum of S within lattice L (ordered by ⊆)
* `isCompleteLattice L` - L is a complete lattice (w.r.t. ⊆)
* `isCompleteAtomicBA A` - 𝒫(A) is a complete atomic Boolean algebra

## Main Theorems

### Supremum
* `sUnion_subset_of_family` - ⋃F ⊆ A when F ⊆ 𝒫(A)
* `sUnion_mem_powerset_of_family` - ⋃S ∈ 𝒫(A) when S ⊆ 𝒫(A)
* `sUnion_is_supremumIn_powerset` - ⋃S is the supremum of S in 𝒫(A)

### Infimum
* `interSet_subset_of_family` - ⋂F ⊆ A when F ⊆ 𝒫(A) and F ≠ ∅
* `interSet_mem_powerset_of_family` - ⋂S ∈ 𝒫(A) when S ⊆ 𝒫(A) and S ≠ ∅
* `interSet_is_infimumIn_powerset` - ⋂S is the infimum of nonempty S in 𝒫(A)
* `universe_is_infimumIn_powerset_empty` - A is the infimum of ∅ in 𝒫(A)

### Completeness
* `supremumIn_unique` - Uniqueness of supremum
* `infimumIn_unique` - Uniqueness of infimum
* `powerset_is_complete_lattice` - 𝒫(A) is a complete lattice
* `powerset_is_complete_atomic_BA` - 𝒫(A) is a complete atomic Boolean algebra
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
  open ZFC.SetOps.SetOrder
  open ZFC.BoolAlg.Atomic
  universe u
  variable {U : Type u}

  namespace BoolAlg.Complete

    /-! ### Relativized Supremum and Infimum -/

    /-- x is the supremum of S within the lattice L (ordered by ⊆) -/
    def isSupremumIn (L S x : U) : Prop :=
      x ∈ L ∧ (∀ y, y ∈ S → y ⊆ x) ∧ (∀ z, z ∈ L → (∀ y, y ∈ S → y ⊆ z) → x ⊆ z)

    /-- x is the infimum of S within the lattice L (ordered by ⊆) -/
    def isInfimumIn (L S x : U) : Prop :=
      x ∈ L ∧ (∀ y, y ∈ S → x ⊆ y) ∧ (∀ z, z ∈ L → (∀ y, y ∈ S → z ⊆ y) → z ⊆ x)

    /-- L is a complete lattice if every subset has both a supremum and infimum in L -/
    def isCompleteLattice (L : U) : Prop :=
      ∀ S, S ⊆ L → (∃ x, isSupremumIn L S x) ∧ (∃ x, isInfimumIn L S x)

    /-! ### Uniqueness of Supremum and Infimum -/

    /-- The supremum is unique -/
    theorem supremumIn_unique (L S x y : U)
        (hx : isSupremumIn L S x) (hy : isSupremumIn L S y) :
        x = y := by
      have h1 : x ⊆ y := hx.2.2 y hy.1 hy.2.1
      have h2 : y ⊆ x := hy.2.2 x hx.1 hx.2.1
      exact order_antisymmetric x y h1 h2

    /-- The infimum is unique -/
    theorem infimumIn_unique (L S x y : U)
        (hx : isInfimumIn L S x) (hy : isInfimumIn L S y) :
        x = y := by
      have h1 : x ⊆ y := hy.2.2 x hx.1 hx.2.1
      have h2 : y ⊆ x := hx.2.2 y hy.1 hy.2.1
      exact order_antisymmetric x y h1 h2

    /-! ### Supremum in 𝒫(A) -/

    /-- ⋃F ⊆ A when F ⊆ 𝒫(A) -/
    theorem sUnion_subset_of_family (A F : U) (hF : F ⊆ 𝒫 A) :
        ⋃ F ⊆ A := by
      intro z hz
      rw [mem_sUnion_iff] at hz
      obtain ⟨X, hX_F, hz_X⟩ := hz
      have hX_PA := hF X hX_F
      rw [mem_powerset_iff] at hX_PA
      exact hX_PA z hz_X

    /-- ⋃S ∈ 𝒫(A) when S ⊆ 𝒫(A) -/
    theorem sUnion_mem_powerset_of_family (A S : U) (hS : S ⊆ 𝒫 A) :
        ⋃ S ∈ 𝒫 A := by
      rw [mem_powerset_iff]
      exact sUnion_subset_of_family A S hS

    /-- ⋃S is the supremum of S in 𝒫(A) -/
    theorem sUnion_is_supremumIn_powerset (A S : U) (hS : S ⊆ 𝒫 A) :
        isSupremumIn (𝒫 A) S (⋃ S) := by
      refine ⟨sUnion_mem_powerset_of_family A S hS, ?_, ?_⟩
      · -- ⋃S is an upper bound: for each X ∈ S, X ⊆ ⋃S
        intro X hX_S z hz_X
        rw [mem_sUnion_iff]
        exact ⟨X, hX_S, hz_X⟩
      · -- ⋃S is the least upper bound
        intro z _hz_PA hz_ub w hw_union
        rw [mem_sUnion_iff] at hw_union
        obtain ⟨X, hX_S, hw_X⟩ := hw_union
        exact hz_ub X hX_S w hw_X

    /-! ### Infimum in 𝒫(A) -/

    /-- ⋂F ⊆ A when F ⊆ 𝒫(A) and F ≠ ∅ -/
    theorem interSet_subset_of_family (A F : U) (hF : F ⊆ 𝒫 A) (hne : F ≠ ∅) :
        (⋂ F) ⊆ A := by
      have h_ex := (nonempty_iff_exists_mem F).mp hne
      obtain ⟨X₀, hX₀⟩ := h_ex
      intro z hz
      have hz_all := (interSet_mem_iff F z hne).mp hz
      have hX₀_PA := hF X₀ hX₀
      rw [mem_powerset_iff] at hX₀_PA
      exact hX₀_PA z (hz_all X₀ hX₀)

    /-- ⋂S ∈ 𝒫(A) when S ⊆ 𝒫(A) and S ≠ ∅ -/
    theorem interSet_mem_powerset_of_family (A S : U) (hS : S ⊆ 𝒫 A) (hne : S ≠ ∅) :
        (⋂ S) ∈ 𝒫 A := by
      rw [mem_powerset_iff]
      exact interSet_subset_of_family A S hS hne

    /-- ⋂S is the infimum of nonempty S in 𝒫(A) -/
    theorem interSet_is_infimumIn_powerset (A S : U) (hS : S ⊆ 𝒫 A) (hne : S ≠ ∅) :
        isInfimumIn (𝒫 A) S (⋂ S) := by
      refine ⟨interSet_mem_powerset_of_family A S hS hne, ?_, ?_⟩
      · -- ⋂S is a lower bound: for each X ∈ S, ⋂S ⊆ X
        intro X hX_S z hz_inter
        exact (interSet_mem_iff S z hne).mp hz_inter X hX_S
      · -- ⋂S is the greatest lower bound
        intro z _hz_PA hz_lb w hw_z
        rw [interSet_mem_iff S w hne]
        intro X hX_S
        exact hz_lb X hX_S w hw_z

    /-- A is the infimum of the empty family in 𝒫(A) -/
    theorem universe_is_infimumIn_powerset_empty (A : U) :
        isInfimumIn (𝒫 A) ∅ A := by
      refine ⟨self_mem_powerset A, ?_, ?_⟩
      · -- A is a lower bound of ∅: vacuously true
        intro Y hY
        exact absurd hY (EmptySet_is_empty Y)
      · -- A is the greatest lower bound: if z ∈ 𝒫(A) is a lower bound, then z ⊆ A
        intro z hz_PA _
        rw [mem_powerset_iff] at hz_PA
        exact hz_PA

    /-! ### Complete Lattice -/

    /-- 𝒫(A) is a complete lattice -/
    theorem powerset_is_complete_lattice (A : U) : isCompleteLattice (𝒫 A) := by
      intro S hS
      constructor
      · -- Supremum exists: ⋃S
        exact ⟨⋃ S, sUnion_is_supremumIn_powerset A S hS⟩
      · -- Infimum exists
        by_cases hne : S = ∅
        · -- S = ∅: infimum is A
          rw [hne]
          exact ⟨A, universe_is_infimumIn_powerset_empty A⟩
        · -- S ≠ ∅: infimum is ⋂S
          exact ⟨⋂ S, interSet_is_infimumIn_powerset A S hS hne⟩

    /-! ### Complete Atomic Boolean Algebra -/

    /-- 𝒫(A) is a complete atomic Boolean algebra:
        it is a complete lattice, has Boolean algebra structure, and is atomic -/
    def isCompleteAtomicBA (A : U) : Prop :=
      isCompleteLattice (𝒫 A) ∧ isAtomic A

    /-- 𝒫(A) is a complete atomic Boolean algebra -/
    theorem powerset_is_complete_atomic_BA (A : U) : isCompleteAtomicBA A :=
      ⟨powerset_is_complete_lattice A, powerset_is_atomic A⟩

  end BoolAlg.Complete

  -- Export key definitions and theorems
  export BoolAlg.Complete (
    isSupremumIn isInfimumIn isCompleteLattice
    supremumIn_unique infimumIn_unique
    sUnion_subset_of_family sUnion_mem_powerset_of_family
    sUnion_is_supremumIn_powerset
    interSet_subset_of_family interSet_mem_powerset_of_family
    interSet_is_infimumIn_powerset
    universe_is_infimumIn_powerset_empty
    powerset_is_complete_lattice
    isCompleteAtomicBA powerset_is_complete_atomic_BA
  )

end ZFC
