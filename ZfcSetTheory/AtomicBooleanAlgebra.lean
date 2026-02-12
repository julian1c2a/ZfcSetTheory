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
import ZfcSetTheory.PowerSetAlgebra
import ZfcSetTheory.SetOrder
import ZfcSetTheory.SetStrictOrder

/-!
# Atomic Boolean Algebra on Power Sets

This file establishes that the power set Boolean algebra is atomic,
and that the atoms are exactly the singletons.

## Main Definitions

* `isAtom A X` - X is an atom in 𝒫(A): X ≠ ∅ and nothing strictly between ∅ and X
* `isAtomic A` - 𝒫(A) is atomic: every non-empty subset contains an atom

## Main Theorems

* `singleton_is_atom` - {x} is an atom when x ∈ A
* `atom_is_singleton` - Every atom is a singleton
* `PowerSet_is_atomic` - 𝒫(A) is an atomic Boolean algebra
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
  open SetUniverse.SetOrder
  open SetUniverse.SetStrictOrder
  universe u
  variable {U : Type u}

  namespace AtomicBooleanAlgebra

    /-! ### Definition of Atom -/

    /-- X is an atom in the Boolean algebra 𝒫(A) if:
        1. X is not empty (not the bottom element)
        2. There is no element strictly between ∅ and X -/
    def isAtom (A X : U) : Prop :=
      X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ∈ 𝒫 A → Y ⊂ X → Y = ∅

    /-- Alternative characterization: X is minimal non-empty -/
    theorem isAtom_alt (A X : U) :
        isAtom A X ↔ X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ⊆ X → Y = ∅ ∨ Y = X := by
      constructor
      · intro ⟨hX_mem, hX_ne, hX_min⟩
        refine ⟨hX_mem, hX_ne, ?_⟩
        intro Y hY_sub
        by_cases hY_eq : Y = X
        · right; exact hY_eq
        · left
          have hY_strict : Y ⊂ X := ⟨hY_sub, hY_eq⟩
          have hY_mem : Y ∈ 𝒫 A := by
            rw [PowerSet_is_specified] at hX_mem ⊢
            exact fun z hz => hX_mem z (hY_sub z hz)
          exact hX_min Y hY_mem hY_strict
      · intro ⟨hX_mem, hX_ne, hX_alt⟩
        refine ⟨hX_mem, hX_ne, ?_⟩
        intro Y _hY_mem hY_strict
        cases hX_alt Y hY_strict.1 with
        | inl h => exact h
        | inr h => exact absurd h hY_strict.2

    /-! ### Singletons are Atoms -/

    /-- A singleton {x} is a subset of A when x ∈ A -/
    theorem singleton_subset (A x : U) (hx : x ∈ A) : {x} ⊆ A := by
      intro z hz
      rw [Singleton_is_specified] at hz
      rw [hz]
      exact hx

    /-- A singleton is in the power set when its element is in A -/
    theorem singleton_mem_PowerSet (A x : U) (hx : x ∈ A) : {x} ∈ 𝒫 A := by
      rw [PowerSet_is_specified]
      exact singleton_subset A x hx

    /-- A singleton is not empty -/
    theorem singleton_nonempty (x : U) : {x} ≠ ∅ := by
      intro h_eq
      have hx_in : x ∈ ({x} : U) := (Singleton_is_specified x x).mpr rfl
      rw [h_eq] at hx_in
      exact EmptySet_is_empty x hx_in

    /-- Any subset of a singleton is either empty or the singleton itself -/
    theorem subset_singleton (x Y : U) (hY : Y ⊆ {x}) : Y = ∅ ∨ Y = {x} := by
      by_cases hY_empty : Y = ∅
      · left; exact hY_empty
      · right
        -- Y is nonempty, so it contains some element
        have h_ex := (nonempty_iff_exists_mem Y).mp hY_empty
        obtain ⟨z, hz⟩ := h_ex
        -- Since Y ⊆ {x}, we have z ∈ {x}, so z = x
        have hz_x : z = x := (Singleton_is_specified x z).mp (hY z hz)
        -- Now show Y = {x}
        apply ExtSet
        intro w
        constructor
        · intro hw
          have hw_x : w = x := (Singleton_is_specified x w).mp (hY w hw)
          exact (Singleton_is_specified x w).mpr hw_x
        · intro hw
          have hw_x : w = x := (Singleton_is_specified x w).mp hw
          rw [hw_x, ← hz_x]
          exact hz

    /-- Every singleton {x} with x ∈ A is an atom in 𝒫(A) -/
    theorem singleton_is_atom (A x : U) (hx : x ∈ A) : isAtom A {x} := by
      rw [isAtom_alt]
      refine ⟨singleton_mem_PowerSet A x hx, singleton_nonempty x, ?_⟩
      intro Y hY
      exact subset_singleton x Y hY

    /-! ### Atoms are Singletons -/

    /-- If X is an atom, then X contains exactly one element -/
    theorem atom_has_unique_element (A X : U) (hAtom : isAtom A X) :
        ∃ z, z ∈ X ∧ ∀ y, y ∈ X → y = z := by
      rw [isAtom_alt] at hAtom
      obtain ⟨_, hX_ne, hX_min⟩ := hAtom
      -- X is nonempty, so it has at least one element
      have h_ex := (nonempty_iff_exists_mem X).mp hX_ne
      obtain ⟨x, hx⟩ := h_ex
      refine ⟨x, hx, ?_⟩
      -- Uniqueness: suppose y ∈ X, show y = x
      intro y hy
      -- Consider {x} ⊆ X and {y} ⊆ X
      have hx_sub : {x} ⊆ X := fun z hz =>
        (Singleton_is_specified x z).mp hz ▸ hx
      have hy_sub : {y} ⊆ X := fun z hz =>
        (Singleton_is_specified y z).mp hz ▸ hy
      -- {x} ≠ ∅, so {x} = X
      have h_x_cases := hX_min {x} hx_sub
      have h_y_cases := hX_min {y} hy_sub
      cases h_x_cases with
      | inl h_empty => exact absurd h_empty (singleton_nonempty x)
      | inr h_eq_X =>
        cases h_y_cases with
        | inl h_empty => exact absurd h_empty (singleton_nonempty y)
        | inr h_eq_Y =>
          -- So {x} = X = {y}, hence y = x
          have h_xy : ({x} : U) = {y} := by rw [h_eq_X, h_eq_Y]
          have hx_in_y : x ∈ ({y} : U) := by rw [← h_xy]; exact (Singleton_is_specified x x).mpr rfl
          exact Eq.symm ((Singleton_is_specified y x).mp hx_in_y)

    /-- Every atom is a singleton -/
    theorem atom_is_singleton (A X : U) (hAtom : isAtom A X) :
        ∃ x, x ∈ A ∧ X = {x} := by
      have h_atom_alt := hAtom
      rw [isAtom_alt] at h_atom_alt
      obtain ⟨hX_mem, _, _⟩ := h_atom_alt
      -- Get the unique element of X
      obtain ⟨x, hx, hx_unique⟩ := atom_has_unique_element A X hAtom
      refine ⟨x, ?_, ?_⟩
      · -- x ∈ A because X ⊆ A
        rw [PowerSet_is_specified] at hX_mem
        exact hX_mem x hx
      · -- X = {x}
        apply ExtSet
        intro z
        constructor
        · intro hz
          have hz_eq_x := hx_unique z hz
          exact (Singleton_is_specified x z).mpr hz_eq_x
        · intro hz
          have hz_eq_x := (Singleton_is_specified x z).mp hz
          rw [hz_eq_x]
          exact hx

    /-- Characterization: X is an atom iff X = {x} for some x ∈ A -/
    theorem atom_iff_singleton (A X : U) :
        isAtom A X ↔ ∃ x, x ∈ A ∧ X = {x} := by
      constructor
      · exact atom_is_singleton A X
      · intro ⟨x, hx, hX_eq⟩
        rw [hX_eq]
        exact singleton_is_atom A x hx

    /-! ### The Family of Atoms -/

    /-- The set of all atoms in 𝒫(A) -/
    noncomputable def Atoms (A : U) : U :=
      SpecSet (𝒫 A) (fun X => isAtom A X)

    /-- Specification for Atoms -/
    theorem Atoms_is_specified (A X : U) :
        X ∈ Atoms A ↔ X ∈ 𝒫 A ∧ isAtom A X := by
      unfold Atoms
      rw [SpecSet_is_specified]

    /-- The atoms of 𝒫(A) are exactly the singletons of elements of A -/
    theorem Atoms_eq_singletons (A X : U) :
        X ∈ Atoms A ↔ ∃ x, x ∈ A ∧ X = {x} := by
      rw [Atoms_is_specified, atom_iff_singleton]
      constructor
      · intro hpair
        exact hpair.2
      · intro h
        constructor
        · obtain ⟨x, hx, hX_eq⟩ := h
          rw [hX_eq]
          exact singleton_mem_PowerSet A x hx
        · exact h

    /-! ### Atomicity of 𝒫(A) -/

    /-- Definition: 𝒫(A) is atomic if every non-empty element has an atom below it -/
    def isAtomic (A : U) : Prop :=
      ∀ X, X ∈ 𝒫 A → X ≠ ∅ → ∃ Y, isAtom A Y ∧ Y ⊆ X

    /-- Every non-empty subset of A contains an element, hence a singleton atom -/
    theorem PowerSet_is_atomic (A : U) : isAtomic A := by
      intro X hX_mem hX_ne
      -- X is nonempty, so pick an element x ∈ X
      have h_ex := (nonempty_iff_exists_mem X).mp hX_ne
      obtain ⟨x, hx⟩ := h_ex
      -- x ∈ A since X ⊆ A
      have hx_A : x ∈ A := by
        rw [PowerSet_is_specified] at hX_mem
        exact hX_mem x hx
      -- {x} is an atom and {x} ⊆ X
      refine ⟨{x}, singleton_is_atom A x hx_A, ?_⟩
      intro z hz
      have hz_eq_x := (Singleton_is_specified x z).mp hz
      rw [hz_eq_x]
      exact hx

    /-- Alternative: Every element is a union of atoms below it -/
    theorem element_is_union_of_atoms (A X : U) (hX : X ∈ 𝒫 A) :
        X = ⋃ (SpecSet (Atoms A) (fun Y => Y ⊆ X)) := by
      apply ExtSet
      intro z
      constructor
      · -- z ∈ X → z ∈ ⋃{atoms below X}
        intro hz
        rw [UnionSet_is_specified]
        -- {z} is an atom below X
        have hz_A : z ∈ A := by
          rw [PowerSet_is_specified] at hX
          exact hX z hz
        refine ⟨{z}, ?_, (Singleton_is_specified z z).mpr rfl⟩
        rw [SpecSet_is_specified]
        constructor
        · rw [Atoms_is_specified]
          exact ⟨singleton_mem_PowerSet A z hz_A, singleton_is_atom A z hz_A⟩
        · intro w hw
          have hw_eq_z := (Singleton_is_specified z w).mp hw
          rw [hw_eq_z]
          exact hz
      · -- z ∈ ⋃{atoms below X} → z ∈ X
        intro hz
        rw [UnionSet_is_specified] at hz
        obtain ⟨Y, hY_mem, hz_Y⟩ := hz
        rw [SpecSet_is_specified] at hY_mem
        exact hY_mem.2 z hz_Y

    /-! ### Atom below relation -/

    /-- An atom is below X if it is a subset of X -/
    def atomBelow (A X Y : U) : Prop := isAtom A Y ∧ Y ⊆ X

    /-- For singletons: {x} is below X iff x ∈ X -/
    theorem singleton_below_iff (A X x : U) (hx : x ∈ A) :
        atomBelow A X {x} ↔ x ∈ X := by
      unfold atomBelow
      constructor
      · intro hpair
        have hY_sub := hpair.2
        have hx_in : x ∈ ({x} : U) := (Singleton_is_specified x x).mpr rfl
        exact hY_sub x hx_in
      · intro hx_X
        refine ⟨singleton_is_atom A x hx, ?_⟩
        intro z hz
        have hz_eq_x := (Singleton_is_specified x z).mp hz
        rw [hz_eq_x]
        exact hx_X

  end AtomicBooleanAlgebra

  -- Export key theorems
  export AtomicBooleanAlgebra (isAtom isAtom_alt singleton_is_atom atom_is_singleton
    atom_iff_singleton Atoms Atoms_is_specified Atoms_eq_singletons
    isAtomic PowerSet_is_atomic element_is_union_of_atoms atomBelow singleton_below_iff)

end SetUniverse
