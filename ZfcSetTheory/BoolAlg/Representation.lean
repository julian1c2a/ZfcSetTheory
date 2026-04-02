/-
Copyright (c) 2026. All rights reserved.
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
import ZfcSetTheory.BoolAlg.Atomic
import ZfcSetTheory.BoolAlg.Complete
import ZfcSetTheory.BoolAlg.GenDeMorgan
import ZfcSetTheory.BoolAlg.GenDistributive
import ZfcSetTheory.SetOps.SetOrder
import ZfcSetTheory.SetOps.OrderedPair
import ZfcSetTheory.SetOps.CartesianProduct
import ZfcSetTheory.SetOps.Relations
import ZfcSetTheory.SetOps.Functions
import ZfcSetTheory.Cardinal.Basic

/-!
# Representation Theorem for Complete Atomic Boolean Algebras

This file proves the **Stone representation theorem (concrete form)**:
every complete atomic Boolean algebra on 𝒫(A) is canonically isomorphic
to 𝒫(Atoms A) via the map that sends each X ⊆ A to the family of atoms below it.

Since atoms of 𝒫(A) are exactly the singletons {a} with a ∈ A
(by `atom_iff_singleton`), the key result reduces to:

  **A ≃ₛ Atoms(A)** via the restricted singleton map a ↦ {a}

and consequently

  **𝒫(A) ≃ₛ 𝒫(Atoms A)** via the lifted map X ↦ {{a} | a ∈ X}

The lifted map preserves ∪, ∩, and complement, making it a Boolean algebra
isomorphism.

## Main Definitions

* `atomsSingletonMap A` — the ZFC function a ↦ {a} from A to Atoms(A)
* `atomsBelowMap A` — the ZFC function X ↦ {Y ∈ Atoms(A) | Y ⊆ X} from 𝒫(A) to 𝒫(Atoms A)

## Main Theorems

### Bijection A ≃ₛ Atoms(A)
* `atomsSingletonMap_is_function` — a ↦ {a} is a function A → Atoms(A)
* `atomsSingletonMap_is_injective` — a ↦ {a} is injective
* `atomsSingletonMap_is_surjective` — a ↦ {a} is surjective onto Atoms(A)
* `atomsSingletonMap_is_bijection` — a ↦ {a} is a bijection A ↔ Atoms(A)
* `A_equipotent_Atoms` — A ≃ₛ Atoms(A)

### Bijection 𝒫(A) ≃ₛ 𝒫(Atoms A)
* `atomsBelowMap_is_function` — X ↦ atomsBelow(X) is a function 𝒫(A) → 𝒫(Atoms A)
* `atomsBelowMap_is_injective` — the map is injective
* `atomsBelowMap_is_surjective` — the map is surjective
* `atomsBelowMap_is_bijection` — the map is a bijection
* `representation_equipotent` — 𝒫(A) ≃ₛ 𝒫(Atoms A)

### Boolean Algebra Isomorphism
* `atomsBelowMap_preserves_union` — Φ(X ∪ Y) = Φ(X) ∪ Φ(Y)
* `atomsBelowMap_preserves_inter` — Φ(X ∩ Y) = Φ(X) ∩ Φ(Y)
* `atomsBelowMap_preserves_complement` — Φ(X^∁[A]) = Φ(X)^∁[Atoms A]
* `atomsBelowMap_preserves_empty` — Φ(∅) = ∅
* `atomsBelowMap_preserves_universe` — Φ(A) = Atoms(A)
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
  open ZFC.BoolAlg.Atomic
  open ZFC.BoolAlg.Complete
  open ZFC.BoolAlg.GenDeMorgan
  open ZFC.BoolAlg.GenDistributive
  open ZFC.SetOps.SetOrder
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Cardinal.Basic
  universe u
  variable {U : Type u}

  namespace BoolAlg.Representation

    -- =========================================================================
    -- Section 1: The bijection A ≃ₛ Atoms(A)
    -- =========================================================================

    /-- The singleton map restricted to codomain Atoms(A): a ↦ {a}.
        Defined as {⟨a, {a}⟩ | a ∈ A} ⊆ A ×ₛ Atoms(A). -/
    noncomputable def atomsSingletonMap (A : U) : U :=
      sep (A ×ₛ Atoms A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, ({x} : U)⟩)

    /-- Specification lemma for atomsSingletonMap -/
    theorem atomsSingletonMap_spec (A a Y : U) :
        ⟨a, Y⟩ ∈ atomsSingletonMap A ↔ a ∈ A ∧ Y = ({a} : U) := by
      unfold atomsSingletonMap
      rw [mem_sep_iff]
      constructor
      · intro ⟨_, z, hz_A, hz_eq⟩
        have h := Eq_of_OrderedPairs_given_projections a Y z {z} hz_eq
        rw [h.1]
        exact ⟨hz_A, h.2⟩
      · intro h
        constructor
        · rw [h.2, OrderedPair_mem_CartesianProduct]
          exact ⟨h.1, (Atoms_eq_singletons A {a}).mpr ⟨a, h.1, rfl⟩⟩
        · exact ⟨a, h.1, h.2 ▸ rfl⟩

    /-- atomsSingletonMap is a function from A to Atoms(A) -/
    theorem atomsSingletonMap_is_function (A : U) :
        IsFunction (atomsSingletonMap A) A (Atoms A) := by
      constructor
      · -- atomsSingletonMap A ⊆ A ×ₛ Atoms A
        intro p hp
        unfold atomsSingletonMap at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · -- For each a ∈ A, ∃! Y, ⟨a, Y⟩ ∈ atomsSingletonMap A
        intro a ha
        refine ⟨({a} : U), (atomsSingletonMap_spec A a {a}).mpr ⟨ha, rfl⟩, ?_⟩
        intro Y₂ hY₂
        rw [atomsSingletonMap_spec] at hY₂
        exact hY₂.2

    /-- atomsSingletonMap is injective -/
    theorem atomsSingletonMap_is_injective (A : U) :
        isInjective (atomsSingletonMap A) := by
      intro a₁ a₂ Y ha₁ ha₂
      rw [atomsSingletonMap_spec] at ha₁ ha₂
      have h : ({a₁} : U) = {a₂} := ha₁.2.symm.trans ha₂.2
      have ha₁_in : a₁ ∈ ({a₁} : U) := (Singleton_is_specified a₁ a₁).mpr rfl
      rw [h] at ha₁_in
      exact (Singleton_is_specified a₂ a₁).mp ha₁_in

    /-- atomsSingletonMap is surjective onto Atoms(A) -/
    theorem atomsSingletonMap_is_surjective (A : U) :
        isSurjectiveOnto (atomsSingletonMap A) (Atoms A) := by
      intro Y hY
      rw [Atoms_eq_singletons] at hY
      obtain ⟨a, ha, hY_eq⟩ := hY
      exact ⟨a, (atomsSingletonMap_spec A a Y).mpr ⟨ha, hY_eq⟩⟩

    /-- atomsSingletonMap is a bijection from A to Atoms(A) -/
    theorem atomsSingletonMap_is_bijection (A : U) :
        isBijection (atomsSingletonMap A) A (Atoms A) :=
      ⟨atomsSingletonMap_is_function A,
       atomsSingletonMap_is_injective A,
       atomsSingletonMap_is_surjective A⟩

    /-- A is equipotent to Atoms(A) -/
    theorem A_equipotent_Atoms (A : U) : isEquipotent A (Atoms A) :=
      ⟨atomsSingletonMap A, atomsSingletonMap_is_bijection A⟩

    -- =========================================================================
    -- Section 2: The atoms-below map 𝒫(A) → 𝒫(Atoms A)
    -- =========================================================================

    /-- The family of atoms below a given subset X ⊆ A -/
    noncomputable def atomsBelow (A X : U) : U :=
      sep (Atoms A) (fun Y => Y ⊆ X)

    /-- Specification for atomsBelow -/
    theorem mem_atomsBelow_iff (A X Y : U) :
        Y ∈ atomsBelow A X ↔ Y ∈ Atoms A ∧ Y ⊆ X := by
      unfold atomsBelow
      rw [mem_sep_iff]

    /-- atomsBelow X is a subset of Atoms(A), hence in 𝒫(Atoms A) -/
    theorem atomsBelow_mem_powerset_Atoms (A X : U) :
        atomsBelow A X ∈ 𝒫 (Atoms A) := by
      rw [mem_powerset_iff]
      intro Y hY
      rw [mem_atomsBelow_iff] at hY
      exact hY.1

    /-- When X ∈ 𝒫(A), atomsBelow A X is the set of singletons {a} with a ∈ X -/
    theorem atomsBelow_eq_singletons_in (A X : U) (hX : X ∈ 𝒫 A) :
        ∀ Y, Y ∈ atomsBelow A X ↔ ∃ a, a ∈ X ∧ Y = ({a} : U) := by
      intro Y
      rw [mem_atomsBelow_iff, Atoms_eq_singletons]
      constructor
      · intro h
        obtain ⟨⟨a, ha, hY_eq⟩, hY_sub⟩ := h
        rw [hY_eq] at hY_sub
        have ha_X : a ∈ X := by
          have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
          exact hY_sub a this
        exact ⟨a, ha_X, hY_eq⟩
      · intro h
        obtain ⟨a, ha_X, hY_eq⟩ := h
        rw [mem_powerset_iff] at hX
        constructor
        · exact ⟨a, hX a ha_X, hY_eq⟩
        · rw [hY_eq]
          intro z hz
          rw [Singleton_is_specified] at hz
          rw [hz]
          exact ha_X

    /-- The ZFC function X ↦ atomsBelow(A, X) from 𝒫(A) to 𝒫(Atoms A).
        Defined as {⟨X, atomsBelow A X⟩ | X ∈ 𝒫(A)}. -/
    noncomputable def atomsBelowMap (A : U) : U :=
      sep (𝒫 A ×ₛ 𝒫 (Atoms A)) (fun p =>
        ∃ W, W ∈ 𝒫 A ∧ p = ⟨W, atomsBelow A W⟩)

    /-- Specification for atomsBelowMap -/
    theorem atomsBelowMap_spec (A X F : U) :
        ⟨X, F⟩ ∈ atomsBelowMap A ↔ X ∈ 𝒫 A ∧ F = atomsBelow A X := by
      unfold atomsBelowMap
      rw [mem_sep_iff]
      constructor
      · intro ⟨_, Z, hZ_PA, hz_eq⟩
        have h := Eq_of_OrderedPairs_given_projections X F Z (atomsBelow A Z) hz_eq
        rw [h.1]
        exact ⟨hZ_PA, h.2⟩
      · intro h
        constructor
        · rw [h.2, OrderedPair_mem_CartesianProduct]
          exact ⟨h.1, atomsBelow_mem_powerset_Atoms A X⟩
        · exact ⟨X, h.1, h.2 ▸ rfl⟩

    /-- atomsBelowMap is a function from 𝒫(A) to 𝒫(Atoms A) -/
    theorem atomsBelowMap_is_function (A : U) :
        IsFunction (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A)) := by
      constructor
      · -- atomsBelowMap A ⊆ 𝒫 A ×ₛ 𝒫 (Atoms A)
        intro p hp
        unfold atomsBelowMap at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · -- For each X ∈ 𝒫(A), ∃! F, ⟨X, F⟩ ∈ atomsBelowMap A
        intro X hX
        refine ⟨atomsBelow A X, (atomsBelowMap_spec A X (atomsBelow A X)).mpr ⟨hX, rfl⟩, ?_⟩
        intro F₂ hF₂
        rw [atomsBelowMap_spec] at hF₂
        exact hF₂.2

    -- =========================================================================
    -- Section 3: Injectivity of atomsBelowMap
    -- =========================================================================

    /-- Key lemma: X can be recovered from atomsBelow A X as ⋃(atomsBelow A X) -/
    theorem union_atomsBelow_eq (A X : U) (hX : X ∈ 𝒫 A) :
        ⋃ (atomsBelow A X) = X := by
      exact (element_is_union_of_atoms A X hX).symm

    /-- atomsBelowMap is injective -/
    theorem atomsBelowMap_is_injective (A : U) :
        isInjective (atomsBelowMap A) := by
      intro X₁ X₂ F hX₁ hX₂
      rw [atomsBelowMap_spec] at hX₁ hX₂
      have h : atomsBelow A X₁ = atomsBelow A X₂ := hX₁.2.symm.trans hX₂.2
      calc X₁ = ⋃ (atomsBelow A X₁) := (union_atomsBelow_eq A X₁ hX₁.1).symm
        _ = ⋃ (atomsBelow A X₂) := by rw [h]
        _ = X₂ := union_atomsBelow_eq A X₂ hX₂.1

    -- =========================================================================
    -- Section 4: Surjectivity of atomsBelowMap
    -- =========================================================================

    /-- Any family of atoms F ⊆ Atoms(A) arises as atomsBelow A (⋃ F) -/
    theorem atomsBelow_of_union (A F : U) (hF : F ⊆ Atoms A) :
        atomsBelow A (⋃ F) = F := by
      apply ExtSet
      intro Y
      constructor
      · intro hY
        rw [mem_atomsBelow_iff] at hY
        obtain ⟨hY_atom, hY_sub⟩ := hY
        rw [Atoms_eq_singletons] at hY_atom
        obtain ⟨a, _ha_A, hY_eq⟩ := hY_atom
        rw [hY_eq] at hY_sub ⊢
        have ha_union : a ∈ ⋃ F := by
          have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
          exact hY_sub a this
        rw [mem_sUnion_iff] at ha_union
        obtain ⟨Z, hZ_F, ha_Z⟩ := ha_union
        have hZ_atom := hF Z hZ_F
        rw [Atoms_eq_singletons] at hZ_atom
        obtain ⟨b, _hb_A, hZ_eq⟩ := hZ_atom
        rw [hZ_eq] at ha_Z
        have ha_eq_b : a = b := (Singleton_is_specified b a).mp ha_Z
        rw [ha_eq_b, ← hZ_eq]
        exact hZ_F
      · intro hY_F
        rw [mem_atomsBelow_iff]
        constructor
        · exact hF Y hY_F
        · intro z hz
          rw [mem_sUnion_iff]
          exact ⟨Y, hY_F, hz⟩

    /-- ⋃F ∈ 𝒫(A) when F ⊆ Atoms(A) -/
    theorem union_atoms_mem_powerset (A F : U) (hF : F ⊆ Atoms A) :
        ⋃ F ∈ 𝒫 A := by
      rw [mem_powerset_iff]
      intro z hz
      rw [mem_sUnion_iff] at hz
      obtain ⟨Y, hY_F, hz_Y⟩ := hz
      have hY_atom := hF Y hY_F
      rw [Atoms_is_specified] at hY_atom
      rw [mem_powerset_iff] at hY_atom
      exact hY_atom.1 z hz_Y

    /-- atomsBelowMap is surjective onto 𝒫(Atoms A) -/
    theorem atomsBelowMap_is_surjective (A : U) :
        isSurjectiveOnto (atomsBelowMap A) (𝒫 (Atoms A)) := by
      intro F hF
      rw [mem_powerset_iff] at hF
      have h_union_PA := union_atoms_mem_powerset A F hF
      refine ⟨⋃ F, (atomsBelowMap_spec A (⋃ F) F).mpr ⟨h_union_PA, ?_⟩⟩
      exact (atomsBelow_of_union A F hF).symm

    -- =========================================================================
    -- Section 5: The representation theorem (bijection)
    -- =========================================================================

    /-- **Representation Theorem (bijection form):**
        atomsBelowMap is a bijection from 𝒫(A) to 𝒫(Atoms A) -/
    theorem atomsBelowMap_is_bijection (A : U) :
        isBijection (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A)) :=
      ⟨atomsBelowMap_is_function A,
       atomsBelowMap_is_injective A,
       atomsBelowMap_is_surjective A⟩

    /-- **Representation Theorem (equipotence form):**
        𝒫(A) ≃ₛ 𝒫(Atoms A) -/
    theorem representation_equipotent (A : U) :
        isEquipotent (𝒫 A) (𝒫 (Atoms A)) :=
      ⟨atomsBelowMap A, atomsBelowMap_is_bijection A⟩

    -- =========================================================================
    -- Section 6: Boolean algebra isomorphism properties
    -- =========================================================================

    /-- Φ(∅) = ∅ : the map sends the bottom element to the bottom element -/
    theorem atomsBelowMap_preserves_empty (A : U) :
        atomsBelow A ∅ = ∅ := by
      apply ExtSet
      intro Y
      constructor
      · intro hY
        rw [mem_atomsBelow_iff] at hY
        have hY_atom := hY.1
        rw [Atoms_eq_singletons] at hY_atom
        obtain ⟨a, _, hY_eq⟩ := hY_atom
        rw [hY_eq] at hY
        have ha_empty : a ∈ (∅ : U) := by
          have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
          exact hY.2 a this
        exact absurd ha_empty (EmptySet_is_empty a)
      · intro hY
        exact absurd hY (EmptySet_is_empty Y)

    /-- Φ(A) = Atoms(A) : the map sends the top element to the top element -/
    theorem atomsBelowMap_preserves_universe (A : U) :
        atomsBelow A A = Atoms A := by
      apply ExtSet
      intro Y
      constructor
      · intro hY
        rw [mem_atomsBelow_iff] at hY
        exact hY.1
      · intro hY
        rw [mem_atomsBelow_iff]
        constructor
        · exact hY
        · rw [Atoms_eq_singletons] at hY
          obtain ⟨a, ha, hY_eq⟩ := hY
          rw [hY_eq]
          intro z hz
          rw [Singleton_is_specified] at hz
          rw [hz]
          exact ha

    /-- Φ(X ∪ Y) = Φ(X) ∪ Φ(Y) : the map preserves binary union -/
    theorem atomsBelowMap_preserves_union (A X Y : U) (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        atomsBelow A (union X Y) = union (atomsBelow A X) (atomsBelow A Y) := by
      apply ExtSet
      intro Z
      constructor
      · intro hZ
        rw [mem_atomsBelow_iff] at hZ
        obtain ⟨hZ_atom, hZ_sub⟩ := hZ
        rw [Atoms_eq_singletons] at hZ_atom
        obtain ⟨a, ha_A, hZ_eq⟩ := hZ_atom
        rw [hZ_eq] at hZ_sub ⊢
        have ha_union : a ∈ union X Y := by
          have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
          exact hZ_sub a this
        rw [mem_union_iff] at ha_union
        rw [mem_union_iff]
        cases ha_union with
        | inl ha_X =>
          left
          rw [mem_atomsBelow_iff]
          exact ⟨(Atoms_eq_singletons A {a}).mpr ⟨a, ha_A, rfl⟩,
                 fun z hz => (Singleton_is_specified a z).mp hz ▸ ha_X⟩
        | inr ha_Y =>
          right
          rw [mem_atomsBelow_iff]
          exact ⟨(Atoms_eq_singletons A {a}).mpr ⟨a, ha_A, rfl⟩,
                 fun z hz => (Singleton_is_specified a z).mp hz ▸ ha_Y⟩
      · intro hZ
        rw [mem_union_iff] at hZ
        rw [mem_atomsBelow_iff]
        cases hZ with
        | inl hZ_X =>
          rw [mem_atomsBelow_iff] at hZ_X
          exact ⟨hZ_X.1, fun z hz => (mem_union_iff X Y z).mpr (Or.inl (hZ_X.2 z hz))⟩
        | inr hZ_Y =>
          rw [mem_atomsBelow_iff] at hZ_Y
          exact ⟨hZ_Y.1, fun z hz => (mem_union_iff X Y z).mpr (Or.inr (hZ_Y.2 z hz))⟩

    /-- Φ(X ∩ Y) = Φ(X) ∩ Φ(Y) : the map preserves binary intersection -/
    theorem atomsBelowMap_preserves_inter (A X Y : U) (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        atomsBelow A (inter X Y) = inter (atomsBelow A X) (atomsBelow A Y) := by
      apply ExtSet
      intro Z
      constructor
      · intro hZ
        rw [mem_atomsBelow_iff] at hZ
        obtain ⟨hZ_atom, hZ_sub⟩ := hZ
        rw [mem_inter_iff]
        constructor
        · rw [mem_atomsBelow_iff]
          exact ⟨hZ_atom, fun z hz => ((mem_inter_iff X Y z).mp (hZ_sub z hz)).1⟩
        · rw [mem_atomsBelow_iff]
          exact ⟨hZ_atom, fun z hz => ((mem_inter_iff X Y z).mp (hZ_sub z hz)).2⟩
      · intro hZ
        rw [mem_inter_iff] at hZ
        rw [mem_atomsBelow_iff]
        obtain ⟨hZ_X, hZ_Y⟩ := hZ
        rw [mem_atomsBelow_iff] at hZ_X hZ_Y
        exact ⟨hZ_X.1, fun z hz =>
          (mem_inter_iff X Y z).mpr ⟨hZ_X.2 z hz, hZ_Y.2 z hz⟩⟩

    /-- Φ(X^∁[A]) = Φ(X)^∁[Atoms A] : the map preserves complement -/
    theorem atomsBelowMap_preserves_complement (A X : U) (_hX : X ∈ 𝒫 A) :
        atomsBelow A (Complement A X) = Complement (Atoms A) (atomsBelow A X) := by
      apply ExtSet
      intro Z
      constructor
      · -- Z ∈ atomsBelow A (Complement A X) → Z ∈ Complement (Atoms A) (atomsBelow A X)
        intro hZ
        rw [mem_atomsBelow_iff] at hZ
        obtain ⟨hZ_atom, hZ_sub⟩ := hZ
        rw [Complement_is_specified]
        constructor
        · exact hZ_atom
        · intro hZ_X
          rw [mem_atomsBelow_iff] at hZ_X
          rw [Atoms_eq_singletons] at hZ_atom
          obtain ⟨a, _ha_A, hZ_eq⟩ := hZ_atom
          rw [hZ_eq] at hZ_sub hZ_X
          have ha_X : a ∈ X := by
            have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
            exact hZ_X.2 a this
          have ha_compl := hZ_sub a ((Singleton_is_specified a a).mpr rfl)
          rw [Complement_is_specified] at ha_compl
          exact ha_compl.2 ha_X
      · -- Z ∈ Complement (Atoms A) (atomsBelow A X) → Z ∈ atomsBelow A (Complement A X)
        intro hZ
        rw [Complement_is_specified] at hZ
        obtain ⟨hZ_atom, hZ_not_below⟩ := hZ
        rw [mem_atomsBelow_iff]
        constructor
        · exact hZ_atom
        · rw [Atoms_eq_singletons] at hZ_atom
          obtain ⟨a, ha_A, hZ_eq⟩ := hZ_atom
          rw [hZ_eq]
          intro z hz
          rw [Singleton_is_specified] at hz
          rw [hz]
          rw [Complement_is_specified]
          constructor
          · exact ha_A
          · intro ha_X
            apply hZ_not_below
            rw [mem_atomsBelow_iff]
            constructor
            · rw [Atoms_eq_singletons]; exact ⟨a, ha_A, hZ_eq⟩
            · rw [hZ_eq]
              intro w hw
              rw [Singleton_is_specified] at hw
              rw [hw]
              exact ha_X

    /-- **Representation Theorem (full statement):**
        For any set A, the complete atomic Boolean algebra 𝒫(A) is
        isomorphic (as a Boolean algebra) to 𝒫(Atoms A) via the
        bijection atomsBelowMap, which preserves ∪, ∩, and complement.

        This is the formal content of the Stone representation theorem
        for complete atomic Boolean algebras. -/
    theorem representation_theorem (A : U) :
        isBijection (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A)) ∧
        (∀ X Y, X ∈ 𝒫 A → Y ∈ 𝒫 A →
          atomsBelow A (union X Y) = union (atomsBelow A X) (atomsBelow A Y)) ∧
        (∀ X Y, X ∈ 𝒫 A → Y ∈ 𝒫 A →
          atomsBelow A (inter X Y) = inter (atomsBelow A X) (atomsBelow A Y)) ∧
        (∀ X, X ∈ 𝒫 A →
          atomsBelow A (Complement A X) = Complement (Atoms A) (atomsBelow A X)) :=
      ⟨atomsBelowMap_is_bijection A,
       fun X Y hX hY => atomsBelowMap_preserves_union A X Y hX hY,
       fun X Y hX hY => atomsBelowMap_preserves_inter A X Y hX hY,
       fun X hX => atomsBelowMap_preserves_complement A X hX⟩

  end BoolAlg.Representation

  -- Export key definitions and theorems
  export BoolAlg.Representation (
    atomsSingletonMap
    atomsSingletonMap_spec
    atomsSingletonMap_is_function
    atomsSingletonMap_is_injective
    atomsSingletonMap_is_surjective
    atomsSingletonMap_is_bijection
    A_equipotent_Atoms
    atomsBelow
    mem_atomsBelow_iff
    atomsBelow_mem_powerset_Atoms
    atomsBelow_eq_singletons_in
    atomsBelowMap atomsBelowMap_spec
    atomsBelowMap_is_function
    atomsBelowMap_is_injective
    atomsBelowMap_is_surjective
    atomsBelowMap_is_bijection
    representation_equipotent
    union_atomsBelow_eq
    atomsBelow_of_union
    union_atoms_mem_powerset
    atomsBelowMap_preserves_empty
    atomsBelowMap_preserves_universe
    atomsBelowMap_preserves_union
    atomsBelowMap_preserves_inter
    atomsBelowMap_preserves_complement
    representation_theorem
  )

end ZFC
