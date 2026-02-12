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
import ZfcSetTheory.OrderedPair
import ZfcSetTheory.CartesianProduct
import ZfcSetTheory.Relations

/-!
# Functions as Relations

This file develops the theory of functions as special relations,
including composition, identity, inverse, image, and preimage.

## Main Definitions

* `isFunctionFromTo f A B` - f is a function from A to B
* `apply f x` - the unique y such that ⟨x, y⟩ ∈ f
* `FunctionComposition g f` - composition g ∘ f
* `IdFunction A` - identity function on A
* `InverseFunction f` - inverse relation of f
* `Restriction f C` - restriction of f to domain C (f ↾ C)
* `ImageSet f X` - direct image f[X]
* `PreimageSet f Y` - preimage f⁻¹[Y]

## Main Theorems

* `comp_is_function` - composition of functions is a function
* `Restriction_is_function` - restriction of a function is a function
* `Restriction_apply` - (f ↾ C)(x) = f(x) for x ∈ C
-/

namespace SetUniverse
  open Classical
  open ExistsUnique
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  universe u
  variable {U : Type u}

  namespace Functions

    /-! ============================================================ -/
    /-! ### BASIC FUNCTION DEFINITIONS ### -/
    /-! ============================================================ -/

    /-- A relation f is single-valued if each x has at most one associated y -/
    def isSingleValued (f : U) : Prop :=
      ∀ x y₁ y₂, ⟨x, y₁⟩ ∈ f → ⟨x, y₂⟩ ∈ f → y₁ = y₂

    /-- f is a function from A to B iff:
        1. f ⊆ A × B
        2. ∀ x ∈ A, ∃! y, ⟨x, y⟩ ∈ f
        (Note: Dom f = A is implied by 2 and 1) -/
    def isFunctionFromTo (f A B : U) : Prop :=
      (f ⊆ (A ×ₛ B)) ∧
      (∀ x, x ∈ A → ∃! y, ⟨x, y⟩ ∈ f)

    /-- Application of f to x, denoted f⦅x⦆.
        If f is not a function or x is not in domain, returns ∅ (by default of choose).
    -/
    noncomputable def apply (f x : U) : U :=
      if h : ∃! y, ⟨x, y⟩ ∈ f then
        ExistsUnique.choose h
      else
        ∅

    notation:90 f "⦅" x "⦆" => apply f x

    /-- Theorem: If f is a function from A to B and x ∈ A, then ⟨x, f(x)⟩ ∈ f.
    -/
    theorem apply_mem (f x : U) (h_unique : ∃! y, ⟨x, y⟩ ∈ f) :
      ⟨x, f⦅x⦆⟩ ∈ f := by
      unfold apply
      simp only [dif_pos h_unique]
      exact choose_spec h_unique

    /-- Theorem: If f is a function and ⟨x, y⟩ ∈ f, then f(x) = y.
    -/
    theorem apply_eq (f x y : U) (h_unique : ∃! y, ⟨x, y⟩ ∈ f) (h_in : ⟨x, y⟩ ∈ f) :
      f⦅x⦆ = y := by
      unfold apply
      simp only [dif_pos h_unique]
      exact (unique h_unique y h_in).symm

    /-! ============================================================ -/
    /-! ### COMPOSITION AND IDENTITY ### -/
    /-! ============================================================ -/

    /-- Function composition g ∘ f.
        Defined as {⟨x, z⟩ | ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g}.
    -/
    noncomputable def FunctionComposition (g f : U) : U :=
      SpecSet (domain f ×ₛ range g) (fun p =>
        ∃ x z, p = ⟨x, z⟩ ∧ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g)

    notation:60 g " ∘ " f:61 => FunctionComposition g f

    theorem comp_is_specified (g f p : U) :
      p ∈ (g ∘ f) ↔ ∃ x z, p = ⟨x, z⟩ ∧ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g := by
      unfold FunctionComposition
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · -- Prove p ∈ domain f ×ₛ range g
          obtain ⟨x, z, hp, y, hf, hg⟩ := h
          rw [hp, OrderedPair_mem_CartesianProduct]
          constructor
          · -- x ∈ domain f
            exact pair_mem_implies_fst_in_domain f x y hf
          · -- z ∈ range g
            exact pair_mem_implies_snd_in_range g y z hg
        · exact h

    /-- Composition of functions is a function -/
    theorem comp_is_function (f g A B C : U)
      (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C) :
      isFunctionFromTo (g ∘ f) A C := by
      constructor
      · -- Subset relation
        intro p hp
        rw [comp_is_specified] at hp
        obtain ⟨x, z, hp_eq, y, hf_in, hg_in⟩ := hp
        rw [hp_eq, OrderedPair_mem_CartesianProduct]
        constructor
        · have := hf.1 ⟨x, y⟩ hf_in
          rw [OrderedPair_mem_CartesianProduct] at this
          exact this.1
        · have := hg.1 ⟨y, z⟩ hg_in
          rw [OrderedPair_mem_CartesianProduct] at this
          exact this.2
      · -- Total and Unique
        intro x hx
        -- f is total on A
        obtain ⟨y, hy_unique⟩ := hf.2 x hx
        have hy_in_B : y ∈ B := by
          have := hf.1 ⟨x, y⟩ hy_unique.1
          rw [OrderedPair_mem_CartesianProduct] at this
          exact this.2
        -- g is total on B
        obtain ⟨z, hz_unique⟩ := hg.2 y hy_in_B
        exists z
        constructor
        · show ⟨x, z⟩ ∈ g ∘ f
          rw [comp_is_specified]
          refine ⟨x, z, rfl, y, hy_unique.1, hz_unique.1⟩
        · intro z' hz'
          rw [comp_is_specified] at hz'
          obtain ⟨x', z'', h_eq, y', hf', hg'⟩ := hz'
          have hx_eq : x = x' := (Eq_of_OrderedPairs_given_projections x z' x' z'' h_eq).1
          subst hx_eq
          have hz_eq : z' = z'' := (Eq_of_OrderedPairs_given_projections x z' x z'' h_eq).2
          subst hz_eq
          -- y' must be y
          have hy_eq : y' = y := hy_unique.2 y' hf'
          subst hy_eq
          -- z' must be z
          exact hz_unique.2 z' hg'

    /-- Identity Function on A -/
    noncomputable def IdFunction (A : U) : U := IdRel A

    theorem apply_id (A x : U) (hx : x ∈ A) :
      (IdFunction A)⦅x⦆ = x := by
      apply apply_eq (IdFunction A) x x
      · apply ExistsUnique.intro x
        · unfold IdFunction
          rw [mem_IdRel]; exact ⟨hx, rfl⟩
        · intro y' hy'
          unfold IdFunction at hy'
          rw [mem_IdRel] at hy'; exact hy'.2.symm
      · unfold IdFunction
        rw [mem_IdRel]; exact ⟨hx, rfl⟩

    /-! ============================================================ -/
    /-! ### INVERSE FUNCTION ### -/
    /-! ============================================================ -/

    noncomputable def InverseFunction (f : U) : U := InverseRel f

    notation:100 f "⁻¹" => InverseFunction f

    theorem inverse_is_specified (f p : U) :
      p ∈ f⁻¹ ↔ isOrderedPair p ∧ ⟨snd p, fst p⟩ ∈ f := by
      unfold InverseFunction InverseRel
      rw [SpecSet_is_specified]
      constructor
      · intro h
        constructor
        · -- p ∈ range f × domain f, so p is a pair
          have : p ∈ range f ×ₛ domain f := h.1
          rw [CartesianProduct_is_specified] at this
          exact this.1
        · exact h.2
      · intro h
        obtain ⟨hp_pair, h_in_f⟩ := h
        constructor
        · -- Need to prove p is in the universe (range f × domain f)
          rw [CartesianProduct_is_specified]
          refine ⟨hp_pair, ?_, ?_⟩
          · -- fst p ∈ range f
            exact pair_mem_implies_snd_in_range f (snd p) (fst p) h_in_f
          · -- snd p ∈ domain f
            exact pair_mem_implies_fst_in_domain f (snd p) (fst p) h_in_f
        · exact h_in_f

    /-! ============================================================ -/
    /-! ### RESTRICTION OF FUNCTIONS ### -/
    /-! ============================================================ -/

    /-- Restriction of a relation f to a domain C: f ↾ C = { p ∈ f | fst p ∈ C } -/
    noncomputable def Restriction (f C : U) : U :=
      SpecSet f (fun p => fst p ∈ C)

    notation:60 f " ↾ " C:61 => Restriction f C

    theorem Restriction_is_specified (f C p : U) :
      p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C := by
      unfold Restriction
      exact SpecSet_is_specified f p (fun p => fst p ∈ C)

    theorem Restriction_subset (f C : U) : (f ↾ C) ⊆ f := by
      intro p hp
      rw [Restriction_is_specified] at hp
      exact hp.1

    /-- Restriction of a function is a function on the restricted domain -/
    theorem Restriction_is_function (f A B C : U)
      (hf : isFunctionFromTo f A B) (hC : C ⊆ A) :
      isFunctionFromTo (f ↾ C) C B := by
      constructor
      · -- Subset of C × B
        intro p hp
        rw [Restriction_is_specified] at hp
        obtain ⟨hp_f, h_fst_C⟩ := hp
        have h_sub : p ∈ A ×ₛ B := hf.1 p hp_f
        -- p ∈ f and fst p ∈ C, with f ⊆ A × B, so p ∈ C × B
        rw [CartesianProduct_is_specified] at h_sub ⊢
        exact ⟨h_sub.1, h_fst_C, h_sub.2.2⟩
      · intro x hx
        -- x ∈ C implies x ∈ A
        have hx_A : x ∈ A := hC x hx
        -- f is total on A, so ∃! y, ⟨x, y⟩ ∈ f
        obtain ⟨y, hy⟩ := hf.2 x hx_A
        apply ExistsUnique.intro y
        · -- Prove ⟨x, y⟩ ∈ f ↾ C
          rw [Restriction_is_specified]
          constructor
          · exact hy.1
          · rw [fst_of_ordered_pair]
            exact hx
        · -- Prove uniqueness
          intro y' hy'
          rw [Restriction_is_specified] at hy'
          exact hy.2 y' hy'.1

    /-- Application of restricted function equals application of original -/
    theorem Restriction_apply (f C x : U) (hx : x ∈ C) :
      apply (f ↾ C) x = apply f x := by
      unfold apply
      have h_iff : (∃! y, ⟨x, y⟩ ∈ f ↾ C) ↔ (∃! y, ⟨x, y⟩ ∈ f) := by
        constructor
        · intro h
          obtain ⟨y, hy, hunique⟩ := h
          rw [Restriction_is_specified] at hy
          refine ⟨y, hy.1, ?_⟩
          intro y' hy'
          apply hunique y'
          show ⟨x, y'⟩ ∈ f ↾ C
          rw [Restriction_is_specified]
          constructor
          · exact hy'
          · rw [fst_of_ordered_pair]
            exact hx
        · intro h
          obtain ⟨y, hy, hunique⟩ := h
          refine ⟨y, ?_, ?_⟩
          · show ⟨x, y⟩ ∈ f ↾ C
            rw [Restriction_is_specified]
            constructor
            · exact hy
            · rw [fst_of_ordered_pair]
              exact hx
          · intro y' hy'
            rw [Restriction_is_specified] at hy'
            exact hunique y' hy'.1

      by_cases h : ∃! y, ⟨x, y⟩ ∈ f
      · rw [dif_pos h]
        have h' : ∃! y, ⟨x, y⟩ ∈ f ↾ C := h_iff.mpr h
        rw [dif_pos h']
        have h_eq_preds : (fun y => ⟨x, y⟩ ∈ f ↾ C) = (fun y => ⟨x, y⟩ ∈ f) := by
          apply funext
          intro y
          apply propext
          rw [Restriction_is_specified]
          constructor
          · intro h_in; exact h_in.1
          · intro h_in
            constructor
            · exact h_in
            · rw [fst_of_ordered_pair]; exact hx
        congr
      · rw [dif_neg h]
        have h' : ¬∃! y, ⟨x, y⟩ ∈ f ↾ C := mt h_iff.mp h
        rw [dif_neg h']

    /-! ============================================================ -/
    /-! ### IMAGE AND PREIMAGE ### -/
    /-! ============================================================ -/

    /-- Image of a set X under f: f[X] = {y | ∃ x ∈ X, f(x) = y} -/
    noncomputable def ImageSet (f X : U) : U :=
      range (f ↾ X)

    notation:90 f "[" X "]" => ImageSet f X

    /-- Preimage of a set Y under f: f⁻¹[Y] = {x | f(x) ∈ Y} -/
    noncomputable def PreimageSet (f Y : U) : U :=
      SpecSet (domain f) (fun x => ∃ y, ⟨x, y⟩ ∈ f ∧ y ∈ Y)

    notation:90 f "⁻¹[" Y "]" => PreimageSet f Y

    /-! ============================================================ -/
    /-! ### EQUIPOTENCE AND DOMINANCE ### -/
    /-! ============================================================ -/

    def isInjective (f : U) : Prop :=
      ∀ x₁ x₂ y, ⟨x₁, y⟩ ∈ f → ⟨x₂, y⟩ ∈ f → x₁ = x₂

    def isSurjectiveOnto (f B : U) : Prop :=
      ∀ y, y ∈ B → ∃ x, ⟨x, y⟩ ∈ f

    def isBijection (f A B : U) : Prop :=
      isFunctionFromTo f A B ∧ isInjective f ∧ isSurjectiveOnto f B

    def isEquipotent (A B : U) : Prop :=
      ∃ f, isBijection f A B

    infix:50 " ≃ₛ " => isEquipotent

    def isDominatedBy (A B : U) : Prop :=
      ∃ f, isFunctionFromTo f A B ∧ isInjective f

    infix:50 " ≼ₛ " => isDominatedBy

    def isStrictlyDominatedBy (A B : U) : Prop :=
      (A ≼ₛ B) ∧ ¬(B ≼ₛ A)

    infix:50 " ≺ₛ " => isStrictlyDominatedBy

    /-! ============================================================ -/
    /-! ### ADDITIONAL THEOREMS FOR INVERSE ### -/
    /-! ============================================================ -/

    theorem injective_inverse_single_valued (f : U) (hf : isInjective f) :
      isSingleValued (f⁻¹) := by
      intro x y z h1 h2
      rw [inverse_is_specified] at h1 h2
      -- h1 : isOrderedPair ⟨x,y⟩ ∧ ⟨snd ⟨x,y⟩, fst ⟨x,y⟩⟩ ∈ f
      -- h2 : isOrderedPair ⟨x,z⟩ ∧ ⟨snd ⟨x,z⟩, fst ⟨x,z⟩⟩ ∈ f
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at h1 h2
      exact hf y z x h1.2 h2.2

  end Functions

  export Functions (
    isSingleValued
    isFunctionFromTo
    apply apply_mem apply_eq
    FunctionComposition comp_is_specified comp_is_function
    IdFunction apply_id
    InverseFunction inverse_is_specified
    Restriction Restriction_is_specified Restriction_subset Restriction_is_function Restriction_apply
    ImageSet PreimageSet
    isInjective isSurjectiveOnto isBijection
    isEquipotent isDominatedBy isStrictlyDominatedBy
    injective_inverse_single_valued
  )

end SetUniverse
