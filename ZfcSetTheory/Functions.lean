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
* `ImageSet f X` - direct image f[X]
* `PreimageSet f Y` - preimage f⁻¹[Y]

## Main Theorems

* `comp_is_function` - composition of functions is a function
* `comp_assoc` - composition is associative
* `id_comp`, `comp_id` - identity is neutral
-/

namespace SetUniverse
  open Classical
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

    /-! ### Function Definitions -/

    /-- f is single-valued (functional): each x has at most one y -/
    def isSingleValued (f : U) : Prop :=
      ∀ x y₁ y₂, ⟨x, y₁⟩ ∈ f → ⟨x, y₂⟩ ∈ f → y₁ = y₂

    /-- f is a function from A to B: f ⊆ A ×ₛ B, total on A, single-valued -/
    def isFunctionFromTo (f A B : U) : Prop :=
      f ⊆ (A ×ₛ B) ∧
      (∀ x, x ∈ A → ∃ y, ⟨x, y⟩ ∈ f) ∧
      isSingleValued f

    /-- Domain of a function/relation -/
    noncomputable def Dom (f : U) : U :=
      SpecSet (⋃ (⋃ f)) (fun x => ∃ y, ⟨x, y⟩ ∈ f)

    /-- Range (image) of a function/relation -/
    noncomputable def Ran (f : U) : U :=
      SpecSet (⋃ (⋃ f)) (fun y => ∃ x, ⟨x, y⟩ ∈ f)

    /-- Specification for Dom -/
    theorem Dom_is_specified (f x : U) :
        x ∈ Dom f ↔ ∃ y, ⟨x, y⟩ ∈ f := by
      unfold Dom
      rw [SpecSet_is_specified]
      constructor
      · intro hpair
        exact hpair.2
      · intro hex
        obtain ⟨y, hxy⟩ := hex
        refine ⟨?_, ⟨y, hxy⟩⟩
        -- x ∈ ⋃ (⋃ f)
        rw [UnionSet_is_specified]
        refine ⟨{x}, ?_, (Singleton_is_specified x x).mpr rfl⟩
        rw [UnionSet_is_specified]
        refine ⟨⟨x, y⟩, hxy, (OrderedPair_is_specified x y {x}).mpr (Or.inl rfl)⟩

    /-- Specification for Ran -/
    theorem Ran_is_specified (f y : U) :
        y ∈ Ran f ↔ ∃ x, ⟨x, y⟩ ∈ f := by
      unfold Ran
      rw [SpecSet_is_specified]
      constructor
      · intro hpair
        exact hpair.2
      · intro hex
        obtain ⟨x, hxy⟩ := hex
        refine ⟨?_, ⟨x, hxy⟩⟩
        -- y ∈ ⋃ (⋃ f)
        rw [UnionSet_is_specified]
        refine ⟨{x, y}, ?_, (PairSet_is_specified x y y).mpr (Or.inr rfl)⟩
        rw [UnionSet_is_specified]
        refine ⟨⟨x, y⟩, hxy, (OrderedPair_is_specified x y {x, y}).mpr (Or.inr rfl)⟩

    /-! ### Function Application -/

    /-- Apply function f to x: the unique y such that ⟨x, y⟩ ∈ f -/
    noncomputable def apply (f x : U) : U :=
      if h : ∃ y, ⟨x, y⟩ ∈ f then Classical.choose h else ∅

    notation:max f "⦅" x "⦆" => apply f x

    /-- If f is single-valued and ⟨x, y⟩ ∈ f, then f⦅x⦆ = y -/
    theorem apply_eq (f x y : U) (hf : isSingleValued f) (hxy : ⟨x, y⟩ ∈ f) :
        f⦅x⦆ = y := by
      unfold apply
      have hex : ∃ y, ⟨x, y⟩ ∈ f := ⟨y, hxy⟩
      simp only [hex, dite_true]
      have h_spec := Classical.choose_spec hex
      exact hf x _ _ h_spec hxy

    /-- If x ∈ Dom f and f is single-valued, then ⟨x, f⦅x⦆⟩ ∈ f -/
    theorem apply_mem (f x : U) (hf : isSingleValued f) (hx : x ∈ Dom f) :
        ⟨x, f⦅x⦆⟩ ∈ f := by
      rw [Dom_is_specified] at hx
      obtain ⟨y, hxy⟩ := hx
      have h_eq : f⦅x⦆ = y := apply_eq f x y hf hxy
      rw [h_eq]
      exact hxy

    /-! ### Identity Function -/

    /-- Identity function on A: { ⟨x, x⟩ | x ∈ A } -/
    noncomputable def IdFunction (A : U) : U :=
      SpecSet (A ×ₛ A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, x⟩)

    notation:max "𝟙" A => IdFunction A

    /-- Specification for IdFunction -/
    theorem IdFunction_is_specified (A x y : U) :
        ⟨x, y⟩ ∈ (𝟙 A) ↔ x ∈ A ∧ x = y := by
      unfold IdFunction
      rw [SpecSet_is_specified]
      constructor
      · intro hpair
        obtain ⟨_, z, hz_A, hz_eq⟩ := hpair
        have h_pair := (OrderedPair_eq_iff x y z z).mp hz_eq
        exact ⟨h_pair.1 ▸ hz_A, h_pair.1.trans h_pair.2.symm⟩
      · intro hpair
        obtain ⟨hx_A, hxy⟩ := hpair
        refine ⟨?_, x, hx_A, hxy ▸ rfl⟩
        rw [hxy, OrderedPair_mem_CartesianProduct]
        exact ⟨hxy ▸ hx_A, hxy ▸ hx_A⟩

    /-- IdFunction is single-valued -/
    theorem IdFunction_single_valued (A : U) : isSingleValued (𝟙 A) := by
      intro x y₁ y₂ hy₁ hy₂
      have h₁ := (IdFunction_is_specified A x y₁).mp hy₁
      have h₂ := (IdFunction_is_specified A x y₂).mp hy₂
      exact h₁.2.symm.trans h₂.2

    /-- IdFunction is a function from A to A -/
    theorem IdFunction_is_function (A : U) : isFunctionFromTo (𝟙 A) A A := by
      refine ⟨?_, ?_, IdFunction_single_valued A⟩
      · -- 𝟙 A ⊆ A ×ₛ A
        intro p hp
        unfold IdFunction at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      · -- ∀ x ∈ A, ∃ y, ⟨x, y⟩ ∈ 𝟙 A
        intro x hx
        exact ⟨x, (IdFunction_is_specified A x x).mpr ⟨hx, rfl⟩⟩

    /-- Applying identity returns the same element -/
    theorem apply_id (A x : U) (hx : x ∈ A) : (𝟙 A)⦅x⦆ = x := by
      apply apply_eq
      · exact IdFunction_single_valued A
      · exact (IdFunction_is_specified A x x).mpr ⟨hx, rfl⟩

    /-! ### Function Composition -/

    /-- Composition of g and f: g ∘ f = { ⟨x, z⟩ | ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g } -/
    noncomputable def FunctionComposition (g f : U) : U :=
      SpecSet ((Dom f) ×ₛ (Ran g)) (fun p =>
        ∃ x z, p = ⟨x, z⟩ ∧ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g)

    infixr:90 " ∘ₛ " => FunctionComposition

    /-- Specification for composition -/
    theorem comp_is_specified (g f x z : U) :
        ⟨x, z⟩ ∈ (g ∘ₛ f) ↔ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g := by
      unfold FunctionComposition
      rw [SpecSet_is_specified]
      constructor
      · intro hpair
        obtain ⟨_, x', z', hp_eq, y, hxy, hyz⟩ := hpair
        have h_pair := (OrderedPair_eq_iff x z x' z').mp hp_eq
        rw [h_pair.1, h_pair.2]
        exact ⟨y, hxy, hyz⟩
      · intro hex
        obtain ⟨y, hxy, hyz⟩ := hex
        refine ⟨?_, x, z, rfl, y, hxy, hyz⟩
        rw [OrderedPair_mem_CartesianProduct]
        exact ⟨(Dom_is_specified f x).mpr ⟨y, hxy⟩, (Ran_is_specified g z).mpr ⟨y, hyz⟩⟩

    /-- Composition of single-valued functions is single-valued -/
    theorem comp_single_valued (g f : U) (hf : isSingleValued f) (hg : isSingleValued g) :
        isSingleValued (g ∘ₛ f) := by
      intro x z₁ z₂ hz₁ hz₂
      rw [comp_is_specified] at hz₁ hz₂
      obtain ⟨y₁, hxy₁, hy₁z₁⟩ := hz₁
      obtain ⟨y₂, hxy₂, hy₂z₂⟩ := hz₂
      have h_y_eq : y₁ = y₂ := hf x y₁ y₂ hxy₁ hxy₂
      rw [h_y_eq] at hy₁z₁
      exact hg y₂ z₁ z₂ hy₁z₁ hy₂z₂

    /-- Composition of functions is a function -/
    theorem comp_is_function (f g A B C : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C) :
        isFunctionFromTo (g ∘ₛ f) A C := by
      obtain ⟨hf_sub, hf_total, hf_sv⟩ := hf
      obtain ⟨hg_sub, hg_total, hg_sv⟩ := hg
      refine ⟨?_, ?_, comp_single_valued g f hf_sv hg_sv⟩
      · -- g ∘ₛ f ⊆ A ×ₛ C
        intro p hp
        unfold FunctionComposition at hp
        rw [SpecSet_is_specified] at hp
        obtain ⟨_, x, z, hp_eq, y, hxy, hyz⟩ := hp
        rw [hp_eq, OrderedPair_mem_CartesianProduct]
        have h1 := hf_sub ⟨x, y⟩ hxy
        have h2 := hg_sub ⟨y, z⟩ hyz
        rw [OrderedPair_mem_CartesianProduct] at h1 h2
        exact ⟨h1.1, h2.2⟩
      · -- ∀ x ∈ A, ∃ z, ⟨x, z⟩ ∈ g ∘ₛ f
        intro x hx
        -- f is total, so there exists y with ⟨x, y⟩ ∈ f
        obtain ⟨y, hxy⟩ := hf_total x hx
        -- y ∈ B
        have hy_B : y ∈ B := by
          have h := hf_sub ⟨x, y⟩ hxy
          rw [OrderedPair_mem_CartesianProduct] at h
          exact h.2
        -- g is total, so there exists z with ⟨y, z⟩ ∈ g
        obtain ⟨z, hyz⟩ := hg_total y hy_B
        exact ⟨z, (comp_is_specified g f x z).mpr ⟨y, hxy, hyz⟩⟩

    /-- Composition with identity on the right -/
    theorem comp_id_right (f A B : U) (hf : isFunctionFromTo f A B) :
        (f ∘ₛ 𝟙 A) = f := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        unfold FunctionComposition at hp
        rw [SpecSet_is_specified] at hp
        obtain ⟨_, x, z, hp_eq, y, hxy, hyz⟩ := hp
        rw [IdFunction_is_specified] at hxy
        rw [hp_eq, hxy.2]
        exact hyz
      · intro hp
        -- p ∈ f, so p = ⟨x, y⟩ for some x ∈ A, y ∈ B
        have h_sub := hf.1 p hp
        rw [CartesianProduct_is_specified] at h_sub
        obtain ⟨h_op, hx_A, hy_B⟩ := h_sub
        obtain ⟨x, y, hp_eq⟩ := h_op
        rw [hp_eq] at hp hx_A hy_B ⊢
        simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hx_A hy_B
        rw [comp_is_specified]
        exact ⟨x, (IdFunction_is_specified A x x).mpr ⟨hx_A, rfl⟩, hp⟩

    /-- Composition with identity on the left -/
    theorem comp_id_left (f A B : U) (hf : isFunctionFromTo f A B) :
        ((𝟙 B) ∘ₛ f) = f := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        unfold FunctionComposition at hp
        rw [SpecSet_is_specified] at hp
        obtain ⟨_, x, z, hp_eq, y, hxy, hyz⟩ := hp
        have h_id := (IdFunction_is_specified B y z).mp hyz
        rw [hp_eq, ← h_id.2]
        exact hxy
      · intro hp
        have h_sub := hf.1 p hp
        rw [CartesianProduct_is_specified] at h_sub
        obtain ⟨h_op, hx_A, hy_B⟩ := h_sub
        obtain ⟨x, y, hp_eq⟩ := h_op
        rw [hp_eq] at hp hx_A hy_B ⊢
        simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hx_A hy_B
        rw [comp_is_specified]
        exact ⟨y, hp, (IdFunction_is_specified B y y).mpr ⟨hy_B, rfl⟩⟩

    /-! ### Inverse Function -/

    /-- Inverse relation: { ⟨y, x⟩ | ⟨x, y⟩ ∈ f } -/
    noncomputable def InverseFunction (f : U) : U :=
      SpecSet ((Ran f) ×ₛ (Dom f)) (fun p =>
        ∃ x y, p = ⟨y, x⟩ ∧ ⟨x, y⟩ ∈ f)

    postfix:max "⁻¹ˢ" => InverseFunction

    /-- Specification for inverse -/
    theorem inverse_is_specified (f y x : U) :
        ⟨y, x⟩ ∈ f⁻¹ˢ ↔ ⟨x, y⟩ ∈ f := by
      unfold InverseFunction
      rw [SpecSet_is_specified]
      constructor
      · intro hpair
        obtain ⟨_, x', y', hp_eq, hxy'⟩ := hpair
        have h_pair := (OrderedPair_eq_iff y x y' x').mp hp_eq
        rw [h_pair.1, h_pair.2]
        exact hxy'
      · intro hxy
        refine ⟨?_, x, y, rfl, hxy⟩
        rw [OrderedPair_mem_CartesianProduct]
        exact ⟨(Ran_is_specified f y).mpr ⟨x, hxy⟩, (Dom_is_specified f x).mpr ⟨y, hxy⟩⟩

    /-- f is injective if different inputs give different outputs -/
    def isInjective (f : U) : Prop :=
      ∀ x₁ x₂ y, ⟨x₁, y⟩ ∈ f → ⟨x₂, y⟩ ∈ f → x₁ = x₂

    /-- f is surjective onto B if every element of B is in the range -/
    def isSurjectiveOnto (f B : U) : Prop :=
      ∀ y, y ∈ B → ∃ x, ⟨x, y⟩ ∈ f

    /-- f is a bijection from A to B -/
    def isBijection (f A B : U) : Prop :=
      isFunctionFromTo f A B ∧ isInjective f ∧ isSurjectiveOnto f B

    /-- Injective function has single-valued inverse -/
    theorem injective_inverse_single_valued (f : U) (hf : isInjective f) :
        isSingleValued (f⁻¹ˢ) := by
      intro y x₁ x₂ hx₁ hx₂
      rw [inverse_is_specified] at hx₁ hx₂
      exact hf x₁ x₂ y hx₁ hx₂

    /-- Single-valued function has injective inverse -/
    theorem single_valued_inverse_injective (f : U) (hf : isSingleValued f) :
        isInjective (f⁻¹ˢ) := by
      intro y₁ y₂ x hy₁ hy₂
      rw [inverse_is_specified] at hy₁ hy₂
      exact hf x y₁ y₂ hy₁ hy₂

    /-! ### Invertibility -/

    /-- f has a left inverse g: g ∘ f = id on A -/
    def hasLeftInverse (f A B g : U) : Prop :=
      isFunctionFromTo f A B ∧ isFunctionFromTo g B A ∧
      ∀ x, x ∈ A → g⦅f⦅x⦆⦆ = x

    /-- f has a right inverse g: f ∘ g = id on B -/
    def hasRightInverse (f A B g : U) : Prop :=
      isFunctionFromTo f A B ∧ isFunctionFromTo g B A ∧
      ∀ y, y ∈ B → f⦅g⦅y⦆⦆ = y

    /-- f is left invertible -/
    def isLeftInvertible (f A B : U) : Prop :=
      ∃ g, hasLeftInverse f A B g

    /-- f is right invertible -/
    def isRightInvertible (f A B : U) : Prop :=
      ∃ g, hasRightInverse f A B g

    /-- f is invertible (has a two-sided inverse) -/
    def isInvertible (f A B : U) : Prop :=
      ∃ g, hasLeftInverse f A B g ∧ hasRightInverse f A B g

    /-! ### Injectivity Equivalences -/

    /-- Alternative characterization: injective means f⁻¹ is single-valued -/
    theorem injective_iff_inverse_functional (f : U) :
        isInjective f ↔ isSingleValued (f⁻¹ˢ) := by
      constructor
      · exact injective_inverse_single_valued f
      · intro hf_inv x₁ x₂ y hx₁y hx₂y
        have h₁ : ⟨y, x₁⟩ ∈ f⁻¹ˢ := (inverse_is_specified f y x₁).mpr hx₁y
        have h₂ : ⟨y, x₂⟩ ∈ f⁻¹ˢ := (inverse_is_specified f y x₂).mpr hx₂y
        exact hf_inv y x₁ x₂ h₁ h₂

    /-- Injective function: composition with apply recovers the original element -/
    theorem injective_apply_eq (f A B x₁ x₂ : U)
        (hf : isFunctionFromTo f A B) (hinj : isInjective f)
        (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (heq : f⦅x₁⦆ = f⦅x₂⦆) : x₁ = x₂ := by
      obtain ⟨_, hf_total, hf_sv⟩ := hf
      obtain ⟨y₁, hx₁y₁⟩ := hf_total x₁ hx₁
      obtain ⟨y₂, hx₂y₂⟩ := hf_total x₂ hx₂
      have h₁ : f⦅x₁⦆ = y₁ := apply_eq f x₁ y₁ hf_sv hx₁y₁
      have h₂ : f⦅x₂⦆ = y₂ := apply_eq f x₂ y₂ hf_sv hx₂y₂
      rw [h₁, h₂] at heq
      rw [← heq] at hx₂y₂
      exact hinj x₁ x₂ y₁ hx₁y₁ hx₂y₂

    /-! ### Surjectivity Equivalences -/

    /-- Surjective means the range equals the codomain -/
    theorem surjective_iff_range_eq (f A B : U) (hf : isFunctionFromTo f A B) :
        isSurjectiveOnto f B ↔ Ran f = B := by
      constructor
      · intro hsurj
        apply ExtSet
        intro y
        constructor
        · intro hy
          rw [Ran_is_specified] at hy
          obtain ⟨x, hxy⟩ := hy
          have h := hf.1 ⟨x, y⟩ hxy
          rw [OrderedPair_mem_CartesianProduct] at h
          exact h.2
        · intro hy
          obtain ⟨x, hxy⟩ := hsurj y hy
          exact (Ran_is_specified f y).mpr ⟨x, hxy⟩
      · intro hran y hy
        rw [← hran] at hy
        rw [Ran_is_specified] at hy
        exact hy

    /-- For surjective functions, f⁻¹ is total on B -/
    theorem surjective_inverse_total (f A B : U)
        (_ : isFunctionFromTo f A B) (hsurj : isSurjectiveOnto f B) :
        ∀ y, y ∈ B → ∃ x, ⟨y, x⟩ ∈ f⁻¹ˢ := by
      intro y hy
      obtain ⟨x, hxy⟩ := hsurj y hy
      exact ⟨x, (inverse_is_specified f y x).mpr hxy⟩

    /-! ### Bijection Properties -/

    /-- Bijection has functional inverse -/
    theorem bijection_inverse_is_function (f A B : U) (hbij : isBijection f A B) :
        isFunctionFromTo (f⁻¹ˢ) B A := by
      obtain ⟨hf, hinj, hsurj⟩ := hbij
      refine ⟨?_, ?_, injective_inverse_single_valued f hinj⟩
      · -- f⁻¹ˢ ⊆ B ×ₛ A
        intro p hp
        unfold InverseFunction at hp
        rw [SpecSet_is_specified] at hp
        obtain ⟨hp_in, x, y, hp_eq, hxy⟩ := hp
        rw [hp_eq, OrderedPair_mem_CartesianProduct]
        have h := hf.1 ⟨x, y⟩ hxy
        rw [OrderedPair_mem_CartesianProduct] at h
        exact ⟨h.2, h.1⟩
      · -- f⁻¹ˢ is total on B
        exact surjective_inverse_total f A B hf hsurj

    /-- Inverse of bijection composed on right gives identity -/
    theorem bijection_comp_inverse_right (f A B : U) (hbij : isBijection f A B) :
        ∀ x, x ∈ A → (f⁻¹ˢ)⦅f⦅x⦆⦆ = x := by
      intro x hx
      obtain ⟨hf, hinj, _⟩ := hbij
      obtain ⟨_, hf_total, hf_sv⟩ := hf
      obtain ⟨y, hxy⟩ := hf_total x hx
      have h_fx : f⦅x⦆ = y := apply_eq f x y hf_sv hxy
      have h_inv : ⟨y, x⟩ ∈ f⁻¹ˢ := (inverse_is_specified f y x).mpr hxy
      have h_inv_sv := injective_inverse_single_valued f hinj
      have h_apply : (f⁻¹ˢ)⦅y⦆ = x := apply_eq (f⁻¹ˢ) y x h_inv_sv h_inv
      rw [h_fx, h_apply]

    /-- Inverse of bijection composed on left gives identity -/
    theorem bijection_comp_inverse_left (f A B : U) (hbij : isBijection f A B) :
        ∀ y, y ∈ B → f⦅(f⁻¹ˢ)⦅y⦆⦆ = y := by
      intro y hy
      obtain ⟨hf, hinj, hsurj⟩ := hbij
      obtain ⟨_, _, hf_sv⟩ := hf
      obtain ⟨x, hxy⟩ := hsurj y hy
      have h_inv : ⟨y, x⟩ ∈ f⁻¹ˢ := (inverse_is_specified f y x).mpr hxy
      have h_inv_sv := injective_inverse_single_valued f hinj
      have h_inv_apply : (f⁻¹ˢ)⦅y⦆ = x := apply_eq (f⁻¹ˢ) y x h_inv_sv h_inv
      have h_apply : f⦅x⦆ = y := apply_eq f x y hf_sv hxy
      rw [h_inv_apply, h_apply]

    /-- Inverse of inverse is original (for relations in A ×ₛ B) -/
    theorem inverse_inverse (f A B : U) (hf : f ⊆ A ×ₛ B) : (f⁻¹ˢ)⁻¹ˢ = f := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        -- p ∈ (f⁻¹ˢ)⁻¹ˢ
        -- (f⁻¹ˢ)⁻¹ˢ = { Ran(f⁻¹ˢ) ×ₛ Dom(f⁻¹ˢ) | ∃ x y, p = ⟨y, x⟩ ∧ ⟨x, y⟩ ∈ f⁻¹ˢ }
        unfold InverseFunction at hp
        rw [SpecSet_is_specified] at hp
        obtain ⟨_, a, b, hp_eq, hab⟩ := hp
        -- hp_eq : p = ⟨b, a⟩ (specification says p = ⟨y, x⟩ with y=b, x=a)
        -- hab : ⟨a, b⟩ ∈ f⁻¹ˢ (specification says ⟨x, y⟩ ∈ f⁻¹ˢ)
        -- Now unfold f⁻¹ˢ in hab
        rw [SpecSet_is_specified] at hab
        obtain ⟨_, c, d, hab_eq, hcd⟩ := hab
        -- hab_eq : ⟨a, b⟩ = ⟨d, c⟩
        -- hcd : ⟨c, d⟩ ∈ f
        -- From hab_eq: a = d and b = c
        have heq := Eq_of_OrderedPairs_given_projections a b d c hab_eq
        -- So ⟨c, d⟩ = ⟨b, a⟩ ∈ f
        rw [hp_eq, heq.2, heq.1]
        exact hcd
      · intro hp
        -- p ∈ f, and f ⊆ A ×ₛ B, so p is an ordered pair
        have h_in_prod := hf p hp
        rw [CartesianProduct_is_specified] at h_in_prod
        obtain ⟨h_op, _, _⟩ := h_in_prod
        obtain ⟨x, y, hp_eq⟩ := h_op
        -- p = ⟨x, y⟩ ∈ f, so ⟨y, x⟩ ∈ f⁻¹ˢ, so ⟨x, y⟩ ∈ (f⁻¹ˢ)⁻¹ˢ
        rw [hp_eq] at hp ⊢
        have h_inv : ⟨y, x⟩ ∈ f⁻¹ˢ := (inverse_is_specified f y x).mpr hp
        exact (inverse_is_specified (f⁻¹ˢ) x y).mpr h_inv

    /-! ### Main Theorem: Bijectivity ↔ Invertibility -/

    /-- Bijection implies invertibility -/
    theorem bijection_implies_invertible (f A B : U) (hbij : isBijection f A B) :
        isInvertible f A B := by
      refine ⟨f⁻¹ˢ, ?_, ?_⟩
      · -- hasLeftInverse
        refine ⟨hbij.1, bijection_inverse_is_function f A B hbij, ?_⟩
        exact bijection_comp_inverse_right f A B hbij
      · -- hasRightInverse
        refine ⟨hbij.1, bijection_inverse_is_function f A B hbij, ?_⟩
        exact bijection_comp_inverse_left f A B hbij

    /-- Left invertible implies injective -/
    theorem left_invertible_implies_injective (f A B : U)
        (hf : isFunctionFromTo f A B) (hleft : isLeftInvertible f A B) :
        isInjective f := by
      obtain ⟨g, hf', hg, hcomp⟩ := hleft
      intro x₁ x₂ y hx₁y hx₂y
      -- x₁ ∈ A and x₂ ∈ A
      have hx₁_A : x₁ ∈ A := by
        have h := hf.1 ⟨x₁, y⟩ hx₁y
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.1
      have hx₂_A : x₂ ∈ A := by
        have h := hf.1 ⟨x₂, y⟩ hx₂y
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.1
      -- f⦅x₁⦆ = y and f⦅x₂⦆ = y
      have hfx₁ : f⦅x₁⦆ = y := apply_eq f x₁ y hf.2.2 hx₁y
      have hfx₂ : f⦅x₂⦆ = y := apply_eq f x₂ y hf.2.2 hx₂y
      -- g⦅f⦅x₁⦆⦆ = x₁ and g⦅f⦅x₂⦆⦆ = x₂
      have h₁ := hcomp x₁ hx₁_A
      have h₂ := hcomp x₂ hx₂_A
      -- g⦅y⦆ = g⦅f⦅x₁⦆⦆ = x₁ and g⦅y⦆ = g⦅f⦅x₂⦆⦆ = x₂
      rw [hfx₁] at h₁
      rw [hfx₂] at h₂
      exact h₁.symm.trans h₂

    /-- Right invertible implies surjective -/
    theorem right_invertible_implies_surjective (f A B : U)
        (hf : isFunctionFromTo f A B) (hright : isRightInvertible f A B) :
        isSurjectiveOnto f B := by
      obtain ⟨g, hf', hg, hcomp⟩ := hright
      intro y hy
      -- g⦅y⦆ ∈ A
      have h_gy_A : g⦅y⦆ ∈ A := by
        have h_gy_dom : y ∈ Dom g := by
          rw [Dom_is_specified]
          obtain ⟨_, hg_total, _⟩ := hg
          obtain ⟨x, hyx⟩ := hg_total y hy
          exact ⟨x, hyx⟩
        have h_mem := apply_mem g y hg.2.2 h_gy_dom
        have h := hg.1 ⟨y, g⦅y⦆⟩ h_mem
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.2
      -- ⟨g⦅y⦆, f⦅g⦅y⦆⦆⟩ ∈ f
      have h_fx_dom : g⦅y⦆ ∈ Dom f := by
        rw [Dom_is_specified]
        obtain ⟨_, hf_total, _⟩ := hf
        exact hf_total (g⦅y⦆) h_gy_A
      have h_mem := apply_mem f (g⦅y⦆) hf.2.2 h_fx_dom
      -- f⦅g⦅y⦆⦆ = y
      have h_eq := hcomp y hy
      rw [h_eq] at h_mem
      exact ⟨g⦅y⦆, h_mem⟩

    /-- Invertibility implies bijectivity -/
    theorem invertible_implies_bijection (f A B : U)
        (hf : isFunctionFromTo f A B) (hinv : isInvertible f A B) :
        isBijection f A B := by
      obtain ⟨g, hleft, hright⟩ := hinv
      refine ⟨hf, ?_, ?_⟩
      · exact left_invertible_implies_injective f A B hf ⟨g, hleft⟩
      · exact right_invertible_implies_surjective f A B hf ⟨g, hright⟩

    /-- Main equivalence: Bijectivity ↔ Invertibility -/
    theorem bijection_iff_invertible (f A B : U) (hf : isFunctionFromTo f A B) :
        isBijection f A B ↔ isInvertible f A B := by
      constructor
      · exact bijection_implies_invertible f A B
      · intro hinv
        exact invertible_implies_bijection f A B hf hinv

    /-! ### Additional Injectivity/Surjectivity Results -/

    /-- Composition of injective functions is injective -/
    theorem comp_injective (f g : U) (hinj_f : isInjective f) (hinj_g : isInjective g) :
        isInjective (g ∘ₛ f) := by
      intro x₁ x₂ z hx₁z hx₂z
      rw [comp_is_specified] at hx₁z hx₂z
      obtain ⟨y₁, hx₁y₁, hy₁z⟩ := hx₁z
      obtain ⟨y₂, hx₂y₂, hy₂z⟩ := hx₂z
      have h_y_eq : y₁ = y₂ := hinj_g y₁ y₂ z hy₁z hy₂z
      rw [h_y_eq] at hx₁y₁
      exact hinj_f x₁ x₂ y₂ hx₁y₁ hx₂y₂

    /-- Composition of surjective functions is surjective -/
    theorem comp_surjective (f g A B C : U)
        (_ : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C)
        (hsurj_f : isSurjectiveOnto f B) (hsurj_g : isSurjectiveOnto g C) :
        isSurjectiveOnto (g ∘ₛ f) C := by
      intro z hz
      obtain ⟨y, hyz⟩ := hsurj_g z hz
      have hy_B : y ∈ B := by
        have h := hg.1 ⟨y, z⟩ hyz
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.1
      obtain ⟨x, hxy⟩ := hsurj_f y hy_B
      exact ⟨x, (comp_is_specified g f x z).mpr ⟨y, hxy, hyz⟩⟩

    /-- Composition of bijections is a bijection -/
    theorem comp_bijection (f g A B C : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C)
        (hbij_f : isBijection f A B) (hbij_g : isBijection g B C) :
        isBijection (g ∘ₛ f) A C := by
      refine ⟨comp_is_function f g A B C hf hg, ?_, ?_⟩
      · exact comp_injective f g hbij_f.2.1 hbij_g.2.1
      · exact comp_surjective f g A B C hf hg hbij_f.2.2 hbij_g.2.2

    /-- Identity is a bijection -/
    theorem id_is_bijection (A : U) : isBijection (𝟙 A) A A := by
      refine ⟨IdFunction_is_function A, ?_, ?_⟩
      · -- Injective
        intro x₁ x₂ y hx₁y hx₂y
        have h₁ := (IdFunction_is_specified A x₁ y).mp hx₁y
        have h₂ := (IdFunction_is_specified A x₂ y).mp hx₂y
        exact h₁.2.trans h₂.2.symm
      · -- Surjective
        intro y hy
        exact ⟨y, (IdFunction_is_specified A y y).mpr ⟨hy, rfl⟩⟩

    /-! ### Image and Preimage -/

    /-- Direct image: f[X] = { y | ∃ x ∈ X, ⟨x, y⟩ ∈ f } -/
    noncomputable def ImageSet (f X : U) : U :=
      SpecSet (Ran f) (fun y => ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f)

    notation:max f "⦃" X "⦄" => ImageSet f X

    /-- Specification for ImageSet -/
    theorem ImageSet_is_specified (f X y : U) :
        y ∈ f⦃X⦄ ↔ ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f := by
      unfold ImageSet
      rw [SpecSet_is_specified]
      constructor
      · intro hpair; exact hpair.2
      · intro hex
        obtain ⟨x, hx, hxy⟩ := hex
        constructor
        · exact (Ran_is_specified f y).mpr ⟨x, hxy⟩
        · exact ⟨x, hx, hxy⟩

    /-- Preimage: f⁻¹[Y] = { x | ∃ y ∈ Y, ⟨x, y⟩ ∈ f } -/
    noncomputable def PreimageSet (f Y : U) : U :=
      SpecSet (Dom f) (fun x => ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f)

    /-- Specification for PreimageSet -/
    theorem PreimageSet_is_specified (f Y x : U) :
        x ∈ PreimageSet f Y ↔ ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f := by
      unfold PreimageSet
      rw [SpecSet_is_specified]
      constructor
      · intro hpair; exact hpair.2
      · intro hex
        obtain ⟨y, hy, hxy⟩ := hex
        constructor
        · exact (Dom_is_specified f x).mpr ⟨y, hxy⟩
        · exact ⟨y, hy, hxy⟩

    /-- Image of empty set is empty -/
    theorem image_empty (f : U) : f⦃∅⦄ = ∅ := by
      apply ExtSet
      intro y
      constructor
      · intro hy
        rw [ImageSet_is_specified] at hy
        obtain ⟨x, hx, _⟩ := hy
        exact absurd hx (EmptySet_is_empty x)
      · intro hy
        exact absurd hy (EmptySet_is_empty y)

    /-- Image preserves subset -/
    theorem image_mono (f X Y : U) (h : X ⊆ Y) : f⦃X⦄ ⊆ f⦃Y⦄ := by
      intro z hz
      rw [ImageSet_is_specified] at hz ⊢
      obtain ⟨x, hx, hxz⟩ := hz
      exact ⟨x, h x hx, hxz⟩

    /-- Image of union -/
    theorem image_union (f X Y : U) : f⦃BinUnion X Y⦄ = BinUnion (f⦃X⦄) (f⦃Y⦄) := by
      apply ExtSet
      intro z
      constructor
      · intro hz
        rw [ImageSet_is_specified] at hz
        obtain ⟨x, hx, hxz⟩ := hz
        rw [BinUnion_is_specified] at hx
        rw [BinUnion_is_specified]
        cases hx with
        | inl hxX =>
          left
          exact (ImageSet_is_specified f X z).mpr ⟨x, hxX, hxz⟩
        | inr hxY =>
          right
          exact (ImageSet_is_specified f Y z).mpr ⟨x, hxY, hxz⟩
      · intro hz
        rw [BinUnion_is_specified] at hz
        rw [ImageSet_is_specified]
        cases hz with
        | inl hzX =>
          rw [ImageSet_is_specified] at hzX
          obtain ⟨x, hx, hxz⟩ := hzX
          exact ⟨x, (BinUnion_is_specified X Y x).mpr (Or.inl hx), hxz⟩
        | inr hzY =>
          rw [ImageSet_is_specified] at hzY
          obtain ⟨x, hx, hxz⟩ := hzY
          exact ⟨x, (BinUnion_is_specified X Y x).mpr (Or.inr hx), hxz⟩

    /-- Preimage of union -/
    theorem preimage_union (f X Y : U) :
        PreimageSet f (BinUnion X Y) = BinUnion (PreimageSet f X) (PreimageSet f Y) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [PreimageSet_is_specified] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        rw [BinUnion_is_specified] at hy
        rw [BinUnion_is_specified]
        cases hy with
        | inl hyX =>
          left
          exact (PreimageSet_is_specified f X x).mpr ⟨y, hyX, hxy⟩
        | inr hyY =>
          right
          exact (PreimageSet_is_specified f Y x).mpr ⟨y, hyY, hxy⟩
      · intro hx
        rw [BinUnion_is_specified] at hx
        rw [PreimageSet_is_specified]
        cases hx with
        | inl hxX =>
          rw [PreimageSet_is_specified] at hxX
          obtain ⟨y, hy, hxy⟩ := hxX
          exact ⟨y, (BinUnion_is_specified X Y y).mpr (Or.inl hy), hxy⟩
        | inr hxY =>
          rw [PreimageSet_is_specified] at hxY
          obtain ⟨y, hy, hxy⟩ := hxY
          exact ⟨y, (BinUnion_is_specified X Y y).mpr (Or.inr hy), hxy⟩

    /-- Preimage of intersection (subset direction) -/
    theorem preimage_inter_subset (f X Y : U) :
        PreimageSet f (BinInter X Y) ⊆ BinInter (PreimageSet f X) (PreimageSet f Y) := by
      intro x hx
      rw [PreimageSet_is_specified] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rw [BinInter_is_specified] at hy
      rw [BinInter_is_specified]
      constructor
      · exact (PreimageSet_is_specified f X x).mpr ⟨y, hy.1, hxy⟩
      · exact (PreimageSet_is_specified f Y x).mpr ⟨y, hy.2, hxy⟩

    /-- For single-valued functions, preimage of intersection is exact -/
    theorem preimage_inter_eq (f X Y : U) (hf : isSingleValued f) :
        PreimageSet f (BinInter X Y) = BinInter (PreimageSet f X) (PreimageSet f Y) := by
      apply ExtSet
      intro x
      constructor
      · exact fun hx => preimage_inter_subset f X Y x hx
      · intro hx
        rw [BinInter_is_specified] at hx
        obtain ⟨hxX, hxY⟩ := hx
        rw [PreimageSet_is_specified] at hxX hxY ⊢
        obtain ⟨y₁, hy₁, hxy₁⟩ := hxX
        obtain ⟨y₂, hy₂, hxy₂⟩ := hxY
        have h_eq : y₁ = y₂ := hf x y₁ y₂ hxy₁ hxy₂
        exact ⟨y₁, (BinInter_is_specified X Y y₁).mpr ⟨hy₁, h_eq ▸ hy₂⟩, hxy₁⟩

  end Functions

  -- Export key definitions and theorems
  export Functions (
    isSingleValued isFunctionFromTo
    Dom Ran Dom_is_specified Ran_is_specified
    apply apply_eq apply_mem
    IdFunction IdFunction_is_specified IdFunction_single_valued IdFunction_is_function apply_id
    FunctionComposition comp_is_specified comp_single_valued comp_is_function
    comp_id_right comp_id_left
    InverseFunction inverse_is_specified
    isInjective isSurjectiveOnto isBijection
    injective_inverse_single_valued single_valued_inverse_injective
    -- Invertibility
    hasLeftInverse hasRightInverse isLeftInvertible isRightInvertible isInvertible
    injective_iff_inverse_functional injective_apply_eq
    surjective_iff_range_eq surjective_inverse_total
    bijection_inverse_is_function bijection_comp_inverse_right bijection_comp_inverse_left
    inverse_inverse
    bijection_implies_invertible left_invertible_implies_injective right_invertible_implies_surjective
    invertible_implies_bijection bijection_iff_invertible
    comp_injective comp_surjective comp_bijection id_is_bijection
    -- Image/Preimage
    ImageSet ImageSet_is_specified PreimageSet PreimageSet_is_specified
    image_empty image_mono image_union preimage_union preimage_inter_subset preimage_inter_eq
  )

end SetUniverse
