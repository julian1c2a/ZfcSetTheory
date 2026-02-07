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
    ImageSet ImageSet_is_specified PreimageSet PreimageSet_is_specified
    image_empty image_mono image_union preimage_union preimage_inter_subset preimage_inter_eq
  )

end SetUniverse
