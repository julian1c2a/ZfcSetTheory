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
import ZfcSetTheory.Functions

/-!
# Cardinality Theorems

This file develops fundamental theorems about cardinality:
* Cantor's theorem: There is no surjection from A to 𝒫(A)
* Cantor-Schröder-Bernstein theorem: Mutual injections imply bijection

## Main Results

* `cantor_no_surjection` - No surjection exists from A to 𝒫(A)
* `cantor_strict_dominance` - A ≺ₛ 𝒫(A)
* `cantor_schroeder_bernstein` - A ≼ₛ B ∧ B ≼ₛ A → A ≃ₛ B

## References

* Cantor's diagonal argument (1891)
* Cantor-Schröder-Bernstein theorem (various proofs: Dedekind, Bernstein, Banach)
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
  open SetUniverse.Functions
  universe u
  variable {U : Type u}

  namespace Cardinality

    /-! ============================================================ -/
    /-! ### CANTOR'S THEOREM ### -/
    /-! ============================================================ -/

    /-! Cantor's theorem states that for any set A, there is no surjection
        from A onto its power set 𝒫(A). This is proved using the diagonal
        argument: given any function f: A → 𝒫(A), the set
        D = { x ∈ A | x ∉ f(x) } cannot be in the range of f. -/

    /-- The diagonal set: { x ∈ A | x ∉ f⦅x⦆ } -/
    noncomputable def DiagonalSet (f A : U) : U :=
      SpecSet A (fun x => x ∉ f⦅x⦆)

    /-- Characterization of the diagonal set -/
    theorem DiagonalSet_is_specified (f A x : U) :
        x ∈ DiagonalSet f A ↔ x ∈ A ∧ x ∉ f⦅x⦆ := by
      unfold DiagonalSet
      exact SpecSet_is_specified A x (fun x => x ∉ f⦅x⦆)

    /-- The diagonal set is a subset of A, hence in 𝒫(A) -/
    theorem DiagonalSet_subset (f A : U) : DiagonalSet f A ⊆ A := by
      intro x hx
      rw [DiagonalSet_is_specified] at hx
      exact hx.1

    /-- The diagonal set is in the power set of A -/
    theorem DiagonalSet_in_PowerSet (f A : U) : DiagonalSet f A ∈ 𝒫 A := by
      rw [PowerSet_is_specified]
      exact DiagonalSet_subset f A

    /-- Key lemma: The diagonal set is not in the range of any function f: A → 𝒫(A) -/
    theorem DiagonalSet_not_in_range (f A : U) :
        ¬∃ d, d ∈ A ∧ f⦅d⦆ = DiagonalSet f A := by
      intro hex
      obtain ⟨d, hd_A, hd_eq⟩ := hex
      -- Consider whether d ∈ DiagonalSet f A
      by_cases h : d ∈ DiagonalSet f A
      · -- Case: d ∈ DiagonalSet f A
        -- By definition of DiagonalSet, d ∉ f⦅d⦆
        have h' := (DiagonalSet_is_specified f A d).mp h
        have h_not : d ∉ f⦅d⦆ := h'.2
        -- But f⦅d⦆ = DiagonalSet f A, so d ∉ DiagonalSet f A
        rw [hd_eq] at h_not
        exact h_not h
      · -- Case: d ∉ DiagonalSet f A
        -- Since d ∈ A and d ∉ DiagonalSet f A, we have ¬(d ∉ f⦅d⦆)
        -- i.e., d ∈ f⦅d⦆
        have h_in : d ∈ f⦅d⦆ := Classical.byContradiction fun h_not_in =>
          h ((DiagonalSet_is_specified f A d).mpr ⟨hd_A, h_not_in⟩)
        -- But f⦅d⦆ = DiagonalSet f A, so d ∈ DiagonalSet f A
        rw [hd_eq] at h_in
        exact h h_in

    /-- Cantor's Theorem: There is no surjection from A to 𝒫(A) -/
    theorem cantor_no_surjection (f A : U) (hf : isFunctionFromTo f A (𝒫 A)) :
        ¬isSurjectiveOnto f (𝒫 A) := by
      intro hsurj
      -- DiagonalSet f A ∈ 𝒫 A
      have h_diag_in : DiagonalSet f A ∈ 𝒫 A := DiagonalSet_in_PowerSet f A
      -- By surjectivity, there exists d ∈ A with f⦅d⦆ = DiagonalSet f A
      obtain ⟨d, hd⟩ := hsurj (DiagonalSet f A) h_diag_in
      -- d ∈ A
      have hd_A : d ∈ A := by
        have h := hf.1 ⟨d, DiagonalSet f A⟩ hd
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.1
      -- f⦅d⦆ = DiagonalSet f A
      have hd_eq : f⦅d⦆ = DiagonalSet f A := apply_eq f d (DiagonalSet f A) (hf.2 d hd_A) hd
      -- But this contradicts DiagonalSet_not_in_range
      exact DiagonalSet_not_in_range f A ⟨d, hd_A, hd_eq⟩

    /-- Corollary: There is no bijection from A to 𝒫(A) -/
    theorem cantor_no_bijection (f A : U) (hf : isFunctionFromTo f A (𝒫 A)) :
        ¬isBijection f A (𝒫 A) := by
      intro hbij
      exact cantor_no_surjection f A hf hbij.2.2

    /-- The canonical injection from A to 𝒫(A): x ↦ {x} -/
    noncomputable def singletonMap (A : U) : U :=
      SpecSet (A ×ₛ 𝒫 A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, {x}⟩)

    /-- The singleton map sends x to {x} -/
    theorem singletonMap_is_specified (A x y : U) :
        ⟨x, y⟩ ∈ singletonMap A ↔ x ∈ A ∧ y = {x} := by
      unfold singletonMap
      rw [SpecSet_is_specified]
      constructor
      · intro ⟨_, z, hz_A, hz_eq⟩
        have h := Eq_of_OrderedPairs_given_projections x y z {z} hz_eq
        rw [h.1]
        exact ⟨hz_A, h.2⟩
      · intro h
        constructor
        · rw [h.2, OrderedPair_mem_CartesianProduct]
          constructor
          · exact h.1
          · rw [PowerSet_is_specified]
            intro z hz
            rw [Singleton_is_specified] at hz
            rw [hz]
            exact h.1
        · exact ⟨x, h.1, h.2 ▸ rfl⟩

    /-- The singleton map is a function from A to 𝒫(A) -/
    theorem singletonMap_is_function (A : U) : isFunctionFromTo (singletonMap A) A (𝒫 A) := by
      constructor
      · -- singletonMap A ⊆ A ×ₛ 𝒫 A
        intro p hp
        unfold singletonMap at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      · -- ExistsUnique: for each x ∈ A, there exists unique y with ⟨x, y⟩ ∈ singletonMap A
        intro x hx
        refine ⟨{x}, (singletonMap_is_specified A x {x}).mpr ⟨hx, rfl⟩, ?_⟩
        intro y₂ hy₂
        rw [singletonMap_is_specified] at hy₂
        exact hy₂.2

    /-- The singleton map is injective -/
    theorem singletonMap_is_injective (A : U) : isInjective (singletonMap A) := by
      intro x₁ x₂ y hx₁ hx₂
      rw [singletonMap_is_specified] at hx₁ hx₂
      -- y = {x₁} and y = {x₂}
      have h : ({x₁} : U) = {x₂} := hx₁.2.symm.trans hx₂.2
      -- x₁ ∈ {x₁} = {x₂}, so x₁ = x₂
      have hx₁_in : x₁ ∈ ({x₁} : U) := (Singleton_is_specified x₁ x₁).mpr rfl
      rw [h] at hx₁_in
      exact (Singleton_is_specified x₂ x₁).mp hx₁_in

    /-- A is dominated by 𝒫(A) -/
    theorem A_dominated_by_PowerSet (A : U) : isDominatedBy A (𝒫 A) :=
      ⟨singletonMap A, singletonMap_is_function A, singletonMap_is_injective A⟩

    /-- 𝒫(A) does not dominate A via a surjection (hence not equipotent) -/
    theorem PowerSet_not_dominated_by_A (A : U) : ¬isDominatedBy (𝒫 A) A := by
      intro hdominates
      obtain ⟨g, hg_func, hg_inj⟩ := hdominates
      -- If g: 𝒫(A) → A is injective, we derive a contradiction via diagonal argument
      -- Consider D = { g⦅S⦆ | S ∈ 𝒫(A) ∧ g⦅S⦆ ∉ S }
      let D := SpecSet A (fun x => ∃ S, S ∈ 𝒫 A ∧ g⦅S⦆ = x ∧ x ∉ S)
      -- D ⊆ A, so D ∈ 𝒫(A)
      have hD_in : D ∈ 𝒫 A := by
        rw [PowerSet_is_specified]
        intro x hx
        rw [SpecSet_is_specified] at hx
        exact hx.1
      -- Consider g⦅D⦆
      -- g⦅D⦆ ∈ A
      have hgD_A : g⦅D⦆ ∈ A := by
        have h_mem := apply_mem g D (hg_func.2 D hD_in)
        have h := hg_func.1 ⟨D, g⦅D⦆⟩ h_mem
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.2
      -- Case analysis: g⦅D⦆ ∈ D or g⦅D⦆ ∉ D
      by_cases h : g⦅D⦆ ∈ D
      · -- g⦅D⦆ ∈ D means ∃ S, g⦅S⦆ = g⦅D⦆ ∧ g⦅D⦆ ∉ S
        rw [SpecSet_is_specified] at h
        obtain ⟨_, S, hS_pow, hgS_eq, hgD_notS⟩ := h
        -- By injectivity, S = D
        have hgS_mem := apply_mem g S (hg_func.2 S hS_pow)
        have hgD_mem := apply_mem g D (hg_func.2 D hD_in)
        -- By injectivity of g
        have hSD : S = D := by
          -- g is injective means ⟨S, g⦅S⦆⟩ ∈ g and ⟨D, g⦅D⦆⟩ ∈ g with same output
          -- Since g⦅S⦆ = g⦅D⦆ and g injective, S = D
          exact hg_inj S D (g⦅D⦆) (hgS_eq ▸ hgS_mem) hgD_mem
        -- But g⦅D⦆ ∉ S = D, contradiction with g⦅D⦆ ∈ D
        rw [hSD] at hgD_notS
        have h' := (SpecSet_is_specified A (g⦅D⦆) (fun x => ∃ S, S ∈ 𝒫 A ∧ g⦅S⦆ = x ∧ x ∉ S)).mpr
          ⟨hgD_A, D, hD_in, rfl, hgD_notS⟩
        exact hgD_notS h'
      · -- g⦅D⦆ ∉ D, but g⦅D⦆ ∈ A and g⦅D⦆ = g⦅D⦆ and g⦅D⦆ ∉ D
        -- So by definition g⦅D⦆ ∈ D
        have h_in : g⦅D⦆ ∈ D := by
          rw [SpecSet_is_specified]
          exact ⟨hgD_A, D, hD_in, rfl, h⟩
        exact h h_in

    /-- Cantor's Theorem (cardinal form): A ≺ₛ 𝒫(A) -/
    theorem cantor_strict_dominance (A : U) : isStrictlyDominatedBy A (𝒫 A) :=
      ⟨A_dominated_by_PowerSet A, PowerSet_not_dominated_by_A A⟩

    /-- Corollary: A and 𝒫(A) are not equipotent -/
    theorem cantor_not_equipotent (A : U) : ¬isEquipotent A (𝒫 A) := by
      intro heq
      obtain ⟨f, hf⟩ := heq
      exact cantor_no_bijection f A hf.1 hf

    /-! ============================================================ -/
    /-! ### CANTOR-SCHRÖDER-BERNSTEIN THEOREM ### -/
    /-! ============================================================ -/

    /-! The Cantor-Schröder-Bernstein theorem states that if there exist
        injections f: A → B and g: B → A, then there exists a bijection
        between A and B.

        The proof uses the idea of "ping-pong" orbits. Define:
        - C₀ = A \ g[B]  (elements not in range of g)
        - Cₙ₊₁ = g[f[Cₙ]]
        - C = ⋃ₙ Cₙ

        Then define h: A → B by:
        - h(x) = f(x) if x ∈ C
        - h(x) = g⁻¹(x) if x ∉ C (this is well-defined since x ∈ g[B])

        For our ZFC framework, we need to construct these sets carefully. -/

    /-- Set difference: A \ B = { x ∈ A | x ∉ B } -/
    noncomputable def SetDiff (A B : U) : U :=
      SpecSet A (fun x => x ∉ B)

    notation:70 A " ∖ " B => SetDiff A B

    /-- Specification for set difference -/
    theorem SetDiff_is_specified (A B x : U) :
        x ∈ (A ∖ B) ↔ x ∈ A ∧ x ∉ B := by
      unfold SetDiff
      exact SpecSet_is_specified A x (fun x => x ∉ B)

    /-- Set difference is a subset -/
    theorem SetDiff_subset (A B : U) : (A ∖ B) ⊆ A := by
      intro x hx
      rw [SetDiff_is_specified] at hx
      exact hx.1

    /-- Predicate: X contains A \ g[B] and is closed under g ∘ f -/
    def isCSB_closed (f g A B X : U) : Prop :=
      (A ∖ ImageSet g B) ⊆ X ∧
      ∀ x, x ∈ X → x ∈ A → g⦅f⦅x⦆⦆ ∈ X

    /-- The CSB core: intersection of all closed sets -/
    noncomputable def CSB_core (f g A B : U) : U :=
      SpecSet A (fun x => ∀ X, X ⊆ A → isCSB_closed f g A B X → x ∈ X)

    /-- The CSB core is a subset of A -/
    theorem CSB_core_subset (f g A B : U) : CSB_core f g A B ⊆ A := by
      intro x hx
      unfold CSB_core at hx
      rw [SpecSet_is_specified] at hx
      exact hx.1

    /-- A \ g[B] is contained in the CSB core -/
    theorem CSB_core_contains_base (f g A B : U) :
        (A ∖ ImageSet g B) ⊆ CSB_core f g A B := by
      intro x hx
      unfold CSB_core
      rw [SpecSet_is_specified]
      constructor
      · rw [SetDiff_is_specified] at hx
        exact hx.1
      · intro X _ hX_closed
        exact hX_closed.1 x hx

    /-- The CSB core is closed under g ∘ f -/
    theorem CSB_core_closed (f g A B : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A) :
        ∀ x, x ∈ CSB_core f g A B → g⦅f⦅x⦆⦆ ∈ CSB_core f g A B := by
      intro x hx
      unfold CSB_core at hx ⊢
      rw [SpecSet_is_specified] at hx ⊢
      have hx_A := hx.1
      -- g⦅f⦅x⦆⦆ ∈ A
      constructor
      · -- f⦅x⦆ ∈ B, so g⦅f⦅x⦆⦆ ∈ A
        have hfx_B : f⦅x⦆ ∈ B := by
          have h_mem := apply_mem f x (hf.2 x hx_A)
          have h := hf.1 ⟨x, f⦅x⦆⟩ h_mem
          rw [OrderedPair_mem_CartesianProduct] at h
          exact h.2
        have h_mem := apply_mem g (f⦅x⦆) (hg.2 (f⦅x⦆) hfx_B)
        have h := hg.1 ⟨f⦅x⦆, g⦅f⦅x⦆⦆⟩ h_mem
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.2
      · -- For all closed X, g⦅f⦅x⦆⦆ ∈ X
        intro X hX_sub hX_closed
        have h_in_X := hx.2 X hX_sub hX_closed
        exact hX_closed.2 x h_in_X hx_A

    /-- Elements not in CSB core are in the image of g -/
    theorem CSB_complement_in_image (f g A B x : U)
        (_ : isFunctionFromTo f A B) (_ : isFunctionFromTo g B A)
        (hx_A : x ∈ A) (hx_not : x ∉ CSB_core f g A B) :
        x ∈ ImageSet g B := Classical.byContradiction fun h_not_img => by
      have h_in_diff : x ∈ A ∖ ImageSet g B := by
        rw [SetDiff_is_specified]
        exact ⟨hx_A, h_not_img⟩
      have h_in_core := CSB_core_contains_base f g A B x h_in_diff
      exact hx_not h_in_core

    /-- The CSB bijection: h(x) = f(x) if x ∈ C, g⁻¹(x) if x ∉ C -/
    noncomputable def CSB_bijection (f g A B : U) : U :=
      let C := CSB_core f g A B
      SpecSet (A ×ₛ B) (fun p =>
        ∃ x y, p = ⟨x, y⟩ ∧ x ∈ A ∧
          ((x ∈ C ∧ y = f⦅x⦆) ∨ (x ∉ C ∧ ⟨y, x⟩ ∈ g)))

    /-- CSB bijection membership characterization -/
    theorem CSB_bijection_is_specified (f g A B x y : U) :
        ⟨x, y⟩ ∈ CSB_bijection f g A B ↔
          x ∈ A ∧ y ∈ B ∧
          ((x ∈ CSB_core f g A B ∧ y = f⦅x⦆) ∨
           (x ∉ CSB_core f g A B ∧ ⟨y, x⟩ ∈ g)) := by
      unfold CSB_bijection
      rw [SpecSet_is_specified]
      constructor
      · intro ⟨hp_in, x', y', hp_eq, hx'_A, hcase⟩
        have h_pair := Eq_of_OrderedPairs_given_projections x y x' y' hp_eq
        rw [h_pair.1.symm] at hx'_A
        rw [h_pair.1.symm, ← h_pair.2] at hcase
        rw [OrderedPair_mem_CartesianProduct] at hp_in
        exact ⟨hx'_A, hp_in.2, hcase⟩
      · intro ⟨hx_A, hy_B, hcase⟩
        constructor
        · rw [OrderedPair_mem_CartesianProduct]
          exact ⟨hx_A, hy_B⟩
        · exact ⟨x, y, rfl, hx_A, hcase⟩

    /-- The CSB bijection is a function -/
    theorem CSB_bijection_is_function (f g A B : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
        (_ : isInjective f) (hg_inj : isInjective g) :
        isFunctionFromTo (CSB_bijection f g A B) A B := by
      constructor
      · -- CSB_bijection f g A B ⊆ A ×ₛ B
        intro p hp
        unfold CSB_bijection at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      · -- Total and Unique
        intro x hx
        let C := CSB_core f g A B
        by_cases hxC : x ∈ C
        · -- Case x ∈ C
          have hfx_B : f⦅x⦆ ∈ B := by
            have h_mem := apply_mem f x (hf.2 x hx)
            have h := hf.1 ⟨x, f⦅x⦆⟩ h_mem
            rw [OrderedPair_mem_CartesianProduct] at h
            exact h.2
          -- Existence
          have h_ex : ⟨x, f⦅x⦆⟩ ∈ CSB_bijection f g A B := by
            rw [CSB_bijection_is_specified]
            exact ⟨hx, hfx_B, Or.inl ⟨hxC, rfl⟩⟩
          -- Uniqueness
          apply ExistsUnique.intro (f⦅x⦆) h_ex
          intro y' hy'
          rw [CSB_bijection_is_specified] at hy'
          cases hy'.2.2 with
          | inl h_inl => exact h_inl.2
          | inr h_inr => exact absurd hxC h_inr.1
        · -- Case x ∉ C
          have h_img := CSB_complement_in_image f g A B x hf hg hx hxC
          -- ImageSet g B = range (g ↾ B)
          have h_img' : ∃ y, ⟨y, x⟩ ∈ g ↾ B := by
            unfold ImageSet at h_img
            simp only [mem_range] at h_img
            exact h_img
          obtain ⟨y, hyx⟩ := h_img'
          have hyx_prop := (Restriction_is_specified g B ⟨y, x⟩).mp hyx
          have hyx_g := hyx_prop.1
          have hyx_fst := hyx_prop.2
          rw [fst_of_ordered_pair] at hyx_fst
          have h_apply : g⦅y⦆ = x := apply_eq g y x (hg.2 y hyx_fst) hyx_g
          -- Existence
          have h_ex : ⟨x, y⟩ ∈ CSB_bijection f g A B := by
            rw [CSB_bijection_is_specified]
            exact ⟨hx, hyx_fst, Or.inr ⟨hxC, hyx_g⟩⟩
          -- Uniqueness
          apply ExistsUnique.intro y h_ex
          intro y' hy'
          rw [CSB_bijection_is_specified] at hy'
          cases hy'.2.2 with
          | inl h_inl => exact absurd h_inl.1 hxC
          | inr h_inr =>
            -- ⟨y', x⟩ ∈ g and ⟨y, x⟩ ∈ g
            -- g is injective
            exact hg_inj y' y x h_inr.2 hyx_g

    /-- The CSB bijection is injective -/
    theorem CSB_bijection_is_injective (f g A B : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A) (hf_inj : isInjective f) :
        isInjective (CSB_bijection f g A B)
        := by
      intro x₁ x₂ y hx₁y hx₂y
      rw [CSB_bijection_is_specified] at hx₁y hx₂y
      let C := CSB_core f g A B
      cases hx₁y.2.2 with
      | inl h₁ =>
        -- x₁ ∈ C, y = f⦅x₁⦆
        cases hx₂y.2.2 with
        | inl h₂ =>
          -- x₂ ∈ C, y = f⦅x₂⦆
          -- f⦅x₁⦆ = y = f⦅x₂⦆, injectivity gives x₁ = x₂
          have hfx₁ := apply_mem f x₁ (hf.2 x₁ hx₁y.1)
          have hfx₂ := apply_mem f x₂ (hf.2 x₂ hx₂y.1)
          -- y = f⦅x₁⦆ and y = f⦅x₂⦆
          have heq : f⦅x₁⦆ = f⦅x₂⦆ := h₁.2.symm.trans h₂.2
          -- ⟨x₁, f⦅x₁⦆⟩ ∈ f and ⟨x₂, f⦅x₁⦆⟩ ∈ f (using heq)
          rw [heq] at hfx₁
          exact hf_inj x₁ x₂ (f⦅x₂⦆) hfx₁ hfx₂
        | inr h₂ =>
          -- x₂ ∉ C, ⟨y, x₂⟩ ∈ g
          -- y = f⦅x₁⦆ and g⦅y⦆ = x₂
          -- So g⦅f⦅x₁⦆⦆ = x₂
          -- Since x₁ ∈ C and C is closed, g⦅f⦅x₁⦆⦆ ∈ C
          -- But x₂ ∉ C, contradiction
          have h_closed := CSB_core_closed f g A B hf hg x₁ h₁.1
          have h_eq_y : y = f⦅x₁⦆ := h₁.2
          have h_gfx₁ : g⦅f⦅x₁⦆⦆ = x₂ := by
            rw [← h_eq_y]
            exact apply_eq g y x₂ (hg.2 y hx₂y.2.1) h₂.2
          rw [h_gfx₁] at h_closed
          exact absurd h_closed h₂.1
      | inr h₁ =>
        -- x₁ ∉ C, ⟨y, x₁⟩ ∈ g
        cases hx₂y.2.2 with
        | inl h₂ =>
          -- x₂ ∈ C, y = f⦅x₂⦆
          -- Symmetric to above
          have h_closed := CSB_core_closed f g A B hf hg x₂ h₂.1
          have h_eq_y : y = f⦅x₂⦆ := h₂.2
          have h_gfx₂ : g⦅f⦅x₂⦆⦆ = x₁ := by
            rw [← h_eq_y]
            exact apply_eq g y x₁ (hg.2 y hx₁y.2.1) h₁.2
          rw [h_gfx₂] at h_closed
          exact absurd h_closed h₁.1
        | inr h₂ =>
          -- x₁ ∉ C, x₂ ∉ C, ⟨y, x₁⟩ ∈ g, ⟨y, x₂⟩ ∈ g
          -- g is single-valued: for y ∈ B, ∃! x such that ⟨y, x⟩ ∈ g
          -- Since both ⟨y, x₁⟩ and ⟨y, x₂⟩ are in g, by uniqueness x₁ = x₂
          have h_unique := hg.2 y hx₁y.2.1
          obtain ⟨x_wit, h_wit, h_uniq⟩ := h_unique
          have h_eq1 : x₁ = x_wit := h_uniq x₁ h₁.2
          have h_eq2 : x₂ = x_wit := h_uniq x₂ h₂.2
          rw [h_eq1, h_eq2]

    /-- The CSB bijection is surjective -/
    theorem CSB_bijection_is_surjective (f g A B : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
        (_ : isInjective f) (hg_inj : isInjective g) :
        isSurjectiveOnto (CSB_bijection f g A B) B := by
      intro y hy
      let C := CSB_core f g A B
      -- Consider g⦅y⦆ ∈ A
      have hgy_A : g⦅y⦆ ∈ A := by
        have h_mem := apply_mem g y (hg.2 y hy)
        have h := hg.1 ⟨y, g⦅y⦆⟩ h_mem
        rw [OrderedPair_mem_CartesianProduct] at h
        exact h.2
      by_cases hgyC : g⦅y⦆ ∈ C
      · -- g⦅y⦆ ∈ C
        -- g⦅y⦆ ∈ C and g⦅y⦆ ∈ g[B] (since y ∈ B)
        -- We show g⦅y⦆ ∈ ImageSet g B, i.e., g⦅y⦆ ∈ range (g ↾ B)
        -- This means: ∃ x, ⟨x, g⦅y⦆⟩ ∈ g ↾ B, and we can use x = y
        have hgy_in_img : g⦅y⦆ ∈ ImageSet g B := by
          unfold ImageSet
          -- g⦅y⦆ ∈ range (g ↾ B)
          have h_mem_restr : ⟨y, g⦅y⦆⟩ ∈ g ↾ B := by
            rw [Restriction_is_specified]
            constructor
            · exact apply_mem g y (hg.2 y hy)
            · rw [fst_of_ordered_pair]
              exact hy
          -- Now show membership in range using Relations theorem
          exact pair_mem_implies_snd_in_range (g ↾ B) y (g⦅y⦆) h_mem_restr

        -- g⦅y⦆ ∉ A ∖ g[B]
        have hgy_not_base : g⦅y⦆ ∉ A ∖ ImageSet g B := by
          intro h_in
          rw [SetDiff_is_specified] at h_in
          exact h_in.2 hgy_in_img

        by_cases h_exists : ∃ x, x ∈ C ∧ f⦅x⦆ = y
        · -- There exists x ∈ C with f⦅x⦆ = y
          have ⟨x, hxC, hfx_eq⟩ := h_exists
          have hx_A := CSB_core_subset f g A B x hxC
          exact ⟨x, (CSB_bijection_is_specified f g A B x y).mpr
            ⟨hx_A, hy, Or.inl (And.intro hxC hfx_eq.symm)⟩⟩
        · -- No such x exists
          exfalso
          -- We show C \ {g⦅y⦆} is still closed if y ∉ f[C]
          let C' := C ∖ Singleton (g⦅y⦆)

          have hC'_closed : isCSB_closed f g A B C' := by
            constructor
            · -- (A \ g[B]) ⊆ C'
              intro z hz
              rw [SetDiff_is_specified]
              constructor
              · exact CSB_core_contains_base f g A B z hz
              · intro hz_eq
                rw [Singleton_is_specified] at hz_eq
                rw [hz_eq] at hz
                exact hgy_not_base hz
            · -- closure under g ∘ f
              intro x hx hx_A
              rw [SetDiff_is_specified] at hx
              have hx_C := hx.1
              rw [SetDiff_is_specified]
              constructor
              · exact CSB_core_closed f g A B hf hg x hx_C
              · -- g⦅f⦅x⦆⦆ ≠ g⦅y⦆
                intro h_eq
                rw [Singleton_is_specified] at h_eq
                -- g⦅f⦅x⦆⦆ = g⦅y⦆, by injectivity f⦅x⦆ = y
                have hfx_mem := apply_mem f x (hf.2 x hx_A)
                have hfx_B : f⦅x⦆ ∈ B := by
                  have h := hf.1 ⟨x, f⦅x⦆⟩ hfx_mem
                  rw [OrderedPair_mem_CartesianProduct] at h
                  exact h.2
                have hy_mem := apply_mem g y (hg.2 y hy)
                have hfx_g_mem := apply_mem g (f⦅x⦆) (hg.2 (f⦅x⦆) hfx_B)
                -- ⟨f⦅x⦆, g⦅f⦅x⦆⦆⟩ ∈ g and ⟨y, g⦅y⦆⟩ ∈ g with g⦅f⦅x⦆⦆ = g⦅y⦆
                -- By injectivity of g, f⦅x⦆ = y
                have h_fy_eq : f⦅x⦆ = y := hg_inj (f⦅x⦆) y (g⦅y⦆)
                  (h_eq ▸ hfx_g_mem) hy_mem
                -- But this contradicts h_exists being false
                exact h_exists ⟨x, hx_C, h_fy_eq⟩

          have hC'_sub : C' ⊆ A := by
            intro z hz
            rw [SetDiff_is_specified] at hz
            exact CSB_core_subset f g A B z hz.1

          -- By definition of C as minimal closed set, C ⊆ C'
          -- But C' = C \ {g⦅y⦆} and g⦅y⦆ ∈ C, so this is impossible
          have hgyC_core : g⦅y⦆ ∈ CSB_core f g A B := hgyC
          unfold CSB_core at hgyC_core
          rw [SpecSet_is_specified] at hgyC_core
          have h_in_C' := hgyC_core.2 C' hC'_sub hC'_closed
          have h_decomp := (SetDiff_is_specified C (Singleton (g⦅y⦆)) (g⦅y⦆)).mp h_in_C'
          exact h_decomp.2 ((Singleton_is_specified (g⦅y⦆) (g⦅y⦆)).mpr rfl)

      · -- g⦅y⦆ ∉ C
        -- Use x = g⦅y⦆, then h⦅x⦆ = y (since x ∉ C and ⟨y, x⟩ = ⟨y, g⦅y⦆⟩ ∈ g)
        have hgy_mem := apply_mem g y (hg.2 y hy)
        exact ⟨g⦅y⦆, (CSB_bijection_is_specified f g A B (g⦅y⦆) y).mpr
          ⟨hgy_A, hy, Or.inr ⟨hgyC, hgy_mem⟩⟩⟩

    /-- The CSB bijection is a bijection -/
    theorem CSB_bijection_is_bijection (f g A B : U)
        (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
        (hf_inj : isInjective f) (hg_inj : isInjective g) :
        isBijection (CSB_bijection f g A B) A B :=
      ⟨CSB_bijection_is_function f g A B hf hg hf_inj hg_inj,
       CSB_bijection_is_injective f g A B hf hg hf_inj,
       CSB_bijection_is_surjective f g A B hf hg hf_inj hg_inj⟩

    /-- Cantor-Schröder-Bernstein Theorem -/
    theorem cantor_schroeder_bernstein (A B : U)
        (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
        isEquipotent A B := by
      obtain ⟨f, hf_func, hf_inj⟩ := hab
      obtain ⟨g, hg_func, hg_inj⟩ := hba
      exact ⟨CSB_bijection f g A B, CSB_bijection_is_bijection f g A B hf_func hg_func hf_inj hg_inj⟩

    /-- Corollary: ≼ₛ is antisymmetric modulo equipotence -/
    theorem dominated_antisymm (A B : U) :
        isDominatedBy A B → isDominatedBy B A → isEquipotent A B :=
      cantor_schroeder_bernstein A B

  end Cardinality

  -- Export key definitions and theorems
  export Cardinality (
    DiagonalSet DiagonalSet_is_specified DiagonalSet_subset DiagonalSet_in_PowerSet
    DiagonalSet_not_in_range
    cantor_no_surjection cantor_no_bijection cantor_not_equipotent
    singletonMap singletonMap_is_specified singletonMap_is_function singletonMap_is_injective
    A_dominated_by_PowerSet PowerSet_not_dominated_by_A cantor_strict_dominance
    SetDiff SetDiff_is_specified SetDiff_subset
    CSB_core CSB_core_subset CSB_core_contains_base CSB_core_closed
    CSB_bijection CSB_bijection_is_specified
    CSB_bijection_is_function CSB_bijection_is_injective CSB_bijection_is_surjective
    CSB_bijection_is_bijection
    cantor_schroeder_bernstein dominated_antisymm
  )

end SetUniverse
