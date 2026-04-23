/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Finite Sets in ZFC

This module defines finite sets and develops their basic theory.
A set is finite if it is equipotent to some natural number n ∈ ω.

## Main Definitions

* `isFiniteSet A` — A is finite if ∃ n ∈ ω, A ≃ₛ n

## Main Theorems

* `empty_is_finite`          — ∅ is finite
* `nat_is_finite`            — every n ∈ ω is finite
* `singleton_is_finite`      — {a} is finite
* `finite_equipotent`        — if A is finite and A ≃ₛ B, then B is finite
* `finite_union_singleton`   — if A is finite and a ∉ A, then A ∪ {a} is finite

## Auxiliary Results

This module also develops infrastructure for bijections and equipotence:
* `id_is_bijection`                — idFn A is a bijection from A to A
* `bijection_inverse_is_bijection` — f⁻¹ is a bijection from B to A
* `comp_bijection`                 — composition of bijections is a bijection
* `equipotent_refl/symm/trans`     — equipotence is an equivalence relation

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Nat.Basic
import ZFC.Axiom.Infinity

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Cardinal.Basic
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  universe u
  variable {U : Type u}

  namespace SetOps.FiniteSets

    /-! ============================================================ -/
    /-! ### SECTION 1: IDENTITY BIJECTION ### -/
    /-! ============================================================ -/

    /-- The identity function on A is a function from A to A. -/
    theorem id_is_function (A : U) : IsFunction (idFn A) A A := by
      constructor
      · -- idFn A ⊆ A ×ₛ A
        intro p hp
        unfold idFn IdRel at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · -- ∀ x ∈ A, ∃! y, ⟨x, y⟩ ∈ idFn A
        intro x hx
        apply ExistsUnique.intro x
        · unfold idFn; exact (mem_IdRel A x x).mpr ⟨hx, rfl⟩
        · intro y' hy'
          unfold idFn at hy'
          exact ((mem_IdRel A x y').mp hy').2.symm

    /-- The identity function on A is injective. -/
    theorem id_is_injective (A : U) : isInjective (idFn A) := by
      intro x₁ x₂ y h₁ h₂
      unfold idFn at h₁ h₂
      rw [mem_IdRel] at h₁ h₂
      exact h₁.2.trans h₂.2.symm

    /-- The identity function on A is surjective onto A. -/
    theorem id_is_surjective (A : U) : isSurjectiveOnto (idFn A) A := by
      intro y hy
      exact ⟨y, by unfold idFn; exact (mem_IdRel A y y).mpr ⟨hy, rfl⟩⟩

    /-- The identity function on A is a bijection from A to A. -/
    theorem id_is_bijection (A : U) : isBijection (idFn A) A A :=
      ⟨id_is_function A, id_is_injective A, id_is_surjective A⟩

    /-- Equipotence is reflexive: A ≃ₛ A. -/
    theorem equipotent_refl (A : U) : A ≃ₛ A :=
      ⟨idFn A, id_is_bijection A⟩

    /-! ============================================================ -/
    /-! ### SECTION 2: DEFINITION ### -/
    /-! ============================================================ -/

    /-- A set is finite if it is equipotent to some natural number n ∈ ω. -/
    def isFiniteSet (A : U) : Prop := ∃ n, n ∈ ω ∧ A ≃ₛ n

    /-! ============================================================ -/
    /-! ### SECTION 3: BASIC PROPERTIES ### -/
    /-! ============================================================ -/

    /-- The empty set is finite. -/
    theorem empty_is_finite : isFiniteSet (∅ : U) :=
      ⟨∅, zero_in_Omega, equipotent_refl ∅⟩

    /-- Every natural number (element of ω) is finite. -/
    theorem nat_is_finite {n : U} (hn : n ∈ ω) : isFiniteSet n :=
      ⟨n, hn, equipotent_refl n⟩

    /-! ============================================================ -/
    /-! ### SECTION 4: INVERSE BIJECTION LEMMAS ### -/
    /-! ============================================================ -/

    /-- Simplified characterization for ordered pairs and the inverse. -/
    theorem inverse_pair_iff (f x y : U) :
        ⟨y, x⟩ ∈ f⁻¹ ↔ ⟨x, y⟩ ∈ f := by
      rw [inverse_is_specified]
      constructor
      · intro h
        have h2 := h.2
        rw [snd_of_ordered_pair, fst_of_ordered_pair] at h2
        exact h2
      · intro h
        refine ⟨⟨y, x, rfl⟩, ?_⟩
        rw [snd_of_ordered_pair, fst_of_ordered_pair]
        exact h

    /-- The inverse of a bijection f : A → B is a function from B to A. -/
    theorem bijection_inverse_is_function {f A B : U} (hbij : isBijection f A B) :
        IsFunction (f⁻¹) B A := by
      obtain ⟨hf, hinj, hsurj⟩ := hbij
      constructor
      · -- f⁻¹ ⊆ B ×ₛ A
        intro p hp
        rw [inverse_is_specified] at hp
        obtain ⟨hp_pair, hmem⟩ := hp
        have hp_eq := (isOrderedPair_by_construction p).mp hp_pair
        rw [hp_eq, OrderedPair_mem_CartesianProduct]
        have h_in_AB := hf.1 _ hmem
        rw [OrderedPair_mem_CartesianProduct] at h_in_AB
        exact ⟨h_in_AB.2, h_in_AB.1⟩
      · -- ∀ y ∈ B, ∃! x, ⟨y, x⟩ ∈ f⁻¹
        intro y hy
        obtain ⟨x, hx⟩ := hsurj y hy
        have hsv := injective_inverse_single_valued f hinj
        apply ExistsUnique.intro x
        · exact (inverse_pair_iff f x y).mpr hx
        · intro x' hx'
          exact hsv y x' x hx' ((inverse_pair_iff f x y).mpr hx)

    /-- The inverse of a bijection is injective. -/
    theorem bijection_inverse_injective {f A B : U} (hbij : isBijection f A B) :
        isInjective (f⁻¹) := by
      obtain ⟨hf, _, _⟩ := hbij
      intro x₁ x₂ y h₁ h₂
      rw [inverse_pair_iff] at h₁ h₂
      have hy_A : y ∈ A := by
        have := hf.1 _ h₁
        rw [OrderedPair_mem_CartesianProduct] at this
        exact this.1
      obtain ⟨_, _, hz_unique⟩ := hf.2 y hy_A
      exact (hz_unique x₁ h₁).trans (hz_unique x₂ h₂).symm

    /-- The inverse of a bijection is surjective onto the original domain. -/
    theorem bijection_inverse_surjective {f A B : U} (hbij : isBijection f A B) :
        isSurjectiveOnto (f⁻¹) A := by
      obtain ⟨hf, _, _⟩ := hbij
      intro x hx
      obtain ⟨y, hy, _⟩ := hf.2 x hx
      exact ⟨y, (inverse_pair_iff f x y).mpr hy⟩

    /-- The inverse of a bijection f : A → B is a bijection from B to A. -/
    theorem bijection_inverse_is_bijection {f A B : U} (hbij : isBijection f A B) :
        isBijection (f⁻¹) B A :=
      ⟨bijection_inverse_is_function hbij,
       bijection_inverse_injective hbij,
       bijection_inverse_surjective hbij⟩

    /-- Equipotence is symmetric: A ≃ₛ B → B ≃ₛ A. -/
    theorem equipotent_symm {A B : U} (h : A ≃ₛ B) : B ≃ₛ A := by
      obtain ⟨f, hf⟩ := h
      exact ⟨f⁻¹, bijection_inverse_is_bijection hf⟩

    /-! ============================================================ -/
    /-! ### SECTION 5: COMPOSITION AND TRANSITIVITY ### -/
    /-! ============================================================ -/

    /-- Composition of injective relations is injective. -/
    theorem comp_injective {f g : U} (hf_inj : isInjective f) (hg_inj : isInjective g) :
        isInjective (g ∘ f) := by
      intro x₁ x₂ z h₁ h₂
      rw [comp_is_specified] at h₁ h₂
      obtain ⟨a₁, c₁, h₁_eq, y₁, hf₁, hg₁⟩ := h₁
      obtain ⟨a₂, c₂, h₂_eq, y₂, hf₂, hg₂⟩ := h₂
      have hp₁ := Eq_of_OrderedPairs_given_projections x₁ z a₁ c₁ h₁_eq
      have hp₂ := Eq_of_OrderedPairs_given_projections x₂ z a₂ c₂ h₂_eq
      rw [← hp₁.1] at hf₁; rw [← hp₁.2] at hg₁
      rw [← hp₂.1] at hf₂; rw [← hp₂.2] at hg₂
      have hy_eq : y₁ = y₂ := hg_inj y₁ y₂ z hg₁ hg₂
      rw [hy_eq] at hf₁
      exact hf_inj x₁ x₂ y₂ hf₁ hf₂

    /-- Composition of surjective functions is surjective. -/
    theorem comp_surjective {f g A B C : U}
        (_hf : IsFunction f A B) (hg : IsFunction g B C)
        (hsurj_f : isSurjectiveOnto f B) (hsurj_g : isSurjectiveOnto g C) :
        isSurjectiveOnto (g ∘ f) C := by
      intro z hz
      obtain ⟨y, hy⟩ := hsurj_g z hz
      have hy_B : y ∈ B := by
        have := hg.1 _ hy
        rw [OrderedPair_mem_CartesianProduct] at this
        exact this.1
      obtain ⟨x, hx⟩ := hsurj_f y hy_B
      exact ⟨x, (comp_is_specified g f ⟨x, z⟩).mpr ⟨x, z, rfl, y, hx, hy⟩⟩

    /-- Composition of bijections is a bijection. -/
    theorem comp_bijection {f g A B C : U}
        (hf_bij : isBijection f A B) (hg_bij : isBijection g B C) :
        isBijection (g ∘ f) A C :=
      ⟨comp_is_function f g A B C hf_bij.1 hg_bij.1,
       comp_injective hf_bij.2.1 hg_bij.2.1,
       comp_surjective hf_bij.1 hg_bij.1 hf_bij.2.2 hg_bij.2.2⟩

    /-- Equipotence is transitive: A ≃ₛ B → B ≃ₛ C → A ≃ₛ C. -/
    theorem equipotent_trans {A B C : U} (hab : A ≃ₛ B) (hbc : B ≃ₛ C) : A ≃ₛ C := by
      obtain ⟨f, hf⟩ := hab
      obtain ⟨g, hg⟩ := hbc
      exact ⟨g ∘ f, comp_bijection hf hg⟩

    /-! ============================================================ -/
    /-! ### SECTION 6: CLOSURE UNDER EQUIPOTENCE ### -/
    /-! ============================================================ -/

    /-- Finiteness is preserved under equipotence. -/
    theorem finite_equipotent {A B : U} (hA : isFiniteSet A) (hab : A ≃ₛ B) :
        isFiniteSet B := by
      obtain ⟨n, hn, hAn⟩ := hA
      exact ⟨n, hn, equipotent_trans (equipotent_symm hab) hAn⟩

    /-! ============================================================ -/
    /-! ### SECTION 7: SINGLETON ### -/
    /-! ============================================================ -/

    /-- Every singleton is finite: {a} ≃ₛ σ ∅ (= 1). -/
    theorem singleton_is_finite (a : U) : isFiniteSet ({a} : U) := by
      refine ⟨σ ∅, Nat_in_Omega _ (isNat_succ ∅ isNat_zero), ?_⟩
      -- Bijection: f = {⟨a, ∅⟩} from {a} to σ ∅ = {∅}
      refine ⟨{⟨a, ∅⟩}, ?_, ?_, ?_⟩
      · -- IsFunction {⟨a, ∅⟩} {a} (σ ∅)
        constructor
        · intro p hp
          rw [Singleton_is_specified] at hp
          rw [hp, OrderedPair_mem_CartesianProduct]
          exact ⟨(Singleton_is_specified a a).mpr rfl, mem_succ_self ∅⟩
        · intro x hx
          rw [Singleton_is_specified] at hx
          rw [hx]
          apply ExistsUnique.intro (∅ : U)
          · exact (Singleton_is_specified ⟨a, ∅⟩ ⟨a, ∅⟩).mpr rfl
          · intro y' hy'
            rw [Singleton_is_specified] at hy'
            exact (Eq_of_OrderedPairs_given_projections a y' a ∅ hy').2
      · -- isInjective {⟨a, ∅⟩}
        intro x₁ x₂ y h₁ h₂
        rw [Singleton_is_specified] at h₁ h₂
        exact (Eq_of_OrderedPairs_given_projections x₁ y a ∅ h₁).1.trans
              (Eq_of_OrderedPairs_given_projections x₂ y a ∅ h₂).1.symm
      · -- isSurjectiveOnto {⟨a, ∅⟩} (σ ∅)
        intro y hy
        rw [mem_succ_iff] at hy
        cases hy with
        | inl h => exact absurd h (EmptySet_is_empty y)
        | inr h =>
          subst h
          exact ⟨a, (Singleton_is_specified ⟨a, ∅⟩ ⟨a, ∅⟩).mpr rfl⟩

    /-! ============================================================ -/
    /-! ### SECTION 8: ADDING AN ELEMENT ### -/
    /-! ============================================================ -/

    /-- Adding a new element to a finite set preserves finiteness. -/
    theorem finite_union_singleton {A a : U} (hA : isFiniteSet A) (ha : a ∉ A) :
        isFiniteSet (A ∪ {a}) := by
      obtain ⟨n, hn, f, hf_bij⟩ := hA
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      obtain ⟨hf_func, hf_inj, hf_surj⟩ := hf_bij
      -- Bijection: g = f ∪ {⟨a, n⟩} from A ∪ {a} to σ n
      refine ⟨σ n, Nat_in_Omega _ (isNat_succ n hn_nat), ?_⟩
      refine ⟨f ∪ {⟨a, n⟩}, ?_, ?_, ?_⟩
      · -- IsFunction (f ∪ {⟨a, n⟩}) (A ∪ {a}) (σ n)
        constructor
        · -- f ∪ {⟨a, n⟩} ⊆ (A ∪ {a}) ×ₛ σ n
          intro p hp
          rw [mem_union_iff] at hp
          cases hp with
          | inl hp_f =>
            have h := hf_func.1 p hp_f
            rw [CartesianProduct_is_specified] at h ⊢
            exact ⟨h.1,
                   (mem_union_iff A {a} (fst p)).mpr (Or.inl h.2.1),
                   (mem_succ_iff n (snd p)).mpr (Or.inl h.2.2)⟩
          | inr hp_eq =>
            rw [Singleton_is_specified] at hp_eq
            rw [hp_eq, OrderedPair_mem_CartesianProduct]
            exact ⟨(mem_union_iff A {a} a).mpr
                      (Or.inr ((Singleton_is_specified a a).mpr rfl)),
                   mem_succ_self n⟩
        · -- ∀ x ∈ A ∪ {a}, ∃! y, ⟨x, y⟩ ∈ f ∪ {⟨a, n⟩}
          intro x hx
          rw [mem_union_iff] at hx
          cases hx with
          | inl hx_A =>
            obtain ⟨y, hy_in, hy_unique⟩ := hf_func.2 x hx_A
            apply ExistsUnique.intro y
            · exact (mem_union_iff f {⟨a, n⟩} ⟨x, y⟩).mpr (Or.inl hy_in)
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl hy'_f => exact hy_unique y' hy'_f
              | inr hy'_eq =>
                rw [Singleton_is_specified] at hy'_eq
                exact absurd ((Eq_of_OrderedPairs_given_projections x y' a n hy'_eq).1 ▸ hx_A) ha
          | inr hx_a =>
            rw [Singleton_is_specified] at hx_a
            -- hx_a : x = a
            apply ExistsUnique.intro n
            · rw [hx_a]
              exact (mem_union_iff f {⟨a, n⟩} ⟨a, n⟩).mpr
                    (Or.inr ((Singleton_is_specified ⟨a, n⟩ ⟨a, n⟩).mpr rfl))
            · intro y' hy'
              rw [hx_a] at hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl hy'_f =>
                have := hf_func.1 _ hy'_f
                rw [OrderedPair_mem_CartesianProduct] at this
                exact absurd this.1 ha
              | inr hy'_eq =>
                rw [Singleton_is_specified] at hy'_eq
                exact (Eq_of_OrderedPairs_given_projections a y' a n hy'_eq).2
      · -- isInjective (f ∪ {⟨a, n⟩})
        intro x₁ x₂ y h₁ h₂
        rw [mem_union_iff] at h₁ h₂
        cases h₁ with
        | inl h₁_f =>
          cases h₂ with
          | inl h₂_f =>
            exact hf_inj x₁ x₂ y h₁_f h₂_f
          | inr h₂_eq =>
            rw [Singleton_is_specified] at h₂_eq
            have h₂_proj := Eq_of_OrderedPairs_given_projections x₂ y a n h₂_eq
            rw [h₂_proj.2] at h₁_f
            have h_mem := hf_func.1 _ h₁_f
            rw [OrderedPair_mem_CartesianProduct] at h_mem
            exact absurd h_mem.2 (not_mem_self n hn_nat)
        | inr h₁_eq =>
          cases h₂ with
          | inl h₂_f =>
            rw [Singleton_is_specified] at h₁_eq
            have h₁_proj := Eq_of_OrderedPairs_given_projections x₁ y a n h₁_eq
            rw [h₁_proj.2] at h₂_f
            have h_mem := hf_func.1 _ h₂_f
            rw [OrderedPair_mem_CartesianProduct] at h_mem
            exact absurd h_mem.2 (not_mem_self n hn_nat)
          | inr h₂_eq =>
            rw [Singleton_is_specified] at h₁_eq h₂_eq
            exact (Eq_of_OrderedPairs_given_projections x₁ y a n h₁_eq).1.trans
                  (Eq_of_OrderedPairs_given_projections x₂ y a n h₂_eq).1.symm
      · -- isSurjectiveOnto (f ∪ {⟨a, n⟩}) (σ n)
        intro y hy
        rw [mem_succ_iff] at hy
        cases hy with
        | inl hy_n =>
          obtain ⟨x, hx⟩ := hf_surj y hy_n
          exact ⟨x, (mem_union_iff f {⟨a, n⟩} ⟨x, y⟩).mpr (Or.inl hx)⟩
        | inr hy_eq =>
          rw [hy_eq]
          exact ⟨a, (mem_union_iff f {⟨a, n⟩} ⟨a, n⟩).mpr
                      (Or.inr ((Singleton_is_specified ⟨a, n⟩ ⟨a, n⟩).mpr rfl))⟩

    /-! ============================================================ -/
    /-! ### SECTION 9: RESTRICTION PRESERVES INJECTIVITY ### -/
    /-! ============================================================ -/

    /-- restrict of an injective relation preserves injectivity. -/
    theorem restriction_is_injective {f C : U} (hf_inj : isInjective f) :
        isInjective (f ↾ C) := by
      intro x₁ x₂ y h₁ h₂
      exact hf_inj x₁ x₂ y (restrict_subset f C ⟨x₁, y⟩ h₁) (restrict_subset f C ⟨x₂, y⟩ h₂)

    /-! ============================================================ -/
    /-! ### SECTION 10: PIGEONHOLE PRINCIPLE ### -/
    /-! ============================================================ -/

    /-- Pigeonhole principle: there is no injection from σn to n for any n ∈ ω. -/
    theorem no_injection_succ_to_nat {n : U} (hn : n ∈ ω) :
        ∀ f, IsFunction f (σ n) n → ¬isInjective f := by
      let P : U → Prop := fun k => ∀ f, IsFunction f (σ k) k → ¬isInjective f
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        exact ((mem_sep_iff (ω : U) n P).mp hn_S).2
      apply induction_principle S
      -- S ⊆ ω
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      -- Base: ∅ ∈ S (no function from σ∅ = {∅} to ∅)
      · rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        simp only [P]
        intro f hf _
        obtain ⟨y, hy, _⟩ := hf.2 ∅ (mem_succ_self ∅)
        have := hf.1 _ hy
        rw [OrderedPair_mem_CartesianProduct] at this
        exact EmptySet_is_empty y this.2
      -- Successor: k ∈ S → σk ∈ S
      · intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        simp only [P] at ih
        have hk_nat := mem_Omega_is_Nat k hk_omega
        have hσk_nat := isNat_succ k hk_nat
        constructor
        · exact succ_in_Omega k hk_omega
        · simp only [P]
          intro f hf hf_inj
          -- f : σ(σk) → σk injective. Derive contradiction.
          have hσk_sub : σ k ⊆ σ (σ k) := fun x hx => mem_succ_of_mem x (σ k) hx
          by_cases h_hit : ∃ a, a ∈ σ k ∧ ⟨a, k⟩ ∈ f
          · ---- CASE 2: ∃ a ∈ σk with ⟨a, k⟩ ∈ f ----
            obtain ⟨a, ha_σk, ha_f⟩ := h_hit
            -- Helper: extract membership from restriction of f to σk∖{a}
            have rest_fst_in_σk : ∀ p, (p ∈ (f ↾ (σ k ∖ {a}))) →
                (((fst p) ∈ (σ k)) ∧ ((fst p) ∉ ({a} : U))) := fun _ hp => by
              have := ((mem_restrict_iff f _ _).mp hp).2
              exact (SetDiff_is_specified _ _ _).mp this
            have ha_ne_σk : a ≠ σ k := fun h =>
              not_mem_self (σ k) hσk_nat (h ▸ ha_σk)
            -- f⦅σk⦆ ∈ k
            have hσk_uniq := hf.2 (σ k) (mem_succ_self (σ k))
            have hfσk_pair : ⟨σ k, f⦅σ k⦆⟩ ∈ f := apply_mem f (σ k) hσk_uniq
            have hfσk_cod : f⦅σ k⦆ ∈ σ k := by
              have := hf.1 _ hfσk_pair
              rw [OrderedPair_mem_CartesianProduct] at this; exact this.2
            have hfσk_ne_k : f⦅σ k⦆ ≠ k := fun h_eq =>
              ha_ne_σk (hf_inj a (σ k) k ha_f
                (h_eq.subst (motive := fun x => ⟨σ k, x⟩ ∈ f) hfσk_pair))
            have hfσk_in_k : f⦅σ k⦆ ∈ k := by
              rw [mem_succ_iff] at hfσk_cod
              exact hfσk_cod.elim id (fun h => absurd h hfσk_ne_k)
            -- Construct g = (f ↾ (σk ∖ {a})) ∪ {⟨a, f⦅σk⦆⟩}
            let g := (f ↾ (σ k ∖ {a})) ∪ ({⟨a, f⦅σ k⦆⟩} : U)
            apply ih g
            · -- IsFunction g (σk) k
              constructor
              · -- g ⊆ σk ×ₛ k
                intro p hp
                rw [mem_union_iff] at hp
                cases hp with
                | inl hp_rest =>
                  have hp_f := restrict_subset f _ p hp_rest
                  obtain ⟨hp_fst_σk, hp_fst_ne_a⟩ := rest_fst_in_σk p hp_rest
                  have hp_cart := hf.1 _ hp_f
                  rw [CartesianProduct_is_specified] at hp_cart
                  obtain ⟨hp_op, _, hp_snd_σk⟩ := hp_cart
                  rw [CartesianProduct_is_specified]
                  refine ⟨hp_op, hp_fst_σk, ?_⟩
                  rw [mem_succ_iff] at hp_snd_σk
                  cases hp_snd_σk with
                  | inl h => exact h
                  | inr h_eq =>
                    exfalso
                    have hp_eq := (isOrderedPair_by_construction p).mp hp_op
                    rw [h_eq] at hp_eq; rw [hp_eq] at hp_f
                    have hp_fst_ne : fst p ≠ a := fun h =>
                      hp_fst_ne_a ((Singleton_is_specified a (fst p)).mpr h)
                    exact hp_fst_ne (hf_inj (fst p) a k hp_f ha_f)
                | inr hp_sing =>
                  rw [Singleton_is_specified] at hp_sing
                  rw [hp_sing, OrderedPair_mem_CartesianProduct]
                  exact ⟨ha_σk, hfσk_in_k⟩
              · -- ∀ x ∈ σk, ∃! y, ⟨x, y⟩ ∈ g
                intro x hx
                by_cases hx_eq_a : x = a
                · -- x = a: unique y is f⦅σk⦆
                  rw [hx_eq_a]
                  apply ExistsUnique.intro (f⦅σ k⦆)
                  · exact (mem_union_iff _ _ _).mpr
                      (Or.inr ((Singleton_is_specified _ _).mpr rfl))
                  · intro y' hy'
                    rw [mem_union_iff] at hy'
                    cases hy' with
                    | inl hy'_rest =>
                      exfalso
                      have hfst := (rest_fst_in_σk _ hy'_rest).2
                      rw [fst_of_ordered_pair] at hfst
                      exact hfst ((Singleton_is_specified a a).mpr rfl)
                    | inr hy'_sing =>
                      exact (Eq_of_OrderedPairs_given_projections a y' a (f⦅σ k⦆)
                        ((Singleton_is_specified _ _).mp hy'_sing)).2
                · -- x ≠ a: unique y comes from f
                  have hx_dom : x ∈ σ (σ k) := hσk_sub x hx
                  obtain ⟨y, hy, hy_uniq⟩ := hf.2 x hx_dom
                  have hx_diff : x ∈ σ k ∖ {a} :=
                    (SetDiff_is_specified (σ k) {a} x).mpr
                      ⟨hx, fun h => hx_eq_a ((Singleton_is_specified a x).mp h)⟩
                  apply ExistsUnique.intro y
                  · exact (mem_union_iff _ _ _).mpr
                      (Or.inl ((mem_restrict_iff f (σ k ∖ {a}) ⟨x, y⟩).mpr
                        ⟨hy, by rw [fst_of_ordered_pair]; exact hx_diff⟩))
                  · intro y' hy'
                    rw [mem_union_iff] at hy'
                    cases hy' with
                    | inl hy'_rest =>
                      exact hy_uniq y' (restrict_subset f _ ⟨x, y'⟩ hy'_rest)
                    | inr hy'_sing =>
                      exfalso
                      exact hx_eq_a (Eq_of_OrderedPairs_given_projections x y' a (f⦅σ k⦆)
                        ((Singleton_is_specified _ _).mp hy'_sing)).1
            · -- g is injective
              intro x₁ x₂ y h₁ h₂
              rw [mem_union_iff] at h₁ h₂
              cases h₁ with
              | inl h₁_rest =>
                have h₁_f := restrict_subset f _ ⟨x₁, y⟩ h₁_rest
                cases h₂ with
                | inl h₂_rest =>
                  exact hf_inj x₁ x₂ y h₁_f (restrict_subset f _ ⟨x₂, y⟩ h₂_rest)
                | inr h₂_sing =>
                  exfalso
                  have h_sing_eq := (Singleton_is_specified _ _).mp h₂_sing
                  obtain ⟨_, hy_eq⟩ := Eq_of_OrderedPairs_given_projections x₂ y a (f⦅σ k⦆) h_sing_eq
                  rw [hy_eq] at h₁_f
                  have h_eq := hf_inj x₁ (σ k) (f⦅σ k⦆) h₁_f hfσk_pair
                  have h_fst := (rest_fst_in_σk _ h₁_rest).1
                  rw [fst_of_ordered_pair, h_eq] at h_fst
                  exact not_mem_self (σ k) hσk_nat h_fst
              | inr h₁_sing =>
                have h_sing_eq := (Singleton_is_specified _ _).mp h₁_sing
                obtain ⟨hx₁_a, hy_eq⟩ := Eq_of_OrderedPairs_given_projections x₁ y a (f⦅σ k⦆) h_sing_eq
                cases h₂ with
                | inl h₂_rest =>
                  exfalso
                  have h₂_f := restrict_subset f _ ⟨x₂, y⟩ h₂_rest
                  rw [hy_eq] at h₂_f
                  have h_eq := hf_inj x₂ (σ k) (f⦅σ k⦆) h₂_f hfσk_pair
                  have h_fst := (rest_fst_in_σk _ h₂_rest).1
                  rw [fst_of_ordered_pair, h_eq] at h_fst
                  exact not_mem_self (σ k) hσk_nat h_fst
                | inr h₂_sing =>
                  exact hx₁_a.trans (Eq_of_OrderedPairs_given_projections x₂ y a (f⦅σ k⦆)
                    ((Singleton_is_specified _ _).mp h₂_sing)).1.symm
          · ---- CASE 1: ∀ x ∈ σk, ⟨x, k⟩ ∉ f ----
            -- f↾σk : σk → k injective, contradicting ih
            apply ih (f ↾ σ k)
            · -- IsFunction (f↾σk) (σk) k
              constructor
              · -- f↾σk ⊆ σk ×ₛ k
                intro p hp
                rw [mem_restrict_iff] at hp
                have hp_f := hp.1
                have hp_fst_σk := hp.2
                have hp_cart := hf.1 _ hp_f
                rw [CartesianProduct_is_specified] at hp_cart
                obtain ⟨hp_op, _, hp_snd_σk⟩ := hp_cart
                rw [CartesianProduct_is_specified]
                refine ⟨hp_op, hp_fst_σk, ?_⟩
                rw [mem_succ_iff] at hp_snd_σk
                cases hp_snd_σk with
                | inl h => exact h
                | inr h_eq =>
                  exfalso
                  have hp_eq := (isOrderedPair_by_construction p).mp hp_op
                  rw [h_eq] at hp_eq; rw [hp_eq] at hp_f
                  exact h_hit ⟨fst p, hp_fst_σk, hp_f⟩
              · -- totality from restrict_is_function
                exact (restrict_is_function f (σ (σ k)) (σ k) (σ k) hf hσk_sub).2
            · exact restriction_is_injective hf_inj

    /-! ============================================================ -/
    /-! ### SECTION 11: FINITE INJECTION IS SURJECTION ### -/
    /-! ============================================================ -/

    /-- An injection f : n → n (n ∈ ω) is necessarily surjective. -/
    theorem nat_injection_is_surjection {n f : U} (hn : n ∈ ω)
        (hf : IsFunction f n n) (hf_inj : isInjective f) :
        isSurjectiveOnto f n := by
      apply Classical.byContradiction
      intro h_not_surj
      -- Extract y₀ ∈ n not in range of f
      have h_exists : ∃ y₀, y₀ ∈ n ∧ ∀ x, ⟨x, y₀⟩ ∉ f := by
        apply Classical.byContradiction
        intro h_all
        exact h_not_surj (fun y hy => Classical.byContradiction fun h_none =>
          h_all ⟨y, hy, fun x hx => h_none ⟨x, hx⟩⟩)
      obtain ⟨y₀, hy₀, hy₀_range⟩ := h_exists
      have hn_nat := mem_Omega_is_Nat n hn
      -- Construct h = f ∪ {⟨n, y₀⟩} : σn → n injective
      let h := f ∪ ({⟨n, y₀⟩} : U)
      exact no_injection_succ_to_nat hn h
        (by
          constructor
          · -- h ⊆ σn ×ₛ n
            intro p hp
            rw [mem_union_iff] at hp
            cases hp with
            | inl hp_f =>
              have := hf.1 _ hp_f
              rw [CartesianProduct_is_specified] at this ⊢
              exact ⟨this.1, mem_succ_of_mem (fst p) n this.2.1, this.2.2⟩
            | inr hp_sing =>
              rw [Singleton_is_specified] at hp_sing
              rw [hp_sing, OrderedPair_mem_CartesianProduct]
              exact ⟨mem_succ_self n, hy₀⟩
          · -- ∀ x ∈ σn, ∃! y, ⟨x, y⟩ ∈ h
            intro x hx
            rw [mem_succ_iff] at hx
            cases hx with
            | inl hx_n =>
              obtain ⟨y, hy, hy_uniq⟩ := hf.2 x hx_n
              apply ExistsUnique.intro y
              · exact (mem_union_iff _ _ _).mpr (Or.inl hy)
              · intro y' hy'
                rw [mem_union_iff] at hy'
                cases hy' with
                | inl hy'_f => exact hy_uniq y' hy'_f
                | inr hy'_sing =>
                  exfalso
                  have := (Eq_of_OrderedPairs_given_projections x y' n y₀
                    ((Singleton_is_specified _ _).mp hy'_sing)).1
                  exact not_mem_self n hn_nat (this ▸ hx_n)
            | inr hx_n =>
              rw [hx_n]
              apply ExistsUnique.intro y₀
              · exact (mem_union_iff _ _ _).mpr
                  (Or.inr ((Singleton_is_specified _ _).mpr rfl))
              · intro y' hy'
                rw [mem_union_iff] at hy'
                cases hy' with
                | inl hy'_f =>
                  exfalso
                  have := hf.1 _ hy'_f
                  rw [OrderedPair_mem_CartesianProduct] at this
                  exact not_mem_self n hn_nat this.1
                | inr hy'_sing =>
                  exact (Eq_of_OrderedPairs_given_projections n y' n y₀
                    ((Singleton_is_specified _ _).mp hy'_sing)).2)
        (by
          -- h is injective
          intro x₁ x₂ y h₁ h₂
          rw [mem_union_iff] at h₁ h₂
          cases h₁ with
          | inl h₁_f =>
            cases h₂ with
            | inl h₂_f => exact hf_inj x₁ x₂ y h₁_f h₂_f
            | inr h₂_sing =>
              exfalso
              have h_sing_eq := (Singleton_is_specified _ _).mp h₂_sing
              obtain ⟨_, hy_eq⟩ := Eq_of_OrderedPairs_given_projections x₂ y n y₀ h_sing_eq
              rw [hy_eq] at h₁_f
              exact hy₀_range x₁ h₁_f
          | inr h₁_sing =>
            cases h₂ with
            | inl h₂_f =>
              exfalso
              have h_sing_eq := (Singleton_is_specified _ _).mp h₁_sing
              obtain ⟨_, hy_eq⟩ := Eq_of_OrderedPairs_given_projections x₁ y n y₀ h_sing_eq
              rw [hy_eq] at h₂_f
              exact hy₀_range x₂ h₂_f
            | inr h₂_sing =>
              exact (Eq_of_OrderedPairs_given_projections x₁ y n y₀
                ((Singleton_is_specified _ _).mp h₁_sing)).1.trans
                (Eq_of_OrderedPairs_given_projections x₂ y n y₀
                ((Singleton_is_specified _ _).mp h₂_sing)).1.symm)

    /-! ============================================================ -/
    /-! ### SECTION 12: UNIQUENESS OF FINITE CARDINALITY ### -/
    /-! ============================================================ -/

    /-- No natural number is equipotent to a strictly smaller one. -/
    theorem not_equipotent_nat_smaller {n m : U} (hn : n ∈ ω) (hm : m ∈ ω)
        (h_mem : m ∈ n) : ¬(m ≃ₛ n) := by
      intro ⟨f, hf_func, hf_inj, hf_surj⟩
      have hm_nat := mem_Omega_is_Nat m hm
      have hm_sub_n : m ⊆ n := Omega_element_is_transitive n hn m h_mem
      have hf_inv_bij := bijection_inverse_is_bijection ⟨hf_func, hf_inj, hf_surj⟩
      -- f⁻¹↾m : m → m injective, hence surjective by nat_injection_is_surjection
      have hf_inv_rest_func := restrict_is_function (f⁻¹) n m m hf_inv_bij.1 hm_sub_n
      have hf_inv_rest_surj :=
        nat_injection_is_surjection hm hf_inv_rest_func (restriction_is_injective hf_inv_bij.2.1)
      -- f surjective onto n: since m ∈ n, ∃ w ∈ m, f(w) = m
      obtain ⟨w, hw⟩ := hf_surj m h_mem
      have hw_m : w ∈ m := by
        have := hf_func.1 _ hw; rw [OrderedPair_mem_CartesianProduct] at this; exact this.1
      -- f⁻¹↾m surjective onto m: apply to w
      obtain ⟨x, hx⟩ := hf_inv_rest_surj w hw_m
      have hx_m : x ∈ m := by
        have := ((mem_restrict_iff (f⁻¹) m ⟨x, w⟩).mp hx).2
        rw [fst_of_ordered_pair] at this; exact this
      have hxw_f : ⟨w, x⟩ ∈ f :=
        (inverse_pair_iff f w x).mp (restrict_subset (f⁻¹) m ⟨x, w⟩ hx)
      -- f(w) = m and f(w) = x, so x = m, but x ∈ m
      obtain ⟨_, _, hz_uniq⟩ := hf_func.2 w hw_m
      have hm_eq := hz_uniq m hw
      have hx_eq := hz_uniq x hxw_f
      have heq : x = m := hx_eq.trans hm_eq.symm
      rw [heq] at hx_m
      exact not_mem_self m hm_nat hx_m

    /-- Uniqueness of finite cardinality: if n, m ∈ ω and n ≃ₛ m, then n = m. -/
    theorem finite_cardinality_unique {n m : U} (hn : n ∈ ω) (hm : m ∈ ω)
        (h : n ≃ₛ m) : n = m := by
      rcases trichotomy n m (mem_Omega_is_Nat n hn) (mem_Omega_is_Nat m hm)
        with h_lt | h_eq | h_gt
      · exact absurd h (not_equipotent_nat_smaller (n := m) (m := n) hm hn h_lt)
      · exact h_eq
      · exact absurd (equipotent_symm h) (not_equipotent_nat_smaller hn hm h_gt)

  end SetOps.FiniteSets

  export SetOps.FiniteSets (
    -- Identity bijection
    id_is_function id_is_injective id_is_surjective id_is_bijection
    equipotent_refl
    -- Definition
    isFiniteSet
    -- Basic properties
    empty_is_finite nat_is_finite
    -- Inverse bijection
    inverse_pair_iff
    bijection_inverse_is_function bijection_inverse_injective
    bijection_inverse_surjective bijection_inverse_is_bijection
    equipotent_symm
    -- Composition
    comp_injective comp_surjective comp_bijection
    equipotent_trans
    -- Closure
    finite_equipotent
    -- Singleton
    singleton_is_finite
    -- Adding an element
    finite_union_singleton
    -- restrict injectivity
    restriction_is_injective
    -- Pigeonhole principle
    no_injection_succ_to_nat
    -- Injection is surjection on finite sets
    nat_injection_is_surjection
    -- Uniqueness of finite cardinality
    not_equipotent_nat_smaller
    finite_cardinality_unique
  )

end ZFC
