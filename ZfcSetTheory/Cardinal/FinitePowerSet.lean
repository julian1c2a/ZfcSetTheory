/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Finite Power Set Cardinality

This module proves that for finite sets, the cardinality of the power set
is a power of 2: if |F| = n then |𝒫(F)| = 2^n.

## Main Definitions

* `removeElemMap A a` — the ZFC function S ↦ S \ {a} from {S ∈ 𝒫(A) | a ∈ S} to 𝒫(A \ {a})

## Main Theorems

* `equipotent_union_singleton` — A ≃ₛ n ∧ a ∉ A → (A ∪ {a}) ≃ₛ σ n
* `disjoint_union_equipotent` — disjoint A ≃ₛ m ∧ B ≃ₛ n → (A ∪ B) ≃ₛ add m n
* `mul_two_eq_double` — mul (σ(σ ∅)) m = add m m
* `powerset_cardinality` — A ≃ₛ n → 𝒫(A) ≃ₛ pow (σ(σ ∅)) n

## References

* Basic combinatorics: finite power set has 2^n elements
-/

import ZfcSetTheory.SetOps.FiniteSets
import ZfcSetTheory.Nat.Pow
import ZfcSetTheory.BoolAlg.FiniteCofinite

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
  open ZFC.SetOps.FiniteSets
  open ZFC.Nat.Add
  open ZFC.Nat.Mul
  open ZFC.Nat.Pow
  open ZFC.BoolAlg.FiniteCofinite
  universe u
  variable {U : Type u}

  namespace Cardinal.FinitePowerSet

    /-! ============================================================ -/
    /-! ### SECTION 1: EXTENDING BIJECTIONS BY ONE ELEMENT ### -/
    /-! ============================================================ -/

    /-- If A ≃ₛ n (n ∈ ω) and a ∉ A, then (A ∪ {a}) ≃ₛ σ n. -/
    theorem equipotent_union_singleton {A a n : U} (hn : n ∈ ω)
        (hAn : A ≃ₛ n) (ha : a ∉ A) : (union A {a}) ≃ₛ σ n := by
      obtain ⟨f, hf_func, hf_inj, hf_surj⟩ := hAn
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      refine ⟨union f {⟨a, n⟩}, ?_, ?_, ?_⟩
      · -- IsFunction (f ∪ {⟨a, n⟩}) (A ∪ {a}) (σ n)
        constructor
        · intro p hp
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
        · intro x hx
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
                exact absurd
                  ((Eq_of_OrderedPairs_given_projections x y' a n hy'_eq).1 ▸ hx_A) ha
          | inr hx_a =>
            rw [Singleton_is_specified] at hx_a
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
          | inl h₂_f => exact hf_inj x₁ x₂ y h₁_f h₂_f
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
    /-! ### SECTION 2: SET IDENTITIES ### -/
    /-! ============================================================ -/

    /-- Reconstruction: (A \ {a}) ∪ {a} = A when a ∈ A. -/
    theorem sdiff_singleton_union {A a : U} (ha : a ∈ A) :
        union (sdiff A {a}) {a} = A := by
      apply ExtSet; intro z; constructor
      · intro hz
        rw [mem_union_iff] at hz
        cases hz with
        | inl h => exact (mem_sdiff_iff A {a} z).mp h |>.1
        | inr h => rw [(Singleton_is_specified a z).mp h]; exact ha
      · intro hz
        rw [mem_union_iff]
        by_cases hza : z = a
        · right; exact (Singleton_is_specified a z).mpr hza
        · left; exact (mem_sdiff_iff A {a} z).mpr
            ⟨hz, fun h => hza ((Singleton_is_specified a z).mp h)⟩

    /-- Removing a freshly added element: (B ∪ {a}) \ {a} = B when a ∉ B. -/
    theorem union_sdiff_cancel {B a : U} (ha : a ∉ B) :
        sdiff (union B {a}) {a} = B := by
      apply ExtSet; intro z; constructor
      · intro hz
        rw [mem_sdiff_iff] at hz
        rw [mem_union_iff] at hz
        cases hz.1 with
        | inl h => exact h
        | inr h =>
          exfalso; exact hz.2 ((Singleton_is_specified a z).mpr
            ((Singleton_is_specified a z).mp h))
      · intro hz
        rw [mem_sdiff_iff, mem_union_iff]
        exact ⟨Or.inl hz, fun h =>
          ha (((Singleton_is_specified a z).mp h) ▸ hz)⟩

    /-- Adding and removing (T ∪ {a}) \ {a} = T when a ∉ T. -/
    theorem union_singleton_sdiff_cancel {T a : U} (ha : a ∉ T) :
        sdiff (union T {a}) {a} = T :=
      union_sdiff_cancel ha

    /-! ============================================================ -/
    /-! ### SECTION 3: DISJOINT UNION CARDINALITY ### -/
    /-! ============================================================ -/

    /-- Disjoint union of finite sets has additive cardinality. -/
    theorem disjoint_union_equipotent {A B m n : U} (hm : m ∈ ω) (hn : n ∈ ω)
        (hAm : A ≃ₛ m) (hBn : B ≃ₛ n) (hdisj : ∀ x, x ∈ A → x ∉ B) :
        (union A B) ≃ₛ add m n := by
      -- By induction on n
      let P : U → Prop := fun k =>
        ∀ B', B' ≃ₛ k → (∀ x, x ∈ A → x ∉ B') → (union A B') ≃ₛ add m k
      suffices hP : P n from hP B hBn hdisj
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have := (hS ▸ hn : n ∈ S)
        exact ((mem_sep_iff (ω : U) n P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · -- Base: ∅ ∈ S
        rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        intro B' hB'0 _hdisj'
        have hB'_empty := equipotent_empty_is_empty hB'0
        rw [hB'_empty, union_empty, add_zero m hm]
        exact hAm
      · -- Step: k ∈ S → σ k ∈ S
        intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        constructor
        · exact succ_in_Omega k hk_omega
        · intro B' hB'_sigma_k hdisj'
          obtain ⟨g, hg_bij⟩ := hB'_sigma_k
          -- Pick b₀ ∈ B' mapping to k
          obtain ⟨b₀, hb₀⟩ := hg_bij.2.2 k (mem_succ_self k)
          have hb₀_B' : b₀ ∈ B' := by
            have := hg_bij.1.1 _ hb₀
            rw [OrderedPair_mem_CartesianProduct] at this; exact this.1
          have hgb₀ : apply g b₀ = k :=
            apply_eq g b₀ k (hg_bij.1.2 b₀ hb₀_B') hb₀
          -- B'' = B' \ {b₀} ≃ₛ k
          have hB''_k : (sdiff B' {b₀}) ≃ₛ k :=
            ⟨g ↾ sdiff B' {b₀},
             remove_element_bijection hk_omega hg_bij hb₀_B' hgb₀⟩
          -- Disjointness for B''
          have hdisj'' : ∀ x, x ∈ A → x ∉ sdiff B' {b₀} := fun x hxA hxB'' =>
            hdisj' x hxA ((mem_sdiff_iff B' {b₀} x).mp hxB'').1
          -- IH: A ∪ B'' ≃ₛ add m k
          have h_ih := ih (sdiff B' {b₀}) hB''_k hdisj''
          -- b₀ ∉ A ∪ B''
          have hb₀_not_A : b₀ ∉ A := fun h => hdisj' b₀ h hb₀_B'
          have hb₀_not_B'' : b₀ ∉ sdiff B' ({b₀} : U) := fun h =>
            ((mem_sdiff_iff B' {b₀} b₀).mp h).2
              ((Singleton_is_specified b₀ b₀).mpr rfl)
          have hb₀_not_AB'' : b₀ ∉ union A (sdiff B' ({b₀} : U)) := fun h => by
            rw [mem_union_iff] at h
            exact h.elim hb₀_not_A hb₀_not_B''
          -- A ∪ B' = (A ∪ B'') ∪ {b₀}
          have h_decomp : union A B' =
              union (union A (sdiff B' ({b₀} : U))) ({b₀} : U) :=
            union_with_remove hb₀_B'
          -- (A ∪ B'') ∪ {b₀} ≃ₛ σ(add m k)
          have h_add_omega : add m k ∈ ω := add_in_Omega m k hm hk_omega
          have h_union_equiv :=
            equipotent_union_singleton h_add_omega h_ih hb₀_not_AB''
          -- σ(add m k) = add m (σ k)
          rw [(add_succ m k hm hk_omega).symm] at h_union_equiv
          -- Combine
          rw [h_decomp]
          exact h_union_equiv

    /-! ============================================================ -/
    /-! ### SECTION 4: POWERSET DECOMPOSITION ### -/
    /-! ============================================================ -/

    /-- The "without a" half of 𝒫(B ∪ {a}) equals 𝒫(B) when a ∉ B. -/
    theorem powerset_without_elem {B a : U} (ha : a ∉ B) :
        sep (𝒫 (union B {a})) (fun S => a ∉ S) = 𝒫 B := by
      apply ExtSet; intro S; constructor
      · intro hS
        rw [mem_sep_iff] at hS
        rw [mem_powerset_iff] at hS ⊢
        intro x hx
        have := hS.1 x hx
        rw [mem_union_iff] at this
        cases this with
        | inl h => exact h
        | inr h =>
          exfalso; exact hS.2 ((Singleton_is_specified a x).mp h ▸ hx)
      · intro hS
        rw [mem_sep_iff]
        constructor
        · rw [mem_powerset_iff] at hS ⊢
          exact fun x hx => (mem_union_iff B {a} x).mpr (Or.inl (hS x hx))
        · intro ha_S
          exact ha ((mem_powerset_iff B S).mp hS a ha_S)

    /-- The halves of 𝒫(A) by an element a are disjoint. -/
    theorem powerset_halves_disjoint (A a : U) :
        ∀ S, S ∈ sep (𝒫 A) (fun S => a ∉ S) →
        S ∉ sep (𝒫 A) (fun S => a ∈ S) := by
      intro S hS hS'
      rw [mem_sep_iff] at hS hS'
      exact hS.2 hS'.2

    /-- The halves of 𝒫(A) by an element a cover 𝒫(A). -/
    theorem powerset_halves_union (A a : U) :
        union (sep (𝒫 A) (fun S => a ∉ S)) (sep (𝒫 A) (fun S => a ∈ S)) = 𝒫 A := by
      apply ExtSet; intro S; constructor
      · intro hS
        rw [mem_union_iff] at hS
        cases hS with
        | inl h => exact (mem_sep_iff (𝒫 A) S (fun S => a ∉ S)).mp h |>.1
        | inr h => exact (mem_sep_iff (𝒫 A) S (fun S => a ∈ S)).mp h |>.1
      · intro hS
        rw [mem_union_iff]
        by_cases h : a ∈ S
        · right; exact (mem_sep_iff (𝒫 A) S (fun S => a ∈ S)).mpr ⟨hS, h⟩
        · left; exact (mem_sep_iff (𝒫 A) S (fun S => a ∉ S)).mpr ⟨hS, h⟩

    /-! ============================================================ -/
    /-! ### SECTION 5: REMOVE-ELEMENT BIJECTION ### -/
    /-! ============================================================ -/

    /-- The function S ↦ S \ {a} from {S ∈ 𝒫(A) | a ∈ S} to 𝒫(A \ {a}). -/
    noncomputable def removeElemMap (A a : U) : U :=
      sep (sep (𝒫 A) (fun S => a ∈ S) ×ₛ 𝒫 (sdiff A {a}))
        (fun p => ∃ S, S ∈ 𝒫 A ∧ a ∈ S ∧ p = ⟨S, sdiff S {a}⟩)

    /-- Specification lemma for removeElemMap. -/
    theorem removeElemMap_is_specified (A a S T : U) :
        ⟨S, T⟩ ∈ removeElemMap A a ↔
        S ∈ 𝒫 A ∧ a ∈ S ∧ T = sdiff S {a} := by
      unfold removeElemMap
      rw [mem_sep_iff]
      constructor
      · intro ⟨_, S', hS'_pow, hS'_a, hS'_eq⟩
        have hproj := Eq_of_OrderedPairs_given_projections S T S' (sdiff S' {a}) hS'_eq
        rw [hproj.1, hproj.2]
        exact ⟨hS'_pow, hS'_a, rfl⟩
      · intro ⟨hS_pow, ha_S, hT_eq⟩
        constructor
        · rw [hT_eq, OrderedPair_mem_CartesianProduct]
          constructor
          · exact (mem_sep_iff (𝒫 A) S (fun S => a ∈ S)).mpr ⟨hS_pow, ha_S⟩
          · rw [mem_powerset_iff]
            intro x hx
            rw [mem_sdiff_iff] at hx ⊢
            exact ⟨(mem_powerset_iff A S).mp hS_pow x hx.1, hx.2⟩
        · exact ⟨S, hS_pow, ha_S, by rw [hT_eq]⟩

    /-- The removeElemMap is a bijection from {S ∈ 𝒫(A) | a ∈ S} to 𝒫(A \ {a}). -/
    theorem removeElemMap_is_bijection (A a : U) (ha : a ∈ A) :
        isBijection (removeElemMap A a)
          (sep (𝒫 A) (fun S => a ∈ S)) (𝒫 (sdiff A {a})) := by
      refine ⟨?_, ?_, ?_⟩
      · -- IsFunction
        constructor
        · intro p hp
          unfold removeElemMap at hp
          rw [mem_sep_iff] at hp
          exact hp.1
        · intro S hS
          rw [mem_sep_iff] at hS
          apply ExistsUnique.intro (sdiff S {a})
          · exact (removeElemMap_is_specified A a S (sdiff S {a})).mpr
              ⟨hS.1, hS.2, rfl⟩
          · intro T' hT'
            exact (removeElemMap_is_specified A a S T').mp hT' |>.2.2
      · -- isInjective
        intro S₁ S₂ T h₁ h₂
        have h₁' := (removeElemMap_is_specified A a S₁ T).mp h₁
        have h₂' := (removeElemMap_is_specified A a S₂ T).mp h₂
        have hdiff_eq : sdiff S₁ ({a} : U) = sdiff S₂ ({a} : U) :=
          h₁'.2.2.symm.trans h₂'.2.2
        calc S₁
            = union (sdiff S₁ ({a} : U)) ({a} : U) := (sdiff_singleton_union h₁'.2.1).symm
          _ = union (sdiff S₂ ({a} : U)) ({a} : U) := by rw [hdiff_eq]
          _ = S₂ := sdiff_singleton_union h₂'.2.1
      · -- isSurjectiveOnto
        intro T hT
        rw [mem_powerset_iff] at hT
        refine ⟨union T {a}, ?_⟩
        apply (removeElemMap_is_specified A a (union T {a}) T).mpr
        refine ⟨?_, ?_, ?_⟩
        · -- T ∪ {a} ∈ 𝒫 A
          rw [mem_powerset_iff]
          intro x hx
          rw [mem_union_iff] at hx
          cases hx with
          | inl h =>
            have := hT x h
            exact (mem_sdiff_iff A {a} x).mp this |>.1
          | inr h => rw [(Singleton_is_specified a x).mp h]; exact ha
        · -- a ∈ T ∪ {a}
          exact (mem_union_iff T {a} a).mpr
            (Or.inr ((Singleton_is_specified a a).mpr rfl))
        · -- (T ∪ {a}) \ {a} = T
          -- a ∉ T because T ⊆ A \ {a}
          have ha_not_T : a ∉ T := fun h =>
            ((mem_sdiff_iff A {a} a).mp (hT a h)).2
              ((Singleton_is_specified a a).mpr rfl)
          exact (union_singleton_sdiff_cancel ha_not_T).symm

    /-! ============================================================ -/
    /-! ### SECTION 6: ARITHMETIC IDENTITY ### -/
    /-! ============================================================ -/

    /-- mul 2 m = add m m for m ∈ ω. -/
    theorem mul_two_eq_double (m : U) (hm : m ∈ ω) :
        mul (σ (σ (∅ : U))) m = add m m := by
      have h1 : σ (∅ : U) ∈ ω := succ_in_Omega (∅ : U) zero_in_Omega
      have h2 : σ (σ (∅ : U)) ∈ ω := succ_in_Omega (σ (∅ : U)) h1
      rw [mul_comm_Omega (σ (σ (∅ : U))) m h2 hm]
      rw [mul_succ m (σ (∅ : U)) hm h1]
      rw [mul_succ m ∅ hm zero_in_Omega]
      rw [mul_zero m hm]
      rw [add_zero m hm]

    /-! ============================================================ -/
    /-! ### SECTION 7: MAIN THEOREM ### -/
    /-! ============================================================ -/

    /-- The cardinality of the power set of a finite set:
        if A ≃ₛ n (n ∈ ω), then 𝒫(A) ≃ₛ pow (σ(σ ∅)) n (= 2^n). -/
    theorem powerset_cardinality {A n : U} (hn : n ∈ ω) (hAn : A ≃ₛ n) :
        𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n := by
      -- By induction on n
      let P : U → Prop := fun k =>
        ∀ A', A' ≃ₛ k → 𝒫 A' ≃ₛ pow (σ (σ (∅ : U))) k
      suffices hP : P n from hP A hAn
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have := (hS ▸ hn : n ∈ S)
        exact ((mem_sep_iff (ω : U) n P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · -- Base: ∅ ∈ S — 𝒫(∅) = {∅} = σ ∅ = pow 2 0
        rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        intro A' hA'0
        have hA'_empty := equipotent_empty_is_empty hA'0
        rw [hA'_empty, powerset_empty]
        have h1 : σ (∅ : U) ∈ ω := succ_in_Omega (∅ : U) zero_in_Omega
        have h2 : σ (σ (∅ : U)) ∈ ω := succ_in_Omega (σ (∅ : U)) h1
        rw [pow_zero (σ (σ (∅ : U))) h2]
        have h_succ_zero : σ (∅ : U) = {(∅ : U)} := empty_union {(∅ : U)}
        rw [h_succ_zero]
        exact equipotent_refl {(∅ : U)}
      · -- Step: k ∈ S → σ k ∈ S
        intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        have h1' : σ (∅ : U) ∈ ω := succ_in_Omega (∅ : U) zero_in_Omega
        have h2 : σ (σ (∅ : U)) ∈ ω := succ_in_Omega (σ (∅ : U)) h1'
        constructor
        · exact succ_in_Omega k hk_omega
        · intro A' hA'_sigma_k
          -- Extract a₀ ∈ A' mapping to k via the bijection
          obtain ⟨f, hf_bij⟩ := hA'_sigma_k
          obtain ⟨a₀, ha₀⟩ := hf_bij.2.2 k (mem_succ_self k)
          have ha₀_A' : a₀ ∈ A' := by
            have := hf_bij.1.1 _ ha₀
            rw [OrderedPair_mem_CartesianProduct] at this; exact this.1
          have hfa₀ : apply f a₀ = k :=
            apply_eq f a₀ k (hf_bij.1.2 a₀ ha₀_A') ha₀
          -- B = A' \ {a₀} ≃ₛ k
          let B := sdiff A' ({a₀} : U)
          have hB_k : B ≃ₛ k :=
            ⟨f ↾ B, remove_element_bijection hk_omega hf_bij ha₀_A' hfa₀⟩
          have ha₀_not_B : a₀ ∉ B := fun h =>
            ((mem_sdiff_iff A' {a₀} a₀).mp h).2
              ((Singleton_is_specified a₀ a₀).mpr rfl)
          -- A' = B ∪ {a₀}
          have hA'_eq : A' = union B ({a₀} : U) :=
            (sdiff_singleton_union ha₀_A').symm
          -- By IH: 𝒫(B) ≃ₛ pow 2 k
          have h_ih := ih B hB_k
          -- Rewrite the goal using A' = B ∪ {a₀}
          rw [hA'_eq]
          -- pow 2 (σ k) = mul 2 (pow 2 k) = add (pow 2 k) (pow 2 k)
          rw [pow_succ (σ (σ (∅ : U))) k h2 hk_omega]
          have hpow : pow (σ (σ (∅ : U))) k ∈ ω :=
            pow_in_Omega (σ (σ (∅ : U))) k h2 hk_omega
          rw [mul_two_eq_double (pow (σ (σ (∅ : U))) k) hpow]
          -- Goal: 𝒫(B ∪ {a₀}) ≃ₛ add (pow 2 k) (pow 2 k)
          -- Decompose: 𝒫(B ∪ {a₀}) = P₀ ∪ P₁
          let C := union B ({a₀} : U)
          let P₀ := sep (𝒫 C) (fun S => a₀ ∉ S)
          let P₁ := sep (𝒫 C) (fun S => a₀ ∈ S)
          -- P₀ = 𝒫(B)
          have hP0_eq : P₀ = 𝒫 B := powerset_without_elem ha₀_not_B
          -- removeElemMap codomain: (B ∪ {a₀}) \ {a₀} = B
          have hC_sdiff : sdiff C ({a₀} : U) = B :=
            union_sdiff_cancel ha₀_not_B
          -- P₁ ≃ₛ 𝒫(B) via removeElemMap
          have ha₀_C : a₀ ∈ C :=
            (mem_union_iff B {a₀} a₀).mpr
              (Or.inr ((Singleton_is_specified a₀ a₀).mpr rfl))
          have hP1_bij := removeElemMap_is_bijection C a₀ ha₀_C
          -- Rewrite codomain of hP1_bij using hC_sdiff
          have hP1_equiv : P₁ ≃ₛ 𝒫 B := by
            refine ⟨removeElemMap C a₀, ?_⟩
            rw [hC_sdiff] at hP1_bij
            exact hP1_bij
          -- 𝒫(C) = P₀ ∪ P₁
          have h_cover : union P₀ P₁ = 𝒫 C := powerset_halves_union C a₀
          -- P₀ ≃ₛ pow 2 k and P₁ ≃ₛ pow 2 k
          have hP0_equiv : P₀ ≃ₛ pow (σ (σ (∅ : U))) k := by
            rw [hP0_eq]; exact h_ih
          have hP1_pow : P₁ ≃ₛ pow (σ (σ (∅ : U))) k :=
            equipotent_trans hP1_equiv h_ih
          -- Disjoint
          have hdisj : ∀ x, x ∈ P₀ → x ∉ P₁ :=
            powerset_halves_disjoint C a₀
          -- Apply disjoint_union_equipotent
          rw [← h_cover]
          exact disjoint_union_equipotent hpow hpow hP0_equiv hP1_pow hdisj

  end Cardinal.FinitePowerSet

  export Cardinal.FinitePowerSet (
    equipotent_union_singleton
    sdiff_singleton_union
    union_sdiff_cancel
    union_singleton_sdiff_cancel
    disjoint_union_equipotent
    removeElemMap removeElemMap_is_specified removeElemMap_is_bijection
    powerset_without_elem
    powerset_halves_disjoint powerset_halves_union
    mul_two_eq_double
    powerset_cardinality
  )

end ZFC
