/-
Copyright (c) 2025. All rights reserved.
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
import ZfcSetTheory.SetOps.OrderedPair
import ZfcSetTheory.SetOps.CartesianProduct
import ZfcSetTheory.SetOps.Functions
import ZfcSetTheory.BoolAlg.PowerSetAlgebra
import ZfcSetTheory.BoolAlg.Basic
import ZfcSetTheory.SetOps.SetOrder
import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.SetOps.FiniteSets
import ZfcSetTheory.Nat.Add
import ZfcSetTheory.Cardinal.Basic
import ZfcSetTheory.BoolAlg.Complete

/-!
# Finite/Cofinite Boolean Algebra — A Non-Complete Counterexample

This file constructs the Boolean algebra of finite and cofinite subsets of ω,
and proves it is NOT a complete lattice, hence NOT isomorphic to any power set
algebra 𝒫(A).

## Main Definitions

* `isCofinite A X` — X is cofinite in A: A \ X is finite
* `isFinCof A X` — X ⊆ A and (X finite or X cofinite in A)
* `FinCofAlg A` — the set of all finite-or-cofinite subsets of A
* `EvenSet` — {n ∈ ω | ∃ k ∈ ω, n = add k k}

## Main Theorems

### Finite Set Closure
* `finite_subset` — subset of a finite set is finite
* `finite_union` — union of two finite sets is finite
* `Omega_not_finite` — ω is not a finite set

### Parity
* `even_or_odd` — every n ∈ ω is even (n = k+k) or odd (n = σ(k+k))
* `even_ne_odd` — add k k ≠ σ(add j j) for all k, j ∈ ω
* `EvenSet_infinite` — the set of even naturals is infinite
* `OddSet_infinite` — ω \ EvenSet is infinite

### Boolean Algebra Structure
* `FinCofAlg_empty` — ∅ ∈ FinCofAlg(ω)
* `FinCofAlg_universe` — ω ∈ FinCofAlg(ω)
* `FinCofAlg_complement` — closed under complement
* `FinCofAlg_union` — closed under union
* `FinCofAlg_inter` — closed under intersection

### Not a Complete Lattice
* `EvenSet_not_in_FinCofAlg` — EvenSet ∉ FinCofAlg(ω)
* `FinCofAlg_not_complete` — FinCofAlg(ω) is not a complete lattice
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
  open ZFC.BoolAlg.Basic
  open ZFC.SetOps.SetOrder
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.FiniteSets
  open ZFC.Nat.Add
  open ZFC.SetOps.Functions
  open ZFC.Cardinal.Basic
  open ZFC.BoolAlg.Complete
  universe u
  variable {U : Type u}

  namespace BoolAlg.FiniteCofinite

    /-! ============================================================ -/
    /-! ### PART 1: FINITE SET CLOSURE PROPERTIES                  -/
    /-! ============================================================ -/

    /-- If A ≃ₛ ∅, then A = ∅ -/
    theorem equipotent_empty_is_empty {A : U} (h : A ≃ₛ (∅ : U)) :
      A = ∅
        := by
      obtain ⟨f, hf_func, _, _⟩ := h
      apply ExtSet; intro z; constructor
      · intro hz
        obtain ⟨y, hy, _⟩ := hf_func.2 z hz
        have := hf_func.1 _ hy
        rw [OrderedPair_mem_CartesianProduct] at this
        exact absurd this.2 (EmptySet_is_empty y)
      · intro hz; exact absurd hz (EmptySet_is_empty z)

    /-- σ(k) \ {k} = k for k ∈ ω -/
    theorem sigma_remove_self {k : U} (hk : k ∈ ω) :
      (((σ k) \ {k}) = k)
        := by
      have hk_nat := mem_Omega_is_Nat k hk
      apply ExtSet; intro z; constructor
      · intro hz
        rw [Difference_is_specified] at hz
        rw [successor_is_specified] at hz
        cases hz.1 with
        | inl h => exact h
        | inr h =>
          exfalso; apply hz.2
          exact (Singleton_is_specified k z).mpr h
      · intro hz
        rw [Difference_is_specified, successor_is_specified]
        refine ⟨Or.inl hz, ?_⟩
        intro hzk
        have := (Singleton_is_specified k z).mp hzk
        rw [this] at hz
        exact nat_not_mem_self k hk_nat hz

    /-- Core removal lemma: removing the preimage of k from a bijection A → σ(k)
        gives a bijection A\{a₀} → k -/
    theorem remove_element_bijection {f A k a₀ : U}
        (hk : k ∈ ω)
        (hbij : isBijection f A (σ k))
        (ha₀ : a₀ ∈ A)
        (hfa₀ : apply f a₀ = k) :
        isBijection (f ↾ (A \ {a₀})) (A \ {a₀}) k := by
      obtain ⟨hf_func, hf_inj, hf_surj⟩ := hbij
      have hk_nat := mem_Omega_is_Nat k hk
      refine ⟨?_, restriction_is_injective hf_inj, ?_⟩
      · -- isFunctionFromTo (f ↾ (A \ {a₀})) (A \ {a₀}) k
        constructor
        · -- f ↾ (A \ {a₀}) ⊆ (A \ {a₀}) ×ₛ k
          intro p hp
          rw [Restriction_is_specified] at hp
          have hp_f := hp.1
          have h_fst := hp.2
          have h_prod := hf_func.1 p hp_f
          rw [CartesianProduct_is_specified] at h_prod ⊢
          refine ⟨h_prod.1, ?_, ?_⟩
          · -- fst p ∈ A \ {a₀}
            exact h_fst
          · -- snd p ∈ k
            have h_snd_sigma : snd p ∈ σ k := h_prod.2.2
            rw [successor_is_specified] at h_snd_sigma
            cases h_snd_sigma with
            | inl h => exact h
            | inr h =>
              -- snd p = k means fst p = a₀ (since f(a₀) = k and f injective)
              exfalso
              rw [Difference_is_specified] at h_fst
              apply h_fst.2
              -- Show fst p = a₀
              have h_fst_A := h_fst.1
              -- ⟨fst p, snd p⟩ ∈ f and ⟨a₀, k⟩ ∈ f
              have hp_in_f := hp_f
              have ha₀_in_f := apply_mem f a₀ (hf_func.2 a₀ ha₀)
              -- From f injective and snd p = k:
              -- need ⟨fst p, k⟩ ∈ f
              have h_pair_eq : p = ⟨fst p, snd p⟩ := by
                have := hf_func.1 p hp_f
                rw [CartesianProduct_is_specified] at this
                exact (isOrderedPair_by_construction p).mp this.1
              rw [h_pair_eq, h] at hp_in_f
              rw [hfa₀] at ha₀_in_f
              exact (Singleton_is_specified a₀ (fst p)).mpr
                (hf_inj (fst p) a₀ k hp_in_f ha₀_in_f)
        · -- ∀ x ∈ A \ {a₀}, ∃! y, ⟨x, y⟩ ∈ f ↾ (A \ {a₀})
          intro x hx
          rw [Difference_is_specified] at hx
          have hx_A := hx.1
          obtain ⟨y, hy, hy_unique⟩ := hf_func.2 x hx_A
          refine ⟨y, ?_, ?_⟩
          · show ⟨x, y⟩ ∈ f ↾ (A \ {a₀})
            rw [Restriction_is_specified]
            refine ⟨hy, ?_⟩
            rw [fst_of_ordered_pair]
            exact (Difference_is_specified A {a₀} x).mpr hx
          · intro y' hy'
            rw [Restriction_is_specified] at hy'
            exact hy_unique y' hy'.1
      · -- isSurjectiveOnto (f ↾ (A \ {a₀})) k
        intro y hy
        have hy_sigma : y ∈ σ k := by
          rw [successor_is_specified]; left; exact hy
        obtain ⟨x, hx⟩ := hf_surj y hy_sigma
        -- x ≠ a₀ because f(x) = y ≠ k = f(a₀)
        have hx_ne : x ≠ a₀ := by
          intro heq; rw [heq] at hx
          have := apply_eq f a₀ y (hf_func.2 a₀ ha₀) hx
          rw [hfa₀] at this; rw [← this] at hy
          exact nat_not_mem_self k hk_nat hy
        have hx_A : x ∈ A := by
          have := hf_func.1 _ hx
          rw [OrderedPair_mem_CartesianProduct] at this
          exact this.1
        refine ⟨x, ?_⟩
        rw [Restriction_is_specified]
        refine ⟨hx, ?_⟩
        rw [fst_of_ordered_pair, Difference_is_specified]
        exact ⟨hx_A, fun h => hx_ne ((Singleton_is_specified a₀ x).mp h)⟩

    /-- Subset of a finite set is finite -/
    theorem finite_subset {A B : U} (hA : isFiniteSet A) (hB : B ⊆ A) :
        isFiniteSet B := by
      obtain ⟨n, hn, hAn⟩ := hA
      -- By strong induction on n
      let P : U → Prop := fun m =>
        ∀ A' B', A' ≃ₛ m → B' ⊆ A' → isFiniteSet B'
      suffices hP : P n from hP A B hAn hB
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have := (hS ▸ hn : n ∈ S)
        exact ((SpecSet_is_specified (ω : U) n P).mp this).2
      apply strong_induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · intro m hm ih
        rw [SpecSet_is_specified]
        refine ⟨hm, ?_⟩
        intro A' B' hA'_eq hB'_sub
        -- Handle zero case
        have hm_nat := mem_Omega_is_Nat m hm
        rcases nat_is_zero_or_succ m hm_nat with rfl | ⟨k, rfl⟩
        · -- m = ∅: A' ≃ₛ ∅ → A' = ∅ → B' = ∅
          have := equipotent_empty_is_empty hA'_eq
          rw [this] at hB'_sub
          have : B' = ∅ := by
            apply ExtSet; intro z; constructor
            · intro hz; exact hB'_sub z hz
            · intro hz; exact absurd hz (EmptySet_is_empty z)
          rw [this]; exact empty_is_finite
        · -- m = σ(k)
          have hk_nat : isNat k := nat_element_is_nat (σ k) k hm_nat (mem_successor_self k)
          by_cases hB'_empty : B' = ∅
          · rw [hB'_empty]; exact empty_is_finite
          · -- B' ≠ ∅: pick b ∈ B'
            obtain ⟨b, hb⟩ := (nonempty_iff_exists_mem B').mp hB'_empty
            have hb_A' := hB'_sub b hb
            -- Get bijection f: A' → σ(k) and preimage a₀ of k
            obtain ⟨f, hf_bij⟩ := hA'_eq
            have hk : k ∈ ω := Nat_in_Omega k hk_nat
            have hk_sigma : k ∈ σ k := mem_successor_self k
            obtain ⟨a₀, ha₀⟩ := hf_bij.2.2 k hk_sigma
            have ha₀_A' : a₀ ∈ A' := by
              have := hf_bij.1.1 _ ha₀
              rw [OrderedPair_mem_CartesianProduct] at this; exact this.1
            have hfa₀ : apply f a₀ = k :=
              apply_eq f a₀ k (hf_bij.1.2 a₀ ha₀_A') ha₀
            -- f↾(A'\{a₀}) : A'\{a₀} → k bijection
            have h_rem_bij := remove_element_bijection hk hf_bij ha₀_A' hfa₀
            have h_rem_eq : ((A' \ {a₀}) ≃ₛ k) := ⟨f ↾ (A' \ {a₀}), h_rem_bij⟩
            -- IH: k ∈ m = σ(k), so P(k) holds
            have hk_in_m : k ∈ σ k := mem_successor_self k
            have ih_k := ih k hk_in_m
            rw [SpecSet_is_specified] at ih_k
            have ih_P := ih_k.2
            by_cases ha₀_B' : a₀ ∈ B'
            · -- a₀ ∈ B': B'\{a₀} ⊆ A'\{a₀}, finite by IH
              have hB'_sub' : ((B' \ {a₀}) ⊆ (A' \ {a₀})) := by
                intro z hz
                rw [Difference_is_specified] at hz ⊢
                exact ⟨hB'_sub z hz.1, hz.2⟩
              have hB'_rem_fin := ih_P (A' \ {a₀}) (B' \ {a₀}) h_rem_eq hB'_sub'
              -- B' = (B'\{a₀}) ∪ {a₀} and a₀ ∉ B'\{a₀}
              have ha₀_not : a₀ ∉ Difference B' {a₀} := by
                intro h; rw [Difference_is_specified] at h
                exact h.2 ((Singleton_is_specified a₀ a₀).mpr rfl)
              have hB'_eq : B' = BinUnion (Difference B' {a₀}) {a₀} := by
                apply ExtSet; intro z; constructor
                · intro hz
                  rw [BinUnion_is_specified]
                  by_cases h : z = a₀
                  · right; exact (Singleton_is_specified a₀ z).mpr h
                  · left; rw [Difference_is_specified]
                    exact ⟨hz, fun h' => h ((Singleton_is_specified a₀ z).mp h')⟩
                · intro hz
                  rw [BinUnion_is_specified] at hz
                  cases hz with
                  | inl h => exact (Difference_is_specified B' {a₀} z).mp h |>.1
                  | inr h =>
                    have := (Singleton_is_specified a₀ z).mp h
                    rw [this]; exact ha₀_B'
              rw [hB'_eq]
              exact finite_union_singleton hB'_rem_fin ha₀_not
            · -- a₀ ∉ B': B' ⊆ A'\{a₀}, finite by IH
              have hB'_sub' : B' ⊆ Difference A' {a₀} := by
                intro z hz
                rw [Difference_is_specified]
                refine ⟨hB'_sub z hz, ?_⟩
                intro h
                have := (Singleton_is_specified a₀ z).mp h
                rw [this] at hz; exact ha₀_B' hz
              exact ih_P (A' \ {a₀}) B' h_rem_eq hB'_sub'

    /-- A ∪ B = (A ∪ (B\{b})) ∪ {b} when b ∈ B -/
    theorem union_with_remove {A B b : U} (hb : b ∈ B) :
        BinUnion A B = BinUnion (BinUnion A (Difference B {b})) {b} := by
      apply ExtSet; intro z; constructor
      · intro hz
        rw [BinUnion_is_specified] at hz ⊢
        rw [BinUnion_is_specified]
        cases hz with
        | inl h => left; left; exact h
        | inr h =>
          by_cases hzb : z = b
          · right; exact (Singleton_is_specified b z).mpr hzb
          · left; right
            rw [Difference_is_specified]
            exact ⟨h, fun h' => hzb ((Singleton_is_specified b z).mp h')⟩
      · intro hz
        rw [BinUnion_is_specified] at hz
        rw [BinUnion_is_specified]
        cases hz with
        | inl h =>
          rw [BinUnion_is_specified] at h
          cases h with
          | inl h => left; exact h
          | inr h =>
            right; exact (Difference_is_specified B {b} z).mp h |>.1
        | inr h =>
          right; rw [(Singleton_is_specified b z).mp h]; exact hb

    /-- Union of two finite sets is finite -/
    theorem finite_union {A B : U} (hA : isFiniteSet A) (hB : isFiniteSet B) :
        isFiniteSet (A ∪ B) := by
      obtain ⟨n, hn, hBn⟩ := hB
      -- By induction on n (size of B)
      let P : U → Prop := fun m =>
        ∀ A' B', isFiniteSet A' → B' ≃ₛ m → isFiniteSet (A' ∪ B')
      suffices hP : P n from hP A B hA hBn
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have := (hS ▸ hn : n ∈ S)
        exact ((SpecSet_is_specified (ω : U) n P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: n = ∅
        rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun A' B' hA' hB'_eq => ?_⟩
        have hB'_empty := equipotent_empty_is_empty hB'_eq
        rw [hB'_empty, BinUnion_empty_right]
        exact hA'
      · -- Step: P(m) → P(σm)
        intro m hm
        rw [SpecSet_is_specified] at hm ⊢
        obtain ⟨hm_w, ih⟩ := hm
        refine ⟨succ_in_Omega m hm_w, fun A' B' hA' hB'_eq => ?_⟩
        -- Get bijection g: B' → σ(m) and preimage of m
        obtain ⟨g, hg_bij⟩ := hB'_eq
        have hm_sigma : m ∈ σ m := mem_successor_self m
        obtain ⟨b₀, hb₀⟩ := hg_bij.2.2 m hm_sigma
        have hb₀_B' : b₀ ∈ B' := by
          have := hg_bij.1.1 _ hb₀
          rw [OrderedPair_mem_CartesianProduct] at this; exact this.1
        have hgb₀ : apply g b₀ = m :=
          apply_eq g b₀ m (hg_bij.1.2 b₀ hb₀_B') hb₀
        -- g↾(B'\{b₀}) : B'\{b₀} → m bijection
        have h_rem := remove_element_bijection hm_w hg_bij hb₀_B' hgb₀
        have h_rem_eq : Difference B' {b₀} ≃ₛ m := ⟨g ↾ (B' \ {b₀}), h_rem⟩
        -- By IH: A' ∪ (B'\{b₀}) is finite
        have h_union_fin := ih A' (B' \ {b₀}) hA' h_rem_eq
        -- A' ∪ B' = (A' ∪ (B'\{b₀})) ∪ {b₀}
        rw [union_with_remove hb₀_B']
        by_cases hb₀_in : b₀ ∈ BinUnion A' (Difference B' {b₀})
        · -- b₀ already present
          have : BinUnion (BinUnion A' (Difference B' {b₀})) {b₀} = BinUnion A' (Difference B' {b₀}) := by
            apply ExtSet; intro z; constructor
            · intro hz
              rw [BinUnion_is_specified] at hz
              cases hz with
              | inl h => exact h
              | inr h =>
                rw [(Singleton_is_specified b₀ z).mp h]; exact hb₀_in
            · intro hz
              rw [BinUnion_is_specified]; left; exact hz
          rw [this]; exact h_union_fin
        · exact finite_union_singleton h_union_fin hb₀_in

    /-- ω is not a finite set -/
    theorem Omega_not_finite : ¬isFiniteSet (ω : U) := by
      intro ⟨n, hn, h_eq⟩
      obtain ⟨f, hf_bij⟩ := h_eq
      -- σ(n) ⊆ ω
      have hσn_sub : σ n ⊆ (ω : U) := by
        intro z hz
        rw [successor_is_specified] at hz
        cases hz with
        | inl h =>
          have h_n_nat := mem_Omega_is_Nat n hn
          exact Nat_in_Omega z (nat_element_is_nat n z h_n_nat h)
        | inr h => rw [h]; exact hn
      -- Restrict f to σ(n): injection σ(n) → n
      have h_sub : σ n ⊆ (ω : U) := hσn_sub
      have h_dom_sub : (σ n : U) ⊆ (ω : U) := hσn_sub
      have h_restr_func := Restriction_is_function f ω n (σ n) hf_bij.1 h_dom_sub
      have h_restr_inj : isInjective (f ↾ (σ n)) := restriction_is_injective hf_bij.2.1
      exact no_injection_succ_to_nat hn (f ↾ σ n) h_restr_func h_restr_inj

    /-! ============================================================ -/
    /-! ### PART 2: PARITY ON ω                                     -/
    /-! ============================================================ -/

    /-- add n n ∈ ω for n ∈ ω -/
    theorem double_in_Omega {n : U} (hn : n ∈ ω) : add n n ∈ (ω : U) :=
      add_in_Omega n n hn hn

    /-- Key computation: σ(σ(add k k)) = add (σ k) (σ k) -/
    theorem succ_succ_double_eq_double_succ {k : U} (hk : k ∈ ω) :
        σ (σ (add k k)) = add (σ k) (σ k) := by
      have hσk : σ k ∈ (ω : U) := succ_in_Omega k hk
      -- add (σ k) (σ k) = σ(add (σ k) k) [by add_succ]
      rw [add_succ (σ k) k hσk hk]
      -- add (σ k) k = add k (σ k) [by add_comm]
      rw [add_comm_Omega (σ k) k hσk hk]
      -- add k (σ k) = σ(add k k) [by add_succ]
      rw [add_succ k k hk hk]

    /-- Even ≠ Odd: add k k ≠ σ(add j j) for all k, j ∈ ω -/
    theorem even_ne_odd : ∀ k, k ∈ (ω : U) → ∀ j, j ∈ (ω : U) →
        add k k ≠ σ (add j j) := by
      -- By induction on k
      let P : U → Prop := fun k => ∀ j, j ∈ (ω : U) → add k k ≠ σ (add j j)
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        intro k hk
        have := (hS ▸ hk : k ∈ S)
        exact ((SpecSet_is_specified (ω : U) k P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: k = ∅. add ∅ ∅ = ∅ ≠ σ(anything)
        rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun j _ h => ?_⟩
        rw [add_zero ∅ zero_in_Omega] at h
        exact successor_nonempty (add j j) h.symm
      · -- Step: P(k) → P(σk)
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        obtain ⟨hk_w, ih⟩ := hk
        refine ⟨succ_in_Omega k hk_w, fun j hj h => ?_⟩
        -- add (σ k) (σ k) = σ(σ(add k k))
        rw [← succ_succ_double_eq_double_succ hk_w] at h
        -- h : σ(σ(add k k)) = σ(add j j)
        -- So σ(add k k) = add j j
        have h1 := successor_injective _ _ (mem_Omega_is_Nat _ (succ_in_Omega _ (double_in_Omega hk_w))) (mem_Omega_is_Nat _ (double_in_Omega hj)) h
        -- j = ∅ or j = σ(j')
        rcases nat_is_zero_or_succ j (mem_Omega_is_Nat j hj) with rfl | ⟨j', rfl⟩
        · -- j = ∅: add ∅ ∅ = ∅, but σ(add k k) ≠ ∅
          rw [add_zero ∅ zero_in_Omega] at h1
          exact successor_nonempty (add k k) h1
        · -- j = σ(j'): add (σ j') (σ j') = σ(σ(add j' j'))
          have hj' : j' ∈ (ω : U) := by
            have := mem_Omega_is_Nat (σ j') hj
            exact Nat_in_Omega j' (nat_element_is_nat (σ j') j' this (mem_successor_self j'))
          rw [← succ_succ_double_eq_double_succ hj'] at h1
          -- h1 : σ(add k k) = σ(σ(add j' j'))
          have h2 := successor_injective _ _ (mem_Omega_is_Nat _ (double_in_Omega hk_w)) (mem_Omega_is_Nat _ (succ_in_Omega _ (double_in_Omega hj'))) h1
          -- h2 : add k k = σ(add j' j')
          exact ih j' hj' h2

    /-- Every n ∈ ω is even or odd -/
    theorem even_or_odd (n : U) (hn : n ∈ ω) :
        (∃ k, k ∈ (ω : U) ∧ n = add k k) ∨
        (∃ k, k ∈ (ω : U) ∧ n = σ (add k k)) := by
      let P : U → Prop := fun m =>
        (∃ k, k ∈ (ω : U) ∧ m = add k k) ∨
        (∃ k, k ∈ (ω : U) ∧ m = σ (add k k))
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have := (hS ▸ hn : n ∈ S)
        exact ((SpecSet_is_specified (ω : U) n P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: ∅ is even (k = ∅)
        rw [SpecSet_is_specified]
        exact ⟨zero_in_Omega, Or.inl ⟨∅, zero_in_Omega, (add_zero ∅ zero_in_Omega).symm⟩⟩
      · -- Step: P(m) → P(σm)
        intro m hm
        rw [SpecSet_is_specified] at hm ⊢
        obtain ⟨hm_w, ih⟩ := hm
        refine ⟨succ_in_Omega m hm_w, ?_⟩
        cases ih with
        | inl h =>
          -- m = add k k (even) → σ(m) = σ(add k k) (odd)
          obtain ⟨k, hk, hm_eq⟩ := h
          exact Or.inr ⟨k, hk, congrArg successor hm_eq⟩
        | inr h =>
          -- m = σ(add k k) (odd) → σ(m) = σ(σ(add k k)) = add (σk) (σk) (even)
          obtain ⟨k, hk, hm_eq⟩ := h
          rw [hm_eq]
          exact Or.inl ⟨σ k, succ_in_Omega k hk,
            succ_succ_double_eq_double_succ hk⟩

    /-- Doubling is injective: add k k = add j j → k = j -/
    theorem double_injective : ∀ k, k ∈ (ω : U) → ∀ j, j ∈ (ω : U) →
        add k k = add j j → k = j := by
      let P : U → Prop := fun k => ∀ j, j ∈ (ω : U) → add k k = add j j → k = j
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        intro k hk
        have := (hS ▸ hk : k ∈ S)
        exact ((SpecSet_is_specified (ω : U) k P).mp this).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: k = ∅
        rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun j hj h => ?_⟩
        rw [add_zero ∅ zero_in_Omega] at h
        rcases nat_is_zero_or_succ j (mem_Omega_is_Nat j hj) with rfl | ⟨j', rfl⟩
        · rfl
        · have hj' : j' ∈ (ω : U) := by
            have := mem_Omega_is_Nat (σ j') hj
            exact Nat_in_Omega j' (nat_element_is_nat (σ j') j' this (mem_successor_self j'))
          rw [← succ_succ_double_eq_double_succ hj'] at h
          exact absurd h.symm (successor_nonempty _)
      · -- Step: P(k) → P(σk)
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        obtain ⟨hk_w, ih⟩ := hk
        refine ⟨succ_in_Omega k hk_w, fun j hj h => ?_⟩
        rw [← succ_succ_double_eq_double_succ hk_w] at h
        rcases nat_is_zero_or_succ j (mem_Omega_is_Nat j hj) with rfl | ⟨j', rfl⟩
        · rw [add_zero ∅ zero_in_Omega] at h
          exact absurd h (successor_nonempty _)
        · have hj' : j' ∈ (ω : U) := by
            have := mem_Omega_is_Nat (σ j') hj
            exact Nat_in_Omega j' (nat_element_is_nat (σ j') j' this (mem_successor_self j'))
          rw [← succ_succ_double_eq_double_succ hj'] at h
          have h_step1 := successor_injective _ _ (mem_Omega_is_Nat _ (succ_in_Omega _ (double_in_Omega hk_w))) (mem_Omega_is_Nat _ (succ_in_Omega _ (double_in_Omega hj'))) h
          have h2 := successor_injective _ _ (mem_Omega_is_Nat _ (double_in_Omega hk_w)) (mem_Omega_is_Nat _ (double_in_Omega hj')) h_step1
          exact congrArg successor (ih j' hj' h2)

    /-- The set of even naturals -/
    noncomputable def EvenSet : U :=
      SpecSet (ω : U) (fun n => ∃ k, k ∈ (ω : U) ∧ n = add k k)

    /-- Specification for EvenSet -/
    theorem EvenSet_is_specified (n : U) :
        n ∈ (EvenSet : U) ↔ n ∈ (ω : U) ∧ ∃ k, k ∈ (ω : U) ∧ n = add k k := by
      exact SpecSet_is_specified (ω : U) n _

    /-- EvenSet ⊆ ω -/
    theorem EvenSet_subset_Omega : (EvenSet : U) ⊆ ω := by
      intro n hn; exact (EvenSet_is_specified n).mp hn |>.1

    /-- add k k ∈ EvenSet for k ∈ ω -/
    theorem double_in_EvenSet {k : U} (hk : k ∈ ω) : add k k ∈ (EvenSet : U) := by
      rw [EvenSet_is_specified]
      exact ⟨double_in_Omega hk, k, hk, rfl⟩

    /-- σ(add k k) ∉ EvenSet for k ∈ ω -/
    theorem succ_double_not_even {k : U} (hk : k ∈ ω) :
        σ (add k k) ∉ (EvenSet : U) := by
      intro h
      rw [EvenSet_is_specified] at h
      obtain ⟨_, j, hj, h_eq⟩ := h
      exact even_ne_odd j hj k hk h_eq.symm

    /-- σ(add k k) ∈ ω \ EvenSet for k ∈ ω -/
    theorem succ_double_in_OddSet {k : U} (hk : k ∈ ω) :
        σ (add k k) ∈ Difference (ω : U) (EvenSet : U) := by
      rw [Difference_is_specified]
      exact ⟨succ_in_Omega (add k k) (double_in_Omega hk), succ_double_not_even hk⟩

    /-- σ(m) ⊆ ω for m ∈ ω -/
    private theorem sigma_sub_Omega {m : U} (hm : m ∈ ω) : σ m ⊆ (ω : U) := by
      intro z hz
      rw [successor_is_specified] at hz
      cases hz with
      | inl h => exact Nat_in_Omega z (nat_element_is_nat m z (mem_Omega_is_Nat m hm) h)
      | inr h => rw [h]; exact hm

    /-- Helper: build a ZFC function from a mapping φ on a domain A,
        prove it is a function into B and injective -/
    private theorem injection_from_mapping {A B : U}
        (φ : U → U) (hφ : ∀ x, x ∈ A → φ x ∈ B)
        (hφ_inj : ∀ x₁ x₂, x₁ ∈ A → x₂ ∈ A → φ x₁ = φ x₂ → x₁ = x₂) :
        let f := SpecSet (A ×ₛ B) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, φ x⟩)
        isFunctionFromTo f A B ∧ isInjective f := by
      intro f
      constructor
      · constructor
        · intro p hp
          rw [SpecSet_is_specified] at hp; exact hp.1
        · intro x hx
          refine ⟨φ x, ?_, ?_⟩
          · show ⟨x, φ x⟩ ∈ f
            rw [SpecSet_is_specified]
            exact ⟨(OrderedPair_mem_CartesianProduct x (φ x) A B).mpr ⟨hx, hφ x hx⟩,
                   x, hx, rfl⟩
          · intro y' hy'
            rw [SpecSet_is_specified] at hy'
            obtain ⟨_, x', hx', h_eq⟩ := hy'
            have heq := Eq_of_OrderedPairs_given_projections x y' x' (φ x') h_eq
            rw [heq.2, ← heq.1]
      · intro x₁ x₂ y h₁ h₂
        rw [SpecSet_is_specified] at h₁ h₂
        obtain ⟨_, j₁, hj₁, h_eq₁⟩ := h₁
        obtain ⟨_, j₂, hj₂, h_eq₂⟩ := h₂
        have heq₁ := Eq_of_OrderedPairs_given_projections x₁ y j₁ (φ j₁) h_eq₁
        have heq₂ := Eq_of_OrderedPairs_given_projections x₂ y j₂ (φ j₂) h_eq₂
        rw [heq₁.1, heq₂.1]
        exact hφ_inj j₁ j₂ hj₁ hj₂ (heq₁.2.symm.trans heq₂.2)

    /-- EvenSet is not finite -/
    theorem EvenSet_infinite : ¬isFiniteSet (EvenSet : U) := by
      intro ⟨m, hm, h_eq⟩
      obtain ⟨g, hg_func, hg_inj, hg_surj⟩ := h_eq
      have hσm_sub := sigma_sub_Omega hm
      have hφ_cod : ∀ k, k ∈ σ m → apply g (add k k) ∈ m := by
        intro k hk
        have hk_w := hσm_sub k hk
        have h_even := double_in_EvenSet hk_w
        have h_pair := apply_mem g (add k k) (hg_func.2 (add k k) h_even)
        have h_prod := hg_func.1 _ h_pair
        rw [OrderedPair_mem_CartesianProduct] at h_prod
        exact h_prod.2
      have hφ_inj : ∀ k₁ k₂, k₁ ∈ σ m → k₂ ∈ σ m →
          apply g (add k₁ k₁) = apply g (add k₂ k₂) → k₁ = k₂ := by
        intro k₁ k₂ hk₁ hk₂ h
        have hk₁_w := hσm_sub k₁ hk₁
        have hk₂_w := hσm_sub k₂ hk₂
        have h₁ := apply_mem g (add k₁ k₁) (hg_func.2 _ (double_in_EvenSet hk₁_w))
        have h₂ := apply_mem g (add k₂ k₂) (hg_func.2 _ (double_in_EvenSet hk₂_w))
        rw [h] at h₁
        have := hg_inj _ _ _ h₁ h₂
        exact double_injective k₁ hk₁_w k₂ hk₂_w this
      have h_data := injection_from_mapping (fun k => apply g (add k k)) hφ_cod hφ_inj
      exact no_injection_succ_to_nat hm _ h_data.1 h_data.2

    /-- ω \ EvenSet (the odd numbers) is not finite -/
    theorem OddSet_infinite : ¬isFiniteSet (Difference (ω : U) (EvenSet : U)) := by
      intro ⟨m, hm, h_eq⟩
      obtain ⟨g, hg_func, hg_inj, hg_surj⟩ := h_eq
      have hσm_sub := sigma_sub_Omega hm
      have hφ_cod : ∀ k, k ∈ σ m → apply g (σ (add k k)) ∈ m := by
        intro k hk
        have hk_w := hσm_sub k hk
        have h_odd := succ_double_in_OddSet hk_w
        have h_pair := apply_mem g (σ (add k k)) (hg_func.2 _ h_odd)
        have h_prod := hg_func.1 _ h_pair
        rw [OrderedPair_mem_CartesianProduct] at h_prod
        exact h_prod.2
      have hφ_inj : ∀ k₁ k₂, k₁ ∈ σ m → k₂ ∈ σ m →
          apply g (σ (add k₁ k₁)) = apply g (σ (add k₂ k₂)) → k₁ = k₂ := by
        intro k₁ k₂ hk₁ hk₂ h
        have hk₁_w := hσm_sub k₁ hk₁
        have hk₂_w := hσm_sub k₂ hk₂
        have h₁ := apply_mem g (σ (add k₁ k₁)) (hg_func.2 _ (succ_double_in_OddSet hk₁_w))
        have h₂ := apply_mem g (σ (add k₂ k₂)) (hg_func.2 _ (succ_double_in_OddSet hk₂_w))
        rw [h] at h₁
        have h_eq_succ := hg_inj _ _ _ h₁ h₂
        have h_eq_double := successor_injective _ _ (mem_Omega_is_Nat _ (double_in_Omega hk₁_w)) (mem_Omega_is_Nat _ (double_in_Omega hk₂_w)) h_eq_succ
        exact double_injective k₁ hk₁_w k₂ hk₂_w h_eq_double
      have h_data := injection_from_mapping (fun k => apply g (σ (add k k))) hφ_cod hφ_inj
      exact no_injection_succ_to_nat hm _ h_data.1 h_data.2

    /-! ============================================================ -/
    /-! ### PART 3: FINITE/COFINITE ALGEBRA                        -/
    /-! ============================================================ -/

    /-- X is cofinite in A: A \ X is finite -/
    def isCofinite (A X : U) : Prop := isFiniteSet (A \ X)

    /-- X is finite or cofinite in A -/
    def isFinCof (A X : U) : Prop := X ⊆ A ∧ (isFiniteSet X ∨ isCofinite A X)

    /-- The finite/cofinite algebra: all finite-or-cofinite subsets of A -/
    noncomputable def FinCofAlg (A : U) : U :=
      SpecSet (𝒫 A) (fun X => isFiniteSet X ∨ isCofinite A X)

    /-- Specification for FinCofAlg -/
    theorem FinCofAlg_is_specified (A X : U) :
        X ∈ FinCofAlg A ↔ X ∈ 𝒫 A ∧ (isFiniteSet X ∨ isCofinite A X) := by
      exact SpecSet_is_specified (𝒫 A) X _

    /-- FinCofAlg(A) ⊆ 𝒫(A) -/
    theorem FinCofAlg_subset_PowerSet (A : U) : FinCofAlg A ⊆ 𝒫 A := by
      intro X hX; exact (FinCofAlg_is_specified A X).mp hX |>.1

    /-- ∅ ∈ FinCofAlg(A) -/
    theorem FinCofAlg_empty (A : U) : (∅ : U) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified]
      exact ⟨empty_mem_PowerSet A, Or.inl empty_is_finite⟩

    /-- A ∈ FinCofAlg(A) -/
    theorem FinCofAlg_universe (A : U) : A ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified]
      refine ⟨self_mem_PowerSet A, Or.inr ?_⟩
      show isFiniteSet (Difference A A)
      rw [Difference_self_empty]; exact empty_is_finite

    /-- Complement swaps finite ↔ cofinite -/
    theorem FinCofAlg_complement (A X : U) (hX : X ∈ FinCofAlg A) :
        (X ^∁[ A ]) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified] at hX ⊢
      obtain ⟨hX_PA, hX_fc⟩ := hX
      have hX_sub := (PowerSet_is_specified A X).mp hX_PA
      refine ⟨complement_mem_PowerSet A X hX_PA, ?_⟩
      cases hX_fc with
      | inl hfin =>
        -- X finite → complement cofinite: A \ (X ^∁[A]) = X
        right
        show isFiniteSet (Difference A (X ^∁[ A ]))
        suffices h : Difference A (X ^∁[ A ]) = X by rw [h]; exact hfin
        apply ExtSet; intro z; constructor
        · intro hz
          rw [Difference_is_specified, Complement_is_specified] at hz
          exact Classical.byContradiction (fun h => hz.2 ⟨hz.1, h⟩)
        · intro hz
          rw [Difference_is_specified, Complement_is_specified]
          exact ⟨hX_sub z hz, fun h_abs => h_abs.2 hz⟩
      | inr hcofin =>
        left; exact hcofin

    /-- Union preserves FinCofAlg -/
    theorem FinCofAlg_union (A X Y : U) (hX : X ∈ FinCofAlg A) (hY : Y ∈ FinCofAlg A) :
        (X ∪ Y) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified] at hX hY ⊢
      obtain ⟨hX_PA, hX_fc⟩ := hX
      obtain ⟨hY_PA, hY_fc⟩ := hY
      refine ⟨union_mem_PowerSet A X Y hX_PA hY_PA, ?_⟩
      cases hX_fc with
      | inl hX_fin =>
        cases hY_fc with
        | inl hY_fin => left; exact finite_union hX_fin hY_fin
        | inr hY_cof =>
          right
          show isFiniteSet (Difference A (X ∪ Y))
          -- A \ (X ∪ Y) ⊆ A \ Y (finite by hY_cof)
          have h_sub : Difference A (X ∪ Y) ⊆ Difference A Y := by
            intro z hz
            rw [Difference_is_specified] at hz ⊢
            exact ⟨hz.1, fun h => hz.2 ((BinUnion_is_specified X Y z).mpr (Or.inr h))⟩
          exact finite_subset hY_cof h_sub
      | inr hX_cof =>
        right
        show isFiniteSet (Difference A (X ∪ Y))
        have h_sub : Difference A (X ∪ Y) ⊆ Difference A X := by
          intro z hz
          rw [Difference_is_specified] at hz ⊢
          exact ⟨hz.1, fun h => hz.2 ((BinUnion_is_specified X Y z).mpr (Or.inl h))⟩
        exact finite_subset hX_cof h_sub

    /-- Intersection preserves FinCofAlg -/
    theorem FinCofAlg_inter (A X Y : U) (hX : X ∈ FinCofAlg A) (hY : Y ∈ FinCofAlg A) :
        (X ∩ Y) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified] at hX hY ⊢
      obtain ⟨hX_PA, hX_fc⟩ := hX
      obtain ⟨hY_PA, hY_fc⟩ := hY
      refine ⟨inter_mem_PowerSet A X Y hX_PA hY_PA, ?_⟩
      cases hX_fc with
      | inl hX_fin =>
        left
        exact finite_subset hX_fin (fun z hz =>
          (BinInter_is_specified X Y z).mp hz |>.1)
      | inr hX_cof =>
        cases hY_fc with
        | inl hY_fin =>
          left
          exact finite_subset hY_fin (fun z hz =>
            (BinInter_is_specified X Y z).mp hz |>.2)
        | inr hY_cof =>
          right
          show isFiniteSet (Difference A (X ∩ Y))
          -- A \ (X ∩ Y) ⊆ (A \ X) ∪ (A \ Y), both finite
          suffices h : Difference A (BinInter X Y) ⊆ BinUnion (Difference A X) (Difference A Y) by
            exact finite_subset (finite_union hX_cof hY_cof) h
          intro z hz
          rw [Difference_is_specified] at hz
          rw [BinUnion_is_specified, Difference_is_specified, Difference_is_specified]
          by_cases hzX : z ∈ X
          · right; exact ⟨hz.1, fun h => hz.2 ((BinInter_is_specified X Y z).mpr ⟨hzX, h⟩)⟩
          · left; exact ⟨hz.1, hzX⟩

    /-! ============================================================ -/
    /-! ### PART 4: NOT COMPLETE, NOT ISOMORPHIC TO ANY 𝒫(A)       -/
    /-! ============================================================ -/

    /-- EvenSet ∉ FinCofAlg(ω): it is neither finite nor cofinite -/
    theorem EvenSet_not_in_FinCofAlg :
        (EvenSet : U) ∉ FinCofAlg (ω : U) := by
      intro h
      rw [FinCofAlg_is_specified] at h
      cases h.2 with
      | inl hfin => exact EvenSet_infinite hfin
      | inr hcofin => exact OddSet_infinite hcofin

    /-- Singletons of elements of X are in FinCofAlg(A) when X ⊆ A -/
    theorem singletons_in_FinCofAlg {A X x : U} (hX : X ⊆ A) (hx : x ∈ X) :
        ({x} : U) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified]
      refine ⟨?_, Or.inl (singleton_is_finite x)⟩
      rw [PowerSet_is_specified]
      intro z hz
      have := (Singleton_is_specified x z).mp hz
      rw [this]; exact hX x hx

    /-- FinCofAlg(ω) is NOT a complete lattice -/
    theorem FinCofAlg_not_complete :
        ¬isCompleteLattice (FinCofAlg (ω : U)) := by
      intro h_complete
      -- S = {{x} | x ∈ EvenSet} ⊆ FinCofAlg(ω)
      let Singletons := SpecSet (FinCofAlg (ω : U))
        (fun Y => ∃ x, x ∈ (EvenSet : U) ∧ Y = {x})
      have hS_sub : Singletons ⊆ FinCofAlg (ω : U) := by
        intro Y hY
        rw [SpecSet_is_specified] at hY; exact hY.1
      -- By completeness, S has a supremum Z ∈ FinCofAlg(ω)
      obtain ⟨⟨Z, hZ_mem, hZ_ub, hZ_lub⟩, _⟩ := h_complete Singletons hS_sub
      -- Z ⊇ EvenSet
      have hEven_sub_Z : (EvenSet : U) ⊆ Z := by
        intro x hx
        have h_sing_in : ({x} : U) ∈ Singletons := by
          rw [SpecSet_is_specified]
          exact ⟨singletons_in_FinCofAlg EvenSet_subset_Omega hx, x, hx, rfl⟩
        exact hZ_ub {x} h_sing_in x ((Singleton_is_specified x x).mpr rfl)
      -- Z ⊆ ω
      have hZ_sub_w : Z ⊆ (ω : U) :=
        (PowerSet_is_specified ω Z).mp (FinCofAlg_subset_PowerSet ω Z hZ_mem)
      -- Z must be cofinite (cannot be finite since EvenSet ⊆ Z and EvenSet is infinite)
      have hZ_cofin : isCofinite (ω : U) Z := by
        cases (FinCofAlg_is_specified ω Z).mp hZ_mem |>.2 with
        | inl hfin => exact absurd (finite_subset hfin hEven_sub_Z) EvenSet_infinite
        | inr hcof => exact hcof
      -- Z ≠ EvenSet (since EvenSet ∉ FinCofAlg)
      have hZ_ne_Even : Z ≠ (EvenSet : U) := by
        intro h; rw [h] at hZ_mem
        exact EvenSet_not_in_FinCofAlg hZ_mem
      -- ∃ z ∈ Z \ EvenSet
      have ⟨z, hz_Z, hz_not_Even⟩ : ∃ z, z ∈ Z ∧ z ∉ (EvenSet : U) := by
        apply Classical.byContradiction
        intro h_all
        apply hZ_ne_Even
        apply ExtSet; intro x; constructor
        · intro hx_Z
          exact Classical.byContradiction fun hx_not => h_all ⟨x, hx_Z, hx_not⟩
        · exact fun hx => hEven_sub_Z x hx
      -- Z' = Z \ {z} is cofinite: complement ⊆ (ω\Z) ∪ {z} which is finite
      have hz_w : z ∈ (ω : U) := hZ_sub_w z hz_Z
      have hZ'_cofin : isCofinite (ω : U) (Difference Z {z}) := by
        show isFiniteSet (Difference (ω : U) (Difference Z {z}))
        apply finite_subset (finite_union hZ_cofin (singleton_is_finite z))
        intro w hw
        rw [Difference_is_specified] at hw
        rw [BinUnion_is_specified]
        by_cases hwz : w = z
        · right; exact (Singleton_is_specified z w).mpr hwz
        · left; rw [Difference_is_specified]
          exact ⟨hw.1, fun hwZ => hw.2 ((Difference_is_specified Z {z} w).mpr
            ⟨hwZ, fun h => hwz ((Singleton_is_specified z w).mp h)⟩)⟩
      -- Z' ∈ FinCofAlg(ω)
      have hZ'_mem : Difference Z {z} ∈ FinCofAlg (ω : U) := by
        rw [FinCofAlg_is_specified]
        exact ⟨(PowerSet_is_specified ω (Difference Z {z})).mpr
          (fun w hw => hZ_sub_w w ((Difference_is_specified Z {z} w).mp hw).1),
          Or.inr hZ'_cofin⟩
      -- Z' is an upper bound of Singletons (z ∉ EvenSet so removing z doesn't remove any singleton)
      have hZ'_ub : ∀ Y, Y ∈ Singletons → Y ⊆ Difference Z {z} := by
        intro Y hY
        obtain ⟨_, x, hx_Even, hY_eq⟩ := (SpecSet_is_specified _ Y _).mp hY
        rw [hY_eq]; intro w hw
        rw [(Singleton_is_specified x w).mp hw, Difference_is_specified]
        exact ⟨hEven_sub_Z x hx_Even, fun h =>
          hz_not_Even (((Singleton_is_specified z x).mp h) ▸ hx_Even)⟩
      -- Z ⊆ Z' (since Z is least upper bound and Z' is upper bound)
      have hZ_sub_Z' := hZ_lub (Difference Z {z}) hZ'_mem hZ'_ub
      -- But z ∈ Z and z ∉ Z', contradiction
      exact ((Difference_is_specified Z {z} z).mp (hZ_sub_Z' z hz_Z)).2
        ((Singleton_is_specified z z).mpr rfl)

  end BoolAlg.FiniteCofinite

  -- Export key definitions and theorems
  export BoolAlg.FiniteCofinite (
    -- Finite set closure
    finite_subset finite_union Omega_not_finite
    -- Parity
    double_injective
    EvenSet EvenSet_is_specified EvenSet_subset_Omega
    even_or_odd even_ne_odd
    EvenSet_infinite OddSet_infinite
    -- Definitions
    isCofinite isFinCof FinCofAlg FinCofAlg_is_specified
    FinCofAlg_subset_PowerSet
    -- Boolean algebra closure
    FinCofAlg_empty FinCofAlg_universe
    FinCofAlg_complement FinCofAlg_union FinCofAlg_inter
    -- Not complete
    EvenSet_not_in_FinCofAlg
    FinCofAlg_not_complete
  )

end ZFC
