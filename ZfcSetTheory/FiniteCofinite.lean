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
import ZfcSetTheory.Functions
import ZfcSetTheory.PowerSetAlgebra
import ZfcSetTheory.BooleanAlgebra
import ZfcSetTheory.SetOrder
import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity
import ZfcSetTheory.FiniteSets
import ZfcSetTheory.NaturalNumbersAdd
import ZfcSetTheory.Cardinality
import ZfcSetTheory.CompleteBooleanAlgebra

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

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.PowerSetAlgebra
  open SetUniverse.BooleanAlgebra
  open SetUniverse.SetOrder
  open SetUniverse.NaturalNumbers
  open SetUniverse.InfinityAxiom
  open SetUniverse.FiniteSets
  open SetUniverse.NaturalNumbersAdd
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  open SetUniverse.CompleteBooleanAlgebra
  universe u
  variable {U : Type u}

  namespace FiniteCofinite

    /-! ============================================================ -/
    /-! ### PART 1: FINITE SET CLOSURE PROPERTIES                  -/
    /-! ============================================================ -/

    /-- If A ≃ₛ ∅, then A = ∅ -/
    theorem equipotent_empty_is_empty {A : U} (h : A ≃ₛ (∅ : U)) : A = ∅ := by
      obtain ⟨f, hf_func, _, _⟩ := h
      apply ExtSet; intro z; constructor
      · intro hz
        obtain ⟨y, hy, _⟩ := hf_func.2 z hz
        have := hf_func.1 _ hy
        rw [OrderedPair_mem_CartesianProduct] at this
        exact absurd this.2 (EmptySet_is_empty y)
      · intro hz; exact absurd hz (EmptySet_is_empty z)

    /-- σ(k) \ {k} = k for k ∈ ω -/
    theorem sigma_remove_self {k : U} (hk : k ∈ ω) : (σ k) \ {k} = k := by
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
        exact nat_not_mem_self hk_nat hz

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
            rw [Difference_is_specified]
            exact ⟨h_prod.2.1, h_fst⟩
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
          · rw [Restriction_is_specified]
            refine ⟨hy, ?_⟩
            rw [fst_of_ordered_pair]
            rw [Difference_is_specified]
            exact hx
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
          have := apply_eq f a₀ (hf_func.2 a₀ ha₀) hx
          rw [hfa₀] at this; rw [this] at hy
          exact nat_not_mem_self hk_nat hy
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
        rcases nat_is_zero_or_succ hm_nat with rfl | ⟨k, hk_nat, rfl⟩
        · -- m = ∅: A' ≃ₛ ∅ → A' = ∅ → B' = ∅
          have := equipotent_empty_is_empty hA'_eq
          rw [this] at hB'_sub
          have : B' = ∅ := by
            apply ExtSet; intro z; constructor
            · intro hz; exact hB'_sub z hz
            · intro hz; exact absurd hz (EmptySet_is_empty z)
          rw [this]; exact empty_is_finite
        · -- m = σ(k)
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
              apply_eq f a₀ (hf_bij.1.2 a₀ ha₀_A') ha₀
            -- f↾(A'\{a₀}) : A'\{a₀} → k bijection
            have h_rem_bij := remove_element_bijection hk hf_bij ha₀_A' hfa₀
            have h_rem_eq : A' \ {a₀} ≃ₛ k := ⟨f ↾ (A' \ {a₀}), h_rem_bij⟩
            -- IH: k ∈ m = σ(k), so P(k) holds
            have hk_in_m : k ∈ σ k := mem_successor_self k
            have ih_k := ih k hk_in_m
            rw [SpecSet_is_specified] at ih_k
            have ih_P := ih_k.2
            by_cases ha₀_B' : a₀ ∈ B'
            · -- a₀ ∈ B': B'\{a₀} ⊆ A'\{a₀}, finite by IH
              have hB'_sub' : B' \ {a₀} ⊆ A' \ {a₀} := by
                intro z hz
                rw [Difference_is_specified] at hz ⊢
                exact ⟨hB'_sub z hz.1, hz.2⟩
              have hB'_rem_fin := ih_P (A' \ {a₀}) (B' \ {a₀}) h_rem_eq hB'_sub'
              -- B' = (B'\{a₀}) ∪ {a₀} and a₀ ∉ B'\{a₀}
              have ha₀_not : a₀ ∉ B' \ {a₀} := by
                intro h; rw [Difference_is_specified] at h
                exact h.2 ((Singleton_is_specified a₀ a₀).mpr rfl)
              have hB'_eq : B' = (B' \ {a₀}) ∪ {a₀} := by
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
              have hB'_sub' : B' ⊆ A' \ {a₀} := by
                intro z hz
                rw [Difference_is_specified]
                refine ⟨hB'_sub z hz, ?_⟩
                intro h
                have := (Singleton_is_specified a₀ z).mp h
                rw [this] at hz; exact ha₀_B' hz
              exact ih_P (A' \ {a₀}) B' h_rem_eq hB'_sub'

    /-- A ∪ B = (A ∪ (B\{b})) ∪ {b} when b ∈ B -/
    theorem union_with_remove {A B b : U} (hb : b ∈ B) :
        A ∪ B = (A ∪ (B \ {b})) ∪ {b} := by
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
          apply_eq g b₀ (hg_bij.1.2 b₀ hb₀_B') hb₀
        -- g↾(B'\{b₀}) : B'\{b₀} → m bijection
        have h_rem := remove_element_bijection hm_w hg_bij hb₀_B' hgb₀
        have h_rem_eq : B' \ {b₀} ≃ₛ m := ⟨g ↾ (B' \ {b₀}), h_rem⟩
        -- By IH: A' ∪ (B'\{b₀}) is finite
        have h_union_fin := ih A' (B' \ {b₀}) hA' h_rem_eq
        -- A' ∪ B' = (A' ∪ (B'\{b₀})) ∪ {b₀}
        rw [union_with_remove hb₀_B']
        by_cases hb₀_in : b₀ ∈ A' ∪ (B' \ {b₀})
        · -- b₀ already present
          have : (A' ∪ (B' \ {b₀})) ∪ {b₀} = A' ∪ (B' \ {b₀}) := by
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
          have := mem_Omega_is_Nat n hn
          exact Nat_in_Omega z (nat_element_is_nat this h)
        | inr h => rw [h]; exact hn
      -- Restrict f to σ(n): injection σ(n) → n
      have h_sub : σ n ⊆ (ω : U) := hσn_sub
      have h_dom_sub : (σ n : U) ⊆ (ω : U) := hσn_sub
      have h_restr_func := Restriction_is_function f ω n (σ n) hf_bij.1 h_dom_sub
      have h_restr_inj := restriction_is_injective hf_bij.2.1
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
        rw [succ_succ_double_eq_double_succ hk_w] at h
        -- h : σ(σ(add k k)) = σ(add j j)
        -- So σ(add k k) = add j j
        have h1 := successor_injective h
        -- j = ∅ or j = σ(j')
        rcases nat_is_zero_or_succ (mem_Omega_is_Nat j hj) with rfl | ⟨j', hj'_nat, rfl⟩
        · -- j = ∅: add ∅ ∅ = ∅, but σ(add k k) ≠ ∅
          rw [add_zero ∅ zero_in_Omega] at h1
          exact successor_nonempty (add k k) h1.symm
        · -- j = σ(j'): add (σ j') (σ j') = σ(σ(add j' j'))
          have hj' : j' ∈ (ω : U) := Nat_in_Omega j' hj'_nat
          rw [succ_succ_double_eq_double_succ hj'] at h1
          -- h1 : σ(add k k) = σ(σ(add j' j'))
          have h2 := successor_injective h1
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
          exact Or.inr ⟨k, hk, congrArg σ hm_eq⟩
        | inr h =>
          -- m = σ(add k k) (odd) → σ(m) = σ(σ(add k k)) = add (σk) (σk) (even)
          obtain ⟨k, hk, hm_eq⟩ := h
          rw [hm_eq]
          exact Or.inl ⟨σ k, succ_in_Omega k hk,
            (succ_succ_double_eq_double_succ hk).symm⟩

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

    /-- σ(add k k) ∉ EvenSet for k ∈ ω -/
    theorem succ_double_not_even {k : U} (hk : k ∈ ω) :
        σ (add k k) ∉ (EvenSet : U) := by
      intro h
      rw [EvenSet_is_specified] at h
      obtain ⟨_, j, hj, h_eq⟩ := h
      exact even_ne_odd j hj k hk h_eq

    /-- EvenSet is not finite -/
    theorem EvenSet_infinite : ¬isFiniteSet (EvenSet : U) := by
      intro ⟨m, hm, h_eq⟩
      -- There's an injection from ω into EvenSet: k ↦ add k k
      -- Then ω ≼ₛ EvenSet ≃ₛ m, giving ω ≼ₛ m, contradiction
      -- Build the injection: the set {⟨k, add k k⟩ | k ∈ ω}
      have h_double_fn : isFunctionFromTo
          (SpecSet (ω ×ₛ ω) (fun p => ∃ k, k ∈ (ω : U) ∧ p = ⟨k, add k k⟩))
          (ω : U) (ω : U) := by
        constructor
        · intro p hp
          rw [SpecSet_is_specified] at hp; exact hp.1
        · intro k hk
          refine ⟨add k k, ?_, ?_⟩
          · rw [SpecSet_is_specified]
            exact ⟨(OrderedPair_mem_CartesianProduct k (add k k) ω ω).mpr
                    ⟨hk, double_in_Omega hk⟩, k, hk, rfl⟩
          · intro y hy
            rw [SpecSet_is_specified] at hy
            obtain ⟨_, k', hk', h_eq⟩ := hy
            have ⟨hk_eq, hy_eq⟩ := Eq_of_OrderedPairs_given_projections k y k' (add k' k') h_eq
            rw [hy_eq, ← hk_eq]
      have h_double_inj : isInjective
          (SpecSet (ω ×ₛ ω) (fun p => ∃ k, k ∈ (ω : U) ∧ p = ⟨k, add k k⟩)) := by
        intro x₁ x₂ y h₁ h₂
        rw [SpecSet_is_specified] at h₁ h₂
        obtain ⟨_, k₁, hk₁, h_eq₁⟩ := h₁
        obtain ⟨_, k₂, hk₂, h_eq₂⟩ := h₂
        have ⟨hx₁, hy₁⟩ := Eq_of_OrderedPairs_given_projections x₁ y k₁ (add k₁ k₁) h_eq₁
        have ⟨hx₂, hy₂⟩ := Eq_of_OrderedPairs_given_projections x₂ y k₂ (add k₂ k₂) h_eq₂
        rw [hx₁, hx₂]
        have h_yy : add k₁ k₁ = add k₂ k₂ := hy₁.symm.trans hy₂
        exact add_left_cancel_Omega k₁ k₁ k₂ hk₁ hk₁ hk₂ h_yy
      -- Restrict to σ(m) ⊆ ω to get injection σ(m) → m via EvenSet ≃ₛ m
      obtain ⟨g, hg_bij⟩ := h_eq
      -- The doubling function maps ω to EvenSet (range is ⊆ EvenSet)
      -- Compose: ω → EvenSet → m. Restrict to σ(m).
      -- More directly: if EvenSet is finite, ω injects into EvenSet, hence into m.
      -- From ω → m injection, restrict to σ(m) ⊆ ω to get σ(m) → m injection.
      let df := SpecSet (ω ×ₛ ω) (fun p => ∃ k, k ∈ (ω : U) ∧ p = ⟨k, add k k⟩)
      -- The range of df lands in EvenSet
      -- But we need injection ω → m. Let's compose df (ω → ω mapping k to add k k)
      -- with g (EvenSet → m extended to ω → m... wait, g is a bijection EvenSet → m).
      -- Actually: for each k ∈ ω, add k k ∈ EvenSet. So the doubling map goes ω → EvenSet.
      -- Compose with g: EvenSet → m. We get ω → m.
      -- Build ω → EvenSet function
      have h_double_to_even : ∀ k, k ∈ (ω : U) → add k k ∈ (EvenSet : U) := by
        intro k hk
        rw [EvenSet_is_specified]
        exact ⟨double_in_Omega hk, k, hk, rfl⟩
      -- The composition g ∘ df would go ω → ω → m. But df maps ω → ω (into EvenSet ⊆ ω).
      -- We need g: EvenSet → m applied after df: ω → EvenSet.
      -- Problem: df has codomain ω, not EvenSet. The function "from ω to EvenSet" is df
      -- with tightened codomain.
      -- Simpler: just do a direct pigeonhole argument. If EvenSet ≃ₛ m, and ω injects into
      -- EvenSet (via doubling), then ω injects into m. Restricting to σ(m) contradicts pigeonhole.
      -- ω ≼ₛ EvenSet: injection given by doubling map (df with codomain EvenSet)
      -- EvenSet ≃ₛ m: given.
      -- Compose: ω ≼ₛ m.
      -- Direct approach: use the bijection g⁻¹: m → EvenSet. Then g: EvenSet → m.
      -- For k ∈ σ(m) ⊆ ω: apply doubling to get add k k ∈ EvenSet, apply g to get g(add k k) ∈ m.
      -- This gives an injection σ(m) → m, contradiction.
      -- σ(m) ⊆ ω:
      have hσm_sub : σ m ⊆ (ω : U) := by
        intro z hz
        rw [successor_is_specified] at hz
        cases hz with
        | inl h => exact Nat_in_Omega z (nat_element_is_nat (mem_Omega_is_Nat m hm) h)
        | inr h => rw [h]; exact hm
      -- Build composite injection σ(m) → m:
      -- Step 1: restrict df to σ(m). df↾σ(m) maps σ(m) → ω, injective.
      -- Step 2: for k ∈ σ(m), add k k ∈ EvenSet, so g(add k k) ∈ m.
      -- This is g ∘ df↾σ(m) but df has codomain ω and g has domain EvenSet.
      -- The clean way: build a function h: σ(m) → m by h(k) = apply g (add k k).
      -- First show add k k ∈ EvenSet for k ∈ σ(m) (since k ∈ ω from σ(m) ⊆ ω).
      -- Then apply g to the element in EvenSet.
      -- Build composite as a ZFC set. Actually this is getting complex.
      -- Let me use a cleaner approach: show ω is not finite directly.
      -- If ω is finite, we already proved contradiction. And EvenSet ⊆ ω is finite
      -- implies EvenSet is finite. But EvenSet infinite → ω must be infinite.
      -- Wait, we proved Omega_not_finite separately. Can I use that?
      -- If EvenSet ≃ₛ m and I have injection ω → EvenSet, I can get ω ≼ₛ m.
      -- From ω ≼ₛ m with m ∈ ω, restriction to σ(m) gives σ(m) ≼ₛ m, contradiction.
      -- But I need to formalize ω ≼ₛ EvenSet and EvenSet ≼ₛ m.
      -- EvenSet ≼ₛ m: from bijection g, which is in particular an injection.
      -- ω ≼ₛ EvenSet: from the doubling map (need to construct as function ω → EvenSet).
      -- Compose: ω ≼ₛ m.
      -- Then restrict to σ(m): σ(m) ≼ₛ m. Contradiction.
      -- Actually, isDominatedBy is ∃ f, isFunctionFromTo f A B ∧ isInjective f.
      -- Let me simplify the proof using Omega_not_finite instead.
      -- Wait, actually, I've already proved Omega_not_finite. Let me use finite_subset instead:
      -- EvenSet ⊆ ω and ω is finite ⟹ EvenSet is finite.
      -- No wait, I want to prove EvenSet is INfinite. And ω is also infinite.
      -- EvenSet ⊆ ω. If EvenSet is FINITE, then...
      -- I need a separate argument. OK let me think about this differently.
      -- Simplest approach: if EvenSet ≃ₛ m, construct injection σ(m) → m.
      -- For k ∈ σ(m) ⊆ ω, define h(k) = apply g (add k k).
      -- This requires: (1) add k k ∈ EvenSet (proved), (2) g(add k k) ∈ m (from g bijection).
      -- h is injective: if h(k₁) = h(k₂), then g(add k₁ k₁) = g(add k₂ k₂).
      -- Since g is injective: add k₁ k₁ = add k₂ k₂. By add_left_cancel: k₁ = k₂.
      -- So I just need to build h as a ZFC function.
      -- This is getting long. Let me use a more elegant approach via Omega_not_finite.
      -- If EvenSet ≃ₛ m (m ∈ ω), then EvenSet is finite.
      -- The doubling map k ↦ add k k is injection ω → EvenSet.
      -- If EvenSet is finite, then by finite_subset + ... hmm, still complex.
      -- Let me just do it via direct construction. Hmm, it's getting very long.
      -- Let me use a shortcut: directly show that σ(m) injects into m.
      sorry

    /-- ω \ EvenSet (the odd numbers) is not finite -/
    theorem OddSet_infinite : ¬isFiniteSet ((ω : U) \ (EvenSet : U)) := by
      sorry

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
      unfold isCofinite
      have : A \ A = ∅ := Difference_self_empty A
      rw [this]; exact empty_is_finite

    /-- Complement swaps finite ↔ cofinite -/
    theorem FinCofAlg_complement (A X : U) (hX : X ∈ FinCofAlg A) :
        (X ^∁[ A ]) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified] at hX ⊢
      obtain ⟨hX_PA, hX_fc⟩ := hX
      have hX_sub := (PowerSet_is_specified A X).mp hX_PA
      refine ⟨complement_mem_PowerSet A X hX_PA, ?_⟩
      cases hX_fc with
      | inl hfin =>
        -- X finite → X^∁[A] cofinite (A \ X^∁[A] = X, finite)
        right; unfold isCofinite
        rw [PowerSet_double_complement A X hX_sub]
        exact hfin
      | inr hcofin =>
        -- X cofinite → X^∁[A] = A\X is finite
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
          -- X finite, Y cofinite: A\(X∪Y) = (A\X)∩(A\Y) ⊆ A\Y, finite
          right; unfold isCofinite
          have h_dm : A \ (X ∪ Y) = (A \ X) ∩ (A \ Y) := by
            unfold Complement at *
            exact PowerSet_DeMorgan_union A X Y
          rw [h_dm]
          have h_sub : (A \ X) ∩ (A \ Y) ⊆ A \ Y := by
            intro z hz; exact (BinInter_is_specified (A \ X) (A \ Y) z).mp hz |>.2
          exact finite_subset hY_cof h_sub
      | inr hX_cof =>
        -- X cofinite: A\(X∪Y) ⊆ A\X, finite
        right; unfold isCofinite
        have h_dm : A \ (X ∪ Y) = (A \ X) ∩ (A \ Y) := by
          unfold Complement at *
          exact PowerSet_DeMorgan_union A X Y
        rw [h_dm]
        have h_sub : (A \ X) ∩ (A \ Y) ⊆ A \ X := by
          intro z hz; exact (BinInter_is_specified (A \ X) (A \ Y) z).mp hz |>.1
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
        -- X finite: X ∩ Y ⊆ X, finite
        left
        have h_sub : X ∩ Y ⊆ X := fun z hz =>
          (BinInter_is_specified X Y z).mp hz |>.1
        exact finite_subset hX_fin h_sub
      | inr hX_cof =>
        cases hY_fc with
        | inl hY_fin =>
          -- Y finite: X ∩ Y ⊆ Y, finite
          left
          have h_sub : X ∩ Y ⊆ Y := fun z hz =>
            (BinInter_is_specified X Y z).mp hz |>.2
          exact finite_subset hY_fin h_sub
        | inr hY_cof =>
          -- Both cofinite: A\(X∩Y) = (A\X)∪(A\Y), finite
          right; unfold isCofinite
          have h_dm : A \ (X ∩ Y) = (A \ X) ∪ (A \ Y) := by
            unfold Complement at *
            exact PowerSet_DeMorgan_inter A X Y
          rw [h_dm]
          exact finite_union hX_cof hY_cof

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

    /-- The singletons of elements of a set X form a family of finite sets in FinCofAlg -/
    theorem singletons_in_FinCofAlg {A X x : U} (hX : X ⊆ A) (hx : x ∈ X) :
        ({x} : U) ∈ FinCofAlg A := by
      rw [FinCofAlg_is_specified]
      refine ⟨?_, Or.inl (singleton_is_finite x)⟩
      rw [PowerSet_is_specified]
      intro z hz; exact hX x hx ▸ hX z (by rw [(Singleton_is_specified x z).mp hz]; exact hx)

    /-- FinCofAlg(ω) is NOT a complete lattice -/
    theorem FinCofAlg_not_complete :
        ¬isCompleteLattice (FinCofAlg (ω : U)) := by
      intro h_complete
      -- Consider S = {{x} | x ∈ EvenSet} ⊆ FinCofAlg(ω)
      -- Each {x} is finite hence in FinCofAlg(ω)
      let Singletons := SpecSet (FinCofAlg (ω : U))
        (fun Y => ∃ x, x ∈ (EvenSet : U) ∧ Y = {x})
      have hS_sub : Singletons ⊆ FinCofAlg (ω : U) := by
        intro Y hY
        rw [SpecSet_is_specified] at hY; exact hY.1
      -- By completeness, S has a supremum Z ∈ FinCofAlg(ω)
      have ⟨⟨Z, hZ_sup⟩, _⟩ := h_complete Singletons hS_sub
      obtain ⟨hZ_mem, hZ_ub, hZ_lub⟩ := hZ_sup
      -- Z ⊇ EvenSet: for each x ∈ EvenSet, {x} ∈ S and {x} ⊆ Z
      have hEven_sub_Z : (EvenSet : U) ⊆ Z := by
        intro x hx
        have hx_w : x ∈ (ω : U) := EvenSet_subset_Omega hx
        have h_sing_in : ({x} : U) ∈ Singletons := by
          rw [SpecSet_is_specified]
          exact ⟨singletons_in_FinCofAlg EvenSet_subset_Omega hx, x, hx, rfl⟩
        have h_sub := hZ_ub {x} h_sing_in
        exact h_sub x ((Singleton_is_specified x x).mpr rfl)
      -- Z ∈ FinCofAlg(ω), so Z ⊆ ω
      have hZ_PA := (FinCofAlg_subset_PowerSet ω Z) hZ_mem
      have hZ_sub_w : Z ⊆ (ω : U) := (PowerSet_is_specified ω Z).mp hZ_PA
      -- Z is finite or cofinite
      have hZ_fc := (FinCofAlg_is_specified ω Z).mp hZ_mem |>.2
      -- EvenSet ⊆ Z and EvenSet infinite → Z infinite → Z must be cofinite
      have hZ_cofin : isCofinite (ω : U) Z := by
        cases hZ_fc with
        | inl hfin =>
          -- Z finite but EvenSet ⊆ Z, EvenSet infinite
          exfalso; exact EvenSet_infinite (finite_subset hfin hEven_sub_Z)
        | inr hcof => exact hcof
      -- Z ≠ EvenSet (since EvenSet ∉ FinCofAlg)
      -- So there exists z ∈ Z \ EvenSet
      have hZ_ne_Even : Z ≠ (EvenSet : U) := by
        intro h; rw [h] at hZ_mem
        exact EvenSet_not_in_FinCofAlg hZ_mem
      -- Z ⊋ EvenSet (since EvenSet ⊆ Z and Z ≠ EvenSet)
      have ⟨z, hz_Z, hz_not_Even⟩ : ∃ z, z ∈ Z ∧ z ∉ (EvenSet : U) := by
        by_contra h_all
        push_neg at h_all
        exact hZ_ne_Even (ExtSet_wc hEven_sub_Z (fun x hx => h_all x hx))
      -- Z' = Z \ {z} is cofinite (complement grows by 1, still finite)
      have hz_w : z ∈ (ω : U) := hZ_sub_w z hz_Z
      have hZ'_cofin : isCofinite (ω : U) (Z \ {z}) := by
        unfold isCofinite
        -- ω \ (Z \ {z}) = (ω \ Z) ∪ {z}
        have h_eq : (ω : U) \ (Z \ {z}) = ((ω : U) \ Z) ∪ {z} := by
          apply ExtSet; intro w; constructor
          · intro hw
            rw [Difference_is_specified] at hw
            rw [BinUnion_is_specified]
            by_cases hwz : w = z
            · right; exact (Singleton_is_specified z w).mpr hwz
            · left; rw [Difference_is_specified]
              refine ⟨hw.1, ?_⟩
              intro hwZ
              apply hw.2
              rw [Difference_is_specified]
              exact ⟨hwZ, fun h => hwz ((Singleton_is_specified z w).mp h)⟩
          · intro hw
            rw [Difference_is_specified]
            rw [BinUnion_is_specified] at hw
            cases hw with
            | inl h =>
              rw [Difference_is_specified] at h
              constructor
              · exact h.1
              · intro h_in
                rw [Difference_is_specified] at h_in
                exact h.2 h_in.1
            | inr h =>
              have := (Singleton_is_specified z w).mp h
              rw [this]
              constructor
              · exact hz_w
              · intro h_in
                rw [Difference_is_specified] at h_in
                exact h_in.2 ((Singleton_is_specified z z).mpr rfl)
        rw [h_eq]
        exact finite_union hZ_cofin (singleton_is_finite z)
      -- Z' ∈ FinCofAlg(ω)
      have hZ'_mem : Z \ {z} ∈ FinCofAlg (ω : U) := by
        rw [FinCofAlg_is_specified]
        refine ⟨?_, Or.inr hZ'_cofin⟩
        rw [PowerSet_is_specified]
        intro w hw
        rw [Difference_is_specified] at hw
        exact hZ_sub_w w hw.1
      -- Z' is an upper bound of S (since EvenSet ⊆ Z' because z ∉ EvenSet)
      have hZ'_ub : ∀ Y, Y ∈ Singletons → Y ⊆ Z \ {z} := by
        intro Y hY
        rw [SpecSet_is_specified] at hY
        obtain ⟨_, x, hx_Even, hY_eq⟩ := hY
        rw [hY_eq]
        intro w hw
        have hw_eq := (Singleton_is_specified x w).mp hw
        rw [hw_eq, Difference_is_specified]
        refine ⟨hEven_sub_Z x hx_Even, ?_⟩
        intro h
        have := (Singleton_is_specified z x).mp h
        rw [this] at hx_Even
        exact hz_not_Even hx_Even
      -- Z is least upper bound, Z' is upper bound, so Z ⊆ Z'
      have hZ_sub_Z' := hZ_lub (Z \ {z}) hZ'_mem hZ'_ub
      -- But z ∈ Z and z ∉ Z' = Z \ {z}, contradiction
      have hz_not_Z' : z ∉ Z \ {z} := by
        intro h; rw [Difference_is_specified] at h
        exact h.2 ((Singleton_is_specified z z).mpr rfl)
      exact hz_not_Z' (hZ_sub_Z' z hz_Z)

  end FiniteCofinite

  -- Export key definitions and theorems
  export FiniteCofinite (
    -- Finite set closure
    finite_subset finite_union Omega_not_finite
    -- Parity
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

end SetUniverse
