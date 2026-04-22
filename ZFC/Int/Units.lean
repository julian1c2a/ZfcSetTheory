/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Units

  This module characterizes the units (invertible elements) of ℤ.
  It is separated from Ring.lean to avoid importing PeanoNatLib.PeanoNatPrimes
  into files that use set-membership notation (∈), since that library defines
  a conflicting DList.Mem notation at the same precedence level.

  ## Main Definitions and Theorems

  * `isUnitZ` — definition of units in ℤ
  * `unitZ_iff` — the only units are ±1
-/

import ZFC.Int.Ring
import PeanoNatLib.PeanoNatPrimes

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Nat.Add
  open ZFC.Nat.Mul
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul

  universe u
  variable {U : Type u}

  namespace Int.Ring

    /-- Every integer is represented as intClass a b for some a b ∈ ω -/
    private theorem intClass_exists (z : U) (hz : z ∈ (IntSet : U)) :
        ∃ a b : U, (a ∈ (ω : U)) ∧ (b ∈ (ω : U)) ∧ (z = (intClass a b)) := by
      unfold IntSet at hz
      rw [mem_QuotientSet] at hz
      obtain ⟨p, hp_mem, hz_eq⟩ := hz
      rw [CartesianProduct_is_specified] at hp_mem
      obtain ⟨⟨a, b, hp_eq⟩, hp_fst, hp_snd⟩ := hp_mem
      subst hp_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hp_fst hp_snd
      exact ⟨a, b, hp_fst, hp_snd, hz_eq⟩

    /-! ### Units — auxiliary lemmas -/

    /-- In ω, n ≠ σ n -/
    private theorem ne_succ_self (n : U) (hn : n ∈ (ω : U)) : n ≠ σ n := by
      intro h
      have h1 := add_succ n ∅ hn zero_in_Omega
      rw [add_zero n hn] at h1
      -- h1 : add n (σ ∅) = σ n
      rw [← h1] at h
      conv at h => lhs; rw [← add_zero n hn]
      -- h : add n ∅ = add n (σ ∅)
      exact succ_nonempty ∅
        (add_left_cancel_Omega n ∅ (σ ∅) hn zero_in_Omega
          (succ_in_Omega ∅ zero_in_Omega) h).symm

    /-- In ω, n ≠ σ(add n m) for any m -/
    private theorem ne_succ_add (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        n ≠ σ (add n m) := by
      intro h
      have h1 := add_succ n m hn hm
      -- h1 : add n (σ m) = σ (add n m)
      rw [← h1] at h
      conv at h => lhs; rw [← add_zero n hn]
      -- h : add n ∅ = add n (σ m)
      exact succ_nonempty m
        (add_left_cancel_Omega n ∅ (σ m) hn zero_in_Omega
          (succ_in_Omega m hm) h).symm

    /-- In ω, mul a b = σ ∅ implies a = σ ∅ and b = σ ∅, lifted from Peano -/
    private theorem mul_eq_one_Omega (a b : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (h : mul a b = σ (∅ : U)) : a = σ (∅ : U) ∧ b = σ (∅ : U) := by
      obtain ⟨p, rfl⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, rfl⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      rw [← fromPeano_mul p q] at h
      have h_one : (σ (∅ : U)) = (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero) : U) := by
        simp only [fromPeano]
      rw [h_one] at h
      obtain ⟨hp, hq⟩ := Peano.Primes.mul_eq_one (fromPeano_injective h)
      exact ⟨by rw [hp]; exact h_one.symm, by rw [hq]; exact h_one.symm⟩

    /-! ### Units -/

    /-- A unit in ℤ is an element with a multiplicative inverse -/
    def isUnitZ (u : U) : Prop :=
      (u ∈ (IntSet : U)) ∧ (∃ v : U, (v ∈ (IntSet : U)) ∧ (mulZ u v = (oneZ : U)))

    /-- The only units in ℤ are ±1 -/
    theorem unitZ_iff (u : U) (hu : u ∈ (IntSet : U)) :
        isUnitZ u ↔ u = (oneZ : U) ∨ u = negZ (oneZ : U) := by
      constructor
      · -- Forward: isUnitZ u → u = oneZ ∨ u = negZ oneZ
        intro ⟨_, v, hv, h_uv⟩
        obtain ⟨a, b, ha, hb, hu_eq⟩ := intClass_exists u hu
        obtain ⟨c, d, hc, hd, hv_eq⟩ := intClass_exists v hv
        subst hu_eq; subst hv_eq
        rw [mulZ_class a b c d ha hb hc hd] at h_uv
        unfold oneZ at h_uv ⊢
        -- Abbreviations
        have hac := mul_in_Omega a c ha hc
        have hbd := mul_in_Omega b d hb hd
        have had := mul_in_Omega a d ha hd
        have hbc := mul_in_Omega b c hb hc
        have hacbd := add_in_Omega _ _ hac hbd
        have hadbc := add_in_Omega _ _ had hbc
        -- Convert h_uv to: ac + bd = σ(ad + bc)
        rw [intClass_eq_iff _ _ (σ (∅ : U)) (∅ : U) hacbd hadbc
            (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega,
            add_zero _ hacbd,
            add_succ _ _ hadbc zero_in_Omega,
            add_zero _ hadbc] at h_uv
        -- h_uv : add (mul a c) (mul b d) = σ (add (mul a d) (mul b c))
        -- Trichotomy on a, b
        rcases trichotomy a b (mem_Omega_is_Nat a ha) (mem_Omega_is_Nat b hb) with
            ha_lt_b | hab_eq | hb_lt_a
        · -- CASE a ∈ b: leads to u = negZ oneZ
          obtain ⟨k, hk, hb_eq⟩ := le_then_exists_add_Omega a b ha hb (Or.inl ha_lt_b)
          -- hb_eq : b = add a k. Substitute in h_uv and goal.
          rw [hb_eq] at h_uv ⊢
          rw [mul_rdistr_Omega a k d ha hk hd,
              mul_rdistr_Omega a k c ha hk hc] at h_uv
          have hkd := mul_in_Omega k d hk hd
          have hkc := mul_in_Omega k c hk hc
          -- h_uv : ac + (ad + kd) = σ(ad + (ac + kc))
          -- Rearrange LHS to: (ac + ad) + kd
          rw [add_assoc_Omega (mul a c) (mul a d) (mul k d) hac had hkd] at h_uv
          -- Rearrange σ-arg to: (ac + ad) + kc
          rw [add_comm_Omega (mul a d) (add (mul a c) (mul k c)) had
              (add_in_Omega _ _ hac hkc),
              ← add_assoc_Omega (mul a c) (mul k c) (mul a d) hac hkc had,
              add_comm_Omega (mul k c) (mul a d) hkc had,
              add_assoc_Omega (mul a c) (mul a d) (mul k c) hac had hkc] at h_uv
          -- h_uv : (ac + ad) + kd = σ((ac + ad) + kc)
          -- Rewrite σ((ac+ad) + kc) as (ac+ad) + σ(kc)
          have hacad := add_in_Omega _ _ hac had
          rw [← add_succ (add (mul a c) (mul a d)) (mul k c) hacad hkc] at h_uv
          -- Cancel ac + ad
          have h_kd_eq := add_left_cancel_Omega _ _ _
            hacad hkd (succ_in_Omega _ hkc) h_uv
          -- h_kd_eq : mul k d = σ(mul k c)
          -- Trichotomy on c, d
          rcases trichotomy c d (mem_Omega_is_Nat c hc) (mem_Omega_is_Nat d hd) with
              hc_lt_d | hcd_eq | hd_lt_c
          · -- c ∈ d: d = add c j → kd = kc + kj = σ(kc) → kj = σ ∅ → k=j=σ ∅
            obtain ⟨j, hj, hd_eq⟩ := le_then_exists_add_Omega c d hc hd (Or.inl hc_lt_d)
            rw [hd_eq, mul_ldistr_Omega k c j hk hc hj] at h_kd_eq
            -- h_kd_eq : kc + kj = σ(kc)
            have hkj := mul_in_Omega k j hk hj
            have h_succ_eq : σ (mul k c) = add (mul k c) (σ (∅ : U)) := by
              rw [add_succ (mul k c) ∅ hkc zero_in_Omega, add_zero (mul k c) hkc]
            rw [h_succ_eq] at h_kd_eq
            have h_kj_eq := add_left_cancel_Omega _ _ _
              hkc hkj (succ_in_Omega (∅ : U) zero_in_Omega) h_kd_eq
            -- h_kj_eq : mul k j = σ ∅
            obtain ⟨hk_one, hj_one⟩ := mul_eq_one_Omega k j hk hj h_kj_eq
            -- b = add a k = add a (σ ∅) = σ a, d = add c j = σ c
            right
            rw [hk_one]
            -- Goal: intClass a (add a (σ ∅)) = negZ (intClass (σ ∅) ∅)
            rw [negZ_class (σ (∅ : U)) (∅ : U) (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega]
            -- Goal: intClass a (add a (σ ∅)) = intClass ∅ (σ ∅)
            rw [intClass_eq_iff a (add a (σ ∅)) ∅ (σ ∅)
                ha (add_in_Omega a (σ ∅) ha (succ_in_Omega ∅ zero_in_Omega))
                zero_in_Omega (succ_in_Omega ∅ zero_in_Omega)]
            -- Goal: add a (σ ∅) = add (add a (σ ∅)) ∅
            rw [add_zero (add a (σ ∅))
                (add_in_Omega a (σ ∅) ha (succ_in_Omega ∅ zero_in_Omega))]
            -- Goal: add a (σ ∅) = add a (σ ∅)
          · -- c = d: kd = σ(kd) — contradiction
            subst hcd_eq
            exact absurd h_kd_eq (ne_succ_self (mul k c) hkc)
          · -- d ∈ c: kd = σ(k(add d j)) = σ(kd + kj) — contradiction
            obtain ⟨j, hj, hc_eq⟩ := le_then_exists_add_Omega d c hd hc (Or.inl hd_lt_c)
            rw [hc_eq, mul_ldistr_Omega k d j hk hd hj] at h_kd_eq
            exact absurd h_kd_eq
              (ne_succ_add (mul k d) (mul k j) hkd (mul_in_Omega k j hk hj))
        · -- CASE a = b: contradiction (n = σ n)
          subst hab_eq
          rw [add_comm_Omega (mul a d) (mul a c) had hac] at h_uv
          exact absurd h_uv
            (ne_succ_self (add (mul a c) (mul a d)) (add_in_Omega _ _ hac had))
        · -- CASE b ∈ a: leads to u = oneZ
          obtain ⟨k, hk, ha_eq⟩ := le_then_exists_add_Omega b a hb ha (Or.inl hb_lt_a)
          -- ha_eq : a = add b k. Substitute in h_uv and goal.
          rw [ha_eq] at h_uv ⊢
          rw [mul_rdistr_Omega b k c hb hk hc,
              mul_rdistr_Omega b k d hb hk hd] at h_uv
          have hkd := mul_in_Omega k d hk hd
          have hkc := mul_in_Omega k c hk hc
          -- h_uv : (bc + kc) + bd = σ((bd + kd) + bc)
          -- Rearrange LHS to: (bc + bd) + kc
          rw [← add_assoc_Omega (mul b c) (mul k c) (mul b d) hbc hkc hbd,
              add_comm_Omega (mul k c) (mul b d) hkc hbd,
              add_assoc_Omega (mul b c) (mul b d) (mul k c) hbc hbd hkc] at h_uv
          -- Rearrange σ-arg to: (bc + bd) + kd
          rw [← add_assoc_Omega (mul b d) (mul k d) (mul b c) hbd hkd hbc,
              add_comm_Omega (mul k d) (mul b c) hkd hbc,
              add_assoc_Omega (mul b d) (mul b c) (mul k d) hbd hbc hkd,
              add_comm_Omega (mul b d) (mul b c) hbd hbc] at h_uv
          -- h_uv : (bc + bd) + kc = σ((bc + bd) + kd)
          have hbcbd := add_in_Omega _ _ hbc hbd
          rw [← add_succ (add (mul b c) (mul b d)) (mul k d) hbcbd hkd] at h_uv
          -- Cancel bc + bd
          have h_kc_eq := add_left_cancel_Omega _ _ _
            hbcbd hkc (succ_in_Omega _ hkd) h_uv
          -- h_kc_eq : mul k c = σ(mul k d)
          -- Trichotomy on c, d
          rcases trichotomy c d (mem_Omega_is_Nat c hc) (mem_Omega_is_Nat d hd) with
              hc_lt_d | hcd_eq | hd_lt_c
          · -- c ∈ d: kc = σ(k(add c j)) = σ(kc + kj) — contradiction
            obtain ⟨j, hj, hd_eq⟩ := le_then_exists_add_Omega c d hc hd (Or.inl hc_lt_d)
            rw [hd_eq, mul_ldistr_Omega k c j hk hc hj] at h_kc_eq
            exact absurd h_kc_eq
              (ne_succ_add (mul k c) (mul k j) hkc (mul_in_Omega k j hk hj))
          · -- c = d: kc = σ(kc) — contradiction
            subst hcd_eq
            exact absurd h_kc_eq (ne_succ_self (mul k c) hkc)
          · -- d ∈ c: c = add d j → kc = kd + kj = σ(kd) → kj = σ ∅ → k=j=σ ∅
            obtain ⟨j, hj, hc_eq⟩ := le_then_exists_add_Omega d c hd hc (Or.inl hd_lt_c)
            rw [hc_eq, mul_ldistr_Omega k d j hk hd hj] at h_kc_eq
            -- h_kc_eq : kd + kj = σ(kd)
            have hkj := mul_in_Omega k j hk hj
            have h_succ_eq : σ (mul k d) = add (mul k d) (σ (∅ : U)) := by
              rw [add_succ (mul k d) ∅ hkd zero_in_Omega, add_zero (mul k d) hkd]
            rw [h_succ_eq] at h_kc_eq
            have h_kj_eq := add_left_cancel_Omega _ _ _
              hkd hkj (succ_in_Omega (∅ : U) zero_in_Omega) h_kc_eq
            -- h_kj_eq : mul k j = σ ∅
            obtain ⟨hk_one, hj_one⟩ := mul_eq_one_Omega k j hk hj h_kj_eq
            -- a = add b k = add b (σ ∅) = σ b, c = add d j = σ d
            left
            rw [hk_one]
            -- Goal: intClass (add b (σ ∅)) b = intClass (σ ∅) ∅
            rw [intClass_eq_iff (add b (σ (∅ : U))) b (σ (∅ : U)) (∅ : U)
                (add_in_Omega b (σ (∅ : U)) hb (succ_in_Omega (∅ : U) zero_in_Omega))
                hb (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega]
            -- Goal: add (add b (σ ∅)) ∅ = add b (σ ∅)
            rw [add_zero (add b (σ ∅))
                (add_in_Omega b (σ ∅) hb (succ_in_Omega ∅ zero_in_Omega))]
            -- Goal: add b (σ ∅) = add b (σ ∅)
      · -- Backward: u = oneZ ∨ u = negZ oneZ → isUnitZ u
        intro h
        refine ⟨hu, ?_⟩
        cases h with
        | inl h_one =>
          exact ⟨oneZ, oneZ_mem_IntSet, by rw [h_one, mulZ_one_right oneZ oneZ_mem_IntSet]⟩
        | inr h_neg_one =>
          exact ⟨negZ oneZ, negZ_in_IntSet oneZ oneZ_mem_IntSet, by
            rw [h_neg_one, negZ_mulZ_negZ oneZ oneZ oneZ_mem_IntSet oneZ_mem_IntSet,
                mulZ_one_right oneZ oneZ_mem_IntSet]⟩

  end Int.Ring

end ZFC

export ZFC.Int.Ring (
  isUnitZ
  unitZ_iff
)
