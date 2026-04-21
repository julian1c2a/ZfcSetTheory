/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Division: GCD and Divisibility Properties

  This module defines the GCD on ℤ (via absolute values) and proves
  divisibility properties including antisymmetry and the greatest-divisor
  characterisation.

  ## Main Definitions

  * `gcdZ` — GCD on ℤ: `gcdZ a b := gcd (absZ a) (absZ b)`, result in ω
  * `modZ` — Remainder on ℤ: `modZ a b := modOf (absZ a) (absZ b)`, result in ω

  ## Main Theorems

  * `gcdZ_in_omega` — gcdZ a b ∈ ω
  * `gcdZ_comm` — gcdZ a b = gcdZ b a
  * `gcdZ_zero_right` — gcdZ a 0 = absZ a
  * `gcdZ_zero_left` — gcdZ 0 b = absZ b
  * `gcdZ_dividesZ_left` — natToInt (gcdZ a b) | a
  * `gcdZ_dividesZ_right` — natToInt (gcdZ a b) | b
  * `gcdZ_is_greatest` — d | a → d | b → d | natToInt (gcdZ a b)
  * `modZ_in_omega` — modZ a b ∈ ω
  * `quotZ_in_IntSet` — quotZ a b ∈ ℤ
  * `euclidean_divisionZ` — a = addZ (mulZ (quotZ a b) b) (mulZ (signZ a) (natToInt (modZ a b)))
  * `dividesZ_antisymm_abs` — a | b → b | a → absZ a = absZ b
  * `dividesZ_antisymm` — a | b → b | a → a = b ∨ a = negZ b
  * `lcmZ_in_omega` — lcmZ a b ∈ ω
  * `lcmZ_comm` — lcmZ a b = lcmZ b a
-/

import ZFC.Int.Abs
import ZFC.Int.DivMod
import ZFC.Nat.Div
import ZFC.Nat.Gcd

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
  open ZFC.Nat.Sub
  open ZFC.Nat.Div
  open ZFC.Nat.Gcd
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Abs
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Ring
  open ZFC.Int.Order
  open ZFC.Int.Embedding
  open ZFC.Int.Abs
  open ZFC.Int.DivMod

  universe u
  variable {U : Type u}

  namespace Int.Div

    -- =========================================================================
    -- Section 1: gcdZ — GCD on ℤ
    -- =========================================================================

    /-- GCD on ℤ, defined as gcd of absolute values. Result is in ω. -/
    noncomputable def gcdZ (a b : U) : U := gcd (absZ a) (absZ b)

    /-- Remainder on ℤ, defined as modOf of absolute values. Result is in ω. -/
    noncomputable def modZ (a b : U) : U := modOf (absZ a) (absZ b)

    /-- Quotient on ℤ, using the sign rule. Result is in ℤ. -/
    noncomputable def quotZ (a b : U) : U :=
      mulZ (mulZ (signZ a) (signZ b)) (natToInt (divOf (absZ a) (absZ b)))

    /-! ### Closure -/

    /-- gcdZ a b ∈ ω for a, b ∈ ℤ. -/
    theorem gcdZ_in_omega (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        gcdZ a b ∈ (ω : U) := by
      unfold gcdZ
      exact gcd_in_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)

    /-- modZ a b ∈ ω for a, b ∈ ℤ. -/
    theorem modZ_in_omega (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        modZ a b ∈ (ω : U) := by
      unfold modZ
      exact modOf_in_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)

    /-- quotZ a b ∈ ℤ for a, b ∈ ℤ. -/
    theorem quotZ_in_IntSet (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        quotZ a b ∈ (IntSet : U) := by
      unfold quotZ
      exact mulZ_in_IntSet (mulZ (signZ a) (signZ b)) (natToInt (divOf (absZ a) (absZ b)))
        (mulZ_in_IntSet (signZ a) (signZ b) (signZ_in_IntSet a ha) (signZ_in_IntSet b hb))
        (natToInt_mem_IntSet (divOf (absZ a) (absZ b)) (divOf_in_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)))

    /-! ### Basic properties -/

    /-- gcdZ is commutative: gcdZ a b = gcdZ b a. -/
    theorem gcdZ_comm (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        gcdZ a b = gcdZ b a := by
      unfold gcdZ
      exact gcd_comm_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)

    /-- gcdZ a 0 = absZ a. -/
    theorem gcdZ_zero_right (a : U) (ha : a ∈ (IntSet : U)) :
        gcdZ a (zeroZ : U) = absZ a := by
      unfold gcdZ
      rw [absZ_zero]
      exact gcd_zero (absZ a) (absZ_in_omega a ha)

    /-- gcdZ 0 b = absZ b. -/
    theorem gcdZ_zero_left (b : U) (hb : b ∈ (IntSet : U)) :
        gcdZ (zeroZ : U) b = absZ b := by
      rw [gcdZ_comm zeroZ b zeroZ_mem_IntSet hb]
      exact gcdZ_zero_right b hb

    /-! ### modZ bound -/

    /-- modZ a b < absZ b when b ≠ 0 (expressed as modZ a b ∈ absZ b). -/
    theorem modZ_lt_absZ (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hb_ne : b ≠ (zeroZ : U)) :
        modZ a b ∈ absZ b := by
      unfold modZ
      have h_absb_ne : absZ b ≠ (∅ : U) := by
        intro h
        exact hb_ne ((absZ_eq_zero_iff b hb).mp h)
      exact mod_lt_divisor_Omega (absZ a) (absZ b) (absZ_in_omega a ha)
            (absZ_in_omega b hb) h_absb_ne

    -- =========================================================================
    -- Section 2: Divisibility lemmas (bridge ω ↔ ℤ)
    -- =========================================================================

    /-- Bridge: if k | n in ω then natToInt k | natToInt n in ℤ. -/
    private theorem divides_natToInt (k n : U)
        (hk : k ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h : divides k n) :
        dividesZ (natToInt k) (natToInt n) := by
      obtain ⟨q, hq, h_eq⟩ := h
      exact ⟨natToInt q, natToInt_mem_IntSet q hq, by
        rw [h_eq, natToInt_preserves_mul k q hk hq]⟩

    /-- absZ (natToInt n) = n for n ∈ ω. -/
      theorem absZ_natToInt (n : U) (hn : n ∈ (ω : U)) :
        absZ (natToInt n) = n := by
      unfold natToInt
      exact absZ_intClass_pos n hn

    /-- natToInt ∅ = zeroZ. -/
    private theorem natToInt_zero : (natToInt (∅ : U) : U) = (zeroZ : U) := by
      unfold natToInt zeroZ; rfl

    -- =========================================================================
    -- Section 3: gcdZ divisibility properties
    -- =========================================================================

    /-- natToInt (gcdZ a b) divides a. -/
    theorem gcdZ_dividesZ_left (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        dividesZ (natToInt (gcdZ a b)) a := by
      unfold gcdZ
      have hg : gcd (absZ a) (absZ b) ∈ (ω : U) :=
        gcd_in_Omega _ _ (absZ_in_omega a ha) (absZ_in_omega b hb)
      -- divides (gcd ...) (absZ a) in ω
      have h_div := gcd_divides_left_Omega (absZ a) (absZ b)
            (absZ_in_omega a ha) (absZ_in_omega b hb)
      -- Bridge to ℤ: dividesZ (natToInt (gcd ...)) (natToInt (absZ a))
      have h_divZ := divides_natToInt _ _ hg (absZ_in_omega a ha) h_div
      -- Use int_trichotomy to relate a and natToInt (absZ a)
      rcases int_trichotomy a ha with h_zero | ⟨n, hn, hn_ne, ha_eq⟩ |
          ⟨m, hm, hm_ne, ha_eq⟩
      · -- a = 0: trivially dividesZ _ zeroZ
        rw [h_zero] at hg ⊢
        exact dividesZ_zero _ (natToInt_mem_IntSet _ hg)
      · -- a positive: a = intClass n ∅ = natToInt n, absZ a = n
        have h_abs_eq : natToInt (absZ a) = a := by
          rw [ha_eq, absZ_intClass_pos n hn]; unfold natToInt; rfl
        rwa [h_abs_eq] at h_divZ
      · -- a negative: a = intClass ∅ m, absZ a = m
        have h_neg : a = negZ (natToInt (absZ a)) := by
          rw [ha_eq, absZ_intClass_neg m hm]
          unfold natToInt
          exact (negZ_class m (∅ : U) hm zero_in_Omega).symm
        have h_neg_div := (dividesZ_negZ_left_right _ (natToInt (absZ a))
              (natToInt_mem_IntSet _ hg)
              (natToInt_mem_IntSet _ (absZ_in_omega a ha))).mp h_divZ
        rwa [← h_neg] at h_neg_div

    /-- natToInt (gcdZ a b) divides b. -/
    theorem gcdZ_dividesZ_right (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        dividesZ (natToInt (gcdZ a b)) b := by
      rw [gcdZ_comm a b ha hb]
      exact gcdZ_dividesZ_left b a hb ha

    -- =========================================================================
    -- Section 4: Divisibility antisymmetry
    -- =========================================================================

    /-- Bridge: dividesZ a b with a, b ∈ ℤ implies divides (absZ a) (absZ b) in ω. -/
    private theorem dividesZ_to_divides_abs (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (h : dividesZ a b) :
        divides (absZ a) (absZ b) := by
      obtain ⟨k, hk, h_eq⟩ := h
      exact ⟨absZ k, absZ_in_omega k hk, by
        rw [h_eq, absZ_mulZ a k ha hk]⟩

    /-- Multiplicative left cancellation in ω, lifted from Peano. -/
    private theorem mul_cancel_left_omega (a b c : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hc : c ∈ (ω : U))
        (ha_ne : a ≠ (∅ : U)) (h : mul a b = mul a c) : b = c := by
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      obtain ⟨r, hr⟩ := fromPeano_surjective c (mem_Omega_is_Nat c hc)
      subst hp; subst hq; subst hr
      have hp_ne : p ≠ Peano.ℕ₀.zero :=
        fun heq => by subst heq; exact ha_ne rfl
      rw [← fromPeano_mul p q, ← fromPeano_mul p r] at h
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.Mul.mul_cancelation_left p q r hp_ne (fromPeano_injective h))

    /-- In ω, mul a b = σ ∅ implies a = σ ∅ and b = σ ∅, lifted from Peano. -/
    private theorem mul_eq_one_omega (a b : U)
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

    /-- Antisymmetry of divisibility: a | b and b | a implies |a| = |b|. -/
    theorem dividesZ_antisymm_abs (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hab : dividesZ a b) (hba : dividesZ b a) :
        absZ a = absZ b := by
      -- Reduce to ω: divides (absZ a) (absZ b) and divides (absZ b) (absZ a)
      have h1 := dividesZ_to_divides_abs a b ha hb hab
      have h2 := dividesZ_to_divides_abs b a hb ha hba
      -- If a = 0 then b = 0 (from hab: ∃ k, b = mulZ zeroZ k = zeroZ)
      by_cases ha0 : a = (zeroZ : U)
      · obtain ⟨k, hk, h_eq⟩ := hab
        rw [ha0, mulZ_zero_left k hk] at h_eq
        rw [ha0, h_eq]
      · -- a ≠ 0 → absZ a ≠ 0
        have h_absa_ne : absZ a ≠ (∅ : U) := by
          intro h; exact ha0 ((absZ_eq_zero_iff a ha).mp h)
        -- divides (absZ a) (absZ b) : absZ b = mul (absZ a) q₁
        -- divides (absZ b) (absZ a) : absZ a = mul (absZ b) q₂
        obtain ⟨q₁, hq₁, h_eq1⟩ := h1
        obtain ⟨q₂, hq₂, h_eq2⟩ := h2
        -- absZ a = mul (absZ a) (mul q₁ q₂)  by associativity
        have h_eq3 : absZ a = mul (absZ a) (mul q₁ q₂) := by
          calc absZ a
              = mul (absZ b) q₂ := h_eq2
            _ = mul (mul (absZ a) q₁) q₂ := by rw [h_eq1]
            _ = mul (absZ a) (mul q₁ q₂) :=
                mul_assoc_Omega (absZ a) q₁ q₂
                  (absZ_in_omega a ha) hq₁ hq₂
        -- mul (absZ a) (mul q₁ q₂) = mul (absZ a) (σ ∅)
        have h_prod : mul (absZ a) (mul q₁ q₂) =
            mul (absZ a) (σ (∅ : U)) := by
          rw [← h_eq3]
          exact (mul_one_Omega (absZ a) (absZ_in_omega a ha)).symm
        -- Cancel: mul q₁ q₂ = σ ∅
        have h_cancel := mul_cancel_left_omega (absZ a) (mul q₁ q₂)
              (σ (∅ : U)) (absZ_in_omega a ha) (mul_in_Omega q₁ q₂ hq₁ hq₂)
              (succ_in_Omega (∅ : U) zero_in_Omega) h_absa_ne h_prod
        -- Product of two ω elements equals 1 → both are 1
        have h_q1_one := mul_eq_one_omega q₁ q₂ hq₁ hq₂ h_cancel
        -- absZ b = mul (absZ a) (σ ∅) = absZ a
        rw [h_eq1, h_q1_one.1,
            mul_one_Omega (absZ a) (absZ_in_omega a ha)]

    -- =========================================================================
    -- Section 5: gcdZ is greatest
    -- =========================================================================

    /-- Helper: dividesZ (natToInt (absZ d)) x → dividesZ d x, for d,x ∈ ℤ. -/
    private theorem dividesZ_natToInt_abs (d x : U)
        (hd : d ∈ (IntSet : U)) (hx : x ∈ (IntSet : U))
        (h : dividesZ (natToInt (absZ d)) x) :
        dividesZ d x := by
      rcases int_trichotomy d hd with rfl | ⟨n, hn, _, rfl⟩ | ⟨m, hm, _, rfl⟩
      · -- d = zeroZ: absZ d = ∅, natToInt ∅ = zeroZ = d
        rwa [absZ_zero, natToInt_zero] at h
      · -- d = intClass n ∅ (positive): natToInt (absZ d) = natToInt n = d
        rwa [absZ_intClass_pos n hn] at h
      · -- d = intClass ∅ m (negative): natToInt (absZ d) = natToInt m = negZ d
        rw [absZ_intClass_neg m hm] at h
        have h_neg : (intClass (∅ : U) m : U) = negZ (natToInt m) := by
          unfold natToInt
          exact (negZ_class m (∅ : U) hm zero_in_Omega).symm
        rw [h_neg]
        exact (dividesZ_negZ_left (natToInt m) x
          (natToInt_mem_IntSet m hm) hx).mp h

    /-- gcdZ is the greatest common divisor: if d | a and d | b then d | natToInt (gcdZ a b). -/
    theorem gcdZ_is_greatest (a b d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) (hd : d ∈ (IntSet : U))
        (hda : dividesZ d a) (hdb : dividesZ d b) :
        dividesZ d (natToInt (gcdZ a b)) := by
      -- Bridge to ω
      have h1 := dividesZ_to_divides_abs d a hd ha hda
      have h2 := dividesZ_to_divides_abs d b hd hb hdb
      have h_gcd := gcd_greatest_Omega (absZ a) (absZ b) (absZ d)
        (absZ_in_omega a ha) (absZ_in_omega b hb) (absZ_in_omega d hd) h1 h2
      -- divides (absZ d) (gcdZ a b) in ω → dividesZ in ℤ
      have hg := gcdZ_in_omega a b ha hb
      have h_bridge := divides_natToInt (absZ d) (gcdZ a b)
        (absZ_in_omega d hd) hg h_gcd
      exact dividesZ_natToInt_abs d (natToInt (gcdZ a b)) hd
        (natToInt_mem_IntSet _ hg) h_bridge

    -- =========================================================================
    -- Section 6: lcmZ — LCM on ℤ
    -- =========================================================================

    /-- LCM on ℤ, defined as lcm of absolute values. Result is in ω. -/
    noncomputable def lcmZ (a b : U) : U := lcm (absZ a) (absZ b)

    /-- lcmZ a b ∈ ω for a, b ∈ ℤ. -/
    theorem lcmZ_in_omega (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        lcmZ a b ∈ (ω : U) := by
      unfold lcmZ
      exact lcm_in_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)

    /-- lcmZ is commutative: lcmZ a b = lcmZ b a. -/
    theorem lcmZ_comm (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        lcmZ a b = lcmZ b a := by
      unfold lcmZ
      exact lcm_comm_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb)

    -- =========================================================================
    -- Section 7: Full divisibility antisymmetry
    -- =========================================================================

    /-- Helper: x ∈ ℤ implies x = natToInt (absZ x) or x = negZ (natToInt (absZ x)). -/
    private theorem int_eq_natToInt_abs_or_neg (x : U) (hx : x ∈ (IntSet : U)) :
        x = natToInt (absZ x) ∨ x = negZ (natToInt (absZ x)) := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, _, rfl⟩ | ⟨m, hm, _, rfl⟩
      · -- x = zeroZ
        left; rw [absZ_zero, natToInt_zero]
      · -- x = intClass n ∅ (positive)
        left; rw [absZ_intClass_pos n hn]; rfl
      · -- x = intClass ∅ m (negative)
        right
        rw [absZ_intClass_neg m hm]
        unfold natToInt
        exact (negZ_class m (∅ : U) hm zero_in_Omega).symm

    /-- Full antisymmetry: a | b and b | a implies a = b or a = negZ b. -/
    theorem dividesZ_antisymm (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hab : dividesZ a b) (hba : dividesZ b a) :
        a = b ∨ a = negZ b := by
      have h_abs_eq := dividesZ_antisymm_abs a b ha hb hab hba
      -- a = natToInt n or a = negZ (natToInt n), same for b, where n = absZ a = absZ b
      rcases int_eq_natToInt_abs_or_neg a ha with ha_eq | ha_eq <;>
        rcases int_eq_natToInt_abs_or_neg b hb with hb_eq | hb_eq
      · -- a = natToInt n, b = natToInt n
        left; rw [ha_eq, hb_eq, h_abs_eq]
      · -- a = natToInt n, b = negZ (natToInt n)
        right; rw [ha_eq, hb_eq, h_abs_eq]
        exact (negZ_negZ _ (natToInt_mem_IntSet _ (absZ_in_omega _ hb))).symm
      · -- a = negZ (natToInt n), b = natToInt n
        right; rw [ha_eq, hb_eq, h_abs_eq]
      · -- a = negZ (natToInt n), b = negZ (natToInt n)
        left; rw [ha_eq, hb_eq, h_abs_eq]

    -- =========================================================================
    -- Section 8: Euclidean Division on ℤ
    -- =========================================================================

    /-- Euclidean division theorem on ℤ. -/
    theorem euclidean_divisionZ (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (h_b_neq_zero : b ≠ zeroZ) :
        a = addZ (mulZ (quotZ a b) b) (mulZ (signZ a) (natToInt (modZ a b))) := by
      have ha_omega := absZ_in_omega a ha
      have hb_omega := absZ_in_omega b hb
      have h_ab_ne : absZ b ≠ (∅ : U) := fun heq => h_b_neq_zero ((absZ_eq_zero_iff b hb).mp heq)
      have h_euclid := divMod_eq_Omega (absZ a) (absZ b) ha_omega hb_omega h_ab_ne
      have hn_euclid := congrArg natToInt h_euclid
      have h_q_om := divOf_in_Omega (absZ a) (absZ b) ha_omega hb_omega
      have h_r_om := modOf_in_Omega (absZ a) (absZ b) ha_omega hb_omega
      have h_prod_om := mul_in_Omega (divOf (absZ a) (absZ b)) (absZ b) h_q_om hb_omega
      have h_qo_in := natToInt_mem_IntSet _ h_q_om
      have h_bo_in := natToInt_mem_IntSet _ hb_omega
      have h_ro_in := natToInt_mem_IntSet _ h_r_om
      have h_sa_in := signZ_in_IntSet a ha
      have h_sb_in := signZ_in_IntSet b hb

      -- Rewrite in hn_euclid:
      have eq1 : natToInt (add (mul (divOf (absZ a) (absZ b)) (absZ b)) (modOf (absZ a) (absZ b))) =
                 addZ (mulZ (natToInt (divOf (absZ a) (absZ b))) (natToInt (absZ b))) (natToInt (modOf (absZ a) (absZ b))) := by
        rw [natToInt_preserves_add _ _ h_prod_om h_r_om]
        rw [natToInt_preserves_mul _ _ h_q_om hb_omega]
      rw [eq1] at hn_euclid
      have hmodZ_eq : natToInt (modZ a b) = natToInt (modOf (absZ a) (absZ b)) := by rfl
      rw [← hmodZ_eq] at hn_euclid

      -- Start with a = signZ a * (absZ a) via signZ_mulZ_absZ
      have h_a_eq := signZ_mulZ_absZ a ha
      rw [hn_euclid] at h_a_eq
      have eq2 : mulZ (signZ a) (addZ (mulZ (natToInt (divOf (absZ a) (absZ b))) (natToInt (absZ b))) (natToInt (modZ a b))) =
                 addZ (mulZ (signZ a) (mulZ (natToInt (divOf (absZ a) (absZ b))) (natToInt (absZ b))))
                      (mulZ (signZ a) (natToInt (modZ a b))) := by
        exact mulZ_addZ_distrib_left (signZ a) _ _ h_sa_in (mulZ_in_IntSet _ _ h_qo_in h_bo_in) h_ro_in
      rw [eq2] at h_a_eq

      have h_b_eq := signZ_mulZ_absZ b hb
      have h_absb : natToInt (absZ b) = mulZ (signZ b) b := by
        have tmp : mulZ (signZ b) b = mulZ (signZ b) (mulZ (signZ b) (natToInt (absZ b))) := by
          exact congrArg (mulZ (signZ b)) h_b_eq
        have eq3 : mulZ (signZ b) (mulZ (signZ b) (natToInt (absZ b))) =
                   mulZ (mulZ (signZ b) (signZ b)) (natToInt (absZ b)) :=
          Eq.symm (mulZ_assoc (signZ b) (signZ b) _ h_sb_in h_sb_in h_bo_in)
        have step2 : mulZ (signZ b) b = mulZ (mulZ (signZ b) (signZ b)) (natToInt (absZ b)) := by
          rw [tmp, eq3]
        have step3 : mulZ (mulZ (signZ b) (signZ b)) (natToInt (absZ b)) = mulZ oneZ (natToInt (absZ b)) := by
          rw [signZ_square b hb h_b_neq_zero]
        have step4 : mulZ oneZ (natToInt (absZ b)) = natToInt (absZ b) := by
          rw [mulZ_one_left _ h_bo_in]
        rw [step2, step3, step4]

      -- Now substitute h_absb into the quotient term:
      have t1 : mulZ (signZ a) (mulZ (natToInt (divOf (absZ a) (absZ b))) (natToInt (absZ b))) =
                mulZ (signZ a) (mulZ (natToInt (divOf (absZ a) (absZ b))) (mulZ (signZ b) b)) := by
        rw [h_absb]

      -- Rearrange to get quotZ a b = signZ a * signZ b * qx
      have t2 : mulZ (signZ a) (mulZ (natToInt (divOf (absZ a) (absZ b))) (mulZ (signZ b) b)) =
                mulZ (mulZ (mulZ (signZ a) (signZ b)) (natToInt (divOf (absZ a) (absZ b)))) b := by
        have e1 : mulZ (natToInt (divOf (absZ a) (absZ b))) (mulZ (signZ b) b) =
                  mulZ (mulZ (natToInt (divOf (absZ a) (absZ b))) (signZ b)) b :=
          Eq.symm (mulZ_assoc _ _ _ h_qo_in h_sb_in hb)
        rw [e1]
        have e2 : mulZ (signZ a) (mulZ (mulZ (natToInt (divOf (absZ a) (absZ b))) (signZ b)) b) =
                  mulZ (mulZ (signZ a) (mulZ (natToInt (divOf (absZ a) (absZ b))) (signZ b))) b :=
          Eq.symm (mulZ_assoc _ _ _ h_sa_in (mulZ_in_IntSet _ _ h_qo_in h_sb_in) hb)
        rw [e2]
        have e3 : mulZ (natToInt (divOf (absZ a) (absZ b))) (signZ b) = mulZ (signZ b) (natToInt (divOf (absZ a) (absZ b))) :=
          mulZ_comm _ _ h_qo_in h_sb_in
        rw [e3]
        have e4 : mulZ (signZ a) (mulZ (signZ b) (natToInt (divOf (absZ a) (absZ b)))) =
                  mulZ (mulZ (signZ a) (signZ b)) (natToInt (divOf (absZ a) (absZ b))) :=
          Eq.symm (mulZ_assoc _ _ _ h_sa_in h_sb_in h_qo_in)
        rw [e4]

      rw [t1, t2] at h_a_eq
      exact h_a_eq


    /-- gcdZ is "associative": gcdZ a (natToInt (gcdZ b c)) = gcdZ (natToInt (gcdZ a b)) c -/
    theorem gcdZ_assoc (a b c : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) (hc : c ∈ (IntSet : U)) :
        gcdZ a (natToInt (gcdZ b c)) = gcdZ (natToInt (gcdZ a b)) c := by
      have hab1 : gcdZ a b ∈ (ω : U) := gcdZ_in_omega a b ha hb
      have hab2 : gcdZ b c ∈ (ω : U) := gcdZ_in_omega b c hb hc
      have habs_ab : absZ (natToInt (gcdZ a b)) = gcdZ a b := absZ_natToInt _ hab1
      have habs_bc : absZ (natToInt (gcdZ b c)) = gcdZ b c := absZ_natToInt _ hab2
      unfold gcdZ
      rw [habs_bc, habs_ab]
      exact ZFC.Nat.Gcd.gcd_assoc_Omega (absZ a) (absZ b) (absZ c) (absZ_in_omega a ha) (absZ_in_omega b hb) (absZ_in_omega c hc)

    /-- lcmZ a 0 = 0 -/
    theorem lcmZ_zero_right (a : U) (ha : a ∈ (IntSet : U)) :
        lcmZ a zeroZ = (∅ : U) := by
      unfold lcmZ
      rw [absZ_zero]
      exact Nat.Gcd.lcm_zero_right_Omega (absZ a) (absZ_in_omega a ha)

    /-- lcmZ 0 b = 0 -/
    theorem lcmZ_zero_left (b : U) (hb : b ∈ (IntSet : U)) :
        lcmZ zeroZ b = (∅ : U) := by
      unfold lcmZ
      rw [absZ_zero]
      exact Nat.Gcd.lcm_zero_left_Omega (absZ b) (absZ_in_omega b hb)

    -- =========================================================================
    -- Section 5: Bezout's identity on ℤ
    -- =========================================================================

    /-- Bridge: `natToInt (absZ a) = signZ a * a`. -/
    private theorem bezout_natToInt_absZ_eq (a : U) (ha : a ∈ (IntSet : U)) :
        natToInt (absZ a) = mulZ (signZ a) a := by
      have habs_mem := natToInt_mem_IntSet (absZ a) (absZ_in_omega a ha)
      have hsign_mem := signZ_in_IntSet a ha
      have h_eq := signZ_mulZ_absZ a ha  -- a = mulZ (signZ a) (natToInt (absZ a))
      by_cases h_zero : a = zeroZ
      · rw [h_zero, signZ_zero, absZ_zero, mulZ_zero_left zeroZ zeroZ_mem_IntSet]
        rfl
      · have hsq := signZ_square a ha h_zero
        calc natToInt (absZ a)
            = mulZ oneZ (natToInt (absZ a))                        := (mulZ_one_left _ habs_mem).symm
          _ = mulZ (mulZ (signZ a) (signZ a)) (natToInt (absZ a)) := by rw [hsq]
          _ = mulZ (signZ a) (mulZ (signZ a) (natToInt (absZ a))) :=
                mulZ_assoc _ _ _ hsign_mem hsign_mem habs_mem
          _ = mulZ (signZ a) a                                     := by rw [← h_eq]

    /-- Bridge: `natToInt (sub x y) = subZ (natToInt x) (natToInt y)` when `y ≤ x`. -/
    private theorem bezout_natToInt_sub_eq (x y : U) (hx : x ∈ ω) (hy : y ∈ ω)
        (hle : y ∈ x ∨ y = x) :
        natToInt (sub x y) = subZ (natToInt x) (natToInt y) := by
      have hs_mem := sub_in_Omega x y hx hy
      have h_int_s := natToInt_mem_IntSet (sub x y) hs_mem
      have h_int_y := natToInt_mem_IntSet y hy
      -- addZ (natToInt (sub x y)) (natToInt y) = natToInt x
      have h1 : addZ (natToInt (sub x y)) (natToInt y) = natToInt x := by
        rw [← natToInt_preserves_add (sub x y) y hs_mem hy,
            add_k_sub_k_Omega x y hx hy hle]
      -- Cancel natToInt y: add negZ (natToInt y) to both sides, then simplify
      have h2 : addZ (addZ (natToInt (sub x y)) (natToInt y)) (negZ (natToInt y)) =
                addZ (natToInt x) (negZ (natToInt y)) := by rw [h1]
      rw [addZ_assoc _ _ _ h_int_s h_int_y (negZ_in_IntSet _ h_int_y),
          addZ_negZ_right _ h_int_y, addZ_zero_right _ h_int_s] at h2
      exact h2

    /-- Bezout case 1: gcd = n·|a| - m·|b|. Witnesses: s = n·sign(a), t = -m·sign(b). -/
    private theorem bezout_case1 (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (n m : U) (hn : n ∈ ω) (hm : m ∈ ω)
        (heq : gcd (absZ a) (absZ b) = sub (mul n (absZ a)) (mul m (absZ b)))
        (hle : mul m (absZ b) ∈ mul n (absZ a) ∨ mul m (absZ b) = mul n (absZ a)) :
        ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
          natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
      have habs_a := absZ_in_omega a ha
      have habs_b := absZ_in_omega b hb
      have h_na := mul_in_Omega n (absZ a) hn habs_a
      have h_mb := mul_in_Omega m (absZ b) hm habs_b
      have h_in := natToInt_mem_IntSet n hn
      have h_im := natToInt_mem_IntSet m hm
      have h_sa := signZ_in_IntSet a ha
      have h_sb := signZ_in_IntSet b hb
      have h_ns : mulZ (natToInt n) (signZ a) ∈ (IntSet : U) := mulZ_in_IntSet _ _ h_in h_sa
      have h_ms : mulZ (natToInt m) (signZ b) ∈ (IntSet : U) := mulZ_in_IntSet _ _ h_im h_sb
      -- Build h1 step by step using rewrite lemmas
      have h1 : natToInt (gcdZ a b) =
                addZ (mulZ (mulZ (natToInt n) (signZ a)) a)
                     (mulZ (negZ (mulZ (natToInt m) (signZ b))) b) := by
        unfold gcdZ
        rw [heq,
            bezout_natToInt_sub_eq (mul n (absZ a)) (mul m (absZ b)) h_na h_mb hle,
            natToInt_preserves_mul n (absZ a) hn habs_a,
            natToInt_preserves_mul m (absZ b) hm habs_b,
            bezout_natToInt_absZ_eq a ha,
            bezout_natToInt_absZ_eq b hb,
            ← mulZ_assoc (natToInt n) (signZ a) a h_in h_sa ha,
            ← mulZ_assoc (natToInt m) (signZ b) b h_im h_sb hb,
            show subZ (mulZ (mulZ (natToInt n) (signZ a)) a)
                      (mulZ (mulZ (natToInt m) (signZ b)) b) =
                 addZ (mulZ (mulZ (natToInt n) (signZ a)) a)
                      (negZ (mulZ (mulZ (natToInt m) (signZ b)) b)) from rfl,
            ← mulZ_negZ_left (mulZ (natToInt m) (signZ b)) b h_ms hb]
      exact ⟨_, _, h_ns, negZ_in_IntSet _ h_ms, h1⟩

    /-- Bezout case 2: gcd = n·|b| - m·|a|. Witnesses: s = -m·sign(a), t = n·sign(b). -/
    private theorem bezout_case2 (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (n m : U) (hn : n ∈ ω) (hm : m ∈ ω)
        (heq : gcd (absZ a) (absZ b) = sub (mul n (absZ b)) (mul m (absZ a)))
        (hle : mul m (absZ a) ∈ mul n (absZ b) ∨ mul m (absZ a) = mul n (absZ b)) :
        ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
          natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
      have habs_a := absZ_in_omega a ha
      have habs_b := absZ_in_omega b hb
      have h_nb := mul_in_Omega n (absZ b) hn habs_b
      have h_ma := mul_in_Omega m (absZ a) hm habs_a
      have h_in := natToInt_mem_IntSet n hn
      have h_im := natToInt_mem_IntSet m hm
      have h_sa := signZ_in_IntSet a ha
      have h_sb := signZ_in_IntSet b hb
      have h_ns : mulZ (natToInt n) (signZ b) ∈ (IntSet : U) := mulZ_in_IntSet _ _ h_in h_sb
      have h_ms : mulZ (natToInt m) (signZ a) ∈ (IntSet : U) := mulZ_in_IntSet _ _ h_im h_sa
      have h1 : natToInt (gcdZ a b) =
                addZ (mulZ (negZ (mulZ (natToInt m) (signZ a))) a)
                     (mulZ (mulZ (natToInt n) (signZ b)) b) := by
        unfold gcdZ
        rw [heq,
            bezout_natToInt_sub_eq (mul n (absZ b)) (mul m (absZ a)) h_nb h_ma hle,
            natToInt_preserves_mul n (absZ b) hn habs_b,
            natToInt_preserves_mul m (absZ a) hm habs_a,
            bezout_natToInt_absZ_eq b hb,
            bezout_natToInt_absZ_eq a ha,
            ← mulZ_assoc (natToInt n) (signZ b) b h_in h_sb hb,
            ← mulZ_assoc (natToInt m) (signZ a) a h_im h_sa ha,
            show subZ (mulZ (mulZ (natToInt n) (signZ b)) b)
                      (mulZ (mulZ (natToInt m) (signZ a)) a) =
                 addZ (mulZ (mulZ (natToInt n) (signZ b)) b)
                      (negZ (mulZ (mulZ (natToInt m) (signZ a)) a)) from rfl,
            ← mulZ_negZ_left (mulZ (natToInt m) (signZ a)) a h_ms ha,
            addZ_comm _ _ (mulZ_in_IntSet _ _ h_ns hb) (mulZ_in_IntSet _ _ (negZ_in_IntSet _ h_ms) ha)]
      exact ⟨_, _, negZ_in_IntSet _ h_ms, h_ns, h1⟩

    /-- Bezout's identity on ℤ:
        ∃ s t ∈ ℤ, natToInt (gcdZ a b) = s·a + t·b. -/
    theorem bezoutZ (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
          natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
      have habs_a := absZ_in_omega a ha
      have habs_b := absZ_in_omega b hb
      obtain ⟨n, m, hn, hm, hor⟩ := Nat.Gcd.bezout_natform_Omega (absZ a) (absZ b) habs_a habs_b
      -- Lemma: if gcd(|a|,|b|) = 0 then a = b = 0, trivial witnesses s=t=0
      have trivial_case : gcd (absZ a) (absZ b) = (∅ : U) →
          ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
            natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
        intro h_gcd_zero
        have ha0 : a = zeroZ := (absZ_eq_zero_iff a ha).mp
          ((zero_divides_iff_Omega _ habs_a).mp
            (h_gcd_zero ▸ gcd_divides_left_Omega (absZ a) (absZ b) habs_a habs_b))
        have hb0 : b = zeroZ := (absZ_eq_zero_iff b hb).mp
          ((zero_divides_iff_Omega _ habs_b).mp
            (h_gcd_zero ▸ gcd_divides_right_Omega (absZ a) (absZ b) habs_a habs_b))
        have hgcd_eq : gcdZ a b = (∅ : U) := by
          unfold gcdZ; rw [ha0, hb0, absZ_zero]
          exact gcd_zero (∅ : U) zero_in_Omega
        refine ⟨zeroZ, zeroZ, zeroZ_mem_IntSet, zeroZ_mem_IntSet, ?_⟩
        rw [mulZ_zero_left a ha, mulZ_zero_left b hb,
            addZ_zero_right zeroZ zeroZ_mem_IntSet, hgcd_eq]
        -- natToInt ∅ = zeroZ, both definitionally intClass ∅ ∅
        rfl
      rcases hor with h1 | h2
      · -- Case: gcd = n·|a| - m·|b|
        have h_na := mul_in_Omega n (absZ a) hn habs_a
        have h_mb := mul_in_Omega m (absZ b) hm habs_b
        -- Trichotomy on mul m (absZ b) vs mul n (absZ a)
        rcases trichotomy (mul m (absZ b)) (mul n (absZ a))
            (mem_Omega_is_Nat _ h_mb) (mem_Omega_is_Nat _ h_na) with hlt | heq | hgt
        · exact bezout_case1 a b ha hb n m hn hm h1 (Or.inl hlt)
        · exact bezout_case1 a b ha hb n m hn hm h1 (Or.inr heq)
        · -- mul n (absZ a) ∈ mul m (absZ b): sub truncates to 0, gcd = 0
          apply trivial_case
          have h_sub0 : sub (mul n (absZ a)) (mul m (absZ b)) = (∅ : U) := by
            apply Classical.byContradiction; intro hne
            have hmem := (sub_pos_iff_lt_Omega (mul n (absZ a)) (mul m (absZ b)) h_na h_mb).mp hne
            exact absurd hgt (mem_asymm (mul m (absZ b)) (mul n (absZ a)) (mem_Omega_is_Nat _ h_mb) (mem_Omega_is_Nat _ h_na) hmem)
          rw [h1, h_sub0]
      · -- Case: gcd = n·|b| - m·|a|
        have h_nb := mul_in_Omega n (absZ b) hn habs_b
        have h_ma := mul_in_Omega m (absZ a) hm habs_a
        rcases trichotomy (mul m (absZ a)) (mul n (absZ b))
            (mem_Omega_is_Nat _ h_ma) (mem_Omega_is_Nat _ h_nb) with hlt | heq | hgt
        · exact bezout_case2 a b ha hb n m hn hm h2 (Or.inl hlt)
        · exact bezout_case2 a b ha hb n m hn hm h2 (Or.inr heq)
        · apply trivial_case
          have h_sub0 : sub (mul n (absZ b)) (mul m (absZ a)) = (∅ : U) := by
            apply Classical.byContradiction; intro hne
            have hmem := (sub_pos_iff_lt_Omega (mul n (absZ b)) (mul m (absZ a)) h_nb h_ma).mp hne
            exact absurd hgt (mem_asymm (mul m (absZ a)) (mul n (absZ b)) (mem_Omega_is_Nat _ h_ma) (mem_Omega_is_Nat _ h_nb) hmem)
          rw [h2, h_sub0]

  end Int.Div


  export Int.Div (
    gcdZ
    modZ
    lcmZ
    quotZ
    absZ_natToInt
    gcdZ_in_omega
    modZ_in_omega
    quotZ_in_IntSet
    euclidean_divisionZ
    lcmZ_in_omega
    gcdZ_comm
    gcdZ_zero_right
    gcdZ_zero_left
    lcmZ_comm
    modZ_lt_absZ
    gcdZ_dividesZ_left
    gcdZ_dividesZ_right
    gcdZ_is_greatest
    dividesZ_antisymm_abs
    dividesZ_antisymm
    bezoutZ
  )

end ZFC
