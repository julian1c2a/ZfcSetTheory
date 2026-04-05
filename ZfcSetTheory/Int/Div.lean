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
  * `dividesZ_antisymm_abs` — a | b → b | a → absZ a = absZ b
  * `dividesZ_antisymm` — a | b → b | a → a = b ∨ a = negZ b
  * `lcmZ_in_omega` — lcmZ a b ∈ ω
  * `lcmZ_comm` — lcmZ a b = lcmZ b a
-/

import ZfcSetTheory.Int.Abs
import ZfcSetTheory.Int.DivMod
import ZfcSetTheory.Nat.Div
import ZfcSetTheory.Nat.Gcd

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
    private theorem absZ_natToInt (n : U) (hn : n ∈ (ω : U)) :
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
      · -- a = negZ (natToInt n), b = natToInt n
        right; rw [ha_eq, hb_eq, h_abs_eq]
      · -- a = negZ (natToInt n), b = negZ (natToInt n)
        left; rw [ha_eq, hb_eq, h_abs_eq]

  end Int.Div

  export Int.Div (
    gcdZ
    modZ
    lcmZ
    gcdZ_in_omega
    modZ_in_omega
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
  )

end ZFC
