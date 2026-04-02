/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Newton's Binomial Theorem on Von Neumann Natural Numbers

  This module defines the binomial term on ω (the Von Neumann naturals) and
  lifts Newton's binomial theorem, the sum-of-binomials identity, and other
  results from the Peano formalization.

  ## Strategy (Pattern B: bridge-only)

  `binomTermOf` follows the standard 4-argument bridge pattern.

  `finSum` takes a Peano function `f : ℕ₀ → ℕ₀` and cannot be directly bridged
  to a ZFC function `g : U → U` without extra hypotheses. Therefore we state
  `newton_binom_peano` and `sum_binom_eq_pow_two_peano` at the Peano level but
  with the result transported into ZFC via `fromPeano`.

  ## Main Results

  - `binomTermOf`:             C(n,k) · a^k · b^(n-k) in ω
  - `binomTermOf_zero`:        binomTerm(a,b,n,0) = b^n
  - `binomTermOf_self`:        binomTerm(a,b,n,n) = a^n
  - `binomTermOf_eq`:          binomTerm expanded as C(n,k)·a^k·b^(n−k)
  - `pow_add_split_Omega`:     n^(m+k) = n^m · n^k
  - `newton_binom_peano`:      (a+b)^n = Σ C(n,k)·a^k·b^(n−k)  (Peano→ZFC)
  - `sum_binom_eq_pow_two_peano`: Σ C(n,k) = 2^n  (Peano→ZFC)
  - `exists_nm_growth_Omega`:  ∃ n m ∈ ω, ∀ k ≥ 1, (n+k)^m < n^(m+k)
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Add
import ZfcSetTheory.Nat.Mul
import ZfcSetTheory.Nat.Sub
import ZfcSetTheory.Nat.Pow
import ZfcSetTheory.Nat.Binom
import PeanoNatLib.PeanoNatNewtonBinom

namespace ZFC
  open Classical

  universe u
  variable {U : Type u}

  namespace Nat.NewtonBinom

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `isNat n`. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : isNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    -- =========================================================================
    -- §0  Definition
    -- =========================================================================

    /-- `binomTermOf a b n k = C(n,k) · a^k · b^(n−k)` in ω.
        Returns `∅` if any argument is not in ω. -/
    noncomputable def binomTermOf (a b n k : U) : U :=
      if ha : a ∈ (ω : U) then
        if hb : b ∈ (ω : U) then
          if hn : n ∈ (ω : U) then
            if hk : k ∈ (ω : U) then
              fromPeano (Peano.NewtonBinom.binomTerm
                (toPeano a (mem_Omega_is_Nat a ha))
                (toPeano b (mem_Omega_is_Nat b hb))
                (toPeano n (mem_Omega_is_Nat n hn))
                (toPeano k (mem_Omega_is_Nat k hk)))
            else ∅
          else ∅
        else ∅
      else ∅

    -- =========================================================================
    -- §1  Closure in ω
    -- =========================================================================

    /-- The binomial term of four natural numbers is a natural number. -/
    theorem binomTermOf_in_Omega (a b n k : U) (ha : a ∈ (ω : U))
        (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        binomTermOf a b n k ∈ (ω : U) := by
      simp only [binomTermOf, dif_pos ha, dif_pos hb, dif_pos hn, dif_pos hk]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- §2  Bridge theorem
    -- =========================================================================

    /-- **Bridge theorem**: `fromPeano` commutes with `binomTerm`. -/
    theorem fromPeano_binomTerm (p q r s : Peano.ℕ₀) :
        (fromPeano (Peano.NewtonBinom.binomTerm p q r s) : U) =
        binomTermOf (fromPeano p) (fromPeano q) (fromPeano r) (fromPeano s) := by
      simp only [binomTermOf,
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat q)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat r)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat s))]
      congr 1; congr 1; congr 1; congr 1
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat q)))
                  (fromPeano_is_nat q)).trans (toPeano_fromPeano q)).symm
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat r)))
                  (fromPeano_is_nat r)).trans (toPeano_fromPeano r)).symm
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat s)))
                  (fromPeano_is_nat s)).trans (toPeano_fromPeano s)).symm

    -- =========================================================================
    -- §3  Concrete values
    -- =========================================================================

    /-- `binomTerm(a, b, n, 0) = b^n` for `a, b, n ∈ ω`. -/
    theorem binomTermOf_zero (a b n : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hn : n ∈ (ω : U)) : binomTermOf a b n ∅ = pow b n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      obtain ⟨r, hr⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq; subst hr
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_binomTerm, Peano.NewtonBinom.binomTerm_zero, fromPeano_pow]

    /-- `binomTerm(a, b, n, n) = a^n` for `a, b, n ∈ ω`. -/
    theorem binomTermOf_self (a b n : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hn : n ∈ (ω : U)) : binomTermOf a b n n = pow a n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      obtain ⟨r, hr⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq; subst hr
      rw [← fromPeano_binomTerm, Peano.NewtonBinom.binomTerm_self, fromPeano_pow]

    -- =========================================================================
    -- §4  Expansion
    -- =========================================================================

    /-- `binomTermOf a b n k = C(n,k) · a^k · b^(n−k)` explicitly. -/
    theorem binomTermOf_eq (a b n k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        binomTermOf a b n k =
        mul (mul (binomOf n k) (pow a k)) (pow b (sub n k)) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      obtain ⟨r, hr⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨s, hs⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr; subst hs
      rw [← fromPeano_binomTerm]
      show (fromPeano (Peano.NewtonBinom.binomTerm p q r s) : U) =
           mul (mul (binomOf (fromPeano r) (fromPeano s))
                    (pow (fromPeano p) (fromPeano s)))
               (pow (fromPeano q) (sub (fromPeano r) (fromPeano s)))
      rw [← fromPeano_binom r s,
          ← fromPeano_pow p s,
          ← fromPeano_sub r s,
          ← fromPeano_pow q (Peano.Sub.sub r s),
          ← fromPeano_mul (Peano.Binom.binom r s) (Peano.Pow.pow p s),
          ← fromPeano_mul
              (Peano.Mul.mul (Peano.Binom.binom r s) (Peano.Pow.pow p s))
              (Peano.Pow.pow q (Peano.Sub.sub r s))]
      rfl

    -- =========================================================================
    -- §5  Power splitting
    -- =========================================================================

    /-- `n^(m+k) = n^m · n^k` for `n, m, k ∈ ω`. -/
    theorem pow_add_split_Omega (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hk : k ∈ (ω : U)) :
        pow n (add m k) = mul (pow n m) (pow n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_add q r,
          ← fromPeano_pow p (Peano.Add.add q r),
          ← fromPeano_pow p q,
          ← fromPeano_pow p r,
          ← fromPeano_mul (Peano.Pow.pow p q) (Peano.Pow.pow p r)]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.NewtonBinom.pow_add_split p q r)

    -- =========================================================================
    -- §6  Newton's binomial theorem (Peano-level statement)
    -- =========================================================================

    /-- **Newton's binomial theorem** at the Peano level, transported to ZFC:
        `(a + b)^n = Σ_{k≤n} C(n,k) · a^k · b^(n-k)`.
        This states the theorem using `fromPeano` applied to both sides. -/
    theorem newton_binom_peano (a b : Peano.ℕ₀) (n : Peano.ℕ₀) :
        pow (add (fromPeano a : U) (fromPeano b)) (fromPeano n) =
        (fromPeano (Peano.NewtonBinom.finSum
          (Peano.NewtonBinom.binomTerm a b n) n) : U) := by
      rw [← fromPeano_add a b, ← fromPeano_pow (Peano.Add.add a b) n]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.NewtonBinom.newton_binom a b n)

    -- =========================================================================
    -- §7  Sum of binomial coefficients = 2^n
    -- =========================================================================

    /-- `Σ_{k≤n} C(n,k) = 2^n` at the Peano level, transported to ZFC. -/
    theorem sum_binom_eq_pow_two_peano (n : Peano.ℕ₀) :
        (fromPeano (Peano.NewtonBinom.finSum
          (fun k => Peano.Binom.binom n k) n) : U) =
        pow (σ (σ (∅ : U))) (fromPeano n) := by
      have h2 : (fromPeano (Peano.ℕ₀.succ (Peano.ℕ₀.succ Peano.ℕ₀.zero)) : U) =
          σ (σ (∅ : U)) := by simp only [fromPeano]
      rw [← h2, ← fromPeano_pow (Peano.ℕ₀.succ (Peano.ℕ₀.succ Peano.ℕ₀.zero)) n]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.NewtonBinom.sum_binom_eq_pow_two n)

    -- =========================================================================
    -- §8  Existential growth comparison
    -- =========================================================================

    /-- There exist `n, m ∈ ω` such that for all `k ∈ ω` with `1 ≤ k`:
        `(n + k)^m < n^(m + k)`. -/
    theorem exists_nm_growth_Omega :
        ∃ n m : U, n ∈ (ω : U) ∧ m ∈ (ω : U) ∧
        ∀ k : U, k ∈ (ω : U) → (σ (∅ : U)) ∈ k ∨ σ (∅ : U) = k →
        pow (add n k) m ∈ pow n (add m k) := by
      obtain ⟨pn, pm, h⟩ := Peano.NewtonBinom.exists_nm_growth
      refine ⟨fromPeano pn, fromPeano pm,
        Nat_in_Omega _ (fromPeano_is_nat pn),
        Nat_in_Omega _ (fromPeano_is_nat pm), ?_⟩
      intro k hk h1k
      obtain ⟨pk, hpk⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hpk
      have h_one : (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero) : U) = σ (∅ : U) := by
        simp only [fromPeano]
      rw [← fromPeano_add pn pk, ← fromPeano_pow (Peano.Add.add pn pk) pm,
          ← fromPeano_add pm pk, ← fromPeano_pow pn (Peano.Add.add pm pk)]
      exact (fromPeano_lt_iff
        (Peano.Pow.pow (Peano.Add.add pn pk) pm)
        (Peano.Pow.pow pn (Peano.Add.add pm pk))).mp
        (h pk (by
          rw [← h_one] at h1k
          exact (fromPeano_le_iff (Peano.ℕ₀.succ Peano.ℕ₀.zero) pk).mpr h1k))

  end Nat.NewtonBinom

  export Nat.NewtonBinom (
    -- §0: definition
    binomTermOf
    -- §1: closure
    binomTermOf_in_Omega
    -- §2: bridge
    fromPeano_binomTerm
    -- §3: concrete values
    binomTermOf_zero
    binomTermOf_self
    -- §4: expansion
    binomTermOf_eq
    -- §5: power splitting
    pow_add_split_Omega
    -- §6: Newton's binomial theorem
    newton_binom_peano
    -- §7: sum of binomial coefficients
    sum_binom_eq_pow_two_peano
    -- §8: growth comparison
    exists_nm_growth_Omega
  )

end ZFC
