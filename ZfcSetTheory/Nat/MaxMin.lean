/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Maximum and Minimum on Von Neumann Natural Numbers

  This module defines `maxOf` and `minOf` on ω (the Von Neumann naturals)
  via Pattern B (bridge-only), lifting the Peano definitions from `PeanoNatMaxMin`.

  ## Strategy (Pattern B: bridge-only)

  Since max and min are defined by recursive pattern matching on the Peano structure,
  we lift the Peano definitions directly via the isomorphism:

    `maxOf n m := fromPeano (Peano.MaxMin.max (toPeano n _) (toPeano m _))`
    `minOf n m := fromPeano (Peano.MaxMin.min (toPeano n _) (toPeano m _))`

  The bridge theorems `fromPeano_max` and `fromPeano_min` show these agree
  with the Peano operations.

  ## Main Results

  - `maxOf_idem`, `minOf_idem`:           idempotence
  - `maxOf_comm`, `minOf_comm`:           commutativity
  - `maxOf_assoc`, `minOf_assoc`:         associativity
  - `maxOf_zero`, `minOf_zero`:           identity/annihilator with ∅
  - `le_maxOf_left`, `le_maxOf_right`:    max is an upper bound
  - `minOf_le_left`, `minOf_le_right`:    min is a lower bound
  - `maxOf_le`:                           max is the least upper bound
  - `le_minOf`:                           min is the greatest lower bound
  - `maxOf_eq_iff_le`, `minOf_eq_iff_le`: characterization via ≤
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Peano.Import
import PeanoNatLib.PeanoNatMaxMin

namespace SetUniverse
  open Classical

  universe u
  variable {U : Type u}

  namespace NaturalNumbersMaxMin

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `isNat n`. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : isNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    -- =========================================================================
    -- §0  Definitions
    -- =========================================================================

    /-- `maxOf n m = max(n, m)` in ω, lifted from Peano via the isomorphism.
        Returns `∅` if `n ∉ ω` or `m ∉ ω`. -/
    noncomputable def maxOf (n m : U) : U :=
      if hn : n ∈ (ω : U) then
        if hm : m ∈ (ω : U) then
          fromPeano (Peano.MaxMin.max
            (toPeano n (mem_Omega_is_Nat n hn))
            (toPeano m (mem_Omega_is_Nat m hm)))
        else ∅
      else ∅

    /-- `minOf n m = min(n, m)` in ω, lifted from Peano via the isomorphism.
        Returns `∅` if `n ∉ ω` or `m ∉ ω`. -/
    noncomputable def minOf (n m : U) : U :=
      if hn : n ∈ (ω : U) then
        if hm : m ∈ (ω : U) then
          fromPeano (Peano.MaxMin.min
            (toPeano n (mem_Omega_is_Nat n hn))
            (toPeano m (mem_Omega_is_Nat m hm)))
        else ∅
      else ∅

    -- =========================================================================
    -- §1  Closure in ω
    -- =========================================================================

    /-- The maximum of two natural numbers is a natural number. -/
    theorem maxOf_in_Omega (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        maxOf n m ∈ (ω : U) := by
      simp only [maxOf, dif_pos hn, dif_pos hm]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    /-- The minimum of two natural numbers is a natural number. -/
    theorem minOf_in_Omega (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        minOf n m ∈ (ω : U) := by
      simp only [minOf, dif_pos hn, dif_pos hm]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- §2  Bridge theorems
    -- =========================================================================

    /-- **Bridge theorem**: `fromPeano` commutes with `max`.
        `fromPeano (max p q) = maxOf (fromPeano p) (fromPeano q)`. -/
    theorem fromPeano_max (p q : Peano.ℕ₀) :
        (fromPeano (Peano.MaxMin.max p q) : U) =
        maxOf (fromPeano p) (fromPeano q) := by
      simp only [maxOf,
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat q)))
                  (fromPeano_is_nat q)).trans (toPeano_fromPeano q)).symm

    /-- **Bridge theorem**: `fromPeano` commutes with `min`.
        `fromPeano (min p q) = minOf (fromPeano p) (fromPeano q)`. -/
    theorem fromPeano_min (p q : Peano.ℕ₀) :
        (fromPeano (Peano.MaxMin.min p q) : U) =
        minOf (fromPeano p) (fromPeano q) := by
      simp only [minOf,
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
      · exact ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat q)))
                  (fromPeano_is_nat q)).trans (toPeano_fromPeano q)).symm

    -- =========================================================================
    -- §3  Idempotence
    -- =========================================================================

    /-- `max(n, n) = n` for `n ∈ ω`. -/
    theorem maxOf_idem (n : U) (hn : n ∈ (ω : U)) :
        maxOf n n = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_max, Peano.MaxMin.max_idem]

    /-- `min(n, n) = n` for `n ∈ ω`. -/
    theorem minOf_idem (n : U) (hn : n ∈ (ω : U)) :
        minOf n n = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_min, Peano.MaxMin.min_idem]

    -- =========================================================================
    -- §4  Commutativity
    -- =========================================================================

    /-- `max(n, m) = max(m, n)` for `n, m ∈ ω`. -/
    theorem maxOf_comm (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        maxOf n m = maxOf m n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max, ← fromPeano_max, Peano.MaxMin.max_comm]

    /-- `min(n, m) = min(m, n)` for `n, m ∈ ω`. -/
    theorem minOf_comm (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        minOf n m = minOf m n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min, ← fromPeano_min, Peano.MaxMin.min_comm]

    -- =========================================================================
    -- §5  Associativity
    -- =========================================================================

    /-- `max(max(n, m), k) = max(n, max(m, k))` for `n, m, k ∈ ω`. -/
    theorem maxOf_assoc (n m k : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        maxOf (maxOf n m) k = maxOf n (maxOf m k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_max p q, ← fromPeano_max q r,
          ← fromPeano_max (Peano.MaxMin.max p q) r,
          ← fromPeano_max p (Peano.MaxMin.max q r),
          Peano.MaxMin.max_assoc]

    /-- `min(min(n, m), k) = min(n, min(m, k))` for `n, m, k ∈ ω`. -/
    theorem minOf_assoc (n m k : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        minOf (minOf n m) k = minOf n (minOf m k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_min p q, ← fromPeano_min q r,
          ← fromPeano_min (Peano.MaxMin.min p q) r,
          ← fromPeano_min p (Peano.MaxMin.min q r),
          Peano.MaxMin.min_assoc]

    -- =========================================================================
    -- §6  Identity / Annihilator with ∅
    -- =========================================================================

    /-- `max(∅, n) = n` for `n ∈ ω`. -/
    theorem maxOf_zero_left (n : U) (hn : n ∈ (ω : U)) :
        maxOf (∅ : U) n = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_max, Peano.MaxMin.max_not_0]

    /-- `max(n, ∅) = n` for `n ∈ ω`. -/
    theorem maxOf_zero_right (n : U) (hn : n ∈ (ω : U)) :
        maxOf n (∅ : U) = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_max, Peano.MaxMin.max_0_not]

    /-- `min(∅, n) = ∅` for `n ∈ ω`. -/
    theorem minOf_zero_left (n : U) (hn : n ∈ (ω : U)) :
        minOf (∅ : U) n = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_min, Peano.MaxMin.min_abs_0]

    /-- `min(n, ∅) = ∅` for `n ∈ ω`. -/
    theorem minOf_zero_right (n : U) (hn : n ∈ (ω : U)) :
        minOf n (∅ : U) = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_min, Peano.MaxMin.min_0_abs]

    -- =========================================================================
    -- §7  Upper/Lower bound properties
    -- =========================================================================

    /-- `n ≤ max(n, m)` for `n, m ∈ ω`. -/
    theorem le_maxOf_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        n ∈ maxOf n m ∨ n = maxOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max]
      exact (fromPeano_le_iff p (Peano.MaxMin.max p q)).mp (Peano.MaxMin.le_max_left p q)

    /-- `m ≤ max(n, m)` for `n, m ∈ ω`. -/
    theorem le_maxOf_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        m ∈ maxOf n m ∨ m = maxOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max]
      exact (fromPeano_le_iff q (Peano.MaxMin.max p q)).mp (Peano.MaxMin.le_max_right p q)

    /-- `max(n, m) ≤ k` when `n ≤ k` and `m ≤ k`, for `n, m, k ∈ ω`. -/
    theorem maxOf_le (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h_n_le_k : n ∈ k ∨ n = k) (h_m_le_k : m ∈ k ∨ m = k) :
        maxOf n m ∈ k ∨ maxOf n m = k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_max]
      exact (fromPeano_le_iff (Peano.MaxMin.max p q) r).mp
        (Peano.MaxMin.max_le p q r
          ((fromPeano_le_iff p r).mpr h_n_le_k)
          ((fromPeano_le_iff q r).mpr h_m_le_k))

    /-- `min(n, m) ≤ n` for `n, m ∈ ω`. -/
    theorem minOf_le_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        minOf n m ∈ n ∨ minOf n m = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min]
      exact (fromPeano_le_iff (Peano.MaxMin.min p q) p).mp (Peano.MaxMin.min_le_left p q)

    /-- `min(n, m) ≤ m` for `n, m ∈ ω`. -/
    theorem minOf_le_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        minOf n m ∈ m ∨ minOf n m = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min]
      exact (fromPeano_le_iff (Peano.MaxMin.min p q) q).mp (Peano.MaxMin.min_le_right p q)

    /-- `k ≤ min(n, m)` when `k ≤ n` and `k ≤ m`, for `n, m, k ∈ ω`. -/
    theorem le_minOf (k n m : U) (hk : k ∈ (ω : U)) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_k_le_n : k ∈ n ∨ k = n) (h_k_le_m : k ∈ m ∨ k = m) :
        k ∈ minOf n m ∨ k = minOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq; subst hr
      rw [← fromPeano_min]
      exact (fromPeano_le_iff p (Peano.MaxMin.min q r)).mp
        (Peano.MaxMin.le_min p q r
          ((fromPeano_le_iff p q).mpr h_k_le_n)
          ((fromPeano_le_iff p r).mpr h_k_le_m))

    -- =========================================================================
    -- §8  Characterization via ≤
    -- =========================================================================

    /-- `max(n, m) = m` when `n ≤ m`, for `n, m ∈ ω`. -/
    theorem maxOf_eq_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_le : n ∈ m ∨ n = m) : maxOf n m = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.MaxMin.le_then_max_eq_right p q ((fromPeano_le_iff p q).mpr h_le))

    /-- `max(n, m) = n` when `m ≤ n`, for `n, m ∈ ω`. -/
    theorem maxOf_eq_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_le : m ∈ n ∨ m = n) : maxOf n m = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.MaxMin.le_then_max_eq_left p q ((fromPeano_le_iff q p).mpr h_le))

    /-- `min(n, m) = n` when `n ≤ m`, for `n, m ∈ ω`. -/
    theorem minOf_eq_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_le : n ∈ m ∨ n = m) : minOf n m = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.MaxMin.le_then_min_eq_left p q ((fromPeano_le_iff p q).mpr h_le))

    /-- `min(n, m) = m` when `m ≤ n`, for `n, m ∈ ω`. -/
    theorem minOf_eq_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_le : m ∈ n ∨ m = n) : minOf n m = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.MaxMin.le_then_min_eq_right p q ((fromPeano_le_iff q p).mpr h_le))

    -- =========================================================================
    -- §9  max/min is one of the arguments
    -- =========================================================================

    /-- `max(n, m) = n ∨ max(n, m) = m` for `n, m ∈ ω`. -/
    theorem maxOf_is_any (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        maxOf n m = n ∨ maxOf n m = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max]
      cases Peano.MaxMin.max_is_any p q with
      | inl h => left; exact congrArg (fromPeano : Peano.ℕ₀ → U) h
      | inr h => right; exact congrArg (fromPeano : Peano.ℕ₀ → U) h

    /-- `min(n, m) = n ∨ min(n, m) = m` for `n, m ∈ ω`. -/
    theorem minOf_is_any (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        minOf n m = n ∨ minOf n m = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_min]
      cases Peano.MaxMin.min_is_any p q with
      | inl h => left; exact congrArg (fromPeano : Peano.ℕ₀ → U) h
      | inr h => right; exact congrArg (fromPeano : Peano.ℕ₀ → U) h

    -- =========================================================================
    -- §10  max = min iff equal
    -- =========================================================================

    /-- `n = m ↔ max(n, m) = min(n, m)` for `n, m ∈ ω`. -/
    theorem eq_iff_maxOf_eq_minOf (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        n = m ↔ maxOf n m = minOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp; subst hq
      rw [← fromPeano_max, ← fromPeano_min]
      constructor
      · intro h
        have := (Peano.MaxMin.eq_then_eq_max_min p q (fromPeano_injective h))
        exact congrArg (fromPeano : Peano.ℕ₀ → U) this
      · intro h
        have := Peano.MaxMin.eq_max_min_then_eq p q (fromPeano_injective h)
        exact congrArg (fromPeano : Peano.ℕ₀ → U) this

  end NaturalNumbersMaxMin

  export NaturalNumbersMaxMin (
    -- §0: definitions
    maxOf
    minOf
    -- §1: closure
    maxOf_in_Omega
    minOf_in_Omega
    -- §2: bridge
    fromPeano_max
    fromPeano_min
    -- §3: idempotence
    maxOf_idem
    minOf_idem
    -- §4: commutativity
    maxOf_comm
    minOf_comm
    -- §5: associativity
    maxOf_assoc
    minOf_assoc
    -- §6: identity/annihilator with ∅
    maxOf_zero_left
    maxOf_zero_right
    minOf_zero_left
    minOf_zero_right
    -- §7: upper/lower bound
    le_maxOf_left
    le_maxOf_right
    maxOf_le
    minOf_le_left
    minOf_le_right
    le_minOf
    -- §8: characterization via ≤
    maxOf_eq_right
    maxOf_eq_left
    minOf_eq_left
    minOf_eq_right
    -- §9: max/min is one of the arguments
    maxOf_is_any
    minOf_is_any
    -- §10: max = min iff equal
    eq_iff_maxOf_eq_minOf
  )

end SetUniverse
