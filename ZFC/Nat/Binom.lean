/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Binomial Coefficients on Von Neumann Natural Numbers

  This module defines binomial coefficients C(n, k) on ω (the Von Neumann naturals)
  via Pattern B (bridge-only), lifting the Peano definition from `PeanoNatBinom`.

  ## Strategy (Pattern B: bridge-only)

  Since binomial coefficients are defined by Pascal's recursion on the Peano structure
  (`C(0,0)=1`, `C(0,σk)=0`, `C(σn,0)=1`, `C(σn,σk)=C(n,k)+C(n,σk)`), we lift
  the Peano definition directly via the isomorphism:

    `binomOf n k := fromPeano (Peano.Binom.binom (toPeano n _) (toPeano k _))`

  The bridge theorem `fromPeano_binom` shows this agrees with Peano's binom.

  ## Main Results

  - `binomOf_zero_zero`:      C(∅, ∅) = σ ∅        (C(0,0) = 1)
  - `binomOf_succ_zero`:      C(σ n, ∅) = σ ∅      (C(n+1,0) = 1)
  - `binomOf_zero_succ`:      C(∅, σ k) = ∅        (C(0,k+1) = 0)
  - `binomOf_pascal`:          C(σ n, σ k) = C(n, k) + C(n, σ k)  (Pascal's rule)
  - `binomOf_n_zero`:          C(n, ∅) = σ ∅        (C(n,0) = 1)
  - `binomOf_n_one`:           C(n, σ ∅) = n        (C(n,1) = n)
  - `binomOf_self`:            C(n, n) = σ ∅        (C(n,n) = 1)
  - `binomOf_succ_n_by_n`:    C(σ n, n) = σ n      (C(n+1,n) = n+1)
  - `binomOf_eq_zero_of_gt`:  n ∈ k → C(n, k) = ∅  (n < k → C(n,k) = 0)
  - `binomOf_pos`:             k ≤ n → ∅ ∈ C(n, k)  (k ≤ n → 0 < C(n,k))
  - `binomOf_mul_factorials`:  C(n,k) · k! · (n−k)! = n!

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Nat.Basic
import ZFC.Axiom.Infinity
import ZFC.Peano.Import
import ZFC.Nat.Add
import ZFC.Nat.Mul
import ZFC.Nat.Sub
import ZFC.Nat.Factorial
import PeanoNatLib.PeanoNatBinom

namespace ZFC
  open Classical

  universe u
  variable {U : Type u}

  namespace Nat.Binom

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `IsNat n`. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : IsNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    -- =========================================================================
    -- §0  Definition
    -- =========================================================================

    /-- `binomOf n k = C(n, k)` in ω, lifted from Peano via the isomorphism.
        Returns `∅` if `n ∉ ω` or `k ∉ ω`. -/
    noncomputable def binomOf (n k : U) : U :=
      if hn : n ∈ (ω : U) then
        if hk : k ∈ (ω : U) then
          fromPeano (Peano.Binom.binom
            (toPeano n (mem_Omega_is_Nat n hn))
            (toPeano k (mem_Omega_is_Nat k hk)))
        else ∅
      else ∅

    -- =========================================================================
    -- §1  Closure in ω
    -- =========================================================================

    /-- The binomial coefficient of two natural numbers is a natural number. -/
    theorem binomOf_in_Omega (n k : U) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        binomOf n k ∈ (ω : U) := by
      simp only [binomOf, dif_pos hn, dif_pos hk]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- §2  Bridge theorem
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with binomial coefficients.
        `fromPeano (binom p q) = binomOf (fromPeano p) (fromPeano q)`. -/
    theorem fromPeano_binom (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Binom.binom p q) : U) =
        binomOf (fromPeano p) (fromPeano q) := by
      simp only [binomOf,
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
    -- §3  Concrete values
    -- =========================================================================

    /-- `C(0, 0) = 1` in ω. -/
    theorem binomOf_zero_zero : binomOf (∅ : U) ∅ = σ (∅ : U) := by
      simp only [binomOf, dif_pos zero_in_Omega]
      have h0 : toPeano (∅ : U) (mem_Omega_is_Nat ∅ zero_in_Omega) = Peano.ℕ₀.zero :=
        (toPeano_proof_irrel ∅ _ _).trans toPeano_zero
      rw [h0, Peano.Binom.binom_zero_zero]
      rfl

    /-- `C(σ n, 0) = 1` for `n ∈ ω`. -/
    theorem binomOf_succ_zero (n : U) (hn : n ∈ (ω : U)) :
        binomOf (σ n) ∅ = σ (∅ : U) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h_succ : (fromPeano (Peano.ℕ₀.succ p) : U) =
          Nat.Basic.succ (fromPeano p) := by simp only [fromPeano]
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h_succ, ← h0, ← fromPeano_binom, Peano.Binom.binom_succ_zero]
      rfl

    /-- `C(0, σ k) = 0` for `k ∈ ω`. -/
    theorem binomOf_zero_succ (k : U) (hk : k ∈ (ω : U)) :
        binomOf (∅ : U) (σ k) = ∅ := by
      obtain ⟨q, hq⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hq
      have h_succ : (fromPeano (Peano.ℕ₀.succ q) : U) =
          Nat.Basic.succ (fromPeano q) := by simp only [fromPeano]
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h_succ, ← h0, ← fromPeano_binom, Peano.Binom.binom_zero_succ]

    -- =========================================================================
    -- §4  Pascal's rule
    -- =========================================================================

    /-- **Pascal's rule**: `C(σ n, σ k) = C(n, k) + C(n, σ k)` for `n, k ∈ ω`. -/
    theorem binomOf_pascal (n k : U) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        binomOf (σ n) (σ k) =
        add (binomOf n k) (binomOf n (σ k)) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq
      have h_succ_p : (fromPeano (Peano.ℕ₀.succ p) : U) =
          Nat.Basic.succ (fromPeano p) := by simp only [fromPeano]
      have h_succ_q : (fromPeano (Peano.ℕ₀.succ q) : U) =
          Nat.Basic.succ (fromPeano q) := by simp only [fromPeano]
      rw [← h_succ_p, ← h_succ_q,
          ← fromPeano_binom (Peano.ℕ₀.succ p) (Peano.ℕ₀.succ q),
          ← fromPeano_binom p q,
          ← fromPeano_binom p (Peano.ℕ₀.succ q),
          Peano.Binom.binom_pascal, fromPeano_add]

    -- =========================================================================
    -- §5  Algebraic properties
    -- =========================================================================

    /-- `C(n, 0) = 1` for `n ∈ ω`. -/
    theorem binomOf_n_zero (n : U) (hn : n ∈ (ω : U)) :
        binomOf n ∅ = σ (∅ : U) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0, ← fromPeano_binom, Peano.Binom.binom_n_zero]
      rfl

    /-- `C(n, 1) = n` for `n ∈ ω`. -/
    theorem binomOf_n_one (n : U) (hn : n ∈ (ω : U)) :
        binomOf n (σ (∅ : U)) = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h_one : (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero) : U) = σ (∅ : U) := by
        simp only [fromPeano]
      rw [← h_one, ← fromPeano_binom]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Binom.binom_n_one p)

    /-- `C(n, n) = 1` for `n ∈ ω`. -/
    theorem binomOf_self (n : U) (hn : n ∈ (ω : U)) :
        binomOf n n = σ (∅ : U) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_binom, Peano.Binom.binom_self]
      rfl

    /-- `C(σ n, n) = σ n` for `n ∈ ω`. -/
    theorem binomOf_succ_n_by_n (n : U) (hn : n ∈ (ω : U)) :
        binomOf (σ n) n = σ n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h_succ : (fromPeano (Peano.ℕ₀.succ p) : U) =
          Nat.Basic.succ (fromPeano p) := by simp only [fromPeano]
      rw [← h_succ, ← fromPeano_binom, Peano.Binom.binom_succ_n_by_n]

    -- =========================================================================
    -- §6  Vanishing and positivity
    -- =========================================================================

    /-- `C(n, k) = 0` when `n < k` (i.e., `n ∈ k`) for `n, k ∈ ω`. -/
    theorem binomOf_eq_zero_of_gt {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h : n ∈ k) : binomOf n k = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq
      rw [← fromPeano_binom,
          Peano.Binom.binom_eq_zero_of_gt ((fromPeano_lt_iff p q).mpr h)]
      rfl

    /-- `0 < C(n, k)` (i.e., `∅ ∈ C(n, k)`) when `k ≤ n` for `n, k ∈ ω`. -/
    theorem binomOf_pos {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h : k ∈ n ∨ k = n) : (∅ : U) ∈ binomOf n k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq
      rw [← fromPeano_binom]
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0]
      exact (fromPeano_lt_iff Peano.ℕ₀.zero (Peano.Binom.binom p q)).mp
        (Peano.Binom.binom_pos ((fromPeano_le_iff q p).mpr h))

    -- =========================================================================
    -- §7  Factorial connection
    -- =========================================================================

    /-- `C(n, k) · k! · (n − k)! = n!` for `k ≤ n` in ω. -/
    theorem binomOf_mul_factorials {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h_le : k ∈ n ∨ k = n) :
        mul (mul (binomOf n k) (factorialOf k)) (factorialOf (sub n k)) =
        factorialOf n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨q, hq⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq
      rw [← fromPeano_binom p q,
          ← fromPeano_factorial q,
          ← fromPeano_sub p q,
          ← fromPeano_factorial (Peano.Sub.sub p q),
          ← fromPeano_mul (Peano.Binom.binom p q) (Peano.Factorial.factorial q),
          ← fromPeano_mul
              (Peano.Mul.mul (Peano.Binom.binom p q) (Peano.Factorial.factorial q))
              (Peano.Factorial.factorial (Peano.Sub.sub p q)),
          ← fromPeano_factorial p]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
        (Peano.Binom.binom_mul_factorials ((fromPeano_le_iff q p).mpr h_le))

  end Nat.Binom

  export Nat.Binom (
    -- §0: definition
    binomOf
    -- §1: closure
    binomOf_in_Omega
    -- §2: bridge
    fromPeano_binom
    -- §3: concrete values
    binomOf_zero_zero
    binomOf_succ_zero
    binomOf_zero_succ
    -- §4: Pascal's rule
    binomOf_pascal
    -- §5: algebraic properties
    binomOf_n_zero
    binomOf_n_one
    binomOf_self
    binomOf_succ_n_by_n
    -- §6: vanishing and positivity
    binomOf_eq_zero_of_gt
    binomOf_pos
    -- §7: factorial connection
    binomOf_mul_factorials
  )

end ZFC
