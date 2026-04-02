/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Factorial on Von Neumann Natural Numbers

  This module defines the factorial function on ω (the Von Neumann naturals)
  and proves it is isomorphic to Peano factorial via the bijection ΠZ/ZΠ defined in PeanoImport.lean.

  ## Strategy (Pattern B: bridge-only)

  Since factorial is defined by primitive recursion on the Peano structure
  (`factorial 0 = 1`, `factorial (σ n) = factorial n * (σ n)`), we lift
  the Peano definition directly via the isomorphism:

    `factorialOf n := fromPeano (Peano.Factorial.factorial (toPeano n _))`

  The bridge theorem `fromPeano_factorial` shows this agrees with Peano's factorial.

  ## Main Results

  - `factorialOf_zero`:    factorialOf ∅ = σ ∅  (0! = 1)
  - `factorialOf_succ`:    factorialOf (σ n) = mul (factorialOf n) (σ n)  ((n+1)! = n! * (n+1))
  - `factorialOf_ne_zero`: factorialOf n ≠ ∅  (n! ≠ 0)
  - `factorialOf_pos`:     ∅ ∈ factorialOf n  (0 < n!)
  - `factorialOf_ge_one`:  σ ∅ ∈ factorialOf n ∨ σ ∅ = factorialOf n  (1 ≤ n!)
  - `factorialOf_le_mono`: m ≤ n → factorialOf m ≤ factorialOf n
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Mul
import PeanoNatLib.PeanoNatFactorial

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
  -- Note: Peano.Import is NOT opened here to avoid ΠZ notation ambiguity.
  -- All Peano.Import exports are available at ZFC level.

  universe u
  variable {U : Type u}

  namespace Nat.Factorial

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `IsNat n`. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : IsNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    -- =========================================================================
    -- Section 0: Definition
    -- =========================================================================

    /-- `factorialOf n = n!` in ω, lifted from Peano via the isomorphism.
        Returns `∅` if `n ∉ ω`. -/
    noncomputable def factorialOf (n : U) : U :=
      if hn : n ∈ (ω : U) then
        fromPeano (Peano.Factorial.factorial (toPeano n (mem_Omega_is_Nat n hn)))
      else ∅

    -- =========================================================================
    -- Section 1: Closure in ω
    -- =========================================================================

    /-- The factorial of a natural number is a natural number. -/
    theorem factorialOf_in_Omega (n : U) (hn : n ∈ (ω : U)) :
        factorialOf n ∈ (ω : U) := by
      simp only [factorialOf, dif_pos hn]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- Section 2: Bridge theorem
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with factorial.
        `fromPeano (factorial p) = factorialOf (fromPeano p)`. -/
    theorem fromPeano_factorial (p : Peano.ℕ₀) :
        (fromPeano (Peano.Factorial.factorial p) : U) =
        factorialOf (fromPeano p) := by
      simp only [factorialOf, dif_pos (Nat_in_Omega _ (fromPeano_is_nat p))]
      exact congrArg Peano.Factorial.factorial
              ((toPeano_proof_irrel _
                  (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
        |> congrArg (fromPeano : Peano.ℕ₀ → U)

    -- =========================================================================
    -- Section 3: Concrete values
    -- =========================================================================

    /-- `0! = 1` in ω. -/
    theorem factorialOf_zero : factorialOf (∅ : U) = σ (∅ : U) := by
      simp only [factorialOf, dif_pos zero_in_Omega]
      rw [show toPeano (∅ : U) (mem_Omega_is_Nat ∅ zero_in_Omega) = Peano.ℕ₀.zero from
              (toPeano_proof_irrel ∅ _ _).trans toPeano_zero,
          Peano.Factorial.factorial_zero]
      rfl

    /-- `(σ n)! = n! * (σ n)` for `n ∈ ω`. -/
    theorem factorialOf_succ (n : U) (hn : n ∈ (ω : U)) :
        factorialOf (Nat.Basic.succ n) =
        mul (factorialOf n) (Nat.Basic.succ n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h_succ : (fromPeano (Peano.ℕ₀.succ p) : U) =
          Nat.Basic.succ (fromPeano p) := by simp only [fromPeano]
      rw [← h_succ, ← fromPeano_factorial, Peano.Factorial.factorial_succ,
          fromPeano_mul, fromPeano_factorial]

    /-- `1! = 1` in ω. -/
    theorem factorialOf_one : factorialOf (σ (∅ : U)) = σ (∅ : U) := by
      rw [factorialOf_succ ∅ zero_in_Omega, factorialOf_zero]
      exact mul_one_Omega (σ (∅ : U)) (succ_in_Omega ∅ zero_in_Omega)

    /-- `2! = 2` in ω. -/
    theorem factorialOf_two :
        factorialOf (σ (σ (∅ : U))) = σ (σ (∅ : U)) := by
      rw [factorialOf_succ (σ (∅ : U)) (succ_in_Omega ∅ zero_in_Omega), factorialOf_one]
      exact one_mul_Omega (σ (σ (∅ : U)))
              (succ_in_Omega (σ (∅ : U)) (succ_in_Omega ∅ zero_in_Omega))

    -- =========================================================================
    -- Section 4: Positivity and bounds
    -- =========================================================================

    /-- `n! ≠ ∅` for all `n ∈ ω`. -/
    theorem factorialOf_ne_zero (n : U) (hn : n ∈ (ω : U)) :
        factorialOf n ≠ ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_factorial]
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      intro heq
      exact Peano.Factorial.factorial_ne_zero p
        (fromPeano_injective (heq.trans h0.symm))

    /-- `∅ ∈ n!` (i.e., `0 < n!`) for all `n ∈ ω`. -/
    theorem factorialOf_pos (n : U) (hn : n ∈ (ω : U)) :
        (∅ : U) ∈ factorialOf n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_factorial]
      have h0 : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by simp only [fromPeano]
      rw [← h0]
      exact (fromPeano_lt_iff Peano.ℕ₀.zero (Peano.Factorial.factorial p)).mp
        (Peano.Factorial.factorial_pos p)

    /-- `σ ∅ ∈ n! ∨ σ ∅ = n!` (i.e., `1 ≤ n!`) for all `n ∈ ω`. -/
    theorem factorialOf_ge_one (n : U) (hn : n ∈ (ω : U)) :
        σ (∅ : U) ∈ factorialOf n ∨ σ (∅ : U) = factorialOf n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      rw [← fromPeano_factorial]
      have h1 : (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero) : U) = σ (∅ : U) := by
        simp only [fromPeano]
      rw [← h1]
      exact (fromPeano_le_iff (Peano.ℕ₀.succ Peano.ℕ₀.zero)
              (Peano.Factorial.factorial p)).mp
        (Peano.Factorial.factorial_ge_one p)

    /-- `n! ∈ (σ n)! ∨ n! = (σ n)!` (i.e., `n! ≤ (n+1)!`) for all `n ∈ ω`. -/
    theorem factorialOf_le_succ (n : U) (hn : n ∈ (ω : U)) :
        factorialOf n ∈ factorialOf (Nat.Basic.succ n) ∨
        factorialOf n = factorialOf (Nat.Basic.succ n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp
      have h_succ : (fromPeano (Peano.ℕ₀.succ p) : U) =
          Nat.Basic.succ (fromPeano p) := by simp only [fromPeano]
      rw [← fromPeano_factorial p, ← h_succ, ← fromPeano_factorial (Peano.ℕ₀.succ p)]
      exact (fromPeano_le_iff
              (Peano.Factorial.factorial p)
              (Peano.Factorial.factorial (Peano.ℕ₀.succ p))).mp
        (Peano.Factorial.factorial_le_succ p)

    /-- `m ≤ n → m! ≤ n!` (monotonicity) for `m n ∈ ω`. -/
    theorem factorialOf_le_mono {m n : U} (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_le : m ∈ n ∨ m = n) :
        factorialOf m ∈ factorialOf n ∨ factorialOf m = factorialOf n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_factorial p, ← fromPeano_factorial q]
      exact (fromPeano_le_iff
              (Peano.Factorial.factorial p)
              (Peano.Factorial.factorial q)).mp
        (Peano.Factorial.factorial_le_mono
          ((fromPeano_le_iff p q).mpr h_le))

  end Nat.Factorial

  export Nat.Factorial (
    -- Section 0: definition
    factorialOf
    -- Section 1: closure
    factorialOf_in_Omega
    -- Section 2: bridge
    fromPeano_factorial
    -- Section 3: concrete values
    factorialOf_zero
    factorialOf_one
    factorialOf_two
    factorialOf_succ
    -- Section 4: positivity and bounds
    factorialOf_ne_zero
    factorialOf_pos
    factorialOf_ge_one
    factorialOf_le_succ
    factorialOf_le_mono
  )

end ZFC
