/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Multiplication on Von Neumann Natural Numbers

  This module defines multiplication on ω (the Von Neumann naturals) via the Recursion Theorem
  and proves it is isomorphic to Peano multiplication via the bijection ΠZ/ZΠ defined in
  PeanoImport.lean.

  ## Strategy

  Fix m ∈ ω. Define `mulFn m hm := RecursiveFn ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)`,
  so that `mulFn m hm : ω → ω` satisfies:
    - (mulFn m hm)(∅) = ∅
    - (mulFn m hm)(σ n) = m + (mulFn m hm)(n)

  That is: `mul m ∅ = ∅` and `mul m (σ n) = add m (mul m n)`.

  Then `mul m n := if h : m ∈ ω then apply (mulFn m h) n else ∅`.

  ## Bridge Theorem

  The central result `fromPeano_mul` states:
    fromPeano (Peano.Mul.mul p q) = mul (fromPeano p) (fromPeano q)

  Note: Peano defines `mul n (σ m) = add (mul n m) n`, so the bridge proof uses
  `add_comm_Omega` in the inductive step.
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Add
import PeanoNatLib.PeanoNatMul

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

  namespace Nat.Mul

    -- =========================================================================
    -- Section 1: Multiplication on ω
    -- =========================================================================

    /-- `mulFn m hm` is the ZFC function ω → ω that computes `m * ·`.
        Constructed via the Recursion Theorem with base `∅` and step `addFn m hm`
        (so each successor step adds `m`). -/
    noncomputable def mulFn (m : U) (hm : m ∈ (ω : U)) : U :=
      RecursiveFn ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)

    /-- `mulFn m hm` is a function from ω to ω. -/
    theorem mulFn_is_function (m : U) (hm : m ∈ (ω : U)) :
        isFunctionFromTo (mulFn m hm) ω ω :=
      RecursiveFn_is_function ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)

    /-- `mul m n` = `m * n` in ZFC.
        Defined without a proof argument (defaults to ∅ when m ∉ ω) so that
        rewrites in algebraic laws avoid dependent-type issues. -/
    noncomputable def mul (m n : U) : U :=
      if h : m ∈ (ω : U) then apply (mulFn m h) n else ∅

    /-- When `m ∈ ω`, `mul m n` unfolds to `apply (mulFn m hm) n`. -/
    theorem mul_eq (m n : U) (hm : m ∈ (ω : U)) :
        mul m n = apply (mulFn m hm) n := by
      simp only [mul, dif_pos hm]

    /-- `mul m n ∈ ω` for all `m n ∈ ω`. -/
    theorem mul_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mul m n ∈ ω := by
      rw [mul_eq m n hm]
      have hf := mulFn_is_function m hm
      have h_unique : ∃! y, ⟨n, y⟩ ∈ mulFn m hm := hf.2 n hn
      have h_pair_in : ⟨n, apply (mulFn m hm) n⟩ ∈ mulFn m hm :=
        apply_mem (mulFn m hm) n h_unique
      have h_sub : ∀ p, p ∈ mulFn m hm → p ∈ (ω ×ₛ ω : U) := hf.1
      have h_in_prod : ⟨n, apply (mulFn m hm) n⟩ ∈ (ω ×ₛ ω : U) := h_sub _ h_pair_in
      exact ((OrderedPair_mem_CartesianProduct n (apply (mulFn m hm) n) ω ω).mp h_in_prod).2

    -- =========================================================================
    -- Section 2: Basic recursion equations for mul
    -- =========================================================================

    /-- `mul m ∅ = ∅` (zero is the right annihilator). -/
    theorem mul_zero (m : U) (hm : m ∈ (ω : U)) :
        mul m ∅ = ∅ := by
      simp only [mul, dif_pos hm, mulFn]
      exact RecursiveFn_zero ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)

    /-- `mul m (σ n) = add m (mul m n)` for `m n ∈ ω`. -/
    theorem mul_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mul m (σ n) = add m (mul m n) := by
      simp only [mul, dif_pos hm, mulFn]
      rw [RecursiveFn_succ ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm) n hn]
      exact (add_eq m _ hm).symm

    -- =========================================================================
    -- Section 3: Bridge theorem — fromPeano commutes with multiplication
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with multiplication.
        `fromPeano (Peano.Mul.mul p q) = mul (fromPeano p) (fromPeano q)`.

        Proof: induction on `q`. The base uses `mul_zero`; the step uses `mul_succ`
        and `add_comm_Omega` (since Peano's `mul_succ` gives `mul n (σ m) = (mul n m) + n`
        while our ZFC `mul_succ` gives `mul m (σ n) = m + mul m n`). -/
    theorem fromPeano_mul (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Mul.mul p q) : U) =
        mul (fromPeano p) (fromPeano q) := by
      induction q with
      | zero =>
        rw [Peano.Mul.mul_zero]
        exact (mul_zero _ (Nat_in_Omega _ (fromPeano_is_nat p))).symm
      | succ q' ih =>
        rw [Peano.Mul.mul_succ]  -- mul p (σ q') = add (mul p q') p
        rw [fromPeano_add (Peano.Mul.mul p q') p]
        -- Goal: add (fromPeano (mul p q')) (fromPeano p) = mul (fromPeano p) (σ (fromPeano q'))
        rw [ih]
        -- Goal: add (mul (fromPeano p) (fromPeano q')) (fromPeano p) = mul (fromPeano p) (σ (fromPeano q'))
        show add (mul (fromPeano p : U) (fromPeano q' : U)) (fromPeano p : U) =
             mul (fromPeano p : U) (successor (fromPeano q' : U))
        rw [mul_succ (fromPeano p : U) (fromPeano q' : U)
                     (Nat_in_Omega _ (fromPeano_is_nat p))
                     (Nat_in_Omega _ (fromPeano_is_nat q'))]
        -- Goal: add (mul (fromPeano p) (fromPeano q')) (fromPeano p) = add (fromPeano p) (mul (fromPeano p) (fromPeano q'))
        exact add_comm_Omega _ _
                (mul_in_Omega (fromPeano p) (fromPeano q')
                   (Nat_in_Omega _ (fromPeano_is_nat p))
                   (Nat_in_Omega _ (fromPeano_is_nat q')))
                (Nat_in_Omega _ (fromPeano_is_nat p))

    -- =========================================================================
    -- Section 4: Algebraic properties lifted from Peano
    -- =========================================================================

    /-- `∅ * n = ∅` (zero is the left annihilator), lifted from Peano. -/
    theorem zero_mul_Omega (n : U) (hn : n ∈ (ω : U)) :
        mul ∅ n = ∅ := by
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hq
      change mul (fromPeano Peano.ℕ₀.zero) (fromPeano q) = fromPeano Peano.ℕ₀.zero
      rw [← fromPeano_mul Peano.ℕ₀.zero q, Peano.Mul.zero_mul]

    /-- Multiplication on ω is commutative, lifted from Peano. -/
    theorem mul_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mul m n = mul n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have hlhs : mul (fromPeano p : U) (fromPeano q : U) =
                  (fromPeano (Peano.Mul.mul p q) : U) :=
        (fromPeano_mul p q).symm
      have hrhs : mul (fromPeano q : U) (fromPeano p : U) =
                  (fromPeano (Peano.Mul.mul q p) : U) :=
        (fromPeano_mul q p).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.mul_comm p q)

    /-- `mul (σ m) n = add (mul m n) n` (left-successor distributes), lifted from Peano. -/
    theorem succ_mul_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mul (σ m) n = add (mul m n) n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      show mul (successor (fromPeano p : U)) (fromPeano q : U) =
           add (mul (fromPeano p : U) (fromPeano q : U)) (fromPeano q : U)
      have hlhs : mul (successor (fromPeano p : U)) (fromPeano q : U) =
                  (fromPeano (Peano.Mul.mul (Peano.ℕ₀.succ p) q) : U) :=
        (fromPeano_mul (Peano.ℕ₀.succ p) q).symm
      have hrhs : add (mul (fromPeano p : U) (fromPeano q : U)) (fromPeano q : U) =
                  (fromPeano (Peano.Add.add (Peano.Mul.mul p q) q) : U) := by
        rw [← fromPeano_mul p q]
        exact (fromPeano_add (Peano.Mul.mul p q) q).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.succ_mul p q)

    /-- `mul m 1 = m` (one is the right identity), lifted from Peano. -/
    theorem mul_one_Omega (m : U) (hm : m ∈ (ω : U)) :
        mul m (σ (∅ : U)) = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp
      change mul (fromPeano p) (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)) = fromPeano p
      rw [← fromPeano_mul p (Peano.ℕ₀.succ Peano.ℕ₀.zero)]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.mul_one p)

    /-- `mul 1 m = m` (one is the left identity), lifted from Peano. -/
    theorem one_mul_Omega (m : U) (hm : m ∈ (ω : U)) :
        mul (σ (∅ : U)) m = m := by
      obtain ⟨q, hq⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hq
      change mul (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)) (fromPeano q) = fromPeano q
      rw [← fromPeano_mul (Peano.ℕ₀.succ Peano.ℕ₀.zero) q]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.one_mul q)

    /-- Multiplication on ω is associative: `mul (mul m n) k = mul m (mul n k)`,
        lifted from Peano. -/
    theorem mul_assoc_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : mul (mul m n) k = mul m (mul n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : mul (mul (fromPeano p : U) (fromPeano q : U)) (fromPeano r : U) =
                  (fromPeano (Peano.Mul.mul (Peano.Mul.mul p q) r) : U) := by
        rw [← fromPeano_mul p q]
        exact (fromPeano_mul (Peano.Mul.mul p q) r).symm
      have hrhs : mul (fromPeano p : U) (mul (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Mul.mul p (Peano.Mul.mul q r)) : U) := by
        rw [← fromPeano_mul q r]
        exact (fromPeano_mul p (Peano.Mul.mul q r)).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.mul_assoc q p r)

    /-- Left distributivity: `mul m (add n k) = add (mul m n) (mul m k)`,
        lifted from Peano. -/
    theorem mul_ldistr_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : mul m (add n k) = add (mul m n) (mul m k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : mul (fromPeano p : U) (add (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Mul.mul p (Peano.Add.add q r)) : U) := by
        rw [← fromPeano_add q r]
        exact (fromPeano_mul p (Peano.Add.add q r)).symm
      have hrhs : add (mul (fromPeano p : U) (fromPeano q : U))
                      (mul (fromPeano p : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Add.add (Peano.Mul.mul p q) (Peano.Mul.mul p r)) : U) := by
        rw [← fromPeano_mul p q, ← fromPeano_mul p r]
        exact (fromPeano_add (Peano.Mul.mul p q) (Peano.Mul.mul p r)).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.mul_ldistr p q r)

    /-- Right distributivity: `mul (add m n) k = add (mul m k) (mul n k)`,
        lifted from Peano. -/
    theorem mul_rdistr_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : mul (add m n) k = add (mul m k) (mul n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : mul (add (fromPeano p : U) (fromPeano q : U)) (fromPeano r : U) =
                  (fromPeano (Peano.Mul.mul (Peano.Add.add p q) r) : U) := by
        rw [← fromPeano_add p q]
        exact (fromPeano_mul (Peano.Add.add p q) r).symm
      have hrhs : add (mul (fromPeano p : U) (fromPeano r : U))
                      (mul (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Add.add (Peano.Mul.mul p r) (Peano.Mul.mul q r)) : U) := by
        rw [← fromPeano_mul p r, ← fromPeano_mul q r]
        exact (fromPeano_add (Peano.Mul.mul p r) (Peano.Mul.mul q r)).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Mul.mul_rdistr p q r)

  end Nat.Mul

  export Nat.Mul (
    -- Section 1: mul
    mulFn
    mulFn_is_function
    mul
    mul_eq
    mul_in_Omega
    -- Section 2: basic recursion equations
    mul_zero
    mul_succ
    -- Section 3: bridge
    fromPeano_mul
    -- Section 4: algebraic properties
    zero_mul_Omega
    mul_comm_Omega
    succ_mul_Omega
    mul_one_Omega
    one_mul_Omega
    mul_assoc_Omega
    mul_ldistr_Omega
    mul_rdistr_Omega
  )

end ZFC
