/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Exponentiation on Von Neumann Natural Numbers

  This module defines exponentiation on ω (the Von Neumann naturals) via the Recursion Theorem
  and proves it is isomorphic to Peano exponentiation via the bijection ΠZ/ZΠ defined in
  PeanoImport.lean.

  ## Strategy

  Fix m ∈ ω. Define `powFn m hm := RecursiveFn ω (σ (∅:U)) (mulFn m hm) one_in_omega (mulFn_is_function m hm)`,
  so that `powFn m hm : ω → ω` satisfies:
    - (powFn m hm)(∅)   = σ (∅:U)             -- m^0 = 1
    - (powFn m hm)(σ n) = m * (powFn m hm)(n)  -- m^(σn) = m * m^n  (left multiply)

  Then `pow m n := if h : m ∈ ω then apply (powFn m h) n else ∅`.

  ## Bridge Theorem

  The central result `fromPeano_pow` states:
    fromPeano (Peano.Pow.pow p q) = pow (fromPeano p) (fromPeano q)

  Note: Peano defines `pow n (σ m) = mul (pow n m) n` (right multiply), while our ZFC
  definition gives `pow m (σ n) = mul m (pow m n)` (left multiply). The bridge proof
  uses `mul_comm_Omega` in the inductive step, exactly as `fromPeano_mul` used
  `add_comm_Omega`.
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Add
import ZfcSetTheory.Nat.Mul
import PeanoNatLib.PeanoNatPow

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  open SetUniverse.NaturalNumbers
  open SetUniverse.InfinityAxiom
  -- Note: PeanoIsomorphism is NOT opened here to avoid ΠZ notation ambiguity.
  -- All PeanoIsomorphism exports are available at SetUniverse level.

  universe u
  variable {U : Type u}

  namespace NaturalNumbersPow

    -- =========================================================================
    -- Section 1: Exponentiation on ω
    -- =========================================================================

    /-- `powFn m hm` is the ZFC function ω → ω that computes `m ^ ·`.
        Constructed via the Recursion Theorem with base `σ (∅:U)` (= 1 in ZFC) and
        step `mulFn m hm` (so each successor step left-multiplies by `m`). -/
    noncomputable def powFn (m : U) (hm : m ∈ (ω : U)) : U :=
      RecursiveFn ω (σ (∅ : U)) (mulFn m hm)
        (succ_in_Omega (∅ : U) zero_in_Omega)
        (mulFn_is_function m hm)

    /-- `powFn m hm` is a function from ω to ω. -/
    theorem powFn_is_function (m : U) (hm : m ∈ (ω : U)) :
        isFunctionFromTo (powFn m hm) ω ω :=
      RecursiveFn_is_function ω (σ (∅ : U)) (mulFn m hm)
        (succ_in_Omega (∅ : U) zero_in_Omega)
        (mulFn_is_function m hm)

    /-- `pow m n` = `m ^ n` in ZFC.
        Defined without a proof argument (defaults to ∅ when m ∉ ω) so that
        rewrites in algebraic laws avoid dependent-type issues. -/
    noncomputable def pow (m n : U) : U :=
      if h : m ∈ (ω : U) then apply (powFn m h) n else ∅

    /-- When `m ∈ ω`, `pow m n` unfolds to `apply (powFn m hm) n`. -/
    theorem pow_eq (m n : U) (hm : m ∈ (ω : U)) :
        pow m n = apply (powFn m hm) n := by
      simp only [pow, dif_pos hm]

    /-- `pow m n ∈ ω` for all `m n ∈ ω`. -/
    theorem pow_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        pow m n ∈ ω := by
      rw [pow_eq m n hm]
      have hf := powFn_is_function m hm
      have h_unique : ∃! y, ⟨n, y⟩ ∈ powFn m hm := hf.2 n hn
      have h_pair_in : ⟨n, apply (powFn m hm) n⟩ ∈ powFn m hm :=
        apply_mem (powFn m hm) n h_unique
      have h_sub : ∀ p, p ∈ powFn m hm → p ∈ (ω ×ₛ ω : U) := hf.1
      have h_in_prod : ⟨n, apply (powFn m hm) n⟩ ∈ (ω ×ₛ ω : U) := h_sub _ h_pair_in
      exact ((OrderedPair_mem_CartesianProduct n (apply (powFn m hm) n) ω ω).mp h_in_prod).2

    -- =========================================================================
    -- Section 2: Basic recursion equations for pow
    -- =========================================================================

    /-- `pow m ∅ = σ (∅:U)` (m^0 = 1 in ZFC). -/
    theorem pow_zero (m : U) (hm : m ∈ (ω : U)) :
        pow m ∅ = σ (∅ : U) := by
      simp only [pow, dif_pos hm, powFn]
      exact RecursiveFn_zero ω (σ (∅ : U)) (mulFn m hm)
        (succ_in_Omega (∅ : U) zero_in_Omega) (mulFn_is_function m hm)

    /-- `pow m (σ n) = mul m (pow m n)` for `m n ∈ ω` (left multiply by m). -/
    theorem pow_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        pow m (σ n) = mul m (pow m n) := by
      simp only [pow, dif_pos hm, powFn]
      rw [RecursiveFn_succ ω (σ (∅ : U)) (mulFn m hm)
            (succ_in_Omega (∅ : U) zero_in_Omega) (mulFn_is_function m hm) n hn]
      exact (mul_eq m _ hm).symm

    -- =========================================================================
    -- Section 3: Bridge theorem — fromPeano commutes with exponentiation
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with exponentiation.
        `fromPeano (Peano.Pow.pow p q) = pow (fromPeano p) (fromPeano q)`.

        Proof: induction on `q`. The base uses `pow_zero`; the step uses `pow_succ`
        and `mul_comm_Omega` (since Peano's `pow_succ` gives `pow n (σ m) = (pow n m) * n`
        (right multiply) while our ZFC `pow_succ` gives `pow m (σ n) = m * pow m n`
        (left multiply)). -/
    theorem fromPeano_pow (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Pow.pow p q) : U) =
        pow (fromPeano p) (fromPeano q) := by
      induction q with
      | zero =>
        rw [Peano.Pow.pow_zero]
        exact (pow_zero _ (Nat_in_Omega _ (fromPeano_is_nat p))).symm
      | succ q' ih =>
        rw [Peano.Pow.pow_succ]  -- pow p (σ q') = mul (pow p q') p
        rw [fromPeano_mul (Peano.Pow.pow p q') p]
        -- Goal: mul (fromPeano (pow p q')) (fromPeano p) = pow (fromPeano p) (fromPeano (σ q'))
        rw [ih]
        -- Goal: mul (pow (fromPeano p) (fromPeano q')) (fromPeano p) =
        --       pow (fromPeano p) (successor (fromPeano q'))
        show mul (pow (fromPeano p : U) (fromPeano q' : U)) (fromPeano p : U) =
             pow (fromPeano p : U) (successor (fromPeano q' : U))
        rw [pow_succ (fromPeano p : U) (fromPeano q' : U)
                     (Nat_in_Omega _ (fromPeano_is_nat p))
                     (Nat_in_Omega _ (fromPeano_is_nat q'))]
        -- Goal: mul (pow (fromPeano p) (fromPeano q')) (fromPeano p) =
        --       mul (fromPeano p) (pow (fromPeano p) (fromPeano q'))
        exact mul_comm_Omega _ _
              (pow_in_Omega (fromPeano p) (fromPeano q')
                 (Nat_in_Omega _ (fromPeano_is_nat p))
                 (Nat_in_Omega _ (fromPeano_is_nat q')))
              (Nat_in_Omega _ (fromPeano_is_nat p))

    -- =========================================================================
    -- Section 4: Algebraic properties lifted from Peano
    -- =========================================================================

    /-- `pow ∅ n = ∅` (zero base with nonzero exponent), lifted from Peano. -/
    theorem zero_pow_Omega (n : U) (hn : n ∈ (ω : U)) (hn_ne : n ≠ (∅ : U)) :
        pow (∅ : U) n = ∅ := by
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hq
      have hq_ne : q ≠ Peano.ℕ₀.zero := fun heq => by subst heq; exact hn_ne rfl
      change pow (fromPeano Peano.ℕ₀.zero) (fromPeano q) = fromPeano Peano.ℕ₀.zero
      rw [← fromPeano_pow Peano.ℕ₀.zero q]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.zero_pow hq_ne)

    /-- `pow (σ (∅:U)) n = σ (∅:U)` (one raised to any power is one), lifted from Peano. -/
    theorem one_pow_Omega (n : U) (hn : n ∈ (ω : U)) :
        pow (σ (∅ : U)) n = σ (∅ : U) := by
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hq
      change pow (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)) (fromPeano q) =
             fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)
      rw [← fromPeano_pow (Peano.ℕ₀.succ Peano.ℕ₀.zero) q]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.one_pow q)

    /-- `pow m (σ (∅:U)) = m` (any base to the first power is itself), lifted from Peano. -/
    theorem pow_one_Omega (m : U) (hm : m ∈ (ω : U)) :
        pow m (σ (∅ : U)) = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp
      change pow (fromPeano p) (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)) = fromPeano p
      rw [← fromPeano_pow p (Peano.ℕ₀.succ Peano.ℕ₀.zero)]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.pow_one p)

    /-- `m ≠ ∅ → pow m n ≠ ∅` (nonzero base raised to any power is nonzero),
        lifted from Peano. -/
    theorem pow_ne_zero_Omega {m : U} (hm : m ∈ (ω : U)) (hm_ne : m ≠ (∅ : U))
        (n : U) (hn : n ∈ (ω : U)) : pow m n ≠ ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have hp_ne : p ≠ Peano.ℕ₀.zero := fun heq => by subst heq; exact hm_ne rfl
      rw [← fromPeano_pow p q]
      intro h_eq
      -- h_eq : (fromPeano (pow p q) : U) = ∅ = fromPeano 0 (definitionally)
      exact absurd (fromPeano_injective h_eq) (Peano.Pow.pow_ne_zero hp_ne q)

    /-- `pow m (σ (σ (∅:U))) = mul m m` (squaring), lifted from Peano. -/
    theorem pow_two_Omega (m : U) (hm : m ∈ (ω : U)) :
        pow m (σ (σ (∅ : U))) = mul m m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp
      change pow (fromPeano p) (fromPeano (Peano.ℕ₀.succ (Peano.ℕ₀.succ Peano.ℕ₀.zero))) =
             mul (fromPeano p) (fromPeano p)
      rw [← fromPeano_pow p (Peano.ℕ₀.succ (Peano.ℕ₀.succ Peano.ℕ₀.zero))]
      rw [← fromPeano_mul p p]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.pow_two p)

    /-- `pow m (add n k) = mul (pow m n) (pow m k)` (exponent addition = product of powers),
        lifted from Peano. -/
    theorem pow_add_eq_mul_pow_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : pow m (add n k) = mul (pow m n) (pow m k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : pow (fromPeano p : U) (add (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Pow.pow p (Peano.Add.add q r)) : U) := by
        rw [← fromPeano_add q r]
        exact (fromPeano_pow p (Peano.Add.add q r)).symm
      have hrhs : mul (pow (fromPeano p : U) (fromPeano q : U))
                      (pow (fromPeano p : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Mul.mul (Peano.Pow.pow p q) (Peano.Pow.pow p r)) : U) := by
        rw [← fromPeano_pow p q, ← fromPeano_pow p r]
        exact (fromPeano_mul (Peano.Pow.pow p q) (Peano.Pow.pow p r)).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.pow_add_eq_mul_pow p q r)

    /-- `mul (pow m n) (pow k n) = pow (mul m k) n` (product of powers = power of product),
        lifted from Peano. -/
    theorem mul_pow_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : mul (pow m n) (pow k n) = pow (mul m k) n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : mul (pow (fromPeano p : U) (fromPeano q : U))
                      (pow (fromPeano r : U) (fromPeano q : U)) =
                  (fromPeano (Peano.Mul.mul (Peano.Pow.pow p q) (Peano.Pow.pow r q)) : U) := by
        rw [← fromPeano_pow p q, ← fromPeano_pow r q]
        exact (fromPeano_mul (Peano.Pow.pow p q) (Peano.Pow.pow r q)).symm
      have hrhs : pow (mul (fromPeano p : U) (fromPeano r : U)) (fromPeano q : U) =
                  (fromPeano (Peano.Pow.pow (Peano.Mul.mul p r) q) : U) := by
        rw [← fromPeano_mul p r]
        exact (fromPeano_pow (Peano.Mul.mul p r) q).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
            (Peano.Pow.mul_pow_n_m_pow_k_m_eq_pow_nk_m p r q)

    /-- `pow (pow m n) k = pow m (mul n k)` (tower law / iterated exponentiation),
        lifted from Peano. -/
    theorem pow_pow_eq_pow_mul_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) : pow (pow m n) k = pow m (mul n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : pow (pow (fromPeano p : U) (fromPeano q : U)) (fromPeano r : U) =
                  (fromPeano (Peano.Pow.pow (Peano.Pow.pow p q) r) : U) := by
        rw [← fromPeano_pow p q]
        exact (fromPeano_pow (Peano.Pow.pow p q) r).symm
      have hrhs : pow (fromPeano p : U) (mul (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Pow.pow p (Peano.Mul.mul q r)) : U) := by
        rw [← fromPeano_mul q r]
        exact (fromPeano_pow p (Peano.Mul.mul q r)).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Pow.pow_pow_eq_pow_mul p q r)

  end NaturalNumbersPow

  export NaturalNumbersPow (
    -- Section 1: pow
    powFn
    powFn_is_function
    pow
    pow_eq
    pow_in_Omega
    -- Section 2: basic recursion equations
    pow_zero
    pow_succ
    -- Section 3: bridge
    fromPeano_pow
    -- Section 4: algebraic properties
    zero_pow_Omega
    one_pow_Omega
    pow_one_Omega
    pow_ne_zero_Omega
    pow_two_Omega
    pow_add_eq_mul_pow_Omega
    mul_pow_Omega
    pow_pow_eq_pow_mul_Omega
  )

end SetUniverse
