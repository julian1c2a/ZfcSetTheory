/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Cauchy Sequences in ℚ

  This module defines Cauchy sequences in ℚ and establishes their
  relationship with convergent sequences. The key facts are:
  (1) Every convergent sequence in ℚ is Cauchy.
  (2) Not every Cauchy sequence in ℚ converges — this is the
      incompleteness of ℚ, to be demonstrated in SqrtApprox.lean.

  ## Main Definitions

  * `IsCauchyQ f`  — f is a Cauchy sequence: ∀ ε>0, ∃ N, ∀ m,n ≥ N, |f(m)−f(n)| < ε

  ## Main Theorems

  * `cauchy_of_convergentQ` — every convergent sequence in ℚ is Cauchy
  * `cauchy_bounded`        — every Cauchy sequence in ℚ is bounded

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Convergence

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
  open ZFC.Nat.MaxMin
  open ZFC.Int.Basic
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Sequences
  open ZFC.Rat.Convergence

  universe u
  variable {U : Type u}

  namespace Rat.CauchyQ

    -- =========================================================================
    -- Section 1: Cauchy criterion
    -- =========================================================================

    /-- f : ω → ℚ is a Cauchy sequence:
        ∀ ε > 0, ∃ N ∈ ω, ∀ m,n ≥ N, |f(m) − f(n)| < ε.
        The ordering is m ≥ N ↔ N ∈ m ∨ N = m (N ≤ m in ω). -/
    def IsCauchyQ (f : U) : Prop :=
      ∀ ε : U, ε ∈ (RatSet : U) → isPositiveQ ε →
        ∃ N : U, N ∈ (ω : U) ∧
          ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) →
            N ∈ m ∨ N = m → N ∈ n ∨ N = n →
            ltQ (absQ (subQ (f⦅m⦆) (f⦅n⦆))) ε

    -- =========================================================================
    -- Section 2: Every convergent sequence is Cauchy
    -- =========================================================================

    /-- If f → L in ℚ then f is Cauchy.
        Proof sketch: for ε > 0, use ε/2 convergence to get N; then for m, n ≥ N:
        |f(m) − f(n)| ≤ |f(m)−L| + |L−f(n)| = |f(m)−L| + |f(n)−L| < ε/2 + ε/2 = ε.
        The complete proof requires a "half epsilon" lemma (divQ ε 2 > 0) and the
        generalized triangle inequality (|a−c| ≤ |a−b| + |b−c|). -/
    theorem cauchy_of_convergentQ (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (h_conv : convergesToQ f L) :
        IsCauchyQ f := by
      sorry

    -- =========================================================================
    -- Section 3: Every Cauchy sequence is bounded
    -- =========================================================================

    /-- Every Cauchy sequence is bounded: ∃ M > 0, ∀ n ∈ ω, |f(n)| ≤ M.
        Proof sketch: take ε = 1; get N with |f(m)−f(n)| < 1 for m,n ≥ N.
        Then M = max(|f(0)|, |f(1)|, ..., |f(N)|, |f(N)| + 1) bounds all terms.
        Requires finite maximum over a set of rationals, which needs more infrastructure. -/
    theorem cauchy_bounded (f : U)
        (hf : IsSeqQ f) (h_cauchy : IsCauchyQ f) :
        ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
          ∀ n : U, n ∈ (ω : U) → leQ (absQ (f⦅n⦆)) M := by
      sorry

    -- =========================================================================
    -- Section 4: Constant sequences are Cauchy
    -- =========================================================================

    /-- The constant sequence at a is Cauchy -/
    theorem constSeqQ_isCauchy (a : U) (ha : a ∈ (RatSet : U)) :
        IsCauchyQ (constSeqQ a) :=
      cauchy_of_convergentQ (constSeqQ a) a
        (constSeqQ_isSeqQ a ha) ha
        (convergesToQ_const a ha)

  end Rat.CauchyQ

end ZFC

export ZFC.Rat.CauchyQ (
  IsCauchyQ
  cauchy_of_convergentQ
  cauchy_bounded
  constSeqQ_isCauchy
)
