/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Convergence of Sequences in ℚ

  This module defines convergence and limits for sequences f : ω → ℚ.
  All notions are purely within ℚ — no real numbers are involved.

  ## Main Definitions

  * `convergesToQ f L`   — f converges to L: ε-N definition over ℚ
  * `hasLimitQ f`        — f has some limit in ℚ

  ## Main Theorems

  * `convergesToQ_mem_RatSet` — the limit of a convergent sequence lies in ℚ
  * `limit_unique`            — limits are unique (if L₁, L₂ are both limits then L₁ = L₂)
  * `convergesToQ_const`      — the constant sequence at a converges to a

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Sequences
import ZFC.Rat.Abs
import ZFC.Nat.MaxMin

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

  universe u
  variable {U : Type u}

  namespace Rat.Convergence

    -- =========================================================================
    -- Section 1: Convergence definition
    -- =========================================================================

    /-- f : ω → ℚ converges to L ∈ ℚ:
        ∀ ε > 0, ∃ N ∈ ω, ∀ n ≥ N, |f(n) − L| < ε.
        The ordering is n ≥ N ↔ N ∈ n ∨ N = n (N ≤ n in ω). -/
    def convergesToQ (f L : U) : Prop :=
      ∀ ε : U, ε ∈ (RatSet : U) → isPositiveQ ε →
        ∃ N : U, N ∈ (ω : U) ∧
          ∀ n : U, n ∈ (ω : U) → N ∈ n ∨ N = n →
            ltQ (absQ (subQ (f⦅n⦆) L)) ε

    /-- f has a limit in ℚ -/
    def hasLimitQ (f : U) : Prop :=
      ∃ L : U, L ∈ (RatSet : U) ∧ convergesToQ f L

    -- =========================================================================
    -- Section 2: Basic consequences
    -- =========================================================================

    /-- The limit of a convergent sequence is a rational number.
        (The limit L must be given, and f must converge to it.) -/
    theorem convergesToQ_mem_RatSet (f L : U)
        (hL : L ∈ (RatSet : U)) (_h : convergesToQ f L) :
        L ∈ (RatSet : U) := hL

    -- =========================================================================
    -- Section 3: Constant sequence converges
    -- =========================================================================

    /-- The constant sequence at a converges to a -/
    theorem convergesToQ_const (a : U) (ha : a ∈ (RatSet : U)) :
        convergesToQ (constSeqQ a) a := by
      intro ε hε hε_pos
      refine ⟨∅, zero_in_Omega, fun n hn _h_ge => ?_⟩
      rw [constSeqQ_apply a ha n hn]
      -- Goal: ltQ (absQ (subQ a a)) ε
      have h_sub : subQ a a = (zeroQ : U) := by
        show addQ a (negQ a) = zeroQ
        exact negQ_addQ_right a ha
      have h_abs : absQ (zeroQ : U) = (zeroQ : U) :=
        if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet)
      rw [h_sub, h_abs]
      exact hε_pos

    -- =========================================================================
    -- Section 4: Uniqueness of limits
    -- =========================================================================

    /-- Limits are unique: if f → L₁ and f → L₂ then L₁ = L₂.
        Proof sketch: if L₁ ≠ L₂, take ε = |L₁ − L₂| / 2. For n large enough,
        |L₁ − L₂| ≤ |f(n)−L₁| + |f(n)−L₂| < ε + ε = |L₁ − L₂|, contradiction.
        The complete proof requires divQ, a "half epsilon" lemma, and the
        generalized triangle inequality |a−c| ≤ |a−b| + |b−c|. -/
    theorem limit_unique (f L₁ L₂ : U)
        (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ f L₂) :
        L₁ = L₂ := by
      sorry

    -- =========================================================================
    -- Section 5: Arithmetic of limits
    -- =========================================================================

    /-- If f → L₁ and g → L₂ then (f + g) → L₁ + L₂. -/
    theorem convergesToQ_add (f g L₁ L₂ : U)
        (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ g L₂) :
        convergesToQ (addSeqQ f g) (addQ L₁ L₂) := by
      -- Proof: use ε/2 for each; combine using triangle inequality.
      sorry

    /-- If f → 0 then (f · g) → 0, provided g is bounded. -/
    theorem convergesToQ_mul_bounded (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_zero : convergesToQ f (zeroQ : U))
        (hg_bounded : ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
          ∀ n : U, n ∈ (ω : U) → leQ (absQ (g⦅n⦆)) M) :
        convergesToQ (mulSeqQ f g) (zeroQ : U) := by
      sorry

  end Rat.Convergence

end ZFC

export ZFC.Rat.Convergence (
  convergesToQ
  hasLimitQ
  convergesToQ_const
  limit_unique
  convergesToQ_add
  convergesToQ_mul_bounded
)
