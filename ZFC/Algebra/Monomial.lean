/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Monomials over ℚ (Phase 8)

  A monomial is a term q·Xⁿ. Representation:
    * the zero monomial = `∅` (canonical sentinel: no Kuratowski pair `⟨n,q⟩` is `∅`);
    * a nonzero monomial = `⟨n, q⟩` with exponent `n ∈ ω` and coefficient `q ∈ ℚ`, `q ≠ 0`.

  The smart constructor `monomMk` normalizes a zero coefficient to the canonical zero.

  ## Degree: WithBot ω encoding

  The order-theoretic degree lives in a copy of `ℕ ∪ {−∞}` encoded inside `ω`:
    * `−∞  ↦  ∅`      (the bottom; degree of the zero monomial)
    * `n   ↦  σ n`     (finite degree `n`)
  so `monomDeg m₁ ≼ monomDeg m₂` is just `ω`'s membership order (`∅` below everything).
  The literal exponent used in evaluation is `monomExp` (junk `0` for the zero monomial,
  equal to `pred (monomDeg m)` on nonzero monomials).

  ## Main Definitions
  * `zeroMonom`, `monomMk`, `IsMonom`, `IsZeroMonom`
  * `monomCoeff`, `monomExp`, `monomDeg`, `monomEval`

  ## Main Theorems
  * `monomMk_isMonom`, `monomCoeff_mk`, `monomExp_mk`, `monomDeg_mk`
  * `monomCoeff_mem_RatSet`, `monomExp_mem_omega`, `monomDeg_mem_omega`
  * `monomEval_zero`, `monomEval_mk`, `monomEval_mem_RatSet`
-/

import ZFC.Rat.Pow

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Pairing
  open ZFC.SetOps.OrderedPair
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  open ZFC.Rat.Basic
  open ZFC.Rat.Mul
  open ZFC.Rat.Pow

  universe u
  variable {U : Type u}

  namespace Algebra.Monomial

    /-! ============================================================ -/
    /-! ### SECTION 1: REPRESENTATION                            ### -/
    /-! ============================================================ -/

    /-- The zero monomial: canonical sentinel `∅`. -/
    noncomputable def zeroMonom : U := (∅ : U)

    /-- Smart constructor: `q = 0` collapses to the canonical zero monomial. -/
    noncomputable def monomMk (n q : U) : U :=
      if q = (zeroQ : U) then (∅ : U) else ⟨n, q⟩

    /-- A monomial is either the zero sentinel or a pair `⟨n,q⟩` with `n ∈ ω`, `q ∈ ℚ`, `q ≠ 0`. -/
    def IsMonom (m : U) : Prop :=
      m = (∅ : U) ∨
        ∃ n q, n ∈ (ω : U) ∧ q ∈ (RatSet : U) ∧ q ≠ (zeroQ : U) ∧ m = ⟨n, q⟩

    /-- Predicate distinguishing the zero monomial. -/
    def IsZeroMonom (m : U) : Prop := m = (∅ : U)

    /-- `⟨a, b⟩` is never empty (it contains `{a}`), so `∅` is a safe sentinel. -/
    private theorem orderedPair_ne_empty (a b : U) : (⟨a, b⟩ : U) ≠ (∅ : U) :=
      (nonempty_iff_exists_mem _).mpr
        ⟨({a} : U), (OrderedPair_is_specified a b ({a} : U)).mpr (Or.inl rfl)⟩

    theorem monomMk_zero (n : U) : monomMk n (zeroQ : U) = (zeroMonom : U) := by
      unfold monomMk zeroMonom; rw [if_pos rfl]

    theorem monomMk_of_ne_zero (n q : U) (hq : q ≠ (zeroQ : U)) :
        monomMk n q = ⟨n, q⟩ := by
      unfold monomMk; rw [if_neg hq]

    theorem zeroMonom_isMonom : IsMonom (zeroMonom : U) := Or.inl rfl

    theorem monomMk_isMonom (n q : U) (hn : n ∈ (ω : U)) (hq : q ∈ (RatSet : U)) :
        IsMonom (monomMk n q) := by
      rcases Classical.em (q = (zeroQ : U)) with h | h
      · rw [h, monomMk_zero]; exact zeroMonom_isMonom
      · rw [monomMk_of_ne_zero n q h]
        exact Or.inr ⟨n, q, hn, hq, h, rfl⟩

    /-! ============================================================ -/
    /-! ### SECTION 2: PROJECTIONS                               ### -/
    /-! ============================================================ -/

    /-- Coefficient of a monomial (`0` for the zero monomial). -/
    noncomputable def monomCoeff (m : U) : U := if m = (∅ : U) then (zeroQ : U) else snd m

    /-- Literal exponent used in evaluation (junk `0` for the zero monomial). -/
    noncomputable def monomExp (m : U) : U := if m = (∅ : U) then (∅ : U) else fst m

    /-- Degree in the WithBot ω encoding: `−∞ ↦ ∅`, finite `n ↦ σ n`. -/
    noncomputable def monomDeg (m : U) : U := if m = (∅ : U) then (∅ : U) else σ (fst m)

    theorem monomCoeff_zero : monomCoeff (zeroMonom : U) = (zeroQ : U) := by
      unfold monomCoeff zeroMonom; rw [if_pos rfl]

    theorem monomCoeff_mk (n q : U) : monomCoeff (monomMk n q) = q := by
      rcases Classical.em (q = (zeroQ : U)) with h | h
      · rw [h, monomMk_zero, monomCoeff_zero]
      · rw [monomMk_of_ne_zero n q h]
        unfold monomCoeff
        rw [if_neg (orderedPair_ne_empty n q), snd_of_ordered_pair]

    theorem monomExp_mk (n q : U) (hq : q ≠ (zeroQ : U)) : monomExp (monomMk n q) = n := by
      rw [monomMk_of_ne_zero n q hq]
      unfold monomExp
      rw [if_neg (orderedPair_ne_empty n q), fst_of_ordered_pair]

    theorem monomDeg_zeroMonom : monomDeg (zeroMonom : U) = (∅ : U) := by
      unfold monomDeg zeroMonom; rw [if_pos rfl]

    theorem monomDeg_mk (n q : U) (hq : q ≠ (zeroQ : U)) : monomDeg (monomMk n q) = σ n := by
      rw [monomMk_of_ne_zero n q hq]
      unfold monomDeg
      rw [if_neg (orderedPair_ne_empty n q), fst_of_ordered_pair]

    theorem monomCoeff_mem_RatSet (m : U) (hm : IsMonom m) :
        monomCoeff m ∈ (RatSet : U) := by
      rcases hm with h | ⟨n, q, _, hq, _, heq⟩
      · rw [h]; unfold monomCoeff; rw [if_pos rfl]; exact zeroQ_mem_RatSet
      · rw [heq]; unfold monomCoeff
        rw [if_neg (orderedPair_ne_empty n q), snd_of_ordered_pair]; exact hq

    theorem monomExp_mem_omega (m : U) (hm : IsMonom m) : monomExp m ∈ (ω : U) := by
      rcases hm with h | ⟨n, q, hn, _, _, heq⟩
      · rw [h]; unfold monomExp; rw [if_pos rfl]; exact zero_in_Omega
      · rw [heq]; unfold monomExp
        rw [if_neg (orderedPair_ne_empty n q), fst_of_ordered_pair]; exact hn

    theorem monomDeg_mem_omega (m : U) (hm : IsMonom m) : monomDeg m ∈ (ω : U) := by
      rcases hm with h | ⟨n, q, hn, _, _, heq⟩
      · rw [h]; unfold monomDeg; rw [if_pos rfl]; exact zero_in_Omega
      · rw [heq]; unfold monomDeg
        rw [if_neg (orderedPair_ne_empty n q), fst_of_ordered_pair]
        exact succ_in_Omega n hn

    /-! ============================================================ -/
    /-! ### SECTION 3: EVALUATION                                ### -/
    /-! ============================================================ -/

    /-- Evaluation of a monomial at `x`: `coeff · x^exp`. Correct even for the
        zero monomial, since the zero coefficient absorbs the junk exponent. -/
    noncomputable def monomEval (m x : U) : U :=
      mulQ (monomCoeff m) (powRatQ x (monomExp m))

    theorem monomEval_zero (x : U) : monomEval (zeroMonom : U) x = (zeroQ : U) := by
      unfold monomEval
      have hexp : monomExp (zeroMonom : U) = (∅ : U) := by
        unfold monomExp zeroMonom; rw [if_pos rfl]
      rw [monomCoeff_zero, hexp]
      exact mulQ_zero_left (powRatQ x (∅ : U)) (powRatQ_mem_RatSet x (∅ : U) zero_in_Omega)

    theorem monomEval_mk (n q x : U) (hn : n ∈ (ω : U)) :
        monomEval (monomMk n q) x = mulQ q (powRatQ x n) := by
      rcases Classical.em (q = (zeroQ : U)) with h | h
      · rw [h, monomMk_zero, monomEval_zero,
            mulQ_zero_left (powRatQ x n) (powRatQ_mem_RatSet x n hn)]
      · unfold monomEval
        rw [monomCoeff_mk n q, monomExp_mk n q h]

    theorem monomEval_mem_RatSet (m x : U) (hm : IsMonom m) :
        monomEval m x ∈ (RatSet : U) := by
      unfold monomEval
      exact mulQ_in_RatSet (monomCoeff m) (powRatQ x (monomExp m))
        (monomCoeff_mem_RatSet m hm)
        (powRatQ_mem_RatSet x (monomExp m) (monomExp_mem_omega m hm))

  end Algebra.Monomial

  export Algebra.Monomial (
    -- Section 1: representation
    zeroMonom
    monomMk
    IsMonom
    IsZeroMonom
    monomMk_zero
    monomMk_of_ne_zero
    zeroMonom_isMonom
    monomMk_isMonom
    -- Section 2: projections
    monomCoeff
    monomExp
    monomDeg
    monomCoeff_zero
    monomCoeff_mk
    monomExp_mk
    monomDeg_zeroMonom
    monomDeg_mk
    monomCoeff_mem_RatSet
    monomExp_mem_omega
    monomDeg_mem_omega
    -- Section 3: evaluation
    monomEval
    monomEval_zero
    monomEval_mk
    monomEval_mem_RatSet
  )

end ZFC
