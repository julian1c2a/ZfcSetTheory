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
import ZFC.Rat.Field

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
  open ZFC.Rat.Field
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
      intro ε hε hε_pos
      -- twoQ and its properties (needed for halfQ)
      let twoQ : U := addQ (oneQ : U) (oneQ : U)
      have htwoQ : twoQ ∈ (RatSet : U) :=
        addQ_in_RatSet oneQ oneQ oneQ_mem_RatSet oneQ_mem_RatSet
      -- oneQ > 0
      have hone_pos : isPositiveQ (oneQ : U) := by
        constructor
        · rw [leQ_iff_repr zeroQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet]
          have hone_i : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
          have hone_nz : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
          have h_one : mulZ oneZ oneZ = (oneZ : U) := mulZ_one_left oneZ hone_i
          have h_zero : mulZ zeroZ oneZ = (zeroZ : U) := mulZ_zero_left oneZ hone_i
          have lhs_eq : mulZ (mulZ zeroZ oneZ) (mulZ oneZ oneZ) = (zeroZ : U) := by
            rw [h_one, h_zero, mulZ_zero_left oneZ hone_i]
          have rhs_eq : mulZ (mulZ oneZ oneZ) (mulZ oneZ oneZ) = (oneZ : U) := by
            simp only [h_one]
          have h_repr : leQ_repr zeroZ oneZ oneZ oneZ := by
            unfold leQ_repr; rw [lhs_eq, rhs_eq]
            have sq := square_nonneg oneZ hone_i; rwa [h_one] at sq
          exact ⟨zeroZ, oneZ, oneZ, oneZ, zeroZ_mem_IntSet, hone_nz,
                 hone_i, hone_nz, rfl, rfl, h_repr⟩
        · exact zeroQ_ne_oneQ
      -- twoQ ≠ zeroQ
      have htwoQ_ne : twoQ ≠ (zeroQ : U) := by
        intro h
        have h_le : leQ (addQ (zeroQ : U) (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
          addQ_leQ_addQ zeroQ oneQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet
            hone_pos.1
        rw [addQ_zero_left oneQ oneQ_mem_RatSet, h] at h_le
        exact zeroQ_ne_oneQ (leQ_antisymm oneQ zeroQ oneQ_mem_RatSet zeroQ_mem_RatSet
          h_le hone_pos.1).symm
      -- invQ(2) + invQ(2) = 1
      have hinvQ := invQ_in_RatSet twoQ htwoQ
      have inv_twoQ_add : addQ (invQ twoQ) (invQ twoQ) = (oneQ : U) := by
        have h_mul := mulQ_invQ_left twoQ htwoQ htwoQ_ne
        rw [show twoQ = addQ (oneQ : U) (oneQ : U) from rfl] at h_mul
        rw [mulQ_addQ_distrib_left (invQ twoQ) oneQ oneQ hinvQ
              oneQ_mem_RatSet oneQ_mem_RatSet,
            mulQ_one_right (invQ twoQ) hinvQ] at h_mul
        exact h_mul
      -- ε/2 = ε · invQ(2)
      let ε₂ : U := mulQ ε (invQ twoQ)
      have hε₂ : ε₂ ∈ (RatSet : U) := mulQ_in_RatSet ε (invQ twoQ) hε hinvQ
      -- ε/2 + ε/2 = ε
      have half_add : addQ ε₂ ε₂ = ε := by
        show addQ (mulQ ε (invQ twoQ)) (mulQ ε (invQ twoQ)) = ε
        rw [← mulQ_addQ_distrib_right ε (invQ twoQ) (invQ twoQ) hε hinvQ hinvQ,
            inv_twoQ_add, mulQ_one_right ε hε]
      -- ε/2 > 0
      have hε₂_pos : isPositiveQ ε₂ := by
        rcases rat_trichotomy_order ε₂ hε₂ with h | h | h
        · exact h
        · exfalso
          have : ε = (zeroQ : U) := by
            have hh := half_add; rw [h, addQ_zero_left zeroQ zeroQ_mem_RatSet] at hh
            exact hh.symm
          exact hε_pos.2 this
        · exfalso
          have h_le : leQ ε₂ (zeroQ : U) := h.1
          have h_le2 : leQ (addQ ε₂ ε₂) (addQ ε₂ (zeroQ : U)) :=
            addQ_leQ_addQ ε₂ (zeroQ : U) ε₂ hε₂ zeroQ_mem_RatSet hε₂ h_le
          rw [addQ_zero_right ε₂ hε₂, half_add] at h_le2
          have h_le3 : leQ ε (zeroQ : U) :=
            leQ_trans ε ε₂ zeroQ hε hε₂ zeroQ_mem_RatSet h_le2 h_le
          exact hε_pos.2 (leQ_antisymm ε zeroQ hε zeroQ_mem_RatSet h_le3 hε_pos.1).symm
      -- Get N from convergence with threshold ε/2
      obtain ⟨N, hN, h'⟩ := h_conv ε₂ hε₂ hε₂_pos
      refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
      have hfm := seqTermQ_mem_RatSet f m hf hm
      have hfn := seqTermQ_mem_RatSet f n hf hn
      have hm_bd := h' m hm hm_ge  -- ltQ |f(m)−L| ε₂
      have hn_bd := h' n hn hn_ge  -- ltQ |f(n)−L| ε₂
      -- |f(m)−f(n)| ≤ |f(m)−L| + |L−f(n)| = |f(m)−L| + |f(n)−L| < ε/2 + ε/2 = ε
      -- subQ f(m) f(n) = addQ (subQ f(m) L) (subQ L f(n))
      have hfmL : subQ (f⦅m⦆) L ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅m⦆) (negQ L) hfm (negQ_in_RatSet L hL)
      have hfnL : subQ (f⦅n⦆) L ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
      have hLfn : subQ L (f⦅n⦆) ∈ (RatSet : U) :=
        addQ_in_RatSet L (negQ (f⦅n⦆)) hL (negQ_in_RatSet (f⦅n⦆) hfn)
      -- |L - f(n)| = |f(n) - L| (symmetry of abs of sub)
      have h_symm : absQ (subQ L (f⦅n⦆)) = absQ (subQ (f⦅n⦆) L) := by
        have h_neg : subQ (f⦅n⦆) L = negQ (subQ L (f⦅n⦆)) := by
          have h_sum : addQ (subQ L (f⦅n⦆)) (subQ (f⦅n⦆) L) = (zeroQ : U) :=
            calc addQ (addQ L (negQ (f⦅n⦆))) (addQ (f⦅n⦆) (negQ L))
                = addQ L (addQ (negQ (f⦅n⦆)) (addQ (f⦅n⦆) (negQ L))) := by
                    rw [addQ_assoc L (negQ (f⦅n⦆)) (addQ (f⦅n⦆) (negQ L)) hL
                          (negQ_in_RatSet (f⦅n⦆) hfn)
                          (addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL))]
              _ = addQ L (addQ (addQ (negQ (f⦅n⦆)) (f⦅n⦆)) (negQ L)) := by
                    rw [← addQ_assoc (negQ (f⦅n⦆)) (f⦅n⦆) (negQ L)
                          (negQ_in_RatSet (f⦅n⦆) hfn) hfn (negQ_in_RatSet L hL)]
              _ = addQ L (addQ (zeroQ : U) (negQ L)) := by rw [negQ_addQ_left (f⦅n⦆) hfn]
              _ = addQ L (negQ L) := by rw [addQ_zero_left (negQ L) (negQ_in_RatSet L hL)]
              _ = zeroQ := negQ_addQ_right L hL
          calc subQ (f⦅n⦆) L
              = addQ (zeroQ : U) (subQ (f⦅n⦆) L) :=
                  (addQ_zero_left (subQ (f⦅n⦆) L) hfnL).symm
            _ = addQ (addQ (negQ (subQ L (f⦅n⦆))) (subQ L (f⦅n⦆))) (subQ (f⦅n⦆) L) := by
                  rw [negQ_addQ_left (subQ L (f⦅n⦆)) hLfn]
            _ = addQ (negQ (subQ L (f⦅n⦆)))
                    (addQ (subQ L (f⦅n⦆)) (subQ (f⦅n⦆) L)) := by
                  rw [addQ_assoc (negQ (subQ L (f⦅n⦆))) (subQ L (f⦅n⦆)) (subQ (f⦅n⦆) L)
                        (negQ_in_RatSet (subQ L (f⦅n⦆)) hLfn) hLfn hfnL]
            _ = addQ (negQ (subQ L (f⦅n⦆))) (zeroQ : U) := by rw [h_sum]
            _ = negQ (subQ L (f⦅n⦆)) :=
                  addQ_zero_right _ (negQ_in_RatSet (subQ L (f⦅n⦆)) hLfn)
        rw [← h_neg, absQ_negQ (subQ L (f⦅n⦆)) hLfn]
      -- Triangle: |f(m)−f(n)| ≤ |f(m)−L| + |L−f(n)|
      have h_sub_eq : subQ (f⦅m⦆) (f⦅n⦆) =
          addQ (subQ (f⦅m⦆) L) (subQ L (f⦅n⦆)) :=
        calc addQ (f⦅m⦆) (negQ (f⦅n⦆))
            = addQ (f⦅m⦆) (addQ (addQ (negQ L) L) (negQ (f⦅n⦆))) := by
                rw [negQ_addQ_left L hL, addQ_zero_left (negQ (f⦅n⦆)) (negQ_in_RatSet (f⦅n⦆) hfn)]
          _ = addQ (f⦅m⦆) (addQ (negQ L) (addQ L (negQ (f⦅n⦆)))) := by
                rw [addQ_assoc (negQ L) L (negQ (f⦅n⦆))
                      (negQ_in_RatSet L hL) hL (negQ_in_RatSet (f⦅n⦆) hfn)]
          _ = addQ (addQ (f⦅m⦆) (negQ L)) (addQ L (negQ (f⦅n⦆))) := by
                rw [← addQ_assoc (f⦅m⦆) (negQ L) (addQ L (negQ (f⦅n⦆)))
                      hfm (negQ_in_RatSet L hL)
                      (addQ_in_RatSet L (negQ (f⦅n⦆)) hL (negQ_in_RatSet (f⦅n⦆) hfn))]
      have h_tri : leQ (absQ (subQ (f⦅m⦆) (f⦅n⦆)))
          (addQ (absQ (subQ (f⦅m⦆) L)) (absQ (subQ L (f⦅n⦆)))) := by
        rw [h_sub_eq]; exact absQ_triangle (subQ (f⦅m⦆) L) (subQ L (f⦅n⦆)) hfmL hLfn
      -- Combine: ≤ |f(m)−L| + |f(n)−L| < ε/2 + ε/2 = ε
      have h_tri2 : leQ (absQ (subQ (f⦅m⦆) (f⦅n⦆)))
          (addQ (absQ (subQ (f⦅m⦆) L)) (absQ (subQ (f⦅n⦆) L))) := by
        rwa [h_symm] at h_tri
      -- |f(m)−L| ≤ ε₂ (weak) and |f(n)−L| < ε₂ (strict)
      have h_sum_lt : ltQ (addQ (absQ (subQ (f⦅m⦆) L)) (absQ (subQ (f⦅n⦆) L))) ε := by
        have h_le1 : leQ (addQ (absQ (subQ (f⦅m⦆) L)) (absQ (subQ (f⦅n⦆) L)))
            (addQ (absQ (subQ (f⦅m⦆) L)) ε₂) := by
          have := addQ_leQ_addQ (absQ (subQ (f⦅n⦆) L)) ε₂
            (absQ (subQ (f⦅m⦆) L))
            (absQ_in_RatSet _ hfnL) hε₂ (absQ_in_RatSet _ hfmL) hn_bd.1
          rwa [addQ_comm (absQ (subQ (f⦅n⦆) L)) _ _ _,
               addQ_comm ε₂ _ _ _] at this
        have h_lt2 : ltQ (addQ (absQ (subQ (f⦅m⦆) L)) ε₂) (addQ ε₂ ε₂) := by
          have := addQ_leQ_addQ (absQ (subQ (f⦅m⦆) L)) ε₂ ε₂
            (absQ_in_RatSet _ hfmL) hε₂ hε₂ hm_bd.1
          constructor
          · exact this
          · intro h_eq
            have h_rev : leQ (addQ ε₂ ε₂) (addQ (absQ (subQ (f⦅m⦆) L)) ε₂) :=
              h_eq ▸ leQ_refl _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) hε₂)
            have h_eq2 : addQ (absQ (subQ (f⦅m⦆) L)) ε₂ = addQ ε₂ ε₂ :=
              leQ_antisymm _ _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) hε₂)
                (addQ_in_RatSet _ _ hε₂ hε₂) this h_rev
            -- cancel ε₂: |f(m)−L| = ε₂ → |f(m)−L| = ε₂ and hm_bd.2 says absQ ... ≠ ε₂
            have cancel := congrArg (fun x => addQ (negQ ε₂) x) h_eq2
            rw [← addQ_assoc (negQ ε₂) _ _ (negQ_in_RatSet ε₂ hε₂) (absQ_in_RatSet _ hfmL) hε₂,
                ← addQ_assoc (negQ ε₂) ε₂ ε₂ (negQ_in_RatSet ε₂ hε₂) hε₂ hε₂,
                negQ_addQ_left ε₂ hε₂,
                addQ_zero_left _ (absQ_in_RatSet _ hfmL),
                addQ_zero_left ε₂ hε₂] at cancel
            exact hm_bd.2 cancel
        rw [half_add] at h_lt2
        exact ⟨leQ_trans _ _ _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) (absQ_in_RatSet _ hfnL))
                (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) hε₂) hε
                h_le1 h_lt2.1,
               fun heq => h_lt2.2 (leQ_antisymm _ _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) hε₂)
                 hε h_lt2.1 (heq ▸ h_le1))⟩
      -- Conclusion: |f(m)−f(n)| < ε
      exact ⟨leQ_trans _ _ _ (absQ_in_RatSet _ (addQ_in_RatSet (f⦅m⦆) (negQ (f⦅n⦆)) hfm (negQ_in_RatSet (f⦅n⦆) hfn)))
              (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) (absQ_in_RatSet _ hfnL)) hε
              h_tri2 h_sum_lt.1,
             fun heq => h_sum_lt.2 (leQ_antisymm _ _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmL) (absQ_in_RatSet _ hfnL))
               hε h_sum_lt.1 (heq ▸ h_tri2))⟩

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
