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
import ZFC.Rat.MaxMin

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
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Field
  open ZFC.Rat.MaxMin
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
          have h_one : mulZ (oneZ : U) (oneZ : U) = (oneZ : U) :=
            mulZ_one_left (oneZ : U) hone_i
          have h_zero : mulZ (zeroZ : U) (oneZ : U) = (zeroZ : U) :=
            mulZ_zero_left (oneZ : U) hone_i
          have lhs_eq : mulZ (mulZ (zeroZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (zeroZ : U) := by
            simp only [h_one, h_zero]
          have rhs_eq : mulZ (mulZ (oneZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (oneZ : U) := by
            simp only [h_one]
          have h_repr : leQ_repr (zeroZ : U) (oneZ : U) (oneZ : U) (oneZ : U) := by
            unfold leQ_repr; rw [lhs_eq, rhs_eq]
            have sq := square_nonneg (oneZ : U) hone_i; rwa [h_one] at sq
          exact ⟨(zeroZ : U), (oneZ : U), (oneZ : U), (oneZ : U), zeroZ_mem_IntSet, hone_nz,
                 hone_i, hone_nz, rfl, rfl, h_repr⟩
        · exact zeroQ_ne_oneQ
      -- twoQ ≠ zeroQ
      have htwoQ_ne : twoQ ≠ (zeroQ : U) := by
        intro h
        have h_le : leQ (addQ (zeroQ : U) (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
          addQ_leQ_addQ zeroQ oneQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet
            hone_pos.1
        rw [addQ_zero_left oneQ oneQ_mem_RatSet] at h_le
        have h_two : addQ (oneQ : U) (oneQ : U) = (zeroQ : U) := h
        rw [h_two] at h_le
        exact zeroQ_ne_oneQ (leQ_antisymm oneQ zeroQ oneQ_mem_RatSet zeroQ_mem_RatSet
          h_le hone_pos.1).symm
      -- invQ(2) + invQ(2) = 1
      have hinvQ := invQ_in_RatSet twoQ htwoQ
      have inv_twoQ_add : addQ (invQ twoQ) (invQ twoQ) = (oneQ : U) := by
        have h1 : addQ (invQ twoQ) (invQ twoQ) =
            mulQ (invQ twoQ) (addQ (oneQ : U) (oneQ : U)) := by
          rw [mulQ_addQ_distrib_left (invQ twoQ) oneQ oneQ hinvQ
                oneQ_mem_RatSet oneQ_mem_RatSet,
              mulQ_one_right (invQ twoQ) hinvQ]
        have h2 : mulQ (invQ twoQ) (addQ (oneQ : U) (oneQ : U)) =
            mulQ (invQ twoQ) twoQ := rfl
        have h3 : mulQ (invQ twoQ) twoQ = (oneQ : U) :=
          mulQ_invQ_left twoQ htwoQ htwoQ_ne
        rw [h1, h2, h3]
      -- ε/2 = ε · invQ(2)
      let ε₂ : U := mulQ ε (invQ twoQ)
      have hε₂ : ε₂ ∈ (RatSet : U) := mulQ_in_RatSet ε (invQ twoQ) hε hinvQ
      -- ε/2 + ε/2 = ε
      have half_add : addQ ε₂ ε₂ = ε := by
        show addQ (mulQ ε (invQ twoQ)) (mulQ ε (invQ twoQ)) = ε
        rw [← mulQ_addQ_distrib_left ε (invQ twoQ) (invQ twoQ) hε hinvQ hinvQ,
            inv_twoQ_add, mulQ_one_right ε hε]
      -- ε/2 > 0
      have hε₂_pos : isPositiveQ ε₂ := by
        rcases rat_trichotomy_order ε₂ hε₂ with h | h | h
        · exact h
        · exfalso
          have : ε = (zeroQ : U) := by
            have hh := half_add; rw [h, addQ_zero_left zeroQ zeroQ_mem_RatSet] at hh
            exact hh.symm
          exact hε_pos.2 this.symm
        · exfalso
          have h_le : leQ ε₂ (zeroQ : U) := h.1
          have h_le2 : leQ (addQ ε₂ ε₂) (addQ (zeroQ : U) ε₂) :=
            addQ_leQ_addQ ε₂ (zeroQ : U) ε₂ hε₂ zeroQ_mem_RatSet hε₂ h_le
          rw [addQ_zero_left ε₂ hε₂, half_add] at h_le2
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
        rw [h_neg, ← absQ_negQ (subQ L (f⦅n⦆)) hLfn]
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
          rwa [addQ_comm (absQ (subQ (f⦅n⦆) L)) (absQ (subQ (f⦅m⦆) L))
                 (absQ_in_RatSet _ hfnL) (absQ_in_RatSet _ hfmL),
               addQ_comm ε₂ (absQ (subQ (f⦅m⦆) L)) hε₂ (absQ_in_RatSet _ hfmL)] at this
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
            -- cancel ε₂: from h_eq2, derive absQ (subQ (f⦅m⦆) L) = ε₂
            have cancel := congrArg (fun x => addQ x (negQ ε₂)) h_eq2
            have h_abs_eq : absQ (subQ (f⦅m⦆) L) = ε₂ :=
              let habs := absQ_in_RatSet (subQ (f⦅m⦆) L) hfmL
              let hneg := negQ_in_RatSet ε₂ hε₂
              (addQ_zero_right (absQ (subQ (f⦅m⦆) L)) habs).symm.trans
              ((congrArg (addQ (absQ (subQ (f⦅m⦆) L))) (negQ_addQ_right ε₂ hε₂).symm).trans
              ((addQ_assoc (absQ (subQ (f⦅m⦆) L)) ε₂ (negQ ε₂) habs hε₂ hneg).symm.trans
              (cancel.trans
              ((addQ_assoc ε₂ ε₂ (negQ ε₂) hε₂ hε₂ hneg).trans
              ((congrArg (addQ ε₂) (negQ_addQ_right ε₂ hε₂)).trans
              (addQ_zero_right ε₂ hε₂))))))
            exact hm_bd.2 h_abs_eq
        rw [show addQ ε₂ ε₂ = ε from half_add] at h_lt2
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
        Proof: take ε=1, get N₀ via Cauchy. Prove by induction that for each N ∈ ω
        there exists a bound for {|f(k)| : k ≤ N} using maxQ. Then for k > N₀ use
        the triangle inequality: |f(k)| ≤ |f(k)−f(N₀)| + |f(N₀)| < 1 + M₀ = M. -/
    theorem cauchy_bounded (f : U)
        (hf : IsSeqQ f) (h_cauchy : IsCauchyQ f) :
        ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
          ∀ n : U, n ∈ (ω : U) → leQ (absQ (f⦅n⦆)) M := by
      -- ① 0 < 1 in ℚ (same proof as private oneQ_pos in Convergence.lean)
      have hone_pos : isPositiveQ (oneQ : U) := by
        constructor
        · rw [leQ_iff_repr zeroQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet]
          have hone_i : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
          have hone_nz : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
          have h_repr : leQ_repr (zeroZ : U) (oneZ : U) (oneZ : U) (oneZ : U) := by
            unfold leQ_repr
            have h_one := mulZ_one_left (oneZ : U) hone_i
            have h_zero := mulZ_zero_left (oneZ : U) hone_i
            have lhs_eq : mulZ (mulZ (zeroZ : U) (oneZ : U))
                            (mulZ (oneZ : U) (oneZ : U)) = (zeroZ : U) := by
              simp only [h_one, h_zero]
            have rhs_eq : mulZ (mulZ (oneZ : U) (oneZ : U))
                            (mulZ (oneZ : U) (oneZ : U)) = (oneZ : U) := by
              simp only [h_one]
            rw [lhs_eq, rhs_eq]
            have sq := square_nonneg (oneZ : U) hone_i; rwa [h_one] at sq
          exact ⟨(zeroZ : U), (oneZ : U), (oneZ : U), (oneZ : U),
                 zeroZ_mem_IntSet, hone_nz, hone_i, hone_nz, rfl, rfl, h_repr⟩
        · exact zeroQ_ne_oneQ
      -- ② Get N₀ from Cauchy at ε = 1
      obtain ⟨N₀, hN₀, hcauchy1⟩ := h_cauchy oneQ oneQ_mem_RatSet hone_pos
      -- ③ Inductive bound: ∀ N ∈ ω, ∃ M > 0, ∀ k ≤ N, |f(k)| ≤ M
      -- Abbreviation for the sep predicate (avoids let-binding issues with rw)
      let Q : U → Prop := fun n => ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
            ∀ k : U, k ∈ (ω : U) → (k ∈ n ∨ k = n) → leQ (absQ (f⦅k⦆)) M
      have hS_eq : sep (ω : U) Q = (ω : U) := by
        apply induction_principle
        · -- sep ω Q ⊆ ω
          intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- ∅ ∈ sep ω Q: bound M₀ = addQ oneQ (absQ (f⦅∅⦆)) ≥ 1 > 0 ≥ |f(0)|
          rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ?_⟩
          have hf0 : f⦅∅⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f ∅ hf zero_in_Omega
          have habs0 : absQ (f⦅∅⦆) ∈ (RatSet : U) := absQ_in_RatSet _ hf0
          show ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
              ∀ k : U, k ∈ (ω : U) → (k ∈ ∅ ∨ k = ∅) → leQ (absQ (f⦅k⦆)) M
          refine ⟨addQ oneQ (absQ (f⦅∅⦆)),
                  addQ_in_RatSet oneQ _ oneQ_mem_RatSet habs0, ?_, ?_⟩
          · -- isPositiveQ
            constructor
            · exact leQ_trans zeroQ (absQ (f⦅∅⦆)) (addQ oneQ (absQ (f⦅∅⦆)))
                zeroQ_mem_RatSet habs0 (addQ_in_RatSet oneQ _ oneQ_mem_RatSet habs0)
                (absQ_nonneg _ hf0)
                (by have h := addQ_leQ_addQ zeroQ oneQ (absQ (f⦅∅⦆))
                          zeroQ_mem_RatSet oneQ_mem_RatSet habs0 hone_pos.1
                    rwa [addQ_zero_left _ habs0] at h)
            · intro heq
              have h1 : leQ oneQ (addQ oneQ (absQ (f⦅∅⦆))) := by
                have h2 := addQ_leQ_addQ zeroQ (absQ (f⦅∅⦆)) oneQ
                  zeroQ_mem_RatSet habs0 oneQ_mem_RatSet (absQ_nonneg _ hf0)
                rwa [addQ_zero_left oneQ oneQ_mem_RatSet,
                     addQ_comm (absQ (f⦅∅⦆)) oneQ habs0 oneQ_mem_RatSet] at h2
              rw [← heq] at h1
              exact hone_pos.2 (leQ_antisymm oneQ zeroQ oneQ_mem_RatSet zeroQ_mem_RatSet
                h1 hone_pos.1).symm
          · -- bound: only k = ∅ is possible
            intro k hk hkle
            cases hkle with
            | inl h => exact absurd h (EmptySet_is_empty k)
            | inr h =>
              rw [h]
              have h2 := addQ_leQ_addQ zeroQ oneQ (absQ (f⦅∅⦆))
                zeroQ_mem_RatSet oneQ_mem_RatSet habs0 hone_pos.1
              rwa [addQ_zero_left _ habs0] at h2
        · -- step: n ∈ sep ω Q → σn ∈ sep ω Q; use bound = maxQ M (absQ (f⦅σn⦆))
          intro n hn_S
          rw [mem_sep_iff] at hn_S
          obtain ⟨hn, hQn⟩ := hn_S
          obtain ⟨M, hM, hMpos, hbound⟩ := hQn
          have hsn : σ n ∈ (ω : U) := succ_in_Omega n hn
          rw [mem_sep_iff]
          refine ⟨hsn, ?_⟩
          show ∃ M' : U, M' ∈ (RatSet : U) ∧ isPositiveQ M' ∧
              ∀ k : U, k ∈ (ω : U) → (k ∈ σ n ∨ k = σ n) → leQ (absQ (f⦅k⦆)) M'
          have hfsn : f⦅σ n⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f (σ n) hf hsn
          have habssn : absQ (f⦅σ n⦆) ∈ (RatSet : U) := absQ_in_RatSet _ hfsn
          refine ⟨maxQ M (absQ (f⦅σ n⦆)), maxQ_in_RatSet M _ hM habssn, ?_, ?_⟩
          · -- isPositiveQ (maxQ M _): since M > 0 ≤ maxQ M _
            constructor
            · exact leQ_trans zeroQ M (maxQ M (absQ (f⦅σ n⦆)))
                zeroQ_mem_RatSet hM (maxQ_in_RatSet M _ hM habssn)
                hMpos.1 (leQ_maxQ_left M _ hM habssn)
            · intro heq
              exact hMpos.2 (leQ_antisymm M zeroQ hM zeroQ_mem_RatSet
                (heq ▸ leQ_maxQ_left M _ hM habssn) hMpos.1).symm
          · -- bound for k ≤ σn
            intro k hk hkle
            rw [mem_succ_iff] at hkle
            cases hkle with
            | inl hkin =>
              -- after mem_succ_iff: hkin : k ∈ n ∨ k = n
              have h_abs_k := absQ_in_RatSet _ (seqTermQ_mem_RatSet f k hf hk)
              exact leQ_trans _ M (maxQ M _) h_abs_k hM (maxQ_in_RatSet M _ hM habssn)
                (hbound k hk hkin) (leQ_maxQ_left M _ hM habssn)
            | inr hksin =>
              rw [hksin]; exact leQ_maxQ_right M _ hM habssn
      have fin_bound : ∀ N : U, N ∈ (ω : U) →
          ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
            ∀ k : U, k ∈ (ω : U) → (k ∈ N ∨ k = N) → leQ (absQ (f⦅k⦆)) M := by
        intro N hN
        have hN_S : N ∈ sep (ω : U) Q := by rw [hS_eq]; exact hN
        rw [mem_sep_iff] at hN_S
        exact hN_S.2
      -- ④ Get M₀ bounding f on [0, N₀]
      obtain ⟨M₀, hM₀, hM₀pos, hbound₀⟩ := fin_bound N₀ hN₀
      -- ⑤ Final bound M = M₀ + 1; M₀ ≤ M and for k > N₀: |f(k)| < 1 + M₀ ≤ M
      have hM : addQ M₀ oneQ ∈ (RatSet : U) := addQ_in_RatSet M₀ oneQ hM₀ oneQ_mem_RatSet
      -- M₀ ≤ M₀ + 1
      have hM₀_le_M : leQ M₀ (addQ M₀ oneQ) := by
        have h := addQ_leQ_addQ zeroQ oneQ M₀ zeroQ_mem_RatSet oneQ_mem_RatSet hM₀ hone_pos.1
        rwa [addQ_zero_left M₀ hM₀, addQ_comm oneQ M₀ oneQ_mem_RatSet hM₀] at h
      refine ⟨addQ M₀ oneQ, hM,
              ⟨leQ_trans zeroQ M₀ _ zeroQ_mem_RatSet hM₀ hM hM₀pos.1 hM₀_le_M,
               fun heq => hM₀pos.2 (leQ_antisymm M₀ zeroQ hM₀ zeroQ_mem_RatSet
                 (heq ▸ hM₀_le_M) hM₀pos.1).symm⟩,
              ?_⟩
      intro n hn
      have hfn : f⦅n⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f n hf hn
      have habsn : absQ (f⦅n⦆) ∈ (RatSet : U) := absQ_in_RatSet _ hfn
      -- Trichotomy on n vs N₀
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      have hN₀_nat : IsNat N₀ := mem_Omega_is_Nat N₀ hN₀
      rcases natLt_trichotomy n N₀ hn_nat hN₀_nat with hlt | heq | hgt
      · -- n ∈ N₀: use induction bound, then M₀ ≤ M
        exact leQ_trans _ M₀ _ habsn hM₀ hM (hbound₀ n hn (Or.inl hlt)) hM₀_le_M
      · -- n = N₀: heq : n = N₀
        subst heq
        exact leQ_trans _ M₀ _ habsn hM₀ hM (hbound₀ n hN₀ (Or.inr rfl)) hM₀_le_M
      · -- N₀ ∈ n: use Cauchy at ε=1
        have hfN₀ : f⦅N₀⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f N₀ hf hN₀
        have hsubf : subQ (f⦅n⦆) (f⦅N₀⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet _ _ hfn (negQ_in_RatSet _ hfN₀)
        have habs_sub : absQ (subQ (f⦅n⦆) (f⦅N₀⦆)) ∈ (RatSet : U) := absQ_in_RatSet _ hsubf
        have habs_N₀ : absQ (f⦅N₀⦆) ∈ (RatSet : U) := absQ_in_RatSet _ hfN₀
        -- |f(n) − f(N₀)| < 1 (from Cauchy, m=n ≥ N₀, n'=N₀ ≥ N₀)
        have hcauchy_n := hcauchy1 n N₀ hn hN₀ (Or.inl hgt) (Or.inr rfl)
        have h_sub_le : leQ (absQ (subQ (f⦅n⦆) (f⦅N₀⦆))) oneQ := hcauchy_n.1
        -- |f(N₀)| ≤ M₀
        have h_absN₀ : leQ (absQ (f⦅N₀⦆)) M₀ := hbound₀ N₀ hN₀ (Or.inr rfl)
        -- f(n) = (f(n) − f(N₀)) + f(N₀)
        have hfn_eq : f⦅n⦆ = addQ (subQ (f⦅n⦆) (f⦅N₀⦆)) (f⦅N₀⦆) := by
          unfold subQ
          rw [addQ_assoc (f⦅n⦆) (negQ (f⦅N₀⦆)) (f⦅N₀⦆) hfn
                (negQ_in_RatSet _ hfN₀) hfN₀,
              negQ_addQ_left (f⦅N₀⦆) hfN₀, addQ_zero_right (f⦅n⦆) hfn]
        -- |f(n)| ≤ |f(n)−f(N₀)| + |f(N₀)| by triangle
        have h_tri : leQ (absQ (f⦅n⦆))
            (addQ (absQ (subQ (f⦅n⦆) (f⦅N₀⦆))) (absQ (f⦅N₀⦆))) := by
          have := absQ_triangle (subQ (f⦅n⦆) (f⦅N₀⦆)) (f⦅N₀⦆) hsubf hfN₀
          rwa [← hfn_eq] at this
        -- |f(n)−f(N₀)| + |f(N₀)| ≤ 1 + M₀ = M₀ + 1
        have h_sum_le : leQ (addQ (absQ (subQ (f⦅n⦆) (f⦅N₀⦆))) (absQ (f⦅N₀⦆)))
            (addQ M₀ oneQ) := by
          have step1 : leQ (addQ (absQ (subQ (f⦅n⦆) (f⦅N₀⦆))) (absQ (f⦅N₀⦆)))
              (addQ oneQ (absQ (f⦅N₀⦆))) :=
            addQ_leQ_addQ _ oneQ (absQ (f⦅N₀⦆)) habs_sub oneQ_mem_RatSet habs_N₀ h_sub_le
          have step2 : leQ (addQ oneQ (absQ (f⦅N₀⦆))) (addQ M₀ oneQ) := by
            have h := addQ_leQ_addQ (absQ (f⦅N₀⦆)) M₀ oneQ
              habs_N₀ hM₀ oneQ_mem_RatSet h_absN₀
            rwa [addQ_comm (absQ (f⦅N₀⦆)) oneQ habs_N₀ oneQ_mem_RatSet] at h
          exact leQ_trans _ _ _ (addQ_in_RatSet _ _ habs_sub habs_N₀)
            (addQ_in_RatSet oneQ _ oneQ_mem_RatSet habs_N₀) hM step1 step2
        exact leQ_trans _ _ _ habsn
          (addQ_in_RatSet _ _ habs_sub habs_N₀) hM h_tri h_sum_le

    -- =========================================================================
    -- Section 4: Constant sequences are Cauchy
    -- =========================================================================

    /-- The constant sequence at a is Cauchy -/
    theorem constSeqQ_isCauchy (a : U) (ha : a ∈ (RatSet : U)) :
        IsCauchyQ (constSeqQ a) :=
      cauchy_of_convergentQ (constSeqQ a) a
        (constSeqQ_isSeqQ a ha) ha
        (convergesToQ_const a ha)

    -- =========================================================================
    -- Section 5: Private helpers for Cauchy arithmetic
    -- =========================================================================

    private theorem omega_le_trans' (m n k : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h1 : m ∈ n ∨ m = n) (h2 : n ∈ k ∨ n = k) : m ∈ k ∨ m = k := by
      rcases h1 with hmn | rfl
      · rcases h2 with hnk | rfl
        · exact Or.inl (mem_trans m n k
            (mem_Omega_is_Nat m hm) (mem_Omega_is_Nat n hn)
            (mem_Omega_is_Nat k hk) hmn hnk)
        · exact Or.inl hmn
      · exact h2

    private theorem leQ_ltQ_trans' (a b c : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U))
        (h1 : leQ a b) (h2 : ltQ b c) : ltQ a c :=
      ⟨leQ_trans a b c ha hb hc h1 h2.1,
       fun h => h2.2 (leQ_antisymm b c hb hc h2.1 (h ▸ h1))⟩

    private theorem ltQ_add_of_leQ_ltQ' (a b c d : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U))
        (hc : c ∈ (RatSet : U)) (hd : d ∈ (RatSet : U))
        (hac : leQ a c) (hbd : ltQ b d) : ltQ (addQ a b) (addQ c d) := by
      have h1 : leQ (addQ a b) (addQ a d) := by
        have := addQ_leQ_addQ b d a hb hd ha hbd.1
        rwa [addQ_comm b a hb ha, addQ_comm d a hd ha] at this
      have h2 := addQ_leQ_addQ a c d ha hc hd hac
      constructor
      · exact leQ_trans _ _ _ (addQ_in_RatSet a b ha hb) (addQ_in_RatSet a d ha hd)
            (addQ_in_RatSet c d hc hd) h1 h2
      · intro heq
        have h3 : leQ (addQ c d) (addQ a d) := heq ▸ h1
        have h4 := leQ_antisymm (addQ a d) (addQ c d) (addQ_in_RatSet a d ha hd)
                     (addQ_in_RatSet c d hc hd) h2 h3
        have h5 : addQ a b = addQ a d := by rw [heq, h4.symm]
        have h6 : b = d :=
          calc b = addQ zeroQ b := (addQ_zero_left b hb).symm
            _ = addQ (addQ (negQ a) a) b := by rw [negQ_addQ_left a ha]
            _ = addQ (negQ a) (addQ a b) := addQ_assoc _ a b (negQ_in_RatSet a ha) ha hb
            _ = addQ (negQ a) (addQ a d) := congrArg (addQ _) h5
            _ = addQ (addQ (negQ a) a) d := (addQ_assoc _ a d (negQ_in_RatSet a ha) ha hd).symm
            _ = addQ zeroQ d := by rw [negQ_addQ_left a ha]
            _ = d := addQ_zero_left d hd
        exact hbd.2 h6

    private theorem oneQ_pos_priv : isPositiveQ (oneQ : U) := by
      constructor
      · rw [leQ_iff_repr zeroQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet]
        have hi : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
        have hn : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
        have h1 := mulZ_one_left (oneZ : U) hi
        have h0 := mulZ_zero_left (oneZ : U) hi
        have h_repr : leQ_repr (zeroZ : U) (oneZ : U) (oneZ : U) (oneZ : U) := by
          unfold leQ_repr
          have lhs : mulZ (mulZ (zeroZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (zeroZ : U) :=
            by simp only [h1, h0]
          have rhs : mulZ (mulZ (oneZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (oneZ : U) :=
            by simp only [h1]
          rw [lhs, rhs]; exact h1 ▸ square_nonneg (oneZ : U) hi
        exact ⟨zeroZ, oneZ, oneZ, oneZ, zeroZ_mem_IntSet, hn, hi, hn, rfl, rfl, h_repr⟩
      · exact zeroQ_ne_oneQ

    private noncomputable def twoQ' : U := addQ (oneQ : U) (oneQ : U)

    private theorem twoQ'_mem : (twoQ' : U) ∈ (RatSet : U) :=
      addQ_in_RatSet oneQ oneQ oneQ_mem_RatSet oneQ_mem_RatSet

    private theorem twoQ'_ne : (twoQ' : U) ≠ (zeroQ : U) := by
      unfold twoQ'
      intro h
      have hone : isPositiveQ (oneQ : U) := oneQ_pos_priv
      have h_le := addQ_leQ_addQ (zeroQ : U) (oneQ : U) (oneQ : U)
                    zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet hone.1
      rw [addQ_zero_left (oneQ : U) oneQ_mem_RatSet, h] at h_le
      exact zeroQ_ne_oneQ
        (leQ_antisymm (oneQ : U) (zeroQ : U) oneQ_mem_RatSet zeroQ_mem_RatSet h_le hone.1).symm

    private noncomputable def halfQ' (ε : U) : U := mulQ ε (invQ (twoQ' : U))

    private theorem halfQ'_mem (ε : U) (hε : ε ∈ (RatSet : U)) : halfQ' ε ∈ (RatSet : U) :=
      mulQ_in_RatSet ε _ hε (invQ_in_RatSet _ twoQ'_mem)

    private theorem half_add_half' (ε : U) (hε : ε ∈ (RatSet : U)) :
        addQ (halfQ' ε) (halfQ' ε) = ε := by
      show addQ (mulQ ε (invQ twoQ')) (mulQ ε (invQ twoQ')) = ε
      have hinv := invQ_in_RatSet (twoQ' : U) twoQ'_mem
      have inv_add : addQ (invQ (twoQ' : U)) (invQ (twoQ' : U)) = (oneQ : U) := by
        have h1 : addQ (invQ (twoQ' : U)) (invQ (twoQ' : U)) =
            mulQ (invQ (twoQ' : U)) (addQ (oneQ : U) (oneQ : U)) := by
          rw [mulQ_addQ_distrib_left _ oneQ oneQ hinv oneQ_mem_RatSet oneQ_mem_RatSet,
              mulQ_one_right _ hinv]
        rw [h1]; exact mulQ_invQ_left _ twoQ'_mem twoQ'_ne
      rw [← mulQ_addQ_distrib_left ε (invQ twoQ') (invQ twoQ') hε hinv hinv,
          inv_add, mulQ_one_right ε hε]

    private theorem halfQ'_pos (ε : U) (hε : ε ∈ (RatSet : U)) (hε_pos : isPositiveQ ε) :
        isPositiveQ (halfQ' ε) := by
      have hε₂ := halfQ'_mem ε hε
      rcases rat_trichotomy_order (halfQ' ε) hε₂ with h | h | h
      · exact h
      · exfalso
        have := half_add_half' ε hε
        rw [h, addQ_zero_left zeroQ zeroQ_mem_RatSet] at this
        exact hε_pos.2 this
      · exfalso
        have h_le2 := addQ_leQ_addQ (halfQ' ε) (zeroQ : U) (halfQ' ε) hε₂ zeroQ_mem_RatSet hε₂ h.1
        rw [addQ_zero_left (halfQ' ε) hε₂, half_add_half' ε hε] at h_le2
        have h_le3 := leQ_trans ε (halfQ' ε) zeroQ hε hε₂ zeroQ_mem_RatSet h_le2 h.1
        exact hε_pos.2 (leQ_antisymm ε zeroQ hε zeroQ_mem_RatSet h_le3 hε_pos.1).symm

    private theorem strictly_increasing_ge' (φ : U)
        (hφ : IsFunction φ (ω : U) (ω : U))
        (hφ_incr : ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) → m ∈ n → (φ⦅m⦆) ∈ (φ⦅n⦆))
        (n : U) (hn : n ∈ (ω : U)) : n ∈ (φ⦅n⦆) ∨ n = (φ⦅n⦆) := by
      have φ_mem : ∀ k, k ∈ (ω : U) → (φ⦅k⦆) ∈ (ω : U) := fun k hk =>
        ((OrderedPair_mem_CartesianProduct k (φ⦅k⦆) (ω : U) (ω : U)).mp
          (hφ.1 _ (apply_mem φ k (hφ.2 k hk)))).2
      let P := fun k : U => k ∈ (φ⦅k⦆) ∨ k = (φ⦅k⦆)
      have hS_eq : sep (ω : U) P = (ω : U) := by
        apply induction_principle
        · intro x hx; exact ((mem_sep_iff (ω : U) x P).mp hx).1
        · rw [mem_sep_iff]; refine ⟨zero_in_Omega, ?_⟩
          have hφ0 := φ_mem (∅ : U) zero_in_Omega
          rcases trichotomy (∅ : U) (φ⦅(∅ : U)⦆)
              (mem_Omega_is_Nat _ zero_in_Omega) (mem_Omega_is_Nat _ hφ0) with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h (EmptySet_is_empty _)
        · intro k hk_S
          have hk_mem := (mem_sep_iff (ω : U) k P).mp hk_S
          have hk   := hk_mem.1
          have hIH  := hk_mem.2
          have hsk  := succ_in_Omega k hk
          have hφk  := φ_mem k hk
          have hφsk := φ_mem (σ k) hsk
          have hφk_nat  := mem_Omega_is_Nat (φ⦅k⦆)  hφk
          have hφsk_nat := mem_Omega_is_Nat (φ⦅σ k⦆) hφsk
          have h_incr : (φ⦅k⦆) ∈ (φ⦅σ k⦆) := hφ_incr k (σ k) hk hsk (mem_succ_self k)
          rw [mem_sep_iff]; refine ⟨hsk, ?_⟩
          cases hIH with
          | inl hk_in_φk =>
            have hk_in_φsk : k ∈ (φ⦅σ k⦆) :=
              transitive_element_subset (φ⦅σ k⦆) (φ⦅k⦆) hφsk_nat.1 h_incr k hk_in_φk
            exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆)
                (mem_Omega_is_Nat _ hsk) hφsk_nat
                (fun x hx => by
                  rw [mem_succ_iff] at hx
                  cases hx with
                  | inl hx_in_k =>
                    exact transitive_element_subset (φ⦅σ k⦆) (φ⦅k⦆) hφsk_nat.1 h_incr x
                      (transitive_element_subset (φ⦅k⦆) k hφk_nat.1 hk_in_φk x hx_in_k)
                  | inr hx_eq_k => rw [hx_eq_k]; exact hk_in_φsk)
          | inr hk_eq_φk =>
            have hk_in_φsk : k ∈ (φ⦅σ k⦆) := by
              have h := h_incr; rw [← hk_eq_φk] at h; exact h
            exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆)
                (mem_Omega_is_Nat _ hsk) hφsk_nat
                (fun x hx => by
                  rw [mem_succ_iff] at hx
                  cases hx with
                  | inl hx_in_k =>
                    exact transitive_element_subset (φ⦅σ k⦆) k hφsk_nat.1 hk_in_φsk x hx_in_k
                  | inr hx_eq_k => rw [hx_eq_k]; exact hk_in_φsk)
      have hn_S : n ∈ sep (ω : U) P := by rw [hS_eq]; exact hn
      exact ((mem_sep_iff (ω : U) n P).mp hn_S).2

    -- =========================================================================
    -- Section 6: Cauchy arithmetic
    -- =========================================================================

    /-- The pointwise negation of a Cauchy sequence is Cauchy. -/
    theorem cauchyQ_neg (f : U) (hf : IsSeqQ f) (h : IsCauchyQ f) :
        IsCauchyQ (negSeqQ f) := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hc⟩ := h ε hε hε_pos
      refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
      have hfm := seqTermQ_mem_RatSet f m hf hm
      have hfn := seqTermQ_mem_RatSet f n hf hn
      rw [negSeqQ_apply f hf m hm, negSeqQ_apply f hf n hn,
          show subQ (negQ (f⦅m⦆)) (negQ (f⦅n⦆)) = subQ (f⦅n⦆) (f⦅m⦆) from by
            show addQ (negQ (f⦅m⦆)) (negQ (negQ (f⦅n⦆))) = addQ (f⦅n⦆) (negQ (f⦅m⦆))
            rw [negQ_negQ _ hfn, addQ_comm (negQ _) _ (negQ_in_RatSet _ hfm) hfn]]
      exact hc n m hn hm hn_ge hm_ge

    /-- The pointwise sum of two Cauchy sequences is Cauchy. -/
    theorem cauchyQ_add (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_c : IsCauchyQ f) (hg_c : IsCauchyQ g) :
        IsCauchyQ (addSeqQ f g) := by
      intro ε hε hε_pos
      let ε₂ := halfQ' ε
      have hε₂     := halfQ'_mem ε hε
      have hε₂_pos := halfQ'_pos ε hε hε_pos
      obtain ⟨Nf, hNf, hNf_c⟩ := hf_c ε₂ hε₂ hε₂_pos
      obtain ⟨Ng, hNg, hNg_c⟩ := hg_c ε₂ hε₂ hε₂_pos
      let N := maxOf Nf Ng
      have hN := maxOf_in_Omega Nf Ng hNf hNg
      refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
      have hNfm := omega_le_trans' Nf N m hNf hN hm (le_maxOf_left Nf Ng hNf hNg) hm_ge
      have hNgm := omega_le_trans' Ng N m hNg hN hm (le_maxOf_right Nf Ng hNf hNg) hm_ge
      have hNfn := omega_le_trans' Nf N n hNf hN hn (le_maxOf_left Nf Ng hNf hNg) hn_ge
      have hNgn := omega_le_trans' Ng N n hNg hN hn (le_maxOf_right Nf Ng hNf hNg) hn_ge
      have hfm   := seqTermQ_mem_RatSet f m hf hm
      have hfn   := seqTermQ_mem_RatSet f n hf hn
      have hgm   := seqTermQ_mem_RatSet g m hg hm
      have hgn   := seqTermQ_mem_RatSet g n hg hn
      have hfmfn := addQ_in_RatSet _ _ hfm (negQ_in_RatSet _ hfn)
      have hgmgn := addQ_in_RatSet _ _ hgm (negQ_in_RatSet _ hgn)
      have hf_mn := hNf_c m n hm hn hNfm hNfn
      have hg_mn := hNg_c m n hm hn hNgm hNgn
      rw [addSeqQ_apply f g hf hg m hm, addSeqQ_apply f g hf hg n hn]
      -- negQ (fn + gn) = negQ fn + negQ gn
      have negQ_distrib : negQ (addQ (f⦅n⦆) (g⦅n⦆)) = addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆)) := by
        have hfngn   := addQ_in_RatSet (f⦅n⦆) (g⦅n⦆) hfn hgn
        have hNfn'   := negQ_in_RatSet (f⦅n⦆) hfn
        have hNgn'   := negQ_in_RatSet (g⦅n⦆) hgn
        have hNfngn  := negQ_in_RatSet _ hfngn
        have hNfnNgn := addQ_in_RatSet (negQ (f⦅n⦆)) (negQ (g⦅n⦆)) hNfn' hNgn'
        have sum_inv : addQ (addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆))) (addQ (f⦅n⦆) (g⦅n⦆)) = zeroQ := by
          rw [addQ_assoc (negQ (f⦅n⦆)) (negQ (g⦅n⦆)) (addQ (f⦅n⦆) (g⦅n⦆))
                hNfn' hNgn' hfngn,
              ← addQ_assoc (negQ (g⦅n⦆)) (f⦅n⦆) (g⦅n⦆) hNgn' hfn hgn,
              addQ_comm (negQ (g⦅n⦆)) (f⦅n⦆) hNgn' hfn,
              addQ_assoc (f⦅n⦆) (negQ (g⦅n⦆)) (g⦅n⦆) hfn hNgn' hgn,
              negQ_addQ_left (g⦅n⦆) hgn, addQ_zero_right (f⦅n⦆) hfn,
              negQ_addQ_left (f⦅n⦆) hfn]
        symm
        calc addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆))
            = addQ (addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆))) zeroQ :=
                  (addQ_zero_right _ hNfnNgn).symm
          _ = addQ (addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆)))
                   (addQ (addQ (f⦅n⦆) (g⦅n⦆)) (negQ (addQ (f⦅n⦆) (g⦅n⦆)))) :=
                  congrArg (addQ _) (negQ_addQ_right _ hfngn).symm
          _ = addQ (addQ (addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆))) (addQ (f⦅n⦆) (g⦅n⦆)))
                   (negQ (addQ (f⦅n⦆) (g⦅n⦆))) :=
                  (addQ_assoc _ _ _ hNfnNgn hfngn hNfngn).symm
          _ = addQ zeroQ (negQ (addQ (f⦅n⦆) (g⦅n⦆))) :=
                  congrArg (fun x => addQ x _) sum_inv
          _ = negQ (addQ (f⦅n⦆) (g⦅n⦆)) := addQ_zero_left _ hNfngn
      -- subQ (fm+gm) (fn+gn) = (fm-fn) + (gm-gn)
      have h_sub : subQ (addQ (f⦅m⦆) (g⦅m⦆)) (addQ (f⦅n⦆) (g⦅n⦆)) =
          addQ (subQ (f⦅m⦆) (f⦅n⦆)) (subQ (g⦅m⦆) (g⦅n⦆)) :=
        calc addQ (addQ (f⦅m⦆) (g⦅m⦆)) (negQ (addQ (f⦅n⦆) (g⦅n⦆)))
            = addQ (f⦅m⦆) (addQ (g⦅m⦆) (negQ (addQ (f⦅n⦆) (g⦅n⦆)))) := by
                rw [addQ_assoc (f⦅m⦆) (g⦅m⦆) _ hfm hgm
                      (negQ_in_RatSet _ (addQ_in_RatSet _ _ hfn hgn))]
          _ = addQ (f⦅m⦆) (addQ (g⦅m⦆) (addQ (negQ (f⦅n⦆)) (negQ (g⦅n⦆)))) :=
                congrArg (fun x => addQ (f⦅m⦆) (addQ (g⦅m⦆) x)) negQ_distrib
          _ = addQ (addQ (f⦅m⦆) (negQ (f⦅n⦆))) (addQ (g⦅m⦆) (negQ (g⦅n⦆))) := by
                rw [← addQ_assoc (g⦅m⦆) (negQ (f⦅n⦆)) (negQ (g⦅n⦆))
                      hgm (negQ_in_RatSet _ hfn) (negQ_in_RatSet _ hgn),
                    addQ_comm (g⦅m⦆) (negQ (f⦅n⦆)) hgm (negQ_in_RatSet _ hfn),
                    addQ_assoc (negQ (f⦅n⦆)) (g⦅m⦆) (negQ (g⦅n⦆))
                      (negQ_in_RatSet _ hfn) hgm (negQ_in_RatSet _ hgn),
                    ← addQ_assoc (f⦅m⦆) (negQ (f⦅n⦆)) (addQ (g⦅m⦆) (negQ (g⦅n⦆)))
                      hfm (negQ_in_RatSet _ hfn) hgmgn]
      rw [h_sub]
      have h_tri := absQ_triangle (subQ (f⦅m⦆) (f⦅n⦆)) (subQ (g⦅m⦆) (g⦅n⦆)) hfmfn hgmgn
      have h_sum_lt : ltQ (addQ (absQ (subQ (f⦅m⦆) (f⦅n⦆))) (absQ (subQ (g⦅m⦆) (g⦅n⦆)))) ε := by
        have h := ltQ_add_of_leQ_ltQ'
          (absQ (subQ (f⦅m⦆) (f⦅n⦆))) (absQ (subQ (g⦅m⦆) (g⦅n⦆))) ε₂ ε₂
          (absQ_in_RatSet _ hfmfn) (absQ_in_RatSet _ hgmgn) hε₂ hε₂ hf_mn.1 hg_mn
        rwa [half_add_half' ε hε] at h
      exact leQ_ltQ_trans' _  _ ε
        (absQ_in_RatSet _ (addQ_in_RatSet _ _ hfmfn hgmgn))
        (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfmfn) (absQ_in_RatSet _ hgmgn))
        hε h_tri h_sum_lt

    /-- The pointwise difference of two Cauchy sequences is Cauchy. -/
    theorem cauchyQ_sub (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_c : IsCauchyQ f) (hg_c : IsCauchyQ g) :
        IsCauchyQ (addSeqQ f (negSeqQ g)) :=
      cauchyQ_add f (negSeqQ g) hf (negSeqQ_isSeqQ g hg)
        hf_c (cauchyQ_neg g hg hg_c)

    /-- The pointwise scalar multiple c·f of a Cauchy sequence is Cauchy. -/
    theorem cauchyQ_const_mul (c f : U)
        (hc : c ∈ (RatSet : U)) (hf : IsSeqQ f) (h : IsCauchyQ f) :
        IsCauchyQ (mulSeqQ (constSeqQ c) f) := by
      by_cases h_zero : c = (zeroQ : U)
      · subst h_zero
        intro ε hε hε_pos
        refine ⟨(∅ : U), zero_in_Omega, fun m n hm hn _ _ => ?_⟩
        have hfm := seqTermQ_mem_RatSet f m hf hm
        have hfn := seqTermQ_mem_RatSet f n hf hn
        rw [mulSeqQ_apply _ f (constSeqQ_isSeqQ (zeroQ : U) zeroQ_mem_RatSet) hf m hm,
            mulSeqQ_apply _ f (constSeqQ_isSeqQ (zeroQ : U) zeroQ_mem_RatSet) hf n hn,
            constSeqQ_apply (zeroQ : U) zeroQ_mem_RatSet m hm,
            constSeqQ_apply (zeroQ : U) zeroQ_mem_RatSet n hn,
            mulQ_zero_left (f⦅m⦆) hfm, mulQ_zero_left (f⦅n⦆) hfn,
            show subQ (zeroQ : U) (zeroQ : U) = (zeroQ : U) from by
              show addQ (zeroQ : U) (negQ (zeroQ : U)) = (zeroQ : U)
              rw [negQ_zero, addQ_zero_left (zeroQ : U) zeroQ_mem_RatSet],
            show absQ (zeroQ : U) = (zeroQ : U) from
              (absQ_eq_zero_iff (zeroQ : U) zeroQ_mem_RatSet).mpr rfl]
        exact hε_pos
      · have hAc     := absQ_in_RatSet c hc
        have hAc_pos := absQ_pos c hc h_zero
        have hAc_ne  : absQ c ≠ (zeroQ : U) := hAc_pos.2.symm
        intro ε hε hε_pos
        let δ := divQ ε (absQ c)
        have hδ     := divQ_in_RatSet ε (absQ c) hε hAc
        have h_eq_ε : mulQ (absQ c) δ = ε := mulQ_divQ_cancel ε (absQ c) hε hAc hAc_ne
        have hδ_pos : isPositiveQ δ := by
          constructor
          · rcases leQ_total (zeroQ : U) δ zeroQ_mem_RatSet hδ with hge | hle
            · exact hge
            · exfalso
              have h1 := mulQ_leQ_mulQ_of_nonneg_left (absQ c) δ (zeroQ : U)
                           hAc hδ zeroQ_mem_RatSet hle hAc_pos.1
              rw [mulQ_zero_right (absQ c) hAc, h_eq_ε] at h1
              exact hε_pos.2 (leQ_antisymm ε (zeroQ : U) hε zeroQ_mem_RatSet h1 hε_pos.1).symm
          · intro h_eq
            exact hε_pos.2 (h_eq_ε.symm.trans
              (show mulQ (absQ c) δ = zeroQ from by
                rw [show δ = zeroQ from h_eq.symm]; exact mulQ_zero_right _ hAc)).symm
        obtain ⟨N, hN, hN_c⟩ := h δ hδ hδ_pos
        refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
        have hfm   := seqTermQ_mem_RatSet f m hf hm
        have hfn   := seqTermQ_mem_RatSet f n hf hn
        have hfmfn := addQ_in_RatSet _ _ hfm (negQ_in_RatSet _ hfn)
        have hAfmfn := absQ_in_RatSet _ hfmfn
        rw [mulSeqQ_apply _ f (constSeqQ_isSeqQ c hc) hf m hm,
            mulSeqQ_apply _ f (constSeqQ_isSeqQ c hc) hf n hn,
            constSeqQ_apply c hc m hm, constSeqQ_apply c hc n hn,
            show subQ (mulQ c (f⦅m⦆)) (mulQ c (f⦅n⦆)) = mulQ c (subQ (f⦅m⦆) (f⦅n⦆)) from by
              show addQ (mulQ c (f⦅m⦆)) (negQ (mulQ c (f⦅n⦆))) =
                   mulQ c (addQ (f⦅m⦆) (negQ (f⦅n⦆)))
              rw [negQ_mulQ_right c (f⦅n⦆) hc hfn,
                  mulQ_addQ_distrib_left c (f⦅m⦆) (negQ (f⦅n⦆)) hc hfm (negQ_in_RatSet _ hfn)],
            absQ_mulQ c (subQ (f⦅m⦆) (f⦅n⦆)) hc hfmfn]
        have hmn := hN_c m n hm hn hm_ge hn_ge
        exact ⟨h_eq_ε ▸ mulQ_leQ_mulQ_of_nonneg_left (absQ c) (absQ (subQ (f⦅m⦆) (f⦅n⦆))) δ
                  hAc hAfmfn hδ hmn.1 hAc_pos.1,
               fun h_eq => hmn.2 (mulQ_left_cancel _ δ (absQ c) hAfmfn hδ hAc hAc_ne
                 (h_eq.trans h_eq_ε.symm))⟩

    /-- The pointwise product of two Cauchy sequences is Cauchy. -/
    theorem cauchyQ_mul (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_c : IsCauchyQ f) (hg_c : IsCauchyQ g) :
        IsCauchyQ (mulSeqQ f g) := by
      obtain ⟨M_f, hM_f, hM_f_pos, hbound_f⟩ := cauchy_bounded f hf hf_c
      obtain ⟨M_g, hM_g, hM_g_pos, hbound_g⟩ := cauchy_bounded g hg hg_c
      let M := addQ M_f M_g
      have hM : M ∈ (RatSet : U) := addQ_in_RatSet M_f M_g hM_f hM_g
      have hM_pos : isPositiveQ M := by
        constructor
        · have h1 := addQ_leQ_addQ zeroQ M_f M_g zeroQ_mem_RatSet hM_f hM_g hM_f_pos.1
          rw [addQ_zero_left M_g hM_g] at h1
          exact leQ_trans zeroQ M_g M zeroQ_mem_RatSet hM_g hM hM_g_pos.1 h1
        · intro heq
          have h1 := addQ_leQ_addQ zeroQ M_g M_f zeroQ_mem_RatSet hM_g hM_f hM_g_pos.1
          rw [addQ_zero_left M_f hM_f, addQ_comm M_g M_f hM_g hM_f] at h1
          exact hM_f_pos.2 (leQ_antisymm M_f zeroQ hM_f zeroQ_mem_RatSet
            (heq ▸ h1) hM_f_pos.1).symm
      have hM_ne : M ≠ (zeroQ : U) := hM_pos.2.symm
      intro ε hε hε_pos
      let δ := divQ ε M
      have hδ     := divQ_in_RatSet ε M hε hM
      have h_δM   : mulQ δ M = ε := divQ_mulQ_cancel ε M hε hM hM_ne
      have hδ_pos : isPositiveQ δ := by
        constructor
        · rcases leQ_total (zeroQ : U) δ zeroQ_mem_RatSet hδ with hge | hle
          · exact hge
          · exfalso
            have h1 := mulQ_leQ_mulQ_of_nonneg_right δ (zeroQ : U) M hδ zeroQ_mem_RatSet hM
                         hle hM_pos.1
            rw [mulQ_zero_left M hM, h_δM] at h1
            exact hε_pos.2 (leQ_antisymm ε (zeroQ : U) hε zeroQ_mem_RatSet h1 hε_pos.1).symm
        · intro h_eq
          exact hε_pos.2 (h_δM.symm.trans
            (show mulQ δ M = zeroQ from by
              rw [show δ = zeroQ from h_eq.symm]; exact mulQ_zero_left M hM)).symm
      obtain ⟨Nf, hNf, hNf_c⟩ := hf_c δ hδ hδ_pos
      obtain ⟨Ng, hNg, hNg_c⟩ := hg_c δ hδ hδ_pos
      let N := maxOf Nf Ng
      have hN := maxOf_in_Omega Nf Ng hNf hNg
      refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
      have hNfm := omega_le_trans' Nf N m hNf hN hm (le_maxOf_left Nf Ng hNf hNg) hm_ge
      have hNgm := omega_le_trans' Ng N m hNg hN hm (le_maxOf_right Nf Ng hNf hNg) hm_ge
      have hNfn := omega_le_trans' Nf N n hNf hN hn (le_maxOf_left Nf Ng hNf hNg) hn_ge
      have hNgn := omega_le_trans' Ng N n hNg hN hn (le_maxOf_right Nf Ng hNf hNg) hn_ge
      have hfm    := seqTermQ_mem_RatSet f m hf hm
      have hfn    := seqTermQ_mem_RatSet f n hf hn
      have hgm    := seqTermQ_mem_RatSet g m hg hm
      have hgn    := seqTermQ_mem_RatSet g n hg hn
      have hfmfn  := addQ_in_RatSet _ _ hfm (negQ_in_RatSet _ hfn)
      have hgmgn  := addQ_in_RatSet _ _ hgm (negQ_in_RatSet _ hgn)
      have h_fmgm := mulQ_in_RatSet (f⦅m⦆) (g⦅m⦆) hfm hgm
      have h_fngn := mulQ_in_RatSet (f⦅n⦆) (g⦅n⦆) hfn hgn
      have h_fngm := mulQ_in_RatSet (f⦅n⦆) (g⦅m⦆) hfn hgm
      have hf_mn  := hNf_c m n hm hn hNfm hNfn
      have hg_mn  := hNg_c m n hm hn hNgm hNgn
      rw [mulSeqQ_apply f g hf hg m hm, mulSeqQ_apply f g hf hg n hn]
      -- f(m)·g(m) - f(n)·g(n) = (f(m)-f(n))·g(m) + f(n)·(g(m)-g(n))
      have h_id : subQ (mulQ (f⦅m⦆) (g⦅m⦆)) (mulQ (f⦅n⦆) (g⦅n⦆)) =
          addQ (mulQ (subQ (f⦅m⦆) (f⦅n⦆)) (g⦅m⦆)) (mulQ (f⦅n⦆) (subQ (g⦅m⦆) (g⦅n⦆))) := by
        show addQ (mulQ (f⦅m⦆) (g⦅m⦆)) (negQ (mulQ (f⦅n⦆) (g⦅n⦆))) =
             addQ (mulQ (addQ (f⦅m⦆) (negQ (f⦅n⦆))) (g⦅m⦆))
                  (mulQ (f⦅n⦆) (addQ (g⦅m⦆) (negQ (g⦅n⦆))))
        rw [mulQ_addQ_distrib_right (f⦅m⦆) (negQ (f⦅n⦆)) (g⦅m⦆)
              hfm (negQ_in_RatSet _ hfn) hgm,
            ← negQ_mulQ_left (f⦅n⦆) (g⦅m⦆) hfn hgm,
            mulQ_addQ_distrib_left (f⦅n⦆) (g⦅m⦆) (negQ (g⦅n⦆))
              hfn hgm (negQ_in_RatSet _ hgn),
            ← negQ_mulQ_right (f⦅n⦆) (g⦅n⦆) hfn hgn]
        symm
        rw [addQ_assoc (mulQ (f⦅m⦆) (g⦅m⦆)) (negQ (mulQ (f⦅n⦆) (g⦅m⦆)))
              (addQ (mulQ (f⦅n⦆) (g⦅m⦆)) (negQ (mulQ (f⦅n⦆) (g⦅n⦆))))
              h_fmgm (negQ_in_RatSet _ h_fngm)
              (addQ_in_RatSet _ _ h_fngm (negQ_in_RatSet _ h_fngn)),
            ← addQ_assoc (negQ (mulQ (f⦅n⦆) (g⦅m⦆))) (mulQ (f⦅n⦆) (g⦅m⦆))
              (negQ (mulQ (f⦅n⦆) (g⦅n⦆)))
              (negQ_in_RatSet _ h_fngm) h_fngm (negQ_in_RatSet _ h_fngn),
            negQ_addQ_left (mulQ (f⦅n⦆) (g⦅m⦆)) h_fngm,
            addQ_zero_left (negQ (mulQ (f⦅n⦆) (g⦅n⦆))) (negQ_in_RatSet _ h_fngn)]
      rw [h_id]
      have h_T1   := mulQ_in_RatSet (subQ (f⦅m⦆) (f⦅n⦆)) (g⦅m⦆) hfmfn hgm
      have h_T2   := mulQ_in_RatSet (f⦅n⦆) (subQ (g⦅m⦆) (g⦅n⦆)) hfn hgmgn
      have h_tri  := absQ_triangle _ _ h_T1 h_T2
      rw [absQ_mulQ (subQ (f⦅m⦆) (f⦅n⦆)) (g⦅m⦆) hfmfn hgm,
          absQ_mulQ (f⦅n⦆) (subQ (g⦅m⦆) (g⦅n⦆)) hfn hgmgn] at h_tri
      have hAfmfn := absQ_in_RatSet _ hfmfn
      have hAgm   := absQ_in_RatSet _ hgm
      have hAfn   := absQ_in_RatSet _ hfn
      have hAgmgn := absQ_in_RatSet _ hgmgn
      -- |f(m)-f(n)|·|g(m)| ≤ |f(m)-f(n)|·M_g < δ·M_g
      have h_first : ltQ (mulQ (absQ (subQ (f⦅m⦆) (f⦅n⦆))) (absQ (g⦅m⦆))) (mulQ δ M_g) := by
        have h_le := mulQ_leQ_mulQ_of_nonneg_left (absQ (subQ (f⦅m⦆) (f⦅n⦆))) (absQ (g⦅m⦆)) M_g
                       hAfmfn hAgm hM_g (hbound_g m hm) (absQ_nonneg _ hfmfn)
        have h_lt : ltQ (mulQ (absQ (subQ (f⦅m⦆) (f⦅n⦆))) M_g) (mulQ δ M_g) :=
          ⟨mulQ_leQ_mulQ_of_nonneg_right _ δ M_g hAfmfn hδ hM_g hf_mn.1 hM_g_pos.1,
           fun heq => hf_mn.2 (mulQ_right_cancel _ δ M_g hAfmfn hδ hM_g hM_g_pos.2.symm heq)⟩
        exact leQ_ltQ_trans' _ _ _ (mulQ_in_RatSet _ _ hAfmfn hAgm)
          (mulQ_in_RatSet _ _ hAfmfn hM_g) (mulQ_in_RatSet δ M_g hδ hM_g) h_le h_lt
      -- |f(n)|·|g(m)-g(n)| ≤ M_f·|g(m)-g(n)| < M_f·δ
      have h_second : ltQ (mulQ (absQ (f⦅n⦆)) (absQ (subQ (g⦅m⦆) (g⦅n⦆)))) (mulQ M_f δ) := by
        have h_le := mulQ_leQ_mulQ_of_nonneg_right (absQ (f⦅n⦆)) M_f (absQ (subQ (g⦅m⦆) (g⦅n⦆)))
                       hAfn hM_f hAgmgn (hbound_f n hn) (absQ_nonneg _ hgmgn)
        have h_lt : ltQ (mulQ M_f (absQ (subQ (g⦅m⦆) (g⦅n⦆)))) (mulQ M_f δ) :=
          ⟨mulQ_leQ_mulQ_of_nonneg_left M_f _ δ hM_f hAgmgn hδ hg_mn.1 hM_f_pos.1,
           fun heq => hg_mn.2 (mulQ_left_cancel _ δ M_f hAgmgn hδ hM_f hM_f_pos.2.symm heq)⟩
        exact leQ_ltQ_trans' _ _ _ (mulQ_in_RatSet _ _ hAfn hAgmgn)
          (mulQ_in_RatSet _ _ hM_f hAgmgn) (mulQ_in_RatSet M_f δ hM_f hδ) h_le h_lt
      -- δ·M_g + M_f·δ = ε
      have h_δ_eq : addQ (mulQ δ M_g) (mulQ M_f δ) = ε :=
        calc addQ (mulQ δ M_g) (mulQ M_f δ)
            = addQ (mulQ δ M_g) (mulQ δ M_f) := by rw [mulQ_comm M_f δ hM_f hδ]
          _ = mulQ δ (addQ M_g M_f) := by
                rw [← mulQ_addQ_distrib_left δ M_g M_f hδ hM_g hM_f]
          _ = mulQ δ M := by rw [addQ_comm M_g M_f hM_g hM_f]
          _ = ε := h_δM
      have h_sum_lt := ltQ_add_of_leQ_ltQ' _ _ _ _
        (mulQ_in_RatSet _ _ hAfmfn hAgm) (mulQ_in_RatSet _ _ hAfn hAgmgn)
        (mulQ_in_RatSet δ M_g hδ hM_g) (mulQ_in_RatSet M_f δ hM_f hδ)
        h_first.1 h_second
      rw [h_δ_eq] at h_sum_lt
      exact leQ_ltQ_trans' _ _ ε
        (absQ_in_RatSet _ (addQ_in_RatSet _ _ h_T1 h_T2))
        (addQ_in_RatSet _ _ (mulQ_in_RatSet _ _ hAfmfn hAgm) (mulQ_in_RatSet _ _ hAfn hAgmgn))
        hε h_tri h_sum_lt

    -- =========================================================================
    -- Section 7: Subsequences of Cauchy sequences
    -- =========================================================================

    /-- Any subsequence of a Cauchy sequence is Cauchy. -/
    theorem subseq_of_cauchyQ (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_c : IsCauchyQ f) (hsub : IsSubseqOf g f) :
        IsCauchyQ g := by
      obtain ⟨φ, hφ_fn, hφ_incr, hg_eq⟩ := hsub
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_c⟩ := hf_c ε hε hε_pos
      refine ⟨N, hN, fun m n hm hn hm_ge hn_ge => ?_⟩
      have hφ_mem : ∀ k, k ∈ (ω : U) → (φ⦅k⦆) ∈ (ω : U) := fun k hk =>
        ((OrderedPair_mem_CartesianProduct k (φ⦅k⦆) (ω : U) (ω : U)).mp
          (hφ_fn.1 _ (apply_mem φ k (hφ_fn.2 k hk)))).2
      have hφm := hφ_mem m hm
      have hφn := hφ_mem n hn
      have hN_φm : N ∈ (φ⦅m⦆) ∨ N = (φ⦅m⦆) :=
        omega_le_trans' N m (φ⦅m⦆) hN hm hφm hm_ge
          (strictly_increasing_ge' φ hφ_fn hφ_incr m hm)
      have hN_φn : N ∈ (φ⦅n⦆) ∨ N = (φ⦅n⦆) :=
        omega_le_trans' N n (φ⦅n⦆) hN hn hφn hn_ge
          (strictly_increasing_ge' φ hφ_fn hφ_incr n hn)
      rw [hg_eq m hm, hg_eq n hn]
      exact hN_c (φ⦅m⦆) (φ⦅n⦆) hφm hφn hN_φm hN_φn

    -- =========================================================================
    -- Section 8: Cauchy equivalence relation
    -- =========================================================================

    /-- Two Cauchy sequences f, g are equivalent if their difference converges to 0. -/
    def CauchyEquivQ (f g : U) : Prop :=
      convergesToQ (addSeqQ f (negSeqQ g)) (zeroQ : U)

    /-- CauchyEquivQ is reflexive. -/
    theorem cauchyQ_equiv_refl (f : U) (hf : IsSeqQ f) :
        CauchyEquivQ f f := by
      unfold CauchyEquivQ
      have hncf  := negSeqQ_isSeqQ f hf
      have hfncf := addSeqQ_isSeqQ f _ hf hncf
      have h_zero : convergesToQ (constSeqQ (zeroQ : U)) (zeroQ : U) :=
        convergesToQ_const (zeroQ : U) zeroQ_mem_RatSet
      apply convergesToQ_of_eventually_eq (constSeqQ (zeroQ : U)) _ (zeroQ : U)
        zeroQ_mem_RatSet (constSeqQ_isSeqQ _ zeroQ_mem_RatSet) hfncf
        (∅ : U) zero_in_Omega
        (fun n hn _ => by
          rw [constSeqQ_apply (zeroQ : U) zeroQ_mem_RatSet n hn,
              addSeqQ_apply f (negSeqQ f) hf hncf n hn,
              negSeqQ_apply f hf n hn]
          exact (negQ_addQ_right _ (seqTermQ_mem_RatSet f n hf hn)).symm)
        h_zero

    /-- CauchyEquivQ is symmetric. -/
    theorem cauchyQ_equiv_symm (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h : CauchyEquivQ f g) : CauchyEquivQ g f := by
      unfold CauchyEquivQ at *
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_h⟩ := h ε hε hε_pos
      refine ⟨N, hN, fun n hn hn_ge => ?_⟩
      have hfn  := seqTermQ_mem_RatSet f n hf hn
      have hgn  := seqTermQ_mem_RatSet g n hg hn
      have hncg := negSeqQ_isSeqQ g hg
      have hncf := negSeqQ_isSeqQ f hf
      -- Get bound for f-g from h
      have h_fg := hN_h n hn hn_ge
      rw [addSeqQ_apply f (negSeqQ g) hf hncg n hn,
          negSeqQ_apply g hg n hn,
          show subQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) (zeroQ : U) =
               addQ (f⦅n⦆) (negQ (g⦅n⦆)) from by
            show addQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) (negQ (zeroQ : U)) =
                 addQ (f⦅n⦆) (negQ (g⦅n⦆))
            rw [negQ_zero, addQ_zero_right _ (addQ_in_RatSet _ _ hfn (negQ_in_RatSet _ hgn))]] at h_fg
      -- Prove g-f bound using absQ symmetry
      rw [addSeqQ_apply g (negSeqQ f) hg hncf n hn,
          negSeqQ_apply f hf n hn,
          show subQ (addQ (g⦅n⦆) (negQ (f⦅n⦆))) (zeroQ : U) =
               addQ (g⦅n⦆) (negQ (f⦅n⦆)) from by
            show addQ (addQ (g⦅n⦆) (negQ (f⦅n⦆))) (negQ (zeroQ : U)) =
                 addQ (g⦅n⦆) (negQ (f⦅n⦆))
            rw [negQ_zero, addQ_zero_right _ (addQ_in_RatSet _ _ hgn (negQ_in_RatSet _ hfn))]]
      -- Show g(n) - f(n) = -(f(n) - g(n)) and use absQ_negQ
      have hab_fg := addQ_in_RatSet _ _ hfn (negQ_in_RatSet _ hgn)
      have hab_gf := addQ_in_RatSet _ _ hgn (negQ_in_RatSet _ hfn)
      have h_neg_eq : addQ (g⦅n⦆) (negQ (f⦅n⦆)) = negQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) := by
        have h_sum : addQ (addQ (f⦅n⦆) (negQ (g⦅n⦆)))
                          (addQ (g⦅n⦆) (negQ (f⦅n⦆))) = zeroQ := by
          rw [addQ_assoc (f⦅n⦆) (negQ (g⦅n⦆)) (addQ (g⦅n⦆) (negQ (f⦅n⦆)))
                hfn (negQ_in_RatSet _ hgn)
                (addQ_in_RatSet _ _ hgn (negQ_in_RatSet _ hfn)),
              ← addQ_assoc (negQ (g⦅n⦆)) (g⦅n⦆) (negQ (f⦅n⦆))
                (negQ_in_RatSet _ hgn) hgn (negQ_in_RatSet _ hfn),
              negQ_addQ_left (g⦅n⦆) hgn,
              addQ_zero_left (negQ (f⦅n⦆)) (negQ_in_RatSet _ hfn),
              negQ_addQ_right (f⦅n⦆) hfn]
        calc addQ (g⦅n⦆) (negQ (f⦅n⦆))
            = addQ zeroQ (addQ (g⦅n⦆) (negQ (f⦅n⦆))) := (addQ_zero_left _ hab_gf).symm
          _ = addQ (addQ (negQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))))
                        (addQ (f⦅n⦆) (negQ (g⦅n⦆)))) (addQ (g⦅n⦆) (negQ (f⦅n⦆))) :=
                  congrArg (fun x => addQ x _) (negQ_addQ_left _ hab_fg).symm
          _ = addQ (negQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))))
                   (addQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) (addQ (g⦅n⦆) (negQ (f⦅n⦆)))) :=
                  addQ_assoc _ _ _ (negQ_in_RatSet _ hab_fg) hab_fg hab_gf
          _ = addQ (negQ (addQ (f⦅n⦆) (negQ (g⦅n⦆)))) zeroQ :=
                  congrArg (addQ _) h_sum
          _ = negQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) :=
                  addQ_zero_right _ (negQ_in_RatSet _ hab_fg)
      rw [h_neg_eq, absQ_negQ _ hab_fg]
      exact h_fg

    /-- CauchyEquivQ is transitive. -/
    theorem cauchyQ_equiv_trans (f g h : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g) (hh : IsSeqQ h)
        (h_fg : CauchyEquivQ f g) (h_gh : CauchyEquivQ g h) :
        CauchyEquivQ f h := by
      unfold CauchyEquivQ at *
      have hncg := negSeqQ_isSeqQ g hg
      have hnch := negSeqQ_isSeqQ h hh
      have hfncg := addSeqQ_isSeqQ f _ hf hncg
      have hgnch := addSeqQ_isSeqQ g _ hg hnch
      have hfnch := addSeqQ_isSeqQ f _ hf hnch
      -- (f-g) + (g-h) → 0+0 = 0 by convergesToQ_add
      have h_sum := convergesToQ_add (addSeqQ f (negSeqQ g)) (addSeqQ g (negSeqQ h))
        (zeroQ : U) (zeroQ : U) zeroQ_mem_RatSet zeroQ_mem_RatSet
        hfncg hgnch h_fg h_gh
      rw [addQ_zero_left zeroQ zeroQ_mem_RatSet] at h_sum
      -- ((f-g)+(g-h))(n) = (f-h)(n) for all n
      apply convergesToQ_of_eventually_eq
        (addSeqQ (addSeqQ f (negSeqQ g)) (addSeqQ g (negSeqQ h)))
        (addSeqQ f (negSeqQ h))
        (zeroQ : U)
        zeroQ_mem_RatSet
        (addSeqQ_isSeqQ _ _ hfncg hgnch)
        hfnch
        (∅ : U) zero_in_Omega
        (fun n hn _ => by
          have hfn := seqTermQ_mem_RatSet f n hf hn
          have hgn := seqTermQ_mem_RatSet g n hg hn
          have hhn := seqTermQ_mem_RatSet h n hh hn
          rw [addSeqQ_apply _ _ hfncg hgnch n hn,
              addSeqQ_apply f _ hf hncg n hn,
              negSeqQ_apply g hg n hn,
              addSeqQ_apply g _ hg hnch n hn,
              negSeqQ_apply h hh n hn,
              addSeqQ_apply f _ hf hnch n hn,
              negSeqQ_apply h hh n hn]
          -- (fn + (-gn)) + (gn + (-hn)) = fn + (-hn)
          calc addQ (addQ (f⦅n⦆) (negQ (g⦅n⦆))) (addQ (g⦅n⦆) (negQ (h⦅n⦆)))
              = addQ (f⦅n⦆) (addQ (negQ (g⦅n⦆)) (addQ (g⦅n⦆) (negQ (h⦅n⦆)))) := by
                    rw [addQ_assoc (f⦅n⦆) (negQ (g⦅n⦆)) _ hfn (negQ_in_RatSet _ hgn)
                          (addQ_in_RatSet _ _ hgn (negQ_in_RatSet _ hhn))]
            _ = addQ (f⦅n⦆) (addQ (addQ (negQ (g⦅n⦆)) (g⦅n⦆)) (negQ (h⦅n⦆))) := by
                    rw [← addQ_assoc (negQ (g⦅n⦆)) (g⦅n⦆) (negQ (h⦅n⦆))
                          (negQ_in_RatSet _ hgn) hgn (negQ_in_RatSet _ hhn)]
            _ = addQ (f⦅n⦆) (addQ zeroQ (negQ (h⦅n⦆))) := by
                    rw [negQ_addQ_left (g⦅n⦆) hgn]
            _ = addQ (f⦅n⦆) (negQ (h⦅n⦆)) := by
                    rw [addQ_zero_left (negQ (h⦅n⦆)) (negQ_in_RatSet _ hhn)])
        h_sum

  end Rat.CauchyQ

end ZFC

export ZFC.Rat.CauchyQ (
  IsCauchyQ
  cauchy_of_convergentQ
  cauchy_bounded
  constSeqQ_isCauchy
  cauchyQ_neg
  cauchyQ_add
  cauchyQ_sub
  cauchyQ_const_mul
  cauchyQ_mul
  subseq_of_cauchyQ
  CauchyEquivQ
  cauchyQ_equiv_refl
  cauchyQ_equiv_symm
  cauchyQ_equiv_trans
)
