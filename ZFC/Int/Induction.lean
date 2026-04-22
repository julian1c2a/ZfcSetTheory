/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Induction Principles

  This module provides induction and well-ordering principles for ℤ
  via the absolute value function |·| : ℤ → ω.

  ## Main Theorems

  * `int_induction_abs` — Induction on |x|: prove P(0),
      then P(intClass n ∅) and P(intClass ∅ n) for successor n,
      to conclude P(x) for all x ∈ ℤ.
  * `int_strong_induction_abs` — Strong induction on |x|:
      if ∀ x ∈ ℤ, (∀ y ∈ ℤ, |y| ∈ |x| → P y) → P x,
      then P holds for all x ∈ ℤ.
  * `int_well_ordering_abs` — Well-ordering on ℤ via |x|:
      any nonempty predicate on ℤ has a minimal element w.r.t. |·|.
  * `int_induction_nonneg` — Induction for non-negative integers
      via the embedding natToInt.
-/

import ZFC.Int.Abs
import ZFC.Nat.WellFounded

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
  open ZFC.Nat.Add
  open ZFC.Nat.WellFounded
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Int.Embedding
  open ZFC.Int.Abs

  universe u
  variable {U : Type u}

  namespace Int.Induction

    -- =========================================================================
    -- Section 1: Induction on |x|
    -- =========================================================================

    /-- **Induction on absolute value**: to prove P(x) for all x ∈ ℤ,
        it suffices to prove:
        1. P(0)
        2. For all n ∈ ω, P(intClass n ∅) → P(intClass (σ n) ∅)
        3. For all n ∈ ω, P(intClass ∅ n) → P(intClass ∅ (σ n))

        This reduces integer induction to natural number induction
        on the absolute value |x|. -/
    theorem int_induction_abs (P : U → Prop)
        (h_zero : P (zeroZ : U))
        (h_pos_succ : ∀ n : U, n ∈ (ω : U) →
          P (intClass n (∅ : U)) → P (intClass (σ n) (∅ : U)))
        (h_neg_succ : ∀ n : U, n ∈ (ω : U) →
          P (intClass (∅ : U) n) → P (intClass (∅ : U) (σ n))) :
        ∀ x : U, x ∈ (IntSet : U) → P x := by
      -- Prove by nat induction that P holds for intClass n ∅ and intClass ∅ n
      -- for all n ∈ ω, then use int_trichotomy.
      have h_pos : ∀ n : U, n ∈ (ω : U) → P (intClass n (∅ : U)) := by
        -- Define S = {n ∈ ω | P(intClass n ∅)} and show S = ω
        let S := sep (ω : U) (fun n => P (intClass n (∅ : U)))
        have hS_zero : (∅ : U) ∈ S := by
          rw [mem_sep_iff]; exact ⟨zero_in_Omega, h_zero⟩
        have hS_succ : ∀ k, k ∈ S → σ k ∈ S := by
          intro k hk; rw [mem_sep_iff] at hk ⊢
          exact ⟨succ_in_Omega k hk.1, h_pos_succ k hk.1 hk.2⟩
        have hS_eq : S = (ω : U) :=
          induction_principle S (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
            hS_zero hS_succ
        intro n hn
        have : n ∈ S := by rw [hS_eq]; exact hn
        rw [mem_sep_iff] at this; exact this.2
      have h_neg : ∀ n : U, n ∈ (ω : U) → P (intClass (∅ : U) n) := by
        let S := sep (ω : U) (fun n => P (intClass (∅ : U) n))
        have hS_zero : (∅ : U) ∈ S := by
          rw [mem_sep_iff]; exact ⟨zero_in_Omega, h_zero⟩
        have hS_succ : ∀ k, k ∈ S → σ k ∈ S := by
          intro k hk; rw [mem_sep_iff] at hk ⊢
          exact ⟨succ_in_Omega k hk.1, h_neg_succ k hk.1 hk.2⟩
        have hS_eq : S = (ω : U) :=
          induction_principle S (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
            hS_zero hS_succ
        intro n hn
        have : n ∈ S := by rw [hS_eq]; exact hn
        rw [mem_sep_iff] at this; exact this.2
      intro x hx
      rcases int_trichotomy x hx with rfl | ⟨n, hn, _, rfl⟩ | ⟨m, hm, _, rfl⟩
      · exact h_zero
      · exact h_pos n hn
      · exact h_neg m hm

    -- =========================================================================
    -- Section 2: Strong induction on |x|
    -- =========================================================================

    /-- **Strong induction on absolute value**: to prove P(x) for all x ∈ ℤ,
        it suffices to show that for every x ∈ ℤ, if P(y) holds for all
        y ∈ ℤ with |y| ∈ |x| (i.e. |y| < |x| in ω), then P(x). -/
    theorem int_strong_induction_abs (P : U → Prop)
        (h_step : ∀ x : U, x ∈ (IntSet : U) →
          (∀ y : U, y ∈ (IntSet : U) → absZ y ∈ absZ x → P y) → P x) :
        ∀ x : U, x ∈ (IntSet : U) → P x := by
      -- Use strong_induction_principle on ω for Q(n) = "P(x) for all x with |x| = n"
      suffices h_all : ∀ n : U, n ∈ (ω : U) →
          ∀ x : U, x ∈ (IntSet : U) → absZ x = n → P x by
        intro x hx
        exact h_all (absZ x) (absZ_in_omega x hx) x hx rfl
      -- Build S = {n ∈ ω | ∀ x ∈ IntSet, |x| = n → P x} and show S = ω
      let S := sep (ω : U)
        (fun n => ∀ x : U, x ∈ (IntSet : U) → absZ x = n → P x)
      have hS_eq : S = (ω : U) := by
        apply strong_induction_principle S
          (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
        intro n hn ih_n
        rw [mem_sep_iff]
        refine ⟨hn, fun x hx h_abs => ?_⟩
        apply h_step x hx
        intro y hy h_lt
        rw [h_abs] at h_lt
        -- |y| ∈ n, so |y| ∈ S by ih_n
        have h_absY_in_S : absZ y ∈ S := ih_n (absZ y) h_lt
        rw [mem_sep_iff] at h_absY_in_S
        exact h_absY_in_S.2 y hy rfl
      intro n hn
      have : n ∈ S := by rw [hS_eq]; exact hn
      rw [mem_sep_iff] at this; exact this.2

    -- =========================================================================
    -- Section 3: Well-ordering via |x|
    -- =========================================================================

    /-- **Well-ordering principle for ℤ via |·|**: if there exists
        x ∈ ℤ satisfying P(x), then there exists z ∈ ℤ satisfying P(z)
        with |z| minimal (i.e., for all w ∈ ℤ with P(w), |z| ∈ |w| ∨ |z| = |w|). -/
    theorem int_well_ordering_abs (P : U → Prop)
        (h_nonempty : ∃ x : U, x ∈ (IntSet : U) ∧ P x) :
        ∃ z : U, z ∈ (IntSet : U) ∧ P z ∧
          ∀ w : U, w ∈ (IntSet : U) → P w →
            (absZ z ∈ absZ w ∨ absZ z = absZ w) := by
      -- Lift to ω: define Q(n) = ∃ x ∈ IntSet, P(x) ∧ absZ(x) = n
      obtain ⟨x₀, hx₀, hPx₀⟩ := h_nonempty
      have h_omega_nonempty : ∃ k : U, k ∈ (ω : U) ∧
          (∃ x : U, x ∈ (IntSet : U) ∧ P x ∧ absZ x = k) :=
        ⟨absZ x₀, absZ_in_omega x₀ hx₀, x₀, hx₀, hPx₀, rfl⟩
      obtain ⟨n, hn, ⟨z, hz, hPz, h_abs_eq⟩, h_min⟩ :=
        well_ordering_Omega_exists
          (fun k => ∃ x : U, x ∈ (IntSet : U) ∧ P x ∧ absZ x = k)
          h_omega_nonempty
      exact ⟨z, hz, hPz, fun w hw hPw => by
        have h := h_min (absZ w) (absZ_in_omega w hw) ⟨w, hw, hPw, rfl⟩
        rwa [h_abs_eq]⟩

    -- =========================================================================
    -- Section 4: Induction for non-negative integers
    -- =========================================================================

    /-- **Induction for non-negative integers**: if P(natToInt 0) and
        P(natToInt n) → P(natToInt (σ n)) for all n ∈ ω, then
        P(natToInt n) for all n ∈ ω. This is simply ω-induction
        transported through natToInt. -/
    theorem int_induction_nonneg (P : U → Prop)
        (h_zero : P (natToInt (∅ : U)))
        (h_succ : ∀ n : U, n ∈ (ω : U) → P (natToInt n) → P (natToInt (σ n))) :
        ∀ n : U, n ∈ (ω : U) → P (natToInt n) := by
      let S := sep (ω : U) (fun n => P (natToInt n))
      have hS_zero : (∅ : U) ∈ S := by
        rw [mem_sep_iff]; exact ⟨zero_in_Omega, h_zero⟩
      have hS_succ : ∀ k, k ∈ S → σ k ∈ S := by
        intro k hk; rw [mem_sep_iff] at hk ⊢
        exact ⟨succ_in_Omega k hk.1, h_succ k hk.1 hk.2⟩
      have hS_eq : S = (ω : U) :=
        induction_principle S (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
          hS_zero hS_succ
      intro n hn
      have : n ∈ S := by rw [hS_eq]; exact hn
      rw [mem_sep_iff] at this; exact this.2

    -- =========================================================================
    -- Section 5: Induction for negative integers
    -- =========================================================================

    /-- **Induction for negative integers**: if P(-1) and
        P(intClass ∅ (σ n)) → P(intClass ∅ (σ (σ n))) for all n ∈ ω,
        then P holds for all intClass ∅ (σ n) with n ∈ ω. -/
    theorem int_induction_neg (P : U → Prop)
        (h_neg_one : P (intClass (∅ : U) (σ (∅ : U))))
        (h_neg_succ : ∀ n : U, n ∈ (ω : U) →
          P (intClass (∅ : U) (σ n)) → P (intClass (∅ : U) (σ (σ n)))) :
        ∀ n : U, n ∈ (ω : U) → P (intClass (∅ : U) (σ n)) := by
      let S := sep (ω : U) (fun n => P (intClass (∅ : U) (σ n)))
      have hS_zero : (∅ : U) ∈ S := by
        rw [mem_sep_iff]; exact ⟨zero_in_Omega, h_neg_one⟩
      have hS_succ : ∀ k, k ∈ S → σ k ∈ S := by
        intro k hk; rw [mem_sep_iff] at hk ⊢
        exact ⟨succ_in_Omega k hk.1, h_neg_succ k hk.1 hk.2⟩
      have hS_eq : S = (ω : U) :=
        induction_principle S (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
          hS_zero hS_succ
      intro n hn
      have : n ∈ S := by rw [hS_eq]; exact hn
      rw [mem_sep_iff] at this; exact this.2

    -- =========================================================================
    -- Section 6: Infinite descent
    -- =========================================================================

    /-- **Infinite descent**: if P implies a "smaller" solution (by |·|),
        then P has no solutions in ℤ. -/
    theorem int_descent (P : U → Prop)
        (h_descent : ∀ x : U, x ∈ (IntSet : U) → P x →
          ∃ y : U, y ∈ (IntSet : U) ∧ P y ∧ absZ y ∈ absZ x) :
        ∀ x : U, x ∈ (IntSet : U) → ¬ P x := by
      apply int_strong_induction_abs (fun x => ¬ P x)
      intro x hx ih hPx
      obtain ⟨y, hy, hPy, hy_lt⟩ := h_descent x hx hPx
      exact ih y hy hy_lt hPy

  end Int.Induction

  export Int.Induction (
    int_induction_abs
    int_strong_induction_abs
    int_well_ordering_abs
    int_induction_nonneg
    int_induction_neg
    int_descent
  )

end ZFC
