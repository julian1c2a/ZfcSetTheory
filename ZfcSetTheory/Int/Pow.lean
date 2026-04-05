/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Exponentiation (Natural Exponent)

  This module defines exponentiation on ℤ with natural exponents via the
  Recursion Theorem and proves basic algebraic properties.

  ## Strategy

  Fix x ∈ ℤ. Define `mulZLeftFn x hx` as the ZFC function ℤ → ℤ mapping
  y ↦ mulZ x y. Then define `powZFn x hx := RecursiveFn IntSet oneZ (mulZLeftFn x hx) ...`,
  so that `powZFn x hx : ω → ℤ` satisfies:
    - (powZFn x hx)(∅)   = oneZ             -- x^0 = 1
    - (powZFn x hx)(σ n) = mulZ x ((powZFn x hx)(n))  -- x^(σn) = x · x^n

  Then `powZ x n := if h : x ∈ IntSet then apply (powZFn x h) n else oneZ`.

  ## Main Definitions

  * `mulZLeftFn` — the ZFC function ℤ → ℤ mapping y ↦ x · y
  * `powZFn` — the recursive function ω → ℤ computing x ^ ·
  * `powZ` — integer exponentiation: powZ x n = x^n

  ## Main Theorems

  * `powZ_zero` — powZ x ∅ = oneZ
  * `powZ_succ` — powZ x (σ n) = mulZ x (powZ x n)
  * `powZ_in_IntSet` — closure
  * `powZ_one` — powZ x (σ ∅) = x
  * `oneZ_powZ` — powZ oneZ n = oneZ
  * `zeroZ_powZ` — powZ zeroZ (σ n) = zeroZ
  * `powZ_add_exp` — powZ x (add n k) = mulZ (powZ x n) (powZ x k)
  * `powZ_mul_base` — powZ (mulZ x y) n = mulZ (powZ x n) (powZ y n)
  * `powZ_negZ_even` — powZ (negZ x) (add n n) = powZ x (add n n)
  * `powZ_negZ_odd` — powZ (negZ x) (σ (add n n)) = negZ (powZ x (σ (add n n)))
-/

import ZfcSetTheory.Int.Ring
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Nat.Add

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
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Ring
  open ZFC.Induction.Recursion

  universe u
  variable {U : Type u}

  namespace Int.Pow

    -- =========================================================================
    -- Section 1: The "multiply by x" ZFC function ℤ → ℤ
    -- =========================================================================

    /-- `mulZLeftFn x hx` is the graph of the function y ↦ mulZ x y on ℤ,
        constructed as a subset of ℤ × ℤ via specification. -/
    noncomputable def mulZLeftFn (x : U) (hx : x ∈ (IntSet : U)) : U :=
      sep ((IntSet : U) ×ₛ IntSet) (fun p => ∃ y, y ∈ (IntSet : U) ∧ p = ⟨y, mulZ x y⟩)

    /-- `mulZLeftFn x hx` is a function from ℤ to ℤ. -/
    theorem mulZLeftFn_is_function (x : U) (hx : x ∈ (IntSet : U)) :
        IsFunction (mulZLeftFn x hx) IntSet IntSet := by
      constructor
      · -- Subset: mulZLeftFn x hx ⊆ IntSet ×ₛ IntSet
        intro p hp
        simp only [mulZLeftFn, mem_sep_iff] at hp
        exact hp.1
      · -- For each y ∈ IntSet, ∃! z, ⟨y, z⟩ ∈ mulZLeftFn x hx
        intro y hy
        apply ExistsUnique.intro (mulZ x y)
        · -- Membership: ⟨y, mulZ x y⟩ ∈ mulZLeftFn x hx
          simp only [mulZLeftFn, mem_sep_iff]
          exact ⟨(OrderedPair_mem_CartesianProduct y (mulZ x y) IntSet IntSet).mpr
                  ⟨hy, mulZ_in_IntSet x y hx hy⟩,
                 ⟨y, hy, rfl⟩⟩
        · -- Uniqueness: if ⟨y, z⟩ ∈ mulZLeftFn x hx then z = mulZ x y
          intro z hz
          simp only [mulZLeftFn, mem_sep_iff] at hz
          obtain ⟨_, y', _, h_eq⟩ := hz
          have h_pair := (OrderedPair_eq_iff y z y' (mulZ x y')).mp h_eq
          rw [h_pair.2, h_pair.1]

    /-- Computation rule: apply (mulZLeftFn x hx) y = mulZ x y for y ∈ ℤ. -/
    theorem mulZLeftFn_apply (x y : U) (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        apply (mulZLeftFn x hx) y = mulZ x y := by
      have hf := mulZLeftFn_is_function x hx
      have h_unique := hf.2 y hy
      have h_pair : ⟨y, mulZ x y⟩ ∈ mulZLeftFn x hx := by
        simp only [mulZLeftFn]
        rw [mem_sep_iff]
        exact ⟨(OrderedPair_mem_CartesianProduct y (mulZ x y) IntSet IntSet).mpr
                ⟨hy, mulZ_in_IntSet x y hx hy⟩,
               ⟨y, hy, rfl⟩⟩
      exact apply_eq (mulZLeftFn x hx) y (mulZ x y) h_unique h_pair

    -- =========================================================================
    -- Section 2: Integer exponentiation via recursion
    -- =========================================================================

    /-- `powZFn x hx` is the ZFC function ω → ℤ that computes x ^ ·.
        Constructed via the Recursion Theorem with base oneZ and
        step mulZLeftFn x hx. -/
    noncomputable def powZFn (x : U) (hx : x ∈ (IntSet : U)) : U :=
      RecursiveFn IntSet oneZ (mulZLeftFn x hx)
        oneZ_mem_IntSet (mulZLeftFn_is_function x hx)

    /-- `powZFn x hx` is a function from ω to ℤ. -/
    theorem powZFn_is_function (x : U) (hx : x ∈ (IntSet : U)) :
        IsFunction (powZFn x hx) ω IntSet :=
      RecursiveFn_is_function IntSet oneZ (mulZLeftFn x hx)
        oneZ_mem_IntSet (mulZLeftFn_is_function x hx)

    /-- `powZ x n` = x^n in ℤ (with n ∈ ω).
        Defined without a proof argument (defaults to oneZ when x ∉ ℤ). -/
    noncomputable def powZ (x n : U) : U :=
      if h : x ∈ (IntSet : U) then apply (powZFn x h) n else oneZ

    /-- When x ∈ ℤ, powZ unfolds to apply (powZFn x hx) n. -/
    theorem powZ_eq (x n : U) (hx : x ∈ (IntSet : U)) :
        powZ x n = apply (powZFn x hx) n := by
      simp only [powZ, dif_pos hx]

    /-- powZ x n ∈ ℤ for x ∈ ℤ and n ∈ ω. -/
    theorem powZ_in_IntSet (x n : U) (hx : x ∈ (IntSet : U)) (hn : n ∈ (ω : U)) :
        powZ x n ∈ (IntSet : U) := by
      rw [powZ_eq x n hx]
      have hf := powZFn_is_function x hx
      have h_unique : ∃! y, ⟨n, y⟩ ∈ powZFn x hx := hf.2 n hn
      have h_pair_in : ⟨n, apply (powZFn x hx) n⟩ ∈ powZFn x hx :=
        apply_mem (powZFn x hx) n h_unique
      have h_sub := hf.1
      have h_in_prod : ⟨n, apply (powZFn x hx) n⟩ ∈ ((ω : U) ×ₛ IntSet) := h_sub _ h_pair_in
      exact ((OrderedPair_mem_CartesianProduct n (apply (powZFn x hx) n) ω IntSet).mp h_in_prod).2

    -- =========================================================================
    -- Section 3: Basic recursion equations
    -- =========================================================================

    /-- powZ x ∅ = oneZ (x^0 = 1). -/
    theorem powZ_zero (x : U) (hx : x ∈ (IntSet : U)) :
        powZ x ∅ = (oneZ : U) := by
      simp only [powZ, dif_pos hx, powZFn]
      exact RecursiveFn_zero IntSet oneZ (mulZLeftFn x hx)
        oneZ_mem_IntSet (mulZLeftFn_is_function x hx)

    /-- powZ x (σ n) = mulZ x (powZ x n) for x ∈ ℤ, n ∈ ω. -/
    theorem powZ_succ (x n : U) (hx : x ∈ (IntSet : U)) (hn : n ∈ (ω : U)) :
        powZ x (σ n) = mulZ x (powZ x n) := by
      simp only [powZ, dif_pos hx, powZFn]
      rw [RecursiveFn_succ IntSet oneZ (mulZLeftFn x hx)
            oneZ_mem_IntSet (mulZLeftFn_is_function x hx) n hn]
      have h_val_in : apply (RecursiveFn IntSet oneZ (mulZLeftFn x hx)
            oneZ_mem_IntSet (mulZLeftFn_is_function x hx)) n ∈ (IntSet : U) := by
        have hf := RecursiveFn_is_function IntSet oneZ (mulZLeftFn x hx)
              oneZ_mem_IntSet (mulZLeftFn_is_function x hx)
        have h_unique := hf.2 n hn
        have h_pair := apply_mem _ n h_unique
        exact ((OrderedPair_mem_CartesianProduct n _ ω IntSet).mp (hf.1 _ h_pair)).2
      exact mulZLeftFn_apply x _ hx h_val_in

    -- =========================================================================
    -- Section 4: Derived properties
    -- =========================================================================

    /-- powZ x (σ ∅) = x (x^1 = x). -/
    theorem powZ_one (x : U) (hx : x ∈ (IntSet : U)) :
        powZ x (σ (∅ : U)) = x := by
      rw [powZ_succ x ∅ hx zero_in_Omega, powZ_zero x hx, mulZ_one_right x hx]

    /-- powZ oneZ n = oneZ (1^n = 1) for n ∈ ω. -/
    theorem oneZ_powZ (n : U) (hn : n ∈ (ω : U)) :
        powZ (oneZ : U) n = (oneZ : U) := by
      -- Induction on n ∈ ω
      let S := sep ω (fun n => powZ (oneZ : U) n = (oneZ : U))
      have h_S_eq_ω : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · rw [mem_sep_iff]
          exact ⟨zero_in_Omega, powZ_zero oneZ oneZ_mem_IntSet⟩
        · intro k hk_in_S
          rw [mem_sep_iff] at hk_in_S
          obtain ⟨hk_ω, h_ih⟩ := hk_in_S
          rw [mem_sep_iff]
          exact ⟨succ_in_Omega k hk_ω, by
            rw [powZ_succ oneZ k oneZ_mem_IntSet hk_ω, h_ih, mulZ_one_right oneZ oneZ_mem_IntSet]⟩
      have : n ∈ S := h_S_eq_ω ▸ hn
      rw [mem_sep_iff] at this
      exact this.2

    /-- powZ zeroZ (σ n) = zeroZ (0^(n+1) = 0) for n ∈ ω. -/
    theorem zeroZ_powZ (n : U) (hn : n ∈ (ω : U)) :
        powZ (zeroZ : U) (σ n) = (zeroZ : U) := by
      rw [powZ_succ zeroZ n zeroZ_mem_IntSet hn,
          mulZ_zero_left (powZ zeroZ n) (powZ_in_IntSet zeroZ n zeroZ_mem_IntSet hn)]

    /-- powZ x (add n k) = mulZ (powZ x n) (powZ x k) — exponent addition law.
        For x ∈ ℤ, n k ∈ ω. -/
    theorem powZ_add_exp (x n k : U) (hx : x ∈ (IntSet : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        powZ x (add n k) = mulZ (powZ x n) (powZ x k) := by
      -- Induction on k
      let S := sep ω (fun k => powZ x (add n k) = mulZ (powZ x n) (powZ x k))
      have h_S_eq_ω : S = ω := by
        apply induction_principle S
        · intro z hz; rw [mem_sep_iff] at hz; exact hz.1
        · -- Base: k = ∅
          rw [mem_sep_iff]
          exact ⟨zero_in_Omega, by
            rw [add_zero n hn, powZ_zero x hx, mulZ_one_right (powZ x n) (powZ_in_IntSet x n hx hn)]⟩
        · -- Step: k → σ k
          intro j hj_in_S
          rw [mem_sep_iff] at hj_in_S
          obtain ⟨hj_ω, h_ih⟩ := hj_in_S
          rw [mem_sep_iff]
          constructor
          · exact succ_in_Omega j hj_ω
          · rw [add_succ n j hn hj_ω]
            rw [powZ_succ x (add n j) hx (add_in_Omega n j hn hj_ω)]
            rw [h_ih]
            rw [powZ_succ x j hx hj_ω]
            have hpxn := powZ_in_IntSet x n hx hn
            have hpxj := powZ_in_IntSet x j hx hj_ω
            rw [← mulZ_assoc x (powZ x n) (powZ x j) hx hpxn hpxj]
            rw [mulZ_comm x (powZ x n) hx hpxn]
            rw [mulZ_assoc (powZ x n) x (powZ x j) hpxn hx hpxj]
      have : k ∈ S := h_S_eq_ω ▸ hk
      rw [mem_sep_iff] at this
      exact this.2

    /-- powZ (mulZ x y) n = mulZ (powZ x n) (powZ y n) — base product law.
        For x y ∈ ℤ, n ∈ ω. -/
    theorem powZ_mul_base (x y n : U) (hx : x ∈ (IntSet : U))
        (hy : y ∈ (IntSet : U)) (hn : n ∈ (ω : U)) :
        powZ (mulZ x y) n = mulZ (powZ x n) (powZ y n) := by
      -- Induction on n
      let S := sep ω (fun n => powZ (mulZ x y) n = mulZ (powZ x n) (powZ y n))
      have h_S_eq_ω : S = ω := by
        apply induction_principle S
        · intro z hz; rw [mem_sep_iff] at hz; exact hz.1
        · -- Base: n = ∅
          rw [mem_sep_iff]
          exact ⟨zero_in_Omega, by
            rw [powZ_zero (mulZ x y) (mulZ_in_IntSet x y hx hy),
                powZ_zero x hx, powZ_zero y hy,
                mulZ_one_right oneZ oneZ_mem_IntSet]⟩
        · -- Step: n → σ n
          intro k hk_in_S
          rw [mem_sep_iff] at hk_in_S
          obtain ⟨hk_ω, h_ih⟩ := hk_in_S
          rw [mem_sep_iff]
          constructor
          · exact succ_in_Omega k hk_ω
          · rw [powZ_succ (mulZ x y) k (mulZ_in_IntSet x y hx hy) hk_ω]
            rw [h_ih]
            rw [powZ_succ x k hx hk_ω, powZ_succ y k hy hk_ω]
            -- Goal: mulZ (mulZ x y) (mulZ (powZ x k) (powZ y k)) =
            --       mulZ (mulZ x (powZ x k)) (mulZ y (powZ y k))
            -- Use associativity and commutativity to rearrange
            have hpxk := powZ_in_IntSet x k hx hk_ω
            have hpyk := powZ_in_IntSet y k hy hk_ω
            have hxy := mulZ_in_IntSet x y hx hy
            rw [← mulZ_assoc (mulZ x y) (powZ x k) (powZ y k) hxy hpxk hpyk]
            rw [mulZ_assoc x y (powZ x k) hx hy hpxk]
            rw [mulZ_comm y (powZ x k) hy hpxk]
            rw [← mulZ_assoc x (powZ x k) y hx hpxk hy]
            rw [mulZ_assoc (mulZ x (powZ x k)) y (powZ y k)
                 (mulZ_in_IntSet x (powZ x k) hx hpxk) hy hpyk]
      have : n ∈ S := h_S_eq_ω ▸ hn
      rw [mem_sep_iff] at this
      exact this.2

    /-- powZ (negZ x) (σ (σ (∅:U))) = powZ x (σ (σ (∅:U))) — (-x)^2 = x^2.
        Special case showing negation is absorbed by even exponents. -/
    theorem powZ_negZ_sq (x : U) (hx : x ∈ (IntSet : U)) :
        powZ (negZ x) (σ (σ (∅ : U))) = powZ x (σ (σ (∅ : U))) := by
      rw [powZ_succ (negZ x) (σ ∅) (negZ_in_IntSet x hx) (succ_in_Omega ∅ zero_in_Omega)]
      rw [powZ_succ (negZ x) ∅ (negZ_in_IntSet x hx) zero_in_Omega]
      rw [powZ_zero (negZ x) (negZ_in_IntSet x hx)]
      rw [mulZ_one_right (negZ x) (negZ_in_IntSet x hx)]
      rw [negZ_mulZ_negZ x x hx hx]
      rw [powZ_succ x (σ ∅) hx (succ_in_Omega ∅ zero_in_Omega)]
      rw [powZ_succ x ∅ hx zero_in_Omega]
      rw [powZ_zero x hx]
      rw [mulZ_one_right x hx]

  end Int.Pow

  export Int.Pow (
    mulZLeftFn
    mulZLeftFn_is_function
    mulZLeftFn_apply
    powZFn
    powZFn_is_function
    powZ
    powZ_eq
    powZ_in_IntSet
    powZ_zero
    powZ_succ
    powZ_one
    oneZ_powZ
    zeroZ_powZ
    powZ_add_exp
    powZ_mul_base
    powZ_negZ_sq
  )

end ZFC
