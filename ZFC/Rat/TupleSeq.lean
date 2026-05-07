/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones correspondientes.
-/

import ZFC.Rat.Mul
import ZFC.Rat.Add
import ZFC.SetOps.TupleOps

/-!
# Summation and Product over Rational Tuples

This file defines summation and product for tuples with values in ℚ,
following the same RecursionTheoremWithStep pattern as FiniteSequencesArith.

## Key difference from the ℕ case

The step functions use a guarded `if t⦅k⦆ ∈ RatSet then ... else zeroQ/oneQ` to stay
in RatSet for all k ∈ ω, even when t only has domain σ n ≠ ω.
No hypothesis on t is required for the step function to be a valid ZFC function.

## Main Definitions

* `sumQStepFn t`     — step function for summation: ⟨k, v⟩ ↦ addQ v (t⦅k⦆) [guarded]
* `seqSumQFn t`      — ZFC function ω → RatSet computing partial sums of t
* `seqSumQ t n`      — Σ_{i < n} t(i) for any t : U and n ∈ ω
* `prodQStepFn t`    — step function for product: ⟨k, v⟩ ↦ mulQ v (t⦅k⦆) [guarded]
* `seqProdQFn t`     — ZFC function ω → RatSet computing partial products of t
* `seqProdQ t n`     — Π_{i < n} t(i) for any t : U and n ∈ ω

## Main Theorems

* `seqSumQ_zero`, `seqSumQ_succ`   — recursion equations for sum
* `seqSumQ_mem_RatSet`             — seqSumQ t n ∈ RatSet for n ∈ ω
* `seqSumQ_singleton`              — seqSumQ t (σ ∅) = t⦅∅⦆ when t⦅∅⦆ ∈ RatSet
* `seqProdQ_zero`, `seqProdQ_succ` — recursion equations for product
* `seqProdQ_mem_RatSet`            — seqProdQ t n ∈ RatSet for n ∈ ω
* `seqProdQ_singleton`             — seqProdQ t (σ ∅) = t⦅∅⦆ when t⦅∅⦆ ∈ RatSet
-/

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
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Mul
  universe u
  variable {U : Type u}

  namespace Rat.TupleSeq

    /-! ============================================================ -/
    /-! ### SECTION 1: SUMMATION STEP FUNCTION ### -/
    /-! ============================================================ -/

    /-- Step function for rational summation: maps ⟨k, v⟩ ↦ addQ v (t⦅k⦆).
        Uses a guard so the result is always in RatSet, even when k ∉ domain(t). -/
    noncomputable def sumQStepFn (t : U) : U :=
      sep ((ω ×ₛ (RatSet : U)) ×ₛ (RatSet : U))
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
          p = ⟨⟨k, v⟩, addQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (zeroQ : U))⟩)

    /-- Membership characterization for sumQStepFn. -/
    theorem mem_sumQStepFn {t p : U} :
        p ∈ sumQStepFn t ↔ (p ∈ ((ω : U) ×ₛ (RatSet : U)) ×ₛ (RatSet : U) ∧
          ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
            p = ⟨⟨k, v⟩, addQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (zeroQ : U))⟩) := by
      unfold sumQStepFn; rw [mem_sep_iff]

    /-- sumQStepFn t is a function from ω ×ₛ RatSet to RatSet (for any t). -/
    theorem sumQStepFn_is_function (t : U) :
        IsFunction (sumQStepFn t) ((ω : U) ×ₛ (RatSet : U)) (RatSet : U) := by
      constructor
      · intro p hp; rw [mem_sumQStepFn] at hp; exact hp.1
      · intro x hx
        rw [CartesianProduct_is_specified] at hx
        obtain ⟨hop, hfst_w, hsnd_w⟩ := hx
        obtain ⟨k, v, rfl⟩ := hop
        rw [fst_of_ordered_pair] at hfst_w
        rw [snd_of_ordered_pair] at hsnd_w
        have h_inner : (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (zeroQ : U)) ∈ (RatSet : U) := by
          rcases Classical.em (t⦅k⦆ ∈ (RatSet : U)) with h | h
          · rw [if_pos h]; exact h
          · rw [if_neg h]; exact zeroQ_mem_RatSet
        have h_result_mem : addQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (zeroQ : U)) ∈
            (RatSet : U) := addQ_in_RatSet v _ hsnd_w h_inner
        refine ⟨addQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (zeroQ : U)),
                ?_, fun y hy => ?_⟩
        · dsimp only; rw [mem_sumQStepFn]
          exact ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ _
                    ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
                   ⟨(OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr
                      ⟨hfst_w, hsnd_w⟩,
                    h_result_mem⟩,
                 k, v, hfst_w, hsnd_w, rfl⟩
        · dsimp only at hy; rw [mem_sumQStepFn] at hy
          obtain ⟨_, k', v', hk', hv', heq⟩ := hy
          obtain ⟨hpair_eq, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections ⟨k, v⟩ y ⟨k', v'⟩
              (addQ v' (if t⦅k'⦆ ∈ (RatSet : U) then t⦅k'⦆ else (zeroQ : U))) heq
          obtain ⟨hk_eq, hv_eq⟩ :=
            Eq_of_OrderedPairs_given_projections k v k' v' hpair_eq
          rw [hy_eq, ← hk_eq, ← hv_eq]

    /-- Applying sumQStepFn at ⟨k, v⟩ yields addQ v (t⦅k⦆) when t⦅k⦆ ∈ RatSet. -/
    theorem sumQStepFn_apply {t k v : U}
        (hk : k ∈ (ω : U)) (hv : v ∈ (RatSet : U)) (htk : t⦅k⦆ ∈ (RatSet : U)) :
        (sumQStepFn t)⦅⟨k, v⟩⦆ = addQ v (t⦅k⦆) := by
      have hkv : ⟨k, v⟩ ∈ ((ω : U) ×ₛ (RatSet : U) : U) :=
        (OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr ⟨hk, hv⟩
      have h_mem : ⟨⟨k, v⟩, addQ v (t⦅k⦆)⟩ ∈ sumQStepFn t :=
        mem_sumQStepFn.mpr
          ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (addQ v (t⦅k⦆))
                ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
             ⟨hkv, addQ_in_RatSet v (t⦅k⦆) hv htk⟩,
           k, v, hk, hv, by rw [if_pos htk]⟩
      exact apply_eq (sumQStepFn t) ⟨k, v⟩ (addQ v (t⦅k⦆))
        ((sumQStepFn_is_function t).2 ⟨k, v⟩ hkv) h_mem

    /-! ============================================================ -/
    /-! ### SECTION 2: SUMMATION ### -/
    /-! ============================================================ -/

    /-- The summation function: seqSumQFn t is the unique F : ω → RatSet
        with F(∅) = zeroQ and F(σ k) = addQ (F k) (t⦅k⦆) [guarded]. -/
    noncomputable def seqSumQFn (t : U) : U :=
      Classical.choose (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (zeroQ : U) (sumQStepFn t)
          zeroQ_mem_RatSet (sumQStepFn_is_function t)))

    /-- seqSumQFn t is a function from ω to RatSet. -/
    theorem seqSumQFn_is_function (t : U) :
        IsFunction (seqSumQFn t) (ω : U) (RatSet : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (zeroQ : U) (sumQStepFn t)
          zeroQ_mem_RatSet (sumQStepFn_is_function t)))).1

    /-- Rational partial sum: Σ_{i < n} t(i). -/
    noncomputable def seqSumQ (t n : U) : U := (seqSumQFn t)⦅n⦆

    /-- Helper: seqSumQFn at any n ∈ ω lies in RatSet. -/
    private theorem seqSumQFn_apply_in_RatSet (t : U) (n : U) (hn : n ∈ (ω : U)) :
        (seqSumQFn t)⦅n⦆ ∈ (RatSet : U) := by
      have hF := seqSumQFn_is_function t
      have h_pair := apply_mem (seqSumQFn t) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ (ω : U) (RatSet : U)).mp
               (hF.1 _ h_pair)).2

    /-- Helper: seqSumQFn at zero gives zeroQ. -/
    private theorem seqSumQFn_zero (t : U) :
        (seqSumQFn t)⦅(∅ : U)⦆ = (zeroQ : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (zeroQ : U) (sumQStepFn t)
          zeroQ_mem_RatSet (sumQStepFn_is_function t)))).2.1

    /-- Helper: seqSumQFn recursion step. -/
    private theorem seqSumQFn_succ (t : U) (n : U) (hn : n ∈ (ω : U)) :
        (seqSumQFn t)⦅σ n⦆ = (sumQStepFn t)⦅⟨n, (seqSumQFn t)⦅n⦆⟩⦆ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (zeroQ : U) (sumQStepFn t)
          zeroQ_mem_RatSet (sumQStepFn_is_function t)))).2.2 n hn

    /-- seqSumQ t ∅ = zeroQ (empty sum is zero). -/
    theorem seqSumQ_zero (t : U) : seqSumQ t ∅ = (zeroQ : U) := by
      unfold seqSumQ; exact seqSumQFn_zero t

    /-- seqSumQ t (σ k) = addQ (seqSumQ t k) (t⦅k⦆) when t⦅k⦆ ∈ RatSet. -/
    theorem seqSumQ_succ (t k : U) (hk : k ∈ (ω : U)) (htk : t⦅k⦆ ∈ (RatSet : U)) :
        seqSumQ t (σ k) = addQ (seqSumQ t k) (t⦅k⦆) := by
      unfold seqSumQ
      rw [seqSumQFn_succ t k hk]
      exact sumQStepFn_apply hk (seqSumQFn_apply_in_RatSet t k hk) htk

    /-- seqSumQ t n ∈ RatSet for any n ∈ ω. -/
    theorem seqSumQ_mem_RatSet (t n : U) (hn : n ∈ (ω : U)) :
        seqSumQ t n ∈ (RatSet : U) := by
      unfold seqSumQ; exact seqSumQFn_apply_in_RatSet t n hn

    /-- Sum of a singleton sequence: seqSumQ t (σ ∅) = t⦅∅⦆. -/
    theorem seqSumQ_singleton (t : U) (htk : t⦅(∅ : U)⦆ ∈ (RatSet : U)) :
        seqSumQ t (σ ∅) = t⦅(∅ : U)⦆ := by
      rw [seqSumQ_succ t ∅ zero_in_Omega htk, seqSumQ_zero]
      exact addQ_zero_left (t⦅(∅ : U)⦆) htk

    /-! ============================================================ -/
    /-! ### SECTION 3: PRODUCT STEP FUNCTION ### -/
    /-! ============================================================ -/

    /-- Step function for rational product: maps ⟨k, v⟩ ↦ mulQ v (t⦅k⦆).
        Uses a guard so the result is always in RatSet, even when k ∉ domain(t). -/
    noncomputable def prodQStepFn (t : U) : U :=
      sep ((ω ×ₛ (RatSet : U)) ×ₛ (RatSet : U))
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
          p = ⟨⟨k, v⟩, mulQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (oneQ : U))⟩)

    /-- Membership characterization for prodQStepFn. -/
    theorem mem_prodQStepFn {t p : U} :
        p ∈ prodQStepFn t ↔ (p ∈ ((ω : U) ×ₛ (RatSet : U)) ×ₛ (RatSet : U) ∧
          ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
            p = ⟨⟨k, v⟩, mulQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (oneQ : U))⟩) := by
      unfold prodQStepFn; rw [mem_sep_iff]

    /-- prodQStepFn t is a function from ω ×ₛ RatSet to RatSet (for any t). -/
    theorem prodQStepFn_is_function (t : U) :
        IsFunction (prodQStepFn t) ((ω : U) ×ₛ (RatSet : U)) (RatSet : U) := by
      constructor
      · intro p hp; rw [mem_prodQStepFn] at hp; exact hp.1
      · intro x hx
        rw [CartesianProduct_is_specified] at hx
        obtain ⟨hop, hfst_w, hsnd_w⟩ := hx
        obtain ⟨k, v, rfl⟩ := hop
        rw [fst_of_ordered_pair] at hfst_w
        rw [snd_of_ordered_pair] at hsnd_w
        have h_inner : (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (oneQ : U)) ∈ (RatSet : U) := by
          rcases Classical.em (t⦅k⦆ ∈ (RatSet : U)) with h | h
          · rw [if_pos h]; exact h
          · rw [if_neg h]; exact oneQ_mem_RatSet
        have h_result_mem : mulQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (oneQ : U)) ∈
            (RatSet : U) := mulQ_in_RatSet v _ hsnd_w h_inner
        refine ⟨mulQ v (if t⦅k⦆ ∈ (RatSet : U) then t⦅k⦆ else (oneQ : U)),
                ?_, fun y hy => ?_⟩
        · dsimp only; rw [mem_prodQStepFn]
          exact ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ _
                    ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
                   ⟨(OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr
                      ⟨hfst_w, hsnd_w⟩,
                    h_result_mem⟩,
                 k, v, hfst_w, hsnd_w, rfl⟩
        · dsimp only at hy; rw [mem_prodQStepFn] at hy
          obtain ⟨_, k', v', hk', hv', heq⟩ := hy
          obtain ⟨hpair_eq, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections ⟨k, v⟩ y ⟨k', v'⟩
              (mulQ v' (if t⦅k'⦆ ∈ (RatSet : U) then t⦅k'⦆ else (oneQ : U))) heq
          obtain ⟨hk_eq, hv_eq⟩ :=
            Eq_of_OrderedPairs_given_projections k v k' v' hpair_eq
          rw [hy_eq, ← hk_eq, ← hv_eq]

    /-- Applying prodQStepFn at ⟨k, v⟩ yields mulQ v (t⦅k⦆) when t⦅k⦆ ∈ RatSet. -/
    theorem prodQStepFn_apply {t k v : U}
        (hk : k ∈ (ω : U)) (hv : v ∈ (RatSet : U)) (htk : t⦅k⦆ ∈ (RatSet : U)) :
        (prodQStepFn t)⦅⟨k, v⟩⦆ = mulQ v (t⦅k⦆) := by
      have hkv : ⟨k, v⟩ ∈ ((ω : U) ×ₛ (RatSet : U) : U) :=
        (OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr ⟨hk, hv⟩
      have h_mem : ⟨⟨k, v⟩, mulQ v (t⦅k⦆)⟩ ∈ prodQStepFn t :=
        mem_prodQStepFn.mpr
          ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (mulQ v (t⦅k⦆))
                ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
             ⟨hkv, mulQ_in_RatSet v (t⦅k⦆) hv htk⟩,
           k, v, hk, hv, by rw [if_pos htk]⟩
      exact apply_eq (prodQStepFn t) ⟨k, v⟩ (mulQ v (t⦅k⦆))
        ((prodQStepFn_is_function t).2 ⟨k, v⟩ hkv) h_mem

    /-! ============================================================ -/
    /-! ### SECTION 4: NUMERIC PRODUCT ### -/
    /-! ============================================================ -/

    /-- The product function: seqProdQFn t is the unique F : ω → RatSet
        with F(∅) = oneQ and F(σ k) = mulQ (F k) (t⦅k⦆) [guarded]. -/
    noncomputable def seqProdQFn (t : U) : U :=
      Classical.choose (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (prodQStepFn t)
          oneQ_mem_RatSet (prodQStepFn_is_function t)))

    /-- seqProdQFn t is a function from ω to RatSet. -/
    theorem seqProdQFn_is_function (t : U) :
        IsFunction (seqProdQFn t) (ω : U) (RatSet : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (prodQStepFn t)
          oneQ_mem_RatSet (prodQStepFn_is_function t)))).1

    /-- Rational partial product: Π_{i < n} t(i). -/
    noncomputable def seqProdQ (t n : U) : U := (seqProdQFn t)⦅n⦆

    /-- Helper: seqProdQFn at any n ∈ ω lies in RatSet. -/
    private theorem seqProdQFn_apply_in_RatSet (t : U) (n : U) (hn : n ∈ (ω : U)) :
        (seqProdQFn t)⦅n⦆ ∈ (RatSet : U) := by
      have hF := seqProdQFn_is_function t
      have h_pair := apply_mem (seqProdQFn t) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ (ω : U) (RatSet : U)).mp
               (hF.1 _ h_pair)).2

    /-- Helper: seqProdQFn at zero gives oneQ. -/
    private theorem seqProdQFn_zero (t : U) :
        (seqProdQFn t)⦅(∅ : U)⦆ = (oneQ : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (prodQStepFn t)
          oneQ_mem_RatSet (prodQStepFn_is_function t)))).2.1

    /-- Helper: seqProdQFn recursion step. -/
    private theorem seqProdQFn_succ (t : U) (n : U) (hn : n ∈ (ω : U)) :
        (seqProdQFn t)⦅σ n⦆ = (prodQStepFn t)⦅⟨n, (seqProdQFn t)⦅n⦆⟩⦆ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (prodQStepFn t)
          oneQ_mem_RatSet (prodQStepFn_is_function t)))).2.2 n hn

    /-- seqProdQ t ∅ = oneQ (empty product is one). -/
    theorem seqProdQ_zero (t : U) : seqProdQ t ∅ = (oneQ : U) := by
      unfold seqProdQ; exact seqProdQFn_zero t

    /-- seqProdQ t (σ k) = mulQ (seqProdQ t k) (t⦅k⦆) when t⦅k⦆ ∈ RatSet. -/
    theorem seqProdQ_succ (t k : U) (hk : k ∈ (ω : U)) (htk : t⦅k⦆ ∈ (RatSet : U)) :
        seqProdQ t (σ k) = mulQ (seqProdQ t k) (t⦅k⦆) := by
      unfold seqProdQ
      rw [seqProdQFn_succ t k hk]
      exact prodQStepFn_apply hk (seqProdQFn_apply_in_RatSet t k hk) htk

    /-- seqProdQ t n ∈ RatSet for any n ∈ ω. -/
    theorem seqProdQ_mem_RatSet (t n : U) (hn : n ∈ (ω : U)) :
        seqProdQ t n ∈ (RatSet : U) := by
      unfold seqProdQ; exact seqProdQFn_apply_in_RatSet t n hn

    /-- Product of a singleton sequence: seqProdQ t (σ ∅) = t⦅∅⦆. -/
    theorem seqProdQ_singleton (t : U) (htk : t⦅(∅ : U)⦆ ∈ (RatSet : U)) :
        seqProdQ t (σ ∅) = t⦅(∅ : U)⦆ := by
      rw [seqProdQ_succ t ∅ zero_in_Omega htk, seqProdQ_zero]
      exact mulQ_one_left (t⦅(∅ : U)⦆) htk

  end Rat.TupleSeq

  export Rat.TupleSeq (
    -- Section 1: Summation step function
    sumQStepFn
    mem_sumQStepFn
    sumQStepFn_is_function
    sumQStepFn_apply
    -- Section 2: Summation
    seqSumQFn
    seqSumQFn_is_function
    seqSumQ
    seqSumQ_zero
    seqSumQ_succ
    seqSumQ_mem_RatSet
    seqSumQ_singleton
    -- Section 3: Product step function
    prodQStepFn
    mem_prodQStepFn
    prodQStepFn_is_function
    prodQStepFn_apply
    -- Section 4: Numeric product
    seqProdQFn
    seqProdQFn_is_function
    seqProdQ
    seqProdQ_zero
    seqProdQ_succ
    seqProdQ_mem_RatSet
    seqProdQ_singleton
  )

end ZFC
