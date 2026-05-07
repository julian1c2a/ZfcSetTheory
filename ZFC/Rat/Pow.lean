/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Rational Exponentiation

  This module defines x^n for x ∈ ℚ and n ∈ ω, using the same
  RecursionTheoremWithStep pattern as Rat/TupleSeq.lean.

  ## Strategy

  Fix x ∈ ℚ. Define `powRatQFn x` via `RecursionTheoremWithStep` with:
    - base:  `oneQ`
    - step:  `⟨k, v⟩ ↦ mulQ v x`  (right-multiply by x each step)

  So `powRatQ x ∅ = oneQ` and `powRatQ x (σ n) = mulQ (powRatQ x n) x`.

  ## Main Definitions

  * `powRatQStepFn x`  — step function for exponentiation (ω ×ₛ ℚ → ℚ)
  * `powRatQFn x`      — ZFC function ω → ℚ computing powers of x
  * `powRatQ x n`      — x^n ∈ ℚ for x ∈ ℚ, n ∈ ω

  ## Main Theorems

  * `powRatQ_zero`       — x^∅ = 1Q
  * `powRatQ_succ`       — x^(σ n) = x^n · x  (n ∈ ω, x ∈ ℚ)
  * `powRatQ_mem_RatSet` — x^n ∈ ℚ  for any n ∈ ω
  * `powRatQ_one`        — x^(σ ∅) = x
  * `powRatQ_zero_base`  — 0Q^n = 0Q  for n ≠ ∅
  * `powRatQ_one_base`   — 1Q^n = 1Q  for all n ∈ ω
  * `powRatQ_add_exp`    — x^(n+m) = x^n · x^m  (n m ∈ ω)
  * `powRatQ_mul_base`   — (x·y)^n = x^n · y^n  (x y ∈ ℚ, n ∈ ω)

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones correspondientes.
-/

import ZFC.Rat.Mul
import ZFC.Nat.Add

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
  open ZFC.Nat.Add

  universe u
  variable {U : Type u}

  namespace Rat.Pow

    /-! ============================================================ -/
    /-! ### SECTION 1: EXPONENTIATION STEP FUNCTION              ### -/
    /-! ============================================================ -/

    /-- Step function for rational exponentiation: maps ⟨k, v⟩ ↦ mulQ v x.
        Uses a guard so the result is in RatSet even when x ∉ RatSet. -/
    noncomputable def powRatQStepFn (x : U) : U :=
      sep ((ω ×ₛ (RatSet : U)) ×ₛ (RatSet : U))
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
          p = ⟨⟨k, v⟩, mulQ v (if x ∈ (RatSet : U) then x else (oneQ : U))⟩)

    /-- Membership characterization for powRatQStepFn. -/
    theorem mem_powRatQStepFn {x p : U} :
        p ∈ powRatQStepFn x ↔ (p ∈ ((ω : U) ×ₛ (RatSet : U)) ×ₛ (RatSet : U) ∧
          ∃ k v, k ∈ (ω : U) ∧ v ∈ (RatSet : U) ∧
            p = ⟨⟨k, v⟩, mulQ v (if x ∈ (RatSet : U) then x else (oneQ : U))⟩) := by
      unfold powRatQStepFn; rw [mem_sep_iff]

    /-- powRatQStepFn x is a function from ω ×ₛ RatSet to RatSet for any x. -/
    theorem powRatQStepFn_is_function (x : U) :
        IsFunction (powRatQStepFn x) ((ω : U) ×ₛ (RatSet : U)) (RatSet : U) := by
      constructor
      · intro p hp; rw [mem_powRatQStepFn] at hp; exact hp.1
      · intro px hpx
        rw [CartesianProduct_is_specified] at hpx
        obtain ⟨hop, hfst_w, hsnd_w⟩ := hpx
        obtain ⟨k, v, rfl⟩ := hop
        rw [fst_of_ordered_pair] at hfst_w
        rw [snd_of_ordered_pair] at hsnd_w
        have h_inner : (if x ∈ (RatSet : U) then x else (oneQ : U)) ∈ (RatSet : U) := by
          rcases Classical.em (x ∈ (RatSet : U)) with h | h
          · rw [if_pos h]; exact h
          · rw [if_neg h]; exact oneQ_mem_RatSet
        have h_result_mem :
            mulQ v (if x ∈ (RatSet : U) then x else (oneQ : U)) ∈ (RatSet : U) :=
          mulQ_in_RatSet v _ hsnd_w h_inner
        refine ⟨mulQ v (if x ∈ (RatSet : U) then x else (oneQ : U)), ?_, fun y hy => ?_⟩
        · dsimp only; rw [mem_powRatQStepFn]
          exact ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ _
                    ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
                   ⟨(OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr
                      ⟨hfst_w, hsnd_w⟩,
                    h_result_mem⟩,
                 k, v, hfst_w, hsnd_w, rfl⟩
        · dsimp only at hy; rw [mem_powRatQStepFn] at hy
          obtain ⟨_, k', v', hk', hv', heq⟩ := hy
          obtain ⟨hpair_eq, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections ⟨k, v⟩ y ⟨k', v'⟩
              (mulQ v' (if x ∈ (RatSet : U) then x else (oneQ : U))) heq
          obtain ⟨hk_eq, hv_eq⟩ :=
            Eq_of_OrderedPairs_given_projections k v k' v' hpair_eq
          rw [hy_eq, ← hv_eq]

    /-- Applying powRatQStepFn at ⟨k, v⟩ yields mulQ v x when x ∈ RatSet. -/
    theorem powRatQStepFn_apply {x k v : U}
        (hk : k ∈ (ω : U)) (hv : v ∈ (RatSet : U)) (hx : x ∈ (RatSet : U)) :
        (powRatQStepFn x)⦅⟨k, v⟩⦆ = mulQ v x := by
      have hkv : ⟨k, v⟩ ∈ ((ω : U) ×ₛ (RatSet : U) : U) :=
        (OrderedPair_mem_CartesianProduct k v (ω : U) (RatSet : U)).mpr ⟨hk, hv⟩
      have h_mem : ⟨⟨k, v⟩, mulQ v x⟩ ∈ powRatQStepFn x :=
        mem_powRatQStepFn.mpr
          ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (mulQ v x)
                ((ω : U) ×ₛ RatSet) (RatSet : U)).mpr
             ⟨hkv, mulQ_in_RatSet v x hv hx⟩,
           k, v, hk, hv, by rw [if_pos hx]⟩
      exact apply_eq (powRatQStepFn x) ⟨k, v⟩ (mulQ v x)
        ((powRatQStepFn_is_function x).2 ⟨k, v⟩ hkv) h_mem

    /-! ============================================================ -/
    /-! ### SECTION 2: RATIONAL POWER                            ### -/
    /-! ============================================================ -/

    /-- The exponentiation function: powRatQFn x is the unique F : ω → ℚ
        with F(∅) = 1Q and F(σ k) = mulQ (F k) x. -/
    noncomputable def powRatQFn (x : U) : U :=
      Classical.choose (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (powRatQStepFn x)
          oneQ_mem_RatSet (powRatQStepFn_is_function x)))

    /-- powRatQFn x is a function from ω to RatSet. -/
    theorem powRatQFn_is_function (x : U) :
        IsFunction (powRatQFn x) (ω : U) (RatSet : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (powRatQStepFn x)
          oneQ_mem_RatSet (powRatQStepFn_is_function x)))).1

    /-- Rational power: x^n. -/
    noncomputable def powRatQ (x n : U) : U := (powRatQFn x)⦅n⦆

    private theorem powRatQFn_apply_in_RatSet (x n : U) (hn : n ∈ (ω : U)) :
        (powRatQFn x)⦅n⦆ ∈ (RatSet : U) := by
      have hF := powRatQFn_is_function x
      have h_pair := apply_mem (powRatQFn x) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ (ω : U) (RatSet : U)).mp
               (hF.1 _ h_pair)).2

    private theorem powRatQFn_zero (x : U) :
        (powRatQFn x)⦅(∅ : U)⦆ = (oneQ : U) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (powRatQStepFn x)
          oneQ_mem_RatSet (powRatQStepFn_is_function x)))).2.1

    private theorem powRatQFn_succ (x n : U) (hn : n ∈ (ω : U)) :
        (powRatQFn x)⦅σ n⦆ = (powRatQStepFn x)⦅⟨n, (powRatQFn x)⦅n⦆⟩⦆ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (RatSet : U) (oneQ : U) (powRatQStepFn x)
          oneQ_mem_RatSet (powRatQStepFn_is_function x)))).2.2 n hn

    /-- x^∅ = 1Q (empty exponent is one). -/
    theorem powRatQ_zero (x : U) : powRatQ x ∅ = (oneQ : U) := by
      unfold powRatQ; exact powRatQFn_zero x

    /-- x^(σ n) = (x^n) · x for x ∈ RatSet, n ∈ ω. -/
    theorem powRatQ_succ (x n : U) (hx : x ∈ (RatSet : U)) (hn : n ∈ (ω : U)) :
        powRatQ x (σ n) = mulQ (powRatQ x n) x := by
      unfold powRatQ
      rw [powRatQFn_succ x n hn]
      exact powRatQStepFn_apply hn (powRatQFn_apply_in_RatSet x n hn) hx

    /-- x^n ∈ ℚ for any n ∈ ω. -/
    theorem powRatQ_mem_RatSet (x n : U) (hn : n ∈ (ω : U)) :
        powRatQ x n ∈ (RatSet : U) := by
      unfold powRatQ; exact powRatQFn_apply_in_RatSet x n hn

    /-! ============================================================ -/
    /-! ### SECTION 3: BASIC ALGEBRAIC PROPERTIES               ### -/
    /-! ============================================================ -/

    /-- x^(σ ∅) = x for x ∈ ℚ. -/
    theorem powRatQ_one (x : U) (hx : x ∈ (RatSet : U)) :
        powRatQ x (σ ∅) = x := by
      rw [powRatQ_succ x ∅ hx zero_in_Omega, powRatQ_zero]
      exact mulQ_one_left x hx

    /-- 0Q^(σ n) = 0Q for any n ∈ ω. -/
    theorem powRatQ_zero_base_succ (n : U) (hn : n ∈ (ω : U)) :
        powRatQ (zeroQ : U) (σ n) = (zeroQ : U) := by
      rw [powRatQ_succ (zeroQ : U) n zeroQ_mem_RatSet hn]
      exact mulQ_zero_right (powRatQ (zeroQ : U) n) (powRatQ_mem_RatSet (zeroQ : U) n hn)

    /-- 0Q^n = 0Q for any n ≠ ∅ in ω. -/
    theorem powRatQ_zero_base (n : U) (hn : n ∈ (ω : U)) (hn_ne : n ≠ (∅ : U)) :
        powRatQ (zeroQ : U) n = (zeroQ : U) := by
      obtain ⟨k, hk_eq⟩ :=
        (eq_zero_or_exists_succ n (mem_Omega_is_Nat n hn)).resolve_left hn_ne
      have hk_nat : IsNat k :=
        nat_element_is_nat n k (mem_Omega_is_Nat n hn) (hk_eq ▸ mem_succ_self k)
      rw [hk_eq]
      exact powRatQ_zero_base_succ k (Nat_in_Omega k hk_nat)

    /-- 1Q^n = 1Q for all n ∈ ω. -/
    theorem powRatQ_one_base (n : U) (hn : n ∈ (ω : U)) :
        powRatQ (oneQ : U) n = (oneQ : U) := by
      have hI : IsInductive
          (sep (ω : U) (fun m => powRatQ (oneQ : U) m = (oneQ : U))) := by
        constructor
        · rw [mem_sep_iff]
          exact ⟨zero_in_Omega, powRatQ_zero (oneQ : U)⟩
        · intro k hk
          rw [mem_sep_iff] at hk ⊢
          obtain ⟨hk_omega, ihk⟩ := hk
          refine ⟨succ_in_Omega k hk_omega, ?_⟩
          rw [powRatQ_succ (oneQ : U) k oneQ_mem_RatSet hk_omega, ihk,
              mulQ_one_left (oneQ : U) oneQ_mem_RatSet]
      have hn_sep := nat_in_inductive_set n (mem_Omega_is_Nat n hn) _ hI
      rw [mem_sep_iff] at hn_sep
      exact hn_sep.2

    /-! ============================================================ -/
    /-! ### SECTION 4: EXPONENT ADDITION                         ### -/
    /-! ============================================================ -/

    /-- x^(n+m) = x^n · x^m for x ∈ ℚ, n m ∈ ω. -/
    theorem powRatQ_add_exp (x n m : U) (hx : x ∈ (RatSet : U))
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        powRatQ x (add n m) = mulQ (powRatQ x n) (powRatQ x m) := by
      have hI : IsInductive (sep (ω : U)
            (fun k => powRatQ x (add n k) = mulQ (powRatQ x n) (powRatQ x k))) := by
        constructor
        · rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ?_⟩
          rw [add_zero n hn, powRatQ_zero,
              mulQ_one_right (powRatQ x n) (powRatQ_mem_RatSet x n hn)]
        · intro k hk
          rw [mem_sep_iff] at hk ⊢
          obtain ⟨hk_omega, ihk⟩ := hk
          refine ⟨succ_in_Omega k hk_omega, ?_⟩
          rw [add_succ n k hn hk_omega,
              powRatQ_succ x (add n k) hx (add_in_Omega n k hn hk_omega),
              ihk,
              mulQ_assoc (powRatQ x n) (powRatQ x k) x
                (powRatQ_mem_RatSet x n hn) (powRatQ_mem_RatSet x k hk_omega) hx,
              ← powRatQ_succ x k hx hk_omega]
      have hm_sep := nat_in_inductive_set m (mem_Omega_is_Nat m hm) _ hI
      rw [mem_sep_iff] at hm_sep
      exact hm_sep.2

    /-! ============================================================ -/
    /-! ### SECTION 5: BASE MULTIPLICATION                       ### -/
    /-! ============================================================ -/

    /-- (a·b)·(c·d) = (a·c)·(b·d) — helper for powRatQ_mul_base. -/
    private theorem mulQ_mul4_swap (a b c d : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U))
        (hc : c ∈ (RatSet : U)) (hd : d ∈ (RatSet : U)) :
        mulQ (mulQ a b) (mulQ c d) = mulQ (mulQ a c) (mulQ b d) :=
      calc mulQ (mulQ a b) (mulQ c d)
          = mulQ a (mulQ b (mulQ c d)) := by
              rw [mulQ_assoc a b (mulQ c d) ha hb (mulQ_in_RatSet c d hc hd)]
        _ = mulQ a (mulQ (mulQ b c) d) := by
              rw [← mulQ_assoc b c d hb hc hd]
        _ = mulQ a (mulQ (mulQ c b) d) := by
              rw [mulQ_comm b c hb hc]
        _ = mulQ a (mulQ c (mulQ b d)) := by
              rw [mulQ_assoc c b d hc hb hd]
        _ = mulQ (mulQ a c) (mulQ b d) := by
              rw [← mulQ_assoc a c (mulQ b d) ha hc (mulQ_in_RatSet b d hb hd)]

    /-- (x·y)^n = x^n · y^n for x y ∈ ℚ, n ∈ ω. -/
    theorem powRatQ_mul_base (x y n : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hn : n ∈ (ω : U)) :
        powRatQ (mulQ x y) n = mulQ (powRatQ x n) (powRatQ y n) := by
      have hI : IsInductive (sep (ω : U)
            (fun k => powRatQ (mulQ x y) k = mulQ (powRatQ x k) (powRatQ y k))) := by
        constructor
        · rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ?_⟩
          rw [powRatQ_zero, powRatQ_zero, powRatQ_zero,
              mulQ_one_left (oneQ : U) oneQ_mem_RatSet]
        · intro k hk
          rw [mem_sep_iff] at hk ⊢
          obtain ⟨hk_omega, ihk⟩ := hk
          refine ⟨succ_in_Omega k hk_omega, ?_⟩
          rw [powRatQ_succ (mulQ x y) k (mulQ_in_RatSet x y hx hy) hk_omega,
              ihk,
              powRatQ_succ x k hx hk_omega,
              powRatQ_succ y k hy hk_omega]
          exact mulQ_mul4_swap (powRatQ x k) (powRatQ y k) x y
            (powRatQ_mem_RatSet x k hk_omega) (powRatQ_mem_RatSet y k hk_omega) hx hy
      have hn_sep := nat_in_inductive_set n (mem_Omega_is_Nat n hn) _ hI
      rw [mem_sep_iff] at hn_sep
      exact hn_sep.2

  end Rat.Pow

  export Rat.Pow (
    -- Section 1: step function
    powRatQStepFn
    mem_powRatQStepFn
    powRatQStepFn_is_function
    powRatQStepFn_apply
    -- Section 2: powRatQ
    powRatQFn
    powRatQFn_is_function
    powRatQ
    powRatQ_zero
    powRatQ_succ
    powRatQ_mem_RatSet
    -- Section 3: basic properties
    powRatQ_one
    powRatQ_zero_base_succ
    powRatQ_zero_base
    powRatQ_one_base
    -- Section 4: exponent addition
    powRatQ_add_exp
    -- Section 5: base multiplication
    powRatQ_mul_base
  )

end ZFC
