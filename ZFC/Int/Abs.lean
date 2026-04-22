/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Absolute Value and Sign

  This module defines the absolute value and sign functions on ℤ
  and proves their main algebraic properties.

  The absolute value is defined using the canonical trichotomy of ℤ:
  every integer is exactly one of zeroZ, intClass n ∅ (positive), or
  intClass ∅ m (negative). The uniqueness of canonical representatives
  (intClass_pos_injective, intClass_neg_injective) ensures well-definedness.

  ## Main Definitions

  * `absZ` — |x| for x ∈ ℤ, result in ω
  * `signZ` — sign(x) for x ∈ ℤ, result in ℤ

  ## Main Theorems

  * `absZ_zero` — |0| = ∅
  * `absZ_intClass_pos` — |intClass n ∅| = n  (n ∈ ω)
  * `absZ_intClass_neg` — |intClass ∅ m| = m  (m ∈ ω)
  * `absZ_in_omega` — |x| ∈ ω
  * `absZ_eq_zero_iff` — |x| = ∅ ↔ x = 0
  * `absZ_negZ` — |−x| = |x|
  * `absZ_mulZ` — |x · y| = |x| · |y|  (result in ω)
  * `signZ_values` — sign(x) ∈ {1, −1, 0}
  * `signZ_mulZ_absZ` — x = sign(x) · natToInt(|x|)
  * `signZ_mulZ` — sign(x · y) = sign(x) · sign(y)
  * `signZ_square` — sign(x) · sign(x) = 1 if x ≠ 0
-/

import ZFC.Int.Order
import ZFC.Int.Mul
import ZFC.Int.Embedding

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
  open ZFC.Nat.Mul
  open ZFC.Nat.Sub
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Int.Embedding

  universe u
  variable {U : Type u}

  namespace Int.Abs

    -- =========================================================================
    -- Section 1: absZ — Absolute Value
    -- =========================================================================

    /-- Absolute value on ℤ.
        Uses the canonical trichotomy: every z ∈ IntSet is exactly one of
        zeroZ (→ ∅), intClass n ∅ with n ≠ ∅ (→ n), or intClass ∅ m
        with m ≠ ∅ (→ m). For z ∉ IntSet, returns ∅. -/
    noncomputable def absZ (z : U) : U :=
      if z = (zeroZ : U) then ∅
      else if h : ∃ n : U, n ∈ (ω : U) ∧ n ≠ ∅ ∧ z = intClass n ∅ then
        Classical.choose h
      else if h : ∃ m : U, m ∈ (ω : U) ∧ m ≠ ∅ ∧ z = intClass ∅ m then
        Classical.choose h
      else ∅

    /-! ### Computation rules -/

    /-- |0| = ∅ -/
    theorem absZ_zero : absZ (zeroZ : U) = (∅ : U) := by
      unfold absZ
      exact if_pos rfl

    /-- |intClass n ∅| = n for any n ∈ ω -/
    theorem absZ_intClass_pos (n : U) (hn : n ∈ (ω : U)) :
        absZ (intClass n (∅ : U)) = n := by
      unfold absZ
      by_cases hn_ne : n = ∅
      · -- n = ∅: intClass ∅ ∅ = zeroZ, first branch gives ∅ = n
        subst hn_ne
        exact if_pos rfl
      · -- n ≠ ∅: intClass n ∅ ≠ zeroZ
        have h_ne_zero : intClass n (∅ : U) ≠ (zeroZ : U) := by
          unfold zeroZ
          intro h_eq
          exact hn_ne (intClass_pos_injective n ∅ hn zero_in_Omega h_eq)
        rw [if_neg h_ne_zero]
        have h_ex : ∃ n' : U, n' ∈ (ω : U) ∧ n' ≠ ∅ ∧
            intClass n (∅ : U) = intClass n' ∅ :=
          ⟨n, hn, hn_ne, rfl⟩
        rw [dif_pos h_ex]
        -- Classical.choose h_ex picks n' with intClass n ∅ = intClass n' ∅
        have h_spec := Classical.choose_spec h_ex
        exact (intClass_pos_injective n (Classical.choose h_ex)
          hn h_spec.1 h_spec.2.2).symm

    /-- |intClass ∅ m| = m for any m ∈ ω -/
    theorem absZ_intClass_neg (m : U) (hm : m ∈ (ω : U)) :
        absZ (intClass (∅ : U) m) = m := by
      unfold absZ
      by_cases hm_ne : m = ∅
      · -- m = ∅: intClass ∅ ∅ = zeroZ
        subst hm_ne
        exact if_pos rfl
      · -- m ≠ ∅
        have h_ne_zero : intClass (∅ : U) m ≠ (zeroZ : U) := by
          unfold zeroZ
          intro h_eq
          exact hm_ne (intClass_neg_injective m ∅ hm zero_in_Omega h_eq)
        rw [if_neg h_ne_zero]
        -- Show no positive canonical form exists
        have h_no_pos : ¬ (∃ n' : U, n' ∈ (ω : U) ∧ n' ≠ ∅ ∧
            intClass (∅ : U) m = intClass n' ∅) := by
          intro ⟨n', hn', hn'_ne, h_eq⟩
          exact intClass_pos_ne_neg n' m hn' hm hn'_ne hm_ne h_eq.symm
        rw [dif_neg h_no_pos]
        have h_ex : ∃ m' : U, m' ∈ (ω : U) ∧ m' ≠ ∅ ∧
            intClass (∅ : U) m = intClass ∅ m' :=
          ⟨m, hm, hm_ne, rfl⟩
        rw [dif_pos h_ex]
        have h_spec := Classical.choose_spec h_ex
        exact (intClass_neg_injective m (Classical.choose h_ex)
          hm h_spec.1 h_spec.2.2).symm

    /-! ### Closure and basic properties -/

    /-- |x| ∈ ω for any x ∈ ℤ -/
    theorem absZ_in_omega (x : U) (hx : x ∈ (IntSet : U)) :
        absZ x ∈ (ω : U) := by
      rcases int_trichotomy x hx with h_zero | ⟨n, hn, _, h_eq⟩ | ⟨m, hm, _, h_eq⟩
      · rw [h_zero, absZ_zero]; exact zero_in_Omega
      · rw [h_eq, absZ_intClass_pos n hn]; exact hn
      · rw [h_eq, absZ_intClass_neg m hm]; exact hm

    /-- |x| = ∅ ↔ x = zeroZ for x ∈ ℤ -/
    theorem absZ_eq_zero_iff (x : U) (hx : x ∈ (IntSet : U)) :
        absZ x = (∅ : U) ↔ x = (zeroZ : U) := by
      constructor
      · intro h_abs
        rcases int_trichotomy x hx with h_zero | ⟨n, hn, hn_ne, h_eq⟩ |
            ⟨m, hm, hm_ne, h_eq⟩
        · exact h_zero
        · rw [h_eq, absZ_intClass_pos n hn] at h_abs
          exact absurd h_abs hn_ne
        · rw [h_eq, absZ_intClass_neg m hm] at h_abs
          exact absurd h_abs hm_ne
      · intro h_eq; rw [h_eq, absZ_zero]

    /-- |−x| = |x| for x ∈ ℤ -/
    theorem absZ_negZ (x : U) (hx : x ∈ (IntSet : U)) :
        absZ (negZ x) = absZ x := by
      rcases int_trichotomy x hx with h_zero | ⟨n, hn, _, h_eq⟩ |
          ⟨m, hm, _, h_eq⟩
      · rw [h_zero, negZ_zero]
      · rw [h_eq, negZ_class n ∅ hn zero_in_Omega,
            absZ_intClass_neg n hn, absZ_intClass_pos n hn]
      · rw [h_eq, negZ_class ∅ m zero_in_Omega hm,
            absZ_intClass_pos m hm, absZ_intClass_neg m hm]

    /-! ### Multiplicativity: |x · y| = |x| · |y| -/

    /-- Helper: compute mulZ on canonical-positive forms. -/
    private theorem mulZ_pos_pos (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        mulZ (intClass n (∅ : U)) (intClass m ∅) = intClass (mul n m) ∅ := by
      rw [mulZ_class n ∅ m ∅ hn zero_in_Omega hm zero_in_Omega]
      rw [mul_zero n hn, zero_mul_Omega m hm, zero_mul_Omega (∅ : U) zero_in_Omega]
      rw [add_zero (mul n m) (mul_in_Omega n m hn hm)]
      rw [add_zero (∅ : U) zero_in_Omega]

    /-- Helper: compute mulZ on positive × negative forms. -/
    private theorem mulZ_pos_neg (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        mulZ (intClass n (∅ : U)) (intClass ∅ m) = intClass ∅ (mul n m) := by
      rw [mulZ_class n ∅ ∅ m hn zero_in_Omega zero_in_Omega hm]
      rw [mul_zero n hn, zero_mul_Omega (∅ : U) zero_in_Omega,
          zero_mul_Omega m hm]
      rw [add_zero (∅ : U) zero_in_Omega]
      rw [add_zero (mul n m) (mul_in_Omega n m hn hm)]

    /-- Helper: compute mulZ on negative × positive forms. -/
    private theorem mulZ_neg_pos (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        mulZ (intClass (∅ : U) n) (intClass m ∅) = intClass ∅ (mul n m) := by
      rw [mulZ_class ∅ n m ∅ zero_in_Omega hn hm zero_in_Omega]
      rw [zero_mul_Omega m hm, mul_zero n hn, mul_zero (∅ : U) zero_in_Omega]
      rw [add_zero (∅ : U) zero_in_Omega]
      rw [zero_add (mul n m) (mul_in_Omega n m hn hm)]

    /-- Helper: compute mulZ on negative × negative forms. -/
    private theorem mulZ_neg_neg (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        mulZ (intClass (∅ : U) n) (intClass ∅ m) = intClass (mul n m) ∅ := by
      rw [mulZ_class ∅ n ∅ m zero_in_Omega hn zero_in_Omega hm]
      rw [zero_mul_Omega (∅ : U) zero_in_Omega, zero_mul_Omega m hm,
          mul_zero n hn]
      rw [zero_add (mul n m) (mul_in_Omega n m hn hm)]
      rw [add_zero (∅ : U) zero_in_Omega]

    /-- |x · y| = |x| · |y| for x, y ∈ ℤ (result in ω) -/
    theorem absZ_mulZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        absZ (mulZ x y) = mul (absZ x) (absZ y) := by
      rcases int_trichotomy x hx with h_x0 | ⟨n, hn, _, hx_eq⟩ |
          ⟨n, hn, _, hx_eq⟩ <;>
      rcases int_trichotomy y hy with h_y0 | ⟨m, hm, _, hy_eq⟩ |
          ⟨m, hm, _, hy_eq⟩
      · -- 0 · 0
        rw [h_x0, h_y0, mulZ_zero_right (zeroZ : U) zeroZ_mem_IntSet,
            absZ_zero, mul_zero (∅ : U) zero_in_Omega]
      · -- 0 · pos
        rw [h_x0, hy_eq, mulZ_zero_left (intClass m ∅) (intClass_mem_IntSet m ∅ hm zero_in_Omega),
            absZ_zero, absZ_intClass_pos m hm, zero_mul_Omega m hm]
      · -- 0 · neg
        rw [h_x0, hy_eq, mulZ_zero_left (intClass (∅ : U) m) (intClass_mem_IntSet (∅ : U) m zero_in_Omega hm),
            absZ_zero, absZ_intClass_neg m hm, zero_mul_Omega m hm]
      · -- pos · 0
        rw [hx_eq, h_y0, mulZ_zero_right (intClass n ∅) (intClass_mem_IntSet n ∅ hn zero_in_Omega),
            absZ_zero, absZ_intClass_pos n hn, mul_zero n hn]
      · -- pos · pos
        rw [hx_eq, hy_eq, mulZ_pos_pos n m hn hm,
            absZ_intClass_pos n hn, absZ_intClass_pos m hm,
            absZ_intClass_pos (mul n m) (mul_in_Omega n m hn hm)]
      · -- pos · neg
        rw [hx_eq, hy_eq, mulZ_pos_neg n m hn hm,
            absZ_intClass_pos n hn, absZ_intClass_neg m hm,
            absZ_intClass_neg (mul n m) (mul_in_Omega n m hn hm)]
      · -- neg · 0
        rw [hx_eq, h_y0, mulZ_zero_right (intClass (∅ : U) n) (intClass_mem_IntSet (∅ : U) n zero_in_Omega hn),
            absZ_zero, absZ_intClass_neg n hn, mul_zero n hn]
      · -- neg · pos
        rw [hx_eq, hy_eq, mulZ_neg_pos n m hn hm,
            absZ_intClass_neg n hn, absZ_intClass_pos m hm,
            absZ_intClass_neg (mul n m) (mul_in_Omega n m hn hm)]
      · -- neg · neg
        rw [hx_eq, hy_eq, mulZ_neg_neg n m hn hm,
            absZ_intClass_neg n hn, absZ_intClass_neg m hm,
            absZ_intClass_pos (mul n m) (mul_in_Omega n m hn hm)]

    -- =========================================================================
    -- Section 2: signZ — Sign Function
    -- =========================================================================

    /-- Sign function on ℤ:
        signZ z = zeroZ if z = 0, oneZ if z is positive,
        negZ oneZ if z is negative. -/
    noncomputable def signZ (z : U) : U :=
      if z = (zeroZ : U) then zeroZ
      else if ∃ n : U, n ∈ (ω : U) ∧ n ≠ ∅ ∧ z = intClass n ∅ then oneZ
      else if z ∈ (IntSet : U) then negZ oneZ
      else ∅

    /-! ### Computation rules -/

    /-- sign(0) = 0 -/
    theorem signZ_zero : signZ (zeroZ : U) = (zeroZ : U) := by
      unfold signZ; exact if_pos rfl

    /-- sign(intClass n ∅) = oneZ for n ∈ ω, n ≠ ∅ -/
    theorem signZ_pos (n : U) (hn : n ∈ (ω : U)) (hn_ne : n ≠ ∅) :
        signZ (intClass n (∅ : U)) = (oneZ : U) := by
      unfold signZ
      have h_ne_zero : intClass n (∅ : U) ≠ (zeroZ : U) := by
        unfold zeroZ
        intro h_eq
        exact hn_ne (intClass_pos_injective n ∅ hn zero_in_Omega h_eq)
      rw [if_neg h_ne_zero]
      exact if_pos ⟨n, hn, hn_ne, rfl⟩

    /-- sign(intClass ∅ m) = negZ oneZ for m ∈ ω, m ≠ ∅ -/
    theorem signZ_neg (m : U) (hm : m ∈ (ω : U)) (hm_ne : m ≠ ∅) :
        signZ (intClass (∅ : U) m) = negZ (oneZ : U) := by
      unfold signZ
      have h_ne_zero : intClass (∅ : U) m ≠ (zeroZ : U) := by
        unfold zeroZ
        intro h_eq
        exact hm_ne (intClass_neg_injective m ∅ hm zero_in_Omega h_eq)
      rw [if_neg h_ne_zero]
      have h_no_pos : ¬ (∃ n' : U, n' ∈ (ω : U) ∧ n' ≠ ∅ ∧
          intClass (∅ : U) m = intClass n' ∅) := by
        intro ⟨n', hn', hn'_ne, h_eq⟩
        exact intClass_pos_ne_neg n' m hn' hm hn'_ne hm_ne h_eq.symm
      rw [if_neg h_no_pos]
      exact if_pos (intClass_mem_IntSet (∅ : U) m zero_in_Omega hm)

    /-! ### signZ values -/

    /-- sign(x) is one of oneZ, negZ oneZ, or zeroZ -/
    theorem signZ_values (x : U) (hx : x ∈ (IntSet : U)) :
        signZ x = (oneZ : U) ∨ signZ x = negZ (oneZ : U) ∨
        signZ x = (zeroZ : U) := by
      rcases int_trichotomy x hx with h_zero | ⟨n, hn, hn_ne, h_eq⟩ |
          ⟨m, hm, hm_ne, h_eq⟩
      · right; right; rw [h_zero, signZ_zero]
      · left; rw [h_eq, signZ_pos n hn hn_ne]
      · right; left; rw [h_eq, signZ_neg m hm hm_ne]

    /-- signZ is closed on ℤ -/
    theorem signZ_in_IntSet (x : U) (hx : x ∈ (IntSet : U)) :
        signZ x ∈ (IntSet : U) := by
      rcases signZ_values x hx with h | h | h <;> rw [h]
      · exact oneZ_mem_IntSet
      · exact negZ_in_IntSet oneZ oneZ_mem_IntSet
      · exact zeroZ_mem_IntSet

    /-! ### Decomposition: x = sign(x) · natToInt(|x|) -/

    /-- x = mulZ (signZ x) (natToInt (absZ x)) for x ∈ ℤ -/
    theorem signZ_mulZ_absZ (x : U) (hx : x ∈ (IntSet : U)) :
        x = mulZ (signZ x) (natToInt (absZ x)) := by
      rcases int_trichotomy x hx with h_zero | ⟨n, hn, hn_ne, h_eq⟩ |
          ⟨m, hm, hm_ne, h_eq⟩
      · -- x = zeroZ: sign = zeroZ, natToInt(∅) = intClass ∅ ∅ = zeroZ
        rw [h_zero, signZ_zero, absZ_zero]
        unfold natToInt
        rw [mulZ_zero_left (intClass (∅ : U) (∅ : U)) (intClass_mem_IntSet (∅ : U) (∅ : U) zero_in_Omega zero_in_Omega)]
      · -- x = intClass n ∅ (positive), sign = oneZ, abs = n
        rw [h_eq, signZ_pos n hn hn_ne, absZ_intClass_pos n hn]
        unfold natToInt
        rw [mulZ_one_left (intClass n (∅ : U)) (intClass_mem_IntSet n ∅ hn zero_in_Omega)]
      · -- x = intClass ∅ m (negative), sign = negZ oneZ, abs = m
        rw [h_eq, signZ_neg m hm hm_ne, absZ_intClass_neg m hm]
        unfold natToInt
        rw [mulZ_negZ_left (oneZ : U) (intClass m (∅ : U))
            oneZ_mem_IntSet (intClass_mem_IntSet m ∅ hm zero_in_Omega)]
        rw [mulZ_one_left (intClass m (∅ : U)) (intClass_mem_IntSet m ∅ hm zero_in_Omega)]
        rw [negZ_class m ∅ hm zero_in_Omega]

    /-! ### Multiplicativity of sign -/

    /-- sign(x · y) = sign(x) · sign(y) for x, y ∈ ℤ -/
    theorem signZ_mulZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        signZ (mulZ x y) = mulZ (signZ x) (signZ y) := by
      rcases int_trichotomy x hx with h_x0 | ⟨n, hn, hn_ne, hx_eq⟩ |
          ⟨n, hn, hn_ne, hx_eq⟩ <;>
      rcases int_trichotomy y hy with h_y0 | ⟨m, hm, hm_ne, hy_eq⟩ |
          ⟨m, hm, hm_ne, hy_eq⟩
      · -- 0 · 0
        rw [h_x0, h_y0, mulZ_zero_right (zeroZ : U) zeroZ_mem_IntSet,
            signZ_zero]
        exact (mulZ_zero_left (zeroZ : U) zeroZ_mem_IntSet).symm
      · -- 0 · pos
        rw [h_x0, hy_eq, mulZ_zero_left _ (intClass_mem_IntSet m ∅ hm zero_in_Omega),
            signZ_zero, signZ_pos m hm hm_ne,
            mulZ_zero_left (oneZ : U) oneZ_mem_IntSet]
      · -- 0 · neg
        rw [h_x0, hy_eq, mulZ_zero_left _ (intClass_mem_IntSet (∅ : U) m zero_in_Omega hm),
            signZ_zero, signZ_neg m hm hm_ne,
            mulZ_zero_left (negZ (oneZ : U)) (negZ_in_IntSet oneZ oneZ_mem_IntSet)]
      · -- pos · 0
        rw [hx_eq, h_y0, mulZ_zero_right _ (intClass_mem_IntSet n ∅ hn zero_in_Omega),
            signZ_zero, signZ_pos n hn hn_ne,
            mulZ_zero_right (oneZ : U) oneZ_mem_IntSet]
      · -- pos · pos → pos
        rw [hx_eq, hy_eq, mulZ_pos_pos n m hn hm,
            signZ_pos n hn hn_ne, signZ_pos m hm hm_ne,
            mulZ_one_right (oneZ : U) oneZ_mem_IntSet]
        exact signZ_pos (mul n m) (mul_in_Omega n m hn hm)
          (fun h => by
            rcases mul_eq_zero_iff n m hn hm |>.mp h with rfl | rfl
            · exact hn_ne rfl
            · exact hm_ne rfl)
      · -- pos · neg → neg
        rw [hx_eq, hy_eq, mulZ_pos_neg n m hn hm,
            signZ_pos n hn hn_ne, signZ_neg m hm hm_ne,
            mulZ_one_left (negZ (oneZ : U)) (negZ_in_IntSet oneZ oneZ_mem_IntSet)]
        exact signZ_neg (mul n m) (mul_in_Omega n m hn hm)
          (fun h => by
            rcases mul_eq_zero_iff n m hn hm |>.mp h with rfl | rfl
            · exact hn_ne rfl
            · exact hm_ne rfl)
      · -- neg · 0
        rw [hx_eq, h_y0, mulZ_zero_right _ (intClass_mem_IntSet (∅ : U) n zero_in_Omega hn),
            signZ_zero, signZ_neg n hn hn_ne,
            mulZ_zero_right (negZ (oneZ : U)) (negZ_in_IntSet oneZ oneZ_mem_IntSet)]
      · -- neg · pos → neg
        rw [hx_eq, hy_eq, mulZ_neg_pos n m hn hm,
            signZ_neg n hn hn_ne, signZ_pos m hm hm_ne,
            mulZ_negZ_left (oneZ : U) (oneZ : U) oneZ_mem_IntSet oneZ_mem_IntSet,
            mulZ_one_right (oneZ : U) oneZ_mem_IntSet]
        exact signZ_neg (mul n m) (mul_in_Omega n m hn hm)
          (fun h => by
            rcases mul_eq_zero_iff n m hn hm |>.mp h with rfl | rfl
            · exact hn_ne rfl
            · exact hm_ne rfl)
      · -- neg · neg → pos
        rw [hx_eq, hy_eq, mulZ_neg_neg n m hn hm,
            signZ_neg n hn hn_ne, signZ_neg m hm hm_ne,
            negZ_mulZ_negZ (oneZ : U) (oneZ : U) oneZ_mem_IntSet oneZ_mem_IntSet,
            mulZ_one_right (oneZ : U) oneZ_mem_IntSet]
        exact signZ_pos (mul n m) (mul_in_Omega n m hn hm)
          (fun h => by
            rcases mul_eq_zero_iff n m hn hm |>.mp h with rfl | rfl
            · exact hn_ne rfl
            · exact hm_ne rfl)

    /-- signZ a * signZ a = 1 if a ≠ 0. -/
    theorem signZ_square (a : U) (ha : a ∈ (IntSet : U)) (ha_ne : a ≠ zeroZ) :
        mulZ (signZ a) (signZ a) = (oneZ : U) := by
      have hs := signZ_values a ha
      rcases hs with h1 | h2 | h3
      · rw [h1]
        exact mulZ_one_left (oneZ : U) oneZ_mem_IntSet
      · rw [h2]
        have eq1 : mulZ (negZ (oneZ : U)) (negZ (oneZ : U)) = mulZ (oneZ : U) (oneZ : U) := negZ_mulZ_negZ (oneZ : U) (oneZ : U) oneZ_mem_IntSet oneZ_mem_IntSet
        rw [eq1]
        exact mulZ_one_left (oneZ : U) oneZ_mem_IntSet
      · exfalso
        have e1 : a = mulZ (signZ a) (natToInt (absZ a)) := signZ_mulZ_absZ a ha
        rw [h3] at e1
        have e2 : mulZ zeroZ (natToInt (absZ a)) = zeroZ := mulZ_zero_left _ (natToInt_mem_IntSet _ (absZ_in_omega a ha))
        rw [e2] at e1
        exact ha_ne e1

    -- =========================================================================
    -- Section 4: Triangle Inequality
    -- =========================================================================

    /-- Helper: for n,m ∈ ω with n,m ≠ ∅, the absolute value of
        intClass n m is ≤ add n m in ω. -/
    private theorem absZ_intClass_le_add (n m : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hn_ne : n ≠ ∅) (hm_ne : m ≠ ∅) :
        absZ (intClass n m) ∈ add n m ∨ absZ (intClass n m) = add n m := by
      have hn_nat := mem_Omega_is_Nat n hn
      have hm_nat := mem_Omega_is_Nat m hm
      have hnm := add_in_Omega n m hn hm
      have hnm_nat := mem_Omega_is_Nat _ hnm
      rcases natLt_trichotomy n m hn_nat hm_nat with h_lt | rfl | h_gt
      · -- n < m: intClass n m = intClass ∅ k where m = add n k
        obtain ⟨k, hk, hm_eq⟩ := le_then_exists_add_Omega n m hn hm (Or.inl h_lt)
        have hk_ne : k ≠ (∅ : U) := by
          intro h_eq
          have h := h_lt
          rw [hm_eq, h_eq, add_zero n hn] at h
          exact not_mem_self n hn_nat h
        have h_class_eq : intClass n m = intClass (∅ : U) k := by
          rw [intClass_eq_iff n m (∅ : U) k hn hm zero_in_Omega hk]
          rw [hm_eq, add_zero (add n k) (add_in_Omega n k hn hk)]
        rw [h_class_eq, absZ_intClass_neg k hk]
        -- Need: k ∈ add n m ∨ k = add n m
        have hk_in_m : k ∈ m := by
          have := add_pos_left_Omega n k hn hk hn_ne
          rw [add_comm_Omega k n hk hn, ← hm_eq] at this
          exact this
        have hm_in_nm : m ∈ add n m := by
          have := add_pos_left_Omega n m hn hm hn_ne
          rw [add_comm_Omega m n hm hn] at this
          exact this
        exact Or.inl (mem_trans k m (add n m)
          (mem_Omega_is_Nat k hk) hm_nat hnm_nat hk_in_m hm_in_nm)
      · -- n = m: intClass n n = zeroZ, absZ = ∅
        have h_class_eq : intClass n n = (zeroZ : U) := by
          show intClass n n = intClass (∅ : U) (∅ : U)
          exact (intClass_eq_iff n n (∅ : U) (∅ : U) hn hn zero_in_Omega zero_in_Omega).mpr rfl
        rw [h_class_eq, absZ_zero]
        -- Need: ∅ ∈ add n n ∨ ∅ = add n n
        have hnn_ne : add n n ≠ (∅ : U) := by
          intro h_eq
          have h_n_in : n ∈ add n n := add_pos_left_Omega n n hn hn hn_ne
          rw [h_eq] at h_n_in
          exact absurd h_n_in (EmptySet_is_empty n)
        rcases eq_zero_or_exists_succ (add n n) (mem_Omega_is_Nat _ (add_in_Omega n n hn hn))
            with h_eq | ⟨j, h_succ⟩
        · exact absurd h_eq hnn_ne
        · rw [h_succ]
          have h_sj := h_succ ▸ add_in_Omega n n hn hn
          have hj := Nat_in_Omega j (nat_element_is_nat (σ j) j
            (mem_Omega_is_Nat _ h_sj) (mem_succ_self j))
          exact Or.inl (zero_in_succ_nat j hj)
      · -- m < n: intClass n m = intClass k ∅ where n = add m k
        obtain ⟨k, hk, hn_eq⟩ := le_then_exists_add_Omega m n hm hn (Or.inl h_gt)
        have hk_ne : k ≠ (∅ : U) := by
          intro h_eq
          have h := h_gt
          rw [hn_eq, h_eq, add_zero m hm] at h
          exact not_mem_self m hm_nat h
        have h_class_eq : intClass n m = intClass k (∅ : U) := by
          rw [intClass_eq_iff n m k (∅ : U) hn hm hk zero_in_Omega]
          rw [hn_eq, add_zero (add m k) (add_in_Omega m k hm hk)]
        rw [h_class_eq, absZ_intClass_pos k hk]
        -- Need: k ∈ add n m ∨ k = add n m
        have hk_in_n : k ∈ n := by
          have := add_pos_left_Omega m k hm hk hm_ne
          rw [add_comm_Omega k m hk hm] at this
          rw [hn_eq]; exact this
        have hn_in_nm : n ∈ add n m := add_pos_left_Omega m n hm hn hm_ne
        exact Or.inl (mem_trans k n (add n m)
          (mem_Omega_is_Nat k hk) hn_nat hnm_nat hk_in_n hn_in_nm)

    /-- **Triangle inequality**: |x + y| ≤ |x| + |y| for x, y ∈ ℤ.
        Here ≤ is the natural number order (∈ or = in ω). -/
    theorem absZ_addZ_le (x y : U) (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        absZ (addZ x y) ∈ add (absZ x) (absZ y) ∨
        absZ (addZ x y) = add (absZ x) (absZ y) := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, hn_ne, rfl⟩ | ⟨n, hn, hn_ne, rfl⟩
      · -- x = zeroZ
        rw [addZ_zero_left y hy, absZ_zero,
            zero_add (absZ y) (absZ_in_omega y hy)]
        exact Or.inr rfl
      · -- x = intClass n ∅ (positive)
        rcases int_trichotomy y hy with rfl | ⟨m, hm, hm_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
        · -- y = zeroZ
          rw [addZ_zero_right _ hx, absZ_zero,
              add_zero (absZ (intClass n (∅ : U))) (absZ_in_omega _ hx)]
          exact Or.inr rfl
        · -- y = intClass m ∅ (pos + pos): equality
          rw [addZ_class n ∅ m ∅ hn zero_in_Omega hm zero_in_Omega,
              add_zero ∅ zero_in_Omega,
              absZ_intClass_pos (add n m) (add_in_Omega n m hn hm),
              absZ_intClass_pos n hn, absZ_intClass_pos m hm]
          exact Or.inr rfl
        · -- y = intClass ∅ m (pos + neg): mixed sign
          rw [addZ_class n ∅ ∅ m hn zero_in_Omega zero_in_Omega hm,
              add_zero n hn, zero_add m hm,
              absZ_intClass_pos n hn, absZ_intClass_neg m hm]
          exact absZ_intClass_le_add n m hn hm hn_ne hm_ne
      · -- x = intClass ∅ n (negative)
        rcases int_trichotomy y hy with rfl | ⟨m, hm, hm_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
        · -- y = zeroZ
          rw [addZ_zero_right _ hx, absZ_zero,
              add_zero (absZ (intClass (∅ : U) n)) (absZ_in_omega _ hx)]
          exact Or.inr rfl
        · -- y = intClass m ∅ (neg + pos): mixed sign
          rw [addZ_class ∅ n m ∅ zero_in_Omega hn hm zero_in_Omega,
              zero_add m hm, add_zero n hn,
              absZ_intClass_neg n hn, absZ_intClass_pos m hm]
          have h := absZ_intClass_le_add m n hm hn hm_ne hn_ne
          rwa [add_comm_Omega m n hm hn] at h
        · -- y = intClass ∅ m (neg + neg): equality
          rw [addZ_class (∅ : U) n (∅ : U) m zero_in_Omega hn zero_in_Omega hm,
              add_zero (∅ : U) zero_in_Omega,
              absZ_intClass_neg (add n m) (add_in_Omega n m hn hm),
              absZ_intClass_neg n hn, absZ_intClass_neg m hm]
          exact Or.inr rfl

    -- =========================================================================
    -- Section 6: Additional absolute value lemmas
    -- =========================================================================

    /-- **Positivity of absolute value**: if x ≠ 0 then |x| ≠ 0 in ω. -/
    theorem absZ_pos (x : U) (hx : x ∈ (IntSet : U)) (hx_ne : x ≠ (zeroZ : U)) :
        absZ x ≠ (∅ : U) := by
      intro h
      exact hx_ne ((absZ_eq_zero_iff x hx).mp h)

    /-- **Non-negativity of |x| in ℤ**: leZ 0 (natToInt (absZ x)) for x ∈ ℤ. -/
    theorem absZ_mulZ_nonneg (x : U) (hx : x ∈ (IntSet : U)) :
        leZ zeroZ (natToInt (absZ x)) := by
      have h := natToInt_preserves_le (∅ : U) (absZ x)
                  zero_in_Omega (absZ_in_omega x hx)
                  (EmptySet_subseteq_any (absZ x))
      have h_zero : natToInt (∅ : U) = (zeroZ : U) := rfl
      rwa [h_zero] at h

    /-- **Subtractive triangle inequality**: |x - y| ≤ |x| + |y| for x, y ∈ ℤ. -/
    theorem absZ_subZ_le (x y : U) (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        absZ (subZ x y) ∈ add (absZ x) (absZ y) ∨
        absZ (subZ x y) = add (absZ x) (absZ y) := by
      unfold subZ
      have h := absZ_addZ_le x (negZ y) hx (negZ_in_IntSet y hy)
      rwa [absZ_negZ y hy] at h

  end Int.Abs

  export Int.Abs (
    absZ
    absZ_zero
    absZ_intClass_pos
    absZ_intClass_neg
    absZ_in_omega
    absZ_eq_zero_iff
    absZ_negZ
    absZ_mulZ
    signZ
    signZ_zero
    signZ_pos
    signZ_neg
    signZ_values
    signZ_in_IntSet
    signZ_mulZ_absZ
    signZ_mulZ
    signZ_square
    absZ_addZ_le
    absZ_pos
    absZ_mulZ_nonneg
    absZ_subZ_le
  )

end ZFC
