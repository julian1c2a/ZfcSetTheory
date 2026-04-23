/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Absolute Value and Sign

  This module defines subtraction, absolute value, and sign on
  ℚ = RatSet, and establishes their main algebraic and order properties.

  ## Main Definitions

  * `subQ`   — subtraction:   subQ x y = addQ x (negQ y)
  * `absQ`   — absolute value: absQ x = if 0 ≤ x then x else −x
  * `signQ`  — sign function:  signQ x ∈ {−1, 0, 1}

  ## Main Theorems

  * `absQ_in_RatSet`   — |x| ∈ ℚ
  * `absQ_nonneg`      — 0 ≤ |x|
  * `absQ_eq_zero_iff` — |x| = 0 ↔ x = 0
  * `absQ_negQ`        — |−x| = |x|
  * `absQ_mulQ`        — |x · y| = |x| · |y|
  * `absQ_triangle`    — |x + y| ≤ |x| + |y|
  * `absQ_subQ_le`     — |x − y| ≤ |x| + |y|
  * `absQ_pos`         — x ≠ 0 → 0 < |x|
  * `signQ_in_RatSet`  — signQ x ∈ ℚ
  * `signQ_mulQ_absQ`  — signQ x · |x| = x

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Mul
import ZFC.Rat.Order

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
  open ZFC.Int.Order
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order

  universe u
  variable {U : Type u}

  namespace Rat.Abs

    -- =========================================================================
    -- Section 1: Definitions
    -- =========================================================================

    /-- Subtraction on ℚ: subQ x y = x + (−y) -/
    noncomputable def subQ (x y : U) : U := addQ x (negQ y)

    /-- Absolute value on ℚ: absQ x = x if 0 ≤ x, else −x -/
    noncomputable def absQ (x : U) : U :=
      if leQ (zeroQ : U) x then x else negQ x

    /-- Sign function on ℚ: signQ x ∈ {−1, 0, 1} -/
    noncomputable def signQ (x : U) : U :=
      if x = (zeroQ : U) then zeroQ
      else if isPositiveQ x then oneQ
      else negQ oneQ

    -- =========================================================================
    -- Section 2: Private algebraic helpers
    -- =========================================================================

    /-- Product of two NonZeroIntSet elements is in NonZeroIntSet -/
    private theorem mul_nz (b d : U)
        (hb : b ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulZ b d ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      exact ⟨mulZ_in_IntSet b d (NonZeroIntSet_mem_IntSet b hb)
               (NonZeroIntSet_mem_IntSet d hd),
             mulZ_nonzero_of_nonzero b d (NonZeroIntSet_mem_IntSet b hb)
               (NonZeroIntSet_mem_IntSet d hd)
               (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)⟩

    /-- Four-fold commutativity: (a·b)·(c·d) = (a·c)·(b·d) -/
    private theorem comm4_priv (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (IntSet : U)) :
        mulZ (mulZ a b) (mulZ c d) = mulZ (mulZ a c) (mulZ b d) := by
      rw [mulZ_assoc a b (mulZ c d) ha hb (mulZ_in_IntSet c d hc hd),
          ← mulZ_assoc b c d hb hc hd,
          mulZ_comm b c hb hc,
          mulZ_assoc c b d hc hb hd,
          ← mulZ_assoc a c (mulZ b d) ha hc (mulZ_in_IntSet b d hb hd)]

    /-- leQ 0 (ratClass a b) ↔ leZ 0 (a·b) — forward direction -/
    private theorem leQ_zeroQ_elim (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (h : leQ (zeroQ : U) (ratClass a b)) :
        leZ (zeroZ : U) (mulZ a b) := by
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have H := h zeroZ oneZ a b zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet ha hb rfl rfl
      unfold leQ_repr at H
      rwa [mulZ_zero_left oneZ oneZ_mem_IntSet,
           mulZ_zero_left (mulZ b b) (mulZ_in_IntSet b b hb_i hb_i),
           mulZ_one_left oneZ oneZ_mem_IntSet,
           mulZ_one_left (mulZ a b) (mulZ_in_IntSet a b ha hb_i)] at H

    /-- leQ 0 (ratClass a b) ↔ leZ 0 (a·b) — backward direction -/
    private theorem leQ_zeroQ_intro (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (h : leZ (zeroZ : U) (mulZ a b)) :
        leQ (zeroQ : U) (ratClass a b) := by
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      rw [leQ_iff_repr zeroQ (ratClass a b) zeroQ_mem_RatSet
            (ratClass_mem_RatSet a b ha hb)]
      refine ⟨zeroZ, oneZ, a, b, zeroZ_mem_IntSet, oneZ_mem_NonZeroIntSet,
              ha, hb, rfl, rfl, ?_⟩
      unfold leQ_repr
      rw [mulZ_zero_left oneZ oneZ_mem_IntSet,
          mulZ_zero_left (mulZ b b) (mulZ_in_IntSet b b hb_i hb_i),
          mulZ_one_left oneZ oneZ_mem_IntSet,
          mulZ_one_left (mulZ a b) (mulZ_in_IntSet a b ha hb_i)]
      exact h

    /-- leQ (ratClass a b) 0 ↔ leZ (a·b) 0 — forward direction -/
    private theorem leQ_toZeroQ_elim (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (h : leQ (ratClass a b) (zeroQ : U)) :
        leZ (mulZ a b) (zeroZ : U) := by
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have H := h a b zeroZ oneZ ha hb zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet rfl rfl
      unfold leQ_repr at H
      rwa [mulZ_one_left oneZ oneZ_mem_IntSet,
           mulZ_one_right (mulZ a b) (mulZ_in_IntSet a b ha hb_i),
           mulZ_zero_left oneZ oneZ_mem_IntSet,
           mulZ_zero_right (mulZ b b) (mulZ_in_IntSet b b hb_i hb_i)] at H

    /-- leQ (ratClass a b) 0 ↔ leZ (a·b) 0 — backward direction -/
    private theorem leQ_toZeroQ_intro (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (h : leZ (mulZ a b) (zeroZ : U)) :
        leQ (ratClass a b) (zeroQ : U) := by
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      rw [leQ_iff_repr (ratClass a b) zeroQ (ratClass_mem_RatSet a b ha hb)
            zeroQ_mem_RatSet]
      refine ⟨a, b, zeroZ, oneZ, ha, hb, zeroZ_mem_IntSet, oneZ_mem_NonZeroIntSet,
              rfl, rfl, ?_⟩
      unfold leQ_repr
      rw [mulZ_one_left oneZ oneZ_mem_IntSet,
          mulZ_one_right (mulZ a b) (mulZ_in_IntSet a b ha hb_i),
          mulZ_zero_left oneZ oneZ_mem_IntSet,
          mulZ_zero_right (mulZ b b) (mulZ_in_IntSet b b hb_i hb_i)]
      exact h

    /-- negQ distributes over addQ: negQ (addQ x y) = addQ (negQ x) (negQ y) -/
    private theorem negQ_addQ_distrib (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        negQ (addQ x y) = addQ (negQ x) (negQ y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have h_num := addZ_in_IntSet (mulZ a d) (mulZ b c)
                     (mulZ_in_IntSet a d ha hd_i) (mulZ_in_IntSet b c hb_i hc)
      rw [addQ_class a b c d ha hb hc hd,
          negQ_class (addZ (mulZ a d) (mulZ b c)) (mulZ b d) h_num (mul_nz b d hb hd),
          negZ_addZ (mulZ a d) (mulZ b c)
            (mulZ_in_IntSet a d ha hd_i) (mulZ_in_IntSet b c hb_i hc),
          ← mulZ_negZ_left a d ha hd_i,
          ← mulZ_negZ_right b c hb_i hc,
          negQ_class a b ha hb,
          negQ_class c d hc hd,
          addQ_class (negZ a) b (negZ c) d
            (negZ_in_IntSet a ha) hb (negZ_in_IntSet c hc) hd]

    /-- mulQ x (negQ y) = negQ (mulQ x y) -/
    private theorem mulQ_negQ_right_priv (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ x (negQ y) = negQ (mulQ x y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      rw [negQ_class c d hc hd,
          mulQ_class a b (negZ c) d ha hb (negZ_in_IntSet c hc) hd,
          mulZ_negZ_right a c ha hc,
          mulQ_class a b c d ha hb hc hd,
          ← negQ_class (mulZ a c) (mulZ b d)
              (mulZ_in_IntSet a c ha hc) (mul_nz b d hb hd)]

    /-- mulQ (negQ x) y = negQ (mulQ x y) -/
    private theorem mulQ_negQ_left_priv (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ (negQ x) y = negQ (mulQ x y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      rw [negQ_class a b ha hb,
          mulQ_class (negZ a) b c d (negZ_in_IntSet a ha) hb hc hd,
          mulZ_negZ_left a c ha hc,
          mulQ_class a b c d ha hb hc hd,
          ← negQ_class (mulZ a c) (mulZ b d)
              (mulZ_in_IntSet a c ha hc) (mul_nz b d hb hd)]

    /-- mulQ (negQ x) (negQ y) = mulQ x y -/
    private theorem mulQ_negQ_negQ_priv (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ (negQ x) (negQ y) = mulQ x y := by
      rw [mulQ_negQ_left_priv x (negQ y) hx (negQ_in_RatSet y hy),
          mulQ_negQ_right_priv x y hx hy,
          negQ_negQ (mulQ x y) (mulQ_in_RatSet x y hx hy)]

    -- =========================================================================
    -- Section 3: Private order helpers
    -- =========================================================================

    /-- x ≤ 0 implies 0 ≤ −x -/
    private theorem leQ_negQ_of_leQ_zero (x : U) (hx : x ∈ (RatSet : U))
        (h : leQ x (zeroQ : U)) : leQ (zeroQ : U) (negQ x) := by
      have h_le := addQ_leQ_addQ x zeroQ (negQ x) hx zeroQ_mem_RatSet
                     (negQ_in_RatSet x hx) h
      rw [negQ_addQ_right x hx, addQ_zero_left (negQ x) (negQ_in_RatSet x hx)] at h_le
      exact h_le

    /-- Product of two nonnegatives is nonneg -/
    private theorem leQ_zeroQ_nonneg_mul (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h_ge_x : leQ (zeroQ : U) x) (h_ge_y : leQ (zeroQ : U) y) :
        leQ (zeroQ : U) (mulQ x y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hac := mulZ_in_IntSet a c ha hc
      have hbd := mul_nz b d hb hd
      have H_ab := leQ_zeroQ_elim a b ha hb h_ge_x
      have H_cd := leQ_zeroQ_elim c d hc hd h_ge_y
      rw [mulQ_class a b c d ha hb hc hd]
      apply leQ_zeroQ_intro (mulZ a c) (mulZ b d) hac hbd
      -- Goal: leZ zeroZ (mulZ (mulZ a c) (mulZ b d))
      -- mulZ_le_mulZ_nonneg zeroZ (a·b) (c·d) : leZ ((c·d)·0) ((c·d)·(a·b))
      have h_mul := mulZ_le_mulZ_nonneg (zeroZ : U) (mulZ a b) (mulZ c d)
                     zeroZ_mem_IntSet (mulZ_in_IntSet a b ha hb_i)
                     (mulZ_in_IntSet c d hc hd_i) H_ab H_cd
      rw [mulZ_zero_right (mulZ c d) (mulZ_in_IntSet c d hc hd_i)] at h_mul
      -- h_mul : leZ zeroZ (mulZ (mulZ c d) (mulZ a b))
      rw [mulZ_comm (mulZ c d) (mulZ a b)
            (mulZ_in_IntSet c d hc hd_i) (mulZ_in_IntSet a b ha hb_i)] at h_mul
      -- h_mul : leZ zeroZ (mulZ (mulZ a b) (mulZ c d))
      rw [comm4_priv a b c d ha hb_i hc hd_i] at h_mul
      -- h_mul : leZ zeroZ (mulZ (mulZ a c) (mulZ b d))
      exact h_mul

    /-- nonneg × nonpos product is ≤ 0 -/
    private theorem leQ_nonpos_mul (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h_ge_x : leQ (zeroQ : U) x) (h_le_y : leQ y (zeroQ : U)) :
        leQ (mulQ x y) (zeroQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hac := mulZ_in_IntSet a c ha hc
      have hbd := mul_nz b d hb hd
      have H_ab := leQ_zeroQ_elim a b ha hb h_ge_x
      have H_cd := leQ_toZeroQ_elim c d hc hd h_le_y
      rw [mulQ_class a b c d ha hb hc hd]
      apply leQ_toZeroQ_intro (mulZ a c) (mulZ b d) hac hbd
      -- Goal: leZ (mulZ (mulZ a c) (mulZ b d)) zeroZ
      -- mulZ_le_mulZ_nonneg (c·d) 0 (a·b) : leZ ((a·b)·(c·d)) ((a·b)·0)
      have h_mul := mulZ_le_mulZ_nonneg (mulZ c d) (zeroZ : U) (mulZ a b)
                     (mulZ_in_IntSet c d hc hd_i) zeroZ_mem_IntSet
                     (mulZ_in_IntSet a b ha hb_i) H_cd H_ab
      rw [mulZ_zero_right (mulZ a b) (mulZ_in_IntSet a b ha hb_i)] at h_mul
      -- h_mul : leZ (mulZ (mulZ a b) (mulZ c d)) zeroZ
      rw [comm4_priv a b c d ha hb_i hc hd_i] at h_mul
      -- h_mul : leZ (mulZ (mulZ a c) (mulZ b d)) zeroZ
      exact h_mul

    /-- nonpos × nonpos product is ≥ 0 -/
    private theorem leQ_nonneg_nonpos_mul (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h_le_x : leQ x (zeroQ : U)) (h_le_y : leQ y (zeroQ : U)) :
        leQ (zeroQ : U) (mulQ x y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hac := mulZ_in_IntSet a c ha hc
      have hbd := mul_nz b d hb hd
      have H_ab := leQ_toZeroQ_elim a b ha hb h_le_x
      have H_cd := leQ_toZeroQ_elim c d hc hd h_le_y
      rw [mulQ_class a b c d ha hb hc hd]
      apply leQ_zeroQ_intro (mulZ a c) (mulZ b d) hac hbd
      -- Goal: leZ zeroZ (mulZ (mulZ a c) (mulZ b d))
      -- mulZ_le_mulZ_nonpos (c·d) 0 (a·b) : leZ ((a·b)·0) ((a·b)·(c·d))
      have h_mul := mulZ_le_mulZ_nonpos (mulZ c d) (zeroZ : U) (mulZ a b)
                     (mulZ_in_IntSet c d hc hd_i) zeroZ_mem_IntSet
                     (mulZ_in_IntSet a b ha hb_i) H_cd H_ab
      rw [mulZ_zero_right (mulZ a b) (mulZ_in_IntSet a b ha hb_i)] at h_mul
      -- h_mul : leZ zeroZ (mulZ (mulZ a b) (mulZ c d))
      rw [comm4_priv a b c d ha hb_i hc hd_i] at h_mul
      -- h_mul : leZ zeroZ (mulZ (mulZ a c) (mulZ b d))
      exact h_mul

    /-- x ≤ |x| -/
    private theorem leQ_self_absQ (x : U) (hx : x ∈ (RatSet : U)) :
        leQ x (absQ x) := by
      by_cases h : leQ (zeroQ : U) x
      · rw [show absQ x = x from if_pos h]
        exact leQ_refl x hx
      · rw [show absQ x = negQ x from if_neg h]
        rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h_ge | h_le
        · exact absurd h_ge h
        · exact leQ_trans x zeroQ (negQ x) hx zeroQ_mem_RatSet (negQ_in_RatSet x hx)
                  h_le (leQ_negQ_of_leQ_zero x hx h_le)

    /-- −x ≤ |x| -/
    private theorem negQ_leQ_absQ (x : U) (hx : x ∈ (RatSet : U)) :
        leQ (negQ x) (absQ x) := by
      by_cases h : leQ (zeroQ : U) x
      · rw [show absQ x = x from if_pos h]
        have h_neg_le : leQ (negQ x) (zeroQ : U) := by
          have h_le := addQ_leQ_addQ zeroQ x (negQ x) zeroQ_mem_RatSet hx
                         (negQ_in_RatSet x hx) h
          rw [addQ_zero_left (negQ x) (negQ_in_RatSet x hx),
              negQ_addQ_right x hx] at h_le
          exact h_le
        exact leQ_trans (negQ x) zeroQ x (negQ_in_RatSet x hx) zeroQ_mem_RatSet hx
                 h_neg_le h
      · rw [show absQ x = negQ x from if_neg h]
        exact leQ_refl (negQ x) (negQ_in_RatSet x hx)

    -- =========================================================================
    -- Section 4: Main theorems
    -- =========================================================================

    /-- |x| ∈ ℚ -/
    theorem absQ_in_RatSet (x : U) (hx : x ∈ (RatSet : U)) :
        absQ x ∈ (RatSet : U) := by
      unfold absQ
      by_cases h : leQ (zeroQ : U) x
      · rw [if_pos h]; exact hx
      · rw [if_neg h]; exact negQ_in_RatSet x hx

    /-- 0 ≤ |x| -/
    theorem absQ_nonneg (x : U) (hx : x ∈ (RatSet : U)) :
        leQ (zeroQ : U) (absQ x) := by
      by_cases h : leQ (zeroQ : U) x
      · rw [show absQ x = x from if_pos h]; exact h
      · rw [show absQ x = negQ x from if_neg h]
        rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h_ge | h_le
        · exact absurd h_ge h
        · exact leQ_negQ_of_leQ_zero x hx h_le

    /-- |x| = 0 ↔ x = 0 -/
    theorem absQ_eq_zero_iff (x : U) (hx : x ∈ (RatSet : U)) :
        absQ x = (zeroQ : U) ↔ x = (zeroQ : U) := by
      constructor
      · intro h_abs
        by_cases h : leQ (zeroQ : U) x
        · have h_eq : absQ x = x := if_pos h
          rw [h_eq] at h_abs
          exact h_abs
        · have h_neg : absQ x = negQ x := if_neg h
          rw [h_neg] at h_abs
          have h_inv := negQ_negQ x hx
          rw [h_abs, negQ_zero] at h_inv
          exact h_inv.symm
      · intro h_eq
        rw [h_eq]
        exact if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet)

    /-- |−x| = |x| -/
    theorem absQ_negQ (x : U) (hx : x ∈ (RatSet : U)) :
        absQ (negQ x) = absQ x := by
      by_cases h : leQ (zeroQ : U) x
      · -- x ≥ 0: absQ x = x
        rw [show absQ x = x from if_pos h]
        by_cases h_eq : x = (zeroQ : U)
        · subst h_eq
          rw [negQ_zero]
          exact if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet)
        · -- x > 0: -x < 0, so absQ(-x) = -(-x) = x
          have h_neg_le : leQ (negQ x) (zeroQ : U) := by
            have h_le := addQ_leQ_addQ zeroQ x (negQ x) zeroQ_mem_RatSet hx
                           (negQ_in_RatSet x hx) h
            rw [addQ_zero_left (negQ x) (negQ_in_RatSet x hx),
                negQ_addQ_right x hx] at h_le
            exact h_le
          have h_neg_not_ge : ¬leQ (zeroQ : U) (negQ x) := by
            intro h_ge
            have h_zero := leQ_antisymm zeroQ (negQ x) zeroQ_mem_RatSet
                             (negQ_in_RatSet x hx) h_ge h_neg_le
            have h_inv := negQ_negQ x hx
            rw [← h_zero, negQ_zero] at h_inv
            exact h_eq h_inv.symm
          rw [show absQ (negQ x) = negQ (negQ x) from if_neg h_neg_not_ge,
              negQ_negQ x hx]
      · -- ¬leQ 0 x, so leQ x 0
        rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h_ge | h_le
        · exact absurd h_ge h
        · -- leQ x 0 so leQ 0 (-x)
          have h_neg_ge : leQ (zeroQ : U) (negQ x) := leQ_negQ_of_leQ_zero x hx h_le
          rw [show absQ x = negQ x from if_neg h,
              show absQ (negQ x) = negQ x from if_pos h_neg_ge]

    /-- |x · y| = |x| · |y| -/
    theorem absQ_mulQ (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        absQ (mulQ x y) = mulQ (absQ x) (absQ y) := by
      rcases rat_trichotomy_order x hx with h_pos_x | h_zero_x | h_neg_x
      · -- x > 0
        have h_abs_x : absQ x = x := if_pos h_pos_x.1
        rcases rat_trichotomy_order y hy with h_pos_y | h_zero_y | h_neg_y
        · -- y > 0: product > 0
          have h_abs_y : absQ y = y := if_pos h_pos_y.1
          have h_ge_mul := leQ_zeroQ_nonneg_mul x y hx hy h_pos_x.1 h_pos_y.1
          rw [h_abs_x, h_abs_y, show absQ (mulQ x y) = mulQ x y from if_pos h_ge_mul]
        · -- y = 0
          rw [h_zero_y, mulQ_zero_right x hx, h_abs_x,
              show absQ (zeroQ : U) = zeroQ from
                if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet),
              mulQ_zero_right x hx]
        · -- y < 0: product ≤ 0
          have h_not_ge_y : ¬leQ (zeroQ : U) y := by
            intro h_ge_y
            exact h_neg_y.2 (leQ_antisymm zeroQ y zeroQ_mem_RatSet hy
                               h_ge_y h_neg_y.1).symm
          have h_abs_y : absQ y = negQ y := if_neg h_not_ge_y
          have h_le_mul := leQ_nonpos_mul x y hx hy h_pos_x.1 h_neg_y.1
          rw [h_abs_x, h_abs_y, mulQ_negQ_right_priv x y hx hy]
          -- Goal: absQ (mulQ x y) = negQ (mulQ x y)
          by_cases h_ge_mul : leQ (zeroQ : U) (mulQ x y)
          · have h_eq := (leQ_antisymm zeroQ (mulQ x y) zeroQ_mem_RatSet
                           (mulQ_in_RatSet x y hx hy) h_ge_mul h_le_mul).symm
            rw [show absQ (mulQ x y) = mulQ x y from if_pos h_ge_mul,
                h_eq, negQ_zero]
          · exact if_neg h_ge_mul
      · -- x = 0
        rw [h_zero_x, mulQ_zero_left y hy,
            show absQ (zeroQ : U) = zeroQ from
              if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet),
            mulQ_zero_left (absQ y) (absQ_in_RatSet y hy)]
      · -- x < 0
        have h_not_ge_x : ¬leQ (zeroQ : U) x := by
          intro h_ge_x
          exact h_neg_x.2 (leQ_antisymm zeroQ x zeroQ_mem_RatSet hx
                             h_ge_x h_neg_x.1).symm
        have h_abs_x : absQ x = negQ x := if_neg h_not_ge_x
        rcases rat_trichotomy_order y hy with h_pos_y | h_zero_y | h_neg_y
        · -- y > 0: product ≤ 0
          have h_abs_y : absQ y = y := if_pos h_pos_y.1
          have h_le_mul_yx := leQ_nonpos_mul y x hy hx h_pos_y.1 h_neg_x.1
          rw [mulQ_comm y x hy hx] at h_le_mul_yx
          -- h_le_mul_yx : leQ (mulQ x y) 0
          rw [h_abs_x, h_abs_y, mulQ_negQ_left_priv x y hx hy]
          -- Goal: absQ (mulQ x y) = negQ (mulQ x y)
          by_cases h_ge_mul : leQ (zeroQ : U) (mulQ x y)
          · have h_eq := (leQ_antisymm zeroQ (mulQ x y) zeroQ_mem_RatSet
                           (mulQ_in_RatSet x y hx hy) h_ge_mul h_le_mul_yx).symm
            rw [show absQ (mulQ x y) = mulQ x y from if_pos h_ge_mul,
                h_eq, negQ_zero]
          · exact if_neg h_ge_mul
        · -- y = 0
          rw [h_zero_y, mulQ_zero_right x hx, h_abs_x,
              show absQ (zeroQ : U) = zeroQ from
                if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet),
              mulQ_zero_right (negQ x) (negQ_in_RatSet x hx)]
        · -- y < 0: product ≥ 0
          have h_not_ge_y : ¬leQ (zeroQ : U) y := by
            intro h_ge_y
            exact h_neg_y.2 (leQ_antisymm zeroQ y zeroQ_mem_RatSet hy
                               h_ge_y h_neg_y.1).symm
          have h_abs_y : absQ y = negQ y := if_neg h_not_ge_y
          have h_ge_mul := leQ_nonneg_nonpos_mul x y hx hy h_neg_x.1 h_neg_y.1
          rw [h_abs_x, h_abs_y,
              show absQ (mulQ x y) = mulQ x y from if_pos h_ge_mul,
              mulQ_negQ_negQ_priv x y hx hy]

    /-- |x + y| ≤ |x| + |y| (triangle inequality) -/
    theorem absQ_triangle (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ (absQ (addQ x y)) (addQ (absQ x) (absQ y)) := by
      have hax := absQ_in_RatSet x hx
      have hay := absQ_in_RatSet y hy
      have hny := negQ_in_RatSet y hy
      have hnx := negQ_in_RatSet x hx
      -- Step 1: addQ x y ≤ |x| + |y|
      have h1 : leQ (addQ x y) (addQ (absQ x) (absQ y)) := by
        have hA := addQ_leQ_addQ x (absQ x) y hx hax hy (leQ_self_absQ x hx)
        -- hA : leQ (addQ x y) (addQ (absQ x) y)
        have hB : leQ (addQ (absQ x) y) (addQ (absQ x) (absQ y)) := by
          have h := addQ_leQ_addQ y (absQ y) (absQ x) hy hay hax
                      (leQ_self_absQ y hy)
          -- h : leQ (addQ y (absQ x)) (addQ (absQ y) (absQ x))
          rw [← addQ_comm (absQ x) y hax hy,
              ← addQ_comm (absQ x) (absQ y) hax hay] at h
          exact h
        exact leQ_trans (addQ x y) (addQ (absQ x) y) (addQ (absQ x) (absQ y))
                 (addQ_in_RatSet x y hx hy) (addQ_in_RatSet (absQ x) y hax hy)
                 (addQ_in_RatSet (absQ x) (absQ y) hax hay) hA hB
      -- Step 2: −(x + y) = (−x) + (−y) ≤ |x| + |y|
      have h2 : leQ (negQ (addQ x y)) (addQ (absQ x) (absQ y)) := by
        rw [negQ_addQ_distrib x y hx hy]
        have hA := addQ_leQ_addQ (negQ x) (absQ x) (negQ y) hnx hax hny
                     (negQ_leQ_absQ x hx)
        -- hA : leQ (addQ (negQ x) (negQ y)) (addQ (absQ x) (negQ y))
        have hB : leQ (addQ (absQ x) (negQ y)) (addQ (absQ x) (absQ y)) := by
          have h := addQ_leQ_addQ (negQ y) (absQ y) (absQ x) hny hay hax
                      (negQ_leQ_absQ y hy)
          -- h : leQ (addQ (negQ y) (absQ x)) (addQ (absQ y) (absQ x))
          rw [← addQ_comm (absQ x) (negQ y) hax hny,
              ← addQ_comm (absQ x) (absQ y) hax hay] at h
          exact h
        exact leQ_trans (addQ (negQ x) (negQ y)) (addQ (absQ x) (negQ y))
                 (addQ (absQ x) (absQ y))
                 (addQ_in_RatSet (negQ x) (negQ y) hnx hny)
                 (addQ_in_RatSet (absQ x) (negQ y) hax hny)
                 (addQ_in_RatSet (absQ x) (absQ y) hax hay) hA hB
      -- Conclude: |x + y| ≤ |x| + |y|
      by_cases h_ge : leQ (zeroQ : U) (addQ x y)
      · rw [show absQ (addQ x y) = addQ x y from if_pos h_ge]
        exact h1
      · rw [show absQ (addQ x y) = negQ (addQ x y) from if_neg h_ge]
        exact h2

    /-- |x − y| ≤ |x| + |y| -/
    theorem absQ_subQ_le (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ (absQ (subQ x y)) (addQ (absQ x) (absQ y)) := by
      unfold subQ
      have h := absQ_triangle x (negQ y) hx (negQ_in_RatSet y hy)
      rw [absQ_negQ y hy] at h
      exact h

    /-- x ≠ 0 → 0 < |x| -/
    theorem absQ_pos (x : U) (hx : x ∈ (RatSet : U)) (h_ne : x ≠ (zeroQ : U)) :
        ltQ (zeroQ : U) (absQ x) :=
      ⟨absQ_nonneg x hx,
       fun h_eq => h_ne ((absQ_eq_zero_iff x hx).mp h_eq.symm)⟩

    /-- signQ x ∈ ℚ -/
    theorem signQ_in_RatSet (x : U) (hx : x ∈ (RatSet : U)) :
        signQ x ∈ (RatSet : U) := by
      unfold signQ
      by_cases h1 : x = (zeroQ : U)
      · rw [if_pos h1]; exact zeroQ_mem_RatSet
      · rw [if_neg h1]
        by_cases h2 : isPositiveQ x
        · rw [if_pos h2]; exact oneQ_mem_RatSet
        · rw [if_neg h2]; exact negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet

    /-- signQ x · |x| = x -/
    theorem signQ_mulQ_absQ (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ (signQ x) (absQ x) = x := by
      rcases rat_trichotomy_order x hx with h_pos | h_zero | h_neg
      · -- x > 0: signQ x = 1, absQ x = x
        have h_ne_zero : x ≠ (zeroQ : U) := fun h => h_pos.2 h.symm
        unfold signQ absQ
        rw [if_neg h_ne_zero, if_pos h_pos, if_pos h_pos.1,
            mulQ_one_left x hx]
      · -- x = 0: signQ 0 = 0, absQ 0 = 0
        subst h_zero
        unfold signQ absQ
        rw [if_pos rfl,
            if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet),
            mulQ_zero_left (zeroQ : U) zeroQ_mem_RatSet]
      · -- x < 0: signQ x = -1, absQ x = -x
        have h_not_zero : x ≠ (zeroQ : U) := h_neg.2
        have h_not_pos : ¬isPositiveQ x := fun h_p =>
          h_neg.2 (leQ_antisymm zeroQ x zeroQ_mem_RatSet hx h_p.1 h_neg.1).symm
        have h_not_ge : ¬leQ (zeroQ : U) x := fun h_ge =>
          h_neg.2 (leQ_antisymm zeroQ x zeroQ_mem_RatSet hx h_ge h_neg.1).symm
        unfold signQ absQ
        rw [if_neg h_not_zero, if_neg h_not_pos, if_neg h_not_ge,
            mulQ_negQ_negQ_priv oneQ x oneQ_mem_RatSet hx,
            mulQ_one_left x hx]

  end Rat.Abs

end ZFC

export ZFC.Rat.Abs (
  subQ
  absQ
  signQ
  absQ_in_RatSet
  absQ_nonneg
  absQ_eq_zero_iff
  absQ_negQ
  absQ_mulQ
  absQ_triangle
  absQ_subQ_le
  absQ_pos
  signQ_in_RatSet
  signQ_mulQ_absQ
)
