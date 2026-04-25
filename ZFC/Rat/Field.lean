/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Field Properties

  This module proves that (ℚ, +, ·, 0, 1) satisfies the field axioms
  beyond what is already proved in Rat.Add, Rat.Neg, and Rat.Mul.

  ## Private helpers

  * `mulZ_in_NonZeroIntSet` — product of NonZero denominators is NonZero
  * `mul4_comm`             — (a·b)·(c·d) = (a·c)·(b·d)
  * `mul_left_swap`         — x·(y·z) = y·(x·z)

  ## Main Theorems

  * `mulQ_eq_zero_iff`        — x·y = 0 ↔ x = 0 ∨ y = 0  (no zero divisors)
  * `mulQ_ne_zeroQ`           — x ≠ 0 → y ≠ 0 → x·y ≠ 0
  * `mulQ_left_cancel`        — z ≠ 0 → z·x = z·y → x = y
  * `mulQ_right_cancel`       — z ≠ 0 → x·z = y·z → x = y
  * `invQ_invQ`               — x ≠ 0 → invQ (invQ x) = x
  * `invQ_mulQ`               — x ≠ 0 → y ≠ 0 → invQ (x·y) = invQ x · invQ y
  * `divQ_self`               — x ≠ 0 → divQ x x = 1
  * `divQ_one`                — divQ x 1 = x
  * `divQ_mulQ_cancel`        — y ≠ 0 → mulQ (divQ x y) y = x
  * `mulQ_divQ_cancel`        — y ≠ 0 → mulQ y (divQ x y) = x
  * `negQ_mulQ_left`          — negQ (mulQ x y) = mulQ (negQ x) y
  * `negQ_mulQ_right`         — negQ (mulQ x y) = mulQ x (negQ y)
  * `mulQ_addQ_distrib_left`  — x·(y+z) = x·y + x·z
  * `mulQ_addQ_distrib_right` — (x+y)·z = x·z + y·z

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
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul

  universe u
  variable {U : Type u}

  namespace Rat.Field

    -- =========================================================================
    -- Section 0: Private helpers
    -- =========================================================================

    /-- Product of two NonZeroIntSet elements is in NonZeroIntSet -/
    private theorem mulZ_in_NonZeroIntSet (b d : U)
        (hb : b ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulZ b d ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      exact ⟨mulZ_in_IntSet b d (NonZeroIntSet_mem_IntSet b hb) (NonZeroIntSet_mem_IntSet d hd),
             mulZ_nonzero_of_nonzero b d
               (NonZeroIntSet_mem_IntSet b hb) (NonZeroIntSet_mem_IntSet d hd)
               (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)⟩

    /-- 4-product rearrangement: (a·b)·(c·d) = (a·c)·(b·d) -/
    private theorem mul4_comm (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (IntSet : U)) :
        mulZ (mulZ a b) (mulZ c d) = mulZ (mulZ a c) (mulZ b d) := by
      rw [mulZ_assoc a b (mulZ c d) ha hb (mulZ_in_IntSet c d hc hd),
          ← mulZ_assoc b c d hb hc hd,
          mulZ_comm b c hb hc,
          mulZ_assoc c b d hc hb hd,
          ← mulZ_assoc a c (mulZ b d) ha hc (mulZ_in_IntSet b d hb hd)]

    /-- Left-swap: x·(y·z) = y·(x·z) -/
    private theorem mul_left_swap (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U)) :
        mulZ x (mulZ y z) = mulZ y (mulZ x z) := by
      rw [← mulZ_assoc x y z hx hy hz,
          mulZ_comm x y hx hy,
          mulZ_assoc y x z hy hx hz]

    -- =========================================================================
    -- Section 1: No zero divisors
    -- =========================================================================

    /-- No zero divisors: x·y = 0 ↔ x = 0 ∨ y = 0 -/
    theorem mulQ_eq_zero_iff (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ x y = (zeroQ : U) ↔ x = (zeroQ : U) ∨ y = (zeroQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      rw [mulQ_class a b c d ha hb hc hd,
          ratClass_eq_zeroQ_iff (mulZ a c) (mulZ b d)
              (mulZ_in_IntSet a c ha hc) (mulZ_in_NonZeroIntSet b d hb hd),
          ratClass_eq_zeroQ_iff a b ha hb,
          ratClass_eq_zeroQ_iff c d hc hd,
          mulZ_eq_zero_iff a c ha hc]

    /-- Product of non-zero rationals is non-zero -/
    theorem mulQ_ne_zeroQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hx_ne : x ≠ (zeroQ : U)) (hy_ne : y ≠ (zeroQ : U)) :
        mulQ x y ≠ (zeroQ : U) := by
      intro h
      rcases (mulQ_eq_zero_iff x y hx hy).mp h with h | h
      · exact hx_ne h
      · exact hy_ne h

    -- =========================================================================
    -- Section 2: Cancellation
    -- =========================================================================

    /-- Left cancellation: z ≠ 0 → z·x = z·y → x = y -/
    theorem mulQ_left_cancel (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (hz_ne : z ≠ (zeroQ : U))
        (h : mulQ z x = mulQ z y) : x = y := by
      have hiz := invQ_in_RatSet z hz
      have key : mulQ (invQ z) (mulQ z x) = mulQ (invQ z) (mulQ z y) := by rw [h]
      rw [← mulQ_assoc (invQ z) z x hiz hz hx,
          ← mulQ_assoc (invQ z) z y hiz hz hy,
          mulQ_invQ_left z hz hz_ne,
          mulQ_one_left x hx,
          mulQ_one_left y hy] at key
      exact key

    /-- Right cancellation: z ≠ 0 → x·z = y·z → x = y -/
    theorem mulQ_right_cancel (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (hz_ne : z ≠ (zeroQ : U))
        (h : mulQ x z = mulQ y z) : x = y := by
      apply mulQ_left_cancel x y z hx hy hz hz_ne
      rw [mulQ_comm z x hz hx, mulQ_comm z y hz hy]
      exact h

    -- =========================================================================
    -- Section 3: Double inverse and inverse of product
    -- =========================================================================

    /-- Double inverse: x ≠ 0 → invQ (invQ x) = x -/
    theorem invQ_invQ (x : U)
        (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        invQ (invQ x) = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have ha_ne := (ratClass_ne_zeroQ_iff a b ha hb).mp hx_ne
      have ha_nz := (mem_NonZeroIntSet a).mpr ⟨ha, ha_ne⟩
      rw [invQ_class a b ha_nz hb, invQ_class b a hb ha_nz]

    /-- Inverse of product: x ≠ 0 → y ≠ 0 → invQ (x·y) = invQ x · invQ y -/
    theorem invQ_mulQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hx_ne : x ≠ (zeroQ : U)) (hy_ne : y ≠ (zeroQ : U)) :
        invQ (mulQ x y) = mulQ (invQ x) (invQ y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have ha_ne := (ratClass_ne_zeroQ_iff a b ha hb).mp hx_ne
      have hc_ne := (ratClass_ne_zeroQ_iff c d hc hd).mp hy_ne
      have ha_nz := (mem_NonZeroIntSet a).mpr ⟨ha, ha_ne⟩
      have hc_nz := (mem_NonZeroIntSet c).mpr ⟨hc, hc_ne⟩
      -- invQ (ratClass (a·c) (b·d)) = ratClass (b·d) (a·c)
      -- mulQ (ratClass b a) (ratClass d c) = ratClass (b·d) (a·c) ← computation
      rw [mulQ_class a b c d ha hb hc hd,
          invQ_class (mulZ a c) (mulZ b d) (mulZ_in_NonZeroIntSet a c ha_nz hc_nz)
              (mulZ_in_NonZeroIntSet b d hb hd),
          invQ_class a b ha_nz hb,
          invQ_class c d hc_nz hd,
          mulQ_class b a d c (NonZeroIntSet_mem_IntSet b hb) ha_nz
              (NonZeroIntSet_mem_IntSet d hd) hc_nz]

    -- =========================================================================
    -- Section 4: Division properties
    -- =========================================================================

    /-- Self-division: x ≠ 0 → divQ x x = 1 -/
    theorem divQ_self (x : U)
        (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        divQ x x = (oneQ : U) :=
      mulQ_invQ_right x hx hx_ne

    /-- Division by one: divQ x 1 = x -/
    theorem divQ_one (x : U) (hx : x ∈ (RatSet : U)) :
        divQ x (oneQ : U) = x := by
      have hinv : invQ (oneQ : U) = (oneQ : U) := by
        unfold oneQ
        rw [invQ_class oneZ oneZ oneZ_mem_NonZeroIntSet oneZ_mem_NonZeroIntSet]
      unfold divQ
      rw [hinv, mulQ_one_right x hx]

    /-- (x / y) · y = x for y ≠ 0 -/
    theorem divQ_mulQ_cancel (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hy_ne : y ≠ (zeroQ : U)) :
        mulQ (divQ x y) y = x := by
      unfold divQ
      rw [mulQ_assoc x (invQ y) y hx (invQ_in_RatSet y hy) hy,
          mulQ_invQ_left y hy hy_ne,
          mulQ_one_right x hx]

    /-- y · (x / y) = x for y ≠ 0 -/
    theorem mulQ_divQ_cancel (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hy_ne : y ≠ (zeroQ : U)) :
        mulQ y (divQ x y) = x := by
      rw [mulQ_comm y (divQ x y) hy (divQ_in_RatSet x y hx hy)]
      exact divQ_mulQ_cancel x y hx hy hy_ne

    -- =========================================================================
    -- Section 5: Negation and multiplication
    -- =========================================================================

    /-- negQ distributes into the left factor: negQ (x·y) = (negQ x)·y -/
    theorem negQ_mulQ_left (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        negQ (mulQ x y) = mulQ (negQ x) y := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      rw [mulQ_class a b c d ha hb hc hd,
          negQ_class (mulZ a c) (mulZ b d)
              (mulZ_in_IntSet a c ha hc) (mulZ_in_NonZeroIntSet b d hb hd),
          negQ_class a b ha hb,
          mulQ_class (negZ a) b c d (negZ_in_IntSet a ha) hb hc hd,
          mulZ_negZ_left a c ha hc]

    /-- negQ distributes into the right factor: negQ (x·y) = x·(negQ y) -/
    theorem negQ_mulQ_right (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        negQ (mulQ x y) = mulQ x (negQ y) := by
      rw [mulQ_comm x y hx hy,
          negQ_mulQ_left y x hy hx,
          mulQ_comm (negQ y) x (negQ_in_RatSet y hy) hx]

    -- =========================================================================
    -- Section 6: Distributivity
    -- =========================================================================

    /-- Left distributivity: x · (y + z) = x·y + x·z -/
    theorem mulQ_addQ_distrib_left (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        mulQ x (addQ y z) = addQ (mulQ x y) (mulQ x z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := mem_RatSet_is_ratClass z hz
      subst hx_eq; subst hy_eq; subst hz_eq
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hf_i := NonZeroIntSet_mem_IntSet f hf
      have hdf := mulZ_in_NonZeroIntSet d f hd hf
      have hbd := mulZ_in_NonZeroIntSet b d hb hd
      have hbf := mulZ_in_NonZeroIntSet b f hb hf
      have hbd_i := NonZeroIntSet_mem_IntSet (mulZ b d) hbd
      have hbf_i := NonZeroIntSet_mem_IntSet (mulZ b f) hbf
      have hdf_i := NonZeroIntSet_mem_IntSet (mulZ d f) hdf
      -- LHS = ratClass (a·(c·f + d·e)) (b·(d·f))
      rw [addQ_class c d e f hc hd he hf,
          mulQ_class a b (addZ (mulZ c f) (mulZ d e)) (mulZ d f) ha hb
              (addZ_in_IntSet (mulZ c f) (mulZ d e)
                (mulZ_in_IntSet c f hc hf_i) (mulZ_in_IntSet d e hd_i he))
              hdf]
      -- RHS = ratClass (a·c·b·f + b·d·a·e) ((b·d)·(b·f))
      rw [mulQ_class a b c d ha hb hc hd,
          mulQ_class a b e f ha hb he hf,
          addQ_class (mulZ a c) (mulZ b d) (mulZ a e) (mulZ b f)
              (mulZ_in_IntSet a c ha hc) hbd (mulZ_in_IntSet a e ha he) hbf]
      rw [ratClass_eq_iff
            (mulZ a (addZ (mulZ c f) (mulZ d e))) (mulZ b (mulZ d f))
            (addZ (mulZ (mulZ a c) (mulZ b f)) (mulZ (mulZ b d) (mulZ a e)))
            (mulZ (mulZ b d) (mulZ b f))
            (mulZ_in_IntSet a _ ha
              (addZ_in_IntSet _ _ (mulZ_in_IntSet c f hc hf_i) (mulZ_in_IntSet d e hd_i he)))
            (mulZ_in_NonZeroIntSet b (mulZ d f) hb hdf)
            (addZ_in_IntSet _ _
              (mulZ_in_IntSet _ _ (mulZ_in_IntSet a c ha hc) hbf_i)
              (mulZ_in_IntSet _ _ hbd_i (mulZ_in_IntSet a e ha he)))
            (mulZ_in_NonZeroIntSet (mulZ b d) (mulZ b f) hbd hbf)]
      -- Expand LHS via distributivity, and RHS via distributivity
      rw [mulZ_addZ_distrib_left a (mulZ c f) (mulZ d e) ha
            (mulZ_in_IntSet c f hc hf_i) (mulZ_in_IntSet d e hd_i he),
          mulZ_addZ_distrib_right (mulZ a (mulZ c f)) (mulZ a (mulZ d e))
            (mulZ (mulZ b d) (mulZ b f))
            (mulZ_in_IntSet a _ ha (mulZ_in_IntSet c f hc hf_i))
            (mulZ_in_IntSet a _ ha (mulZ_in_IntSet d e hd_i he))
            (mulZ_in_IntSet _ _ hbd_i hbf_i),
          mulZ_addZ_distrib_left (mulZ b (mulZ d f))
            (mulZ (mulZ a c) (mulZ b f)) (mulZ (mulZ b d) (mulZ a e))
            (mulZ_in_IntSet b _ hb_i hdf_i)
            (mulZ_in_IntSet _ _ (mulZ_in_IntSet a c ha hc) hbf_i)
            (mulZ_in_IntSet _ _ hbd_i (mulZ_in_IntSet a e ha he))]
      -- Reduce to two pointwise equalities: term1 and term2
      congr 1
      · -- term1: (a·(c·f)) · ((b·d)·(b·f)) = (b·(d·f)) · ((a·c)·(b·f))
        -- Strategy:
        --   (a·(c·f)) · ((b·d)·(b·f))
        -- = ((a·c)·f) · ((b·d)·(b·f))         [← mulZ_assoc a c f]
        -- = ((a·c)·(b·d)) · (f·(b·f))         [mul4_comm]
        -- = ((a·c)·(b·d)) · ((b·f)·f)         [comm]
        -- = ((a·c)·(b·f)) · ((b·d)·f)         [mul4_comm]
        -- = ((a·c)·(b·f)) · (b·(d·f))         [mulZ_assoc b d f]
        -- = (b·(d·f)) · ((a·c)·(b·f))         [comm]
        calc mulZ (mulZ a (mulZ c f)) (mulZ (mulZ b d) (mulZ b f))
            = mulZ (mulZ (mulZ a c) f) (mulZ (mulZ b d) (mulZ b f)) := by
                congr 1; exact (mulZ_assoc a c f ha hc hf_i).symm
          _ = mulZ (mulZ (mulZ a c) (mulZ b d)) (mulZ f (mulZ b f)) :=
                mul4_comm (mulZ a c) f (mulZ b d) (mulZ b f)
                  (mulZ_in_IntSet a c ha hc) hf_i hbd_i hbf_i
          _ = mulZ (mulZ (mulZ a c) (mulZ b d)) (mulZ (mulZ b f) f) := by
                congr 1; exact mulZ_comm f (mulZ b f) hf_i hbf_i
          _ = mulZ (mulZ (mulZ a c) (mulZ b f)) (mulZ (mulZ b d) f) :=
                mul4_comm (mulZ a c) (mulZ b d) (mulZ b f) f
                  (mulZ_in_IntSet a c ha hc) hbd_i hbf_i hf_i
          _ = mulZ (mulZ (mulZ a c) (mulZ b f)) (mulZ b (mulZ d f)) := by
                congr 1; exact mulZ_assoc b d f hb_i hd_i hf_i
          _ = mulZ (mulZ b (mulZ d f)) (mulZ (mulZ a c) (mulZ b f)) :=
                mulZ_comm _ _ (mulZ_in_IntSet _ _ (mulZ_in_IntSet a c ha hc) hbf_i)
                  (mulZ_in_IntSet b _ hb_i hdf_i)
      · -- term2: (a·(d·e)) · ((b·d)·(b·f)) = (b·(d·f)) · ((b·d)·(a·e))
        -- Strategy:
        --   (a·(d·e)) · ((b·d)·(b·f))
        -- = ((a·e)·d) · ((b·d)·(b·f))         [a·(d·e) = (a·e)·d via mul_left_swap + comm]
        -- = ((a·e)·(b·d)) · (d·(b·f))         [mul4_comm]
        -- = ((a·e)·(b·d)) · (b·(d·f))         [mul_left_swap d b f]
        -- = ((b·d)·(a·e)) · (b·(d·f))         [comm]
        -- = (b·(d·f)) · ((b·d)·(a·e))         [comm]
        calc mulZ (mulZ a (mulZ d e)) (mulZ (mulZ b d) (mulZ b f))
            = mulZ (mulZ (mulZ a e) d) (mulZ (mulZ b d) (mulZ b f)) := by
                congr 1
                rw [← mul_left_swap d a e hd_i ha he,
                    mulZ_comm d (mulZ a e) hd_i (mulZ_in_IntSet a e ha he)]
          _ = mulZ (mulZ (mulZ a e) (mulZ b d)) (mulZ d (mulZ b f)) :=
                mul4_comm (mulZ a e) d (mulZ b d) (mulZ b f)
                  (mulZ_in_IntSet a e ha he) hd_i hbd_i hbf_i
          _ = mulZ (mulZ (mulZ a e) (mulZ b d)) (mulZ b (mulZ d f)) := by
                congr 1; exact mul_left_swap d b f hd_i hb_i hf_i
          _ = mulZ (mulZ (mulZ b d) (mulZ a e)) (mulZ b (mulZ d f)) := by
                congr 1
                exact mulZ_comm (mulZ a e) (mulZ b d)
                  (mulZ_in_IntSet a e ha he) hbd_i
          _ = mulZ (mulZ b (mulZ d f)) (mulZ (mulZ b d) (mulZ a e)) :=
                mulZ_comm _ _ (mulZ_in_IntSet _ _ hbd_i (mulZ_in_IntSet a e ha he))
                  (mulZ_in_IntSet b _ hb_i hdf_i)

    /-- Right distributivity: (x + y) · z = x·z + y·z -/
    theorem mulQ_addQ_distrib_right (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        mulQ (addQ x y) z = addQ (mulQ x z) (mulQ y z) := by
      rw [mulQ_comm (addQ x y) z (addQ_in_RatSet x y hx hy) hz,
          mulQ_addQ_distrib_left z x y hz hx hy,
          mulQ_comm z x hz hx,
          mulQ_comm z y hz hy]

  end Rat.Field

end ZFC

export ZFC.Rat.Field (
  mulQ_eq_zero_iff
  mulQ_ne_zeroQ
  mulQ_left_cancel
  mulQ_right_cancel
  invQ_invQ
  invQ_mulQ
  divQ_self
  divQ_one
  divQ_mulQ_cancel
  mulQ_divQ_cancel
  negQ_mulQ_left
  negQ_mulQ_right
  mulQ_addQ_distrib_left
  mulQ_addQ_distrib_right
)
