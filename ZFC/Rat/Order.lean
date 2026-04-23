/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Order

  This module defines the order relations on Q = QuotientSet RatBase RatEquivRel.

  ## Approach

  For rationals [(a,b)] with a ∈ ℤ, b ∈ NonZeroIntSet, the order is:
    [(a,b)] ≤ [(c,d)]  ⟺  (a·b)·d² ≤ b²·(c·d)  in ℤ

  This works regardless of denominator sign (positive or negative b, d).

  ## Main Definitions

  * `leQ`         — non-strict order on Q
  * `ltQ`         — strict order on Q
  * `isPositiveQ` — x is positive: ltQ zeroQ x
  * `isNegativeQ` — x is negative: ltQ x zeroQ

  ## Main Theorems

  * `leQ_repr_well_defined` — order is independent of representative
  * `leQ_iff_repr`          — leQ via SOME representatives
  * `leQ_refl`              — reflexivity
  * `leQ_trans`             — transitivity
  * `leQ_antisymm`          — antisymmetry
  * `leQ_total`             — totality
  * `ltQ_iff_leQ_and_ne`    — x < y ↔ x ≤ y ∧ x ≠ y
  * `ltQ_irrefl`            — ¬ x < x
  * `ltQ_trans`             — transitivity of <
  * `leQ_iff_ltQ_or_eq`     — x ≤ y ↔ x < y ∨ x = y
  * `addQ_leQ_addQ`         — order compatible with addition
  * `rat_trichotomy_order`   — positive, zero, or negative

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Mul
import ZFC.Int.Order

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

  universe u
  variable {U : Type u}

  namespace Rat.Order

    -- =========================================================================
    -- Section 1: Private algebraic helpers
    -- =========================================================================

    /-- (a·b)·(c·d) = (a·c)·(b·d) — rearrange four-factor product -/
    private theorem mulZ_comm4 (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (IntSet : U)) :
        mulZ (mulZ a b) (mulZ c d) = mulZ (mulZ a c) (mulZ b d) := by
      rw [mulZ_assoc a b (mulZ c d) ha hb (mulZ_in_IntSet c d hc hd),
          ← mulZ_assoc b c d hb hc hd,
          mulZ_comm b c hb hc,
          mulZ_assoc c b d hc hb hd,
          ← mulZ_assoc a c (mulZ b d) ha hc (mulZ_in_IntSet b d hb hd)]

    /-- Square of nonzero integer is strictly positive -/
    private theorem square_pos_of_ne_zero (x : U) (hx : x ∈ (IntSet : U)) (hx_ne : x ≠ zeroZ) :
        ltZ (zeroZ : U) (mulZ x x) :=
      ⟨square_nonneg x hx, fun h_eq =>
        have := (mulZ_eq_zero_iff x x hx hx).mp h_eq.symm
        this.elim hx_ne hx_ne⟩

    /-- z·x ≤ z·y and 0 < z implies x ≤ y (left cancellation) -/
    private theorem leZ_cancel_mulZ_left (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (hz_pos : ltZ (zeroZ : U) z) (h : leZ (mulZ z x) (mulZ z y)) : leZ x y := by
      rcases leZ_total x y hx hy with h_le | h_ge
      · exact h_le
      · have h_rev := mulZ_le_mulZ_nonneg y x z hy hx hz h_ge hz_pos.1
        have h_eq_zx_zy := leZ_antisymm (mulZ z x) (mulZ z y)
                           (mulZ_in_IntSet z x hz hx) (mulZ_in_IntSet z y hz hy) h h_rev
        rw [mulZ_comm z x hz hx, mulZ_comm z y hz hy] at h_eq_zx_zy
        have hxy := mulZ_cancel_right x y z hx hy hz hz_pos.2.symm h_eq_zx_zy
        rw [hxy]; exact leZ_refl y hy

    /-- x·z ≤ y·z and 0 < z implies x ≤ y (right cancellation) -/
    private theorem leZ_cancel_mulZ_right (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (hz_pos : ltZ (zeroZ : U) z) (h : leZ (mulZ x z) (mulZ y z)) : leZ x y := by
      rw [mulZ_comm x z hx hz, mulZ_comm y z hy hz] at h
      exact leZ_cancel_mulZ_left x y z hx hy hz hz_pos h

    /-- x ≤ y and 0 ≤ z → x·z ≤ y·z (right-multiply by nonneg) -/
    private theorem mulZ_le_mulZ_nonneg_right (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_le : leZ x y) (h_z_nonneg : leZ (zeroZ : U) z) :
        leZ (mulZ x z) (mulZ y z) := by
      rw [mulZ_comm x z hx hz, mulZ_comm y z hy hz]
      exact mulZ_le_mulZ_nonneg x y z hx hy hz h_le h_z_nonneg

    -- =========================================================================
    -- Section 2: leQ_repr definition and well-definedness
    -- =========================================================================

    /-- [(a,b)] ≤ [(c,d)] at representative level: (a·b)·d² ≤ b²·(c·d) -/
    def leQ_repr (a b c d : U) : Prop :=
      leZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ b b) (mulZ c d))

    -- Key algebraic identity for well-definedness (left pair substitution):
    -- Given a·b' = b·a', we have (a·b·d²)·(b'²·d'²) = (a'·b'·d'²)·(b²·d²)
    private theorem leQ_wd_lhs (a b a' b' d d' : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (ha' : a' ∈ (IntSet : U)) (hb' : b' ∈ (IntSet : U))
        (hd : d ∈ (IntSet : U)) (hd' : d' ∈ (IntSet : U))
        (hα : mulZ a b' = mulZ b a') :
        mulZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ b' b') (mulZ d' d')) =
        mulZ (mulZ (mulZ a' b') (mulZ d' d')) (mulZ (mulZ b b) (mulZ d d)) := by
      -- (a·b)·(d²) · (b'²·d'²)
      -- = (a·b)·(b'²) · (d²·d'²)        [mulZ_comm4]
      -- (a·b)·(b'²) = (a·b')·(b·b') = (b·a')·(b·b') = (b²)·(a'·b')  [using hα]
      -- = (b²)·(a'·b') · (d²·d'²)
      -- = (a'·b')·(b²) · (d²·d'²)       [comm]
      -- = (a'·b')·(d'²) · (b²·d²)       [mulZ_comm4]
      have hab  := mulZ_in_IntSet a b ha hb
      have hb'b' := mulZ_in_IntSet b' b' hb' hb'
      have hdd  := mulZ_in_IntSet d d hd hd
      have hd'd' := mulZ_in_IntSet d' d' hd' hd'
      have ha'b' := mulZ_in_IntSet a' b' ha' hb'
      have hbb  := mulZ_in_IntSet b b hb hb
      -- step1: (a·b·d²)·(b'²·d'²) = (a·b·b'²)·(d²·d'²)
      have step1 : mulZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ b' b') (mulZ d' d')) =
                   mulZ (mulZ (mulZ a b) (mulZ b' b')) (mulZ (mulZ d d) (mulZ d' d')) :=
        mulZ_comm4 (mulZ a b) (mulZ d d) (mulZ b' b') (mulZ d' d') hab hdd hb'b' hd'd'
      -- step2: (a·b)·(b'²) = (b²)·(a'·b')
      have step2 : mulZ (mulZ a b) (mulZ b' b') = mulZ (mulZ b b) (mulZ a' b') :=
        calc mulZ (mulZ a b) (mulZ b' b')
            = mulZ (mulZ a b') (mulZ b b') := mulZ_comm4 a b b' b' ha hb hb' hb'
          _ = mulZ (mulZ b a') (mulZ b b') := by rw [hα]
          _ = mulZ (mulZ b b) (mulZ a' b') := mulZ_comm4 b a' b b' hb ha' hb hb'
      -- assemble
      rw [step1, step2]
      calc mulZ (mulZ (mulZ b b) (mulZ a' b')) (mulZ (mulZ d d) (mulZ d' d'))
          = mulZ (mulZ (mulZ a' b') (mulZ b b)) (mulZ (mulZ d d) (mulZ d' d')) := by
            rw [mulZ_comm (mulZ b b) (mulZ a' b') hbb (mulZ_in_IntSet a' b' ha' hb')]
        _ = mulZ (mulZ (mulZ a' b') (mulZ d' d')) (mulZ (mulZ b b) (mulZ d d)) := by
            rw [mulZ_comm (mulZ d d) (mulZ d' d') hdd hd'd']
            exact mulZ_comm4 (mulZ a' b') (mulZ b b) (mulZ d' d') (mulZ d d)
                    ha'b' hbb hd'd' hdd

    -- Key algebraic identity for well-definedness (right pair substitution):
    -- Given c·d' = d·c', we have (b²·c·d)·(b'²·d'²) = (b'²·c'·d')·(b²·d²)
    private theorem leQ_wd_rhs (b b' c d c' d' : U)
        (hb : b ∈ (IntSet : U)) (hb' : b' ∈ (IntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (IntSet : U))
        (hc' : c' ∈ (IntSet : U)) (hd' : d' ∈ (IntSet : U))
        (hβ : mulZ c d' = mulZ d c') :
        mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ b' b') (mulZ d' d')) =
        mulZ (mulZ (mulZ b' b') (mulZ c' d')) (mulZ (mulZ b b) (mulZ d d)) := by
      -- (b²·c·d)·(b'²·d'²) = (b²·b'²)·(c·d·d'²)  [mulZ_comm4]
      -- (c·d)·(d'²) = (c·d')·(d·d') = (d·c')·(d·d') = (c'·d')·(d²)  [using hβ]
      -- = (b²·b'²)·(c'·d'·d²)
      -- = (b'²·b²)·(c'·d'·d²)  [comm]
      -- = (b'²·c'·d')·(b²·d²)  [mulZ_comm4]
      have hbb  := mulZ_in_IntSet b b hb hb
      have hb'b' := mulZ_in_IntSet b' b' hb' hb'
      have hcd  := mulZ_in_IntSet c d hc hd
      have hdd  := mulZ_in_IntSet d d hd hd
      have hd'd' := mulZ_in_IntSet d' d' hd' hd'
      have hc'd' := mulZ_in_IntSet c' d' hc' hd'
      -- hβ_step: (c·d)·(d'²) = (c'·d')·(d²)
      have hβ_step : mulZ (mulZ c d) (mulZ d' d') = mulZ (mulZ c' d') (mulZ d d) :=
        calc mulZ (mulZ c d) (mulZ d' d')
            = mulZ (mulZ c d') (mulZ d d') := mulZ_comm4 c d d' d' hc hd hd' hd'
          _ = mulZ (mulZ d c') (mulZ d d') := by rw [hβ]
          _ = mulZ (mulZ d d) (mulZ c' d') := mulZ_comm4 d c' d d' hd hc' hd hd'
          _ = mulZ (mulZ c' d') (mulZ d d) :=
              mulZ_comm (mulZ d d) (mulZ c' d') hdd hc'd'
      -- step1: (b²·c·d)·(b'²·d'²) = (b²·b'²)·(c·d·d'²)
      have step1 : mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ b' b') (mulZ d' d')) =
                   mulZ (mulZ (mulZ b b) (mulZ b' b')) (mulZ (mulZ c d) (mulZ d' d')) :=
        mulZ_comm4 (mulZ b b) (mulZ c d) (mulZ b' b') (mulZ d' d') hbb hcd hb'b' hd'd'
      rw [step1, hβ_step]
      -- (b²·b'²)·(c'·d'·d²) = (b'²·c'·d')·(b²·d²)
      calc mulZ (mulZ (mulZ b b) (mulZ b' b')) (mulZ (mulZ c' d') (mulZ d d))
          = mulZ (mulZ (mulZ b' b') (mulZ b b)) (mulZ (mulZ c' d') (mulZ d d)) := by
            rw [mulZ_comm (mulZ b b) (mulZ b' b') hbb hb'b']
        _ = mulZ (mulZ (mulZ b' b') (mulZ c' d')) (mulZ (mulZ b b) (mulZ d d)) :=
            mulZ_comm4 (mulZ b' b') (mulZ b b) (mulZ c' d') (mulZ d d)
              hb'b' hbb hc'd' hdd

    /-- leQ_repr is independent of representative choice -/
    theorem leQ_repr_well_defined (a b a' b' c d c' d' : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (ha' : a' ∈ (IntSet : U)) (hb' : b' ∈ (NonZeroIntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (NonZeroIntSet : U))
        (hc' : c' ∈ (IntSet : U)) (hd' : d' ∈ (NonZeroIntSet : U))
        (h₁ : ratClass a b = ratClass a' b')
        (h₂ : ratClass c d = ratClass c' d') :
        leQ_repr a b c d ↔ leQ_repr a' b' c' d' := by
      -- Extract IntSet memberships
      have hb_i  := NonZeroIntSet_mem_IntSet b hb
      have hb'_i := NonZeroIntSet_mem_IntSet b' hb'
      have hd_i  := NonZeroIntSet_mem_IntSet d hd
      have hd'_i := NonZeroIntSet_mem_IntSet d' hd'
      -- Extract cross-product conditions
      rw [ratClass_eq_iff a b a' b' ha hb ha' hb'] at h₁
      rw [ratClass_eq_iff c d c' d' hc hd hc' hd'] at h₂
      -- h₁ : a·b' = b·a',  h₂ : c·d' = d·c'
      -- Q = b²·d² > 0,  P = b'²·d'² > 0
      have hQ_pos : ltZ (zeroZ : U) (mulZ (mulZ b b) (mulZ d d)) :=
        positiveZ_mul_closed (mulZ b b) (mulZ d d)
          (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet d d hd_i hd_i)
          (square_pos_of_ne_zero b hb_i (NonZeroIntSet_ne_zero b hb))
          (square_pos_of_ne_zero d hd_i (NonZeroIntSet_ne_zero d hd))
      have hP_pos : ltZ (zeroZ : U) (mulZ (mulZ b' b') (mulZ d' d')) :=
        positiveZ_mul_closed (mulZ b' b') (mulZ d' d')
          (mulZ_in_IntSet b' b' hb'_i hb'_i) (mulZ_in_IntSet d' d' hd'_i hd'_i)
          (square_pos_of_ne_zero b' hb'_i (NonZeroIntSet_ne_zero b' hb'))
          (square_pos_of_ne_zero d' hd'_i (NonZeroIntSet_ne_zero d' hd'))
      -- Algebraic identities
      have hE1 := leQ_wd_lhs a b a' b' d d' ha hb_i ha' hb'_i hd_i hd'_i h₁
      have hE2 := leQ_wd_rhs b b' c d c' d' hb_i hb'_i hc hd_i hc' hd'_i h₂
      -- Membership helpers
      have hLHS  := mulZ_in_IntSet (mulZ a b) (mulZ d d)
                      (mulZ_in_IntSet a b ha hb_i) (mulZ_in_IntSet d d hd_i hd_i)
      have hRHS  := mulZ_in_IntSet (mulZ b b) (mulZ c d)
                      (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet c d hc hd_i)
      have hLHS' := mulZ_in_IntSet (mulZ a' b') (mulZ d' d')
                      (mulZ_in_IntSet a' b' ha' hb'_i) (mulZ_in_IntSet d' d' hd'_i hd'_i)
      have hRHS' := mulZ_in_IntSet (mulZ b' b') (mulZ c' d')
                      (mulZ_in_IntSet b' b' hb'_i hb'_i) (mulZ_in_IntSet c' d' hc' hd'_i)
      have hP    := mulZ_in_IntSet (mulZ b' b') (mulZ d' d')
                      (mulZ_in_IntSet b' b' hb'_i hb'_i) (mulZ_in_IntSet d' d' hd'_i hd'_i)
      have hQ    := mulZ_in_IntSet (mulZ b b) (mulZ d d)
                      (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet d d hd_i hd_i)
      constructor
      · -- Forward: leQ_repr a b c d → leQ_repr a' b' c' d'
        intro H
        unfold leQ_repr at H ⊢
        -- Multiply H on right by P ≥ 0
        have H_P := mulZ_le_mulZ_nonneg_right _ _ _ hLHS hRHS hP H hP_pos.1
        rw [hE1, hE2] at H_P
        exact leZ_cancel_mulZ_right _ _ _ hLHS' hRHS' hQ hQ_pos H_P
      · -- Backward: leQ_repr a' b' c' d' → leQ_repr a b c d
        intro H'
        unfold leQ_repr at H' ⊢
        -- Multiply H' on right by Q ≥ 0
        have H'_Q := mulZ_le_mulZ_nonneg_right _ _ _ hLHS' hRHS' hQ H' hQ_pos.1
        rw [← hE1, ← hE2] at H'_Q
        exact leZ_cancel_mulZ_right _ _ _ hLHS hRHS hP hP_pos H'_Q

    -- =========================================================================
    -- Section 3: Definitions
    -- =========================================================================

    /-- Non-strict order on Q: leQ x y holds when for ANY representatives
        (a,b) of x and (c,d) of y, we have (a·b)·d² ≤ b²·(c·d) in ℤ -/
    def leQ (x y : U) : Prop :=
      ∀ (a b c d : U), a ∈ (IntSet : U) → b ∈ (NonZeroIntSet : U) →
        c ∈ (IntSet : U) → d ∈ (NonZeroIntSet : U) →
        x = ratClass a b → y = ratClass c d → leQ_repr a b c d

    /-- Strict order on Q -/
    def ltQ (x y : U) : Prop := leQ x y ∧ x ≠ y

    /-- A rational is positive iff strictly greater than zero -/
    def isPositiveQ (x : U) : Prop := ltQ (zeroQ : U) x

    /-- A rational is negative iff strictly less than zero -/
    def isNegativeQ (x : U) : Prop := ltQ x (zeroQ : U)

    -- =========================================================================
    -- Section 4: leQ iff SOME representatives satisfy leQ_repr
    -- =========================================================================

    theorem leQ_iff_repr (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ x y ↔ ∃ a b c d : U,
          a ∈ (IntSet : U) ∧ b ∈ (NonZeroIntSet : U) ∧
          c ∈ (IntSet : U) ∧ d ∈ (NonZeroIntSet : U) ∧
          x = ratClass a b ∧ y = ratClass c d ∧ leQ_repr a b c d := by
      constructor
      · intro h_le
        obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
        obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
        exact ⟨a, b, c, d, ha, hb, hc, hd, hx_eq, hy_eq,
               h_le a b c d ha hb hc hd hx_eq hy_eq⟩
      · intro h_ex
        obtain ⟨a, b, c, d, ha, hb, hc, hd, hx_eq, hy_eq, h_repr⟩ := h_ex
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have h₁ : ratClass a b = ratClass a' b' := by rw [← hx_eq, hx_eq']
        have h₂ : ratClass c d = ratClass c' d' := by rw [← hy_eq, hy_eq']
        exact (leQ_repr_well_defined a b a' b' c d c' d'
               ha hb ha' hb' hc hd hc' hd' h₁ h₂).mp h_repr

    -- =========================================================================
    -- Section 5: Order properties
    -- =========================================================================

    /-! ### Reflexivity -/

    /-- leQ is reflexive: x ≤ x -/
    theorem leQ_refl (x : U) (hx : x ∈ (RatSet : U)) : leQ x x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      -- leQ_repr a b a b: (a·b)·b² ≤ b²·(a·b)  which is equality → refl
      have h_base : leQ_repr a b a b := by
        unfold leQ_repr
        rw [mulZ_comm (mulZ b b) (mulZ a b)
              (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet a b ha hb_i)]
        exact leZ_refl _ (mulZ_in_IntSet (mulZ a b) (mulZ b b)
                           (mulZ_in_IntSet a b ha hb_i) (mulZ_in_IntSet b b hb_i hb_i))
      intro a' b' a'' b'' ha' hb' ha'' hb'' hx_eq' hx_eq''
      have h₁ : ratClass a b = ratClass a' b' := by rw [← hx_eq, hx_eq']
      have h₂ : ratClass a b = ratClass a'' b'' := by rw [← hx_eq, hx_eq'']
      exact (leQ_repr_well_defined a b a' b' a b a'' b''
             ha hb ha' hb' ha hb ha'' hb'' h₁ h₂).mp h_base

    /-! ### Totality -/

    /-- leQ is total: x ≤ y ∨ y ≤ x -/
    theorem leQ_total (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ x y ∨ leQ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      rcases leZ_total
               (mulZ (mulZ a b) (mulZ d d))
               (mulZ (mulZ b b) (mulZ c d))
               (mulZ_in_IntSet (mulZ a b) (mulZ d d)
                 (mulZ_in_IntSet a b ha hb_i) (mulZ_in_IntSet d d hd_i hd_i))
               (mulZ_in_IntSet (mulZ b b) (mulZ c d)
                 (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet c d hc hd_i))
        with h_le | h_ge
      · -- leQ x y
        left
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have h₁ : ratClass a b = ratClass a' b' := by rw [← hx_eq, hx_eq']
        have h₂ : ratClass c d = ratClass c' d' := by rw [← hy_eq, hy_eq']
        exact (leQ_repr_well_defined a b a' b' c d c' d'
               ha hb ha' hb' hc hd hc' hd' h₁ h₂).mp h_le
      · -- leQ y x
        right
        have hb_i' := NonZeroIntSet_mem_IntSet b hb
        have hd_i' := NonZeroIntSet_mem_IntSet d hd
        -- leQ_repr c d a b: (c·d)·b² ≤ d²·(a·b)
        -- But h_ge : (b²·c·d) ≤ (a·b·d²), i.e., (c·d)·b² ≤ (a·b)·d² via comm
        have h_cd_ab : leQ_repr c d a b := by
          unfold leQ_repr
          rw [mulZ_comm (mulZ b b) (mulZ c d)
                (mulZ_in_IntSet b b hb_i' hb_i') (mulZ_in_IntSet c d hc hd_i'),
              mulZ_comm (mulZ a b) (mulZ d d)
                (mulZ_in_IntSet a b ha hb_i') (mulZ_in_IntSet d d hd_i' hd_i')] at h_ge
          exact h_ge
        intro c' d' a' b' hc' hd' ha' hb' hy_eq' hx_eq'
        have h₁ : ratClass c d = ratClass c' d' := by rw [← hy_eq, hy_eq']
        have h₂ : ratClass a b = ratClass a' b' := by rw [← hx_eq, hx_eq']
        exact (leQ_repr_well_defined c d c' d' a b a' b'
               hc hd hc' hd' ha hb ha' hb' h₁ h₂).mp h_cd_ab

    /-! ### Antisymmetry -/

    /-- leQ is antisymmetric: x ≤ y → y ≤ x → x = y -/
    theorem leQ_antisymm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h₁ : leQ x y) (h₂ : leQ y x) : x = y := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have h_le1 := h₁ a b c d ha hb hc hd hx_eq hy_eq
      have h_le2 := h₂ c d a b hc hd ha hb hy_eq hx_eq
      unfold leQ_repr at h_le1 h_le2
      -- h_le2 : (c·d)·b² ≤ d²·(a·b); rewrite with comm → same as reverse of h_le1
      rw [mulZ_comm (mulZ c d) (mulZ b b)
            (mulZ_in_IntSet c d hc hd_i) (mulZ_in_IntSet b b hb_i hb_i),
          mulZ_comm (mulZ d d) (mulZ a b)
            (mulZ_in_IntSet d d hd_i hd_i) (mulZ_in_IntSet a b ha hb_i)] at h_le2
      -- Now h_le1 : (a·b·d²) ≤ (b²·c·d) and h_le2 : (b²·c·d) ≤ (a·b·d²)
      have h_eq := leZ_antisymm _ _
                     (mulZ_in_IntSet (mulZ a b) (mulZ d d)
                       (mulZ_in_IntSet a b ha hb_i) (mulZ_in_IntSet d d hd_i hd_i))
                     (mulZ_in_IntSet (mulZ b b) (mulZ c d)
                       (mulZ_in_IntSet b b hb_i hb_i) (mulZ_in_IntSet c d hc hd_i))
                     h_le1 h_le2
      -- h_eq : (a·b)·d² = b²·(c·d)
      -- Use mulZ_comm4 to rewrite: (a·b)·(d·d) = (a·d)·(b·d) and (b·b)·(c·d) = (b·c)·(b·d)
      have h_lhs_rw : mulZ (mulZ a b) (mulZ d d) = mulZ (mulZ a d) (mulZ b d) :=
        mulZ_comm4 a b d d ha hb_i hd_i hd_i
      have h_rhs_rw : mulZ (mulZ b b) (mulZ c d) = mulZ (mulZ b c) (mulZ b d) :=
        mulZ_comm4 b b c d hb_i hb_i hc hd_i
      rw [h_lhs_rw, h_rhs_rw] at h_eq
      -- h_eq : (a·d)·(b·d) = (b·c)·(b·d)
      -- Cancel b·d ≠ 0
      have hbd_ne : mulZ b d ≠ (zeroZ : U) :=
        mulZ_nonzero_of_nonzero b d hb_i hd_i
          (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)
      have h_ad_bc := mulZ_cancel_right (mulZ a d) (mulZ b c) (mulZ b d)
                        (mulZ_in_IntSet a d ha hd_i) (mulZ_in_IntSet b c hb_i hc)
                        (mulZ_in_IntSet b d hb_i hd_i) hbd_ne h_eq
      -- h_ad_bc : a·d = b·c → ratClass a b = ratClass c d
      rw [hx_eq, hy_eq, ratClass_eq_iff a b c d ha hb hc hd]
      exact h_ad_bc

    /-! ### Transitivity -/

    /-- leQ is transitive: x ≤ y → y ≤ z → x ≤ z -/
    theorem leQ_trans (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (hxy : leQ x y) (hyz : leQ y z) : leQ x z := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := mem_RatSet_is_ratClass z hz
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hf_i := NonZeroIntSet_mem_IntSet f hf
      -- H1 : (a·b)·d² ≤ b²·(c·d)
      have H1 := hxy a b c d ha hb hc hd hx_eq hy_eq
      -- H2 : (c·d)·f² ≤ d²·(e·f)
      have H2 := hyz c d e f hc hd he hf hy_eq hz_eq
      unfold leQ_repr at H1 H2
      -- Membership helpers
      have hab := mulZ_in_IntSet a b ha hb_i
      have hcd := mulZ_in_IntSet c d hc hd_i
      have hef := mulZ_in_IntSet e f he hf_i
      have hb2 := mulZ_in_IntSet b b hb_i hb_i
      have hd2 := mulZ_in_IntSet d d hd_i hd_i
      have hf2 := mulZ_in_IntSet f f hf_i hf_i
      have hd4 := mulZ_in_IntSet (mulZ d d) (mulZ d d) hd2 hd2
      -- d² > 0 (d ≠ 0)
      have hd2_pos : ltZ (zeroZ : U) (mulZ d d) :=
        square_pos_of_ne_zero d hd_i (NonZeroIntSet_ne_zero d hd)
      -- d⁴ > 0
      have hd4_pos : ltZ (zeroZ : U) (mulZ (mulZ d d) (mulZ d d)) :=
        positiveZ_mul_closed _ _ hd2 hd2 hd2_pos hd2_pos
      -- f² ≥ 0 and b² ≥ 0
      have hf2_nn : leZ (zeroZ : U) (mulZ f f) :=
        (square_pos_of_ne_zero f hf_i (NonZeroIntSet_ne_zero f hf)).1
      have hb2_nn : leZ (zeroZ : U) (mulZ b b) :=
        (square_pos_of_ne_zero b hb_i (NonZeroIntSet_ne_zero b hb)).1
      -- d²·f² ≥ 0 and b²·d² ≥ 0
      have hd2f2_nn : leZ (zeroZ : U) (mulZ (mulZ d d) (mulZ f f)) :=
        (positiveZ_mul_closed _ _ hd2 hf2 hd2_pos
          (square_pos_of_ne_zero f hf_i (NonZeroIntSet_ne_zero f hf))).1
      have hb2d2_nn : leZ (zeroZ : U) (mulZ (mulZ b b) (mulZ d d)) :=
        (positiveZ_mul_closed _ _ hb2 hd2
          (square_pos_of_ne_zero b hb_i (NonZeroIntSet_ne_zero b hb)) hd2_pos).1
      -- Multiply H1 by (d²·f²) on the right
      have H1_mult := mulZ_le_mulZ_nonneg_right
                        (mulZ (mulZ a b) (mulZ d d))
                        (mulZ (mulZ b b) (mulZ c d))
                        (mulZ (mulZ d d) (mulZ f f))
                        (mulZ_in_IntSet (mulZ a b) (mulZ d d) hab hd2)
                        (mulZ_in_IntSet (mulZ b b) (mulZ c d) hb2 hcd)
                        (mulZ_in_IntSet (mulZ d d) (mulZ f f) hd2 hf2)
                        H1 hd2f2_nn
      -- Multiply H2 by (b²·d²) on the right
      have H2_mult := mulZ_le_mulZ_nonneg_right
                        (mulZ (mulZ c d) (mulZ f f))
                        (mulZ (mulZ d d) (mulZ e f))
                        (mulZ (mulZ b b) (mulZ d d))
                        (mulZ_in_IntSet (mulZ c d) (mulZ f f) hcd hf2)
                        (mulZ_in_IntSet (mulZ d d) (mulZ e f) hd2 hef)
                        (mulZ_in_IntSet (mulZ b b) (mulZ d d) hb2 hd2)
                        H2 hb2d2_nn
      -- Show middle terms are equal:
      -- (b²·c·d)·(d²·f²) = (c·d·f²)·(b²·d²)
      have h_mid : mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ d d) (mulZ f f)) =
                   mulZ (mulZ (mulZ c d) (mulZ f f)) (mulZ (mulZ b b) (mulZ d d)) :=
        calc mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ d d) (mulZ f f))
            = mulZ (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ c d) (mulZ f f)) :=
                mulZ_comm4 (mulZ b b) (mulZ c d) (mulZ d d) (mulZ f f) hb2 hcd hd2 hf2
          _ = mulZ (mulZ (mulZ c d) (mulZ f f)) (mulZ (mulZ b b) (mulZ d d)) :=
                mulZ_comm (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ c d) (mulZ f f))
                  (mulZ_in_IntSet (mulZ b b) (mulZ d d) hb2 hd2)
                  (mulZ_in_IntSet (mulZ c d) (mulZ f f) hcd hf2)
      -- Show LHS: (a·b·d²)·(d²·f²) = (a·b·f²)·d⁴
      have h_lhs_final : mulZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ d d) (mulZ f f)) =
                         mulZ (mulZ (mulZ a b) (mulZ f f)) (mulZ (mulZ d d) (mulZ d d)) := by
        rw [mulZ_comm (mulZ d d) (mulZ f f) hd2 hf2]
        exact mulZ_comm4 (mulZ a b) (mulZ d d) (mulZ f f) (mulZ d d) hab hd2 hf2 hd2
      -- Show RHS: (d²·e·f)·(b²·d²) = (b²·e·f)·d⁴
      have h_rhs_final : mulZ (mulZ (mulZ d d) (mulZ e f)) (mulZ (mulZ b b) (mulZ d d)) =
                         mulZ (mulZ (mulZ b b) (mulZ e f)) (mulZ (mulZ d d) (mulZ d d)) := by
        rw [mulZ_comm4 (mulZ d d) (mulZ e f) (mulZ b b) (mulZ d d) hd2 hef hb2 hd2]
        rw [mulZ_comm (mulZ d d) (mulZ b b) hd2 hb2]
        exact mulZ_comm4 (mulZ b b) (mulZ d d) (mulZ e f) (mulZ d d) hb2 hd2 hef hd2
      -- Apply transitivity
      rw [h_mid] at H1_mult
      rw [h_lhs_final] at H1_mult
      rw [h_rhs_final] at H2_mult
      -- H1_mult : (a·b·f²)·d⁴ ≤ (c·d·f²)·(b²·d²)
      -- H2_mult : (c·d·f²)·(b²·d²) ≤ (b²·e·f)·d⁴
      have hcdf2_b2d2 := mulZ_in_IntSet (mulZ (mulZ c d) (mulZ f f)) (mulZ (mulZ b b) (mulZ d d))
                           (mulZ_in_IntSet (mulZ c d) (mulZ f f) hcd hf2)
                           (mulZ_in_IntSet (mulZ b b) (mulZ d d) hb2 hd2)
      have H_trans := leZ_trans
                        (mulZ (mulZ (mulZ a b) (mulZ f f)) (mulZ (mulZ d d) (mulZ d d)))
                        (mulZ (mulZ (mulZ c d) (mulZ f f)) (mulZ (mulZ b b) (mulZ d d)))
                        (mulZ (mulZ (mulZ b b) (mulZ e f)) (mulZ (mulZ d d) (mulZ d d)))
                        (mulZ_in_IntSet (mulZ (mulZ a b) (mulZ f f)) (mulZ (mulZ d d) (mulZ d d))
                          (mulZ_in_IntSet (mulZ a b) (mulZ f f) hab hf2) hd4)
                        hcdf2_b2d2
                        (mulZ_in_IntSet (mulZ (mulZ b b) (mulZ e f)) (mulZ (mulZ d d) (mulZ d d))
                          (mulZ_in_IntSet (mulZ b b) (mulZ e f) hb2 hef) hd4)
                        H1_mult H2_mult
      -- Cancel d⁴ > 0 on the right
      have h_trans_result := leZ_cancel_mulZ_right _ _
                               (mulZ (mulZ d d) (mulZ d d))
                               (mulZ_in_IntSet (mulZ a b) (mulZ f f) hab hf2)
                               (mulZ_in_IntSet (mulZ b b) (mulZ e f) hb2 hef)
                               hd4 hd4_pos H_trans
      -- h_trans_result : leQ_repr a b e f
      -- Use well-definedness to propagate to any representatives
      intro a' b' e' f' ha' hb' he' hf' hx_eq' hz_eq'
      have h₁ : ratClass a b = ratClass a' b' := by rw [← hx_eq, hx_eq']
      have h₂ : ratClass e f = ratClass e' f' := by rw [← hz_eq, hz_eq']
      exact (leQ_repr_well_defined a b a' b' e f e' f'
             ha hb ha' hb' he hf he' hf' h₁ h₂).mp h_trans_result

    /-! ### ltQ characterization -/

    theorem ltQ_iff_leQ_and_ne (x y : U)
        (_ : x ∈ (RatSet : U)) (_ : y ∈ (RatSet : U)) :
        ltQ x y ↔ leQ x y ∧ x ≠ y := Iff.rfl

    theorem ltQ_irrefl (x : U) (_ : x ∈ (RatSet : U)) : ¬ ltQ x x :=
      fun h => h.2 rfl

    theorem ltQ_trans (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (h_xy : ltQ x y) (h_yz : ltQ y z) : ltQ x z :=
      ⟨leQ_trans x y z hx hy hz h_xy.1 h_yz.1,
       fun h_eq => h_xy.2 (leQ_antisymm x y hx hy h_xy.1 (h_eq ▸ h_yz.1))⟩

    theorem leQ_iff_ltQ_or_eq (x y : U)
        (hx : x ∈ (RatSet : U)) (_ : y ∈ (RatSet : U)) :
        leQ x y ↔ ltQ x y ∨ x = y :=
      ⟨fun h => by
        by_cases h_eq : x = y
        · exact Or.inr h_eq
        · exact Or.inl ⟨h, h_eq⟩,
       fun h => h.elim (fun hlt => hlt.1) (fun heq => heq ▸ leQ_refl x hx)⟩

    /-! ### Trichotomy -/

    /-- Every rational is positive, zero, or negative -/
    theorem rat_trichotomy_order (x : U) (hx : x ∈ (RatSet : U)) :
        isPositiveQ x ∨ x = (zeroQ : U) ∨ isNegativeQ x := by
      rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h_ge | h_le
      · by_cases h_eq : (zeroQ : U) = x
        · exact Or.inr (Or.inl h_eq.symm)
        · exact Or.inl ⟨h_ge, h_eq⟩
      · by_cases h_eq : x = (zeroQ : U)
        · exact Or.inr (Or.inl h_eq)
        · exact Or.inr (Or.inr ⟨h_le, h_eq⟩)

    /-! ### Compatibility with addition -/

    /-- Helper: product of nonzero denominators is in NonZeroIntSet -/
    private theorem mul_nz (b d : U)
        (hb : b ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulZ b d ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      exact ⟨mulZ_in_IntSet b d (NonZeroIntSet_mem_IntSet b hb) (NonZeroIntSet_mem_IntSet d hd),
             mulZ_nonzero_of_nonzero b d (NonZeroIntSet_mem_IntSet b hb)
               (NonZeroIntSet_mem_IntSet d hd)
               (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)⟩

    /-- Order is compatible with addition: x ≤ y → addQ x z ≤ addQ y z -/
    theorem addQ_leQ_addQ (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (h_le : leQ x y) : leQ (addQ x z) (addQ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := mem_RatSet_is_ratClass z hz
      have hb_i := NonZeroIntSet_mem_IntSet b hb
      have hd_i := NonZeroIntSet_mem_IntSet d hd
      have hf_i := NonZeroIntSet_mem_IntSet f hf
      -- H : leQ_repr a b c d, i.e., (a·b)·d² ≤ b²·(c·d)
      have H := h_le a b c d ha hb hc hd hx_eq hy_eq
      unfold leQ_repr at H
      -- Compute addQ x z and addQ y z
      have hxz_eq : addQ x z = ratClass (addZ (mulZ a f) (mulZ b e)) (mulZ b f) := by
        rw [hx_eq, hz_eq]; exact addQ_class a b e f ha hb he hf
      have hyz_eq : addQ y z = ratClass (addZ (mulZ c f) (mulZ d e)) (mulZ d f) := by
        rw [hy_eq, hz_eq]; exact addQ_class c d e f hc hd he hf
      -- Denominators of the sums
      have hbf : mulZ b f ∈ (NonZeroIntSet : U) := mul_nz b f hb hf
      have hdf : mulZ d f ∈ (NonZeroIntSet : U) := mul_nz d f hd hf
      have hbf_i := NonZeroIntSet_mem_IntSet _ hbf
      have hdf_i := NonZeroIntSet_mem_IntSet _ hdf
      -- Numerators
      have haf_sum := addZ_in_IntSet (mulZ a f) (mulZ b e)
                       (mulZ_in_IntSet a f ha hf_i) (mulZ_in_IntSet b e hb_i he)
      have hcf_sum := addZ_in_IntSet (mulZ c f) (mulZ d e)
                       (mulZ_in_IntSet c f hc hf_i) (mulZ_in_IntSet d e hd_i he)
      -- Membership helpers
      have hb2 := mulZ_in_IntSet b b hb_i hb_i
      have hd2 := mulZ_in_IntSet d d hd_i hd_i
      have hf2 := mulZ_in_IntSet f f hf_i hf_i
      have hf4 := mulZ_in_IntSet (mulZ f f) (mulZ f f) hf2 hf2
      have hef := mulZ_in_IntSet e f he hf_i
      have hab := mulZ_in_IntSet a b ha hb_i
      have hcd := mulZ_in_IntSet c d hc hd_i
      -- Goal: leQ_repr (af+be) (bf) (cf+de) (df)
      have h_base : leQ_repr
                      (addZ (mulZ a f) (mulZ b e)) (mulZ b f)
                      (addZ (mulZ c f) (mulZ d e)) (mulZ d f) := by
        unfold leQ_repr
        -- Expand (df)·(df) = d²·f²
        have hdf_sq : mulZ (mulZ d f) (mulZ d f) = mulZ (mulZ d d) (mulZ f f) :=
          mulZ_comm4 d f d f hd_i hf_i hd_i hf_i
        -- Expand (bf)·(bf) = b²·f²
        have hbf_sq : mulZ (mulZ b f) (mulZ b f) = mulZ (mulZ b b) (mulZ f f) :=
          mulZ_comm4 b f b f hb_i hf_i hb_i hf_i
        -- f⁴ ≥ 0
        have hf4_nn : leZ (zeroZ : U) (mulZ (mulZ f f) (mulZ f f)) :=
          (positiveZ_mul_closed _ _ hf2 hf2
            (square_pos_of_ne_zero f hf_i (NonZeroIntSet_ne_zero f hf))
            (square_pos_of_ne_zero f hf_i (NonZeroIntSet_ne_zero f hf))).1
        -- Common term C = (b²·d²)·(ef·f²)
        let C := mulZ (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ e f) (mulZ f f))
        -- Expand LHS of leQ_repr: ((af+be)·bf) · (df)²
        -- = (ab·d²)·f⁴ + C
        have h_lhs_expand :
            mulZ (mulZ (addZ (mulZ a f) (mulZ b e)) (mulZ b f))
                 (mulZ (mulZ d f) (mulZ d f)) =
            addZ (mulZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ f f) (mulZ f f))) C := by
          rw [mulZ_addZ_distrib_right (mulZ a f) (mulZ b e) (mulZ b f)
                (mulZ_in_IntSet a f ha hf_i) (mulZ_in_IntSet b e hb_i he) hbf_i,
              mulZ_comm4 a f b f ha hf_i hb_i hf_i,
              mulZ_comm4 b e b f hb_i he hb_i hf_i,
              hdf_sq,
              mulZ_addZ_distrib_right (mulZ (mulZ a b) (mulZ f f))
                (mulZ (mulZ b b) (mulZ e f)) (mulZ (mulZ d d) (mulZ f f))
                (mulZ_in_IntSet (mulZ a b) (mulZ f f) hab hf2)
                (mulZ_in_IntSet (mulZ b b) (mulZ e f) hb2 hef)
                (mulZ_in_IntSet (mulZ d d) (mulZ f f) hd2 hf2)]
          congr 1
          · exact mulZ_comm4 (mulZ a b) (mulZ f f) (mulZ d d) (mulZ f f) hab hf2 hd2 hf2
          · exact mulZ_comm4 (mulZ b b) (mulZ e f) (mulZ d d) (mulZ f f) hb2 hef hd2 hf2
        -- Expand RHS of leQ_repr: (bf)²·((cf+de)·df)
        -- = (b²·cd)·f⁴ + C
        have h_rhs_expand :
            mulZ (mulZ (mulZ b f) (mulZ b f))
                 (mulZ (addZ (mulZ c f) (mulZ d e)) (mulZ d f)) =
            addZ (mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ f f) (mulZ f f))) C := by
          rw [hbf_sq,
              mulZ_addZ_distrib_right (mulZ c f) (mulZ d e) (mulZ d f)
                (mulZ_in_IntSet c f hc hf_i) (mulZ_in_IntSet d e hd_i he) hdf_i,
              mulZ_comm4 c f d f hc hf_i hd_i hf_i,
              mulZ_comm4 d e d f hd_i he hd_i hf_i,
              mulZ_addZ_distrib_left (mulZ (mulZ b b) (mulZ f f))
                (mulZ (mulZ c d) (mulZ f f)) (mulZ (mulZ d d) (mulZ e f))
                (mulZ_in_IntSet (mulZ b b) (mulZ f f) hb2 hf2)
                (mulZ_in_IntSet (mulZ c d) (mulZ f f) hcd hf2)
                (mulZ_in_IntSet (mulZ d d) (mulZ e f) hd2 hef)]
          congr 1
          · exact mulZ_comm4 (mulZ b b) (mulZ f f) (mulZ c d) (mulZ f f) hb2 hf2 hcd hf2
          · -- (b²·f²)·(d²·ef) = C = (b²·d²)·(ef·f²)  [comm4 then comm]
            calc mulZ (mulZ (mulZ b b) (mulZ f f)) (mulZ (mulZ d d) (mulZ e f))
                = mulZ (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ f f) (mulZ e f)) :=
                    mulZ_comm4 (mulZ b b) (mulZ f f) (mulZ d d) (mulZ e f) hb2 hf2 hd2 hef
              _ = mulZ (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ e f) (mulZ f f)) := by
                    rw [mulZ_comm (mulZ f f) (mulZ e f) hf2 hef]
        rw [h_lhs_expand, h_rhs_expand]
        -- Now: addZ (ab·d²·f⁴) C ≤ addZ (b²·cd·f⁴) C
        -- From H: ab·d² ≤ b²·cd; multiply by f⁴ ≥ 0
        have H_f4 := mulZ_le_mulZ_nonneg_right
                       (mulZ (mulZ a b) (mulZ d d))
                       (mulZ (mulZ b b) (mulZ c d))
                       (mulZ (mulZ f f) (mulZ f f))
                       (mulZ_in_IntSet (mulZ a b) (mulZ d d) hab hd2)
                       (mulZ_in_IntSet (mulZ b b) (mulZ c d) hb2 hcd)
                       hf4 H hf4_nn
        exact addZ_leZ_addZ
                (mulZ (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ f f) (mulZ f f)))
                (mulZ (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ f f) (mulZ f f)))
                C
                (mulZ_in_IntSet (mulZ (mulZ a b) (mulZ d d)) (mulZ (mulZ f f) (mulZ f f))
                  (mulZ_in_IntSet (mulZ a b) (mulZ d d) hab hd2) hf4)
                (mulZ_in_IntSet (mulZ (mulZ b b) (mulZ c d)) (mulZ (mulZ f f) (mulZ f f))
                  (mulZ_in_IntSet (mulZ b b) (mulZ c d) hb2 hcd) hf4)
                (mulZ_in_IntSet (mulZ (mulZ b b) (mulZ d d)) (mulZ (mulZ e f) (mulZ f f))
                  (mulZ_in_IntSet (mulZ b b) (mulZ d d) hb2 hd2)
                  (mulZ_in_IntSet (mulZ e f) (mulZ f f) hef hf2))
                H_f4
      -- Propagate to arbitrary representatives via well-definedness
      intro a' b' c' d' ha' hb' hc' hd' hxz_eq' hyz_eq'
      have h₁ : ratClass (addZ (mulZ a f) (mulZ b e)) (mulZ b f) = ratClass a' b' := by
        rw [← hxz_eq, hxz_eq']
      have h₂ : ratClass (addZ (mulZ c f) (mulZ d e)) (mulZ d f) = ratClass c' d' := by
        rw [← hyz_eq, hyz_eq']
      exact (leQ_repr_well_defined
               (addZ (mulZ a f) (mulZ b e)) (mulZ b f)
               a' b'
               (addZ (mulZ c f) (mulZ d e)) (mulZ d f)
               c' d'
               haf_sum hbf ha' hb' hcf_sum hdf hc' hd'
               h₁ h₂).mp h_base

  end Rat.Order

export ZFC.Rat.Order (
  leQ_repr
  leQ_repr_well_defined
  leQ
  ltQ
  isPositiveQ
  isNegativeQ
  leQ_iff_repr
  leQ_refl
  leQ_trans
  leQ_antisymm
  leQ_total
  ltQ_iff_leQ_and_ne
  ltQ_irrefl
  ltQ_trans
  leQ_iff_ltQ_or_eq
  addQ_leQ_addQ
  rat_trichotomy_order
)
