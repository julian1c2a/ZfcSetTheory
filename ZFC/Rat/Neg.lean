/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Negation

  This module defines negation on Q = QuotientSet RatBase RatEquivRel
  using the QuotientLift infrastructure. The operation lifts the formula
  (a, b) ↦ ratClass (negZ a) b from RatBase to Q.

  ## Main Definitions

  * `negQ` — negation on Q: negQ x

  ## Main Theorems

  * `negQ_class`       — computation rule: negQ (ratClass a b) = ratClass (negZ a) b
  * `negQ_in_RatSet`   — closure: x ∈ Q → negQ x ∈ Q
  * `negQ_addQ_right`  — right inverse: addQ x (negQ x) = zeroQ
  * `negQ_addQ_left`   — left inverse:  addQ (negQ x) x = zeroQ
  * `negQ_negQ`        — involution: negQ (negQ x) = x
  * `negQ_zero`        — negQ zeroQ = zeroQ

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Add

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

  universe u
  variable {U : Type u}

  namespace Rat.Neg

    -- =========================================================================
    -- Section 1: Helper
    -- =========================================================================

    /-- Product of two nonzero rationals' denominators is nonzero -/
    private theorem mulZ_mem_NonZeroIntSet' (b d : U)
        (hb : b ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulZ b d ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      exact ⟨mulZ_in_IntSet b d hb_int hd_int,
             mulZ_nonzero_of_nonzero b d hb_int hd_int
               (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)⟩

    -- =========================================================================
    -- Section 2: Raw negation function on RatBase (maps to RatSet)
    -- =========================================================================

    /-- The raw negation on representative pairs: (a, b) ↦ ratClass (negZ a) b.
        This maps a RatBase element to its negated equivalence class in RatSet. -/
    noncomputable def negQ_fn (p : U) : U :=
      ratClass (negZ (fst p)) (snd p)

    /-- negQ_fn maps RatBase into RatSet -/
    private theorem negQ_fn_closed (p : U) (hp : p ∈ (RatBase : U)) :
        negQ_fn p ∈ (RatSet : U) := by
      unfold RatBase at hp
      rw [CartesianProduct_is_specified] at hp
      obtain ⟨⟨a, b, hp_eq⟩, ha, hb⟩ := hp
      subst hp_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      unfold negQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      exact ratClass_mem_RatSet (negZ a) b
            (negZ_in_IntSet a ha) hb

    /-- negQ_fn respects RatEquivRel:
        if ⟨(a,b), (c,d)⟩ ∈ RatEquivRel then ratClass (negZ a) b = ratClass (negZ c) d -/
    private theorem negQ_fn_compat (x y : U)
        (hx : x ∈ (RatBase : U)) (hy : y ∈ (RatBase : U))
        (hR : ⟨x, y⟩ ∈ (RatEquivRel : U)) :
        negQ_fn x = negQ_fn y := by
      unfold RatBase at hx hy
      rw [CartesianProduct_is_specified] at hx hy
      obtain ⟨⟨a, b, hx_eq⟩, ha, hb⟩ := hx
      obtain ⟨⟨c, d, hy_eq⟩, hc, hd⟩ := hy
      subst hx_eq; subst hy_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      rw [mem_RatEquivRel] at hR
      obtain ⟨_, _, _, _, hR_eq⟩ := hR   -- mulZ a d = mulZ b c
      -- ha : a ∈ IntSet, hb : b ∈ NonZeroIntSet (denominators)
      -- hc : c ∈ IntSet, hd : d ∈ NonZeroIntSet
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      unfold negQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      -- Goal: ratClass (negZ a) b = ratClass (negZ c) d
      have key := ratClass_eq_iff (negZ a) b (negZ c) d
            (negZ_in_IntSet a ha) hb (negZ_in_IntSet c hc) hd
      rw [key]
      -- Goal: mulZ (negZ a) d = mulZ b (negZ c)
      calc mulZ (negZ a) d
          = negZ (mulZ a d) := mulZ_negZ_left a d ha hd_int
        _ = negZ (mulZ b c) := by rw [hR_eq]
        _ = mulZ b (negZ c) := (mulZ_negZ_right b c hb_int hc).symm

    -- =========================================================================
    -- Section 3: Definition of negQ via QuotientLift
    -- =========================================================================

    /-- The graph of rational negation, via QuotientLift -/
    noncomputable def negQ_graph : U :=
      QuotientLiftGraph negQ_fn RatEquivRel RatBase (RatSet : U)

    /-- Negation on Q -/
    noncomputable def negQ (x : U) : U := negQ_graph⦅x⦆

    -- =========================================================================
    -- Section 4: Computation rule
    -- =========================================================================

    /-- Computation rule: negQ (ratClass a b) = ratClass (negZ a) b -/
    theorem negQ_class (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U)) :
        negQ (ratClass a b) = ratClass (negZ a) b := by
      unfold negQ negQ_graph
      have h_unfold : ratClass a b = EqClass (⟨a, b⟩ : U) RatEquivRel RatBase := rfl
      rw [h_unfold]
      have key := QuotientLift_apply negQ_fn RatEquivRel RatBase (RatSet : U) ⟨a, b⟩
          RatEquivRel_is_equivalence
          negQ_fn_closed
          negQ_fn_compat
          ((mem_RatBase a b).mpr ⟨ha, hb⟩)
      rw [key]
      unfold negQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 5: Closure
    -- =========================================================================

    /-- Negation is closed on Q -/
    theorem negQ_in_RatSet (x : U) (hx : x ∈ (RatSet : U)) :
        negQ x ∈ (RatSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      rw [negQ_class a b ha hb]
      exact ratClass_mem_RatSet (negZ a) b (negZ_in_IntSet a ha) hb

    -- =========================================================================
    -- Section 6: Algebraic properties
    -- =========================================================================

    /-- Right additive inverse: addQ x (negQ x) = zeroQ -/
    theorem negQ_addQ_right (x : U) (hx : x ∈ (RatSet : U)) :
        addQ x (negQ x) = (zeroQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      rw [negQ_class a b ha hb,
          addQ_class a b (negZ a) b ha hb (negZ_in_IntSet a ha) hb]
      -- Goal: ratClass (addZ (mulZ a b) (mulZ b (negZ a))) (mulZ b b) = zeroQ
      have hbb_nz := mulZ_mem_NonZeroIntSet' b b hb hb
      -- Numerator vanishes: a·b + b·(−a) = a·b − b·a = a·b − a·b = 0
      have num_zero : addZ (mulZ a b) (mulZ b (negZ a)) = (zeroZ : U) := by
        rw [mulZ_negZ_right b a hb_int ha, mulZ_comm b a hb_int ha,
            addZ_negZ_right (mulZ a b) (mulZ_in_IntSet a b ha hb_int)]
      rw [num_zero]
      -- Goal: ratClass zeroZ (mulZ b b) = zeroQ
      unfold zeroQ
      rw [ratClass_eq_iff (zeroZ : U) (mulZ b b) (zeroZ : U) (oneZ : U)
            zeroZ_mem_IntSet hbb_nz zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet]
      -- Goal: mulZ zeroZ oneZ = mulZ (mulZ b b) zeroZ
      rw [mulZ_zero_left (oneZ : U) oneZ_mem_IntSet,
          mulZ_zero_right (mulZ b b) (mulZ_in_IntSet b b hb_int hb_int)]

    /-- Left additive inverse: addQ (negQ x) x = zeroQ -/
    theorem negQ_addQ_left (x : U) (hx : x ∈ (RatSet : U)) :
        addQ (negQ x) x = (zeroQ : U) := by
      rw [addQ_comm (negQ x) x (negQ_in_RatSet x hx) hx]
      exact negQ_addQ_right x hx

    /-- Negation is an involution: negQ (negQ x) = x -/
    theorem negQ_negQ (x : U) (hx : x ∈ (RatSet : U)) :
        negQ (negQ x) = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      rw [negQ_class a b ha hb,
          negQ_class (negZ a) b (negZ_in_IntSet a ha) hb,
          negZ_negZ a ha]

    /-- Negation of zero is zero: negQ zeroQ = zeroQ -/
    theorem negQ_zero : negQ (zeroQ : U) = (zeroQ : U) := by
      unfold zeroQ
      rw [negQ_class (zeroZ : U) (oneZ : U) zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet,
          negZ_zero]

  end Rat.Neg

end ZFC

export ZFC.Rat.Neg (
  negQ
  negQ_class
  negQ_in_RatSet
  negQ_addQ_right
  negQ_addQ_left
  negQ_negQ
  negQ_zero
)
