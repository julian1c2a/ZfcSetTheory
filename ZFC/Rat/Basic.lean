/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Basic Definitions for the Rational Numbers Q

  This module establishes the fundamental objects of Q: the equivalence class
  constructor `ratClass`, the constants `zeroQ` and `oneQ`, and the basic
  membership and equality theorems.

  ## Main Definitions

  * `ratClass a b` -- the equivalence class [(a,b)] in RatSet, representing a/b
  * `zeroQ`        -- the rational zero:  [(0Z, 1Z)]
  * `oneQ`         -- the rational one:   [(1Z, 1Z)]

  ## Main Theorems

  * `oneZ_mem_NonZeroIntSet`  -- 1Z in NonZeroIntSet
  * `ratClass_mem_RatSet`     -- [(a,b)] in RatSet when a in IntSet, b in NonZeroIntSet
  * `zeroQ_mem_RatSet`        -- 0Q in RatSet
  * `oneQ_mem_RatSet`         -- 1Q in RatSet
  * `ratClass_eq_iff`         -- [(a,b)] = [(c,d)] iff mulZ a d = mulZ b c
  * `ratClass_ne_iff`         -- [(a,b)] != [(c,d)] iff mulZ a d != mulZ b c
  * `zeroQ_ne_oneQ`           -- 0Q != 1Q
  * `ratClass_eq_zeroQ_iff`   -- [(a,b)] = 0Q iff a = zeroZ
  * `ratClass_ne_zeroQ_iff`   -- [(a,b)] != 0Q iff a != zeroZ
  * `mem_RatSet_is_ratClass`  -- every element of RatSet is a ratClass

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Equiv

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

  universe u
  variable {U : Type u}

  namespace Rat.Basic

    -- =========================================================================
    -- Section 1: Core Definitions
    -- =========================================================================

    /-- The equivalence class [(a,b)] in RatSet, representing the fraction a/b.
        Requires a in IntSet and b in NonZeroIntSet (b != zeroZ). -/
    noncomputable def ratClass (a b : U) : U :=
      EqClass (⟨a, b⟩ : U) RatEquivRel RatBase

    /-- The rational zero: 0Q := [(0Z, 1Z)] -/
    noncomputable def zeroQ : U := ratClass (zeroZ : U) (oneZ : U)

    /-- The rational one: 1Q := [(1Z, 1Z)] -/
    noncomputable def oneQ : U := ratClass (oneZ : U) (oneZ : U)

    -- =========================================================================
    -- Section 2: Membership in NonZeroIntSet and RatSet
    -- =========================================================================

    /-- oneZ is in NonZeroIntSet: 1Z != zeroZ -/
    theorem oneZ_mem_NonZeroIntSet : (oneZ : U) ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      refine ⟨oneZ_mem_IntSet, ?_⟩
      -- Prove oneZ != zeroZ  using intClass_eq_iff:
      -- oneZ = intClass (sigma empty) empty, zeroZ = intClass empty empty
      -- they're equal iff add (sigma empty) empty = add empty empty
      -- i.e., sigma empty = empty, which is false by succ_nonempty
      unfold oneZ zeroZ
      intro h
      rw [intClass_eq_iff (σ (∅ : U)) ∅ ∅ ∅
            (succ_in_Omega ∅ zero_in_Omega) zero_in_Omega zero_in_Omega zero_in_Omega] at h
      rw [add_zero (σ (∅ : U)) (succ_in_Omega ∅ zero_in_Omega),
          add_zero ∅ zero_in_Omega] at h
      exact succ_nonempty ∅ h

    /-- Every equivalence class [(a,b)] with a in IntSet and b in NonZeroIntSet
        belongs to RatSet -/
    theorem ratClass_mem_RatSet (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U)) :
        ratClass a b ∈ (RatSet : U) := by
      unfold ratClass RatSet
      exact EqClass_mem_QuotientSet RatEquivRel RatBase ⟨a, b⟩
        ((mem_RatBase a b).mpr ⟨ha, hb⟩)

    /-- 0Q in RatSet -/
    theorem zeroQ_mem_RatSet : (zeroQ : U) ∈ (RatSet : U) := by
      unfold zeroQ
      exact ratClass_mem_RatSet zeroZ oneZ zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet

    /-- 1Q in RatSet -/
    theorem oneQ_mem_RatSet : (oneQ : U) ∈ (RatSet : U) := by
      unfold oneQ
      exact ratClass_mem_RatSet oneZ oneZ oneZ_mem_IntSet oneZ_mem_NonZeroIntSet

    -- =========================================================================
    -- Section 3: Equality of rational classes
    -- =========================================================================

    /-- Two rational classes are equal iff the cross-products agree:
        [(a,b)] = [(c,d)] iff a*d = b*c -/
    theorem ratClass_eq_iff (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        ratClass a b = ratClass c d ↔ mulZ a d = mulZ b c := by
      unfold ratClass
      have key := EqClass_eq_iff RatEquivRel RatBase ⟨a, b⟩ ⟨c, d⟩
        RatEquivRel_is_equivalence
        ((mem_RatBase a b).mpr ⟨ha, hb⟩)
        ((mem_RatBase c d).mpr ⟨hc, hd⟩)
      rw [key, mem_RatEquivRel]
      constructor
      · intro h; exact h.2.2.2.2
      · intro h; exact ⟨ha, hb, hc, hd, h⟩

    /-- Two rational classes are distinct iff the cross-products differ -/
    theorem ratClass_ne_iff (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        ratClass a b ≠ ratClass c d ↔ mulZ a d ≠ mulZ b c := by
      rw [ne_eq, ratClass_eq_iff a b c d ha hb hc hd]

    -- =========================================================================
    -- Section 4: Zero and One
    -- =========================================================================

    /-- 0Q != 1Q -/
    theorem zeroQ_ne_oneQ : (zeroQ : U) ≠ (oneQ : U) := by
      unfold zeroQ oneQ
      rw [ratClass_ne_iff zeroZ oneZ oneZ oneZ
            zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet
            oneZ_mem_IntSet oneZ_mem_NonZeroIntSet]
      -- Goal: mulZ zeroZ oneZ != mulZ oneZ oneZ
      rw [mulZ_zero_left oneZ oneZ_mem_IntSet,
          mulZ_one_right oneZ oneZ_mem_IntSet]
      -- Goal: zeroZ != oneZ, i.e., intClass empty empty != intClass (sigma empty) empty
      intro h
      unfold zeroZ oneZ at h
      rw [intClass_eq_iff ∅ ∅ (σ (∅ : U)) ∅
            zero_in_Omega zero_in_Omega (succ_in_Omega ∅ zero_in_Omega) zero_in_Omega] at h
      rw [add_zero ∅ zero_in_Omega,
          zero_add (σ (∅ : U)) (succ_in_Omega ∅ zero_in_Omega)] at h
      exact succ_nonempty ∅ h.symm

    /-- [(a,b)] = zeroQ iff a = zeroZ -/
    theorem ratClass_eq_zeroQ_iff (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U)) :
        ratClass a b = (zeroQ : U) ↔ a = (zeroZ : U) := by
      unfold zeroQ
      rw [ratClass_eq_iff a b zeroZ oneZ ha hb zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet]
      -- Goal: mulZ a oneZ = mulZ b zeroZ iff a = zeroZ
      rw [mulZ_one_right a ha,
          mulZ_zero_right b (NonZeroIntSet_mem_IntSet b hb)]

    /-- [(a,b)] != zeroQ iff a != zeroZ -/
    theorem ratClass_ne_zeroQ_iff (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U)) :
        ratClass a b ≠ (zeroQ : U) ↔ a ≠ (zeroZ : U) := by
      rw [ne_eq, ratClass_eq_zeroQ_iff a b ha hb]

    /-- Every element of RatSet is ratClass a b for some a in IntSet, b in NonZeroIntSet -/
    theorem mem_RatSet_is_ratClass (x : U) (hx : x ∈ (RatSet : U)) :
        ∃ a b : U, a ∈ (IntSet : U) ∧ b ∈ (NonZeroIntSet : U) ∧ x = ratClass a b := by
      unfold RatSet at hx
      rw [mem_QuotientSet RatBase RatEquivRel x] at hx
      obtain ⟨p, hp_mem, hx_eq⟩ := hx
      unfold RatBase at hp_mem
      rw [CartesianProduct_is_specified] at hp_mem
      obtain ⟨hp_pair, ha, hb⟩ := hp_mem
      obtain ⟨a, b, hp_def⟩ := hp_pair
      subst hp_def
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at ha hb
      exact ⟨a, b, ha, hb, hx_eq⟩

  end Rat.Basic

end ZFC

export ZFC.Rat.Basic (
  ratClass
  zeroQ
  oneQ
  oneZ_mem_NonZeroIntSet
  ratClass_mem_RatSet
  zeroQ_mem_RatSet
  oneQ_mem_RatSet
  ratClass_eq_iff
  ratClass_ne_iff
  zeroQ_ne_oneQ
  ratClass_eq_zeroQ_iff
  ratClass_ne_zeroQ_iff
  mem_RatSet_is_ratClass
)
