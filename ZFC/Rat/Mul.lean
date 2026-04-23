/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Multiplication and Inverse

  This module defines multiplication on Q = QuotientSet RatBase RatEquivRel
  using the QuotientLift₂ infrastructure, and the multiplicative inverse
  via a conditional QuotientLift. Division is derived as mulQ x (invQ y).

  ## Main Definitions

  * `mulQ`  — multiplication on Q: mulQ x y, defined via QuotientLift₂
  * `invQ`  — multiplicative inverse: invQ x (= zeroQ when x = zeroQ)
  * `divQ`  — division: divQ x y = mulQ x (invQ y)

  ## Main Theorems

  * `mulQ_class`      — computation rule: mulQ [(a,b)] [(c,d)] = [(a·c, b·d)]
  * `mulQ_in_RatSet`  — closure: x, y ∈ Q → mulQ x y ∈ Q
  * `mulQ_comm`       — commutativity
  * `mulQ_assoc`      — associativity
  * `mulQ_one_left`   — left identity:  mulQ 1Q x = x
  * `mulQ_one_right`  — right identity: mulQ x 1Q = x
  * `mulQ_zero_left`  — left absorbing:  mulQ 0Q x = 0Q
  * `mulQ_zero_right` — right absorbing: mulQ x 0Q = 0Q
  * `invQ_class`      — computation rule: invQ [(a,b)] = [(b,a)] when a ≠ 0Z
  * `invQ_in_RatSet`  — closure: x ∈ Q → invQ x ∈ Q
  * `invQ_ne_zeroQ`   — x ≠ 0Q → invQ x ≠ 0Q
  * `mulQ_invQ_right` — right inverse: x ≠ 0Q → mulQ x (invQ x) = 1Q
  * `mulQ_invQ_left`  — left inverse:  x ≠ 0Q → mulQ (invQ x) x = 1Q
  * `divQ_class`      — computation rule: divQ [(a,b)] [(c,d)] = [(a·d, b·c)]

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Neg

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

  universe u
  variable {U : Type u}

  namespace Rat.Mul

    -- =========================================================================
    -- Section 1: Helper
    -- =========================================================================

    /-- Product of two nonzero integer denominators is nonzero -/
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
    -- Section 2: Raw operation on RatBase representatives
    -- =========================================================================

    /-- The raw operation on ordered pairs: (a,b) * (c,d) := (a·c, b·d) -/
    noncomputable def mulQ_op (p q : U) : U :=
      ⟨mulZ (fst p) (fst q), mulZ (snd p) (snd q)⟩

    /-- mulQ_op is closed on RatBase -/
    private theorem mulQ_op_closed (p q : U)
        (hp : p ∈ (RatBase : U)) (hq : q ∈ (RatBase : U)) :
        mulQ_op p q ∈ (RatBase : U) := by
      unfold RatBase at hp hq
      rw [CartesianProduct_is_specified] at hp hq
      obtain ⟨⟨a, b, hp_eq⟩, ha, hb⟩ := hp
      obtain ⟨⟨c, d, hq_eq⟩, hc, hd⟩ := hq
      subst hp_eq; subst hq_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      unfold mulQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_RatBase]
      exact ⟨mulZ_in_IntSet a c ha hc,
             mulZ_mem_NonZeroIntSet' b d hb hd⟩

    /-- mulQ_op respects RatEquivRel (compatibility for QuotientLift₂) -/
    private theorem mulQ_op_compat (p₁ p₂ q₁ q₂ : U)
        (hp₁ : p₁ ∈ (RatBase : U)) (hp₂ : p₂ ∈ (RatBase : U))
        (hq₁ : q₁ ∈ (RatBase : U)) (hq₂ : q₂ ∈ (RatBase : U))
        (hR₁ : ⟨p₁, p₂⟩ ∈ (RatEquivRel : U))
        (hR₂ : ⟨q₁, q₂⟩ ∈ (RatEquivRel : U)) :
        ⟨mulQ_op p₁ q₁, mulQ_op p₂ q₂⟩ ∈ (RatEquivRel : U) := by
      unfold RatBase at hp₁ hp₂ hq₁ hq₂
      rw [CartesianProduct_is_specified] at hp₁ hp₂ hq₁ hq₂
      obtain ⟨⟨a, b, hp₁_eq⟩, ha, hb⟩ := hp₁
      obtain ⟨⟨a', b', hp₂_eq⟩, ha', hb'⟩ := hp₂
      obtain ⟨⟨c, d, hq₁_eq⟩, hc, hd⟩ := hq₁
      obtain ⟨⟨c', d', hq₂_eq⟩, hc', hd'⟩ := hq₂
      subst hp₁_eq; subst hp₂_eq; subst hq₁_eq; subst hq₂_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      rw [mem_RatEquivRel] at hR₁ hR₂
      obtain ⟨_, _, _, _, hR₁_eq⟩ := hR₁   -- mulZ a b' = mulZ b a'
      obtain ⟨_, _, _, _, hR₂_eq⟩ := hR₂   -- mulZ c d' = mulZ d c'
      unfold mulQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_RatEquivRel]
      have hb_int  := NonZeroIntSet_mem_IntSet b hb
      have hb'_int := NonZeroIntSet_mem_IntSet b' hb'
      have hd_int  := NonZeroIntSet_mem_IntSet d hd
      have hd'_int := NonZeroIntSet_mem_IntSet d' hd'
      refine ⟨mulZ_in_IntSet a c ha hc,
              mulZ_mem_NonZeroIntSet' b d hb hd,
              mulZ_in_IntSet a' c' ha' hc',
              mulZ_mem_NonZeroIntSet' b' d' hb' hd',
              ?_⟩
      -- Goal: mulZ (mulZ a c) (mulZ b' d') = mulZ (mulZ b d) (mulZ a' c')
      calc mulZ (mulZ a c) (mulZ b' d')
          = mulZ (mulZ a b') (mulZ c d') := by
              rw [mulZ_assoc a c (mulZ b' d') ha hc (mulZ_in_IntSet b' d' hb'_int hd'_int),
                  ← mulZ_assoc c b' d' hc hb'_int hd'_int,
                  mulZ_comm c b' hc hb'_int,
                  mulZ_assoc b' c d' hb'_int hc hd'_int,
                  ← mulZ_assoc a b' (mulZ c d') ha hb'_int (mulZ_in_IntSet c d' hc hd'_int)]
        _ = mulZ (mulZ b a') (mulZ d c') := by rw [hR₁_eq, hR₂_eq]
        _ = mulZ (mulZ b d) (mulZ a' c') := by
              rw [mulZ_assoc b a' (mulZ d c') hb_int ha' (mulZ_in_IntSet d c' hd_int hc'),
                  ← mulZ_assoc a' d c' ha' hd_int hc',
                  mulZ_comm a' d ha' hd_int,
                  mulZ_assoc d a' c' hd_int ha' hc',
                  ← mulZ_assoc b d (mulZ a' c') hb_int hd_int (mulZ_in_IntSet a' c' ha' hc')]

    -- =========================================================================
    -- Section 3: Definition of mulQ via QuotientLift₂
    -- =========================================================================

    /-- The graph of rational multiplication, constructed via QuotientLift₂ -/
    noncomputable def mulQ_graph : U :=
      QuotientLift₂Graph mulQ_op RatEquivRel RatBase

    /-- Multiplication on Q -/
    noncomputable def mulQ (x y : U) : U := mulQ_graph⦅⟨x, y⟩⦆

    -- =========================================================================
    -- Section 4: Computation rule
    -- =========================================================================

    /-- Computation rule: mulQ [(a,b)] [(c,d)] = [(a·c, b·d)] -/
    theorem mulQ_class (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulQ (ratClass a b) (ratClass c d) =
          ratClass (mulZ a c) (mulZ b d) := by
      unfold mulQ mulQ_graph ratClass
      have key := QuotientLift₂_apply mulQ_op RatEquivRel RatBase ⟨a, b⟩ ⟨c, d⟩
          RatEquivRel_is_equivalence mulQ_op_closed mulQ_op_compat
          ((mem_RatBase a b).mpr ⟨ha, hb⟩)
          ((mem_RatBase c d).mpr ⟨hc, hd⟩)
      rw [key]
      unfold mulQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 5: Closure
    -- =========================================================================

    /-- Multiplication is closed on Q -/
    theorem mulQ_in_RatSet (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ x y ∈ (RatSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      rw [mulQ_class a b c d ha hb hc hd]
      exact ratClass_mem_RatSet (mulZ a c) (mulZ b d)
        (mulZ_in_IntSet a c ha hc)
        (mulZ_mem_NonZeroIntSet' b d hb hd)

    -- =========================================================================
    -- Section 6: Algebraic properties of mulQ
    -- =========================================================================

    /-- Commutativity: mulQ x y = mulQ y x -/
    theorem mulQ_comm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        mulQ x y = mulQ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      rw [mulQ_class a b c d ha hb hc hd,
          mulQ_class c d a b hc hd ha hb,
          mulZ_comm a c ha hc,
          mulZ_comm b d hb_int hd_int]

    /-- Associativity: mulQ (mulQ x y) z = mulQ x (mulQ y z) -/
    theorem mulQ_assoc (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        mulQ (mulQ x y) z = mulQ x (mulQ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := mem_RatSet_is_ratClass z hz
      subst hx_eq; subst hy_eq; subst hz_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      have hf_int := NonZeroIntSet_mem_IntSet f hf
      have hbd := mulZ_mem_NonZeroIntSet' b d hb hd
      have hdf := mulZ_mem_NonZeroIntSet' d f hd hf
      rw [mulQ_class a b c d ha hb hc hd,
          mulQ_class (mulZ a c) (mulZ b d) e f
            (mulZ_in_IntSet a c ha hc) hbd he hf,
          mulQ_class c d e f hc hd he hf,
          mulQ_class a b (mulZ c e) (mulZ d f)
            ha hb (mulZ_in_IntSet c e hc he) hdf,
          mulZ_assoc a c e ha hc he,
          mulZ_assoc b d f hb_int hd_int hf_int]

    /-- Left identity: mulQ 1Q x = x -/
    theorem mulQ_one_left (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ (oneQ : U) x = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      unfold oneQ
      rw [mulQ_class oneZ oneZ a b oneZ_mem_IntSet oneZ_mem_NonZeroIntSet ha hb,
          mulZ_one_left a ha,
          mulZ_one_left b hb_int]

    /-- Right identity: mulQ x 1Q = x -/
    theorem mulQ_one_right (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ x (oneQ : U) = x := by
      rw [mulQ_comm x (oneQ : U) hx oneQ_mem_RatSet]
      exact mulQ_one_left x hx

    /-- Left absorbing: mulQ 0Q x = 0Q -/
    theorem mulQ_zero_left (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ (zeroQ : U) x = (zeroQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      unfold zeroQ
      rw [mulQ_class zeroZ oneZ a b zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet ha hb,
          mulZ_zero_left a ha,
          mulZ_one_left b hb_int,
          ratClass_eq_iff zeroZ b zeroZ oneZ
            zeroZ_mem_IntSet hb zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet,
          mulZ_zero_left (oneZ : U) oneZ_mem_IntSet,
          mulZ_zero_right b hb_int]

    /-- Right absorbing: mulQ x 0Q = 0Q -/
    theorem mulQ_zero_right (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ x (zeroQ : U) = (zeroQ : U) := by
      rw [mulQ_comm x (zeroQ : U) hx zeroQ_mem_RatSet]
      exact mulQ_zero_left x hx

    -- =========================================================================
    -- Section 7: Multiplicative inverse (invQ)
    -- =========================================================================

    /-- The raw inverse on ordered pairs: (a,b) ↦ (b,a) when a ≠ 0Z, else 0Q.
        This defines a total function on all of RatBase that maps into RatSet. -/
    noncomputable def invQ_fn (p : U) : U :=
      if fst p ∈ (NonZeroIntSet : U) then ratClass (snd p) (fst p)
      else (zeroQ : U)

    /-- invQ_fn maps RatBase into RatSet -/
    private theorem invQ_fn_closed (p : U) (hp : p ∈ (RatBase : U)) :
        invQ_fn p ∈ (RatSet : U) := by
      unfold RatBase at hp
      rw [CartesianProduct_is_specified] at hp
      obtain ⟨⟨a, b, hp_eq⟩, ha, hb⟩ := hp
      subst hp_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      unfold invQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      by_cases ha_nz : a ∈ (NonZeroIntSet : U)
      · rw [if_pos ha_nz]
        exact ratClass_mem_RatSet b a (NonZeroIntSet_mem_IntSet b hb) ha_nz
      · rw [if_neg ha_nz]
        exact zeroQ_mem_RatSet

    /-- invQ_fn respects RatEquivRel -/
    private theorem invQ_fn_compat (x y : U)
        (hx : x ∈ (RatBase : U)) (hy : y ∈ (RatBase : U))
        (hR : ⟨x, y⟩ ∈ (RatEquivRel : U)) :
        invQ_fn x = invQ_fn y := by
      unfold RatBase at hx hy
      rw [CartesianProduct_is_specified] at hx hy
      obtain ⟨⟨a, b, hx_eq⟩, ha, hb⟩ := hx
      obtain ⟨⟨c, d, hy_eq⟩, hc, hd⟩ := hy
      subst hx_eq; subst hy_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      rw [mem_RatEquivRel] at hR
      obtain ⟨_, _, _, _, hR_eq⟩ := hR   -- mulZ a d = mulZ b c
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      unfold invQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      -- Goal: (if a ∈ NonZeroIntSet then ratClass b a else zeroQ) =
      --       (if c ∈ NonZeroIntSet then ratClass d c else zeroQ)
      by_cases ha_nz : a ∈ (NonZeroIntSet : U)
      · -- a ∈ NonZeroIntSet: reduce LHS first, then deduce c ∈ NonZeroIntSet
        rw [if_pos ha_nz]
        have ha_ne : a ≠ (zeroZ : U) := NonZeroIntSet_ne_zero a ha_nz
        have hc_ne : c ≠ (zeroZ : U) := by
          intro hc_eq
          subst hc_eq
          -- hR_eq : mulZ a d = mulZ b zeroZ = zeroZ, but mulZ a d ≠ zeroZ
          rw [mulZ_zero_right b hb_int] at hR_eq
          exact (mulZ_nonzero_of_nonzero a d ha hd_int ha_ne
                   (NonZeroIntSet_ne_zero d hd)) hR_eq
        have hc_nz : c ∈ (NonZeroIntSet : U) := (mem_NonZeroIntSet c).mpr ⟨hc, hc_ne⟩
        rw [if_pos hc_nz,
            ratClass_eq_iff b a d c
              (NonZeroIntSet_mem_IntSet b hb) ha_nz
              (NonZeroIntSet_mem_IntSet d hd) hc_nz]
        exact hR_eq.symm
      · -- a ∉ NonZeroIntSet: reduce LHS, then deduce c ∉ NonZeroIntSet
        rw [if_neg ha_nz]
        have ha_eq : a = (zeroZ : U) :=
          Classical.byContradiction fun ha_ne =>
            ha_nz ((mem_NonZeroIntSet a).mpr ⟨ha, ha_ne⟩)
        have hc_eq : c = (zeroZ : U) := by
          have mulbc_zero : mulZ b c = (zeroZ : U) := by
            have had_zero : mulZ a d = (zeroZ : U) := by
              rw [ha_eq]; exact mulZ_zero_left d hd_int
            exact hR_eq.symm.trans had_zero
          rcases (mulZ_eq_zero_iff b c hb_int hc).mp mulbc_zero with h | h
          · exact absurd h (NonZeroIntSet_ne_zero b hb)
          · exact h
        have hc_nz_false : c ∉ (NonZeroIntSet : U) :=
          fun hc_mem => (NonZeroIntSet_ne_zero c hc_mem) hc_eq
        rw [if_neg hc_nz_false]

    /-- The graph of rational inverse, via QuotientLift -/
    noncomputable def invQ_graph : U :=
      QuotientLiftGraph invQ_fn RatEquivRel RatBase (RatSet : U)

    /-- Multiplicative inverse on Q -/
    noncomputable def invQ (x : U) : U := invQ_graph⦅x⦆

    -- =========================================================================
    -- Section 8: Computation rule for invQ
    -- =========================================================================

    /-- Computation rule: invQ (ratClass a b) = ratClass b a, for a ∈ NonZeroIntSet -/
    theorem invQ_class (a b : U)
        (ha : a ∈ (NonZeroIntSet : U)) (hb : b ∈ (NonZeroIntSet : U)) :
        invQ (ratClass a b) = ratClass b a := by
      unfold invQ invQ_graph
      have h_unfold : ratClass a b = EqClass (⟨a, b⟩ : U) RatEquivRel RatBase := rfl
      rw [h_unfold]
      have key := QuotientLift_apply invQ_fn RatEquivRel RatBase (RatSet : U) ⟨a, b⟩
          RatEquivRel_is_equivalence
          invQ_fn_closed
          invQ_fn_compat
          ((mem_RatBase a b).mpr ⟨NonZeroIntSet_mem_IntSet a ha, hb⟩)
      rw [key]
      unfold invQ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [if_pos ha]

    -- =========================================================================
    -- Section 9: Closure and non-zero properties of invQ
    -- =========================================================================

    /-- Inverse is closed on Q -/
    theorem invQ_in_RatSet (x : U) (hx : x ∈ (RatSet : U)) :
        invQ x ∈ (RatSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      unfold invQ invQ_graph
      have h_unfold : ratClass a b = EqClass (⟨a, b⟩ : U) RatEquivRel RatBase := rfl
      rw [h_unfold]
      have key := QuotientLift_apply invQ_fn RatEquivRel RatBase (RatSet : U) ⟨a, b⟩
          RatEquivRel_is_equivalence
          invQ_fn_closed
          invQ_fn_compat
          ((mem_RatBase a b).mpr ⟨ha, hb⟩)
      rw [key]
      exact invQ_fn_closed ⟨a, b⟩ ((mem_RatBase a b).mpr ⟨ha, hb⟩)

    /-- Inverse of a non-zero rational is non-zero -/
    theorem invQ_ne_zeroQ (x : U) (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        invQ x ≠ (zeroQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have ha_ne : a ≠ (zeroZ : U) := (ratClass_ne_zeroQ_iff a b ha hb).mp hx_ne
      have ha_nz : a ∈ (NonZeroIntSet : U) := (mem_NonZeroIntSet a).mpr ⟨ha, ha_ne⟩
      rw [invQ_class a b ha_nz hb,
          ratClass_ne_zeroQ_iff b a (NonZeroIntSet_mem_IntSet b hb) ha_nz]
      exact NonZeroIntSet_ne_zero b hb

    -- =========================================================================
    -- Section 10: Division
    -- =========================================================================

    /-- Division: divQ x y = mulQ x (invQ y) -/
    noncomputable def divQ (x y : U) : U := mulQ x (invQ y)

    /-- Computation rule: divQ [(a,b)] [(c,d)] = [(a·d, b·c)], for c ∈ NonZeroIntSet -/
    theorem divQ_class (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (hc : c ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        divQ (ratClass a b) (ratClass c d) = ratClass (mulZ a d) (mulZ b c) := by
      unfold divQ
      rw [invQ_class c d hc hd,
          mulQ_class a b d c ha hb (NonZeroIntSet_mem_IntSet d hd) hc]

    /-- Division is closed on Q when the divisor is non-zero -/
    theorem divQ_in_RatSet (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        divQ x y ∈ (RatSet : U) := by
      unfold divQ
      exact mulQ_in_RatSet x (invQ y) hx (invQ_in_RatSet y hy)

    -- =========================================================================
    -- Section 11: Field inverse laws
    -- =========================================================================

    /-- Right multiplicative inverse: x ≠ 0Q → mulQ x (invQ x) = 1Q -/
    theorem mulQ_invQ_right (x : U) (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        mulQ x (invQ x) = (oneQ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have ha_ne : a ≠ (zeroZ : U) := (ratClass_ne_zeroQ_iff a b ha hb).mp hx_ne
      have ha_nz : a ∈ (NonZeroIntSet : U) := (mem_NonZeroIntSet a).mpr ⟨ha, ha_ne⟩
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      rw [invQ_class a b ha_nz hb,
          mulQ_class a b b a ha hb hb_int ha_nz]
      -- Goal: ratClass (mulZ a b) (mulZ b a) = oneQ
      unfold oneQ
      rw [ratClass_eq_iff (mulZ a b) (mulZ b a) oneZ oneZ
            (mulZ_in_IntSet a b ha hb_int)
            (mulZ_mem_NonZeroIntSet' b a hb ha_nz)
            oneZ_mem_IntSet oneZ_mem_NonZeroIntSet,
          mulZ_one_right (mulZ a b) (mulZ_in_IntSet a b ha hb_int),
          mulZ_one_right (mulZ b a) (mulZ_in_IntSet b a hb_int ha)]
      exact mulZ_comm a b ha hb_int

    /-- Left multiplicative inverse: x ≠ 0Q → mulQ (invQ x) x = 1Q -/
    theorem mulQ_invQ_left (x : U) (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        mulQ (invQ x) x = (oneQ : U) := by
      rw [mulQ_comm (invQ x) x (invQ_in_RatSet x hx) hx]
      exact mulQ_invQ_right x hx hx_ne

  end Rat.Mul

end ZFC

export ZFC.Rat.Mul (
  mulQ
  mulQ_class
  mulQ_in_RatSet
  mulQ_comm
  mulQ_assoc
  mulQ_one_left
  mulQ_one_right
  mulQ_zero_left
  mulQ_zero_right
  invQ
  invQ_class
  invQ_in_RatSet
  invQ_ne_zeroQ
  divQ
  divQ_class
  divQ_in_RatSet
  mulQ_invQ_right
  mulQ_invQ_left
)
