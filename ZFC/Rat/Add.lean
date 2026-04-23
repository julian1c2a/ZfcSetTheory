/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Addition

  This module defines addition on Q = QuotientSet RatBase RatEquivRel
  using the QuotientLift₂ infrastructure. The operation lifts the
  pairwise formula (a,b) + (c,d) := (a·d + b·c, b·d) from RatBase to Q.

  ## Main Definitions

  * `addQ` — addition on Q: addQ x y, defined via QuotientLift₂

  ## Main Theorems

  * `mulZ_nonzero_of_nonzero` — if a ≠ 0Z and b ≠ 0Z then mulZ a b ≠ 0Z
  * `addQ_class`      — computation rule: addQ [(a,b)] [(c,d)] = [(a·d+b·c, b·d)]
  * `addQ_in_RatSet`  — closure: x, y ∈ Q → addQ x y ∈ Q
  * `addQ_comm`       — commutativity
  * `addQ_assoc`      — associativity
  * `addQ_zero_left`  — left identity:  addQ 0Q x = x
  * `addQ_zero_right` — right identity: addQ x 0Q = x

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Basic

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

  universe u
  variable {U : Type u}

  namespace Rat.Add

    -- =========================================================================
    -- Section 1: Preliminary lemma
    -- =========================================================================

    /-- Product of two non-zero integers is non-zero (no zero divisors) -/
    theorem mulZ_nonzero_of_nonzero (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
        (ha_ne : a ≠ zeroZ) (hb_ne : b ≠ zeroZ) : mulZ a b ≠ zeroZ := by
      intro h
      rcases (mulZ_eq_zero_iff a b ha hb).mp h with h1 | h2
      · exact ha_ne h1
      · exact hb_ne h2

    -- =========================================================================
    -- Section 2: Raw operation on RatBase representatives
    -- =========================================================================

    /-- The raw operation on ordered pairs: (a,b) + (c,d) := (a·d + b·c, b·d) -/
    noncomputable def addQ_op (p q : U) : U :=
      ⟨addZ (mulZ (fst p) (snd q)) (mulZ (snd p) (fst q)), mulZ (snd p) (snd q)⟩

    -- Helper used in multiple places
    private theorem mulZ_mem_NonZeroIntSet (b d : U)
        (hb : b ∈ (NonZeroIntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        mulZ b d ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]
      exact ⟨mulZ_in_IntSet b d (NonZeroIntSet_mem_IntSet b hb) (NonZeroIntSet_mem_IntSet d hd),
             mulZ_nonzero_of_nonzero b d
               (NonZeroIntSet_mem_IntSet b hb) (NonZeroIntSet_mem_IntSet d hd)
               (NonZeroIntSet_ne_zero b hb) (NonZeroIntSet_ne_zero d hd)⟩

    /-- addQ_op is closed on RatBase -/
    private theorem addQ_op_closed (p q : U)
        (hp : p ∈ (RatBase : U)) (hq : q ∈ (RatBase : U)) :
        addQ_op p q ∈ (RatBase : U) := by
      unfold RatBase at hp hq
      rw [CartesianProduct_is_specified] at hp hq
      obtain ⟨⟨a, b, hp_eq⟩, ha, hb⟩ := hp
      obtain ⟨⟨c, d, hq_eq⟩, hc, hd⟩ := hq
      subst hp_eq; subst hq_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      unfold addQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_RatBase]
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      exact ⟨addZ_in_IntSet _ _ (mulZ_in_IntSet a d ha hd_int) (mulZ_in_IntSet b c hb_int hc),
             mulZ_mem_NonZeroIntSet b d hb hd⟩

    /-- addQ_op respects RatEquivRel (compatibility for QuotientLift₂) -/
    private theorem addQ_op_compat (p₁ p₂ q₁ q₂ : U)
        (hp₁ : p₁ ∈ (RatBase : U)) (hp₂ : p₂ ∈ (RatBase : U))
        (hq₁ : q₁ ∈ (RatBase : U)) (hq₂ : q₂ ∈ (RatBase : U))
        (hR₁ : ⟨p₁, p₂⟩ ∈ (RatEquivRel : U))
        (hR₂ : ⟨q₁, q₂⟩ ∈ (RatEquivRel : U)) :
        ⟨addQ_op p₁ q₁, addQ_op p₂ q₂⟩ ∈ (RatEquivRel : U) := by
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
      unfold addQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_RatEquivRel]
      have ha_int  := ha;  have hb_int  := NonZeroIntSet_mem_IntSet b hb
      have ha'_int := ha'; have hb'_int := NonZeroIntSet_mem_IntSet b' hb'
      have hc_int  := hc;  have hd_int  := NonZeroIntSet_mem_IntSet d hd
      have hc'_int := hc'; have hd'_int := NonZeroIntSet_mem_IntSet d' hd'
      refine ⟨addZ_in_IntSet _ _ (mulZ_in_IntSet a d ha_int hd_int)
                                  (mulZ_in_IntSet b c hb_int hc_int),
              mulZ_mem_NonZeroIntSet b d hb hd,
              addZ_in_IntSet _ _ (mulZ_in_IntSet a' d' ha'_int hd'_int)
                                  (mulZ_in_IntSet b' c' hb'_int hc'_int),
              mulZ_mem_NonZeroIntSet b' d' hb' hd', ?_⟩
      -- Goal: mulZ (addZ (mulZ a d) (mulZ b c)) (mulZ b' d')
      --     = mulZ (mulZ b d) (addZ (mulZ a' d') (mulZ b' c'))
      rw [mulZ_addZ_distrib_right (mulZ a d) (mulZ b c) (mulZ b' d')
            (mulZ_in_IntSet a d ha_int hd_int) (mulZ_in_IntSet b c hb_int hc_int)
            (mulZ_in_IntSet b' d' hb'_int hd'_int)]
      rw [mulZ_addZ_distrib_left (mulZ b d) (mulZ a' d') (mulZ b' c')
            (mulZ_in_IntSet b d hb_int hd_int)
            (mulZ_in_IntSet a' d' ha'_int hd'_int)
            (mulZ_in_IntSet b' c' hb'_int hc'_int)]
      congr 1
      · -- (a·d)·(b'·d') = (b·d)·(a'·d')
        -- = (a·b')·(d·d') = (b·a')·(d·d')
        calc mulZ (mulZ a d) (mulZ b' d')
            = mulZ (mulZ a b') (mulZ d d') := by
                rw [mulZ_assoc a d (mulZ b' d') ha_int hd_int (mulZ_in_IntSet b' d' hb'_int hd'_int),
                    ← mulZ_assoc d b' d' hd_int hb'_int hd'_int,
                    mulZ_comm d b' hd_int hb'_int,
                    mulZ_assoc b' d d' hb'_int hd_int hd'_int,
                    ← mulZ_assoc a b' (mulZ d d') ha_int hb'_int (mulZ_in_IntSet d d' hd_int hd'_int)]
          _ = mulZ (mulZ b a') (mulZ d d') := by rw [hR₁_eq]
          _ = mulZ (mulZ b d) (mulZ a' d') := by
                rw [mulZ_assoc b a' (mulZ d d') hb_int ha'_int (mulZ_in_IntSet d d' hd_int hd'_int),
                    ← mulZ_assoc a' d d' ha'_int hd_int hd'_int,
                    mulZ_comm a' d ha'_int hd_int,
                    mulZ_assoc d a' d' hd_int ha'_int hd'_int,
                    ← mulZ_assoc b d (mulZ a' d') hb_int hd_int (mulZ_in_IntSet a' d' ha'_int hd'_int)]
      · -- (b·c)·(b'·d') = (b·d)·(b'·c')
        -- = (b·b')·(c·d') = (b·b')·(d·c')
        calc mulZ (mulZ b c) (mulZ b' d')
            = mulZ (mulZ b b') (mulZ c d') := by
                rw [mulZ_assoc b c (mulZ b' d') hb_int hc_int (mulZ_in_IntSet b' d' hb'_int hd'_int),
                    ← mulZ_assoc c b' d' hc_int hb'_int hd'_int,
                    mulZ_comm c b' hc_int hb'_int,
                    mulZ_assoc b' c d' hb'_int hc_int hd'_int,
                    ← mulZ_assoc b b' (mulZ c d') hb_int hb'_int (mulZ_in_IntSet c d' hc_int hd'_int)]
          _ = mulZ (mulZ b b') (mulZ d c') := by rw [hR₂_eq]
          _ = mulZ (mulZ b d) (mulZ b' c') := by
                rw [mulZ_assoc b b' (mulZ d c') hb_int hb'_int (mulZ_in_IntSet d c' hd_int hc'_int),
                    ← mulZ_assoc b' d c' hb'_int hd_int hc'_int,
                    mulZ_comm b' d hb'_int hd_int,
                    mulZ_assoc d b' c' hd_int hb'_int hc'_int,
                    ← mulZ_assoc b d (mulZ b' c') hb_int hd_int (mulZ_in_IntSet b' c' hb'_int hc'_int)]

    -- =========================================================================
    -- Section 3: Definition of addQ via QuotientLift₂
    -- =========================================================================

    /-- The graph of rational addition, constructed via QuotientLift₂ -/
    noncomputable def addQ_graph : U :=
      QuotientLift₂Graph addQ_op RatEquivRel RatBase

    /-- Addition on Q -/
    noncomputable def addQ (x y : U) : U := addQ_graph⦅⟨x, y⟩⦆

    -- =========================================================================
    -- Section 4: Computation rule
    -- =========================================================================

    /-- Computation rule: addQ [(a,b)] [(c,d)] = [(a·d + b·c, b·d)] -/
    theorem addQ_class (a b c d : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (NonZeroIntSet : U))
        (hc : c ∈ (IntSet : U)) (hd : d ∈ (NonZeroIntSet : U)) :
        addQ (ratClass a b) (ratClass c d) =
          ratClass (addZ (mulZ a d) (mulZ b c)) (mulZ b d) := by
      unfold addQ addQ_graph ratClass
      have key := QuotientLift₂_apply addQ_op RatEquivRel RatBase ⟨a, b⟩ ⟨c, d⟩
          RatEquivRel_is_equivalence addQ_op_closed addQ_op_compat
          ((mem_RatBase a b).mpr ⟨ha, hb⟩)
          ((mem_RatBase c d).mpr ⟨hc, hd⟩)
      rw [key]
      unfold addQ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 5: Closure
    -- =========================================================================

    /-- Addition is closed on Q -/
    theorem addQ_in_RatSet (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        addQ x y ∈ (RatSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      rw [addQ_class a b c d ha hb hc hd]
      apply ratClass_mem_RatSet
      · exact addZ_in_IntSet _ _
          (mulZ_in_IntSet a d ha (NonZeroIntSet_mem_IntSet d hd))
          (mulZ_in_IntSet b c (NonZeroIntSet_mem_IntSet b hb) hc)
      · exact mulZ_mem_NonZeroIntSet b d hb hd

    -- =========================================================================
    -- Section 6: Algebraic properties
    -- =========================================================================

    /-- Commutativity: addQ x y = addQ y x -/
    theorem addQ_comm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        addQ x y = addQ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      subst hx_eq; subst hy_eq
      rw [addQ_class a b c d ha hb hc hd, addQ_class c d a b hc hd ha hb]
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      have had := mulZ_in_IntSet a d ha hd_int
      have hbc := mulZ_in_IntSet b c hb_int hc
      have hcb := mulZ_in_IntSet c b hc hb_int
      have hda := mulZ_in_IntSet d a hd_int ha
      have hbd := mulZ_in_IntSet b d hb_int hd_int
      have hdb := mulZ_in_IntSet d b hd_int hb_int
      have hbd_nz := mulZ_mem_NonZeroIntSet b d hb hd
      have hdb_nz := mulZ_mem_NonZeroIntSet d b hd hb
      -- Use ratClass_eq_iff
      have key := ratClass_eq_iff
                    (addZ (mulZ a d) (mulZ b c)) (mulZ b d)
                    (addZ (mulZ c b) (mulZ d a)) (mulZ d b)
                    (addZ_in_IntSet _ _ had hbc) hbd_nz
                    (addZ_in_IntSet _ _ hcb hda) hdb_nz
      rw [key]
      -- mulZ (addZ (mulZ a d) (mulZ b c)) (mulZ d b)
      -- = mulZ (mulZ b d) (addZ (mulZ c b) (mulZ d a))
      -- Expand both sides:
      rw [mulZ_addZ_distrib_right (mulZ a d) (mulZ b c) (mulZ d b) had hbc hdb]
      rw [mulZ_addZ_distrib_left _ _ _ hbd hcb hda]
      -- LHS: addZ (mulZ (mulZ a d) (mulZ d b)) (mulZ (mulZ b c) (mulZ d b))
      -- RHS: addZ (mulZ (mulZ b d) (mulZ c b)) (mulZ (mulZ b d) (mulZ d a))
      -- Show: (a·d)·(d·b) = (b·d)·(d·a)  and  (b·c)·(d·b) = (b·d)·(c·b)
      -- Use addZ_comm on LHS to swap terms, matching order with RHS
      rw [addZ_comm (mulZ (mulZ a d) (mulZ d b)) (mulZ (mulZ b c) (mulZ d b))
            (mulZ_in_IntSet (mulZ a d) (mulZ d b) had hdb)
            (mulZ_in_IntSet (mulZ b c) (mulZ d b) hbc hdb)]
      congr 1
      · -- (b·c)·(d·b) = (b·d)·(c·b): both = b²·c·d
        -- LHS: (b·c)·(d·b) = (c·b)·(b·d) [comm b c, comm d b]
        --     = c·(b·(b·d)) [assoc] = c·(b²·d) = c·b²·d = b²·c·d
        -- RHS: (b·d)·(c·b) = b·(d·(c·b)) [assoc] = b·(d·c·b) = b·(c·d·b) = b·(c·(d·b)) = ...
        -- Simplest: show both equal mulZ (mulZ b b) (mulZ c d)
        have hbb := mulZ_in_IntSet b b hb_int hb_int
        have hcd := mulZ_in_IntSet c d hc hd_int
        have lhs_eq : mulZ (mulZ b c) (mulZ d b) = mulZ (mulZ b b) (mulZ c d) := by
          calc mulZ (mulZ b c) (mulZ d b)
              = mulZ (mulZ c b) (mulZ b d) := by
                    rw [mulZ_comm b c hb_int hc, mulZ_comm d b hd_int hb_int]
            _ = mulZ c (mulZ b (mulZ b d)) := by rw [mulZ_assoc c b (mulZ b d) hc hb_int hbd]
            _ = mulZ c (mulZ (mulZ b b) d) := by rw [mulZ_assoc b b d hb_int hb_int hd_int]
            _ = mulZ (mulZ b b) (mulZ c d) := by
                    rw [← mulZ_assoc c (mulZ b b) d hc hbb hd_int,
                        mulZ_comm c (mulZ b b) hc hbb,
                        mulZ_assoc (mulZ b b) c d hbb hc hd_int]
        have rhs_eq : mulZ (mulZ b d) (mulZ c b) = mulZ (mulZ b b) (mulZ c d) := by
          calc mulZ (mulZ b d) (mulZ c b)
              = mulZ b (mulZ d (mulZ c b)) := by rw [mulZ_assoc b d (mulZ c b) hb_int hd_int hcb]
            _ = mulZ b (mulZ (mulZ d c) b) := by rw [mulZ_assoc d c b hd_int hc hb_int]
            _ = mulZ b (mulZ (mulZ c d) b) := by rw [mulZ_comm d c hd_int hc]
            _ = mulZ (mulZ b (mulZ c d)) b := by rw [mulZ_assoc b (mulZ c d) b hb_int hcd hb_int]
            _ = mulZ (mulZ (mulZ b c) d) b := by rw [mulZ_assoc b c d hb_int hc hd_int]
            _ = mulZ (mulZ b c) (mulZ d b) := by
                    rw [← mulZ_assoc (mulZ b c) d b (mulZ_in_IntSet b c hb_int hc) hd_int hb_int]
            _ = mulZ (mulZ b b) (mulZ c d) := lhs_eq
        rw [lhs_eq, rhs_eq]
      · -- (a·d)·(d·b) = (b·d)·(d·a): both = a·b·d²
        have h1 : mulZ (mulZ a d) (mulZ d b) = mulZ (mulZ a b) (mulZ d d) :=
          calc mulZ (mulZ a d) (mulZ d b)
              = mulZ a (mulZ d (mulZ d b)) := by rw [mulZ_assoc a d (mulZ d b) ha hd_int hdb]
            _ = mulZ a (mulZ (mulZ d d) b) := by rw [mulZ_assoc d d b hd_int hd_int hb_int]
            _ = mulZ a (mulZ b (mulZ d d)) := by
                  rw [mulZ_comm (mulZ d d) b (mulZ_in_IntSet d d hd_int hd_int) hb_int]
            _ = mulZ (mulZ a b) (mulZ d d) := by
                  rw [mulZ_assoc a b (mulZ d d) ha hb_int (mulZ_in_IntSet d d hd_int hd_int)]
        have h2 : mulZ (mulZ b d) (mulZ d a) = mulZ (mulZ a b) (mulZ d d) :=
          calc mulZ (mulZ b d) (mulZ d a)
              = mulZ b (mulZ d (mulZ d a)) := by rw [mulZ_assoc b d (mulZ d a) hb_int hd_int hda]
            _ = mulZ b (mulZ (mulZ d d) a) := by rw [mulZ_assoc d d a hd_int hd_int ha]
            _ = mulZ b (mulZ a (mulZ d d)) := by
                  rw [mulZ_comm (mulZ d d) a (mulZ_in_IntSet d d hd_int hd_int) ha]
            _ = mulZ (mulZ b a) (mulZ d d) := by
                  rw [mulZ_assoc b a (mulZ d d) hb_int ha (mulZ_in_IntSet d d hd_int hd_int)]
            _ = mulZ (mulZ a b) (mulZ d d) := by rw [mulZ_comm b a hb_int ha]
        rw [h1, h2]

    /-- Associativity: addQ (addQ x y) z = addQ x (addQ y z) -/
    theorem addQ_assoc (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        addQ (addQ x y) z = addQ x (addQ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := mem_RatSet_is_ratClass y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := mem_RatSet_is_ratClass z hz
      subst hx_eq; subst hy_eq; subst hz_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      have hd_int := NonZeroIntSet_mem_IntSet d hd
      have hf_int := NonZeroIntSet_mem_IntSet f hf
      have hbd_mem := mulZ_mem_NonZeroIntSet b d hb hd
      have hdf_mem := mulZ_mem_NonZeroIntSet d f hd hf
      have hbdf_mem := mulZ_mem_NonZeroIntSet (mulZ b d) f hbd_mem hf
      have hadbcI := addZ_in_IntSet _ _ (mulZ_in_IntSet a d ha hd_int) (mulZ_in_IntSet b c hb_int hc)
      have hcfdeI := addZ_in_IntSet _ _ (mulZ_in_IntSet c f hc hf_int) (mulZ_in_IntSet d e hd_int he)
      rw [addQ_class a b c d ha hb hc hd,
          addQ_class c d e f hc hd he hf,
          addQ_class (addZ (mulZ a d) (mulZ b c)) (mulZ b d) e f hadbcI hbd_mem he hf,
          addQ_class a b (addZ (mulZ c f) (mulZ d e)) (mulZ d f) ha hb hcfdeI hdf_mem]
      -- LHS ratClass num: addZ(mulZ(addZ(mulZ a d)(mulZ b c)) f)(mulZ(mulZ b d) e)
      --                 = (ad+bc)f + bde = adf+bcf+bde
      -- RHS ratClass num: addZ(mulZ a (mulZ d f))(mulZ b (addZ(mulZ c f)(mulZ d e)))
      --                 = a·df + b(cf+de) = adf+bcf+bde
      -- LHS denom: mulZ(mulZ b d) f = bdf
      -- RHS denom: mulZ b (mulZ d f) = bdf  (equal by mulZ_assoc)
      -- Show denominators equal, then numerators equal → ratClass equal
      have denom_eq : mulZ (mulZ b d) f = mulZ b (mulZ d f) := by
        rw [mulZ_assoc b d f hb_int hd_int hf_int]
      -- Numerators equal:
      have num_lhs := addZ_in_IntSet _ _
        (mulZ_in_IntSet (addZ (mulZ a d) (mulZ b c)) f hadbcI hf_int)
        (mulZ_in_IntSet (mulZ b d) e (NonZeroIntSet_mem_IntSet (mulZ b d) hbd_mem) he)
      have num_rhs := addZ_in_IntSet _ _
        (mulZ_in_IntSet a (mulZ d f) ha (NonZeroIntSet_mem_IntSet (mulZ d f) hdf_mem))
        (mulZ_in_IntSet b (addZ (mulZ c f) (mulZ d e)) hb_int hcfdeI)
      have num_eq : addZ (mulZ (addZ (mulZ a d) (mulZ b c)) f) (mulZ (mulZ b d) e)
                  = addZ (mulZ a (mulZ d f)) (mulZ b (addZ (mulZ c f) (mulZ d e))) := by
        rw [mulZ_addZ_distrib_right (mulZ a d) (mulZ b c) f
              (mulZ_in_IntSet a d ha hd_int) (mulZ_in_IntSet b c hb_int hc) hf_int]
        rw [mulZ_addZ_distrib_left b (mulZ c f) (mulZ d e) hb_int
              (mulZ_in_IntSet c f hc hf_int) (mulZ_in_IntSet d e hd_int he)]
        rw [addZ_assoc (mulZ (mulZ a d) f) (mulZ (mulZ b c) f) (mulZ (mulZ b d) e)
              (mulZ_in_IntSet (mulZ a d) f (mulZ_in_IntSet a d ha hd_int) hf_int)
              (mulZ_in_IntSet (mulZ b c) f (mulZ_in_IntSet b c hb_int hc) hf_int)
              (mulZ_in_IntSet (mulZ b d) e (NonZeroIntSet_mem_IntSet (mulZ b d) hbd_mem) he)]
        -- State: addZ (mulZ(mulZ a d) f) (addZ (mulZ(mulZ b c) f) (mulZ(mulZ b d) e))
        --      = addZ (mulZ a (mulZ d f)) (addZ (mulZ b (mulZ c f)) (mulZ b (mulZ d e)))
        congr 1
        · rw [mulZ_assoc a d f ha hd_int hf_int]
        · congr 1
          · rw [mulZ_assoc b c f hb_int hc hf_int]
          · rw [mulZ_assoc b d e hb_int hd_int he]
      -- Now combine: same numerator, equal denominators
      rw [denom_eq, num_eq]

    /-- Right identity: addQ x 0Q = x -/
    theorem addQ_zero_right (x : U) (hx : x ∈ (RatSet : U)) :
        addQ x zeroQ = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      unfold zeroQ
      rw [addQ_class a b zeroZ oneZ ha hb zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet,
          mulZ_one_right a ha, mulZ_zero_right b hb_int, addZ_zero_right a ha,
          mulZ_one_right b hb_int]

    /-- Left identity: addQ 0Q x = x -/
    theorem addQ_zero_left (x : U) (hx : x ∈ (RatSet : U)) :
        addQ zeroQ x = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := mem_RatSet_is_ratClass x hx
      subst hx_eq
      have hb_int := NonZeroIntSet_mem_IntSet b hb
      unfold zeroQ
      rw [addQ_class zeroZ oneZ a b zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet ha hb,
          mulZ_zero_left b hb_int, mulZ_one_left a ha, addZ_zero_left a ha,
          mulZ_one_left b hb_int]

  end Rat.Add

  -- Export
  export Rat.Add (
    mulZ_nonzero_of_nonzero
    addQ_class
    addQ_in_RatSet
    addQ_comm
    addQ_assoc
    addQ_zero_left
    addQ_zero_right
  )

end ZFC
