/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Rational Equivalence Relation on ℤ × ℤ*

  This module defines the equivalence relation on ℤ × ℤ* used to construct
  the rationals ℚ as a quotient set. Two pairs (a, b) and (c, d) (with b ≠ 0
  and d ≠ 0) are equivalent iff a · d = b · c, representing the fractions
  a/b = c/d.

  ## Main Definitions

  * `NonZeroIntSet` -- ℤ* := sep IntSet (. ≠ zeroZ)
  * `RatBase`       -- ℤ × ℤ* (the carrier of the pre-rational pairs)
  * `RatEquivRel`   -- the relation {<<a,b>,<c,d>> in (ℤxℤ*)x(ℤxℤ*) | a.d = b.c}

  ## Main Theorems

  * `mem_NonZeroIntSet`        -- z in ℤ* iff z in IntSet /\ z ≠ zeroZ
  * `NonZeroIntSet_sub_IntSet` -- ℤ* ⊆ IntSet
  * `NonZeroIntSet_ne_zero`    -- elements of ℤ* are nonzero
  * `NonZeroIntSet_mem_IntSet` -- elements of ℤ* are integers
  * `mem_RatBase`              -- <a,b> in RatBase iff a in IntSet /\ b in ℤ*
  * `mem_RatEquivRel`          -- membership characterization for RatEquivRel
  * `RatEquivRel_is_relation`  -- RatEquivRel ⊆ RatBase × RatBase
  * `RatEquivRel_refl`         -- reflexivity
  * `RatEquivRel_symm`         -- symmetry
  * `RatEquivRel_trans`        -- transitivity
  * `RatEquivRel_is_equivalence` -- RatEquivRel is an equivalence on RatBase

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md §3, §4 y §6
cuando esté completo y compilando.
-/

import ZFC.Int.Ring

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

  universe u
  variable {U : Type u}

  namespace Rat.Equiv

    noncomputable def NonZeroIntSet : U :=
      sep (IntSet : U) (fun z => z ≠ (zeroZ : U))

    theorem mem_NonZeroIntSet (z : U) :
        z ∈ (NonZeroIntSet : U) ↔ z ∈ (IntSet : U) ∧ z ≠ (zeroZ : U) := by
      unfold NonZeroIntSet
      rw [mem_sep_iff]

    theorem NonZeroIntSet_sub_IntSet :
        (NonZeroIntSet : U) ⊆ (IntSet : U) := by
      intro z hz
      exact ((mem_NonZeroIntSet z).mp hz).1

    theorem NonZeroIntSet_ne_zero (z : U) (hz : z ∈ (NonZeroIntSet : U)) :
        z ≠ (zeroZ : U) :=
      ((mem_NonZeroIntSet z).mp hz).2

    theorem NonZeroIntSet_mem_IntSet (z : U) (hz : z ∈ (NonZeroIntSet : U)) :
        z ∈ (IntSet : U) :=
      ((mem_NonZeroIntSet z).mp hz).1

    noncomputable def RatBase : U :=
      (IntSet : U) ×ₛ NonZeroIntSet

    theorem mem_RatBase (a b : U) :
        ⟨a, b⟩ ∈ (RatBase : U) ↔ a ∈ (IntSet : U) ∧ b ∈ (NonZeroIntSet : U) := by
      unfold RatBase
      rw [OrderedPair_mem_CartesianProduct]

    noncomputable def RatEquivRel : U :=
      sep ((RatBase : U) ×ₛ RatBase)
        (fun p => mulZ (fst (fst p)) (snd (snd p)) =
                  mulZ (snd (fst p)) (fst (snd p)))

    theorem mem_RatEquivRel (a b c d : U) :
        ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∈ (RatEquivRel : U) ↔
          a ∈ (IntSet : U) ∧ b ∈ (NonZeroIntSet : U) ∧
          c ∈ (IntSet : U) ∧ d ∈ (NonZeroIntSet : U) ∧
          mulZ a d = mulZ b c := by
      unfold RatEquivRel
      rw [mem_sep_iff]
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      constructor
      · intro h
        have h_carrier := h.1
        have h_eq := h.2
        rw [OrderedPair_mem_CartesianProduct] at h_carrier
        have h1 := h_carrier.1
        have h2 := h_carrier.2
        rw [mem_RatBase] at h1 h2
        exact ⟨h1.1, h1.2, h2.1, h2.2, h_eq⟩
      · intro h
        obtain ⟨ha, hb, hc, hd, h_eq⟩ := h
        exact ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr
          ⟨(mem_RatBase a b).mpr ⟨ha, hb⟩,
           (mem_RatBase c d).mpr ⟨hc, hd⟩⟩, h_eq⟩

    theorem RatEquivRel_is_relation :
        isRelationOn (RatEquivRel : U) (RatBase : U) := by
      intro p hp
      unfold RatEquivRel at hp
      rw [mem_sep_iff] at hp
      exact hp.1

    theorem RatEquivRel_refl :
        isReflexiveOn (RatEquivRel : U) (RatBase : U) := by
      intro x hx
      unfold RatBase at hx
      rw [CartesianProduct_is_specified] at hx
      obtain ⟨hx_pair, ha, hb⟩ := hx
      unfold RatEquivRel
      rw [mem_sep_iff]
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      constructor
      · rw [OrderedPair_mem_CartesianProduct]
        unfold RatBase
        exact ⟨(CartesianProduct_is_specified _ _ _).mpr ⟨hx_pair, ha, hb⟩,
               (CartesianProduct_is_specified _ _ _).mpr ⟨hx_pair, ha, hb⟩⟩
      · exact mulZ_comm (fst x) (snd x) ha (NonZeroIntSet_mem_IntSet (snd x) hb)

    theorem RatEquivRel_symm :
        isSymmetricOn (RatEquivRel : U) (RatBase : U) := by
      intro x y hx hy hxy
      have hx_mem := hx
      have hy_mem := hy
      unfold RatBase at hx hy
      rw [CartesianProduct_is_specified] at hx hy
      obtain ⟨_, ha, hb⟩ := hx
      obtain ⟨_, hc, hd⟩ := hy
      unfold RatEquivRel at hxy ⊢
      rw [mem_sep_iff] at hxy ⊢
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hxy ⊢
      refine ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr ⟨hy_mem, hx_mem⟩, ?_⟩
      rw [mulZ_comm (fst y) (snd x) hc (NonZeroIntSet_mem_IntSet (snd x) hb),
          mulZ_comm (snd y) (fst x) (NonZeroIntSet_mem_IntSet (snd y) hd) ha]
      exact hxy.2.symm

    theorem RatEquivRel_trans :
        isTransitiveOn (RatEquivRel : U) (RatBase : U) := by
      intro x y z hx hy hz hxy hyz
      have hx_mem := hx
      have hz_mem := hz
      unfold RatBase at hx hy hz
      rw [CartesianProduct_is_specified] at hx hy hz
      obtain ⟨_, ha, hb⟩ := hx
      obtain ⟨_, hc, hd⟩ := hy
      obtain ⟨_, he, hf⟩ := hz
      have ha_int := ha
      have hb_int := NonZeroIntSet_mem_IntSet (snd x) hb
      have hc_int := hc
      have hd_int := NonZeroIntSet_mem_IntSet (snd y) hd
      have he_int := he
      have hf_int := NonZeroIntSet_mem_IntSet (snd z) hf
      have hd_ne : (snd y) ≠ (zeroZ : U) := NonZeroIntSet_ne_zero (snd y) hd
      unfold RatEquivRel at hxy hyz ⊢
      rw [mem_sep_iff] at hxy hyz ⊢
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hxy hyz ⊢
      have h1 := hxy.2   -- a·d = b·c
      have h2 := hyz.2   -- c·f = d·e
      refine ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr ⟨hx_mem, hz_mem⟩, ?_⟩
      -- Goal: a·f = b·e
      -- (a·d)·f = (b·c)·f
      have step : mulZ (mulZ (fst x) (snd y)) (snd z) =
                  mulZ (mulZ (snd x) (fst y)) (snd z) := by rw [h1]
      -- a·(d·f) = b·(c·f)
      rw [mulZ_assoc (fst x) (snd y) (snd z) ha_int hd_int hf_int] at step
      rw [mulZ_assoc (snd x) (fst y) (snd z) hb_int hc_int hf_int] at step
      -- a·(d·f) = b·(d·e)  [by h2: c·f = d·e]
      rw [h2] at step
      -- Rewrite LHS: a·(d·f) → d·(a·f)
      rw [mulZ_comm (snd y) (snd z) hd_int hf_int,
          ← mulZ_assoc (fst x) (snd z) (snd y) ha_int hf_int hd_int,
          mulZ_comm (mulZ (fst x) (snd z)) (snd y)
            (mulZ_in_IntSet (fst x) (snd z) ha_int hf_int) hd_int] at step
      -- Rewrite RHS: b·(d·e) → d·(b·e)
      rw [mulZ_comm (snd y) (fst z) hd_int he_int,
          ← mulZ_assoc (snd x) (fst z) (snd y) hb_int he_int hd_int,
          mulZ_comm (mulZ (snd x) (fst z)) (snd y)
            (mulZ_in_IntSet (snd x) (fst z) hb_int he_int) hd_int] at step
      -- Cancel d ≠ 0
      exact mulZ_cancel_left (mulZ (fst x) (snd z)) (mulZ (snd x) (fst z)) (snd y)
        (mulZ_in_IntSet (fst x) (snd z) ha_int hf_int)
        (mulZ_in_IntSet (snd x) (fst z) hb_int he_int)
        hd_int hd_ne step

    theorem RatEquivRel_is_equivalence :
        isEquivalenceOn (RatEquivRel : U) (RatBase : U) :=
      ⟨RatEquivRel_is_relation,
       RatEquivRel_refl,
       RatEquivRel_symm,
       RatEquivRel_trans⟩

    noncomputable def RatSet : U :=
      QuotientSet RatBase RatEquivRel

  end Rat.Equiv

end ZFC

export ZFC.Rat.Equiv (
  NonZeroIntSet
  mem_NonZeroIntSet
  NonZeroIntSet_sub_IntSet
  NonZeroIntSet_ne_zero
  NonZeroIntSet_mem_IntSet
  RatBase
  mem_RatBase
  RatEquivRel
  mem_RatEquivRel
  RatEquivRel_is_relation
  RatEquivRel_refl
  RatEquivRel_symm
  RatEquivRel_trans
  RatEquivRel_is_equivalence
  RatSet
)