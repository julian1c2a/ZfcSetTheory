/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Rational Embedding — Canonical Injection ℤ ↪ ℚ

  This module defines the canonical embedding of integers into rationals
  and proves its main algebraic, order, and cardinality properties.

  ## Main Definitions

  * `intToRat` — maps n ∈ ℤ to ratClass n oneZ ∈ ℚ  (= n/1)

  ## Main Theorems

  * `intToRat_mem_RatSet`      — intToRat n ∈ ℚ
  * `intToRat_injective`       — intToRat is injective
  * `intToRat_zeroZ`           — intToRat zeroZ = zeroQ
  * `intToRat_oneZ`            — intToRat oneZ = oneQ
  * `intToRat_preserves_add`   — intToRat (addZ m n) = addQ (intToRat m) (intToRat n)
  * `intToRat_preserves_neg`   — intToRat (negZ n) = negQ (intToRat n)
  * `intToRat_preserves_sub`   — intToRat (subZ m n) = subQ (intToRat m) (intToRat n)
  * `intToRat_preserves_mul`   — intToRat (mulZ m n) = mulQ (intToRat m) (intToRat n)
  * `intToRat_preserves_leZ`   — leZ m n → leQ (intToRat m) (intToRat n)
  * `intToRat_reflects_leZ`    — leQ (intToRat m) (intToRat n) → leZ m n
  * `intToRat_preserves_ltZ`   — ltZ m n → ltQ (intToRat m) (intToRat n)
  * `intToRat_reflects_ltZ`    — ltQ (intToRat m) (intToRat n) → ltZ m n
  * `intToRat_not_surjective`  — intToRat is not surjective onto ℚ
  * `archQ`                    — Archimedean property of ℚ

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Abs
import ZFC.Int.Embedding
import ZFC.Int.Induction
import ZFC.Int.Units

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
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Ring
  open ZFC.Int.Order
  open ZFC.Int.Embedding
  open ZFC.Int.Abs
  open ZFC.Int.Induction
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs

  universe u
  variable {U : Type u}

  namespace Rat.Embedding

    -- =========================================================================
    -- Section 0: Private helpers
    -- =========================================================================

    /-- x ≠ 0 → 0 < x² (re-proved locally since the Int.Order version is private). -/
    private theorem sq_pos_ne_zero (x : U) (hx : x ∈ (IntSet : U))
        (hx_ne : x ≠ (zeroZ : U)) :
        ltZ (zeroZ : U) (mulZ x x) :=
      ⟨square_nonneg x hx,
       fun h => hx_ne ((mulZ_eq_zero_iff x x hx hx).mp h.symm |>.elim id id)⟩

    -- =========================================================================
    -- Section 1: Definition
    -- =========================================================================

    /-- The canonical embedding: n ↦ ratClass n oneZ = n/1. -/
    noncomputable def intToRat (n : U) : U := ratClass n oneZ

    -- =========================================================================
    -- Section 2: Membership
    -- =========================================================================

    /-- intToRat maps ℤ into ℚ. -/
    theorem intToRat_mem_RatSet
      (n : U) (hn : n ∈ (IntSet : U)) :
        intToRat n ∈ (RatSet : U)
          := by
      unfold intToRat
      exact ratClass_mem_RatSet n oneZ hn oneZ_mem_NonZeroIntSet

    -- =========================================================================
    -- Section 3: Injectivity
    -- =========================================================================

    /-- intToRat is injective. -/
    theorem intToRat_injective
      (m n : U)
      (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U))
      (h : intToRat m = intToRat n) :
        m = n
          := by
      unfold intToRat at h
      rw [ratClass_eq_iff m oneZ n oneZ hm oneZ_mem_NonZeroIntSet hn oneZ_mem_NonZeroIntSet] at h
      -- h : mulZ m oneZ = mulZ oneZ n
      rw [mulZ_one_right m hm, mulZ_one_left n hn] at h
      exact h

    -- =========================================================================
    -- Section 4: Ring homomorphism properties
    -- =========================================================================

    /-- intToRat sends zeroZ to zeroQ. -/
    theorem intToRat_zeroZ : intToRat (zeroZ : U) = (zeroQ : U) := rfl

    /-- intToRat sends oneZ to oneQ. -/
    theorem intToRat_oneZ : intToRat (oneZ : U) = (oneQ : U) := rfl

    /-- intToRat preserves addition. -/
    theorem intToRat_preserves_add
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U)) :
        intToRat (addZ m n) = addQ (intToRat m) (intToRat n)
          := by
      unfold intToRat
      rw [addQ_class m oneZ n oneZ hm oneZ_mem_NonZeroIntSet hn oneZ_mem_NonZeroIntSet,
          mulZ_one_right m hm, mulZ_one_left n hn, mulZ_one_left oneZ oneZ_mem_IntSet]

    /-- intToRat preserves negation. -/
    theorem intToRat_preserves_neg
      (n : U) (hn : n ∈ (IntSet : U)) :
        intToRat (negZ n) = negQ (intToRat n)
          := by
      unfold intToRat
      rw [negQ_class n oneZ hn oneZ_mem_NonZeroIntSet]

    /-- intToRat preserves subtraction. -/
    theorem intToRat_preserves_sub
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U)) :
        intToRat (subZ m n) = subQ (intToRat m) (intToRat n)
          := by
      unfold subZ subQ
      rw [intToRat_preserves_add m (negZ n) hm (negZ_in_IntSet n hn),
          intToRat_preserves_neg n hn]

    /-- intToRat preserves multiplication. -/
    theorem intToRat_preserves_mul
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U)) :
        intToRat (mulZ m n) = mulQ (intToRat m) (intToRat n)
          := by
      unfold intToRat
      rw [mulQ_class m oneZ n oneZ hm oneZ_mem_NonZeroIntSet hn oneZ_mem_NonZeroIntSet,
          mulZ_one_left oneZ oneZ_mem_IntSet]

    -- =========================================================================
    -- Section 5: Order preservation / reflection
    -- =========================================================================

    /-- Key lemma: leQ (intToRat m) (intToRat n) ↔ leZ m n. -/
    private theorem intToRat_leQ_iff_leZ
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U)) :
        leQ (intToRat m) (intToRat n) ↔ leZ m n
          := by
      unfold intToRat
      constructor
      · -- Forward: apply the universal leQ to canonical representatives (m, oneZ, n, oneZ).
        intro h_le
        have h_repr := h_le m oneZ n oneZ
                         hm oneZ_mem_NonZeroIntSet hn oneZ_mem_NonZeroIntSet rfl rfl
        unfold leQ_repr at h_repr
        -- h_repr : leZ (mulZ (mulZ m oneZ) (mulZ oneZ oneZ))
        --                (mulZ (mulZ oneZ oneZ) (mulZ n oneZ))
        rw [mulZ_one_right m hm,
            mulZ_one_right oneZ oneZ_mem_IntSet,
            mulZ_one_right m hm,
            mulZ_one_left (mulZ n oneZ) (mulZ_in_IntSet n oneZ hn oneZ_mem_IntSet),
            mulZ_one_right n hn] at h_repr
        exact h_repr
      · -- Backward: leZ m n → for ALL representatives (a, b, c, d), leQ_repr a b c d.
        intro h_le
        intro a b c d ha hb hc hd h_x h_y
        have hb_i := NonZeroIntSet_mem_IntSet b hb
        have hd_i := NonZeroIntSet_mem_IntSet d hd
        rw [ratClass_eq_iff m oneZ a b hm oneZ_mem_NonZeroIntSet ha hb,
            mulZ_one_left a ha] at h_x
        -- h_x : mulZ m b = a
        rw [ratClass_eq_iff n oneZ c d hn oneZ_mem_NonZeroIntSet hc hd,
            mulZ_one_left c hc] at h_y
        -- h_y : mulZ n d = c
        -- Goal: leQ_repr a b c d = leZ ((a·b)·d²) (b²·(c·d))
        -- Substitute a = m·b and c = n·d, factor as m·K ≤ n·K (K = b²·d² > 0).
        unfold leQ_repr
        rw [← h_x, ← h_y]
        have hb_sq := mulZ_in_IntSet b b hb_i hb_i
        have hd_sq := mulZ_in_IntSet d d hd_i hd_i
        -- LHS: (m·b)·b · d² → m·(b²·d²)
        rw [mulZ_assoc m b b hm hb_i hb_i,
            mulZ_assoc m (mulZ b b) (mulZ d d) hm hb_sq hd_sq]
        -- RHS: b² · (n·d)·d → n·(b²·d²)
        rw [mulZ_assoc n d d hn hd_i hd_i,
            mulZ_comm (mulZ b b) (mulZ n (mulZ d d))
              hb_sq (mulZ_in_IntSet n (mulZ d d) hn hd_sq),
            mulZ_assoc n (mulZ d d) (mulZ b b) hn hd_sq hb_sq,
            mulZ_comm (mulZ d d) (mulZ b b) hd_sq hb_sq]
        -- Goal: leZ (mulZ m K) (mulZ n K),  K = b²·d² > 0
        have hK := mulZ_in_IntSet (mulZ b b) (mulZ d d) hb_sq hd_sq
        have hK_pos : ltZ (zeroZ : U) (mulZ (mulZ b b) (mulZ d d)) :=
          positiveZ_mul_closed (mulZ b b) (mulZ d d) hb_sq hd_sq
            (sq_pos_ne_zero b hb_i (NonZeroIntSet_ne_zero b hb))
            (sq_pos_ne_zero d hd_i (NonZeroIntSet_ne_zero d hd))
        have h_Km_Kn := mulZ_le_mulZ_nonneg m n (mulZ (mulZ b b) (mulZ d d))
                          hm hn hK h_le hK_pos.1
        rwa [mulZ_comm (mulZ (mulZ b b) (mulZ d d)) m hK hm,
             mulZ_comm (mulZ (mulZ b b) (mulZ d d)) n hK hn] at h_Km_Kn

    /-- intToRat preserves leZ: m ≤ n → intToRat m ≤ intToRat n. -/
    theorem intToRat_preserves_leZ
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U)) (h : leZ m n) :
        leQ (intToRat m) (intToRat n)
          :=
      (intToRat_leQ_iff_leZ m n hm hn).mpr h

    /-- intToRat reflects leZ: intToRat m ≤ intToRat n → m ≤ n. -/
    theorem intToRat_reflects_leZ
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U))
      (h : leQ (intToRat m) (intToRat n)) :
        leZ m n
          :=
      (intToRat_leQ_iff_leZ m n hm hn).mp h

    /-- intToRat preserves ltZ: m < n → intToRat m < intToRat n. -/
    theorem intToRat_preserves_ltZ
      (m n : U)
      (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U))
      (h : ltZ m n) :
        ltQ (intToRat m) (intToRat n)
          :=
      ⟨intToRat_preserves_leZ m n hm hn h.1,
       fun h_eq => h.2 (intToRat_injective m n hm hn h_eq)⟩

    /-- intToRat reflects ltZ: intToRat m < intToRat n → m < n. -/
    theorem intToRat_reflects_ltZ
      (m n : U) (hm : m ∈ (IntSet : U)) (hn : n ∈ (IntSet : U))
      (h : ltQ (intToRat m) (intToRat n)) :
        ltZ m n
          :=
      ⟨intToRat_reflects_leZ m n hm hn h.1,
       fun h_eq => h.2 (congrArg intToRat h_eq)⟩

    -- =========================================================================
    -- Section 6: Non-surjectivity
    -- =========================================================================

    private noncomputable def twoInt : U := intClass (σ (σ (∅ : U))) (∅ : U)

    private theorem twoInt_in_Omega2 : σ (σ (∅ : U)) ∈ (ω : U) :=
      succ_in_Omega _ (succ_in_Omega _ zero_in_Omega)

    private theorem twoInt_mem_IntSet : (twoInt : U) ∈ (IntSet : U) :=
      intClass_mem_IntSet (σ (σ (∅ : U))) (∅ : U) twoInt_in_Omega2 zero_in_Omega

    private theorem twoInt_ne_zeroZ : (twoInt : U) ≠ (zeroZ : U) := by
      unfold twoInt zeroZ
      intro h
      have h' := (intClass_eq_iff (σ (σ (∅ : U))) (∅ : U) (∅ : U) (∅ : U)
                    twoInt_in_Omega2 zero_in_Omega zero_in_Omega zero_in_Omega).mp h
      rw [add_zero (σ (σ (∅ : U))) twoInt_in_Omega2,
          add_zero (∅ : U) zero_in_Omega] at h'
      exact absurd h' (succ_nonempty (σ (∅ : U)))

    private theorem twoInt_mem_NonZeroIntSet : (twoInt : U) ∈ (NonZeroIntSet : U) := by
      rw [mem_NonZeroIntSet]; exact ⟨twoInt_mem_IntSet, twoInt_ne_zeroZ⟩

    private theorem twoInt_ne_oneZ : (twoInt : U) ≠ (oneZ : U) := by
      unfold twoInt oneZ
      intro h
      have h' := (intClass_eq_iff (σ (σ (∅ : U))) (∅ : U) (σ (∅ : U)) (∅ : U)
                    twoInt_in_Omega2 zero_in_Omega
                    (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega).mp h
      rw [add_zero (σ (σ (∅ : U))) twoInt_in_Omega2,
          zero_add (σ (∅ : U)) (succ_in_Omega (∅ : U) zero_in_Omega)] at h'
      exact absurd (succ_injective (σ (∅ : U)) (∅ : U)
                     (mem_Omega_is_Nat _ (succ_in_Omega (∅ : U) zero_in_Omega))
                     (mem_Omega_is_Nat _ zero_in_Omega)
                     h')
                   (succ_nonempty (∅ : U))

    private theorem twoInt_ne_negOneZ : (twoInt : U) ≠ negZ (oneZ : U) := by
      have h_neg : negZ (oneZ : U) = intClass (∅ : U) (σ (∅ : U)) :=
        negZ_class (σ (∅ : U)) (∅ : U) (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega
      rw [h_neg]
      unfold twoInt
      intro h
      have h' := (intClass_eq_iff (σ (σ (∅ : U))) (∅ : U) (∅ : U) (σ (∅ : U))
                    twoInt_in_Omega2 zero_in_Omega
                    zero_in_Omega (succ_in_Omega (∅ : U) zero_in_Omega)).mp h
      rw [add_succ (σ (σ (∅ : U))) (∅ : U) twoInt_in_Omega2 zero_in_Omega,
          add_zero (σ (σ (∅ : U))) twoInt_in_Omega2,
          add_zero (∅ : U) zero_in_Omega] at h'
      exact absurd h' (succ_nonempty (σ (σ (∅ : U))))

    /-- intToRat is not surjective onto ℚ: 1/2 has no preimage in ℤ. -/
    theorem intToRat_not_surjective :
        ¬ ∀ x : U, (x ∈ (RatSet : U)) → ∃ z : U, (z ∈ (IntSet : U)) ∧ intToRat z = x := by
      intro h_surj
      have h_half_mem : ratClass (oneZ : U) twoInt ∈ (RatSet : U) :=
        ratClass_mem_RatSet oneZ twoInt oneZ_mem_IntSet twoInt_mem_NonZeroIntSet
      obtain ⟨z, hz, h_eq⟩ := h_surj (ratClass oneZ twoInt) h_half_mem
      unfold intToRat at h_eq
      rw [ratClass_eq_iff z oneZ oneZ twoInt
            hz oneZ_mem_NonZeroIntSet oneZ_mem_IntSet twoInt_mem_NonZeroIntSet,
          mulZ_one_left oneZ oneZ_mem_IntSet] at h_eq
      -- h_eq : mulZ z twoInt = oneZ
      rw [mulZ_comm z twoInt hz twoInt_mem_IntSet] at h_eq
      -- mulZ twoInt z = oneZ → isUnitZ twoInt
      have h_unit : isUnitZ (twoInt : U) := ⟨twoInt_mem_IntSet, z, hz, h_eq⟩
      rcases (unitZ_iff twoInt twoInt_mem_IntSet).mp h_unit with h | h
      · exact twoInt_ne_oneZ h
      · exact twoInt_ne_negOneZ h

    -- =========================================================================
    -- Section 7: Archimedean property
    -- =========================================================================

    /-- Archimedean property for ℤ (sorry — needs Archimedean induction on ω). -/
    private theorem archZ (M N : U)
        (hM : M ∈ (IntSet : U)) (hN : N ∈ (IntSet : U))
        (hN_pos : ltZ (zeroZ : U) N) :
        ∃ k : U, (k ∈ (ω : U)) ∧ leZ M (mulZ (natToInt k) N) := by
      sorry

    /-- Archimedean property for ℚ:
        For any x, y ∈ ℚ with 0 < y, there exists k ∈ ω such that x ≤ k · y. -/
    theorem archQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hy_pos : isPositiveQ y) :
        ∃ k : U, (k ∈ (ω : U)) ∧ leQ x (mulQ (intToRat (natToInt k)) y) := by
      sorry

  end Rat.Embedding

end ZFC

export ZFC.Rat.Embedding (
  intToRat
  intToRat_mem_RatSet
  intToRat_injective
  intToRat_zeroZ
  intToRat_oneZ
  intToRat_preserves_add
  intToRat_preserves_neg
  intToRat_preserves_sub
  intToRat_preserves_mul
  intToRat_preserves_leZ
  intToRat_reflects_leZ
  intToRat_preserves_ltZ
  intToRat_reflects_ltZ
  intToRat_not_surjective
  archQ
)
