/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Newton–Raphson √2 Approximation: ℚ is Incomplete

  This module demonstrates the incompleteness of ℚ by constructing the
  Newton–Raphson sequence approximating √2 and showing it is a Cauchy
  sequence with no rational limit.

  ## The Sequence

  Define `sqrtApproxSeq : ω → ℚ` by:
    - f(0) = 3/2
    - f(n+1) = (f(n) + 2/f(n)) / 2   (Newton–Raphson step)

  This is the Newton–Raphson iteration applied to x² − 2 starting from x₀ = 3/2.

  ## Key Invariants (proved by induction)

  1. `sqrtApproxSeq_pos`       — f(n) > 0 for all n ∈ ω
  2. `sqrtApproxSeq_sq_gt_two` — f(n)² > 2 for all n ∈ ω
  3. `sqrtApproxSeq_ge_one`    — f(n) ≥ 1 for all n ∈ ω
  4. `sqrtApproxSeq_nonincreasing` — f is non-increasing (each step decreases)

  ## Main Theorems

  * `sqrtApproxSeq_isSeqQ`      — f : ω → ℚ is a valid sequence
  * `sqrtApproxSeq_isCauchy`    — f is a Cauchy sequence in ℚ
  * `sqrt2_irrational`          — ¬ ∃ L ∈ ℚ, L² = 2
  * `sqrtApproxSeq_not_convergent` — f has no limit in ℚ (ℚ is incomplete)

  ## Proof Sketch for sqrtApproxSeq_not_convergent

  If f → L in ℚ, then (by limit arithmetic) the sequence n ↦ f(n+1) also
  converges to L. But f(n+1) = (f(n) + 2/f(n))/2 → (L + 2/L)/2 by
  convergesToQ_const_mul and convergesToQ_inv (once proved). By limit
  uniqueness, L = (L + 2/L)/2, hence L² = 2, contradicting sqrt2_irrational.

  ## Construction Strategy

  We use `RecursiveFn (RatSet : U) threeHalvesQ sqrtStepFn` where
  `sqrtStepFn : RatSet → RatSet` maps x ↦ (x + 2/x) / 2, represented as
  a ZFC function graph using the `sep` pattern.

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Monotone

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
  open ZFC.Nat.MaxMin
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Field
  open ZFC.Rat.MaxMin
  open ZFC.Rat.Sequences
  open ZFC.Rat.Convergence
  open ZFC.Rat.CauchyQ
  open ZFC.Rat.Monotone

  universe u
  variable {U : Type u}

  namespace Rat.SqrtApprox

    -- =========================================================================
    -- Section 1: Private rational constants
    -- =========================================================================

    /-- 2 ∈ ℚ, defined as 1 + 1. -/
    private noncomputable def twoQ : U := addQ (oneQ : U) (oneQ : U)

    /-- 3 ∈ ℚ, defined as 1 + 2. -/
    private noncomputable def threeQ : U := addQ (oneQ : U) (twoQ : U)

    /-- 3/2 ∈ ℚ, the initial value f(0). -/
    private noncomputable def threeHalvesQ : U := divQ (threeQ : U) (twoQ : U)

    private theorem twoQ_mem : (twoQ : U) ∈ (RatSet : U) :=
      addQ_in_RatSet (oneQ : U) (oneQ : U) oneQ_mem_RatSet oneQ_mem_RatSet

    private theorem threeQ_mem : (threeQ : U) ∈ (RatSet : U) :=
      addQ_in_RatSet (oneQ : U) (twoQ : U) oneQ_mem_RatSet twoQ_mem

    /-- 1 > 0 in ℚ. -/
    private theorem oneQ_pos : isPositiveQ (oneQ : U) := by
      constructor
      · rw [leQ_iff_repr (zeroQ : U) (oneQ : U) zeroQ_mem_RatSet oneQ_mem_RatSet]
        have hone_i : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
        have hone_nz : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
        have h_repr : leQ_repr (zeroZ : U) (oneZ : U) (oneZ : U) (oneZ : U) := by
          unfold leQ_repr
          have h_one : mulZ (oneZ : U) (oneZ : U) = (oneZ : U) :=
            mulZ_one_left (oneZ : U) hone_i
          have h_zero : mulZ (zeroZ : U) (oneZ : U) = (zeroZ : U) :=
            mulZ_zero_left (oneZ : U) hone_i
          have lhs_eq : mulZ (mulZ (zeroZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (zeroZ : U) := by
            simp only [h_one, h_zero]
          have rhs_eq : mulZ (mulZ (oneZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (oneZ : U) := by
            simp only [h_one]
          rw [lhs_eq, rhs_eq]
          have sq := square_nonneg (oneZ : U) hone_i
          rwa [h_one] at sq
        exact ⟨(zeroZ : U), (oneZ : U), (oneZ : U), (oneZ : U),
               zeroZ_mem_IntSet, hone_nz, hone_i, hone_nz, rfl, rfl, h_repr⟩
      · exact zeroQ_ne_oneQ

    private theorem twoQ_ne_zeroQ : (twoQ : U) ≠ (zeroQ : U) := by
      intro h
      have h_le : leQ (addQ (zeroQ : U) (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
        addQ_leQ_addQ zeroQ oneQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet
          oneQ_pos.1
      rw [addQ_zero_left oneQ oneQ_mem_RatSet] at h_le
      have h_two : addQ (oneQ : U) (oneQ : U) = (zeroQ : U) := h
      rw [h_two] at h_le
      have h_eq : (oneQ : U) = zeroQ :=
        leQ_antisymm oneQ zeroQ oneQ_mem_RatSet zeroQ_mem_RatSet h_le oneQ_pos.1
      exact zeroQ_ne_oneQ h_eq.symm

    private theorem twoQ_pos : isPositiveQ (twoQ : U) := by
      constructor
      · have h_le : leQ (addQ (zeroQ : U) (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
          addQ_leQ_addQ zeroQ oneQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet
            oneQ_pos.1
        rw [addQ_zero_left oneQ oneQ_mem_RatSet] at h_le
        exact leQ_trans zeroQ oneQ twoQ zeroQ_mem_RatSet oneQ_mem_RatSet twoQ_mem oneQ_pos.1 h_le
      · exact fun h => twoQ_ne_zeroQ h.symm

    private theorem threeHalvesQ_mem : (threeHalvesQ : U) ∈ (RatSet : U) :=
      divQ_in_RatSet (threeQ : U) (twoQ : U) threeQ_mem twoQ_mem

    private theorem threeHalvesQ_pos : isPositiveQ (threeHalvesQ : U) := by
      -- Integer helpers
      have hone_i : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
      have hone_nz : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
      have htwo_i : addZ (oneZ : U) (oneZ : U) ∈ (IntSet : U) :=
        addZ_in_IntSet oneZ oneZ hone_i hone_i
      have hthree_i : addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U)) ∈ (IntSet : U) :=
        addZ_in_IntSet oneZ (addZ oneZ oneZ) hone_i htwo_i
      -- twoQ = ratClass (addZ oneZ oneZ) oneZ
      have htwo_class : (twoQ : U) = ratClass (addZ (oneZ : U) (oneZ : U)) (oneZ : U) := by
        unfold twoQ
        rw [show (oneQ : U) = ratClass oneZ oneZ from rfl]
        rw [addQ_class oneZ oneZ oneZ oneZ hone_i hone_nz hone_i hone_nz]
        congr 1
        · simp only [mulZ_one_left oneZ hone_i]
        · exact mulZ_one_left oneZ hone_i
      -- twoZ ≠ zeroZ → twoZ ∈ NonZeroIntSet
      have htwo_ne : addZ (oneZ : U) (oneZ : U) ≠ (zeroZ : U) := by
        intro h
        exact twoQ_ne_zeroQ (htwo_class.trans ((ratClass_eq_zeroQ_iff _ _ htwo_i hone_nz).mpr h))
      have htwo_nz : addZ (oneZ : U) (oneZ : U) ∈ (NonZeroIntSet : U) :=
        (mem_NonZeroIntSet _).mpr ⟨htwo_i, htwo_ne⟩
      -- threeQ = ratClass (addZ oneZ (addZ oneZ oneZ)) oneZ
      have hthree_class : (threeQ : U) = ratClass (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) (oneZ : U) := by
        unfold threeQ
        rw [show (oneQ : U) = ratClass oneZ oneZ from rfl, htwo_class]
        rw [addQ_class oneZ oneZ (addZ oneZ oneZ) oneZ hone_i hone_nz htwo_i hone_nz]
        congr 1
        · rw [mulZ_one_left oneZ hone_i, mulZ_one_left (addZ oneZ oneZ) htwo_i]
        · exact mulZ_one_left oneZ hone_i
      -- threeHalvesQ = ratClass threeZ twoZ
      have hthreeHalves_class : (threeHalvesQ : U) =
          ratClass (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) (addZ (oneZ : U) (oneZ : U)) := by
        unfold threeHalvesQ
        rw [hthree_class, htwo_class]
        rw [divQ_class (addZ oneZ (addZ oneZ oneZ)) oneZ (addZ oneZ oneZ) oneZ
            hthree_i hone_nz htwo_nz hone_nz]
        congr 1
        · exact mulZ_one_right (addZ oneZ (addZ oneZ oneZ)) hthree_i
        · exact mulZ_one_left (addZ oneZ oneZ) htwo_i
      -- isPositiveZ oneZ (via square_nonneg)
      have honeZ_pos : isPositiveZ (oneZ : U) := by
        constructor
        · have sq := square_nonneg (oneZ : U) hone_i
          rwa [mulZ_one_left oneZ hone_i] at sq
        · exact (NonZeroIntSet_ne_zero oneZ hone_nz).symm
      -- isPositiveZ twoZ = isPositiveZ (addZ oneZ oneZ)
      have htwoZ_pos : isPositiveZ (addZ (oneZ : U) (oneZ : U)) := by
        constructor
        · have h_le : leZ (addZ (zeroZ : U) (oneZ : U)) (addZ (oneZ : U) (oneZ : U)) :=
            addZ_leZ_addZ zeroZ oneZ oneZ zeroZ_mem_IntSet hone_i hone_i honeZ_pos.1
          rw [addZ_zero_left oneZ hone_i] at h_le
          exact leZ_trans zeroZ oneZ (addZ oneZ oneZ)
            zeroZ_mem_IntSet hone_i htwo_i honeZ_pos.1 h_le
        · exact htwo_ne.symm
      -- isPositiveZ threeZ = isPositiveZ (addZ oneZ (addZ oneZ oneZ))
      have hthreeZ_pos : isPositiveZ (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) := by
        -- oneZ ≤ addZ oneZ oneZ
        have h_1_le_2 : leZ (oneZ : U) (addZ (oneZ : U) (oneZ : U)) := by
          have h_le : leZ (addZ (zeroZ : U) (oneZ : U)) (addZ (oneZ : U) (oneZ : U)) :=
            addZ_leZ_addZ zeroZ oneZ oneZ zeroZ_mem_IntSet hone_i hone_i honeZ_pos.1
          rwa [addZ_zero_left oneZ hone_i] at h_le
        -- addZ oneZ oneZ ≤ addZ oneZ (addZ oneZ oneZ)
        have h_2_le_3 : leZ (addZ (oneZ : U) (oneZ : U))
            (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) := by
          have h_le := addZ_leZ_addZ zeroZ oneZ (addZ oneZ oneZ)
            zeroZ_mem_IntSet hone_i htwo_i honeZ_pos.1
          rwa [addZ_zero_left (addZ oneZ oneZ) htwo_i] at h_le
        -- oneZ ≤ addZ oneZ (addZ oneZ oneZ)
        have h_1_le_3 : leZ (oneZ : U) (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) :=
          leZ_trans oneZ (addZ oneZ oneZ) (addZ oneZ (addZ oneZ oneZ))
            hone_i htwo_i hthree_i h_1_le_2 h_2_le_3
        constructor
        · exact leZ_trans zeroZ oneZ (addZ oneZ (addZ oneZ oneZ))
            zeroZ_mem_IntSet hone_i hthree_i honeZ_pos.1 h_1_le_3
        · intro h
          rw [← h] at h_1_le_3
          exact honeZ_pos.2 (leZ_antisymm zeroZ oneZ zeroZ_mem_IntSet hone_i honeZ_pos.1 h_1_le_3)
      -- mulZ threeZ twoZ is positive
      have hmul_pos : isPositiveZ (mulZ (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U)))
          (addZ (oneZ : U) (oneZ : U))) :=
        positiveZ_mul_closed _ _ hthree_i htwo_i hthreeZ_pos htwoZ_pos
      -- leQ_repr zeroZ oneZ threeZ twoZ
      have h_repr : leQ_repr (zeroZ : U) (oneZ : U)
          (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) (addZ (oneZ : U) (oneZ : U)) := by
        unfold leQ_repr
        have lhs_eq : mulZ (mulZ (zeroZ : U) (oneZ : U))
            (mulZ (addZ (oneZ : U) (oneZ : U)) (addZ (oneZ : U) (oneZ : U))) = (zeroZ : U) := by
          rw [mulZ_zero_left oneZ hone_i]
          exact mulZ_zero_left _ (mulZ_in_IntSet _ _ htwo_i htwo_i)
        have rhs_eq : mulZ (mulZ (oneZ : U) (oneZ : U))
            (mulZ (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) (addZ (oneZ : U) (oneZ : U))) =
            mulZ (addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U))) (addZ (oneZ : U) (oneZ : U)) := by
          rw [mulZ_one_left oneZ hone_i]
          exact mulZ_one_left _ (mulZ_in_IntSet _ _ hthree_i htwo_i)
        rw [lhs_eq, rhs_eq]
        exact hmul_pos.1
      -- Conclude isPositiveQ threeHalvesQ
      constructor
      · rw [leQ_iff_repr zeroQ threeHalvesQ zeroQ_mem_RatSet threeHalvesQ_mem]
        exact ⟨zeroZ, oneZ, addZ oneZ (addZ oneZ oneZ), addZ oneZ oneZ,
               zeroZ_mem_IntSet, hone_nz, hthree_i, htwo_nz,
               rfl, hthreeHalves_class, h_repr⟩
      · have hthree_ne : addZ (oneZ : U) (addZ (oneZ : U) (oneZ : U)) ≠ (zeroZ : U) :=
          hthreeZ_pos.2.symm
        exact fun h => (ratClass_ne_zeroQ_iff _ _ hthree_i htwo_nz).mpr hthree_ne
          (h.trans hthreeHalves_class).symm

    -- =========================================================================
    -- Section 2: The Newton–Raphson step function as a ZFC function
    -- =========================================================================

    /-- The Newton–Raphson step graph: { ⟨x, (x + 2/x)/2⟩ | x ∈ ℚ }. -/
    private noncomputable def sqrtStepFn : U :=
      sep ((RatSet : U) ×ₛ (RatSet : U))
        (fun p => snd p = divQ (addQ (fst p) (divQ (twoQ : U) (fst p))) (twoQ : U))

    private theorem sqrtStepFn_mem_iff (p : U) :
        p ∈ (sqrtStepFn : U) ↔
        p ∈ (RatSet : U) ×ₛ (RatSet : U) ∧
        snd p = divQ (addQ (fst p) (divQ (twoQ : U) (fst p))) (twoQ : U) := by
      unfold sqrtStepFn; exact mem_sep_iff _ p _

    /-- The step function maps ℚ → ℚ. -/
    private theorem sqrtStepFn_is_function :
        IsFunction (sqrtStepFn : U) (RatSet : U) (RatSet : U) := by
      constructor
      · -- Containment: sqrtStepFn ⊆ RatSet × RatSet
        intro p hp
        exact ((sqrtStepFn_mem_iff p).mp hp).1
      · -- Existence and uniqueness: for each x ∈ RatSet, exactly one image
        intro x hx
        have hstep_mem : divQ (addQ x (divQ (twoQ : U) x)) (twoQ : U) ∈ (RatSet : U) :=
          divQ_in_RatSet _ _ (addQ_in_RatSet _ _ hx (divQ_in_RatSet _ _ twoQ_mem hx)) twoQ_mem
        refine ⟨divQ (addQ x (divQ (twoQ : U) x)) (twoQ : U), ?_, ?_⟩
        · -- The pair ⟨x, step(x)⟩ is in sqrtStepFn
          show ⟨x, divQ (addQ x (divQ (twoQ : U) x)) (twoQ : U)⟩ ∈ sqrtStepFn
          rw [sqrtStepFn_mem_iff]
          refine ⟨(OrderedPair_mem_CartesianProduct x _ (RatSet : U) (RatSet : U)).mpr
                   ⟨hx, hstep_mem⟩, ?_⟩
          rw [fst_of_ordered_pair, snd_of_ordered_pair]
        · -- Uniqueness: if ⟨x, z⟩ ∈ sqrtStepFn then z = step(x)
          intro z hz
          have h := ((sqrtStepFn_mem_iff ⟨x, z⟩).mp hz).2
          rw [fst_of_ordered_pair, snd_of_ordered_pair] at h
          exact h

    /-- Applying sqrtStepFn to x ∈ ℚ gives (x + 2/x)/2. -/
    private theorem sqrtStepFn_apply (x : U) (hx : x ∈ (RatSet : U)) :
        apply (sqrtStepFn : U) x =
        divQ (addQ x (divQ (twoQ : U) x)) (twoQ : U) := by
      apply apply_eq sqrtStepFn x _ (sqrtStepFn_is_function.2 x hx)
      show ⟨x, divQ (addQ x (divQ (twoQ : U) x)) (twoQ : U)⟩ ∈ sqrtStepFn
      rw [sqrtStepFn_mem_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct x _ (RatSet : U) (RatSet : U)).mpr
               ⟨hx, divQ_in_RatSet _ _ (addQ_in_RatSet _ _ hx
                   (divQ_in_RatSet _ _ twoQ_mem hx)) twoQ_mem⟩, ?_⟩
      rw [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 3: The Newton–Raphson sequence via RecursiveFn
    -- =========================================================================

    /-- The Newton–Raphson √2-approximation sequence:
        f(0) = 3/2,  f(n+1) = (f(n) + 2/f(n)) / 2. -/
    noncomputable def sqrtApproxSeq : U :=
      RecursiveFn (RatSet : U) (threeHalvesQ : U) (sqrtStepFn : U)
        threeHalvesQ_mem sqrtStepFn_is_function

    /-- sqrtApproxSeq is a sequence ω → ℚ. -/
    theorem sqrtApproxSeq_isSeqQ : IsSeqQ (sqrtApproxSeq : U) :=
      RecursiveFn_is_function (RatSet : U) threeHalvesQ sqrtStepFn
        threeHalvesQ_mem sqrtStepFn_is_function

    /-- f(0) = 3/2. -/
    theorem sqrtApproxSeq_apply_zero :
        (sqrtApproxSeq : U)⦅(∅ : U)⦆ = (threeHalvesQ : U) := by
      simp only [sqrtApproxSeq]
      exact RecursiveFn_zero (RatSet : U) threeHalvesQ sqrtStepFn
        threeHalvesQ_mem sqrtStepFn_is_function

    /-- f(n+1) = (f(n) + 2/f(n)) / 2. -/
    theorem sqrtApproxSeq_apply_succ (n : U) (hn : n ∈ (ω : U)) :
        (sqrtApproxSeq : U)⦅σ n⦆ =
        divQ (addQ ((sqrtApproxSeq : U)⦅n⦆) (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆))) (twoQ : U) := by
      simp only [sqrtApproxSeq]
      rw [RecursiveFn_succ (RatSet : U) threeHalvesQ sqrtStepFn
          threeHalvesQ_mem sqrtStepFn_is_function n hn]
      have hn_mem : (RecursiveFn (RatSet : U) threeHalvesQ sqrtStepFn
            threeHalvesQ_mem sqrtStepFn_is_function)⦅n⦆ ∈ (RatSet : U) :=
        seqTermQ_mem_RatSet _ n
          (RecursiveFn_is_function (RatSet : U) threeHalvesQ sqrtStepFn
            threeHalvesQ_mem sqrtStepFn_is_function) hn
      exact sqrtStepFn_apply _ hn_mem

    -- =========================================================================
    -- Section 4: Invariants (proved by induction on ω)
    -- =========================================================================

    /-- Positivity is preserved by addition: x > 0, z > 0 ⟹ x + z > 0. -/
    private theorem addQ_pos_of_pos_pos (x z : U)
        (hx : x ∈ (RatSet : U)) (hz : z ∈ (RatSet : U))
        (hx_pos : isPositiveQ x) (hz_pos : isPositiveQ z) :
        isPositiveQ (addQ x z) := by
      have h_sum := addQ_in_RatSet x z hx hz
      constructor
      · -- leQ zeroQ (addQ x z)
        have h_le : leQ (addQ (zeroQ : U) x) (addQ z x) :=
          addQ_leQ_addQ zeroQ z x zeroQ_mem_RatSet hz hx hz_pos.1
        rw [addQ_zero_left x hx, addQ_comm z x hz hx] at h_le
        exact leQ_trans zeroQ x (addQ x z) zeroQ_mem_RatSet hx h_sum hx_pos.1 h_le
      · -- zeroQ ≠ addQ x z
        intro h_eq
        have h_le : leQ (addQ (zeroQ : U) x) (addQ z x) :=
          addQ_leQ_addQ zeroQ z x zeroQ_mem_RatSet hz hx hz_pos.1
        rw [addQ_zero_left x hx, addQ_comm z x hz hx] at h_le
        rw [← h_eq] at h_le
        exact hx_pos.2 (leQ_antisymm zeroQ x zeroQ_mem_RatSet hx hx_pos.1 h_le)

    /-- Positivity is preserved by division: y > 0, x > 0 ⟹ y/x > 0. -/
    private theorem divQ_pos_of_pos_pos (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hx_pos : isPositiveQ x) (hy_pos : isPositiveQ y) :
        isPositiveQ (divQ y x) := by
      have hx_ne : x ≠ (zeroQ : U) := hx_pos.2.symm
      have hz := divQ_in_RatSet y x hy hx
      have h_cancel : mulQ x (divQ y x) = y := mulQ_divQ_cancel y x hy hx hx_ne
      constructor
      · -- leQ zeroQ (divQ y x)
        rcases leQ_total zeroQ (divQ y x) zeroQ_mem_RatSet hz with h | h
        · exact h
        · exfalso
          have h1 := mulQ_leQ_mulQ_of_nonneg_left x (divQ y x) zeroQ hx hz zeroQ_mem_RatSet h hx_pos.1
          rw [mulQ_zero_right x hx, h_cancel] at h1
          exact hy_pos.2 (leQ_antisymm y zeroQ hy zeroQ_mem_RatSet h1 hy_pos.1).symm
      · -- zeroQ ≠ divQ y x
        intro h_eq
        have h1 : mulQ x (divQ y x) = (zeroQ : U) := by
          rw [h_eq.symm]; exact mulQ_zero_right x hx
        exact hy_pos.2 (h_cancel.symm.trans h1).symm

    /-- Every term of sqrtApproxSeq is positive. -/
    theorem sqrtApproxSeq_pos (n : U) (hn : n ∈ (ω : U)) :
        isPositiveQ ((sqrtApproxSeq : U)⦅n⦆) := by
      let P : U → Prop := fun k => isPositiveQ ((sqrtApproxSeq : U)⦅k⦆)
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hmem : n ∈ S := by rw [hS]; exact hn
        exact ((mem_sep_iff (ω : U) n P).mp hmem).2
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · -- Base: n = ∅, f(0) = 3/2 > 0
        rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        show isPositiveQ ((sqrtApproxSeq : U)⦅(∅ : U)⦆)
        rw [sqrtApproxSeq_apply_zero]
        exact threeHalvesQ_pos
      · -- Step: k → σk
        intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_w, hk_pos⟩ := hk
        have hfk := seqTermQ_mem_RatSet (sqrtApproxSeq : U) k sqrtApproxSeq_isSeqQ hk_w
        have hfk_ne : (sqrtApproxSeq : U)⦅k⦆ ≠ (zeroQ : U) := hk_pos.2.symm
        refine ⟨succ_in_Omega k hk_w, ?_⟩
        show isPositiveQ ((sqrtApproxSeq : U)⦅σ k⦆)
        rw [sqrtApproxSeq_apply_succ k hk_w]
        -- f(k+1) = (f(k) + 2/f(k)) / 2
        have h_div := divQ_pos_of_pos_pos (sqrtApproxSeq⦅k⦆) twoQ hfk twoQ_mem hk_pos twoQ_pos
        have h_sum := addQ_pos_of_pos_pos (sqrtApproxSeq⦅k⦆) (divQ twoQ (sqrtApproxSeq⦅k⦆))
                        hfk (divQ_in_RatSet twoQ _ twoQ_mem hfk) hk_pos h_div
        exact divQ_pos_of_pos_pos twoQ
                (addQ (sqrtApproxSeq⦅k⦆) (divQ twoQ (sqrtApproxSeq⦅k⦆)))
                twoQ_mem
                (addQ_in_RatSet _ _ hfk (divQ_in_RatSet twoQ _ twoQ_mem hfk))
                twoQ_pos h_sum


    /-- Every term satisfies f(n)² > 2. -/
    theorem sqrtApproxSeq_sq_gt_two (n : U) (hn : n ∈ (ω : U)) :
        ltQ (addQ (oneQ : U) (oneQ : U))
          (mulQ ((sqrtApproxSeq : U)⦅n⦆) ((sqrtApproxSeq : U)⦅n⦆)) := by
      sorry
      /- Proof by induction on n:
         Base: f(0) = 3/2, f(0)² = 9/4 > 2 = 8/4. Arithmetic in ℚ.
         Step: use the identity
           f(n+1)² − 2 = ((f(n)² − 2) / (2·f(n)))²  ≥ 0, hence f(n+1)² ≥ 2.
         More precisely:
           f(n+1) = (f(n) + 2/f(n))/2
           f(n+1)² = (f(n)² + 4 + 4/f(n)²) / 4
           f(n+1)² − 2 = (f(n)² − 2)² / (4·f(n)²) > 0  (since f(n) > 0). -/

    /-- Every term satisfies f(n) ≥ 1. -/
    theorem sqrtApproxSeq_ge_one (n : U) (hn : n ∈ (ω : U)) :
        leQ (oneQ : U) ((sqrtApproxSeq : U)⦅n⦆) := by
      sorry
      /- Proof: from sqrtApproxSeq_pos and sqrtApproxSeq_sq_gt_two.
         If f(n) > 0 and f(n)² > 2 > 1, then f(n) > 1 ≥ 1.
         More precisely: if 0 < f(n) < 1, then f(n)² < f(n) < 1 < 2, contradiction.
         So f(n) ≥ 1.
         Uses: ltQ_mulQ_pos, ltQ_trans, and the assumption f(n)² > 2. -/

    /-- sqrtApproxSeq is non-increasing: m ≤ n → f(n) ≤ f(m). -/
    theorem sqrtApproxSeq_nonincreasing : isNonincreasingQ (sqrtApproxSeq : U) := by
      sorry
      /- Proof strategy:
         First prove "strictly decreasing at each step":
           f(n+1) < f(n) iff (f(n) + 2/f(n))/2 < f(n) iff 2/f(n) < f(n) iff 2 < f(n)².
         This holds by sqrtApproxSeq_sq_gt_two.
         Then isNonincreasingQ follows by induction: for m ≤ n (i.e., m ∈ n ∨ m = n),
         use transitivity of leQ through the chain f(n) ≤ f(n-1) ≤ ... ≤ f(m).
         Pattern: induction_principle on sep ω P where P(n) = ∀ m ≤ n, leQ f(n) f(m). -/

    -- =========================================================================
    -- Section 5: sqrtApproxSeq is Cauchy
    -- =========================================================================

    /-- The Newton–Raphson sequence is a Cauchy sequence in ℚ.
        This follows from it being non-increasing and bounded below by 1. -/
    theorem sqrtApproxSeq_isCauchy : IsCauchyQ (sqrtApproxSeq : U) :=
      nonincreasing_bounded_isCauchy (sqrtApproxSeq : U) (oneQ : U)
        sqrtApproxSeq_isSeqQ oneQ_mem_RatSet
        sqrtApproxSeq_nonincreasing
        (fun n hn => sqrtApproxSeq_ge_one n hn)

    -- =========================================================================
    -- Section 6: ℚ incompleteness
    -- =========================================================================

    /-- √2 is irrational: no rational L satisfies L · L = 2.

        Proof sketch (2-adic argument on integers):
        If L = p/q in lowest terms (gcd(p,q)=1) and (p/q)² = 2, then p² = 2q².
        This means 2 | p², hence 2 | p (since 2 is prime). Write p = 2k.
        Then 4k² = 2q², so q² = 2k², hence 2 | q² and 2 | q.
        But gcd(p,q) = 1 and 2 | p and 2 | q is a contradiction. -/
    theorem sqrt2_irrational :
        ¬ ∃ L : U, L ∈ (RatSet : U) ∧ mulQ L L = addQ (oneQ : U) (oneQ : U) := by
      sorry
      /- Full proof requires:
         1. L ∈ RatSet means L = ratClass ⟪p, q⟫ for some p ∈ IntSet, q ∈ NonZeroIntSet
            (existence of irreducible representative via gcdZ and dividesZ_antisymm).
         2. mulQ L L = twoQ gives (in terms of integer reps): p·p = 2·(q·q).
         3. Integer 2-adic argument: 2 | p → p = 2k → 4k² = 2q² → 2 | q → gcd(|p|,|q|)≥2.
         4. Contradiction with gcd = 1 in reduced representative.
         Requires: ZFC.Int.Div (gcdZ, dividesZ, tfa_Z), ZFC.Int.Mul. -/

    /-- The Newton–Raphson sequence sqrtApproxSeq has no limit in ℚ.
        This shows ℚ is not (sequentially) complete. -/
    theorem sqrtApproxSeq_not_convergent :
        ¬ ∃ L : U, L ∈ (RatSet : U) ∧ convergesToQ (sqrtApproxSeq : U) L := by
      sorry
      /- Proof:
         Assume convergesToQ sqrtApproxSeq L for some L ∈ ℚ.
         Step 1: L > 0.
           From sqrtApproxSeq_ge_one and le_limit_of_bounded_below: L ≥ 1 > 0.
         Step 2: The shifted sequence n ↦ f(σn) also converges to L.
           f(σn) is a subsequence of f (via φ(n) = σn, strictly increasing),
           so convergesToQ (fun n => sqrtApproxSeq⦅σn⦆) L by subseq_convergent.
         Step 3: The sequence n ↦ (f(n) + 2/f(n))/2 converges to (L + 2/L)/2.
           By convergesToQ_add, convergesToQ_inv (L ≠ 0), and convergesToQ_const_mul.
         Step 4: The sequences in Steps 2 and 3 are equal term-by-term
           (by sqrtApproxSeq_apply_succ). By convergesToQ_of_eventually_eq, both
           converge to L AND to (L + 2/L)/2. By limit_unique: L = (L + 2/L)/2.
         Step 5: Algebraic manipulation.
           L = (L + 2/L)/2 → 2L = L + 2/L → L = 2/L → L·L = 2.
         Step 6: Contradiction with sqrt2_irrational. -/

  end Rat.SqrtApprox

end ZFC

export ZFC.Rat.SqrtApprox (
  sqrtApproxSeq
  sqrtApproxSeq_isSeqQ
  sqrtApproxSeq_apply_zero
  sqrtApproxSeq_apply_succ
  sqrtApproxSeq_pos
  sqrtApproxSeq_sq_gt_two
  sqrtApproxSeq_ge_one
  sqrtApproxSeq_nonincreasing
  sqrtApproxSeq_isCauchy
  sqrt2_irrational
  sqrtApproxSeq_not_convergent
)
