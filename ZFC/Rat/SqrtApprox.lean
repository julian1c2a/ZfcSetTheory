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
    noncomputable def twoQ : U := addQ (oneQ : U) (oneQ : U)

    /-- 3 ∈ ℚ, defined as 1 + 2. -/
    private noncomputable def threeQ : U := addQ (oneQ : U) (twoQ : U)

    /-- 3/2 ∈ ℚ, the initial value f(0). -/
    private noncomputable def threeHalvesQ : U := divQ (threeQ : U) (twoQ : U)

    theorem twoQ_mem : (twoQ : U) ∈ (RatSet : U) :=
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

    theorem twoQ_ne_zeroQ : (twoQ : U) ≠ (zeroQ : U) := by
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

    theorem twoQ_pos : isPositiveQ (twoQ : U) := by
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

    /-- mulQ twoQ x = addQ x x  (porque twoQ = 1+1, distributividad por la derecha). -/
    private theorem mulQ_two_eq_addSelf (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ (twoQ : U) x = addQ x x := by
      show mulQ (addQ (oneQ : U) (oneQ : U)) x = addQ x x
      rw [mulQ_addQ_distrib_right (oneQ : U) (oneQ : U) x oneQ_mem_RatSet oneQ_mem_RatSet hx,
          mulQ_one_left x hx]

    /-- mulQ x twoQ = addQ x x. -/
    private theorem mulQ_two_eq_addSelf' (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ x (twoQ : U) = addQ x x := by
      rw [mulQ_comm x (twoQ : U) hx twoQ_mem]
      exact mulQ_two_eq_addSelf x hx

    /-- Producto de positivos es positivo. -/
    private theorem mulQ_pos_of_pos_pos (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (hx_pos : isPositiveQ x) (hy_pos : isPositiveQ y) :
        isPositiveQ (mulQ x y) := by
      have hxy := mulQ_in_RatSet x y hx hy
      constructor
      · have h := mulQ_leQ_mulQ_of_nonneg_right (zeroQ : U) x y
                    zeroQ_mem_RatSet hx hy hx_pos.1 hy_pos.1
        rwa [mulQ_zero_left y hy] at h
      · intro h_eq
        exact mulQ_ne_zeroQ x y hx hy hx_pos.2.symm hy_pos.2.symm h_eq.symm

    /-- Cuadrado de algo no nulo es positivo. -/
    private theorem mulQ_self_pos_of_ne_zero (x : U)
        (hx : x ∈ (RatSet : U)) (hx_ne : x ≠ (zeroQ : U)) :
        isPositiveQ (mulQ x x) := by
      have hxx := mulQ_in_RatSet x x hx hx
      have hxx_ne : mulQ x x ≠ (zeroQ : U) := mulQ_ne_zeroQ x x hx hx hx_ne hx_ne
      constructor
      · -- Caso por leQ_total: si zeroQ ≤ x, usar mulQ_leQ_mulQ_of_nonneg_right;
        -- si x ≤ zeroQ, usar negQ.
        rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h | h
        · have h1 := mulQ_leQ_mulQ_of_nonneg_right (zeroQ : U) x x
                       zeroQ_mem_RatSet hx hx h h
          rwa [mulQ_zero_left x hx] at h1
        · -- x ≤ 0, entonces -x ≥ 0, y x*x = (-x)*(-x) ≥ 0
          have h_neg_pos : leQ (zeroQ : U) (negQ x) := by
            have := addQ_leQ_addQ x (zeroQ : U) (negQ x) hx zeroQ_mem_RatSet
                      (negQ_in_RatSet x hx) h
            rwa [negQ_addQ_right x hx, addQ_zero_left (negQ x) (negQ_in_RatSet x hx)] at this
          have h2 := mulQ_leQ_mulQ_of_nonneg_right (zeroQ : U) (negQ x) (negQ x)
                       zeroQ_mem_RatSet (negQ_in_RatSet x hx) (negQ_in_RatSet x hx)
                       h_neg_pos h_neg_pos
          rw [mulQ_zero_left (negQ x) (negQ_in_RatSet x hx)] at h2
          -- (negQ x) * (negQ x) = x * x
          have h_eq : mulQ (negQ x) (negQ x) = mulQ x x := by
            rw [← negQ_mulQ_left x (negQ x) hx (negQ_in_RatSet x hx),
                ← negQ_mulQ_right x x hx hx]
            exact negQ_negQ (mulQ x x) hxx
          rwa [h_eq] at h2
      · exact fun h => hxx_ne h.symm

    /-- Identidad clave: para `x ∈ ℚ` con `x ≠ 0`, `mulQ twoQ (mulQ (invQ twoQ) x) = x`. -/
    private theorem mulQ_two_invTwo (x : U) (hx : x ∈ (RatSet : U)) :
        mulQ (twoQ : U) (mulQ (invQ (twoQ : U)) x) = x := by
      have hinv := invQ_in_RatSet (twoQ : U) twoQ_mem
      rw [← mulQ_assoc (twoQ : U) (invQ (twoQ : U)) x twoQ_mem hinv hx,
          mulQ_invQ_right (twoQ : U) twoQ_mem twoQ_ne_zeroQ,
          mulQ_one_left x hx]

    /-- Multiplicación por positivo preserva orden estricto (izquierda). -/
    private theorem mulQ_pos_ltQ_left (a b c : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U))
        (ha_pos : isPositiveQ a) (h : ltQ b c) : ltQ (mulQ a b) (mulQ a c) :=
      ⟨mulQ_leQ_mulQ_of_nonneg_left a b c ha hb hc h.1 ha_pos.1,
       fun h_eq => h.2 (mulQ_left_cancel b c a hb hc ha ha_pos.2.symm h_eq)⟩

    /-- Cancelación de positivo (izquierda) preservando ltQ. -/
    private theorem ltQ_of_mulQ_pos_ltQ_left (a b c : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U))
        (ha_pos : isPositiveQ a) (h : ltQ (mulQ a b) (mulQ a c)) : ltQ b c := by
      refine ⟨?_, fun heq => h.2 (by rw [heq])⟩
      rcases leQ_total b c hb hc with hbc | hcb
      · exact hbc
      · exfalso
        have h_le : leQ (mulQ a c) (mulQ a b) :=
          mulQ_leQ_mulQ_of_nonneg_left a c b ha hc hb hcb ha_pos.1
        exact h.2 (leQ_antisymm (mulQ a b) (mulQ a c)
          (mulQ_in_RatSet a b ha hb) (mulQ_in_RatSet a c ha hc) h.1 h_le)

    /-- Every term satisfies f(n)² > 2. -/
    theorem sqrtApproxSeq_sq_gt_two (n : U) (hn : n ∈ (ω : U)) :
        ltQ (addQ (oneQ : U) (oneQ : U))
          (mulQ ((sqrtApproxSeq : U)⦅n⦆) ((sqrtApproxSeq : U)⦅n⦆)) := by
      let P : U → Prop := fun k => ltQ (addQ (oneQ : U) (oneQ : U))
                                        (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hmem : n ∈ S := by rw [hS]; exact hn
        exact ((mem_sep_iff (ω : U) n P).mp hmem).2
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · -- Base: f(0) = threeHalvesQ. (3/2)² = 9/4 > 2 = 8/4.
        -- Proof: write threeHalvesQ = 1 + h, then (1+h)² = 2 + h², and h² > 0.
        rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        show ltQ (addQ oneQ oneQ) (mulQ (sqrtApproxSeq⦅(∅ : U)⦆) (sqrtApproxSeq⦅(∅ : U)⦆))
        rw [sqrtApproxSeq_apply_zero]
        -- Set h = 1/2
        have hh : invQ (twoQ : U) ∈ (RatSet : U) := invQ_in_RatSet (twoQ : U) twoQ_mem
        have hh_pos : isPositiveQ (invQ (twoQ : U)) := invQ_pos (twoQ : U) twoQ_mem twoQ_pos
        have hh_ne : invQ (twoQ : U) ≠ (zeroQ : U) := hh_pos.2.symm
        have h_2h : mulQ (twoQ : U) (invQ (twoQ : U)) = (oneQ : U) :=
          mulQ_invQ_right (twoQ : U) twoQ_mem twoQ_ne_zeroQ
        have h_hh : addQ (invQ (twoQ : U)) (invQ (twoQ : U)) = (oneQ : U) := by
          rw [← mulQ_two_eq_addSelf (invQ (twoQ : U)) hh]; exact h_2h
        -- threeHalvesQ = 1 + h
        have h_3h : (threeHalvesQ : U) = addQ (oneQ : U) (invQ (twoQ : U)) := by
          show divQ (threeQ : U) (twoQ : U) = addQ (oneQ : U) (invQ (twoQ : U))
          show mulQ (threeQ : U) (invQ (twoQ : U)) = addQ (oneQ : U) (invQ (twoQ : U))
          show mulQ (addQ (oneQ : U) (twoQ : U)) (invQ (twoQ : U)) = addQ (oneQ : U) (invQ (twoQ : U))
          rw [mulQ_addQ_distrib_right (oneQ : U) (twoQ : U) (invQ (twoQ : U))
                oneQ_mem_RatSet twoQ_mem hh,
              mulQ_one_left (invQ (twoQ : U)) hh, h_2h,
              addQ_comm (invQ (twoQ : U)) (oneQ : U) hh oneQ_mem_RatSet]
        -- (1 + h)² = 2 + h² (algebraic identity)
        have hone_h : addQ (oneQ : U) (invQ (twoQ : U)) ∈ (RatSet : U) :=
          addQ_in_RatSet (oneQ : U) (invQ (twoQ : U)) oneQ_mem_RatSet hh
        have hh_h : mulQ (invQ (twoQ : U)) (invQ (twoQ : U)) ∈ (RatSet : U) :=
          mulQ_in_RatSet (invQ (twoQ : U)) (invQ (twoQ : U)) hh hh
        have hsq : mulQ (threeHalvesQ : U) (threeHalvesQ : U) =
            addQ (twoQ : U) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) := by
          show mulQ (threeHalvesQ : U) (threeHalvesQ : U) =
            addQ (addQ (oneQ : U) (oneQ : U)) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U)))
          rw [h_3h,
              mulQ_addQ_distrib_left (addQ (oneQ : U) (invQ (twoQ : U))) (oneQ : U) (invQ (twoQ : U))
                hone_h oneQ_mem_RatSet hh,
              mulQ_one_right (addQ (oneQ : U) (invQ (twoQ : U))) hone_h,
              mulQ_addQ_distrib_right (oneQ : U) (invQ (twoQ : U)) (invQ (twoQ : U))
                oneQ_mem_RatSet hh hh,
              mulQ_one_left (invQ (twoQ : U)) hh,
              addQ_assoc (oneQ : U) (invQ (twoQ : U))
                (addQ (invQ (twoQ : U)) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))))
                oneQ_mem_RatSet hh
                (addQ_in_RatSet (invQ (twoQ : U)) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) hh hh_h),
              ← addQ_assoc (invQ (twoQ : U)) (invQ (twoQ : U))
                (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) hh hh hh_h,
              h_hh,
              ← addQ_assoc (oneQ : U) (oneQ : U) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U)))
                oneQ_mem_RatSet oneQ_mem_RatSet hh_h]
        rw [hsq]
        -- Now: ltQ twoQ (addQ twoQ (h*h)). h*h > 0 since h ≠ 0.
        have hh_h_pos : isPositiveQ (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) :=
          mulQ_self_pos_of_ne_zero (invQ (twoQ : U)) hh hh_ne
        refine ⟨?_, ?_⟩
        · -- leQ twoQ (twoQ + h*h)
          have step := addQ_leQ_addQ (zeroQ : U) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U)))
            (twoQ : U) zeroQ_mem_RatSet hh_h twoQ_mem hh_h_pos.1
          rw [addQ_zero_left (twoQ : U) twoQ_mem,
              addQ_comm (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) (twoQ : U) hh_h twoQ_mem] at step
          exact step
        · -- twoQ ≠ twoQ + h*h
          intro h_eq
          have h_zero : mulQ (invQ (twoQ : U)) (invQ (twoQ : U)) = (zeroQ : U) := by
            have step : addQ (negQ (twoQ : U)) (twoQ : U) =
                addQ (negQ (twoQ : U)) (addQ (twoQ : U) (mulQ (invQ (twoQ : U)) (invQ (twoQ : U)))) :=
              congrArg (fun y => addQ (negQ (twoQ : U)) y) h_eq
            rw [negQ_addQ_left (twoQ : U) twoQ_mem,
                ← addQ_assoc (negQ (twoQ : U)) (twoQ : U)
                  (mulQ (invQ (twoQ : U)) (invQ (twoQ : U)))
                  (negQ_in_RatSet (twoQ : U) twoQ_mem) twoQ_mem hh_h,
                negQ_addQ_left (twoQ : U) twoQ_mem,
                addQ_zero_left (mulQ (invQ (twoQ : U)) (invQ (twoQ : U))) hh_h] at step
            exact step.symm
          exact hh_h_pos.2 h_zero.symm
      · -- Inductive step
        intro k hk_S
        rw [mem_sep_iff] at hk_S ⊢
        obtain ⟨hk, hk_sq⟩ := hk_S
        refine ⟨succ_in_Omega k hk, ?_⟩
        -- IH hk_sq: 2 < f(k)²
        let fk : U := (sqrtApproxSeq : U)⦅k⦆
        have hfk : fk ∈ (RatSet : U) := seqTermQ_mem_RatSet sqrtApproxSeq k sqrtApproxSeq_isSeqQ hk
        have hfk_pos : isPositiveQ fk := sqrtApproxSeq_pos k hk
        have hfk_ne : fk ≠ (zeroQ : U) := hfk_pos.2.symm
        have hfk_inv := invQ_in_RatSet fk hfk
        -- a = h*fk, b = invQ fk
        have hh : invQ (twoQ : U) ∈ (RatSet : U) := invQ_in_RatSet (twoQ : U) twoQ_mem
        have hh_ne : invQ (twoQ : U) ≠ (zeroQ : U) :=
          (invQ_pos (twoQ : U) twoQ_mem twoQ_pos).2.symm
        have h_2h : mulQ (twoQ : U) (invQ (twoQ : U)) = (oneQ : U) :=
          mulQ_invQ_right (twoQ : U) twoQ_mem twoQ_ne_zeroQ
        let a : U := mulQ (invQ (twoQ : U)) fk
        let b : U := invQ fk
        have ha : a ∈ (RatSet : U) := mulQ_in_RatSet (invQ (twoQ : U)) fk hh hfk
        have hb : b ∈ (RatSet : U) := hfk_inv
        -- f(σk) = a + b
        have h_fsk_eq : (sqrtApproxSeq : U)⦅σ k⦆ = addQ a b := by
          rw [sqrtApproxSeq_apply_succ k hk]
          show divQ (addQ fk (divQ (twoQ : U) fk)) (twoQ : U) = addQ a b
          show mulQ (addQ fk (divQ (twoQ : U) fk)) (invQ (twoQ : U)) = addQ a b
          rw [mulQ_addQ_distrib_right fk (divQ (twoQ : U) fk) (invQ (twoQ : U)) hfk
                (divQ_in_RatSet (twoQ : U) fk twoQ_mem hfk) hh,
              mulQ_comm fk (invQ (twoQ : U)) hfk hh]
          show addQ a (mulQ (mulQ (twoQ : U) (invQ fk)) (invQ (twoQ : U))) = addQ a b
          rw [mulQ_assoc (twoQ : U) (invQ fk) (invQ (twoQ : U)) twoQ_mem hfk_inv hh,
              mulQ_comm (invQ fk) (invQ (twoQ : U)) hfk_inv hh,
              ← mulQ_assoc (twoQ : U) (invQ (twoQ : U)) (invQ fk) twoQ_mem hh hfk_inv,
              h_2h, mulQ_one_left (invQ fk) hfk_inv]
        -- a*b = h
        have h_ab_eq : mulQ a b = invQ (twoQ : U) := by
          show mulQ (mulQ (invQ (twoQ : U)) fk) (invQ fk) = invQ (twoQ : U)
          rw [mulQ_assoc (invQ (twoQ : U)) fk (invQ fk) hh hfk hfk_inv,
              mulQ_invQ_right fk hfk hfk_ne,
              mulQ_one_right (invQ (twoQ : U)) hh]
        -- 2*(a*b) = 1
        have h_2ab : mulQ (twoQ : U) (mulQ a b) = (oneQ : U) := by rw [h_ab_eq]; exact h_2h
        -- (a+b)+(a+b) = (a+b)+(a+b) ... actually we just need (ab+ab) = 1
        have h_abab : addQ (mulQ a b) (mulQ a b) = (oneQ : U) := by
          rw [← mulQ_two_eq_addSelf (mulQ a b) (mulQ_in_RatSet a b ha hb)]
          exact h_2ab
        -- Helper: (a+b)*(a+b) = aa + bb + 1
        have hab := mulQ_in_RatSet a b ha hb
        have haa := mulQ_in_RatSet a a ha ha
        have hbb := mulQ_in_RatSet b b hb hb
        have h_lhs : mulQ (addQ a b) (addQ a b) =
            addQ (addQ (mulQ a a) (mulQ b b)) (oneQ : U) := by
          rw [mulQ_addQ_distrib_left (addQ a b) a b (addQ_in_RatSet a b ha hb) ha hb,
              mulQ_addQ_distrib_right a b a ha hb ha,
              mulQ_addQ_distrib_right a b b ha hb hb,
              mulQ_comm b a hb ha]
          -- (aa + ab) + (ab + bb) = aa + ab + ab + bb
          rw [addQ_assoc (mulQ a a) (mulQ a b) (addQ (mulQ a b) (mulQ b b))
                haa hab (addQ_in_RatSet (mulQ a b) (mulQ b b) hab hbb),
              ← addQ_assoc (mulQ a b) (mulQ a b) (mulQ b b) hab hab hbb,
              h_abab,
              addQ_comm (oneQ : U) (mulQ b b) oneQ_mem_RatSet hbb,
              ← addQ_assoc (mulQ a a) (mulQ b b) (oneQ : U) haa hbb oneQ_mem_RatSet]
        -- Helper: (a-b)*(a-b) = aa + bb + (-1)
        have h_rhs_subQ : mulQ (subQ a b) (subQ a b) =
            addQ (addQ (mulQ a a) (mulQ b b)) (negQ (oneQ : U)) := by
          show mulQ (addQ a (negQ b)) (addQ a (negQ b)) = _
          rw [mulQ_addQ_distrib_left (addQ a (negQ b)) a (negQ b)
                (addQ_in_RatSet a (negQ b) ha (negQ_in_RatSet b hb)) ha (negQ_in_RatSet b hb),
              mulQ_addQ_distrib_right a (negQ b) a ha (negQ_in_RatSet b hb) ha,
              mulQ_addQ_distrib_right a (negQ b) (negQ b) ha (negQ_in_RatSet b hb) (negQ_in_RatSet b hb),
              mulQ_comm (negQ b) a (negQ_in_RatSet b hb) ha,
              ← negQ_mulQ_right a b ha hb,
              ← negQ_mulQ_left b (negQ b) hb (negQ_in_RatSet b hb),
              ← negQ_mulQ_right b b hb hb,
              negQ_negQ (mulQ b b) hbb]
          -- (aa + (-ab)) + ((-ab) + bb)
          rw [addQ_assoc (mulQ a a) (negQ (mulQ a b)) (addQ (negQ (mulQ a b)) (mulQ b b))
                haa (negQ_in_RatSet (mulQ a b) hab)
                (addQ_in_RatSet (negQ (mulQ a b)) (mulQ b b) (negQ_in_RatSet (mulQ a b) hab) hbb),
              ← addQ_assoc (negQ (mulQ a b)) (negQ (mulQ a b)) (mulQ b b)
                (negQ_in_RatSet (mulQ a b) hab) (negQ_in_RatSet (mulQ a b) hab) hbb]
          -- now: aa + ((-ab + -ab) + bb)
          -- want to show -ab + -ab = -1
          have h_neg_abab : addQ (negQ (mulQ a b)) (negQ (mulQ a b)) = negQ (oneQ : U) := by
            -- (-ab) + (-ab) = -(ab+ab) = -1
            have h_ne_ab := negQ_in_RatSet (mulQ a b) hab
            have h_neg_pair : addQ (negQ (mulQ a b)) (negQ (mulQ a b)) ∈ (RatSet : U) :=
              addQ_in_RatSet _ _ h_ne_ab h_ne_ab
            have hcancel : addQ (oneQ : U) (addQ (negQ (mulQ a b)) (negQ (mulQ a b))) = (zeroQ : U) := by
              rw [← h_abab,
                  addQ_assoc (mulQ a b) (mulQ a b) (addQ (negQ (mulQ a b)) (negQ (mulQ a b)))
                    hab hab h_neg_pair,
                  ← addQ_assoc (mulQ a b) (negQ (mulQ a b)) (negQ (mulQ a b))
                    hab h_ne_ab h_ne_ab,
                  negQ_addQ_right (mulQ a b) hab,
                  addQ_zero_left (negQ (mulQ a b)) h_ne_ab,
                  negQ_addQ_right (mulQ a b) hab]
            -- From 1 + (-ab + -ab) = 0, conclude -ab + -ab = -1.
            -- Step: (-ab)+(-ab) = 0 + ((-ab)+(-ab)) = (-1 + 1) + ... = -1 + (1 + ((-ab)+(-ab))) = -1 + 0 = -1
            calc addQ (negQ (mulQ a b)) (negQ (mulQ a b))
                = addQ (zeroQ : U) (addQ (negQ (mulQ a b)) (negQ (mulQ a b))) :=
                    (addQ_zero_left _ h_neg_pair).symm
              _ = addQ (addQ (negQ (oneQ : U)) (oneQ : U))
                    (addQ (negQ (mulQ a b)) (negQ (mulQ a b))) := by
                    rw [negQ_addQ_left (oneQ : U) oneQ_mem_RatSet]
              _ = addQ (negQ (oneQ : U)) (addQ (oneQ : U)
                    (addQ (negQ (mulQ a b)) (negQ (mulQ a b)))) := by
                    rw [addQ_assoc (negQ (oneQ : U)) (oneQ : U)
                        (addQ (negQ (mulQ a b)) (negQ (mulQ a b)))
                        (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet) oneQ_mem_RatSet h_neg_pair]
              _ = addQ (negQ (oneQ : U)) (zeroQ : U) := by rw [hcancel]
              _ = negQ (oneQ : U) := addQ_zero_right _ (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet)
          rw [h_neg_abab,
              addQ_comm (negQ (oneQ : U)) (mulQ b b)
                (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet) hbb,
              ← addQ_assoc (mulQ a a) (mulQ b b) (negQ (oneQ : U)) haa hbb
                (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet)]
        -- Combine: 2 + (a-b)² = 2 + (aa + bb + (-1)) = (aa + bb) + (2 + (-1)) = (aa + bb) + 1 = (a+b)²
        have h_2_neg1 : addQ (twoQ : U) (negQ (oneQ : U)) = (oneQ : U) := by
          show addQ (addQ (oneQ : U) (oneQ : U)) (negQ (oneQ : U)) = (oneQ : U)
          rw [addQ_assoc (oneQ : U) (oneQ : U) (negQ (oneQ : U)) oneQ_mem_RatSet oneQ_mem_RatSet
                (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet),
              negQ_addQ_right (oneQ : U) oneQ_mem_RatSet,
              addQ_zero_right (oneQ : U) oneQ_mem_RatSet]
        have hX := addQ_in_RatSet (mulQ a a) (mulQ b b) haa hbb
        have hab_sq : mulQ (addQ a b) (addQ a b) =
            addQ (twoQ : U) (mulQ (subQ a b) (subQ a b)) := by
          rw [h_lhs, h_rhs_subQ,
              ← addQ_assoc (twoQ : U) (addQ (mulQ a a) (mulQ b b)) (negQ (oneQ : U))
                twoQ_mem hX (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet),
              addQ_comm (twoQ : U) (addQ (mulQ a a) (mulQ b b)) twoQ_mem hX,
              addQ_assoc (addQ (mulQ a a) (mulQ b b)) (twoQ : U) (negQ (oneQ : U))
                hX twoQ_mem (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet),
              h_2_neg1]
        show ltQ (addQ (oneQ : U) (oneQ : U))
               (mulQ ((sqrtApproxSeq : U)⦅σ k⦆) ((sqrtApproxSeq : U)⦅σ k⦆))
        rw [h_fsk_eq, hab_sq]
        -- Now we have ltQ twoQ (twoQ + (subQ a b)²)
        -- Need subQ a b ≠ 0, equivalently a ≠ b, i.e., h*fk ≠ invQ fk
        -- which is fk² ≠ twoQ (cross-multiply by fk and twoQ).
        have h_a_ne_b : a ≠ b := by
          intro h_eq
          -- a = b → fk*a = fk*b → fk*(h*fk) = fk*(invQ fk) = 1
          --       → h*(fk*fk) = 1 → fk*fk = twoQ (multiply by twoQ)
          -- contradicting hk_sq.2
          have h1 : mulQ fk a = mulQ fk b := congrArg (mulQ fk) h_eq
          -- mulQ fk a = mulQ fk (mulQ h fk) = mulQ h (mulQ fk fk)
          have h2 : mulQ fk a = mulQ (invQ (twoQ : U)) (mulQ fk fk) := by
            show mulQ fk (mulQ (invQ (twoQ : U)) fk) = mulQ (invQ (twoQ : U)) (mulQ fk fk)
            rw [← mulQ_assoc fk (invQ (twoQ : U)) fk hfk hh hfk,
                mulQ_comm fk (invQ (twoQ : U)) hfk hh,
                mulQ_assoc (invQ (twoQ : U)) fk fk hh hfk hfk]
          have h3 : mulQ fk b = (oneQ : U) := mulQ_invQ_right fk hfk hfk_ne
          have h4 : mulQ (invQ (twoQ : U)) (mulQ fk fk) = (oneQ : U) := h2.symm.trans (h1.trans h3)
          -- Multiply both sides by twoQ on the left
          have h5 : mulQ (twoQ : U) (mulQ (invQ (twoQ : U)) (mulQ fk fk)) =
                    mulQ (twoQ : U) (oneQ : U) := congrArg (mulQ (twoQ : U)) h4
          rw [mulQ_two_invTwo (mulQ fk fk) (mulQ_in_RatSet fk fk hfk hfk),
              mulQ_one_right (twoQ : U) twoQ_mem] at h5
          -- h5 : mulQ fk fk = twoQ. But hk_sq.2 says twoQ ≠ mulQ fk fk
          exact hk_sq.2 h5.symm
        have h_sub_ne : subQ a b ≠ (zeroQ : U) := by
          intro h_eq
          apply h_a_ne_b
          calc a = addQ a (zeroQ : U) := (addQ_zero_right a ha).symm
            _ = addQ a (addQ (negQ b) b) := by rw [negQ_addQ_left b hb]
            _ = addQ (addQ a (negQ b)) b := by
                rw [← addQ_assoc a (negQ b) b ha (negQ_in_RatSet b hb) hb]
            _ = addQ (subQ a b) b := rfl
            _ = addQ (zeroQ : U) b := by rw [h_eq]
            _ = b := addQ_zero_left b hb
        have h_sub_mem : subQ a b ∈ (RatSet : U) := addQ_in_RatSet a (negQ b) ha (negQ_in_RatSet b hb)
        have h_sub_sq_pos : isPositiveQ (mulQ (subQ a b) (subQ a b)) :=
          mulQ_self_pos_of_ne_zero (subQ a b) h_sub_mem h_sub_ne
        have h_sub_sq_mem : mulQ (subQ a b) (subQ a b) ∈ (RatSet : U) :=
          mulQ_in_RatSet _ _ h_sub_mem h_sub_mem
        refine ⟨?_, ?_⟩
        · -- leQ twoQ (twoQ + (subQ a b)²)
          have step := addQ_leQ_addQ (zeroQ : U) (mulQ (subQ a b) (subQ a b)) (twoQ : U)
            zeroQ_mem_RatSet h_sub_sq_mem twoQ_mem h_sub_sq_pos.1
          rw [addQ_zero_left (twoQ : U) twoQ_mem,
              addQ_comm (mulQ (subQ a b) (subQ a b)) (twoQ : U) h_sub_sq_mem twoQ_mem] at step
          -- step : leQ twoQ (twoQ + (sub a b)²) but the goal has addQ oneQ oneQ in place of twoQ
          show leQ (addQ (oneQ : U) (oneQ : U)) (addQ (twoQ : U) (mulQ (subQ a b) (subQ a b)))
          exact step
        · intro h_eq
          have h_zero : mulQ (subQ a b) (subQ a b) = (zeroQ : U) := by
            have step : addQ (negQ (twoQ : U)) (twoQ : U) =
                addQ (negQ (twoQ : U)) (addQ (twoQ : U) (mulQ (subQ a b) (subQ a b))) :=
              congrArg (fun y => addQ (negQ (twoQ : U)) y) h_eq
            rw [negQ_addQ_left (twoQ : U) twoQ_mem,
                ← addQ_assoc (negQ (twoQ : U)) (twoQ : U) (mulQ (subQ a b) (subQ a b))
                  (negQ_in_RatSet (twoQ : U) twoQ_mem) twoQ_mem h_sub_sq_mem,
                negQ_addQ_left (twoQ : U) twoQ_mem,
                addQ_zero_left (mulQ (subQ a b) (subQ a b)) h_sub_sq_mem] at step
            exact step.symm
          exact h_sub_sq_pos.2 h_zero.symm

    /-- Every term satisfies f(n) ≥ 1. -/
    theorem sqrtApproxSeq_ge_one (n : U) (hn : n ∈ (ω : U)) :
        leQ (oneQ : U) ((sqrtApproxSeq : U)⦅n⦆) := by
      let x : U := (sqrtApproxSeq : U)⦅n⦆
      have hx : x ∈ (RatSet : U) :=
        seqTermQ_mem_RatSet sqrtApproxSeq n sqrtApproxSeq_isSeqQ hn
      have hx_pos : isPositiveQ x := sqrtApproxSeq_pos n hn
      have hxx_gt_two : ltQ (addQ (oneQ : U) (oneQ : U)) (mulQ x x) :=
        sqrtApproxSeq_sq_gt_two n hn
      have hxx_mem : mulQ x x ∈ (RatSet : U) := mulQ_in_RatSet x x hx hx
      have h11 : addQ (oneQ : U) (oneQ : U) ∈ (RatSet : U) :=
        addQ_in_RatSet (oneQ : U) (oneQ : U) oneQ_mem_RatSet oneQ_mem_RatSet
      -- 1 < 1+1
      have h_one_lt_two : ltQ (oneQ : U) (addQ (oneQ : U) (oneQ : U)) := by
        refine ⟨?_, ?_⟩
        · have step := addQ_leQ_addQ (zeroQ : U) (oneQ : U) (oneQ : U) zeroQ_mem_RatSet
            oneQ_mem_RatSet oneQ_mem_RatSet oneQ_pos.1
          rw [addQ_zero_left (oneQ : U) oneQ_mem_RatSet,
              addQ_comm (oneQ : U) (oneQ : U) oneQ_mem_RatSet oneQ_mem_RatSet] at step
          exact step
        · intro h_eq
          have h_zero : (oneQ : U) = (zeroQ : U) := by
            have step : addQ (negQ (oneQ : U)) (oneQ : U) =
                addQ (negQ (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
              congrArg (fun y => addQ (negQ (oneQ : U)) y) h_eq
            rw [negQ_addQ_left (oneQ : U) oneQ_mem_RatSet,
                ← addQ_assoc (negQ (oneQ : U)) (oneQ : U) (oneQ : U)
                  (negQ_in_RatSet (oneQ : U) oneQ_mem_RatSet) oneQ_mem_RatSet oneQ_mem_RatSet,
                negQ_addQ_left (oneQ : U) oneQ_mem_RatSet,
                addQ_zero_left (oneQ : U) oneQ_mem_RatSet] at step
            exact step.symm
          exact oneQ_pos.2 h_zero.symm
      have h_one_lt_xx : ltQ (oneQ : U) (mulQ x x) :=
        ltQ_trans (oneQ : U) (addQ (oneQ : U) (oneQ : U)) (mulQ x x)
          oneQ_mem_RatSet h11 hxx_mem h_one_lt_two hxx_gt_two
      rcases leQ_total (oneQ : U) x oneQ_mem_RatSet hx with h_ge | h_le
      · exact h_ge
      · exfalso
        -- x ≤ 1 ∧ 0 ≤ x ⇒ x*x ≤ x ≤ 1, contradicting 1 < x*x
        have h_xx_le_x : leQ (mulQ x x) x := by
          have h := mulQ_leQ_mulQ_of_nonneg_left x x (oneQ : U) hx hx oneQ_mem_RatSet
            h_le hx_pos.1
          rw [mulQ_one_right x hx] at h
          exact h
        have h_xx_le_one : leQ (mulQ x x) (oneQ : U) :=
          leQ_trans (mulQ x x) x (oneQ : U) hxx_mem hx oneQ_mem_RatSet h_xx_le_x h_le
        exact h_one_lt_xx.2
          (leQ_antisymm (oneQ : U) (mulQ x x) oneQ_mem_RatSet hxx_mem
            h_one_lt_xx.1 h_xx_le_one)

    /-- sqrtApproxSeq is non-increasing: m ≤ n → f(n) ≤ f(m). -/
    theorem sqrtApproxSeq_nonincreasing : isNonincreasingQ (sqrtApproxSeq : U) := by
      -- Step 1: cada paso decrece estrictamente: ltQ (f(σk)) (f k).
      have step : ∀ k : U, k ∈ (ω : U) →
          ltQ ((sqrtApproxSeq : U)⦅σ k⦆) ((sqrtApproxSeq : U)⦅k⦆) := by
        intro k hk
        have hx : (sqrtApproxSeq : U)⦅k⦆ ∈ (RatSet : U) :=
          seqTermQ_mem_RatSet sqrtApproxSeq k sqrtApproxSeq_isSeqQ hk
        have hx_pos : isPositiveQ ((sqrtApproxSeq : U)⦅k⦆) := sqrtApproxSeq_pos k hk
        have hx_ne : (sqrtApproxSeq : U)⦅k⦆ ≠ (zeroQ : U) := hx_pos.2.symm
        have hxx_gt_two :
            ltQ (addQ (oneQ : U) (oneQ : U))
              (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) :=
          sqrtApproxSeq_sq_gt_two k hk
        have hxx_mem : mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆) ∈ (RatSet : U) :=
          mulQ_in_RatSet _ _ hx hx
        have h2x_pos : isPositiveQ (mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆)) :=
          mulQ_pos_of_pos_pos (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆) twoQ_mem hx twoQ_pos hx_pos
        have h2x_mem : mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆) ∈ (RatSet : U) :=
          mulQ_in_RatSet _ _ twoQ_mem hx
        have hfsk_mem : (sqrtApproxSeq : U)⦅σ k⦆ ∈ (RatSet : U) :=
          seqTermQ_mem_RatSet sqrtApproxSeq (σ k) sqrtApproxSeq_isSeqQ (succ_in_Omega k hk)
        -- Aplicar cancelación: basta con `2*x*f(σk) < 2*x*x`.
        apply ltQ_of_mulQ_pos_ltQ_left (mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆))
          ((sqrtApproxSeq : U)⦅σ k⦆) ((sqrtApproxSeq : U)⦅k⦆)
          h2x_mem hfsk_mem hx h2x_pos
        -- Identidad: 2*x*f(σk) = x*x + 2.
        have h_id : mulQ (mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆)) ((sqrtApproxSeq : U)⦅σ k⦆) =
            addQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) (twoQ : U) := by
          rw [sqrtApproxSeq_apply_succ k hk]
          show mulQ (mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆))
                (mulQ (addQ ((sqrtApproxSeq : U)⦅k⦆)
                  (mulQ (twoQ : U) (invQ ((sqrtApproxSeq : U)⦅k⦆)))) (invQ (twoQ : U))) =
                addQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) (twoQ : U)
          let T : U := (twoQ : U)
          let X : U := (sqrtApproxSeq : U)⦅k⦆
          show mulQ (mulQ T X) (mulQ (addQ X (mulQ T (invQ X))) (invQ T)) = addQ (mulQ X X) T
          have hT : T ∈ (RatSet : U) := twoQ_mem
          have hX : X ∈ (RatSet : U) := hx
          have hT_ne : T ≠ (zeroQ : U) := twoQ_ne_zeroQ
          have hX_ne : X ≠ (zeroQ : U) := hx_ne
          have hiT := invQ_in_RatSet T hT
          have hiX := invQ_in_RatSet X hX
          have hTiX := mulQ_in_RatSet T (invQ X) hT hiX
          have hZ := addQ_in_RatSet X (mulQ T (invQ X)) hX hTiX
          have hZiT := mulQ_in_RatSet (addQ X (mulQ T (invQ X))) (invQ T) hZ hiT
          have hTX := mulQ_in_RatSet T X hT hX
          have hXX := mulQ_in_RatSet X X hX hX
          calc mulQ (mulQ T X) (mulQ (addQ X (mulQ T (invQ X))) (invQ T))
              = mulQ T (mulQ X (mulQ (addQ X (mulQ T (invQ X))) (invQ T))) :=
                  mulQ_assoc T X (mulQ (addQ X (mulQ T (invQ X))) (invQ T)) hT hX hZiT
            _ = mulQ T (mulQ (mulQ X (addQ X (mulQ T (invQ X)))) (invQ T)) := by
                  rw [← mulQ_assoc X (addQ X (mulQ T (invQ X))) (invQ T) hX hZ hiT]
            _ = mulQ T (mulQ (invQ T) (mulQ X (addQ X (mulQ T (invQ X))))) := by
                  rw [mulQ_comm (mulQ X (addQ X (mulQ T (invQ X)))) (invQ T)
                        (mulQ_in_RatSet X (addQ X (mulQ T (invQ X))) hX hZ) hiT]
            _ = mulQ X (addQ X (mulQ T (invQ X))) := by
                  rw [← mulQ_assoc T (invQ T) (mulQ X (addQ X (mulQ T (invQ X)))) hT hiT
                        (mulQ_in_RatSet X (addQ X (mulQ T (invQ X))) hX hZ),
                      mulQ_invQ_right T hT hT_ne,
                      mulQ_one_left (mulQ X (addQ X (mulQ T (invQ X))))
                        (mulQ_in_RatSet X (addQ X (mulQ T (invQ X))) hX hZ)]
            _ = addQ (mulQ X X) (mulQ X (mulQ T (invQ X))) :=
                  mulQ_addQ_distrib_left X X (mulQ T (invQ X)) hX hX hTiX
            _ = addQ (mulQ X X) (mulQ T (mulQ X (invQ X))) := by
                  rw [← mulQ_assoc X T (invQ X) hX hT hiX,
                      mulQ_comm X T hX hT,
                      mulQ_assoc T X (invQ X) hT hX hiX]
            _ = addQ (mulQ X X) (mulQ T (oneQ : U)) := by
                  rw [mulQ_invQ_right X hX hX_ne]
            _ = addQ (mulQ X X) T := by rw [mulQ_one_right T hT]
        -- Identidad: 2*x*x = (xx) + (xx).
        have h_rhs : mulQ (mulQ (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆)) ((sqrtApproxSeq : U)⦅k⦆) =
            addQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                 (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) := by
          rw [mulQ_assoc (twoQ : U) ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆) twoQ_mem hx hx]
          exact mulQ_two_eq_addSelf (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) hxx_mem
        rw [h_id, h_rhs]
        -- Goal: ltQ (xx + 2) (xx + xx). Cancela xx por addQ_leQ_addQ + neq por 2 ≠ xx.
        refine ⟨?_, ?_⟩
        · -- leQ (xx + 2) (xx + xx). Use addQ_leQ_addQ on left for 2 ≤ xx.
          have h_le : leQ (addQ (oneQ : U) (oneQ : U))
                          (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) := hxx_gt_two.1
          have step := addQ_leQ_addQ (addQ (oneQ : U) (oneQ : U))
            (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
            (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
            (addQ_in_RatSet (oneQ : U) (oneQ : U) oneQ_mem_RatSet oneQ_mem_RatSet)
            hxx_mem hxx_mem h_le
          rw [addQ_comm (addQ (oneQ : U) (oneQ : U))
                (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                (addQ_in_RatSet _ _ oneQ_mem_RatSet oneQ_mem_RatSet) hxx_mem,
              addQ_comm (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) hxx_mem hxx_mem] at step
          exact step
        · intro h_eq
          -- xx + 2 = xx + xx → 2 = xx, contradicting hxx_gt_two
          have h2_eq_xx : (twoQ : U) = mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆) := by
            have step : addQ (negQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)))
                          (addQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) (twoQ : U)) =
                        addQ (negQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)))
                          (addQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                            (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)))  :=
              congrArg
                (fun y => addQ (negQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))) y)
                h_eq
            rw [← addQ_assoc
                  (negQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)))
                  (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                  (twoQ : U)
                  (negQ_in_RatSet _ hxx_mem) hxx_mem twoQ_mem,
                ← addQ_assoc
                  (negQ (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)))
                  (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                  (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆))
                  (negQ_in_RatSet _ hxx_mem) hxx_mem hxx_mem,
                negQ_addQ_left (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) hxx_mem,
                addQ_zero_left (twoQ : U) twoQ_mem,
                addQ_zero_left (mulQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅k⦆)) hxx_mem] at step
            exact step
          -- twoQ = mulQ X X but ltQ (addQ oneQ oneQ) (mulQ X X) means 2 ≠ XX.
          -- Note twoQ = addQ oneQ oneQ definitionally, so hxx_gt_two.2 says addQ oneQ oneQ ≠ XX.
          exact hxx_gt_two.2 h2_eq_xx
      -- Step 2: Estrictamente decreciente: m ∈ n → ltQ (f n) (f m).
      have strict : isStrictlyDecreasingQ (sqrtApproxSeq : U) := by
        -- Inducción sobre n.
        intro m n hm hn hmn
        let P : U → Prop := fun nn => ∀ mm : U, mm ∈ (ω : U) → mm ∈ nn →
          ltQ ((sqrtApproxSeq : U)⦅nn⦆) ((sqrtApproxSeq : U)⦅mm⦆)
        let S := sep (ω : U) P
        suffices hS : S = (ω : U) by
          have hmem : n ∈ S := by rw [hS]; exact hn
          exact ((mem_sep_iff (ω : U) n P).mp hmem).2 m hm hmn
        apply induction_principle S
        · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
        · -- Base: n = ∅. ∀ m ∈ ω, m ∈ ∅ → ...  vacuous.
          rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ?_⟩
          intro mm _ hmm_in
          exact absurd hmm_in (EmptySet_is_empty mm)
        · -- Inductivo
          intro k hk_S
          rw [mem_sep_iff] at hk_S ⊢
          obtain ⟨hk, hk_P⟩ := hk_S
          refine ⟨succ_in_Omega k hk, ?_⟩
          intro mm hmm hmm_in
          -- mm ∈ σ k = k ∪ {k}, so mm ∈ k or mm = k.
          rcases mem_succ_iff k mm |>.mp hmm_in with hmm_lt | hmm_eq
          · -- mm ∈ k: by IH, f(k) < f(mm). And f(σ k) < f(k). So f(σ k) < f(mm).
            have h1 : ltQ ((sqrtApproxSeq : U)⦅σ k⦆) ((sqrtApproxSeq : U)⦅k⦆) := step k hk
            have h2 : ltQ ((sqrtApproxSeq : U)⦅k⦆) ((sqrtApproxSeq : U)⦅mm⦆) :=
              hk_P mm hmm hmm_lt
            exact ltQ_trans ((sqrtApproxSeq : U)⦅σ k⦆) ((sqrtApproxSeq : U)⦅k⦆)
              ((sqrtApproxSeq : U)⦅mm⦆)
              (seqTermQ_mem_RatSet sqrtApproxSeq (σ k) sqrtApproxSeq_isSeqQ
                (succ_in_Omega k hk))
              (seqTermQ_mem_RatSet sqrtApproxSeq k sqrtApproxSeq_isSeqQ hk)
              (seqTermQ_mem_RatSet sqrtApproxSeq mm sqrtApproxSeq_isSeqQ hmm)
              h1 h2
          · -- mm = k: directo de step.
            subst hmm_eq
            exact step mm hmm
      exact strictlyDecreasing_isNonincreasing (sqrtApproxSeq : U) sqrtApproxSeq_isSeqQ strict

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

    -- The theorems `sqrt2_irrational` and `sqrtApproxSeq_not_convergent`
    -- live in `ZFC/Rat/SqrtIrrational.lean`. They were placed in a separate
    -- file because their proofs require importing `ZFC.Nat.Primes`, which
    -- transitively brings in `PeanoNatLib.PeanoNatArith` — declaring a
    -- global `notation:50 a " ∈ " l => DList.Mem a l` that shadows the ZFC
    -- `mem` notation `∈` and breaks parsing of expressions of the form
    -- `p ∈ X ↔ p ∈ Y ∧ ...` used throughout this file.

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
  twoQ
  twoQ_mem
  twoQ_ne_zeroQ
  twoQ_pos
)
