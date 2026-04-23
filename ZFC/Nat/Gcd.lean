/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

Nat.Gcd.lean — ZFC-native GCD and LCM via the Euclidean algorithm.

We implement gcd(a, b) by running σ b steps of the Euclidean pair recursion
  ⟨a, b⟩ → if b = ∅ then ⟨a, b⟩ else ⟨b, a mod b⟩
using RecursiveFn on ω ×ₛ ω.  After σ b steps the second component is ∅ and
the first component equals gcd(a, b) in the classical sense.

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Nat.Basic
import ZFC.Axiom.Infinity
import ZFC.Induction.Recursion
import ZFC.Peano.Import
import ZFC.Nat.Add
import ZFC.Nat.Mul
import ZFC.Nat.Sub
import ZFC.Nat.Div
import ZFC.Nat.Arith

namespace ZFC
  open Classical

  universe u
  variable {U : Type u}

  namespace Nat.Gcd

    -- =========================================================================
    -- §1  The Euclidean step function  euclid_stepFn : ω ×ₛ ω → ω ×ₛ ω
    -- =========================================================================

    /-- One step of the Euclidean algorithm on pairs.
        ⟨a, ∅⟩ ↦ ⟨a, ∅⟩    (fixed point)
        ⟨a, b⟩ ↦ ⟨b, a mod b⟩   when b ≠ ∅  -/
    private noncomputable def euclid_stepFn : U :=
      sep ((ω ×ₛ ω : U) ×ₛ (ω ×ₛ ω : U)) (fun p =>
        ∃ a b : U, (a ∈ (ω : U)) ∧ (b ∈ (ω : U)) ∧
          ((b = ∅ ∧ p = ⟨⟨a, b⟩, ⟨a, b⟩⟩) ∨
           (b ≠ ∅ ∧ p = ⟨⟨a, b⟩, ⟨b, mod a b⟩⟩)))

    private theorem mem_euclid_zero (a : U) (ha : a ∈ (ω : U)) :
        (⟨⟨a, ∅⟩, ⟨a, ∅⟩⟩ : U) ∈ euclid_stepFn := by
      unfold euclid_stepFn
      rw [mem_sep_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr
               ⟨(OrderedPair_mem_CartesianProduct a ∅ ω ω).mpr ⟨ha, zero_in_Omega⟩,
                (OrderedPair_mem_CartesianProduct a ∅ ω ω).mpr ⟨ha, zero_in_Omega⟩⟩,
             a, ∅, ha, zero_in_Omega, Or.inl ⟨rfl, rfl⟩⟩

    private theorem mem_euclid_pos (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hb_pos : b ≠ ∅) :
        (⟨⟨a, b⟩, ⟨b, mod a b⟩⟩ : U) ∈ euclid_stepFn := by
      unfold euclid_stepFn
      rw [mem_sep_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr
               ⟨(OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩,
                (OrderedPair_mem_CartesianProduct b (mod a b) ω ω).mpr
                  ⟨hb, mod_in_Omega a b ha hb⟩⟩,
             a, b, ha, hb, Or.inr ⟨hb_pos, rfl⟩⟩

    private theorem euclid_stepFn_is_function :
        IsFunction euclid_stepFn (ω ×ₛ ω : U) (ω ×ₛ ω : U) := by
      constructor
      · -- euclid_stepFn ⊆ (ω ×ₛ ω) ×ₛ (ω ×ₛ ω)
        intro p hp
        unfold euclid_stepFn at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · -- For each input ∈ ω ×ₛ ω, unique output
        intro p hp
        rw [CartesianProduct_is_specified] at hp
        obtain ⟨hop, ha, hb⟩ := hp
        unfold isOrderedPair at hop
        obtain ⟨a, b, rfl⟩ := hop
        rw [fst_of_ordered_pair] at ha
        rw [snd_of_ordered_pair] at hb
        rcases Classical.em (b = (∅ : U)) with rfl | hb_pos
        · -- b = ∅: unique output ⟨a, ∅⟩
          apply ExistsUnique.intro (⟨a, ∅⟩ : U)
          · exact mem_euclid_zero a ha
          · intro y hy
            unfold euclid_stepFn at hy
            rw [mem_sep_iff] at hy
            obtain ⟨-, a', b', -, -, h⟩ := hy
            rcases h with ⟨rfl, heq⟩ | ⟨hb'_pos, heq⟩
            · have hpair := (OrderedPair_eq_iff ⟨a, ∅⟩ y ⟨a', ∅⟩ ⟨a', ∅⟩).mp heq
              exact hpair.2.trans hpair.1.symm
            · have hpair := (OrderedPair_eq_iff ⟨a, ∅⟩ y ⟨a', b'⟩ ⟨b', mod a' b'⟩).mp heq
              have hfst := (OrderedPair_eq_iff a (∅ : U) a' b').mp hpair.1
              exact absurd hfst.2.symm hb'_pos
        · -- b ≠ ∅: unique output ⟨b, mod a b⟩
          apply ExistsUnique.intro (⟨b, mod a b⟩ : U)
          · exact mem_euclid_pos a b ha hb hb_pos
          · intro y hy
            unfold euclid_stepFn at hy
            rw [mem_sep_iff] at hy
            obtain ⟨-, a', b', ha', hb', h⟩ := hy
            rcases h with ⟨rfl, heq⟩ | ⟨-, heq⟩
            · have hpair := (OrderedPair_eq_iff ⟨a, b⟩ y ⟨a', ∅⟩ ⟨a', ∅⟩).mp heq
              have hfst := (OrderedPair_eq_iff a b a' (∅ : U)).mp hpair.1
              exact absurd hfst.2 hb_pos
            · have hpair := (OrderedPair_eq_iff ⟨a, b⟩ y ⟨a', b'⟩ ⟨b', mod a' b'⟩).mp heq
              have hfst := (OrderedPair_eq_iff a b a' b').mp hpair.1
              rw [hpair.2, ← hfst.2, ← hfst.1]

    private theorem euclid_apply_zero (a : U) (ha : a ∈ (ω : U)) :
        apply euclid_stepFn (⟨a, ∅⟩ : U) = (⟨a, ∅⟩ : U) :=
      apply_eq euclid_stepFn ⟨a, ∅⟩ ⟨a, ∅⟩
        (euclid_stepFn_is_function.2 ⟨a, ∅⟩
          ((OrderedPair_mem_CartesianProduct a ∅ ω ω).mpr ⟨ha, zero_in_Omega⟩))
        (mem_euclid_zero a ha)

    private theorem euclid_apply_pos (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hb_pos : b ≠ ∅) :
        apply euclid_stepFn (⟨a, b⟩ : U) = (⟨b, mod a b⟩ : U) :=
      apply_eq euclid_stepFn ⟨a, b⟩ ⟨b, mod a b⟩
        (euclid_stepFn_is_function.2 ⟨a, b⟩
          ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩))
        (mem_euclid_pos a b ha hb hb_pos)

    -- =========================================================================
    -- §2  RecursiveFn instantiation: euclidFn
    -- =========================================================================

    /-- Iterate the Euclidean step n times starting from ⟨a, b⟩. -/
    private noncomputable def euclidFn (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : U :=
      RecursiveFn (ω ×ₛ ω : U) ⟨a, b⟩ euclid_stepFn
        ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
        euclid_stepFn_is_function

    private theorem euclidFn_zero (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        apply (euclidFn a b ha hb) ∅ = (⟨a, b⟩ : U) :=
      RecursiveFn_zero (ω ×ₛ ω : U) ⟨a, b⟩ euclid_stepFn
        ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
        euclid_stepFn_is_function

    private theorem euclidFn_succ (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (n : U) (hn : n ∈ (ω : U)) :
        apply (euclidFn a b ha hb) (σ n) =
          apply euclid_stepFn (apply (euclidFn a b ha hb) n) :=
      RecursiveFn_succ (ω ×ₛ ω : U) ⟨a, b⟩ euclid_stepFn
        ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
        euclid_stepFn_is_function n hn

    /-- Every iterate lies in ω ×ₛ ω. -/
    private theorem euclidFn_in_prod (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (n : U) (hn : n ∈ (ω : U)) :
        apply (euclidFn a b ha hb) n ∈ (ω ×ₛ ω : U) := by
      have hF := RecursiveFn_is_function (ω ×ₛ ω : U) ⟨a, b⟩ euclid_stepFn
        ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
        euclid_stepFn_is_function
      have huniq := hF.2 n hn
      have hpair := apply_mem (euclidFn a b ha hb) n huniq
      have hsub := hF.1 _ hpair
      exact ((OrderedPair_mem_CartesianProduct n (apply (euclidFn a b ha hb) n)
               ω (ω ×ₛ ω)).mp hsub).2

    -- =========================================================================
    -- §3  Shift lemma
    -- =========================================================================
    -- apply (euclidFn a b ..) (σ n) = apply (euclidFn a' b' ..) n
    -- where ⟨a', b'⟩ = apply euclid_stepFn ⟨a, b⟩

    private theorem euclidFn_shift (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (a' b' : U) (ha' : a' ∈ (ω : U)) (hb' : b' ∈ (ω : U))
        (heq : apply euclid_stepFn (⟨a, b⟩ : U) = (⟨a', b'⟩ : U))
        (n : U) (hn : n ∈ (ω : U)) :
        apply (euclidFn a b ha hb) (σ n) = apply (euclidFn a' b' ha' hb') n := by
      let P := fun k => apply (euclidFn a b ha hb) (σ k) = apply (euclidFn a' b' ha' hb') k
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        rw [mem_sep_iff] at hn_S
        exact hn_S.2
      apply induction_principle S
      · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
      · rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        simp only [P]
        rw [euclidFn_succ a b ha hb ∅ zero_in_Omega,
            euclidFn_zero a b ha hb,
            heq,
            euclidFn_zero a' b' ha' hb']
      · intro k hk_S
        rw [mem_sep_iff] at hk_S ⊢
        refine ⟨succ_in_Omega k hk_S.1, ?_⟩
        simp only [P]
        rw [euclidFn_succ a b ha hb (σ k) (succ_in_Omega k hk_S.1),
            hk_S.2,
            ← euclidFn_succ a' b' ha' hb' k hk_S.1]

    -- =========================================================================
    -- §4  Stability lemmas
    -- =========================================================================

    /-- Fixed-point: one more step from ⟨x, ∅⟩ stays at ⟨x, ∅⟩. -/
    private theorem euclid_stable_step (a b x : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hx : x ∈ (ω : U)) (n : U) (hn : n ∈ (ω : U))
        (hstable : apply (euclidFn a b ha hb) n = (⟨x, ∅⟩ : U)) :
        apply (euclidFn a b ha hb) (σ n) = (⟨x, ∅⟩ : U) := by
      rw [euclidFn_succ a b ha hb n hn, hstable, euclid_apply_zero x hx]

    /-- Stability over k extra steps. -/
    private theorem euclid_stable_add (a b x n k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hx : x ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (hstable : apply (euclidFn a b ha hb) n = (⟨x, ∅⟩ : U)) :
        apply (euclidFn a b ha hb) (add n k) = (⟨x, ∅⟩ : U) := by
      let P := fun k => apply (euclidFn a b ha hb) (add n k) = (⟨x, ∅⟩ : U)
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hk_S : k ∈ S := hS ▸ hk
        rw [mem_sep_iff] at hk_S
        exact hk_S.2
      apply induction_principle S
      · intro z hz; rw [mem_sep_iff] at hz; exact hz.1
      · rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        simp only [P]
        rw [add_zero n hn, hstable]
      · intro m hm_S
        rw [mem_sep_iff] at hm_S ⊢
        refine ⟨succ_in_Omega m hm_S.1, ?_⟩
        simp only [P]
        rw [add_succ n m hn hm_S.1,
            euclid_stable_step a b x ha hb hx (add n m)
              (add_in_Omega n m hn hm_S.1) hm_S.2]

    -- =========================================================================
    -- §5  Convergence: after σ b steps, snd = ∅
    -- =========================================================================

    /-- Main convergence theorem: after σ b steps, the state is ⟨gcd(a,b), ∅⟩. -/
    private theorem euclid_converges (b : U) (hb : b ∈ (ω : U))
        (a : U) (ha : a ∈ (ω : U)) :
        ∃ (x : U), (x ∈ (ω : U)) ∧
          apply (euclidFn a b ha hb) (σ b) = (⟨x, ∅⟩ : U) := by
      -- Strong induction on b, universally quantifying over all a and proof terms
      let S := sep (ω : U) (fun b =>
        ∀ (a : U) (_ : a ∈ (ω : U)) (hb' : b ∈ (ω : U)) (ha' : a ∈ (ω : U)),
        ∃ x, (x ∈ (ω : U)) ∧ apply (euclidFn a b ha' hb') (σ b) = (⟨x, ∅⟩ : U))
      suffices hS_eq : S = ω by
        have hb_S : b ∈ S := hS_eq ▸ hb
        rw [mem_sep_iff] at hb_S
        exact hb_S.2 a ha hb ha
      apply strong_induction_principle S
      · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
      · intro b hb_ω ih_b
        rw [mem_sep_iff]
        refine ⟨hb_ω, fun a_v _ha_v hb' ha' => ?_⟩
        rcases Classical.em (b = (∅ : U)) with rfl | hb_pos
        · -- Base: b = ∅
          refine ⟨a_v, ha', ?_⟩
          rw [euclidFn_succ a_v (∅ : U) ha' zero_in_Omega (∅ : U) zero_in_Omega,
              euclidFn_zero a_v (∅ : U) ha' zero_in_Omega,
              euclid_apply_zero a_v ha']
        · -- Step: b ≠ ∅
          have hmod : mod a_v b ∈ (ω : U) := mod_in_Omega a_v b ha' hb_ω
          have hmod_lt : mod a_v b ∈ b := mod_lt_divisor_ZFC a_v b ha' hb_ω hb_pos
          -- IH for mod a_v b
          have hmod_S : mod a_v b ∈ S := ih_b (mod a_v b) hmod_lt
          rw [mem_sep_iff] at hmod_S
          -- Convergence for (b, mod a_v b): ∃ x, apply (euclidFn b (mod a_v b) hb' hmod) (σ (mod a_v b)) = ⟨x, ∅⟩
          obtain ⟨x, hx, hconv⟩ := hmod_S.2 b hb_ω hmod hb'
          -- σ (mod a_v b) ≤ b
          have h_sb_in_sb : σ (mod a_v b) ∈ σ b :=
            (succ_mem_succ_iff (mod a_v b) b
              (mem_Omega_is_Nat _ hmod) (mem_Omega_is_Nat b hb_ω)).mp hmod_lt
          have h_sb_le_b : (σ (mod a_v b) ∈ b) ∨ σ (mod a_v b) = b :=
            subset_of_mem_succ b _ h_sb_in_sb
          obtain ⟨d, hd, hsum⟩ :=
            le_then_exists_add_Omega (σ (mod a_v b)) b
              (succ_in_Omega _ hmod) hb_ω h_sb_le_b
          -- Stability: apply (euclidFn b (mod a_v b) hb' hmod) b = ⟨x, ∅⟩
          have hstab : apply (euclidFn b (mod a_v b) hb' hmod) b = (⟨x, ∅⟩ : U) := by
            have := euclid_stable_add b (mod a_v b) x (σ (mod a_v b)) d hb' hmod hx
              (succ_in_Omega _ hmod) hd hconv
            rw [← hsum] at this
            exact this
          -- Shift: apply (euclidFn a_v b ha' hb') (σ b) = apply (euclidFn b (mod a_v b) hb' hmod) b
          have hstep : apply euclid_stepFn (⟨a_v, b⟩ : U) = (⟨b, mod a_v b⟩ : U) :=
            euclid_apply_pos a_v b ha' hb' hb_pos
          refine ⟨x, hx, ?_⟩
          rw [euclidFn_shift a_v b ha' hb' b (mod a_v b) hb' hmod hstep b hb_ω, hstab]

    -- =========================================================================
    -- §6  Definition of gcd
    -- =========================================================================

    /-- ZFC-native GCD: run σ b steps of the Euclidean algorithm starting from ⟨a, b⟩
        and take the first component. -/
    noncomputable def gcd (a b : U) : U :=
      if ha : a ∈ (ω : U) then
        if hb : b ∈ (ω : U) then
          fst (apply (euclidFn a b ha hb) (σ b))
        else ∅
      else ∅

    theorem gcd_in_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        gcd a b ∈ (ω : U) := by
      simp only [gcd, dif_pos ha, dif_pos hb]
      obtain ⟨x, hx, hconv⟩ := euclid_converges b hb a ha
      rw [hconv, fst_of_ordered_pair]
      exact hx

    theorem gcd_zero (a : U) (ha : a ∈ (ω : U)) :
        gcd a ∅ = a := by
      simp only [gcd, dif_pos ha, dif_pos zero_in_Omega]
      rw [euclidFn_succ a ∅ ha zero_in_Omega ∅ zero_in_Omega,
          euclidFn_zero a ∅ ha zero_in_Omega,
          euclid_apply_zero a ha,
          fst_of_ordered_pair]

    /-- Key step: gcd a b = gcd b (mod a b) when b ≠ ∅.
        This is the Euclidean algorithm recursion. -/
    theorem gcd_pos_step (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hb_pos : b ≠ ∅) :
        gcd a b = gcd b (mod a b) := by
      have hmod : mod a b ∈ (ω : U) := mod_in_Omega a b ha hb
      -- Convergence: ∃ x, apply (euclidFn b (mod a b) ..) (σ (mod a b)) = ⟨x, ∅⟩
      obtain ⟨x, hx, hconv⟩ := euclid_converges (mod a b) hmod b hb
      -- σ (mod a b) ≤ b: derive from mod a b ∈ b
      have hmod_lt : mod a b ∈ b := mod_lt_divisor_ZFC a b ha hb hb_pos
      have h_sb_in_sb : σ (mod a b) ∈ σ b :=
        (succ_mem_succ_iff (mod a b) b
          (mem_Omega_is_Nat (mod a b) hmod) (mem_Omega_is_Nat b hb)).mp hmod_lt
      have h_sb_le_b : (σ (mod a b) ∈ b) ∨ σ (mod a b) = b :=
        subset_of_mem_succ b (σ (mod a b)) h_sb_in_sb
      -- b = add (σ (mod a b)) d for some d
      obtain ⟨d, hd, hsum⟩ :=
        le_then_exists_add_Omega (σ (mod a b)) b
          (succ_in_Omega (mod a b) hmod) hb h_sb_le_b
      -- Stability: apply (euclidFn b (mod a b) ..) b = ⟨x, ∅⟩
      have hstab : apply (euclidFn b (mod a b) hb hmod) b = (⟨x, ∅⟩ : U) := by
        have := euclid_stable_add b (mod a b) x (σ (mod a b)) d hb hmod hx
          (succ_in_Omega (mod a b) hmod) hd hconv
        rw [← hsum] at this
        exact this
      -- Shift: apply (euclidFn a b ..) (σ b) = apply (euclidFn b (mod a b) ..) b
      have hstep : apply euclid_stepFn (⟨a, b⟩ : U) = (⟨b, mod a b⟩ : U) :=
        euclid_apply_pos a b ha hb hb_pos
      have hshift : apply (euclidFn a b ha hb) (σ b) =
          apply (euclidFn b (mod a b) hb hmod) b :=
        euclidFn_shift a b ha hb b (mod a b) hb hmod hstep b hb
      -- Conclude
      simp only [gcd, dif_pos ha, dif_pos hb, dif_pos hmod]
      rw [hshift, hstab, hconv]

    -- =========================================================================
    -- §7  Auxiliary bridge lemmas for gcdOf
    -- =========================================================================

    /-- gcdOf a ∅ = a (zero right). -/
    private theorem gcdOf_zero_right (a : U) (ha : a ∈ (ω : U)) :
        gcdOf a ∅ = a := by
      apply antisymm_divides_Omega (gcdOf a ∅) a
        (gcdOf_in_Omega a ∅ ha zero_in_Omega) ha
      · exact gcdOf_divides_left_Omega a ∅ ha zero_in_Omega
      · apply gcdOf_greatest_Omega a ∅ a ha zero_in_Omega ha
        · exact divides_refl_Omega a ha
        · exact divides_zero_Omega a ha

    /-- gcdOf a b = gcdOf b (mod a b) when b ≠ ∅.
        Proved from divisibility characterization. -/
    private theorem gcdOf_pos_step (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hb_pos : b ≠ ∅) :
        gcdOf a b = gcdOf b (mod a b) := by
      have hmod : mod a b ∈ (ω : U) := mod_in_Omega a b ha hb
      apply antisymm_divides_Omega (gcdOf a b) (gcdOf b (mod a b))
        (gcdOf_in_Omega a b ha hb) (gcdOf_in_Omega b (mod a b) hb hmod)
      · -- gcdOf a b | gcdOf b (mod a b)
        apply gcdOf_greatest_Omega b (mod a b) (gcdOf a b)
          hb hmod (gcdOf_in_Omega a b ha hb)
        · exact gcdOf_divides_right_Omega a b ha hb
        · -- gcdOf a b | mod a b
          -- since mod a b = a - (div a b) * b (Euclidean) and gcdOf a b | a and | b
          rw [mod_eq_modOf a b ha hb hb_pos]
          exact divides_modOf_Omega a b (gcdOf a b) ha hb
            (gcdOf_in_Omega a b ha hb)
            (gcdOf_divides_left_Omega a b ha hb)
            (gcdOf_divides_right_Omega a b ha hb)
      · -- gcdOf b (mod a b) | gcdOf a b
        apply gcdOf_greatest_Omega a b (gcdOf b (mod a b))
          ha hb (gcdOf_in_Omega b (mod a b) hb hmod)
        · -- gcdOf b (mod a b) | a: since a = q*b + mod a b
          have h_div_b := gcdOf_divides_left_Omega b (mod a b) hb hmod
          have h_div_mod := gcdOf_divides_right_Omega b (mod a b) hb hmod
          -- a = add (mul (div a b) b) (mod a b) and gcdOf b (mod a b) | b and | mod a b
          -- gcdOf b (mod a b) | (div a b) * b
          have h_div_qb := divides_mul_left_Omega (gcdOf b (mod a b)) b (div a b)
            (gcdOf_in_Omega b (mod a b) hb hmod) hb (div_in_Omega a b ha hb) h_div_b
          -- a = (div a b) * b + mod a b
          have heucl := divMod_eq_ZFC a b ha hb hb_pos
          -- so gcdOf b (mod a b) | a
          have hcombined := divides_add_Omega (gcdOf b (mod a b)) (mul (div a b) b) (mod a b)
            (gcdOf_in_Omega b (mod a b) hb hmod)
            (mul_in_Omega (div a b) b (div_in_Omega a b ha hb) hb)
            (mod_in_Omega a b ha hb)
            h_div_qb h_div_mod
          rw [← heucl] at hcombined
          exact hcombined
        · exact gcdOf_divides_left_Omega b (mod a b) hb hmod

    -- =========================================================================
    -- §8  Bridge: gcd = gcdOf
    -- =========================================================================

    theorem gcd_eq_gcdOf (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        gcd a b = gcdOf a b := by
      -- Strong induction on b with simple S predicate
      let S := sep (ω : U) (fun b => ∀ (a : U), (a ∈ (ω : U)) → gcd a b = gcdOf a b)
      have hS_eq : S = ω := by
        apply strong_induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · intro b hb_ω ih
          rw [mem_sep_iff]
          refine ⟨hb_ω, fun a ha => ?_⟩
          rcases Classical.em (b = (∅ : U)) with rfl | hb_pos
          · rw [gcd_zero a ha, gcdOf_zero_right a ha]
          · have hmod : mod a b ∈ (ω : U) := mod_in_Omega a b ha hb_ω
            have hmod_lt : mod a b ∈ b := mod_lt_divisor_ZFC a b ha hb_ω hb_pos
            have hmod_S : mod a b ∈ S := ih (mod a b) hmod_lt
            rw [mem_sep_iff] at hmod_S
            have ih_mod : gcd b (mod a b) = gcdOf b (mod a b) := hmod_S.2 b hb_ω
            rw [gcd_pos_step a b ha hb_ω hb_pos, ih_mod, ← gcdOf_pos_step a b ha hb_ω hb_pos]
      have hb_S : b ∈ S := hS_eq ▸ hb
      rw [mem_sep_iff] at hb_S
      exact hb_S.2 a ha

    -- =========================================================================
    -- §9  GCD properties (via bridge)
    -- =========================================================================

    theorem gcd_divides_left_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        divides (gcd a b) a := by
      rw [gcd_eq_gcdOf a b ha hb]
      exact gcdOf_divides_left_Omega a b ha hb

    theorem gcd_divides_right_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        divides (gcd a b) b := by
      rw [gcd_eq_gcdOf a b ha hb]
      exact gcdOf_divides_right_Omega a b ha hb

    theorem gcd_greatest_Omega (a b k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hk : k ∈ (ω : U)) (hka : divides k a) (hkb : divides k b) :
        divides k (gcd a b) := by
      rw [gcd_eq_gcdOf a b ha hb]
      exact gcdOf_greatest_Omega a b k ha hb hk hka hkb

    theorem gcd_comm_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        gcd a b = gcd b a := by
      rw [gcd_eq_gcdOf a b ha hb, gcd_eq_gcdOf b a hb ha]
      exact gcdOf_comm_Omega a b ha hb

    theorem gcd_assoc_Omega (a b c : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hc : c ∈ (ω : U)) :
        gcd a (gcd b c) = gcd (gcd a b) c := by
      let g1 := gcd a (gcd b c)
      let g2 := gcd (gcd a b) c
      have hg1 : g1 ∈ (ω : U) := gcd_in_Omega a (gcd b c) ha (gcd_in_Omega b c hb hc)
      have hg2 : g2 ∈ (ω : U) := gcd_in_Omega (gcd a b) c (gcd_in_Omega a b ha hb) hc
      apply antisymm_divides_Omega g1 g2 hg1 hg2
      · apply gcd_greatest_Omega (gcd a b) c g1 (gcd_in_Omega a b ha hb) hc hg1
        · apply gcd_greatest_Omega a b g1 ha hb hg1
          · exact gcd_divides_left_Omega a (gcd b c) ha (gcd_in_Omega b c hb hc)
          · have h1 := gcd_divides_right_Omega a (gcd b c) ha (gcd_in_Omega b c hb hc)
            have h2 := gcd_divides_left_Omega b c hb hc
            exact divides_trans_Omega g1 (gcd b c) b hg1 (gcd_in_Omega b c hb hc) hb h1 h2
        · have h1 := gcd_divides_right_Omega a (gcd b c) ha (gcd_in_Omega b c hb hc)
          have h2 := gcd_divides_right_Omega b c hb hc
          exact divides_trans_Omega g1 (gcd b c) c hg1 (gcd_in_Omega b c hb hc) hc h1 h2
      · apply gcd_greatest_Omega a (gcd b c) g2 ha (gcd_in_Omega b c hb hc) hg2
        · have h1 := gcd_divides_left_Omega (gcd a b) c (gcd_in_Omega a b ha hb) hc
          have h2 := gcd_divides_left_Omega a b ha hb
          exact divides_trans_Omega g2 (gcd a b) a hg2 (gcd_in_Omega a b ha hb) ha h1 h2
        · apply gcd_greatest_Omega b c g2 hb hc hg2
          · have h1 := gcd_divides_left_Omega (gcd a b) c (gcd_in_Omega a b ha hb) hc
            have h2 := gcd_divides_right_Omega a b ha hb
            exact divides_trans_Omega g2 (gcd a b) b hg2 (gcd_in_Omega a b ha hb) hb h1 h2
          · exact gcd_divides_right_Omega (gcd a b) c (gcd_in_Omega a b ha hb) hc

    theorem bezout_natform_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        ∃ n m : U, (n ∈ (ω : U)) ∧ (m ∈ (ω : U)) ∧
          (gcd a b = sub (mul n a) (mul m b) ∨ gcd a b = sub (mul n b) (mul m a)) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      subst hp; subst hq
      obtain ⟨n_peano, m_peano, h_bez⟩ := Peano.Arith.bezout_natform p q
      exact ⟨fromPeano n_peano, fromPeano m_peano, Nat_in_Omega _ (fromPeano_is_nat n_peano), Nat_in_Omega _ (fromPeano_is_nat m_peano), by
        rw [← fromPeano_mul, ← fromPeano_mul, ← fromPeano_mul, ← fromPeano_mul]
        rw [← fromPeano_sub, ← fromPeano_sub]
        rw [gcd_eq_gcdOf]
        · change gcdOf (fromPeano p) (fromPeano q) = fromPeano (Peano.Sub.sub (Peano.Mul.mul n_peano p) (Peano.Mul.mul m_peano q)) ∨
                 gcdOf (fromPeano p) (fromPeano q) = fromPeano (Peano.Sub.sub (Peano.Mul.mul n_peano q) (Peano.Mul.mul m_peano p))
          rw [← fromPeano_gcd]
          cases h_bez with
          | inl h => left; rw [h]
          | inr h => right; rw [h]
        · exact Nat_in_Omega _ (fromPeano_is_nat p)
        · exact Nat_in_Omega _ (fromPeano_is_nat q)
      ⟩

    -- =========================================================================
    -- §10  LCM
    -- =========================================================================

    /-- ZFC-native LCM: a * b / gcd(a, b). -/
    noncomputable def lcm (a b : U) : U :=
      if _ : a ∈ (ω : U) then
        if _ : b ∈ (ω : U) then
          divOf (mul a b) (gcd a b)
        else ∅
      else ∅

    theorem lcm_eq_lcmOf (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        lcm a b = lcmOf a b := by
      simp only [lcm, dif_pos ha, dif_pos hb]
      obtain ⟨p, hp⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
      obtain ⟨q, hq⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
      subst hp; subst hq
      rw [gcd_eq_gcdOf (fromPeano p) (fromPeano q) ha hb]
      rw [← fromPeano_gcd p q, ← fromPeano_mul p q, ← fromPeano_lcm p q]
      rw [← fromPeano_div (Peano.Mul.mul p q) (Peano.Arith.gcd p q)]
      congr 1

    theorem lcm_in_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        lcm a b ∈ (ω : U) := by
      rw [lcm_eq_lcmOf a b ha hb]
      exact lcmOf_in_Omega a b ha hb

    theorem lcm_multiple_left_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        divides a (lcm a b) := by
      rw [lcm_eq_lcmOf a b ha hb]
      exact lcmOf_multiple_left_Omega a b ha hb

    theorem lcm_multiple_right_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        divides b (lcm a b) := by
      rw [lcm_eq_lcmOf a b ha hb]
      exact lcmOf_multiple_right_Omega a b ha hb

    theorem lcm_comm_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        lcm a b = lcm b a := by
      rw [lcm_eq_lcmOf a b ha hb, lcm_eq_lcmOf b a hb ha]
      exact lcmOf_comm_Omega a b ha hb

    theorem lcm_zero_right_Omega (a : U) (ha : a ∈ (ω:U)) : lcm a ∅ = ∅ := by
      unfold lcm
      rw [dif_pos ha, dif_pos (zero_in_Omega : (∅:U) ∈ (ω:U))]
      have mul_0 : mul a ∅ = ∅ := mul_zero a ha
      rw [mul_0]
      have gcd_0 : gcd a ∅ = a := gcd_zero a ha
      rw [gcd_0]
      exact divOf_zero_Omega a ha

    theorem lcm_zero_left_Omega (a : U) (ha : a ∈ (ω:U)) : lcm ∅ a = ∅ := by
      rw [lcm_comm_Omega (∅:U) a zero_in_Omega ha]
      exact lcm_zero_right_Omega a ha

  end Nat.Gcd

  export Nat.Gcd (
    -- Definitions
    gcd
    lcm
    -- GCD basic properties
    gcd_in_Omega
    gcd_zero
    gcd_pos_step
    gcd_eq_gcdOf
    -- GCD divisibility properties
    gcd_divides_left_Omega
    gcd_divides_right_Omega
    gcd_greatest_Omega
    gcd_comm_Omega
    gcd_assoc_Omega
    bezout_natform_Omega
    -- LCM properties
    lcm_in_Omega
    lcm_eq_lcmOf
    lcm_multiple_left_Omega
    lcm_multiple_right_Omega
    lcm_comm_Omega
    lcm_zero_right_Omega
    lcm_zero_left_Omega
  )

end ZFC
