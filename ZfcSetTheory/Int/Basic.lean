/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Set ℤ and Fundamental Properties

  This module defines the integer set ℤ as the quotient of ω × ω by the
  equivalence relation IntEquivRel, and establishes basic properties including
  class membership, equality characterization, canonical representatives,
  and the trichotomy (zero / positive / negative).

  ## Main Definitions

  * `IntSet` — ℤ := QuotientSet (ω × ω) IntEquivRel
  * `intClass` — the equivalence class [(a,b)] representing the integer a - b
  * `zeroZ` — the integer zero, 0ℤ := [(0,0)]
  * `oneZ` — the integer one, 1ℤ := [(1,0)]

  ## Main Theorems

  * `intClass_mem_IntSet` — every class [(a,b)] with a,b ∈ ω belongs to ℤ
  * `intClass_eq_iff` — [(a,b)] = [(c,d)] ↔ a + d = b + c
  * `canonical_pos_exists` — if b ≤ a then [(a,b)] = [(a-b, 0)]
  * `canonical_neg_exists` — if a ≤ b and a ≠ b then [(a,b)] = [(0, b-a)]
  * `int_trichotomy` — every z ∈ ℤ is zero, positive, or negative
-/

import ZfcSetTheory.Int.Equiv
import ZfcSetTheory.Nat.Sub

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
  open ZFC.Nat.Sub
  open ZFC.Int.Equiv

  universe u
  variable {U : Type u}

  namespace Int.Basic

    /-! ### Core Definitions -/

    /-- The integer set ℤ, defined as the quotient of ω × ω by IntEquivRel -/
    noncomputable def IntSet : U :=
      QuotientSet ((ω : U) ×ₛ ω) IntEquivRel

    /-- The equivalence class [(a,b)] representing the integer a - b -/
    noncomputable def intClass (a b : U) : U :=
      EqClass (⟨a, b⟩ : U) IntEquivRel ((ω : U) ×ₛ ω)

    /-- The integer zero: 0ℤ := [(0,0)] -/
    noncomputable def zeroZ : U := intClass (∅ : U) ∅

    /-- The integer one: 1ℤ := [(1,0)] = [(σ ∅, ∅)] -/
    noncomputable def oneZ : U := intClass (σ (∅ : U)) ∅

    /-! ### Class membership in ℤ -/

    /-- Every equivalence class [(a,b)] with a,b ∈ ω belongs to ℤ -/
    theorem intClass_mem_IntSet (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        intClass a b ∈ (IntSet : U) := by
      unfold intClass IntSet
      exact EqClass_mem_QuotientSet IntEquivRel ((ω : U) ×ₛ ω) ⟨a, b⟩
        ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)

    /-- 0ℤ ∈ ℤ -/
    theorem zeroZ_mem_IntSet : (zeroZ : U) ∈ (IntSet : U) := by
      unfold zeroZ
      exact intClass_mem_IntSet ∅ ∅ zero_in_Omega zero_in_Omega

    /-- 1ℤ ∈ ℤ -/
    theorem oneZ_mem_IntSet : (oneZ : U) ∈ (IntSet : U) := by
      unfold oneZ
      exact intClass_mem_IntSet (σ (∅ : U)) (∅ : U)
        (succ_in_Omega (∅ : U) zero_in_Omega) zero_in_Omega

    /-! ### Equality of equivalence classes -/

    /-- Two integer classes are equal iff the cross-sums agree:
        [(a,b)] = [(c,d)] ↔ a + d = b + c -/
    theorem intClass_eq_iff (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U)) :
        intClass a b = intClass c d ↔ add a d = add b c := by
      unfold intClass
      rw [EqClass_eq_iff IntEquivRel ((ω : U) ×ₛ ω) ⟨a, b⟩ ⟨c, d⟩
            IntEquivRel_is_equivalence
            ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
            ((OrderedPair_mem_CartesianProduct c d ω ω).mpr ⟨hc, hd⟩)]
      rw [mem_IntEquivRel]
      constructor
      · intro h
        exact h.2.2.2.2
      · intro h
        exact ⟨ha, hb, hc, hd, h⟩

    /-! ### Canonical representatives -/

    /-- If b ≤ a (i.e. b ∈ a ∨ b = a), the canonical positive representative is (a-b, 0) -/
    theorem canonical_pos_exists (a b : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (h_le : b ∈ a ∨ b = a) :
        intClass a b = intClass (sub a b) ∅ := by
      rw [intClass_eq_iff a b (sub a b) ∅ ha hb (sub_in_Omega a b ha hb) zero_in_Omega]
      -- Goal: add a ∅ = add b (sub a b)
      rw [add_zero a ha]
      rw [add_comm_Omega b (sub a b) hb (sub_in_Omega a b ha hb)]
      exact (add_k_sub_k_Omega a b ha hb h_le).symm

    /-- If a ≤ b (i.e. a ∈ b ∨ a = b) and a ≠ b, the canonical negative
        representative is (0, b-a) -/
    theorem canonical_neg_exists (a b : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (h_le : a ∈ b ∨ a = b) (_h_ne : a ≠ b) :
        intClass a b = intClass ∅ (sub b a) := by
      rw [intClass_eq_iff a b ∅ (sub b a) ha hb zero_in_Omega (sub_in_Omega b a hb ha)]
      -- Goal: add a (sub b a) = add b ∅
      rw [add_comm_Omega a (sub b a) ha (sub_in_Omega b a hb ha)]
      rw [add_k_sub_k_Omega b a hb ha h_le]
      rw [add_zero b hb]

    /-- Every integer class has a canonical representative: either (n, 0) for
        some n ∈ ω, or (0, m) for some non-zero m ∈ ω -/
    theorem canonical_representative_exists (a b : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        (∃ n : U, n ∈ (ω : U) ∧ intClass a b = intClass n ∅) ∨
        (∃ m : U, m ∈ (ω : U) ∧ m ≠ ∅ ∧ intClass a b = intClass ∅ m) := by
      -- Use trichotomy on a and b
      have tri := natLt_trichotomy b a (mem_Omega_is_Nat b hb) (mem_Omega_is_Nat a ha)
      rcases tri with h_lt | h_eq | h_gt
      · -- Case b < a (b ∈ a): positive canonical form
        left
        exact ⟨sub a b, sub_in_Omega a b ha hb,
               canonical_pos_exists a b ha hb (Or.inl h_lt)⟩
      · -- Case b = a: zero (sub a a = ∅)
        left
        exact ⟨sub a b, sub_in_Omega a b ha hb,
               canonical_pos_exists a b ha hb (Or.inr h_eq)⟩
      · -- Case a < b (a ∈ b): negative canonical form
        right
        have h_ne : a ≠ b := fun heq =>
          absurd (heq ▸ h_gt : a ∈ a) (not_mem_self a (mem_Omega_is_Nat a ha))
        have h_sub_ne : sub b a ≠ ∅ :=
          (sub_pos_iff_lt_Omega b a hb ha).mpr h_gt
        exact ⟨sub b a, sub_in_Omega b a hb ha, h_sub_ne,
               canonical_neg_exists a b ha hb (Or.inl h_gt) h_ne⟩

    /-! ### Uniqueness of canonical representatives -/

    /-- If intClass n ∅ = intClass m ∅ then n = m -/
    theorem intClass_pos_injective (n m : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        intClass n ∅ = intClass m ∅ → n = m := by
      intro h
      rw [intClass_eq_iff n ∅ m ∅ hn zero_in_Omega hm zero_in_Omega] at h
      -- h : add n ∅ = add ∅ m
      rw [add_zero n hn, zero_add m hm] at h
      exact h

    /-- If intClass ∅ n = intClass ∅ m then n = m -/
    theorem intClass_neg_injective (n m : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        intClass ∅ n = intClass ∅ m → n = m := by
      intro h
      rw [intClass_eq_iff ∅ n ∅ m zero_in_Omega hn zero_in_Omega hm] at h
      -- h : add ∅ m = add n ∅
      rw [zero_add m hm, add_zero n hn] at h  -- h : m = n
      exact h.symm

    /-- A positive canonical class (n ≠ ∅) is not a negative canonical class (m ≠ ∅) -/
    theorem intClass_pos_ne_neg (n m : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hn_ne : n ≠ ∅) (_hm_ne : m ≠ ∅) :
        intClass n ∅ ≠ intClass ∅ m := by
      intro h
      rw [intClass_eq_iff n ∅ ∅ m hn zero_in_Omega zero_in_Omega hm] at h
      -- h : add n m = add ∅ ∅
      rw [zero_add ∅ zero_in_Omega] at h
      -- h : add n m = ∅
      -- But n ≠ ∅ and m ∈ ω, so add n m ≠ ∅
      -- Since n ∈ ω and n ≠ ∅, n = σ k for some k
      have hn_nat := mem_Omega_is_Nat n hn
      rcases eq_zero_or_exists_succ n hn_nat with h_zero | ⟨k, hk_eq⟩
      · exact absurd h_zero hn_ne
      · subst hk_eq
        have hk_omega : k ∈ (ω : U) := Omega_is_transitive (σ k) hn k (mem_succ_self k)
        rw [add_comm_Omega (σ k) m (succ_in_Omega k hk_omega) hm] at h
        rw [add_succ m k hm hk_omega] at h
        -- h : σ (add m k) = ∅
        exact succ_nonempty (add m k) h

    /-! ### Trichotomy -/

    /-- Every element of ℤ is either zero, strictly positive, or strictly negative -/
    theorem int_trichotomy (z : U) (hz : z ∈ (IntSet : U)) :
        (z = (zeroZ : U)) ∨
        (∃ n : U, n ∈ (ω : U) ∧ n ≠ ∅ ∧ z = intClass n ∅) ∨
        (∃ m : U, m ∈ (ω : U) ∧ m ≠ ∅ ∧ z = intClass ∅ m) := by
      -- z ∈ IntSet = QuotientSet (ω ×ₛ ω) IntEquivRel
      -- So z = EqClass p IntEquivRel (ω ×ₛ ω) for some p ∈ ω ×ₛ ω
      unfold IntSet at hz
      rw [mem_QuotientSet] at hz
      obtain ⟨p, hp_mem, hz_eq⟩ := hz
      rw [CartesianProduct_is_specified] at hp_mem
      obtain ⟨hp_pair, hp_fst, hp_snd⟩ := hp_mem
      -- isOrderedPair p means ∃ x y, p = ⟨x, y⟩
      obtain ⟨a, b, hp_eq⟩ := hp_pair
      subst hp_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hp_fst hp_snd
      -- Now z = EqClass ⟨a, b⟩ IntEquivRel (ω ×ₛ ω) = intClass a b
      have hz_class : z = intClass a b := hz_eq
      -- Use canonical_representative_exists
      have h_canon := canonical_representative_exists a b hp_fst hp_snd
      rcases h_canon with ⟨n, hn, h_eq⟩ | ⟨m, hm, hm_ne, h_eq⟩
      · -- Canonical form (n, 0)
        by_cases hn_ne : n = ∅
        · -- n = ∅: z = intClass ∅ ∅ = zeroZ
          left
          rw [hz_class, h_eq, hn_ne]
          rfl
        · -- n ≠ ∅: strictly positive
          right; left
          exact ⟨n, hn, hn_ne, by rw [hz_class, h_eq]⟩
      · -- Canonical form (0, m) with m ≠ ∅: strictly negative
        right; right
        exact ⟨m, hm, hm_ne, by rw [hz_class, h_eq]⟩

  end Int.Basic

end ZFC

export ZFC.Int.Basic (
  IntSet
  intClass
  zeroZ
  oneZ
  intClass_mem_IntSet
  zeroZ_mem_IntSet
  oneZ_mem_IntSet
  intClass_eq_iff
  canonical_pos_exists
  canonical_neg_exists
  canonical_representative_exists
  intClass_pos_injective
  intClass_neg_injective
  intClass_pos_ne_neg
  int_trichotomy
)
