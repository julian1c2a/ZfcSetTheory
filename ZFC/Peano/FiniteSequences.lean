/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Finite Sequences in ZFC

This module develops the theory of finite sequences as functions f : n → A
where n ∈ ω (Von Neumann naturals) and A is any set.

## Main Definitions

* `isFinSeq f n A`   — f is a finite sequence of length n in A
* `FinSeqSet n A`    — the set of all n-sequences in A
* `appendElem f n a` — extend f : n → A to (σ n) → A by appending a at index n
* `seqLength f`      — the length (= domain) of a finite sequence
* `concatSeq f n g m A` — concatenation of f : n → A and g : m → A

## Main Theorems

* `isFinSeq_empty`         — ∅ : ∅ → A is a valid 0-sequence
* `isFinSeq_appendElem`    — appending preserves isFinSeq
* `isFinSeq_restriction`   — restricting a (σ n)-sequence to n gives an n-sequence
* `appendElem_apply_last`  — last element access
* `appendElem_apply_prev`  — previous elements unchanged
* `concatSeq_isFinSeq`     — concatenation yields a (n+m)-sequence
* `concatSeq_left`         — accessing left part of concatenation
* `concatSeq_right`        — accessing right part of concatenation
-/

import ZFC.Nat.Add

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Cardinal.Basic
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  open ZFC.Nat.Add
  universe u
  variable {U : Type u}

  namespace Peano.FiniteSequences

    /-! ============================================================ -/
    /-! ### SECTION 1: CORE PREDICATE ### -/
    /-! ============================================================ -/

    /-- A finite sequence of length n in A: n ∈ ω and f is a function from n to A. -/
    def isFinSeq (f n A : U) : Prop :=
      n ∈ ω ∧ IsFunction f n A

    theorem isFinSeq_in_Omega {f n A : U} (h : isFinSeq f n A) : n ∈ ω :=
      h.1

    theorem isFinSeq_is_function {f n A : U} (h : isFinSeq f n A) :
        IsFunction f n A :=
      h.2

    theorem isFinSeq_domain {f n A : U} (h : isFinSeq f n A) : domain f = n :=
      function_domain_eq f n A h.2

    theorem isFinSeq_subset {f n A : U} (h : isFinSeq f n A) : f ⊆ n ×ₛ A :=
      h.2.1

    /-- The length of a finite sequence is unique: if f : n → A and f : m → A then n = m. -/
    theorem isFinSeq_unique_length {f n m A : U}
        (hn : isFinSeq f n A) (hm : isFinSeq f m A) : n = m := by
      rw [← isFinSeq_domain hn, isFinSeq_domain hm]

    /-- Application of a finite sequence at index i lies in A. -/
    theorem isFinSeq_apply_mem {f n A i : U}
        (h : isFinSeq f n A) (hi : i ∈ n) : f⦅i⦆ ∈ A := by
      have h_unique : ∃! y, ⟨i, y⟩ ∈ f := h.2.2 i hi
      have h_mem : ⟨i, f⦅i⦆⟩ ∈ f := apply_mem f i h_unique
      have h_pair : ⟨i, f⦅i⦆⟩ ∈ n ×ₛ A := h.2.1 _ h_mem
      rw [OrderedPair_mem_CartesianProduct] at h_pair
      exact h_pair.2

    /-- The pair ⟨i, f⦅i⦆⟩ belongs to f for every index i in the domain. -/
    theorem isFinSeq_pair_mem {f n A i : U}
        (h : isFinSeq f n A) (hi : i ∈ n) : ⟨i, f⦅i⦆⟩ ∈ f :=
      apply_mem f i (h.2.2 i hi)

    /-- Extensionality: two finite sequences of the same length agreeing on every index are equal. -/
    theorem isFinSeq_ext {f g n A : U}
        (hf : isFinSeq f n A) (hg : isFinSeq g n A)
        (hval : ∀ i, i ∈ n → f⦅i⦆ = g⦅i⦆) : f = g := by
      apply eq_of_subset_of_subset
      · intro p hp
        obtain ⟨hpair, hfst, _⟩ := (CartesianProduct_is_specified n A p).mp (hf.2.1 p hp)
        have hp_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hpair
        rw [hp_eq] at hp
        have h_snd : f⦅fst p⦆ = snd p :=
          apply_eq f (fst p) (snd p) (hf.2.2 (fst p) hfst) hp
        rw [hp_eq, ← h_snd, hval (fst p) hfst]
        exact apply_mem g (fst p) (hg.2.2 (fst p) hfst)
      · intro p hp
        obtain ⟨hpair, hfst, _⟩ := (CartesianProduct_is_specified n A p).mp (hg.2.1 p hp)
        have hp_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hpair
        rw [hp_eq] at hp
        have h_snd : g⦅fst p⦆ = snd p :=
          apply_eq g (fst p) (snd p) (hg.2.2 (fst p) hfst) hp
        rw [hp_eq, ← h_snd, ← hval (fst p) hfst]
        exact apply_mem f (fst p) (hf.2.2 (fst p) hfst)

    /-! ============================================================ -/
    /-! ### SECTION 2: FinSeqSet ### -/
    /-! ============================================================ -/

    /-- The set of all n-sequences in A. -/
    noncomputable def FinSeqSet (n A : U) : U :=
      sep (𝒫(n ×ₛ A)) (fun f => n ∈ ω ∧ IsFunction f n A)

    theorem mem_FinSeqSet_iff {f n A : U} : f ∈ FinSeqSet n A ↔ isFinSeq f n A := by
      unfold FinSeqSet isFinSeq
      rw [mem_sep_iff]
      constructor
      · intro h; exact h.2
      · intro h
        exact ⟨(mem_powerset_iff (n ×ₛ A) f).mpr h.2.1, h⟩

    theorem isFinSeq_mem_FinSeqSet {f n A : U} (h : isFinSeq f n A) :
        f ∈ FinSeqSet n A :=
      mem_FinSeqSet_iff.mpr h

    /-! ============================================================ -/
    /-! ### SECTION 3: EMPTY SEQUENCE ### -/
    /-! ============================================================ -/

    /-- The empty function ∅ is a finite sequence of length 0. -/
    theorem isFinSeq_empty (A : U) : isFinSeq (∅ : U) (∅ : U) A := by
      refine ⟨zero_in_Omega, ?_, ?_⟩
      · intro p hp; exact absurd hp (EmptySet_is_empty p)
      · intro x hx; exact absurd hx (EmptySet_is_empty x)

    /-- The only 0-sequence is ∅. -/
    theorem isFinSeq_zero_unique {f A : U} (h : isFinSeq f ∅ A) : f = ∅ := by
      apply eq_of_subset_of_subset
      · intro p hp
        have h_mem := h.2.1 p hp
        rw [CartesianProduct_empty_left] at h_mem
        exact absurd h_mem (EmptySet_is_empty p)
      · intro p hp; exact absurd hp (EmptySet_is_empty p)

    /-- The set of 0-sequences contains only ∅. -/
    theorem FinSeqSet_zero (A : U) : FinSeqSet (∅ : U) A = {(∅ : U)} := by
      apply ExtSet
      intro f
      rw [mem_FinSeqSet_iff, Singleton_is_specified]
      exact ⟨isFinSeq_zero_unique, fun hf => hf ▸ isFinSeq_empty A⟩

    /-! ============================================================ -/
    /-! ### SECTION 4: appendElem ### -/
    /-! ============================================================ -/

    /-- Extend f : n → A by appending element a at new index n.
        Since n ∉ n (not_mem_self), no collision occurs. -/
    noncomputable def appendElem (f n a : U) : U := f ∪ {⟨n, a⟩}

    /-- Characterization of membership in appendElem. -/
    theorem appendElem_is_specified {f n a x : U} :
        x ∈ appendElem f n a ↔ x ∈ f ∨ x = ⟨n, a⟩ := by
      unfold appendElem
      rw [mem_union_iff, Singleton_is_specified]

    /-- n is a subset of its own succ. -/
    private theorem nat_subset_succ (n : U) : n ⊆ σ n :=
      fun x hx => (mem_succ_iff n x).mpr (Or.inl hx)

    /-- Appending an element a ∈ A to a finite n-sequence gives a finite (σ n)-sequence. -/
    theorem isFinSeq_appendElem {f n A a : U}
        (hf : isFinSeq f n A) (ha : a ∈ A) : isFinSeq (appendElem f n a) (σ n) A := by
      have hn_nat : IsNat n := mem_Omega_is_Nat n hf.1
      constructor
      · exact Nat_in_Omega (σ n) (isNat_succ n hn_nat)
      · constructor
        · -- appendElem f n a ⊆ σ n ×ₛ A
          intro p hp
          rw [appendElem_is_specified] at hp
          cases hp with
          | inl hp_f =>
            have h1 := (CartesianProduct_is_specified n A p).mp (hf.2.1 p hp_f)
            rw [CartesianProduct_is_specified]
            exact ⟨h1.1, nat_subset_succ n _ h1.2.1, h1.2.2⟩
          | inr hp_eq =>
            rw [hp_eq, OrderedPair_mem_CartesianProduct]
            exact ⟨mem_succ_self n, ha⟩
        · -- ∀ x ∈ σ n, ∃! y, ⟨x, y⟩ ∈ appendElem f n a
          intro x hx
          rw [mem_succ_iff] at hx
          cases hx with
          | inl hx_n =>
            obtain ⟨y, hy_in, hy_uniq⟩ := hf.2.2 x hx_n
            apply ExistsUnique.intro y
            · rw [appendElem_is_specified]; exact Or.inl hy_in
            · intro y' hy'
              rw [appendElem_is_specified] at hy'
              cases hy' with
              | inl hy'_f => exact hy_uniq y' hy'_f
              | inr hy'_eq =>
                have hxn := (Eq_of_OrderedPairs_given_projections x y' n a hy'_eq).1
                exact absurd (hxn ▸ hx_n) (not_mem_self n hn_nat)
          | inr hx_eq =>
            apply ExistsUnique.intro a
            · rw [hx_eq, appendElem_is_specified]; exact Or.inr rfl
            · intro y' hy'
              rw [hx_eq] at hy'
              rw [appendElem_is_specified] at hy'
              cases hy' with
              | inl hy'_f =>
                have hn_dom : n ∈ domain f :=
                  (mem_domain f n).mpr ⟨y', hy'_f⟩
                exact absurd (isFinSeq_domain hf ▸ hn_dom) (not_mem_self n hn_nat)
              | inr hy'_eq =>
                exact (Eq_of_OrderedPairs_given_projections n y' n a hy'_eq).2

    /-- The new element a is accessed at the last index n. -/
    theorem appendElem_apply_last {f n A a : U} (hf : isFinSeq f n A) :
        (appendElem f n a)⦅n⦆ = a := by
      have hn_nat : IsNat n := mem_Omega_is_Nat n hf.1
      have h_pair_mem : ⟨n, a⟩ ∈ appendElem f n a := by
        rw [appendElem_is_specified]; exact Or.inr rfl
      have h_unique : ∃! y, ⟨n, y⟩ ∈ appendElem f n a := by
        apply ExistsUnique.intro a
        · exact h_pair_mem
        · intro y' hy'
          rw [appendElem_is_specified] at hy'
          cases hy' with
          | inl hy'_f =>
            exact absurd (isFinSeq_domain hf ▸ (mem_domain f n).mpr ⟨y', hy'_f⟩)
              (not_mem_self n hn_nat)
          | inr hy'_eq =>
            exact (Eq_of_OrderedPairs_given_projections n y' n a hy'_eq).2
      exact apply_eq (appendElem f n a) n a h_unique h_pair_mem

    /-- Previous elements are unchanged after appending. -/
    theorem appendElem_apply_prev {f n A a i : U}
        (hf : isFinSeq f n A) (hi : i ∈ n) :
        (appendElem f n a)⦅i⦆ = f⦅i⦆ := by
      have hn_nat : IsNat n := mem_Omega_is_Nat n hf.1
      have hi_ne : i ≠ n := fun h => absurd (h ▸ hi) (not_mem_self n hn_nat)
      have h_mem : ⟨i, f⦅i⦆⟩ ∈ appendElem f n a := by
        rw [appendElem_is_specified]
        exact Or.inl (isFinSeq_pair_mem hf hi)
      have h_unique : ∃! y, ⟨i, y⟩ ∈ appendElem f n a := by
        apply ExistsUnique.intro (f⦅i⦆)
        · exact h_mem
        · intro y' hy'
          rw [appendElem_is_specified] at hy'
          cases hy' with
          | inl hy'_f =>
            exact (apply_eq f i y' (hf.2.2 i hi) hy'_f).symm
          | inr hy'_eq =>
            exact absurd (Eq_of_OrderedPairs_given_projections i y' n a hy'_eq).1 hi_ne
      exact apply_eq (appendElem f n a) i (f⦅i⦆) h_unique h_mem

    /-- appendElem is injective in the appended element. -/
    theorem appendElem_inj {f n A a b : U}
        (hf : isFinSeq f n A)
        (h : appendElem f n a = appendElem f n b) : a = b := by
      have := appendElem_apply_last hf (a := a)
      have hb_eq := appendElem_apply_last hf (a := b)
      rw [h] at this
      rw [← this, hb_eq]

    /-! ============================================================ -/
    /-! ### SECTION 5: DECOMPOSITION AND INDUCTION ### -/
    /-! ============================================================ -/

    /-- Restricting a (σ n)-sequence to n gives an n-sequence. -/
    theorem isFinSeq_restriction {f n A : U} (h : isFinSeq f (σ n) A) :
        isFinSeq (f ↾ n) n A := by
      have hσn_nat : IsNat (σ n) := mem_Omega_is_Nat (σ n) h.1
      have hn_nat : IsNat n := nat_element_is_nat (σ n) n hσn_nat (mem_succ_self n)
      have hn_omega : n ∈ ω := Nat_in_Omega n hn_nat
      have hn_sub : n ⊆ σ n := nat_subset_succ n
      exact ⟨hn_omega, restrict_is_function f (σ n) A n h.2 hn_sub⟩

    /-! ============================================================ -/
    /-! ### SECTION 6: LENGTH ### -/
    /-! ============================================================ -/

    /-- The length of a finite sequence is its domain. -/
    noncomputable def seqLength (f : U) : U := domain f

    /-- For a finite sequence f : n → A, seqLength f = n. -/
    theorem seqLength_eq {f n A : U} (h : isFinSeq f n A) : seqLength f = n :=
      isFinSeq_domain h

    /-- The length of a finite sequence is in ω. -/
    theorem seqLength_in_Omega {f n A : U} (h : isFinSeq f n A) : seqLength f ∈ ω :=
      seqLength_eq h ▸ h.1

    /-- The length of the empty sequence is ∅. -/
    theorem seqLength_empty : seqLength (∅ : U) = (∅ : U) := by
      unfold seqLength domain
      apply ExtSet
      intro x
      rw [mem_sep_iff]
      constructor
      · intro h
        obtain ⟨_, y, hy⟩ := h
        exact absurd hy (EmptySet_is_empty ⟨x, y⟩)
      · intro hx; exact absurd hx (EmptySet_is_empty x)

    /-- After appending, the length is σ n. -/
    theorem seqLength_appendElem {f n A a : U} (hf : isFinSeq f n A) (ha : a ∈ A) :
        seqLength (appendElem f n a) = σ n :=
      seqLength_eq (isFinSeq_appendElem hf ha)

    /-! ============================================================ -/
    /-! ### SECTION 7: AUXILIARY ADD-MEMBERSHIP LEMMAS ### -/
    /-! ============================================================ -/

    /-- add n j ∉ n for n, j ∈ ω. -/
    theorem add_not_mem_left (n j : U) (hn : n ∈ (ω : U)) (hj : j ∈ (ω : U)) :
        add n j ∉ n := by
      intro h_mem
      have hn_nat := mem_Omega_is_Nat n hn
      by_cases hj_ne : j = ∅
      · rw [hj_ne, add_zero n hn] at h_mem
        exact not_mem_self n hn_nat h_mem
      · have h_n_in := add_pos_left_Omega j n hj hn hj_ne
        have hn_trans : ∀ x, x ∈ n → x ⊆ n := hn_nat.1
        have h_sub : (add n j) ⊆ n := hn_trans (add n j) h_mem
        exact not_mem_self n hn_nat (h_sub n h_n_in)

    /-- i ∈ n → i ∈ add n m for n, m ∈ ω. -/
    theorem mem_add_of_mem_left {i n m : U} (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hi : i ∈ n) : i ∈ add n m := by
      -- Induction on m
      let P : U → Prop := fun k => i ∈ add n k
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hm_S : m ∈ S := hS ▸ hm
        exact ((mem_sep_iff (ω : U) m P).mp hm_S).2
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · rw [mem_sep_iff]
        exact ⟨zero_in_Omega, by simp only [P]; rw [add_zero n hn]; exact hi⟩
      · intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        simp only [P] at ih ⊢
        constructor
        · exact succ_in_Omega k hk_omega
        · rw [add_succ n k hn hk_omega]
          exact mem_succ_of_mem i (add n k) ih

    /-- Partition: i ∈ add n m → i ∈ n ∨ (∃ j ∈ m, i = add n j). -/
    theorem add_partition {i n m : U} (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hi : i ∈ add n m) : i ∈ n ∨ (∃ j, j ∈ m ∧ i = add n j) := by
      -- Induction on m
      let P : U → Prop := fun k => ∀ x, x ∈ add n k →
        x ∈ n ∨ (∃ j, j ∈ k ∧ x = add n j)
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have hm_S : m ∈ S := hS ▸ hm
        exact ((mem_sep_iff (ω : U) m P).mp hm_S).2 i hi
      apply induction_principle S
      · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
      · rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        simp only [P]
        intro x hx
        rw [add_zero n hn] at hx
        exact Or.inl hx
      · intro k hk
        rw [mem_sep_iff] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        simp only [P] at ih ⊢
        constructor
        · exact succ_in_Omega k hk_omega
        · intro x hx
          rw [add_succ n k hn hk_omega, mem_succ_iff] at hx
          cases hx with
          | inl hx_prev =>
            cases ih x hx_prev with
            | inl hx_n => exact Or.inl hx_n
            | inr h_ex =>
              obtain ⟨j, hj_k, hx_eq⟩ := h_ex
              exact Or.inr ⟨j, mem_succ_of_mem j k hj_k, hx_eq⟩
          | inr hx_eq =>
            exact Or.inr ⟨k, mem_succ_self k, hx_eq⟩

    /-! ============================================================ -/
    /-! ### SECTION 8: CONCATENATION ### -/
    /-! ============================================================ -/

    /-- The shifted graph: {⟨add n j, g⦅j⦆⟩ | j ∈ m}. -/
    noncomputable def shiftedGraph (n g m A : U) : U :=
      sep ((add n m) ×ₛ A) (fun p => ∃ j, j ∈ m ∧ p = ⟨add n j, g⦅j⦆⟩)

    /-- Membership characterization for shiftedGraph. -/
    theorem mem_shiftedGraph {n g m A p : U} :
        p ∈ shiftedGraph n g m A ↔
        (p ∈ (add n m) ×ₛ A ∧ ∃ j, j ∈ m ∧ p = ⟨add n j, g⦅j⦆⟩) := by
      unfold shiftedGraph
      rw [mem_sep_iff]

    /-- Concatenation of f : n → A and g : m → A. -/
    noncomputable def concatSeq (f n g m A : U) : U :=
      f ∪ shiftedGraph n g m A

    /-- Concatenation produces a valid (add n m)-sequence. -/
    theorem concatSeq_isFinSeq {f n g m A : U}
        (hf : isFinSeq f n A) (hg : isFinSeq g m A) :
        isFinSeq (concatSeq f n g m A) (add n m) A := by
      have hn := hf.1
      have hm := hg.1
      have hn_nat := mem_Omega_is_Nat n hn
      have hnm := add_in_Omega n m hn hm
      constructor
      · exact hnm
      · constructor
        · -- concatSeq ⊆ (add n m) ×ₛ A
          intro p hp
          unfold concatSeq at hp
          rw [mem_union_iff] at hp
          cases hp with
          | inl hp_f =>
            have h := hf.2.1 p hp_f
            rw [CartesianProduct_is_specified] at h ⊢
            exact ⟨h.1, mem_add_of_mem_left hn hm h.2.1, h.2.2⟩
          | inr hp_g =>
            rw [mem_shiftedGraph] at hp_g
            exact hp_g.1
        · -- ∀ i ∈ add n m, ∃! y, ⟨i, y⟩ ∈ concatSeq
          intro i hi
          cases add_partition hn hm hi with
          | inl hi_n =>
            -- i ∈ n: use f
            obtain ⟨y, hy, hy_uniq⟩ := hf.2.2 i hi_n
            apply ExistsUnique.intro y
            · exact (mem_union_iff f (shiftedGraph n g m A) ⟨i, y⟩).mpr (Or.inl hy)
            · intro y' hy'
              unfold concatSeq at hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl hy'_f => exact hy_uniq y' hy'_f
              | inr hy'_sg =>
                rw [mem_shiftedGraph] at hy'_sg
                obtain ⟨_, j, hj, hpair_eq⟩ := hy'_sg
                have h_fst := (Eq_of_OrderedPairs_given_projections i y' (add n j) (g⦅j⦆) hpair_eq).1
                have hj_omega : j ∈ (ω : U) :=
                  Nat_in_Omega j (nat_element_is_nat m j (mem_Omega_is_Nat m hm) hj)
                exact absurd (h_fst ▸ hi_n) (add_not_mem_left n j hn hj_omega)
          | inr h_ex =>
            -- i = add n j with j ∈ m: use g
            obtain ⟨j, hj, hi_eq⟩ := h_ex
            have hj_omega : j ∈ (ω : U) :=
              Nat_in_Omega j (nat_element_is_nat m j (mem_Omega_is_Nat m hm) hj)
            obtain ⟨y, hy, hy_uniq⟩ := hg.2.2 j hj
            apply ExistsUnique.intro y
            · rw [hi_eq]
              have h_apply_eq : y = g⦅j⦆ :=
                (apply_eq g j y (hg.2.2 j hj) hy).symm
              rw [h_apply_eq]
              apply (mem_union_iff f (shiftedGraph n g m A) ⟨add n j, g⦅j⦆⟩).mpr
              exact Or.inr (mem_shiftedGraph.mpr
                ⟨(OrderedPair_mem_CartesianProduct (add n j) (g⦅j⦆) (add n m) A).mpr
                  ⟨add_lt_of_lt_Omega n j m hn hj_omega hm hj, isFinSeq_apply_mem hg hj⟩,
                 j, hj, rfl⟩)
            · intro y' hy'
              rw [hi_eq] at hy'
              unfold concatSeq at hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl hy'_f =>
                -- ⟨add n j, y'⟩ ∈ f, but add n j ∉ n — contradiction
                have h_cart := hf.2.1 _ hy'_f
                rw [OrderedPair_mem_CartesianProduct] at h_cart
                exact absurd h_cart.1 (add_not_mem_left n j hn hj_omega)
              | inr hy'_sg =>
                rw [mem_shiftedGraph] at hy'_sg
                obtain ⟨_, j', hj', hpair_eq⟩ := hy'_sg
                have hj'_omega : j' ∈ (ω : U) :=
                  Nat_in_Omega j' (nat_element_is_nat m j' (mem_Omega_is_Nat m hm) hj')
                obtain ⟨h_add_eq, h_y'_eq⟩ :=
                  Eq_of_OrderedPairs_given_projections (add n j) y' (add n j') (g⦅j'⦆) hpair_eq
                have hj_eq : j = j' := add_left_cancel_Omega n j j' hn hj_omega hj'_omega h_add_eq
                subst hj_eq
                rw [h_y'_eq]
                exact apply_eq g j y (hg.2.2 j hj) hy

    /-- Left part of concatenation: for i ∈ n, (concatSeq f n g m A)⦅i⦆ = f⦅i⦆. -/
    theorem concatSeq_left {f n g m A i : U}
        (hf : isFinSeq f n A) (hg : isFinSeq g m A) (hi : i ∈ n) :
        (concatSeq f n g m A)⦅i⦆ = f⦅i⦆ := by
      have hn := hf.1
      have hm := hg.1
      have h_concat := concatSeq_isFinSeq hf hg
      have hi_add : i ∈ add n m := mem_add_of_mem_left hn hm hi
      have h_pair : ⟨i, f⦅i⦆⟩ ∈ concatSeq f n g m A :=
        (mem_union_iff f (shiftedGraph n g m A) ⟨i, f⦅i⦆⟩).mpr
          (Or.inl (isFinSeq_pair_mem hf hi))
      exact apply_eq (concatSeq f n g m A) i (f⦅i⦆)
        (h_concat.2.2 i hi_add) h_pair

    /-- Right part of concatenation: for j ∈ m, (concatSeq f n g m A)⦅add n j⦆ = g⦅j⦆. -/
    theorem concatSeq_right {f n g m A j : U}
        (hf : isFinSeq f n A) (hg : isFinSeq g m A) (hj : j ∈ m) :
        (concatSeq f n g m A)⦅add n j⦆ = g⦅j⦆ := by
      have hn := hf.1
      have hm := hg.1
      have hj_omega : j ∈ (ω : U) :=
        Nat_in_Omega j (nat_element_is_nat m j (mem_Omega_is_Nat m hm) hj)
      have h_concat := concatSeq_isFinSeq hf hg
      have hi_add : add n j ∈ add n m := add_lt_of_lt_Omega n j m hn hj_omega hm hj
      have h_pair : ⟨add n j, g⦅j⦆⟩ ∈ concatSeq f n g m A :=
        (mem_union_iff f (shiftedGraph n g m A) ⟨add n j, g⦅j⦆⟩).mpr
          (Or.inr (mem_shiftedGraph.mpr
            ⟨(OrderedPair_mem_CartesianProduct (add n j) (g⦅j⦆) (add n m) A).mpr
              ⟨hi_add, isFinSeq_apply_mem hg hj⟩,
             j, hj, rfl⟩))
      exact apply_eq (concatSeq f n g m A) (add n j) (g⦅j⦆)
        (h_concat.2.2 (add n j) hi_add) h_pair

    /-- Length of concatenation. -/
    theorem concatSeq_length {f n g m A : U}
        (hf : isFinSeq f n A) (hg : isFinSeq g m A) :
        seqLength (concatSeq f n g m A) = add n m :=
      seqLength_eq (concatSeq_isFinSeq hf hg)

    /-- Concatenation with empty right sequence. -/
    theorem concatSeq_empty_right {f n A : U} (_hf : isFinSeq f n A) :
        concatSeq f n ∅ ∅ A = f := by
      unfold concatSeq shiftedGraph
      have h_sg_empty : sep ((add n ∅) ×ₛ A)
          (fun p => ∃ j, j ∈ (∅ : U) ∧ p = ⟨add n j, (∅ : U)⦅j⦆⟩) = ∅ := by
        apply ExtSet
        intro x
        rw [mem_sep_iff]
        constructor
        · intro ⟨_, j, hj, _⟩; exact absurd hj (EmptySet_is_empty j)
        · intro hx; exact absurd hx (EmptySet_is_empty x)
      rw [h_sg_empty]
      apply ExtSet
      intro x
      rw [mem_union_iff]
      constructor
      · intro h; cases h with
        | inl h => exact h
        | inr h => exact absurd h (EmptySet_is_empty x)
      · intro h; exact Or.inl h

  end Peano.FiniteSequences

  export Peano.FiniteSequences (
    -- Section 1: Core predicate
    isFinSeq
    isFinSeq_in_Omega
    isFinSeq_is_function
    isFinSeq_domain
    isFinSeq_subset
    isFinSeq_unique_length
    isFinSeq_apply_mem
    isFinSeq_pair_mem
    isFinSeq_ext
    -- Section 2: FinSeqSet
    FinSeqSet
    mem_FinSeqSet_iff
    isFinSeq_mem_FinSeqSet
    -- Section 3: Empty sequence
    isFinSeq_empty
    isFinSeq_zero_unique
    FinSeqSet_zero
    -- Section 4: appendElem
    appendElem
    appendElem_is_specified
    isFinSeq_appendElem
    appendElem_apply_last
    appendElem_apply_prev
    appendElem_inj
    -- Section 5: Decomposition
    isFinSeq_restriction
    -- Section 6: Length
    seqLength
    seqLength_eq
    seqLength_in_Omega
    seqLength_empty
    seqLength_appendElem
    -- Section 7: Auxiliary add-membership lemmas
    add_not_mem_left
    mem_add_of_mem_left
    add_partition
    -- Section 8: Concatenation
    shiftedGraph
    mem_shiftedGraph
    concatSeq
    concatSeq_isFinSeq
    concatSeq_left
    concatSeq_right
    concatSeq_length
    concatSeq_empty_right
  )

end ZFC
