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

## Main Theorems

* `isFinSeq_empty`         — ∅ : ∅ → A is a valid 0-sequence
* `isFinSeq_appendElem`    — appending preserves isFinSeq
* `isFinSeq_restriction`   — restricting a (σ n)-sequence to n gives an n-sequence
* `appendElem_apply_last`  — last element access
* `appendElem_apply_prev`  — previous elements unchanged
-/

import ZfcSetTheory.NaturalNumbersAdd

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  open SetUniverse.NaturalNumbers
  open SetUniverse.InfinityAxiom
  universe u
  variable {U : Type u}

  namespace FiniteSequences

    /-! ============================================================ -/
    /-! ### SECTION 1: CORE PREDICATE ### -/
    /-! ============================================================ -/

    /-- A finite sequence of length n in A: n ∈ ω and f is a function from n to A. -/
    def isFinSeq (f n A : U) : Prop :=
      n ∈ ω ∧ isFunctionFromTo f n A

    theorem isFinSeq_in_Omega {f n A : U} (h : isFinSeq f n A) : n ∈ ω :=
      h.1

    theorem isFinSeq_is_function {f n A : U} (h : isFinSeq f n A) :
        isFunctionFromTo f n A :=
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
      apply ExtSet_wc
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
      SpecSet (𝒫(n ×ₛ A)) (fun f => n ∈ ω ∧ isFunctionFromTo f n A)

    theorem mem_FinSeqSet_iff {f n A : U} : f ∈ FinSeqSet n A ↔ isFinSeq f n A := by
      unfold FinSeqSet isFinSeq
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        exact ⟨(PowerSet_is_specified (n ×ₛ A) f).mpr h.2.1, h⟩

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
      apply ExtSet_wc
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
        Since n ∉ n (nat_not_mem_self), no collision occurs. -/
    noncomputable def appendElem (f n a : U) : U := f ∪ {⟨n, a⟩}

    /-- Characterization of membership in appendElem. -/
    theorem appendElem_is_specified {f n a x : U} :
        x ∈ appendElem f n a ↔ x ∈ f ∨ x = ⟨n, a⟩ := by
      unfold appendElem
      rw [BinUnion_is_specified, Singleton_is_specified]

    /-- n is a subset of its own successor. -/
    private theorem nat_subset_succ (n : U) : n ⊆ σ n :=
      fun x hx => (successor_is_specified n x).mpr (Or.inl hx)

    /-- Appending an element a ∈ A to a finite n-sequence gives a finite (σ n)-sequence. -/
    theorem isFinSeq_appendElem {f n A a : U}
        (hf : isFinSeq f n A) (ha : a ∈ A) : isFinSeq (appendElem f n a) (σ n) A := by
      have hn_nat : isNat n := mem_Omega_is_Nat n hf.1
      constructor
      · exact Nat_in_Omega (σ n) (nat_successor_is_nat n hn_nat)
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
            exact ⟨mem_successor_self n, ha⟩
        · -- ∀ x ∈ σ n, ∃! y, ⟨x, y⟩ ∈ appendElem f n a
          intro x hx
          rw [successor_is_specified] at hx
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
                exact absurd (hxn ▸ hx_n) (nat_not_mem_self n hn_nat)
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
                exact absurd (isFinSeq_domain hf ▸ hn_dom) (nat_not_mem_self n hn_nat)
              | inr hy'_eq =>
                exact (Eq_of_OrderedPairs_given_projections n y' n a hy'_eq).2

    /-- The new element a is accessed at the last index n. -/
    theorem appendElem_apply_last {f n A a : U} (hf : isFinSeq f n A) :
        (appendElem f n a)⦅n⦆ = a := by
      have hn_nat : isNat n := mem_Omega_is_Nat n hf.1
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
              (nat_not_mem_self n hn_nat)
          | inr hy'_eq =>
            exact (Eq_of_OrderedPairs_given_projections n y' n a hy'_eq).2
      exact apply_eq (appendElem f n a) n a h_unique h_pair_mem

    /-- Previous elements are unchanged after appending. -/
    theorem appendElem_apply_prev {f n A a i : U}
        (hf : isFinSeq f n A) (hi : i ∈ n) :
        (appendElem f n a)⦅i⦆ = f⦅i⦆ := by
      have hn_nat : isNat n := mem_Omega_is_Nat n hf.1
      have hi_ne : i ≠ n := fun h => absurd (h ▸ hi) (nat_not_mem_self n hn_nat)
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
      have hσn_nat : isNat (σ n) := mem_Omega_is_Nat (σ n) h.1
      have hn_nat : isNat n := nat_element_is_nat (σ n) n hσn_nat (mem_successor_self n)
      have hn_omega : n ∈ ω := Nat_in_Omega n hn_nat
      have hn_sub : n ⊆ σ n := nat_subset_succ n
      exact ⟨hn_omega, Restriction_is_function f (σ n) A n h.2 hn_sub⟩

  end FiniteSequences

end SetUniverse
