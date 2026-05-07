/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones correspondientes.
-/

import ZFC.SetOps.Functions
import ZFC.Axiom.Infinity

/-!
# Tuples as ZFC Functions (Convention D9)

A tuple of degree n is a function with domain σ(n) = {0, 1, ..., n},
i.e., a set t such that `IsFunction t (σ n) Ω`.

## Main Definitions

* `IsTuple t n Ω` — t is an n-tuple with values in Ω
* `tupleGraph n Ω vals` — construct a tuple from a Lean function `vals : U → U`

## Main Theorems

* `tuple_apply_mem` — t⦅i⦆ ∈ Ω whenever i ∈ σ n
* `tupleGraph_isTuple` — tupleGraph produces a valid IsTuple
* `tupleGraph_apply` — (tupleGraph n Ω vals)⦅i⦆ = vals i
* `tuple_ext` — extensionality: equal on all indices implies equal as sets
* `zero_mem_sigma` — ∅ ∈ σ n for any n ∈ ω (index 0 always present)
-/

namespace ZFC
  open Classical
  open ExistsUnique
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
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  universe u
  variable {U : Type u}

  namespace SetOps.Tuple

    /-! ============================================================ -/
    /-! ### DEFINITION OF TUPLE ### -/
    /-! ============================================================ -/

    /-- A tuple of degree n with values in Ω is a function t : σ(n) → Ω.
        By convention D9, σ(n) = {0, 1, ..., n} has n+1 elements. -/
    def IsTuple (t n Ω : U) : Prop := n ∈ (ω : U) ∧ IsFunction t (σ n) Ω

    theorem isTuple_degree_mem_omega (t n Ω : U) (h : IsTuple t n Ω) : n ∈ (ω : U) :=
      h.1

    theorem isTuple_isFunction (t n Ω : U) (h : IsTuple t n Ω) : IsFunction t (σ n) Ω :=
      h.2

    theorem isTuple_subset (t n Ω : U) (h : IsTuple t n Ω) : t ⊆ (σ n) ×ₛ Ω :=
      h.2.1

    /-- The value t⦅i⦆ lies in Ω whenever i ∈ σ n. -/
    theorem tuple_apply_mem (t n Ω i : U) (ht : IsTuple t n Ω) (hi : i ∈ σ n) :
        t⦅i⦆ ∈ Ω := by
      have huniq := ht.2.2 i hi
      have h_pair := apply_mem t i huniq
      have h_in := ht.2.1 ⟨i, t⦅i⦆⟩ h_pair
      rw [OrderedPair_mem_CartesianProduct] at h_in
      exact h_in.2

    /-! ============================================================ -/
    /-! ### TUPLE CONSTRUCTION FROM LEAN FUNCTION ### -/
    /-! ============================================================ -/

    /-- Construct a tuple graph from a Lean-level function `vals : U → U`.
        `tupleGraph n Ω vals = { ⟨i, vals i⟩ | i ∈ σ n, vals i ∈ Ω }` -/
    noncomputable def tupleGraph (n Ω : U) (vals : U → U) : U :=
      sep (σ n ×ₛ Ω) (fun p => snd p = vals (fst p))

    theorem tupleGraph_mem_iff (n Ω : U) (vals : U → U) (p : U) :
        p ∈ tupleGraph n Ω vals ↔
        isOrderedPair p ∧ fst p ∈ σ n ∧ snd p ∈ Ω ∧ snd p = vals (fst p) := by
      unfold tupleGraph
      rw [mem_sep_iff, CartesianProduct_is_specified]
      constructor
      · intro h
        exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

    /-- `tupleGraph n Ω vals` is a valid tuple whenever vals maps σ n into Ω. -/
    theorem tupleGraph_isTuple (n Ω : U) (vals : U → U)
        (hn : n ∈ (ω : U))
        (hvals : ∀ i, i ∈ σ n → vals i ∈ Ω) :
        IsTuple (tupleGraph n Ω vals) n Ω := by
      refine ⟨hn, ?_, ?_⟩
      · -- tupleGraph n Ω vals ⊆ σ n ×ₛ Ω
        intro p hp
        rw [tupleGraph_mem_iff] at hp
        rw [CartesianProduct_is_specified]
        exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
      · -- ∀ i ∈ σ n, ∃! v, ⟨i, v⟩ ∈ tupleGraph n Ω vals
        intro i hi
        apply ExistsUnique.intro (vals i)
        · show ⟨i, vals i⟩ ∈ tupleGraph n Ω vals
          rw [tupleGraph_mem_iff, fst_of_ordered_pair, snd_of_ordered_pair]
          exact ⟨⟨i, vals i, rfl⟩, hi, hvals i hi, rfl⟩
        · intro v hv
          show v = vals i
          rw [tupleGraph_mem_iff, fst_of_ordered_pair, snd_of_ordered_pair] at hv
          exact hv.2.2.2

    /-- Applying a tupleGraph returns vals. -/
    theorem tupleGraph_apply (n Ω : U) (vals : U → U)
        (hn : n ∈ (ω : U)) (i : U) (hi : i ∈ σ n)
        (hvals : ∀ i, i ∈ σ n → vals i ∈ Ω) :
        (tupleGraph n Ω vals)⦅i⦆ = vals i := by
      have ht := tupleGraph_isTuple n Ω vals hn hvals
      apply apply_eq (tupleGraph n Ω vals) i (vals i)
      · exact ht.2.2 i hi
      · rw [tupleGraph_mem_iff, fst_of_ordered_pair, snd_of_ordered_pair]
        exact ⟨⟨i, vals i, rfl⟩, hi, hvals i hi, rfl⟩

    /-! ============================================================ -/
    /-! ### EXTENSIONALITY ### -/
    /-! ============================================================ -/

    /-- Two tuples over the same domain/codomain that agree on all indices are equal. -/
    theorem tuple_ext (t₁ t₂ n Ω : U)
        (ht₁ : IsTuple t₁ n Ω) (ht₂ : IsTuple t₂ n Ω)
        (h : ∀ i, i ∈ σ n → t₁⦅i⦆ = t₂⦅i⦆) : t₁ = t₂ := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        have h_sub := ht₁.2.1 p hp
        rw [CartesianProduct_is_specified] at h_sub
        obtain ⟨hop, hi, _⟩ := h_sub
        have h_wc : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p hop
        have h_unique₁ := ht₁.2.2 (fst p) hi
        have h_in₁ : ⟨fst p, snd p⟩ ∈ t₁ := by rw [← h_wc]; exact hp
        have hval₁ : t₁⦅fst p⦆ = snd p := apply_eq t₁ (fst p) (snd p) h_unique₁ h_in₁
        have hval₂ : t₂⦅fst p⦆ = snd p := by rw [← h (fst p) hi]; exact hval₁
        have h_unique₂ := ht₂.2.2 (fst p) hi
        have h_in₂ : ⟨fst p, snd p⟩ ∈ t₂ := by
          have := apply_mem t₂ (fst p) h_unique₂
          rwa [hval₂] at this
        rw [h_wc]; exact h_in₂
      · intro hp
        have h_sub := ht₂.2.1 p hp
        rw [CartesianProduct_is_specified] at h_sub
        obtain ⟨hop, hi, _⟩ := h_sub
        have h_wc : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p hop
        have h_unique₂ := ht₂.2.2 (fst p) hi
        have h_in₂ : ⟨fst p, snd p⟩ ∈ t₂ := by rw [← h_wc]; exact hp
        have hval₂ : t₂⦅fst p⦆ = snd p := apply_eq t₂ (fst p) (snd p) h_unique₂ h_in₂
        have hval₁ : t₁⦅fst p⦆ = snd p := by rw [h (fst p) hi]; exact hval₂
        have h_unique₁ := ht₁.2.2 (fst p) hi
        have h_in₁ : ⟨fst p, snd p⟩ ∈ t₁ := by
          have := apply_mem t₁ (fst p) h_unique₁
          rwa [hval₁] at this
        rw [h_wc]; exact h_in₁

    /-! ============================================================ -/
    /-! ### UTILITY LEMMA ### -/
    /-! ============================================================ -/

    /-- Index 0 = ∅ is always in σ n for any n ∈ ω. -/
    theorem zero_mem_sigma (n : U) (hn : n ∈ (ω : U)) : (∅ : U) ∈ σ n := by
      rw [mem_succ_iff]
      rcases Classical.em (n = ∅) with h | h
      · exact Or.inr h.symm
      · exact Or.inl (zero_mem_of_nat_nonempty n (mem_Omega_is_Nat n hn) h)

  end SetOps.Tuple

  export SetOps.Tuple (
    IsTuple
    isTuple_degree_mem_omega
    isTuple_isFunction
    isTuple_subset
    tuple_apply_mem
    tupleGraph
    tupleGraph_mem_iff
    tupleGraph_isTuple
    tupleGraph_apply
    tuple_ext
    zero_mem_sigma
  )

end ZFC
