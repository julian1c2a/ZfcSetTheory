/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Sequences in ℚ

  This module defines sequences in ℚ as functions f : ω → RatSet
  and establishes their basic closure and operational properties.
  Sequences are the foundation for convergence, Cauchy sequences,
  and the eventual proof of incompleteness of ℚ.

  ## Main Definitions

  * `IsSeqQ f`      — f is a sequence in ℚ: IsFunction f ω RatSet
  * `constSeqQ a`   — constant sequence: f(n) = a for all n ∈ ω
  * `addSeqQ f g`   — pointwise sum:      (f + g)(n) = f(n) + g(n)
  * `negSeqQ f`     — pointwise negation: (−f)(n) = −f(n)
  * `mulSeqQ f g`   — pointwise product:  (f · g)(n) = f(n) · g(n)

  ## Main Theorems

  * `seqTermQ_mem_RatSet`  — f⦅n⦆ ∈ ℚ for any sequence f and n ∈ ω
  * `constSeqQ_isSeqQ`     — constSeqQ a is a sequence (for a ∈ ℚ)
  * `constSeqQ_apply`      — (constSeqQ a)⦅n⦆ = a
  * `addSeqQ_isSeqQ`       — addSeqQ f g is a sequence (given f, g sequences)
  * `addSeqQ_apply`        — (addSeqQ f g)⦅n⦆ = f⦅n⦆ + g⦅n⦆
  * `negSeqQ_isSeqQ`       — negSeqQ f is a sequence
  * `negSeqQ_apply`        — (negSeqQ f)⦅n⦆ = −f⦅n⦆
  * `mulSeqQ_isSeqQ`       — mulSeqQ f g is a sequence
  * `mulSeqQ_apply`        — (mulSeqQ f g)⦅n⦆ = f⦅n⦆ · g⦅n⦆

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Mul

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
  open ZFC.Int.Basic
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul

  universe u
  variable {U : Type u}

  namespace Rat.Sequences

    -- =========================================================================
    -- Section 1: Definition
    -- =========================================================================

    /-- A sequence in ℚ is a function f : ω → RatSet -/
    def IsSeqQ (f : U) : Prop := IsFunction f (ω : U) (RatSet : U)

    -- =========================================================================
    -- Section 2: Basic membership
    -- =========================================================================

    /-- The n-th term of a sequence lies in ℚ -/
    theorem seqTermQ_mem_RatSet (f n : U)
        (hf : IsSeqQ f) (hn : n ∈ (ω : U)) :
        f⦅n⦆ ∈ (RatSet : U) := by
      have h_unique := hf.2 n hn
      have h_pair := apply_mem f n h_unique
      have h_in_prod := hf.1 ⟨n, f⦅n⦆⟩ h_pair
      rw [OrderedPair_mem_CartesianProduct] at h_in_prod
      exact h_in_prod.2

    -- =========================================================================
    -- Section 3: Constant sequence
    -- =========================================================================

    /-- Constant sequence at a: the Cartesian product ω × {a} -/
    noncomputable def constSeqQ (a : U) : U := (ω : U) ×ₛ ({a} : U)

    /-- constSeqQ a is a sequence in ℚ whenever a ∈ ℚ -/
    theorem constSeqQ_isSeqQ (a : U) (ha : a ∈ (RatSet : U)) :
        IsSeqQ (constSeqQ a) := by
      unfold IsSeqQ
      constructor
      · -- constSeqQ a ⊆ ω ×ₛ RatSet
        intro p hp
        unfold constSeqQ at hp
        rw [CartesianProduct_is_specified] at hp
        rw [CartesianProduct_is_specified]
        refine ⟨hp.1, hp.2.1, ?_⟩
        have h_eq : snd p = a := (Singleton_is_specified a (snd p)).mp hp.2.2
        rw [h_eq]; exact ha
      · -- ∀ n ∈ ω, ∃! y, ⟨n, y⟩ ∈ constSeqQ a
        intro n hn
        refine ⟨a, ?_, ?_⟩
        · -- existence: ⟨n, a⟩ ∈ constSeqQ a
          show ⟨n, a⟩ ∈ constSeqQ a
          unfold constSeqQ
          rw [OrderedPair_mem_CartesianProduct]
          exact ⟨hn, (Singleton_is_specified a a).mpr rfl⟩
        · -- uniqueness
          intro y hy
          show y = a
          unfold constSeqQ at hy
          rw [OrderedPair_mem_CartesianProduct] at hy
          exact (Singleton_is_specified a y).mp hy.2

    /-- Every index of the constant sequence at a returns a -/
    theorem constSeqQ_apply (a : U) (ha : a ∈ (RatSet : U))
        (n : U) (hn : n ∈ (ω : U)) :
        (constSeqQ a)⦅n⦆ = a := by
      apply apply_eq _ n a ((constSeqQ_isSeqQ a ha).2 n hn)
      show ⟨n, a⟩ ∈ constSeqQ a
      unfold constSeqQ
      rw [OrderedPair_mem_CartesianProduct]
      exact ⟨hn, (Singleton_is_specified a a).mpr rfl⟩

    -- =========================================================================
    -- Section 4: Pointwise addition
    -- =========================================================================

    /-- Pointwise sum of sequences: {⟨n, f(n)+g(n)⟩ | n ∈ ω} -/
    noncomputable def addSeqQ (f g : U) : U :=
      sep ((ω : U) ×ₛ (RatSet : U))
        (fun p => snd p = addQ (f⦅fst p⦆) (g⦅fst p⦆))

    private theorem addSeqQ_mem_iff (f g p : U) :
        p ∈ addSeqQ f g ↔
        p ∈ (ω : U) ×ₛ (RatSet : U) ∧ snd p = addQ (f⦅fst p⦆) (g⦅fst p⦆) := by
      unfold addSeqQ; exact mem_sep_iff _ p _

    /-- addSeqQ f g is a sequence in ℚ whenever f and g are -/
    theorem addSeqQ_isSeqQ (f g : U) (hf : IsSeqQ f) (hg : IsSeqQ g) :
        IsSeqQ (addSeqQ f g) := by
      unfold IsSeqQ
      constructor
      · intro p hp; exact ((addSeqQ_mem_iff f g p).mp hp).1
      · intro n hn
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hgn := seqTermQ_mem_RatSet g n hg hn
        refine ⟨addQ (f⦅n⦆) (g⦅n⦆), ?_, ?_⟩
        · show ⟨n, addQ (f⦅n⦆) (g⦅n⦆)⟩ ∈ addSeqQ f g
          rw [addSeqQ_mem_iff]
          refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
                   ⟨hn, addQ_in_RatSet _ _ hfn hgn⟩, ?_⟩
          rw [fst_of_ordered_pair, snd_of_ordered_pair]
        · intro z hz
          show z = addQ (f⦅n⦆) (g⦅n⦆)
          have h := ((addSeqQ_mem_iff f g ⟨n, z⟩).mp hz).2
          rw [fst_of_ordered_pair, snd_of_ordered_pair] at h
          exact h

    /-- Pointwise addition evaluates to f(n) + g(n) -/
    theorem addSeqQ_apply (f g : U) (hf : IsSeqQ f) (hg : IsSeqQ g)
        (n : U) (hn : n ∈ (ω : U)) :
        (addSeqQ f g)⦅n⦆ = addQ (f⦅n⦆) (g⦅n⦆) := by
      apply apply_eq _ n _ ((addSeqQ_isSeqQ f g hf hg).2 n hn)
      show ⟨n, addQ (f⦅n⦆) (g⦅n⦆)⟩ ∈ addSeqQ f g
      rw [addSeqQ_mem_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
               ⟨hn, addQ_in_RatSet _ _ (seqTermQ_mem_RatSet f n hf hn)
                       (seqTermQ_mem_RatSet g n hg hn)⟩, ?_⟩
      rw [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 5: Pointwise negation
    -- =========================================================================

    /-- Pointwise negation of a sequence: {⟨n, −f(n)⟩ | n ∈ ω} -/
    noncomputable def negSeqQ (f : U) : U :=
      sep ((ω : U) ×ₛ (RatSet : U))
        (fun p => snd p = negQ (f⦅fst p⦆))

    private theorem negSeqQ_mem_iff (f p : U) :
        p ∈ negSeqQ f ↔
        p ∈ (ω : U) ×ₛ (RatSet : U) ∧ snd p = negQ (f⦅fst p⦆) := by
      unfold negSeqQ; exact mem_sep_iff _ p _

    /-- negSeqQ f is a sequence in ℚ whenever f is -/
    theorem negSeqQ_isSeqQ (f : U) (hf : IsSeqQ f) :
        IsSeqQ (negSeqQ f) := by
      unfold IsSeqQ
      constructor
      · intro p hp; exact ((negSeqQ_mem_iff f p).mp hp).1
      · intro n hn
        have hfn := seqTermQ_mem_RatSet f n hf hn
        refine ⟨negQ (f⦅n⦆), ?_, ?_⟩
        · show ⟨n, negQ (f⦅n⦆)⟩ ∈ negSeqQ f
          rw [negSeqQ_mem_iff]
          refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
                   ⟨hn, negQ_in_RatSet _ hfn⟩, ?_⟩
          rw [fst_of_ordered_pair, snd_of_ordered_pair]
        · intro z hz
          show z = negQ (f⦅n⦆)
          have h := ((negSeqQ_mem_iff f ⟨n, z⟩).mp hz).2
          rw [fst_of_ordered_pair, snd_of_ordered_pair] at h
          exact h

    /-- Pointwise negation evaluates to −f(n) -/
    theorem negSeqQ_apply (f : U) (hf : IsSeqQ f)
        (n : U) (hn : n ∈ (ω : U)) :
        (negSeqQ f)⦅n⦆ = negQ (f⦅n⦆) := by
      apply apply_eq _ n _ ((negSeqQ_isSeqQ f hf).2 n hn)
      show ⟨n, negQ (f⦅n⦆)⟩ ∈ negSeqQ f
      rw [negSeqQ_mem_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
               ⟨hn, negQ_in_RatSet _ (seqTermQ_mem_RatSet f n hf hn)⟩, ?_⟩
      rw [fst_of_ordered_pair, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 6: Pointwise multiplication
    -- =========================================================================

    /-- Pointwise product of sequences: {⟨n, f(n)·g(n)⟩ | n ∈ ω} -/
    noncomputable def mulSeqQ (f g : U) : U :=
      sep ((ω : U) ×ₛ (RatSet : U))
        (fun p => snd p = mulQ (f⦅fst p⦆) (g⦅fst p⦆))

    private theorem mulSeqQ_mem_iff (f g p : U) :
        p ∈ mulSeqQ f g ↔
        p ∈ (ω : U) ×ₛ (RatSet : U) ∧ snd p = mulQ (f⦅fst p⦆) (g⦅fst p⦆) := by
      unfold mulSeqQ; exact mem_sep_iff _ p _

    /-- mulSeqQ f g is a sequence in ℚ whenever f and g are -/
    theorem mulSeqQ_isSeqQ (f g : U) (hf : IsSeqQ f) (hg : IsSeqQ g) :
        IsSeqQ (mulSeqQ f g) := by
      unfold IsSeqQ
      constructor
      · intro p hp; exact ((mulSeqQ_mem_iff f g p).mp hp).1
      · intro n hn
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hgn := seqTermQ_mem_RatSet g n hg hn
        refine ⟨mulQ (f⦅n⦆) (g⦅n⦆), ?_, ?_⟩
        · show ⟨n, mulQ (f⦅n⦆) (g⦅n⦆)⟩ ∈ mulSeqQ f g
          rw [mulSeqQ_mem_iff]
          refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
                   ⟨hn, mulQ_in_RatSet _ _ hfn hgn⟩, ?_⟩
          rw [fst_of_ordered_pair, snd_of_ordered_pair]
        · intro z hz
          show z = mulQ (f⦅n⦆) (g⦅n⦆)
          have h := ((mulSeqQ_mem_iff f g ⟨n, z⟩).mp hz).2
          rw [fst_of_ordered_pair, snd_of_ordered_pair] at h
          exact h

    /-- Pointwise multiplication evaluates to f(n) · g(n) -/
    theorem mulSeqQ_apply (f g : U) (hf : IsSeqQ f) (hg : IsSeqQ g)
        (n : U) (hn : n ∈ (ω : U)) :
        (mulSeqQ f g)⦅n⦆ = mulQ (f⦅n⦆) (g⦅n⦆) := by
      apply apply_eq _ n _ ((mulSeqQ_isSeqQ f g hf hg).2 n hn)
      show ⟨n, mulQ (f⦅n⦆) (g⦅n⦆)⟩ ∈ mulSeqQ f g
      rw [mulSeqQ_mem_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
               ⟨hn, mulQ_in_RatSet _ _ (seqTermQ_mem_RatSet f n hf hn)
                       (seqTermQ_mem_RatSet g n hg hn)⟩, ?_⟩
      rw [fst_of_ordered_pair, snd_of_ordered_pair]

  end Rat.Sequences

end ZFC

export ZFC.Rat.Sequences (
  IsSeqQ
  seqTermQ_mem_RatSet
  constSeqQ
  constSeqQ_isSeqQ
  constSeqQ_apply
  addSeqQ
  addSeqQ_isSeqQ
  addSeqQ_apply
  negSeqQ
  negSeqQ_isSeqQ
  negSeqQ_apply
  mulSeqQ
  mulSeqQ_isSeqQ
  mulSeqQ_apply
)
