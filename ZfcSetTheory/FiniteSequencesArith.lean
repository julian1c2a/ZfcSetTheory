/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Arithmetic Operations on Finite Sequences in ZFC

This module defines summation and product for finite sequences of naturals,
the Cartesian product of a finite family of sets, and proves that the
cardinality of the Cartesian product equals the product of the cardinalities.

## Main Definitions

* `seqSumFn f`     — ZFC function ω → ω computing partial sums of f
* `seqSum f n`     — Σ_{i<n} f(i) for f : n → ω
* `seqProdFn f`    — ZFC function ω → ω computing partial products of f
* `seqProd f n`    — Π_{i<n} f(i) for f : n → ω
* `familyProduct F n` — Cartesian product Π_{i<n} F(i) for a family F : n → 𝒫(U)

## Main Theorems

* `seqSum_zero`, `seqSum_succ`   — recursion equations for sum
* `seqProd_zero`, `seqProd_succ` — recursion equations for product
* `familyProduct_zero`, `familyProduct_succ` — recursion for Cartesian product
-/

import ZfcSetTheory.NaturalNumbersMul
import ZfcSetTheory.FiniteSequences
import ZfcSetTheory.FiniteSets

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
  open SetUniverse.NaturalNumbersAdd
  open SetUniverse.NaturalNumbersMul
  open SetUniverse.FiniteSequences
  open SetUniverse.FiniteSets

  universe u
  variable {U : Type u}

  namespace FiniteSequencesArith

    /-! ============================================================ -/
    /-! ### SECTION 1: SUMMATION STEP FUNCTION ### -/
    /-! ============================================================ -/

    /-- Step function for summation: maps ⟨k, v⟩ ↦ add v (f⦅k⦆).
        Constructed as a ZFC set in (ω ×ₛ ω) ×ₛ ω. -/
    noncomputable def sumStepFn (f : U) : U :=
      SpecSet ((ω ×ₛ ω) ×ₛ ω)
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧
          p = ⟨⟨k, v⟩, add v (f⦅k⦆)⟩)

    /-- Membership characterization for sumStepFn. -/
    theorem mem_sumStepFn {f p : U} :
        p ∈ sumStepFn f ↔ (p ∈ (ω ×ₛ ω) ×ₛ ω ∧
          ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧ p = ⟨⟨k, v⟩, add v (f⦅k⦆)⟩) := by
      unfold sumStepFn; rw [SpecSet_is_specified]

    /-- f⦅k⦆ ∈ ω for any k ∈ ω when f is a finite sequence into ω. -/
    private theorem apply_in_Omega_of_isFinSeq {f n k : U}
        (hf : isFinSeq f n ω) : f⦅k⦆ ∈ (ω : U) := by
      by_cases hk_in_n : k ∈ n
      · exact isFinSeq_apply_mem hf hk_in_n
      · have h_neg : ¬(∃! y, ⟨k, y⟩ ∈ f) := by
          intro ⟨y, hy, _⟩
          exact hk_in_n ((OrderedPair_mem_CartesianProduct k y n ω).mp (hf.2.1 _ hy)).1
        show f⦅k⦆ ∈ (ω : U)
        unfold apply
        rw [dif_neg h_neg]
        exact zero_in_Omega

    /-- sumStepFn f is a function from ω ×ₛ ω to ω, when f maps into ω. -/
    theorem sumStepFn_is_function {f n : U} (hf : isFinSeq f n ω) :
        isFunctionFromTo (sumStepFn f) (ω ×ₛ ω) ω := by
      constructor
      · intro p hp; rw [mem_sumStepFn] at hp; exact hp.1
      · intro x hx
        rw [CartesianProduct_is_specified] at hx
        obtain ⟨hop, hfst_w, hsnd_w⟩ := hx
        obtain ⟨k, v, rfl⟩ := hop
        rw [fst_of_ordered_pair] at hfst_w
        rw [snd_of_ordered_pair] at hsnd_w
        refine ⟨add v (f⦅k⦆), ?_, fun y hy => ?_⟩
        · dsimp only; rw [mem_sumStepFn]
          exact ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (add v (f⦅k⦆)) (ω ×ₛ ω) ω).mpr
                   ⟨(OrderedPair_mem_CartesianProduct k v ω ω).mpr ⟨hfst_w, hsnd_w⟩,
                    add_in_Omega v (f⦅k⦆) hsnd_w (apply_in_Omega_of_isFinSeq hf)⟩,
                 k, v, hfst_w, hsnd_w, rfl⟩
        · dsimp only at hy; rw [mem_sumStepFn] at hy
          obtain ⟨_, k', v', hk', hv', heq⟩ := hy
          obtain ⟨hpair_eq, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections ⟨k, v⟩ y ⟨k', v'⟩ (add v' (f⦅k'⦆)) heq
          obtain ⟨hk_eq, hv_eq⟩ := Eq_of_OrderedPairs_given_projections k v k' v' hpair_eq
          rw [hy_eq, ← hk_eq, ← hv_eq]

    /-- Applying sumStepFn yields add v (f⦅k⦆). -/
    theorem sumStepFn_apply {f n k v : U} (hf : isFinSeq f n ω)
        (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) :
        (sumStepFn f)⦅⟨k, v⟩⦆ = add v (f⦅k⦆) := by
      have hkv : ⟨k, v⟩ ∈ (ω ×ₛ ω : U) :=
        (OrderedPair_mem_CartesianProduct k v ω ω).mpr ⟨hk, hv⟩
      have h_mem : ⟨⟨k, v⟩, add v (f⦅k⦆)⟩ ∈ sumStepFn f :=
        mem_sumStepFn.mpr
          ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (add v (f⦅k⦆)) (ω ×ₛ ω) ω).mpr
             ⟨hkv, add_in_Omega v (f⦅k⦆) hv (apply_in_Omega_of_isFinSeq hf)⟩,
           k, v, hk, hv, rfl⟩
      exact apply_eq (sumStepFn f) ⟨k, v⟩ (add v (f⦅k⦆))
        ((sumStepFn_is_function hf).2 ⟨k, v⟩ hkv) h_mem

    /-! ============================================================ -/
    /-! ### SECTION 2: SUMMATION ### -/
    /-! ============================================================ -/

    /-- The summation function: given f, seqSumFn f is the unique F : ω → ω
        satisfying F(∅) = ∅ and F(σ k) = add (F k) (f⦅k⦆).
        Uses RecursionTheoremWithStep. -/
    noncomputable def seqSumFn (f : U) (hf : isFinSeq f (domain f) ω) : U :=
      Classical.choose (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) ∅ (sumStepFn f)
          zero_in_Omega (sumStepFn_is_function hf)))

    /-- seqSumFn is a function from ω to ω. -/
    theorem seqSumFn_is_function {f : U} (hf : isFinSeq f (domain f) ω) :
        isFunctionFromTo (seqSumFn f hf) ω ω :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) ∅ (sumStepFn f)
          zero_in_Omega (sumStepFn_is_function hf)))).1

    /-- Sum of a finite numeric sequence: Σ_{i<n} f(i). -/
    noncomputable def seqSum (f n : U) : U :=
      if h : isFinSeq f (domain f) ω then
        apply (seqSumFn f h) n
      else ∅

    /-- Helper: apply of seqSumFn at a natural lies in ω. -/
    private theorem seqSumFn_apply_in_Omega {f : U} (hf : isFinSeq f (domain f) ω)
        (n : U) (hn : n ∈ (ω : U)) : apply (seqSumFn f hf) n ∈ (ω : U) := by
      have hF := seqSumFn_is_function hf
      have h_pair := apply_mem (seqSumFn f hf) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ ω ω).mp (hF.1 _ h_pair)).2

    /-- Helper: seqSumFn at zero gives ∅. -/
    private theorem seqSumFn_zero {f : U} (hf : isFinSeq f (domain f) ω) :
        apply (seqSumFn f hf) (∅ : U) = ∅ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) ∅ (sumStepFn f)
          zero_in_Omega (sumStepFn_is_function hf)))).2.1

    /-- Helper: seqSumFn recursion step. -/
    private theorem seqSumFn_succ {f : U} (hf : isFinSeq f (domain f) ω)
        (n : U) (hn : n ∈ ω) :
        apply (seqSumFn f hf) (σ n) =
          apply (sumStepFn f) ⟨n, apply (seqSumFn f hf) n⟩ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) ∅ (sumStepFn f)
          zero_in_Omega (sumStepFn_is_function hf)))).2.2 n hn

    /-- seqSum f ∅ = ∅ (empty sum is zero). -/
    theorem seqSum_zero {f : U} (hf : isFinSeq f ∅ ω) : seqSum f ∅ = ∅ := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqSum, dif_pos hf']
      exact seqSumFn_zero hf'

    /-- seqSum f (σ k) = add (seqSum f k) (f⦅k⦆) for k ∈ ω. -/
    theorem seqSum_succ {f k : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) :
        seqSum f (σ k) = add (seqSum f k) (f⦅k⦆) := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqSum, dif_pos hf']
      rw [seqSumFn_succ hf' k hk]
      exact sumStepFn_apply hf' hk (seqSumFn_apply_in_Omega hf' k hk)

    /-- seqSum f n ∈ ω when f : n → ω. -/
    theorem seqSum_in_Omega {f n : U} (hf : isFinSeq f n ω) :
        seqSum f n ∈ ω := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqSum, dif_pos hf']
      exact seqSumFn_apply_in_Omega hf' n hf.1

    /-- Sum of a singleton sequence. -/
    theorem seqSum_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) :
        seqSum f (σ ∅) = f⦅∅⦆ := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqSum, dif_pos hf']
      rw [seqSumFn_succ hf' ∅ zero_in_Omega]
      rw [sumStepFn_apply hf' zero_in_Omega (seqSumFn_apply_in_Omega hf' ∅ zero_in_Omega)]
      rw [seqSumFn_zero hf']
      exact zero_add (f⦅∅⦆) (isFinSeq_apply_mem hf (zero_in_succ_nat ∅ zero_in_Omega))

    /-! ============================================================ -/
    /-! ### SECTION 3: PRODUCT STEP FUNCTION ### -/
    /-! ============================================================ -/

    /-- Step function for product: maps ⟨k, v⟩ ↦ mul v (f⦅k⦆). -/
    noncomputable def prodStepFn (f : U) : U :=
      SpecSet ((ω ×ₛ ω) ×ₛ ω)
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧
          p = ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩)

    /-- Membership characterization for prodStepFn. -/
    theorem mem_prodStepFn {f p : U} :
        p ∈ prodStepFn f ↔ (p ∈ (ω ×ₛ ω) ×ₛ ω ∧
          ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧ p = ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩) := by
      unfold prodStepFn; rw [SpecSet_is_specified]

    /-- prodStepFn f is a function from ω ×ₛ ω to ω. -/
    theorem prodStepFn_is_function {f n : U} (hf : isFinSeq f n ω) :
        isFunctionFromTo (prodStepFn f) (ω ×ₛ ω) ω := by
      constructor
      · intro p hp; rw [mem_prodStepFn] at hp; exact hp.1
      · intro x hx
        rw [CartesianProduct_is_specified] at hx
        obtain ⟨hop, hfst_w, hsnd_w⟩ := hx
        obtain ⟨k, v, rfl⟩ := hop
        rw [fst_of_ordered_pair] at hfst_w
        rw [snd_of_ordered_pair] at hsnd_w
        refine ⟨mul v (f⦅k⦆), ?_, fun y hy => ?_⟩
        · dsimp only; rw [mem_prodStepFn]
          exact ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (mul v (f⦅k⦆)) (ω ×ₛ ω) ω).mpr
                   ⟨(OrderedPair_mem_CartesianProduct k v ω ω).mpr ⟨hfst_w, hsnd_w⟩,
                    mul_in_Omega v (f⦅k⦆) hsnd_w (apply_in_Omega_of_isFinSeq hf)⟩,
                 k, v, hfst_w, hsnd_w, rfl⟩
        · dsimp only at hy; rw [mem_prodStepFn] at hy
          obtain ⟨_, k', v', hk', hv', heq⟩ := hy
          obtain ⟨hpair_eq, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections ⟨k, v⟩ y ⟨k', v'⟩ (mul v' (f⦅k'⦆)) heq
          obtain ⟨hk_eq, hv_eq⟩ := Eq_of_OrderedPairs_given_projections k v k' v' hpair_eq
          rw [hy_eq, ← hk_eq, ← hv_eq]

    /-- Applying prodStepFn yields mul v (f⦅k⦆). -/
    theorem prodStepFn_apply {f n k v : U} (hf : isFinSeq f n ω)
        (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) :
        (prodStepFn f)⦅⟨k, v⟩⦆ = mul v (f⦅k⦆) := by
      have hkv : ⟨k, v⟩ ∈ (ω ×ₛ ω : U) :=
        (OrderedPair_mem_CartesianProduct k v ω ω).mpr ⟨hk, hv⟩
      have h_mem : ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩ ∈ prodStepFn f :=
        mem_prodStepFn.mpr
          ⟨(OrderedPair_mem_CartesianProduct ⟨k, v⟩ (mul v (f⦅k⦆)) (ω ×ₛ ω) ω).mpr
             ⟨hkv, mul_in_Omega v (f⦅k⦆) hv (apply_in_Omega_of_isFinSeq hf)⟩,
           k, v, hk, hv, rfl⟩
      exact apply_eq (prodStepFn f) ⟨k, v⟩ (mul v (f⦅k⦆))
        ((prodStepFn_is_function hf).2 ⟨k, v⟩ hkv) h_mem

    /-! ============================================================ -/
    /-! ### SECTION 4: NUMERIC PRODUCT ### -/
    /-! ============================================================ -/

    /-- The product function: given f, seqProdFn f is the unique F : ω → ω
        satisfying F(∅) = σ ∅ and F(σ k) = mul (F k) (f⦅k⦆).
        Uses RecursionTheoremWithStep with initial value 1 = σ ∅. -/
    noncomputable def seqProdFn (f : U) (hf : isFinSeq f (domain f) ω) : U :=
      Classical.choose (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
          (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))

    /-- seqProdFn is a function from ω to ω. -/
    theorem seqProdFn_is_function {f : U} (hf : isFinSeq f (domain f) ω) :
        isFunctionFromTo (seqProdFn f hf) ω ω :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
          (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))).1

    /-- Numeric product of a finite sequence: Π_{i<n} f(i). -/
    noncomputable def seqProd (f n : U) : U :=
      if h : isFinSeq f (domain f) ω then
        apply (seqProdFn f h) n
      else ∅

    /-- Helper: apply of seqProdFn at a natural lies in ω. -/
    private theorem seqProdFn_apply_in_Omega {f : U} (hf : isFinSeq f (domain f) ω)
        (n : U) (hn : n ∈ (ω : U)) : apply (seqProdFn f hf) n ∈ (ω : U) := by
      have hF := seqProdFn_is_function hf
      have h_pair := apply_mem (seqProdFn f hf) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ ω ω).mp (hF.1 _ h_pair)).2

    /-- Helper: seqProdFn at zero gives σ ∅ (= 1). -/
    private theorem seqProdFn_zero {f : U} (hf : isFinSeq f (domain f) ω) :
        apply (seqProdFn f hf) (∅ : U) = (σ (∅ : U)) :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
          (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))).2.1

    /-- Helper: seqProdFn recursion step. -/
    private theorem seqProdFn_succ {f : U} (hf : isFinSeq f (domain f) ω)
        (n : U) (hn : n ∈ ω) :
        apply (seqProdFn f hf) (σ n) =
          apply (prodStepFn f) ⟨n, apply (seqProdFn f hf) n⟩ :=
      (Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
          (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))).2.2 n hn

    /-- seqProd f ∅ = σ ∅ (empty product is one). -/
    theorem seqProd_zero {f : U} (hf : isFinSeq f ∅ ω) : seqProd f ∅ = (σ (∅ : U)) := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqProd, dif_pos hf']
      exact seqProdFn_zero hf'

    /-- seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) for k ∈ ω. -/
    theorem seqProd_succ {f k : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) :
        seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqProd, dif_pos hf']
      rw [seqProdFn_succ hf' k hk]
      exact prodStepFn_apply hf' hk (seqProdFn_apply_in_Omega hf' k hk)

    /-- seqProd f n ∈ ω when f : n → ω. -/
    theorem seqProd_in_Omega {f n : U} (hf : isFinSeq f n ω) :
        seqProd f n ∈ ω := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqProd, dif_pos hf']
      exact seqProdFn_apply_in_Omega hf' n hf.1

    /-- Product of a singleton sequence. -/
    theorem seqProd_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) :
        seqProd f (σ ∅) = f⦅∅⦆ := by
      have hf' : isFinSeq f (domain f) ω := isFinSeq_domain hf ▸ hf
      simp only [seqProd, dif_pos hf']
      rw [seqProdFn_succ hf' ∅ zero_in_Omega]
      rw [prodStepFn_apply hf' zero_in_Omega (seqProdFn_apply_in_Omega hf' ∅ zero_in_Omega)]
      rw [seqProdFn_zero hf']
      exact one_mul_Omega (f⦅∅⦆) (isFinSeq_apply_mem hf (zero_in_succ_nat ∅ zero_in_Omega))

    /-! ============================================================ -/
    /-! ### SECTION 5: CARTESIAN PRODUCT OF A FAMILY ### -/
    /-! ============================================================ -/

    /-- The Cartesian product of a family F : n → Sets.
        Π_{i<n} F(i) = {g : n → ⋃(range F) | ∀ i ∈ n, g⦅i⦆ ∈ F⦅i⦆}.
        These are the "choice functions" selecting one element from each F(i). -/
    noncomputable def familyProduct (F n : U) : U :=
      SpecSet (FinSeqSet n (⋃ (ImageSet F n)))
        (fun g => ∀ i, i ∈ n → g⦅i⦆ ∈ F⦅i⦆)

    /-- Membership characterization for familyProduct. -/
    theorem mem_familyProduct {F n g : U} :
        g ∈ familyProduct F n ↔
        (g ∈ FinSeqSet n (⋃ (ImageSet F n)) ∧ ∀ i, i ∈ n → g⦅i⦆ ∈ F⦅i⦆) := by
      unfold familyProduct; rw [SpecSet_is_specified]

    /-- The empty Cartesian product is {∅} (singleton of the empty function). -/
    theorem familyProduct_zero (F : U) : familyProduct F (∅ : U) = ({∅} : U) := by
      apply ExtSet
      intro g
      rw [mem_familyProduct, Singleton_is_specified]
      constructor
      · intro h
        exact isFinSeq_zero_unique (mem_FinSeqSet_iff.mp h.1)
      · intro hg
        rw [hg]
        exact ⟨mem_FinSeqSet_iff.mpr (isFinSeq_empty _),
               fun i hi => absurd hi (EmptySet_is_empty i)⟩

    /-- The Cartesian product of a family indexed by σ n is isomorphic to
        (familyProduct F n) ×ₛ F⦅n⦆. This states: g ∈ familyProduct F (σ n) ↔
        g↾n ∈ familyProduct F n ∧ g⦅n⦆ ∈ F⦅n⦆. -/
    theorem familyProduct_succ_char {F n : U} (hn : n ∈ (ω : U))
        (hF : isFinSeq F (σ n) (⋃ (ImageSet F (σ n)))) :
        ∀ g, g ∈ familyProduct F (σ n) →
          (g ↾ n) ∈ familyProduct F n ∧ g⦅n⦆ ∈ F⦅n⦆ := by
      intro g hg
      rw [mem_familyProduct] at hg
      obtain ⟨hg_seq, hg_choice⟩ := hg
      have hg_fs : isFinSeq g (σ n) (⋃ (ImageSet F (σ n))) := mem_FinSeqSet_iff.mp hg_seq
      have hgr := isFinSeq_restriction hg_fs
      constructor
      · -- (g ↾ n) ∈ familyProduct F n
        rw [mem_familyProduct]
        constructor
        · -- g ↾ n ∈ FinSeqSet n (⋃ (ImageSet F n))
          rw [mem_FinSeqSet_iff]
          refine ⟨hn, ?_, hgr.2.2⟩
          -- Subset: g ↾ n ⊆ n ×ₛ (⋃ (ImageSet F n))
          intro p hp
          have hp' := hgr.2.1 p hp
          rw [CartesianProduct_is_specified] at hp' ⊢
          obtain ⟨hop, hfst_n, _⟩ := hp'
          refine ⟨hop, hfst_n, ?_⟩
          -- snd p ∈ ⋃ (ImageSet F n)
          obtain ⟨i, y, rfl⟩ := hop
          rw [fst_of_ordered_pair] at hfst_n
          rw [snd_of_ordered_pair]
          have h_iy_in_g : ⟨i, y⟩ ∈ g :=
            ((Restriction_is_specified g n ⟨i, y⟩).mp hp).1
          have h_y_eq : y = g⦅i⦆ :=
            (apply_eq g i y (hg_fs.2.2 i (mem_successor_of_mem i n hfst_n)) h_iy_in_g).symm
          rw [h_y_eq]
          rw [UnionSet_is_specified]
          exact ⟨F⦅i⦆,
            (mem_range (F ↾ n) (F⦅i⦆)).mpr
              ⟨i, (Restriction_is_specified F n ⟨i, F⦅i⦆⟩).mpr
                ⟨isFinSeq_pair_mem hF (mem_successor_of_mem i n hfst_n),
                 by rw [fst_of_ordered_pair]; exact hfst_n⟩⟩,
            hg_choice i (mem_successor_of_mem i n hfst_n)⟩
        · -- ∀ i ∈ n, (g ↾ n)⦅i⦆ ∈ F⦅i⦆
          intro i hi
          rw [Restriction_apply g n i hi]
          exact hg_choice i (mem_successor_of_mem i n hi)
      · -- g⦅n⦆ ∈ F⦅n⦆
        exact hg_choice n (mem_successor_self n)

    /-! ============================================================ -/
    /-! ### HELPERS FOR CARDINALITY THEOREMS ### -/
    /-! ============================================================ -/

    /-- If A ≃ₛ ∅, then A has no elements. -/
    private theorem equip_empty_no_elements {A : U} (h : A ≃ₛ (∅ : U)) :
        ∀ x, x ∉ A := by
      intro x hx
      obtain ⟨f, hf_func, _, _⟩ := h
      obtain ⟨y, hy, _⟩ := hf_func.2 x hx
      exact EmptySet_is_empty y
        ((OrderedPair_mem_CartesianProduct x y A ∅).mp (hf_func.1 _ hy)).2

    /-- If A ≃ₛ n (n ∈ ω) and a ∉ A, then A ∪ {a} ≃ₛ σ n.
        Bijection: f ∪ {⟨a, n⟩}. -/
    private theorem union_singleton_equip {A n : U} (hn : n ∈ (ω : U))
        (hA : A ≃ₛ n) {a : U} (ha : a ∉ A) :
        (A ∪ {a}) ≃ₛ σ n := by
      obtain ⟨f, hf_func, hf_inj, hf_surj⟩ := hA
      have hn_nat := mem_Omega_is_Nat n hn
      refine ⟨f ∪ {⟨a, n⟩}, ?_, ?_, ?_⟩
      · constructor
        · intro p hp
          rw [BinUnion_is_specified] at hp
          cases hp with
          | inl hp_f =>
            have h := hf_func.1 p hp_f
            rw [CartesianProduct_is_specified] at h ⊢
            exact ⟨h.1,
                   (BinUnion_is_specified A {a} (fst p)).mpr (Or.inl h.2.1),
                   (successor_is_specified n (snd p)).mpr (Or.inl h.2.2)⟩
          | inr hp_eq =>
            rw [Singleton_is_specified] at hp_eq
            rw [hp_eq, OrderedPair_mem_CartesianProduct]
            exact ⟨(BinUnion_is_specified A {a} a).mpr
                      (Or.inr ((Singleton_is_specified a a).mpr rfl)),
                   mem_successor_self n⟩
        · intro x hx
          rw [BinUnion_is_specified] at hx
          cases hx with
          | inl hx_A =>
            obtain ⟨y, hy_in, hy_unique⟩ := hf_func.2 x hx_A
            exact ⟨y,
              (BinUnion_is_specified f {⟨a, n⟩} ⟨x, y⟩).mpr (Or.inl hy_in),
              fun y' (hy' : ⟨x, y'⟩ ∈ BinUnion f {⟨a, n⟩}) => by
                rw [BinUnion_is_specified] at hy'
                cases hy' with
                | inl hy'_f => exact hy_unique y' hy'_f
                | inr hy'_eq =>
                  rw [Singleton_is_specified] at hy'_eq
                  exact absurd
                    ((Eq_of_OrderedPairs_given_projections x y' a n hy'_eq).1 ▸ hx_A) ha⟩
          | inr hx_a =>
            rw [Singleton_is_specified] at hx_a
            exact ⟨n,
              by rw [hx_a]; exact (BinUnion_is_specified f {⟨a, n⟩} ⟨a, n⟩).mpr
                    (Or.inr ((Singleton_is_specified ⟨a, n⟩ ⟨a, n⟩).mpr rfl)),
              fun y' hy' => by
                rw [hx_a] at hy'
                rw [BinUnion_is_specified] at hy'
                cases hy' with
                | inl hy'_f =>
                  exact absurd
                    ((OrderedPair_mem_CartesianProduct a y' A n).mp (hf_func.1 _ hy'_f)).1 ha
                | inr hy'_eq =>
                  rw [Singleton_is_specified] at hy'_eq
                  exact (Eq_of_OrderedPairs_given_projections a y' a n hy'_eq).2⟩
      · intro x₁ x₂ y h₁ h₂
        rw [BinUnion_is_specified] at h₁ h₂
        cases h₁ with
        | inl h₁_f =>
          cases h₂ with
          | inl h₂_f => exact hf_inj x₁ x₂ y h₁_f h₂_f
          | inr h₂_eq =>
            rw [Singleton_is_specified] at h₂_eq
            rw [(Eq_of_OrderedPairs_given_projections x₂ y a n h₂_eq).2] at h₁_f
            exact absurd
              ((OrderedPair_mem_CartesianProduct x₁ n A n).mp (hf_func.1 _ h₁_f)).2
              (nat_not_mem_self n hn_nat)
        | inr h₁_eq =>
          cases h₂ with
          | inl h₂_f =>
            rw [Singleton_is_specified] at h₁_eq
            rw [(Eq_of_OrderedPairs_given_projections x₁ y a n h₁_eq).2] at h₂_f
            exact absurd
              ((OrderedPair_mem_CartesianProduct x₂ n A n).mp (hf_func.1 _ h₂_f)).2
              (nat_not_mem_self n hn_nat)
          | inr h₂_eq =>
            rw [Singleton_is_specified] at h₁_eq h₂_eq
            exact (Eq_of_OrderedPairs_given_projections x₁ y a n h₁_eq).1.trans
                  (Eq_of_OrderedPairs_given_projections x₂ y a n h₂_eq).1.symm
      · intro y hy
        rw [successor_is_specified] at hy
        cases hy with
        | inl hy_n =>
          obtain ⟨x, hx⟩ := hf_surj y hy_n
          exact ⟨x, (BinUnion_is_specified f {⟨a, n⟩} ⟨x, y⟩).mpr (Or.inl hx)⟩
        | inr hy_eq =>
          rw [hy_eq]
          exact ⟨a, (BinUnion_is_specified f {⟨a, n⟩} ⟨a, n⟩).mpr
                      (Or.inr ((Singleton_is_specified ⟨a, n⟩ ⟨a, n⟩).mpr rfl))⟩

    /-- Restricting a bijection g : B → σ m by removing the preimage of m
        gives B ∖ {b₀} ≃ₛ m. -/
    private theorem bijection_remove_top {B g m : U} (hm : m ∈ (ω : U))
        (hg : isBijection g B (σ m)) {b₀ : U} (hb₀ : ⟨b₀, m⟩ ∈ g) :
        (B ∖ {b₀}) ≃ₛ m := by
      obtain ⟨hg_func, hg_inj, hg_surj⟩ := hg
      have hm_nat := mem_Omega_is_Nat m hm
      have hb₀_B : b₀ ∈ B :=
        ((OrderedPair_mem_CartesianProduct b₀ m B (σ m)).mp (hg_func.1 _ hb₀)).1
      refine ⟨g ↾ (B ∖ {b₀}), ?_, restriction_is_injective hg_inj, ?_⟩
      · constructor
        · intro p hp
          rw [Restriction_is_specified] at hp
          obtain ⟨hp_g, hp_fst⟩ := hp
          have h_cp := hg_func.1 p hp_g
          rw [CartesianProduct_is_specified] at h_cp ⊢
          refine ⟨h_cp.1, hp_fst, ?_⟩
          cases (successor_is_specified m (snd p)).mp h_cp.2.2 with
          | inl h => exact h
          | inr h =>
            exfalso
            have hp_pair := (isOrderedPair_by_construction p).mp h_cp.1
            have h_fst_m : ⟨fst p, m⟩ ∈ g := by
              have hp_eq : ⟨fst p, m⟩ = p := by rw [← h]; exact hp_pair.symm
              rw [hp_eq]; exact hp_g
            have h_fst_eq : fst p = b₀ := hg_inj (fst p) b₀ m h_fst_m hb₀
            exact ((SetDiff_is_specified B {b₀} (fst p)).mp hp_fst).2
              ((Singleton_is_specified b₀ (fst p)).mpr h_fst_eq)
        · intro x hx
          have hx_B := ((SetDiff_is_specified B {b₀} x).mp hx).1
          obtain ⟨y, hy, hy_u⟩ := hg_func.2 x hx_B
          exact ⟨y,
            (Restriction_is_specified g (B ∖ {b₀}) ⟨x, y⟩).mpr
              ⟨hy, by rw [fst_of_ordered_pair]; exact hx⟩,
            fun y' hy' => hy_u y' (Restriction_subset g (B ∖ {b₀}) ⟨x, y'⟩ hy')⟩
      · intro y hy
        have hy_sm := (successor_is_specified m y).mpr (Or.inl hy)
        obtain ⟨x, hx⟩ := hg_surj y hy_sm
        have hx_B := ((OrderedPair_mem_CartesianProduct x y B (σ m)).mp (hg_func.1 _ hx)).1
        have hx_neq : x ≠ b₀ := by
          intro heq; rw [heq] at hx
          obtain ⟨_, _, hu⟩ := hg_func.2 b₀ hb₀_B
          rw [(hu y hx).trans (hu m hb₀).symm] at hy
          exact nat_not_mem_self m hm_nat hy
        exact ⟨x, (Restriction_is_specified g (B ∖ {b₀}) ⟨x, y⟩).mpr
          ⟨hx, by rw [fst_of_ordered_pair]
                  exact (SetDiff_is_specified B {b₀} x).mpr
                    ⟨hx_B, fun h => hx_neq ((Singleton_is_specified b₀ x).mp h)⟩⟩⟩

    /-- A ×ₛ {b} ≃ₛ A via projection. -/
    private theorem product_singleton_equip (A b : U) :
        (A ×ₛ {b}) ≃ₛ A := by
      apply equipotent_symm
      -- Bijection A → A ×ₛ {b}: a ↦ ⟨a, b⟩
      let h := SpecSet (A ×ₛ (A ×ₛ {b}))
        (fun p => ∃ a, a ∈ A ∧ p = ⟨a, ⟨a, b⟩⟩)
      refine ⟨h, ?_, ?_, ?_⟩
      · constructor
        · intro p hp; exact ((SpecSet_is_specified _ p _).mp hp).1
        · intro x hx
          refine ⟨⟨x, b⟩, ?_, fun y hy => ?_⟩
          · exact (SpecSet_is_specified _ _ _).mpr
              ⟨(OrderedPair_mem_CartesianProduct x ⟨x, b⟩ A (A ×ₛ {b})).mpr
                ⟨hx, (OrderedPair_mem_CartesianProduct x b A {b}).mpr
                  ⟨hx, (Singleton_is_specified b b).mpr rfl⟩⟩,
               x, hx, rfl⟩
          · obtain ⟨_, a, _, heq⟩ := (SpecSet_is_specified _ _ _).mp hy
            have p := Eq_of_OrderedPairs_given_projections x y a ⟨a, b⟩ heq
            rw [p.1]; exact p.2
      · intro x₁ x₂ y h₁ h₂
        obtain ⟨_, a₁, _, h₁_eq⟩ := (SpecSet_is_specified _ _ _).mp h₁
        obtain ⟨_, a₂, _, h₂_eq⟩ := (SpecSet_is_specified _ _ _).mp h₂
        have p₁ := Eq_of_OrderedPairs_given_projections x₁ y a₁ ⟨a₁, b⟩ h₁_eq
        have p₂ := Eq_of_OrderedPairs_given_projections x₂ y a₂ ⟨a₂, b⟩ h₂_eq
        have h_eq_ab := Eq_of_OrderedPairs_given_projections a₁ b a₂ b
          (p₁.2.symm.trans p₂.2)
        exact p₁.1.trans (h_eq_ab.1.trans p₂.1.symm)
      · intro y hy
        have hcp := (CartesianProduct_is_specified A {b} y).mp hy
        have h_fst_A : fst y ∈ A := hcp.2.1
        have h_snd_eq : snd y = b := (Singleton_is_specified b (snd y)).mp hcp.2.2
        have h_pair : y = ⟨fst y, snd y⟩ := (isOrderedPair_by_construction y).mp hcp.1
        have hy_eq : y = ⟨fst y, b⟩ := h_pair.trans (by rw [h_snd_eq])
        refine ⟨fst y, (SpecSet_is_specified _ _ _).mpr ⟨?_, fst y, h_fst_A, ?_⟩⟩
        · exact (OrderedPair_mem_CartesianProduct (fst y) y A (A ×ₛ {b})).mpr ⟨h_fst_A, hy⟩
        · exact congrArg (OrderedPair (fst y)) hy_eq

    /-- Disjoint union preserves equipotence:
        C₁ ≃ₛ k, C₂ ≃ₛ n, C₁ ⟂ C₂ → C₁ ∪ C₂ ≃ₛ add n k. -/
    private theorem disjoint_union_equip {C₁ C₂ k n : U}
        (hk : k ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hC₁ : C₁ ≃ₛ k) (hC₂ : C₂ ≃ₛ n) (hdisj : C₁ ⟂ C₂) :
        (C₁ ∪ C₂) ≃ₛ add n k := by
      let P : U → Prop := fun n' => ∀ (C₁' C₂' k' : U),
        k' ∈ (ω : U) → C₁' ≃ₛ k' → C₂' ≃ₛ n' → C₁' ⟂ C₂' → (C₁' ∪ C₂') ≃ₛ add n' k'
      suffices h : P n from h C₁ C₂ k hk hC₁ hC₂ hdisj
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        exact ((SpecSet_is_specified (ω : U) n P).mp hn_S).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun C₁' C₂' k' hk' hC₁' hC₂' _ => ?_⟩
        have h_eq : (C₁' ∪ C₂' : U) = C₁' := by
          apply ExtSet; intro z; rw [BinUnion_is_specified]
          exact ⟨fun h => h.elim id (fun h2 => absurd h2 (equip_empty_no_elements hC₂' z)),
                 Or.inl⟩
        rw [h_eq, zero_add k' hk']
        exact hC₁'
      · intro n' hn'
        rw [SpecSet_is_specified] at hn' ⊢
        obtain ⟨hn'_w, ih⟩ := hn'
        refine ⟨succ_in_Omega n' hn'_w, fun C₁' C₂' k' hk' hC₁' hC₂' hdisj' => ?_⟩
        obtain ⟨g, hg_func, hg_inj, hg_surj⟩ := hC₂'
        obtain ⟨c₀, hc₀⟩ := hg_surj n' (mem_successor_self n')
        have hc₀_C₂ : c₀ ∈ C₂' :=
          ((OrderedPair_mem_CartesianProduct c₀ n' C₂' (σ n')).mp (hg_func.1 _ hc₀)).1
        have hC₂''_equip : (C₂' ∖ {c₀}) ≃ₛ n' :=
          bijection_remove_top hn'_w ⟨hg_func, hg_inj, hg_surj⟩ hc₀
        have hdisj'' : C₁' ⟂ (C₂' ∖ {c₀}) := fun z hz hz' =>
          hdisj' z hz ((SetDiff_is_specified C₂' {c₀} z).mp hz').1
        have ih_result := ih C₁' (C₂' ∖ {c₀}) k' hk' hC₁' hC₂''_equip hdisj''
        have h_decomp : C₂' = BinUnion (C₂' ∖ {c₀}) {c₀} := by
          apply ExtSet; intro z
          rw [BinUnion_is_specified, SetDiff_is_specified, Singleton_is_specified]
          exact ⟨fun hz => if h : z = c₀ then Or.inr h
                            else Or.inl ⟨hz, h⟩,
                 fun h => h.elim (·.1) (by intro heq; rw [heq]; exact hc₀_C₂)⟩
        have h_union_eq : (C₁' ∪ C₂' : U) = BinUnion (C₁' ∪ (C₂' ∖ {c₀}) : U) {c₀} :=
          (congrArg (BinUnion C₁') h_decomp).trans
            (BinUnion_assoc C₁' (C₂' ∖ {c₀}) {c₀}).symm
        have hc₀_not : c₀ ∉ (C₁' ∪ (C₂' ∖ {c₀}) : U) := by
          intro h; rw [BinUnion_is_specified] at h
          cases h with
          | inl h => exact (disjoint_symm C₁' C₂' hdisj') c₀ hc₀_C₂ h
          | inr h => exact ((SetDiff_is_specified C₂' {c₀} c₀).mp h).2
                       ((Singleton_is_specified c₀ c₀).mpr rfl)
        rw [h_union_eq, succ_add_Omega n' k' hn'_w hk']
        exact union_singleton_equip (add_in_Omega n' k' hn'_w hk') ih_result hc₀_not

    /-! ============================================================ -/
    /-! ### SECTION 6: CARDINALITY PRODUCT THEOREM ### -/
    /-! ============================================================ -/

    /-- For finite sets with known cardinalities, the Cartesian product of
        two sets A and B has cardinality |A| * |B|. -/
    theorem card_product_two {A B n m : U}
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hA : A ≃ₛ n) (hB : B ≃ₛ m) :
        (A ×ₛ B) ≃ₛ mul n m := by
      let P : U → Prop := fun m' => ∀ (B' : U),
        B' ≃ₛ m' → (A ×ₛ B') ≃ₛ mul n m'
      suffices h : P m from h B hB
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have hm_S : m ∈ S := hS ▸ hm
        exact ((SpecSet_is_specified (ω : U) m P).mp hm_S).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun B' hB' => ?_⟩
        have h_eq : (A ×ₛ B' : U) = ∅ := by
          apply ExtSet; intro z
          exact ⟨fun hz => absurd ((CartesianProduct_is_specified A B' z).mp hz).2.2
                    (equip_empty_no_elements hB' (snd z)),
                 fun hz => absurd hz (EmptySet_is_empty z)⟩
        rw [h_eq, mul_zero n hn]
        exact equipotent_refl ∅
      · intro m' hm'
        rw [SpecSet_is_specified] at hm' ⊢
        obtain ⟨hm'_w, ih⟩ := hm'
        refine ⟨succ_in_Omega m' hm'_w, fun B' hB' => ?_⟩
        obtain ⟨g, hg_func, hg_inj, hg_surj⟩ := hB'
        obtain ⟨b₀, hb₀⟩ := hg_surj m' (mem_successor_self m')
        have hb₀_B : b₀ ∈ B' :=
          ((OrderedPair_mem_CartesianProduct b₀ m' B' (σ m')).mp (hg_func.1 _ hb₀)).1
        have hB''_equip : (B' ∖ {b₀}) ≃ₛ m' :=
          bijection_remove_top hm'_w ⟨hg_func, hg_inj, hg_surj⟩ hb₀
        have h_decomp : B' = BinUnion (B' ∖ {b₀}) {b₀} := by
          apply ExtSet; intro z
          rw [BinUnion_is_specified, SetDiff_is_specified, Singleton_is_specified]
          exact ⟨fun hz => if h : z = b₀ then Or.inr h
                            else Or.inl ⟨hz, h⟩,
                 fun h => h.elim (·.1) (by intro heq; rw [heq]; exact hb₀_B)⟩
        have h_product_eq : (A ×ₛ B' : U) = BinUnion (A ×ₛ (B' ∖ {b₀})) (A ×ₛ {b₀}) :=
          (congrArg (CartesianProduct A) h_decomp).trans
            (CartesianProduct_distrib_union_right A (B' ∖ {b₀}) {b₀})
        have h_disj : (A ×ₛ (B' ∖ {b₀})) ⟂ (A ×ₛ {b₀}) := by
          intro z hz₁ hz₂
          exact ((SetDiff_is_specified B' {b₀} (snd z)).mp
              ((CartesianProduct_is_specified A (B' ∖ {b₀}) z).mp hz₁).2.2).2
            ((CartesianProduct_is_specified A {b₀} z).mp hz₂).2.2
        have ih_result := ih (B' ∖ {b₀}) hB''_equip
        have h_singleton := equipotent_trans (product_singleton_equip A b₀) hA
        rw [h_product_eq, mul_succ n m' hn hm'_w]
        exact disjoint_union_equip (mul_in_Omega n m' hn hm'_w) hn
          ih_result h_singleton h_disj

    /-- Double restriction to the same set is idempotent. -/
    private theorem restriction_idempotent (f C : U) : (f ↾ C) ↾ C = f ↾ C := by
      apply ExtSet; intro p
      constructor
      · intro hp
        exact ((Restriction_is_specified (f ↾ C) C p).mp hp).1
      · intro hp
        rw [Restriction_is_specified]
        exact ⟨hp, ((Restriction_is_specified f C p).mp hp).2⟩

    /-- ImageSet commutes with restriction idempotence:
        ImageSet (F ↾ n) n = ImageSet F n. -/
    private theorem ImageSet_restriction_eq (F n : U) :
        ImageSet (F ↾ n) n = ImageSet F n := by
      unfold ImageSet
      rw [restriction_idempotent]

    /-- familyProduct is invariant under restriction of the family to the index set. -/
    private theorem familyProduct_restriction (F n : U) :
        familyProduct (F ↾ n) n = familyProduct F n := by
      apply ExtSet; intro g
      constructor
      · intro h
        rw [mem_familyProduct] at h ⊢
        rw [ImageSet_restriction_eq] at h
        exact ⟨h.1, fun i hi => by rw [← Restriction_apply F n i hi]; exact h.2 i hi⟩
      · intro h
        rw [mem_familyProduct] at h ⊢
        rw [ImageSet_restriction_eq]
        exact ⟨h.1, fun i hi => by rw [Restriction_apply F n i hi]; exact h.2 i hi⟩

    /-- seqProd at ∅ equals σ ∅ for any sequence with isFinSeq f (domain f) ω. -/
    private theorem seqProd_at_zero {f : U} (hf : isFinSeq f (domain f) ω) :
        seqProd f ∅ = (σ (∅ : U)) := by
      simp only [seqProd, dif_pos hf]
      exact seqProdFn_zero hf

    /-- seqProd step for any sequence with isFinSeq f (domain f) ω. -/
    private theorem seqProd_at_succ {f k : U}
        (hf : isFinSeq f (domain f) ω) (hk : k ∈ (ω : U)) :
        seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) := by
      simp only [seqProd, dif_pos hf]
      rw [seqProdFn_succ hf k hk]
      exact prodStepFn_apply hf hk (seqProdFn_apply_in_Omega hf k hk)

    /-- Restriction nesting: if A ⊆ B then (f ↾ B) ↾ A = f ↾ A. -/
    private theorem restriction_nesting {f A B : U} (hAB : A ⊆ B) :
        (f ↾ B) ↾ A = f ↾ A := by
      apply ExtSet; intro p
      constructor
      · intro hp
        have h := (Restriction_is_specified (f ↾ B) A p).mp hp
        have hp_fB := (Restriction_is_specified f B p).mp h.1
        exact (Restriction_is_specified f A p).mpr ⟨hp_fB.1, h.2⟩
      · intro hp
        have h := (Restriction_is_specified f A p).mp hp
        exact (Restriction_is_specified (f ↾ B) A p).mpr
          ⟨(Restriction_is_specified f B p).mpr ⟨h.1, hAB _ h.2⟩, h.2⟩

    /-- Restrict a sequence to a smaller domain. -/
    private theorem isFinSeq_restriction_general {f n A C : U}
        (h : isFinSeq f n A) (hC : C ⊆ n) (hC_omega : C ∈ (ω : U)) :
        isFinSeq (f ↾ C) C A :=
      ⟨hC_omega, Restriction_is_function f n A C h.2 hC⟩

    /-- seqProd is invariant under restriction of the sequence to n
        when the original sequence has domain σ n. -/
    private theorem seqProd_restriction {c n : U}
        (hc : isFinSeq c (σ n) ω) (hn : n ∈ (ω : U)) :
        seqProd (c ↾ n) n = seqProd c n := by
      -- Stronger induction: P(k) holds for ANY c' with ANY domain containing k
      let P : U → Prop := fun k =>
        ∀ c' n', isFinSeq c' n' ω → k ⊆ n' → seqProd (c' ↾ k) k = seqProd c' k
      suffices hP : P n from
        hP c (σ n) hc (fun x hx => mem_successor_of_mem x n hx)
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        exact ((SpecSet_is_specified (ω : U) n P).mp hn_S).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: P(∅)
        rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun c' n' hc' _ => ?_⟩
        have hcr : isFinSeq (c' ↾ ∅) ∅ ω :=
          isFinSeq_restriction_general hc'
            (fun x hx => absurd hx (EmptySet_is_empty x)) zero_in_Omega
        have hc'_dom : isFinSeq c' (domain c') ω := isFinSeq_domain hc' ▸ hc'
        rw [seqProd_zero hcr, seqProd_at_zero hc'_dom]
      · -- Step: P(k) → P(σ k)
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        obtain ⟨hk_w, ih⟩ := hk
        refine ⟨succ_in_Omega k hk_w, fun c' n' hc' hsk_sub => ?_⟩
        -- Need: seqProd (c' ↾ σ k) (σ k) = seqProd c' (σ k)
        have hk_sub : k ⊆ n' := fun x hx =>
          hsk_sub x (mem_successor_of_mem x k hx)
        have hcr_sk : isFinSeq (c' ↾ σ k) (σ k) ω :=
          isFinSeq_restriction_general hc' hsk_sub (succ_in_Omega k hk_w)
        have hc'_dom : isFinSeq c' (domain c') ω := isFinSeq_domain hc' ▸ hc'
        -- Expand both sides
        rw [seqProd_succ hcr_sk hk_w, seqProd_at_succ hc'_dom hk_w]
        -- Goal: mul (seqProd (c' ↾ σ k) k) ((c' ↾ σ k)⦅k⦆) = mul (seqProd c' k) (c'⦅k⦆)
        rw [Restriction_apply c' (σ k) k (mem_successor_self k)]
        -- Goal: mul (seqProd (c' ↾ σ k) k) (c'⦅k⦆) = mul (seqProd c' k) (c'⦅k⦆)
        -- Chain via IH:
        -- (1) seqProd ((c' ↾ σ k) ↾ k) k = seqProd (c' ↾ σ k) k   [IH on c' ↾ σ k]
        -- (2) (c' ↾ σ k) ↾ k = c' ↾ k                              [restriction nesting]
        -- (3) seqProd (c' ↾ k) k = seqProd c' k                     [IH on c']
        -- So: seqProd (c' ↾ σ k) k = seqProd (c' ↾ k) k = seqProd c' k
        have h_nest : (c' ↾ σ k) ↾ k = c' ↾ k :=
          restriction_nesting (fun x hx => mem_successor_of_mem x k hx)
        have h1 := ih (c' ↾ σ k) (σ k) hcr_sk
          (fun x hx => mem_successor_of_mem x k hx)
        -- h1 : seqProd ((c' ↾ σ k) ↾ k) k = seqProd (c' ↾ σ k) k
        rw [h_nest] at h1
        -- h1 : seqProd (c' ↾ k) k = seqProd (c' ↾ σ k) k
        have h2 := ih c' n' hc' hk_sub
        -- h2 : seqProd (c' ↾ k) k = seqProd c' k
        rw [← h1, h2]

    /-- familyProduct F (σ n) ≃ₛ (familyProduct F n) ×ₛ F⦅n⦆. -/
    private theorem familyProduct_succ_decomp {F' n' A' : U} (hn' : n' ∈ (ω : U))
        (hF' : isFinSeq F' (σ n') A') :
        familyProduct F' (σ n') ≃ₛ (familyProduct F' n') ×ₛ F'⦅n'⦆ := by
      -- ImageSet monotonicity
      have h_img_sub : ⋃ (ImageSet F' n') ⊆ ⋃ (ImageSet F' (σ n')) := by
        intro x hx
        rw [UnionSet_is_specified] at hx ⊢
        obtain ⟨S, hS_img, hx_S⟩ := hx
        refine ⟨S, ?_, hx_S⟩
        unfold ImageSet at hS_img ⊢
        rw [mem_range] at hS_img ⊢
        obtain ⟨i, hi⟩ := hS_img
        have hp := (Restriction_is_specified F' n' ⟨i, S⟩).mp hi
        refine ⟨i, (Restriction_is_specified F' (σ n') ⟨i, S⟩).mpr ⟨hp.1, ?_⟩⟩
        rw [fst_of_ordered_pair] at hp ⊢
        exact mem_successor_of_mem i n' hp.2
      -- Forward decomposition
      have h_fwd : ∀ g, g ∈ familyProduct F' (σ n') →
          (g ↾ n') ∈ familyProduct F' n' ∧ g⦅n'⦆ ∈ F'⦅n'⦆ := by
        intro g hg
        have hg_mp := mem_familyProduct.mp hg
        have hg_fs : isFinSeq g (σ n') (⋃ ImageSet F' (σ n')) :=
          mem_FinSeqSet_iff.mp hg_mp.1
        have hg_choice := hg_mp.2
        have hgr := isFinSeq_restriction hg_fs
        constructor
        · rw [mem_familyProduct]
          refine ⟨mem_FinSeqSet_iff.mpr ⟨hn', ?_, hgr.2.2⟩,
                  fun i hi => ?_⟩
          · intro p hp
            have hp' := hgr.2.1 p hp
            rw [CartesianProduct_is_specified] at hp' ⊢
            refine ⟨hp'.1, hp'.2.1, ?_⟩
            obtain ⟨i₀, y₀, rfl⟩ := hp'.1
            rw [fst_of_ordered_pair] at hp'
            rw [snd_of_ordered_pair]
            have h_iy_in_g := ((Restriction_is_specified g n' ⟨i₀, y₀⟩).mp hp).1
            have h_y_eq : y₀ = g⦅i₀⦆ :=
              (apply_eq g i₀ y₀ (hg_fs.2.2 i₀
                (mem_successor_of_mem i₀ n' hp'.2.1)) h_iy_in_g).symm
            rw [h_y_eq, UnionSet_is_specified]
            exact ⟨F'⦅i₀⦆,
              (mem_range (F' ↾ n') (F'⦅i₀⦆)).mpr ⟨i₀,
                (Restriction_is_specified F' n' ⟨i₀, F'⦅i₀⦆⟩).mpr
                  ⟨isFinSeq_pair_mem hF' (mem_successor_of_mem i₀ n' hp'.2.1),
                   by rw [fst_of_ordered_pair]; exact hp'.2.1⟩⟩,
              hg_choice i₀ (mem_successor_of_mem i₀ n' hp'.2.1)⟩
          · rw [Restriction_apply g n' i hi]
            exact hg_choice i (mem_successor_of_mem i n' hi)
        · exact hg_choice n' (mem_successor_self n')
      -- Bijection φ: g ↦ ⟨g ↾ n', g⦅n'⦆⟩
      let FPsn := familyProduct F' (σ n')
      let FPn := familyProduct F' n'
      let Fn' := F'⦅n'⦆
      let φ := SpecSet (FPsn ×ₛ (FPn ×ₛ Fn'))
        (fun p => ∃ g, g ∈ FPsn ∧ p = ⟨g, ⟨g ↾ n', g⦅n'⦆⟩⟩)
      refine ⟨φ, ?_, ?_, ?_⟩
      · -- isFunctionFromTo
        constructor
        · exact fun p hp => ((SpecSet_is_specified _ p _).mp hp).1
        · intro x hx
          have hsc := h_fwd x hx
          refine ⟨⟨x ↾ n', x⦅n'⦆⟩, ?_, fun y hy => ?_⟩
          · exact (SpecSet_is_specified _ _ _).mpr
              ⟨(OrderedPair_mem_CartesianProduct x ⟨x ↾ n', x⦅n'⦆⟩ FPsn (FPn ×ₛ Fn')).mpr
                ⟨hx, (OrderedPair_mem_CartesianProduct (x ↾ n') (x⦅n'⦆) FPn Fn').mpr
                  ⟨hsc.1, hsc.2⟩⟩,
               x, hx, rfl⟩
          · obtain ⟨_, g, hg_mem, heq⟩ := (SpecSet_is_specified _ _ _).mp hy
            have hpair := Eq_of_OrderedPairs_given_projections x y g ⟨g ↾ n', g⦅n'⦆⟩ heq
            rw [hpair.1]; exact hpair.2
      · -- isInjective
        intro x₁ x₂ y h₁ h₂
        obtain ⟨_, g₁, hg₁_mem, heq₁⟩ := (SpecSet_is_specified _ _ _).mp h₁
        obtain ⟨_, g₂, hg₂_mem, heq₂⟩ := (SpecSet_is_specified _ _ _).mp h₂
        have p₁ := Eq_of_OrderedPairs_given_projections x₁ y g₁ ⟨g₁ ↾ n', g₁⦅n'⦆⟩ heq₁
        have p₂ := Eq_of_OrderedPairs_given_projections x₂ y g₂ ⟨g₂ ↾ n', g₂⦅n'⦆⟩ heq₂
        have h_y_eq := p₁.2.symm.trans p₂.2
        have h_pair := (OrderedPair_eq_iff (g₁ ↾ n') (g₁⦅n'⦆) (g₂ ↾ n') (g₂⦅n'⦆)).mp h_y_eq
        have hg₁_fs : isFinSeq g₁ (σ n') (⋃ ImageSet F' (σ n')) :=
          mem_FinSeqSet_iff.mp ((mem_familyProduct.mp hg₁_mem).1)
        have hg₂_fs : isFinSeq g₂ (σ n') (⋃ ImageSet F' (σ n')) :=
          mem_FinSeqSet_iff.mp ((mem_familyProduct.mp hg₂_mem).1)
        have h_ext : g₁ = g₂ := isFinSeq_ext hg₁_fs hg₂_fs (fun i hi => by
          cases (successor_is_specified n' i).mp hi with
          | inl h_in =>
            rw [← Restriction_apply g₁ n' i h_in, ← Restriction_apply g₂ n' i h_in,
                h_pair.1]
          | inr h_eq => rw [h_eq]; exact h_pair.2)
        exact p₁.1.trans (h_ext ▸ p₂.1.symm)
      · -- isSurjectiveOnto
        intro y hy
        have hycp := (CartesianProduct_is_specified FPn Fn' y).mp hy
        have hy_pair : y = ⟨fst y, snd y⟩ :=
          (isOrderedPair_by_construction y).mp hycp.1
        have hfst_FP : fst y ∈ FPn := hycp.2.1
        have hsnd_F : snd y ∈ Fn' := hycp.2.2
        have hfs : isFinSeq (fst y) n' (⋃ ImageSet F' n') :=
          mem_FinSeqSet_iff.mp ((mem_familyProduct.mp hfst_FP).1)
        have hfs_choice := (mem_familyProduct.mp hfst_FP).2
        -- Widen codomain for appendElem
        have h_widen : isFinSeq (fst y) n' (⋃ ImageSet F' (σ n')) :=
          ⟨hfs.1, fun p hp =>
            CartesianProduct_mono n' n' _ _ (fun x hx => hx) h_img_sub _ (hfs.2.1 p hp),
           hfs.2.2⟩
        have h_snd_union : snd y ∈ ⋃ (ImageSet F' (σ n')) := by
          rw [UnionSet_is_specified]
          refine ⟨F'⦅n'⦆, ?_, hsnd_F⟩
          unfold ImageSet; rw [mem_range]
          exact ⟨n', (Restriction_is_specified F' (σ n') ⟨n', F'⦅n'⦆⟩).mpr
            ⟨isFinSeq_pair_mem hF' (mem_successor_self n'),
             by rw [fst_of_ordered_pair]; exact mem_successor_self n'⟩⟩
        have hg_fs := isFinSeq_appendElem h_widen h_snd_union
        have hg_mem : appendElem (fst y) n' (snd y) ∈ FPsn := by
          rw [mem_familyProduct]
          refine ⟨mem_FinSeqSet_iff.mpr hg_fs, fun i hi => ?_⟩
          cases (successor_is_specified n' i).mp hi with
          | inl h_in =>
            rw [appendElem_apply_prev h_widen h_in]
            exact hfs_choice i h_in
          | inr h_eq =>
            rw [h_eq, appendElem_apply_last h_widen]
            exact hsnd_F
        have h_restr_eq : appendElem (fst y) n' (snd y) ↾ n' = fst y :=
          isFinSeq_ext (isFinSeq_restriction hg_fs) h_widen (fun i hi => by
            rw [Restriction_apply (appendElem (fst y) n' (snd y)) n' i hi,
                appendElem_apply_prev h_widen hi])
        have h_last : (appendElem (fst y) n' (snd y))⦅n'⦆ = snd y :=
          appendElem_apply_last h_widen
        have h_pair_eq : ⟨appendElem (fst y) n' (snd y) ↾ n',
            (appendElem (fst y) n' (snd y))⦅n'⦆⟩ = y := by
          rw [h_restr_eq, h_last]; exact hy_pair.symm
        refine ⟨appendElem (fst y) n' (snd y),
          (SpecSet_is_specified _ _ _).mpr
            ⟨(OrderedPair_mem_CartesianProduct _ _ FPsn (FPn ×ₛ Fn')).mpr ⟨hg_mem, hy⟩,
             appendElem (fst y) n' (snd y), hg_mem,
             OrderedPair_eq_of _ _ _ _ ⟨rfl, h_pair_eq.symm⟩⟩⟩

    /-- For a finite family F : n → Sets where each F(i) is finite with
        cardinality c(i), the Cartesian product Π_{i<n} F(i) is equipotent
        to the numeric product Π_{i<n} c(i). -/
    theorem card_familyProduct {F c n : U}
        (hn : n ∈ (ω : U))
        (hF : isFinSeq F n (⋃ (ImageSet F n)))
        (hc : isFinSeq c n ω)
        (hcard : ∀ i, i ∈ n → F⦅i⦆ ≃ₛ c⦅i⦆) :
        familyProduct F n ≃ₛ seqProd c n := by
      let P : U → Prop := fun n' => ∀ F' c' A',
        isFinSeq F' n' A' → isFinSeq c' n' ω →
        (∀ i, i ∈ n' → F'⦅i⦆ ≃ₛ c'⦅i⦆) →
        familyProduct F' n' ≃ₛ seqProd c' n'
      suffices h : P n from h F c _ hF hc hcard
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        exact ((SpecSet_is_specified (ω : U) n P).mp hn_S).2
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- BASE: P(∅)
        rw [SpecSet_is_specified]
        refine ⟨zero_in_Omega, fun F' c' A' _ hc' _ => ?_⟩
        rw [familyProduct_zero, seqProd_zero hc']
        have h_succ_zero : σ (∅ : U) = {∅} := BinUnion_empty_left {∅}
        rw [h_succ_zero]
        exact equipotent_refl {∅}
      · -- STEP: P(n') → P(σ n')
        intro n' hn'
        rw [SpecSet_is_specified] at hn' ⊢
        obtain ⟨hn'_w, ih⟩ := hn'
        refine ⟨succ_in_Omega n' hn'_w, fun F' c' A' hF' hc' hcard' => ?_⟩
        rw [seqProd_succ hc' hn'_w]
        -- IH: familyProduct F' n' ≃ₛ seqProd c' n'
        have hFr := isFinSeq_restriction hF'
        have hcr := isFinSeq_restriction hc'
        have hcard_r : ∀ i, i ∈ n' → (F' ↾ n')⦅i⦆ ≃ₛ (c' ↾ n')⦅i⦆ := fun i hi => by
          rw [Restriction_apply F' n' i hi, Restriction_apply c' n' i hi]
          exact hcard' i (mem_successor_of_mem i n' hi)
        have ih_result := ih (F' ↾ n') (c' ↾ n') A' hFr hcr hcard_r
        rw [familyProduct_restriction, seqProd_restriction hc' hn'_w] at ih_result
        -- Decomposition + card_product_two
        have h_decomp := familyProduct_succ_decomp hn'_w hF'
        have hsp_w : seqProd c' n' ∈ (ω : U) :=
          seqProd_restriction hc' hn'_w ▸ seqProd_in_Omega hcr
        have hcn'_w : c'⦅n'⦆ ∈ (ω : U) := apply_in_Omega_of_isFinSeq hc'
        exact equipotent_trans h_decomp
          (card_product_two hsp_w hcn'_w ih_result (hcard' n' (mem_successor_self n')))

  end FiniteSequencesArith

  export FiniteSequencesArith (
    -- Section 1: Summation step function
    sumStepFn
    mem_sumStepFn
    sumStepFn_is_function
    sumStepFn_apply
    -- Section 2: Summation
    seqSumFn
    seqSumFn_is_function
    seqSum
    seqSum_zero
    seqSum_succ
    seqSum_in_Omega
    seqSum_singleton
    -- Section 3: Product step function
    prodStepFn
    prodStepFn_is_function
    prodStepFn_apply
    -- Section 4: Numeric product
    seqProdFn
    seqProdFn_is_function
    seqProd
    seqProd_zero
    seqProd_succ
    seqProd_in_Omega
    seqProd_singleton
    -- Section 5: Cartesian product of a family
    familyProduct
    mem_familyProduct
    familyProduct_zero
    familyProduct_succ_char
    -- Section 6: Cardinality product theorem
    card_product_two
    card_familyProduct
  )

end SetUniverse
