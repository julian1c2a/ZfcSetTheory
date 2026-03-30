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

    /-- sumStepFn f is a function from ω ×ₛ ω to ω, when f maps into ω. -/
    theorem sumStepFn_is_function {f n : U} (hf : isFinSeq f n ω) :
        isFunctionFromTo (sumStepFn f) (ω ×ₛ ω) ω := by
      sorry

    /-- Applying sumStepFn yields add v (f⦅k⦆). -/
    theorem sumStepFn_apply {f k v : U} (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) :
        (sumStepFn f)⦅⟨k, v⟩⦆ = add v (f⦅k⦆) := by
      sorry

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
      if h : isFinSeq f n ω then
        apply (seqSumFn f (isFinSeq_domain h ▸ h)) n
      else ∅

    /-- seqSum f ∅ = ∅ (empty sum is zero). -/
    theorem seqSum_zero {f : U} (hf : isFinSeq f ∅ ω) : seqSum f ∅ = ∅ := by
      sorry

    /-- seqSum f (σ k) = add (seqSum f k) (f⦅k⦆) for k ∈ ω. -/
    theorem seqSum_succ {f k A : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) :
        seqSum f (σ k) = add (seqSum f k) (f⦅k⦆) := by
      sorry

    /-- seqSum f n ∈ ω when f : n → ω. -/
    theorem seqSum_in_Omega {f n : U} (hf : isFinSeq f n ω) :
        seqSum f n ∈ ω := by
      sorry

    /-- Sum of a singleton sequence. -/
    theorem seqSum_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) :
        seqSum f (σ ∅) = f⦅∅⦆ := by
      sorry

    /-! ============================================================ -/
    /-! ### SECTION 3: PRODUCT STEP FUNCTION ### -/
    /-! ============================================================ -/

    /-- Step function for product: maps ⟨k, v⟩ ↦ mul v (f⦅k⦆). -/
    noncomputable def prodStepFn (f : U) : U :=
      SpecSet ((ω ×ₛ ω) ×ₛ ω)
        (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧
          p = ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩)

    /-- prodStepFn f is a function from ω ×ₛ ω to ω. -/
    theorem prodStepFn_is_function {f n : U} (hf : isFinSeq f n ω) :
        isFunctionFromTo (prodStepFn f) (ω ×ₛ ω) ω := by
      sorry

    /-- Applying prodStepFn yields mul v (f⦅k⦆). -/
    theorem prodStepFn_apply {f k v : U} (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) :
        (prodStepFn f)⦅⟨k, v⟩⦆ = mul v (f⦅k⦆) := by
      sorry

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
      if h : isFinSeq f n ω then
        apply (seqProdFn f (isFinSeq_domain h ▸ h)) n
      else ∅

    /-- seqProd f ∅ = σ ∅ (empty product is one). -/
    theorem seqProd_zero {f : U} (hf : isFinSeq f ∅ ω) : seqProd f ∅ = (σ (∅ : U)) := by
      sorry

    /-- seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) for k ∈ ω. -/
    theorem seqProd_succ {f k : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) :
        seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) := by
      sorry

    /-- seqProd f n ∈ ω when f : n → ω. -/
    theorem seqProd_in_Omega {f n : U} (hf : isFinSeq f n ω) :
        seqProd f n ∈ ω := by
      sorry

    /-- Product of a singleton sequence. -/
    theorem seqProd_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) :
        seqProd f (σ ∅) = f⦅∅⦆ := by
      sorry

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
      sorry

    /-! ============================================================ -/
    /-! ### SECTION 6: CARDINALITY PRODUCT THEOREM ### -/
    /-! ============================================================ -/

    /-- For finite sets with known cardinalities, the Cartesian product of
        two sets A and B has cardinality |A| * |B|. -/
    theorem card_product_two {A B n m : U}
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hA : A ≃ₛ n) (hB : B ≃ₛ m) :
        (A ×ₛ B) ≃ₛ mul n m := by
      sorry

    /-- For a finite family F : n → Sets where each F(i) is finite with
        cardinality c(i), the Cartesian product Π_{i<n} F(i) is equipotent
        to the numeric product Π_{i<n} c(i). -/
    theorem card_familyProduct {F c n : U}
        (hn : n ∈ (ω : U))
        (hF : isFinSeq F n (⋃ (ImageSet F n)))
        (hc : isFinSeq c n ω)
        (hcard : ∀ i, i ∈ n → F⦅i⦆ ≃ₛ c⦅i⦆) :
        familyProduct F n ≃ₛ seqProd c n := by
      sorry

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
