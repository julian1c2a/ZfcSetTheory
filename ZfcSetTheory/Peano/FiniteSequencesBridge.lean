/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Finite Sequences Bridge: DList ↔ ZFC and TFA Restatement

This module establishes the bridge between Peano-side DList ℕ₀ and ZFC finite
sequences, defines nth (element access), and restates the Fundamental Theorem
of Arithmetic using ZFC-native sequences.

## Strategy

We define `dlistToSeq : DList ℕ₀ → U` via appendElem recursion (reverse order),
prove it produces a valid finite sequence, and show the product correspondence
via a general `seqProd_ext` extensionality lemma. The TFA is restated in pure
ZFC terms: ∃ f k, isFinSeq f k ω ∧ allPrime ∧ seqProd f k = n.

## Key design decisions

1. `seqProd_succ_gen` / `seqProd_zero_gen`: generalized recursion equations
   for seqProd that work with `isFinSeq f (domain f) ω` rather than requiring
   domain f = σ k exactly. Derived by accessing RecursionTheoremWithStep spec.

2. `seqProd_ext`: extensionality — seqProd only depends on function values
   at indices < n. This is the critical lemma enabling the DList bridge.

3. `dlistToSeq` places elements in REVERSE order (head of DList goes to
   last index). This is irrelevant for TFA since multiplication is commutative.

## Main Definitions

* `nth f i`               — element access (wrapper for apply)
* `dlistToSeq ps`         — convert DList ℕ₀ to ZFC finite sequence in ω
* `isPrimeSeq f k`        — f is a finite sequence of primes of length k

## Main Theorems

* `seqProd_zero_gen`       — seqProd f ∅ = σ ∅ (general version)
* `seqProd_succ_gen`       — seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) (general)
* `seqProd_ext`            — extensionality for seqProd
* `dlistToSeq_isFinSeq`    — dlistToSeq produces valid finite sequences
* `dlistToSeq_seqProd`     — product correspondence with product_list
* `exists_prime_factorization_native` — TFA existence with ZFC sequences
* `unique_prime_factorization_native` — TFA uniqueness with ZFC sequences
-/

import ZfcSetTheory.Peano.FiniteSequencesArith
import ZfcSetTheory.Nat.Primes

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
  open SetUniverse.FiniteSequencesArith
  open SetUniverse.NaturalNumbersPrimes

  universe u
  variable {U : Type u}

  namespace FiniteSequencesBridge

    -- =========================================================================
    -- §1  nth — Element access for finite sequences
    -- =========================================================================

    /-- Element access at index i of a finite sequence f.
        This is a named wrapper for `apply f i` = `f⦅i⦆`. -/
    noncomputable def nth (f i : U) : U := f⦅i⦆

    /-- nth is just apply. -/
    theorem nth_eq_apply (f i : U) : nth f i = f⦅i⦆ := rfl

    /-- Accessed element lies in the codomain. -/
    theorem nth_mem {f n A i : U} (h : isFinSeq f n A) (hi : i ∈ n) :
        nth f i ∈ A :=
      nth_eq_apply f i ▸ isFinSeq_apply_mem h hi

    /-- Last element access after appending. -/
    theorem nth_appendElem_last {f n A a : U} (hf : isFinSeq f n A) :
        nth (appendElem f n a) n = a :=
      nth_eq_apply _ n ▸ appendElem_apply_last hf

    /-- Previous elements unchanged after appending. -/
    theorem nth_appendElem_prev {f n A a i : U} (hf : isFinSeq f n A) (hi : i ∈ n) :
        nth (appendElem f n a) i = nth f i :=
      nth_eq_apply _ i ▸ nth_eq_apply f i ▸ appendElem_apply_prev hf hi

    -- =========================================================================
    -- §2  General seqProd recursion equations
    -- =========================================================================

    /-- Full specification of seqProdFn, re-derived from RecursionTheoremWithStep.
        This gives access to the zero and succ equations without needing the
        private helpers from FiniteSequencesArith. -/
    private theorem seqProdFn_spec {f : U} (hf : isFinSeq f (domain f) ω) :
        isFunctionFromTo (seqProdFn f hf) ω ω ∧
        apply (seqProdFn f hf) (∅ : U) = σ (∅ : U) ∧
        ∀ n, n ∈ ω → apply (seqProdFn f hf) (σ n) =
          apply (prodStepFn f) ⟨n, apply (seqProdFn f hf) n⟩ :=
      Classical.choose_spec (ExistsUnique.exists
        (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
          (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))

    /-- Apply of seqProdFn at a natural lies in ω. -/
    private theorem seqProdFn_apply_in_Omega' {f : U} (hf : isFinSeq f (domain f) ω)
        (n : U) (hn : n ∈ (ω : U)) : apply (seqProdFn f hf) n ∈ (ω : U) := by
      have hF := (seqProdFn_spec hf).1
      have h_pair := apply_mem (seqProdFn f hf) n (hF.2 n hn)
      exact ((OrderedPair_mem_CartesianProduct n _ ω ω).mp (hF.1 _ h_pair)).2

    /-- **General zero equation**: seqProd f ∅ = σ ∅ for any f with
        `isFinSeq f (domain f) ω`, regardless of what domain f is. -/
    theorem seqProd_zero_gen {f : U} (hf : isFinSeq f (domain f) ω) :
        seqProd f ∅ = σ (∅ : U) := by
      simp only [seqProd, dif_pos hf]
      exact (seqProdFn_spec hf).2.1

    /-- **General succ equation**: seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆)
        for any k ∈ ω, regardless of the domain of f. -/
    theorem seqProd_succ_gen {f : U} (hf : isFinSeq f (domain f) ω)
        (k : U) (hk : k ∈ (ω : U)) :
        seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆) := by
      simp only [seqProd, dif_pos hf]
      rw [(seqProdFn_spec hf).2.2 k hk]
      exact prodStepFn_apply hf hk (seqProdFn_apply_in_Omega' hf k hk)

    /-- seqProd f k ∈ ω for any k ∈ ω (general version). -/
    theorem seqProd_in_Omega_gen {f : U} (hf : isFinSeq f (domain f) ω)
        (k : U) (hk : k ∈ (ω : U)) : seqProd f k ∈ (ω : U) := by
      simp only [seqProd, dif_pos hf]
      exact seqProdFn_apply_in_Omega' hf k hk

    -- =========================================================================
    -- §3  seqProd extensionality
    -- =========================================================================

    /-- **Extensionality for seqProd**: if two finite sequences into ω agree
        on all indices in n, then their products up to n are equal. -/
    theorem seqProd_ext {f g : U}
        (hf : isFinSeq f (domain f) ω)
        (hg : isFinSeq g (domain g) ω)
        (n : U) (hn : n ∈ (ω : U))
        (h_agree : ∀ i, i ∈ n → f⦅i⦆ = g⦅i⦆) :
        seqProd f n = seqProd g n := by
      -- Induction on n ∈ ω
      let P : U → Prop := fun k =>
        ∀ f' g' : U, isFinSeq f' (domain f') ω → isFinSeq g' (domain g') ω →
          (∀ i, i ∈ k → f'⦅i⦆ = g'⦅i⦆) → seqProd f' k = seqProd g' k
      let S := SpecSet (ω : U) P
      suffices hS : S = ω by
        have hn_S : n ∈ S := hS ▸ hn
        exact ((SpecSet_is_specified (ω : U) n P).mp hn_S).2 f g hf hg h_agree
      apply induction_principle S
      · exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
      · -- Base: k = ∅
        rw [SpecSet_is_specified]
        exact ⟨zero_in_Omega, fun f' g' hf' hg' _ =>
          (seqProd_zero_gen hf').trans (seqProd_zero_gen hg').symm⟩
      · -- Step: k → σ k
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        obtain ⟨hk_omega, ih⟩ := hk
        simp only [P] at ih ⊢
        exact ⟨succ_in_Omega k hk_omega, fun f' g' hf' hg' h_agree_sk => by
          rw [seqProd_succ_gen hf' k hk_omega, seqProd_succ_gen hg' k hk_omega]
          have h_sub : ∀ i, i ∈ k → f'⦅i⦆ = g'⦅i⦆ :=
            fun i hi => h_agree_sk i (mem_successor_of_mem i k hi)
          rw [ih f' g' hf' hg' h_sub, h_agree_sk k (mem_successor_self k)]⟩

    -- =========================================================================
    -- §4  DList → ZFC Sequence Bridge
    -- =========================================================================

    /-- fromPeano maps zero to ∅. -/
    private theorem fromPeano_zero_eq : (fromPeano Peano.ℕ₀.zero : U) = ∅ :=
      (congrArg fromPeano toPeano_zero.symm).trans (fromPeano_toPeano ∅ zero_is_nat)

    /-- fromPeano maps succ to σ. -/
    private theorem fromPeano_succ_eq (n : Peano.ℕ₀) :
        (fromPeano (Peano.ℕ₀.succ n) : U) = σ (fromPeano n : U) := by
      have hn : isNat (fromPeano n : U) := fromPeano_is_nat n
      have h1 := toPeano_successor (fromPeano n : U) hn
      rw [toPeano_fromPeano] at h1
      exact (congrArg fromPeano h1.symm).trans
        (fromPeano_toPeano (σ (fromPeano n : U) : U) (nat_successor_is_nat _ hn))

    /-- Convert a `DList ℕ₀` to a ZFC finite sequence in ω.
        Elements are placed in REVERSE order: head of DList goes to the
        last index. This is irrelevant for product computations since
        multiplication in ω is commutative. -/
    noncomputable def dlistToSeq : DList Peano.ℕ₀ → U
      | .nil       => (∅ : U)
      | .cons x xs =>
          appendElem (dlistToSeq xs) (fromPeano (DList.length xs)) (fromPeano x)

    /-- The ZFC length of a converted DList. -/
    noncomputable def dlistLen (ps : DList Peano.ℕ₀) : U :=
      fromPeano (DList.length ps)

    /-- Unfolding lemma: dlistToSeq nil = ∅. -/
    @[simp] theorem dlistToSeq_nil : (dlistToSeq (.nil : DList Peano.ℕ₀) : U) = ∅ := rfl

    /-- Unfolding lemma: dlistToSeq (cons x xs). -/
    @[simp] theorem dlistToSeq_cons (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀) :
        (dlistToSeq (.cons x xs) : U) =
          appendElem (dlistToSeq xs) (fromPeano (DList.length xs)) (fromPeano x) := rfl

    /-- Unfolding lemma: dlistLen nil = fromPeano 𝟘. -/
    @[simp] theorem dlistLen_nil : (dlistLen (.nil : DList Peano.ℕ₀) : U) = fromPeano (Peano.ℕ₀.zero) := rfl

    /-- Unfolding lemma: dlistLen (cons x xs) = fromPeano (succ (length xs)). -/
    @[simp] theorem dlistLen_cons (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀) :
        (dlistLen (.cons x xs) : U) = fromPeano (Peano.ℕ₀.succ (DList.length xs)) := rfl

    /-- dlistToSeq produces a valid finite sequence in ω. -/
    theorem dlistToSeq_isFinSeq : (ps : DList Peano.ℕ₀) →
        isFinSeq (dlistToSeq ps : U) (dlistLen ps) (ω : U)
      | .nil => by
          rw [dlistToSeq_nil, dlistLen_nil, fromPeano]
          exact isFinSeq_empty ω
      | .cons x xs => by
          rw [dlistToSeq_cons, dlistLen_cons, fromPeano]
          exact isFinSeq_appendElem (dlistToSeq_isFinSeq xs)
            (Nat_in_Omega (fromPeano x) (fromPeano_is_nat x))

    /-- Domain of dlistToSeq equals dlistLen. -/
    theorem dlistToSeq_domain (ps : DList Peano.ℕ₀) :
        domain (dlistToSeq ps : U) = dlistLen ps :=
      isFinSeq_domain (dlistToSeq_isFinSeq ps)

    /-- dlistToSeq satisfies isFinSeq at domain level. -/
    theorem dlistToSeq_isFinSeq_domain (ps : DList Peano.ℕ₀) :
        isFinSeq (dlistToSeq ps : U) (domain (dlistToSeq ps)) (ω : U) :=
      dlistToSeq_domain ps ▸ dlistToSeq_isFinSeq ps

    /-- The length of dlistToSeq as seqLength. -/
    theorem dlistToSeq_seqLength (ps : DList Peano.ℕ₀) :
        seqLength (dlistToSeq ps : U) = dlistLen ps :=
      seqLength_eq (dlistToSeq_isFinSeq ps)

    /-- dlistLen is in ω. -/
    theorem dlistLen_in_Omega (ps : DList Peano.ℕ₀) :
        (dlistLen ps : U) ∈ (ω : U) :=
      Nat_in_Omega _ (fromPeano_is_nat (DList.length ps))

    /-- Element access at the last index of dlistToSeq (cons x xs). -/
    theorem dlistToSeq_apply_last (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀) :
        (dlistToSeq (.cons x xs) : U)⦅dlistLen xs⦆ =
          (fromPeano x : U) :=
      appendElem_apply_last (dlistToSeq_isFinSeq xs)

    /-- Element access at earlier indices of dlistToSeq (cons x xs). -/
    theorem dlistToSeq_apply_prev (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀)
        (i : U) (hi : i ∈ (dlistLen xs : U)) :
        (dlistToSeq (.cons x xs) : U)⦅i⦆ = (dlistToSeq xs : U)⦅i⦆ :=
      appendElem_apply_prev (dlistToSeq_isFinSeq xs) hi

    -- =========================================================================
    -- §5  seqProd correspondence: dlistToSeq ↔ product_list
    -- =========================================================================

    /-- **Product correspondence**: the seqProd of a converted DList equals
        the fromPeano of the Peano product_list.
        Uses seqProd_ext to handle the appendElem extensionality. -/
    theorem dlistToSeq_seqProd : (ps : DList Peano.ℕ₀) →
        seqProd (dlistToSeq ps : U) (dlistLen ps) =
          (fromPeano (product_list ps) : U)
      | .nil => by
          rw [dlistToSeq_nil, dlistLen_nil, fromPeano_zero_eq,
              seqProd_zero (isFinSeq_empty ω)]
          -- Goal: σ ∅ = fromPeano (product_list .nil)
          -- product_list .nil = 𝟙 = Peano.ℕ₀.succ Peano.ℕ₀.zero (by def)
          change σ (∅ : U) = fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero)
          rw [fromPeano_succ_eq, fromPeano_zero_eq]
      | .cons x xs => by
          -- Step 1: Unfold dlistLen (.cons x xs) = σ (dlistLen xs)
          have h_len : (dlistLen (.cons x xs) : U) = σ (dlistLen xs : U) := by
            rw [dlistLen_cons, fromPeano_succ_eq]; rfl
          rw [h_len]
          -- Goal: seqProd (dlistToSeq (.cons x xs) : U) (σ (dlistLen xs))
          --      = fromPeano (product_list (.cons x xs))
          -- Step 2: Apply seqProd_succ_gen
          have h_dom := @dlistToSeq_isFinSeq_domain U (.cons x xs)
          have h_len_xs_omega : (dlistLen xs : U) ∈ (ω : U) :=
            @dlistLen_in_Omega U xs
          rw [seqProd_succ_gen h_dom (dlistLen xs) h_len_xs_omega]
          -- Goal: mul (seqProd (dlistToSeq (.cons x xs)) (dlistLen xs))
          --           ((dlistToSeq (.cons x xs))⦅dlistLen xs⦆)
          --      = fromPeano (product_list (.cons x xs))
          -- Step 3: Last element access
          rw [dlistToSeq_apply_last x xs]
          -- Goal: mul (seqProd (dlistToSeq (.cons x xs)) (dlistLen xs)) (fromPeano x)
          --      = fromPeano (product_list (.cons x xs))
          -- Step 4: seqProd extensionality
          have h_dom_xs := @dlistToSeq_isFinSeq_domain U xs
          have h_agree : ∀ i, i ∈ (dlistLen xs : U) →
              (dlistToSeq (.cons x xs : DList Peano.ℕ₀) : U)⦅i⦆ =
                (dlistToSeq xs : U)⦅i⦆ :=
            fun i hi => dlistToSeq_apply_prev x xs i hi
          rw [seqProd_ext h_dom h_dom_xs (dlistLen xs) h_len_xs_omega h_agree]
          -- Goal: mul (seqProd (dlistToSeq xs) (dlistLen xs)) (fromPeano x)
          --      = fromPeano (product_list (.cons x xs))
          -- Step 5: Apply IH
          rw [dlistToSeq_seqProd xs]
          -- Goal: mul (fromPeano (product_list xs)) (fromPeano x)
          --      = fromPeano (product_list (.cons x xs))
          -- Step 6: product_cons + fromPeano_mul + mul_comm
          rw [product_cons, fromPeano_mul x (product_list xs)]
          exact mul_comm_Omega (fromPeano (product_list xs))
            (fromPeano x)
            (Nat_in_Omega _ (fromPeano_is_nat (product_list xs)))
            (Nat_in_Omega _ (fromPeano_is_nat x))

    -- =========================================================================
    -- §6  isPrimeSeq and DList conversion
    -- =========================================================================

    /-- A finite sequence of primes of length k. -/
    def isPrimeSeq (f k : U) : Prop :=
      isFinSeq f k ω ∧ ∀ i, i ∈ k → isPrime (f⦅i⦆)

    /-- Converting a PrimeList DList yields an isPrimeSeq. -/
    theorem dlistToSeq_isPrimeSeq : (ps : DList Peano.ℕ₀) → PrimeList ps →
        isPrimeSeq (dlistToSeq ps : U) (dlistLen ps)
      | .nil, _ => by
          constructor
          · exact @dlistToSeq_isFinSeq U .nil
          · intro i hi; exact absurd hi (EmptySet_is_empty i)
      | .cons x xs, hpl => by
          constructor
          · exact @dlistToSeq_isFinSeq U (.cons x xs)
          · intro i hi
            have h_len : (dlistLen (.cons x xs) : U) = σ (dlistLen xs : U) := by
              rw [dlistLen_cons, fromPeano_succ_eq]; rfl
            rw [h_len] at hi
            cases (successor_is_specified (dlistLen xs : U) i).mp hi with
            | inl hi_prev =>
              rw [dlistToSeq_apply_prev x xs i hi_prev]
              exact (dlistToSeq_isPrimeSeq xs (fun q hq => hpl q (Or.inr hq))).2 i hi_prev
            | inr hi_last =>
              rw [hi_last, dlistToSeq_apply_last]
              exact (fromPeano_prime x).mp (hpl x (Or.inl rfl))

    -- =========================================================================
    -- §7  TFA with ZFC-native sequences
    -- =========================================================================

    /-- **TFA — Existence (Approach B)**: every `n ∈ ω` with `n ≥ 2` has a
        ZFC-native finite sequence of primes whose seqProd equals `n`.
        This is a pure ZFC statement — no DList or Peano types appear
        in the conclusion. -/
    theorem exists_prime_factorization_native (n : U) (hn : n ∈ (ω : U))
        (h_ge2 : σ (σ (∅ : U)) ∈ n ∨ σ (σ (∅ : U)) = n) :
        ∃ f k : U, isPrimeSeq f k ∧ seqProd f k = n := by
      -- Get DList factorization from Approach A
      obtain ⟨ps, hpl, hprod⟩ := exists_prime_factorization_ZFC n hn h_ge2
      -- Convert to ZFC sequence
      refine ⟨dlistToSeq ps, dlistLen ps, dlistToSeq_isPrimeSeq ps hpl, ?_⟩
      -- Product correspondence
      rw [dlistToSeq_seqProd ps]
      exact hprod

    /-- **TFA — Uniqueness (Approach B)**: if two `DList ℕ₀` prime lists yield
        the same ZFC seqProd, they have equal multiplicity for each prime.
        This bridges the uniqueness statement to seqProd equality. -/
    theorem unique_prime_factorization_native
        (ps qs : DList Peano.ℕ₀) (hps : PrimeList ps) (hqs : PrimeList qs)
        (h_prod : seqProd (dlistToSeq ps : U) (dlistLen ps) =
                  seqProd (dlistToSeq qs : U) (dlistLen qs))
        (p : Peano.ℕ₀) (hp : Peano.Arith.Prime p) :
        DList.length (DList.filter (fun q => decide (q = p)) ps) =
        DList.length (DList.filter (fun q => decide (q = p)) qs) := by
      -- Convert seqProd equality to fromPeano product_list equality
      rw [dlistToSeq_seqProd, dlistToSeq_seqProd] at h_prod
      -- Apply Approach A uniqueness
      exact unique_prime_factorization_ZFC ps qs hps hqs h_prod p hp

  end FiniteSequencesBridge

  export FiniteSequencesBridge (
    -- §1: nth
    nth
    nth_eq_apply
    nth_mem
    nth_appendElem_last
    nth_appendElem_prev
    -- §2: General seqProd recursion
    seqProd_zero_gen
    seqProd_succ_gen
    seqProd_in_Omega_gen
    -- §3: seqProd extensionality
    seqProd_ext
    -- §4: DList → ZFC bridge
    dlistToSeq
    dlistLen
    dlistToSeq_isFinSeq
    dlistToSeq_domain
    dlistToSeq_isFinSeq_domain
    dlistToSeq_seqLength
    dlistLen_in_Omega
    dlistToSeq_apply_last
    dlistToSeq_apply_prev
    -- §5: seqProd correspondence
    dlistToSeq_seqProd
    -- §6: isPrimeSeq
    isPrimeSeq
    dlistToSeq_isPrimeSeq
    -- §7: TFA native
    exists_prime_factorization_native
    unique_prime_factorization_native
  )

end SetUniverse
