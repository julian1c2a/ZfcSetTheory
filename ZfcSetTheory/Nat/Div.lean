/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Euclidean Division on Von Neumann Natural Numbers

  This module defines Euclidean division (quotient and remainder) on ω (the Von Neumann naturals)
  and proves it is isomorphic to Peano division via the bijection ΠZ/ZΠ defined in PeanoImport.lean.

  ## Strategy

  ### Pattern B (bridge-only, original)
  Since Euclidean division's natural recursion (decrement by `b`) does not fit
  `RecursiveFn` directly, we originally lifted the Peano definition via the isomorphism.

  ### Pattern A (native, added later)
  We also provide native definitions via `RecursiveFn` by "counting up":
    F(∅)   = ⟨∅, ∅⟩
    F(σ n) = step_b(F(n))   where step_b(⟨q, r⟩) = ⟨q, σ r⟩ if σ r < b
                                                    = ⟨σ q, ∅⟩ if σ r ≥ b
  This fits `RecursiveFn` with A = ω×ω, exactly like add/sub/mul/pow use Pattern A.

  For `m, n ∈ ω`:
    `divOf m n := fromPeano (Peano.Div.div (toPeano m _) (toPeano n _))`
    `modOf m n := fromPeano (Peano.Div.mod (toPeano m _) (toPeano n _))`

  The bridge theorems `fromPeano_div` and `fromPeano_mod` show these ZFC operations agree
  with Peano's `Peano.Div.div` and `Peano.Div.mod` under the isomorphism.

  ## Helper: proof irrelevance of toPeano

  Since `IsNat n` is a `Prop`, any two proofs of `IsNat n` yield the same `toPeano n _` result.
  The private theorem `toPeano_proof_irrel` makes this explicit.

  ## Main Results

  - `divMod_eq_Omega`: `n ≠ ∅ → m = mul (divOf m n) n + modOf m n`
  - `mod_lt_divisor_Omega`: `n ≠ ∅ → modOf m n ∈ n`
  - `div_of_lt_Omega`: `m ∈ n → divOf m n = ∅`
  - `mod_of_lt_Omega`: `m ∈ n → modOf m n = m`
  - `div_le_self_Omega`: `n ≠ ∅ → divOf m n ∈ m ∨ divOf m n = m`
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Add
import ZfcSetTheory.Nat.Mul
import ZfcSetTheory.Nat.Sub
import PeanoNatLib.PeanoNatDiv

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
  -- Note: Peano.Import is NOT opened here to avoid ΠZ notation ambiguity.
  -- All Peano.Import exports are available at ZFC level.

  universe u
  variable {U : Type u}

  namespace Nat.Div

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `IsNat n`.
        Since the predicate `fun p => fromPeano p = n` has a unique witness (by injectivity
        of `fromPeano`), any two `Classical.choose` calls return the same result. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : IsNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    /-- `fromPeano Peano.ℕ₀.zero = ∅`. Follows from `toPeano_zero` + `fromPeano_toPeano`. -/
    private theorem fromPeano_zero_is_empty : (fromPeano Peano.ℕ₀.zero : U) = ∅ :=
      (congrArg (fromPeano : Peano.ℕ₀ → U) toPeano_zero.symm).trans
        (fromPeano_toPeano ∅ isNat_zero)

    -- =========================================================================
    -- Section 0: Definitions
    -- =========================================================================

    /-- `divOf m n` is the Euclidean quotient `⌊m / n⌋` in ω, lifted from Peano.
        Returns `∅` if `m ∉ ω` or `n ∉ ω`. When `n = ∅`, returns `∅` (convention). -/
    noncomputable def divOf (m n : U) : U :=
      if hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          fromPeano (Peano.Div.div
            (toPeano m (mem_Omega_is_Nat m hm))
            (toPeano n (mem_Omega_is_Nat n hn)))
        else ∅
      else ∅

    /-- `modOf m n` is the Euclidean remainder `m mod n` in ω, lifted from Peano.
        Returns `∅` if `m ∉ ω` or `n ∉ ω`. When `n = ∅`, returns `∅` (convention). -/
    noncomputable def modOf (m n : U) : U :=
      if hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          fromPeano (Peano.Div.mod
            (toPeano m (mem_Omega_is_Nat m hm))
            (toPeano n (mem_Omega_is_Nat n hn)))
        else ∅
      else ∅

    -- =========================================================================
    -- Section 1: Closure in ω
    -- =========================================================================

    /-- The Euclidean quotient of two naturals is a natural. -/
    theorem divOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divOf m n ∈ ω := by
      simp only [divOf, dif_pos hm, dif_pos hn]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    /-- The Euclidean remainder of two naturals is a natural. -/
    theorem modOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        modOf m n ∈ ω := by
      simp only [modOf, dif_pos hm, dif_pos hn]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- Section 2: Bridge theorems
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with Euclidean division.
        `fromPeano (div p q) = divOf (fromPeano p) (fromPeano q)`. -/
    theorem fromPeano_div (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Div.div p q) : U) =
        divOf (fromPeano p) (fromPeano q) := by
      simp only [divOf,
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · exact ((toPeano_proof_irrel _ (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
      · exact ((toPeano_proof_irrel _ (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat q)))
                  (fromPeano_is_nat q)).trans (toPeano_fromPeano q)).symm

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with Euclidean remainder.
        `fromPeano (mod p q) = modOf (fromPeano p) (fromPeano q)`. -/
    theorem fromPeano_mod (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Div.mod p q) : U) =
        modOf (fromPeano p) (fromPeano q) := by
      simp only [modOf,
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
        dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · exact ((toPeano_proof_irrel _ (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat p)))
                  (fromPeano_is_nat p)).trans (toPeano_fromPeano p)).symm
      · exact ((toPeano_proof_irrel _ (mem_Omega_is_Nat _ (Nat_in_Omega _ (fromPeano_is_nat q)))
                  (fromPeano_is_nat q)).trans (toPeano_fromPeano q)).symm

    -- =========================================================================
    -- Section 3: Algebraic properties lifted from Peano
    -- =========================================================================

    /-- **Euclidean division identity**: `m = divOf m n · n + modOf m n` for `n ≠ ∅`,
        lifted from Peano (`divMod_eq`). -/
    theorem divMod_eq_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_n_neq_zero : n ≠ ∅) :
        m = add (mul (divOf m n) n) (modOf m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_q_neq_zero : q ≠ Peano.ℕ₀.zero := fun heq =>
        h_n_neq_zero ((congrArg (fromPeano : Peano.ℕ₀ → U) heq).trans fromPeano_zero_is_empty)
      -- Peano: p = add (mul (div p q) q) (mod p q)
      have h_peano := Peano.Div.divMod_eq p q h_q_neq_zero
      rw [← fromPeano_div p q, ← fromPeano_mod p q,
          ← fromPeano_mul (Peano.Div.div p q) q,
          ← fromPeano_add (Peano.Mul.mul (Peano.Div.div p q) q) (Peano.Div.mod p q)]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) h_peano

    /-- **Remainder bound**: `modOf m n ∈ n` (strict) for `n ≠ ∅`,
        lifted from Peano (`mod_lt_divisor`). -/
    theorem mod_lt_divisor_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_n_neq_zero : n ≠ ∅) :
        modOf m n ∈ n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_q_neq_zero : q ≠ Peano.ℕ₀.zero := fun heq =>
        h_n_neq_zero ((congrArg (fromPeano : Peano.ℕ₀ → U) heq).trans fromPeano_zero_is_empty)
      rw [← fromPeano_mod p q]
      exact (fromPeano_lt_iff (Peano.Div.mod p q) q).mp
              (Peano.Div.mod_lt_divisor p q h_q_neq_zero)

    /-- **Quotient of lesser**: `m ∈ n → divOf m n = ∅` (when dividend < divisor, quotient is 0),
        lifted from Peano (`div_of_lt`). -/
    theorem div_of_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_lt : m ∈ n) :
        divOf m n = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_lt_peano : Peano.StrictOrder.Lt p q := (fromPeano_lt_iff p q).mpr h_lt
      rw [← fromPeano_div p q]
      exact (congrArg (fromPeano : Peano.ℕ₀ → U)
               (Peano.Div.div_of_lt p q h_lt_peano)).trans fromPeano_zero_is_empty

    /-- **Zero Dividend Quotient**: `divOf ∅ a = ∅` natively in ZFC, matching Peano rules. -/
    theorem divOf_zero_Omega (a : U) (ha : a ∈ (ω:U)) : divOf (∅:U) a = ∅ := by
      have h_p : (∅ : U) = fromPeano 𝟘 := rfl
      have hna : IsNat a := mem_Omega_is_Nat a ha
      have ha_p : a = fromPeano (toPeano a hna) := by
        exact (fromPeano_toPeano a hna).symm
      have h_div : fromPeano ((𝟘 / toPeano a hna) : ℕ₀) = divOf (fromPeano 𝟘 : U) (fromPeano (toPeano a hna)) := by
        exact fromPeano_div 𝟘 (toPeano a hna)
      rw [← ha_p] at h_div
      have h_p_eq : (fromPeano 𝟘 : U) = (∅:U) := rfl
      rw [h_p_eq] at h_div
      rw [← h_div]
      let q := toPeano a hna
      have h_cases : q = 𝟘 ∨ q ≠ 𝟘 := by exact Classical.em (q = 𝟘)
      cases h_cases with
      | inl hq =>
        have hq_typed : toPeano a hna = 𝟘 := hq
        rw [hq_typed]
        have h0 : ((𝟘 / 𝟘) : ℕ₀) = 𝟘 := by
          unfold Peano.Div.div
          rw [Peano.Div.divMod]
          rw [dif_pos rfl]
        rw [h0]
        rfl
      | inr hq =>
        have h_p_q : toPeano a hna = q := rfl
        rw [h_p_q]
        have h_lt : Lt 𝟘 q := lt_0_n q hq
        have h0 : ((𝟘 / q) : ℕ₀) = 𝟘 := div_of_lt 𝟘 q h_lt
        rw [h0]
        rfl

    /-- **Remainder of lesser**: `m ∈ n → modOf m n = m` (when dividend < divisor, remainder is dividend),
        lifted from Peano (`mod_of_lt`). -/
    theorem mod_of_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_lt : m ∈ n) :
        modOf m n = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_lt_peano : Peano.StrictOrder.Lt p q := (fromPeano_lt_iff p q).mpr h_lt
      rw [← fromPeano_mod p q]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Div.mod_of_lt p q h_lt_peano)

    /-- **Quotient does not exceed dividend**: `n ≠ ∅ → divOf m n ∈ m ∨ divOf m n = m`,
        lifted from Peano (`div_le_self`). This expresses `divOf m n ≤ m` in ZFC membership order. -/
    theorem div_le_self_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_n_neq_zero : n ≠ ∅) :
        divOf m n ∈ m ∨ divOf m n = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_q_neq_zero : q ≠ Peano.ℕ₀.zero := fun heq =>
        h_n_neq_zero ((congrArg (fromPeano : Peano.ℕ₀ → U) heq).trans fromPeano_zero_is_empty)
      rw [← fromPeano_div p q]
      exact (fromPeano_le_iff (Peano.Div.div p q) p).mp
              (Peano.Div.div_le_self p q h_q_neq_zero)

    -- =========================================================================
    -- Section 4: Native divmod step function (Pattern A)
    -- =========================================================================

    /-- The step function for native Euclidean divmod recursion.
        Maps ⟨q, r⟩ ∈ ω×ω to:
          - ⟨q, σ r⟩  if σ r ∈ b  (i.e. σ r < b: increment remainder)
          - ⟨σ q, ∅⟩  if σ r ∉ b  (i.e. σ r ≥ b: increment quotient, reset remainder)

        This encodes "counting up" from 0 to m: at each step we decide
        whether the remainder has room to grow (< b) or wraps around. -/
    noncomputable def divModStepFn (b : U) : U :=
      sep ((ω ×ₛ ω) ×ₛ (ω ×ₛ ω)) (fun p =>
        ∃ q r : U, q ∈ (ω : U) ∧ r ∈ (ω : U) ∧
          p = ⟨⟨q, r⟩, if σ r ∈ b then ⟨q, σ r⟩ else ⟨σ q, ∅⟩⟩)

    /-- For q, r ∈ ω, the pair ⟨⟨q,r⟩, output⟩ belongs to `divModStepFn b`. -/
    private theorem mem_divModStepFn (b q r : U) (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) :
        (⟨⟨q, r⟩, if σ r ∈ b then ⟨q, σ r⟩ else ⟨σ q, ∅⟩⟩ : U) ∈ (divModStepFn b : U) := by
      unfold divModStepFn
      rw [mem_sep_iff]
      constructor
      · -- membership in (ω×ω) × (ω×ω)
        apply (OrderedPair_mem_CartesianProduct _ _ (ω ×ₛ ω) (ω ×ₛ ω)).mpr
        constructor
        · exact (OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩
        · split
          · exact (OrderedPair_mem_CartesianProduct q (σ r) ω ω).mpr
              ⟨hq, succ_in_Omega r hr⟩
          · exact (OrderedPair_mem_CartesianProduct (σ q) ∅ ω ω).mpr
              ⟨succ_in_Omega q hq, zero_in_Omega⟩
      · exact ⟨q, r, hq, hr, rfl⟩

    /-- `divModStepFn b` is a function from ω×ω to ω×ω. -/
    theorem divModStepFn_is_function (b : U) :
        IsFunction (divModStepFn b : U) (ω ×ₛ ω) (ω ×ₛ ω) := by
      constructor
      · -- graph ⊆ (ω×ω) × (ω×ω)
        intro p hp
        unfold divModStepFn at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · -- for every x ∈ ω×ω, ∃! y, ⟨x,y⟩ ∈ divModStepFn b
        intro x hx
        have hx_cp := (CartesianProduct_is_specified ω ω x).mp hx
        obtain ⟨⟨a₀, b₀, hx_eq⟩, hfst_in, hsnd_in⟩ := hx_cp
        subst hx_eq
        simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hfst_in hsnd_in
        exact ⟨if σ b₀ ∈ b then ⟨ a₀ , σ b₀ ⟩ else ⟨ σ a₀ , ∅ ⟩,
               mem_divModStepFn b a₀ b₀ hfst_in hsnd_in,
               fun y hy => by
                 dsimp only at hy
                 unfold divModStepFn at hy
                 rw [mem_sep_iff] at hy
                 obtain ⟨_, q', r', _, _, heq⟩ := hy
                 have hproj := Eq_of_OrderedPairs_given_projections
                   ⟨ a₀ , b₀ ⟩ y ⟨ q' , r' ⟩
                   (if σ r' ∈ b then ⟨ q' , σ r' ⟩ else ⟨ σ q' , ∅ ⟩) heq
                 have hqr := Eq_of_OrderedPairs_given_projections a₀ b₀ q' r' hproj.1
                 rw [hqr.1, hqr.2]
                 exact hproj.2⟩

    /-- Applying `divModStepFn b` to ⟨q,r⟩ ∈ ω×ω gives the expected output. -/
    theorem divModStepFn_apply (b q r : U) (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) :
        apply (divModStepFn b : U) ⟨q, r⟩ =
          if σ r ∈ b then ⟨q, σ r⟩ else ⟨σ q, ∅⟩ :=
      apply_eq (divModStepFn b) ⟨q, r⟩ _
        ((divModStepFn_is_function b).2 ⟨q, r⟩
          ((OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩))
        (mem_divModStepFn b q r hq hr)

    -- =========================================================================
    -- Section 5: Native Euclidean division and modulus
    -- =========================================================================

    /-- `⟨∅, ∅⟩ ∈ ω ×ₛ ω` — the zero pair is in the Cartesian product. -/
    private theorem zero_pair_in_OmegaProd :
        (⟨∅, ∅⟩ : U) ∈ ((ω : U) ×ₛ ω) :=
      (OrderedPair_mem_CartesianProduct ∅ ∅ ω ω).mpr ⟨zero_in_Omega, zero_in_Omega⟩

    /-- `divModRecFn b hb` is the ZFC function ω → ω×ω computing (div · b, mod · b)
        via the Recursion Theorem. For n ∈ ω:
          F(∅)   = ⟨∅, ∅⟩
          F(σ n) = divModStepFn b (F(n)) -/
    noncomputable def divModRecFn (b : U) (_hb : b ∈ (ω : U)) : U :=
      RecursiveFn (ω ×ₛ ω) (⟨ ∅ , ∅ ⟩ : U) (divModStepFn b)
        zero_pair_in_OmegaProd (divModStepFn_is_function b)

    /-- `divModRecFn b hb` is a function from ω to ω×ω. -/
    theorem divModRecFn_is_function (b : U) (hb : b ∈ (ω : U)) :
        IsFunction (divModRecFn b hb) ω (ω ×ₛ ω) :=
      RecursiveFn_is_function (ω ×ₛ ω) (⟨ ∅ , ∅ ⟩ : U) (divModStepFn b)
        zero_pair_in_OmegaProd (divModStepFn_is_function b)

    /-- Base case: `divModRecFn b hb` applied to ∅ gives ⟨∅, ∅⟩. -/
    theorem divModRecFn_zero (b : U) (hb : b ∈ (ω : U)) :
        apply (divModRecFn b hb) (∅ : U) = (⟨ ∅ , ∅ ⟩ : U) :=
      RecursiveFn_zero (ω ×ₛ ω) (⟨ ∅ , ∅ ⟩ : U) (divModStepFn b)
        zero_pair_in_OmegaProd (divModStepFn_is_function b)

    /-- Step case: `divModRecFn b hb` applied to σ n gives `step(F(n))`. -/
    theorem divModRecFn_succ (b : U) (hb : b ∈ (ω : U)) (n : U) (hn : n ∈ ω) :
        apply (divModRecFn b hb) (σ n) =
          apply (divModStepFn b) (apply (divModRecFn b hb) n) :=
      RecursiveFn_succ (ω ×ₛ ω) (⟨ ∅ , ∅ ⟩ : U) (divModStepFn b)
        zero_pair_in_OmegaProd (divModStepFn_is_function b) n hn

    /-- The value `apply (divModRecFn b hb) n` is always in ω×ω. -/
    private theorem divModRecFn_value_in_OmegaProd (b n : U) (hb : b ∈ (ω : U))
        (hn : n ∈ (ω : U)) :
        apply (divModRecFn b hb) n ∈ ((ω : U) ×ₛ ω) := by
      have hfn := divModRecFn_is_function b hb
      obtain ⟨y, hy_in, _⟩ := hfn.2 n hn
      have hy_prod := hfn.1 ⟨ n , y ⟩ hy_in
      rw [OrderedPair_mem_CartesianProduct] at hy_prod
      have happly := apply_eq (divModRecFn b hb) n y (hfn.2 n hn) hy_in
      rw [happly]
      exact hy_prod.2

    /-- **Native Euclidean quotient** `div m n` = ⌊m/n⌋ in ω, defined via
        the Recursion Theorem (Pattern A). Returns ∅ for degenerate cases. -/
    noncomputable def div (m n : U) : U :=
      if _hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          if n = ∅ then ∅
          else fst (apply (divModRecFn n hn) m)
        else ∅
      else ∅

    /-- **Native Euclidean remainder** `mod m n` = m mod n in ω, defined via
        the Recursion Theorem (Pattern A). Returns ∅ for degenerate cases. -/
    noncomputable def mod (m n : U) : U :=
      if _hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          if n = ∅ then ∅
          else snd (apply (divModRecFn n hn) m)
        else ∅
      else ∅

    -- =========================================================================
    -- Section 6: Native recursion equations
    -- =========================================================================

    /-- Helper: `apply (divModRecFn b hb) n` is an ordered pair. -/
    private theorem divModRecFn_value_isOP (b n : U) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        isOrderedPair (apply (divModRecFn b hb) n) := by
      have h := divModRecFn_value_in_OmegaProd b n hb hn
      exact (CartesianProduct_is_specified ω ω (apply (divModRecFn b hb) n)).mp h |>.1

    /-- Helper: fst of the recursion value is in ω. -/
    private theorem divModRecFn_fst_in_Omega (b n : U) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        fst (apply (divModRecFn b hb) n) ∈ (ω : U) := by
      have h := divModRecFn_value_in_OmegaProd b n hb hn
      exact (CartesianProduct_is_specified ω ω (apply (divModRecFn b hb) n)).mp h |>.2.1

    /-- Helper: snd of the recursion value is in ω. -/
    private theorem divModRecFn_snd_in_Omega (b n : U) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        snd (apply (divModRecFn b hb) n) ∈ (ω : U) := by
      have h := divModRecFn_value_in_OmegaProd b n hb hn
      exact (CartesianProduct_is_specified ω ω (apply (divModRecFn b hb) n)).mp h |>.2.2

    /-- `div ∅ n = ∅` for all `n ∈ ω`, `n ≠ ∅`. -/
    theorem div_zero (n : U) (hn : n ∈ (ω : U)) (hn0 : n ≠ ∅) :
        div ∅ n = ∅ := by
      simp only [div, dif_pos zero_in_Omega, dif_pos hn, if_neg hn0]
      rw [divModRecFn_zero n hn, fst_of_ordered_pair]

    /-- `mod ∅ n = ∅` for all `n ∈ ω`, `n ≠ ∅`. -/
    theorem mod_zero (n : U) (hn : n ∈ (ω : U)) (hn0 : n ≠ ∅) :
        mod ∅ n = ∅ := by
      simp only [mod, dif_pos zero_in_Omega, dif_pos hn, if_neg hn0]
      rw [divModRecFn_zero n hn, snd_of_ordered_pair]

    /-- Native step equation for the divmod pair:
        `apply (divModRecFn b) (σ m)` is determined by `apply (divModRecFn b) m`. -/
    theorem divModRecFn_succ_explicit (b m : U) (hb : b ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        apply (divModRecFn b hb) (σ m) =
          (if σ (snd (apply (divModRecFn b hb) m)) ∈ b then
             ⟨ fst (apply (divModRecFn b hb) m) , σ (snd (apply (divModRecFn b hb) m)) ⟩
           else
             ⟨ σ (fst (apply (divModRecFn b hb) m)) , ∅ ⟩) := by
      rw [divModRecFn_succ b hb m hm]
      have hv_op := divModRecFn_value_isOP b m hb hm
      have hv_eq := OrderedPairSet_is_WellConstructed _ hv_op
      -- Rewrite the argument of divModStepFn
      have h := divModStepFn_apply b
        (fst (apply (divModRecFn b hb) m))
        (snd (apply (divModRecFn b hb) m))
        (divModRecFn_fst_in_Omega b m hb hm)
        (divModRecFn_snd_in_Omega b m hb hm)
      rw [← hv_eq] at h
      exact h

    /-- div step: when remainder has room (σ r < b), quotient stays. -/
    theorem div_succ_lt (b m : U) (hb : b ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hb0 : b ≠ ∅)
        (h_lt : σ (mod m b) ∈ b) :
        div (σ m) b = div m b := by
      simp only [div, dif_pos (succ_in_Omega m hm), dif_pos hb, if_neg hb0,
                 dif_pos hm]
      rw [divModRecFn_succ_explicit b m hb hm]
      simp only [mod, dif_pos hm, dif_pos hb, if_neg hb0] at h_lt
      simp only [if_pos h_lt, fst_of_ordered_pair]

    /-- div step: when remainder wraps (σ r = b), quotient increments. -/
    theorem div_succ_ge (b m : U) (hb : b ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hb0 : b ≠ ∅)
        (h_nlt : ¬ (σ (mod m b) ∈ b)) :
        div (σ m) b = σ (div m b) := by
      simp only [div, dif_pos (succ_in_Omega m hm), dif_pos hb, if_neg hb0,
                 dif_pos hm]
      rw [divModRecFn_succ_explicit b m hb hm]
      simp only [mod, dif_pos hm, dif_pos hb, if_neg hb0] at h_nlt
      simp only [if_neg h_nlt, fst_of_ordered_pair]

    /-- mod step: when remainder has room (σ r < b), remainder increments. -/
    theorem mod_succ_lt (b m : U) (hb : b ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hb0 : b ≠ ∅)
        (h_lt : σ (mod m b) ∈ b) :
        mod (σ m) b = σ (mod m b) := by
      simp only [mod, dif_pos (succ_in_Omega m hm), dif_pos hb, if_neg hb0,
                 dif_pos hm]
      rw [divModRecFn_succ_explicit b m hb hm]
      simp only [mod, dif_pos hm, dif_pos hb, if_neg hb0] at h_lt
      simp only [if_pos h_lt, snd_of_ordered_pair]

    /-- mod step: when remainder wraps (σ r ≥ b), remainder resets to 0. -/
    theorem mod_succ_ge (b m : U) (hb : b ∈ (ω : U)) (hm : m ∈ (ω : U))
        (hb0 : b ≠ ∅)
        (h_nlt : ¬ (σ (mod m b) ∈ b)) :
        mod (σ m) b = ∅ := by
      simp only [mod, dif_pos (succ_in_Omega m hm), dif_pos hb, if_neg hb0]
      rw [divModRecFn_succ_explicit b m hb hm]
      simp only [mod, dif_pos hm, dif_pos hb, if_neg hb0] at h_nlt
      simp only [if_neg h_nlt, snd_of_ordered_pair]

    -- =========================================================================
    -- Section 7: Native closure in ω
    -- =========================================================================

    /-- Native div is in ω. -/
    theorem div_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        div m n ∈ ω := by
      by_cases hn0 : n = ∅
      · simp only [div, dif_pos hm, dif_pos hn, if_pos hn0]; exact zero_in_Omega
      · simp only [div, dif_pos hm, dif_pos hn, if_neg hn0]
        exact divModRecFn_fst_in_Omega n m hn hm

    /-- Native mod is in ω. -/
    theorem mod_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mod m n ∈ ω := by
      by_cases hn0 : n = ∅
      · simp only [mod, dif_pos hm, dif_pos hn, if_pos hn0]; exact zero_in_Omega
      · simp only [mod, dif_pos hm, dif_pos hn, if_neg hn0]
        exact divModRecFn_snd_in_Omega n m hn hm

    -- =========================================================================
    -- Section 8: Native algebraic properties
    -- =========================================================================

    /-- Helper: if `r ∈ n` and `¬ (σ r ∈ n)` with both in ω, then `σ r = n`.
        Uses trichotomy + asymmetry of membership on naturals. -/
    private theorem succ_eq_of_not_succ_mem (r n : U) (hr : r ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hr_lt : r ∈ n) (h_nlt : ¬ (σ r ∈ n)) : σ r = n := by
      have hr_nat := mem_Omega_is_Nat r hr
      have hn_nat := mem_Omega_is_Nat n hn
      have hσr_nat := isNat_succ r hr_nat
      rcases trichotomy (σ r) n hσr_nat hn_nat with h | h | h
      · exact absurd h h_nlt
      · exact h
      · rw [mem_succ_iff] at h
        rcases h with h | h
        · exact absurd hr_lt (mem_asymm n r hn_nat hr_nat h)
        · exact absurd (h ▸ hr_lt) (not_mem_self r hr_nat)

    /-- **Remainder bound (native)**: `mod m n ∈ n` (i.e. mod m n < n) for `n ≠ ∅`.

        Proof by ω-induction on m. -/
    theorem mod_lt_native (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hn0 : n ≠ ∅) :
        mod m n ∈ n := by
      let P := fun k => mod k n ∈ n
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have := hS ▸ hm; rw [mem_sep_iff] at this; exact this.2
      apply induction_principle S
      · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
      · rw [mem_sep_iff]
        exact ⟨zero_in_Omega, by
          simp only [P]; rw [mod_zero n hn hn0]
          exact zero_mem_of_nat_nonempty n (mem_Omega_is_Nat n hn) hn0⟩
      · intro k hk_S
        rw [mem_sep_iff] at hk_S ⊢
        refine ⟨succ_in_Omega k hk_S.1, ?_⟩
        simp only [P]
        by_cases h : σ (mod k n) ∈ n
        · rw [mod_succ_lt n k hn hk_S.1 hn0 h]; exact h
        · rw [mod_succ_ge n k hn hk_S.1 hn0 h]
          exact zero_mem_of_nat_nonempty n (mem_Omega_is_Nat n hn) hn0

    /-- **Euclidean division identity (native)**:
        `m = add (mul (div m n) n) (mod m n)` for `n ≠ ∅`.

        Proof by ω-induction on m. At each step:
        - If σ (mod m n) < n: σ m = div(m,n)·n + σ(mod(m,n)) ✓
        - If σ (mod m n) = n: σ m = σ(div(m,n))·n + 0        ✓ -/
    theorem divMod_eq_native (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hn0 : n ≠ ∅) :
        m = add (mul (div m n) n) (mod m n) := by
      let P := fun k => k = add (mul (div k n) n) (mod k n)
      let S := sep (ω : U) P
      suffices hS : S = ω by
        have := hS ▸ hm; rw [mem_sep_iff] at this; exact this.2
      apply induction_principle S
      · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
      · -- Base: ∅ = add (mul (div ∅ n) n) (mod ∅ n)
        rw [mem_sep_iff]
        refine ⟨zero_in_Omega, ?_⟩
        simp only [P]
        rw [div_zero n hn hn0, mod_zero n hn hn0,
            zero_mul_Omega n hn, add_zero ∅ zero_in_Omega]
      · -- Step: k ∈ S → σ k ∈ S
        intro k hk_S
        rw [mem_sep_iff] at hk_S ⊢
        have hk := hk_S.1
        have ih : k = add (mul (div k n) n) (mod k n) := hk_S.2
        refine ⟨succ_in_Omega k hk, ?_⟩
        simp only [P]
        have hq := div_in_Omega k n hk hn
        have hr := mod_in_Omega k n hk hn
        have hmq := mul_in_Omega (div k n) n hq hn
        by_cases h : σ (mod k n) ∈ n
        · -- Case: σ (mod k n) < n — quotient stays, remainder increments
          rw [div_succ_lt n k hn hk hn0 h, mod_succ_lt n k hn hk hn0 h]
          rw [add_succ (mul (div k n) n) (mod k n) hmq hr]
          exact congrArg succ ih
        · -- Case: ¬ (σ (mod k n) < n) — quotient increments, remainder resets
          rw [div_succ_ge n k hn hk hn0 h, mod_succ_ge n k hn hk hn0 h]
          have hr_lt := mod_lt_native k n hk hn hn0
          have hσr_eq := succ_eq_of_not_succ_mem (mod k n) n hr hn hr_lt h
          rw [add_zero (mul (σ (div k n)) n)
                (mul_in_Omega (σ (div k n)) n (succ_in_Omega _ hq) hn),
              succ_mul_Omega (div k n) n hq hn]
          -- Goal: σ k = add (mul (div k n) n) n
          calc σ k
              = succ (add (mul (div k n) n) (mod k n)) := congrArg succ ih
            _ = add (mul (div k n) n) (σ (mod k n)) :=
                (add_succ (mul (div k n) n) (mod k n) hmq hr).symm
            _ = add (mul (div k n) n) n := by rw [hσr_eq]

    -- =========================================================================
    -- Section 9: Note on bridge equivalence
    -- =========================================================================

    -- The bridge theorems `div_eq_divOf` and `mod_eq_modOf` (showing that
    -- Nat.Div.div = Nat.Arith.div = divOf, etc.) are proved in Nat.Arith
    -- via Euclidean division uniqueness (`euclid_unique_ZFC`).

  end Nat.Div

  export Nat.Div (
    -- Section 0: bridge definitions
    divOf
    modOf
    -- Section 1: bridge closure
    divOf_in_Omega
    modOf_in_Omega
    -- Section 2: bridge theorems
    fromPeano_div
    fromPeano_mod
    -- Section 3: bridge algebraic properties
    divMod_eq_Omega
    mod_lt_divisor_Omega
    div_of_lt_Omega
    divOf_zero_Omega
    mod_of_lt_Omega
    div_le_self_Omega
    -- Section 4: native step function
    divModStepFn
    divModStepFn_is_function
    divModStepFn_apply
    -- Section 5: native recursive function
    divModRecFn
    divModRecFn_is_function
    divModRecFn_zero
    divModRecFn_succ
    -- Section 6: native recursion equations (via Nat.Div.div / Nat.Div.mod)
    divModRecFn_succ_explicit
    -- Section 8: native algebraic properties (via Nat.Div.div / Nat.Div.mod)
    divMod_eq_native
    mod_lt_native
  )

end ZFC
