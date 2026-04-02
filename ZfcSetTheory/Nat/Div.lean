/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Euclidean Division on Von Neumann Natural Numbers

  This module defines Euclidean division (quotient and remainder) on ω (the Von Neumann naturals)
  and proves it is isomorphic to Peano division via the bijection ΠZ/ZΠ defined in PeanoImport.lean.

  ## Strategy (Pattern B: bridge-only)

  Since Euclidean division requires well-founded recursion that does not fit the simple
  `RecursiveFn` pattern (the recursive call decreases by `b` at each step, not by one),
  we lift the Peano definition directly via the isomorphism.

  For `m, n ∈ ω`:
    `divOf m n := fromPeano (Peano.Div.div (toPeano m _) (toPeano n _))`
    `modOf m n := fromPeano (Peano.Div.mod (toPeano m _) (toPeano n _))`

  The bridge theorems `fromPeano_div` and `fromPeano_mod` show these ZFC operations agree
  with Peano's `Peano.Div.div` and `Peano.Div.mod` under the isomorphism.

  ## Helper: proof irrelevance of toPeano

  Since `isNat n` is a `Prop`, any two proofs of `isNat n` yield the same `toPeano n _` result.
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
  open ZFC.ExtensionAxiom
  open ZFC.ExistenceAxiom
  open ZFC.SpecificationAxiom
  open ZFC.PairingAxiom
  open ZFC.UnionAxiom
  open ZFC.PowerSetAxiom
  open ZFC.OrderedPairExtensions
  open ZFC.CartesianProduct
  open ZFC.Relations
  open ZFC.Functions
  open ZFC.Cardinality
  open ZFC.NaturalNumbers
  open ZFC.InfinityAxiom
  -- Note: PeanoIsomorphism is NOT opened here to avoid ΠZ notation ambiguity.
  -- All PeanoIsomorphism exports are available at ZFC level.

  universe u
  variable {U : Type u}

  namespace NaturalNumbersDiv

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- `toPeano n` gives the same value for any two proofs of `isNat n`.
        Since the predicate `fun p => fromPeano p = n` has a unique witness (by injectivity
        of `fromPeano`), any two `Classical.choose` calls return the same result. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : isNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    /-- `fromPeano Peano.ℕ₀.zero = ∅`. Follows from `toPeano_zero` + `fromPeano_toPeano`. -/
    private theorem fromPeano_zero_is_empty : (fromPeano Peano.ℕ₀.zero : U) = ∅ :=
      (congrArg (fromPeano : Peano.ℕ₀ → U) toPeano_zero.symm).trans
        (fromPeano_toPeano ∅ zero_is_nat)

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

  end NaturalNumbersDiv

  export NaturalNumbersDiv (
    -- Section 0: definitions
    divOf
    modOf
    -- Section 1: closure
    divOf_in_Omega
    modOf_in_Omega
    -- Section 2: bridge theorems
    fromPeano_div
    fromPeano_mod
    -- Section 3: algebraic properties
    divMod_eq_Omega
    mod_lt_divisor_Omega
    div_of_lt_Omega
    mod_of_lt_Omega
    div_le_self_Omega
  )

end ZFC
