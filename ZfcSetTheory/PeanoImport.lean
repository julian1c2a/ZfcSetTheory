import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity
import PeanoNatLib.PeanoNatAxioms

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  This module establishes an isomorphism between the Von Neumann natural numbers
  defined in this project and the Peano natural numbers from the `peanolib` library.
-/

namespace SetUniverse

/-- Converts a Peano natural number to its Von Neumann representation. -/
noncomputable def fromPeano : Peano.ℕ₀ → U
  | Peano.ℕ₀.zero   => (∅ : U)
  | Peano.ℕ₀.succ n' => successor (fromPeano n')

/-- `fromPeano` maps Peano naturals to Von Neumann naturals. -/
theorem fromPeano_is_nat (n : Peano.ℕ₀) : isNat (fromPeano n) := by
  induction n with
  | zero     => exact zero_is_nat
  | succ n' ih => exact nat_successor_is_nat (fromPeano n') ih

/-- `fromPeano` is injective. -/
theorem fromPeano_injective : Function.Injective fromPeano := by
  intro m n h_eq
  induction m generalizing n with
  | zero =>
    cases n with
    | zero   => rfl
    | succ n' =>
      have h1 : fromPeano Peano.ℕ₀.zero = (∅ : U) := rfl
      have h2 : fromPeano (Peano.ℕ₀.succ n') = successor (fromPeano n') := rfl
      rw [h1, h2] at h_eq
      exact absurd h_eq.symm (successor_nonempty (fromPeano n'))
  | succ m' ih =>
    cases n with
    | zero =>
      have h1 : fromPeano (Peano.ℕ₀.succ m') = successor (fromPeano m') := rfl
      have h2 : fromPeano Peano.ℕ₀.zero = (∅ : U) := rfl
      rw [h1, h2] at h_eq
      exact absurd h_eq (successor_nonempty (fromPeano m'))
    | succ n' =>
      have h1 : fromPeano (Peano.ℕ₀.succ m') = successor (fromPeano m') := rfl
      have h2 : fromPeano (Peano.ℕ₀.succ n') = successor (fromPeano n') := rfl
      rw [h1, h2] at h_eq
      congr 1
      exact ih n' (successor_injective h_eq)

/-- Every Von Neumann natural is in the image of `fromPeano`. -/
theorem fromPeano_surjective (n : U) (hn : isNat n) : ∃ p : Peano.ℕ₀, fromPeano p = n := by
  -- S = { m ∈ ω | ∃ p : ℕ₀, fromPeano p = m }
  let S := SpecSet ω (fun m => ∃ p : Peano.ℕ₀, fromPeano p = m)
  suffices h : S = ω by
    have hn_in_S : n ∈ S := by rw [h]; exact Nat_in_Omega n hn
    rw [SpecSet_is_specified] at hn_in_S
    exact hn_in_S.2
  apply strong_induction_principle S (fun z hz => by rw [SpecSet_is_specified] at hz; exact hz.1)
  intro m hm ih
  rw [SpecSet_is_specified]
  refine ⟨hm, ?_⟩
  rcases nat_is_zero_or_succ m (mem_Omega_is_Nat m hm) with rfl | ⟨k, rfl⟩
  · -- m = ∅: fromPeano ℕ₀.zero = ∅
    exact ⟨Peano.ℕ₀.zero, rfl⟩
  · -- m = successor k: use IH on k ∈ m
    have hk_in_S : k ∈ S := ih k (mem_successor_self k)
    rw [SpecSet_is_specified] at hk_in_S
    obtain ⟨p, hp⟩ := hk_in_S.2
    -- fromPeano (ℕ₀.succ p) = successor (fromPeano p) = successor k
    exact ⟨Peano.ℕ₀.succ p,
      show successor (fromPeano p) = successor k from by rw [hp]⟩

/-- Converts a Von Neumann natural to its Peano representation (via classical choice). -/
noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ₀ :=
  Classical.choose (fromPeano_surjective n hn)

/-- `fromPeano (toPeano n hn) = n`. -/
theorem fromPeano_toPeano (n : U) (hn : isNat n) : fromPeano (toPeano n hn) = n :=
  Classical.choose_spec (fromPeano_surjective n hn)

/-- `toPeano (fromPeano p) = p`. -/
theorem toPeano_fromPeano (p : Peano.ℕ₀) :
    toPeano (fromPeano p) (fromPeano_is_nat p) = p :=
  fromPeano_injective (fromPeano_toPeano (fromPeano p) (fromPeano_is_nat p))

/-- The equivalence between Von Neumann naturals and Peano naturals. -/
noncomputable def natEquivPeano : {n : U // isNat n} ≃ Peano.ℕ₀ where
  toFun    := fun ⟨n, hn⟩ => toPeano n hn
  invFun   := fun p => ⟨fromPeano p, fromPeano_is_nat p⟩
  left_inv := fun ⟨n, hn⟩ => Subtype.ext (fromPeano_toPeano n hn)
  right_inv := toPeano_fromPeano

end SetUniverse
