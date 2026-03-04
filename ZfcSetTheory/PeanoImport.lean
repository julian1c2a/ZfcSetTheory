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

  universe u
  variable {U : Type u}

  /-- Converts a Peano natural number to its Von Neumann representation. -/
  noncomputable def fromPeano : Peano.ℕ₀ → U
    | Peano.ℕ₀.zero    => (∅ : U)
    | Peano.ℕ₀.succ n' => successor (fromPeano n')

  /-- `fromPeano` maps Peano naturals to Von Neumann naturals. -/
  theorem fromPeano_is_nat (n : Peano.ℕ₀) : isNat (fromPeano (U := U) n) := by
    induction n with
    | zero     => exact zero_is_nat
    | succ n' ih => exact nat_successor_is_nat (fromPeano n') ih

  /-- `fromPeano` is injective. -/
  theorem fromPeano_injective : Function.Injective (fromPeano (U := U)) := by
    -- Function.Injective uses ⦃⦄ strict-implicit binders, so the IH is
    -- ih : ∀ ⦃b⦄, fromPeano m' = fromPeano b → m' = b
    -- Lean infers b from the proof, so use `ih proof` not `ih n' proof`.
    intro m
    induction m with
    | zero =>
      intro n h
      cases n with
      | zero   => rfl
      | succ n' => exact absurd h (Ne.symm (successor_nonempty (fromPeano n')))
    | succ m' ih =>
      intro n h
      cases n with
      | zero => exact absurd h (successor_nonempty (fromPeano m'))
      | succ n' =>
        -- h : fromPeano (succ m') = fromPeano (succ n')
        -- definitionally: successor (fromPeano m') = successor (fromPeano n')
        -- ih : ∀ ⦃b⦄, fromPeano m' = fromPeano b → m' = b
        congr 1
        apply ih
        exact successor_injective (fromPeano m') (fromPeano n')
          (fromPeano_is_nat m') (fromPeano_is_nat n') h

  /-- Every Von Neumann natural is in the image of `fromPeano`. -/
  theorem fromPeano_surjective (n : U) (hn : isNat n) :
      ∃ p : Peano.ℕ₀, fromPeano (U := U) p = n := by
    -- S = { m ∈ ω | ∃ p : ℕ₀, fromPeano p = m }
    let S := SpecSet (ω : U) (fun m => ∃ p : Peano.ℕ₀, fromPeano (U := U) p = m)
    suffices h : S = (ω : U) by
      have hn_in_S : n ∈ S := by rw [h]; exact Nat_in_Omega n hn
      rw [SpecSet_is_specified] at hn_in_S
      exact hn_in_S.2
    apply strong_induction_principle S
      (fun z hz => by rw [SpecSet_is_specified] at hz; exact hz.1)
    intro m hm ih
    rw [SpecSet_is_specified]
    refine ⟨hm, ?_⟩
    rcases nat_is_zero_or_succ m (mem_Omega_is_Nat m hm) with rfl | ⟨k, rfl⟩
    · -- m = ∅ : fromPeano ℕ₀.zero = ∅
      exact ⟨Peano.ℕ₀.zero, rfl⟩
    · -- m = successor k : use IH on k ∈ m
      have hk_in_S : k ∈ S := ih k (mem_successor_self k)
      rw [SpecSet_is_specified] at hk_in_S
      obtain ⟨p, hp⟩ := hk_in_S.2
      -- fromPeano (ℕ₀.succ p) = successor (fromPeano p) = successor k
      exact ⟨Peano.ℕ₀.succ p,
        show successor (fromPeano (U := U) p) = successor k from by rw [hp]⟩

  /-- Converts a Von Neumann natural to its Peano representation (via classical choice). -/
  noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ₀ :=
    Classical.choose (fromPeano_surjective n hn)

  /-- `fromPeano (toPeano n hn) = n`. -/
  theorem fromPeano_toPeano (n : U) (hn : isNat n) :
      fromPeano (U := U) (toPeano n hn) = n :=
    Classical.choose_spec (fromPeano_surjective n hn)

  /-- `toPeano (fromPeano p) = p`. -/
  theorem toPeano_fromPeano (p : Peano.ℕ₀) :
      toPeano (fromPeano (U := U) p) (fromPeano_is_nat p) = p :=
    fromPeano_injective (fromPeano_toPeano (fromPeano (U := U) p) (fromPeano_is_nat p))

  /-- `toPeano` is injective on Von Neumann naturals. -/
  theorem toPeano_injective {m n : U} (hm : isNat m) (hn : isNat n)
      (h : toPeano m hm = toPeano n hn) : m = n := by
    rw [← fromPeano_toPeano m hm, ← fromPeano_toPeano n hn, h]

  /-- `toPeano` is surjective onto Peano naturals. -/
  theorem toPeano_surjective (p : Peano.ℕ₀) :
      ∃ (n : U) (hn : isNat n), toPeano n hn = p :=
    ⟨fromPeano (U := U) p, fromPeano_is_nat p, toPeano_fromPeano p⟩

end SetUniverse
