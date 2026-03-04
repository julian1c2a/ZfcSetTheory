import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity
import PeanoNatLib.PeanoNatAxioms

/--
Copyright (c) 2026. All rights reserved.
Author: Your Name
License: MIT
-/

namespace SetUniverse

/--
This module establishes an isomorphism between the Von Neumann natural numbers
defined in this project and the Peano natural numbers from the `peanolib` library.
-/

/-- Converts a Peano natural number to its Von Neumann representation. -/
noncomputable def fromPeano : Peano.ℕ → U
| Peano.ℕ.zero => (zero : U)
| Peano.ℕ.succ n' => successor (fromPeano n')

/-- Converts a Von Neumann natural number to its Peano representation.
    This function is defined by well-founded recursion on the `∈` relation. -/
noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ :=
  if h : n = zero then
    Peano.ℕ.zero
  else
    have : isNat (predecessor n) := predecessor_is_nat n hn h
    have : predecessor n ∈ n := predecessor_mem n hn h
    Peano.ℕ.succ (toPeano (predecessor n) (predecessor_is_nat n hn h))
termination_by n hn => n

/-- A property relating `fromPeano` to natural numbers, for use in proofs. -/
theorem fromPeano_is_nat (n : Peano.ℕ) : isNat (fromPeano n) := by
  induction n with
  | zero => exact zero_is_nat
  | succ n' ih => exact nat_successor_is_nat (fromPeano n') ih

/-- `fromPeano` and `toPeano` are inverses of each other (Peano to Von Neumann and back). -/
theorem fromPeano_toPeano (n : Peano.ℕ) : toPeano (fromPeano n) (fromPeano_is_nat n) = n := by
  induction n with
  | zero =>
    simp [fromPeano, toPeano]
  | succ n' ih =>
    let vn' := fromPeano n'
    let h_vn'_nat := fromPeano_is_nat n'
    let vn_succ := successor vn'
    have h_vn_succ_nat : isNat vn_succ := nat_successor_is_nat vn' h_vn'_nat
    have h_ne_zero : vn_succ ≠ zero := by
      intro h_eq
      have : vn' ∈ vn_succ := mem_successor_self vn'
      rw [h_eq] at this
      exact EmptySet_is_empty vn' this
    simp [fromPeano, toPeano, h_ne_zero, predecessor_of_successor h_vn'_nat, ih]

/-- `toPeano` and `fromPeano` are inverses of each other (Von Neumann to Peano and back). -/
theorem toPeano_fromPeano (n : U) (hn : isNat n) : fromPeano (toPeano n hn) = n := by
  refine Peano_induction (fun k => isNat k → fromPeano (toPeano k (by assumption)) = k) ?h_zero ?h_succ n hn
  · -- Base case: n = 0
    intro hn_zero
    simp [toPeano, fromPeano, hn_zero]
  · -- Inductive step
    intro k hk_nat ih
    intro h_succ_k_nat
    -- We need to prove `fromPeano (toPeano (σ k) h_succ_k_nat) = σ k`
    -- The induction hypothesis `ih` is `isNat k → fromPeano (toPeano k (by assumption)) = k`
    have h_ne_zero : σ k ≠ zero := by
      intro h_eq
      have : k ∈ σ k := mem_successor_self k
      rw [h_eq] at this
      exact EmptySet_is_empty k this
    simp [toPeano, fromPeano, h_ne_zero, predecessor_of_successor hk_nat]
    -- The goal is now `successor (fromPeano (toPeano k hk_nat)) = successor k`
    -- We can rewrite the inner part using the induction hypothesis
    rw [ih hk_nat]

/-- The equivalence between Von Neumann naturals (`isNat`) and Peano naturals (`Peano.ℕ`). -/
noncomputable def natEquivPeano : {n : U // isNat n} ≃ Peano.ℕ where
  toFun := fun n => toPeano n.val n.property
  invFun := fun pn => ⟨fromPeano pn, fromPeano_is_nat pn⟩
  left_inv := fun ⟨n, hn⟩ => by
    simp
    exact toPeano_fromPeano n hn
  right_inv := fun n => by
    simp
    exact fromPeano_toPeano n

end SetUniverse
