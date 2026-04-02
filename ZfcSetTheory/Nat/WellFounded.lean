/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Well-Foundedness and Well-Ordering Principle on Von Neumann Natural Numbers

  This module lifts the well-foundedness and well-ordering principle from the
  Peano formalization to von Neumann naturals ω.

  ## Strategy (Pattern B: bridge-only)

  The ZFC side already has `nat_mem_wf` (well-foundedness of membership on ω)
  proved directly. This module adds:

  1. A bridge connecting Peano's `well_founded_lt` to ZFC's `nat_mem_wf`.
  2. The well-ordering principle for arbitrary predicates on ω.

  ## Main Results

  - `well_founded_lt_Omega`:       membership on ω is well-founded (via Peano)
  - `well_ordering_Omega`:         every nonempty subset of ω has a unique minimum
  - `well_ordering_Omega_exists`:  simplified form without uniqueness
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Peano.Import
import PeanoNatLib.PeanoNatWellFounded

namespace ZFC
  open Classical

  universe u
  variable {U : Type u}

  namespace Nat.WellFounded

    -- =========================================================================
    -- §0  Well-foundedness via Peano bridge
    -- =========================================================================

    /-- Peano's accessibility lifted to ZFC: every `n ∈ ω` is accessible under
        the membership relation restricted to ω. -/
    theorem acc_lt_Omega (n : U) (_hn : n ∈ (ω : U)) :
        Acc (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b) n :=
      nat_mem_wf.apply n

    -- =========================================================================
    -- §1  Well-ordering principle
    -- =========================================================================

    /-- **Well-ordering principle for ω**: given a predicate `P` on `U` and
        evidence that some `k ∈ ω` satisfies `P k`, there exists a unique
        minimum `n ∈ ω` with `P n` and `∀ m ∈ ω, P m → n ≼ m`. -/
    theorem well_ordering_Omega (P : U → Prop)
        (h_nonempty : ∃ k : U, k ∈ (ω : U) ∧ P k) :
        ∃ n : U, n ∈ (ω : U) ∧ P n ∧
          (∀ m : U, m ∈ (ω : U) → P m → (n ∈ m ∨ n = m)) ∧
          (∀ n' : U, n' ∈ (ω : U) → P n' →
            (∀ m : U, m ∈ (ω : U) → P m → (n' ∈ m ∨ n' = m)) → n' = n) := by
      -- Lift the predicate to Peano:
      let Q : Peano.ℕ₀ → Prop := fun p => P (fromPeano p)
      -- Get a Peano witness from the ZFC one:
      obtain ⟨k, hk_mem, hPk⟩ := h_nonempty
      obtain ⟨pk, hpk⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk_mem)
      subst hpk
      have hQ_nonempty : ∃ q : Peano.ℕ₀, Q q := ⟨pk, hPk⟩
      -- Apply Peano's well-ordering principle:
      obtain ⟨pn, ⟨hQn, hLeast⟩, hUniq⟩ :=
        Peano.WellFounded.well_ordering_principle Q hQ_nonempty
      -- Transport back to ZFC:
      refine ⟨fromPeano pn, Nat_in_Omega _ (fromPeano_is_nat pn), hQn, ?_, ?_⟩
      · -- Minimality: n ≼ m for all m ∈ ω with P m
        intro m hm hPm
        obtain ⟨pm, hpm⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
        subst hpm
        exact (fromPeano_le_iff pn pm).mp (hLeast pm hPm)
      · -- Uniqueness: any other minimum equals n
        intro n' hn'_mem hPn' hLeast'
        obtain ⟨pn', hpn'⟩ := fromPeano_surjective n' (mem_Omega_is_Nat n' hn'_mem)
        subst hpn'
        have hQn' : Q pn' := hPn'
        have hLeast_pn' : ∀ m : Peano.ℕ₀, Q m → Peano.Order.Le pn' m := by
          intro pm hQpm
          have hpm_mem : (fromPeano pm : U) ∈ ω :=
            Nat_in_Omega _ (fromPeano_is_nat pm)
          exact (fromPeano_le_iff pn' pm).mpr (hLeast' (fromPeano pm) hpm_mem hQpm)
        exact congrArg (fromPeano : Peano.ℕ₀ → U) (hUniq pn' ⟨hQn', hLeast_pn'⟩)

    /-- **Simplified well-ordering**: every nonempty subset of ω has a minimum. -/
    theorem well_ordering_Omega_exists (P : U → Prop)
        (h_nonempty : ∃ k : U, k ∈ (ω : U) ∧ P k) :
        ∃ n : U, n ∈ (ω : U) ∧ P n ∧
          ∀ m : U, m ∈ (ω : U) → P m → (n ∈ m ∨ n = m) := by
      obtain ⟨n, hn_mem, hPn, hLeast, _⟩ := well_ordering_Omega P h_nonempty
      exact ⟨n, hn_mem, hPn, hLeast⟩

  end Nat.WellFounded

  export Nat.WellFounded (
    -- §0: well-foundedness
    acc_lt_Omega
    -- §1: well-ordering principle
    well_ordering_Omega
    well_ordering_Omega_exists
  )

end ZFC
