/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Finite Boolean Algebra Cardinality

This module proves that the cardinality of every finite Boolean algebra
(realized as 𝒫(A) in our set-theoretic framework) is a power of 2.
The key theorems connect finiteness, atoms, and 2^n cardinality.

The proof proceeds through two independent paths:
1. **Direct path**: A ≃ₛ n → 𝒫(A) ≃ₛ 2^n (via `powerset_cardinality`)
2. **Atoms path**: Atoms(A) ≃ₛ n → 𝒫(A) ≃ₛ 𝒫(Atoms A) ≃ₛ 2^n
   (via `representation_equipotent` + `powerset_cardinality`)

## Main Theorems

* `atoms_equipotent_base`       — Atoms(A) ≃ₛ A
* `finite_atoms_of_finite`      — A finite → Atoms(A) finite
* `finite_of_finite_atoms`      — Atoms(A) finite → A finite
* `BA_cardinality_via_atoms`    — Atoms(A) ≃ₛ n → 𝒫(A) ≃ₛ 2^n (representation path)
* `finite_powerset_is_finite`   — A finite → 𝒫(A) finite
* `finite_BA_cardinality`       — A finite → ∃ n ∈ ω, 𝒫(A) ≃ₛ 2^n
* `finite_BA_cardinality_atoms` — A finite → ∃ n ∈ ω, Atoms(A) ≃ₛ n ∧ 𝒫(A) ≃ₛ 2^n
* `finite_complete_atomic_BA`   — A finite → 𝒫(A) is a complete atomic BA with card 2^n

## References

* Every finite Boolean algebra has 2^n elements for some n ∈ ω
-/

import ZFC.Cardinal.FinitePowerSet
import ZFC.BoolAlg.Representation

namespace ZFC
  open Classical
  open ZFC.Axiom.Infinity
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.Functions
  open ZFC.SetOps.FiniteSets
  open ZFC.Cardinal.Basic
  open ZFC.Cardinal.FinitePowerSet
  open ZFC.Nat.Basic
  open ZFC.Nat.Pow
  open ZFC.BoolAlg.Atomic
  open ZFC.BoolAlg.Complete
  open ZFC.BoolAlg.Representation

  universe u
  variable {U : Type u}

  namespace BoolAlg.FiniteBA

    /-! ============================================================ -/
    /-! ### SECTION 1: ATOMS AND FINITENESS                        ### -/
    /-! ============================================================ -/

    /-- Atoms(A) ≃ₛ A (reverse of A_equipotent_Atoms). -/
    theorem atoms_equipotent_base (A : U) : Atoms A ≃ₛ A :=
      equipotent_symm (A_equipotent_Atoms A)

    /-- If A is finite, then Atoms(A) is finite. -/
    theorem finite_atoms_of_finite {A : U} (hA : isFiniteSet A) :
        isFiniteSet (Atoms A) :=
      finite_equipotent hA (A_equipotent_Atoms A)

    /-- If Atoms(A) is finite, then A is finite. -/
    theorem finite_of_finite_atoms {A : U} (hAt : isFiniteSet (Atoms A)) :
        isFiniteSet A :=
      finite_equipotent hAt (atoms_equipotent_base A)

    /-! ============================================================ -/
    /-! ### SECTION 2: CARDINALITY VIA ATOMS (REPRESENTATION PATH) ### -/
    /-! ============================================================ -/

    /-- If Atoms(A) ≃ₛ n (n ∈ ω), then 𝒫(A) ≃ₛ 2^n.
        This proof goes through the representation theorem:
        𝒫(A) ≃ₛ 𝒫(Atoms A) ≃ₛ 2^n. -/
    theorem BA_cardinality_via_atoms {A n : U} (hn : n ∈ ω)
        (hAtoms : Atoms A ≃ₛ n) :
        𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n :=
      equipotent_trans (representation_equipotent A)
        (powerset_cardinality hn hAtoms)

    /-! ============================================================ -/
    /-! ### SECTION 3: FINITE BOOLEAN ALGEBRA HAS CARDINALITY 2^n  ### -/
    /-! ============================================================ -/

    /-- If A is finite, then 𝒫(A) is finite. -/
    theorem finite_powerset_is_finite {A : U} (hA : isFiniteSet A) :
        isFiniteSet (𝒫 A) := by
      obtain ⟨n, hn, hAn⟩ := hA
      have h1 : σ (∅ : U) ∈ ω := succ_in_Omega (∅ : U) zero_in_Omega
      have h2 : σ (σ (∅ : U)) ∈ ω := succ_in_Omega (σ (∅ : U)) h1
      exact ⟨pow (σ (σ (∅ : U))) n,
             pow_in_Omega (σ (σ (∅ : U))) n h2 hn,
             powerset_cardinality hn hAn⟩

    /-- **Main theorem**: Every finite Boolean algebra 𝒫(A) has cardinality
        2^n for some n ∈ ω. -/
    theorem finite_BA_cardinality {A : U} (hA : isFiniteSet A) :
        ∃ n, n ∈ ω ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n := by
      obtain ⟨n, hn, hAn⟩ := hA
      exact ⟨n, hn, powerset_cardinality hn hAn⟩

    /-- Every finite Boolean algebra 𝒫(A) has cardinality 2^n where n is
        the number of atoms. This gives the full characterization connecting
        the Boolean algebra structure (atoms) to the cardinality. -/
    theorem finite_BA_cardinality_atoms {A : U} (hA : isFiniteSet A) :
        ∃ n, n ∈ ω ∧ Atoms A ≃ₛ n ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n := by
      obtain ⟨n, hn, hAn⟩ := hA
      have hAtoms : Atoms A ≃ₛ n :=
        equipotent_trans (atoms_equipotent_base A) hAn
      exact ⟨n, hn, hAtoms, BA_cardinality_via_atoms hn hAtoms⟩

    /-- Complete atomic BA form: if A is finite, then 𝒫(A) is a complete
        atomic Boolean algebra with cardinality 2^n. -/
    theorem finite_complete_atomic_BA {A : U} (hA : isFiniteSet A) :
        isCompleteAtomicBA A ∧ ∃ n, n ∈ ω ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n :=
      ⟨powerset_is_complete_atomic_BA A, finite_BA_cardinality hA⟩

  end BoolAlg.FiniteBA

  export BoolAlg.FiniteBA (
    atoms_equipotent_base
    finite_atoms_of_finite
    finite_of_finite_atoms
    BA_cardinality_via_atoms
    finite_powerset_is_finite
    finite_BA_cardinality
    finite_BA_cardinality_atoms
    finite_complete_atomic_BA
  )

end ZFC
