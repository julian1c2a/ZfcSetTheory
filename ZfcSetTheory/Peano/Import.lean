import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  This module establishes an isomorphism between the Von Neumann natural numbers
  defined in this project and the Peano natural numbers from the `peanolib` library.

  Predecessor theorems (predecessorPos, predecessor_zero, successor_predecessorPos)
  live in `ZFC.Nat.Basic` (Nat.Basic.lean).

  Order on ω (≺, ≼, natLt_*, natLe_*, Omega_has_min) lives in
  `ZFC.Axiom.Infinity` (Infinity.lean).
-/

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

  universe u
  variable {U : Type u}

  namespace Peano.Import

    -- =========================================================================
    -- Section 1: The bijection between Peano and Von Neumann naturals
    -- =========================================================================

    /-- Converts a Peano natural number to its Von Neumann representation. -/
    noncomputable def fromPeano : Peano.ℕ₀ → U
      | Peano.ℕ₀.zero    => (∅ : U)
      | Peano.ℕ₀.succ n' => successor (fromPeano n')

    /-- `ΠZ p` : canonical embedding Peano ℕ → Von Neumann ℕ.
        Typed as `\PiZ` in the editor.
        Note: `Π` is a reserved Lean 4 token; `ΠZ` works as a registered notation.
        In theorem headers where `U` cannot be inferred, use the type ascription
        `(ΠZ p : U)` or `(ΠZ : Peano.ℕ₀ → U)`. -/
    scoped notation "ΠZ" => fromPeano

    /-- `ΠZ` maps Peano naturals to Von Neumann naturals. -/
    theorem fromPeano_is_nat (n : Peano.ℕ₀) : isNat (ΠZ n : U) := by
      induction n with
      | zero       => exact zero_is_nat
      | succ n' ih => exact nat_successor_is_nat (ΠZ n') ih

    /-- `ΠZ` is injective. -/
    theorem fromPeano_injective : Function.Injective (ΠZ : Peano.ℕ₀ → U) := by
      -- ih : ∀ ⦃b⦄, ΠZ m' = ΠZ b → m' = b
      -- Lean infers b from the proof, so use `ih proof` not `ih n' proof`.
      intro m
      induction m with
      | zero =>
        intro n h
        cases n with
        | zero   => rfl
        | succ n' => exact absurd h (Ne.symm (successor_nonempty (ΠZ n')))
      | succ m' ih =>
        intro n h
        cases n with
        | zero => exact absurd h (successor_nonempty (ΠZ m'))
        | succ n' =>
          congr 1
          apply ih
          exact successor_injective (ΠZ m') (ΠZ n')
            (fromPeano_is_nat m') (fromPeano_is_nat n') h

    /-- Every Von Neumann natural is in the image of `ΠZ`. -/
    theorem fromPeano_surjective (n : U) (hn : isNat n) :
        ∃ p : Peano.ℕ₀, (ΠZ p : U) = n := by
      -- S = { m ∈ ω | ∃ p : ℕ₀, ΠZ p = m }
      let S := SpecSet (ω : U) (fun m => ∃ p : Peano.ℕ₀, (ΠZ p : U) = m)
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
      · -- m = ∅ : ΠZ ℕ₀.zero = ∅
        exact ⟨Peano.ℕ₀.zero, rfl⟩
      · -- m = σ k : use IH on k ∈ m
        have hk_in_S : k ∈ S := ih k (mem_successor_self k)
        rw [SpecSet_is_specified] at hk_in_S
        obtain ⟨p, hp⟩ := hk_in_S.2
        -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) = σ k
        exact ⟨Peano.ℕ₀.succ p,
          show successor (ΠZ p : U) = successor k from by rw [hp]⟩

    /-- `ZΠ n h` : inverse isomorphism Von Neumann ℕ → Peano ℕ.
        Typed as `Z\Pi` in the editor. -/
    noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ₀ :=
      Classical.choose (fromPeano_surjective n hn)

    scoped notation "ZΠ" => toPeano

    /-- `ΠZ (ZΠ n hn) = n`. -/
    theorem fromPeano_toPeano (n : U) (hn : isNat n) :
        ΠZ (ZΠ n hn) = n :=
      Classical.choose_spec (fromPeano_surjective n hn)

    /-- `ZΠ (ΠZ p) _ = p`. -/
    theorem toPeano_fromPeano (p : Peano.ℕ₀) :
        ZΠ (ΠZ p : U) (fromPeano_is_nat p) = p :=
      fromPeano_injective (fromPeano_toPeano (ΠZ p) (fromPeano_is_nat p))

    /-- `ZΠ` is injective on Von Neumann naturals. -/
    theorem toPeano_injective {m n : U} (hm : isNat m) (hn : isNat n)
        (h : ZΠ m hm = ZΠ n hn) : m = n := by
      rw [← fromPeano_toPeano m hm, ← fromPeano_toPeano n hn, h]

    /-- `ZΠ` is surjective onto Peano naturals. -/
    theorem toPeano_surjective (p : Peano.ℕ₀) :
        ∃ (n : U) (hn : isNat n), ZΠ n hn = p :=
      ⟨(ΠZ p : U), fromPeano_is_nat p, toPeano_fromPeano p⟩

    -- =========================================================================
    -- Section 2: The bijection is an isomorphism of Peano algebras
    -- =========================================================================

    /-- `ZΠ` maps ∅ to `Peano.ℕ₀.zero`.
        Together with `toPeano_successor`, this shows the bijection is a
        homomorphism of Peano algebras in both directions. -/
    theorem toPeano_zero :
        ZΠ (∅ : U) zero_is_nat = Peano.ℕ₀.zero :=
      -- ΠZ Peano.ℕ₀.zero = ∅ by definition, so fromPeano_toPeano gives
      -- ΠZ (ZΠ ∅ _) = ∅ = ΠZ ℕ₀.zero; injectivity concludes.
      fromPeano_injective (fromPeano_toPeano (∅ : U) zero_is_nat)

    /-- `ZΠ` commutes with successor: the bijection is a homomorphism of
        the successor structure in both directions. -/
    theorem toPeano_successor (n : U) (hn : isNat n) :
        ZΠ (σ n) (nat_successor_is_nat n hn) =
        Peano.ℕ₀.succ (ZΠ n hn) := by
      apply fromPeano_injective
      -- Goal: ΠZ (ZΠ (σ n) _) = ΠZ (ℕ₀.succ (ZΠ n hn))
      rw [fromPeano_toPeano]
      -- Goal: σ n = ΠZ (ℕ₀.succ (ZΠ n hn))
      -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) by definition
      show successor n = successor (ΠZ (ZΠ n hn))
      rw [fromPeano_toPeano]

    -- =========================================================================
    -- Section 3: Recursion transport theorems
    -- =========================================================================

    /-- **Recursion transport (VN → Peano)**: any Von Neumann recursive function
        `F : ω → U` induces a Peano recursive function via `ΠZ`.

        If `apply F ∅ = a` and `apply F (σ n) = apply g (apply F n)` for all `n ∈ ω`,
        then `f p := apply F (ΠZ p)` satisfies `f 𝟘 = a` and
        `f (σ p) = apply g (f p)` for all `p : ℕ₀`. -/
    theorem recursion_transport (F a g : U)
        (hF_zero : apply F (∅ : U) = a)
        (hF_succ : ∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) :
        let f : Peano.ℕ₀ → U := fun p => apply F (ΠZ p : U)
        f Peano.ℕ₀.zero = a ∧ ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p) :=
      ⟨hF_zero, fun p =>
        -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) by definition
        -- ΠZ p ∈ ω by fromPeano_is_nat + Nat_in_Omega
        hF_succ (ΠZ p) (Nat_in_Omega _ (fromPeano_is_nat p))⟩

    /-- **Recursion transport (Peano → VN)**: any Lean function `f : ℕ₀ → U`
        satisfying Peano recursion also satisfies Von Neumann recursion via `ZΠ`.

        If `f 𝟘 = a` and `f (σ p) = apply g (f p)`, then
        `f (ZΠ ∅ _) = a` and
        `f (ZΠ (σ n) _) = apply g (f (ZΠ n _))` for all `n ∈ ω`. -/
    theorem recursion_transport_inv (a g : U) (f : Peano.ℕ₀ → U)
        (hf_zero : f Peano.ℕ₀.zero = a)
        (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p)) :
        f (ZΠ (∅ : U) zero_is_nat) = a ∧
        ∀ (n : U) (hn : n ∈ ω),
          f (ZΠ (σ n) (nat_successor_is_nat n (mem_Omega_is_Nat n hn))) =
          apply g (f (ZΠ n (mem_Omega_is_Nat n hn))) := by
      refine ⟨?_, fun n hn => ?_⟩
      · rw [toPeano_zero]; exact hf_zero
      · rw [toPeano_successor]; exact hf_succ _

    /-- **Recursion transport (VN → Peano, with step)**: variant of `recursion_transport`
        for `RecursionTheoremWithStep`, where the step function receives the current index.

        If `apply F ∅ = a` and `apply F (σ n) = apply g ⟨n, apply F n⟩` for all `n ∈ ω`,
        then `f p := apply F (ΠZ p)` satisfies `f 𝟘 = a` and
        `f (σ p) = apply g ⟨ΠZ p, f p⟩` for all `p : ℕ₀`. -/
    theorem recursion_transport_step (F a g : U)
        (hF_zero : apply F (∅ : U) = a)
        (hF_succ : ∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩) :
        let f : Peano.ℕ₀ → U := fun p => apply F (ΠZ p : U)
        f Peano.ℕ₀.zero = a ∧ ∀ p, f (Peano.ℕ₀.succ p) = apply g ⟨(ΠZ p : U), f p⟩ :=
      ⟨hF_zero, fun p => hF_succ (ΠZ p) (Nat_in_Omega _ (fromPeano_is_nat p))⟩

    /-- **Recursion transport (Peano → VN, with step)**: variant of `recursion_transport_inv`
        for `RecursionTheoremWithStep`.

        If `f 𝟘 = a` and `f (σ p) = apply g ⟨ΠZ p, f p⟩`, then
        `f (ZΠ ∅ _) = a` and `f (ZΠ (σ n) _) = apply g ⟨n, f (ZΠ n _)⟩`
        for all `n ∈ ω`. -/
    theorem recursion_transport_step_inv (a g : U) (f : Peano.ℕ₀ → U)
        (hf_zero : f Peano.ℕ₀.zero = a)
        (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g ⟨(ΠZ p : U), f p⟩) :
        f (ZΠ (∅ : U) zero_is_nat) = a ∧
        ∀ (n : U) (hn : n ∈ ω),
          f (ZΠ (σ n) (nat_successor_is_nat n (mem_Omega_is_Nat n hn))) =
          apply g ⟨n, f (ZΠ n (mem_Omega_is_Nat n hn))⟩ := by
      refine ⟨?_, fun n hn => ?_⟩
      · rw [toPeano_zero]; exact hf_zero
      · rw [toPeano_successor]
        have h := hf_succ (ZΠ n (mem_Omega_is_Nat n hn))
        rw [fromPeano_toPeano] at h
        exact h

    -- =========================================================================
    -- Section 4: Bridge theorems for order
    -- =========================================================================

    /-- The successor function preserves and reflects membership:
        `n ∈ m ↔ σ n ∈ σ m` for Von Neumann naturals. -/
    theorem succ_mem_succ_iff (n m : U) (hn : isNat n) (hm : isNat m) :
        n ∈ m ↔ σ n ∈ σ m := by
      constructor
      · intro h_nm
        -- n ⊆ m by transitivity of m; then σn = n ∪ {n} ⊆ m ∪ {m} = σm
        have hn_sub_m : n ⊆ m := hm.1 n h_nm
        have h_σn_sub_σm : σ n ⊆ σ m := by
          intro x hx
          rw [successor_is_specified] at hx
          rcases hx with hx | hx
          · exact mem_successor_of_mem x m (hn_sub_m x hx)
          · rw [hx]; exact mem_successor_of_mem n m h_nm
        rcases nat_subset_mem_or_eq (σ n) (σ m)
            (nat_successor_is_nat n hn) (nat_successor_is_nat m hm) h_σn_sub_σm with h | h
        · exact h
        · exact absurd (successor_injective n m hn hm h ▸ h_nm) (nat_not_mem_self n hn)
      · intro h_sn_sm
        rcases nat_trichotomy n m hn hm with h | h | h
        · exact h
        · -- n = m → σn = σm → σn ∈ σn: contradicts irreflexivity
          exact absurd (h ▸ h_sn_sm) (nat_not_mem_self (σ n) (nat_successor_is_nat n hn))
        · -- m ∈ n → σm ∈ σn; combined with σn ∈ σm: asymmetry contradiction
          have hm_sub_n : m ⊆ n := hn.1 m h
          have h_σm_sub_σn : σ m ⊆ σ n := by
            intro x hx
            rw [successor_is_specified] at hx
            rcases hx with hx | hx
            · exact mem_successor_of_mem x n (hm_sub_n x hx)
            · rw [hx]; exact mem_successor_of_mem m n h
          rcases nat_subset_mem_or_eq (σ m) (σ n)
              (nat_successor_is_nat m hm) (nat_successor_is_nat n hn) h_σm_sub_σn with hh | hh
          · exact absurd h_sn_sm (nat_mem_asymm (σ m) (σ n)
                (nat_successor_is_nat m hm) (nat_successor_is_nat n hn) hh)
          · exact absurd (successor_injective m n hm hn hh ▸ h) (nat_not_mem_self m hm)

    /-- `ΠZ` preserves and reflects the strict order:
        `Peano.StrictOrder.Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U)`. -/
    theorem fromPeano_lt_iff (p q : Peano.ℕ₀) :
        Peano.StrictOrder.Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U) := by
      induction q generalizing p with
      | zero =>
        -- Lt p 0 = False definitionally; ΠZ 0 = ∅ so ΠZ p ∉ ∅
        constructor
        · intro h
          unfold Peano.StrictOrder.Lt at h
          exact False.elim h
        · intro h
          exact (EmptySet_is_empty _ h).elim
      | succ q' ihq =>
        cases p with
        | zero =>
          -- Lt 0 (σ q') = True; ∅ ∈ σ (ΠZ q') since σ (ΠZ q') ≠ ∅
          constructor
          · intro _
            exact zero_mem_of_nat_nonempty (σ (ΠZ q' : U))
              (nat_successor_is_nat _ (fromPeano_is_nat q'))
              (successor_nonempty _)
          · intro _; trivial
        | succ p' =>
          -- Lt (σ p') (σ q') = Lt p' q' definitionally
          show Peano.StrictOrder.Lt p' q' ↔ σ (ΠZ p' : U) ∈ σ (ΠZ q' : U)
          exact (ihq p').trans (succ_mem_succ_iff _ _ (fromPeano_is_nat p') (fromPeano_is_nat q'))

    /-- `ΠZ` preserves and reflects the non-strict order:
        `Peano.Order.Le p q ↔ (ΠZ p : U) ∈ (ΠZ q : U) ∨ (ΠZ p : U) = (ΠZ q : U)`. -/
    theorem fromPeano_le_iff (p q : Peano.ℕ₀) :
        Peano.Order.Le p q ↔
        ((ΠZ p : U) ∈ (ΠZ q : U) ∨ (ΠZ p : U) = (ΠZ q : U)) := by
      unfold Peano.Order.Le
      rw [fromPeano_lt_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (congrArg (ΠZ : Peano.ℕ₀ → U) h)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (fromPeano_injective h)

  end Peano.Import

  -- Notations re-exported at ZFC level (require open ZFC)
  scoped notation "ΠZ" => Peano.Import.fromPeano
  scoped notation "ZΠ" => Peano.Import.toPeano

  export Peano.Import (
    -- Definitions
    fromPeano
    toPeano
    -- Section 1: Bijection
    fromPeano_is_nat
    fromPeano_injective
    fromPeano_surjective
    fromPeano_toPeano
    toPeano_fromPeano
    toPeano_injective
    toPeano_surjective
    -- Section 2: Peano algebra isomorphism
    toPeano_zero
    toPeano_successor
    -- Section 3: Recursion transport
    recursion_transport
    recursion_transport_inv
    recursion_transport_step
    recursion_transport_step_inv
    -- Section 4: Bridge theorems for order
    succ_mem_succ_iff
    fromPeano_lt_iff
    fromPeano_le_iff
  )

end ZFC
