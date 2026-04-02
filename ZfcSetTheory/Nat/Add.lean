/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Addition on Von Neumann Natural Numbers

  This module defines addition on ω (the Von Neumann naturals) via the Recursion Theorem
  and proves it is isomorphic to Peano addition via the bijection ΠZ/ZΠ defined in
  PeanoImport.lean.

  ## Strategy

  Fix m ∈ ω. Define `addFn m hm := RecursiveFn ω m successorFn hm hsucc`, so that
  `addFn m hm : ω → ω` satisfies:
    - (addFn m hm)(∅) = m
    - (addFn m hm)(σ n) = σ ((addFn m hm)(n))

  Then `add m n := if h : m ∈ ω then apply (addFn m h) n else ∅`.

  Carrying no proof argument avoids dependency problems in rewrites and allows
  clean transport of algebraic laws from Peano via `fromPeano_add`.

  ## Bridge Theorem

  The central result `fromPeano_add` states:
    fromPeano (Peano.Add.add p q) = add (fromPeano p) (fromPeano q)

  This allows lifting all theorems from PeanoNatAdd to ZFC sets automatically.
-/

import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity
import ZfcSetTheory.Induction.Recursion
import ZfcSetTheory.Peano.Import
import PeanoNatLib.PeanoNatAdd

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

  namespace Nat.Add

    -- =========================================================================
    -- Section 1: The successor set-function ω → ω
    -- =========================================================================

    /-- The successor function as a ZFC set: `{⟨n, σ n⟩ | n ∈ ω} ⊆ ω ×ₛ ω`. -/
    noncomputable def successorFn : U :=
      SpecSet (ω ×ₛ ω) (fun p => ∃ n, n ∈ (ω : U) ∧ p = ⟨n, σ n⟩)

    /-- The pair `⟨n, σ n⟩` belongs to `successorFn` for every `n ∈ ω`. -/
    theorem mem_successorFn (n : U) (hn : n ∈ (ω : U)) :
        (⟨n, σ n⟩ : U) ∈ (successorFn : U) := by
      unfold successorFn
      rw [SpecSet_is_specified]
      exact ⟨(OrderedPair_mem_CartesianProduct n (σ n) ω ω).mpr
               ⟨hn, succ_in_Omega n hn⟩,
             n, hn, rfl⟩

    /-- `successorFn` is a function from ω to ω. -/
    theorem successorFn_is_function :
        isFunctionFromTo (successorFn : U) ω ω := by
      constructor
      · intro p hp
        unfold successorFn at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      · intro n hn
        exact ⟨σ n, mem_successorFn n hn, fun y hy => by
          dsimp only at hy
          unfold successorFn at hy
          rw [SpecSet_is_specified] at hy
          obtain ⟨_, k, _, heq⟩ := hy
          obtain ⟨hn_eq_k, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections n y k (σ k) heq
          rw [hy_eq, ← hn_eq_k]⟩

    /-- Applying `successorFn` to any `n ∈ ω` yields `σ n`. -/
    theorem successorFn_apply (n : U) (hn : n ∈ (ω : U)) :
        apply (successorFn : U) n = σ n :=
      apply_eq successorFn n (σ n)
        (successorFn_is_function.2 n hn)
        (mem_successorFn n hn)

    -- =========================================================================
    -- Section 2: Addition on ω
    -- =========================================================================

    /-- `addFn m hm` is the ZFC function ω → ω that computes `m + ·`.
        Constructed via the Recursion Theorem with base `m` and step `successorFn`. -/
    noncomputable def addFn (m : U) (hm : m ∈ (ω : U)) : U :=
      RecursiveFn ω m successorFn hm successorFn_is_function

    /-- `addFn m hm` is a function from ω to ω. -/
    theorem addFn_is_function (m : U) (hm : m ∈ (ω : U)) :
        isFunctionFromTo (addFn m hm) ω ω :=
      RecursiveFn_is_function ω m successorFn hm successorFn_is_function

    /-- `add m n` = `m + n` in ZFC.
        Defined without a proof argument (defaults to ∅ when m ∉ ω) so that
        rewrites in algebraic laws avoid dependent-type issues. -/
    noncomputable def add (m n : U) : U :=
      if h : m ∈ (ω : U) then apply (addFn m h) n else ∅

    /-- When `m ∈ ω`, `add m n` unfolds to `apply (addFn m hm) n`. -/
    theorem add_eq (m n : U) (hm : m ∈ (ω : U)) :
        add m n = apply (addFn m hm) n := by
      simp only [add, dif_pos hm]

    /-- `add m n ∈ ω` for all `m n ∈ ω`. -/
    theorem add_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        add m n ∈ ω := by
      rw [add_eq m n hm]
      have hf := addFn_is_function m hm
      have h_unique : ∃! y, ⟨n, y⟩ ∈ addFn m hm := hf.2 n hn
      have h_pair_in : ⟨n, apply (addFn m hm) n⟩ ∈ addFn m hm :=
        apply_mem (addFn m hm) n h_unique
      have h_sub : ∀ p, p ∈ addFn m hm → p ∈ (ω ×ₛ ω : U) := hf.1
      have h_in_prod : ⟨n, apply (addFn m hm) n⟩ ∈ (ω ×ₛ ω : U) := h_sub _ h_pair_in
      exact ((OrderedPair_mem_CartesianProduct n (apply (addFn m hm) n) ω ω).mp h_in_prod).2

    -- =========================================================================
    -- Section 3: Basic recursion equations for add
    -- =========================================================================

    /-- `add m ∅ = m` (zero is the right identity). -/
    theorem add_zero (m : U) (hm : m ∈ (ω : U)) :
        add m ∅ = m := by
      simp only [add, dif_pos hm, addFn]
      exact RecursiveFn_zero ω m successorFn hm successorFn_is_function

    /-- `add m (σ n) = σ (add m n)` for `m n ∈ ω`. -/
    theorem add_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        add m (σ n) = σ (add m n) := by
      simp only [add, dif_pos hm, addFn]
      rw [RecursiveFn_succ ω m successorFn hm successorFn_is_function n hn]
      have h_val_in : apply (RecursiveFn ω m successorFn hm successorFn_is_function) n ∈ ω := by
        have := add_in_Omega m n hm hn
        simp only [add, dif_pos hm, addFn] at this
        exact this
      exact successorFn_apply _ h_val_in

    -- =========================================================================
    -- Section 4: Bridge theorem — fromPeano commutes with addition
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with addition.
        `fromPeano (Peano.Add.add p q) = add (fromPeano p) (fromPeano q)`.

        Proof: induction on `q`. The base uses `add_zero`; the step uses `add_succ`
        and `successorFn_apply`. This allows all theorems of `Peano.Add` to be
        transported to ZFC. -/
    theorem fromPeano_add (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Add.add p q) : U) =
        add (fromPeano p) (fromPeano q) := by
      induction q with
      | zero =>
        -- Peano.Add.add p 𝟘 = p  and  add (fromPeano p) ∅ = fromPeano p
        rw [Peano.Add.add_zero]
        exact (add_zero _ (Nat_in_Omega _ (fromPeano_is_nat p))).symm
      | succ q' ih =>
        -- Peano.Add.add p (succ q') = succ (Peano.Add.add p q')
        rw [Peano.Add.add_succ]
        -- fromPeano (succ x) = σ (fromPeano x) by definition
        -- fromPeano (succ q') = σ (fromPeano q') by definition
        show successor (fromPeano (Peano.Add.add p q') : U) =
             add (fromPeano p) (successor (fromPeano q' : U))
        rw [add_succ _ _ (Nat_in_Omega _ (fromPeano_is_nat p))
                         (Nat_in_Omega _ (fromPeano_is_nat q'))]
        exact congrArg successor ih

    -- =========================================================================
    -- Section 5: Algebraic properties lifted from Peano
    -- =========================================================================

    /-- `∅ + n = n` (zero is the left identity), lifted from Peano. -/
    theorem zero_add (n : U) (hn : n ∈ (ω : U)) :
        add ∅ n = n := by
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hq
      -- Goal: add ∅ (fromPeano q) = fromPeano q
      -- ∅ = fromPeano 𝟘 definitionally; use change to make it syntactic
      change add (fromPeano Peano.ℕ₀.zero) (fromPeano q) = fromPeano q
      rw [← fromPeano_add Peano.ℕ₀.zero q, Peano.Add.zero_add]

    /-- Addition on ω is commutative, lifted from Peano. -/
    theorem add_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        add m n = add n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have hlhs : add (fromPeano p : U) (fromPeano q : U) =
                  (fromPeano (Peano.Add.add p q) : U) :=
        (fromPeano_add p q).symm
      have hrhs : add (fromPeano q : U) (fromPeano p : U) =
                  (fromPeano (Peano.Add.add q p) : U) :=
        (fromPeano_add q p).symm
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Add.add_comm p q)

    /-- Addition on ω is associative, lifted from Peano. -/
    theorem add_assoc_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) :
        add m (add n k) = add (add m n) k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have hlhs : add (fromPeano p : U) (add (fromPeano q : U) (fromPeano r : U)) =
                  (fromPeano (Peano.Add.add p (Peano.Add.add q r)) : U) := by
        rw [← fromPeano_add q r, ← fromPeano_add p (Peano.Add.add q r)]
      have hrhs : add (add (fromPeano p : U) (fromPeano q : U)) (fromPeano r : U) =
                  (fromPeano (Peano.Add.add (Peano.Add.add p q) r) : U) := by
        rw [← fromPeano_add p q, ← fromPeano_add (Peano.Add.add p q) r]
      rw [hlhs, hrhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Add.add_assoc p q r)

    -- =========================================================================
    -- Section 6: More algebraic properties lifted from Peano
    -- =========================================================================

    /-- `σ m + n = σ (m + n)` — follows from commutativity and `add_succ`. -/
    theorem succ_add_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        add (σ m) n = σ (add m n) := by
      rw [add_comm_Omega _ _ (succ_in_Omega m hm) hn,
          add_succ n m hn hm,
          add_comm_Omega m n hm hn]

    /-- Left cancellation: `m + n = m + k → n = k`. -/
    theorem add_left_cancel_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) (h : add m n = add m k) : n = k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have h' : (fromPeano (Peano.Add.add p q) : U) = fromPeano (Peano.Add.add p r) := by
        rwa [fromPeano_add p q, fromPeano_add p r]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
              (Peano.Add.add_cancelation p q r (fromPeano_injective h'))

    /-- Right cancellation: `n + m = k + m → n = k`. -/
    theorem add_right_cancel_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) (h : add n m = add k m) : n = k := by
      apply add_left_cancel_Omega m n k hm hn hk
      rw [add_comm_Omega m n hm hn, add_comm_Omega m k hm hk, h]

    /-- When `m ≠ ∅`, `n ∈ add n m` (i.e. n < n + m). -/
    theorem add_pos_left_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hm_ne : m ≠ ∅) : n ∈ add n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have hp_ne : p ≠ Peano.ℕ₀.zero := by
        intro heq; subst heq; exact hm_ne rfl
      have h_lt : Peano.StrictOrder.Lt q (Peano.Add.add q p) :=
        Peano.Add.lt_self_add_r q p hp_ne
      have h_mem : (fromPeano q : U) ∈ (fromPeano (Peano.Add.add q p) : U) :=
        (fromPeano_lt_iff q (Peano.Add.add q p)).mp h_lt
      rwa [fromPeano_add q p] at h_mem

    /-- If `m ≤ n` (i.e. `m ∈ n ∨ m = n`), then `∃ k ∈ ω, n = add m k`. -/
    theorem le_then_exists_add_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h : m ∈ n ∨ m = n) : ∃ k, k ∈ (ω : U) ∧ n = add m k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_le : Peano.Order.Le p q := (fromPeano_le_iff p q).mpr h
      obtain ⟨r, hr⟩ := Peano.Add.le_then_exists_add p q h_le
      refine ⟨fromPeano r, Nat_in_Omega _ (fromPeano_is_nat r), ?_⟩
      have : (fromPeano (Peano.Add.add p r) : U) = add (fromPeano p) (fromPeano r) :=
        fromPeano_add p r
      rw [← hr] at this
      exact this

    /-- `n ∈ k → add m n ∈ add m k` (strict monotonicity of addition on the left). -/
    theorem add_lt_of_lt_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hk : k ∈ (ω : U)) (h : n ∈ k) : add m n ∈ add m k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      have h_lt : Peano.StrictOrder.Lt q r := (fromPeano_lt_iff q r).mpr h
      have h_lt' : Peano.StrictOrder.Lt (Peano.Add.add p q) (Peano.Add.add p r) :=
        (Peano.Add.add_lt_add_left_iff p q r).mpr h_lt
      have h_mem : (fromPeano (Peano.Add.add p q) : U) ∈ (fromPeano (Peano.Add.add p r) : U) :=
        (fromPeano_lt_iff (Peano.Add.add p q) (Peano.Add.add p r)).mp h_lt'
      rwa [fromPeano_add p q, fromPeano_add p r] at h_mem

  end Nat.Add

  export Nat.Add (
    -- Section 1: successorFn
    successorFn
    mem_successorFn
    successorFn_is_function
    successorFn_apply
    -- Section 2: add
    addFn
    addFn_is_function
    add
    add_eq
    add_in_Omega
    -- Section 3: basic recursion equations
    add_zero
    add_succ
    -- Section 4: bridge
    fromPeano_add
    -- Section 5: algebraic properties
    zero_add
    add_comm_Omega
    add_assoc_Omega
    -- Section 6: further properties
    succ_add_Omega
    add_left_cancel_Omega
    add_right_cancel_Omega
    add_pos_left_Omega
    le_then_exists_add_Omega
    add_lt_of_lt_Omega
  )

end ZFC
