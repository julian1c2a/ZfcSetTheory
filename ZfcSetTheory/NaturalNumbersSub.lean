/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Saturated (Monus) Subtraction on Von Neumann Natural Numbers

  This module defines saturated subtraction (monus) on ω (the Von Neumann naturals) via the
  Recursion Theorem and proves it is isomorphic to Peano monus via the bijection ΠZ/ZΠ
  defined in PeanoImport.lean.

  ## Strategy

  Fix m ∈ ω. Define `subFn m hm := RecursiveFn ω m predecessorFn hm predecessorFn_is_function`,
  so that `subFn m hm : ω → ω` satisfies:
    - (subFn m hm)(∅)   = m                            -- m - 0 = m
    - (subFn m hm)(σ n) = predecessor ((subFn m hm)(n)) -- m - (σn) = pred(m - n)

  Since `predecessor ∅ = ∅`, applying predecessor repeatedly saturates at 0, giving exactly
  monus (truncated subtraction).

  Then `sub m n := if h : m ∈ ω then apply (subFn m h) n else ∅`.

  ## Bridge Theorem

  The central result `fromPeano_sub` states:
    fromPeano (Peano.Sub.sub p q) = sub (fromPeano p) (fromPeano q)

  Proof uses the helper theorem `peano_sub_succ_tau`:
    Peano.Sub.sub p (σ q) = Peano.τ (Peano.Sub.sub p q)
  (which holds unconditionally), combined with `predecessor_fromPeano_eq_tau`:
    predecessor (fromPeano x) = fromPeano (τ x).
  Induction on q then closes the bridge.
-/

import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity
import ZfcSetTheory.Recursion
import ZfcSetTheory.PeanoImport
import ZfcSetTheory.NaturalNumbersAdd
import PeanoNatLib.PeanoNatSub

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
  -- Note: PeanoIsomorphism is NOT opened here to avoid ΠZ notation ambiguity.
  -- All PeanoIsomorphism exports are available at SetUniverse level.

  universe u
  variable {U : Type u}

  namespace NaturalNumbersSub

    -- =========================================================================
    -- Section 0: The predecessor set-function ω → ω
    -- =========================================================================

    /-- `predecessorFn` is the ZFC set `{⟨n, predecessor n⟩ | n ∈ ω} ⊆ ω ×ₛ ω`.
        Since `predecessor (σ n) = n` and `predecessor ∅ = ∅`, this represents the
        saturated predecessor function on Von Neumann naturals. -/
    noncomputable def predecessorFn : U :=
      SpecSet (ω ×ₛ ω) (fun p => ∃ n, n ∈ (ω : U) ∧ p = ⟨n, predecessor n⟩)

    /-- For `n ∈ ω`, the pair `⟨n, predecessor n⟩` belongs to `predecessorFn`. -/
    theorem mem_predecessorFn (n : U) (hn : n ∈ (ω : U)) :
        (⟨n, predecessor n⟩ : U) ∈ (predecessorFn : U) := by
      unfold predecessorFn
      rw [SpecSet_is_specified]
      have hn_nat : isNat n := mem_Omega_is_Nat n hn
      have hpred_in : predecessor n ∈ (ω : U) := by
        by_cases h : n = ∅
        · rw [h, predecessor_zero]; exact zero_in_Omega
        · exact Nat_in_Omega _ (predecessor_is_nat n hn_nat h)
      exact ⟨(OrderedPair_mem_CartesianProduct n (predecessor n) ω ω).mpr
               ⟨hn, hpred_in⟩,
             n, hn, rfl⟩

    /-- `predecessorFn` is a function from ω to ω. -/
    theorem predecessorFn_is_function :
        isFunctionFromTo (predecessorFn : U) ω ω := by
      constructor
      · intro p hp
        unfold predecessorFn at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      · intro n hn
        exact ⟨predecessor n, mem_predecessorFn n hn, fun y hy => by
          dsimp only at hy
          unfold predecessorFn at hy
          rw [SpecSet_is_specified] at hy
          obtain ⟨_, k, _, heq⟩ := hy
          obtain ⟨hn_eq_k, hy_eq⟩ :=
            Eq_of_OrderedPairs_given_projections n y k (predecessor k) heq
          rw [hy_eq, ← hn_eq_k]⟩

    /-- Applying `predecessorFn` to any `n ∈ ω` yields `predecessor n`. -/
    theorem predecessorFn_apply (n : U) (hn : n ∈ (ω : U)) :
        apply (predecessorFn : U) n = predecessor n :=
      apply_eq predecessorFn n (predecessor n)
        (predecessorFn_is_function.2 n hn)
        (mem_predecessorFn n hn)

    -- =========================================================================
    -- Section 1: Subtraction (monus) on ω
    -- =========================================================================

    /-- `subFn m hm` is the ZFC function ω → ω that computes `m - ·` (saturated).
        Constructed via the Recursion Theorem with base `m` and step `predecessorFn`.
        Applying `predecessorFn` n times to `m` gives `m - n` (saturated at 0). -/
    noncomputable def subFn (m : U) (hm : m ∈ (ω : U)) : U :=
      RecursiveFn ω m predecessorFn hm predecessorFn_is_function

    /-- `subFn m hm` is a function from ω to ω. -/
    theorem subFn_is_function (m : U) (hm : m ∈ (ω : U)) :
        isFunctionFromTo (subFn m hm) ω ω :=
      RecursiveFn_is_function ω m predecessorFn hm predecessorFn_is_function

    /-- `sub m n` = saturated subtraction `m - n` in ZFC.
        Defined without a proof argument (defaults to ∅ when m ∉ ω) so that
        rewrites in algebraic laws avoid dependent-type issues. -/
    noncomputable def sub (m n : U) : U :=
      if h : m ∈ (ω : U) then apply (subFn m h) n else ∅

    /-- When `m ∈ ω`, `sub m n` unfolds to `apply (subFn m hm) n`. -/
    theorem sub_eq (m n : U) (hm : m ∈ (ω : U)) :
        sub m n = apply (subFn m hm) n := by
      simp only [sub, dif_pos hm]

    /-- `sub m n ∈ ω` for all `m n ∈ ω`. -/
    theorem sub_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub m n ∈ ω := by
      rw [sub_eq m n hm]
      have hf := subFn_is_function m hm
      have h_unique : ∃! y, ⟨n, y⟩ ∈ subFn m hm := hf.2 n hn
      have h_pair_in : ⟨n, apply (subFn m hm) n⟩ ∈ subFn m hm :=
        apply_mem (subFn m hm) n h_unique
      have h_sub : ∀ x, x ∈ subFn m hm → x ∈ (ω ×ₛ ω : U) := hf.1
      have h_in_prod : ⟨n, apply (subFn m hm) n⟩ ∈ (ω ×ₛ ω : U) := h_sub _ h_pair_in
      exact ((OrderedPair_mem_CartesianProduct n (apply (subFn m hm) n) ω ω).mp h_in_prod).2

    -- =========================================================================
    -- Section 2: Basic recursion equations for sub
    -- =========================================================================

    /-- `sub m ∅ = m` (subtracting zero is identity). -/
    theorem sub_zero (m : U) (hm : m ∈ (ω : U)) :
        sub m ∅ = m := by
      simp only [sub, dif_pos hm, subFn]
      exact RecursiveFn_zero ω m predecessorFn hm predecessorFn_is_function

    /-- `sub m (σ n) = predecessor (sub m n)` for `m n ∈ ω`. -/
    theorem sub_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub m (σ n) = predecessor (sub m n) := by
      simp only [sub, dif_pos hm, subFn]
      rw [RecursiveFn_succ ω m predecessorFn hm predecessorFn_is_function n hn]
      have h_val_in : apply (RecursiveFn ω m predecessorFn hm predecessorFn_is_function) n ∈ ω := by
        have := sub_in_Omega m n hm hn
        simp only [sub, dif_pos hm, subFn] at this
        exact this
      exact predecessorFn_apply _ h_val_in

    -- =========================================================================
    -- Section 3: Peano helper theorems for the bridge
    -- =========================================================================

    /-- **Helper**: `sub p (σ q) = τ (sub p q)` in Peano — holds unconditionally.
        When `σ q ≤ p`: direct application of `succ_sub`.
        When `σ q > p` (i.e., `p ≤ q`): both sides equal 0. -/
    private theorem peano_sub_succ_tau (p q : Peano.ℕ₀) :
        Peano.Sub.sub p (Peano.ℕ₀.succ q) = Peano.τ (Peano.Sub.sub p q) := by
      by_cases h : Peano.Order.Le (Peano.ℕ₀.succ q) p
      · -- σ q ≤ p: use Peano.Sub.succ_sub directly
        exact Peano.Sub.succ_sub p q h
      · -- ¬(σ q ≤ p), so p ≤ q
        have h_p_le_q : Peano.Order.Le p q :=
          (Peano.Order.lt_succ_iff_le p q).mp (Peano.Order.nle_then_gt_wp h)
        -- sub p (σ q) = 0
        have h1 : Peano.Sub.sub p (Peano.ℕ₀.succ q) = Peano.ℕ₀.zero := by
          simp only [Peano.Sub.sub, dif_neg h]
        -- sub p q = 0
        have h2 : Peano.Sub.sub p q = Peano.ℕ₀.zero := by
          by_cases heq : Peano.Order.Le q p
          · -- q ≤ p and p ≤ q, so p = q
            rw [Peano.Order.le_antisymm p q h_p_le_q heq]
            exact Peano.Sub.sub_self q
          · -- ¬(q ≤ p)
            simp only [Peano.Sub.sub, dif_neg heq]
        rw [h1, h2]
        rfl  -- τ 𝟘 = 𝟘 by definition

    /-- **Helper**: `predecessor (ΠZ x : U) = ΠZ (τ x)`.
        For `x = 0`: `predecessor ∅ = ∅ = ΠZ (τ 0)`.
        For `x = σ k`: `predecessor (σ (ΠZ k)) = ΠZ k = ΠZ (τ (σ k))`. -/
    private theorem predecessor_fromPeano_eq_tau (x : Peano.ℕ₀) :
        predecessor (fromPeano x : U) = fromPeano (Peano.τ x) := by
      cases x with
      | zero =>
        simp only [Peano.τ]
        exact predecessor_zero
      | succ k =>
        -- fromPeano (σ k) = successor (fromPeano k) definitionally
        show predecessor (successor (fromPeano k : U)) = fromPeano k
        exact predecessor_of_successor (fromPeano_is_nat k)

    -- =========================================================================
    -- Section 4: Bridge theorem — fromPeano commutes with subtraction
    -- =========================================================================

    /-- **Bridge theorem**: the isomorphism `fromPeano` commutes with monus subtraction.
        `fromPeano (Peano.Sub.sub p q) = sub (fromPeano p) (fromPeano q)`.

        Proof: induction on `q`. The base uses `sub_zero`; the step uses
        `peano_sub_succ_tau` (unconditional monus recursion in Peano) and
        `predecessor_fromPeano_eq_tau` to convert `τ` to `predecessor`. -/
    theorem fromPeano_sub (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Sub.sub p q) : U) =
        sub (fromPeano p) (fromPeano q) := by
      induction q with
      | zero =>
        -- Peano: sub p 0 = p, via sub_k_add_k p 0 (zero_le p)
        have h_peano_sub_zero : Peano.Sub.sub p Peano.ℕ₀.zero = p := by
          have h := Peano.Sub.sub_k_add_k p Peano.ℕ₀.zero
                      (Peano.Order.zero_le p)
          rw [Peano.Add.add_zero] at h
          exact h
        rw [h_peano_sub_zero]
        exact (sub_zero _ (Nat_in_Omega _ (fromPeano_is_nat p))).symm
      | succ q' ih =>
        -- Peano: sub p (σ q') = τ (sub p q')
        rw [peano_sub_succ_tau p q']
        -- fromPeano (τ x) = predecessor (fromPeano x)
        rw [← predecessor_fromPeano_eq_tau (Peano.Sub.sub p q')]
        -- IH: fromPeano (sub p q') = sub (fromPeano p) (fromPeano q')
        rw [ih]
        -- Goal: predecessor (sub (fromPeano p) (fromPeano q')) =
        --       sub (fromPeano p) (successor (fromPeano q'))
        show predecessor (sub (fromPeano p : U) (fromPeano q' : U)) =
             sub (fromPeano p : U) (successor (fromPeano q' : U))
        exact (sub_succ (fromPeano p) (fromPeano q')
                 (Nat_in_Omega _ (fromPeano_is_nat p))
                 (Nat_in_Omega _ (fromPeano_is_nat q'))).symm

    -- =========================================================================
    -- Section 5: Algebraic properties lifted from Peano
    -- =========================================================================

    /-- `sub ∅ n = ∅` (subtracting from zero always gives zero), lifted from Peano. -/
    theorem zero_sub_Omega (n : U) (hn : n ∈ (ω : U)) :
        sub ∅ n = ∅ := by
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hq
      change sub (fromPeano Peano.ℕ₀.zero) (fromPeano q) = fromPeano Peano.ℕ₀.zero
      rw [← fromPeano_sub Peano.ℕ₀.zero q]
      have h_le : Peano.Order.Le (Peano.Sub.sub Peano.ℕ₀.zero q)
                                  Peano.ℕ₀.zero :=
        Peano.Sub.sub_le_self Peano.ℕ₀.zero q
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
              (Peano.Order.le_zero_eq (Peano.Sub.sub Peano.ℕ₀.zero q) h_le)

    /-- `sub m m = ∅` (any natural minus itself is zero), lifted from Peano. -/
    theorem sub_self_Omega (m : U) (hm : m ∈ (ω : U)) :
        sub m m = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp
      change sub (fromPeano p) (fromPeano p) = fromPeano Peano.ℕ₀.zero
      rw [← fromPeano_sub p p]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Sub.sub_self p)

    /-- `sub (σ m) (σ n) = sub m n` (cancel matching successors), lifted from Peano. -/
    theorem sub_succ_succ_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub (σ m) (σ n) = sub m n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      -- fromPeano (σ p) = σ (fromPeano p) definitionally
      change sub (fromPeano (Peano.ℕ₀.succ p) : U) (fromPeano (Peano.ℕ₀.succ q) : U) =
             sub (fromPeano p : U) (fromPeano q : U)
      rw [← fromPeano_sub (Peano.ℕ₀.succ p) (Peano.ℕ₀.succ q),
          ← fromPeano_sub p q]
      exact congrArg (fromPeano : Peano.ℕ₀ → U)
              (Peano.Sub.sub_succ_succ_eq p q).symm

    /-- `sub (add m n) n = m` for `m n ∈ ω` (subtracting what was added cancels),
        lifted from Peano (`add_k_sub_k`). -/
    theorem sub_k_add_k_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub (add m n) n = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      -- Peano: sub (add q p) q = p  (add_k_sub_k p q)
      -- ZFC wants: sub (add (fromPeano p) (fromPeano q)) (fromPeano q) = fromPeano p
      -- Use add_comm to rewrite add p q to add q p
      have h_peano : Peano.Sub.sub (Peano.Add.add p q) q = p := by
        rw [Peano.Add.add_comm p q]
        exact Peano.Sub.add_k_sub_k p q
      have hlhs : sub (add (fromPeano p : U) (fromPeano q : U)) (fromPeano q : U) =
                  (fromPeano (Peano.Sub.sub (Peano.Add.add p q) q) : U) := by
        rw [← fromPeano_add p q]
        exact (fromPeano_sub (Peano.Add.add p q) q).symm
      rw [hlhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) h_peano

    /-- `n ≤ m → add (sub m n) n = m` for `m n ∈ ω` (adding back what was subtracted),
        lifted from Peano (`sub_k_add_k`). Here `n ≤ m` is stated as `n ∈ m ∨ n = m`. -/
    theorem add_k_sub_k_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_le : n ∈ m ∨ n = m) : add (sub m n) n = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      have h_peano_le : Peano.Order.Le q p :=
        (fromPeano_le_iff q p).mpr h_le
      -- Peano: sub_k_add_k p q h_peano_le : add (sub p q) q = p
      have h_peano : Peano.Add.add (Peano.Sub.sub p q) q = p :=
        Peano.Sub.sub_k_add_k p q h_peano_le
      have hlhs : add (sub (fromPeano p : U) (fromPeano q : U)) (fromPeano q : U) =
                  (fromPeano (Peano.Add.add (Peano.Sub.sub p q) q) : U) := by
        rw [← fromPeano_sub p q]
        exact (fromPeano_add (Peano.Sub.sub p q) q).symm
      rw [hlhs]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) h_peano

    /-- `sub m n ∈ m ∨ sub m n = m` for `m n ∈ ω` (subtraction does not exceed the minuend),
        lifted from Peano. This expresses `sub m n ≤ m` in ZFC membership order. -/
    theorem sub_le_self_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub m n ∈ m ∨ sub m n = m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_sub p q]
      exact (fromPeano_le_iff (Peano.Sub.sub p q) p).mp
              (Peano.Sub.sub_le_self p q)

    /-- `sub m n ≠ ∅ ↔ n ∈ m` for `m n ∈ ω` (subtraction is positive iff n < m),
        lifted from Peano. In ZFC, `n < m ↔ n ∈ m` for Von Neumann naturals. -/
    theorem sub_pos_iff_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        sub m n ≠ ∅ ↔ n ∈ m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_sub p q]
      constructor
      · intro h_ne
        -- fromPeano (sub p q) ≠ ∅ → sub p q ≠ 𝟘
        have h_peano_ne : Peano.Sub.sub p q ≠ Peano.ℕ₀.zero := fun heq =>
          h_ne (congrArg (fromPeano : Peano.ℕ₀ → U) heq)
        -- Le 𝟙 (sub p q) from sub p q ≠ 𝟘 (by case analysis)
        have h_pos : Peano.Order.Le Peano.one (Peano.Sub.sub p q) := by
          cases h_val : Peano.Sub.sub p q with
          | zero => exact absurd h_val h_peano_ne
          | succ k =>
            -- Le 𝟙 (σ k) = Le (σ 𝟘) (σ k) ↔ Le 𝟘 k, which is zero_le k
            exact (Peano.Order.succ_le_succ_iff Peano.ℕ₀.zero k).mpr
                    (Peano.Order.zero_le k)
        -- Lt q p from sub_pos_iff_lt
        have h_lt : Peano.StrictOrder.Lt q p :=
          (Peano.Sub.sub_pos_iff_lt p q).mp h_pos
        exact (fromPeano_lt_iff q p).mp h_lt
      · intro h_mem
        -- fromPeano q ∈ fromPeano p → Lt q p
        have h_lt : Peano.StrictOrder.Lt q p := (fromPeano_lt_iff q p).mpr h_mem
        -- Lt q p → sub p q ≠ 𝟘
        have h_peano_ne : Peano.Sub.sub p q ≠ Peano.ℕ₀.zero :=
          Peano.Sub.lt_b_a_then_sub_a_b_neq_0 p q h_lt
        intro h_eq
        exact h_peano_ne (fromPeano_injective h_eq)

  end NaturalNumbersSub

  export NaturalNumbersSub (
    -- Section 0: predecessorFn
    predecessorFn
    mem_predecessorFn
    predecessorFn_is_function
    predecessorFn_apply
    -- Section 1: sub
    subFn
    subFn_is_function
    sub
    sub_eq
    sub_in_Omega
    -- Section 2: basic recursion equations
    sub_zero
    sub_succ
    -- Section 4: bridge
    fromPeano_sub
    -- Section 5: algebraic properties
    zero_sub_Omega
    sub_self_Omega
    sub_succ_succ_Omega
    sub_k_add_k_Omega
    add_k_sub_k_Omega
    sub_le_self_Omega
    sub_pos_iff_lt_Omega
  )

end SetUniverse
