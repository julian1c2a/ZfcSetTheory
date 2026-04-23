/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Arithmetic (Divisibility, GCD, LCM) on Von Neumann Natural Numbers

  This module defines divisibility on ω (the Von Neumann naturals), lifts it from
  the Peano isomorphism, and constructs GCD and LCM via Pattern B (bridge-only).

  ## Divisibility

  `divides m n` is defined directly in ZFC as `∃ k ∈ ω, n = mul m k`.
  The bridge theorem `fromPeano_divides` establishes the equivalence with Peano divisibility.
  Basic divisibility properties are lifted via the bridge.

  ## GCD and LCM (Pattern B)

  Both `gcdOf` and `lcmOf` are defined as:
    `gcdOf m n := fromPeano (Peano.Arith.gcd (toPeano m hm) (toPeano n hn))`
    `lcmOf m n := fromPeano (Peano.Arith.lcm (toPeano m hm) (toPeano n hn))`
  (defaulting to ∅ when m ∉ ω or n ∉ ω).

  ## Bézout (subtractive form)

  `bezout_natform_Omega` lifts the Peano subtractive Bézout identity:
    gcd(m, n) = a·m − b·n   or   gcd(m, n) = a·n − b·m  for some a, b ∈ ω.

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Nat.Basic
import ZFC.Axiom.Infinity
import ZFC.Induction.Recursion
import ZFC.Peano.Import
import ZFC.Nat.Add
import ZFC.Nat.Mul
import ZFC.Nat.Sub
import ZFC.Nat.Div
import PeanoNatLib.PeanoNatArith

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

  universe u
  variable {U : Type u}

  namespace Nat.Arith

    -- Restore ZFC set-membership notation: PeanoNatArith defines globally
    --   notation:50 a " ∈ " l => DList.Mem a l
    -- which shadows Membership.mem inside this file. Priority 100 wins.
    local notation:100 a " ∈ " b => @Membership.mem _ _ _ a b

    -- =========================================================================
    -- Section 0: Divisibility predicate (ZFC direct definition)
    -- =========================================================================

    /-- `divides m n` means `n` is a multiple of `m`: there exists `k ∈ ω` with `n = m * k`.
        This is the ZFC analogue of Peano divisibility. -/
    def divides (m n : U) : Prop :=
        ∃ (k : U) , ((k ∈ (ω : U)) ∧ (n = (mul m k)))

    -- =========================================================================
    -- Section 1: Bridge theorem — fromPeano commutes with divisibility
    -- =========================================================================

    /-- **Bridge**: Peano divisibility and ZFC divisibility coincide under `fromPeano`. -/
    theorem fromPeano_divides (p q : Peano.ℕ₀) :
        Peano.Arith.Divides p q ↔ divides (fromPeano p : U) (fromPeano q) := by
      constructor
      · -- Peano: ∃ k, q = p*k  →  ZFC: ∃ k ∈ ω, fromPeano q = mul (fromPeano p) k
        intro h_div
        obtain ⟨k, hk⟩ : ∃ k : Peano.ℕ₀, q = Peano.Mul.mul p k := h_div
        exact ⟨fromPeano k,
               Nat_in_Omega _ (fromPeano_is_nat k),
               by rw [← fromPeano_mul p k];
                  exact congrArg (fromPeano : Peano.ℕ₀ → U) hk⟩
      · -- ZFC: ∃ kz ∈ ω, fromPeano q = mul (fromPeano p) kz  →  Peano: ∃ k, q = p*k
        intro ⟨kz, hkz_in, hkz_eq⟩
        obtain ⟨k, hk⟩ := fromPeano_surjective kz (mem_Omega_is_Nat kz hkz_in)
        subst hk
        exact ⟨k, fromPeano_injective (hkz_eq.trans (fromPeano_mul p k).symm)⟩

    -- =========================================================================
    -- Section 2: Basic divisibility properties
    -- =========================================================================

    /-- `m ∣ m` for all `m ∈ ω`. -/
    theorem divides_refl_Omega (m : U) (hm : m ∈ (ω : U)) :
        divides m m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      subst hp
      exact (fromPeano_divides p p).mp (Peano.Arith.divides_refl p)

    /-- `1 = σ ∅` divides every `m ∈ ω`. -/
    theorem one_divides_Omega (m : U) (hm : m ∈ (ω : U)) :
        divides (σ (∅ : U)) m :=
      ⟨m, hm, (one_mul_Omega m hm).symm⟩

    /-- Every `m ∈ ω` divides `0 = ∅`. -/
    theorem divides_zero_Omega (m : U) (hm : m ∈ (ω : U)) :
        divides m ∅ :=
      ⟨∅, zero_in_Omega, (mul_zero m hm).symm⟩

    /-- `∅ ∣ n ↔ n = ∅` for `n ∈ ω`. -/
    theorem zero_divides_iff_Omega (n : U) (hn : n ∈ (ω : U)) :
        divides ∅ n ↔ n = ∅ := by
      constructor
      · intro ⟨k, hk_in, hk_eq⟩
        rw [zero_mul_Omega k hk_in] at hk_eq
        exact hk_eq
      · intro h
        subst h
        exact ⟨∅, zero_in_Omega, (zero_mul_Omega ∅ zero_in_Omega).symm⟩

    /-- Transitivity of divisibility. -/
    theorem divides_trans_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        divides m n → divides n k → divides m k := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      intro h1 h2
      rw [← fromPeano_divides p q] at h1
      rw [← fromPeano_divides q r] at h2
      exact (fromPeano_divides p r).mp (Peano.Arith.divides_trans h1 h2)

    /-- If `m ∣ n` then `m ∣ n * k`. -/
    theorem divides_mul_right_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        divides m n → divides m (mul n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      intro h
      rw [← fromPeano_divides p q] at h
      rw [← fromPeano_mul q r]
      exact (fromPeano_divides p (Peano.Mul.mul q r)).mp (Peano.Arith.divides_mul_right h)

    /-- If `m ∣ n` then `m ∣ k * n`. -/
    theorem divides_mul_left_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        divides m n → divides m (mul k n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      intro h
      rw [← fromPeano_divides p q] at h
      rw [← fromPeano_mul r q]
      exact (fromPeano_divides p (Peano.Mul.mul r q)).mp (Peano.Arith.divides_mul_left h)

    /-- If `m ∣ n` and `m ∣ k` then `m ∣ n + k`. -/
    theorem divides_add_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        divides m n → divides m k → divides m (add n k) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      intro h1 h2
      rw [← fromPeano_divides p q] at h1
      rw [← fromPeano_divides p r] at h2
      rw [← fromPeano_add q r]
      exact (fromPeano_divides p (Peano.Add.add q r)).mp (Peano.Arith.divides_add h1 h2)

    /-- If `n ∈ m` (i.e., `n < m`) and `k ∣ m` and `k ∣ n` then `k ∣ m − n`. -/
    theorem divides_sub_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h_lt : n ∈ m) (hdm : divides k m) (hdn : divides k n) :
        divides k (sub m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_divides r p] at hdm
      rw [← fromPeano_divides r q] at hdn
      rw [← fromPeano_sub p q]
      exact (fromPeano_divides r (Peano.Sub.sub p q)).mp
              (Peano.Arith.divides_sub ((fromPeano_lt_iff q p).mpr h_lt) hdm hdn)

    /-- If `k ∣ m` and `k ∣ n` then `k ∣ modOf m n`. -/
    theorem divides_modOf_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U))
        (hdm : divides k m) (hdn : divides k n) :
        divides k (modOf m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      rw [← fromPeano_divides r p] at hdm
      rw [← fromPeano_divides r q] at hdn
      rw [← fromPeano_mod p q]
      exact (fromPeano_divides r (Peano.Div.mod p q)).mp
              (Peano.Arith.divides_mod hdm hdn)

    /-- If `m ∣ n` and `n ≠ ∅` then `m ≤ n` (i.e., `m ∈ n ∨ m = n`). -/
    theorem divides_le_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        (divides m n) → (n ≠ ∅) → ((m ∈ n) ∨ (m = n)) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      intro h_div h_ne
      rw [← fromPeano_divides p q] at h_div
      have h_q_ne : q ≠ Peano.ℕ₀.zero := by
        intro heq; apply h_ne; subst heq
        have h1 := fromPeano_toPeano (∅ : U) (mem_Omega_is_Nat ∅ zero_in_Omega)
        rwa [toPeano_zero] at h1
      exact (fromPeano_le_iff p q).mp (Peano.Arith.divides_le h_div h_q_ne)

    /-- Antisymmetry of divisibility. -/
    theorem antisymm_divides_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divides m n → divides n m → m = n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      intro h1 h2
      rw [← fromPeano_divides p q] at h1
      rw [← fromPeano_divides q p] at h2
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (Peano.Arith.antisymm_divides h1 h2)

    -- =========================================================================
    -- Section 2.5: ZFC-native Euclidean division via RecursiveFn
    -- =========================================================================

    /-- The step function for the counting-up division algorithm.
        Maps `⟨q, r⟩ ↦ ⟨σ q, ∅⟩` when `σ r = n` (wrap: increment quotient, reset remainder),
        and `⟨q, r⟩ ↦ ⟨q, σ r⟩` otherwise (continue: just increment remainder).
        Applying this step `m` times from `⟨∅, ∅⟩` yields `⟨⌊m/n⌋, m mod n⟩`. -/
    private noncomputable def divMod_stepFn (n : U) : U :=
      sep ((ω ×ₛ ω) ×ₛ (ω ×ₛ ω)) (fun p =>
        ∃ q : U, (q ∈ (ω : U)) ∧ ∃ r : U, (r ∈ (ω : U)) ∧
          ((σ r = n ∧ p = ⟨⟨q, r⟩, ⟨σ q, (∅ : U)⟩⟩) ∨
           (σ r ≠ n ∧ p = ⟨⟨q, r⟩, ⟨q, σ r⟩⟩)))

    private theorem mem_divMod_stepFn_wrap (n q r : U)
        (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) (h_wrap : σ r = n) :
        (⟨⟨q, r⟩, ⟨σ q, ∅⟩⟩ : U) ∈ divMod_stepFn n := by
      unfold divMod_stepFn
      rw [mem_sep_iff]
      refine ⟨?_, q, hq, r, hr, Or.inl ⟨h_wrap, rfl⟩⟩
      rw [OrderedPair_mem_CartesianProduct]
      exact ⟨(OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩,
             (OrderedPair_mem_CartesianProduct (σ q) (∅ : U) ω ω).mpr
               ⟨succ_in_Omega q hq, zero_in_Omega⟩⟩

    private theorem mem_divMod_stepFn_continue (n q r : U)
        (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) (h_cont : σ r ≠ n) :
        (⟨⟨q, r⟩, ⟨q, σ r⟩⟩ : U) ∈ divMod_stepFn n := by
      unfold divMod_stepFn
      rw [mem_sep_iff]
      refine ⟨?_, q, hq, r, hr, Or.inr ⟨h_cont, rfl⟩⟩
      rw [OrderedPair_mem_CartesianProduct]
      exact ⟨(OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩,
             (OrderedPair_mem_CartesianProduct q (σ r) ω ω).mpr ⟨hq, succ_in_Omega r hr⟩⟩

    private theorem divMod_stepFn_is_function (n : U) :
        IsFunction (divMod_stepFn n) (ω ×ₛ ω) (ω ×ₛ ω) := by
      constructor
      · intro p hp
        unfold divMod_stepFn at hp
        rw [mem_sep_iff] at hp
        exact hp.1
      · intro x hx
        have hx_op : isOrderedPair x := ((CartesianProduct_is_specified ω ω x).mp hx).1
        have hq : fst x ∈ (ω : U) := ((CartesianProduct_is_specified ω ω x).mp hx).2.1
        have hr : snd x ∈ (ω : U) := ((CartesianProduct_is_specified ω ω x).mp hx).2.2
        have hx_eq : x = (⟨fst x, snd x⟩ : U) := OrderedPairSet_is_WellConstructed x hx_op
        by_cases h_wrap : σ (snd x) = n
        · -- Wrap case: unique output is ⟨σ (fst x), ∅⟩
          refine ⟨⟨σ (fst x), ∅⟩, ?_, fun y hy => ?_⟩
          · rw [hx_eq, fst_of_ordered_pair]
            exact mem_divMod_stepFn_wrap n (fst x) (snd x) hq hr h_wrap
          · dsimp only at hy
            unfold divMod_stepFn at hy
            rw [mem_sep_iff] at hy
            obtain ⟨_, q', hq', r', hr', hcase⟩ := hy
            rcases hcase with ⟨_, heq⟩ | ⟨h_nc, heq⟩
            · obtain ⟨hx_eq', hy_eq⟩ :=
                Eq_of_OrderedPairs_given_projections x y ⟨q', r'⟩ ⟨σ q', ∅⟩ heq
              obtain ⟨hq'_eq, _⟩ :=
                Eq_of_OrderedPairs_given_projections (fst x) (snd x) q' r'
                  (hx_eq.symm.trans hx_eq')
              rw [hy_eq, ← hq'_eq]
            · obtain ⟨hx_eq', _⟩ :=
                Eq_of_OrderedPairs_given_projections x y ⟨q', r'⟩ ⟨q', σ r'⟩ heq
              obtain ⟨_, hr'_eq⟩ :=
                Eq_of_OrderedPairs_given_projections (fst x) (snd x) q' r'
                  (hx_eq.symm.trans hx_eq')
              exact absurd (hr'_eq ▸ h_wrap) h_nc
        · -- Continue case: unique output is ⟨fst x, σ (snd x)⟩
          refine ⟨⟨fst x, σ (snd x)⟩, ?_, fun y hy => ?_⟩
          · rw [hx_eq, fst_of_ordered_pair, snd_of_ordered_pair]
            exact mem_divMod_stepFn_continue n (fst x) (snd x) hq hr h_wrap
          · dsimp only at hy
            unfold divMod_stepFn at hy
            rw [mem_sep_iff] at hy
            obtain ⟨_, q', hq', r', hr', hcase⟩ := hy
            rcases hcase with ⟨h_w, heq⟩ | ⟨_, heq⟩
            · obtain ⟨hx_eq', _⟩ :=
                Eq_of_OrderedPairs_given_projections x y ⟨q', r'⟩ ⟨σ q', ∅⟩ heq
              obtain ⟨_, hr'_eq⟩ :=
                Eq_of_OrderedPairs_given_projections (fst x) (snd x) q' r'
                  (hx_eq.symm.trans hx_eq')
              exact absurd (hr'_eq.symm ▸ h_w) h_wrap
            · obtain ⟨hx_eq', hy_eq⟩ :=
                Eq_of_OrderedPairs_given_projections x y ⟨q', r'⟩ ⟨q', σ r'⟩ heq
              obtain ⟨hq'_eq, hr'_eq⟩ :=
                Eq_of_OrderedPairs_given_projections (fst x) (snd x) q' r'
                  (hx_eq.symm.trans hx_eq')
              rw [hy_eq, ← hq'_eq, ← hr'_eq]

    /-- Applying `divMod_stepFn n` to `⟨q, r⟩` yields `⟨σ q, ∅⟩` in the wrap case. -/
    private theorem divMod_stepFn_apply_wrap (n q r : U)
        (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) (h_wrap : σ r = n) :
        apply (divMod_stepFn n) ⟨q, r⟩ = (⟨σ q, ∅⟩ : U) :=
      apply_eq (divMod_stepFn n) ⟨q, r⟩ ⟨σ q, ∅⟩
        ((divMod_stepFn_is_function n).2 ⟨q, r⟩
          ((OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩))
        (mem_divMod_stepFn_wrap n q r hq hr h_wrap)

    /-- Applying `divMod_stepFn n` to `⟨q, r⟩` yields `⟨q, σ r⟩` in the continue case. -/
    private theorem divMod_stepFn_apply_continue (n q r : U)
        (hq : q ∈ (ω : U)) (hr : r ∈ (ω : U)) (h_cont : σ r ≠ n) :
        apply (divMod_stepFn n) ⟨q, r⟩ = (⟨q, σ r⟩ : U) :=
      apply_eq (divMod_stepFn n) ⟨q, r⟩ ⟨q, σ r⟩
        ((divMod_stepFn_is_function n).2 ⟨q, r⟩
          ((OrderedPair_mem_CartesianProduct q r ω ω).mpr ⟨hq, hr⟩))
        (mem_divMod_stepFn_continue n q r hq hr h_cont)

    /-- `divModFn n hn` iterates the step function `m` times from `⟨∅, ∅⟩`,
        producing a ZFC function `ω → ω ×ₛ ω`. -/
    private noncomputable def divModFn (n : U) (_hn : n ∈ (ω : U)) : U :=
      RecursiveFn (ω ×ₛ ω) ⟨∅, ∅⟩ (divMod_stepFn n)
        ((OrderedPair_mem_CartesianProduct ∅ ∅ ω ω).mpr ⟨zero_in_Omega, zero_in_Omega⟩)
        (divMod_stepFn_is_function n)

    private theorem divModFn_is_function (n : U) (hn : n ∈ (ω : U)) :
        IsFunction (divModFn n hn) ω (ω ×ₛ ω) := by
      unfold divModFn
      exact RecursiveFn_is_function (ω ×ₛ ω) ⟨∅, ∅⟩ (divMod_stepFn n)
        ((OrderedPair_mem_CartesianProduct ∅ ∅ ω ω).mpr ⟨zero_in_Omega, zero_in_Omega⟩)
        (divMod_stepFn_is_function n)

    private theorem divModFn_zero (n : U) (hn : n ∈ (ω : U)) :
        apply (divModFn n hn) ∅ = (⟨∅, ∅⟩ : U) := by
      unfold divModFn
      exact RecursiveFn_zero (ω ×ₛ ω) ⟨∅, ∅⟩ (divMod_stepFn n)
        ((OrderedPair_mem_CartesianProduct ∅ ∅ ω ω).mpr ⟨zero_in_Omega, zero_in_Omega⟩)
        (divMod_stepFn_is_function n)

    private theorem divModFn_succ (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        apply (divModFn n hn) (σ m) =
          apply (divMod_stepFn n) (apply (divModFn n hn) m) := by
      unfold divModFn
      exact RecursiveFn_succ (ω ×ₛ ω) ⟨∅, ∅⟩ (divMod_stepFn n)
        ((OrderedPair_mem_CartesianProduct ∅ ∅ ω ω).mpr ⟨zero_in_Omega, zero_in_Omega⟩)
        (divMod_stepFn_is_function n) m hm

    private theorem divModFn_apply_in_prod (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) :
        apply (divModFn n hn) m ∈ (ω ×ₛ ω : U) := by
      have hf := divModFn_is_function n hn
      have h_pair := apply_mem (divModFn n hn) m (hf.2 m hm)
      exact ((OrderedPair_mem_CartesianProduct m (apply (divModFn n hn) m) ω (ω ×ₛ ω)).mp
        (hf.1 _ h_pair)).2

    /-- `div m n` is the Euclidean quotient of `m` by `n`, defined via ZFC recursion. -/
    noncomputable def div (m n : U) : U :=
      if _ : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          fst (apply (divModFn n hn) m)
        else ∅
      else ∅

    /-- `mod m n` is the Euclidean remainder of `m` by `n`, defined via ZFC recursion. -/
    noncomputable def mod (m n : U) : U :=
      if _ : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          snd (apply (divModFn n hn) m)
        else ∅
      else ∅

    theorem div_eq (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        div m n = fst (apply (divModFn n hn) m) := by
      simp only [div, dif_pos hm, dif_pos hn]

    theorem mod_eq (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mod m n = snd (apply (divModFn n hn) m) := by
      simp only [mod, dif_pos hm, dif_pos hn]

    theorem div_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        div m n ∈ (ω : U) := by
      rw [div_eq m n hm hn]
      exact ((CartesianProduct_is_specified ω ω _).mp
        (divModFn_apply_in_prod n m hn hm)).2.1

    theorem mod_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mod m n ∈ (ω : U) := by
      rw [mod_eq m n hm hn]
      exact ((CartesianProduct_is_specified ω ω _).mp
        (divModFn_apply_in_prod n m hn hm)).2.2

    /-- The combined pair: `apply (divModFn n hn) m = ⟨div m n, mod m n⟩`. -/
    private theorem div_mod_pair (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        apply (divModFn n hn) m = (⟨div m n, mod m n⟩ : U) := by
      have h_in := divModFn_apply_in_prod n m hn hm
      have h_op : isOrderedPair (apply (divModFn n hn) m) :=
        ((CartesianProduct_is_specified ω ω _).mp h_in).1
      rw [div_eq m n hm hn, mod_eq m n hm hn]
      exact OrderedPairSet_is_WellConstructed _ h_op

    /-- `div ∅ n = ∅` for all `n ∈ ω`. -/
    theorem div_zero_left (n : U) (hn : n ∈ (ω : U)) : div ∅ n = ∅ := by
      rw [div_eq ∅ n zero_in_Omega hn, divModFn_zero n hn, fst_of_ordered_pair]

    /-- `mod ∅ n = ∅` for all `n ∈ ω`. -/
    theorem mod_zero_left (n : U) (hn : n ∈ (ω : U)) : mod ∅ n = ∅ := by
      rw [mod_eq ∅ n zero_in_Omega hn, divModFn_zero n hn, snd_of_ordered_pair]

    /-- Successor step — wrap case: when `σ (mod m n) = n`, `div (σ m) n = σ (div m n)`. -/
    theorem div_succ_wrap (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_wrap : σ (mod m n) = n) :
        div (σ m) n = σ (div m n) := by
      rw [div_eq (σ m) n (succ_in_Omega m hm) hn, divModFn_succ n m hn hm,
          div_mod_pair m n hm hn,
          divMod_stepFn_apply_wrap n (div m n) (mod m n)
            (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn) h_wrap,
          fst_of_ordered_pair]

    /-- Successor step — wrap case: when `σ (mod m n) = n`, `mod (σ m) n = ∅`. -/
    theorem mod_succ_wrap (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_wrap : σ (mod m n) = n) :
        mod (σ m) n = ∅ := by
      rw [mod_eq (σ m) n (succ_in_Omega m hm) hn, divModFn_succ n m hn hm,
          div_mod_pair m n hm hn,
          divMod_stepFn_apply_wrap n (div m n) (mod m n)
            (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn) h_wrap,
          snd_of_ordered_pair]

    /-- Successor step — continue case: when `σ (mod m n) ≠ n`, `div (σ m) n = div m n`. -/
    theorem div_succ_continue (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_cont : σ (mod m n) ≠ n) :
        div (σ m) n = div m n := by
      rw [div_eq (σ m) n (succ_in_Omega m hm) hn, divModFn_succ n m hn hm,
          div_mod_pair m n hm hn,
          divMod_stepFn_apply_continue n (div m n) (mod m n)
            (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn) h_cont,
          fst_of_ordered_pair]

    /-- Successor step — continue case: when `σ (mod m n) ≠ n`, `mod (σ m) n = σ (mod m n)`. -/
    theorem mod_succ_continue (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_cont : σ (mod m n) ≠ n) :
        mod (σ m) n = σ (mod m n) := by
      rw [mod_eq (σ m) n (succ_in_Omega m hm) hn, divModFn_succ n m hn hm,
          div_mod_pair m n hm hn,
          divMod_stepFn_apply_continue n (div m n) (mod m n)
            (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn) h_cont,
          snd_of_ordered_pair]

    /-- **Euclidean correctness** of the ZFC-native `div`/`mod`: for `n ≠ ∅`,
        after `m` steps from zero, `m = (div m n) * n + (mod m n)` and `mod m n ∈ n`. -/
    private theorem divMod_ZFC_correct (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_pos : n ≠ ∅) :
        m = add (mul (div m n) n) (mod m n) ∧ mod m n ∈ n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      clear hm hn
      have hq_om : fromPeano q ∈ (ω : U) := Nat_in_Omega _ (fromPeano_is_nat q)
      induction p with
      | zero =>
        simp only [fromPeano]
        rw [div_zero_left (fromPeano q) hq_om, mod_zero_left (fromPeano q) hq_om]
        exact ⟨by rw [zero_mul_Omega (fromPeano q) hq_om, add_zero ∅ zero_in_Omega],
               zero_mem_of_nat_nonempty _ (fromPeano_is_nat q) h_pos⟩
      | succ p' ih =>
        -- Use Nat.Basic.succ (fully qualified) to avoid σ notation ambiguity
        -- with PeanoNatLib's σ n:max notation
        have hfp_succ : (fromPeano (Peano.ℕ₀.succ p') : U) =
            Nat.Basic.succ (fromPeano p') := by simp only [fromPeano]
        rw [hfp_succ]
        have hm' : fromPeano p' ∈ (ω : U) := Nat_in_Omega _ (fromPeano_is_nat p')
        obtain ⟨ih_eq, ih_mod_lt⟩ := ih
        have hd := div_in_Omega (fromPeano p') (fromPeano q) hm' hq_om
        have hr := mod_in_Omega (fromPeano p') (fromPeano q) hm' hq_om
        rcases Classical.em
            (Nat.Basic.succ (mod (fromPeano p') (fromPeano q)) = fromPeano q)
            with h_wrap | h_wrap
        · -- Wrap: quotient increments, remainder resets to ∅
          rw [div_succ_wrap (fromPeano p') (fromPeano q) hm' hq_om h_wrap,
              mod_succ_wrap (fromPeano p') (fromPeano q) hm' hq_om h_wrap]
          constructor
          · symm
            calc add (mul (Nat.Basic.succ (div (fromPeano p') (fromPeano q)))
                      (fromPeano q)) (∅ : U)
                = mul (Nat.Basic.succ (div (fromPeano p') (fromPeano q)))
                      (fromPeano q) :=
                    add_zero _ (mul_in_Omega _ _ (succ_in_Omega _ hd) hq_om)
              _ = add (mul (div (fromPeano p') (fromPeano q)) (fromPeano q)) (fromPeano q) :=
                    succ_mul_Omega _ _ hd hq_om
              _ = add (mul (div (fromPeano p') (fromPeano q)) (fromPeano q))
                      (Nat.Basic.succ (mod (fromPeano p') (fromPeano q))) :=
                    by rw [h_wrap]
              _ = Nat.Basic.succ
                      (add (mul (div (fromPeano p') (fromPeano q)) (fromPeano q))
                      (mod (fromPeano p') (fromPeano q))) :=
                    add_succ _ _ (mul_in_Omega _ _ hd hq_om) hr
              _ = Nat.Basic.succ (fromPeano p') :=
                    (congrArg Nat.Basic.succ ih_eq).symm
          · exact zero_mem_of_nat_nonempty _ (fromPeano_is_nat q) h_pos
        · -- Continue: quotient unchanged, remainder increments
          rw [div_succ_continue (fromPeano p') (fromPeano q) hm' hq_om h_wrap,
              mod_succ_continue (fromPeano p') (fromPeano q) hm' hq_om h_wrap]
          constructor
          · rw [add_succ _ _ (mul_in_Omega _ _ hd hq_om) hr]
            exact congrArg Nat.Basic.succ ih_eq
          · -- Nat.Basic.succ (mod p' q) ∈ fromPeano q
            have h_succ_in_succ :=
              (succ_mem_succ_iff (mod (fromPeano p') (fromPeano q)) (fromPeano q)
                (mem_Omega_is_Nat _ hr) (fromPeano_is_nat q)).mp ih_mod_lt
            exact ((mem_succ_iff (fromPeano q)
              (Nat.Basic.succ (mod (fromPeano p') (fromPeano q)))).mp
              h_succ_in_succ).resolve_right h_wrap

    /-- The Euclidean equation for ZFC-native division: `m = (div m n)*n + (mod m n)`. -/
    theorem divMod_eq_ZFC (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h : n ≠ ∅) :
        m = add (mul (div m n) n) (mod m n) :=
      (divMod_ZFC_correct m n hm hn h).1

    /-- The remainder bound: `mod m n ∈ n` (i.e., `mod m n < n`). -/
    theorem mod_lt_divisor_ZFC (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h : n ≠ ∅) :
        mod m n ∈ n :=
      (divMod_ZFC_correct m n hm hn h).2

    /-- Uniqueness of Euclidean division in Peano: if `p = r₁*q + s₁ = r₂*q + s₂`
        with `s₁, s₂ < q`, then `r₁ = r₂` and `s₁ = s₂`. -/
    private theorem peano_euclid_unique (p q r1 s1 r2 s2 : Peano.ℕ₀)
        (hq : Peano.StrictOrder.Lt Peano.ℕ₀.zero q)
        (h1 : p = Peano.Add.add (Peano.Mul.mul r1 q) s1)
        (hs1 : Peano.StrictOrder.Lt s1 q)
        (h2 : p = Peano.Add.add (Peano.Mul.mul r2 q) s2)
        (hs2 : Peano.StrictOrder.Lt s2 q) :
        r1 = r2 ∧ s1 = s2 := by
      have hr1_le : Peano.Order.Le (Peano.Mul.mul r1 q) p := by
        rw [h1]; exact Peano.Add.le_self_add (Peano.Mul.mul r1 q) s1
      have hr1_lt : Peano.StrictOrder.Lt p (Peano.Mul.mul (Peano.ℕ₀.succ r1) q) := by
        rw [h1, Peano.Mul.succ_mul]
        exact (Peano.Add.add_lt_add_left_iff (Peano.Mul.mul r1 q) s1 q).mpr hs1
      have hr2_le : Peano.Order.Le (Peano.Mul.mul r2 q) p := by
        rw [h2]; exact Peano.Add.le_self_add (Peano.Mul.mul r2 q) s2
      have hr2_lt : Peano.StrictOrder.Lt p (Peano.Mul.mul (Peano.ℕ₀.succ r2) q) := by
        rw [h2, Peano.Mul.succ_mul]
        exact (Peano.Add.add_lt_add_left_iff (Peano.Mul.mul r2 q) s2 q).mpr hs2
      obtain ⟨k, ⟨_, _⟩, huniq⟩ :=
        Peano.Mul.exists_unique_mul_le_and_lt_succ_mul q p hq
      have hr1_k : r1 = k := huniq r1 ⟨hr1_le, hr1_lt⟩
      have hr2_k : r2 = k := huniq r2 ⟨hr2_le, hr2_lt⟩
      have hr_eq : r1 = r2 := hr1_k.trans hr2_k.symm
      constructor
      · exact hr_eq
      · have heq : Peano.Add.add (Peano.Mul.mul r1 q) s1 =
                   Peano.Add.add (Peano.Mul.mul r1 q) s2 := by
          have := h1.symm.trans h2
          rw [← hr_eq] at this
          exact this
        exact Peano.Add.add_cancelation (Peano.Mul.mul r1 q) s1 s2 heq

    /-- ZFC uniqueness of Euclidean division: two representations `m = d₁*n + r₁ = d₂*n + r₂`
        with remainders in `n` must be equal. -/
    private theorem euclid_unique_ZFC (m n d1 r1 d2 r2 : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (hd1 : d1 ∈ (ω : U)) (hr1 : r1 ∈ (ω : U))
        (hd2 : d2 ∈ (ω : U)) (hr2 : r2 ∈ (ω : U))
        (h_pos : n ≠ ∅)
        (h1 : m = add (mul d1 n) r1) (hr1_lt : r1 ∈ n)
        (h2 : m = add (mul d2 n) r2) (hr2_lt : r2 ∈ n) :
        d1 = d2 ∧ r1 = r2 := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨a1, ha1⟩ := fromPeano_surjective d1 (mem_Omega_is_Nat d1 hd1)
      obtain ⟨b1, hb1⟩ := fromPeano_surjective r1 (mem_Omega_is_Nat r1 hr1)
      obtain ⟨a2, ha2⟩ := fromPeano_surjective d2 (mem_Omega_is_Nat d2 hd2)
      obtain ⟨b2, hb2⟩ := fromPeano_surjective r2 (mem_Omega_is_Nat r2 hr2)
      subst hp; subst hq; subst ha1; subst hb1; subst ha2; subst hb2
      have h1_p : p = Peano.Add.add (Peano.Mul.mul a1 q) b1 :=
        fromPeano_injective (h1.trans (by rw [fromPeano_add, fromPeano_mul]))
      have h2_p : p = Peano.Add.add (Peano.Mul.mul a2 q) b2 :=
        fromPeano_injective (h2.trans (by rw [fromPeano_add, fromPeano_mul]))
      have hq_pos : Peano.StrictOrder.Lt Peano.ℕ₀.zero q :=
        (fromPeano_lt_iff Peano.ℕ₀.zero q).mpr
          (show (fromPeano Peano.ℕ₀.zero : U) ∈ fromPeano q from
            zero_mem_of_nat_nonempty _ (fromPeano_is_nat q) h_pos)
      have hb1_lt : Peano.StrictOrder.Lt b1 q := (fromPeano_lt_iff b1 q).mpr hr1_lt
      have hb2_lt : Peano.StrictOrder.Lt b2 q := (fromPeano_lt_iff b2 q).mpr hr2_lt
      obtain ⟨ha_eq, hb_eq⟩ :=
        peano_euclid_unique p q a1 b1 a2 b2 hq_pos h1_p hb1_lt h2_p hb2_lt
      exact ⟨congrArg (fromPeano : Peano.ℕ₀ → U) ha_eq,
             congrArg (fromPeano : Peano.ℕ₀ → U) hb_eq⟩

    /-- **Bridge**: ZFC-native `div` equals `divOf` (the Pattern-B definition). -/
    theorem div_eq_divOf (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_pos : n ≠ ∅) :
        div m n = divOf m n :=
      (euclid_unique_ZFC m n (div m n) (mod m n) (divOf m n) (modOf m n)
        hm hn (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn)
        (divOf_in_Omega m n hm hn) (modOf_in_Omega m n hm hn)
        h_pos (divMod_eq_ZFC m n hm hn h_pos) (mod_lt_divisor_ZFC m n hm hn h_pos)
        (divMod_eq_Omega m n hm hn h_pos) (mod_lt_divisor_Omega m n hm hn h_pos)).1

    /-- **Bridge**: ZFC-native `mod` equals `modOf` (the Pattern-B definition). -/
    theorem mod_eq_modOf (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_pos : n ≠ ∅) :
        mod m n = modOf m n :=
      (euclid_unique_ZFC m n (div m n) (mod m n) (divOf m n) (modOf m n)
        hm hn (div_in_Omega m n hm hn) (mod_in_Omega m n hm hn)
        (divOf_in_Omega m n hm hn) (modOf_in_Omega m n hm hn)
        h_pos (divMod_eq_ZFC m n hm hn h_pos) (mod_lt_divisor_ZFC m n hm hn h_pos)
        (divMod_eq_Omega m n hm hn h_pos) (mod_lt_divisor_Omega m n hm hn h_pos)).2

    -- =========================================================================
    -- Section 3: GCD and LCM via Pattern B (bridge-only)
    -- =========================================================================

    /-- Proof-irrelevance for `toPeano`. -/
    private theorem toPeano_proof_irrel (n : U) (h1 h2 : IsNat n) :
        toPeano n h1 = toPeano n h2 :=
      fromPeano_injective
        ((fromPeano_toPeano n h1).trans (fromPeano_toPeano n h2).symm)

    /-- `gcdOf m n` is the greatest common divisor of `m` and `n` in ω. -/
    noncomputable def gcdOf (m n : U) : U :=
      if hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          fromPeano (Peano.Arith.gcd (toPeano m (mem_Omega_is_Nat m hm))
                                      (toPeano n (mem_Omega_is_Nat n hn)))
        else ∅
      else ∅

    /-- `lcmOf m n` is the least common multiple of `m` and `n` in ω. -/
    noncomputable def lcmOf (m n : U) : U :=
      if hm : m ∈ (ω : U) then
        if hn : n ∈ (ω : U) then
          fromPeano (Peano.Arith.lcm (toPeano m (mem_Omega_is_Nat m hm))
                                      (toPeano n (mem_Omega_is_Nat n hn)))
        else ∅
      else ∅

    /-- `gcdOf m n ∈ ω`. -/
    theorem gcdOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        gcdOf m n ∈ (ω : U) := by
      simp only [gcdOf, dif_pos hm, dif_pos hn]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    /-- `lcmOf m n ∈ ω`. -/
    theorem lcmOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        lcmOf m n ∈ (ω : U) := by
      simp only [lcmOf, dif_pos hm, dif_pos hn]
      exact Nat_in_Omega _ (fromPeano_is_nat _)

    -- =========================================================================
    -- Section 4: Bridge theorems for gcdOf and lcmOf
    -- =========================================================================

    /-- **Bridge**: `fromPeano` commutes with GCD. -/
    theorem fromPeano_gcd (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Arith.gcd p q) : U) = gcdOf (fromPeano p) (fromPeano q) := by
      simp only [gcdOf, dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
                          dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · symm
        exact (toPeano_proof_irrel _ _ (fromPeano_is_nat p)).trans (toPeano_fromPeano p)
      · symm
        exact (toPeano_proof_irrel _ _ (fromPeano_is_nat q)).trans (toPeano_fromPeano q)

    /-- **Bridge**: `fromPeano` commutes with LCM. -/
    theorem fromPeano_lcm (p q : Peano.ℕ₀) :
        (fromPeano (Peano.Arith.lcm p q) : U) = lcmOf (fromPeano p) (fromPeano q) := by
      simp only [lcmOf, dif_pos (Nat_in_Omega _ (fromPeano_is_nat p)),
                         dif_pos (Nat_in_Omega _ (fromPeano_is_nat q))]
      congr 1; congr 1
      · symm
        exact (toPeano_proof_irrel _ _ (fromPeano_is_nat p)).trans (toPeano_fromPeano p)
      · symm
        exact (toPeano_proof_irrel _ _ (fromPeano_is_nat q)).trans (toPeano_fromPeano q)

    -- =========================================================================
    -- Private helpers: work around identifiers now private in peanolib v4.29.0
    -- =========================================================================

    /-- `div 0 b = 0` for all `b`. Used in the zero-case of `peano_lcm_div_left`. -/
    private theorem peano_div_zero_left (b : Peano.ℕ₀) :
        Peano.Div.div Peano.ℕ₀.zero b = Peano.ℕ₀.zero := by
      unfold Peano.Div.div Peano.Div.divMod
      by_cases hb : b = Peano.ℕ₀.zero
      · rw [dif_pos hb]
      · rw [dif_neg hb, dif_pos rfl]

    /-- `gcd p q ∣ p` — replaces private `Peano.Arith.gcd_divides_left`. -/
    private theorem peano_gcd_div_left (p q : Peano.ℕ₀) :
        Peano.Arith.Divides (Peano.Arith.gcd p q) p := by
      have h := Peano.Arith.gcd_divides_linear_combo p q 𝟙 𝟘
      simp only [Peano.Mul.mul_one, Peano.Mul.mul_zero, Peano.Add.add_zero] at h
      exact h

    /-- `gcd p q ∣ q` — replaces private `Peano.Arith.gcd_divides_right`. -/
    private theorem peano_gcd_div_right (p q : Peano.ℕ₀) :
        Peano.Arith.Divides (Peano.Arith.gcd p q) q := by
      have h := Peano.Arith.gcd_divides_linear_combo p q 𝟘 𝟙
      simp only [Peano.Mul.mul_zero, Peano.Add.zero_add, Peano.Mul.mul_one] at h
      exact h

    /-- `gcd p q = gcd q p` — replaces private `Peano.Arith.gcd_comm`. -/
    private theorem peano_gcd_comm (p q : Peano.ℕ₀) :
        Peano.Arith.gcd p q = Peano.Arith.gcd q p :=
      Peano.Arith.antisymm_divides
        (Peano.Arith.gcd_greatest q p (Peano.Arith.gcd p q)
          ⟨peano_gcd_div_right p q, peano_gcd_div_left p q⟩)
        (Peano.Arith.gcd_greatest p q (Peano.Arith.gcd q p)
          ⟨peano_gcd_div_right q p, peano_gcd_div_left q p⟩)

    /-- `p ∣ lcm p q` — replaces missing `Peano.Arith.lcm_multiple_left`. -/
    private theorem peano_lcm_div_left (p q : Peano.ℕ₀) :
        Peano.Arith.Divides p (Peano.Arith.lcm p q) := by
      obtain ⟨k, hk⟩ := peano_gcd_div_right p q
      unfold Peano.Arith.lcm
      by_cases hg : Peano.Arith.gcd p q = Peano.ℕ₀.zero
      · -- gcd = 0 → 0 ∣ p → p = 0; then lcm 0 q = div 0 _ = 0 and 0 ∣ 0
        have hp_zero : p = Peano.ℕ₀.zero := by
          obtain ⟨k', hk'⟩ : Peano.Arith.Divides Peano.ℕ₀.zero p := hg ▸ peano_gcd_div_left p q
          simp only [Peano.Mul.zero_mul] at hk'; exact hk'
        rw [hp_zero, Peano.Mul.zero_mul, peano_div_zero_left]
        exact Peano.Arith.divides_refl Peano.ℕ₀.zero
      · -- mul p q = mul (gcd p q) (mul p k)
        have hmul : Peano.Mul.mul p q =
            Peano.Mul.mul (Peano.Arith.gcd p q) (Peano.Mul.mul p k) :=
          calc Peano.Mul.mul p q
              = Peano.Mul.mul p (Peano.Mul.mul (Peano.Arith.gcd p q) k) :=
                    congrArg (Peano.Mul.mul p) hk
            _ = Peano.Mul.mul (Peano.Mul.mul p (Peano.Arith.gcd p q)) k :=
                  (Peano.Mul.mul_assoc (Peano.Arith.gcd p q) p k).symm
            _ = Peano.Mul.mul (Peano.Mul.mul (Peano.Arith.gcd p q) p) k := by
                  rw [Peano.Mul.mul_comm p (Peano.Arith.gcd p q)]
            _ = Peano.Mul.mul (Peano.Arith.gcd p q) (Peano.Mul.mul p k) :=
                  Peano.Mul.mul_assoc p (Peano.Arith.gcd p q) k
        -- mod (mul p q) (gcd p q) = 0
        have hmod_zero : Peano.Div.mod (Peano.Mul.mul p q) (Peano.Arith.gcd p q) =
            Peano.ℕ₀.zero :=
          Classical.byContradiction fun hne =>
            Peano.Order.le_not_lt
              (Peano.Arith.divides_le
                (Peano.Arith.divides_mod ⟨Peano.Mul.mul p k, hmul⟩
                  (Peano.Arith.divides_refl (Peano.Arith.gcd p q)))
                hne)
              (Peano.Div.mod_lt_divisor (Peano.Mul.mul p q) (Peano.Arith.gcd p q) hg)
        -- div (mul p q) (gcd p q) = mul p k (by cancellation)
        have hdiv : Peano.Div.div (Peano.Mul.mul p q) (Peano.Arith.gcd p q) =
            Peano.Mul.mul p k := by
          apply Peano.Mul.mul_cancelation_left (Peano.Arith.gcd p q) _ _ hg
          have heq : Peano.Mul.mul p q =
              Peano.Add.add
                (Peano.Mul.mul
                  (Peano.Div.div (Peano.Mul.mul p q) (Peano.Arith.gcd p q))
                  (Peano.Arith.gcd p q))
                (Peano.Div.mod (Peano.Mul.mul p q) (Peano.Arith.gcd p q)) := by
            simp only [Peano.Div.div, Peano.Div.mod]
            exact Peano.Div.divMod_eq (Peano.Mul.mul p q) (Peano.Arith.gcd p q) hg
          rw [hmod_zero, Peano.Add.add_zero] at heq
          calc Peano.Mul.mul (Peano.Arith.gcd p q)
                  (Peano.Div.div (Peano.Mul.mul p q) (Peano.Arith.gcd p q))
              = Peano.Mul.mul
                  (Peano.Div.div (Peano.Mul.mul p q) (Peano.Arith.gcd p q))
                  (Peano.Arith.gcd p q) := Peano.Mul.mul_comm _ _
            _ = Peano.Mul.mul p q := heq.symm
            _ = Peano.Mul.mul (Peano.Arith.gcd p q) (Peano.Mul.mul p k) := hmul
        rw [hdiv]
        exact ⟨k, rfl⟩

    /-- `lcm p q = lcm q p` — replaces missing `Peano.Arith.lcm_comm`. -/
    private theorem peano_lcm_comm (p q : Peano.ℕ₀) :
        Peano.Arith.lcm p q = Peano.Arith.lcm q p := by
      unfold Peano.Arith.lcm
      rw [Peano.Mul.mul_comm p q, peano_gcd_comm p q]

    /-- `q ∣ lcm p q` — replaces missing `Peano.Arith.lcm_multiple_right`. -/
    private theorem peano_lcm_div_right (p q : Peano.ℕ₀) :
        Peano.Arith.Divides q (Peano.Arith.lcm p q) := by
      rw [peano_lcm_comm]; exact peano_lcm_div_left q p

    -- =========================================================================
    -- Section 5: Algebraic properties of gcdOf
    -- =========================================================================

    /-- `gcdOf m n ∣ m`. -/
    theorem gcdOf_divides_left_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divides (gcdOf m n) m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_gcd p q]
      exact (fromPeano_divides (Peano.Arith.gcd p q) p).mp (peano_gcd_div_left p q)

    /-- `gcdOf m n ∣ n`. -/
    theorem gcdOf_divides_right_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divides (gcdOf m n) n := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_gcd p q]
      exact (fromPeano_divides (Peano.Arith.gcd p q) q).mp (peano_gcd_div_right p q)

    /-- Universal property of GCD: if `k ∣ m` and `k ∣ n` then `k ∣ gcdOf m n`. -/
    theorem gcdOf_greatest_Omega (m n k : U) (hm : m ∈ (ω : U))
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        divides k m → divides k n → divides k (gcdOf m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, hr⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      subst hp; subst hq; subst hr
      intro h1 h2
      rw [← fromPeano_divides r p] at h1
      rw [← fromPeano_divides r q] at h2
      rw [← fromPeano_gcd p q]
      exact (fromPeano_divides r (Peano.Arith.gcd p q)).mp
              (Peano.Arith.gcd_greatest p q r ⟨h1, h2⟩)

    /-- `gcdOf m n = gcdOf n m`. -/
    theorem gcdOf_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        gcdOf m n = gcdOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_gcd p q, ← fromPeano_gcd q p]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (peano_gcd_comm p q)

    -- =========================================================================
    -- Section 6: Algebraic properties of lcmOf
    -- =========================================================================

    /-- `m ∣ lcmOf m n`. -/
    theorem lcmOf_multiple_left_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divides m (lcmOf m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_lcm p q]
      exact (fromPeano_divides p (Peano.Arith.lcm p q)).mp (peano_lcm_div_left p q)

    /-- `n ∣ lcmOf m n`. -/
    theorem lcmOf_multiple_right_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        divides n (lcmOf m n) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_lcm p q]
      exact (fromPeano_divides q (Peano.Arith.lcm p q)).mp (peano_lcm_div_right p q)

    /-- `lcmOf m n = lcmOf n m`. -/
    theorem lcmOf_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        lcmOf m n = lcmOf n m := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      rw [← fromPeano_lcm p q, ← fromPeano_lcm q p]
      exact congrArg (fromPeano : Peano.ℕ₀ → U) (peano_lcm_comm p q)

    -- =========================================================================
    -- Section 7: Bézout identity (subtractive form)
    -- =========================================================================

    /-- **Bézout (subtractive form)**: for `m n ∈ ω`, there exist `a b ∈ ω` such that
        `gcdOf m n = a·m − b·n` or `gcdOf m n = a·n − b·m`. -/
    theorem bezout_natform_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        ∃ a b : U, (a ∈ (ω : U)) ∧ (b ∈ (ω : U)) ∧
          (gcdOf m n = sub (mul a m) (mul b n) ∨
           gcdOf m n = sub (mul a n) (mul b m)) := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      obtain ⟨np, mp, h⟩ := Peano.Arith.bezout_natform p q
      refine ⟨fromPeano np, fromPeano mp,
              Nat_in_Omega _ (fromPeano_is_nat np),
              Nat_in_Omega _ (fromPeano_is_nat mp), ?_⟩
      rcases h with h | h
      · left
        rw [← fromPeano_gcd p q,
            ← fromPeano_mul np p, ← fromPeano_mul mp q,
            ← fromPeano_sub (Peano.Mul.mul np p) (Peano.Mul.mul mp q)]
        exact congrArg (fromPeano : Peano.ℕ₀ → U) h
      · right
        rw [← fromPeano_gcd p q,
            ← fromPeano_mul np q, ← fromPeano_mul mp p,
            ← fromPeano_sub (Peano.Mul.mul np q) (Peano.Mul.mul mp p)]
        exact congrArg (fromPeano : Peano.ℕ₀ → U) h

  end Nat.Arith

  export Nat.Arith (
    -- Section 0: divisibility predicate
    divides
    -- Section 1: bridge
    fromPeano_divides
    -- Section 2: basic properties
    divides_refl_Omega
    one_divides_Omega
    divides_zero_Omega
    zero_divides_iff_Omega
    divides_trans_Omega
    divides_mul_right_Omega
    divides_mul_left_Omega
    divides_add_Omega
    divides_sub_Omega
    divides_modOf_Omega
    divides_le_Omega
    antisymm_divides_Omega
    -- Section 2.5: ZFC-native div/mod
    div
    mod
    div_eq
    mod_eq
    div_in_Omega
    mod_in_Omega
    div_zero_left
    mod_zero_left
    div_succ_wrap
    mod_succ_wrap
    div_succ_continue
    mod_succ_continue
    divMod_eq_ZFC
    mod_lt_divisor_ZFC
    div_eq_divOf
    mod_eq_modOf
    -- Section 3: gcdOf, lcmOf definitions
    gcdOf
    lcmOf
    gcdOf_in_Omega
    lcmOf_in_Omega
    -- Section 4: bridge for gcd/lcm
    fromPeano_gcd
    fromPeano_lcm
    -- Section 5: gcdOf properties
    gcdOf_divides_left_Omega
    gcdOf_divides_right_Omega
    gcdOf_greatest_Omega
    gcdOf_comm_Omega
    -- Section 6: lcmOf properties
    lcmOf_multiple_left_Omega
    lcmOf_multiple_right_Omega
    lcmOf_comm_Omega
    -- Section 7: Bézout
    bezout_natform_Omega
  )

end ZFC
