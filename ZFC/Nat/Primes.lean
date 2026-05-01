/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Primes and Fundamental Theorem of Arithmetic on Von Neumann Natural Numbers

  This module defines a ZFC-native notion of primality on ω and lifts
  the Fundamental Theorem of Arithmetic from peanolib via the isomorphism ΠZ/ZΠ.

  ## Strategy (Approach A: DList stays on Peano side)

  We define `isPrime p` as a ZFC proposition (p ∈ ω, p ≠ ∅, p ≠ σ ∅, and
  p is Euclid-prime under ZFC divisibility).  The bridge theorem
  `fromPeano_prime` connects this to `Peano.Arith.Prime`.

  The TFA theorems keep `DList ℕ₀` on the Peano side:
    `exists_prime_factorization_ZFC`:
        ∃ ps : DList ℕ₀, PrimeList ps ∧ (fromPeano (product_list ps) : U) = n
    `unique_prime_factorization_ZFC`:
        uniqueness by equal multiplicity for each prime (Peano counting).

  ## Main Results

  - `isPrime p` — ZFC-native primality
  - `fromPeano_prime` — bridge: Peano.Arith.Prime p ↔ isPrime (fromPeano p)
  - `isPrime_in_Omega`, `isPrime_ne_zero`, `isPrime_ne_one`, `isPrime_ge_two`
  - `isPrime_prime_divisors` — if d ∣ p and isPrime p, then d = σ ∅ or d = p
  - `exists_prime_divisor_ZFC` — every n ≥ 2 in ω has a ZFC-prime divisor
  - `exists_prime_factorization_ZFC` — TFA existence (Approach A)
  - `unique_prime_factorization_ZFC` — TFA uniqueness (Approach A)

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
import ZFC.Nat.Arith
import ZFC.Nat.Gcd
import PeanoNatLib.PeanoNatPrimes

namespace ZFC
  open Classical

  universe u
  variable {U : Type u}

  namespace Nat.Primes

    -- =========================================================================
    -- §1  ZFC-native definition of isPrime
    -- =========================================================================

    /-- `p` is a ZFC-prime if: `p ∈ ω`, `p ≠ ∅`, `p ≠ σ ∅`, and for all `a b ∈ ω`,
        `divides p (mul a b) → divides p a ∨ divides p b`. -/
    def isPrime (p : U) : Prop :=
      mem p (ω : U) ∧ p ≠ (∅ : U) ∧ p ≠ σ (∅ : U) ∧
      ∀ a b : U, mem a (ω : U) → mem b (ω : U) →
        divides p (mul a b) → divides p a ∨ divides p b

    -- =========================================================================
    -- §2  Private helpers: fromPeano values at 0, 1, 2
    -- =========================================================================

    /-- `fromPeano 𝟘 = ∅` in U. -/
    private theorem fromPeano_zero_eq : (fromPeano Peano.ℕ₀.zero : U) = ∅ := by
      simp only [fromPeano]

    /-- `fromPeano 𝟙 = σ ∅` in U. -/
    private theorem fromPeano_one_eq : (fromPeano 𝟙 : U) = σ (∅ : U) := by
      show (fromPeano (Peano.ℕ₀.succ Peano.ℕ₀.zero) : U) = σ (∅ : U)
      simp only [fromPeano]

    /-- `fromPeano 𝟚 = σ (σ ∅)` in U. -/
    private theorem fromPeano_two_eq : (fromPeano 𝟚 : U) = σ (σ (∅ : U)) := by
      show (fromPeano (Peano.ℕ₀.succ (Peano.ℕ₀.succ Peano.ℕ₀.zero)) : U) = σ (σ (∅ : U))
      simp only [fromPeano]

    -- =========================================================================
    -- §3  Bridge theorem: Peano.Arith.Prime p ↔ isPrime (fromPeano p)
    -- =========================================================================

    /-- **Bridge theorem**: Peano primality coincides with ZFC primality
        under `fromPeano`. -/
    theorem fromPeano_prime (p : Peano.ℕ₀) :
        Peano.Arith.Prime p ↔ isPrime (fromPeano p : U) := by
      constructor
      · intro hp
        unfold isPrime
        refine ⟨Nat_in_Omega _ (fromPeano_is_nat p), ?_, ?_, ?_⟩
        · -- fromPeano p ≠ ∅
          intro heq
          exact hp.1 (fromPeano_injective (heq.trans fromPeano_zero_eq.symm))
        · -- fromPeano p ≠ σ ∅
          intro heq
          exact hp.2.1 (fromPeano_injective (heq.trans fromPeano_one_eq.symm))
        · -- divisibility: ∀ a b ∈ ω, divides (fromPeano p) (mul a b) → ...
          intro a b ha hb hdvd
          obtain ⟨pa, rfl⟩ := fromPeano_surjective a (mem_Omega_is_Nat a ha)
          obtain ⟨pb, rfl⟩ := fromPeano_surjective b (mem_Omega_is_Nat b hb)
          rw [← fromPeano_mul] at hdvd
          have hdvd_peano : Peano.Arith.Divides p (Peano.Mul.mul pa pb) :=
            (fromPeano_divides p (Peano.Mul.mul pa pb)).mpr hdvd
          rcases hp.2.2 pa pb hdvd_peano with h | h
          · exact Or.inl ((fromPeano_divides p pa).mp h)
          · exact Or.inr ((fromPeano_divides p pb).mp h)
      · intro ⟨h_mem, h_ne0, h_ne1, h_div⟩
        refine ⟨?_, ?_, ?_⟩
        · -- p ≠ 𝟘
          intro heq
          apply h_ne0
          rw [heq]; exact fromPeano_zero_eq
        · -- p ≠ 𝟙
          intro heq
          apply h_ne1
          rw [heq]; exact fromPeano_one_eq
        · -- ∀ a b : ℕ₀, Peano.Arith.Divides p (Peano.Mul.mul a b) → ...
          intro a b hdvd_peano
          have ha : (fromPeano a : U) ∈ (ω : U) := Nat_in_Omega _ (fromPeano_is_nat a)
          have hb : (fromPeano b : U) ∈ (ω : U) := Nat_in_Omega _ (fromPeano_is_nat b)
          have hdvd_ZFC : divides (fromPeano p : U) (mul (fromPeano a) (fromPeano b)) := by
            rw [← fromPeano_mul]
            exact (fromPeano_divides p (Peano.Mul.mul a b)).mp hdvd_peano
          rcases h_div (fromPeano a) (fromPeano b) ha hb hdvd_ZFC with h | h
          · exact Or.inl ((fromPeano_divides p a).mpr h)
          · exact Or.inr ((fromPeano_divides p b).mpr h)

    -- =========================================================================
    -- §4  Basic properties of isPrime (immediate from definition or bridge)
    -- =========================================================================

    theorem isPrime_in_Omega (p : U) (hp : isPrime p) : p ∈ (ω : U) :=
      hp.1

    theorem isPrime_ne_zero (p : U) (hp : isPrime p) : p ≠ (∅ : U) :=
      hp.2.1

    theorem isPrime_ne_one (p : U) (hp : isPrime p) : p ≠ σ (∅ : U) :=
      hp.2.2.1

    /-- Every ZFC-prime is at least 2: `σ(σ ∅) ∈ p ∨ σ(σ ∅) = p`. -/
    theorem isPrime_ge_two (p : U) (hp : isPrime p) :
        (σ (σ (∅ : U)) ∈ p) ∨ σ (σ (∅ : U)) = p := by
      obtain ⟨pp, rfl⟩ := fromPeano_surjective p (mem_Omega_is_Nat p hp.1)
      have hprime : Peano.Arith.Prime pp := (fromPeano_prime pp).mpr hp
      have hle := prime_ge_two hprime
      rw [fromPeano_le_iff 𝟚 pp] at hle
      rwa [fromPeano_two_eq] at hle

    /-- If `p` is ZFC-prime and `d ∈ ω` divides `p`, then `d = σ ∅` or `d = p`. -/
    theorem isPrime_prime_divisors (p d : U) (hp : isPrime p)
        (hd : d ∈ (ω : U)) (hdvd : divides d p) :
        d = σ (∅ : U) ∨ d = p := by
      obtain ⟨pp, rfl⟩ := fromPeano_surjective p (mem_Omega_is_Nat p hp.1)
      obtain ⟨pd, rfl⟩ := fromPeano_surjective d (mem_Omega_is_Nat d hd)
      have hprime : Peano.Arith.Prime pp := (fromPeano_prime pp).mpr hp
      have hdvd_peano : Peano.Arith.Divides pd pp :=
        (fromPeano_divides pd pp).mpr hdvd
      rcases prime_divisors hprime hdvd_peano with h | h
      · left
        rw [h]; exact fromPeano_one_eq
      · right
        exact congrArg (fromPeano : Peano.ℕ₀ → U) h

    -- =========================================================================
    -- §5  Existence of a prime divisor (ZFC version)
    -- =========================================================================

    /-- Every `n ∈ ω` with `2 ≤ n` has a ZFC-prime divisor. -/
    theorem exists_prime_divisor_ZFC (n : U) (hn : n ∈ (ω : U))
        (h_ge_2 : (σ (σ (∅ : U)) ∈ n) ∨ σ (σ (∅ : U)) = n) :
        ∃ p : U, isPrime p ∧ divides p n := by
      obtain ⟨pn, rfl⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      -- Convert ZFC ≥2 to Peano Le 𝟚 pn
      have hle_peano : Peano.Order.Le 𝟚 pn := by
        rw [fromPeano_le_iff 𝟚 pn]
        rwa [fromPeano_two_eq]
      -- Apply the Peano prime divisor theorem
      obtain ⟨p_peano, hp_prime, hp_dvd⟩ := exists_prime_divisor pn hle_peano
      exact ⟨fromPeano p_peano,
             (fromPeano_prime p_peano).mp hp_prime,
             (fromPeano_divides p_peano pn).mp hp_dvd⟩

    -- =========================================================================
    -- §6  TFA — Existence of prime factorization (Approach A)
    -- =========================================================================

    /-- **TFA — Existence** (Approach A): every `n ∈ ω` with `2 ≤ n` has a prime
        factorization given as a `DList ℕ₀` on the Peano side whose ZFC product
        equals `n`. -/
    theorem exists_prime_factorization_ZFC (n : U) (hn : n ∈ (ω : U))
        (h_ge_2 : (σ (σ (∅ : U)) ∈ n) ∨ σ (σ (∅ : U)) = n) :
        ∃ ps : DList ℕ₀, PrimeList ps ∧ (fromPeano (product_list ps) : U) = n := by
      obtain ⟨pn, rfl⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      have hle_peano : Peano.Order.Le 𝟚 pn := by
        rw [fromPeano_le_iff 𝟚 pn]; rwa [fromPeano_two_eq]
      obtain ⟨ps, hpl, hprod⟩ := exists_prime_factorization pn hle_peano
      exact ⟨ps, hpl, congrArg (fromPeano : Peano.ℕ₀ → U) hprod⟩

    -- =========================================================================
    -- §7  TFA — Uniqueness of prime factorization (Approach A)
    -- =========================================================================

    /-- **TFA — Uniqueness** (Approach A): if two `DList ℕ₀` prime lists have the
        same ZFC product, then they have the same multiplicity for every prime `p`. -/
    theorem unique_prime_factorization_ZFC
        (ps qs : DList ℕ₀) (hps : PrimeList ps) (hqs : PrimeList qs)
        (h_prod : (fromPeano (product_list ps) : U) = fromPeano (product_list qs))
        (p : Peano.ℕ₀) (hp : Peano.Arith.Prime p) :
        DList.length (DList.filter (fun q => decide (q = p)) ps) =
        DList.length (DList.filter (fun q => decide (q = p)) qs) := by
      exact unique_prime_factorization ps qs hps hqs
        (fromPeano_injective h_prod) p hp

    -- =========================================================================
    -- §8  Primality of 𝟚 (needed for sqrt2_irrational)
    -- =========================================================================

    /-- 𝟚 is a prime in the Peano sense.
        Strategy: any prime divisor `p` of 𝟚 satisfies `p ≥ 𝟚` (by `prime_ge_two`)
        and `p ≤ 𝟚` (by `divides_le`), hence `p = 𝟚` by antisymmetry. -/
    theorem peano_prime_two : Peano.Arith.Prime 𝟚 := by
      have hle : Peano.Order.Le 𝟚 𝟚 := Peano.Order.le_refl 𝟚
      obtain ⟨p, hp_prime, hp_dvd⟩ := exists_prime_divisor 𝟚 hle
      have h_two_ne_zero : (𝟚 : Peano.ℕ₀) ≠ 𝟘 := by
        intro h
        exact (Peano.Axioms.succ_neq_zero 𝟙) h
      have hp_le_two : Peano.Order.Le p 𝟚 :=
        Peano.Arith.divides_le hp_dvd h_two_ne_zero
      have hp_ge_two : Peano.Order.Le 𝟚 p := prime_ge_two hp_prime
      have hp_eq : p = 𝟚 := Peano.Order.le_antisymm p 𝟚 hp_le_two hp_ge_two
      rw [← hp_eq]
      exact hp_prime

    /-- σ(σ ∅) is a ZFC-prime in U. -/
    theorem isPrime_two : isPrime (σ (σ (∅ : U))) := by
      have h : isPrime ((fromPeano 𝟚 : U)) := (fromPeano_prime (U := U) 𝟚).mp peano_prime_two
      rwa [fromPeano_two_eq] at h

    /-- Key consequence of `Prime 𝟚`: if 𝟚 divides a square, it divides the base. -/
    theorem two_dvd_of_two_dvd_mul_self (a : Peano.ℕ₀)
        (h : (𝟚 : Peano.ℕ₀) ∣ Peano.Mul.mul a a) :
        (𝟚 : Peano.ℕ₀) ∣ a := by
      have hcase : (𝟚 : Peano.ℕ₀) ∣ a ∨ (𝟚 : Peano.ℕ₀) ∣ a :=
        peano_prime_two.2.2 a a h
      cases hcase with
      | inl h1 => exact h1
      | inr h2 => exact h2

    -- Local helper: (2k)*(2k) = 2*(2*(k*k)) in Peano ℕ₀.
    private theorem peano_two_k_squared (k : Peano.ℕ₀) :
        Peano.Mul.mul (Peano.Mul.mul 𝟚 k) (Peano.Mul.mul 𝟚 k)
          = Peano.Mul.mul 𝟚 (Peano.Mul.mul 𝟚 (Peano.Mul.mul k k)) := by
      -- (2k)(2k) = 2 (k (2k))   [mul_assoc]
      -- (2k)    in mul_assoc form: mul (mul m n) k = mul m (mul n k)
      -- match: mul (mul 𝟚 k) (mul 𝟚 k) ↦ m=𝟚, n=k, k=mul 𝟚 k.
      -- Call: mul_assoc n m k = mul_assoc k 𝟚 (mul 𝟚 k).
      calc Peano.Mul.mul (Peano.Mul.mul 𝟚 k) (Peano.Mul.mul 𝟚 k)
          = Peano.Mul.mul 𝟚 (Peano.Mul.mul k (Peano.Mul.mul 𝟚 k)) :=
              Peano.Mul.mul_assoc k 𝟚 (Peano.Mul.mul 𝟚 k)
        _ = Peano.Mul.mul 𝟚 (Peano.Mul.mul (Peano.Mul.mul k 𝟚) k) := by
              rw [show Peano.Mul.mul k (Peano.Mul.mul 𝟚 k)
                    = Peano.Mul.mul (Peano.Mul.mul k 𝟚) k from
                  (Peano.Mul.mul_assoc 𝟚 k k).symm]
        _ = Peano.Mul.mul 𝟚 (Peano.Mul.mul (Peano.Mul.mul 𝟚 k) k) := by
              rw [Peano.Mul.mul_comm k 𝟚]
        _ = Peano.Mul.mul 𝟚 (Peano.Mul.mul 𝟚 (Peano.Mul.mul k k)) := by
              rw [Peano.Mul.mul_assoc k 𝟚 k]

    /-- Infinite descent: if `m*m = 2 * (n*n)` in `Peano.ℕ₀`, then `m = 𝟘`.
        (Hence `n = 𝟘` too, since then `2 * n² = 0`.)
        This is the key fact used to prove √2 is irrational. -/
    theorem peano_descent_two_squares :
        ∀ m : Peano.ℕ₀, ∀ n : Peano.ℕ₀,
          Peano.Mul.mul m m = Peano.Mul.mul 𝟚 (Peano.Mul.mul n n) →
          m = 𝟘 := by
      intro m
      induction m using Peano.WellFounded.well_founded_lt.induction with
      | _ m IH =>
        intro n hmn
        -- We argue by contradiction: assume m ≠ 𝟘 and derive False via descent.
        apply Classical.byContradiction
        intro hm_ne
        -- 1) 2 ∣ m*m
        have h_two_dvd_mm : (𝟚 : Peano.ℕ₀) ∣ Peano.Mul.mul m m :=
          ⟨Peano.Mul.mul n n, hmn⟩
        -- 2) 2 ∣ m
        have h_two_dvd_m : (𝟚 : Peano.ℕ₀) ∣ m :=
          two_dvd_of_two_dvd_mul_self m h_two_dvd_mm
        obtain ⟨k₁, hk₁⟩ := h_two_dvd_m
        -- k₁ ≠ 𝟘 (else m = 0)
        have hk₁_ne : k₁ ≠ 𝟘 := by
          intro hk₁0
          apply hm_ne
          rw [hk₁, hk₁0, Peano.Mul.mul_zero]
        -- 3) Substitute m = 2 k₁ into the original equation and unfold (2 k₁)²
        have h_two_ne : (𝟚 : Peano.ℕ₀) ≠ 𝟘 := fun h => Peano.Axioms.succ_neq_zero 𝟙 h
        have h_subst : Peano.Mul.mul 𝟚 (Peano.Mul.mul 𝟚 (Peano.Mul.mul k₁ k₁))
                       = Peano.Mul.mul 𝟚 (Peano.Mul.mul n n) := by
          rw [← peano_two_k_squared k₁, ← hk₁]; exact hmn
        -- Cancel one 2: 2*(k₁*k₁) = n*n.
        have h_inner : Peano.Mul.mul 𝟚 (Peano.Mul.mul k₁ k₁) = Peano.Mul.mul n n :=
          Peano.Mul.mul_cancelation_left 𝟚 _ _ h_two_ne h_subst
        -- 4) From n*n = 2*(k₁*k₁), get 2 ∣ n, so n = 2 k₂.
        have h_nn : Peano.Mul.mul n n = Peano.Mul.mul 𝟚 (Peano.Mul.mul k₁ k₁) := h_inner.symm
        have h_two_dvd_nn : (𝟚 : Peano.ℕ₀) ∣ Peano.Mul.mul n n :=
          ⟨Peano.Mul.mul k₁ k₁, h_nn⟩
        have h_two_dvd_n : (𝟚 : Peano.ℕ₀) ∣ n :=
          two_dvd_of_two_dvd_mul_self n h_two_dvd_nn
        obtain ⟨k₂, hk₂⟩ := h_two_dvd_n
        -- 5) Substitute n = 2 k₂ and cancel 2 to obtain k₁² = 2 (k₂²)
        have h_subst2 :
            Peano.Mul.mul 𝟚 (Peano.Mul.mul 𝟚 (Peano.Mul.mul k₂ k₂))
            = Peano.Mul.mul 𝟚 (Peano.Mul.mul k₁ k₁) := by
          rw [← peano_two_k_squared k₂, ← hk₂]; exact h_nn
        have h_kk : Peano.Mul.mul 𝟚 (Peano.Mul.mul k₂ k₂) = Peano.Mul.mul k₁ k₁ :=
          Peano.Mul.mul_cancelation_left 𝟚 _ _ h_two_ne h_subst2
        have h_k1_eq : Peano.Mul.mul k₁ k₁ = Peano.Mul.mul 𝟚 (Peano.Mul.mul k₂ k₂) := h_kk.symm
        -- 6) Lt k₁ m: since m = 2 k₁ = k₁ + k₁ and k₁ ≠ 𝟘.
        have h_k1_lt_m : Peano.StrictOrder.Lt k₁ m := by
          rw [hk₁, Peano.Mul.two_mul k₁]
          exact Peano.Add.lt_self_add_r k₁ k₁ hk₁_ne
        -- 7) Apply IH at k₁ to k₂: k₁ = 𝟘. Contradicts hk₁_ne.
        exact hk₁_ne (IH k₁ h_k1_lt_m k₂ h_k1_eq)

  end Nat.Primes

  export Nat.Primes (
    -- Definition
    isPrime
    -- Bridge theorem
    fromPeano_prime
    -- Basic properties
    isPrime_in_Omega
    isPrime_ne_zero
    isPrime_ne_one
    isPrime_ge_two
    isPrime_prime_divisors
    -- Existence of prime divisor
    exists_prime_divisor_ZFC
    -- Fundamental Theorem of Arithmetic (Approach A)
    exists_prime_factorization_ZFC
    unique_prime_factorization_ZFC
    -- Primality of 𝟚
    peano_prime_two
    isPrime_two
    two_dvd_of_two_dvd_mul_self
    peano_descent_two_squares
  )

end ZFC
