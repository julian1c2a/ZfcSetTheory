/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Embedding — Canonical Injection ω ↪ ℤ and Equipotence

  This module defines the canonical embedding of natural numbers into integers
  and proves that ℤ is equipotent to ω via an explicit zigzag bijection.

  ## Main Definitions

  * `natToInt` — maps n ∈ ω to intClass n ∅ ∈ ℤ
  * `natToInt_graph` — the ZFC function graph {⟨n, intClass n ∅⟩ | n ∈ ω}
  * `intToNat_zigzag` — the zigzag bijection ℤ → ω:
      intClass n ∅ ↦ add n n (even), intClass ∅ (σ k) ↦ σ (add k k) (odd)

  ## Main Theorems

  * `natToInt_is_function` — natToInt_graph is a function ω → ℤ
  * `natToInt_injective` — natToInt_graph is injective
  * `natToInt_preserves_add` — natToInt (add m n) = addZ (natToInt m) (natToInt n)
  * `natToInt_preserves_mul` — natToInt (mul m n) = mulZ (natToInt m) (natToInt n)
  * `natToInt_preserves_le` — m ⊆ n → leZ (natToInt m) (natToInt n)
  * `natToInt_reflects_le` — leZ (natToInt m) (natToInt n) → m ⊆ n
  * `natToInt_not_surjective` — natToInt is not surjective onto ℤ
  * `intToNat_zigzag_is_bijection` — zigzag is a bijection ℤ → ω
  * `IntSet_equipotent_omega` — |ℤ| = |ω|
-/

import ZfcSetTheory.Int.Order
import ZfcSetTheory.Int.Mul

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Nat.Add
  open ZFC.Nat.Mul
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul
  open ZFC.Int.Order

  universe u
  variable {U : Type u}

  namespace Int.Embedding

    -- =========================================================================
    -- Section 1: natToInt — canonical embedding ω → ℤ
    -- =========================================================================

    /-- The canonical embedding: n ↦ intClass n ∅ = [(n, 0)]. -/
    noncomputable def natToInt (n : U) : U := intClass n ∅

    /-- The ZFC function graph of natToInt: {⟨n, intClass n ∅⟩ | n ∈ ω}. -/
    noncomputable def natToInt_graph : U :=
      sep ((ω : U) ×ₛ IntSet) (fun p =>
        ∃ n, n ∈ (ω : U) ∧ p = ⟨n, intClass n ∅⟩)

    /-- natToInt maps into ℤ. -/
    theorem natToInt_mem_IntSet (n : U) (hn : n ∈ (ω : U)) :
        natToInt n ∈ (IntSet : U) :=
      intClass_mem_IntSet n ∅ hn zero_in_Omega

    /-- Membership characterization of natToInt_graph. -/
    private theorem mem_natToInt_graph (p : U) :
        p ∈ (natToInt_graph : U) ↔
          p ∈ ((ω : U) ×ₛ IntSet) ∧
          ∃ n, n ∈ (ω : U) ∧ p = ⟨n, intClass n ∅⟩ := by
      simp only [natToInt_graph, mem_sep_iff]

    /-- natToInt_graph is a function from ω to ℤ. -/
    theorem natToInt_is_function :
        IsFunction (natToInt_graph : U) ω IntSet := by
      constructor
      · -- Subset: natToInt_graph ⊆ ω ×ₛ IntSet
        intro p hp
        rw [mem_natToInt_graph] at hp
        exact hp.1
      · -- For each n ∈ ω, ∃! y, ⟨n, y⟩ ∈ natToInt_graph
        intro n hn
        apply ExistsUnique.intro (intClass n ∅)
        · -- Membership
          rw [mem_natToInt_graph]
          exact ⟨(OrderedPair_mem_CartesianProduct n (intClass n ∅) ω IntSet).mpr
                  ⟨hn, intClass_mem_IntSet n ∅ hn zero_in_Omega⟩,
                 ⟨n, hn, rfl⟩⟩
        · -- Uniqueness
          intro y hy
          rw [mem_natToInt_graph] at hy
          obtain ⟨_, m, _, h_eq⟩ := hy
          have := (OrderedPair_eq_iff n y m (intClass m ∅)).mp h_eq
          exact this.2

    /-- natToInt_graph is injective. -/
    theorem natToInt_injective :
        isInjective (natToInt_graph : U) := by
      intro x₁ x₂ y hx₁ hx₂
      rw [mem_natToInt_graph] at hx₁ hx₂
      obtain ⟨_, n₁, hn₁, h₁⟩ := hx₁
      obtain ⟨_, n₂, hn₂, h₂⟩ := hx₂
      have heq₁ := (OrderedPair_eq_iff x₁ y n₁ (intClass n₁ ∅)).mp h₁
      have heq₂ := (OrderedPair_eq_iff x₂ y n₂ (intClass n₂ ∅)).mp h₂
      rw [heq₁.1, heq₂.1]
      have h_class_eq : intClass n₁ ∅ = intClass n₂ ∅ := by
        rw [← heq₁.2, ← heq₂.2]
      exact intClass_pos_injective n₁ n₂ hn₁ hn₂ h_class_eq

    -- =========================================================================
    -- Section 2: Preservation of algebraic structure
    -- =========================================================================

    /-- natToInt preserves addition: natToInt (add m n) = addZ (natToInt m) (natToInt n). -/
    theorem natToInt_preserves_add (m n : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        natToInt (add m n) = addZ (natToInt m) (natToInt n) := by
      unfold natToInt
      rw [addZ_class m ∅ n ∅ hm zero_in_Omega hn zero_in_Omega]
      rw [add_zero ∅ zero_in_Omega]

    /-- natToInt preserves multiplication: natToInt (mul m n) = mulZ (natToInt m) (natToInt n). -/
    theorem natToInt_preserves_mul (m n : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        natToInt (mul m n) = mulZ (natToInt m) (natToInt n) := by
      unfold natToInt
      rw [mulZ_class m ∅ n ∅ hm zero_in_Omega hn zero_in_Omega]
      rw [mul_zero m hm, mul_zero n hn,
          zero_mul_Omega n hn, zero_mul_Omega m hm]
      rw [add_zero (mul m n) (mul_in_Omega m n hm hn)]
      rw [add_zero ∅ zero_in_Omega]

    -- =========================================================================
    -- Section 3: Preservation of order
    -- =========================================================================

    /-- natToInt preserves order: m ⊆ n → leZ (natToInt m) (natToInt n). -/
    theorem natToInt_preserves_le (m n : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_sub : m ⊆ n) :
        leZ (natToInt m) (natToInt n) := by
      unfold natToInt
      rw [leZ_iff_repr (intClass m ∅) (intClass n ∅)
          (intClass_mem_IntSet m ∅ hm zero_in_Omega)
          (intClass_mem_IntSet n ∅ hn zero_in_Omega)]
      exact ⟨m, ∅, n, ∅, hm, zero_in_Omega, hn, zero_in_Omega,
             rfl, rfl, by
        unfold leZ_repr
        rw [add_zero m hm, zero_add n hn]
        exact nat_subset_mem_or_eq m n
                (mem_Omega_is_Nat m hm) (mem_Omega_is_Nat n hn) h_sub⟩

    /-- natToInt reflects order: leZ (natToInt m) (natToInt n) → m ⊆ n. -/
    theorem natToInt_reflects_le (m n : U)
        (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U))
        (h_le : leZ (natToInt m) (natToInt n)) :
        m ⊆ n := by
      unfold natToInt at h_le
      have h_repr := h_le m ∅ n ∅ hm zero_in_Omega hn zero_in_Omega rfl rfl
      unfold leZ_repr at h_repr
      rw [add_zero m hm, zero_add n hn] at h_repr
      cases h_repr with
      | inl h_mem =>
        -- m ∈ n → m ⊆ n (naturals are transitive)
        exact (mem_Omega_is_Nat n hn).1 m h_mem
      | inr h_eq =>
        -- m = n → m ⊆ n
        rw [h_eq]
        intro x hx; exact hx

    -- =========================================================================
    -- Section 4: Non-surjectivity
    -- =========================================================================

    /-- natToInt is not surjective onto ℤ. -/
    theorem natToInt_not_surjective :
        ¬ isSurjectiveOnto (natToInt_graph : U) IntSet := by
      intro h_surj
      -- intClass ∅ (σ ∅) ∈ IntSet is a negative integer with no preimage
      have h_neg_in : intClass (∅ : U) (σ ∅) ∈ (IntSet : U) :=
        intClass_mem_IntSet ∅ (σ ∅) zero_in_Omega (succ_in_Omega ∅ zero_in_Omega)
      obtain ⟨x, hx⟩ := h_surj (intClass (∅ : U) (σ ∅)) h_neg_in
      rw [mem_natToInt_graph] at hx
      obtain ⟨_, n, hn, h_eq⟩ := hx
      have h_pair := (OrderedPair_eq_iff x (intClass (∅ : U) (σ ∅)) n (intClass n ∅)).mp h_eq
      have h_class_eq : intClass n ∅ = intClass (∅ : U) (σ ∅) := h_pair.2.symm
      -- intClass_eq_iff: add n (σ ∅) = add ∅ ∅
      rw [intClass_eq_iff n ∅ ∅ (σ ∅) hn zero_in_Omega zero_in_Omega
          (succ_in_Omega ∅ zero_in_Omega)] at h_class_eq
      rw [add_zero ∅ zero_in_Omega] at h_class_eq
      rw [add_succ n ∅ hn zero_in_Omega, add_zero n hn] at h_class_eq
      -- h_class_eq : σ n = ∅, contradicts succ_nonempty
      exact absurd h_class_eq (succ_nonempty n)

    -- =========================================================================
    -- Section 5: Even/odd decomposition of natural numbers
    -- =========================================================================

    /-- Helper: add (σ k) (σ k) = σ (σ (add k k)). -/
    private theorem double_succ (k : U) (hk : k ∈ (ω : U)) :
        add (σ k) (σ k) = σ (σ (add k k)) := by
      rw [add_succ (σ k) k (succ_in_Omega k hk) hk]
      rw [succ_add_Omega k k hk hk]

    /-- Every natural number is either even (= add k k) or odd (= σ (add k k)). -/
    private theorem even_or_odd (n : U) (hn : n ∈ (ω : U)) :
        (∃ k, k ∈ (ω : U) ∧ n = add k k) ∨
        (∃ k, k ∈ (ω : U) ∧ n = σ (add k k)) := by
      let S := sep ω (fun n =>
        (∃ k, k ∈ (ω : U) ∧ n = add k k) ∨
        (∃ k, k ∈ (ω : U) ∧ n = σ (add k k)))
      have h_S_eq_ω : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base: ∅ = add ∅ ∅
          rw [mem_sep_iff]
          exact ⟨zero_in_Omega, Or.inl ⟨∅, zero_in_Omega, (add_zero ∅ zero_in_Omega).symm⟩⟩
        · -- Step: m → σ m
          intro m hm_in_S
          rw [mem_sep_iff] at hm_in_S
          obtain ⟨hm_ω, h_ih⟩ := hm_in_S
          rw [mem_sep_iff]
          constructor
          · exact succ_in_Omega m hm_ω
          · cases h_ih with
            | inl h_even =>
              -- m = add k k → σ m = σ (add k k) (odd)
              obtain ⟨k, hk, h_eq⟩ := h_even
              exact Or.inr ⟨k, hk, by rw [h_eq]⟩
            | inr h_odd =>
              -- m = σ (add k k) → σ m = σ (σ (add k k)) = add (σ k) (σ k) (even)
              obtain ⟨k, hk, h_eq⟩ := h_odd
              exact Or.inl ⟨σ k, succ_in_Omega k hk, by
                rw [h_eq, ← double_succ k hk]⟩
      have : n ∈ S := h_S_eq_ω ▸ hn
      rw [mem_sep_iff] at this
      exact this.2

    /-- Even numbers are never odd: add n n ≠ σ (add k k). -/
    private theorem double_ne_succ_double (n : U) (hn : n ∈ (ω : U)) :
        ∀ k, k ∈ (ω : U) → add n n ≠ σ (add k k) := by
      -- Induction on n
      let S := sep ω (fun n => ∀ k, k ∈ (ω : U) → add n n ≠ σ (add k k))
      have h_S_eq_ω : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base: add ∅ ∅ = ∅ ≠ σ (add k k) for any k
          rw [mem_sep_iff]
          exact ⟨zero_in_Omega, fun k _ h_eq => by
            rw [add_zero ∅ zero_in_Omega] at h_eq
            exact absurd h_eq.symm (succ_nonempty (add k k))⟩
        · -- Step: j → σ j
          intro j hj_in_S
          rw [mem_sep_iff] at hj_in_S
          obtain ⟨hj_ω, h_ih⟩ := hj_in_S
          rw [mem_sep_iff]
          constructor
          · exact succ_in_Omega j hj_ω
          · intro k hk h_eq
            -- add (σ j) (σ j) = σ (σ (add j j)) by double_succ
            rw [double_succ j hj_ω] at h_eq
            -- σ (σ (add j j)) = σ (add k k) → σ (add j j) = add k k
            have h_eq' := succ_injective (σ (add j j)) (add k k)
              (mem_Omega_is_Nat _ (succ_in_Omega _ (add_in_Omega j j hj_ω hj_ω)))
              (mem_Omega_is_Nat _ (add_in_Omega k k hk hk)) h_eq
            -- add k k = σ (add j j), so k ≠ ∅
            by_cases hk_zero : k = ∅
            · rw [hk_zero, add_zero ∅ zero_in_Omega] at h_eq'
              exact absurd h_eq'.symm (succ_nonempty (add j j))
            · -- k ≠ ∅ → k = σ l for some l
              have ⟨hk_nat⟩ := Nat_iff_mem_Omega k
              have hk_is_nat := hk_nat hk
              have hl_eq := succ_predecessorPos k hk_is_nat hk_zero
              set l := predecessorPos k hk_zero
              have hl_nat := predecessorPos_is_nat k hk_is_nat hk_zero
              have hl_ω := (Nat_iff_mem_Omega l).mp hl_nat
              -- k = σ l, so add k k = add (σ l) (σ l) = σ (σ (add l l))
              rw [← hl_eq] at h_eq'
              rw [double_succ l hl_ω] at h_eq'
              -- σ (σ (add l l)) = σ (add j j) → σ (add l l) = add j j
              have h_eq'' := succ_injective (σ (add l l)) (add j j)
                (mem_Omega_is_Nat _ (succ_in_Omega _ (add_in_Omega l l hl_ω hl_ω)))
                (mem_Omega_is_Nat _ (add_in_Omega j j hj_ω hj_ω)) h_eq'
              -- add j j = σ (add l l), contradicts IH with k := l
              exact absurd h_eq''.symm (h_ih l hl_ω)
      have : n ∈ S := h_S_eq_ω ▸ hn
      rw [mem_sep_iff] at this
      exact this.2

    /-- Doubling is injective: add n n = add m m → n = m. -/
    private theorem double_injective (n m : U)
        (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h_eq : add n n = add m m) : n = m := by
      -- By trichotomy on n, m
      have h_tri := natLt_trichotomy n m
                      (mem_Omega_is_Nat n hn) (mem_Omega_is_Nat m hm)
      rcases h_tri with h_lt | h_eq' | h_gt
      · -- n ∈ m: add n n ∈ add m m, but add n n = add m m → contradiction
        exfalso
        have h1 := add_lt_of_lt_Omega n n m hn hn hm h_lt
        -- add n n ∈ add n m
        have h2 := add_lt_of_lt_Omega m n m hm hn hm h_lt
        rw [add_comm_Omega m n hm hn, add_comm_Omega m m hm hm] at h2
        -- add n m ∈ add m m
        have h_trans := natLt_trans
          (mem_Omega_is_Nat _ (add_in_Omega n n hn hn))
          (mem_Omega_is_Nat _ (add_in_Omega n m hn hm))
          (mem_Omega_is_Nat _ (add_in_Omega m m hm hm))
          h1 h2
        rw [h_eq] at h_trans
        exact not_mem_self (add m m) (mem_Omega_is_Nat _ (add_in_Omega m m hm hm)) h_trans
      · exact h_eq'
      · -- m ∈ n: symmetric case
        exfalso
        have h1 := add_lt_of_lt_Omega m m n hm hm hn h_gt
        have h2 := add_lt_of_lt_Omega n m n hn hm hn h_gt
        rw [add_comm_Omega n m hn hm, add_comm_Omega n n hn hn] at h2
        have h_trans := natLt_trans
          (mem_Omega_is_Nat _ (add_in_Omega m m hm hm))
          (mem_Omega_is_Nat _ (add_in_Omega m n hm hn))
          (mem_Omega_is_Nat _ (add_in_Omega n n hn hn))
          h1 h2
        rw [← h_eq] at h_trans
        exact not_mem_self (add n n) (mem_Omega_is_Nat _ (add_in_Omega n n hn hn)) h_trans

    -- =========================================================================
    -- Section 6: Zigzag bijection ℤ → ω
    -- =========================================================================

    /-- The zigzag bijection ℤ → ω:
        intClass n ∅ ↦ add n n (even)
        intClass ∅ (σ k) ↦ σ (add k k) (odd) -/
    noncomputable def intToNat_zigzag : U :=
      sep ((IntSet : U) ×ₛ ω) (fun p =>
        (∃ n, n ∈ (ω : U) ∧ p = ⟨intClass n ∅, add n n⟩) ∨
        (∃ k, k ∈ (ω : U) ∧ p = ⟨intClass ∅ (σ k), σ (add k k)⟩))

    /-- Membership characterization. -/
    private theorem mem_intToNat_zigzag (p : U) :
        p ∈ (intToNat_zigzag : U) ↔
          p ∈ ((IntSet : U) ×ₛ ω) ∧
          ((∃ n, n ∈ (ω : U) ∧ p = ⟨intClass n ∅, add n n⟩) ∨
           (∃ k, k ∈ (ω : U) ∧ p = ⟨intClass ∅ (σ k), σ (add k k)⟩)) := by
      simp only [intToNat_zigzag, mem_sep_iff]

    /-- Helper: every z ∈ IntSet is either intClass n ∅ for some n,
        or intClass ∅ (σ k) for some k. -/
    private theorem int_canonical (z : U) (hz : z ∈ (IntSet : U)) :
        (∃ n, n ∈ (ω : U) ∧ z = intClass n ∅) ∨
        (∃ k, k ∈ (ω : U) ∧ z = intClass ∅ (σ k)) := by
      have h_tri := int_trichotomy z hz
      rcases h_tri with h_zero | h_pos | h_neg
      · -- z = zeroZ = intClass ∅ ∅
        exact Or.inl ⟨∅, zero_in_Omega, h_zero⟩
      · -- z = intClass n ∅, n ≠ ∅
        obtain ⟨n, hn, _, h_eq⟩ := h_pos
        exact Or.inl ⟨n, hn, h_eq⟩
      · -- z = intClass ∅ m, m ≠ ∅ → m = σ k
        obtain ⟨m, hm, hm_ne, h_eq⟩ := h_neg
        have hm_nat := mem_Omega_is_Nat m hm
        have h_succ := succ_predecessorPos m hm_nat hm_ne
        set k := predecessorPos m hm_ne
        have hk_ω := (Nat_iff_mem_Omega k).mp (predecessorPos_is_nat m hm_nat hm_ne)
        exact Or.inr ⟨k, hk_ω, by rw [h_eq, ← h_succ]⟩

    /-- Uniqueness helper: intClass n ∅ ≠ intClass ∅ (σ k) for all n, k ∈ ω. -/
    private theorem intClass_pos_ne_intClass_neg_succ (n k : U)
        (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) :
        intClass n ∅ ≠ intClass (∅ : U) (σ k) := by
      intro h_eq
      rw [intClass_eq_iff n ∅ ∅ (σ k) hn zero_in_Omega zero_in_Omega
          (succ_in_Omega k hk)] at h_eq
      -- h_eq : add n (σ k) = add ∅ ∅
      rw [add_zero ∅ zero_in_Omega] at h_eq
      rw [add_succ n k hn hk] at h_eq
      exact absurd h_eq (succ_nonempty (add n k))

    /-- intToNat_zigzag is a function from IntSet to ω. -/
    theorem intToNat_zigzag_is_function :
        IsFunction (intToNat_zigzag : U) IntSet ω := by
      constructor
      · -- Subset
        intro p hp; rw [mem_intToNat_zigzag] at hp; exact hp.1
      · -- Totality and uniqueness
        intro z hz
        have h_canon := int_canonical z hz
        rcases h_canon with ⟨n, hn, hz_eq⟩ | ⟨k, hk, hz_eq⟩
        · -- z = intClass n ∅, image = add n n
          apply ExistsUnique.intro (add n n)
          · -- Membership
            rw [mem_intToNat_zigzag]
            exact ⟨(OrderedPair_mem_CartesianProduct z (add n n) IntSet ω).mpr
                    ⟨hz, add_in_Omega n n hn hn⟩,
                   Or.inl ⟨n, hn, by rw [hz_eq]⟩⟩
          · -- Uniqueness
            intro w hw
            rw [mem_intToNat_zigzag] at hw
            obtain ⟨_, h_cases⟩ := hw
            cases h_cases with
            | inl h_even =>
              obtain ⟨m, _, h_p_eq⟩ := h_even
              have h_pair := (OrderedPair_eq_iff z w m (add m m)).mp h_p_eq
              exact h_pair.2
            | inr h_odd =>
              obtain ⟨j, hj, h_p_eq⟩ := h_odd
              have h_pair := (OrderedPair_eq_iff z w (intClass ∅ (σ j)) (σ (add j j))).mp h_p_eq
              -- z = intClass ∅ (σ j), but z = intClass n ∅ → contradiction
              exfalso
              exact intClass_pos_ne_intClass_neg_succ n j hn hj
                (by rw [hz_eq, h_pair.1])
        · -- z = intClass ∅ (σ k), image = σ (add k k)
          apply ExistsUnique.intro (σ (add k k))
          · -- Membership
            rw [mem_intToNat_zigzag]
            exact ⟨(OrderedPair_mem_CartesianProduct z (σ (add k k)) IntSet ω).mpr
                    ⟨hz, succ_in_Omega (add k k) (add_in_Omega k k hk hk)⟩,
                   Or.inr ⟨k, hk, by rw [hz_eq]⟩⟩
          · -- Uniqueness
            intro w hw
            rw [mem_intToNat_zigzag] at hw
            obtain ⟨_, h_cases⟩ := hw
            cases h_cases with
            | inl h_even =>
              obtain ⟨m, hm, h_p_eq⟩ := h_even
              have h_pair := (OrderedPair_eq_iff z w m (add m m)).mp h_p_eq
              -- z = intClass m ∅, but z = intClass ∅ (σ k) → contradiction
              exfalso
              exact intClass_pos_ne_intClass_neg_succ m k hm hk
                (by rw [← h_pair.1, hz_eq])
            | inr h_odd =>
              obtain ⟨j, _, h_p_eq⟩ := h_odd
              have h_pair := (OrderedPair_eq_iff z w (intClass ∅ (σ j)) (σ (add j j))).mp h_p_eq
              exact h_pair.2

    /-- intToNat_zigzag is injective. -/
    theorem intToNat_zigzag_injective :
        isInjective (intToNat_zigzag : U) := by
      intro z₁ z₂ w hz₁ hz₂
      rw [mem_intToNat_zigzag] at hz₁ hz₂
      obtain ⟨_, h₁⟩ := hz₁
      obtain ⟨_, h₂⟩ := hz₂
      cases h₁ with
      | inl h₁_even =>
        obtain ⟨n₁, hn₁, hp₁⟩ := h₁_even
        have hpair₁ := (OrderedPair_eq_iff z₁ w n₁ (add n₁ n₁)).mp hp₁
        cases h₂ with
        | inl h₂_even =>
          -- Both even: add n₁ n₁ = add n₂ n₂ → n₁ = n₂
          obtain ⟨n₂, hn₂, hp₂⟩ := h₂_even
          have hpair₂ := (OrderedPair_eq_iff z₂ w n₂ (add n₂ n₂)).mp hp₂
          have h_w_eq : add n₁ n₁ = add n₂ n₂ := by
            rw [← hpair₁.2, ← hpair₂.2]
          have h_n_eq := double_injective n₁ n₂ hn₁ hn₂ h_w_eq
          rw [hpair₁.1, hpair₂.1, h_n_eq]
        | inr h₂_odd =>
          -- Even = Odd: contradiction
          obtain ⟨k₂, hk₂, hp₂⟩ := h₂_odd
          have hpair₂ := (OrderedPair_eq_iff z₂ w (intClass ∅ (σ k₂)) (σ (add k₂ k₂))).mp hp₂
          exfalso
          have h_w_eq : add n₁ n₁ = σ (add k₂ k₂) := by
            rw [← hpair₁.2, ← hpair₂.2]
          exact double_ne_succ_double n₁ hn₁ k₂ hk₂ h_w_eq
      | inr h₁_odd =>
        obtain ⟨k₁, hk₁, hp₁⟩ := h₁_odd
        have hpair₁ := (OrderedPair_eq_iff z₁ w (intClass ∅ (σ k₁)) (σ (add k₁ k₁))).mp hp₁
        cases h₂ with
        | inl h₂_even =>
          -- Odd = Even: contradiction
          obtain ⟨n₂, hn₂, hp₂⟩ := h₂_even
          have hpair₂ := (OrderedPair_eq_iff z₂ w n₂ (add n₂ n₂)).mp hp₂
          exfalso
          have h_w_eq : add n₂ n₂ = σ (add k₁ k₁) := by
            rw [← hpair₂.2, ← hpair₁.2]
          exact double_ne_succ_double n₂ hn₂ k₁ hk₁ h_w_eq
        | inr h₂_odd =>
          -- Both odd: σ (add k₁ k₁) = σ (add k₂ k₂) → k₁ = k₂
          obtain ⟨k₂, hk₂, hp₂⟩ := h₂_odd
          have hpair₂ := (OrderedPair_eq_iff z₂ w (intClass ∅ (σ k₂)) (σ (add k₂ k₂))).mp hp₂
          have h_w_eq : σ (add k₁ k₁) = σ (add k₂ k₂) := by
            rw [← hpair₁.2, ← hpair₂.2]
          have h_kk_eq := succ_injective (add k₁ k₁) (add k₂ k₂)
            (mem_Omega_is_Nat _ (add_in_Omega k₁ k₁ hk₁ hk₁))
            (mem_Omega_is_Nat _ (add_in_Omega k₂ k₂ hk₂ hk₂)) h_w_eq
          have h_k_eq := double_injective k₁ k₂ hk₁ hk₂ h_kk_eq
          rw [hpair₁.1, hpair₂.1, h_k_eq]

    /-- intToNat_zigzag is surjective onto ω. -/
    theorem intToNat_zigzag_surjective :
        isSurjectiveOnto (intToNat_zigzag : U) ω := by
      intro w hw
      have h_eo := even_or_odd w hw
      cases h_eo with
      | inl h_even =>
        obtain ⟨k, hk, hw_eq⟩ := h_even
        exact ⟨intClass k ∅, by
          rw [mem_intToNat_zigzag]
          exact ⟨(OrderedPair_mem_CartesianProduct (intClass k ∅) w IntSet ω).mpr
                  ⟨intClass_mem_IntSet k ∅ hk zero_in_Omega, hw⟩,
                 Or.inl ⟨k, hk, by rw [hw_eq]⟩⟩⟩
      | inr h_odd =>
        obtain ⟨k, hk, hw_eq⟩ := h_odd
        exact ⟨intClass ∅ (σ k), by
          rw [mem_intToNat_zigzag]
          exact ⟨(OrderedPair_mem_CartesianProduct (intClass ∅ (σ k)) w IntSet ω).mpr
                  ⟨intClass_mem_IntSet ∅ (σ k) zero_in_Omega (succ_in_Omega k hk), hw⟩,
                 Or.inr ⟨k, hk, by rw [hw_eq]⟩⟩⟩

    /-- intToNat_zigzag is a bijection from ℤ to ω. -/
    theorem intToNat_zigzag_is_bijection :
        isBijection (intToNat_zigzag : U) IntSet ω :=
      ⟨intToNat_zigzag_is_function,
       intToNat_zigzag_injective,
       intToNat_zigzag_surjective⟩

    /-- ℤ is equipotent to ω: |ℤ| = |ω|. -/
    theorem IntSet_equipotent_omega :
        isEquipotent (IntSet : U) (ω : U) :=
      ⟨intToNat_zigzag, intToNat_zigzag_is_bijection⟩

  end Int.Embedding

end ZFC

export ZFC.Int.Embedding (
  natToInt
  natToInt_graph
  natToInt_mem_IntSet
  natToInt_is_function
  natToInt_injective
  natToInt_preserves_add
  natToInt_preserves_mul
  natToInt_preserves_le
  natToInt_reflects_le
  natToInt_not_surjective
  intToNat_zigzag
  intToNat_zigzag_is_function
  intToNat_zigzag_injective
  intToNat_zigzag_surjective
  intToNat_zigzag_is_bijection
  IntSet_equipotent_omega
)
