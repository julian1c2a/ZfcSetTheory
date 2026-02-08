/-
  # Natural Numbers (von Neumann ordinals)

  This file defines each natural number as a von Neumann ordinal.

  ## Main definitions
  - `σ` : Successor function σ(n) = n ∪ {n}
  - `is_natural_number` n ↔ n = ∅ ∨ ∃ m, `is_natural_number`m  ∧ n = σ(m)
  - `isTransitive` x :
    - ∅ ∈ x
    - ∀ y ∈ x, y ⊆ x
    - ∀ y ∈ x, `isTransitive` y
  - `is_natural_number` n → `isTransitive` n
  - `isInductive` : A set I is inductive if I is closed under transitivity

  ## Main theorems
  - `each_elements_of_transitive_set` : Every element of a transitive set is a transitive set
  - `ω_no_self_membership` : No element of ω contains itself
  - `σ_injective_on_ω` : σ is injective on ω
  - `induction_principle` : Induction on ω
-/

import ZfcSetTheory.Functions

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  universe u
  variable {U : Type u}

  namespace NaturalNumbers

    /-! ## Successor Function -/

    /-- The successor of a set: σ(x) = x ∪ {x} -/
    noncomputable def σ (x : U) : U := x ∪ Singleton x

    /-- Notation for successor -/
    notation:max "σ(" x ")" => σ x

    /-- Characterization of σ -/
    theorem σ_is_specified (x y : U) : y ∈ σ(x) ↔ y ∈ x ∨ y = x := by
      unfold σ
      rw [BinUnion_is_specified, Singleton_is_specified]

    /-- x is always in its successor -/
    theorem mem_σ_self (x : U) : x ∈ σ(x) := by
      rw [σ_is_specified]
      right; rfl

    /-- Elements of x are in σ(x) -/
    theorem mem_σ_of_mem (x y : U) (h : y ∈ x) : y ∈ σ(x) := by
      rw [σ_is_specified]
      left; exact h

    /-- σ(x) is never empty -/
    theorem σ_nonempty (x : U) : σ(x) ≠ ∅ := by
      intro h
      have hself : x ∈ σ(x) := mem_σ_self x
      rw [h] at hself
      exact EmptySet_is_empty x hself

    /-! ## Transitive Sets -/

    /-- A set x is transitive if every element is also a subset -/
    def isTransitive (x : U) : Prop :=
      ∀ y, y ∈ x → y ⊆ x

    /-- The empty set is transitive -/
    theorem empty_is_transitive : isTransitive (∅ : U) := by
      intro y hy
      exact False.elim (EmptySet_is_empty y hy)

    /-- If x is transitive, then σ(x) is transitive -/
    theorem σ_preserves_transitive (a : U) (ha : isTransitive a) : isTransitive (σ(a)) := by
      intro y hy
      rw [σ_is_specified] at hy
      cases hy with
      | inl hy_in_a =>
        -- y ∈ a, so y ⊆ a ⊆ σ(a)
        intro z hz
        have hz_in_a : z ∈ a := ha y hy_in_a z hz
        exact mem_σ_of_mem a z hz_in_a
      | inr hy_eq_a =>
        -- y = a, so y ⊆ σ(a) because a ⊆ σ(a)
        rw [hy_eq_a]
        intro z hz
        exact mem_σ_of_mem a z hz

    /-- For transitive sets: if y ∈ x and z ∈ y, then z ∈ x -/
    theorem transitive_chain (x : U) (hx : isTransitive x) (y z : U)
        (hy : y ∈ x) (hz : z ∈ y) : z ∈ x := by
      exact hx y hy z hz

    /-- In a transitive set, membership is transitive -/
    theorem mem_transitive_of_mem_mem (x y z : U) (hx : isTransitive x)
        (hzy : z ∈ y) (hyx : y ∈ x) : z ∈ x :=
      hx y hyx z hzy

    /-! ## Inductive Sets -/

    /-- A set I is inductive if ∅ ∈ I and it's closed under successor -/
    def isInductive (I : U) : Prop :=
      ∅ ∈ I ∧ ∀ x, x ∈ I → σ(x) ∈ I

    /-! ## Axiom of Infinity -/

    /-- Axiom of Infinity: There exists an inductive set -/
    axiom Infinity : ∃ (I : U), isInductive I

    /-! ## The Set of Natural Numbers ω -/

    /-- ω is the intersection of all inductive sets -/
    noncomputable def ω : U :=
      let I := Classical.choose (@Infinity U)
      SpecSet I (fun x => ∀ J : U, isInductive J → x ∈ J)

    /-- Characterization of ω -/
    theorem ω_is_specified (x : U) : x ∈ ω ↔ ∀ J : U, isInductive J → x ∈ J := by
      unfold ω
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · exact h _ (Classical.choose_spec (@Infinity U))
        · exact h

    /-- ω is inductive -/
    theorem ω_is_inductive : isInductive (ω : U) := by
      constructor
      · -- ∅ ∈ ω
        rw [ω_is_specified]
        intro J hJ
        exact hJ.1
      · -- Closed under σ
        intro x hx
        rw [ω_is_specified] at hx ⊢
        intro J hJ
        exact hJ.2 x (hx J hJ)

    /-- ω is the smallest inductive set -/
    theorem ω_minimal (I : U) (hI : isInductive I) : ω ⊆ I := by
      intro x hx
      rw [ω_is_specified] at hx
      exact hx I hI

    /-- Empty set is in ω -/
    theorem zero_in_ω : (∅ : U) ∈ ω := ω_is_inductive.1

    /-- ω is closed under successor -/
    theorem σ_closed_in_ω (x : U) (hx : x ∈ ω) : σ(x) ∈ ω := ω_is_inductive.2 x hx

    /-! ## Induction Principle -/

    /-- Induction principle on ω -/
    theorem induction_principle (P : U → Prop)
        (hbase : P (∅ : U))
        (hstep : ∀ n : U, n ∈ ω → P n → P (σ(n))) :
        ∀ n : U, n ∈ ω → P n := by
      intro n hn
      let S := SpecSet ω P
      have hS_ind : isInductive S := by
        constructor
        · rw [SpecSet_is_specified]
          exact ⟨zero_in_ω, hbase⟩
        · intro x hx
          rw [SpecSet_is_specified] at hx ⊢
          exact ⟨σ_closed_in_ω x hx.1, hstep x hx.1 hx.2⟩
      have hω_sub_S : ω ⊆ S := ω_minimal S hS_ind
      have hn_S := hω_sub_S n hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2

    /-! ## Properties of ω Elements via Induction -/

    /-- Every element of ω is transitive -/
    theorem ω_elements_transitive : ∀ n : U, n ∈ ω → isTransitive n := by
      apply induction_principle
      · -- Base: ∅ is transitive
        exact empty_is_transitive
      · -- Step: if n is transitive, so is σ(n)
        intro n _ hn_trans
        exact σ_preserves_transitive n hn_trans

    /-- Key lemma: if n ∈ ω and n is transitive, and m ∈ σ(n), then m ⊆ n -/
    theorem mem_σ_implies_subseteq (n m : U) (hn : isTransitive n)
        (hm : m ∈ σ(n)) : m ⊆ n := by
      rw [σ_is_specified] at hm
      cases hm with
      | inl hm_in_n =>
        -- m ∈ n, by transitivity m ⊆ n
        exact hn m hm_in_n
      | inr hm_eq_n =>
        -- m = n, so m ⊆ n trivially
        subst hm_eq_n
        intro z hz; exact hz

    /-- No element of ω contains itself -/
    theorem ω_no_self_membership : ∀ n : U, n ∈ ω → n ∉ n := by
      apply induction_principle
      · -- Base: ∅ ∉ ∅
        exact EmptySet_is_empty ∅
      · -- Step: if n ∉ n, then σ(n) ∉ σ(n)
        intro n hn_ω hn_not_self
        intro h_σn_in_σn
        -- σ(n) ∈ σ(n) means σ(n) ∈ n ∨ σ(n) = n
        rw [σ_is_specified] at h_σn_in_σn
        cases h_σn_in_σn with
        | inl h_σn_in_n =>
          -- σ(n) ∈ n, and n is transitive, so σ(n) ⊆ n
          have hn_trans := ω_elements_transitive n hn_ω
          have h_σn_sub_n := hn_trans (σ(n)) h_σn_in_n
          -- But n ∈ σ(n), so n ∈ n
          have hn_in_σn := mem_σ_self n
          have hn_in_n := h_σn_sub_n n hn_in_σn
          exact hn_not_self hn_in_n
        | inr h_σn_eq_n =>
          -- σ(n) = n, but n ∈ σ(n), so n ∈ n
          have hn_in_σn := mem_σ_self n
          rw [h_σn_eq_n] at hn_in_σn
          exact hn_not_self hn_in_σn

    /-- No membership cycles in ω: if m ∈ n ∈ ω, then n ∉ m -/
    theorem ω_no_membership_cycle (m n : U) (hn : n ∈ ω) (hm_in_n : m ∈ n) : n ∉ m := by
      intro hn_in_m
      have hn_trans := ω_elements_transitive n hn
      -- n is transitive and m ∈ n, so m ⊆ n
      have hm_sub_n := hn_trans m hm_in_n
      -- n ∈ m ⊆ n, so n ∈ n
      have hn_in_n := hm_sub_n n hn_in_m
      exact ω_no_self_membership n hn hn_in_n

    /-- σ is injective on ω -/
    theorem σ_injective_on_ω (x y : U) (hx : x ∈ ω) (hy : y ∈ ω)
        (h : σ(x) = σ(y)) : x = y := by
      have hx_in_σx := mem_σ_self x
      have hy_in_σy := mem_σ_self y
      rw [h] at hx_in_σx
      rw [σ_is_specified] at hx_in_σx
      cases hx_in_σx with
      | inl hx_in_y =>
        rw [← h] at hy_in_σy
        rw [σ_is_specified] at hy_in_σy
        cases hy_in_σy with
        | inl hy_in_x =>
          -- x ∈ y and y ∈ x, contradiction by no_membership_cycle
          exact False.elim (ω_no_membership_cycle x y hy hx_in_y hy_in_x)
        | inr hy_eq_x => exact hy_eq_x.symm
      | inr hx_eq_y => exact hx_eq_y

    /-- ∅ is not a successor in ω -/
    theorem zero_not_σ (n : U) : σ(n) ≠ (∅ : U) := by
      intro h
      have hself : n ∈ σ(n) := mem_σ_self n
      rw [h] at hself
      exact EmptySet_is_empty n hself

    /-! ## Specific Natural Numbers -/

    /-- 0 = ∅ -/
    noncomputable def zero : U := ∅

    /-- 1 = {∅} = σ(0) -/
    noncomputable def one : U := σ(zero)

    /-- 2 = {∅, {∅}} = σ(1) -/
    noncomputable def two : U := σ(one)

    /-- 3 = {∅, {∅}, {∅, {∅}}} = σ(2) -/
    noncomputable def three : U := σ(two)

    /-- 0 ∈ ω -/
    theorem zero_mem_ω : (zero : U) ∈ ω := zero_in_ω

    /-- 1 ∈ ω -/
    theorem one_mem_ω : (one : U) ∈ ω := σ_closed_in_ω zero zero_mem_ω

    /-- 2 ∈ ω -/
    theorem two_mem_ω : (two : U) ∈ ω := σ_closed_in_ω one one_mem_ω

    /-- 3 ∈ ω -/
    theorem three_mem_ω : (three : U) ∈ ω := σ_closed_in_ω two two_mem_ω

    /-- 1 = {∅} -/
    theorem one_eq_singleton_zero : (one : U) = {zero} := by
      unfold one zero σ
      apply ExtSet; intro x
      rw [BinUnion_is_specified]
      constructor
      · intro h
        cases h with
        | inl h => exact False.elim (EmptySet_is_empty x h)
        | inr h => exact h
      · intro h; right; exact h

    /-- 0 ≠ 1 -/
    theorem zero_ne_one : (zero : U) ≠ one := by
      intro h
      have hempty : (zero : U) ∈ one := by
        rw [one_eq_singleton_zero, Singleton_is_specified]
      rw [← h] at hempty
      exact EmptySet_is_empty zero hempty

    /-- 1 ≠ 2 -/
    theorem one_ne_two : (one : U) ≠ two := by
      intro h
      have h1 : (one : U) ∈ two := mem_σ_self one
      rw [← h] at h1
      rw [one_eq_singleton_zero, Singleton_is_specified] at h1
      have hzero_in : (zero : U) ∈ {zero} := by rw [Singleton_is_specified]
      rw [h1] at hzero_in
      exact EmptySet_is_empty zero hzero_in

    /-- 0 ∈ 1 -/
    theorem zero_mem_one : (zero : U) ∈ one := by
      rw [one_eq_singleton_zero, Singleton_is_specified]

    /-- n ∈ σ(n) for all n -/
    theorem n_mem_σn (n : U) : n ∈ σ(n) := mem_σ_self n

    /-- ω is transitive as a set -/
    theorem ω_is_transitive_set : isTransitive (ω : U) := by
      intro n hn m hm
      -- n ∈ ω and m ∈ n, need to show m ∈ ω
      -- Use the fact that elements of ω are built inductively
      have h : ∀ n : U, n ∈ ω → ∀ m : U, m ∈ n → m ∈ ω := by
        apply induction_principle
        · -- Base case: nothing is in ∅
          intro m hm_empty
          exact False.elim (EmptySet_is_empty m hm_empty)
        · -- Inductive step
          intro k hk_ω ih m hm_σk
          rw [σ_is_specified] at hm_σk
          cases hm_σk with
          | inl hm_k => exact ih m hm_k
          | inr hm_eq_k => subst hm_eq_k; exact hk_ω
      exact h n hn m hm

    /-- Membership in ω is transitive -/
    theorem ω_transitive (n m : U) (hnm : n ∈ m) (hm : m ∈ ω) : n ∈ ω :=
      ω_is_transitive_set m hm n hnm

    /-- Every element of ω is either zero or a successor -/
    theorem ω_zero_or_σ (n : U) (hn : n ∈ ω) : n = (zero : U) ∨ ∃ m : U, m ∈ ω ∧ n = σ(m) := by
      -- We need the axiom of replacement or foundation for this
      -- For now, we leave it as sorry
      sorry

  end NaturalNumbers

  export NaturalNumbers (
    σ_is_specified, mem_σ_self, mem_σ_of_mem, σ_nonempty,
    isTransitive, empty_is_transitive, σ_preserves_transitive,
    transitive_chain, mem_transitive_of_mem_mem,
    isInductive, Infinity,
    ω_is_specified, ω_is_inductive, ω_minimal, zero_in_ω, σ_closed_in_ω,
    induction_principle,
    ω_elements_transitive, mem_σ_implies_subseteq,
    ω_no_self_membership, ω_no_membership_cycle, σ_injective_on_ω,
    zero_not_σ,
    zero_mem_ω, one_mem_ω, two_mem_ω, three_mem_ω,
    one_eq_singleton_zero, zero_ne_one, one_ne_two, zero_mem_one,
    n_mem_σn, ω_is_transitive_set, ω_transitive
  )

end SetUniverse
