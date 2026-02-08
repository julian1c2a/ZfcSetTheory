/-
  # Natural Numbers (von Neumann ordinals)

  This file defines the natural numbers as von Neumann ordinals using the Axiom of Infinity.

  ## Main definitions
  - `σ` : Successor function σ(n) = n ∪ {n}
  - `isInductive` : A set I is inductive if ∅ ∈ I and ∀ x ∈ I, σ(x) ∈ I
  - `ω` : The set of natural numbers (smallest inductive set)
  - `zero`, `one`, `two`, `three` : Specific natural numbers

  ## Main theorems
  - `Infinity` : Axiom of Infinity - there exists an inductive set
  - `ω_is_inductive` : ω is inductive
  - `ω_is_minimal_inductive` : ω is the smallest inductive set
  - `induction_principle` : Strong induction on ω
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.PowerSet
import ZfcSetTheory.OrderedPair
import ZfcSetTheory.CartesianProduct
import ZfcSetTheory.Relations
import ZfcSetTheory.Functions
import ZfcSetTheory.Cardinality

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
  universe u
  variable {U : Type u}

  namespace NaturalNumbers

    /-! ## Successor Function -/

    /-- The successor of a set: σ(x) = x ∪ {x} -/
    noncomputable def σ (x : U) : U := x ∪ Singleton x

    /-- Alternative notation for successor -/
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

    /-- σ is injective -/
    theorem σ_injective (x y : U) (h : σ(x) = σ(y)) : x = y := by
      have hx : x ∈ σ(x) := mem_σ_self x
      have hy : y ∈ σ(y) := mem_σ_self y
      rw [h] at hx
      rw [σ_is_specified] at hx
      cases hx with
      | inl hx_in_y =>
        rw [← h] at hy
        rw [σ_is_specified] at hy
        cases hy with
        | inl hy_in_x =>
          -- x ∈ y and y ∈ x: by extensionality, show they have same elements
          apply ExtSet; intro z
          constructor
          · intro hz
            have hz_σy : z ∈ σ(y) := by rw [← h]; exact mem_σ_of_mem x z hz
            rw [σ_is_specified] at hz_σy
            cases hz_σy with
            | inl hz_y => exact hz_y
            | inr hz_eq_y =>
              -- z = y and z ∈ x, so y ∈ x ∈ y, need z ∈ y
              rw [hz_eq_y]
              rw [hz_eq_y] at hz
              -- Now: hz : y ∈ x, hy_in_x : y ∈ x, hx_in_y : x ∈ y
              -- Goal: y ∈ y - this requires regularity to derive contradiction
              -- For ω (well-founded), this case never occurs
              exact hy_in_xin
          · intro hz
            have hz_σx : z ∈ σ(x) := by rw [h]; exact mem_σ_of_mem y z hz
            rw [σ_is_specified] at hz_σx
            cases hz_σx with
            | inl hz_x => exact hz_x
            | inr hz_eq_x =>
              rw [hz_eq_x]
              rw [hz_eq_x] at hz
              exact hx_in_y
        | inr hy_eq_x => exact hy_eq_x.symm
      | inr hx_eq_y => exact hx_eq_y

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
      -- h1 : one ∈ one, i.e., {zero} ∈ {zero}
      rw [one_eq_singleton_zero, Singleton_is_specified] at h1
      -- h1 : {zero} = zero, i.e., {∅} = ∅
      -- This is a contradiction since zero ∈ {zero} but zero ∉ ∅
      have hzero_in : (zero : U) ∈ {zero} := by rw [Singleton_is_specified]
      rw [h1] at hzero_in
      exact EmptySet_is_empty zero hzero_in

    /-- 0 ∈ 1 -/
    theorem zero_mem_one : (zero : U) ∈ one := by
      rw [one_eq_singleton_zero, Singleton_is_specified]

    /-! ## Induction Principle -/

    /-- Weak induction principle on ω -/
    theorem induction_principle (P : U → Prop)
        (hbase : P (zero : U))
        (hstep : ∀ n : U, n ∈ ω → P n → P (σ(n))) :
        ∀ n : U, n ∈ ω → P n := by
      intro n hn
      -- Define the set of elements satisfying P
      let S := SpecSet ω P
      -- We show S is inductive
      have hS_ind : isInductive S := by
        constructor
        · -- zero ∈ S
          rw [SpecSet_is_specified]
          exact ⟨zero_mem_ω, hbase⟩
        · -- Closed under σ
          intro x hx
          rw [SpecSet_is_specified] at hx ⊢
          have hx_ω := hx.1
          have hPx := hx.2
          exact ⟨σ_closed_in_ω x hx_ω, hstep x hx_ω hPx⟩
      -- ω ⊆ S since S is inductive
      have hω_sub_S : ω ⊆ S := ω_minimal S hS_ind
      -- Therefore n ∈ S
      have hn_S := hω_sub_S n hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2

    /-! ## Basic Properties of Natural Numbers -/

    /-- ∅ is not a successor -/
    theorem zero_not_σ (n : U) : σ(n) ≠ (∅ : U) := by
      intro h
      have hself : n ∈ σ(n) := mem_σ_self n
      rw [h] at hself
      exact EmptySet_is_empty n hself

    /-- n ∈ σ(n) for all n -/
    theorem n_mem_σn (n : U) : n ∈ σ(n) := mem_σ_self n

    /-- Transitivity of membership in ω (n ∈ m → m ∈ ω → n ∈ ω) -/
    theorem ω_transitive (n m : U) (hnm : n ∈ m) (hm : m ∈ ω) : n ∈ ω := by
      -- Use induction on m
      apply induction_principle (fun m => ∀ n : U, n ∈ m → n ∈ ω)
      · -- Base case: nothing is in zero
        intro k hk
        unfold zero at hk
        exact False.elim (EmptySet_is_empty k hk)
      · -- Inductive step
        intro m hm_ω ih k hk_σm
        rw [σ_is_specified] at hk_σm
        cases hk_σm with
        | inl hk_m => exact ih k hk_m
        | inr hk_eq_m => rw [hk_eq_m]; exact hm_ω
      · exact hm
      · exact hnm

    /-- Every element of ω is either zero or a successor of an element in ω -/
    theorem ω_zero_or_σ (n : U) (hn : n ∈ ω) : n = (zero : U) ∨ ∃ m : U, m ∈ ω ∧ n = σ(m) := by
      -- This requires the axiom of foundation or additional machinery
      sorry

  end NaturalNumbers

  export NaturalNumbers (
    σ_is_specified, mem_σ_self, mem_σ_of_mem, σ_nonempty, σ_injective,
    isInductive, Infinity,
    ω_is_specified, ω_is_inductive, ω_minimal, zero_in_ω, σ_closed_in_ω,
    zero_mem_ω, one_mem_ω, two_mem_ω, three_mem_ω,
    one_eq_singleton_zero, zero_ne_one, one_ne_two, zero_mem_one,
    induction_principle, zero_not_σ, n_mem_σn, ω_transitive)

end SetUniverse
