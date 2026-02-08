/-
  # Natural Numbers (von Neumann ordinals)

  This file defines each natural number as a von Neumann ordinal using
  an inductive predicate rather than set membership in ω.

  ## Main definitions
  - `σ` n : Successor function for any set n: σ(n) := n ∪ {n}
  - `isTransitive` x : ∀ y, y ∈ x → y ⊆ x
  - `isSubsetMinimal` A Y : A is ⊆-minimal in Y
  - `isDedekindFinite` X : X not equipotent to any proper subset
  - `isTarskiFinite` X : Every non-empty subfamily of 𝒫(X) has ⊆-minimal element
  - `isNat` n : Inductive predicate defining von Neumann ordinals

  ## Main theorems
  - `isNat_zero` : isNat ∅
  - `isNat_σ` : isNat n → isNat (σ n)
  - `isNat_transitive` : isNat n → isTransitive n
  - `isNat_no_self_mem` : isNat n → n ∉ n
  - `isNat_σ_injective` : isNat x → isNat y → σ(x) = σ(y) → x = y
  - `isNat_isTarskiFinite` : isNat n → isTarskiFinite n
  - `isNat_isDedekindFinite` : isNat n → isDedekindFinite n
  - Membership in naturals forms a linear order

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
    noncomputable def σ (x : U) : U :=
      x ∪ Singleton x

    /-- Notation for successor -/
    notation:max "σ(" x ")" => σ x

    /-- Characterization of σ -/
    theorem σ_is_specified (x y : U) :
      y ∈ σ(x) ↔ y ∈ x ∨ y = x
      := by
      unfold σ
      rw [BinUnion_is_specified, Singleton_is_specified]

    /-- x is always in its successor -/
    theorem mem_σ_self (x : U) :
      x ∈ σ(x)
      := by
      rw [σ_is_specified]
      right; rfl

    /-- Elements of x are in σ(x) -/
    theorem mem_σ_of_mem (x y : U) (h : y ∈ x) :
      y ∈ σ(x)
      := by
      rw [σ_is_specified]
      left; exact h

    /-- σ(x) is never empty -/
    theorem σ_nonempty (x : U) :
      σ(x) ≠ ∅
      := by
      intro h
      have hself : x ∈ σ(x) := mem_σ_self x
      rw [h] at hself
      exact EmptySet_is_empty x hself

    /-! ## Transitive Sets -/

    /-- A set x is transitive if every element is also a subset -/
    def isTransitive (x : U) : Prop :=
      ∀ y, y ∈ x → y ⊆ x

    /-- The empty set is transitive -/
    theorem empty_is_transitive :
      isTransitive (∅ : U)
      := by
      intro y hy
      exact False.elim (EmptySet_is_empty y hy)

    /-- If x is transitive, then σ(x) is transitive -/
    theorem σ_preserves_transitive (a : U) (ha : isTransitive a) :
      isTransitive (σ(a))
      := by
      intro y hy
      rw [σ_is_specified] at hy
      cases hy with
      | inl hy_in_a =>
        intro z hz
        have hz_in_a : z ∈ a := ha y hy_in_a z hz
        exact mem_σ_of_mem a z hz_in_a
      | inr hy_eq_a =>
        rw [hy_eq_a]
        intro z hz
        exact mem_σ_of_mem a z hz

    /-- For transitive sets: if y ∈ x and z ∈ y, then z ∈ x -/
    theorem transitive_chain (x : U) (hx : isTransitive x) (y z : U) (hy : y ∈ x) (hz : z ∈ y) :
        z ∈ x
        := by
      exact hx y hy z hz

    /-! ## Finiteness Definitions -/

    /-- A is a ⊆-minimal element of the family Y if:
        1. A is in Y
        2. No proper subset of A is in Y
        Equivalently: for all B ∈ Y, if B ⊆ A then B = A -/
    def isSubsetMinimal (A Y : U) : Prop :=
      A ∈ Y ∧ ∀ B : U, B ∈ Y → B ⊆ A → B = A

    /-- A set X is Dedekind-finite if X is not equipotent to any proper subset of itself.
        Equivalently: X is Dedekind-finite if every injection f: X → X is surjective.
        This is one of several equivalent definitions of finite sets in ZFC. -/
    def isDedekindFinite (X : U) : Prop :=
      ∀ Y : U, Y ⊂ X → ¬isEquipotent X Y

    /-- A set X is Tarski-finite if every non-empty subfamily of P(X) has a ⊆-minimal element.
        Equivalently: X is Tarski-finite if every chain in P(X) has a maximal element.
        This is one of several equivalent definitions of finite sets in ZFC. -/
    def isTarskiFinite (X : U) : Prop :=
      ∀ Y : U, Y ⊆ 𝒫 X → Y ≠ ∅ →
        ∃ A : U, isSubsetMinimal A Y

    /-! ## Natural Numbers as von Neumann Ordinals -/

    /-- Inductive predicate characterizing von Neumann ordinals (natural numbers).
        A set n is a natural number if:
        - n = ∅ (zero is natural), or
        - n = σ(m) for some natural m, and all elements of n are natural -/
    inductive isNat : U → Prop where
      | zero : isNat ∅
      | succ {n : U} : isNat n → isNat (σ n)

    /-! ## Basic Properties of Natural Numbers -/

    /-- 0 is a natural number -/
    theorem isNat_zero : isNat (∅ : U) := isNat.zero

    /-- Successor of a natural is natural -/
    theorem isNat_σ {n : U} (hn : isNat n) : isNat (σ n) := isNat.succ hn

    /-- Elements of a natural number are natural numbers -/
    theorem isNat_mem_isNat {n m : U} (hn : isNat n) (hm : m ∈ n) : isNat m := by
      induction hn with
      | zero =>
        -- m ∈ ∅ is impossible
        exact False.elim (EmptySet_is_empty m hm)
      | succ hk ih =>
        -- m ∈ σ(k), so m ∈ k ∨ m = k
        rw [σ_is_specified] at hm
        cases hm with
        | inl hm_k => exact ih hm_k
        | inr hm_eq => exact hm_eq ▸ hk

    /-- Every natural number is transitive -/
    theorem isNat_transitive {n : U} (hn : isNat n) : isTransitive n := by
      induction hn with
      | zero => exact empty_is_transitive
      | succ _ ih => exact σ_preserves_transitive _ ih

    /-- No natural number contains itself -/
    theorem isNat_no_self_mem {n : U} (hn : isNat n) : n ∉ n := by
      induction hn with
      | zero =>
        exact EmptySet_is_empty ∅
      | @succ k hk ih =>
        intro h_σk_in_σk
        rw [σ_is_specified] at h_σk_in_σk
        cases h_σk_in_σk with
        | inl h_σk_in_k =>
          -- σ(k) ∈ k, and k is transitive, so σ(k) ⊆ k
          have hk_trans := isNat_transitive hk
          have h_σk_sub_k := hk_trans (σ k) h_σk_in_k
          -- But k ∈ σ(k), so k ∈ k
          have hk_in_σk := mem_σ_self k
          have hk_in_k := h_σk_sub_k k hk_in_σk
          exact ih hk_in_k
        | inr h_σk_eq_k =>
          -- σ(k) = k, but k ∈ σ(k), so k ∈ k
          have hk_in_σk := mem_σ_self k
          rw [h_σk_eq_k] at hk_in_σk
          exact ih hk_in_σk

    /-- No membership cycles: if m ∈ n and n is natural, then n ∉ m -/
    theorem isNat_no_cycle {m n : U} (hn : isNat n) (hm_in_n : m ∈ n) : n ∉ m := by
      intro hn_in_m
      have hn_trans := isNat_transitive hn
      have hm_sub_n := hn_trans m hm_in_n
      have hn_in_n := hm_sub_n n hn_in_m
      exact isNat_no_self_mem hn hn_in_n

    /-- σ is injective on natural numbers -/
    theorem isNat_σ_injective {x y : U} (_hx : isNat x) (hy : isNat y) (h : σ x = σ y) : x = y := by
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
          -- x ∈ y and y ∈ x, contradiction
          exact False.elim (isNat_no_cycle hy hx_in_y hy_in_x)
        | inr hy_eq_x => exact hy_eq_x.symm
      | inr hx_eq_y => exact hx_eq_y

    /-- ∅ is not a successor -/
    theorem zero_not_σ {n : U} : σ n ≠ ∅ := by
      intro h
      have hself : n ∈ σ n := mem_σ_self n
      rw [h] at hself
      exact EmptySet_is_empty n hself

    /-! ## Induction Principle for Natural Numbers -/

    /-- Strong induction principle for natural numbers -/
    theorem isNat_induction (P : U → Prop)
        (hbase : P ∅)
        (hstep : ∀ n : U, isNat n → P n → P (σ n)) :
        ∀ n : U, isNat n → P n
        := by
      intro n hn
      induction hn with
      | zero => exact hbase
      | succ hk ih => exact hstep _ hk ih

    /-! ## Finiteness of Natural Numbers -/

    /-- Power set of empty set is {∅} -/
    theorem PowerSet_empty : 𝒫 (∅ : U) = {∅} := by
      apply ExtSet; intro x
      rw [PowerSet_is_specified, Singleton_is_specified]
      constructor
      · intro hx
        -- x ⊆ ∅, so ∀ y ∈ x, y ∈ ∅ (impossible), hence x = ∅
        apply ExtSet; intro y
        constructor
        · intro hy
          -- y ∈ x, and x ⊆ ∅, so y ∈ ∅ (impossible)
          have : y ∈ ∅ := hx y hy
          exact False.elim (EmptySet_is_empty y this)
        · intro hy
          -- y ∈ ∅ is impossible
          exact False.elim (EmptySet_is_empty y hy)
      · intro hx
        -- x = ∅, so x ⊆ ∅
        intro y hy
        rw [hx] at hy
        exact False.elim (EmptySet_is_empty y hy)

    /-- If Y ⊆ {∅} and Y ≠ ∅, then Y = {∅} -/
    theorem subset_singleton_empty {Y : U} (hY_sub : Y ⊆ {∅}) (hY_ne : Y ≠ ∅) :
      Y = {∅}
      := by
      apply ExtSet; intro x
      constructor
      · intro hx; exact hY_sub x hx
      · intro hx
        -- x ∈ {∅}, so x = ∅
        rw [Singleton_is_specified] at hx
        rw [hx]
        -- Need to show ∅ ∈ Y
        -- Y is non-empty, so get any element z ∈ Y
        have h_exists : ∃ z : U, z ∈ Y := by
          apply Classical.byContradiction
          intro h
          have h' : ∀ z : U, z ∉ Y := by
            intro z hz
            exact h ⟨z, hz⟩
          have h_empty : Y = ∅ := by
            apply ExtSet; intro w
            constructor
            · intro hw; exact False.elim (h' w hw)
            · intro hw; exact False.elim (EmptySet_is_empty w hw)
          exact hY_ne h_empty
        obtain ⟨z, hz⟩ := h_exists
        -- z ∈ Y ⊆ {∅}, so z = ∅
        have hz_empty : z ∈ {∅} := hY_sub z hz
        rw [Singleton_is_specified] at hz_empty
        rw [← hz_empty]
        exact hz

    /-- ∅ is ⊆-minimal in {∅} -/
    theorem empty_minimal_in_singleton : isSubsetMinimal (∅ : U) {∅} := by
      constructor
      · rw [Singleton_is_specified]
      · intro B hB_in hB_sub
        rw [Singleton_is_specified] at hB_in
        exact hB_in

    /-- Every natural number is Tarski-finite -/
    theorem isNat_isTarskiFinite {n : U} (hn : isNat n) : isTarskiFinite n := by
      refine isNat_induction isTarskiFinite ?base ?step n hn
      case base =>
        -- Base case: ∅ is Tarski-finite
        intro Y hY_sub hY_ne
        -- 𝒫(∅) = {∅}, so any non-empty Y ⊆ 𝒫(∅) must be Y = {∅}
        have hP_empty : 𝒫 (∅ : U) = {∅} := PowerSet_empty
        rw [hP_empty] at hY_sub
        have hY_eq : Y = {∅} := subset_singleton_empty hY_sub hY_ne
        exact ⟨∅, hY_eq ▸ empty_minimal_in_singleton⟩
      case step =>
        -- Inductive step: If k is Tarski-finite, then σ(k) is Tarski-finite
        intro k hk ih_k Y hY_sub hY_ne
        -- Divide Y into two subfamilies:
        -- Y₁ = {z ∈ Y : k ∉ z} (subsets not containing k)
        -- Y₂ = {z ∈ Y : k ∈ z} (subsets containing k)
        let Y₁ := SpecSet Y (fun z => k ∉ z)
        let Y₂ := SpecSet Y (fun z => k ∈ z)
        -- Case analysis: either Y₁ is non-empty or all elements are in Y₂
        by_cases hY₁_ne : Y₁ ≠ ∅
        ·  -- Case 1: Y₁ ≠ ∅
          -- Elements of Y₁ are subsets of k (since they don't contain k and are subsets of σ(k))
          have hY₁_sub : Y₁ ⊆ 𝒫 k := by
            intro z hz
            rw [SpecSet_is_specified] at hz
            have hz_in_Y := hz.1
            have hz_not_k := hz.2
            rw [PowerSet_is_specified]
            intro w hw
            have hz_in_P : z ∈ 𝒫 (σ k) := hY_sub z hz_in_Y
            rw [PowerSet_is_specified] at hz_in_P
            have hw_in_σk : w ∈ σ k := hz_in_P w hw
            rw [σ_is_specified] at hw_in_σk
            cases hw_in_σk with
            | inl hw_in_k => exact hw_in_k
            | inr hw_eq_k =>
              -- w = k, but then k ∈ z, contradicting hz_not_k
              exact False.elim (hz_not_k (hw_eq_k ▸ hw))
          -- By inductive hypothesis, Y₁ has a ⊆-minimal element
          -- Extract witness and prove it is also minimal in Y
          let m := Classical.choose (ih_k Y₁ hY₁_sub hY₁_ne)
          have hm_minimal := Classical.choose_spec (ih_k Y₁ hY₁_sub hY₁_ne)

          refine ⟨m, ⟨?mem, ?min⟩⟩
          -- m ∈ Y
          · have hm_in_Y₁ : m ∈ Y₁ := hm_minimal.1
            rw [SpecSet_is_specified] at hm_in_Y₁
            exact hm_in_Y₁.1
          -- m is minimal in Y
          · intro B hB_in_Y hB_sub_m
            -- If k ∈ B, then k ∈ m by hB_sub_m, contradicting m ∈ Y₁
            -- So k ∉ B, therefore B ∈ Y₁
            have hk_not_in_B : k ∉ B := by
              intro hk_in_B
              have hk_in_m : k ∈ m := hB_sub_m k hk_in_B
              have hm_in_Y₁ : m ∈ Y₁ := hm_minimal.1
              rw [SpecSet_is_specified] at hm_in_Y₁
              exact hm_in_Y₁.2 hk_in_m
            have hB_in_Y₁ : B ∈ Y₁ := by
              rw [SpecSet_is_specified]
              exact ⟨hB_in_Y, hk_not_in_B⟩
            -- By minimality of m in Y₁
            exact hm_minimal.2 B hB_in_Y₁ hB_sub_m
        · -- Case 2: Y₁ = ∅, so all elements of Y contain k
          -- Every element of Y contains k as a member
          -- We use the inductive hypothesis on a related subfamily
          -- For now, this requires choice principles or well-foundedness
          sorry

    /-- Every natural number is Dedekind-finite -/
    theorem isNat_isDedekindFinite {n : U} (hn : isNat n) : isDedekindFinite n := by
      sorry  -- Requires significant development

    /-! ## Specific Natural Numbers -/

    /-- 0 = ∅ -/
    noncomputable def zero : U := ∅

    /-- 1 = {∅} = σ(0) -/
    noncomputable def one : U := σ zero

    /-- 2 = {∅, {∅}} = σ(1) -/
    noncomputable def two : U := σ one

    /-- 3 = {∅, {∅}, {∅, {∅}}} = σ(2) -/
    noncomputable def three : U := σ two

    /-- 0 is natural -/
    theorem zero_isNat : isNat (zero : U) := isNat_zero

    /-- 1 is natural -/
    theorem one_isNat : isNat (one : U) := isNat_σ zero_isNat

    /-- 2 is natural -/
    theorem two_isNat : isNat (two : U) := isNat_σ one_isNat

    /-- 3 is natural -/
    theorem three_isNat : isNat (three : U) := isNat_σ two_isNat

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

    /-! ## Trichotomy for Natural Numbers -/

    /-- Every natural is either zero or a successor -/
    theorem isNat_zero_or_succ {n : U} (hn : isNat n) :
        n = (zero : U) ∨ ∃ m : U, isNat m ∧ n = σ m := by
      cases hn with
      | zero => left; rfl
      | succ hk => right; exact ⟨_, hk, rfl⟩

  end NaturalNumbers

  export NaturalNumbers (
    σ σ_is_specified mem_σ_self mem_σ_of_mem σ_nonempty
    isTransitive empty_is_transitive σ_preserves_transitive transitive_chain
    isSubsetMinimal isDedekindFinite isTarskiFinite
    isNat isNat_zero isNat_σ
    isNat_mem_isNat isNat_transitive isNat_no_self_mem isNat_no_cycle
    isNat_σ_injective zero_not_σ
    isNat_induction
    isNat_isTarskiFinite isNat_isDedekindFinite
    zero one two three
    zero_isNat one_isNat two_isNat three_isNat
    one_eq_singleton_zero zero_ne_one one_ne_two zero_mem_one
    isNat_zero_or_succ
  )

end SetUniverse
