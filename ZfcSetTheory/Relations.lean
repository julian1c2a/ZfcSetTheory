/-
Copyright (c) 2025. All rights reserved.
Author: ZfcSetTheory project
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

/-!
# Relations on Sets

This file defines relations on sets using the Cartesian product, and establishes
fundamental properties: reflexivity, symmetry, antisymmetry, transitivity, and
derived concepts like equivalence relations, preorders, partial orders, linear orders,
and strict orders.

## Main Definitions

* `isRelationOn R A` - R is a relation on A (R ⊆ A ×ₛ A)
* `isReflexiveOn R A` - R is reflexive on A
* `isSymmetricOn R A` - R is symmetric on A
* `isTransitiveOn R A` - R is transitive on A
* `isEquivalenceOn R A` - R is an equivalence relation on A
* `isPartialOrderOn R A` - R is a partial order on A
* `isLinearOrderOn R A` - R is a linear (total) order on A
* `isStrictOrderOn R A` - R is a strict order on A
* `EqClass a R A` - The equivalence class of a under R within A

## Main Theorems

* `Asymmetric_implies_Irreflexive` - Asymmetry implies irreflexivity
* `StrictOrder_is_Irreflexive` - Strict orders are irreflexive
* `IdRel_is_Equivalence` - The identity relation is an equivalence relation
-/

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
  universe u
  variable {U : Type u}

  namespace Relations

    /-! ### Basic Relation Definition -/

    /-- A relation R on a set A is a subset of the Cartesian product A ×ₛ A -/
    def isRelationOn (R A : U) : Prop := R ⊆ (A ×ₛ A)

    /-- A relation R from A to B is a subset of A ×ₛ B -/
    def isRelationFrom (R A B : U) : Prop := R ⊆ (A ×ₛ B)

    /-- R relates x to y -/
    def Related (R x y : U) : Prop := ⟨x, y⟩ ∈ R

    /-! ### Fundamental Properties of Relations -/

    /-- R is reflexive on A: for all x ∈ A, (x, x) ∈ R -/
    def isReflexiveOn (R A : U) : Prop :=
      ∀ x : U, x ∈ A → ⟨x, x⟩ ∈ R

    /-- R is irreflexive on A: for all x ∈ A, (x, x) ∉ R -/
    def isIrreflexiveOn (R A : U) : Prop :=
      ∀ x : U, x ∈ A → ⟨x, x⟩ ∉ R

    /-- R is symmetric on A: for all x, y ∈ A, (x, y) ∈ R → (y, x) ∈ R -/
    def isSymmetricOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R

    /-- R is antisymmetric on A: for all x, y ∈ A, (x, y) ∈ R ∧ (y, x) ∈ R → x = y -/
    def isAntiSymmetricOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y

    /-- R is asymmetric on A: for all x, y ∈ A, (x, y) ∈ R → (y, x) ∉ R -/
    def isAsymmetricOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∉ R

    /-- R is transitive on A: for all x, y, z ∈ A, (x, y) ∈ R ∧ (y, z) ∈ R → (x, z) ∈ R -/
    def isTransitiveOn (R A : U) : Prop :=
      ∀ x y z : U, x ∈ A → y ∈ A → z ∈ A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R

    /-- R is connected (total) on A: for all distinct x, y ∈ A, (x, y) ∈ R ∨ (y, x) ∈ R -/
    def isConnectedOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A → x ≠ y → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R

    /-- R is strongly connected on A: for all x, y ∈ A, (x, y) ∈ R ∨ (y, x) ∈ R -/
    def isStronglyConnectedOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R

    /-- R is trichotomous on A: for all x, y ∈ A, exactly one of x < y, x = y, y < x -/
    def isTrichotomousOn (R A : U) : Prop :=
      ∀ x y : U, x ∈ A → y ∈ A →
        (⟨x, y⟩ ∈ R ∧ x ≠ y ∧ ⟨y, x⟩ ∉ R) ∨
        (⟨x, y⟩ ∉ R ∧ x = y ∧ ⟨y, x⟩ ∉ R) ∨
        (⟨x, y⟩ ∉ R ∧ x ≠ y ∧ ⟨y, x⟩ ∈ R)

    /-! ### Composite Relation Types -/

    /-- R is an equivalence relation on A -/
    def isEquivalenceOn (R A : U) : Prop :=
      isRelationOn R A ∧ isReflexiveOn R A ∧ isSymmetricOn R A ∧ isTransitiveOn R A

    /-- R is a preorder on A (reflexive and transitive) -/
    def isPreorderOn (R A : U) : Prop :=
      isRelationOn R A ∧ isReflexiveOn R A ∧ isTransitiveOn R A

    /-- R is a partial order on A (reflexive, antisymmetric, and transitive) -/
    def isPartialOrderOn (R A : U) : Prop :=
      isRelationOn R A ∧ isReflexiveOn R A ∧ isAntiSymmetricOn R A ∧ isTransitiveOn R A

    /-- R is a linear (total) order on A -/
    def isLinearOrderOn (R A : U) : Prop :=
      isPartialOrderOn R A ∧ isConnectedOn R A

    /-- R is a strict order on A (irreflexive and transitive) -/
    def isStrictOrderOn (R A : U) : Prop :=
      isRelationOn R A ∧ isIrreflexiveOn R A ∧ isTransitiveOn R A

    /-- R is a strict partial order on A (asymmetric and transitive) -/
    def isStrictPartialOrderOn (R A : U) : Prop :=
      isRelationOn R A ∧ isAsymmetricOn R A ∧ isTransitiveOn R A

    /-- R is a strict linear order on A (strict order + trichotomous) -/
    def isStrictLinearOrderOn (R A : U) : Prop :=
      isStrictOrderOn R A ∧ isTrichotomousOn R A

    /-! ### Well-Founded Relations -/

    /-- R is well-founded on A: every non-empty subset has a minimal element -/
    def isWellFoundedOn (R A : U) : Prop :=
      ∀ S : U, S ⊆ A → S ≠ ∅ → ∃ m : U, m ∈ S ∧ ∀ x : U, x ∈ S → ⟨x, m⟩ ∉ R

    /-- R is a well-order on A -/
    def isWellOrderOn (R A : U) : Prop :=
      isLinearOrderOn R A ∧ isWellFoundedOn R A

    /-! ### Equivalence Classes -/

    /-- The equivalence class of a under R within set A:
        EqClass a R A = {x ∈ A | (a, x) ∈ R} -/
    noncomputable def EqClass (a R A : U) : U :=
      SpecSet A (fun x => ⟨a, x⟩ ∈ R)

    /-- The quotient set A/R: the set of all equivalence classes -/
    noncomputable def QuotientSet (A R : U) : U :=
      SpecSet (𝒫 A) (fun C => ∃ a : U, a ∈ A ∧ C = EqClass a R A)

    /-! ### Relation Constructions -/

    /-- The identity relation on A: IdRel A = {(x, x) | x ∈ A} -/
    noncomputable def IdRel (A : U) : U :=
      SpecSet (A ×ₛ A) (fun p => fst p = snd p)

    /-- The inverse relation R⁻¹ = {(y, x) | (x, y) ∈ R} -/
    noncomputable def InverseRel (R : U) : U :=
      SpecSet (𝒫 (𝒫 (⋃(⋃ R)))) (fun p => ⟨snd p, fst p⟩ ∈ R)

    /-! ### Domain and Range for Relations -/

    /-- Domain of a relation R (properly defined for relations):
        domain_rel R = {x | ∃ y, ⟨x, y⟩ ∈ R} -/
    noncomputable def domain_rel (R : U) : U :=
      SpecSet (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)

    /-- Range (image) of a relation R (properly defined for relations):
        range_rel R = {y | ∃ x, ⟨x, y⟩ ∈ R} -/
    noncomputable def range_rel (R : U) : U :=
      SpecSet (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)

    /-- Alternative name for range_rel -/
    noncomputable def imag_rel (R : U) : U := range_rel R

    /-! ### Theorems about Relation Properties -/

    /-- If R is asymmetric on A, then R is irreflexive on A -/
    theorem Asymmetric_implies_Irreflexive (R A : U) :
        isAsymmetricOn R A → isIrreflexiveOn R A := by
      intro hAsym x hxA hxx
      exact hAsym x x hxA hxA hxx hxx

    /-- A strict order is irreflexive -/
    theorem StrictOrder_is_Irreflexive (R A : U) :
        isStrictOrderOn R A → isIrreflexiveOn R A := by
      intro h
      exact h.2.1

    /-- A strict partial order is irreflexive -/
    theorem StrictPartialOrder_is_Irreflexive (R A : U) :
        isStrictPartialOrderOn R A → isIrreflexiveOn R A := by
      intro h
      exact Asymmetric_implies_Irreflexive R A h.2.1

    /-- If R is irreflexive and transitive on A, then R is asymmetric on A -/
    theorem Irreflexive_Transitive_implies_Asymmetric (R A : U) :
        isIrreflexiveOn R A → isTransitiveOn R A →
        isAsymmetricOn R A := by
      intro hIrr hTrans x y hxA hyA hxy hyx
      have hxx : ⟨x, x⟩ ∈ R := hTrans x y x hxA hyA hxA hxy hyx
      exact hIrr x hxA hxx

    /-- Asymmetry is equivalent to irreflexivity + antisymmetry (for transitive relations) -/
    theorem Asymmetric_iff_Irreflexive_and_AntiSymmetric (R A : U)
        (hTrans : isTransitiveOn R A) :
        isAsymmetricOn R A ↔ isIrreflexiveOn R A ∧ isAntiSymmetricOn R A := by
      constructor
      · intro hAsym
        constructor
        · exact Asymmetric_implies_Irreflexive R A hAsym
        · intro x y hxA hyA hxy hyx
          exfalso
          exact hAsym x y hxA hyA hxy hyx
      · intro hIrrAnti
        exact Irreflexive_Transitive_implies_Asymmetric R A hIrrAnti.1 hTrans

    /-- A partial order with connectivity is a linear order -/
    theorem PartialOrder_Connected_is_LinearOrder (R A : U) :
        isPartialOrderOn R A → isConnectedOn R A → isLinearOrderOn R A := by
      intro hPO hConn
      exact ⟨hPO, hConn⟩

    /-- Linear order: any two elements are comparable -/
    theorem LinearOrder_comparable (R A : U) (hLO : isLinearOrderOn R A)
        (x y : U) (hxA : x ∈ A) (hyA : y ∈ A) :
        ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R := by
      have hPO := hLO.1
      have hConn := hLO.2
      have hRefl := hPO.2.1
      by_cases heq : x = y
      · subst heq
        left
        exact hRefl x hxA
      · exact hConn x y hxA hyA heq

    /-- A strict order with connectivity is trichotomous -/
    theorem StrictOrder_Connected_is_Trichotomous (R A : U)
        (hStrict : isStrictOrderOn R A) (hConn : isConnectedOn R A) :
        isTrichotomousOn R A := by
      intro x y hxA hyA
      have hIrr := hStrict.2.1
      have hTrans := hStrict.2.2
      -- Derive asymmetry from irreflexivity and transitivity
      have hAsym := Irreflexive_Transitive_implies_Asymmetric R A hIrr hTrans
      by_cases heq : x = y
      · -- Case x = y: middle option (neither xRy nor yRx)
        right; left
        subst heq
        exact ⟨fun h => hIrr x hxA h, rfl, fun h => hIrr x hxA h⟩
      · -- Case x ≠ y: by connectivity, either xRy or yRx
        cases hConn x y hxA hyA heq with
        | inl hxy =>
          -- xRy holds, so by asymmetry yRx doesn't hold
          left
          exact ⟨hxy, heq, hAsym x y hxA hyA hxy⟩
        | inr hyx =>
          -- yRx holds, so by asymmetry xRy doesn't hold
          right; right
          exact ⟨hAsym y x hyA hxA hyx, heq, hyx⟩

    /-- A strict linear order is equivalent to a strict order that is connected -/
    theorem StrictLinearOrder_iff_StrictOrder_Connected (R A : U) :
        isStrictLinearOrderOn R A ↔ isStrictOrderOn R A ∧ isConnectedOn R A := by
      constructor
      · intro h
        have hStrict := h.1
        have hTrich := h.2
        constructor
        · exact hStrict
        · -- Derive connectivity from trichotomy
          intro x y hxA hyA hneq
          cases hTrich x y hxA hyA with
          | inl h1 => left; exact h1.1
          | inr h2 =>
            cases h2 with
            | inl h2a => exact absurd h2a.2.1 hneq
            | inr h2b => right; exact h2b.2.2
      · intro h
        exact ⟨h.1, StrictOrder_Connected_is_Trichotomous R A h.1 h.2⟩

    /-! ### Membership characterization for IdRel -/

    /-- Membership in identity relation -/
    theorem mem_IdRel (A x y : U) :
        ⟨x, y⟩ ∈ IdRel A ↔ x ∈ A ∧ x = y := by
      unfold IdRel
      rw [SpecSet_is_specified]
      constructor
      · intro h
        have hprod := h.1
        have heq := h.2
        rw [OrderedPair_mem_CartesianProduct] at hprod
        rw [fst_of_ordered_pair, snd_of_ordered_pair] at heq
        exact ⟨hprod.1, heq⟩
      · intro h
        have hxA := h.1
        have heq := h.2
        constructor
        · rw [OrderedPair_mem_CartesianProduct]
          subst heq
          exact ⟨hxA, hxA⟩
        · rw [fst_of_ordered_pair, snd_of_ordered_pair]
          exact heq

    /-- The identity relation is an equivalence relation -/
    theorem IdRel_is_Equivalence (A : U) :
        isEquivalenceOn (IdRel A) A := by
      constructor
      · -- isRelationOn
        intro p hp
        unfold IdRel at hp
        rw [SpecSet_is_specified] at hp
        exact hp.1
      constructor
      · -- isReflexiveOn
        intro x hxA
        rw [mem_IdRel]
        exact ⟨hxA, rfl⟩
      constructor
      · -- isSymmetricOn
        intro x y hxA hyA hxy
        rw [mem_IdRel] at hxy ⊢
        exact ⟨hyA, hxy.2.symm⟩
      · -- isTransitiveOn
        intro x y z hxA hyA hzA hxy hyz
        rw [mem_IdRel] at hxy hyz ⊢
        exact ⟨hxA, hxy.2.trans hyz.2⟩

    /-! ### Theorems about Equivalence Classes -/

    /-- Membership in equivalence class -/
    theorem mem_EqClass (a R A x : U) :
        x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a, x⟩ ∈ R := by
      unfold EqClass
      rw [SpecSet_is_specified]

    /-- For an equivalence relation, a is in its own equivalence class -/
    theorem EqClass_mem_self (R A a : U)
        (hEq : isEquivalenceOn R A) (haA : a ∈ A) :
        a ∈ EqClass a R A := by
      have hRefl := hEq.2.1
      rw [mem_EqClass]
      exact ⟨haA, hRefl a haA⟩

    /-- For equivalence relations, if (a, b) ∈ R and b ∈ A then b ∈ EqClass a R A -/
    theorem mem_EqClass_of_Related (R A a b : U)
        (_ : isEquivalenceOn R A) (hbA : b ∈ A) (hab : ⟨a, b⟩ ∈ R) :
        b ∈ EqClass a R A := by
      rw [mem_EqClass]
      exact ⟨hbA, hab⟩

    /-- For equivalence relations, if b ∈ EqClass a R A then (a, b) ∈ R -/
    theorem Related_of_mem_EqClass (R A a b : U)
        (_ : isEquivalenceOn R A) (hb : b ∈ EqClass a R A) :
        ⟨a, b⟩ ∈ R := by
      rw [mem_EqClass] at hb
      exact hb.2

    /-- Characterization of equivalence class membership -/
    theorem mem_EqClass_iff (R A a b : U)
        (hEq : isEquivalenceOn R A) (hbA : b ∈ A) :
        b ∈ EqClass a R A ↔ ⟨a, b⟩ ∈ R := by
      constructor
      · exact Related_of_mem_EqClass R A a b hEq
      · intro hab
        exact mem_EqClass_of_Related R A a b hEq hbA hab

    /-- For equivalence relations, EqClass a R A = EqClass b R A iff (a, b) ∈ R -/
    theorem EqClass_eq_iff (R A a b : U)
        (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
        EqClass a R A = EqClass b R A ↔ ⟨a, b⟩ ∈ R := by
      have hRel := hEq.1
      have hRefl := hEq.2.1
      have hSym := hEq.2.2.1
      have hTrans := hEq.2.2.2
      constructor
      · intro heq
        -- b ∈ EqClass b R A by reflexivity
        have hb_in_b : b ∈ EqClass b R A := EqClass_mem_self R A b hEq hbA
        -- So b ∈ EqClass a R A
        rw [← heq] at hb_in_b
        -- This means ⟨a, b⟩ ∈ R
        exact Related_of_mem_EqClass R A a b hEq hb_in_b
      · intro hab
        apply ExtSet
        intro x
        constructor
        · intro hx_in_a
          -- x ∈ EqClass a R A means x ∈ A ∧ ⟨a, x⟩ ∈ R
          rw [mem_EqClass] at hx_in_a ⊢
          have hxA := hx_in_a.1
          have hax := hx_in_a.2
          -- We have ⟨a, b⟩ ∈ R, so ⟨b, a⟩ ∈ R by symmetry
          have hba : ⟨b, a⟩ ∈ R := hSym a b haA hbA hab
          -- By transitivity: ⟨b, a⟩ ∈ R and ⟨a, x⟩ ∈ R gives ⟨b, x⟩ ∈ R
          have hbx : ⟨b, x⟩ ∈ R := hTrans b a x hbA haA hxA hba hax
          exact ⟨hxA, hbx⟩
        · intro hx_in_b
          -- Similar reasoning
          rw [mem_EqClass] at hx_in_b ⊢
          have hxA := hx_in_b.1
          have hbx := hx_in_b.2
          -- By transitivity: ⟨a, b⟩ ∈ R and ⟨b, x⟩ ∈ R gives ⟨a, x⟩ ∈ R
          have hax : ⟨a, x⟩ ∈ R := hTrans a b x haA hbA hxA hab hbx
          exact ⟨hxA, hax⟩

    /-- Equivalence classes partition the set: either equal or disjoint -/
    theorem EqClass_eq_or_disjoint (R A a b : U)
        (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
        EqClass a R A = EqClass b R A ∨ BinInter (EqClass a R A) (EqClass b R A) = ∅ := by
      by_cases hab : ⟨a, b⟩ ∈ R
      · left
        exact (EqClass_eq_iff R A a b hEq haA hbA).mpr hab
      · right
        apply ExtSet
        intro x
        constructor
        · intro hx
          rw [BinInter_is_specified] at hx
          have hxa := hx.1
          have hxb := hx.2
          -- x ∈ EqClass a R A means ⟨a, x⟩ ∈ R
          have hax : ⟨a, x⟩ ∈ R := Related_of_mem_EqClass R A a x hEq hxa
          -- x ∈ EqClass b R A means ⟨b, x⟩ ∈ R
          have hbx : ⟨b, x⟩ ∈ R := Related_of_mem_EqClass R A b x hEq hxb
          -- Get properties
          have hSym := hEq.2.2.1
          have hTrans := hEq.2.2.2
          -- Get x ∈ A
          rw [mem_EqClass] at hxa
          have hxA : x ∈ A := hxa.1
          -- ⟨x, b⟩ ∈ R by symmetry
          have hxb' : ⟨x, b⟩ ∈ R := hSym b x hbA hxA hbx
          -- ⟨a, b⟩ ∈ R by transitivity
          have hab' : ⟨a, b⟩ ∈ R := hTrans a x b haA hxA hbA hax hxb'
          exact absurd hab' hab
        · intro hx
          exfalso
          exact EmptySet_is_empty x hx

    /-! ### Domain and Range Characterization Theorems -/

    /-- Characterization of domain membership:
        x is in the domain of R if and only if there exists y such that ⟨x, y⟩ ∈ R -/
    theorem mem_domain (R x : U) :
        x ∈ domain R ↔ ∃ y, ⟨x, y⟩ ∈ R := by
      unfold domain
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · -- x ∈ fst R
          -- NOTE: This requires a theorem about the structure of fst applied to relations
          -- The definition domain R = SpecSet (fst R) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
          -- assumes fst R makes sense, but fst is defined for ordered pairs, not relations
          -- Ideally domain should be redefined as SpecSet (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
          sorry
        · exact h

    /-- Characterization of range membership:
        y is in the range of R if and only if there exists x such that ⟨x, y⟩ ∈ R -/
    theorem mem_range (R y : U) :
        y ∈ range R ↔ ∃ x, ⟨x, y⟩ ∈ R := by
      unfold range
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · -- y ∈ snd R
          -- NOTE: Same structural issue as mem_domain
          -- snd is defined for ordered pairs, not relations
          -- Ideally range should be redefined as SpecSet (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)
          sorry
        · exact h

    /-- If ⟨x, y⟩ ∈ R, then x ∈ domain R -/
    theorem pair_mem_implies_fst_in_domain (R x y : U) :
        ⟨x, y⟩ ∈ R → x ∈ domain R := by
      intro h
      rw [mem_domain]
      exact ⟨y, h⟩

    /-- If ⟨x, y⟩ ∈ R, then y ∈ range R -/
    theorem pair_mem_implies_snd_in_range (R x y : U) :
        ⟨x, y⟩ ∈ R → y ∈ range R := by
      intro h
      rw [mem_range]
      exact ⟨x, h⟩

    /-! ### Domain and Range for Relations (Properly Defined) -/

    /-- Characterization of domain_rel membership:
        x is in the domain of R if and only if there exists y such that ⟨x, y⟩ ∈ R -/
    theorem mem_domain_rel (R x : U) :
        x ∈ domain_rel R ↔ ∃ y, ⟨x, y⟩ ∈ R := by
      unfold domain_rel
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · -- x ∈ ⋃(⋃ R)
          obtain ⟨y, hxy⟩ := h
          -- ⟨x, y⟩ ∈ R means ⟨x, y⟩ is an ordered pair
          -- By definition: ⟨x, y⟩ = {{x}, {x, y}}
          -- So {{x}, {x, y}} ∈ R
          -- Therefore {x} ∈ ⋃ R (as {x} ∈ {{x}, {x, y}})
          -- And x ∈ ⋃(⋃ R) (as x ∈ {x})
          rw [UnionSet_is_specified]
          use {x}
          constructor
          · rw [UnionSet_is_specified]
            use ⟨x, y⟩
            constructor
            · exact hxy
            · -- {x} ∈ ⟨x, y⟩
              rw [OrderedPair_is_specified]
              left
              rfl
          · simp [Singleton_is_specified]
        · exact h

    /-- Characterization of range_rel membership:
        y is in the range of R if and only if there exists x such that ⟨x, y⟩ ∈ R -/
    theorem mem_range_rel (R y : U) :
        y ∈ range_rel R ↔ ∃ x, ⟨x, y⟩ ∈ R := by
      unfold range_rel
      rw [SpecSet_is_specified]
      constructor
      · intro h; exact h.2
      · intro h
        constructor
        · -- y ∈ ⋃(⋃ R)
          obtain ⟨x, hxy⟩ := h
          -- Similar to mem_domain_rel:
          -- ⟨x, y⟩ = {{x}, {x, y}} ∈ R
          -- So {x, y} ∈ ⋃ R
          -- And y ∈ ⋃(⋃ R)
          rw [UnionSet_is_specified]
          use {x, y}
          constructor
          · rw [UnionSet_is_specified]
            use ⟨x, y⟩
            constructor
            · exact hxy
            · -- {x, y} ∈ ⟨x, y⟩
              rw [OrderedPair_is_specified]
              right
              rfl
          · simp [PairSet_is_specified]
        · exact h

    /-- Characterization of imag_rel (alias for range_rel) -/
    theorem mem_imag_rel (R y : U) :
        y ∈ imag_rel R ↔ ∃ x, ⟨x, y⟩ ∈ R := by
      unfold imag_rel
      exact mem_range_rel R y

    /-- If ⟨x, y⟩ ∈ R, then x ∈ domain_rel R -/
    theorem pair_mem_implies_fst_in_domain_rel (R x y : U) :
        ⟨x, y⟩ ∈ R → x ∈ domain_rel R := by
      intro h
      rw [mem_domain_rel]
      exact ⟨y, h⟩

    /-- If ⟨x, y⟩ ∈ R, then y ∈ range_rel R -/
    theorem pair_mem_implies_snd_in_range_rel (R x y : U) :
        ⟨x, y⟩ ∈ R → y ∈ range_rel R := by
      intro h
      rw [mem_range_rel]
      exact ⟨x, h⟩

    /-- If ⟨x, y⟩ ∈ R, then y ∈ imag_rel R -/
    theorem pair_mem_implies_snd_in_imag_rel (R x y : U) :
        ⟨x, y⟩ ∈ R → y ∈ imag_rel R := by
      intro h
      rw [mem_imag_rel]
      exact ⟨x, h⟩

  end Relations

end SetUniverse

export SetUniverse.Relations (
    isRelationOn
    isRelationFrom
    Related
    isReflexiveOn
    isIrreflexiveOn
    isSymmetricOn
    isAntiSymmetricOn
    isAsymmetricOn
    isTransitiveOn
    isConnectedOn
    isStronglyConnectedOn
    isTrichotomousOn
    isEquivalenceOn
    isPreorderOn
    isPartialOrderOn
    isLinearOrderOn
    isStrictOrderOn
    isStrictPartialOrderOn
    isStrictLinearOrderOn
    isWellFoundedOn
    isWellOrderOn
    EqClass
    QuotientSet
    IdRel
    InverseRel
    Asymmetric_implies_Irreflexive
    StrictOrder_is_Irreflexive
    StrictPartialOrder_is_Irreflexive
    Irreflexive_Transitive_implies_Asymmetric
    Asymmetric_iff_Irreflexive_and_AntiSymmetric
    PartialOrder_Connected_is_LinearOrder
    LinearOrder_comparable
    StrictOrder_Connected_is_Trichotomous
    StrictLinearOrder_iff_StrictOrder_Connected
    mem_IdRel
    IdRel_is_Equivalence
    mem_EqClass
    EqClass_mem_self
    mem_EqClass_of_Related
    Related_of_mem_EqClass
    mem_EqClass_iff
    EqClass_eq_iff
    EqClass_eq_or_disjoint
    mem_domain
    mem_range
    pair_mem_implies_fst_in_domain
    pair_mem_implies_snd_in_range
)
