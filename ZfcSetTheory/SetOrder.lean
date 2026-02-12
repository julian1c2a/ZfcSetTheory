/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  universe u
  variable {U : Type u}

  namespace SetOrder

    /-! ### Propiedades de Orden Parcial Completas ### -/

    /-! ### Elemento Mínimo Global ### -/
    @[simp]
    theorem empty_is_minimum (x : U) :
      ∅ ⊆ x := by
      intro y hy_in_empty
      exfalso
      exact EmptySet_is_empty y hy_in_empty

    @[simp]
    theorem empty_is_unique_minimum (x : U) :
      (∀ y, x ⊆ y) → x = ∅ := by
      intro h_min
      have h_empty_sub : ∅ ⊆ x := empty_is_minimum x
      have h_x_sub_empty : x ⊆ ∅ := h_min ∅
      exact EqualityOfSubset x ∅ h_x_sub_empty h_empty_sub

    /-! ### Propiedades de Supremo e Ínfimo ### -/
    @[simp]
    def isUpperBound (S x : U) : Prop :=
      ∀ y, y ∈ S → y ⊆ x

    @[simp]
    def isLowerBound (S x : U) : Prop :=
      ∀ y, y ∈ S → x ⊆ y

    @[simp]
    def isSupremum (S x : U) : Prop :=
      isUpperBound S x ∧ ∀ z, isUpperBound S z → x ⊆ z

    @[simp]
    def isInfimum (S x : U) : Prop :=
      isLowerBound S x ∧ ∀ z, isLowerBound S z → z ⊆ x

    /-! ### Familias acotadas ### -/
    @[simp]
    def isBoundedAbove (S : U) : Prop :=
      ∃ x, isUpperBound S x

    @[simp]
    def isBoundedBelow (S : U) : Prop :=
      ∃ x, isLowerBound S x

    @[simp]
    theorem any_family_bounded_below (S : U) :
      isBoundedBelow S := by
      exact ⟨∅, fun y _ => empty_is_minimum y⟩

    /-! ### Teoremas sobre Intersección como Greatest Lower Bound ### -/
    /-! A ∩ B es el glb (mayor cota inferior) de A y B en el orden de inclusión -/
    @[simp]
    theorem inter_is_glb (A B : U) :
      -- A ∩ B es cota superior de cualquier subconjunto común de A y B
      (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ (A ∩ B)) ∧
      -- A ∩ B es la menor cota superior (el supremo)
      (∀ z, (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ z) → (A ∩ B) ⊆ z) := by
      constructor
      · -- Primera parte: Si x ⊆ A y x ⊆ B, entonces x ⊆ A ∩ B
        intro x hx
        obtain ⟨hxA, hxB⟩ := hx
        intro w hw_in_x
        exact (BinInter_is_specified A B w).mpr ⟨hxA w hw_in_x, hxB w hw_in_x⟩
      · -- Segunda parte: A ∩ B es la menor cota superior
        -- Basta observar que A ∩ B ⊆ A y A ∩ B ⊆ B
        intro z hz_upper
        have h_inter_sub_both : (A ∩ B) ⊆ A ∧ (A ∩ B) ⊆ B := BinInter_subset A B
        exact hz_upper (A ∩ B) h_inter_sub_both

    /-! ### Teoremas sobre Unión como Least Upper Bound ### -/
    /-! A ∪ B es el lub (menor cota superior) de A y B en el orden de inclusión -/
    @[simp]
    theorem union_is_lub (A B : U) :
      -- A ∪ B es cota inferior de cualquier superconjunto de A y B
      (∀ x, (A ⊆ x ∧ B ⊆ x) → (A ∪ B) ⊆ x) ∧
      -- A ∪ B es la mayor cota inferior (el ínfimo)
      (∀ z, (∀ x, (A ⊆ x ∧ B ⊆ x) → z ⊆ x) → z ⊆ (A ∪ B)) := by
      constructor
      · -- Primera parte: Si A ⊆ x y B ⊆ x, entonces A ∪ B ⊆ x
        intro x hx
        obtain ⟨hAx, hBx⟩ := hx
        intro w hw_in_union
        have hw_cases := (BinUnion_is_specified A B w).mp hw_in_union
        cases hw_cases with
        | inl hw_in_A => exact hAx w hw_in_A
        | inr hw_in_B => exact hBx w hw_in_B
      · -- Segunda parte: A ∪ B es la mayor cota inferior
        -- Basta observar que A ⊆ A ∪ B y B ⊆ A ∪ B
        intro z hz_lower
        have h_A_sub_union : A ⊆ (A ∪ B) := fun w hw =>
          (BinUnion_is_specified A B w).mpr (Or.inl hw)
        have h_B_sub_union : B ⊆ (A ∪ B) := fun w hw =>
          (BinUnion_is_specified A B w).mpr (Or.inr hw)
        exact hz_lower (A ∪ B) ⟨h_A_sub_union, h_B_sub_union⟩

    /-! ### Propiedades de Orden Parcial ### -/
    @[simp]
    theorem order_reflexive (x : U) : x ⊆ x := subseteq_reflexive x

    @[simp]
    theorem order_transitive (x y z : U) : x ⊆ y → y ⊆ z → x ⊆ z := subseteq_transitive x y z

    @[simp]
    theorem order_antisymmetric (x y : U) : x ⊆ y → y ⊆ x → x = y := subseteq_antisymmetric x y

    /-! ### Monotonía de operaciones ### -/
    @[simp]
    theorem union_monotone_left (A B C : U) :
      A ⊆ B → (A ∪ C) ⊆ (B ∪ C) := by
      intro h x hx
      simp only [BinUnion_is_specified] at hx ⊢
      rcases hx with hxA | hxC
      · left; exact h x hxA
      · right; exact hxC

    @[simp]
    theorem union_monotone_right (A B C : U) :
      A ⊆ B → (C ∪ A) ⊆ (C ∪ B) := by
      intro h x hx
      simp only [BinUnion_is_specified] at hx ⊢
      rcases hx with hxC | hxA
      · left; exact hxC
      · right; exact h x hxA

    @[simp]
    theorem inter_monotone_left (A B C : U) :
      A ⊆ B → (A ∩ C) ⊆ (B ∩ C) := by
      intro h x hx
      have hxAC := (BinInter_is_specified A C x).mp hx
      exact (BinInter_is_specified B C x).mpr ⟨h x hxAC.1, hxAC.2⟩

    @[simp]
    theorem inter_monotone_right (A B C : U) :
      A ⊆ B → (C ∩ A) ⊆ (C ∩ B) := by
      intro h x hx
      have hxCA := (BinInter_is_specified C A x).mp hx
      exact (BinInter_is_specified C B x).mpr ⟨hxCA.1, h x hxCA.2⟩

  end SetOrder

end SetUniverse

export SetUniverse.SetOrder (
    empty_is_minimum empty_is_unique_minimum
    isUpperBound isLowerBound isSupremum isInfimum
    isBoundedAbove isBoundedBelow any_family_bounded_below
    inter_is_glb union_is_lub
    order_reflexive order_transitive order_antisymmetric
    union_monotone_left union_monotone_right
    inter_monotone_left inter_monotone_right
)
