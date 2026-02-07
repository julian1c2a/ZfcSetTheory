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

    /-! ### Teoremas sobre Intersección como Supremo ### -/
    @[simp]
    theorem intersection_is_supremum_of_lower_bounds (A B : U) :
      isSupremum {x | x ⊆ A ∧ x ⊆ B} (A ∩ B) := by
      constructor
      · -- A ∩ B es cota superior de todos los conjuntos contenidos en ambos A y B
        intro x hx_in_set
        intro z hz_in_x
        -- Si z ∈ x, y sabemos que x ⊆ A y x ⊆ B, entonces z ∈ A y z ∈ B
        have hz_in_A : z ∈ A := by
          rw [SpecSet_is_specified] at hx_in_set
          exact hx_in_set.2.1 z hz_in_x
        have hz_in_B : z ∈ B := by
          rw [SpecSet_is_specified] at hx_in_set
          exact hx_in_set.2.2 z hz_in_x
        -- Por tanto z ∈ A ∩ B
        exact (BinIntersection_is_specified A B z).mpr ⟨hz_in_A, hz_in_B⟩
      · -- A ∩ B es la menor cota superior
        intro z hz_upper
        intro w hw_in_inter
        -- Si w ∈ A ∩ B, entonces w ∈ A y w ∈ B
        have hw_both := (BinIntersection_is_specified A B w).mp hw_in_inter
        -- Consideremos el conjunto {w}. Este conjunto satisface {w} ⊆ A y {w} ⊆ B
        have h_singleton_in_set : {w} ∈ {x | x ⊆ A ∧ x ⊆ B} := by
          rw [SpecSet_is_specified]
          constructor
          · -- {w} ∈ algún conjunto base (usamos A)
            exact hw_both.1
          · -- {w} ⊆ A ∧ {w} ⊆ B
            constructor
            · intro y hy_in_singleton
              have hy_eq_w := (Singleton_is_specified w y).mp hy_in_singleton
              rw [hy_eq_w]
              exact hw_both.1
            · intro y hy_in_singleton
              have hy_eq_w := (Singleton_is_specified w y).mp hy_in_singleton
              rw [hy_eq_w]
              exact hw_both.2
        -- Como z es cota superior, {w} ⊆ z, por tanto w ∈ z
        have h_singleton_sub_z := hz_upper {w} h_singleton_in_set
        exact h_singleton_sub_z w ((Singleton_is_specified w w).mpr rfl)

    /-! ### Teoremas sobre Unión como Ínfimo ### -/
    @[simp]
    theorem union_is_infimum_of_upper_bounds (A B : U) :
      isInfimum {x | A ⊆ x ∧ B ⊆ x} (A ∪ B) := by
      constructor
      · -- A ∪ B es cota inferior de todos los conjuntos que contienen tanto A como B
        intro x hx_in_set
        intro z hz_in_union
        -- Si z ∈ A ∪ B, entonces z ∈ A ∨ z ∈ B
        have hz_cases := (BinUnion_is_specified A B z).mp hz_in_union
        cases hz_cases with
        | inl hz_in_A => 
          -- z ∈ A, y como A ⊆ x, entonces z ∈ x
          rw [SpecSet_is_specified] at hx_in_set
          exact hx_in_set.2.1 z hz_in_A
        | inr hz_in_B => 
          -- z ∈ B, y como B ⊆ x, entonces z ∈ x
          rw [SpecSet_is_specified] at hx_in_set
          exact hx_in_set.2.2 z hz_in_B
      · -- A ∪ B es la mayor cota inferior
        intro z hz_lower
        intro w hw_in_z
        -- Para cualquier w ∈ z, necesitamos mostrar w ∈ A ∪ B
        -- Usamos el principio del tercero excluido: w ∈ A ∨ w ∉ A
        by_cases hw_in_A : w ∈ A
        · -- Caso w ∈ A
          exact (BinUnion_is_specified A B w).mpr (Or.inl hw_in_A)
        · -- Caso w ∉ A
          -- Necesitamos mostrar w ∈ B
          -- Consideremos el conjunto (A ∪ B ∪ {w})
          have h_extended_in_set : (A ∪ B ∪ {w}) ∈ {x | A ⊆ x ∧ B ⊆ x} := by
            rw [SpecSet_is_specified]
            constructor
            · -- (A ∪ B ∪ {w}) ∈ algún conjunto base
              exact (BinUnion_is_specified (A ∪ B) {w} w).mpr (Or.inr ((Singleton_is_specified w w).mpr rfl))
            · -- A ⊆ (A ∪ B ∪ {w}) ∧ B ⊆ (A ∪ B ∪ {w})
              constructor
              · intro y hy_in_A
                exact (BinUnion_is_specified (A ∪ B) {w} y).mpr (Or.inl ((BinUnion_is_specified A B y).mpr (Or.inl hy_in_A)))
              · intro y hy_in_B
                exact (BinUnion_is_specified (A ∪ B) {w} y).mpr (Or.inl ((BinUnion_is_specified A B y).mpr (Or.inr hy_in_B)))
          -- Como z es cota inferior, z ⊆ (A ∪ B ∪ {w})
          have h_z_sub_extended := hz_lower (A ∪ B ∪ {w}) h_extended_in_set
          have hw_in_extended := h_z_sub_extended w hw_in_z
          -- Ahora hw_in_extended: w ∈ A ∪ B ∪ {w}
          have hw_cases := (BinUnion_is_specified (A ∪ B) {w} w).mp hw_in_extended
          cases hw_cases with
          | inl hw_in_union => exact hw_in_union
          | inr hw_in_singleton => 
            -- w ∈ {w}, que es trivialmente cierto
            -- En este caso, necesitamos un argumento más sofisticado
            -- Por contradicción: si w ∉ A ∪ B, entonces w ∉ A y w ∉ B
            by_cases hw_in_B : w ∈ B
            · exact (BinUnion_is_specified A B w).mpr (Or.inr hw_in_B)
            · -- w ∉ A y w ∉ B, pero w ∈ z y z ⊆ (A ∪ B ∪ {w})
              -- Esto significa que w debe estar en {w}, lo cual es consistente
              -- pero no nos ayuda a probar w ∈ A ∪ B
              -- Este caso requiere un análisis más profundo de la teoría
              sorry

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
      intro h x ⟨hxA, hxC⟩
      exact ⟨h x hxA, hxC⟩

    @[simp]
    theorem inter_monotone_right (A B C : U) :
      A ⊆ B → (C ∩ A) ⊆ (C ∩ B) := by
      intro h x ⟨hxC, hxA⟩
      exact ⟨hxC, h x hxA⟩

  end SetOrder

end SetUniverse

export SetUniverse.SetOrder (
    empty_is_minimum empty_is_unique_minimum
    isUpperBound isLowerBound isSupremum isInfimum
    isBoundedAbove isBoundedBelow any_family_bounded_below
    intersection_is_supremum_of_lower_bounds
    union_is_infimum_of_upper_bounds
    order_reflexive order_transitive order_antisymmetric
    union_monotone_left union_monotone_right
    inter_monotone_left inter_monotone_right
)
