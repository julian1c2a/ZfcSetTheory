import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence

namespace SetUniverse
  open Classical
  open SetUniverse.ExistenceAxiom
  open SetUniverse.ExtensionAxiom
  universe u
  variable {U : Type u}

  namespace SpecificationAxiom


    /-! ### Axioma de Especificación, Separación o Comprehensión ### -/
    /-! ### Specification : existe algún conjunto en el universo U que cumple que es subconjunto de otro y que cumple la proposición P ### -/
    @[simp]
    axiom Specification (x : U) (P : U → Prop) :
      ∃ (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)

    /-! ### Teorema de Existencia Única para el Axioma de Especificación ### -/
    /-! ### SpecificationUnique : existe un único conjunto que cumple la especificación P ### -/
    @[simp]
    theorem SpecificationUnique (x : U) (P : U → Prop) :
      ExistsUnique fun (y : U) => ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)
        := by
      obtain ⟨y, hy⟩ := Specification x P
      apply ExistsUnique.intro y
      · -- Existencia del conjunto especificado
        exact hy
      · -- Unicidad del conjunto especificado
        intro z hz_spec
        apply (ExtSet z y)
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_w_in_y : w ∈ y := by
            apply (hy w).2
            exact (hz_spec w).mp hw_in_z
          exact h_w_in_y
        · -- Dirección <-
          intro hw_in_y
          have h := (hy w).mp hw_in_y
          have h_w_in_x : w ∈ x := h.1
          have h_P_w : P w := h.2
          have h_w_in_z : w ∈ z := by
            apply (hz_spec w).mpr
            exact ⟨h_w_in_x, h_P_w⟩
          exact h_w_in_z

    /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
    @[simp]
    noncomputable def SpecSet (x : U) (P : U → Prop) : U :=
      choose (SpecificationUnique x P)

    @[simp]
    theorem SpecSet_is_specified (x z : U) (P : U → Prop) :
      z ∈ SpecSet x P ↔ (z ∈ x ∧ P z)
        := by
      exact (choose_spec (SpecificationUnique x P)).1 z

    notation " { " x " | " P " } " => SpecSet x P

    /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
    @[simp]
    noncomputable def BinInter (x y : U) : U :=
      choose (SpecificationUnique x fun z => z ∈ y)

    @[simp]
    theorem BinInter_is_specified (x y z : U) :
      z ∈ BinInter x y ↔ (z ∈ x ∧ z ∈ y)
        := by
      have h := choose_spec (SpecificationUnique x fun z => z ∈ y)
      exact h.1 z

    @[simp]
    theorem BinInterUniqueSet (x y : U) :
      ExistsUnique fun (z : U) => ∀ (w : U), w ∈ z ↔ (w ∈ x ∧ w ∈ y)
        := by
      apply ExistsUnique.intro (BinInter x y)
      · -- Existencia del conjunto de intersección binaria
        exact BinInter_is_specified x y
      · -- Unicidad del conjunto de intersección binaria
        intro z hz_inter
        apply (ExtSet z (BinInter x y))
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_both := (hz_inter w).mp hw_in_z
          have h_w_in_x : w ∈ x := h_both.1
          have h_w_in_y : w ∈ y := h_both.2
          exact (BinInter_is_specified x y w).mpr ⟨h_w_in_x, h_w_in_y⟩
        · -- Dirección <-
          intro hw_in_bin_inter
          have h_both := (BinInter_is_specified x y w).mp hw_in_bin_inter
          exact (hz_inter w).mpr h_both

    /-! ### Notación estándar de conjuntos de la Intersección Binaria ### -/
    notation:50 lhs:51 " ∩ " rhs:51 => BinInter lhs rhs

    /-! ### Teorema de la Intersección es Subconjunto ### -/
    @[simp]
    theorem BinInter_subset (x y : U) :
      (x ∩ y) ⊆ x ∧ (x ∩ y) ⊆ y
        := by
      constructor
      · -- Subconjunto de x
        intro z h_z_in_bin_inter
        have h := BinInter_is_specified x y z
        exact (h.1 h_z_in_bin_inter).1
      · -- Subconjunto de y
        intro z h_z_in_bin_inter
        have h := BinInter_is_specified x y z
        exact (h.1 h_z_in_bin_inter).2

    /-! ### Teorema de la Intersección de Conjuntos Disjuntos es Vacía ### -/
    @[simp]
    theorem BinInter_empty (x y : U) :
      (x ∩ y) = ∅ ↔ (x ⟂ y)
        := by
      constructor
      · -- Dirección ->
        intro h_bin_inter_empty z h_z_in_x h_z_in_y
        have h_bin_inter := BinInter_is_specified x y z
        have h_z_in_bin_inter : z ∈ (x ∩ y) := by
          apply h_bin_inter.mpr
          exact ⟨h_z_in_x, h_z_in_y⟩
        apply EmptySet_is_empty z
        rw [← h_bin_inter_empty]
        exact h_z_in_bin_inter
      · -- Dirección <-
        intro h_disj
        apply ExtSet (x ∩ y) ∅
        intro z
        constructor
        · -- Dirección ->
          intro h_z_in_bin_inter
          have h_bin_inter := BinInter_is_specified x y z
          have h_both := h_bin_inter.mp h_z_in_bin_inter
          have h_false := h_disj z h_both.1 h_both.2
          exact False.elim h_false
        · -- Dirección <-
          intro h_z_in_empty
          exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem BinInter_empty_left_wc {x y : U} (h_empty : (x ∩ y) = ∅) :
      x ⟂ y
        := by
      exact (BinInter_empty x y).mp h_empty

    @[simp]
    theorem BinInter_empty_right_wc {x y : U} (h_perp : x ⟂ y) :
      (x ∩ y) = ∅
        := by
      exact (BinInter_empty x y).mpr h_perp

    @[simp]
    theorem BinInter_commutative (x y : U) :
      (x ∩ y) = (y ∩ x)
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h := BinInter_is_specified x y z
        have h_both := h.mp h_z_in_bin_inter
        exact (BinInter_is_specified y x z).mpr ⟨h_both.2, h_both.1⟩
      · -- Dirección <-
        intro h_z_in_bin_inter
        have h := BinInter_is_specified y x z
        have h_both := h.mp h_z_in_bin_inter
        exact (BinInter_is_specified x y z).mpr ⟨h_both.2, h_both.1⟩

    @[simp]
    theorem BinInter_associative (x y z : U) :
      ((x ∩ y) ∩ z) = (x ∩ (y ∩ z))
        := by
      apply ExtSet
      intro w
      constructor
      · -- Dirección ->
        intro h_w_in_bin_inter
        have h_bin_inter := BinInter_is_specified (x ∩ y) z w
        have h_both := h_bin_inter.mp h_w_in_bin_inter
        have h_w_in_xy := (BinInter_is_specified x y w).mp h_both.1
        have h_w_in_y_inter_z : w ∈ (y ∩ z) := by
          apply (BinInter_is_specified y z w).mpr
          exact ⟨h_w_in_xy.2, h_both.2⟩
        have h_w_in_x_inter_yz : w ∈ (x ∩ (y ∩ z)) := by
          apply (BinInter_is_specified x (y ∩ z) w).mpr
          exact ⟨h_w_in_xy.1, h_w_in_y_inter_z⟩
        exact h_w_in_x_inter_yz
      · -- Dirección <-
        intro h_w_in_x_inter_yz
        have h_bin_inter := BinInter_is_specified x (y ∩ z) w
        have h_both := h_bin_inter.mp h_w_in_x_inter_yz
        have h_w_in_yz : w ∈ (y ∩ z) := h_both.2
        have h_w_in_yz_components := (BinInter_is_specified y z w).mp h_w_in_yz
        have h_w_in_x_inter_y : w ∈ (x ∩ y) := by
          apply (BinInter_is_specified x y w).mpr
          exact ⟨h_both.1, h_w_in_yz_components.1⟩
        have h_w_in_bin_inter : w ∈ ((x ∩ y) ∩ z) := by
          apply (BinInter_is_specified (x ∩ y) z w).mpr
          exact ⟨h_w_in_x_inter_y, h_w_in_yz_components.2⟩
        exact h_w_in_bin_inter

    @[simp]
      theorem BinInter_absorbent_elem (x : U) :
      (x ∩ ∅) = ∅
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h_bin_inter := BinInter_is_specified x ∅ z
        have h_both := h_bin_inter.mp h_z_in_bin_inter
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_in_empty : z ∈ ∅ := h_both.2
        exact h_z_in_empty
      · -- Dirección <-
        intro h_z_in_empty
        exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem BinInter_with_subseteq (x y : U) :
      x ⊆ y → (x ∩ y) ⊆ x
        := by
      intro h_subset z h_z_in_bin_inter
      have h_bin_inter := BinInter_is_specified x y z
      have h_both := h_bin_inter.mp h_z_in_bin_inter
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_in_y : z ∈ y := h_both.2
      exact h_z_in_x

    @[simp]
    theorem BinInter_with_subseteq_full (x y : U) :
      x ⊆ y ↔ (x ∩ y) = x
        := by
      constructor
      · -- Direction: x ⊆ y → (x ∩ y) = x
        intro h_subset
        apply ExtSet
        intro z
        constructor
        · -- z ∈ (x ∩ y) → z ∈ x
          intro h_z_in_inter
          have h_bin_inter := BinInter_is_specified x y z
          have h_both := h_bin_inter.mp h_z_in_inter
          exact h_both.1
        · -- z ∈ x → z ∈ (x ∩ y)
          intro h_z_in_x
          have h_z_in_y := h_subset z h_z_in_x
          exact (BinInter_is_specified x y z).mpr ⟨h_z_in_x, h_z_in_y⟩
      · -- Direction: (x ∩ y) = x → x ⊆ y
        intro h_eq z h_z_in_x
        have h_z_in_inter : z ∈ (x ∩ y) := by
          rw [h_eq]
          exact h_z_in_x
        have h_bin_inter := BinInter_is_specified x y z
        have h_both := h_bin_inter.mp h_z_in_inter
        exact h_both.2

    @[simp]
    theorem BinInter_with_empty (x : U) :
      (x ∩ ∅) = ∅
        := by
      exact BinInter_absorbent_elem x

    @[simp]
    theorem BinInter_idempotence (x : U) :
      (x ∩ x) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_inter
        have h_bin_inter := BinInter_is_specified x x z
        have h_both := h_bin_inter.mp h_z_in_bin_inter
        exact h_both.1
      · -- Dirección <-
        intro h_z_in_x
        exact (BinInter_is_specified x x z).mpr ⟨h_z_in_x, h_z_in_x⟩

    /-! ### Definición de la Diferencia de Conjuntos ### -/
    @[simp]
    noncomputable def Difference (x y : U) : U :=
      choose (SpecificationUnique x (fun z => z ∉ y))

    /-! ### Notación estándar de la Diferencia de Conjuntos ### -/
    notation:50 lhs:51 " \\ " rhs:51 => Difference lhs rhs

    @[simp]
    theorem Difference_is_specified (x y z : U) :
      z ∈ (x \ y) ↔ (z ∈ x ∧ z ∉ y)
        := by
      have h := choose_spec (SpecificationUnique x fun z => z ∉ y)
      exact h.1 z

    @[simp]
    theorem DifferenceUniqueSet (x y : U) :
      ExistsUnique fun (z : U) => ∀ (w : U), w ∈ z ↔ (w ∈ x ∧ w ∉ y)
        := by
      apply ExistsUnique.intro (Difference x y)
      · -- Existencia de la diferencia binaria
        exact Difference_is_specified x y
      · -- Unicidad de la diferencia binaria
        intro z hz_difference
        apply (ExtSet z (Difference x y))
        intro w
        constructor
        · -- Dirección ->
          intro hw_in_z
          have h_both := (hz_difference w).mp hw_in_z
          have h_w_in_x : w ∈ x := h_both.1
          have h_w_not_in_y : w ∉ y := h_both.2
          exact (Difference_is_specified x y w).mpr ⟨h_w_in_x, h_w_not_in_y⟩
        · -- Dirección <-
          intro hw_in_difference
          have h_both := (Difference_is_specified x y w).mp hw_in_difference
          exact (hz_difference w).mpr h_both

    @[simp]
    theorem Difference_subset (x y : U) :
      (x \ y) ⊆ x
        := by
      intro z h_z_in_difference
      have h_difference := Difference_is_specified x y z
      have h_both := h_difference.mp h_z_in_difference
      exact h_both.1

    @[simp]
    theorem Difference_empty_iff_subseteq (x y : U) :
      (x \ y) = ∅ ↔ x ⊆ y := by
      constructor
      · -- Dirección: (x \ y) = ∅ → x ⊆ y
        intro h_empty_diff z h_z_in_x
        -- Queremos demostrar z ∈ y. Usaremos una prueba por contradicción.
        -- Esto es el equivalente en Lean 4 puro de `by_contra h_z_notin_y`.
        apply Classical.byContradiction
        intro h_z_notin_y
        -- Ahora tenemos `h_z_notin_y : z ∉ y` y el objetivo es `False`.
        have h_in_diff : z ∈ (x \ y) := (Difference_is_specified x y z).mpr ⟨h_z_in_x, h_z_notin_y⟩
        rw [h_empty_diff] at h_in_diff
        exact EmptySet_is_empty z h_in_diff
      · -- Dirección <-
        intro h_subset
        apply ExtSet
        intro z
        rw [Difference_is_specified]
        -- Membership in the empty set is always false
        have h_empty : ∀ x, x ∈ (∅ : U) → False := EmptySet_is_empty
        constructor
        · intro h_in_diff
          have h_z_in_y := h_subset z h_in_diff.left
          -- h_in_diff.right h_z_in_y is False, so z ∈ ∅ is impossible
          exact False.elim (h_in_diff.right h_z_in_y)
        · intro h_false
          exact False.elim (EmptySet_is_empty z h_false)

    @[simp]
    theorem Difference_with_empty (x : U) :
      (x \ ∅) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := Difference_is_specified x ∅ z
        have h_both := h_difference.mp h_z_in_difference
        exact h_both.1
      · -- Dirección <-
        intro h_z_in_x
        exact (Difference_is_specified x ∅ z).mpr ⟨h_z_in_x, fun h_z_in_y => EmptySet_is_empty z h_z_in_y⟩

    @[simp]
    theorem Difference_self_empty (x : U) :
      (x \ x) = ∅
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := Difference_is_specified x x z
        have h_both := h_difference.mp h_z_in_difference
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_not_in_x : z ∉ x := h_both.2
        exact False.elim (h_z_not_in_x h_z_in_x)
      · -- Dirección <-
        intro h_z_in_empty
        exact False.elim (EmptySet_is_empty z h_z_in_empty)

    @[simp]
    theorem Difference_disjoint (x : U) {y: U} (h_disjoint : x ⟂ y) :
      (x \ y) = x
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_difference
        have h_difference := Difference_is_specified x y z
        have h_both := h_difference.mp h_z_in_difference
        have h_z_in_x : z ∈ x := h_both.1
        have h_z_not_in_y : z ∉ y := h_both.2
        exact h_z_in_x
      · -- Dirección <-
        intro h_z_in_x
        have h_z_not_in_y : z ∉ y := h_disjoint z h_z_in_x
        exact (Difference_is_specified x y z).mpr ⟨h_z_in_x, h_z_not_in_y⟩

    @[simp]
    theorem Difference_empty (A B : U) :
      ((A \ B) = (∅ : U)) → ∀ x, x ∈ A → x ∈ B
        := by
    intro h_empty x hx_in_A
    rw [Difference_empty_iff_subseteq] at h_empty
    -- Since A \ B = ∅, every x ∈ A must be in B, otherwise x ∈ A \ B ≠ ∅
    have h_sub : ∀ x, x ∈ A → x ∈ B := h_empty
    exact h_sub x hx_in_A

    @[simp]
    theorem Difference_empty_wc (A B : U) (h_empty : (A \ B) = ∅) :
      ∀ x, x ∈ A → x ∈ B
        := by
      intro x hx_in_A
      -- We can use the previous theorem to show this
      exact Difference_empty A B h_empty x hx_in_A

    @[simp]
    theorem Difference_subseteq (A B : U) :
      (∀ x, x ∈ A → x ∈ B) → ((A \ B) = (∅ : U))
        := by
      intro h
      apply ExtSet
      intro x
      constructor
      · intro hx
        -- x ∈ A \ B means x ∈ A and x ∉ B
        rw [Difference_is_specified] at hx
        have hxA := hx.left
        have hxB := hx.right
        have hAB := h x hxA
        -- But hAB: x ∈ B, contradiction
        exfalso
        exact hxB hAB
      · intro hx_empty
        -- x ∈ ∅ is impossible
        exfalso
        exact EmptySet_is_empty x hx_empty

    @[simp]
    theorem Difference_subseteq_wc (A B : U) (h_subseteq : ∀ x, x ∈ A → x ∈ B) :
      (A \ B) = (∅ : U)
        := by
      exact Difference_subseteq A B h_subseteq

  end SpecificationAxiom
end SetUniverse

export SetUniverse.SpecificationAxiom (
    Specification SpecificationUnique SpecSet SpecSet_is_specified
    BinInter BinInter_is_specified BinInterUniqueSet
    BinInter_subset BinInter_empty BinInter_empty_left_wc
    BinInter_empty_right_wc BinInter_commutative
    BinInter_associative BinInter_absorbent_elem
    BinInter_with_subseteq BinInter_with_subseteq_full
    BinInter_with_empty BinInter_idempotence
    Difference Difference_is_specified DifferenceUniqueSet
    Difference_subset Difference_with_empty
    Difference_self_empty Difference_disjoint
    Difference_empty_iff_subseteq
    Difference_empty Difference_empty_wc Difference_subseteq Difference_subseteq_wc
)
