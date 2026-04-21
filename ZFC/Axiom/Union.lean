/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Init.Classical
import ZFC.Core.Prelim
import ZFC.Axiom.Extension
import ZFC.Axiom.Existence
import ZFC.Axiom.Specification
import ZFC.Axiom.Pairing

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  universe u
  variable {U : Type u}

  namespace Axiom.Union

    /-! ### Axioma de Unión ### -/
    @[simp]
    axiom Axiom.Union :
      ∀ (C : U), ∃ (UC : U), ∀ (x : U), x ∈ UC ↔ ∃ (y : U), y ∈ C ∧ x ∈ y

    /-! ### Teorema de Existencia Única para el Axioma de Unión ### -/
    @[simp]
    theorem sUnion_existsUnique (C : U) :
      ∃! UC, ∀ x : U, x ∈ UC ↔ ∃ y : U, y ∈ C ∧ x ∈ y
        := by
      obtain ⟨UC, hUC⟩ := Axiom.Union C
      apply ExistsUnique.intro UC
      · exact hUC
      · -- proof of uniqueness
        intros UC₁ h₁
        apply ExtSet
        intro x
        constructor
        · intro hx
          have h_ex : ∃ y, y ∈ C ∧ x ∈ y := (h₁ x).mp hx
          exact (hUC x).mpr h_ex
        · intro hx
          have h_ex : ∃ y, y ∈ C ∧ x ∈ y := (hUC x).mp hx
          exact (h₁ x).mpr h_ex

    @[simp]
    theorem mem_sUnion_raw (C x : U) :
      x ∈ (choose (Axiom.Union C)) ↔ ∃ (S : U), S ∈ C ∧ x ∈ S
        := by
      have hUC := choose_spec (Axiom.Union C)
      constructor
      . intro h
        exact (hUC x).mp h
      . intro h
        exact (hUC x).mpr h

    @[simp]
    noncomputable def sUnion (C : U) : U :=
      (sUnion_existsUnique C).choose

    notation " ⋃ " C:100 => sUnion C

    @[simp]
    theorem mem_sUnion_iff (C x : U) :
      x ∈ (sUnion C) ↔ ∃ (S : U), S ∈ C ∧ x ∈ S
        := by
      unfold sUnion
      constructor
      . intro h
        exact ((sUnion_existsUnique C).choose_spec x).mp h
      . intro h
        exact ((sUnion_existsUnique C).choose_spec x).mpr h

    @[simp]
    theorem sUnion_unique (C UC : U) :
      ( ∀ (y : U), y ∈ UC ↔ ∃ (S : U), S ∈ C ∧ y ∈ S )
      ↔ ( UC = (sUnion C) )
        := by
      constructor
      -- (→) direction
      · intro h
        apply ExtSet
        intro y
        rw [h, mem_sUnion_iff]
      -- (←) direction
      · intro h_eq
        rw [h_eq]
        intro y
        rw [mem_sUnion_iff]

    theorem sUnion_empty_of_empty (C : U) (hC_empty : C = (∅ : U)) :
      (sUnion C) = (∅ : U)
        := by
      rw [hC_empty]
      apply ExtSet
      intro y
      constructor
      . intro hy
        have h_union_spec := (mem_sUnion_iff ∅ y).mp hy
        cases h_union_spec with
        | intro S hS =>
          cases hS with
          | intro hS_in_C hS_mem_y =>
            -- S ∈ ∅ is impossible, so this case is vacuously true
            exact False.elim (EmptySet_is_empty S hS_in_C)
      . intro hy
        exact False.elim (EmptySet_is_empty y hy)

    @[simp]
    theorem sUnion_singleton_empty (C : U) (hC_empty : C = ({∅} : U)) :
      (sUnion C) = (∅ : U)
        := by
      rw [hC_empty]
      apply ExtSet
      intro y
      constructor
      . intro hy
        have h_union_spec := (mem_sUnion_iff ({∅} : U) y).mp hy
        cases h_union_spec with
        | intro S hS =>
          cases hS with
          | intro hS_in_C hS_mem_y =>
            -- S ∈ {∅} is impossible unless S = ∅, but then y ∈ ∅, contradiction
            have hS_eq : S = ∅ := by
              -- S ∈ {∅} means S = ∅ by definition of singleton
              rw [Singleton_is_specified] at hS_in_C
              cases hS_in_C with
              | refl => exact rfl
            rw [hS_eq] at hS_mem_y
            exact False.elim (EmptySet_is_empty y hS_mem_y)
      . intro hy
        exact False.elim (EmptySet_is_empty y hy)

    theorem sUnion_ne_empty (C : U)
      (hC_not_empty : C ≠ (∅ : U))
      (hC_not_singleton_empty : C ≠ ({∅} : U)) :
        (sUnion C) ≠ (∅ : U)
          := by
        -- Empezamos la prueba por reducción al absurdo asumiendo lo contrario.
        -- h_union_empty : (sUnion C) = ∅
        intro h_union_empty
        -- Nuestro objetivo es contradecir una de las hipótesis. Elegimos hC_not_singleton_empty.
        -- Para ello, demostraremos que nuestra suposición implica C = {∅}.
        apply hC_not_singleton_empty

        -- Demostramos C = {∅} usando el Axioma de Extensionalidad.
        apply ExtSet
        intro x
        constructor

        -- Primera dirección: x ∈ C → x ∈ {∅}
        · intro hx_in_C -- Asumimos que x es un elemento de C.
          -- Para demostrar que x ∈ {∅}, por la definición de singulete, debemos probar que x = ∅.
          rw [Singleton_is_specified]
          -- Usamos de nuevo Extensionalidad para probar x = ∅.
          apply ExtSet
          intro y
          constructor

          -- Probamos que si y ∈ x, entonces y ∈ ∅ (lo cual es falso).
          · intro hy_in_x
            -- Por definición de la unión, si x ∈ C y y ∈ x, entonces y ∈ (sUnion C).
            have hy_in_union : y ∈ (sUnion C) := (mem_sUnion_iff C y).mpr ⟨x, hx_in_C, hy_in_x⟩
            -- Usamos nuestra suposición inicial de que (sUnion C) = ∅.
            rw [h_union_empty] at hy_in_union
            -- Ahora tenemos y ∈ ∅, que es lo que queríamos probar.
            exact hy_in_union

          -- La otra dirección (y ∈ ∅ → y ∈ x) es trivialmente cierta.
          · intro hy_in_empty
            exact False.elim (EmptySet_is_empty y hy_in_empty)

        -- Segunda dirección: x ∈ {∅} → x ∈ C
        · intro hx_in_singleton -- Asumimos x ∈ {∅}, lo que implica x = ∅.
          rw [Singleton_is_specified] at hx_in_singleton
          -- Sustituimos x por ∅. El objetivo ahora es demostrar ∅ ∈ C.
          subst hx_in_singleton

          -- Sabemos por la hipótesis hC_not_empty que C no es vacío, por lo que existe al menos un elemento en C.
          have h_exists_mem_C : ∃ y, y ∈ C := by
            -- Esto se demuestra por contradicción. Si no existiera tal y, C sería ∅.
            apply Classical.byContradiction
            intro h_not_exists_mem
            apply hC_not_empty
            apply ExtSet
            intro z
            constructor
            · intro hz_in_C
              exact False.elim (h_not_exists_mem ⟨z, hz_in_C⟩)
            · intro hz_in_empty
              exact False.elim (EmptySet_is_empty z hz_in_empty)

          -- Obtenemos ese elemento, al que llamamos 'y'.
          obtain ⟨y, hy_in_C⟩ := h_exists_mem_C

          -- Ahora demostramos que este elemento 'y' tiene que ser ∅.
          -- La lógica es idéntica a la usada en la primera dirección de la prueba principal.
          have hy_is_empty : y = (∅ : U) := by
            apply ExtSet
            intro z
            constructor
            · intro hz_in_y
              have hz_in_union : z ∈ (sUnion C) := (mem_sUnion_iff C z).mpr ⟨y, hy_in_C, hz_in_y⟩
              rw [h_union_empty] at hz_in_union
              exact hz_in_union
            · intro hz_in_empty
              exact False.elim (EmptySet_is_empty z hz_in_empty)

          -- Como y ∈ C y hemos demostrado que y = ∅, podemos concluir que ∅ ∈ C.
          rw [←hy_is_empty]
          exact hy_in_C

    theorem sUnion_eq_empty' (C : U) :
      (sUnion C) = (∅ : U) ↔ (C = (∅ : U)) ∨ (∀ (S : U), S ∈ C → S = (∅ : U))
        := by
      constructor
      . intro h_union_empty
        by_cases hC_empty : C = (∅ : U)
        . left
          exact hC_empty
        . right
          intro S hS_in_C
          apply ExtSet
          intro x
          constructor
          . intro hx_in_S
            have h_union_spec := (mem_sUnion_iff C x).mpr ⟨S, hS_in_C, hx_in_S⟩
            rw [h_union_empty] at h_union_spec
            exact False.elim (EmptySet_is_empty x h_union_spec)
          . intro hx_in_empty
            exact False.elim (EmptySet_is_empty x hx_in_empty)
      . intro h_or
        cases h_or with
        | inl hC_empty =>
          exact sUnion_empty_of_empty C hC_empty
        | inr h_all_empty =>
          apply ExtSet
          intro x
          constructor
          . intro hx_in_union
            have h_union_spec := (mem_sUnion_iff C x).mp hx_in_union
            cases h_union_spec with
            | intro S hS =>
              cases hS with
              | intro hS_in_C hx_in_S =>
                have hS_empty := h_all_empty S hS_in_C
                rw [hS_empty] at hx_in_S
                exact hx_in_S
          . intro hx_in_empty
            exact False.elim (EmptySet_is_empty x hx_in_empty)

    @[simp]
    theorem sUnion_eq_empty (C : U) :
      (sUnion C) = (∅ : U) ↔ (∀ (S : U), S ∈ C → S = (∅ : U))
        := by
      constructor
      . intro h_union_empty
        intro S hS_in_C
        apply ExtSet
        intro x
        constructor
        . intro hx_in_S
          have h_union_spec := (mem_sUnion_iff C x).mpr ⟨S, hS_in_C, hx_in_S⟩
          rw [h_union_empty] at h_union_spec
          exact False.elim (EmptySet_is_empty x h_union_spec)
        . intro hx_in_empty
          exact False.elim (EmptySet_is_empty x hx_in_empty)
      . intro h_all_empty
        apply ExtSet
        intro x
        constructor
        . intro hx_in_union
          have h_union_spec := (mem_sUnion_iff C x).mp hx_in_union
          cases h_union_spec with
          | intro S hS =>
            cases hS with
            | intro hS_in_C hx_in_S =>
              have hS_empty := h_all_empty S hS_in_C
              rw [hS_empty] at hx_in_S
              exact hx_in_S
        . intro hx_in_empty
          exact False.elim (EmptySet_is_empty x hx_in_empty)

    theorem sUnion_eq_empty_iff_singleton_empty
      (C : U)
      (hC_non_empty : C ≠ (∅ : U)) :
        (sUnion C) = ∅ ↔ C = ({ ∅ }: U)
          := by
      constructor
      · -- Forward direction: (sUnion C) = ∅ → C = {∅}
        intro h_union_empty
        apply ExtSet
        intro x
        constructor
        · -- x ∈ C → x ∈ {∅}, i.e., x = ∅
          intro hx_in_C
          rw [Singleton_is_specified]
          apply ExtSet
          intro z
          constructor
          · intro hz_in_x
            have hz_in_union : z ∈ (sUnion C) := (mem_sUnion_iff C z).mpr ⟨x, hx_in_C, hz_in_x⟩
            rw [h_union_empty] at hz_in_union
            exact False.elim (EmptySet_is_empty z hz_in_union)
          · intro hz_in_empty
            exact False.elim (EmptySet_is_empty z hz_in_empty)
        · -- x ∈ {∅} → x ∈ C, i.e., x = ∅ → x ∈ C
          intro hx_in_singleton
          rw [Singleton_is_specified] at hx_in_singleton
          subst hx_in_singleton
          -- Need to show ∅ ∈ C
          -- Since C ≠ ∅, there exists some element in C
          have h_nonempty_C : ∃ y, y ∈ C := by
            -- Proof by contradiction using absurd
            by_cases h : ∃ y, y ∈ C
            case pos => exact h
            case neg =>
              exfalso
              apply hC_non_empty
              apply ExtSet
              intro z
              constructor
              · intro hz_in_C
                exfalso
                exact h ⟨z, hz_in_C⟩
              · intro hz_in_empty
                exact False.elim (EmptySet_is_empty z hz_in_empty)
          obtain ⟨y, hy_in_C⟩ := h_nonempty_C
          -- Every element of C must be ∅ (since sUnion C = ∅)
          have y_eq_empty : y = ∅ := by
            apply ExtSet
            intro z
            constructor
            · intro hz_in_y
              have hz_in_union : z ∈ (sUnion C) := (mem_sUnion_iff C z).mpr ⟨y, hy_in_C, hz_in_y⟩
              rw [h_union_empty] at hz_in_union
              exact hz_in_union
            · intro hz_in_empty
              exact False.elim (EmptySet_is_empty z hz_in_empty)
          rw [←y_eq_empty]
          exact hy_in_C
      · -- Backward direction: C = {∅} → (sUnion C) = ∅
        intro hC_is_singleton
        rw [hC_is_singleton]
        apply ExtSet
        intro x
        constructor
        · intro hx_in_union
          have : ∃ S, S ∈ ({ ∅ }: U) ∧ x ∈ S := (mem_sUnion_iff ({ ∅ }: U) x).mp hx_in_union
          obtain ⟨S, hS_in_singleton, hx_in_S⟩ := this
          rw [Singleton_is_specified] at hS_in_singleton
          rw [hS_in_singleton] at hx_in_S
          exact False.elim (EmptySet_is_empty x hx_in_S)
        · intro hx_in_empty
          exact False.elim (EmptySet_is_empty x hx_in_empty)

    /-! ### Unión Binaria ### -/
    noncomputable def union (A B : U) : U :=
      sUnion (PairSet A B)

    notation:50 lhs:51 " ∪ " rhs:51 => union lhs rhs



    theorem mem_union_iff (A B x : U) :
      x ∈ (A ∪ B) ↔ x ∈ A ∨ x ∈ B := by
      unfold union
      simp only [mem_sUnion_iff, PairSet_is_specified]
      constructor
      · intro ⟨S, h, hx⟩
        rcases h with rfl | rfl
        · left; exact hx
        · right; exact hx
      · intro h
        rcases h with hx | hx
        · exact ⟨A, Or.inl rfl, hx⟩
        · exact ⟨B, Or.inr rfl, hx⟩

    /-! ### Propiedades Algebraicas de la Unión Binaria ### -/

    theorem union_comm (A B : U) :
      (A ∪ B) = (B ∪ A) := by
      apply ExtSet
      intro x
      simp only [mem_union_iff, or_comm]

    theorem empty_union (A : U) :
      (∅ ∪ A) = A := by
      apply ExtSet
      intro x
      simp only [mem_union_iff]
      exact ⟨fun h => h.resolve_left (EmptySet_is_empty x), Or.inr⟩

    theorem union_empty (A : U) :
      (A ∪ ∅) = A := by
      rw [union_comm, empty_union]

    theorem union_self (A : U) :
      (A ∪ A) = A := by
      apply ExtSet
      intro x
      simp only [mem_union_iff]
      constructor
      · intro h
        cases h with
        | inl hx => exact hx
        | inr hx => exact hx
      · intro hx
        exact Or.inl hx

    theorem union_assoc (A B C : U) :
      ((A ∪ B) ∪ C) = (A ∪ (B ∪ C)) := by
      apply ExtSet
      intro x
      simp only [mem_union_iff]
      constructor
      · intro h
        cases h with
        | inl hAB =>
          cases hAB with
          | inl hA => exact Or.inl hA
          | inr hB => exact Or.inr (Or.inl hB)
        | inr hC => exact Or.inr (Or.inr hC)
      · intro h
        cases h with
        | inl hA => exact Or.inl (Or.inl hA)
        | inr hBC =>
          cases hBC with
          | inl hB => exact Or.inl (Or.inr hB)
          | inr hC => exact Or.inr hC

    theorem sUnion_singleton (A : U) : sUnion {A} = A := by
      apply ExtSet
      intro x
      rw [mem_sUnion_iff]
      constructor
      · intro h
        obtain ⟨y, hy, hx_in_y⟩ := h
        rw [Singleton_is_specified] at hy
        rw [hy] at hx_in_y
        exact hx_in_y
      · intro h
        exists A
        constructor
        · rw [Singleton_is_specified]
        · exact h

    theorem sUnion_union (A B : U) : sUnion (A ∪ B) = ((sUnion A) ∪ (sUnion B)) := by
      apply ExtSet
      intro x
      simp only [mem_sUnion_iff, mem_union_iff]
      constructor
      · rintro ⟨S, hS | hS, hxS⟩
        · exact Or.inl ⟨S, hS, hxS⟩
        · exact Or.inr ⟨S, hS, hxS⟩
      · rintro (⟨S, hSA, hxS⟩ | ⟨S, hSB, hxS⟩)
        · exact ⟨S, Or.inl hSA, hxS⟩
        · exact ⟨S, Or.inr hSB, hxS⟩

theorem union_inter_self (A B : U) :
      ( union A (inter A B) ) = A := by
      apply ExtSet
      intro x
      simp only [mem_union_iff, mem_inter_iff]
      constructor
      · intro h
        cases h with
        | inl hx => exact hx
        | inr hAB => exact hAB.1
      · intro hx
        exact Or.inl hx

    /-! ### Diferencia Simétrica ### -/
    noncomputable def symmDiff (A B : U) : U :=
      union (sdiff A B) (sdiff B A)

    notation:50 lhs:51 " △ " rhs:51 => symmDiff lhs rhs

    theorem mem_symmDiff_iff (A B x : U) :
      x ∈ (A △ B) ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) := by
      unfold symmDiff
      simp only [mem_union_iff, mem_sdiff_iff]

    theorem symmDiff_comm (A B : U) :
      (A △ B) = (B △ A) := by
      apply ExtSet
      intro x
      simp only [mem_symmDiff_iff]
      constructor
      · intro h
        cases h with
        | inl hx => exact Or.inr hx
        | inr hx => exact Or.inl hx
      · intro h
        cases h with
        | inl hx => exact Or.inr hx
        | inr hx => exact Or.inl hx

    theorem empty_symmDiff (A : U) :
      (∅ △ A) = A := by
      apply ExtSet
      intro x
      simp only [mem_symmDiff_iff]
      constructor
      · intro h
        cases h with
        | inl hx => exact False.elim (EmptySet_is_empty x hx.1)
        | inr hx => exact hx.1
      · intro hx
        exact Or.inr ⟨hx, fun h => EmptySet_is_empty x h⟩

    theorem symmDiff_self (A : U) :
      (A △ A) = ∅ := by
      apply ExtSet
      intro x
      simp only [mem_symmDiff_iff]
      constructor
      · intro h
        cases h with
        | inl hx =>
          -- hx: x ∈ A ∧ x ∉ A, contradicción
          have h_in : x ∈ A := hx.1
          have h_notin : x ∉ A := hx.2
          exact False.elim (h_notin h_in)
        | inr hx =>
          -- hx: x ∈ A ∧ x ∉ A, contradicción
          have h_in : x ∈ A := hx.1
          have h_notin : x ∉ A := hx.2
          exact False.elim (h_notin h_in)
      · intro hx
        exact False.elim (EmptySet_is_empty x hx)


  end Axiom.Union
end ZFC

export ZFC.Axiom.Union (
  Axiom.Union
  sUnion_existsUnique
  mem_sUnion_raw
  sUnion
  sUnion_eq_empty
  sUnion_eq_empty'
  mem_sUnion_iff
  sUnion_unique
  sUnion_empty_of_empty
  sUnion_singleton_empty
  sUnion_ne_empty
  sUnion_eq_empty_iff_singleton_empty
  union
  mem_union_iff
  union_comm
  empty_union
  union_empty
  union_self
  union_assoc
  sUnion_singleton
  sUnion_union
  union_inter_self
  symmDiff
  mem_symmDiff_iff
  symmDiff_comm
  empty_symmDiff
  symmDiff_self
)

/-!
## UNION Axiom
# Example of Union Axiom
    C = { {x}, {y} , {z} }
    U = sUnion C
    U = { x, y, z }

# This means that the union set of C is the set of all elements of every element of C.

## Define the Union Set of Two Sets

# The union set of two sets A and B is the set of all elements that are in A, in B, or in both.
# This is often denoted as A union B.
# Example of Union Set
    A = { 1, 2 }
    B = { a, b }
    union A B = { 1, 2, a, b }


-/
