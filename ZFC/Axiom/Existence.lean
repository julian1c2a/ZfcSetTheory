/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import Init.Classical
import ZFC.Core.Prelim
import ZFC.Axiom.Extension

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  universe u
  variable {U : Type u}

  namespace Axiom.Existence

    /-! ### Axioma de Existencia ### -/
    /-! ### Existence : existe algún conjunto vacío en el universo U ### -/
    @[simp]
    axiom ExistsAnEmptySet : ∃ (x : U), ∀ (y : U), y ∉ x

    /-! ### Teorema de Existencia Única ### -/
    /-! ### ExistsUniqueEmptySet : existe un único conjunto vacío en el universo U ### -/
    @[simp]
    theorem ExistsUniqueEmptySet :
      ∃! x, ∀ y : U, y ∉ x
        := by
      obtain ⟨x, hx⟩ := ExistsAnEmptySet
      apply ExistsUnique.intro x
      · exact hx
      · -- Unicidad del conjunto vacío
        intro y hy_empty
        apply (ExtSet y x)
        intro z
        constructor
        · -- Dirección ->
          intro hz_in_y
          exfalso
          exact hy_empty z hz_in_y
        · -- Dirección <-
          intro hz_in_x
          exfalso
          exact hx z hz_in_x

    @[simp]
    noncomputable def EmptySet : U :=
      ExistsUnique.choose ExistsUniqueEmptySet

    @[simp]
    theorem EmptySet_is_empty : ∀ (y : U), y ∉ EmptySet := by
      intro y
      exact (ExistsUnique.choose_spec ExistsUniqueEmptySet) y

    @[simp]
    theorem EmptySet_unique : ∀ (x : U), (∀ (y : U), y ∉ x) → (x = EmptySet) := by
      intro x hx_empty
      apply ExtSet
      intro y
      constructor
      · -- Dirección ->
        intro hy_in_x
        exfalso
        apply hx_empty y
        exact hy_in_x
      · -- Dirección <-
        intro hy_in_empty
        exfalso
        exact EmptySet_is_empty y hy_in_empty

    notation " ∅ " => EmptySet

    @[simp]
    theorem EmptySet_subseteq_any (x : U) : ∅ ⊆ x := by
      intro y hy_in_empty
      exfalso
      exact EmptySet_is_empty y hy_in_empty

  end Axiom.Existence
end ZFC

export ZFC.Axiom.Existence (
    ExistsAnEmptySet ExistsUniqueEmptySet EmptySet EmptySet_is_empty EmptySet_unique
    EmptySet_subseteq_any
)
