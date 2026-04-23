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
import ZFC.Axiom.Existence
import ZFC.Axiom.Specification
import ZFC.Axiom.Pairing
import ZFC.Axiom.Union

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  universe u
  variable {U : Type u}

  namespace BoolAlg.Basic

    /-! ### Álgebra Booleana - Teoremas que mezclan ∪ y ∩ ### -/

    /-! Absorción -/
    theorem union_inter_self (A B : U) :
      (A ∪ (A ∩ B)) = A := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_union_iff] at hx
        cases hx with
        | inl hA => exact hA
        | inr hAB =>
          rw [mem_inter_iff] at hAB
          exact hAB.1
      · intro hA
        rw [mem_union_iff]
        exact Or.inl hA

    theorem inter_union_self (A B : U) :
      (A ∩ (A ∪ B)) = A := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_inter_iff] at hx
        exact hx.1
      · intro hA
        rw [mem_inter_iff, mem_union_iff]
        exact ⟨hA, Or.inl hA⟩

    /-! ### Distributividad ### -/

    theorem union_inter_distrib_left (A B C : U) :
      (A ∪ (B ∩ C)) = ((A ∪ B) ∩ (A ∪ C)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_union_iff] at hx
        rw [mem_inter_iff, mem_union_iff, mem_union_iff]
        cases hx with
        | inl hA => exact ⟨Or.inl hA, Or.inl hA⟩
        | inr hBC =>
          rw [mem_inter_iff] at hBC
          exact ⟨Or.inr hBC.1, Or.inr hBC.2⟩
      · intro hx
        rw [mem_inter_iff, mem_union_iff, mem_union_iff] at hx
        rw [mem_union_iff]
        cases hx.1 with
        | inl hA => exact Or.inl hA
        | inr hB =>
          cases hx.2 with
          | inl hA => exact Or.inl hA
          | inr hC =>
            rw [mem_inter_iff]
            exact Or.inr ⟨hB, hC⟩

    theorem inter_union_distrib_left (A B C : U) :
      (A ∩ (B ∪ C)) = ((A ∩ B) ∪ (A ∩ C)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_inter_iff, mem_union_iff] at hx
        rw [mem_union_iff]
        cases hx.2 with
        | inl hB =>
          rw [mem_inter_iff]
          exact Or.inl ⟨hx.1, hB⟩
        | inr hC =>
          exact Or.inr ((mem_inter_iff A C x).mpr ⟨hx.1, hC⟩)
      · intro hx
        rw [mem_union_iff] at hx
        rw [mem_inter_iff, mem_union_iff]
        cases hx with
        | inl hAB =>
          rw [mem_inter_iff] at hAB
          exact ⟨hAB.1, Or.inl hAB.2⟩
        | inr hAC =>
          rw [mem_inter_iff] at hAC
          exact ⟨hAC.1, Or.inr hAC.2⟩

    /-! ### Leyes de De Morgan ### -/

    theorem compl_union (A B C : U) :
      (C \ (A ∪ B)) = ((C \ A) ∩ (C \ B)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_sdiff_iff, mem_union_iff] at hx
        rw [mem_inter_iff, mem_sdiff_iff, mem_sdiff_iff]
        constructor
        · exact ⟨hx.1, fun hA => hx.2 (Or.inl hA)⟩
        · exact ⟨hx.1, fun hB => hx.2 (Or.inr hB)⟩
      · intro hx
        rw [mem_inter_iff, mem_sdiff_iff, mem_sdiff_iff] at hx
        rw [mem_sdiff_iff, mem_union_iff]
        exact ⟨hx.1.1, fun h => h.elim hx.1.2 hx.2.2⟩

    theorem compl_inter (A B C : U) :
      (C \ (A ∩ B)) = ((C \ A) ∪ (C \ B)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_sdiff_iff, mem_inter_iff] at hx
        rw [mem_union_iff]
        by_cases hA : x ∈ A
        · -- x ∈ A, entonces x ∉ B (de lo contrario x ∈ A ∩ B)
          have hnotB : x ∉ B := fun hB => hx.2 ⟨hA, hB⟩
          exact Or.inr ((mem_sdiff_iff C B x).mpr ⟨hx.1, hnotB⟩)
        · -- x ∉ A
          exact Or.inl ((mem_sdiff_iff C A x).mpr ⟨hx.1, hA⟩)
      · intro hx
        rw [mem_union_iff] at hx
        rw [mem_sdiff_iff, mem_inter_iff]
        cases hx with
        | inl hCA =>
          rw [mem_sdiff_iff] at hCA
          exact ⟨hCA.1, fun hAB => hCA.2 hAB.1⟩
        | inr hCB =>
          rw [mem_sdiff_iff] at hCB
          exact ⟨hCB.1, fun hAB => hCB.2 hAB.2⟩

    /-! ### Complemento Relativo ### -/

    theorem Complement_union (A C : U) (h : A ⊆ C) :
      (A ∪ (C \ A)) = C := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_union_iff] at hx
        cases hx with
        | inl hA => exact h x hA
        | inr hCA =>
          rw [mem_sdiff_iff] at hCA
          exact hCA.1
      · intro hC
        rw [mem_union_iff]
        by_cases hA : x ∈ A
        · exact Or.inl hA
        · rw [mem_sdiff_iff]
          exact Or.inr ⟨hC, hA⟩

    theorem Complement_inter (A C : U) :
      (A ∩ (C \ A)) = ∅ := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_inter_iff, mem_sdiff_iff] at hx
        exact False.elim (hx.2.2 hx.1)
      · intro hEmpty
        exact False.elim (EmptySet_is_empty x hEmpty)

  end BoolAlg.Basic

end ZFC

export ZFC.BoolAlg.Basic (
  union_inter_self
  inter_union_self
  union_inter_distrib_left
  inter_union_distrib_left
  compl_union
  compl_inter
  Complement_union
  Complement_inter
)
