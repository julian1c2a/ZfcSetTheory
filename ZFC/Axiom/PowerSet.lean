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

  namespace Axiom.PowerSet

    /-! ### Axioma de Conjunto Potencia ### -/
    /-! Para todo conjunto A, existe un conjunto P(A) cuyos elementos son
        exactamente los subconjuntos de A:
        ∀A ∃P ∀x (x ∈ P ↔ x ⊆ A) -/
    @[simp]
    axiom PowerSet :
      ∀ (A : U), ∃ (P : U), ∀ (x : U), x ∈ P ↔ x ⊆ A

    /-! ### Teorema de Existencia Única para el Axioma de Potencia ### -/
    @[simp]
    theorem powersetExistsUnique (A : U) :
      ∃! P, ∀ x : U, x ∈ P ↔ x ⊆ A
        := by
      obtain ⟨P, hP⟩ := PowerSet A
      apply ExistsUnique.intro P
      · exact hP
      · intros P₁ h₁
        apply ExtSet
        intro x
        constructor
        · intro hx
          exact (hP x).mpr ((h₁ x).mp hx)
        · intro hx
          exact (h₁ x).mpr ((hP x).mp hx)

    /-! ### Definición del Conjunto Potencia ### -/
    @[simp]
    noncomputable def powerset (A : U) : U :=
      (powersetExistsUnique A).choose

    notation " 𝒫 " A: 100 => powerset A

    /-! ### Teorema de Especificación del Conjunto Potencia ### -/
    @[simp]
    theorem mem_powerset_iff (A x : U) :
      x ∈ (𝒫 A) ↔ x ⊆ A
        := by
      unfold powerset
      exact (powersetExistsUnique A).choose_spec x

    /-! ### Unicidad del Conjunto Potencia ### -/
    @[simp]
    theorem powerset_eq_iff (A P : U) :
      (∀ (x : U), x ∈ P ↔ x ⊆ A) ↔ (P = 𝒫 A)
        := by
      constructor
      · intro h
        apply ExtSet
        intro x
        rw [h, mem_powerset_iff]
      · intro h_eq
        rw [h_eq]
        intro x
        exact mem_powerset_iff A x

    /-! ============================================================ -/
    /-! ### PROPIEDADES BÁSICAS DEL CONJUNTO POTENCIA ### -/
    /-! ============================================================ -/

    /-! ### El conjunto vacío pertenece a cualquier conjunto potencia ### -/
    theorem empty_mem_powerset (A : U) :
      ∅ ∈ (𝒫 A)
        := by
      rw [mem_powerset_iff]
      exact EmptySet_subseteq_any A

    /-! ### Todo conjunto pertenece a su propio conjunto potencia ### -/
    theorem self_mem_powerset (A : U) :
      A ∈ (𝒫 A)
        := by
      rw [mem_powerset_iff]
      exact subset_refl A

    /-! ### El conjunto potencia nunca es vacío ### -/
    theorem powerset_nonempty (A : U) :
      (𝒫 A) ≠ ∅
        := by
      intro h
      have h_empty_mem := empty_mem_powerset A
      rw [h] at h_empty_mem
      exact EmptySet_is_empty ∅ h_empty_mem

    /-! ### La potencia del vacío es el singleton del vacío ### -/
    theorem powerset_empty :
      (𝒫 (∅ : U)) = ({∅} : U)
        := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_powerset_iff] at hx
        rw [Singleton_is_specified]
        -- x ⊆ ∅ implica x = ∅
        apply ExtSet
        intro z
        constructor
        · intro hz
          exact hx z hz
        · intro hz
          exact False.elim (EmptySet_is_empty z hz)
      · intro hx
        rw [Singleton_is_specified] at hx
        rw [mem_powerset_iff, hx]
        exact EmptySet_subseteq_any ∅

    /-! ============================================================ -/
    /-! ### RELACIONES CON SUBCONJUNTOS ### -/
    /-! ============================================================ -/

    /-! ### Si A ⊆ B entonces 𝒫(A) ⊆ 𝒫(B) ### -/
    theorem powerset_mono (A B : U) (h : A ⊆ B) :
      (𝒫 A) ⊆ (𝒫 B)
        := by
      intro x hx
      rw [mem_powerset_iff] at hx ⊢
      exact subset_trans x A B hx h

    /-! ### Recíproco: Si 𝒫(A) ⊆ 𝒫(B) entonces A ⊆ B ### -/
    theorem powerset_mono_iff (A B : U) :
      (𝒫 A) ⊆ (𝒫 B) ↔ A ⊆ B
        := by
      constructor
      · -- (→) 𝒫 A ⊆ 𝒫 B → A ⊆ B
        intro h
        -- A ∈ 𝒫 A por self_mem_powerset
        have hA_in_PA : A ∈ (𝒫 A) := self_mem_powerset A
        -- Por hipótesis, A ∈ 𝒫 B
        have hA_in_PB : A ∈ (𝒫 B) := h A hA_in_PA
        -- Por especificación, A ⊆ B
        exact (mem_powerset_iff B A).mp hA_in_PB
      · -- (←) A ⊆ B → 𝒫 A ⊆ 𝒫 B
        exact powerset_mono A B

    /-! ============================================================ -/
    /-! ### RELACIONES CON UNIÓN E INTERSECCIÓN ### -/
    /-! ============================================================ -/

    /-! ### 𝒫(A) ∩ 𝒫(B) = 𝒫(A ∩ B) ### -/
    theorem powerset_inter (A B : U) :
      ((𝒫 A) ∩ (𝒫 B)) = (𝒫 (A ∩ B))
        := by
      apply ExtSet
      intro x
      constructor
      · -- (→) x ∈ 𝒫(A) ∩ 𝒫(B) → x ∈ 𝒫(A ∩ B)
        intro hx
        rw [mem_inter_iff, mem_powerset_iff, mem_powerset_iff] at hx
        rw [mem_powerset_iff]
        -- x ⊆ A y x ⊆ B implica x ⊆ A ∩ B
        intro z hz
        rw [mem_inter_iff]
        exact ⟨hx.1 z hz, hx.2 z hz⟩
      · -- (←) x ∈ 𝒫(A ∩ B) → x ∈ 𝒫(A) ∩ 𝒫(B)
        intro hx
        rw [mem_powerset_iff] at hx
        rw [mem_inter_iff, mem_powerset_iff, mem_powerset_iff]
        constructor
        · -- x ⊆ A
          intro z hz
          have hz_inter := hx z hz
          exact (mem_inter_iff A B z).mp hz_inter |>.1
        · -- x ⊆ B
          intro z hz
          have hz_inter := hx z hz
          exact (mem_inter_iff A B z).mp hz_inter |>.2

    /-! ### 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) (la igualdad NO vale en general) ### -/
    theorem powerset_union_subset (A B : U) :
      ((𝒫 A) ∪ (𝒫 B)) ⊆ (𝒫 (A ∪ B))
        := by
      intro x hx
      rw [mem_union_iff, mem_powerset_iff, mem_powerset_iff] at hx
      rw [mem_powerset_iff]
      cases hx with
      | inl hxA =>
        -- x ⊆ A, entonces x ⊆ A ∪ B
        intro z hz
        rw [mem_union_iff]
        exact Or.inl (hxA z hz)
      | inr hxB =>
        -- x ⊆ B, entonces x ⊆ A ∪ B
        intro z hz
        rw [mem_union_iff]
        exact Or.inr (hxB z hz)

    /-! ============================================================ -/
    /-! ### RELACIONES CON LA UNIÓN GENERALIZADA ### -/
    /-! ============================================================ -/

    /-! ### A ⊆ 𝒫(⋃ A) para cualquier familia A ### -/
    theorem subset_powerset_sUnion (A : U) :
      A ⊆ (𝒫 (⋃ A))
        := by
      intro x hx
      rw [mem_powerset_iff]
      -- x ∈ A, debemos probar x ⊆ ⋃ A
      intro z hz
      rw [mem_sUnion_iff]
      exact ⟨x, hx, hz⟩

    /-! ### ⋃ 𝒫(A) = A ### -/
    theorem sUnion_powerset (A : U) :
      ⋃ (𝒫 A) = A
        := by
      apply ExtSet
      intro x
      constructor
      · -- (→) x ∈ ⋃ 𝒫(A) → x ∈ A
        intro hx
        rw [mem_sUnion_iff] at hx
        obtain ⟨S, hS_in_PA, hx_in_S⟩ := hx
        rw [mem_powerset_iff] at hS_in_PA
        -- S ⊆ A y x ∈ S implica x ∈ A
        exact hS_in_PA x hx_in_S
      · -- (←) x ∈ A → x ∈ ⋃ 𝒫(A)
        intro hx
        rw [mem_sUnion_iff]
        -- Tomamos S = {x}
        refine ⟨({x} : U), ?_, ?_⟩
        · -- {x} ∈ 𝒫(A), es decir, {x} ⊆ A
          rw [mem_powerset_iff]
          intro z hz
          rw [Singleton_is_specified] at hz
          rw [hz]
          exact hx
        · -- x ∈ {x}
          rw [Singleton_is_specified]

  end Axiom.PowerSet
end ZFC

export ZFC.Axiom.PowerSet (
  PowerSet
  powersetExistsUnique
  powerset
  mem_powerset_iff
  powerset_eq_iff
  empty_mem_powerset
  self_mem_powerset
  powerset_nonempty
  powerset_empty
  powerset_mono
  powerset_mono_iff
  powerset_inter
  powerset_union_subset
  subset_powerset_sUnion
  sUnion_powerset
)

/-!
## Axioma de Conjunto Potencia (Power Set Axiom)

### Enunciado formal:
∀A ∃P ∀x (x ∈ P ↔ x ⊆ A)

### Intuición:
Para cualquier conjunto A, existe el conjunto de todos sus subconjuntos,
denotado 𝒫(A) o P(A).

### Ejemplos:
- 𝒫(∅) = {∅}
- 𝒫({a}) = {∅, {a}}
- 𝒫({a,b}) = {∅, {a}, {b}, {a,b}}

### Propiedades fundamentales:
1. ∅ ∈ 𝒫(A) para todo A
2. A ∈ 𝒫(A) para todo A
3. 𝒫(A) ≠ ∅ para todo A
4. |𝒫(A)| = 2^|A| para conjuntos finitos
5. A ⊆ B ⟹ 𝒫(A) ⊆ 𝒫(B)
6. 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B)
7. 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) (desigualdad estricta en general)
8. ⋃ 𝒫(A) = A

### Teorema de Cantor:
No existe función sobreyectiva f : A → 𝒫(A).
El Teorema de Cantor formal se encuentra en el módulo `Cardinality.lean`.

### Notas de implementación:
- Los teoremas comentados requieren desarrollos adicionales
- El Teorema de Cantor requiere definir funciones y sobreyectividad
- Las propiedades de cardinalidad requieren desarrollar números naturales
-/
