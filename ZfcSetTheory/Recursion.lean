/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  # Teorema de Recursión

  Este archivo formaliza el Teorema de Recursión en la Teoría de Conjuntos ZFC.
  Permite definir funciones f: ω → A tales que:
    f(0) = a
    f(σ n) = g(f(n))

  ## Estructura de la prueba
  1. Definimos `isComputation n f`: f es una aproximación de longitud n.
  2. Probamos que para cada n, el cómputo es único (`computation_uniqueness`).
  3. Probamos que para cada n, el cómputo existe (`computation_existence`).
  4. Definimos la función final como la unión de todos los cómputos.
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
import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.Functions
  open SetUniverse.NaturalNumbers
  open SetUniverse.InfinityAxiom

  universe u
  variable {U : Type u}

  namespace Recursion

    /-! ============================================================ -/
    /-! ### 1. DEFINICIÓN DE CÓMPUTO DE LONGITUD n ### -/
    /-! ============================================================ -/

    /-!
      Un conjunto `f` es un cómputo de longitud `n` para la base `a` y el paso `g` si:
      1. `f` es una función con dominio `σ(n)` (es decir, {0, ..., n}).
      2. `f(0) = a`.
      3. `∀ k ∈ n, f(σ k) = g(f(k))`.
    -/
    def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      isFunctionFromTo f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))

    /-! ============================================================ -/
    /-! ### 2. UNICIDAD DEL CÓMPUTO ### -/
    /-! ============================================================ -/

    /-!
      Lema: Si f y f' son cómputos de longitud n, entonces f = f'.
      Demostración: Usamos el Principio de Inducción sobre n.

      Sea S = { n ∈ ω | los cómputos de longitud n son únicos }.
      Probaremos que S = ω.
    -/

    theorem computation_uniqueness (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∀ n, n ∈ ω → ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂ := by

      -- Definimos el conjunto S para la inducción
      let S := SpecSet ω (fun n => ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂)

      -- Aplicamos el principio de inducción
      have h_ind : S = ω := by
        apply induction_principle S
        · -- S ⊆ ω
          intro x hx
          rw [SpecSet_is_specified] at hx
          exact hx.1

        · -- CASO BASE: n = 0
          -- isComputation 0 f implica dom(f) = σ(0) = {0}.
          -- f(0) = a. Una función con dominio unitario está determinada por su valor.
          rw [SpecSet_is_specified]
          constructor
          · exact zero_in_Omega
          · intro f₁ f₂ hf₁ hf₂
            obtain ⟨hfunc1, hval1, _⟩ := hf₁
            obtain ⟨hfunc2, hval2, _⟩ := hf₂

            -- f₁ y f₂ son funciones {0} → A
            have h_dom1 : domain f₁ = σ (∅ : U) := hfunc1.1
            have h_dom2 : domain f₂ = σ (∅ : U) := hfunc2.1

            -- Probamos que f₁ = f₂ comprobando sus pares ordenados
            apply ExtSet
            intro p
            constructor
            · intro hp
              -- Si p ∈ f₁, p = ⟨x, y⟩ con x ∈ {0}
              have hp_pair : isOrderedPair p := hfunc1.2.1.1 p hp
              rw [isOrderedPair_iff] at hp_pair
              obtain ⟨x, y, hp_eq⟩ := hp_pair
              have hx_dom : x ∈ domain f₁ := by
                rw [h_dom1, successor_is_specified, Singleton_is_specified]; left; exact domain_is_specified f₁ x |>.mpr ⟨y, hp⟩

              -- Como dominio es {0}, x = 0
              rw [one_eq, Singleton_is_specified] at hx_dom
              rw [hx_dom] at hp_eq

              -- Como f₁ es función, y = f₁(0) = a
              have hy_val : y = a := by
                rw [←hval1]
                apply function_apply_def f₁ (∅ : U) y hfunc1.2.1 hp (by rw [hp_eq]; rw [fst_of_ordered_pair])

              rw [hy_val] at hp_eq
              -- p = ⟨0, a⟩. Ahora vemos si está en f₂
              -- f₂(0) = a, así que ⟨0, a⟩ ∈ f₂
              have h_in_f2 : ⟨(∅ : U), a⟩ ∈ f₂ := by
                rw [←hval2]
                exact apply_mem f₂ (∅ : U) hfunc2.2.1 (by rw [h_dom2, one_eq, Singleton_is_specified])

              rw [←hp_eq] at h_in_f2
              exact h_in_f2

            · -- Dirección simétrica f₂ ⊆ f₁ (análoga)
              intro hp
              have hp_pair : isOrderedPair p := hfunc2.2.1.1 p hp
              rw [isOrderedPair_iff] at hp_pair
              obtain ⟨x, y, hp_eq⟩ := hp_pair
              have hx_dom : x ∈ domain f₂ := by
                 rw [h_dom2, successor_is_specified, Singleton_is_specified]; left; exact domain_is_specified f₂ x |>.mpr ⟨y, hp⟩
              rw [one_eq, Singleton_is_specified] at hx_dom
              rw [hx_dom] at hp_eq
              have hy_val : y = a := by
                rw [←hval2]
                apply function_apply_def f₂ (∅ : U) y hfunc2.2.1 hp (by rw [hp_eq]; rw [fst_of_ordered_pair])
              rw [hy_val] at hp_eq
              have h_in_f1 : ⟨(∅ : U), a⟩ ∈ f₁ := by
                rw [←hval1]
                exact apply_mem f₁ (∅ : U) hfunc1.2.1 (by rw [h_dom1, one_eq, Singleton_is_specified])
              rw [←hp_eq] at h_in_f1
              exact h_in_f1

        · -- PASO INDUCTIVO: n → σ n
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S ⊢
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S

          constructor
          · exact succ_in_Omega n hn_omega
          · intro f₁ f₂ hf₁ hf₂
            -- f₁ y f₂ son cómputos de longitud σ(σ n).
            -- Estrategia: Restringir f₁ y f₂ a σ(n).
            -- La restricción debe ser un cómputo de longitud n.
            -- Por HI, las restricciones son iguales.
            -- Luego probamos que coinciden en el último punto σ(n).

            -- Nota técnica: Implementar restricción de funciones en Functions.lean ayudaría,
            -- pero podemos hacerlo "a mano" sabiendo que los puntos coinciden.

            apply ExtSet
            intro p
            rw [OrderedPair_in_CartesianProduct] -- Simplificación conceptual
            -- p = ⟨x, y⟩
            -- Si x ∈ σ(n), usamos HI.
            -- Si x = σ(n), usamos la regla recursiva.
            sorry -- (Aquí va la lógica detallada del paso inductivo, que es larga)

      -- Conclusión
      intro n hn f₁ f₂ hf₁ hf₂
      have hn_S : n ∈ S := by rw [h_ind]; exact hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2 f₁ f₂ hf₁ hf₂

  end Recursion
end SetUniverse
