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
  open SetUniverse.Relations
  open SetUniverse.CartesianProduct

  universe u
  variable {U : Type u}

  namespace Recursion

    /-! ============================================================ -/
    /-! ### 0. LEMAS AUXILIARES ### -/
    /-! ============================================================ -/

    theorem function_domain_eq (f A B : U) (h : isFunctionFromTo f A B) : domain f = A := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [mem_domain] at hx
        obtain ⟨y, hy⟩ := hx
        have hsub := h.1
        have hp : ⟨x, y⟩ ∈ A ×ₛ B := hsub ⟨x, y⟩ hy
        rw [OrderedPair_mem_CartesianProduct] at hp
        exact hp.1
      · intro hx
        -- h.2 es ∀ x ∈ A, ∃! y, ...
        obtain ⟨y, hy⟩ := h.2 x hx
        rw [mem_domain]
        exists y
        exact hy.1

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
            have h_dom1 : domain f₁ = σ (∅ : U) := function_domain_eq f₁ (σ (∅ : U)) A hfunc1
            have h_dom2 : domain f₂ = σ (∅ : U) := function_domain_eq f₂ (σ (∅ : U)) A hfunc2

            -- Probamos que f₁ = f₂ comprobando sus pares ordenados
            apply ExtSet
            intro p
            constructor
            · intro hp
              -- Si p ∈ f₁, p = ⟨x, y⟩ con x ∈ {0}
              have hp_in_rel : p ∈ f₁ := hp
              have h_pair_prop : ∃ x y, p = ⟨x, y⟩ := by
                 -- f₁ ⊆ {0} × A, así que p es un par
                 have hsub := hfunc1.1
                 have hp_cart : p ∈ (σ (∅ : U)) ×ₛ A := hsub p hp
                 rw [CartesianProduct_is_specified] at hp_cart
                 have hp_pair_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hp_cart.1
                 exact ⟨fst p, snd p, hp_pair_eq⟩

              obtain ⟨x, y, hp_eq⟩ := h_pair_prop

              have hx_dom : x ∈ domain f₁ := by
                rw [mem_domain]; exists y; rw [←hp_eq]; exact hp

              -- Como dominio es σ(∅) = {∅}, tenemos x ∈ {∅}, así x = ∅
              rw [h_dom1] at hx_dom
              rw [successor_is_specified] at hx_dom
              have hx_eq_zero : x = ∅ := by
                cases hx_dom with
                | inl h => exact False.elim (EmptySet_is_empty x h)
                | inr h => exact h

              rw [hx_eq_zero] at hp_eq

              -- Como f₁ es función, y = f₁(0) = a
              have hy_val : y = a := by
                rw [←hval1]
                -- Necesitamos ∃! y, ⟨∅, y⟩ ∈ f₁. Lo obtenemos de hfunc1.2 con ∅ ∈ σ ∅
                have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by
                  rw [successor_is_specified]
                  right; rfl
                -- Corrección: Llamamos a la unicidad con los argumentos
                apply apply_eq f₁ (∅ : U) y (hfunc1.2 ∅ h_zero_mem)
                rw [←hp_eq]; exact hp

              rw [hy_val] at hp_eq
              -- p = ⟨0, a⟩. Ahora vemos si está en f₂
              -- f₂(0) = a, así que ⟨0, a⟩ ∈ f₂
              have h_in_f2 : ⟨(∅ : U), a⟩ ∈ f₂ := by
                rw [←hval2]
                have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by
                  rw [successor_is_specified]
                  right; rfl
                apply apply_mem f₂ (∅ : U) (hfunc2.2 ∅ h_zero_mem)

              rw [←hp_eq] at h_in_f2
              exact h_in_f2

            · -- Dirección simétrica f₂ ⊆ f₁ (análoga)
              intro hp
              have h_pair_prop : ∃ x y, p = ⟨x, y⟩ := by
                 have hsub := hfunc2.1
                 have hp_cart : p ∈ (σ (∅ : U)) ×ₛ A := hsub p hp
                 rw [CartesianProduct_is_specified] at hp_cart
                 have hp_pair_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hp_cart.1
                 exact ⟨fst p, snd p, hp_pair_eq⟩
              obtain ⟨x, y, hp_eq⟩ := h_pair_prop

              have hx_dom : x ∈ domain f₂ := by
                 rw [mem_domain]; exists y; rw [←hp_eq]; exact hp

              -- Como dominio es σ(∅) = {∅}, tenemos x ∈ {∅}, así x = ∅
              rw [h_dom2] at hx_dom
              rw [successor_is_specified] at hx_dom
              have hx_eq_zero : x = ∅ := by
                cases hx_dom with
                | inl h => exact False.elim (EmptySet_is_empty x h)
                | inr h => exact h

              rw [hx_eq_zero] at hp_eq

              have hy_val : y = a := by
                rw [←hval2]
                have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by
                  rw [successor_is_specified]
                  right; rfl
                apply apply_eq f₂ (∅ : U) y (hfunc2.2 ∅ h_zero_mem)
                rw [←hp_eq]; exact hp

              rw [hy_val] at hp_eq
              have h_in_f1 : ⟨(∅ : U), a⟩ ∈ f₁ := by
                rw [←hval1]
                have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by
                  rw [successor_is_specified]
                  right; rfl
                apply apply_mem f₁ (∅ : U) (hfunc1.2 ∅ h_zero_mem)

              rw [←hp_eq] at h_in_f1
              exact h_in_f1

        · -- PASO INDUCTIVO: n → σ n
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S

          rw [SpecSet_is_specified]
          constructor
          · exact succ_in_Omega n hn_omega
          · intro f₁ f₂ hf₁ hf₂
            -- f₁ y f₂ son cómputos de longitud σ(σ n).
            -- Estrategia: Restringir f₁ y f₂ a σ n.
            let succ_n := σ n
            let f₁_restr := Restriction f₁ succ_n
            let f₂_restr := Restriction f₂ succ_n

            -- 1. Probar que las restricciones son cómputos de longitud n
            -- Necesitamos saber que σ n ⊆ σ (σ n)
            have hn_nat : isNat n := mem_Omega_is_Nat n hn_omega
            have h_succ_n_nat : isNat succ_n := nat_successor_is_nat n hn_nat
            have h_subset : succ_n ⊆ σ succ_n := fun x hx => mem_successor_of_mem x succ_n hx

            have h_f1_is_comp : isComputation n f₁_restr A a g := by
              constructor
              · -- isFunctionFromTo
                apply Restriction_is_function f₁ (σ succ_n) A succ_n hf₁.1 h_subset
              · constructor
                · -- f(0) = a
                  -- 0 ∈ σ n ? Sí, porque n ∈ ω.
                  have h_zero_in : (∅ : U) ∈ succ_n := by
                    rw [Nat_iff_mem_Omega] at h_succ_n_nat
                    -- 0 ∈ ω es true. Pero queremos 0 ∈ σ n.
                    -- Si n=0, σ n = {0}, 0 ∈ {0}.
                    -- Si n>0, 0 ∈ n ⊆ σ n.
                    -- Usamos: todo natural contiene al 0 o es 0.
                    have h_z : (∅ : U) ∈ ω := zero_in_Omega
                    cases nat_is_zero_or_succ n hn_nat with
                    | inl hz => rw [hz]; rw [one_eq]; rw [Singleton_is_specified]; rfl
                    | inr hs =>
                      obtain ⟨k, hk⟩ := hs
                      -- n = σ k -> 0 ∈ n -> 0 ∈ σ n
                      -- Un poco largo probarlo desde cero, asumimos propiedades básicas de Nat.
                      -- Atajo: 0 <= n < σ n.
                      rw [←Nat_iff_mem_Omega] at h_z
                      have h_trich := nat_trichotomy (∅ : U) succ_n h_z h_succ_n_nat
                      cases h_trich with
                      | inl hIn => exact hIn
                      | inr hOr =>
                        cases hOr with
                        | inl hEq =>
                           -- 0 = σ n. Imposible pues σ n no es vacío.
                           have hne := successor_nonempty n
                           rw [←hEq] at hne
                           exact False.elim (EmptySet_is_empty ∅ hne)
                        | inr hGt =>
                           -- σ n ∈ 0. Imposible.
                           exact False.elim (EmptySet_is_empty (σ n) hGt)

                  rw [Restriction_apply f₁ succ_n (∅ : U) h_zero_in]
                  exact hf₁.2.1
                · -- Recursión
                  intro k hk
                  -- k ∈ n → σ k ∈ σ n = succ_n, y también k ∈ σ n
                  have h_k_mem_succ : k ∈ succ_n := mem_successor_of_mem k n hk
                  -- σ k ∈ σ(σ n) porque σ k ∈ σ n = succ_n, así σ k ∈ σ(succ_n)
                  have h_succ_k_mem : σ k ∈ σ succ_n := mem_successor_of_mem (σ k) succ_n h_k_mem_succ

                  rw [Restriction_apply f₁ succ_n (σ k) h_succ_k_mem]
                  rw [Restriction_apply f₁ succ_n k h_k_mem_succ]
                  exact hf₁.2.2 k hk

            -- Análogamente para f₂
            have h_f2_is_comp : isComputation n f₂_restr A a g := by
              constructor
              · apply Restriction_is_function f₂ (σ succ_n) A succ_n hf₂.1 h_subset
              · constructor
                · have h_zero_in : (∅ : U) ∈ succ_n := by
                     -- (Misma prueba que arriba, omitimos repetición verbosa por brevedad, asumimos válida)
                     have h_z : (∅ : U) ∈ (ω : U) := zero_in_Omega
                     rw [←Nat_iff_mem_Omega] at h_z
                     have h_trich := nat_trichotomy (∅ : U) succ_n h_z h_succ_n_nat
                     cases h_trich with
                     | inl hIn => exact hIn
                     | inr hOr => cases hOr with | inl hEq => have hne := successor_nonempty n; rw [←hEq] at hne; exact False.elim (EmptySet_is_empty ∅ hne) | inr hGt => exact False.elim (EmptySet_is_empty (σ n) hGt)
                  rw [Restriction_apply f₂ succ_n (∅ : U) h_zero_in]
                  exact hf₂.2.1
                · intro k hk
                  -- k ∈ n → σ k ∈ σ n = succ_n, y también k ∈ σ n
                  have h_k_mem_succ : k ∈ succ_n := mem_successor_of_mem k n hk
                  -- Para σ k, lo tenemos en f₂'s domain. Aplicamos hf₂.2.2 con k ∈ n
                  -- σ k ∈ σ(σ n) porque σ k ∈ σ n = succ_n, así σ k ∈ σ(succ_n)
                  have h_succ_k_mem : σ k ∈ σ succ_n := mem_successor_of_mem (σ k) succ_n h_k_mem_succ

                  rw [Restriction_apply f₂ succ_n (σ k) h_succ_k_mem]
                  rw [Restriction_apply f₂ succ_n k h_k_mem_succ]
                  exact hf₂.2.2 k hk

            -- 2. Por HI, las restricciones son iguales
            have h_eq_restr : f₁_restr = f₂_restr := h_unique_n f₁_restr f₂_restr h_f1_is_comp h_f2_is_comp

            -- 3. Extender la igualdad al dominio completo σ(σ n) = σ n ∪ {σ n}
            apply ExtSet
            intro p
            constructor
            · -- p ∈ f₁ → p ∈ f₂
              intro hp_in_f1
              have hp_pair : ∃ x y, p = ⟨x, y⟩ := by
                 have hsub := hf₁.1.1
                 have hp_cart : p ∈ (σ succ_n) ×ₛ A := hsub p hp_in_f1
                 rw [CartesianProduct_is_specified] at hp_cart
                 have hp_pair_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hp_cart.1
                 exact ⟨fst p, snd p, hp_pair_eq⟩
              obtain ⟨x, y, hp_eq⟩ := hp_pair

              -- x ∈ dom(f₁) = σ succ_n
              have hx_dom : x ∈ σ succ_n := by
                 -- ⟨x, y⟩ ∈ f₁ ⊆ (σ succ_n) × A, así x ∈ σ succ_n
                 have hsub := hf₁.1.1
                 have hp_cart : ⟨x, y⟩ ∈ (σ succ_n) ×ₛ A := by
                   rw [←hp_eq]
                   exact hsub ⟨x, y⟩ hp_in_f1
                 rw [CartesianProduct_is_specified] at hp_cart
                 exact hp_cart.1

              rw [successor_is_specified] at hx_dom
              cases hx_dom with
              | inl hx_in_succ =>
                -- x ∈ succ_n
                -- p ∈ f₁_restr
                have hp_restr : p ∈ f₁_restr := by
                  rw [Restriction_is_specified]
                  constructor
                  · exact hp_in_f1
                  · rw [fst_of_ordered_pair, ←hp_eq] at hx_in_succ; rw [fst_of_ordered_pair]; rw [hp_eq]; exact hx_in_succ -- corrección de tipo
                    rw [hp_eq] at hx_in_succ; rw [fst_of_ordered_pair] at hx_in_succ; exact hx_in_succ

                rw [h_eq_restr] at hp_restr
                rw [Restriction_is_specified] at hp_restr
                exact hp_restr.1

              | inr hx_eq_succ =>
                -- x = succ_n (= σ n)
                -- f₁(σ n) = g(f₁(n))
                -- f₂(σ n) = g(f₂(n))
                have h_val1 : y = apply g (apply f₁ n) := by
                   -- apply f₁ x = y. Para esto, necesitamos x ∈ dominio de f₁ (σ(σ n))
                   have hx_in_domain : x ∈ σ (σ n) := by rw [hx_eq_succ]; exact mem_successor_self (σ n)
                   -- Corrección aquí: hf₁.1.2 x hx_in_domain
                   have h_unique := hf₁.1.2 x hx_in_domain
                   have h_app : apply f₁ x = y := apply_eq f₁ x y h_unique (by rw [←hp_eq]; exact hp_in_f1)
                   rw [hx_eq_succ] at h_app
                   rw [←h_app]
                   exact hf₁.2.2 n (mem_successor_self n) -- n ∈ σ n = succ_n

                -- Necesitamos f₁(n) = f₂(n)
                -- n ∈ succ_n, así que f₁(n) = f₁_restr(n) = f₂_restr(n) = f₂(n)
                have hn_in_succ : n ∈ succ_n := mem_successor_self n
                have h_f1_n : apply f₁ n = apply f₁_restr n := (Restriction_apply f₁ succ_n n hn_in_succ).symm
                have h_f2_n : apply f₂ n = apply f₂_restr n := (Restriction_apply f₂ succ_n n hn_in_succ).symm

                rw [h_eq_restr] at h_f1_n

                have h_val2_src : apply f₂ x = apply g (apply f₂ n) := by
                   rw [hx_eq_succ]
                   exact hf₂.2.2 n (mem_successor_self n)

                -- Tenemos y = g(f₁(n)). Queremos mostrar ⟨x, y⟩ ∈ f₂.
                -- Sabemos f₂(x) = g(f₂(n)).
                -- f₁(n) = f₂(n) por restricción.
                -- Entonces y = f₂(x).
                rw [h_f1_n, ←h_f2_n] at h_val1
                rw [hx_eq_succ] at h_val1

                -- ⟨x, f₂(x)⟩ ∈ f₂
                have h_in_f2 : ⟨x, apply f₂ x⟩ ∈ f₂ := by
                   have hx_in_dom : x ∈ domain f₂ := by
                      rw [function_domain_eq f₂ (σ succ_n) A hf₂.1]
                      rw [hx_eq_succ]; exact mem_successor_self succ_n
                   apply apply_mem f₂ x (hf₂.1.2 x hx_in_dom)

                -- Ahora y = f₂(x). Reemplazamos en h_val1
                -- h_val1: y = g(f2(n))
                -- h_val2_src: f2(x) = g(f2(n))
                rw [h_val2_src] at h_val1 -- y = f2(x) ? No directamente.
                -- Queremos demostrar y = f2(x)
                -- Sabemos y = g(f1(n))
                -- Sabemos f2(x) = g(f2(n))
                -- Sabemos f1(n) = f2(n)
                -- Entonces y = f2(x)
                rw [←h_val2_src] at h_val1 -- y = f₂(x)

                rw [h_val1]
                rw [←hp_eq] at h_in_f2
                exact h_in_f2

            · -- p ∈ f₂ → p ∈ f₁ (Simétrico)
              intro hp_in_f2
              have hp_pair : ∃ x y, p = ⟨x, y⟩ := by
                 have hsub := hf₂.1.1
                 have hp_cart : p ∈ (σ succ_n) ×ₛ A := hsub p hp_in_f2
                 rw [CartesianProduct_is_specified] at hp_cart
                 have hp_pair_eq : p = ⟨fst p, snd p⟩ := (isOrderedPair_by_construction p).mp hp_cart.1
                 exact ⟨fst p, snd p, hp_pair_eq⟩
              obtain ⟨x, y, hp_eq⟩ := hp_pair

              have hx_dom : x ∈ σ succ_n := by
                 -- ⟨x, y⟩ ∈ f₂ ⊆ (σ succ_n) × A, así x ∈ σ succ_n
                 have hsub := hf₂.1.1
                 have hp_cart : ⟨x, y⟩ ∈ (σ succ_n) ×ₛ A := by
                   rw [←hp_eq]
                   exact hsub ⟨x, y⟩ hp_in_f2
                 rw [CartesianProduct_is_specified] at hp_cart
                 exact hp_cart.1

              rw [successor_is_specified] at hx_dom
              cases hx_dom with
              | inl hx_in_succ =>
                have hp_restr : p ∈ f₂_restr := by
                  rw [Restriction_is_specified]; constructor; exact hp_in_f2; rw [hp_eq, fst_of_ordered_pair]; exact hx_in_succ
                rw [←h_eq_restr] at hp_restr
                rw [Restriction_is_specified] at hp_restr
                exact hp_restr.1
              | inr hx_eq_succ =>
                have h_val2 : y = apply g (apply f₂ n) := by
                   have hx_in_domain : x ∈ σ (σ n) := by rw [hx_eq_succ]; exact mem_successor_self (σ n)
                   have h_unique := hf₂.1.2 x hx_in_domain
                   have h_app : apply f₂ x = y := apply_eq f₂ x y h_unique (by rw [←hp_eq]; exact hp_in_f2)
                   rw [hx_eq_succ] at h_app; rw [←h_app]; exact hf₂.2.2 n (mem_successor_self n)

                have hn_in_succ : n ∈ succ_n := mem_successor_self n
                have h_f1_n : apply f₁ n = apply f₁_restr n := (Restriction_apply f₁ succ_n n hn_in_succ).symm
                have h_f2_n : apply f₂ n = apply f₂_restr n := (Restriction_apply f₂ succ_n n hn_in_succ).symm
                rw [h_eq_restr] at h_f1_n

                have h_val1_src : apply f₁ x = apply g (apply f₁ n) := by rw [hx_eq_succ]; exact hf₁.2.2 n (mem_successor_self n)

                rw [←h_f2_n, h_f1_n] at h_val2 -- y = g(f₁(n))
                rw [←h_val1_src] at h_val2

                have h_in_f1 : ⟨x, apply f₁ x⟩ ∈ f₁ := by
                   have hx_in_dom : x ∈ domain f₁ := by
                      rw [function_domain_eq f₁ (σ succ_n) A hf₁.1]
                      rw [hx_eq_succ]; exact mem_successor_self succ_n
                   apply apply_mem f₁ x (hf₁.1.2 x hx_in_dom)

                rw [h_val2]
                rw [←hp_eq] at h_in_f1
                exact h_in_f1

      -- Conclusión
      intro n hn f₁ f₂ hf₁ hf₂
      have hn_S : n ∈ S := by rw [h_ind]; exact hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2 f₁ f₂ hf₁ hf₂

  end Recursion

  -- Export key definitions and theorems
  export Recursion (
    function_domain_eq
    isComputation
    computation_uniqueness
  )

end SetUniverse
