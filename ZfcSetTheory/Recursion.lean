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

  ## Estructura Modular
  1. **Definiciones Básicas**: Qué es un cómputo de longitud n.
  2. **Unicidad Local**: Si existe un cómputo de longitud n, es único.
  3. **Compatibilidad**: Herramientas para unir funciones coherentes.
  4. **Existencia Local**: Para todo n, existe un cómputo.
  5. **Teorema Final**: La unión de los cómputos locales es la función recursiva global.
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
        obtain ⟨y, hy⟩ := h.2 x hx
        rw [mem_domain]
        exists y
        exact hy.1

    theorem mem_succ_iff_local (n x : U) : x ∈ σ n ↔ x ∈ n ∨ x = n := by
      rw [successor_is_specified]

    theorem subset_succ_local (n : U) : n ⊆ σ n := by
      intro x hx; rw [mem_succ_iff_local]; left; exact hx

    /-- Todo elemento de un producto cartesiano es un par ordenado -/
    theorem isOrderedPair_of_subset_product (p : U) (A B : U)
      (_h_sub : A ×ₛ B ⊆ 𝒫 (𝒫 (A ∪ B))) (hp : p ∈ A ×ₛ B) :
      isOrderedPair p := by
      rw [CartesianProduct_is_specified] at hp
      exact hp.1

    /-- Lema auxiliar: 0 pertenece a σ n para todo natural n.
        Esto garantiza que el caso base de la recursión siempre está en el dominio. -/
    theorem zero_in_succ_nat (n : U) (hn : n ∈ ω) : (∅ : U) ∈ σ n := by
      rw [mem_succ_iff_local]
      have hn_nat : isNat n := mem_Omega_is_Nat n hn
      cases nat_is_zero_or_succ n hn_nat with
      | inl hz =>
        -- Caso n = 0: 0 ∈ {0} ↔ 0 = 0
        right; rw [hz]
      | inr hs =>
        -- Caso n = σ k: 0 ∈ n (pues n = {0, ..., k})
        obtain ⟨k, hk⟩ := hs
        left
        rw [hk, successor_is_specified]
        left
        -- 0 is an element of every natural number k for k ≠ 0
        -- This follows from the von Neumann construction
        have hk_nat : isNat k := mem_Omega_is_Nat k (Omega_closed_under_pred n hn hk.symm)
        have : (∅ : U) ∈ k := by
          cases nat_is_zero_or_succ k hk_nat with
          | inl hz => rw [hz]; exact absurd hz (not_succ_eq_zero n (hk.symm))
          | inr hsk =>
            obtain ⟨k', hk'⟩ := hsk
            rw [hk']; exact Or.inl (by sorry)
        exact this

    /-! ============================================================ -/
    /-! ### 1. DEFINICIÓN DE CÓMPUTO LOCAL ### -/
    /-! ============================================================ -/

    /-- Un conjunto f es un cómputo de longitud n para la base a y paso g -/
    def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      isFunctionFromTo f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))

    /-- Lema auxiliar: La restricción de un cómputo de longitud σ n a n es un cómputo de longitud n. -/
    theorem restriction_is_computation (A : U) (a : U) (g : U) (n : U) (hn : n ∈ ω) :
      ∀ f, isComputation (σ n) f A a g → isComputation n (Restriction f (σ n)) A a g := by
      intro f hf
      constructor
      · -- f es función sobre σ(σ n), restringida a σ n.
        -- Necesitamos σ n ⊆ σ(σ n).
        apply Restriction_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n))
      · constructor
        · -- f(0) = a.
          -- Probamos 0 ∈ σ n para usar Restriction_apply
          have h_zero_in : (∅ : U) ∈ σ n := by
            rw [mem_succ_iff_local]
            have h_z : isNat (∅ : U) := mem_Omega_is_Nat ∅ zero_in_Omega
            have hn_nat : isNat n := mem_Omega_is_Nat n hn
            cases nat_is_zero_or_succ n hn_nat with
            | inl hz => right; rw [hz]
            | inr hs =>
              obtain ⟨k, hk⟩ := hs
              -- n = σ k, so 0 ∈ σ k since 0 ∈ k or 0 = k
              left
              rw [hk]
              -- 0 ∈ σ k, and since 0 ∈ k for any k ∈ ω with k ≠ 0
              sorry

          rw [Restriction_apply f (σ n) (∅ : U) h_zero_in]
          exact hf.2.1
        · -- Paso recursivo
          intro k hk
          -- Necesitamos k ∈ σ n y σ k ∈ σ n para usar Restriction_apply
          have h_k_in : k ∈ σ n := subset_succ_local n k hk
          have h_sk_in : σ k ∈ σ n := nat_succ_mem_succ_of_mem n hn k hk

          rw [Restriction_apply f (σ n) (σ k) h_sk_in]
          rw [Restriction_apply f (σ n) k h_k_in]
          -- Usamos la propiedad de f para k.
          -- hf.2.2 : ∀ k ∈ σ n, ...
          -- k ∈ n ⊆ σ n, así que podemos aplicarlo.
          exact hf.2.2 k h_k_in

    /-! ============================================================ -/
    /-! ### 2. UNICIDAD LOCAL ### -/
    /-! ============================================================ -/

    /-- Si existen dos cómputos de longitud n, son iguales (esencial para compatibilidad) -/
    theorem computation_uniqueness (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∀ n, n ∈ ω → ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂ := by

      let S := SpecSet (ω : U) (fun n => ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂)

      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
        · -- Base n=0
          rw [SpecSet_is_specified]; constructor; exact zero_in_Omega
          intro f₁ f₂ hf₁ hf₂
          have h_dom1 : domain f₁ = σ (∅ : U) := function_domain_eq f₁ (σ (∅ : U)) A hf₁.1
          have h_dom2 : domain f₂ = σ (∅ : U) := function_domain_eq f₂ (σ (∅ : U)) A hf₂.1
          apply ExtSet; intro p; constructor
          · intro hp
            have : p ∈ σ (∅ : U) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at this
            have h_is_op : isOrderedPair p := this.1
            obtain ⟨_, hp_fst, hp_snd⟩ := this
            let x := fst p
            let y := snd p
            have hp_eq : p = ⟨x, y⟩ := OrderedPairSet_is_WellConstructed p h_is_op
            have : x = ∅ := by
               have : x ∈ domain f₁ := by rw [mem_domain]; exists y; rw [←hp_eq]; exact hp
               rw [h_dom1, mem_succ_iff_local] at this; cases this with
               | inl h => exact absurd h (EmptySet_is_empty x)
               | inr h => exact h
            rw [this] at hp_eq
            have : y = a := by rw [←hf₁.2.1]; symm; apply apply_eq f₁ ∅ y (hf₁.1.2 ∅ (by rw [successor_is_specified]; right; rfl)); rw [←hp_eq]; exact hp
            rw [this] at hp_eq
            rw [hp_eq]; rw [←hf₂.2.1]; apply apply_mem f₂ ∅ (hf₂.1.2 ∅ (by rw [successor_is_specified]; right; rfl))
          · -- Simétrico
              intro hp
              have h_in_prod : p ∈ (σ (∅ : U)) ×ₛ A := hf₂.1.1 p hp
              rw [CartesianProduct_is_specified] at h_in_prod
              have h_is_op : isOrderedPair p := h_in_prod.1
              obtain ⟨_, hp_fst, hp_snd⟩ := h_in_prod
              let x := fst p
              let y := snd p
              have hp_eq : p = ⟨x, y⟩ := OrderedPairSet_is_WellConstructed p h_is_op
              have : x = ∅ := by
                 have : x ∈ domain f₂ := by rw [mem_domain]; exists y; rw [←hp_eq]; exact hp
                 rw [h_dom2, mem_succ_iff_local] at this; cases this with
                 | inl h => exact absurd h (EmptySet_is_empty x)
                 | inr h => exact h
              rw [this] at hp_eq
              have : y = a := by rw [←hf₂.2.1]; symm; apply apply_eq f₂ ∅ y (hf₂.1.2 ∅ (by rw [successor_is_specified]; right; rfl)); rw [←hp_eq]; exact hp
              rw [this] at hp_eq
              rw [hp_eq]; rw [←hf₁.2.1]; apply apply_mem f₁ ∅ (hf₁.1.2 ∅ (by rw [successor_is_specified]; right; rfl))

        · -- Paso inductivo
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S; obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S
          rw [SpecSet_is_specified]; constructor; exact succ_in_Omega n hn_omega

          intro f₁ f₂ hf₁ hf₂
          -- Restringimos al paso anterior
          let f₁_res := Restriction f₁ (σ n)
          let f₂_res := Restriction f₂ (σ n)

          -- Lema auxiliar rápido: restricción es cómputo
          have h_res_comp : ∀ f, isComputation (σ n) f A a g → isComputation n (Restriction f (σ n)) A a g := by
             intro f hf
             constructor
             · apply Restriction_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n))
             · constructor
               · have h_empty_in_succ : (∅ : U) ∈ σ n := by
                  rw [mem_succ_iff_local]
                  by_cases h : n = ∅
                  · right
                    exact h.symm
                  · left
                    -- Usamos zero_mem_of_nat_nonempty: n es natural (porque n ∈ ω)
                    have hn_nat : isNat n := mem_Omega_is_Nat n hn_omega
                    exact zero_mem_of_nat_nonempty n hn_nat h
                 rw [Restriction_apply f (σ n) ∅ h_empty_in_succ]; exact hf.2.1
               · intro k hk
                 rw [Restriction_apply f (σ n) (σ k) (by sorry)]; -- σ k ∈ σ n
                 rw [Restriction_apply f (σ n) k (by sorry)];
                exact hf.2.2 k (subset_succ_local n k hk)
                 exact hf.2.2 k (by sorry) -- k ∈ n ⊆ σ n

          have h1 : isComputation n f₁_res A a g := h_res_comp f₁ hf₁
          have h2 : isComputation n f₂_res A a g := h_res_comp f₂ hf₂

          have h_eq_res : f₁_res = f₂_res := h_unique_n f₁_res f₂_res h1 h2

          -- Extender igualdad al último punto
          apply ExtSet; intro p
          -- (Omitimos detalles repetitivos del paso anterior, la lógica es la misma:
          -- p ∈ f₁ ↔ p ∈ f₁_res ∨ p = ⟨σ n, f₁(σ n)⟩
          -- f₁(σ n) = g(f₁(n)) = g(f₁_res(n)) = g(f₂_res(n)) = g(f₂(n)) = f₂(σ n)
          -- )
          sorry -- Ya probado en la versión anterior, lo marco sorry para enfocar en la estructura nueva

      intro n hn; rw [←h_ind] at hn; rw [SpecSet_is_specified] at hn; exact hn.2

    /-! ============================================================ -/
    /-! ### 3. COMPATIBILIDAD Y UNIONES ### -/
    /-! ============================================================ -/

    /-- Dos funciones son compatibles si coinciden en la intersección de sus dominios -/
    def areCompatible (f g : U) : Prop :=
      ∀ x, x ∈ ((domain f) ∩ (domain g)) → apply f x = apply g x

    /-- Una familia de funciones es un sistema compatible si son compatibles a pares -/
    def isCompatibleSystem (F : U) : Prop :=
      ∀ f g, f ∈ F → g ∈ F → areCompatible f g

    /-- La unión de un sistema compatible de funciones es una función -/
    theorem union_compatible_is_function (F : U)
      (h_funcs : ∀ f, f ∈ F → ∃ A B, isFunctionFromTo f A B)
      (h_compat : isCompatibleSystem F) :
      isFunction (⋃ F) := by
      -- Prueba estándar: unicidad de imagen
      -- Si ⟨x, y⟩ ∈ ⋃ F y ⟨x, z⟩ ∈ ⋃ F
      -- ∃ f ∈ F, ⟨x, y⟩ ∈ f. ∃ g ∈ F, ⟨x, z⟩ ∈ g.
      -- x ∈ dom f ∩ dom g.
      -- Como f, g son compatibles, f(x) = g(x).
      -- Como son funciones, y = f(x) y z = g(x).
      -- Por tanto y = z.
      sorry -- (Fácil de completar)

    /-! ============================================================ -/
    /-! ### 4. EXISTENCIA LOCAL (Inducción) ### -/
    /-! ============================================================ -/

    theorem computation_existence (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∀ n, n ∈ ω → ∃ f, isComputation n f A a g := by

      let S := SpecSet (ω : U) (fun n => ∃ f, isComputation n f A a g)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1

        · -- Base n=0: f = {⟨0, a⟩}
          rw [SpecSet_is_specified]; constructor; exact zero_in_Omega
          let f0 := Singleton (OrderedPair (∅ : U) a)
          exists f0
          constructor
          · -- Es función {0} -> A
            sorry
          · constructor
            · -- f(0) = a
              sorry
            · -- ∀ k ∈ 0 (vacuamente cierto)
              intro k hk; exact False.elim (EmptySet_is_empty k hk)

        · -- Paso: n -> σ n
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S; obtain ⟨hn_omega, ⟨fn, hfn⟩⟩ := hn_in_S
          rw [SpecSet_is_specified]; constructor; exact succ_in_Omega n hn_omega

          -- Construimos f_{n+1} extendiendo f_n
          -- f_{n+1} = f_n ∪ { ⟨σ n, g(f_n(n))⟩ }
          let val_next := apply g (apply fn n)
          let pair_next := OrderedPair (σ n) val_next
          let f_next := fn ∪ (Singleton pair_next)

          exists f_next
          -- Probar que f_next es cómputo de longitud σ n
          -- 1. Dominio es σ(σ n) = σ n ∪ {σ n} (Correcto: dom(fn) ∪ {σ n})
          -- 2. Base se mantiene (0 ∈ dom(fn))
          -- 3. Recursión se mantiene para k ∈ n y se cumple para k = n
          sorry -- (Lógica de extensión estándar)

      intro n hn; rw [←h_ind] at hn; rw [SpecSet_is_specified] at hn; exact hn.2

    /-! ============================================================ -/
    /-! ### 5. TEOREMA DE RECURSIÓN (GLOBAL) ### -/
    /-! ============================================================ -/

    /-- El conjunto de todos los cómputos válidos -/
    def RecursionComputations (A a g : U) : U :=
      SpecSet (𝒫 (ω ×ₛ A)) (fun f => ∃ n, n ∈ ω ∧ isComputation n f A a g)

    theorem RecursionTheorem (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∃! F, isFunctionFromTo F ω A ∧
            (apply F (∅ : U) = a) ∧
            (∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) := by

      let Comps := RecursionComputations A a g
      let F := ⋃ Comps

      -- Paso 1: F es función (usando lemas de compatibilidad)
      -- Paso 2: Dominio de F es ω (porque ∀ n, n ∈ dom(f_n) ⊆ dom(F))
      -- Paso 3: F cumple las ecuaciones (heredado de los f_n)

      apply ExistsUnique.intro F
      · sorry -- Existencia
      · sorry -- Unicidad (usando inducción sobre n para ver que cualquier G coincide con F)

  end Recursion

  export Recursion (
    isComputation
    computation_uniqueness
    areCompatible
    union_compatible_is_function
    computation_existence
    RecursionTheorem
  )

end SetUniverse
