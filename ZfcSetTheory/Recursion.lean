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

    /-- Lema auxiliar local: x ∈ σ n ↔ x ∈ n ∨ x = n -/
    theorem mem_succ_iff_local (n x : U) : x ∈ (σ n) ↔ x ∈ n ∨ x = n := by
      rw [successor_is_specified]

    /-- Lema auxiliar local: n ⊆ σ n -/
    theorem subset_succ_local (n : U) : n ⊆ σ n := by
      intro x hx
      rw [mem_succ_iff_local]
      left
      exact hx

    /-- Lema auxiliar: Si k ∈ n, entonces σ k ∈ σ n. -/
    theorem nat_succ_mem_succ_of_mem (n : U) (hn : n ∈ ω) :
      ∀ k, k ∈ n → σ k ∈ σ n := by
      -- Induction on n
      let S := SpecSet (ω : U) (fun n => ∀ k, k ∈ n → σ k ∈ σ n)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
        · -- Base 0
          rw [SpecSet_is_specified]
          constructor; exact zero_in_Omega
          intro k hk; exact False.elim (EmptySet_is_empty k hk)
        · -- Step m -> σ m
          intro m hm_in_S
          rw [SpecSet_is_specified] at hm_in_S ⊢
          obtain ⟨hm_omega, h_hyp⟩ := hm_in_S
          constructor; exact succ_in_Omega m hm_omega
          intro k hk
          rw [mem_succ_iff_local] at hk
          cases hk with
          | inl h_in_m =>
            -- k ∈ m. σ k ∈ σ m by IH. σ m ⊆ σ (σ m)
            have h_sk_sm : σ k ∈ σ m := h_hyp k h_in_m
            exact subset_succ_local (σ m) (σ k) h_sk_sm
          | inr h_eq_m =>
            -- k = m. σ k = σ m ∈ σ (σ m)
            rw [h_eq_m]
            exact mem_successor_self (σ m)
      have hn_S : n ∈ S := by rw [h_ind]; exact hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2

    /-! ============================================================ -/
    /-! ### 1. DEFINICIÓN DE CÓMPUTO DE LONGITUD n ### -/
    /-! ============================================================ -/

    def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      isFunctionFromTo f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))

    /-! ============================================================ -/
    /-! ### 2. UNICIDAD DEL CÓMPUTO ### -/
    /-! ============================================================ -/

    theorem computation_uniqueness (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∀ n, n ∈ ω → ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂ := by

      let S := SpecSet (ω : U) (fun n => ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂)

      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1

        · -- CASO BASE: n = 0
          rw [SpecSet_is_specified]
          constructor; exact zero_in_Omega
          intro f₁ f₂ hf₁ hf₂
          obtain ⟨hfunc1, hval1, _⟩ := hf₁
          obtain ⟨hfunc2, hval2, _⟩ := hf₂

          have h_dom1 : domain f₁ = σ (∅ : U) := function_domain_eq f₁ (σ (∅ : U)) A hfunc1
          have h_dom2 : domain f₂ = σ (∅ : U) := function_domain_eq f₂ (σ (∅ : U)) A hfunc2

          apply ExtSet
          intro p
          constructor
          · intro hp
            have hsub := hfunc1.1
            have hp_cart : p ∈ (σ (∅ : U)) ×ₛ A := hsub p hp
            rw [CartesianProduct_is_specified] at hp_cart
            obtain ⟨h_is_pair, -⟩ := hp_cart
            obtain ⟨x, y, hp_eq⟩ := h_is_pair

            have hx_dom : x ∈ domain f₁ := by
              rw [mem_domain]; exists y; rw [←hp_eq]; exact hp

            rw [h_dom1, mem_succ_iff_local] at hx_dom
            have hx_eq_zero : x = ∅ := by
              cases hx_dom with
              | inl h => exact False.elim (EmptySet_is_empty x h)
              | inr h => exact h
            rw [hx_eq_zero] at hp_eq

            have hy_val : y = a := by
              rw [←hval1]
              have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by rw [mem_succ_iff_local]; right; rfl
              symm
              apply apply_eq f₁ (∅ : U) y (hfunc1.2 ∅ h_zero_mem)
              rw [←hp_eq]; exact hp

            rw [hy_val] at hp_eq
            have h_in_f2 : ⟨(∅ : U), a⟩ ∈ f₂ := by
              rw [←hval2]
              have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by rw [mem_succ_iff_local]; right; rfl
              apply apply_mem f₂ (∅ : U) (hfunc2.2 ∅ h_zero_mem)

            rw [←hp_eq] at h_in_f2
            exact h_in_f2

          · -- Simétrico
            intro hp
            have hsub := hfunc2.1
            have hp_cart : p ∈ (σ (∅ : U)) ×ₛ A := hsub p hp
            rw [CartesianProduct_is_specified] at hp_cart
            obtain ⟨h_is_pair, -⟩ := hp_cart
            obtain ⟨x, y, hp_eq⟩ := h_is_pair

            have hx_dom : x ∈ domain f₂ := by rw [mem_domain]; exists y; rw [←hp_eq]; exact hp
            rw [h_dom2, mem_succ_iff_local] at hx_dom
            have hx_eq_zero : x = ∅ := by
              cases hx_dom with | inl h => exact False.elim (EmptySet_is_empty x h) | inr h => exact h
            rw [hx_eq_zero] at hp_eq

            have hy_val : y = a := by
              rw [←hval2]
              have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by rw [mem_succ_iff_local]; right; rfl
              symm; apply apply_eq f₂ (∅ : U) y (hfunc2.2 ∅ h_zero_mem); rw [←hp_eq]; exact hp

            rw [hy_val] at hp_eq
            have h_in_f1 : ⟨(∅ : U), a⟩ ∈ f₁ := by
              rw [←hval1]
              have h_zero_mem : (∅ : U) ∈ σ (∅ : U) := by rw [mem_succ_iff_local]; right; rfl
              apply apply_mem f₁ (∅ : U) (hfunc1.2 ∅ h_zero_mem)

            rw [←hp_eq] at h_in_f1
            exact h_in_f1

        · -- PASO INDUCTIVO
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S

          rw [SpecSet_is_specified]
          constructor; exact succ_in_Omega n hn_omega
          intro f₁ f₂ hf₁ hf₂

          let succ_n := σ n
          let f₁_restr := Restriction f₁ succ_n
          let f₂_restr := Restriction f₂ succ_n

          have hn_nat_prop : isNat n := mem_Omega_is_Nat n hn_omega
          have h_succ_n_in_omega : succ_n ∈ ω := succ_in_Omega n hn_omega
          have h_succ_n_nat_prop : isNat succ_n := mem_Omega_is_Nat succ_n h_succ_n_in_omega
          have h_subset : succ_n ⊆ σ succ_n := subset_succ_local succ_n

          -- Probar que restricciones son cómputos
          have h_f1_is_comp : isComputation n f₁_restr A a g := by
            constructor
            · apply Restriction_is_function f₁ (σ succ_n) A succ_n hf₁.1 h_subset
            · constructor
              · -- f(0) = a. Hay que probar 0 ∈ σ n
                have h_zero_in : (∅ : U) ∈ succ_n := by
                  have h_z : isNat (∅ : U) := mem_Omega_is_Nat ∅ zero_in_Omega
                  cases nat_is_zero_or_succ n hn_nat_prop with
                  | inl hz => rw [hz]; rw [one_eq, Singleton_is_specified]; rfl
                  | inr hs =>
                    obtain ⟨k, hk⟩ := hs
                    have h_trich := nat_trichotomy (∅ : U) succ_n h_z h_succ_n_nat_prop
                    cases h_trich with
                    | inl hIn => exact hIn
                    | inr hOr =>
                      cases hOr with
                      | inl hEq =>
                         have hne := successor_nonempty n
                         rw [←hEq] at hne
                         exact False.elim (EmptySet_is_empty ∅ hne)
                      | inr hGt =>
                         exact False.elim (EmptySet_is_empty (σ n) hGt)

                rw [Restriction_apply f₁ succ_n (∅ : U) h_zero_in]
                exact hf₁.2.1
              · intro k hk
                -- Necesitamos σ k ∈ succ_n y k ∈ succ_n
                have h_succ_k_in : σ k ∈ succ_n := nat_succ_mem_succ_of_mem n hn_omega k hk
                have h_k_in : k ∈ succ_n := subset_succ_local n k hk
                rw [Restriction_apply f₁ succ_n (σ k) h_succ_k_in]
                rw [Restriction_apply f₁ succ_n k h_k_in]
                -- Aplicar hipótesis recursiva de f₁
                have h_k_in_dom_orig : k ∈ σ n := h_k_in
                exact hf₁.2.2 k h_k_in_dom_orig

          have h_f2_is_comp : isComputation n f₂_restr A a g := by
            constructor
            · apply Restriction_is_function f₂ (σ succ_n) A succ_n hf₂.1 h_subset
            · constructor
              · have h_zero_in : (∅ : U) ∈ succ_n := by
                   have h_z : isNat (∅ : U) := mem_Omega_is_Nat ∅ zero_in_Omega
                   cases nat_is_zero_or_succ n hn_nat_prop with
                   | inl hz => rw [hz]; rw [one_eq, Singleton_is_specified]; rfl
                   | inr hs =>
                     obtain ⟨k, hk⟩ := hs
                     have h_trich := nat_trichotomy (∅ : U) succ_n h_z h_succ_n_nat_prop
                     cases h_trich with
                     | inl hIn => exact hIn
                     | inr hOr =>
                        cases hOr with
                        | inl hEq => have hne := successor_nonempty n; rw [←hEq] at hne; exact False.elim (EmptySet_is_empty ∅ hne)
                        | inr hGt => exact False.elim (EmptySet_is_empty (σ n) hGt)
                rw [Restriction_apply f₂ succ_n (∅ : U) h_zero_in]
                exact hf₂.2.1
              · intro k hk
                have h_succ_k_in : σ k ∈ succ_n := nat_succ_mem_succ_of_mem n hn_omega k hk
                have h_k_in : k ∈ succ_n := subset_succ_local n k hk
                rw [Restriction_apply f₂ succ_n (σ k) h_succ_k_in]
                rw [Restriction_apply f₂ succ_n k h_k_in]
                have h_k_in_dom_orig : k ∈ σ n := h_k_in
                exact hf₂.2.2 k h_k_in_dom_orig

          -- HI: f₁_restr = f₂_restr
          have h_eq_restr : f₁_restr = f₂_restr := h_unique_n f₁_restr f₂_restr h_f1_is_comp h_f2_is_comp

          apply ExtSet
          intro p
          constructor
          · intro hp_in_f1
            have hsub := hf₁.1.1
            have hp_cart : p ∈ (σ succ_n) ×ₛ A := hsub p hp_in_f1
            rw [CartesianProduct_is_specified] at hp_cart
            obtain ⟨h_is_pair, -⟩ := hp_cart
            obtain ⟨x, y, hp_eq⟩ := h_is_pair

            have hx_dom : x ∈ σ succ_n := by
               have hp_cart2 : ⟨x, y⟩ ∈ (σ succ_n) ×ₛ A := by rw [←hp_eq]; exact hsub ⟨x, y⟩ hp_in_f1
               rw [CartesianProduct_is_specified] at hp_cart2
               exact hp_cart2.1

            rw [mem_succ_iff_local] at hx_dom
            cases hx_dom with
            | inl hx_in_succ =>
              have hp_restr : p ∈ f₁_restr := by
                rw [Restriction_is_specified]; constructor; exact hp_in_f1; rw [hp_eq, fst_of_ordered_pair]; exact hx_in_succ
              rw [h_eq_restr] at hp_restr
              rw [Restriction_is_specified] at hp_restr
              exact hp_restr.1
            | inr hx_eq_succ =>
              -- x = σ n
              have h_val1 : y = apply g (apply f₁ n) := by
                 have hx_in_domain : x ∈ σ (σ n) := by rw [hx_eq_succ]; exact mem_successor_self (σ n)
                 have h_unique := hf₁.1.2 x hx_in_domain
                 have h_y_val : f₁⦅x⦆ = y := apply_eq f₁ x y h_unique (by rw [←hp_eq]; exact hp_in_f1)
                 rw [←h_y_val, hx_eq_succ]
                 exact hf₁.2.2 n (mem_successor_self n)

              -- n ∈ succ_n
              have hn_in_succ : n ∈ succ_n := mem_successor_self n
              have h_f1_n : apply f₁ n = apply f₁_restr n := (Restriction_apply f₁ succ_n n hn_in_succ).symm
              have h_f2_n : apply f₂ n = apply f₂_restr n := (Restriction_apply f₂ succ_n n hn_in_succ).symm

              rw [h_eq_restr] at h_f1_n
              have h_val2_src : apply f₂ x = apply g (apply f₂ n) := by
                 rw [hx_eq_succ]; exact hf₂.2.2 n (mem_successor_self n)

              rw [h_f1_n, ←h_f2_n] at h_val1
              rw [←h_val2_src] at h_val1

              have h_in_f2 : ⟨x, apply f₂ x⟩ ∈ f₂ := by
                 have hx_in_dom : x ∈ domain f₂ := by
                    rw [function_domain_eq f₂ (σ succ_n) A hf₂.1]
                    rw [hx_eq_succ]; exact mem_successor_self succ_n
                 apply apply_mem f₂ x (hf₂.1.2 x hx_in_dom)

              rw [h_val1]
              rw [←hp_eq] at h_in_f2
              exact h_in_f2

          · -- Simétrico
            intro hp_in_f2
            have hsub := hf₂.1.1
            have hp_cart : p ∈ (σ succ_n) ×ₛ A := hsub p hp_in_f2
            rw [CartesianProduct_is_specified] at hp_cart
            obtain ⟨h_is_pair, -⟩ := hp_cart
            obtain ⟨x, y, hp_eq⟩ := h_is_pair

            have hx_dom : x ∈ σ succ_n := by
               have hp_cart2 : ⟨x, y⟩ ∈ (σ succ_n) ×ₛ A := by rw [←hp_eq]; exact hsub ⟨x, y⟩ hp_in_f2
               rw [CartesianProduct_is_specified] at hp_cart2
               exact hp_cart2.1

            rw [mem_succ_iff_local] at hx_dom
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
                 have h_y_val : f₂⦅x⦆ = y := apply_eq f₂ x y h_unique (by rw [←hp_eq]; exact hp_in_f2)
                 rw [←h_y_val, hx_eq_succ]
                 exact hf₂.2.2 n (mem_successor_self n)

              have hn_in_succ : n ∈ succ_n := mem_successor_self n
              have h_f1_n : apply f₁ n = apply f₁_restr n := (Restriction_apply f₁ succ_n n hn_in_succ).symm
              have h_f2_n : apply f₂ n = apply f₂_restr n := (Restriction_apply f₂ succ_n n hn_in_succ).symm
              rw [h_eq_restr] at h_f1_n

              have h_val1_src : apply f₁ x = apply g (apply f₁ n) := by rw [hx_eq_succ]; exact hf₁.2.2 n (mem_successor_self n)

              rw [←h_f2_n, h_f1_n] at h_val2
              rw [←h_val1_src] at h_val2

              have h_in_f1 : ⟨x, apply f₁ x⟩ ∈ f₁ := by
                 have hx_in_dom : x ∈ domain f₁ := by
                    rw [function_domain_eq f₁ (σ succ_n) A hf₁.1]
                    rw [hx_eq_succ]; exact mem_successor_self succ_n
                 apply apply_mem f₁ x (hf₁.1.2 x hx_in_dom)

              rw [h_val2]
              rw [←hp_eq] at h_in_f1
              exact h_in_f1

      intro n hn f₁ f₂ hf₁ hf₂
      have hn_S : n ∈ S := by rw [h_ind]; exact hn
      rw [SpecSet_is_specified] at hn_S
      exact hn_S.2 f₁ f₂ hf₁ hf₂

  end Recursion

  export Recursion (
    function_domain_eq
    isComputation
    computation_uniqueness
  )

end SetUniverse
