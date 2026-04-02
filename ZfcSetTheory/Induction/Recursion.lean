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
import ZfcSetTheory.Core.Prelim
import ZfcSetTheory.Axiom.Extension
import ZfcSetTheory.Axiom.Existence
import ZfcSetTheory.Axiom.Specification
import ZfcSetTheory.Axiom.Pairing
import ZfcSetTheory.Axiom.Union
import ZfcSetTheory.Axiom.PowerSet
import ZfcSetTheory.SetOps.OrderedPair
import ZfcSetTheory.SetOps.CartesianProduct
import ZfcSetTheory.SetOps.Relations
import ZfcSetTheory.SetOps.Functions
import ZfcSetTheory.Nat.Basic
import ZfcSetTheory.Axiom.Infinity

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.Relations
  open ZFC.SetOps.CartesianProduct

  universe u
  variable {U : Type u}

  namespace Induction.Recursion

    /-! ============================================================ -/
    /-! ### 0. LEMAS AUXILIARES ### -/
    /-! ============================================================ -/

    theorem function_domain_eq (f A B : U) (h : IsFunction f A B) : domain f = A := by
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
      rw [mem_succ_iff]

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
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      by_cases h : n = ∅
      · right; rw [h]
      · left; exact zero_mem_of_nat_nonempty n hn_nat h

    /-- Si k ∈ n (ambos naturales), entonces σ k ∈ σ n -/
    theorem succ_mem_succ_of_mem (k n : U) (hk_nat : IsNat k) (hn_nat : IsNat n)
        (hk : k ∈ n) : σ k ∈ σ n := by
      rw [mem_succ_iff_local]
      exact nat_subset_mem_or_eq (σ k) n (isNat_succ k hk_nat) hn_nat
        (no_nat_between k n hk_nat hn_nat hk)

    /-! ============================================================ -/
    /-! ### 1. DEFINICIÓN DE CÓMPUTO LOCAL ### -/
    /-! ============================================================ -/

    /-- Un conjunto f es un cómputo de longitud n para la base a y paso g -/
    def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      IsFunction f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))

    /-- Lema auxiliar: La restricción de un cómputo de longitud σ n a n es un cómputo de longitud n. -/
    theorem restriction_is_computation (A : U) (a : U) (g : U) (n : U) (hn : n ∈ ω) :
      ∀ f, isComputation (σ n) f A a g → isComputation n (restrict f (σ n)) A a g := by
      intro f hf
      constructor
      · -- f es función sobre σ(σ n), restringida a σ n.
        -- Necesitamos σ n ⊆ σ(σ n).
        apply restrict_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n))
      · constructor
        · -- f(0) = a.
          have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn
          rw [restrict_apply f (σ n) (∅ : U) h_zero_in]
          exact hf.2.1
        · -- Paso recursivo
          intro k hk
          -- Necesitamos k ∈ σ n y σ k ∈ σ n para usar restrict_apply
          have hn_nat : IsNat n := mem_Omega_is_Nat n hn
          have hk_nat : IsNat k := nat_element_is_nat n k hn_nat hk
          have h_k_in : k ∈ σ n := subset_succ_local n k hk
          have h_sk_in : σ k ∈ σ n := succ_mem_succ_of_mem k n hk_nat hn_nat hk

          rw [restrict_apply f (σ n) (σ k) h_sk_in]
          rw [restrict_apply f (σ n) k h_k_in]
          -- Usamos la propiedad de f para k.
          -- hf.2.2 : ∀ k ∈ σ n, ...
          -- k ∈ n ⊆ σ n, así que podemos aplicarlo.
          exact hf.2.2 k h_k_in

    /-! ============================================================ -/
    /-! ### 2. UNICIDAD LOCAL ### -/
    /-! ============================================================ -/

    /-- Si existen dos cómputos de longitud n, son iguales (esencial para compatibilidad) -/
    theorem computation_uniqueness (A : U) (a : U) (g : U) :
      ∀ n, n ∈ ω → ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂
        := by

      let S := sep (ω : U) (fun n => ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂)

      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base n=0
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
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
            have : y = a := by rw [←hf₁.2.1]; symm; apply apply_eq f₁ ∅ y (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl)); rw [←hp_eq]; exact hp
            rw [this] at hp_eq
            rw [hp_eq]; rw [←hf₂.2.1]; apply apply_mem f₂ ∅ (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
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
              have : y = a := by rw [←hf₂.2.1]; symm; apply apply_eq f₂ ∅ y (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl)); rw [←hp_eq]; exact hp
              rw [this] at hp_eq
              rw [hp_eq]; rw [←hf₁.2.1]; apply apply_mem f₁ ∅ (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))

        · -- Paso inductivo
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S; obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega

          intro f₁ f₂ hf₁ hf₂
          -- Restringimos al paso anterior
          let f₁_res := restrict f₁ (σ n)
          let f₂_res := restrict f₂ (σ n)

          -- Restricción es cómputo (ya demostrado)
          have h_res_comp := restriction_is_computation A a g n hn_omega

          have h1 : isComputation n f₁_res A a g := h_res_comp f₁ hf₁
          have h2 : isComputation n f₂_res A a g := h_res_comp f₂ hf₂

          have h_eq_res : f₁_res = f₂_res := h_unique_n f₁_res f₂_res h1 h2

          -- Extender igualdad al último punto
          apply ExtSet; intro p
          -- Clave: f₁(σ n) = g(f₁(n)) = g(f₁_res(n)) = g(f₂_res(n)) = g(f₂(n)) = f₂(σ n)
          have h_apply_eq : apply f₁ (σ n) = apply f₂ (σ n) :=
            calc apply f₁ (σ n)
                = apply g (apply f₁ n)       := hf₁.2.2 n (mem_succ_self n)
              _ = apply g (apply f₁_res n)   := by rw [← restrict_apply f₁ (σ n) n (mem_succ_self n)]
              _ = apply g (apply f₂_res n)   := by rw [h_eq_res]
              _ = apply g (apply f₂ n)       := by rw [restrict_apply f₂ (σ n) n (mem_succ_self n)]
              _ = apply f₂ (σ n)             := (hf₂.2.2 n (mem_succ_self n)).symm
          constructor
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_in_f1res : p ∈ f₁_res :=
                (mem_restrict_iff f₁ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_in_f2res : p ∈ f₂_res := h_eq_res ▸ hp_in_f1res
              exact restrict_subset f₂ (σ n) p hp_in_f2res
            | inr h_eq_sn =>
              have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
              have h_uniq1 : ∃! y, ⟨fst p, y⟩ ∈ f₁ :=
                hf₁.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn)
              have h_snd_eq : snd p = apply f₁ (fst p) :=
                (apply_eq f₁ (fst p) (snd p) h_uniq1 (by rw [← hp_eq]; exact hp)).symm
              rw [hp_eq, h_snd_eq, h_eq_sn, h_apply_eq]
              exact apply_mem f₂ (σ n) (hf₂.1.2 (σ n) (mem_succ_self (σ n)))
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_in_f2res : p ∈ f₂_res :=
                (mem_restrict_iff f₂ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_in_f1res : p ∈ f₁_res := h_eq_res.symm ▸ hp_in_f2res
              exact restrict_subset f₁ (σ n) p hp_in_f1res
            | inr h_eq_sn =>
              have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
              have h_uniq2 : ∃! y, ⟨fst p, y⟩ ∈ f₂ :=
                hf₂.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn)
              have h_snd_eq : snd p = apply f₂ (fst p) :=
                (apply_eq f₂ (fst p) (snd p) h_uniq2 (by rw [← hp_eq]; exact hp)).symm
              rw [hp_eq, h_snd_eq, h_eq_sn, ← h_apply_eq]
              exact apply_mem f₁ (σ n) (hf₁.1.2 (σ n) (mem_succ_self (σ n)))

      intro n hn; rw [←h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    /-! ============================================================ -/
    /-! ### 3. COMPATIBILIDAD Y UNIONES ### -/
    /-! ============================================================ -/

    /-- Dos funciones son compatibles si coinciden en la intersección de sus dominios -/
    def areCompatible (f g : U) : Prop :=
      ∀ x, x ∈ ((domain f) ∩ (domain g)) → apply f x = apply g x

    /-- Una familia de funciones es un sistema compatible si son compatibles a pares -/
    def isCompatibleSystem (F : U) : Prop :=
      ∀ f g, f ∈ F → g ∈ F → areCompatible f g

    /-- La unión de un sistema compatible de funciones es monovaluada -/
    theorem union_compatible_is_function (F : U)
      (h_funcs : ∀ f, f ∈ F → ∃ A B, IsFunction f A B)
      (h_compat : isCompatibleSystem F) :
      IsSingleValued (⋃ F) := by
      intro x y₁ y₂ hy₁ hy₂
      rw [mem_sUnion_iff] at hy₁ hy₂
      obtain ⟨f, hf_in_F, hpair1⟩ := hy₁
      obtain ⟨g, hg_in_F, hpair2⟩ := hy₂
      obtain ⟨A_f, B_f, hf_func⟩ := h_funcs f hf_in_F
      obtain ⟨A_g, B_g, hg_func⟩ := h_funcs g hg_in_F
      -- x ∈ A_f (de ⟨x, y₁⟩ ∈ f ⊆ A_f ×ₛ B_f)
      have hx_in_Af : x ∈ A_f := by
        have h := hf_func.1 ⟨x, y₁⟩ hpair1
        rw [CartesianProduct_is_specified] at h
        have := h.2.1; rwa [fst_of_ordered_pair] at this
      have hx_in_Ag : x ∈ A_g := by
        have h := hg_func.1 ⟨x, y₂⟩ hpair2
        rw [CartesianProduct_is_specified] at h
        have := h.2.1; rwa [fst_of_ordered_pair] at this
      have h_uniq_f := hf_func.2 x hx_in_Af
      have h_uniq_g := hg_func.2 x hx_in_Ag
      -- x ∈ domain f ∩ domain g → apply f x = apply g x
      have hx_dom_f : x ∈ domain f := (mem_domain f x).mpr ⟨y₁, hpair1⟩
      have hx_dom_g : x ∈ domain g := (mem_domain g x).mpr ⟨y₂, hpair2⟩
      have hx_inter : x ∈ ((domain f) ∩ (domain g)) :=
        (mem_inter_iff (domain f) (domain g) x).mpr ⟨hx_dom_f, hx_dom_g⟩
      have h_apply_eq := h_compat f g hf_in_F hg_in_F x hx_inter
      -- y₁ = apply f x = apply g x = y₂
      calc y₁ = apply f x := (apply_eq f x y₁ h_uniq_f hpair1).symm
        _ = apply g x    := h_apply_eq
        _ = y₂           := apply_eq g x y₂ h_uniq_g hpair2

    /-! ============================================================ -/
    /-! ### 4. EXISTENCIA LOCAL (Inducción) ### -/
    /-! ============================================================ -/

    theorem computation_existence (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : IsFunction g A A) :
      ∀ n, n ∈ ω → ∃ f, isComputation n f A a g := by

      let S := sep (ω : U) (fun n => ∃ f, isComputation n f A a g)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1

        · -- Base n=0: f = {⟨0, a⟩}
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
          let f0 := Singleton (OrderedPair (∅ : U) a)
          exists f0
          constructor
          · -- Es función {0} -> A
            constructor
            · -- f0 ⊆ σ∅ ×ₛ A
              intro p hp
              rw [Singleton_is_specified] at hp
              rw [hp, OrderedPair_mem_CartesianProduct]
              exact ⟨(mem_succ_iff_local ∅ ∅).mpr (Or.inr rfl), ha⟩
            · -- ∀ x ∈ σ∅, ∃! y, ⟨x,y⟩ ∈ f0
              intro x hx
              rw [mem_succ_iff_local] at hx
              have hx_eq : x = ∅ := by
                cases hx with
                | inl h => exact absurd h (EmptySet_is_empty x)
                | inr h => exact h
              rw [hx_eq]
              exact ⟨a, (Singleton_is_specified _ _).mpr rfl, fun y hy =>
                (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                  ((Singleton_is_specified _ _).mp hy)).2⟩
          · constructor
            · -- f(0) = a
              have h_uniq : ∃! y, ⟨(∅ : U), y⟩ ∈ f0 :=
                ⟨a, (Singleton_is_specified _ _).mpr rfl, fun y hy =>
                  (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                    ((Singleton_is_specified _ _).mp hy)).2⟩
              exact apply_eq f0 ∅ a h_uniq ((Singleton_is_specified _ _).mpr rfl)
            · -- ∀ k ∈ 0 (vacuamente cierto)
              intro k hk; exact False.elim (EmptySet_is_empty k hk)

        · -- Paso: n -> σ n
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S; obtain ⟨hn_omega, ⟨fn, hfn⟩⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega

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
          have hn_nat : IsNat n := mem_Omega_is_Nat n hn_omega
          have hσn_nat : IsNat (σ n) := isNat_succ n hn_nat
          have h_dom_fn : domain fn = σ n := function_domain_eq fn (σ n) A hfn.1
          have h_sn_notin : σ n ∉ σ n := not_mem_self (σ n) hσn_nat
          have hn_in_sn : n ∈ σ n := mem_succ_self n
          -- apply fn n ∈ A
          have h_fn_n_in_A : apply fn n ∈ A := by
            have h := hfn.1.1 ⟨n, apply fn n⟩ (apply_mem fn n (hfn.1.2 n hn_in_sn))
            rw [OrderedPair_mem_CartesianProduct] at h
            exact h.2
          -- val_next ∈ A
          have h_val_in : val_next ∈ A := by
            have h_uniq_g := hg.2 (apply fn n) h_fn_n_in_A
            have h := hg.1 ⟨apply fn n, val_next⟩ (apply_mem g (apply fn n) h_uniq_g)
            rw [OrderedPair_mem_CartesianProduct] at h
            exact h.2
          -- Para x ∈ σ n: ∃! y, ⟨x,y⟩ ∈ f_next (coincide con fn)
          have h_restrict : ∀ x, x ∈ σ n → ∃! y, ⟨x, y⟩ ∈ f_next := by
            intro x hx
            obtain ⟨y, hy, huniq⟩ := hfn.1.2 x hx
            apply ExistsUnique.intro y
            · rw [mem_union_iff]; left; exact hy
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h => exact huniq y' h
              | inr h =>
                rw [Singleton_is_specified] at h
                have heq := Eq_of_OrderedPairs_given_projections x y' (σ n) val_next h
                rw [heq.1] at hx
                exact absurd hx h_sn_notin
          -- apply f_next x = apply fn x para x ∈ σ n
          have h_apply_fn : ∀ x, x ∈ σ n → apply f_next x = apply fn x := by
            intro x hx
            apply apply_eq f_next x (apply fn x) (h_restrict x hx)
            rw [mem_union_iff]; left
            exact apply_mem fn x (hfn.1.2 x hx)
          -- ∃! y, ⟨σ n, y⟩ ∈ f_next
          have h_sn_uniq : ∃! y, ⟨σ n, y⟩ ∈ f_next := by
            apply ExistsUnique.intro val_next
            · rw [mem_union_iff]; right
              exact (Singleton_is_specified _ _).mpr rfl
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h =>
                have hx_in_dom : σ n ∈ domain fn := (mem_domain fn (σ n)).mpr ⟨y', h⟩
                rw [h_dom_fn] at hx_in_dom
                exact absurd hx_in_dom h_sn_notin
              | inr h =>
                rw [Singleton_is_specified] at h
                exact (Eq_of_OrderedPairs_given_projections (σ n) y' (σ n) val_next h).2
          constructor
          · -- 1. IsFunction f_next (σ (σ n)) A
            constructor
            · -- f_next ⊆ σ(σ n) ×ₛ A
              intro p hp
              rw [mem_union_iff] at hp
              cases hp with
              | inl h_fn =>
                have hp_prod := hfn.1.1 p h_fn
                rw [CartesianProduct_is_specified] at hp_prod ⊢
                exact ⟨hp_prod.1,
                  (mem_succ_iff_local (σ n) (fst p)).mpr (Or.inl hp_prod.2.1),
                  hp_prod.2.2⟩
              | inr h_sing =>
                rw [Singleton_is_specified] at h_sing
                rw [h_sing]
                exact (OrderedPair_mem_CartesianProduct (σ n) val_next (σ (σ n)) A).mpr
                  ⟨(mem_succ_iff_local (σ n) (σ n)).mpr (Or.inr rfl), h_val_in⟩
            · -- ∀ x ∈ σ(σ n), ∃! y, ⟨x,y⟩ ∈ f_next
              intro x hx
              rw [mem_succ_iff_local] at hx
              cases hx with
              | inl h_in_sn => exact h_restrict x h_in_sn
              | inr h_eq_sn => rw [h_eq_sn]; exact h_sn_uniq
          · constructor
            · -- 2. apply f_next ∅ = a
              have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn_omega
              apply apply_eq f_next ∅ a (h_restrict ∅ h_zero_in)
              rw [mem_union_iff]; left
              have := apply_mem fn ∅ (hfn.1.2 ∅ h_zero_in)
              rwa [hfn.2.1] at this
            · -- 3. ∀ k ∈ σ n, apply f_next (σ k) = apply g (apply f_next k)
              intro k hk
              rw [mem_succ_iff_local] at hk
              cases hk with
              | inl hk_in_n =>
                have hk_nat : IsNat k := nat_element_is_nat n k hn_nat hk_in_n
                have hk_in_sn : k ∈ σ n := subset_succ_local n k hk_in_n
                have hsk_in_sn : σ k ∈ σ n := succ_mem_succ_of_mem k n hk_nat hn_nat hk_in_n
                rw [h_apply_fn (σ k) hsk_in_sn, h_apply_fn k hk_in_sn]
                exact hfn.2.2 k hk_in_n
              | inr hk_eq_n =>
                rw [hk_eq_n]
                have h_apply_sn : apply f_next (σ n) = val_next :=
                  apply_eq f_next (σ n) val_next h_sn_uniq
                    ((mem_union_iff fn (Singleton pair_next) ⟨σ n, val_next⟩).mpr
                      (Or.inr ((Singleton_is_specified _ _).mpr rfl)))
                rw [h_apply_sn, h_apply_fn n hn_in_sn]

      intro n hn; rw [←h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    /-! ============================================================ -/
    /-! ### 5. LEMAS DE COMPATIBILIDAD GLOBAL ### -/
    /-! ============================================================ -/

    /-- σ n ⊆ ω para todo n ∈ ω -/
    theorem succ_subset_omega (n : U) (hn : n ∈ ω) : (σ n) ⊆ ω := by
      intro x hx
      rw [mem_succ_iff_local] at hx
      cases hx with
      | inl hx_in_n =>
        exact transitive_element_subset ω n Omega_is_transitive hn x hx_in_n
      | inr hx_eq_n =>
        rw [hx_eq_n]
        exact hn

    /-- Todo cómputo de longitud n es subconjunto de ω ×ₛ A -/
    theorem computation_subset_omega_times_A (A a g n : U) (hn : n ∈ ω)
        (f : U) (hf : isComputation n f A a g) : f ⊆ ω ×ₛ A := by
      intro p hp
      have hp_in : p ∈ σ n ×ₛ A := hf.1.1 p hp
      rw [CartesianProduct_is_specified] at hp_in ⊢
      exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩

    /-- Si n₁ ∈ n₂ (con n₂ natural), entonces σ n₁ ⊆ σ n₂ -/
    theorem succ_subset_succ_of_mem (n₁ n₂ : U) (hn₂_nat : IsNat n₂) (h : n₁ ∈ n₂) :
        σ n₁ ⊆ σ n₂ := by
      have hn₂_trans : IsTransitive n₂ := hn₂_nat.1
      have hn₁_sub : n₁ ⊆ n₂ := transitive_element_subset n₂ n₁ hn₂_trans h
      intro x hx
      rw [mem_succ_iff_local] at hx ⊢
      cases hx with
      | inl hx_in_n₁ => left; exact hn₁_sub x hx_in_n₁
      | inr hx_eq_n₁ => left; rw [hx_eq_n₁]; exact h

    /-- Restricción general: cómputo de longitud n₂ restringido a σ n₁ es cómputo de longitud n₁ -/
    theorem restriction_computation_general (A a g n₁ n₂ : U)
        (hn₁ : n₁ ∈ ω) (hn₂_nat : IsNat n₂) (hlt : n₁ ∈ n₂)
        (f : U) (hf : isComputation n₂ f A a g) :
        isComputation n₁ (restrict f (σ n₁)) A a g := by
      have h_sn₁_sub : σ n₁ ⊆ σ n₂ := succ_subset_succ_of_mem n₁ n₂ hn₂_nat hlt
      constructor
      · exact restrict_is_function f (σ n₂) A (σ n₁) hf.1 h_sn₁_sub
      · constructor
        · have h_zero_in : (∅ : U) ∈ σ n₁ := zero_in_succ_nat n₁ hn₁
          rw [restrict_apply f (σ n₁) ∅ h_zero_in]
          exact hf.2.1
        · intro k hk
          have hn₁_nat : IsNat n₁ := mem_Omega_is_Nat n₁ hn₁
          have hk_nat : IsNat k := nat_element_is_nat n₁ k hn₁_nat hk
          have hk_in_sn₁ : k ∈ σ n₁ := subset_succ_local n₁ k hk
          have hsk_in_sn₁ : σ k ∈ σ n₁ := succ_mem_succ_of_mem k n₁ hk_nat hn₁_nat hk
          rw [restrict_apply f (σ n₁) (σ k) hsk_in_sn₁]
          rw [restrict_apply f (σ n₁) k hk_in_sn₁]
          exact hf.2.2 k (mem_trans k n₁ n₂ hk_nat hn₁_nat hn₂_nat hk hlt)

    /-- El conjunto de todos los cómputos válidos -/
    noncomputable def RecursionComputations (A a g : U) : U :=
      sep (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputation n f A a g))

    /-- Los cómputos en RecursionComputations son compatibles a pares -/
    theorem computations_are_compatible (A a g : U) :
        isCompatibleSystem (RecursionComputations A a g) := by
      intro f₁ f₂ hf₁_in hf₂_in
      unfold RecursionComputations at hf₁_in hf₂_in
      rw [mem_sep_iff] at hf₁_in hf₂_in
      obtain ⟨_, n₁, hn₁_omega, hf₁⟩ := hf₁_in
      obtain ⟨_, n₂, hn₂_omega, hf₂⟩ := hf₂_in
      have hn₁_nat : IsNat n₁ := mem_Omega_is_Nat n₁ hn₁_omega
      have hn₂_nat : IsNat n₂ := mem_Omega_is_Nat n₂ hn₂_omega
      intro x hx
      rw [mem_inter_iff] at hx
      obtain ⟨hx_dom1, hx_dom2⟩ := hx
      -- Por tricotomía sobre n₁ y n₂
      rcases trichotomy n₁ n₂ hn₁_nat hn₂_nat with h | h | h
      · -- n₁ ∈ n₂: f₂ restringida a σ n₁ es cómputo de longitud n₁
        have hf₂_res : isComputation n₁ (restrict f₂ (σ n₁)) A a g :=
          restriction_computation_general A a g n₁ n₂ hn₁_omega hn₂_nat h f₂ hf₂
        have h_eq : f₁ = restrict f₂ (σ n₁) :=
          computation_uniqueness A a g n₁ hn₁_omega f₁ (restrict f₂ (σ n₁)) hf₁ hf₂_res
        -- x ∈ domain f₁ = σ n₁
        have hx_in_sn₁ : x ∈ σ n₁ := by
          rwa [← function_domain_eq f₁ (σ n₁) A hf₁.1]
        calc apply f₁ x
            = apply (restrict f₂ (σ n₁)) x := by rw [h_eq]
          _ = apply f₂ x                       := restrict_apply f₂ (σ n₁) x hx_in_sn₁
      · -- n₁ = n₂: por unicidad f₁ = f₂
        have h_eq : f₁ = f₂ :=
          computation_uniqueness A a g n₁ hn₁_omega f₁ f₂ hf₁ (h ▸ hf₂)
        rw [h_eq]
      · -- n₂ ∈ n₁: simétrico
        have hf₁_res : isComputation n₂ (restrict f₁ (σ n₂)) A a g :=
          restriction_computation_general A a g n₂ n₁ hn₂_omega hn₁_nat h f₁ hf₁
        have h_eq : f₂ = restrict f₁ (σ n₂) :=
          computation_uniqueness A a g n₂ hn₂_omega f₂ (restrict f₁ (σ n₂)) hf₂ hf₁_res
        have hx_in_sn₂ : x ∈ σ n₂ := by
          rwa [← function_domain_eq f₂ (σ n₂) A hf₂.1]
        calc apply f₁ x
            = apply (restrict f₁ (σ n₂)) x := (restrict_apply f₁ (σ n₂) x hx_in_sn₂).symm
          _ = apply f₂ x                       := by rw [← h_eq]

    /-! ============================================================ -/
    /-! ### 6. TEOREMA DE RECURSIÓN (GLOBAL) ### -/
    /-! ============================================================ -/

    theorem RecursionTheorem (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : IsFunction g A A) :
      ∃! F, IsFunction F ω A ∧
            (apply F (∅ : U) = a) ∧
            (∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) := by

      let Comps := RecursionComputations A a g
      let F := (⋃ Comps)

      -- Paso 1: F es función (usando lemas de compatibilidad)
      -- Paso 2: Dominio de F es ω (porque ∀ n, n ∈ dom(f_n) ⊆ dom(F))
      -- Paso 3: F cumple las ecuaciones (heredado de los f_n)

      -- Lema local: meter un cómputo en Comps (usando mem_sep_iff directamente)
      have h_mem_Comps : ∀ n f, n ∈ ω → isComputation n f A a g → f ∈ Comps := by
        intro n f hn hf
        exact (mem_sep_iff _ _ _).mpr
          ⟨(mem_powerset_iff _ _).mpr (computation_subset_omega_times_A A a g n hn f hf),
           n, hn, hf⟩

      -- F es monovaluada (por compatibilidad de los cómputos)
      have h_sv : IsSingleValued F :=
        union_compatible_is_function Comps
          (fun f hf => by
            obtain ⟨_, n, _, hf_comp⟩ := (mem_sep_iff _ _ _).mp hf
            exact ⟨σ n, A, hf_comp.1⟩)
          (computations_are_compatible A a g)

      -- F es función de ω a A
      have h_F_func : IsFunction F ω A := by
        constructor
        · -- F ⊆ ω ×ₛ A
          intro p hp
          rw [mem_sUnion_iff] at hp
          obtain ⟨f, hf_in, hp_in_f⟩ := hp
          obtain ⟨_, n, hn, hf_comp⟩ := (mem_sep_iff _ _ _).mp hf_in
          exact computation_subset_omega_times_A A a g n hn f hf_comp p hp_in_f
        · -- ∀ x ∈ ω, ∃! y, ⟨x, y⟩ ∈ F
          intro x hx
          obtain ⟨fx, hfx⟩ := computation_existence A a g ha hg x hx
          have h_pair_in_F : ⟨x, apply fx x⟩ ∈ F := by
            rw [mem_sUnion_iff]
            exact ⟨fx, h_mem_Comps x fx hx hfx,
                   apply_mem fx x (hfx.1.2 x (mem_succ_self x))⟩
          exact ExistsUnique.intro (apply fx x) h_pair_in_F
            (fun y hy => (h_sv x (apply fx x) y h_pair_in_F hy).symm)

      -- Propiedades de F (extraídas para usarlas en unicidad)
      have h_F_zero : apply F (∅ : U) = a := by
        obtain ⟨f₀, hf₀⟩ := computation_existence A a g ha hg ∅ zero_in_Omega
        have h_pair_in_f₀ : ⟨(∅ : U), a⟩ ∈ f₀ := by
          have := apply_mem f₀ ∅ (hf₀.1.2 ∅ (mem_succ_self ∅))
          rwa [hf₀.2.1] at this
        have h_pair_in_F : ⟨(∅ : U), a⟩ ∈ F := by
          rw [mem_sUnion_iff]
          exact ⟨f₀, h_mem_Comps ∅ f₀ zero_in_Omega hf₀, h_pair_in_f₀⟩
        exact apply_eq F ∅ a (h_F_func.2 ∅ zero_in_Omega) h_pair_in_F

      have h_F_step : ∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n) := by
        intro n hn
        obtain ⟨fsn, hfsn⟩ := computation_existence A a g ha hg (σ n) (succ_in_Omega n hn)
        have h_n_in_ssn : n ∈ σ (σ n) := subset_succ_local (σ n) n (mem_succ_self n)
        have h_sn_in_ssn : σ n ∈ σ (σ n) := mem_succ_self (σ n)
        have h_sn_in_F : ⟨σ n, apply fsn (σ n)⟩ ∈ F := by
          rw [mem_sUnion_iff]
          exact ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
                 apply_mem fsn (σ n) (hfsn.1.2 (σ n) h_sn_in_ssn)⟩
        have h_n_in_F : ⟨n, apply fsn n⟩ ∈ F := by
          rw [mem_sUnion_iff]
          exact ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
                 apply_mem fsn n (hfsn.1.2 n h_n_in_ssn)⟩
        have hF_sn := apply_eq F (σ n) _ (h_F_func.2 (σ n) (succ_in_Omega n hn)) h_sn_in_F
        have hF_n  := apply_eq F n _ (h_F_func.2 n hn) h_n_in_F
        rw [hF_sn, hfsn.2.2 n (mem_succ_self n), ← hF_n]

      apply ExistsUnique.intro F
      · -- Existencia
        exact ⟨h_F_func, h_F_zero, h_F_step⟩
      · -- Unicidad: cualquier G con las mismas propiedades es igual a F
        intro G hG
        obtain ⟨hG_func, hG_zero, hG_step⟩ := hG
        -- Lema: apply G n = apply F n para todo n ∈ ω (inducción)
        have h_agree : ∀ n, n ∈ ω → apply G n = apply F n := by
          let S := sep ω (fun n => apply G n = apply F n)
          have h_S_eq_ω : S = ω := by
            apply induction_principle S
            · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
            · rw [mem_sep_iff]
              exact ⟨zero_in_Omega, hG_zero.trans h_F_zero.symm⟩
            · intro n hn_in_S
              rw [mem_sep_iff] at hn_in_S
              obtain ⟨hn_ω, h_eq_n⟩ := hn_in_S
              rw [mem_sep_iff]
              exact ⟨succ_in_Omega n hn_ω, by
                rw [hG_step n hn_ω, h_eq_n, ← h_F_step n hn_ω]⟩
          intro n hn
          rw [← h_S_eq_ω] at hn
          rw [mem_sep_iff] at hn
          exact hn.2
        -- G = F por extensión: sus pares coinciden
        apply ExtSet; intro p; constructor
        · intro hp
          have hp_prod := hG_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_is_op, h_fst_in_ω, _⟩ := hp_prod
          have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
          have h_snd_eq : snd p = apply F (fst p) := by
            have h_pair_in_G : ⟨fst p, snd p⟩ ∈ G := hp_eq ▸ hp
            have := apply_eq G (fst p) (snd p) (hG_func.2 (fst p) h_fst_in_ω) h_pair_in_G
            rw [h_agree (fst p) h_fst_in_ω] at this
            exact this.symm
          rw [hp_eq, h_snd_eq]
          exact apply_mem F (fst p) (h_F_func.2 (fst p) h_fst_in_ω)
        · intro hp
          have hp_prod := h_F_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_is_op, h_fst_in_ω, _⟩ := hp_prod
          have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
          have h_snd_eq : snd p = apply G (fst p) := by
            have h_pair_in_F : ⟨fst p, snd p⟩ ∈ F := hp_eq ▸ hp
            have := apply_eq F (fst p) (snd p) (h_F_func.2 (fst p) h_fst_in_ω) h_pair_in_F
            rw [← h_agree (fst p) h_fst_in_ω] at this
            exact this.symm
          rw [hp_eq, h_snd_eq]
          exact apply_mem G (fst p) (hG_func.2 (fst p) h_fst_in_ω)

    /-! ============================================================ -/
    /-! ### 7. RECURSIÓN CON PASO INDEXADO ### -/
    /-! ============================================================ -/

    /-- Cómputo de longitud n donde la función de paso recibe el índice: g : ω ×ₛ A → A -/
    def isComputationStep (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      IsFunction f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g ⟨k, apply f k⟩)

    theorem restriction_is_computation_step (A a g n : U) (hn : n ∈ ω) :
        ∀ f, isComputationStep (σ n) f A a g → isComputationStep n (restrict f (σ n)) A a g := by
      intro f hf
      refine ⟨restrict_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n)), ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn
        rw [restrict_apply f (σ n) (∅ : U) h_zero_in]; exact hf.2.1
      · intro k hk
        have hn_nat := mem_Omega_is_Nat n hn
        have hk_nat := nat_element_is_nat n k hn_nat hk
        have h_k_in  : k ∈ σ n    := subset_succ_local n k hk
        have h_sk_in : σ k ∈ σ n  := succ_mem_succ_of_mem k n hk_nat hn_nat hk
        rw [restrict_apply f (σ n) (σ k) h_sk_in, restrict_apply f (σ n) k h_k_in]
        exact hf.2.2 k h_k_in

    theorem restriction_computation_general_step (A a g n₁ n₂ : U)
        (hn₁ : n₁ ∈ ω) (hn₂_nat : IsNat n₂) (hlt : n₁ ∈ n₂)
        (f : U) (hf : isComputationStep n₂ f A a g) :
        isComputationStep n₁ (restrict f (σ n₁)) A a g := by
      have h_sn₁_sub : σ n₁ ⊆ σ n₂ := succ_subset_succ_of_mem n₁ n₂ hn₂_nat hlt
      refine ⟨restrict_is_function f (σ n₂) A (σ n₁) hf.1 h_sn₁_sub, ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n₁ := zero_in_succ_nat n₁ hn₁
        rw [restrict_apply f (σ n₁) ∅ h_zero_in]; exact hf.2.1
      · intro k hk
        have hn₁_nat := mem_Omega_is_Nat n₁ hn₁
        have hk_nat  := nat_element_is_nat n₁ k hn₁_nat hk
        have hk_in_sn₁  : k ∈ σ n₁   := subset_succ_local n₁ k hk
        have hsk_in_sn₁ : σ k ∈ σ n₁ := succ_mem_succ_of_mem k n₁ hk_nat hn₁_nat hk
        rw [restrict_apply f (σ n₁) (σ k) hsk_in_sn₁, restrict_apply f (σ n₁) k hk_in_sn₁]
        exact hf.2.2 k (mem_trans k n₁ n₂ hk_nat hn₁_nat hn₂_nat hk hlt)

    theorem computation_uniqueness_step (A a g : U) :
        ∀ n, n ∈ ω → ∀ f₁ f₂,
          isComputationStep n f₁ A a g → isComputationStep n f₂ A a g → f₁ = f₂ := by
      let S := sep (ω : U) (fun n => ∀ f₁ f₂,
        isComputationStep n f₁ A a g → isComputationStep n f₂ A a g → f₁ = f₂)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base n = ∅
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
          intro f₁ f₂ hf₁ hf₂
          have h_dom1 := function_domain_eq f₁ (σ (∅ : U)) A hf₁.1
          have h_dom2 := function_domain_eq f₂ (σ (∅ : U)) A hf₂.1
          apply ExtSet; intro p; constructor
          · intro hp
            have : p ∈ σ (∅ : U) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at this
            have h_is_op : isOrderedPair p := this.1
            obtain ⟨_, _, _⟩ := this
            have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
            have hx_eq : fst p = ∅ := by
              have : fst p ∈ domain f₁ := by rw [mem_domain]; exact ⟨snd p, hp_eq ▸ hp⟩
              rw [h_dom1, mem_succ_iff_local] at this
              cases this with | inl h => exact absurd h (EmptySet_is_empty _) | inr h => exact h
            rw [hx_eq] at hp_eq
            have hy_eq : snd p = a := by
              rw [← hf₁.2.1]; symm
              exact apply_eq f₁ ∅ _ (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₂.2.1]
            exact apply_mem f₂ ∅ (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
          · intro hp
            have : p ∈ σ (∅ : U) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at this
            have h_is_op : isOrderedPair p := this.1
            have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
            have hx_eq : fst p = ∅ := by
              have : fst p ∈ domain f₂ := by rw [mem_domain]; exact ⟨snd p, hp_eq ▸ hp⟩
              rw [h_dom2, mem_succ_iff_local] at this
              cases this with | inl h => exact absurd h (EmptySet_is_empty _) | inr h => exact h
            rw [hx_eq] at hp_eq
            have hy_eq : snd p = a := by
              rw [← hf₂.2.1]; symm
              exact apply_eq f₂ ∅ _ (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₁.2.1]
            exact apply_mem f₁ ∅ (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
        · -- Paso inductivo
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega
          intro f₁ f₂ hf₁ hf₂
          let f₁_res := restrict f₁ (σ n)
          let f₂_res := restrict f₂ (σ n)
          have h1 : isComputationStep n f₁_res A a g :=
            restriction_is_computation_step A a g n hn_omega f₁ hf₁
          have h2 : isComputationStep n f₂_res A a g :=
            restriction_is_computation_step A a g n hn_omega f₂ hf₂
          have h_eq_res : f₁_res = f₂_res := h_unique_n f₁_res f₂_res h1 h2
          have h_apply_eq : apply f₁ (σ n) = apply f₂ (σ n) :=
            calc apply f₁ (σ n)
                = apply g ⟨n, apply f₁ n⟩       := hf₁.2.2 n (mem_succ_self n)
              _ = apply g ⟨n, apply f₁_res n⟩   := by
                    rw [← restrict_apply f₁ (σ n) n (mem_succ_self n)]
              _ = apply g ⟨n, apply f₂_res n⟩   := by rw [h_eq_res]
              _ = apply g ⟨n, apply f₂ n⟩       := by
                    rw [restrict_apply f₂ (σ n) n (mem_succ_self n)]
              _ = apply f₂ (σ n)                 := (hf₂.2.2 n (mem_succ_self n)).symm
          apply ExtSet; intro p; constructor
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f1 : p ∈ f₁_res := (mem_restrict_iff f₁ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f2 : p ∈ f₂_res := h_eq_res ▸ hp_f1
              exact restrict_subset f₂ (σ n) p hp_f2
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₁ (fst p) :=
                (apply_eq f₁ (fst p) (snd p)
                  (hf₁.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, h_apply_eq]
              exact apply_mem f₂ (σ n) (hf₂.1.2 (σ n) (mem_succ_self (σ n)))
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f2 : p ∈ f₂_res := (mem_restrict_iff f₂ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f1 : p ∈ f₁_res := h_eq_res.symm ▸ hp_f2
              exact restrict_subset f₁ (σ n) p hp_f1
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₂ (fst p) :=
                (apply_eq f₂ (fst p) (snd p)
                  (hf₂.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, ← h_apply_eq]
              exact apply_mem f₁ (σ n) (hf₁.1.2 (σ n) (mem_succ_self (σ n)))
      intro n hn; rw [← h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    theorem computation_existence_step (A a g : U)
        (ha : a ∈ A) (hg : IsFunction g (ω ×ₛ A) A) :
        ∀ n, n ∈ ω → ∃ f, isComputationStep n f A a g := by
      let S := sep (ω : U) (fun n => ∃ f, isComputationStep n f A a g)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base n = ∅
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
          let f0 := Singleton (OrderedPair (∅ : U) a)
          exact ⟨f0, ⟨fun p hp => by
            rw [Singleton_is_specified] at hp; rw [hp, OrderedPair_mem_CartesianProduct]
            exact ⟨(mem_succ_iff_local ∅ ∅).mpr (Or.inr rfl), ha⟩,
            fun x hx => by
              rw [mem_succ_iff_local] at hx
              have : x = ∅ := by cases hx with
                | inl h => exact absurd h (EmptySet_is_empty x)
                | inr h => exact h
              rw [this]
              exact ⟨a, (Singleton_is_specified _ _).mpr rfl,
                fun y hy => (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                  ((Singleton_is_specified _ _).mp hy)).2⟩⟩,
            apply_eq f0 ∅ a
              ⟨a, (Singleton_is_specified _ _).mpr rfl,
                fun y hy => (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                  ((Singleton_is_specified _ _).mp hy)).2⟩
              ((Singleton_is_specified _ _).mpr rfl),
            fun k hk => absurd hk (EmptySet_is_empty k)⟩
        · -- Paso inductivo
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S
          obtain ⟨hn_omega, ⟨fn, hfn⟩⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega
          have hn_nat    := mem_Omega_is_Nat n hn_omega
          have hσn_nat   := isNat_succ n hn_nat
          have h_dom_fn  := function_domain_eq fn (σ n) A hfn.1
          have h_sn_ni   : σ n ∉ σ n := not_mem_self (σ n) hσn_nat
          have hn_in_sn  : n ∈ σ n   := mem_succ_self n
          have h_fn_n_A  : apply fn n ∈ A := by
            have h := hfn.1.1 ⟨n, apply fn n⟩ (apply_mem fn n (hfn.1.2 n hn_in_sn))
            rw [OrderedPair_mem_CartesianProduct] at h; exact h.2
          -- ⟨n, fn(n)⟩ ∈ ω ×ₛ A
          have h_pair_dom : ⟨n, apply fn n⟩ ∈ ω ×ₛ A :=
            (OrderedPair_mem_CartesianProduct n (apply fn n) ω A).mpr ⟨hn_omega, h_fn_n_A⟩
          let val_next  := apply g ⟨n, apply fn n⟩
          let pair_next := OrderedPair (σ n) val_next
          let f_next    := fn ∪ Singleton pair_next
          have h_val_A : val_next ∈ A := by
            have h := hg.1 ⟨⟨n, apply fn n⟩, val_next⟩
              (apply_mem g ⟨n, apply fn n⟩ (hg.2 ⟨n, apply fn n⟩ h_pair_dom))
            rw [OrderedPair_mem_CartesianProduct] at h; exact h.2
          have h_restrict : ∀ x, x ∈ σ n → ∃! y, ⟨x, y⟩ ∈ f_next := by
            intro x hx
            obtain ⟨y, hy, huniq⟩ := hfn.1.2 x hx
            apply ExistsUnique.intro y
            · rw [mem_union_iff]; left; exact hy
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h => exact huniq y' h
              | inr h =>
                rw [Singleton_is_specified] at h
                have heq := Eq_of_OrderedPairs_given_projections x y' (σ n) val_next h
                rw [heq.1] at hx; exact absurd hx h_sn_ni
          have h_app_fn : ∀ x, x ∈ σ n → apply f_next x = apply fn x := by
            intro x hx
            apply apply_eq f_next x (apply fn x) (h_restrict x hx)
            rw [mem_union_iff]; left
            exact apply_mem fn x (hfn.1.2 x hx)
          have h_sn_uniq : ∃! y, ⟨σ n, y⟩ ∈ f_next := by
            apply ExistsUnique.intro val_next
            · rw [mem_union_iff]; right
              exact (Singleton_is_specified _ _).mpr rfl
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h =>
                exact absurd (h_dom_fn ▸ (mem_domain fn (σ n)).mpr ⟨y', h⟩) h_sn_ni
              | inr h =>
                exact (Eq_of_OrderedPairs_given_projections (σ n) y' (σ n) val_next
                  ((Singleton_is_specified _ _).mp h)).2
          exact ⟨f_next,
            ⟨fun p hp => by
              rw [mem_union_iff] at hp
              cases hp with
              | inl h =>
                have hp_prod := hfn.1.1 p h
                rw [CartesianProduct_is_specified] at hp_prod ⊢
                exact ⟨hp_prod.1,
                  (mem_succ_iff_local (σ n) (fst p)).mpr (Or.inl hp_prod.2.1), hp_prod.2.2⟩
              | inr h =>
                rw [Singleton_is_specified] at h; rw [h]
                exact (OrderedPair_mem_CartesianProduct (σ n) val_next (σ (σ n)) A).mpr
                  ⟨(mem_succ_iff_local (σ n) (σ n)).mpr (Or.inr rfl), h_val_A⟩,
            fun x hx => by
              rw [mem_succ_iff_local] at hx
              cases hx with
              | inl h => exact h_restrict x h
              | inr h => rw [h]; exact h_sn_uniq⟩,
            by
              have h0 : (∅ : U) ∈ σ n := zero_in_succ_nat n hn_omega
              apply apply_eq f_next ∅ a (h_restrict ∅ h0)
              rw [mem_union_iff]; left
              have := apply_mem fn ∅ (hfn.1.2 ∅ h0); rwa [hfn.2.1] at this,
            fun k hk => by
              rw [mem_succ_iff_local] at hk
              cases hk with
              | inl hk_in_n =>
                have hk_nat  := nat_element_is_nat n k hn_nat hk_in_n
                have hk_sn   := subset_succ_local n k hk_in_n
                have hsk_sn  := succ_mem_succ_of_mem k n hk_nat hn_nat hk_in_n
                rw [h_app_fn (σ k) hsk_sn, h_app_fn k hk_sn]
                exact hfn.2.2 k hk_in_n
              | inr hk_eq_n =>
                rw [hk_eq_n,
                  apply_eq f_next (σ n) val_next h_sn_uniq
                    ((mem_union_iff _ _ _).mpr (Or.inr ((Singleton_is_specified _ _).mpr rfl))),
                  h_app_fn n hn_in_sn]⟩
      intro n hn; rw [← h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    noncomputable def RecursionComputationsStep (A a g : U) : U :=
      sep (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputationStep n f A a g))

    theorem computations_are_compatible_step (A a g : U) :
        isCompatibleSystem (RecursionComputationsStep A a g) := by
      intro f₁ f₂ hf₁_in hf₂_in
      unfold RecursionComputationsStep at hf₁_in hf₂_in
      rw [mem_sep_iff] at hf₁_in hf₂_in
      obtain ⟨_, n₁, hn₁_omega, hf₁⟩ := hf₁_in
      obtain ⟨_, n₂, hn₂_omega, hf₂⟩ := hf₂_in
      have hn₁_nat := mem_Omega_is_Nat n₁ hn₁_omega
      have hn₂_nat := mem_Omega_is_Nat n₂ hn₂_omega
      intro x hx
      rw [mem_inter_iff] at hx
      obtain ⟨hx_dom1, hx_dom2⟩ := hx
      rcases trichotomy n₁ n₂ hn₁_nat hn₂_nat with h | h | h
      · have hf₂_res := restriction_computation_general_step A a g n₁ n₂ hn₁_omega hn₂_nat h f₂ hf₂
        have h_eq := computation_uniqueness_step A a g n₁ hn₁_omega f₁ _ hf₁ hf₂_res
        have hx_in : x ∈ σ n₁ := by rwa [← function_domain_eq f₁ (σ n₁) A hf₁.1]
        calc apply f₁ x = apply (restrict f₂ (σ n₁)) x := by rw [h_eq]
          _ = apply f₂ x := restrict_apply f₂ (σ n₁) x hx_in
      · have h_eq : f₁ = f₂ :=
          computation_uniqueness_step A a g n₁ hn₁_omega f₁ f₂ hf₁ (h ▸ hf₂)
        rw [h_eq]
      · have hf₁_res := restriction_computation_general_step A a g n₂ n₁ hn₂_omega hn₁_nat h f₁ hf₁
        have h_eq := computation_uniqueness_step A a g n₂ hn₂_omega f₂ _ hf₂ hf₁_res
        have hx_in : x ∈ σ n₂ := by rwa [← function_domain_eq f₂ (σ n₂) A hf₂.1]
        calc apply f₁ x = apply (restrict f₁ (σ n₂)) x := (restrict_apply f₁ (σ n₂) x hx_in).symm
          _ = apply f₂ x := by rw [← h_eq]

    /-- Teorema de Recursión con Paso Indexado: F(σ n) = g(n, F(n)) con g : ω ×ₛ A → A -/
    theorem RecursionTheoremWithStep (A a g : U)
        (ha : a ∈ A) (hg : IsFunction g (ω ×ₛ A) A) :
        ∃! F, IsFunction F ω A ∧
              (apply F (∅ : U) = a) ∧
              (∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩) := by
      let Comps := RecursionComputationsStep A a g
      let F := ⋃ Comps
      have h_mem_Comps : ∀ n f, n ∈ ω → isComputationStep n f A a g → f ∈ Comps := fun n f hn hf =>
        (mem_sep_iff _ _ _).mpr ⟨(mem_powerset_iff _ _).mpr (fun p hp => by
          have hp_in : p ∈ σ n ×ₛ A := hf.1.1 p hp
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩), n, hn, hf⟩
      have h_sv : IsSingleValued F :=
        union_compatible_is_function Comps
          (fun f hf => by
            obtain ⟨_, n, _, hf_c⟩ := (mem_sep_iff _ _ _).mp hf
            exact ⟨σ n, A, hf_c.1⟩)
          (computations_are_compatible_step A a g)
      have h_F_func : IsFunction F ω A := by
        constructor
        · intro p hp
          rw [mem_sUnion_iff] at hp
          obtain ⟨f, hf_in, hp_f⟩ := hp
          obtain ⟨_, n, hn, hf_c⟩ := (mem_sep_iff _ _ _).mp hf_in
          have hp_in : p ∈ σ n ×ₛ A := hf_c.1.1 p hp_f
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩
        · intro x hx
          obtain ⟨fx, hfx⟩ := computation_existence_step A a g ha hg x hx
          have h_pair : ⟨x, apply fx x⟩ ∈ F := by
            rw [mem_sUnion_iff]
            exact ⟨fx, h_mem_Comps x fx hx hfx, apply_mem fx x (hfx.1.2 x (mem_succ_self x))⟩
          exact ⟨apply fx x, h_pair, fun y hy => (h_sv x (apply fx x) y h_pair hy).symm⟩
      have h_F_zero : apply F (∅ : U) = a := by
        obtain ⟨f₀, hf₀⟩ := computation_existence_step A a g ha hg ∅ zero_in_Omega
        have h_pair : ⟨(∅ : U), a⟩ ∈ F := by
          rw [mem_sUnion_iff]
          exact ⟨f₀, h_mem_Comps ∅ f₀ zero_in_Omega hf₀, by
            have := apply_mem f₀ ∅ (hf₀.1.2 ∅ (mem_succ_self ∅))
            rwa [hf₀.2.1] at this⟩
        exact apply_eq F ∅ a (h_F_func.2 ∅ zero_in_Omega) h_pair
      have h_F_step : ∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩ := by
        intro n hn
        obtain ⟨fsn, hfsn⟩ := computation_existence_step A a g ha hg (σ n) (succ_in_Omega n hn)
        have h_n_in_ssn  : n ∈ σ (σ n) := subset_succ_local (σ n) n (mem_succ_self n)
        have h_sn_in_ssn : σ n ∈ σ (σ n) := mem_succ_self (σ n)
        have h_sn_F : ⟨σ n, apply fsn (σ n)⟩ ∈ F :=
          (mem_sUnion_iff _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
            apply_mem fsn (σ n) (hfsn.1.2 (σ n) h_sn_in_ssn)⟩
        have h_n_F : ⟨n, apply fsn n⟩ ∈ F :=
          (mem_sUnion_iff _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
            apply_mem fsn n (hfsn.1.2 n h_n_in_ssn)⟩
        rw [apply_eq F (σ n) _ (h_F_func.2 (σ n) (succ_in_Omega n hn)) h_sn_F,
            hfsn.2.2 n (mem_succ_self n),
            apply_eq F n _ (h_F_func.2 n hn) h_n_F]
      apply ExistsUnique.intro F
      · exact ⟨h_F_func, h_F_zero, h_F_step⟩
      · intro G hG
        obtain ⟨hG_func, hG_zero, hG_step⟩ := hG
        have h_agree : ∀ n, n ∈ ω → apply G n = apply F n := by
          let S := sep ω (fun n => apply G n = apply F n)
          have h_S_eq_ω : S = ω := by
            apply induction_principle S
            · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
            · rw [mem_sep_iff]
              exact ⟨zero_in_Omega, hG_zero.trans h_F_zero.symm⟩
            · intro n hn_in_S
              rw [mem_sep_iff] at hn_in_S
              obtain ⟨hn_ω, h_eq_n⟩ := hn_in_S
              rw [mem_sep_iff]
              exact ⟨succ_in_Omega n hn_ω,
                by rw [hG_step n hn_ω, h_eq_n, ← h_F_step n hn_ω]⟩
          intro n hn
          rw [← h_S_eq_ω] at hn
          rw [mem_sep_iff] at hn
          exact hn.2
        apply ExtSet; intro p; constructor
        · intro hp
          have hp_prod := hG_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_op, h_fst_ω, _⟩ := hp_prod
          have hp_eq := OrderedPairSet_is_WellConstructed p h_op
          have h_snd : snd p = apply F (fst p) := by
            have := apply_eq G (fst p) (snd p) (hG_func.2 (fst p) h_fst_ω) (hp_eq ▸ hp)
            rw [h_agree (fst p) h_fst_ω] at this; exact this.symm
          rw [hp_eq, h_snd]; exact apply_mem F (fst p) (h_F_func.2 (fst p) h_fst_ω)
        · intro hp
          have hp_prod := h_F_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_op, h_fst_ω, _⟩ := hp_prod
          have hp_eq := OrderedPairSet_is_WellConstructed p h_op
          have h_snd : snd p = apply G (fst p) := by
            have := apply_eq F (fst p) (snd p) (h_F_func.2 (fst p) h_fst_ω) (hp_eq ▸ hp)
            rw [← h_agree (fst p) h_fst_ω] at this; exact this.symm
          rw [hp_eq, h_snd]; exact apply_mem G (fst p) (hG_func.2 (fst p) h_fst_ω)

    /-! ============================================================ -/
    /-! ### 8. RECURSIÓN POR VALORES ACUMULADOS ### -/
    /-! ============================================================ -/

    /-- Cómputo de longitud n donde el paso recibe el historial completo: g : 𝒫(ω ×ₛ A) → A -/
    def isComputationCoV (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
      IsFunction f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g (restrict f (σ k)))

    theorem restriction_is_computation_cov (A a g n : U) (hn : n ∈ ω) :
        ∀ f, isComputationCoV (σ n) f A a g → isComputationCoV n (restrict f (σ n)) A a g := by
      intro f hf
      refine ⟨restrict_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n)), ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn
        rw [restrict_apply f (σ n) (∅ : U) h_zero_in]; exact hf.2.1
      · intro k hk
        have hn_nat := mem_Omega_is_Nat n hn
        have hk_nat := nat_element_is_nat n k hn_nat hk
        have h_k_in  : k ∈ σ n    := subset_succ_local n k hk
        have h_sk_in : σ k ∈ σ n  := succ_mem_succ_of_mem k n hk_nat hn_nat hk
        have h_sk_sub_sn : σ k ⊆ σ n := succ_subset_succ_of_mem k n hn_nat hk
        rw [restrict_apply f (σ n) (σ k) h_sk_in, hf.2.2 k h_k_in]
        congr 1
        apply ExtSet; intro p; constructor
        · intro hp
          obtain ⟨hp_f, hfst_sk⟩ := (mem_restrict_iff f (σ k) p).mp hp
          exact (mem_restrict_iff (restrict f (σ n)) (σ k) p).mpr
            ⟨(mem_restrict_iff f (σ n) p).mpr ⟨hp_f, h_sk_sub_sn (fst p) hfst_sk⟩, hfst_sk⟩
        · intro hp
          obtain ⟨hp_res_n, hfst_sk⟩ := (mem_restrict_iff (restrict f (σ n)) (σ k) p).mp hp
          obtain ⟨hp_f, _⟩ := (mem_restrict_iff f (σ n) p).mp hp_res_n
          exact (mem_restrict_iff f (σ k) p).mpr ⟨hp_f, hfst_sk⟩

    theorem restriction_computation_general_cov (A a g n₁ n₂ : U)
        (hn₁ : n₁ ∈ ω) (hn₂_nat : IsNat n₂) (hlt : n₁ ∈ n₂)
        (f : U) (hf : isComputationCoV n₂ f A a g) :
        isComputationCoV n₁ (restrict f (σ n₁)) A a g := by
      have h_sn₁_sub : σ n₁ ⊆ σ n₂ := succ_subset_succ_of_mem n₁ n₂ hn₂_nat hlt
      refine ⟨restrict_is_function f (σ n₂) A (σ n₁) hf.1 h_sn₁_sub, ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n₁ := zero_in_succ_nat n₁ hn₁
        rw [restrict_apply f (σ n₁) ∅ h_zero_in]; exact hf.2.1
      · intro k hk
        have hn₁_nat := mem_Omega_is_Nat n₁ hn₁
        have hk_nat  := nat_element_is_nat n₁ k hn₁_nat hk
        have hk_in_sn₁  : k ∈ σ n₁   := subset_succ_local n₁ k hk
        have hsk_in_sn₁ : σ k ∈ σ n₁ := succ_mem_succ_of_mem k n₁ hk_nat hn₁_nat hk
        have h_sk_sub_sn₁ : σ k ⊆ σ n₁ := succ_subset_succ_of_mem k n₁ hn₁_nat hk
        rw [restrict_apply f (σ n₁) (σ k) hsk_in_sn₁,
            hf.2.2 k (mem_trans k n₁ n₂ hk_nat hn₁_nat hn₂_nat hk hlt)]
        congr 1
        apply ExtSet; intro p; constructor
        · intro hp
          obtain ⟨hp_f, hfst_sk⟩ := (mem_restrict_iff f (σ k) p).mp hp
          exact (mem_restrict_iff (restrict f (σ n₁)) (σ k) p).mpr
            ⟨(mem_restrict_iff f (σ n₁) p).mpr ⟨hp_f, h_sk_sub_sn₁ (fst p) hfst_sk⟩, hfst_sk⟩
        · intro hp
          obtain ⟨hp_res, hfst_sk⟩ := (mem_restrict_iff (restrict f (σ n₁)) (σ k) p).mp hp
          obtain ⟨hp_f, _⟩ := (mem_restrict_iff f (σ n₁) p).mp hp_res
          exact (mem_restrict_iff f (σ k) p).mpr ⟨hp_f, hfst_sk⟩

    theorem computation_uniqueness_cov (A a g : U) :
        ∀ n, n ∈ ω → ∀ f₁ f₂,
          isComputationCoV n f₁ A a g → isComputationCoV n f₂ A a g → f₁ = f₂ := by
      let S := sep (ω : U) (fun n => ∀ f₁ f₂,
        isComputationCoV n f₁ A a g → isComputationCoV n f₂ A a g → f₁ = f₂)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base n = ∅
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
          intro f₁ f₂ hf₁ hf₂
          have h_dom1 := function_domain_eq f₁ (σ (∅ : U)) A hf₁.1
          have h_dom2 := function_domain_eq f₂ (σ (∅ : U)) A hf₂.1
          apply ExtSet; intro p; constructor
          · intro hp
            have : p ∈ σ (∅ : U) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at this
            have h_is_op : isOrderedPair p := this.1
            obtain ⟨_, _, _⟩ := this
            have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
            have hx_eq : fst p = ∅ := by
              have : fst p ∈ domain f₁ := by rw [mem_domain]; exact ⟨snd p, hp_eq ▸ hp⟩
              rw [h_dom1, mem_succ_iff_local] at this
              cases this with | inl h => exact absurd h (EmptySet_is_empty _) | inr h => exact h
            rw [hx_eq] at hp_eq
            have hy_eq : snd p = a := by
              rw [← hf₁.2.1]; symm
              exact apply_eq f₁ ∅ _ (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₂.2.1]
            exact apply_mem f₂ ∅ (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
          · intro hp
            have : p ∈ σ (∅ : U) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at this
            have h_is_op : isOrderedPair p := this.1
            have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
            have hx_eq : fst p = ∅ := by
              have : fst p ∈ domain f₂ := by rw [mem_domain]; exact ⟨snd p, hp_eq ▸ hp⟩
              rw [h_dom2, mem_succ_iff_local] at this
              cases this with | inl h => exact absurd h (EmptySet_is_empty _) | inr h => exact h
            rw [hx_eq] at hp_eq
            have hy_eq : snd p = a := by
              rw [← hf₂.2.1]; symm
              exact apply_eq f₂ ∅ _ (hf₂.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₁.2.1]
            exact apply_mem f₁ ∅ (hf₁.1.2 ∅ (by rw [mem_succ_iff]; right; rfl))
        · -- Paso inductivo
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega
          intro f₁ f₂ hf₁ hf₂
          let f₁_res := restrict f₁ (σ n)
          let f₂_res := restrict f₂ (σ n)
          have h1 : isComputationCoV n f₁_res A a g :=
            restriction_is_computation_cov A a g n hn_omega f₁ hf₁
          have h2 : isComputationCoV n f₂_res A a g :=
            restriction_is_computation_cov A a g n hn_omega f₂ hf₂
          have h_eq_res : f₁_res = f₂_res := h_unique_n f₁_res f₂_res h1 h2
          have h_apply_eq : apply f₁ (σ n) = apply f₂ (σ n) :=
            calc apply f₁ (σ n)
                = apply g (restrict f₁ (σ n))  := hf₁.2.2 n (mem_succ_self n)
              _ = apply g (restrict f₂ (σ n))  := by
                    have : restrict f₁ (σ n) = restrict f₂ (σ n) := h_eq_res
                    rw [this]
              _ = apply f₂ (σ n)                   := (hf₂.2.2 n (mem_succ_self n)).symm
          apply ExtSet; intro p; constructor
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f1 : p ∈ f₁_res := (mem_restrict_iff f₁ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f2 : p ∈ f₂_res := h_eq_res ▸ hp_f1
              exact restrict_subset f₂ (σ n) p hp_f2
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₁ (fst p) :=
                (apply_eq f₁ (fst p) (snd p)
                  (hf₁.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, h_apply_eq]
              exact apply_mem f₂ (σ n) (hf₂.1.2 (σ n) (mem_succ_self (σ n)))
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f2 : p ∈ f₂_res := (mem_restrict_iff f₂ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f1 : p ∈ f₁_res := h_eq_res.symm ▸ hp_f2
              exact restrict_subset f₁ (σ n) p hp_f1
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₂ (fst p) :=
                (apply_eq f₂ (fst p) (snd p)
                  (hf₂.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, ← h_apply_eq]
              exact apply_mem f₁ (σ n) (hf₁.1.2 (σ n) (mem_succ_self (σ n)))
      intro n hn; rw [← h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    theorem computation_existence_cov (A a g : U)
        (ha : a ∈ A) (hg : IsFunction g (𝒫 (ω ×ₛ A)) A) :
        ∀ n, n ∈ ω → ∃ f, isComputationCoV n f A a g := by
      let S := sep (ω : U) (fun n => ∃ f, isComputationCoV n f A a g)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [mem_sep_iff] at hx; exact hx.1
        · -- Base n = ∅
          rw [mem_sep_iff]; constructor; exact zero_in_Omega
          let f0 := Singleton (OrderedPair (∅ : U) a)
          exact ⟨f0, ⟨fun p hp => by
            rw [Singleton_is_specified] at hp; rw [hp, OrderedPair_mem_CartesianProduct]
            exact ⟨(mem_succ_iff_local ∅ ∅).mpr (Or.inr rfl), ha⟩,
            fun x hx => by
              rw [mem_succ_iff_local] at hx
              have : x = ∅ := by cases hx with
                | inl h => exact absurd h (EmptySet_is_empty x)
                | inr h => exact h
              rw [this]
              exact ⟨a, (Singleton_is_specified _ _).mpr rfl,
                fun y hy => (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                  ((Singleton_is_specified _ _).mp hy)).2⟩⟩,
            apply_eq f0 ∅ a
              ⟨a, (Singleton_is_specified _ _).mpr rfl,
                fun y hy => (Eq_of_OrderedPairs_given_projections ∅ y ∅ a
                  ((Singleton_is_specified _ _).mp hy)).2⟩
              ((Singleton_is_specified _ _).mpr rfl),
            fun k hk => absurd hk (EmptySet_is_empty k)⟩
        · -- Paso inductivo
          intro n hn_in_S
          rw [mem_sep_iff] at hn_in_S
          obtain ⟨hn_omega, ⟨fn, hfn⟩⟩ := hn_in_S
          rw [mem_sep_iff]; constructor; exact succ_in_Omega n hn_omega
          have hn_nat    := mem_Omega_is_Nat n hn_omega
          have hσn_nat   := isNat_succ n hn_nat
          have h_dom_fn  := function_domain_eq fn (σ n) A hfn.1
          have h_sn_ni   : σ n ∉ σ n := not_mem_self (σ n) hσn_nat
          have hn_in_sn  : n ∈ σ n   := mem_succ_self n
          -- fn ∈ 𝒫(ω ×ₛ A)
          have h_fn_powerset : fn ∈ 𝒫 (ω ×ₛ A) :=
            (mem_powerset_iff _ _).mpr (fun p hp => by
              have hp_prod := hfn.1.1 p hp
              rw [CartesianProduct_is_specified] at hp_prod ⊢
              exact ⟨hp_prod.1, succ_subset_omega n hn_omega (fst p) hp_prod.2.1, hp_prod.2.2⟩)
          let val_next  := apply g fn
          let pair_next := OrderedPair (σ n) val_next
          let f_next    := fn ∪ Singleton pair_next
          have h_val_A : val_next ∈ A := by
            have h := hg.1 ⟨fn, val_next⟩ (apply_mem g fn (hg.2 fn h_fn_powerset))
            rw [OrderedPair_mem_CartesianProduct] at h; exact h.2
          -- σ n ∉ σ k for all k ∈ n
          have h_sn_not_sk : ∀ k, k ∈ n → σ n ∉ σ k := by
            intro k hk_in_n h_sn_in_sk
            have hk_nat := nat_element_is_nat n k hn_nat hk_in_n
            rw [mem_succ_iff_local] at h_sn_in_sk
            cases h_sn_in_sk with
            | inl h_sn_in_k =>
              have h_sn_in_n := mem_trans (σ n) k n hσn_nat hk_nat hn_nat h_sn_in_k hk_in_n
              exact not_mem_self n hn_nat
                (mem_trans n (σ n) n hn_nat hσn_nat hn_nat (mem_succ_self n) h_sn_in_n)
            | inr h_sn_eq_k =>
              have h_sn_in_n : σ n ∈ n := h_sn_eq_k ▸ hk_in_n
              exact not_mem_self n hn_nat
                (mem_trans n (σ n) n hn_nat hσn_nat hn_nat (mem_succ_self n) h_sn_in_n)
          -- restrict f_next (σ n) = fn
          have h_res_fn : restrict f_next (σ n) = fn := by
            apply ExtSet; intro p; constructor
            · intro hp
              obtain ⟨hp_fn_next, hfst_sn⟩ := (mem_restrict_iff f_next (σ n) p).mp hp
              rw [mem_union_iff] at hp_fn_next
              cases hp_fn_next with
              | inl h => exact h
              | inr h =>
                rw [Singleton_is_specified] at h
                rw [h, fst_of_ordered_pair] at hfst_sn
                exact absurd hfst_sn h_sn_ni
            · intro hp_fn
              have hp_prod := hfn.1.1 p hp_fn
              rw [CartesianProduct_is_specified] at hp_prod
              exact (mem_restrict_iff f_next (σ n) p).mpr
                ⟨(mem_union_iff _ _ _).mpr (Or.inl hp_fn), hp_prod.2.1⟩
          -- restrict fn (σ k) = restrict f_next (σ k) for k ∈ n
          have h_res_eq : ∀ k, k ∈ n → restrict fn (σ k) = restrict f_next (σ k) := by
            intro k hk_in_n
            apply ExtSet; intro p; constructor
            · intro hp
              obtain ⟨hp_fn, hfst_sk⟩ := (mem_restrict_iff fn (σ k) p).mp hp
              exact (mem_restrict_iff f_next (σ k) p).mpr
                ⟨(mem_union_iff _ _ _).mpr (Or.inl hp_fn), hfst_sk⟩
            · intro hp
              obtain ⟨hp_fn_next, hfst_sk⟩ := (mem_restrict_iff f_next (σ k) p).mp hp
              rw [mem_union_iff] at hp_fn_next
              cases hp_fn_next with
              | inl h => exact (mem_restrict_iff fn (σ k) p).mpr ⟨h, hfst_sk⟩
              | inr h =>
                rw [Singleton_is_specified] at h
                rw [h, fst_of_ordered_pair] at hfst_sk
                exact absurd hfst_sk (h_sn_not_sk k hk_in_n)
          have h_restrict : ∀ x, x ∈ σ n → ∃! y, ⟨x, y⟩ ∈ f_next := by
            intro x hx
            obtain ⟨y, hy, huniq⟩ := hfn.1.2 x hx
            apply ExistsUnique.intro y
            · rw [mem_union_iff]; left; exact hy
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h => exact huniq y' h
              | inr h =>
                rw [Singleton_is_specified] at h
                have heq := Eq_of_OrderedPairs_given_projections x y' (σ n) val_next h
                rw [heq.1] at hx; exact absurd hx h_sn_ni
          have h_app_fn : ∀ x, x ∈ σ n → apply f_next x = apply fn x := by
            intro x hx
            apply apply_eq f_next x (apply fn x) (h_restrict x hx)
            rw [mem_union_iff]; left
            exact apply_mem fn x (hfn.1.2 x hx)
          have h_sn_uniq : ∃! y, ⟨σ n, y⟩ ∈ f_next := by
            apply ExistsUnique.intro val_next
            · rw [mem_union_iff]; right
              exact (Singleton_is_specified _ _).mpr rfl
            · intro y' hy'
              rw [mem_union_iff] at hy'
              cases hy' with
              | inl h =>
                exact absurd (h_dom_fn ▸ (mem_domain fn (σ n)).mpr ⟨y', h⟩) h_sn_ni
              | inr h =>
                exact (Eq_of_OrderedPairs_given_projections (σ n) y' (σ n) val_next
                  ((Singleton_is_specified _ _).mp h)).2
          exact ⟨f_next,
            ⟨fun p hp => by
              rw [mem_union_iff] at hp
              cases hp with
              | inl h =>
                have hp_prod := hfn.1.1 p h
                rw [CartesianProduct_is_specified] at hp_prod ⊢
                exact ⟨hp_prod.1,
                  (mem_succ_iff_local (σ n) (fst p)).mpr (Or.inl hp_prod.2.1), hp_prod.2.2⟩
              | inr h =>
                rw [Singleton_is_specified] at h; rw [h]
                exact (OrderedPair_mem_CartesianProduct (σ n) val_next (σ (σ n)) A).mpr
                  ⟨(mem_succ_iff_local (σ n) (σ n)).mpr (Or.inr rfl), h_val_A⟩,
            fun x hx => by
              rw [mem_succ_iff_local] at hx
              cases hx with
              | inl h => exact h_restrict x h
              | inr h => rw [h]; exact h_sn_uniq⟩,
            by
              have h0 : (∅ : U) ∈ σ n := zero_in_succ_nat n hn_omega
              apply apply_eq f_next ∅ a (h_restrict ∅ h0)
              rw [mem_union_iff]; left
              have := apply_mem fn ∅ (hfn.1.2 ∅ h0); rwa [hfn.2.1] at this,
            fun k hk => by
              rw [mem_succ_iff_local] at hk
              cases hk with
              | inl hk_in_n =>
                have hk_nat  := nat_element_is_nat n k hn_nat hk_in_n
                have hk_sn   := subset_succ_local n k hk_in_n
                have hsk_sn  := succ_mem_succ_of_mem k n hk_nat hn_nat hk_in_n
                rw [h_app_fn (σ k) hsk_sn, ← h_res_eq k hk_in_n]
                exact hfn.2.2 k hk_in_n
              | inr hk_eq_n =>
                rw [hk_eq_n,
                  apply_eq f_next (σ n) val_next h_sn_uniq
                    ((mem_union_iff _ _ _).mpr (Or.inr ((Singleton_is_specified _ _).mpr rfl))),
                  h_res_fn]⟩
      intro n hn; rw [← h_ind] at hn; rw [mem_sep_iff] at hn; exact hn.2

    noncomputable def RecursionComputationsCoV (A a g : U) : U :=
      sep (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputationCoV n f A a g))

    theorem computations_are_compatible_cov (A a g : U) :
        isCompatibleSystem (RecursionComputationsCoV A a g) := by
      intro f₁ f₂ hf₁_in hf₂_in
      unfold RecursionComputationsCoV at hf₁_in hf₂_in
      rw [mem_sep_iff] at hf₁_in hf₂_in
      obtain ⟨_, n₁, hn₁_omega, hf₁⟩ := hf₁_in
      obtain ⟨_, n₂, hn₂_omega, hf₂⟩ := hf₂_in
      have hn₁_nat := mem_Omega_is_Nat n₁ hn₁_omega
      have hn₂_nat := mem_Omega_is_Nat n₂ hn₂_omega
      intro x hx
      rw [mem_inter_iff] at hx
      obtain ⟨hx_dom1, hx_dom2⟩ := hx
      rcases trichotomy n₁ n₂ hn₁_nat hn₂_nat with h | h | h
      · have hf₂_res := restriction_computation_general_cov A a g n₁ n₂ hn₁_omega hn₂_nat h f₂ hf₂
        have h_eq := computation_uniqueness_cov A a g n₁ hn₁_omega f₁ _ hf₁ hf₂_res
        have hx_in : x ∈ σ n₁ := by rwa [← function_domain_eq f₁ (σ n₁) A hf₁.1]
        calc apply f₁ x = apply (restrict f₂ (σ n₁)) x := by rw [h_eq]
          _ = apply f₂ x := restrict_apply f₂ (σ n₁) x hx_in
      · have h_eq : f₁ = f₂ :=
          computation_uniqueness_cov A a g n₁ hn₁_omega f₁ f₂ hf₁ (h ▸ hf₂)
        rw [h_eq]
      · have hf₁_res := restriction_computation_general_cov A a g n₂ n₁ hn₂_omega hn₁_nat h f₁ hf₁
        have h_eq := computation_uniqueness_cov A a g n₂ hn₂_omega f₂ _ hf₂ hf₁_res
        have hx_in : x ∈ σ n₂ := by rwa [← function_domain_eq f₂ (σ n₂) A hf₂.1]
        calc apply f₁ x = apply (restrict f₁ (σ n₂)) x := (restrict_apply f₁ (σ n₂) x hx_in).symm
          _ = apply f₂ x := by rw [← h_eq]

    /-- Teorema de Recursión por Valores Acumulados: F(σ n) = g(F ↾ (σ n)) con g : 𝒫(ω ×ₛ A) → A -/
    theorem RecursionCourseOfValues (A a g : U)
        (ha : a ∈ A) (hg : IsFunction g (𝒫 (ω ×ₛ A)) A) :
        ∃! F, IsFunction F ω A ∧
              (apply F (∅ : U) = a) ∧
              (∀ n, n ∈ ω → apply F (σ n) = apply g (restrict F (σ n))) := by
      let Comps := RecursionComputationsCoV A a g
      let F := ⋃ Comps
      have h_mem_Comps : ∀ n f, n ∈ ω → isComputationCoV n f A a g → f ∈ Comps := fun n f hn hf =>
        (mem_sep_iff _ _ _).mpr ⟨(mem_powerset_iff _ _).mpr (fun p hp => by
          have hp_in : p ∈ σ n ×ₛ A := hf.1.1 p hp
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩), n, hn, hf⟩
      have h_sv : IsSingleValued F :=
        union_compatible_is_function Comps
          (fun f hf => by
            obtain ⟨_, n, _, hf_c⟩ := (mem_sep_iff _ _ _).mp hf
            exact ⟨σ n, A, hf_c.1⟩)
          (computations_are_compatible_cov A a g)
      have h_F_func : IsFunction F ω A := by
        constructor
        · intro p hp
          rw [mem_sUnion_iff] at hp
          obtain ⟨f, hf_in, hp_f⟩ := hp
          obtain ⟨_, n, hn, hf_c⟩ := (mem_sep_iff _ _ _).mp hf_in
          have hp_in : p ∈ σ n ×ₛ A := hf_c.1.1 p hp_f
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩
        · intro x hx
          obtain ⟨fx, hfx⟩ := computation_existence_cov A a g ha hg x hx
          have h_pair : ⟨x, apply fx x⟩ ∈ F := by
            rw [mem_sUnion_iff]
            exact ⟨fx, h_mem_Comps x fx hx hfx, apply_mem fx x (hfx.1.2 x (mem_succ_self x))⟩
          exact ⟨apply fx x, h_pair, fun y hy => (h_sv x (apply fx x) y h_pair hy).symm⟩
      have h_F_zero : apply F (∅ : U) = a := by
        obtain ⟨f₀, hf₀⟩ := computation_existence_cov A a g ha hg ∅ zero_in_Omega
        have h_pair : ⟨(∅ : U), a⟩ ∈ F := by
          rw [mem_sUnion_iff]
          exact ⟨f₀, h_mem_Comps ∅ f₀ zero_in_Omega hf₀, by
            have := apply_mem f₀ ∅ (hf₀.1.2 ∅ (mem_succ_self ∅))
            rwa [hf₀.2.1] at this⟩
        exact apply_eq F ∅ a (h_F_func.2 ∅ zero_in_Omega) h_pair
      have h_F_step : ∀ n, n ∈ ω → apply F (σ n) = apply g (restrict F (σ n)) := by
        intro n hn
        obtain ⟨fsn, hfsn⟩ := computation_existence_cov A a g ha hg (σ n) (succ_in_Omega n hn)
        have h_sn_in_ssn : σ n ∈ σ (σ n) := mem_succ_self (σ n)
        have h_sn_F : ⟨σ n, apply fsn (σ n)⟩ ∈ F :=
          (mem_sUnion_iff _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
            apply_mem fsn (σ n) (hfsn.1.2 (σ n) h_sn_in_ssn)⟩
        have h_agree_sn : ∀ x, x ∈ σ n → apply fsn x = apply F x := by
          intro x hx
          have h_x_ssn := subset_succ_local (σ n) x hx
          have h_x_ω   := succ_subset_omega n hn x hx
          have h_x_F : ⟨x, apply fsn x⟩ ∈ F :=
            (mem_sUnion_iff _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
              apply_mem fsn x (hfsn.1.2 x h_x_ssn)⟩
          exact (apply_eq F x _ (h_F_func.2 x h_x_ω) h_x_F).symm
        have h_res_eq : restrict fsn (σ n) = restrict F (σ n) := by
          apply ExtSet; intro p; constructor
          · intro hp
            obtain ⟨hp_fsn, hfst_sn⟩ := (mem_restrict_iff fsn (σ n) p).mp hp
            have hp_prod := hfsn.1.1 p hp_fsn
            rw [CartesianProduct_is_specified] at hp_prod
            have hp_eq := OrderedPairSet_is_WellConstructed p hp_prod.1
            have h_snd_eq : snd p = apply fsn (fst p) :=
              (apply_eq fsn (fst p) (snd p) (hfsn.1.2 (fst p) (subset_succ_local (σ n) (fst p) hfst_sn))
                (hp_eq ▸ hp_fsn)).symm
            exact (mem_restrict_iff F (σ n) p).mpr ⟨by
              rw [hp_eq, h_snd_eq, h_agree_sn (fst p) hfst_sn]
              exact apply_mem F (fst p) (h_F_func.2 (fst p) (succ_subset_omega n hn (fst p) hfst_sn)),
              hfst_sn⟩
          · intro hp
            obtain ⟨hp_F, hfst_sn⟩ := (mem_restrict_iff F (σ n) p).mp hp
            have hp_prod := h_F_func.1 p hp_F
            rw [CartesianProduct_is_specified] at hp_prod
            have hp_eq := OrderedPairSet_is_WellConstructed p hp_prod.1
            have h_snd_eq : snd p = apply F (fst p) :=
              (apply_eq F (fst p) (snd p) (h_F_func.2 (fst p) hp_prod.2.1) (hp_eq ▸ hp_F)).symm
            exact (mem_restrict_iff fsn (σ n) p).mpr ⟨by
              rw [hp_eq, h_snd_eq, ← h_agree_sn (fst p) hfst_sn]
              exact apply_mem fsn (fst p) (hfsn.1.2 (fst p) (subset_succ_local (σ n) (fst p) hfst_sn)),
              hfst_sn⟩
        rw [apply_eq F (σ n) _ (h_F_func.2 (σ n) (succ_in_Omega n hn)) h_sn_F,
            hfsn.2.2 n (mem_succ_self n), h_res_eq]
      apply ExistsUnique.intro F
      · exact ⟨h_F_func, h_F_zero, h_F_step⟩
      · intro G hG
        obtain ⟨hG_func, hG_zero, hG_step⟩ := hG
        -- restrict G (σ n) es un cómputo CoV de longitud n
        have h_Gn_is_cov : ∀ n, n ∈ ω → isComputationCoV n (restrict G (σ n)) A a g := by
          intro n hn
          have hn_nat := mem_Omega_is_Nat n hn
          refine ⟨restrict_is_function G ω A (σ n) hG_func (succ_subset_omega n hn), ?_, ?_⟩
          · rw [restrict_apply G (σ n) ∅ (zero_in_succ_nat n hn)]; exact hG_zero
          · intro k hk
            have hk_nat     := nat_element_is_nat n k hn_nat hk
            have hk_sn      := subset_succ_local n k hk
            have hsk_sn     := succ_mem_succ_of_mem k n hk_nat hn_nat hk
            have h_sk_sub   := succ_subset_succ_of_mem k n hn_nat hk
            rw [restrict_apply G (σ n) (σ k) hsk_sn,
                hG_step k (succ_subset_omega n hn k hk_sn)]
            congr 1
            apply ExtSet; intro p; constructor
            · intro hp
              obtain ⟨hp_G, hfst_sk⟩ := (mem_restrict_iff G (σ k) p).mp hp
              exact (mem_restrict_iff (restrict G (σ n)) (σ k) p).mpr
                ⟨(mem_restrict_iff G (σ n) p).mpr ⟨hp_G, h_sk_sub (fst p) hfst_sk⟩, hfst_sk⟩
            · intro hp
              obtain ⟨hp_res, hfst_sk⟩ := (mem_restrict_iff (restrict G (σ n)) (σ k) p).mp hp
              obtain ⟨hp_G, _⟩ := (mem_restrict_iff G (σ n) p).mp hp_res
              exact (mem_restrict_iff G (σ k) p).mpr ⟨hp_G, hfst_sk⟩
        -- restrict F (σ n) es un cómputo CoV de longitud n
        have h_Fn_is_cov : ∀ n, n ∈ ω → isComputationCoV n (restrict F (σ n)) A a g := by
          intro n hn
          have hn_nat := mem_Omega_is_Nat n hn
          refine ⟨restrict_is_function F ω A (σ n) h_F_func (succ_subset_omega n hn), ?_, ?_⟩
          · rw [restrict_apply F (σ n) ∅ (zero_in_succ_nat n hn)]; exact h_F_zero
          · intro k hk
            have hk_nat     := nat_element_is_nat n k hn_nat hk
            have hk_sn      := subset_succ_local n k hk
            have hsk_sn     := succ_mem_succ_of_mem k n hk_nat hn_nat hk
            have h_sk_sub   := succ_subset_succ_of_mem k n hn_nat hk
            rw [restrict_apply F (σ n) (σ k) hsk_sn,
                h_F_step k (succ_subset_omega n hn k hk_sn)]
            congr 1
            apply ExtSet; intro p; constructor
            · intro hp
              obtain ⟨hp_F, hfst_sk⟩ := (mem_restrict_iff F (σ k) p).mp hp
              exact (mem_restrict_iff (restrict F (σ n)) (σ k) p).mpr
                ⟨(mem_restrict_iff F (σ n) p).mpr ⟨hp_F, h_sk_sub (fst p) hfst_sk⟩, hfst_sk⟩
            · intro hp
              obtain ⟨hp_res, hfst_sk⟩ := (mem_restrict_iff (restrict F (σ n)) (σ k) p).mp hp
              obtain ⟨hp_F, _⟩ := (mem_restrict_iff F (σ n) p).mp hp_res
              exact (mem_restrict_iff F (σ k) p).mpr ⟨hp_F, hfst_sk⟩
        -- Por unicidad CoV, restrict G (σ n) = restrict F (σ n)
        have h_agree_res : ∀ n, n ∈ ω → restrict G (σ n) = restrict F (σ n) := fun n hn =>
          computation_uniqueness_cov A a g n hn _ _ (h_Gn_is_cov n hn) (h_Fn_is_cov n hn)
        -- En particular, apply G n = apply F n
        have h_agree : ∀ n, n ∈ ω → apply G n = apply F n := fun n hn => by
          rw [← restrict_apply G (σ n) n (mem_succ_self n),
              h_agree_res n hn,
              restrict_apply F (σ n) n (mem_succ_self n)]
        apply ExtSet; intro p; constructor
        · intro hp
          have hp_prod := hG_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_op, h_fst_ω, _⟩ := hp_prod
          have hp_eq := OrderedPairSet_is_WellConstructed p h_op
          have h_snd : snd p = apply F (fst p) := by
            have := apply_eq G (fst p) (snd p) (hG_func.2 (fst p) h_fst_ω) (hp_eq ▸ hp)
            rw [h_agree (fst p) h_fst_ω] at this; exact this.symm
          rw [hp_eq, h_snd]; exact apply_mem F (fst p) (h_F_func.2 (fst p) h_fst_ω)
        · intro hp
          have hp_prod := h_F_func.1 p hp
          rw [CartesianProduct_is_specified] at hp_prod
          obtain ⟨h_op, h_fst_ω, _⟩ := hp_prod
          have hp_eq := OrderedPairSet_is_WellConstructed p h_op
          have h_snd : snd p = apply G (fst p) := by
            have := apply_eq F (fst p) (snd p) (h_F_func.2 (fst p) h_fst_ω) (hp_eq ▸ hp)
            rw [← h_agree (fst p) h_fst_ω] at this; exact this.symm
          rw [hp_eq, h_snd]; exact apply_mem G (fst p) (hG_func.2 (fst p) h_fst_ω)

    /-! ============================================================ -/
    /-! ### 9. INTERFAZ OPERACIONAL ### -/
    /-! ============================================================ -/

    /-- La función recursiva definida por a y g, extraída del ∃! de RecursionTheorem -/
    noncomputable def RecursiveFn (A a g : U)
        (ha : a ∈ A) (hg : IsFunction g A A) : U :=
      Classical.choose (ExistsUnique.exists (RecursionTheorem A a g ha hg))

    theorem RecursiveFn_is_function (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A) :
        IsFunction (RecursiveFn A a g ha hg) ω A :=
      (Classical.choose_spec (ExistsUnique.exists (RecursionTheorem A a g ha hg))).1

    theorem RecursiveFn_zero (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A) :
        apply (RecursiveFn A a g ha hg) (∅ : U) = a :=
      (Classical.choose_spec (ExistsUnique.exists (RecursionTheorem A a g ha hg))).2.1

    theorem RecursiveFn_succ (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A)
        (n : U) (hn : n ∈ ω) :
        apply (RecursiveFn A a g ha hg) (σ n) = apply g (apply (RecursiveFn A a g ha hg) n) :=
      (Classical.choose_spec (ExistsUnique.exists (RecursionTheorem A a g ha hg))).2.2 n hn

    theorem RecursiveFn_unique (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A)
        (G : U) (hG_func : IsFunction G ω A) (hG_zero : apply G (∅ : U) = a)
        (hG_succ : ∀ n, n ∈ ω → apply G (σ n) = apply g (apply G n)) :
        G = RecursiveFn A a g ha hg := by
      have hG_prop : IsFunction G ω A ∧ apply G (∅ : U) = a ∧
                     ∀ n, n ∈ ω → apply G (σ n) = apply g (apply G n) :=
        ⟨hG_func, hG_zero, hG_succ⟩
      have hRF_prop := Classical.choose_spec (ExistsUnique.exists (RecursionTheorem A a g ha hg))
      obtain ⟨F, _, hF_unique⟩ := RecursionTheorem A a g ha hg
      have hRF_eq_F : RecursiveFn A a g ha hg = F := by
        unfold RecursiveFn; exact hF_unique _ hRF_prop
      rw [hRF_eq_F]
      exact hF_unique G hG_prop

  end Induction.Recursion

  export Induction.Recursion (
    -- Auxiliary lemmas
    function_domain_eq
    mem_succ_iff_local
    subset_succ_local
    zero_in_succ_nat
    succ_mem_succ_of_mem
    -- Computation (standard recursion)
    isComputation
    restriction_is_computation
    computation_uniqueness
    areCompatible
    isCompatibleSystem
    union_compatible_is_function
    computation_existence
    succ_subset_omega
    computation_subset_omega_times_A
    succ_subset_succ_of_mem
    restriction_computation_general
    RecursionComputations
    computations_are_compatible
    RecursionTheorem
    -- Computation (step-indexed variant)
    isComputationStep
    restriction_is_computation_step
    restriction_computation_general_step
    computation_uniqueness_step
    computation_existence_step
    RecursionComputationsStep
    computations_are_compatible_step
    RecursionTheoremWithStep
    -- Computation (course-of-values variant)
    isComputationCoV
    restriction_is_computation_cov
    restriction_computation_general_cov
    computation_uniqueness_cov
    computation_existence_cov
    RecursionComputationsCoV
    computations_are_compatible_cov
    RecursionCourseOfValues
    -- Canonical recursive function
    RecursiveFn
    RecursiveFn_is_function
    RecursiveFn_zero
    RecursiveFn_succ
    RecursiveFn_unique
  )

end ZFC

export ZFC.Induction.Recursion (
  isComputation
  computation_uniqueness
  areCompatible
  union_compatible_is_function
  computation_existence
  RecursionComputations
  succ_subset_omega
  computation_subset_omega_times_A
  succ_subset_succ_of_mem
  restriction_computation_general
  computations_are_compatible
  RecursionTheorem
  isComputationStep
  restriction_is_computation_step
  restriction_computation_general_step
  computation_uniqueness_step
  computation_existence_step
  RecursionComputationsStep
  computations_are_compatible_step
  RecursionTheoremWithStep
  isComputationCoV
  restriction_is_computation_cov
  restriction_computation_general_cov
  computation_uniqueness_cov
  computation_existence_cov
  RecursionComputationsCoV
  computations_are_compatible_cov
  RecursionCourseOfValues
  RecursiveFn
  RecursiveFn_is_function
  RecursiveFn_zero
  RecursiveFn_succ
  RecursiveFn_unique
)
