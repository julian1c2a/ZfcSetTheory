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
      by_cases h : n = ∅
      · right; rw [h]
      · left; exact zero_mem_of_nat_nonempty n hn_nat h

    /-- Si k ∈ n (ambos naturales), entonces σ k ∈ σ n -/
    theorem succ_mem_succ_of_mem (k n : U) (hk_nat : isNat k) (hn_nat : isNat n)
        (hk : k ∈ n) : σ k ∈ σ n := by
      rw [mem_succ_iff_local]
      exact nat_subset_mem_or_eq (σ k) n (nat_successor_is_nat k hk_nat) hn_nat
        (no_nat_between k n hk_nat hn_nat hk)

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
          have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn
          rw [Restriction_apply f (σ n) (∅ : U) h_zero_in]
          exact hf.2.1
        · -- Paso recursivo
          intro k hk
          -- Necesitamos k ∈ σ n y σ k ∈ σ n para usar Restriction_apply
          have hn_nat : isNat n := mem_Omega_is_Nat n hn
          have hk_nat : isNat k := nat_element_is_nat n k hn_nat hk
          have h_k_in : k ∈ σ n := subset_succ_local n k hk
          have h_sk_in : σ k ∈ σ n := succ_mem_succ_of_mem k n hk_nat hn_nat hk

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
    theorem computation_uniqueness (A : U) (a : U) (g : U) :
      ∀ n, n ∈ ω → ∀ f₁ f₂,
        isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂
        := by

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
                = apply g (apply f₁ n)       := hf₁.2.2 n (mem_successor_self n)
              _ = apply g (apply f₁_res n)   := by rw [← Restriction_apply f₁ (σ n) n (mem_successor_self n)]
              _ = apply g (apply f₂_res n)   := by rw [h_eq_res]
              _ = apply g (apply f₂ n)       := by rw [Restriction_apply f₂ (σ n) n (mem_successor_self n)]
              _ = apply f₂ (σ n)             := (hf₂.2.2 n (mem_successor_self n)).symm
          constructor
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_in_f1res : p ∈ f₁_res :=
                (Restriction_is_specified f₁ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_in_f2res : p ∈ f₂_res := h_eq_res ▸ hp_in_f1res
              exact Restriction_subset f₂ (σ n) p hp_in_f2res
            | inr h_eq_sn =>
              have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
              have h_uniq1 : ∃! y, ⟨fst p, y⟩ ∈ f₁ :=
                hf₁.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn)
              have h_snd_eq : snd p = apply f₁ (fst p) :=
                (apply_eq f₁ (fst p) (snd p) h_uniq1 (by rw [← hp_eq]; exact hp)).symm
              rw [hp_eq, h_snd_eq, h_eq_sn, h_apply_eq]
              exact apply_mem f₂ (σ n) (hf₂.1.2 (σ n) (mem_successor_self (σ n)))
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_in_f2res : p ∈ f₂_res :=
                (Restriction_is_specified f₂ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_in_f1res : p ∈ f₁_res := h_eq_res.symm ▸ hp_in_f2res
              exact Restriction_subset f₁ (σ n) p hp_in_f1res
            | inr h_eq_sn =>
              have hp_eq : p = ⟨fst p, snd p⟩ := OrderedPairSet_is_WellConstructed p h_is_op
              have h_uniq2 : ∃! y, ⟨fst p, y⟩ ∈ f₂ :=
                hf₂.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn)
              have h_snd_eq : snd p = apply f₂ (fst p) :=
                (apply_eq f₂ (fst p) (snd p) h_uniq2 (by rw [← hp_eq]; exact hp)).symm
              rw [hp_eq, h_snd_eq, h_eq_sn, ← h_apply_eq]
              exact apply_mem f₁ (σ n) (hf₁.1.2 (σ n) (mem_successor_self (σ n)))

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

    /-- La unión de un sistema compatible de funciones es monovaluada -/
    theorem union_compatible_is_function (F : U)
      (h_funcs : ∀ f, f ∈ F → ∃ A B, isFunctionFromTo f A B)
      (h_compat : isCompatibleSystem F) :
      isSingleValued (⋃ F) := by
      intro x y₁ y₂ hy₁ hy₂
      rw [UnionSet_is_specified] at hy₁ hy₂
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
        (BinInter_is_specified (domain f) (domain g) x).mpr ⟨hx_dom_f, hx_dom_g⟩
      have h_apply_eq := h_compat f g hf_in_F hg_in_F x hx_inter
      -- y₁ = apply f x = apply g x = y₂
      calc y₁ = apply f x := (apply_eq f x y₁ h_uniq_f hpair1).symm
        _ = apply g x    := h_apply_eq
        _ = y₂           := apply_eq g x y₂ h_uniq_g hpair2

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
          have hn_nat : isNat n := mem_Omega_is_Nat n hn_omega
          have hσn_nat : isNat (σ n) := nat_successor_is_nat n hn_nat
          have h_dom_fn : domain fn = σ n := function_domain_eq fn (σ n) A hfn.1
          have h_sn_notin : σ n ∉ σ n := nat_not_mem_self (σ n) hσn_nat
          have hn_in_sn : n ∈ σ n := mem_successor_self n
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
            · rw [BinUnion_is_specified]; left; exact hy
            · intro y' hy'
              rw [BinUnion_is_specified] at hy'
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
            rw [BinUnion_is_specified]; left
            exact apply_mem fn x (hfn.1.2 x hx)
          -- ∃! y, ⟨σ n, y⟩ ∈ f_next
          have h_sn_uniq : ∃! y, ⟨σ n, y⟩ ∈ f_next := by
            apply ExistsUnique.intro val_next
            · rw [BinUnion_is_specified]; right
              exact (Singleton_is_specified _ _).mpr rfl
            · intro y' hy'
              rw [BinUnion_is_specified] at hy'
              cases hy' with
              | inl h =>
                have hx_in_dom : σ n ∈ domain fn := (mem_domain fn (σ n)).mpr ⟨y', h⟩
                rw [h_dom_fn] at hx_in_dom
                exact absurd hx_in_dom h_sn_notin
              | inr h =>
                rw [Singleton_is_specified] at h
                exact (Eq_of_OrderedPairs_given_projections (σ n) y' (σ n) val_next h).2
          constructor
          · -- 1. isFunctionFromTo f_next (σ (σ n)) A
            constructor
            · -- f_next ⊆ σ(σ n) ×ₛ A
              intro p hp
              rw [BinUnion_is_specified] at hp
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
              rw [BinUnion_is_specified]; left
              have := apply_mem fn ∅ (hfn.1.2 ∅ h_zero_in)
              rwa [hfn.2.1] at this
            · -- 3. ∀ k ∈ σ n, apply f_next (σ k) = apply g (apply f_next k)
              intro k hk
              rw [mem_succ_iff_local] at hk
              cases hk with
              | inl hk_in_n =>
                have hk_nat : isNat k := nat_element_is_nat n k hn_nat hk_in_n
                have hk_in_sn : k ∈ σ n := subset_succ_local n k hk_in_n
                have hsk_in_sn : σ k ∈ σ n := succ_mem_succ_of_mem k n hk_nat hn_nat hk_in_n
                rw [h_apply_fn (σ k) hsk_in_sn, h_apply_fn k hk_in_sn]
                exact hfn.2.2 k hk_in_n
              | inr hk_eq_n =>
                rw [hk_eq_n]
                have h_apply_sn : apply f_next (σ n) = val_next :=
                  apply_eq f_next (σ n) val_next h_sn_uniq
                    ((BinUnion_is_specified fn (Singleton pair_next) ⟨σ n, val_next⟩).mpr
                      (Or.inr ((Singleton_is_specified _ _).mpr rfl)))
                rw [h_apply_sn, h_apply_fn n hn_in_sn]

      intro n hn; rw [←h_ind] at hn; rw [SpecSet_is_specified] at hn; exact hn.2

    /-! ============================================================ -/
    /-! ### 5. TEOREMA DE RECURSIÓN (GLOBAL) ### -/
    /-! ============================================================ -/

    /-- El conjunto de todos los cómputos válidos -/
    noncomputable def RecursionComputations (A a g : U) : U :=
      SpecSet (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputation n f A a g))

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
