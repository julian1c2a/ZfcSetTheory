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
    theorem succ_subset_succ_of_mem (n₁ n₂ : U) (hn₂_nat : isNat n₂) (h : n₁ ∈ n₂) :
        σ n₁ ⊆ σ n₂ := by
      have hn₂_trans : isTransitiveSet n₂ := hn₂_nat.1
      have hn₁_sub : n₁ ⊆ n₂ := transitive_element_subset n₂ n₁ hn₂_trans h
      intro x hx
      rw [mem_succ_iff_local] at hx ⊢
      cases hx with
      | inl hx_in_n₁ => left; exact hn₁_sub x hx_in_n₁
      | inr hx_eq_n₁ => left; rw [hx_eq_n₁]; exact h

    /-- Restricción general: cómputo de longitud n₂ restringido a σ n₁ es cómputo de longitud n₁ -/
    theorem restriction_computation_general (A a g n₁ n₂ : U)
        (hn₁ : n₁ ∈ ω) (hn₂_nat : isNat n₂) (hlt : n₁ ∈ n₂)
        (f : U) (hf : isComputation n₂ f A a g) :
        isComputation n₁ (Restriction f (σ n₁)) A a g := by
      have h_sn₁_sub : σ n₁ ⊆ σ n₂ := succ_subset_succ_of_mem n₁ n₂ hn₂_nat hlt
      constructor
      · exact Restriction_is_function f (σ n₂) A (σ n₁) hf.1 h_sn₁_sub
      · constructor
        · have h_zero_in : (∅ : U) ∈ σ n₁ := zero_in_succ_nat n₁ hn₁
          rw [Restriction_apply f (σ n₁) ∅ h_zero_in]
          exact hf.2.1
        · intro k hk
          have hn₁_nat : isNat n₁ := mem_Omega_is_Nat n₁ hn₁
          have hk_nat : isNat k := nat_element_is_nat n₁ k hn₁_nat hk
          have hk_in_sn₁ : k ∈ σ n₁ := subset_succ_local n₁ k hk
          have hsk_in_sn₁ : σ k ∈ σ n₁ := succ_mem_succ_of_mem k n₁ hk_nat hn₁_nat hk
          rw [Restriction_apply f (σ n₁) (σ k) hsk_in_sn₁]
          rw [Restriction_apply f (σ n₁) k hk_in_sn₁]
          exact hf.2.2 k (nat_mem_trans k n₁ n₂ hk_nat hn₁_nat hn₂_nat hk hlt)

    /-- El conjunto de todos los cómputos válidos -/
    noncomputable def RecursionComputations (A a g : U) : U :=
      SpecSet (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputation n f A a g))

    /-- Los cómputos en RecursionComputations son compatibles a pares -/
    theorem computations_are_compatible (A a g : U) :
        isCompatibleSystem (RecursionComputations A a g) := by
      intro f₁ f₂ hf₁_in hf₂_in
      unfold RecursionComputations at hf₁_in hf₂_in
      rw [SpecSet_is_specified] at hf₁_in hf₂_in
      obtain ⟨_, n₁, hn₁_omega, hf₁⟩ := hf₁_in
      obtain ⟨_, n₂, hn₂_omega, hf₂⟩ := hf₂_in
      have hn₁_nat : isNat n₁ := mem_Omega_is_Nat n₁ hn₁_omega
      have hn₂_nat : isNat n₂ := mem_Omega_is_Nat n₂ hn₂_omega
      intro x hx
      rw [BinInter_is_specified] at hx
      obtain ⟨hx_dom1, hx_dom2⟩ := hx
      -- Por tricotomía sobre n₁ y n₂
      rcases nat_trichotomy n₁ n₂ hn₁_nat hn₂_nat with h | h | h
      · -- n₁ ∈ n₂: f₂ restringida a σ n₁ es cómputo de longitud n₁
        have hf₂_res : isComputation n₁ (Restriction f₂ (σ n₁)) A a g :=
          restriction_computation_general A a g n₁ n₂ hn₁_omega hn₂_nat h f₂ hf₂
        have h_eq : f₁ = Restriction f₂ (σ n₁) :=
          computation_uniqueness A a g n₁ hn₁_omega f₁ (Restriction f₂ (σ n₁)) hf₁ hf₂_res
        -- x ∈ domain f₁ = σ n₁
        have hx_in_sn₁ : x ∈ σ n₁ := by
          rwa [← function_domain_eq f₁ (σ n₁) A hf₁.1]
        calc apply f₁ x
            = apply (Restriction f₂ (σ n₁)) x := by rw [h_eq]
          _ = apply f₂ x                       := Restriction_apply f₂ (σ n₁) x hx_in_sn₁
      · -- n₁ = n₂: por unicidad f₁ = f₂
        have h_eq : f₁ = f₂ :=
          computation_uniqueness A a g n₁ hn₁_omega f₁ f₂ hf₁ (h ▸ hf₂)
        rw [h_eq]
      · -- n₂ ∈ n₁: simétrico
        have hf₁_res : isComputation n₂ (Restriction f₁ (σ n₂)) A a g :=
          restriction_computation_general A a g n₂ n₁ hn₂_omega hn₁_nat h f₁ hf₁
        have h_eq : f₂ = Restriction f₁ (σ n₂) :=
          computation_uniqueness A a g n₂ hn₂_omega f₂ (Restriction f₁ (σ n₂)) hf₂ hf₁_res
        have hx_in_sn₂ : x ∈ σ n₂ := by
          rwa [← function_domain_eq f₂ (σ n₂) A hf₂.1]
        calc apply f₁ x
            = apply (Restriction f₁ (σ n₂)) x := (Restriction_apply f₁ (σ n₂) x hx_in_sn₂).symm
          _ = apply f₂ x                       := by rw [← h_eq]

    /-! ============================================================ -/
    /-! ### 6. TEOREMA DE RECURSIÓN (GLOBAL) ### -/
    /-! ============================================================ -/

    theorem RecursionTheorem (A : U) (a : U) (g : U)
      (ha : a ∈ A) (hg : isFunctionFromTo g A A) :
      ∃! F, isFunctionFromTo F ω A ∧
            (apply F (∅ : U) = a) ∧
            (∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) := by

      let Comps := RecursionComputations A a g
      let F := (⋃ Comps)

      -- Paso 1: F es función (usando lemas de compatibilidad)
      -- Paso 2: Dominio de F es ω (porque ∀ n, n ∈ dom(f_n) ⊆ dom(F))
      -- Paso 3: F cumple las ecuaciones (heredado de los f_n)

      -- Lema local: meter un cómputo en Comps (usando SpecSet_is_specified directamente)
      have h_mem_Comps : ∀ n f, n ∈ ω → isComputation n f A a g → f ∈ Comps := by
        intro n f hn hf
        exact (SpecSet_is_specified _ _ _).mpr
          ⟨(PowerSet_is_specified _ _).mpr (computation_subset_omega_times_A A a g n hn f hf),
           n, hn, hf⟩

      -- F es monovaluada (por compatibilidad de los cómputos)
      have h_sv : isSingleValued F :=
        union_compatible_is_function Comps
          (fun f hf => by
            obtain ⟨_, n, _, hf_comp⟩ := (SpecSet_is_specified _ _ _).mp hf
            exact ⟨σ n, A, hf_comp.1⟩)
          (computations_are_compatible A a g)

      -- F es función de ω a A
      have h_F_func : isFunctionFromTo F ω A := by
        constructor
        · -- F ⊆ ω ×ₛ A
          intro p hp
          rw [UnionSet_is_specified] at hp
          obtain ⟨f, hf_in, hp_in_f⟩ := hp
          obtain ⟨_, n, hn, hf_comp⟩ := (SpecSet_is_specified _ _ _).mp hf_in
          exact computation_subset_omega_times_A A a g n hn f hf_comp p hp_in_f
        · -- ∀ x ∈ ω, ∃! y, ⟨x, y⟩ ∈ F
          intro x hx
          obtain ⟨fx, hfx⟩ := computation_existence A a g ha hg x hx
          have h_pair_in_F : ⟨x, apply fx x⟩ ∈ F := by
            rw [UnionSet_is_specified]
            exact ⟨fx, h_mem_Comps x fx hx hfx,
                   apply_mem fx x (hfx.1.2 x (mem_successor_self x))⟩
          exact ExistsUnique.intro (apply fx x) h_pair_in_F
            (fun y hy => (h_sv x (apply fx x) y h_pair_in_F hy).symm)

      -- Propiedades de F (extraídas para usarlas en unicidad)
      have h_F_zero : apply F (∅ : U) = a := by
        obtain ⟨f₀, hf₀⟩ := computation_existence A a g ha hg ∅ zero_in_Omega
        have h_pair_in_f₀ : ⟨(∅ : U), a⟩ ∈ f₀ := by
          have := apply_mem f₀ ∅ (hf₀.1.2 ∅ (mem_successor_self ∅))
          rwa [hf₀.2.1] at this
        have h_pair_in_F : ⟨(∅ : U), a⟩ ∈ F := by
          rw [UnionSet_is_specified]
          exact ⟨f₀, h_mem_Comps ∅ f₀ zero_in_Omega hf₀, h_pair_in_f₀⟩
        exact apply_eq F ∅ a (h_F_func.2 ∅ zero_in_Omega) h_pair_in_F

      have h_F_step : ∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n) := by
        intro n hn
        obtain ⟨fsn, hfsn⟩ := computation_existence A a g ha hg (σ n) (succ_in_Omega n hn)
        have h_n_in_ssn : n ∈ σ (σ n) := subset_succ_local (σ n) n (mem_successor_self n)
        have h_sn_in_ssn : σ n ∈ σ (σ n) := mem_successor_self (σ n)
        have h_sn_in_F : ⟨σ n, apply fsn (σ n)⟩ ∈ F := by
          rw [UnionSet_is_specified]
          exact ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
                 apply_mem fsn (σ n) (hfsn.1.2 (σ n) h_sn_in_ssn)⟩
        have h_n_in_F : ⟨n, apply fsn n⟩ ∈ F := by
          rw [UnionSet_is_specified]
          exact ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
                 apply_mem fsn n (hfsn.1.2 n h_n_in_ssn)⟩
        have hF_sn := apply_eq F (σ n) _ (h_F_func.2 (σ n) (succ_in_Omega n hn)) h_sn_in_F
        have hF_n  := apply_eq F n _ (h_F_func.2 n hn) h_n_in_F
        rw [hF_sn, hfsn.2.2 n (mem_successor_self n), ← hF_n]

      apply ExistsUnique.intro F
      · -- Existencia
        exact ⟨h_F_func, h_F_zero, h_F_step⟩
      · -- Unicidad: cualquier G con las mismas propiedades es igual a F
        intro G hG
        obtain ⟨hG_func, hG_zero, hG_step⟩ := hG
        -- Lema: apply G n = apply F n para todo n ∈ ω (inducción)
        have h_agree : ∀ n, n ∈ ω → apply G n = apply F n := by
          let S := SpecSet ω (fun n => apply G n = apply F n)
          have h_S_eq_ω : S = ω := by
            apply induction_principle S
            · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
            · rw [SpecSet_is_specified]
              exact ⟨zero_in_Omega, hG_zero.trans h_F_zero.symm⟩
            · intro n hn_in_S
              rw [SpecSet_is_specified] at hn_in_S
              obtain ⟨hn_ω, h_eq_n⟩ := hn_in_S
              rw [SpecSet_is_specified]
              exact ⟨succ_in_Omega n hn_ω, by
                rw [hG_step n hn_ω, h_eq_n, ← h_F_step n hn_ω]⟩
          intro n hn
          rw [← h_S_eq_ω] at hn
          rw [SpecSet_is_specified] at hn
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
      isFunctionFromTo f (σ n) A ∧
      (apply f (∅ : U) = a) ∧
      (∀ k, k ∈ n → apply f (σ k) = apply g ⟨k, apply f k⟩)

    theorem restriction_is_computation_step (A a g n : U) (hn : n ∈ ω) :
        ∀ f, isComputationStep (σ n) f A a g → isComputationStep n (Restriction f (σ n)) A a g := by
      intro f hf
      refine ⟨Restriction_is_function f (σ (σ n)) A (σ n) hf.1 (subset_succ_local (σ n)), ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n := zero_in_succ_nat n hn
        rw [Restriction_apply f (σ n) (∅ : U) h_zero_in]; exact hf.2.1
      · intro k hk
        have hn_nat := mem_Omega_is_Nat n hn
        have hk_nat := nat_element_is_nat n k hn_nat hk
        have h_k_in  : k ∈ σ n    := subset_succ_local n k hk
        have h_sk_in : σ k ∈ σ n  := succ_mem_succ_of_mem k n hk_nat hn_nat hk
        rw [Restriction_apply f (σ n) (σ k) h_sk_in, Restriction_apply f (σ n) k h_k_in]
        exact hf.2.2 k h_k_in

    theorem restriction_computation_general_step (A a g n₁ n₂ : U)
        (hn₁ : n₁ ∈ ω) (hn₂_nat : isNat n₂) (hlt : n₁ ∈ n₂)
        (f : U) (hf : isComputationStep n₂ f A a g) :
        isComputationStep n₁ (Restriction f (σ n₁)) A a g := by
      have h_sn₁_sub : σ n₁ ⊆ σ n₂ := succ_subset_succ_of_mem n₁ n₂ hn₂_nat hlt
      refine ⟨Restriction_is_function f (σ n₂) A (σ n₁) hf.1 h_sn₁_sub, ?_, ?_⟩
      · have h_zero_in : (∅ : U) ∈ σ n₁ := zero_in_succ_nat n₁ hn₁
        rw [Restriction_apply f (σ n₁) ∅ h_zero_in]; exact hf.2.1
      · intro k hk
        have hn₁_nat := mem_Omega_is_Nat n₁ hn₁
        have hk_nat  := nat_element_is_nat n₁ k hn₁_nat hk
        have hk_in_sn₁  : k ∈ σ n₁   := subset_succ_local n₁ k hk
        have hsk_in_sn₁ : σ k ∈ σ n₁ := succ_mem_succ_of_mem k n₁ hk_nat hn₁_nat hk
        rw [Restriction_apply f (σ n₁) (σ k) hsk_in_sn₁, Restriction_apply f (σ n₁) k hk_in_sn₁]
        exact hf.2.2 k (nat_mem_trans k n₁ n₂ hk_nat hn₁_nat hn₂_nat hk hlt)

    theorem computation_uniqueness_step (A a g : U) :
        ∀ n, n ∈ ω → ∀ f₁ f₂,
          isComputationStep n f₁ A a g → isComputationStep n f₂ A a g → f₁ = f₂ := by
      let S := SpecSet (ω : U) (fun n => ∀ f₁ f₂,
        isComputationStep n f₁ A a g → isComputationStep n f₂ A a g → f₁ = f₂)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
        · -- Base n = ∅
          rw [SpecSet_is_specified]; constructor; exact zero_in_Omega
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
              exact apply_eq f₁ ∅ _ (hf₁.1.2 ∅ (by rw [successor_is_specified]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₂.2.1]
            exact apply_mem f₂ ∅ (hf₂.1.2 ∅ (by rw [successor_is_specified]; right; rfl))
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
              exact apply_eq f₂ ∅ _ (hf₂.1.2 ∅ (by rw [successor_is_specified]; right; rfl))
                (hp_eq ▸ hp)
            rw [hp_eq, hy_eq, ← hf₁.2.1]
            exact apply_mem f₁ ∅ (hf₁.1.2 ∅ (by rw [successor_is_specified]; right; rfl))
        · -- Paso inductivo
          intro n hn_in_S
          rw [SpecSet_is_specified] at hn_in_S
          obtain ⟨hn_omega, h_unique_n⟩ := hn_in_S
          rw [SpecSet_is_specified]; constructor; exact succ_in_Omega n hn_omega
          intro f₁ f₂ hf₁ hf₂
          let f₁_res := Restriction f₁ (σ n)
          let f₂_res := Restriction f₂ (σ n)
          have h1 : isComputationStep n f₁_res A a g :=
            restriction_is_computation_step A a g n hn_omega f₁ hf₁
          have h2 : isComputationStep n f₂_res A a g :=
            restriction_is_computation_step A a g n hn_omega f₂ hf₂
          have h_eq_res : f₁_res = f₂_res := h_unique_n f₁_res f₂_res h1 h2
          have h_apply_eq : apply f₁ (σ n) = apply f₂ (σ n) :=
            calc apply f₁ (σ n)
                = apply g ⟨n, apply f₁ n⟩       := hf₁.2.2 n (mem_successor_self n)
              _ = apply g ⟨n, apply f₁_res n⟩   := by
                    rw [← Restriction_apply f₁ (σ n) n (mem_successor_self n)]
              _ = apply g ⟨n, apply f₂_res n⟩   := by rw [h_eq_res]
              _ = apply g ⟨n, apply f₂ n⟩       := by
                    rw [Restriction_apply f₂ (σ n) n (mem_successor_self n)]
              _ = apply f₂ (σ n)                 := (hf₂.2.2 n (mem_successor_self n)).symm
          apply ExtSet; intro p; constructor
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₁.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f1 : p ∈ f₁_res := (Restriction_is_specified f₁ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f2 : p ∈ f₂_res := h_eq_res ▸ hp_f1
              exact Restriction_subset f₂ (σ n) p hp_f2
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₁ (fst p) :=
                (apply_eq f₁ (fst p) (snd p)
                  (hf₁.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, h_apply_eq]
              exact apply_mem f₂ (σ n) (hf₂.1.2 (σ n) (mem_successor_self (σ n)))
          · intro hp
            have h_in_prod : p ∈ σ (σ n) ×ₛ A := hf₂.1.1 p hp
            rw [CartesianProduct_is_specified] at h_in_prod
            obtain ⟨h_is_op, h_fst, _⟩ := h_in_prod
            rw [mem_succ_iff_local] at h_fst
            cases h_fst with
            | inl h_in_sn =>
              have hp_f2 : p ∈ f₂_res := (Restriction_is_specified f₂ (σ n) p).mpr ⟨hp, h_in_sn⟩
              have hp_f1 : p ∈ f₁_res := h_eq_res.symm ▸ hp_f2
              exact Restriction_subset f₁ (σ n) p hp_f1
            | inr h_eq_sn =>
              have hp_eq := OrderedPairSet_is_WellConstructed p h_is_op
              have h_snd : snd p = apply f₂ (fst p) :=
                (apply_eq f₂ (fst p) (snd p)
                  (hf₂.1.2 (fst p) (by rw [mem_succ_iff_local]; right; exact h_eq_sn))
                  (hp_eq ▸ hp)).symm
              rw [hp_eq, h_snd, h_eq_sn, ← h_apply_eq]
              exact apply_mem f₁ (σ n) (hf₁.1.2 (σ n) (mem_successor_self (σ n)))
      intro n hn; rw [← h_ind] at hn; rw [SpecSet_is_specified] at hn; exact hn.2

    theorem computation_existence_step (A a g : U)
        (ha : a ∈ A) (hg : isFunctionFromTo g (ω ×ₛ A) A) :
        ∀ n, n ∈ ω → ∃ f, isComputationStep n f A a g := by
      let S := SpecSet (ω : U) (fun n => ∃ f, isComputationStep n f A a g)
      have h_ind : S = ω := by
        apply induction_principle S
        · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
        · -- Base n = ∅
          rw [SpecSet_is_specified]; constructor; exact zero_in_Omega
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
          rw [SpecSet_is_specified] at hn_in_S
          obtain ⟨hn_omega, ⟨fn, hfn⟩⟩ := hn_in_S
          rw [SpecSet_is_specified]; constructor; exact succ_in_Omega n hn_omega
          have hn_nat    := mem_Omega_is_Nat n hn_omega
          have hσn_nat   := nat_successor_is_nat n hn_nat
          have h_dom_fn  := function_domain_eq fn (σ n) A hfn.1
          have h_sn_ni   : σ n ∉ σ n := nat_not_mem_self (σ n) hσn_nat
          have hn_in_sn  : n ∈ σ n   := mem_successor_self n
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
            · rw [BinUnion_is_specified]; left; exact hy
            · intro y' hy'
              rw [BinUnion_is_specified] at hy'
              cases hy' with
              | inl h => exact huniq y' h
              | inr h =>
                rw [Singleton_is_specified] at h
                have heq := Eq_of_OrderedPairs_given_projections x y' (σ n) val_next h
                rw [heq.1] at hx; exact absurd hx h_sn_ni
          have h_app_fn : ∀ x, x ∈ σ n → apply f_next x = apply fn x := by
            intro x hx
            apply apply_eq f_next x (apply fn x) (h_restrict x hx)
            rw [BinUnion_is_specified]; left
            exact apply_mem fn x (hfn.1.2 x hx)
          have h_sn_uniq : ∃! y, ⟨σ n, y⟩ ∈ f_next := by
            apply ExistsUnique.intro val_next
            · rw [BinUnion_is_specified]; right
              exact (Singleton_is_specified _ _).mpr rfl
            · intro y' hy'
              rw [BinUnion_is_specified] at hy'
              cases hy' with
              | inl h =>
                exact absurd (h_dom_fn ▸ (mem_domain fn (σ n)).mpr ⟨y', h⟩) h_sn_ni
              | inr h =>
                exact (Eq_of_OrderedPairs_given_projections (σ n) y' (σ n) val_next
                  ((Singleton_is_specified _ _).mp h)).2
          exact ⟨f_next,
            ⟨fun p hp => by
              rw [BinUnion_is_specified] at hp
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
              rw [BinUnion_is_specified]; left
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
                    ((BinUnion_is_specified _ _ _).mpr (Or.inr ((Singleton_is_specified _ _).mpr rfl))),
                  h_app_fn n hn_in_sn]⟩
      intro n hn; rw [← h_ind] at hn; rw [SpecSet_is_specified] at hn; exact hn.2

    noncomputable def RecursionComputationsStep (A a g : U) : U :=
      SpecSet (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputationStep n f A a g))

    theorem computations_are_compatible_step (A a g : U) :
        isCompatibleSystem (RecursionComputationsStep A a g) := by
      intro f₁ f₂ hf₁_in hf₂_in
      unfold RecursionComputationsStep at hf₁_in hf₂_in
      rw [SpecSet_is_specified] at hf₁_in hf₂_in
      obtain ⟨_, n₁, hn₁_omega, hf₁⟩ := hf₁_in
      obtain ⟨_, n₂, hn₂_omega, hf₂⟩ := hf₂_in
      have hn₁_nat := mem_Omega_is_Nat n₁ hn₁_omega
      have hn₂_nat := mem_Omega_is_Nat n₂ hn₂_omega
      intro x hx
      rw [BinInter_is_specified] at hx
      obtain ⟨hx_dom1, hx_dom2⟩ := hx
      rcases nat_trichotomy n₁ n₂ hn₁_nat hn₂_nat with h | h | h
      · have hf₂_res := restriction_computation_general_step A a g n₁ n₂ hn₁_omega hn₂_nat h f₂ hf₂
        have h_eq := computation_uniqueness_step A a g n₁ hn₁_omega f₁ _ hf₁ hf₂_res
        have hx_in : x ∈ σ n₁ := by rwa [← function_domain_eq f₁ (σ n₁) A hf₁.1]
        calc apply f₁ x = apply (Restriction f₂ (σ n₁)) x := by rw [h_eq]
          _ = apply f₂ x := Restriction_apply f₂ (σ n₁) x hx_in
      · have h_eq : f₁ = f₂ :=
          computation_uniqueness_step A a g n₁ hn₁_omega f₁ f₂ hf₁ (h ▸ hf₂)
        rw [h_eq]
      · have hf₁_res := restriction_computation_general_step A a g n₂ n₁ hn₂_omega hn₁_nat h f₁ hf₁
        have h_eq := computation_uniqueness_step A a g n₂ hn₂_omega f₂ _ hf₂ hf₁_res
        have hx_in : x ∈ σ n₂ := by rwa [← function_domain_eq f₂ (σ n₂) A hf₂.1]
        calc apply f₁ x = apply (Restriction f₁ (σ n₂)) x := (Restriction_apply f₁ (σ n₂) x hx_in).symm
          _ = apply f₂ x := by rw [← h_eq]

    /-- Teorema de Recursión con Paso Indexado: F(σ n) = g(n, F(n)) con g : ω ×ₛ A → A -/
    theorem RecursionTheoremWithStep (A a g : U)
        (ha : a ∈ A) (hg : isFunctionFromTo g (ω ×ₛ A) A) :
        ∃! F, isFunctionFromTo F ω A ∧
              (apply F (∅ : U) = a) ∧
              (∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩) := by
      let Comps := RecursionComputationsStep A a g
      let F := ⋃ Comps
      have h_mem_Comps : ∀ n f, n ∈ ω → isComputationStep n f A a g → f ∈ Comps := fun n f hn hf =>
        (SpecSet_is_specified _ _ _).mpr ⟨(PowerSet_is_specified _ _).mpr (fun p hp => by
          have hp_in : p ∈ σ n ×ₛ A := hf.1.1 p hp
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩), n, hn, hf⟩
      have h_sv : isSingleValued F :=
        union_compatible_is_function Comps
          (fun f hf => by
            obtain ⟨_, n, _, hf_c⟩ := (SpecSet_is_specified _ _ _).mp hf
            exact ⟨σ n, A, hf_c.1⟩)
          (computations_are_compatible_step A a g)
      have h_F_func : isFunctionFromTo F ω A := by
        constructor
        · intro p hp
          rw [UnionSet_is_specified] at hp
          obtain ⟨f, hf_in, hp_f⟩ := hp
          obtain ⟨_, n, hn, hf_c⟩ := (SpecSet_is_specified _ _ _).mp hf_in
          have hp_in : p ∈ σ n ×ₛ A := hf_c.1.1 p hp_f
          rw [CartesianProduct_is_specified] at hp_in ⊢
          exact ⟨hp_in.1, succ_subset_omega n hn (fst p) hp_in.2.1, hp_in.2.2⟩
        · intro x hx
          obtain ⟨fx, hfx⟩ := computation_existence_step A a g ha hg x hx
          have h_pair : ⟨x, apply fx x⟩ ∈ F := by
            rw [UnionSet_is_specified]
            exact ⟨fx, h_mem_Comps x fx hx hfx, apply_mem fx x (hfx.1.2 x (mem_successor_self x))⟩
          exact ⟨apply fx x, h_pair, fun y hy => (h_sv x (apply fx x) y h_pair hy).symm⟩
      have h_F_zero : apply F (∅ : U) = a := by
        obtain ⟨f₀, hf₀⟩ := computation_existence_step A a g ha hg ∅ zero_in_Omega
        have h_pair : ⟨(∅ : U), a⟩ ∈ F := by
          rw [UnionSet_is_specified]
          exact ⟨f₀, h_mem_Comps ∅ f₀ zero_in_Omega hf₀, by
            have := apply_mem f₀ ∅ (hf₀.1.2 ∅ (mem_successor_self ∅))
            rwa [hf₀.2.1] at this⟩
        exact apply_eq F ∅ a (h_F_func.2 ∅ zero_in_Omega) h_pair
      have h_F_step : ∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩ := by
        intro n hn
        obtain ⟨fsn, hfsn⟩ := computation_existence_step A a g ha hg (σ n) (succ_in_Omega n hn)
        have h_n_in_ssn  : n ∈ σ (σ n) := subset_succ_local (σ n) n (mem_successor_self n)
        have h_sn_in_ssn : σ n ∈ σ (σ n) := mem_successor_self (σ n)
        have h_sn_F : ⟨σ n, apply fsn (σ n)⟩ ∈ F :=
          (UnionSet_is_specified _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
            apply_mem fsn (σ n) (hfsn.1.2 (σ n) h_sn_in_ssn)⟩
        have h_n_F : ⟨n, apply fsn n⟩ ∈ F :=
          (UnionSet_is_specified _ _).mpr ⟨fsn, h_mem_Comps (σ n) fsn (succ_in_Omega n hn) hfsn,
            apply_mem fsn n (hfsn.1.2 n h_n_in_ssn)⟩
        rw [apply_eq F (σ n) _ (h_F_func.2 (σ n) (succ_in_Omega n hn)) h_sn_F,
            hfsn.2.2 n (mem_successor_self n),
            apply_eq F n _ (h_F_func.2 n hn) h_n_F]
      apply ExistsUnique.intro F
      · exact ⟨h_F_func, h_F_zero, h_F_step⟩
      · intro G hG
        obtain ⟨hG_func, hG_zero, hG_step⟩ := hG
        have h_agree : ∀ n, n ∈ ω → apply G n = apply F n := by
          let S := SpecSet ω (fun n => apply G n = apply F n)
          have h_S_eq_ω : S = ω := by
            apply induction_principle S
            · intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
            · rw [SpecSet_is_specified]
              exact ⟨zero_in_Omega, hG_zero.trans h_F_zero.symm⟩
            · intro n hn_in_S
              rw [SpecSet_is_specified] at hn_in_S
              obtain ⟨hn_ω, h_eq_n⟩ := hn_in_S
              rw [SpecSet_is_specified]
              exact ⟨succ_in_Omega n hn_ω,
                by rw [hG_step n hn_ω, h_eq_n, ← h_F_step n hn_ω]⟩
          intro n hn
          rw [← h_S_eq_ω] at hn
          rw [SpecSet_is_specified] at hn
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

  end Recursion

end SetUniverse

export SetUniverse.Recursion (
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
)
