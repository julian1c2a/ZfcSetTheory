/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  # Axioma de Infinito y el Conjunto Omega (ω)

  Este archivo introduce el Axioma de Infinito, necesario para construir el conjunto
  de todos los números naturales (ω). Sin este axioma, podemos construir números
  naturales individuales, pero no el conjunto que los contiene a todos.

  ## Contenido

  ### Axioma y Construcción
  - `ExistsInductiveSet`: Axioma de Infinito - existe un conjunto inductivo
  - `Omega` (ω): El menor conjunto inductivo (intersección de todos los inductivos)

  ### Propiedades Básicas de ω
  - `Omega_is_inductive`: ω es un conjunto inductivo
  - `Omega_subset_all_inductive`: ω ⊆ K para todo K inductivo (minimalidad)
  - `zero_in_Omega`: 0 ∈ ω
  - `succ_in_Omega`: n ∈ ω → σ(n) ∈ ω

  ### Caracterización de Naturales
  - `mem_Omega_is_Nat`: n ∈ ω → IsNat n
  - `Nat_in_Omega`: IsNat n → n ∈ ω
  - `Nat_iff_mem_Omega`: IsNat n ↔ n ∈ ω (caracterización completa)

  ### Principios de Inducción
  - `induction_principle`: Inducción matemática débil sobre ω
  - `strong_induction_principle`: Inducción fuerte (completa) sobre ω

  ### Propiedades Estructurales
  - `Omega_is_transitive`: ω es un conjunto transitivo
  - `Omega_element_is_transitive`: Todo elemento de ω es transitivo
  - `Omega_has_total_order`: ω tiene orden total estricto por membresía
  - `Omega_no_maximum`: ω no tiene elemento máximo (infinitud)

  ## Próximos Desarrollos

  El **Teorema de Recursión** (que permite definir funciones recursivas sobre ω)
  se desarrollará en el archivo `Recursion.lean`, que construirá sobre este.
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
import ZfcSetTheory.Cardinal.Basic
import ZfcSetTheory.Nat.Basic

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Cardinal.Basic
  open ZFC.Nat.Basic

  universe u
  variable {U : Type u}

  namespace Axiom.Infinity

    /-! ============================================================ -/
    /-! ### EL AXIOMA DE INFINITO ### -/
    /-! ============================================================ -/

    /-!
      Existe un conjunto I tal que:
      1. ∅ ∈ I
      2. ∀ x ∈ I, σ(x) ∈ I

      Es decir, existe un conjunto inductivo.
    -/
    axiom ExistsInductiveSet : ∃ (I : U), IsInductive I

    /-! ============================================================ -/
    /-! ### CONSTRUCCIÓN DE OMEGA (ω) ### -/
    /-! ============================================================ -/

    /-!
      Definimos ω como la intersección de todos los conjuntos inductivos.
      Técnicamente, para usar el esquema de especificación, tomamos un conjunto
      inductivo I₀ (dado por el axioma) y definimos ω como la intersección de
      todos los subconjuntos inductivos de I₀.

      Luego probamos que este conjunto no depende de la elección de I₀.
    -/

    /-- Selección de un conjunto inductivo testigo -/
    noncomputable def WitnessInductiveSet : U := ExistsInductiveSet.choose

    theorem Witness_is_inductive : IsInductive (WitnessInductiveSet : U) := by
      exact ExistsInductiveSet.choose_spec

    /--
      Definición de ω: La intersección de todos los subconjuntos inductivos
      del conjunto testigo.
      ω = { x ∈ Witness | ∀ J, (J ⊆ Witness ∧ IsInductive J) → x ∈ J }
    -/
    noncomputable def Omega : U :=
      sep WitnessInductiveSet (fun x =>
        ∀ (J : U), J ⊆ WitnessInductiveSet → IsInductive J → x ∈ J)

    notation "ω" => Omega

    /-! ### Propiedades de ω ### -/

    /-- ω es un subconjunto del testigo inductivo -/
    theorem Omega_subset_witness : Omega ⊆ (WitnessInductiveSet : U) := by
      intro x hx
      unfold Omega at hx
      rw [mem_sep_iff] at hx
      exact hx.1

    /-- ω contiene al vacío (0) -/
    theorem zero_in_Omega : (∅ : U) ∈ ω := by
      unfold Omega
      rw [mem_sep_iff]
      constructor
      · -- ∅ ∈ Witness
        exact Witness_is_inductive.1
      · -- Para todo subconjunto inductivo J, ∅ ∈ J
        intro J _ hJ_ind
        exact hJ_ind.1

    /-- ω es cerrado bajo sucesor -/
    theorem succ_in_Omega (n : U) (hn : n ∈ ω) : σ n ∈ ω := by
      unfold Omega at hn ⊢
      rw [mem_sep_iff] at hn ⊢
      constructor
      · -- σ(n) ∈ Witness
        apply Witness_is_inductive.2
        exact hn.1
      · -- Para todo subconjunto inductivo J...
        intro J hJ_sub hJ_ind
        -- Sabemos que n ∈ J
        have hn_in_J : n ∈ J := hn.2 J hJ_sub hJ_ind
        -- Como J es inductivo, σ(n) ∈ J
        exact hJ_ind.2 n hn_in_J

    /-- Teorema: ω es un conjunto inductivo -/
    theorem Omega_is_inductive : IsInductive (ω : U) := by
      constructor
      · exact zero_in_Omega
      · exact succ_in_Omega

    /-- Teorema: ω es subconjunto de CUALQUIER conjunto inductivo K.
        (No solo de los subconjuntos del testigo).
        Esta es la propiedad de minimalidad de ω. -/
    theorem Omega_subset_all_inductive (K : U) (hK : IsInductive K) : ω ⊆ K := by
      intro x hx
      -- Sea I el testigo. Consideramos L = I ∩ K.
      let I : U := WitnessInductiveSet
      let L := I ∩ K

      -- L es inductivo
      have hL_ind : IsInductive L := by
        constructor
        · -- 0 ∈ I ∩ K
          rw [mem_inter_iff]
          exact ⟨Witness_is_inductive.1, hK.1⟩
        · -- Si y ∈ L, entonces σ(y) ∈ L
          intro y hy
          rw [mem_inter_iff] at hy ⊢
          constructor
          · exact Witness_is_inductive.2 y hy.1
          · exact hK.2 y hy.2

      -- L es subconjunto de I
      have hL_sub_I : L ⊆ I := inter_subset I K |>.1

      -- Por definición de ω, x debe estar en L (porque L es inductivo y L ⊆ I)
      unfold Omega at hx
      rw [mem_sep_iff] at hx
      have hx_in_L : x ∈ L := hx.2 L hL_sub_I hL_ind

      -- Si x ∈ L, entonces x ∈ K
      rw [mem_inter_iff] at hx_in_L
      exact hx_in_L.2

    /-! ============================================================ -/
    /-! ### PRINCIPIO DE INDUCCIÓN MATEMÁTICA ### -/
    /-! ============================================================ -/

    /-!
      Si un conjunto S ⊆ ω satisface:
      1. 0 ∈ S
      2. ∀ n, n ∈ S → σ(n) ∈ S
      Entonces S = ω.
    -/
    theorem induction_principle (S : U) (hS_sub : S ⊆ ω)
      (h_zero : (∅ : U) ∈ S)
      (h_succ : ∀ n, n ∈ S → σ n ∈ S) :
      S = ω := by
      apply eq_of_subset_of_subset
      · -- S ⊆ ω (hipótesis)
        exact hS_sub
      · -- ω ⊆ S
        -- S es un conjunto inductivo (por hipótesis h_zero y h_succ)
        have hS_ind : IsInductive S := ⟨h_zero, h_succ⟩
        -- ω es el conjunto inductivo más pequeño
        exact Omega_subset_all_inductive S hS_ind

    /-! ### Caracterización de Naturales en términos de ω ### -/

    /--
      Todo elemento de ω es un número natural (en el sentido de von Neumann: IsNat).
      Esto conecta nuestra definición estructural anterior con el conjunto ω.
    -/
    theorem mem_Omega_is_Nat (n : U) (hn : n ∈ ω) : IsNat n := by
      -- Definimos S = {x ∈ ω | IsNat x}
      let S := sep ω (fun (x : U) => IsNat x)

      -- Demostramos que S es inductivo
      have h_zero : (∅ : U) ∈ S := by
        rw [mem_sep_iff]
        exact ⟨zero_in_Omega, isNat_zero⟩

      have h_succ : ∀ k, k ∈ S → σ k ∈ S := by
        intro k hk
        rw [mem_sep_iff] at hk ⊢
        constructor
        · exact succ_in_Omega k hk.1
        · exact isNat_succ k hk.2

      -- Por inducción, S = ω
      have hS_eq_Omega : S = ω := by
        apply induction_principle S
        · intro z hz; rw [mem_sep_iff] at hz; exact hz.1
        · exact h_zero
        · exact h_succ

      -- Por tanto, si n ∈ ω, entonces n ∈ S, lo que implica IsNat n
      have hn_in_S : n ∈ S := by rw [hS_eq_Omega]; exact hn
      rw [mem_sep_iff] at hn_in_S
      exact hn_in_S.2

    /-- Todo número natural (von Neumann) pertenece a ω -/
    theorem Nat_in_Omega (n : U) (hn : IsNat n) : n ∈ ω := by
      have h_ind : IsInductive (ω : U) := Omega_is_inductive
      exact nat_in_inductive_set n hn ω h_ind

    /-- Caracterización completa: n es natural ↔ n ∈ ω -/
    theorem Nat_iff_mem_Omega (n : U) : IsNat n ↔ n ∈ ω :=
      ⟨Nat_in_Omega n, mem_Omega_is_Nat n⟩

    /-! ============================================================ -/
    /-! ### INDUCCIÓN FUERTE ### -/
    /-! ============================================================ -/

    /-- **Principio de Inducción Fuerte** (inducción completa). -/
    theorem strong_induction_principle (S : U) (hS_sub : S ⊆ ω)
      (h_strong : ∀ n, n ∈ ω → (∀ m, m ∈ n → m ∈ S) → n ∈ S) :
      S = ω := by
      let T := sep ω (fun n => ∀ m, m ∈ n → m ∈ S)

      have hT_sub_S : T ⊆ S := by
        intro n hn
        rw [mem_sep_iff] at hn
        exact h_strong n hn.1 hn.2

      have hT_zero : (∅ : U) ∈ T := by
        rw [mem_sep_iff]
        constructor
        · exact zero_in_Omega
        · intro m hm
          exfalso
          exact EmptySet_is_empty m hm

      have hT_succ : ∀ k, k ∈ T → σ k ∈ T := by
        intro k hk
        rw [mem_sep_iff] at hk ⊢
        constructor
        · exact succ_in_Omega k hk.1
        · intro m hm_in_succ
          rw [mem_succ_iff] at hm_in_succ
          cases hm_in_succ with
          | inl hm_in_k => exact hk.2 m hm_in_k
          | inr hm_eq_k =>
            rw [hm_eq_k]
            have hk_in_T : k ∈ T := by
              rw [mem_sep_iff]
              exact ⟨hk.1, hk.2⟩
            exact hT_sub_S k hk_in_T

      have hT_eq_omega : T = ω := by
        apply induction_principle T
        · intro z hz; rw [mem_sep_iff] at hz; exact hz.1
        · exact hT_zero
        · exact hT_succ

      apply ExtSet
      intro x
      constructor
      · exact hS_sub x
      · intro hx
        have hx_in_T : x ∈ T := by rw [hT_eq_omega]; exact hx
        exact hT_sub_S x hx_in_T

    /-! ============================================================ -/
    /-! ### PROPIEDADES ESTRUCTURALES ### -/
    /-! ============================================================ -/

    /-- ω es un conjunto transitivo -/
    theorem Omega_is_transitive : IsTransitive (ω : U) := by
      intro n hn x hx_in_n
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      have hx_nat : IsNat x := nat_element_is_nat n x hn_nat hx_in_n
      exact Nat_in_Omega x hx_nat

    /-- Todo elemento de ω es transitivo -/
    theorem Omega_element_is_transitive (n : U) (hn : n ∈ ω) :
      IsTransitive n := by
      have hn_nat : IsNat n := mem_Omega_is_Nat n hn
      exact hn_nat.1

    /-- ω tiene un orden total estricto (membresía) -/
    theorem Omega_has_total_order : isTotalStrictOrderMembershipGuided (ω : U) := by
      constructor
      · exact Omega_is_transitive
      · constructor
        · intro n m hn hm hnm
          have hn_nat : IsNat n := mem_Omega_is_Nat n hn
          have hm_nat : IsNat m := mem_Omega_is_Nat m hm
          exact mem_asymm n m hn_nat hm_nat hnm
        · intro n m hn hm
          have hn_nat : IsNat n := mem_Omega_is_Nat n hn
          have hm_nat : IsNat m := mem_Omega_is_Nat m hm
          exact trichotomy n m hn_nat hm_nat

    /-- ω NO tiene elemento máximo (infinitud) -/
    theorem Omega_no_maximum : ∀ n : U, n ∈ ω → ∃ m : U, m ∈ ω ∧ n ∈ m := by
      intro n hn
      exists (σ n)
      constructor
      · exact succ_in_Omega n hn
      · exact mem_succ_self n

    /-- The membership relation is well-founded on ω. -/
    theorem nat_mem_wf : WellFounded (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b) := by
      constructor
      intro a
      by_cases ha : a ∈ ω
      · -- Every element of ω is accessible, proved by strong induction.
        -- S = { n ∈ ω | Acc R n } where R is the membership relation.
        let S := sep ω (fun n => Acc (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b) n)
        have hS_sub : S ⊆ ω := fun z hz => by
          rw [mem_sep_iff] at hz; exact hz.1
        have hS_eq : S = ω := strong_induction_principle S hS_sub (fun n hn ih => by
          rw [mem_sep_iff]
          refine ⟨hn, Acc.intro n (fun y hy => ?_)⟩
          -- hy : y ∈ ω ∧ n ∈ ω ∧ y ∈ n; ih says every m ∈ n is in S
          have hy_in_S : y ∈ S := ih y hy.2.2
          rw [mem_sep_iff] at hy_in_S
          exact hy_in_S.2)
        have ha_in_S : a ∈ S := by rw [hS_eq]; exact ha
        rw [mem_sep_iff] at ha_in_S
        exact ha_in_S.2
      · -- Elements outside ω are vacuously accessible: R y a requires a ∈ ω.
        exact Acc.intro a (fun y hy => absurd hy.2.1 ha)

    -- =========================================================================
    -- Order on ω: strict (≺) and non-strict (≼)
    -- =========================================================================

    /-- Strict order on Von Neumann naturals: `n ≺ m` iff `n ∈ m`. -/
    scoped notation:50 n:51 " ≺ " m:51 => (n ∈ m)

    /-- Non-strict order on Von Neumann naturals: `n ≼ m` iff `n ∈ m ∨ n = m`. -/
    scoped notation:50 n:51 " ≼ " m:51 => (n ∈ m ∨ n = m)

    /-- The strict order on ω is transitive. -/
    theorem natLt_trans {n m k : U} (hn : IsNat n) (hm : IsNat m) (hk : IsNat k)
        (h₁ : n ≺ m) (h₂ : m ≺ k) : n ≺ k :=
      mem_trans n m k hn hm hk h₁ h₂

    /-- The strict order on ω is asymmetric. -/
    theorem natLt_asymm {n m : U} (hn : IsNat n) (hm : IsNat m)
        (h : n ≺ m) : ¬(m ≺ n) :=
      mem_asymm n m hn hm h

    /-- Trichotomy: for any two naturals, exactly one of `n ≺ m`, `n = m`, `m ≺ n`. -/
    theorem natLt_trichotomy (n m : U) (hn : IsNat n) (hm : IsNat m) :
        n ≺ m ∨ n = m ∨ m ≺ n :=
      trichotomy n m hn hm

    /-- The non-strict order is reflexive. -/
    theorem natLe_refl (n : U) : n ≼ n := Or.inr rfl

    /-- The non-strict order is transitive. -/
    theorem natLe_trans {n m k : U} (hn : IsNat n) (hm : IsNat m) (hk : IsNat k)
        (h₁ : n ≼ m) (h₂ : m ≼ k) : n ≼ k := by
      cases h₁ with
      | inl h => cases h₂ with
        | inl h' => exact Or.inl (mem_trans n m k hn hm hk h h')
        | inr h' => exact Or.inl (h' ▸ h)
      | inr h => exact h ▸ h₂

    /-- Every non-empty subset of ω has a `≺`-minimum element. -/
    theorem Omega_has_min (T : U) (hT_sub : T ⊆ (ω : U)) (hT_ne : T ≠ ∅) :
        ∃ n, n ∈ T ∧ ∀ m, m ∈ T → n ≼ m := by
      let S := sep (ω : U) (fun n =>
        n ∈ T → ∃ p, p ∈ T ∧ ∀ k, k ∈ T → p ≼ k)
      have hS_eq : S = (ω : U) :=
        strong_induction_principle S
          (fun z hz => by rw [mem_sep_iff] at hz; exact hz.1)
          (fun n hn ih => by
            rw [mem_sep_iff]
            refine ⟨hn, fun hnT => ?_⟩
            by_cases h : ∃ l, l ∈ T ∧ l ∈ n
            · obtain ⟨l, hlT, hln⟩ := h
              have hl_in_S : l ∈ S := ih l hln
              rw [mem_sep_iff] at hl_in_S
              exact hl_in_S.2 hlT
            · have h' : ∀ l, l ∈ T → l ∉ n := fun l hl hln => h ⟨l, hl, hln⟩
              exact ⟨n, hnT, fun k hkT => by
                rcases trichotomy n k
                    (mem_Omega_is_Nat n hn) (mem_Omega_is_Nat k (hT_sub k hkT))
                  with hk | hk | hk
                · exact Or.inl hk
                · exact Or.inr hk
                · exact absurd hk (h' k hkT)⟩)
      obtain ⟨x, hxT⟩ := (nonempty_iff_exists_mem T).mp hT_ne
      have hx_in_S : x ∈ S := by rw [hS_eq]; exact hT_sub x hxT
      rw [mem_sep_iff] at hx_in_S
      exact hx_in_S.2 hxT

  end Axiom.Infinity

  export Axiom.Infinity (
    ExistsInductiveSet
    Omega
    Omega_is_inductive
    Omega_subset_all_inductive
    zero_in_Omega
    succ_in_Omega
    induction_principle
    mem_Omega_is_Nat
    Nat_in_Omega
    Nat_iff_mem_Omega
    strong_induction_principle
    Omega_is_transitive
    Omega_element_is_transitive
    Omega_has_total_order
    Omega_no_maximum
    nat_mem_wf
    -- Order on ω
    natLt_trans
    natLt_asymm
    natLt_trichotomy
    natLe_refl
    natLe_trans
    Omega_has_min
  )

end ZFC
