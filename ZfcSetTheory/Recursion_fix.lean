/-
  # Axioma de Infinito y el Conjunto Omega (ω)

  Este archivo introduce el Axioma de Infinito, necesario para construir el conjunto
  de todos los números naturales (ω). Sin este axioma, podemos construir números
  naturales individuales, pero no el conjunto que los contiene a todos.

  ## Definiciones Principales
  - `InfinityAxiom`: Existe un conjunto inductivo.
  - `Omega` (ω): La intersección de todos los subconjuntos inductivos.

  ## Teoremas Principales
  - `Omega_is_inductive`: ω es un conjunto inductivo.
  - `Omega_subset_all_inductive`: ω es subconjunto de cualquier conjunto inductivo.
  - `induction_principle`: El Principio de Inducción Matemática para ω.
  - `Nat_iff_mem_Omega`: Caracterización completa de los naturales en términos de ω.
  - `strong_induction_principle`: Principio de inducción fuerte sobre ω.
  - Propiedades estructurales: transitividad, orden total, infinitud de ω.
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
import ZfcSetTheory.Cardinality
import ZfcSetTheory.NaturalNumbers

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  open SetUniverse.NaturalNumbers

  universe u
  variable {U : Type u}

  namespace InfinityAxiom

    /-! ============================================================ -/
    /-! ### EL AXIOMA DE INFINITO ### -/
    /-! ============================================================ -/

    /-!
      **AXIOMA DE INFINITO**: Existe un conjunto I tal que:
      1. ∅ ∈ I
      2. ∀ x ∈ I, σ(x) ∈ I

      Es decir, existe un conjunto inductivo.

      **Justificación filosófica**: Los axiomas anteriores de ZFC
      permiten construir conjuntos finitos (usando Existencia, Pairing, Union, PowerSet).
      Sin embargo, no garantizan la existencia de conjuntos infinitos.
      Este axioma afirma la existencia del infinito actual (no potencial).
    -/
    axiom ExistsInductiveSet : ∃ (I : U), isInductive I

    /-! ============================================================ -/
    /-! ### CONSTRUCCIÓN DE OMEGA (ω) ### -/
    /-! ============================================================ -/

    /-!
      **ESTRATEGIA DE CONSTRUCCIÓN**:

      Queremos definir ω como la intersección de todos los conjuntos inductivos:
        ω = ⋂ {I | isInductive I}

      **Problema técnico**: No podemos formar directamente "el conjunto de todos
      los conjuntos inductivos" (violaría el esquema de especificación).

      **Solución**: Usamos un conjunto inductivo testigo I₀ (garantizado por el axioma)
      y definimos:
        ω = {x ∈ I₀ | ∀J ⊆ I₀, isInductive J → x ∈ J}

      **Observación clave**: Este conjunto NO depende de la elección de I₀.
      Cualquier conjunto inductivo contiene a ω, por lo que ω es intrínseco.
    -/

    /-- Selección de un conjunto inductivo testigo del axioma -/
    noncomputable def WitnessInductiveSet : U := ExistsInductiveSet.choose

    /-- El conjunto testigo es efectivamente inductivo (por el axioma) -/
    theorem Witness_is_inductive : isInductive WitnessInductiveSet :=
      ExistsInductiveSet.choose_spec

    /--
      **DEFINICIÓN DE ω**: El conjunto de todos los números naturales.

      **Def formal**: ω = {x ∈ Witness | ∀J, (J ⊆ Witness ∧ isInductive J) → x ∈ J}

      Es decir, ω contiene exactamente aquellos elementos que están en
      TODOS los subconjuntos inductivos del testigo.

      **Interpretación**: ω es el menor conjunto inductivo, la intersección
      de todos los conjuntos inductivos.
    -/
    noncomputable def Omega : U :=
      SpecSet WitnessInductiveSet (fun x =>
        ∀ (J : U), J ⊆ WitnessInductiveSet → isInductive J → x ∈ J)

    notation "ω" => Omega

    /-! ============================================================ -/
    /-! ### PROPIEDADES BÁSICAS DE ω ### -/
    /-! ============================================================ -/

    /-- ω es un subconjunto del testigo inductivo (propiedad técnica) -/
    theorem Omega_subset_witness : ω ⊆ WitnessInductiveSet := by
      intro x hx
      unfold Omega at hx
      rw [SpecSet_is_specified] at hx
      exact hx.1

    /-- **TEOREMA**: El conjunto vacío (cero) pertenece a ω -/
    theorem zero_in_Omega : (∅ : U) ∈ ω := by
      unfold Omega
      rw [SpecSet_is_specified]
      constructor
      · exact Witness_is_inductive.1
      · intro J _ hJ_ind
        exact hJ_ind.1

    /-- **TEOREMA**: ω es cerrado bajo la función sucesor -/
    theorem succ_in_Omega (n : U) (hn : n ∈ ω) : σ n ∈ ω := by
      unfold Omega at hn ⊢
      rw [SpecSet_is_specified] at hn ⊢
      constructor
      · apply Witness_is_inductive.2
        exact hn.1
      · intro J hJ_sub hJ_ind
        have hn_in_J : n ∈ J := hn.2 J hJ_sub hJ_ind
        exact hJ_ind.2 n hn_in_J

    /-- **TEOREMA FUNDAMENTAL**: ω es un conjunto inductivo -/
    theorem Omega_is_inductive : isInductive ω :=
      ⟨zero_in_Omega, succ_in_Omega⟩

    /-- **TEOREMA DE MINIMALIDAD**: ω es subconjunto de CUALQUIER conjunto inductivo -/
    theorem Omega_subset_all_inductive (K : U) (hK : isInductive K) : ω ⊆ K := by
      intro x hx
      let I := WitnessInductiveSet
      let L := I ∩ K

      have hL_ind : isInductive L := by
        constructor
        · rw [BinInter_is_specified]
          exact ⟨Witness_is_inductive.1, hK.1⟩
        · intro y hy
          rw [BinInter_is_specified] at hy ⊢
          constructor
          · exact Witness_is_inductive.2 y hy.1
          · exact hK.2 y hy.2

      have hL_sub_I : L ⊆ I := BinInter_subset I K |>.1

      unfold Omega at hx
      rw [SpecSet_is_specified] at hx
      have hx_in_L : x ∈ L := hx.2 L hL_sub_I hL_ind

      rw [BinInter_is_specified] at hx_in_L
      exact hx_in_L.2

    /-! ============================================================ -/
    /-! ### PRINCIPIO DE INDUCCIÓN MATEMÁTICA ### -/
    /-! ============================================================ -/

    /--
      **PRINCIPIO DE INDUCCIÓN** (forma débil/clásica).

      Si un conjunto S ⊆ ω satisface:
      1. 0 ∈ S (caso base)
      2. ∀n ∈ S, σ(n) ∈ S (paso inductivo)
      Entonces S = ω.

      **Interpretación**: Para probar que una propiedad P(n) vale para todo n ∈ ω,
      basta probar P(0) y que P(n) implica P(σ(n)).
    -/
    theorem induction_principle (S : U) (hS_sub : S ⊆ ω)
      (h_zero : (∅ : U) ∈ S)
      (h_succ : ∀ n, n ∈ S → σ n ∈ S) :
      S = ω := by
      apply ExtSet_wc
      · exact hS_sub
      · have hS_ind : isInductive S := ⟨h_zero, h_succ⟩
        exact Omega_subset_all_inductive S hS_ind

    /-! ============================================================ -/
    /-! ### CARACTERIZACIÓN DE NATURALES ### -/
    /-! ============================================================ -/

    /--
      **TEOREMA**: Todo elemento de ω es un número natural (von Neumann).

      **Enunciado**: n ∈ ω → isNat n

      Conecta el conjunto ω con la definición estructural de isNat.
    -/
    theorem mem_Omega_is_Nat (n : U) (hn : n ∈ ω) : isNat n := by
      let S := SpecSet (ω) (fun x : U => isNat x)

      have h_zero : (∅ : U) ∈ S := by
        rw [SpecSet_is_specified]
        exact ⟨zero_in_Omega, zero_is_nat⟩

      have h_succ : ∀ k, k ∈ S → σ k ∈ S := by
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        constructor
        · exact succ_in_Omega k hk.1
        · exact nat_successor_is_nat k hk.2

      have hS_eq_Omega : S = ω := by
        apply induction_principle S
        · intro z hz; rw [SpecSet_is_specified] at hz; exact hz.1
        · exact h_zero
        · exact h_succ

      have hn_in_S : n ∈ S := by rw [hS_eq_Omega]; exact hn
      rw [SpecSet_is_specified] at hn_in_S
      exact hn_in_S.2

    /-- **TEOREMA**: Todo número natural (von Neumann) pertenece a ω -/
    theorem Nat_in_Omega (n : U) (hn : isNat n) : n ∈ ω := by
      exact nat_in_inductive_set n hn (ω) (Omega_is_inductive)

    /-- **CARACTERIZACIÓN COMPLETA**: n es natural ↔ n ∈ ω -/
    theorem Nat_iff_mem_Omega (n : U) : isNat n ↔ n ∈ ω :=
      ⟨Nat_in_Omega n, mem_Omega_is_Nat n⟩

    /-! ============================================================ -/
    /-! ### INDUCCIÓN FUERTE ### -/
    /-! ============================================================ -/

    /--
      **PRINCIPIO DE INDUCCIÓN FUERTE** (también llamado inducción completa).

      Si S ⊆ ω sat isface:
      ∀n ∈ ω, (∀m ∈ n, m ∈ S) → n ∈ S
      Entonces S = ω.

      **Diferencia con inducción débil**:
      - Inducción débil: asume P(n) para probar P(σ(n))
      - Inducción fuerte: asume P(m) para TODO m ∈ n para probar P(n)

      **Ventaja**: No necesita caso base explícito. El caso n = ∅ es vacuamente verdadero.
    -/
    theorem strong_induction_principle (S : U) (hS_sub : S ⊆ ω)
      (h_strong : ∀ n, n ∈ ω → (∀ m, m ∈ n → m ∈ S) → n ∈ S) :
      S = ω := by
      let T := SpecSet (ω) (fun n => ∀ m, m ∈ n → m ∈ S)

      have hT_sub_S : T ⊆ S := by
        intro n hn
        rw [SpecSet_is_specified] at hn
        exact h_strong n hn.1 hn.2

      have hT_zero : (∅ : U) ∈ T := by
        rw [SpecSet_is_specified]
        constructor
        · exact zero_in_Omega
        · intro m hm
          exfalso
          exact EmptySet_is_empty m hm

      have hT_succ : ∀ k, k ∈ T → σ k ∈ T := by
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        constructor
        · exact succ_in_Omega k hk.1
        · intro m hm_in_succ
          rw [successor_is_specified] at hm_in_succ
          cases hm_in_succ with
          | inl hm_in_k => exact hk.2 m hm_in_k
          | inr hm_eq_k =>
            rw [hm_eq_k]
            exact hT_sub_S k hk

      have hT_eq_omega : T = ω := by
        apply induction_principle T
        · intro z hz; rw [SpecSet_is_specified] at hz; exact hz.1
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
    /-! ### PROPIEDADES ESTRUCTURALES DE ω ### -/
    /-! ============================================================ -/

    /-- **TEOREMA**: ω es un conjunto transitivo -/
    theorem Omega_is_transitive : isTransitiveSet (ω) := by
      intro n hn
      let S := SpecSet (ω) (fun n => n ⊆ ω)

      have hS_strong : ∀ k, k ∈ ω → (∀ m, m ∈ k → m ∈ S) → k ∈ S := by
        intro k hk_omega _
        rw [SpecSet_is_specified]
        constructor
        · exact hk_omega
        · intro x hx_in_k
          have hk_nat : isNat k := mem_Omega_is_Nat k hk_omega
          have hx_nat : isNat x := nat_element_is_nat k x hk_nat hx_in_k
          exact Nat_in_Omega x hx_nat

      have hS_eq_omega : S = ω := by
        apply strong_induction_principle S
        · intro z hz; rw [SpecSet_is_specified] at hz; exact hz.1
        · exact hS_strong

      have hn_in_S : n ∈ S := by rw [hS_eq_omega]; exact hn
      rw [SpecSet_is_specified] at hn_in_S
      exact hn_in_S.2

    /-- **TEOREMA**: Todo elemento de ω es transitivo -/
    theorem Omega_element_is_transitive (n : U) (hn : n ∈ ω) :
      isTransitiveSet n := by
      have hn_nat : isNat n := mem_Omega_is_Nat n hn
      exact hn_nat.1

    /-- **TEOREMA**: ω tiene un orden total estricto (membresía) -/
    theorem Omega_has_total_order : isTotalStrictOrderMembershipGuided (ω) := by
      constructor
      · exact Omega_is_transitive
      · constructor
        · intro n m hn hm hnm
          have hn_nat : isNat n := mem_Omega_is_Nat n hn
          have hm_nat : isNat m := mem_Omega_is_Nat m hm
          exact nat_mem_asymm n m hn_nat hm_nat hnm
        · intro n m hn hm
          have hn_nat : isNat n := mem_Omega_is_Nat n hn
          have hm_nat : isNat m := mem_Omega_is_Nat m hm
          exact nat_trichotomy n m hn_nat hm_nat

    /-- **TEOREMA**: ω NO tiene elemento máximo (infinitud de ω) -/
    theorem Omega_no_maximum : ∀ n : U, n ∈ ω → ∃ m : U, m ∈ ω ∧ n ∈ m := by
      intro n hn
      exists (σ n)
      constructor
      · exact succ_in_Omega n hn
      · exact mem_successor_self n

  end InfinityAxiom

  export InfinityAxiom (
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
  )

end SetUniverse

