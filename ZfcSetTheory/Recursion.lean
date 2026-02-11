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
      Existe un conjunto I tal que:
      1. ∅ ∈ I
      2. ∀ x ∈ I, σ(x) ∈ I

      Es decir, existe un conjunto inductivo.
    -/
    axiom ExistsInductiveSet : ∃ (I : U), isInductive I

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

    theorem Witness_is_inductive : isInductive WitnessInductiveSet :=
      ExistsInductiveSet.choose_spec

    /--
      Definición de ω: La intersección de todos los subconjuntos inductivos
      del conjunto testigo.
      ω = { x ∈ Witness | ∀ J, (J ⊆ Witness ∧ isInductive J) → x ∈ J }
    -/
    noncomputable def Omega : U :=
      SpecSet WitnessInductiveSet (fun x =>
        ∀ (J : U), J ⊆ WitnessInductiveSet → isInductive J → x ∈ J)

    notation "ω" => Omega

    /-! ### Propiedades de ω ### -/

    /-- ω es un subconjunto del testigo inductivo -/
    theorem Omega_subset_witness : ω ⊆ WitnessInductiveSet := by
      intro x hx
      rw [SpecSet_is_specified] at hx
      exact hx.1

    /-- ω contiene al vacío (0) -/
    theorem zero_in_Omega : (∅ : U) ∈ ω := by
      rw [SpecSet_is_specified]
      constructor
      · -- ∅ ∈ Witness
        exact Witness_is_inductive.1
      · -- Para todo subconjunto inductivo J, ∅ ∈ J
        intro J _ hJ_ind
        exact hJ_ind.1

    /-- ω es cerrado bajo sucesor -/
    theorem succ_in_Omega (n : U) (hn : n ∈ ω) : σ n ∈ ω := by
      rw [SpecSet_is_specified] at hn ⊢
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
    theorem Omega_is_inductive : isInductive ω :=
      ⟨zero_in_Omega, succ_in_Omega⟩

    /-- Teorema: ω es subconjunto de CUALQUIER conjunto inductivo K.
        (No solo de los subconjuntos del testigo).
        Esta es la propiedad de minimalidad de ω. -/
    theorem Omega_subset_all_inductive (K : U) (hK : isInductive K) : ω ⊆ K := by
      intro x hx
      -- Sea I el testigo. Consideramos L = I ∩ K.
      let I := WitnessInductiveSet
      let L := I ∩ K

      -- L es inductivo
      have hL_ind : isInductive L := by
        constructor
        · -- 0 ∈ I ∩ K
          rw [BinInter_is_specified]
          exact ⟨Witness_is_inductive.1, hK.1⟩
        · -- Si y ∈ L, entonces σ(y) ∈ L
          intro y hy
          rw [BinInter_is_specified] at hy ⊢
          constructor
          · exact Witness_is_inductive.2 y hy.1
          · exact hK.2 y hy.2

      -- L es subconjunto de I
      have hL_sub_I : L ⊆ I := BinInter_subset I K |>.1

      -- Por definición de ω, x debe estar en L (porque L es inductivo y L ⊆ I)
      rw [SpecSet_is_specified] at hx
      have hx_in_L : x ∈ L := hx.2 L hL_sub_I hL_ind

      -- Si x ∈ L, entonces x ∈ K
      rw [BinInter_is_specified] at hx_in_L
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
      apply ExtSet_wc
      · -- S ⊆ ω (hipótesis)
        exact hS_sub
      · -- ω ⊆ S
        -- S es un conjunto inductivo (por hipótesis h_zero y h_succ)
        have hS_ind : isInductive S := ⟨h_zero, h_succ⟩
        -- ω es el conjunto inductivo más pequeño
        exact Omega_subset_all_inductive S hS_ind

    /-! ### Caracterización de Naturales en términos de ω ### -/

    /--
      Todo elemento de ω es un número natural (en el sentido de von Neumann: isNat).
      Esto conecta nuestra definición estructural anterior con el conjunto ω.
    -/
    theorem mem_Omega_is_Nat (n : U) (hn : n ∈ ω) : isNat n := by
      -- Definimos S = {x ∈ ω | isNat x}
      let S := SpecSet ω (fun x => isNat x)

      -- Demostramos que S es inductivo
      have h_zero : (∅ : U) ∈ S := by
        rw [SpecSet_is_specified]
        exact ⟨zero_in_Omega, zero_is_nat⟩

      have h_succ : ∀ k, k ∈ S → σ k ∈ S := by
        intro k hk
        rw [SpecSet_is_specified] at hk ⊢
        constructor
        · exact succ_in_Omega k hk.1
        · exact nat_successor_is_nat k hk.2

      -- Por inducción, S = ω
      have hS_eq_Omega : S = ω := by
        apply induction_principle S
        · intro z hz; rw [SpecSet_is_specified] at hz; exact hz.1
        · exact h_zero
        · exact h_succ

      -- Por tanto, si n ∈ ω, entonces n ∈ S, lo que implica isNat n
      have hn_in_S : n ∈ S := by rw [hS_eq_Omega]; exact hn
      rw [SpecSet_is_specified] at hn_in_S
      exact hn_in_S.2

  end InfinityAxiom

  export InfinityAxiom (
    ExistsInductiveSet
    Omega
    Omega_is_inductive
    Omega_subset_all_inductive
    induction_principle
    mem_Omega_is_Nat
  )

end SetUniverse
