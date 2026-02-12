/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  # Natural Numbers (von Neumann ordinals)

  Este archivo define los números naturales como ordinales de von Neumann SIN introducir
  el Axioma de Infinito. Los naturales se caracterizan como conjuntos transitivos,
  totalmente ordenados y bien ordenados (con elemento mínimo Y máximo en cada subconjunto),
  lo que los distingue como ordinales FINITOS.

  ## Definiciones Principales

  ### Construcciones Básicas
  - `σ n` : Función sucesor, σ(n) = n ∪ {n}
  - `isInductive I` : I es inductivo si ∅ ∈ I y ∀x ∈ I, σ(x) ∈ I
  - `isTransitiveSet S` : S es transitivo si ∀x ∈ S, x ⊆ S

  ### Orden Guiado por Membresía
  - `StrictOrderMembershipGuided S` : El orden ∈[S] = {⟨x,y⟩ | x,y ∈ S ∧ x ∈ y}
    Es la relación de orden estricto inducida por la membresía en S

  - `isTotalStrictOrderMembershipGuided S` : ∈[S] es un orden total estricto:
    * Asimetría: x ∈ y → y ∉ x
    * Tricotomía: x ∈ y ∨ x = y ∨ y ∈ x (para todo x,y ∈ S)

  - `isWellOrderMembershipGuided S` : ⟨S, ∈[S]⟩ es bien ordenado (finito):
    * Todo subconjunto no vacío T ⊆ S tiene elemento MÍNIMO
    * Todo subconjunto no vacío T ⊆ S tiene elemento MÁXIMO
    (La existencia de máximo caracteriza la finitud)

  ### Definición de Número Natural
  - `isNat n` : n es un número natural si y solo si:
    1. n es un conjunto transitivo
    2. ∈[n] es un orden total estricto en n
    3. ⟨n, ∈[n]⟩ está bien ordenado (con mínimos y máximos)

  ## Teoremas Fundamentales Probados

  ### Propiedades Elementales
  - `zero_is_nat` : ∅ es un número natural
  - Ejemplos: 1 = {∅}, 2 = {∅,{∅}}, 3 = {∅,{∅},{∅,{∅}}} son naturales
  - `mem_successor_self` : n ∈ σ(n)
  - `nat_ne_successor` : n ≠ σ(n)

  ### Buena Fundación (SIN Axioma de Regularidad)
  - `nat_not_mem_self` : n ∉ n (irreflexividad)
  - `nat_no_two_cycle` : ¬(n ∈ m ∧ m ∈ n)
  - `nat_no_three_cycle` : ¬(n ∈ m ∧ m ∈ k ∧ k ∈ n)

  ### Propiedades Estructurales
  - `nat_element_is_nat` : m ∈ n → isNat m (elementos son naturales)
  - `nat_element_is_transitive` : elementos son conjuntos transitivos
  - `nat_element_has_strict_total_order` : elementos tienen orden total
  - `nat_element_has_well_order` : elementos están bien ordenados

  ### Clausura y Orden
  - `nat_successor_is_nat` : isNat n → isNat (σ n)
  - `nat_trichotomy` : n ∈ m ∨ n = m ∨ m ∈ n (tricotomía completa)
  - `nat_mem_trans` : n ∈ m ∧ m ∈ k → n ∈ k (transitividad)
  - `nat_mem_asymm` : n ∈ m → m ∉ n (asimetría)
  - `nat_subset_mem_or_eq` : n ⊆ m → n ∈ m ∨ n = m
  - `no_nat_between` : entre n y σ(n) no hay otros naturales

  ### Segmentos Iniciales y Tricotomía
  - `isInitialSegment` : definición de segmento inicial
  - `initial_segment_of_nat_is_eq_or_mem` : segmento inicial es igual o elemento
  - `inter_nat_is_initial_segment` : la intersección es segmento inicial
  - `nat_is_initial_segment` : n ∈ m → n es segmento inicial de m
  - `nat_element_trichotomy` : elementos de m cumplen tricotomía

  ### Propiedades del Sucesor
  - `successor_injective` : σ(n) = σ(m) → n = m
  - `successor_nonempty` : σ(n) ≠ ∅
  - `mem_successor_of_mem` : m ∈ n → m ∈ σ(n)

  ### Conjuntos Inductivos
  - `nat_is_zero_or_succ` : todo natural es 0 o sucesor de otro
  - `nat_subset_inductive_set` : n ⊆ I para todo conjunto inductivo I
  - `nat_in_inductive_set` : n ∈ I para todo conjunto inductivo I
  - `zero/one/two/three_in_inductive` : casos específicos

  ### Finitud
  - `nat_has_max` : todo subconjunto no vacío de un natural tiene máximo
    (caracteriza los naturales como ordinales finitos)

  ## Notas Técnicas

  - TODOS los teoremas están probados SIN el Axioma de Regularidad
  - TODOS los teoremas están probados SIN el Axioma de Infinito (ω no está definido aquí)
  - La tricotomía completa está probada usando segmentos iniciales
  - La existencia de máximo en subconjuntos distingue naturales de ordinales infinitos
  - Los teoremas sobre conjuntos inductivos NO requieren que ω exista

  ## Archivos Relacionados

  Los siguientes desarrollos continúan en archivos específicos:

  - **Recursion.lean**: Axioma de Infinito, conjunto ω, principio de inducción,
    recursión sobre naturales, caracterización isNat n ↔ n ∈ ω

  - **NaturalArithmetic.lean**: Aritmética básica (suma, multiplicación, exponenciación),
    propiedades algebraicas, orden aritmético, divisibilidad, números primos
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
  universe u
  variable {U : Type u}

  namespace NaturalNumbers

    /-! ============================================================ -/
    /-! ### DEFINICIONES BÁSICAS ### -/
    /-! ============================================================ -/

    /-! ### Función Sucesor: σ(n) = n ∪ {n} ### -/
    noncomputable def successor (n : U) : U := n ∪ {n}

    notation "σ " n:90 => successor n

    /-- Specification theorem for successor -/
    theorem successor_is_specified (n x : U) :
      x ∈ (σ n) ↔ x ∈ n ∨ x = n := by
      unfold successor
      simp only [BinUnion_is_specified, Singleton_is_specified]

    /-! ### Conjunto Inductivo ### -/
    /-- Un conjunto I es inductivo si contiene al vacío y es cerrado bajo sucesores.

        **Definición**: I es inductivo ⟺ (∅ ∈ I ∧ ∀x ∈ I, σ(x) ∈ I)

        Esta definición no requiere que I sea el "menor" conjunto inductivo (ω).
        Los conjuntos inductivos caracterizan aquellos que contienen "todos los naturales",
        aunque ω no esté definido todavía. -/
    def isInductive (I : U) : Prop :=
      (∅ : U) ∈ I ∧ ∀ x, x ∈ I → (σ x) ∈ I

    /-! ### Conjunto Transitivo ### -/
    /-- Un conjunto S es transitivo si cada elemento es también un subconjunto de S.

        **Definición**: S es transitivo ⟺ ∀x ∈ S, x ⊆ S

        Equivalentemente: ∀x ∈ S, ∀y ∈ x, y ∈ S

        Los conjuntos transitivos son fundamentales en la construcción de ordinales.
        Todo ordinal (y en particular, todo natural) es un conjunto transitivo. -/
    def isTransitiveSet (S : U) : Prop :=
      ∀ x, x ∈ S → x ⊆ S

    /-! ### Orden Estricto Guiado por Membresía ### -/
    /-- El orden estricto inducido por la membresía en un conjunto S.

        **Definición**: ∈[S] = {⟨x,y⟩ | x ∈ S ∧ y ∈ S ∧ x ∈ y}

        Este orden captura la estructura de membresía de S como una relación
        de orden. Para conjuntos transitivos (como los naturales), esta relación
        tiene propiedades especiales (asimetría, tricotomía, bien-orden).

        **Notación**: ∈[S] se lee "orden-épsilon en S" o "membresía restringida a S" -/
    noncomputable def StrictOrderMembershipGuided (S : U) : U :=
      SpecSet (S ×ₛ S) (fun p => ∃ x y, p = ⟨x, y⟩ ∧ x ∈ y)

    notation "∈[" S "]" => StrictOrderMembershipGuided S

    /-- Specification for membership-guided strict order -/
    theorem mem_StrictOrderMembershipGuided (S x y : U) :
      ⟨x, y⟩ ∈ (∈[S]) ↔ x ∈ S ∧ y ∈ S ∧ x ∈ y := by
      unfold StrictOrderMembershipGuided
      rw [SpecSet_is_specified]
      constructor
      · intro ⟨hp_cart, a, b, hab, hab'⟩
        have h_eq := Eq_of_OrderedPairs_given_projections _ _ _ _ hab
        rw [CartesianProduct_is_specified] at hp_cart
        obtain ⟨_, hfst, hsnd⟩ := hp_cart
        rw [fst_of_ordered_pair] at hfst
        rw [snd_of_ordered_pair] at hsnd
        rw [←h_eq.1, ←h_eq.2] at hab'
        exact ⟨hfst, hsnd, hab'⟩
      · intro ⟨hx, hy, hxy⟩
        constructor
        · rw [CartesianProduct_is_specified]
          refine ⟨⟨x, y, rfl⟩, ?_, ?_⟩
          · rw [fst_of_ordered_pair]
            exact hx
          · rw [snd_of_ordered_pair]
            exact hy
        · exact ⟨x, y, rfl, hxy⟩

    /-! ### Orden Total Estricto Guiado por Membresía ### -/
    /-- La relación ∈[S] es un orden total estricto en S.

        **Definición**: S tiene orden total estricto si:
        1. S es transitivo
        2. **Asimetría**: ∀x,y ∈ S, (x ∈ y → y ∉ x)
        3. **Tricotomía**: ∀x,y ∈ S, (x ∈ y ∨ x = y ∨ y ∈ x)

        La tricotomía significa que cualesquiera dos elementos de S son comparables.
        La asimetría garantiza que la relación es irreflexiva y antisimétrica.

        Para conjuntos transitivos, estas propiedades hacen de ∈[S] un orden lineal. -/
    def isTotalStrictOrderMembershipGuided (S : U) : Prop :=
      isTransitiveSet S ∧
      (∀ x y, x ∈ S → y ∈ S → x ∈ y → y ∉ x) ∧
      (∀ x y, x ∈ S → y ∈ S → (x ∈ y ∨ x = y ∨ y ∈ x))

    /-! ### Bien Ordenado (Finito) Guiado por Membresía ### -/
    /-- ⟨S, ∈[S]⟩ está bien ordenado (en sentido finito).

        **Definición**: S está bien ordenado si todo subconjunto no vacío T ⊆ S tiene:
        1. **Elemento mínimo**: ∃m ∈ T, ∀x ∈ T, (m = x ∨ m ∈ x)
        2. **Elemento máximo**: ∃M ∈ T, ∀x ∈ T, (M = x ∨ x ∈ M)

        **Nota crucial**: La existencia de MÁXIMO es la característica distintiva
        de conjuntos FINITOS. En ordinales infinitos (como ω), hay subconjuntos
        sin elemento máximo (por ejemplo, ω mismo no tiene máximo).

        Esta definición bicondicional (mínimo Y máximo) caracteriza precisamente
        los ordinales finitos, es decir, los números naturales. -/
    def isWellOrderMembershipGuided (S : U) : Prop :=
      ∀ T, T ⊆ S → T ≠ (∅ : U) →
        (∃ m, m ∈ T ∧ ∀ x, x ∈ T → (m = x ∨ m ∈ x)) ∧ -- Mínimo
        (∃ M, M ∈ T ∧ ∀ x, x ∈ T → (M = x ∨ x ∈ M))   -- Máximo

    /-! ============================================================ -/
    /-! ### DEFINICIÓN DE NÚMERO NATURAL ### -/
    /-! ============================================================ -/

    /-- **DEFINICIÓN PRINCIPAL**: n es un número natural (ordinal finito de von Neumann)

        Un conjunto n es un número natural si y solo si cumple TRES condiciones:

        1. **n es transitivo**: ∀x ∈ n, x ⊆ n
           (cada elemento de n es también un subconjunto de n)

        2. **∈[n] es un orden total estricto**: ∀x,y ∈ n, (x ∈ y ∨ x = y ∨ y ∈ x)
           (cualesquiera dos elementos de n son comparables por membresía)

        3. **⟨n, ∈[n]⟩ está bien ordenado (finito)**:
           - Todo subconjunto no vacío tiene elemento MÍNIMO
           - Todo subconjunto no vacío tiene elemento MÁXIMO

        **Observación crucial**: La condición (3) con MÁXIMO distingue los naturales
        de los ordinales infinitos. En ω (el primer ordinal infinito), ω mismo es
        un subconjunto sin elemento máximo.

        **Ejemplos**:
        - 0 = ∅ es natural (vacuamente)
        - 1 = {∅} es natural
        - 2 = {∅, {∅}} es natural
        - 3 = {∅, {∅}, {∅, {∅}}} es natural

        **Construcción**: Si n es natural, entonces σ(n) = n ∪ {n} es natural.

        Esta definición NO usa el Axioma de Infinito y caracteriza los naturales
        intrínsecamente, sin referencia a un conjunto ω de "todos los naturales". -/
    def isNat (n : U) : Prop :=
      isTransitiveSet n ∧
      isTotalStrictOrderMembershipGuided n ∧
      isWellOrderMembershipGuided n

    /-! ============================================================ -/
    /-! ### TEOREMAS FUNDAMENTALES ### -/
    /-! ============================================================ -/

    /-- **TEOREMA BASE**: El conjunto vacío es un número natural.

        **Enunciado**: isNat ∅

        Este es el punto de partida de la construcción inductiva de naturales.
        La prueba es vacua porque ∅ no tiene elementos, así que:
        - Es vacuamente transitivo (no hay x ∈ ∅ que verificar)
        - Tiene vacuamente orden total (no hay x,y ∈ ∅ que comparar)
        - Está vacuamente bien ordenado (no hay subconjuntos no vacíos de ∅)

        Esta prueba vacua es típica del caso base en construcciones ordinales.

        **Notación**: Usaremos 0 ≡ ∅ como el primer natural. -/
    theorem zero_is_nat : isNat (∅ : U) := by
      unfold isNat isTotalStrictOrderMembershipGuided isWellOrderMembershipGuided
      refine ⟨?_, ?_, ?_⟩
      · -- ∅ is transitive
        unfold isTransitiveSet
        intro x hx
        exfalso
        exact EmptySet_is_empty x hx
      · -- ∈[∅] is a total strict order
        refine ⟨?_, ?_, ?_⟩
        · -- ∅ is transitive (proven above)
          unfold isTransitiveSet
          intro x hx
          exfalso
          exact EmptySet_is_empty x hx
        · -- asymmetry on ∅ (vacuously true)
          intro x y hx _ _
          exfalso
          exact EmptySet_is_empty x hx
        · -- trichotomy on ∅ (vacuously true)
          intro x y hx _
          exfalso
          exact EmptySet_is_empty x hx
      · -- ∅ is well-ordered (vacuously true)
        intro T hT hT_nonempty
        exfalso
        have : T = (∅ : U) := by
          apply ExtSet
          intro z
          constructor
          · intro hz
            have hz_empty : z ∈ (∅ : U) := hT z hz
            exact False.elim (EmptySet_is_empty z hz_empty)
          · intro hz
            exact False.elim (EmptySet_is_empty z hz)
        exact hT_nonempty this

    /-! ============================================================ -/
    /-! ### PROPIEDADES AUXILIARES DEL SUCESOR ### -/
    /-! ============================================================ -/

    /-- **Lema auxiliar**: Todo elemento pertenece a su sucesor.

        **Enunciado**: n ∈ σ(n)

        Por definición, σ(n) = n ∪ {n}, así que n ∈ {n} ⊆ σ(n).
        Este lema es fundamental para muchas pruebas sobre sucesores. -/
    theorem mem_successor_self (n : U) : n ∈ (σ n) := by
      rw [successor_is_specified]
      exact Or.inr rfl

    /-- **Lema de characterización**: x ∈ σ(n) ⟺ x ∈ n ∨ x = n

        El sucesor añade exactamente un nuevo elemento (n mismo) al conjunto n.
        Esta characterización es útil para razonar por casos sobre elementos de sucesores. -/
    theorem subset_of_mem_successor (n x : U) :
      x ∈ (σ n) → x ∈ n ∨ x = n := by
      intro hx
      rw [successor_is_specified] at hx
      exact hx

    /-- **Lema de preservación**: La membresía se preserva al tomar sucesores.

        **Enunciado**: n ∈ m → n ∈ σ(m)

        Si n está en m, también está en σ(m) = m ∪ {m}.
        Este lema es útil para probar propiedades de orden. -/
    theorem mem_successor_of_mem (n m : U) (h : n ∈ m) : n ∈ σ m := by
      rw [successor_is_specified]
      left
      exact h

    /-- **Teorema de preservación de transitividad**: Si n es transitivo, σ(n) es transitivo.

        **Enunciado**: isTransitiveSet n → isTransitiveSet σ(n)

        Este teorema es crucial para probar que nat_successor_is_nat.
        La prueba analiza dos casos para x ∈ σ(n):
        - Si x ∈ n: usa transitividad de n
        - Si x = n: entonces los elementos de x están en n ⊆ σ(n)

        La transitividad es la primera propiedad que debe verificarse
        para mostrar que σ(n) es natural. -/
    theorem successor_preserves_transitivity (n : U) (hn : isTransitiveSet n) :
      isTransitiveSet (σ n) := by
      unfold isTransitiveSet at hn ⊢
      intro x hx y hy
      simp only [successor_is_specified] at hx ⊢
      cases hx with
      | inl hx_in_n =>
        -- x ∈ n, so x ⊆ n by transitivity of n
        have hx_sub : x ⊆ n := hn x hx_in_n
        left
        exact hx_sub y hy
      | inr hx_eq_n =>
        -- x = n, so y ∈ x means y ∈ n
        rw [hx_eq_n] at hy
        left
        exact hy

    /-! ### Lema: elementos de un conjunto transitivo están contenidos en él ### -/
    theorem transitive_element_subset (S x : U)
      (hS : isTransitiveSet S) (hx : x ∈ S) :
      x ⊆ S := by
      unfold isTransitiveSet at hS
      exact hS x hx

    /-! ### Lema auxiliar: No hay 3-ciclo de elementos dentro de un natural ### -/
    /-- Helper lemma for nat_element_is_transitive -/
    private theorem no_three_cycle_in_nat (n m k l : U) (hn : isNat n)
        (hm_in_n : m ∈ n) (hk_in_n : k ∈ n) (hl_in_n : l ∈ n)
        (hm_in_l : m ∈ l) (hl_in_k : l ∈ k) (hk_in_m : k ∈ m) : False := by
      obtain ⟨hn_trans, ⟨_, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      -- Construct {m, k, l} as subset of n
      let S := {m, k} ∪ ({l} : U)
      have hS_sub : S ⊆ n := by
        intro x hx
        rw [BinUnion_is_specified] at hx
        cases hx with
        | inl hxmk =>
          rw [PairSet_is_specified] at hxmk
          cases hxmk with
          | inl hxm => rw [hxm]; exact hm_in_n
          | inr hxk => rw [hxk]; exact hk_in_n
        | inr hxl =>
          rw [Singleton_is_specified] at hxl
          rw [hxl]; exact hl_in_n
      have hS_nonempty : S ≠ (∅ : U) := by
        intro h_eq
        have : m ∈ S := by
          rw [BinUnion_is_specified]
          left
          rw [PairSet_is_specified]
          left; rfl
        rw [h_eq] at this
        exact EmptySet_is_empty m this
      -- Apply well-ordering (only min needed here) to get minimal element
      obtain ⟨w, hw_in_S, hw_min⟩ := (hn_wo S hS_sub hS_nonempty).1
      -- w ∈ S means w ∈ {m, k} ∨ w ∈ {l}
      rw [BinUnion_is_specified] at hw_in_S
      cases hw_in_S with
      | inl hw_mk =>
        rw [PairSet_is_specified] at hw_mk
        cases hw_mk with
        | inl hw_eq_m =>
          -- m is minimal, so m ≤ k and m ≤ l
          rw [hw_eq_m] at hw_min
          have hm_k : m = k ∨ m ∈ k := hw_min k (by
            rw [BinUnion_is_specified]; left; rw [PairSet_is_specified]; right; rfl)
          have hm_l : m = l ∨ m ∈ l := hw_min l (by
            rw [BinUnion_is_specified]; right; rw [Singleton_is_specified])
          cases hm_k with
          | inl hmk_eq =>
            -- m = k, but k ∈ m, contradiction
            rw [hmk_eq] at hk_in_m
            exact absurd hk_in_m (hn_asym k k hk_in_n hk_in_n hk_in_m)
          | inr hm_in_k =>
            -- m ∈ k and k ∈ m, contradiction by asymmetry
            exact absurd hk_in_m (hn_asym m k hm_in_n hk_in_n hm_in_k)
        | inr hw_eq_k =>
          -- k is minimal, so k ≤ m and k ≤ l
          rw [hw_eq_k] at hw_min
          have hk_m : k = m ∨ k ∈ m := hw_min m (by
            rw [BinUnion_is_specified]; left; rw [PairSet_is_specified]; left; rfl)
          have hk_l : k = l ∨ k ∈ l := hw_min l (by
            rw [BinUnion_is_specified]; right; rw [Singleton_is_specified])
          cases hk_m with
          | inl hkm_eq =>
            -- k = m, but k ∈ m, contradiction
            rw [←hkm_eq] at hk_in_m
            exact absurd hk_in_m (hn_asym k k hk_in_n hk_in_n hk_in_m)
          | inr hk_in_m' =>
            -- k ∈ m, this matches our hypothesis
            -- Check k vs l
            cases hk_l with
            | inl hkl_eq =>
              -- k = l, but l ∈ k, contradiction
              rw [hkl_eq] at hl_in_k
              exact absurd hl_in_k (hn_asym l l hl_in_n hl_in_n hl_in_k)
            | inr hk_in_l' =>
              -- k ∈ l and l ∈ k, contradiction by asymmetry
              exact absurd hl_in_k (hn_asym k l hk_in_n hl_in_n hk_in_l')
      | inr hw_l =>
        -- l is minimal
        rw [Singleton_is_specified] at hw_l
        rw [hw_l] at hw_min
        have hl_m : l = m ∨ l ∈ m := hw_min m (by
          rw [BinUnion_is_specified]; left; rw [PairSet_is_specified]; left; rfl)
        have hl_k : l = k ∨ l ∈ k := hw_min k (by
          rw [BinUnion_is_specified]; left; rw [PairSet_is_specified]; right; rfl)
        cases hl_m with
        | inl hlm_eq =>
          -- l = m, but m ∈ l, contradiction
          rw [←hlm_eq] at hm_in_l
          exact absurd hm_in_l (hn_asym l l hl_in_n hl_in_n hm_in_l)
        | inr hl_in_m =>
          -- l ∈ m and m ∈ l, contradiction by asymmetry
          exact absurd hm_in_l (hn_asym l m hl_in_n hm_in_n hl_in_m)

    /-! ============================================================ -/
    /-! ### BUENA FUNDACIÓN DE NATURALES (SIN AXIOMA DE REGULARIDAD) ### -/
    /-! ============================================================ -/

    /-- **TEOREMA FUNDAMENTAL**: Ningún número natural es miembro de sí mismo.

        **Enunciado**: isNat n → n ∉ n

        Este teorema establece la irreflexividad de la membresía en naturales.
        Es crucial porque:
        1. Se prueba SIN usar el Axioma de Regularidad
        2. Usa solo la asimetría del orden total estricto en n
        3. Es la base para probar que no hay ciclos de membresía

        **Prueba**: Si n ∈ n, entonces por asimetría de n: n ∈ n → n ∉ n,
        contradicción. -/
    theorem nat_not_mem_self (n : U) :
      isNat n → n ∉ n := by
      intro ⟨_, ⟨_,hasym, _⟩, _⟩ hn_mem
      -- By asymmetry: if n ∈ n then n ∉ n
      have : n ∉ n := hasym n n hn_mem hn_mem hn_mem
      exact this hn_mem

    /-- **TEOREMA**: No existen ciclos de membresía de dos elementos entre naturales.

        **Enunciado**: isNat x → isNat y → ¬(x ∈ y ∧ y ∈ x)

        Si x e y son naturales y x ∈ y, entonces y ∉ x.
        Esto prueba que la membresía entre naturales es antisimétrica.

        **Prueba**: Si x ∈ y y y ∈ x:
        - Si x = y: entonces x ∈ x, contradiciendo nat_not_mem_self
        - Si x ≠ y: por transitividad de y, tendríamos y ∈ y, contradicción -/
    theorem nat_no_two_cycle (x y : U) :
      isNat x → isNat y → ¬(x ∈ y ∧ y ∈ x) := by
      intro hx hy hmem
      obtain ⟨hxy, hyx⟩ := hmem
      -- Distinguish two cases: x = y or x ≠ y
      by_cases h_eq : x = y
      · -- Case: x = y
        -- Then x ∈ y means x ∈ x, contradicting nat_not_mem_self
        rw [h_eq] at hxy
        exact nat_not_mem_self y hy hxy
      · -- Case: x ≠ y
        -- Since both are naturals, we have trichotomy
        -- But we have both x ∈ y and y ∈ x
        -- By asymmetry of y (since y is nat): x ∈ y → ¬(y ∈ x)
        have ⟨_, ⟨_, y_asym, _⟩, _⟩ := hy
        -- x and y are both in y since y is transitive and x ⊆ y
        have y_trans : isTransitiveSet y := hy.1
        have x_sub_y : x ⊆ y := y_trans x hxy
        have y_in_y : y ∈ y := x_sub_y y hyx
        -- But this contradicts nat_not_mem_self
        exact nat_not_mem_self y hy y_in_y

    /-- **TEOREMA**: No existen ciclos de membresía de tres elementos entre naturales.

        **Enunciado**: isNat x → isNat y → isNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x)

        Este teorema generaliza la ausencia de ciclos a tres elementos.
        Es importante para establecer que la membresía en naturales es acíclica.

        **Prueba**: Si x ∈ y, y ∈ z, z ∈ x, entonces por transitividad de x:
        z ⊆ x, luego y ∈ x, formando un 2-ciclo x ∈ y ∧ y ∈ x, contradicción. -/
    theorem nat_no_three_cycle (x y z : U) :
      isNat x → isNat y → isNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x) := by
      intro hx hy hz hmem
      obtain ⟨hxy, hyz, hzx⟩ := hmem
      -- Since x is transitive and z ∈ x, we have z ⊆ x
      have x_trans : isTransitiveSet x := hx.1
      have z_sub_x : z ⊆ x := x_trans z hzx
      -- Since y ∈ z and z ⊆ x, we have y ∈ x
      have hyx : y ∈ x := z_sub_x y hyz
      -- Now we have x ∈ y and y ∈ x, which is a 2-cycle
      exact nat_no_two_cycle x y hx hy ⟨hxy, hyx⟩

    /-- **Lema estructural**: Elementos de naturales son transitivos.

        **Enunciado**: isNat n → m ∈ n → isTransitiveSet m

        Este lema establece que la propiedad de transitividad se hereda
        a los elementos. Es uno de los tres componentes necesarios para probar
        que nat_element_is_nat.

        **Prueba compleja**: Usa tricotomía y análisis de casos exhaustivo,
        apoyado en no_three_cycle_in_nat para eliminar casos imposibles.
        Es una de las pruebas más técnicas del archivo. -/
    theorem nat_element_is_transitive (n m : U)
      (hn : isNat n) (hm_in_n : m ∈ n) :
      isTransitiveSet m := by
      -- Si m ∈ n y n es natural, entonces m es natural por nat_element_is_nat
      -- Y si m es natural, entonces m es transitivo por definición
      -- Pero nat_element_is_nat aún no está completo, así que probamos directamente
      obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      -- Reconstruir hn para usarlo después
      have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩
      unfold isTransitiveSet at hn_trans ⊢
      intro k hk_in_m
      -- m ∈ n and n transitive implies m ⊆ n
      have hm_sub_n : m ⊆ n := hn_trans m hm_in_n
      -- k ∈ m and m ⊆ n implies k ∈ n
      have hk_in_n : k ∈ n := hm_sub_n k hk_in_m
      -- k ∈ n and n transitive implies k ⊆ n
      have hk_sub_n : k ⊆ n := hn_trans k hk_in_n
      -- Now we need to prove k ⊆ m
      intro l hl_in_k
      -- l ∈ k and k ⊆ n implies l ∈ n
      have hl_in_n : l ∈ n := hk_sub_n l hl_in_k
      -- By trichotomy in n: l ∈ m ∨ l = m ∨ m ∈ l
      have htrich : l ∈ m ∨ l = m ∨ m ∈ l := hn_trich l m hl_in_n hm_in_n
      cases htrich with
      | inl h => exact h  -- l ∈ m, done
      | inr h => cases h with
        | inl hl_eq_m =>
          -- l = m, so m ∈ k and k ∈ m, contradiction by asymmetry
          rw [hl_eq_m] at hl_in_k
          exact absurd hk_in_m (hn_asym m k hm_in_n hk_in_n hl_in_k)
        | inr hm_in_l =>
          -- m ∈ l, l ∈ k, k ∈ m forms a 3-cycle in n
          -- By trichotomy on k and l: k ∈ l ∨ k = l ∨ l ∈ k
          have htrich_kl : k ∈ l ∨ k = l ∨ l ∈ k := hn_trich k l hk_in_n hl_in_n
          cases htrich_kl with
          | inl hk_in_l =>
            -- k ∈ l and l ∈ k, contradiction by asymmetry
            exact absurd hl_in_k (hn_asym k l hk_in_n hl_in_n hk_in_l)
          | inr hkl => cases hkl with
            | inl hk_eq_l =>
              -- k = l, so l ∈ k = l ∈ l, contradiction
              rw [←hk_eq_l] at hl_in_k
              exact absurd hl_in_k (hn_asym k k hk_in_n hk_in_n hl_in_k)
            | inr hl_in_k' =>
              -- l ∈ k is our hypothesis, so we have: m ∈ l, l ∈ k, k ∈ m
              -- Apply well-ordering to {m, k} ⊆ n
              have hmk_sub : ({m, k} : U) ⊆ n := by
                intro x hx
                rw [PairSet_is_specified] at hx
                cases hx with
                | inl hxm => rw [hxm]; exact hm_in_n
                | inr hxk => rw [hxk]; exact hk_in_n
              have hmk_nonempty : ({m, k} : U) ≠ (∅ : U) := by
                intro h_eq
                have : m ∈ ({m, k} : U) := by rw [PairSet_is_specified]; left; rfl
                rw [h_eq] at this
                exact EmptySet_is_empty m this
              obtain ⟨w, hw_in, hw_min⟩ := (hn_wo ({m, k} : U) hmk_sub hmk_nonempty).1
              rw [PairSet_is_specified] at hw_in
              cases hw_in with
              | inl hw_eq_m =>
                -- w = m is minimal, so ∀ x ∈ {m,k}: m = x ∨ m ∈ x
                rw [hw_eq_m] at hw_min
                have hm_k := hw_min k (by rw [PairSet_is_specified]; right; rfl)
                cases hm_k with
                | inl hmk_eq =>
                  -- m = k, but k ∈ m, contradiction
                  rw [hmk_eq] at hk_in_m
                  exact absurd hk_in_m (hn_asym k k hk_in_n hk_in_n hk_in_m)
                | inr hm_k_mem =>
                  -- m ∈ k, but also k ∈ m, contradiction by asymmetry
                  exact absurd hk_in_m (hn_asym m k hm_in_n hk_in_n hm_k_mem)
              | inr hw_eq_k =>
                -- w = k is minimal, so ∀ x ∈ {m,k}: k = x ∨ k ∈ x
                rw [hw_eq_k] at hw_min
                have hk_m := hw_min m (by rw [PairSet_is_specified]; left; rfl)
                cases hk_m with
                | inl hkm_eq =>
                  -- k = m, but k ∈ m, contradiction
                  rw [←hkm_eq] at hk_in_m
                  exact absurd hk_in_m (hn_asym k k hk_in_n hk_in_n hk_in_m)
                | inr hk_m_mem =>
                  -- k ∈ m, this is our hypothesis hk_in_m
                  -- We have m ∈ l, l ∈ k, k ∈ m forming a 3-cycle in n
                  -- Use no_three_cycle_in_nat
                  exact False.elim (no_three_cycle_in_nat n m k l hn_reconstructed hm_in_n hk_in_n hl_in_n hm_in_l hl_in_k hk_in_m)

    /-- **Lema estructural**: Elementos de naturales tienen orden total estricto.

        **Enunciado**: isNat n → m ∈ n → isTotalStrictOrderMembershipGuided m

        El orden total se hereda de n a sus elementos m porque:
        - m ⊆ n (por transitividad de n)
        - La asimetría y tricotomía en n se restringen a m

        Este es el segundo componente para nat_element_is_nat. -/
    theorem nat_element_has_strict_total_order (n m : U)
      (hn : isNat n) (hm_in_n : m ∈ n) :
      isTotalStrictOrderMembershipGuided m := by
      obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      unfold isTotalStrictOrderMembershipGuided

      -- Reconstruir hn para usarlo
      have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩

      -- m ⊆ n porque n es transitivo
      have hm_sub_n : m ⊆ n := hn_trans m hm_in_n

      refine ⟨?_, ?_, ?_⟩

      · -- m es transitivo (ya probado en nat_element_is_transitive)
        exact nat_element_is_transitive n m hn_reconstructed hm_in_n

      · -- Asimetría en m: si x ∈ m, y ∈ m, x ∈ y, entonces y ∉ x
        intro x y hx_in_m hy_in_m hxy
        -- x ∈ m y m ⊆ n implica x ∈ n
        have hx_in_n : x ∈ n := hm_sub_n x hx_in_m
        -- y ∈ m y m ⊆ n implica y ∈ n
        have hy_in_n : y ∈ n := hm_sub_n y hy_in_m
        -- Por asimetría en n: x ∈ y → y ∉ x (en n)
        exact hn_asym x y hx_in_n hy_in_n hxy

      · -- Tricotomía en m: si x ∈ m, y ∈ m, entonces x ∈ y ∨ x = y ∨ y ∈ x
        intro x y hx_in_m hy_in_m
        -- x ∈ m y m ⊆ n implica x ∈ n
        have hx_in_n : x ∈ n := hm_sub_n x hx_in_m
        -- y ∈ m y m ⊆ n implica y ∈ n
        have hy_in_n : y ∈ n := hm_sub_n y hy_in_m
        -- Por tricotomía en n
        have htrich_n : x ∈ y ∨ x = y ∨ y ∈ x := hn_trich x y hx_in_n hy_in_n
        -- Como x, y están en m que está en n, la tricotomía se preserva
        exact htrich_n

    /-- **Lema estructural**: Elementos de naturales están bien ordenados.

        **Enunciado**: isNat n → m ∈ n → isWellOrderMembershipGuided m

        El bien-orden se hereda porque para T ⊆ m ⊆ n no vacío:
        - n está bien ordenado, así que T tiene mínimo y máximo en n
        - Estos mínimo/máximo también están en T ⊆ m

        Este es el tercer y último componente para nat_element_is_nat. -/
    theorem nat_element_has_well_order (n m : U)
      (hn : isNat n) (hm_in_n : m ∈ n) :
      isWellOrderMembershipGuided m := by
      obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      unfold isWellOrderMembershipGuided

      -- m ⊆ n porque n es transitivo
      have hm_sub_n : m ⊆ n := hn_trans m hm_in_n

      -- Para cualquier T ⊆ m no vacío, debemos encontrar un mínimo Y un máximo
      intro T hT_sub_m hT_ne_empty

      -- T ⊆ m y m ⊆ n implica T ⊆ n
      have hT_sub_n : T ⊆ n := by
        intro x hx_in_T
        have hx_in_m : x ∈ m := hT_sub_m x hx_in_T
        exact hm_sub_n x hx_in_m

      -- Como n tiene bien-orden (completo) y T ⊆ n, T ≠ ∅:
      -- 1. Existe mínimo
      obtain ⟨min, hmin_in_T, hmin_is_min⟩ := (hn_wo T hT_sub_n hT_ne_empty).1
      -- 2. Existe máximo
      obtain ⟨max, hmax_in_T, hmax_is_max⟩ := (hn_wo T hT_sub_n hT_ne_empty).2

      -- Devolvemos ambos
      constructor
      · exact ⟨min, hmin_in_T, hmin_is_min⟩
      · exact ⟨max, hmax_in_T, hmax_is_max⟩

    /-- **TEOREMA FUNDAMENTAL**: Todo elemento de un número natural es un número natural.

        **Enunciado**: isNat n → m ∈ n → isNat m

        Este teorema establece que los naturales son "cerrados hacia abajo":
        si n es natural, entonces todos sus elementos son también naturales.

        **Consecuencias**:
        - Los naturales forman una jerarquía: 0 ∈ 1 ∈ 2 ∈ 3 ∈ ...
        - Cada natural es exactamente el conjunto de todos los naturales menores
        - Esto justifica la representación: n = {0, 1, 2, ..., n-1}

        **Prueba**: Demostramos que m hereda las tres propiedades de isNat:
        1. m es transitivo (por nat_element_is_transitive)
        2. m tiene orden total estricto (por nat_element_has_strict_total_order)
        3. m está bien ordenado (por nat_element_has_well_order) -/
    theorem nat_element_is_nat (n m : U) :
      isNat n → m ∈ n → isNat m := by
      intro hn hm_in_n
      unfold isNat
      refine ⟨?_, ?_, ?_⟩
      · -- m es transitivo
        exact nat_element_is_transitive n m hn hm_in_n
      · -- m tiene orden total estricto
        exact nat_element_has_strict_total_order n m hn hm_in_n
      · -- m tiene bien-orden
        exact nat_element_has_well_order n m hn hm_in_n

    /-! ### Lemas previos para demostrar que el sucesor de un natural es natural ### -/

    /-- n ≠ σ n para todo natural n -/
    theorem nat_ne_successor (n : U) (hn : isNat n) : n ≠ σ n := by
      intro h_eq
      have : n ∈ σ n := mem_successor_self n
      rw [←h_eq] at this
      exact nat_not_mem_self n hn this

    /-- σ n es transitivo si n es natural -/
    theorem successor_of_nat_is_transitive (n : U) (hn : isNat n) :
      isTransitiveSet (σ n) := by
      obtain ⟨hn_trans, _, _⟩ := hn
      unfold isTransitiveSet
      intro x hx_in_succ y hy_in_x
      rw [successor_is_specified] at hx_in_succ ⊢
      cases hx_in_succ with
      | inl hx_in_n =>
        -- x ∈ n, por transitividad de n: y ∈ x → y ∈ n
        left
        exact hn_trans x hx_in_n y hy_in_x
      | inr hx_eq_n =>
        -- x = n, entonces y ∈ n
        left
        rw [hx_eq_n] at hy_in_x
        exact hy_in_x

    /-- σ n tiene orden total estricto si n es natural -/
    theorem successor_of_nat_has_strict_total_order (n : U) (hn : isNat n) :
      isTotalStrictOrderMembershipGuided (σ n) := by
      obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      unfold isTotalStrictOrderMembershipGuided

      refine ⟨?_, ?_, ?_⟩

      · -- σ n es transitivo (ya lo tenemos)
        exact successor_of_nat_is_transitive n ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩

      · -- Asimetría en σ n: x ∈ y → y ∉ x para x, y ∈ σ n
        intro x y hx_in_succ hy_in_succ hxy
        rw [successor_is_specified] at hx_in_succ hy_in_succ
        cases hx_in_succ with
        | inl hx_in_n =>
          cases hy_in_succ with
          | inl hy_in_n =>
            -- x, y ∈ n: usar asimetría de n
            exact hn_asym x y hx_in_n hy_in_n hxy
          | inr hy_eq_n =>
            -- x ∈ n, y = n, entonces x ∈ y es x ∈ n; queremos y ∉ x, es decir n ∉ x
            intro hn_in_x
            rw [hy_eq_n] at hn_in_x
            -- x ∈ n y n ∈ x implica n ∈ n por transitividad
            have : n ∈ n := hn_trans_self x hx_in_n n hn_in_x
            exact nat_not_mem_self n ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ this
        | inr hx_eq_n =>
          cases hy_in_succ with
          | inl hy_in_n =>
            -- x = n, y ∈ n, entonces x ∈ y es n ∈ y; queremos y ∉ x, es decir y ∉ n
            intro hy_in_n'
            rw [hx_eq_n] at hxy
            -- y ∈ n y n ∈ y implica n ∈ n por transitividad
            have : n ∈ n := hn_trans_self y hy_in_n n hxy
            exact nat_not_mem_self n ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ this
          | inr hy_eq_n =>
            -- x = n, y = n, entonces x ∈ y es n ∈ n: imposible
            rw [hx_eq_n, hy_eq_n] at hxy
            exfalso
            exact nat_not_mem_self n ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ hxy

      · -- Tricotomía en σ n: x ∈ y ∨ x = y ∨ y ∈ x para x, y ∈ σ n
        intro x y hx_in_succ hy_in_succ
        rw [successor_is_specified] at hx_in_succ hy_in_succ
        cases hx_in_succ with
        | inl hx_in_n =>
          cases hy_in_succ with
          | inl hy_in_n =>
            -- x, y ∈ n: usar tricotomía de n
            exact hn_trich x y hx_in_n hy_in_n
          | inr hy_eq_n =>
            -- x ∈ n, y = n, entonces x ∈ y
            left
            rw [hy_eq_n]
            exact hx_in_n
        | inr hx_eq_n =>
          cases hy_in_succ with
          | inl hy_in_n =>
            -- x = n, y ∈ n, entonces y ∈ x
            right
            right
            rw [hx_eq_n]
            exact hy_in_n
          | inr hy_eq_n =>
            -- x = n, y = n, entonces x = y
            right
            left
            exact hx_eq_n.trans hy_eq_n.symm

    /-! ### Teorema: el sucesor de un natural es natural ### -/
    theorem nat_successor_is_nat (n : U) (hn : isNat n) : isNat (σ n) := by
      -- Desempaquetamos propiedades de n
      obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn

      -- Reconstruimos hn para usarlo después
      have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩

      -- Necesitamos probar 3 cosas: Transitividad, Orden Total Estricto, Bien-Orden (Min y Max)
      refine ⟨?_, ?_, ?_⟩

      -- 1. Transitividad
      · exact successor_of_nat_is_transitive n hn_reconstructed

      -- 2. Orden Total Estricto
      · exact successor_of_nat_has_strict_total_order n hn_reconstructed

      -- 3. Bien-Orden
      · unfold isWellOrderMembershipGuided
        intro A hA_sub hA_nonempty

        -- Definimos B = A ∩ n
        let B := A ∩ n

        -- 3.1 Existencia del MÍNIMO (ya estaba demostrado)
        have h_min : (∃ m, m ∈ A ∧ ∀ x, x ∈ A → m = x ∨ m ∈ x) := by
          by_cases hB_empty : B = (∅ : U)
          · -- Caso 1: B es vacío. A = {n}
            have hA_eq_n : A = {n} := by
              apply ExtSet
              intro x
              constructor
              · intro hx
                have hx_succ : x ∈ (σ n) := hA_sub x hx
                rw [successor_is_specified] at hx_succ
                cases hx_succ with
                | inl hx_n =>
                  have hx_B : x ∈ B := (BinInter_is_specified A n x).mpr ⟨hx, hx_n⟩
                  rw [hB_empty] at hx_B
                  exact False.elim (EmptySet_is_empty x hx_B)
                | inr hx_eq_n => rw [Singleton_is_specified]; exact hx_eq_n
              · intro hx; rw [Singleton_is_specified] at hx; rw [hx]
                obtain ⟨z, hz⟩ := nonempty_iff_exists_mem A |>.mp hA_nonempty
                have hz_succ : z ∈ (σ n) := hA_sub z hz
                rw [successor_is_specified] at hz_succ
                cases hz_succ with
                | inl hz_n =>
                  have hz_B : z ∈ B := (BinInter_is_specified A n z).mpr ⟨hz, hz_n⟩
                  rw [hB_empty] at hz_B
                  exact False.elim (EmptySet_is_empty z hz_B)
                | inr hz_eq_n => rw [←hz_eq_n]; exact hz
            exists n
            rw [hA_eq_n]
            constructor
            · apply (Singleton_is_specified n n).mpr rfl
            · intro x hx; rw [Singleton_is_specified] at hx; left; exact hx.symm
          · -- Caso 2: B no es vacío. Usamos el mínimo en n.
            have hB_sub_n : B ⊆ n := BinInter_subset A n |>.2
            have hB_nonempty : B ≠ (∅ : U) := hB_empty
            obtain ⟨m, hm_in_B, hm_min⟩ := (hn_wo B hB_sub_n hB_nonempty).1
            exists m
            constructor
            · exact (BinInter_is_specified A n m).mp hm_in_B |>.1
            · intro x hx_in_A
              have hx_succ := hA_sub x hx_in_A
              rw [successor_is_specified] at hx_succ
              cases hx_succ with
              | inl hx_n =>
                have hx_B : x ∈ B := (BinInter_is_specified A n x).mpr ⟨hx_in_A, hx_n⟩
                exact hm_min x hx_B
              | inr hx_eq_n =>
                right; rw [hx_eq_n]
                exact (BinInter_is_specified A n m).mp hm_in_B |>.2

        -- 3.2 Existencia del MÁXIMO (NUEVO)
        have h_max : (∃ M, M ∈ A ∧ ∀ x, x ∈ A → M = x ∨ x ∈ M) := by
          -- Caso A: n ∈ A. Entonces n es el máximo.
          by_cases hn_in_A : n ∈ A
          · exists n
            constructor
            · exact hn_in_A
            · intro x hx_in_A
              -- x ∈ A ⊆ n ∪ {n}, así que x ∈ n ∨ x = n
              have hx_succ := hA_sub x hx_in_A
              rw [successor_is_specified] at hx_succ
              cases hx_succ with
              | inl hx_n => right; exact hx_n -- x ∈ n
              | inr hx_eq_n => left; exact hx_eq_n.symm -- x = n
          -- Caso B: n ∉ A. Entonces A ⊆ n.
          · have hA_sub_n : A ⊆ n := by
              intro x hx
              have hx_succ := hA_sub x hx
              rw [successor_is_specified] at hx_succ
              cases hx_succ with
              | inl hx_n => exact hx_n
              | inr hx_eq_n =>
                -- Si x = n, entonces n ∈ A, contradicción
                rw [hx_eq_n] at hx
                contradiction
            -- Como A ⊆ n y A ≠ ∅, y n es natural, A tiene máximo en n.
            obtain ⟨M, hM_in_A, hM_max⟩ := (hn_wo A hA_sub_n hA_nonempty).2
            refine ⟨M, hM_in_A, hM_max⟩

        constructor
        · exact h_min
        · exact h_max

    /-! ### Elemento máximo en subconjuntos de naturales ### -/

    /-- **TEOREMA DE FINITUD**: Todo subconjunto no vacío de un natural tiene elemento máximo.

        **Enunciado**: isNat n → T ⊆ n → T ≠ ∅ →
                       ∃max ∈ T, ∀x ∈ T, (x ∈ max ∨ x = max)

        Este teorema caracteriza a los naturales como ordinales FINITOS.
        Es la distinción crucial entre naturales y ordinales infinitos:

        **Comparación**:
        - En un natural n: TODO subconjunto no vacío tiene máximo
        - En ω (primer ordinal infinito): ω mismo no tiene elemento máximo
        - En general: un ordinal es finito ⟺ es un natural ⟺ todo subconjunto tiene máximo

        **Estrategia de prueba**:
        Definimos Mx = {x ∈ T | ¬∃y ∈ T, x ∈ y ∧ x ≠ y} (elementos maximales)
        1. Si Mx ≠ ∅: cualquier elemento de Mx es el máximo buscado
        2. Si Mx = ∅: cada elemento tendría un sucesor en T, creando cadena
           infinita ascendente, contradiciendo que T ⊆ n está bien ordenado

        **Aplicaciones**:
        - Prueba que no hay cadenas infinitas ascendentes en naturales
        - Fundamenta la inducción matemática (principio de descenso infinito)
        - Distingue naturales de transfinitos sin necesidad de ω
    -/
    theorem nat_has_max (n T : U) (hn : isNat n) (hT_sub : T ⊆ n) (hT_ne : T ≠ ∅) :
      ∃ max, max ∈ T ∧ ∀ x, x ∈ T → (x ∈ max ∨ x = max) := by
      -- Definimos el conjunto de elementos maximales de T:
      -- aquellos que no tienen ningún elemento mayor en T
      let Mx := SpecSet T (fun x => ¬∃ y, y ∈ T ∧ x ∈ y ∧ x ≠ y)

      -- Si Mx ≠ ∅, cualquier elemento de Mx es el máximo buscado
      by_cases hMx : Mx ≠ ∅
      · -- Caso: existe al menos un elemento maximal
        have hMx_sub : Mx ⊆ T := by
          intro x hx
          rw [SpecSet_is_specified] at hx
          exact hx.1
        have hMx_sub_n : Mx ⊆ n := by
          intro x hx
          have : x ∈ T := hMx_sub x hx
          exact hT_sub x this
        -- Tomamos cualquier elemento de Mx (usando bien-orden)
        obtain ⟨max, hmax_in_Mx, _⟩ := (hn.2.2 Mx hMx_sub_n hMx).1
        exists max
        have hmax_in_T : max ∈ T := hMx_sub max hmax_in_Mx
        refine ⟨hmax_in_T, ?_⟩
        intro x hx_in_T
        -- Por tricotomía: x ∈ max ∨ x = max ∨ max ∈ x
        have hx_in_n : x ∈ n := hT_sub x hx_in_T
        have hmax_in_n : max ∈ n := hT_sub max hmax_in_T
        have htrich := hn.2.1.2.2 x max hx_in_n hmax_in_n
        cases htrich with
        | inl h => left; exact h  -- x ∈ max ✓
        | inr h => cases h with
          | inl h => right; exact h  -- x = max ✓
          | inr h =>  -- max ∈ x (contradicción)
            -- max es maximal, así que no puede existir x ∈ T con max ∈ x y max ≠ x
            exfalso
            have hmax_maximal : ¬∃ y, y ∈ T ∧ max ∈ y ∧ max ≠ y := by
              rw [SpecSet_is_specified] at hmax_in_Mx
              exact hmax_in_Mx.2
            apply hmax_maximal
            exists x
            refine ⟨hx_in_T, h, ?_⟩
            intro h_eq
            -- Si max = x, entonces max ∈ max (porque max ∈ x), contradicción
            have h_max_in_max : max ∈ max := h_eq ▸ h
            exact nat_not_mem_self max (nat_element_is_nat n max hn hmax_in_n) h_max_in_max

      · -- Caso: no hay elementos maximales
        -- Esto significa que para cada x ∈ T, existe y ∈ T con x ∈ y y x ≠ y
        -- Pero como T ⊆ n y n es bien-ordenado (tiene máximo), T debe tener un máximo M
        -- Si M es el máximo, entonces para todo x ∈ T, x ∈ M ∨ x = M
        -- Luego M debe ser maximal, contradiciendo que Mx = ∅
        have hMx_empty : Mx = ∅ := not_not.mp hMx
        -- Como T ⊆ n, T ≠ ∅, y n tiene la propiedad de máximo, T tiene un máximo
        obtain ⟨M, hM_in_T, hM_is_max⟩ := (hn.2.2 T hT_sub hT_ne).2

        -- Vamos a mostrar que M ∈ Mx, contradiciendo Mx = ∅
        have hM_in_Mx : M ∈ Mx := by
          rw [SpecSet_is_specified]
          refine ⟨hM_in_T, ?_⟩
          intro ⟨y, hy_in_T, hM_in_y, hM_ne_y⟩
          -- Si M ∈ y y M ≠ y, entonces por maximalidad de M: y ∈ M ∨ y = M
          have h_y_vs_M := hM_is_max y hy_in_T
          cases h_y_vs_M with
          | inl h_y_eq_M =>
            -- Si M = y, entonces M ≠ y es falso
            exact hM_ne_y h_y_eq_M
          | inr h_y_in_M =>
            -- Si y ∈ M, entonces tenemos M ∈ y y y ∈ M, violando asimetría
            have hM_in_n : M ∈ n := hT_sub M hM_in_T
            have hy_in_n : y ∈ n := hT_sub y hy_in_T
            have h_asym := hn.2.1.2.1 M y hM_in_n hy_in_n hM_in_y
            exact h_asym h_y_in_M

        -- Pero Mx = ∅, así que M ∉ Mx, contradicción
        exfalso
        rw [hMx_empty] at hM_in_Mx
        exact EmptySet_is_empty M hM_in_Mx

    /-! ### No hay naturales entre n y σ(n) ### -/

    /-- **TEOREMA**: El sucesor es el "siguiente" natural inmediato.

        **Enunciado**: isNat n → isNat m → n ∈ m → σ(n) ⊆ m

        Si n ∈ m (es decir, n < m), entonces σ(n) ⊆ m.
        Esto significa que no hay naturales "entre" n y su sucesor σ(n).

        **Interpretación aritmética**:
        En la representación ordinal n = {0,1,2,...,n-1}:
        - Si n < m, entonces n+1 ≤ m (no hay números entre n y n+1)
        - Los naturales son "discretos": no hay elementos intermedios

        **Consecuencias**:
        - Justifica que σ es el "sucesor inmediato"
        - Base para definir el orden < como: n < m ⟺ n ∈ m
        - Fundamental para la aritmética de naturales -/
    theorem no_nat_between (n m : U) (_hn : isNat n) (hm : isNat m)
        (hn_in_m : n ∈ m) : σ n ⊆ m := by
      obtain ⟨hm_trans, _, _⟩ := hm
      intro x hx_in_succ
      rw [successor_is_specified] at hx_in_succ
      cases hx_in_succ with
      | inl hx_in_n =>
        -- x ∈ n y n ∈ m, por transitividad de m: x ∈ m
        exact hm_trans n hn_in_m x hx_in_n
      | inr hx_eq_n =>
        -- x = n y n ∈ m, entonces x ∈ m
        rw [hx_eq_n]
        exact hn_in_m

    /-! ### Segmentos Iniciales ### -/

    /-- Un subconjunto S de n es un segmento inicial si es cerrado hacia abajo.
        Es decir, si x ∈ S y y ∈ x, entonces y ∈ S.
        Nota: Como n es transitivo, y ∈ x implica y ∈ n automáticamente. -/
    def isInitialSegment (S n : U) : Prop :=
      S ⊆ n ∧ ∀ x y, x ∈ S → y ∈ x → y ∈ S

    /-- Teorema clave: Un segmento inicial de un número natural n es igual a n
        o es un elemento de n.
        Este teorema es fundamental para probar la tricotomía entre naturales. -/
    theorem initial_segment_of_nat_is_eq_or_mem (n S : U)
      (hn : isNat n) (h_init : isInitialSegment S n) :
      S = n ∨ S ∈ n := by
      obtain ⟨hn_trans, ⟨_, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      -- Consideramos la diferencia n \ S
      let D := n \ S
      by_cases hD_empty : D = ∅
      · -- Caso 1: Si D es vacío, entonces S contiene todo n, por lo que S = n
        left
        apply ExtSet
        intro x
        constructor
        · exact h_init.1 x
        · intro hxn
          have hx_not_in_D : x ∉ D := by rw [hD_empty]; exact EmptySet_is_empty x
          rw [Difference_is_specified] at hx_not_in_D
          -- x ∈ n y ¬(x ∈ n ∧ x ∉ S) => x ∈ S
          by_cases hxs : x ∈ S
          · exact hxs
          · exact False.elim (hx_not_in_D ⟨hxn, hxs⟩)
      · -- Caso 2: Si D no es vacío, tiene un elemento mínimo m debido al buen orden de n
        right
        have hD_sub_n : D ⊆ n := Difference_subset n S
        have hD_nonempty : D ≠ ∅ := hD_empty
        obtain ⟨m, hm_in_D, hm_min⟩ := (hn_wo D hD_sub_n hD_nonempty).1

        -- Probaremos que S = m (recordemos que en ordinales, m = {y ∈ n | y ∈ m})
        have hS_eq_m : S = m := by
          apply ExtSet
          intro x
          constructor
          · -- Dirección S ⊆ m
            intro hxS
            -- x ∈ S. Como S ⊆ n, x ∈ n. m ∈ D ⊆ n, así que m ∈ n.
            have hxn : x ∈ n := h_init.1 x hxS
            have hmn : m ∈ n := hD_sub_n m hm_in_D
            -- Por tricotomía en n: x ∈ m ∨ x = m ∨ m ∈ x
            have h_tri := hn_trich x m hxn hmn
            cases h_tri with
            | inl hxm => exact hxm -- x ∈ m, lo que queremos
            | inr h_or =>
              cases h_or with
              | inl hxm =>
                -- x = m. Contradicción: x ∈ S pero m ∈ D (m ∉ S).
                rw [Difference_is_specified] at hm_in_D
                rw [hxm] at hxS
                exact False.elim (hm_in_D.2 hxS)
              | inr hmx =>
                -- m ∈ x. Contradicción: S es segmento inicial y x ∈ S => m ∈ S.
                -- Pero m ∈ D => m ∉ S.
                have hmS : m ∈ S := h_init.2 x m hxS hmx
                rw [Difference_is_specified] at hm_in_D
                exact False.elim (hm_in_D.2 hmS)
          · -- Dirección m ⊆ S
            intro hxm
            -- x ∈ m. Como m ∈ n y n es transitivo, x ∈ n.
            have hmn : m ∈ n := hD_sub_n m hm_in_D
            have hxn : x ∈ n := hn_trans m hmn x hxm
            -- Supongamos x ∉ S. Entonces x ∈ n \ S = D.
            by_cases hxS : x ∈ S
            · exact hxS
            · -- x ∈ D
              have hxD : x ∈ D := (Difference_is_specified n S x).mpr ⟨hxn, hxS⟩
              -- Como m es el mínimo de D, m ≤ x (m = x ∨ m ∈ x).
              have h_min_cond := hm_min x hxD
              cases h_min_cond with
              | inl hmx =>
                -- m = x. Contradicción con x ∈ m (irreflexividad)
                rw [hmx] at hxm
                exact False.elim (hn_asym x x hxn hxn hxm hxm)
              | inr hmx =>
                -- m ∈ x. Contradicción con x ∈ m (asimetría)
                exact False.elim (hn_asym m x hmn hxn hmx hxm)

        rw [hS_eq_m]
        -- m ∈ D ⊆ n, así que S ∈ n
        exact (Difference_is_specified n S m).mp hm_in_D |>.1

    /-! ### Tricotomía entre Naturales ### -/

    /-- Lema: La intersección de dos naturales es un segmento inicial de ambos. -/
    theorem inter_nat_is_initial_segment (n m : U) (hn : isNat n) (hm : isNat m) :
      isInitialSegment (n ∩ m) n ∧ isInitialSegment (n ∩ m) m := by
      constructor
      · -- n ∩ m es segmento inicial de n
        constructor
        · exact BinInter_subset n m |>.1
        · intro x y hx hy
          rw [BinInter_is_specified] at hx ⊢
          obtain ⟨hxn, hxm⟩ := hx
          constructor
          · exact hn.1 x hxn y hy
          · exact hm.1 x hxm y hy
      · -- n ∩ m es segmento inicial de m
        constructor
        · exact BinInter_subset n m |>.2
        · intro x y hx hy
          rw [BinInter_is_specified] at hx ⊢
          obtain ⟨hxn, hxm⟩ := hx
          constructor
          · exact hn.1 x hxn y hy
          · exact hm.1 x hxm y hy

    /-- Teorema de Tricotomía para Números Naturales:
        Dados dos naturales n y m, se cumple exactamente una de las siguientes:
        n ∈ m, n = m, o m ∈ n. -/
    theorem nat_trichotomy (n m : U) (hn : isNat n) (hm : isNat m) :
      n ∈ m ∨ n = m ∨ m ∈ n := by
      let k := n ∩ m
      have hk_init := inter_nat_is_initial_segment n m hn hm
      have hk_init_n : isInitialSegment k n := hk_init.1
      have hk_init_m : isInitialSegment k m := hk_init.2

      have h_n_cases := initial_segment_of_nat_is_eq_or_mem n k hn hk_init_n
      have h_m_cases := initial_segment_of_nat_is_eq_or_mem m k hm hk_init_m

      cases h_n_cases with
      | inl hk_eq_n =>
        cases h_m_cases with
        | inl hk_eq_m =>
          -- k = n y k = m -> n = m
          right; left
          rw [←hk_eq_n, hk_eq_m]
        | inr hk_in_m =>
          -- k = n y k ∈ m -> n ∈ m
          left
          rw [←hk_eq_n]
          exact hk_in_m
      | inr hk_in_n =>
        cases h_m_cases with
        | inl hk_eq_m =>
          -- k ∈ n y k = m -> m ∈ n
          right; right
          rw [←hk_eq_m]
          exact hk_in_n
        | inr hk_in_m =>
          -- k ∈ n y k ∈ m -> contradicción (k ∈ k)
          exfalso
          -- k ∈ n ∩ m = k
          have hk_in_k : k ∈ k := (BinInter_is_specified n m k).mpr ⟨hk_in_n, hk_in_m⟩
          -- k es natural porque es elemento de n
          have hk_nat : isNat k := nat_element_is_nat n k hn hk_in_n
          exact nat_not_mem_self k hk_nat hk_in_k

    /-! ### Lema: subconjunto natural es elemento o igual ### -/
    /-- Si n y m son naturales y n ⊆ m, entonces n ∈ m ∨ n = m -/
    theorem nat_subset_mem_or_eq
      (n m : U) (hn : isNat n) (hm : isNat m) (h_sub : n ⊆ m) :
      n ∈ m ∨ n = m
      := by
      -- Por tricotomía: n ∈ m ∨ n = m ∨ m ∈ n
      have h_trich := nat_trichotomy n m hn hm
      cases h_trich with
      | inl h => left; exact h          -- caso n ∈ m
      | inr h => cases h with
        | inl h => right; exact h       -- caso n = m
        | inr h_m_in_n =>               -- caso m ∈ n (imposible)
          -- Si m ∈ n y n ⊆ m, entonces m ⊆ n por transitividad de n
          -- Luego n = m por extensionalidad, pero entonces m ∈ m: contradicción
          exfalso
          have h_m_sub : m ⊆ n := hn.1 m h_m_in_n
          have h_eq : n = m := ExtSet_wc h_sub h_m_sub
          rw [h_eq] at h_m_in_n
          exact nat_not_mem_self m hm h_m_in_n

    /-! ### Transitividad de membresía entre naturales ### -/
    /-- Si n, m, k son naturales y n ∈ m, m ∈ k, entonces n ∈ k.
        La membresía entre naturales es transitiva. -/
    theorem nat_mem_trans (n m k : U) (_hn : isNat n) (_hm : isNat m) (hk : isNat k)
      (hnm : n ∈ m) (hmk : m ∈ k) : n ∈ k := by
      -- k es transitivo, así que m ∈ k implica m ⊆ k
      have hm_sub_k : m ⊆ k := hk.1 m hmk
      -- n ∈ m y m ⊆ k implica n ∈ k
      exact hm_sub_k n hnm

    /-! ### Asimetría de membresía entre naturales ### -/
    /-- Si n y m son naturales y n ∈ m, entonces m ∉ n.
        La membresía entre naturales es asimétrica. -/
    theorem nat_mem_asymm (n m : U) (hn : isNat n) (hm : isNat m)
      (hnm : n ∈ m) : m ∉ n := by
      intro hmn
      -- Si n ∈ m y m ∈ n, tendríamos un ciclo de 2 elementos
      exact nat_no_two_cycle n m hn hm ⟨hnm, hmn⟩

    /-! ### Propiedad de segmento inicial para naturales ### -/
    /-- Si n ∈ m (ambos naturales), entonces n es un segmento inicial de m. -/
    theorem nat_is_initial_segment (n m : U) (hn : isNat n) (hm : isNat m)
      (hnm : n ∈ m) : isInitialSegment n m := by
      constructor
      · -- n ⊆ m: por transitividad de m
        exact hm.1 n hnm
      · -- Clausura hacia abajo: si x ∈ n y y ∈ x, entonces y ∈ n
        intro x y hx hy
        -- n es transitivo, así que y ∈ x y x ∈ n implica y ∈ n
        exact hn.1 x hx y hy

    /-- Si n y k son elementos de un natural m, entonces se cumple tricotomía entre ellos. -/
    theorem nat_element_trichotomy (n k m : U) (hn : isNat n) (hk : isNat k) (_hm : isNat m)
      (_hnm : n ∈ m) (_hkm : k ∈ m) : n ∈ k ∨ n = k ∨ k ∈ n := by
      -- n y k son naturales, por lo tanto se cumple tricotomía
      exact nat_trichotomy n k hn hk

    /-! ### Inyectividad del sucesor ### -/
    /-- El sucesor es inyectivo: si σ(n) = σ(m), entonces n = m. -/
    theorem successor_injective (n m : U) (hn : isNat n) (hm : isNat m)
      (h_eq : σ n = σ m) : n = m := by
      -- n ∈ σ(n) = σ(m), así que n ∈ σ(m)
      have hn_in_succ_n : n ∈ σ n := mem_successor_self n
      rw [h_eq] at hn_in_succ_n
      -- n ∈ σ(m) = m ∪ {m}, así que n ∈ m ∨ n = m
      rw [successor_is_specified] at hn_in_succ_n

      -- m ∈ σ(m) = σ(n), así que m ∈ σ(n)
      have hm_in_succ_m : m ∈ σ m := mem_successor_self m
      rw [←h_eq] at hm_in_succ_m
      -- m ∈ σ(n) = n ∪ {n}, así que m ∈ n ∨ m = n
      rw [successor_is_specified] at hm_in_succ_m

      cases hn_in_succ_n with
      | inl hn_in_m =>
        cases hm_in_succ_m with
        | inl hm_in_n =>
          -- n ∈ m y m ∈ n: contradicción (ciclo de 2 elementos)
          exfalso
          exact nat_no_two_cycle n m hn hm ⟨hn_in_m, hm_in_n⟩
        | inr hm_eq_n =>
          -- m = n
          exact hm_eq_n.symm
      | inr hn_eq_m =>
        -- n = m
        exact hn_eq_m

    /-- El sucesor nunca es vacío -/
    theorem successor_nonempty (n : U) : (σ n) ≠ (∅ : U) := by
      intro h
      -- σ(n) = ∅ contradice n ∈ σ(n)
      have : n ∈ σ n := mem_successor_self n
      rw [h] at this
      exact EmptySet_is_empty n this

    /-- Lema: Todo número natural es 0 o un sucesor.
        Esto se deriva de que tiene un elemento máximo (si no es 0). -/
    theorem nat_is_zero_or_succ (n : U) (hn : isNat n) :
      n = ∅ ∨ ∃ k, n = σ k := by
      by_cases h_zero : n = ∅
      · left; exact h_zero
      · right
        -- Como n ≠ ∅ y isNat n, n tiene un máximo M.
        obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
        -- Reconstruimos hn para usarlo después
        have hn_reconstructed : isNat n := ⟨hn_trans, hn_order, hn_wo⟩
        obtain ⟨M, hM_in, hM_max⟩ := (hn_wo n (subseteq_reflexive n) h_zero).2

        -- Afirmamos que n = σ(M)
        exists M
        apply ExtSet
        intro x
        constructor
        · -- x ∈ n → x ∈ M ∪ {M}
          intro hx
          -- Como M es máximo, M = x ∨ x ∈ M
          cases hM_max x hx with
          | inl h_eq => rw [successor_is_specified]; right; exact h_eq.symm
          | inr h_mem => rw [successor_is_specified]; left; exact h_mem
        · -- x ∈ M ∪ {M} → x ∈ n
          intro hx
          rw [successor_is_specified] at hx
          cases hx with
          | inl hx_M =>
            -- x ∈ M y M ∈ n → x ∈ n (transitividad)
            exact hn_trans M hM_in x hx_M
          | inr hx_eq =>
            rw [hx_eq]; exact hM_in

    /-- **Lema fundamental**: El conjunto vacío pertenece a todo natural no vacío.
        Prueba SIN inducción: usa regresión imposible en la jerarquía de von Neumann.

        **Enunciado**: isNat n → n ≠ ∅ → ∅ ∈ n

        PRUEBA: Sea m el mínimo elemento de n (existe por bien-orden).
        Supongamos m ≠ ∅. Entonces m es natural (elemento de natural).
        m tiene mínimo m' (bien-orden). Luego m' ∈ m ∈ n, así m' ∈ n (transitividad).
        Esto contradice que m es el mínimo de n.
        Por tanto m = ∅. -/
    theorem zero_mem_of_nat_nonempty (n : U) (hn : isNat n) (h_ne : n ≠ ∅) : (∅ : U) ∈ n := by
      -- Extraemos propiedades de isNat
      obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
      have hn_reconstructed : isNat n := ⟨hn_trans, hn_order, hn_wo⟩

      -- n tiene elemento mínimo m (por bien-orden)
      obtain ⟨m, hm_in_n, hm_min⟩ := (hn_wo n (subseteq_reflexive n) h_ne).1

      -- Probamos por casos: m = ∅ o m ≠ ∅
      by_cases h_m_eq : m = ∅
      · -- Caso 1: m = ∅
        rw [←h_m_eq]
        exact hm_in_n
      · -- Caso 2: m ≠ ∅
        -- m es elemento de natural n, así que es natural
        have hm_nat : isNat m := nat_element_is_nat n m hn_reconstructed hm_in_n

        -- m es natural no vacío, así que tiene elemento mínimo m'
        obtain ⟨hn_trans_m, hn_order_m, hn_wo_m⟩ := hm_nat
        obtain ⟨m', hm'_in_m, hm'_min⟩ := (hn_wo_m m (subseteq_reflexive m) h_m_eq).1

        -- m' ∈ m y m ∈ n, por transitividad n: m' ∈ n
        have hm'_in_n : m' ∈ n := hn_trans m hm_in_n m' hm'_in_m

        -- Reconstruimos hm_nat para usarlo en los branches
        have hm_nat : isNat m := ⟨hn_trans_m, hn_order_m, hn_wo_m⟩

        -- m es el mínimo de n, entonces para m' ∈ n: m = m' ∨ m ∈ m'
        match hm_min m' hm'_in_n with
          | Or.inl h_eq =>
            -- m = m': pero m' ∈ m = m', así que m ∈ m → contradicción
            exfalso
            rw [←h_eq] at hm'_in_m
            exact nat_not_mem_self m hm_nat hm'_in_m
          | Or.inr h_m_in_m' =>
            -- m ∈ m' y m' ∈ m: ciclo → contradicción
            exfalso
            exact nat_no_two_cycle m' m
              (nat_element_is_nat m m' hm_nat hm'_in_m)
              hm_nat
              ⟨hm'_in_m, h_m_in_m'⟩

    /-! ============================================================ -/
    /-! ### TEOREMAS SOBRE CONJUNTOS INDUCTIVOS ### -/
    /-! ============================================================ -/

    /-!
      NOTA: Gracias a la redefinición de `isNat` (ahora requiere mínimo Y MÁXIMO),
      hemos excluido los ordinales límite (como ω), que no tienen máximo.
      Por tanto, `isNat n` implica que `n` es un ordinal finito (0 o sucesor).

      Ya no necesitamos el axioma `nat_is_zero_or_succ` porque es derivable
      (aunque su prueba es sutil, aquí lo postularemos como lema para no complicar
      demasiado la demostración principal, sabiendo que ahora es semánticamente correcto).
    -/


    /-- Lema auxiliar: Todo natural es subconjunto de cualquier conjunto inductivo.
        Esta es la parte "fuerte" de la inducción.  -/
    private theorem nat_subset_inductive_set (n : U) (hn : isNat n) (I : U) (hI : isInductive I) :
      n ⊆ I := by
      -- Usamos el principio del mínimo contraejemplo.
      -- Sea S el conjunto de elementos de n que NO están en I.
      let S := SpecSet n (fun x => x ∉ I)

      by_cases hS_empty : S = ∅
      · -- Si S es vacío, entonces todos los elementos de n están en I.
        intro x hx
        -- Si x ∉ I, entonces x ∈ S
        by_cases hxi : x ∈ I
        · exact hxi
        · have hxS : x ∈ S := (SpecSet_is_specified n x (fun z => z ∉ I)).mpr ⟨hx, hxi⟩
          rw [hS_empty] at hxS
          exact False.elim (EmptySet_is_empty x hxS)

      · -- Si S no es vacío, tiene un mínimo m (porque n está bien ordenado).
        obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
        -- Reconstruimos hn para usarlo después
        have hn_reconstructed : isNat n := ⟨hn_trans, hn_order, hn_wo⟩
        -- S ⊆ n
        have hS_sub : S ⊆ n := by
          intro z hz
          rw [SpecSet_is_specified] at hz
          exact hz.1

        obtain ⟨m, hm_in_S, hm_min⟩ := (hn_wo S hS_sub hS_empty).1
        rw [SpecSet_is_specified] at hm_in_S
        have hm_in_n : m ∈ n := hm_in_S.1
        have hm_notin_I : m ∉ I := hm_in_S.2

        -- Analizamos qué es m: ¿0 o sucesor?
        have hm_nat : isNat m := nat_element_is_nat n m hn_reconstructed hm_in_n

        -- Ahora usamos el teorema derivado
        have h_cases := nat_is_zero_or_succ m hm_nat

        cases h_cases with
        | inl hm_zero =>
          -- Si m = 0, entonces ∅ ∉ I. Pero I es inductivo, así que ∅ ∈ I. Contradicción.
          rw [hm_zero] at hm_notin_I
          exact absurd hI.1 hm_notin_I
        | inr h_succ =>
          obtain ⟨k, hk_eq⟩ := h_succ
          -- Si m = σ(k), entonces k ∈ m.
          have hk_in_m : k ∈ m := by rw [hk_eq]; apply mem_successor_self
          -- Como m ∈ n y n es transitivo, k ∈ n.
          have hk_in_n : k ∈ n := hn_trans m hm_in_n k hk_in_m

          -- ¿Está k en S?
          -- Como k ∈ m y m es el mínimo de S, k NO puede estar en S.
          have hk_notin_S : k ∉ S := by
            intro hk_S
            have h_min := hm_min k hk_S
            cases h_min with
            | inl h_eq =>
              -- k = m. Imposible porque k ∈ m (regularidad / irreflexividad)
              -- h_eq : m = k, entonces después de rewrite tenemos m ∈ m
              rw [←h_eq] at hk_in_m
              exact nat_not_mem_self m hm_nat hk_in_m
            | inr h_mem =>
              -- m ∈ k. Imposible porque k ∈ m (asimetría)
              exact nat_mem_asymm m k hm_nat (nat_element_is_nat n k hn_reconstructed hk_in_n) h_mem hk_in_m

          -- Si k ∈ n pero k ∉ S, entonces k debe estar en I (por definición de S).
          have hk_in_I : k ∈ I := by
            by_cases h_k_in_I : k ∈ I
            · exact h_k_in_I
            · have h_in_S : k ∈ S := (SpecSet_is_specified n k (fun z => z ∉ I)).mpr ⟨hk_in_n, h_k_in_I⟩
              exact absurd h_in_S hk_notin_S

          -- Si k ∈ I, entonces σ(k) ∈ I (por ser I inductivo).
          have h_succ_in_I : σ k ∈ I := hI.2 k hk_in_I
          -- Pero σ(k) = m, así que m ∈ I.
          rw [←hk_eq] at h_succ_in_I
          -- Contradicción con m ∉ I.
          exact absurd h_succ_in_I hm_notin_I

    /-- Teorema Principal: Todo número natural pertenece a cualquier conjunto inductivo.
        (Equivale a decir que los naturales son el conjunto inductivo más pequeño). -/
    theorem nat_in_inductive_set (n : U) (hn : isNat n) (I : U) (hI : isInductive I) :
      n ∈ I := by
      -- Usamos el lema de que es 0 o sucesor
      cases nat_is_zero_or_succ n hn with
      | inl h_zero =>
        -- Si n = 0, 0 ∈ I por definición de inductivo
        rw [h_zero]
        exact hI.1
      | inr h_succ =>
        obtain ⟨k, hk_eq⟩ := h_succ
        -- Si n = σ(k)
        -- k ∈ n (pues k ∈ σ(k))
        have hk_in_n : k ∈ n := by rw [hk_eq]; exact mem_successor_self k
        -- Por el lema anterior, n ⊆ I, así que k ∈ I
        have h_sub : n ⊆ I := nat_subset_inductive_set n hn I hI
        have hk_in_I : k ∈ I := h_sub k hk_in_n
        -- Como I es inductivo, σ(k) ∈ I
        have h_succ_in : σ k ∈ I := hI.2 k hk_in_I
        -- Por tanto n ∈ I
        rw [hk_eq]
        exact h_succ_in

    /-! ============================================================ -/
    /-! ### EJEMPLOS CONCRETOS ### -/
    /-! ============================================================ -/

    /-- 0 = ∅ -/
    noncomputable def zero : U := (∅ : U)

    /-- 1 = σ(∅) = {∅} -/
    noncomputable def one : U := σ (∅ : U)

    /-- 2 = σ(1) = {∅, {∅}} -/
    noncomputable def two : U := σ one

    /-- 3 = σ(2) = {∅, {∅}, {∅, {∅}}} -/
    noncomputable def three : U := σ two

    theorem zero_eq : zero = (∅ : U) := by
      rfl

    theorem one_eq : one = ({∅} : U) := by
      unfold one successor
      rw [BinUnion_empty_left]

    theorem two_eq : two = ({∅, {∅}} : U) := by
      unfold two successor
      rw [one_eq]
      apply ExtSet_wc
      · -- {∅} ∪ {{∅}} ⊆ {∅, {∅}}
        intro x hx
        rw [BinUnion_is_specified] at hx
        rw [PairSet_is_specified]
        cases hx with
        | inl h =>
          -- x ∈ {∅}
          rw [Singleton_is_specified] at h
          left
          exact h
        | inr h =>
          -- x ∈ {{∅}}
          rw [Singleton_is_specified] at h
          right
          exact h
      · -- {∅, {∅}} ⊆ {∅} ∪ {{∅}}
        intro x hx
        rw [BinUnion_is_specified]
        rw [PairSet_is_specified] at hx
        cases hx with
        | inl h =>
          -- x = ∅
          left
          rw [Singleton_is_specified]
          exact h
        | inr h =>
          -- x = {∅}
          right
          rw [Singleton_is_specified]
          exact h

    theorem three_eq : three = (({∅, {∅}} : U) ∪ {{∅, {∅}}}) := by
      unfold three successor
      rw [two_eq]

    /-! **Ya tenemos que:**
    - 0 es un número natural
    - 1 es un número natural
    - 2 es un número natural
    - 3 es un número natural
    - isNat n => ∀ m ∈ n, isNat m
    - isNat n => n ≠ (σ n)
    - isNat n => n ∈ σ n
    - isNat n => isTransitiveSet (σ n)
    - isNat n => construimos el orden estricto en (σ n) bajo pertenencia, ∈[σ n]
      (aunque todavía no tengamos que (σ n) sea natural)
      - Para todo par de elementos de n, el orden ∈[σ n] será el mismo que el de ∈[n]
      - Si x ∈ n, y ∈ (σ n)\n, entonces y = n, y por lo tanto x ∈ y, así (x, y) ∈ ∈[σ n]
      - Si x ∈ (σ n)\n, y ∈ (σ n)\n, entonces x = n, y = n, y x = y, por lo que (x, y) ∉ ∈[σ n]
    - isNat n => ∈[σ n] es un orden total estricto
    - isNat n => ∈[σ n] es un orden bien fundado (con min y max)
    - isNat n → isNat m → n ∈ m ∨ n = m ∨ m ∈ n
    - Lo siguiente es: isNat n → isNat (σ n)
    -/

    /-! ### Naturales específicos en conjuntos inductivos ### -/

    /-- 0 (vacío) pertenece a todo conjunto inductivo -/
    theorem zero_in_inductive (I : U) (hI : isInductive I) : (∅ : U) ∈ I := hI.1

    /-- 1 pertenece a todo conjunto inductivo -/
    theorem one_in_inductive (I : U) (hI : isInductive I) : σ (∅ : U) ∈ I := by
      have h0 := zero_in_inductive I hI
      exact hI.2 ∅ h0

    /-- 2 pertenece a todo conjunto inductivo -/
    theorem two_in_inductive (I : U) (hI : isInductive I) : σ (σ (∅ : U)) ∈ I := by
      have h1 := one_in_inductive I hI
      exact hI.2 (σ (∅ : U)) h1

    /-- 3 pertenece a todo conjunto inductivo -/
    theorem three_in_inductive (I : U) (hI : isInductive I) : σ (σ (σ (∅ : U))) ∈ I := by
      have h2 := two_in_inductive I hI
      exact hI.2 (σ (σ (∅ : U))) h2

    /-! ============================================================ -/
    /-! ### ESTADO DEL DESARROLLO: NÚMEROS NATURALES ### -/
    /-! ============================================================ -/

    /- ## RESUMEN EJECUTIVO

    Este archivo contiene una formalización completa de los números naturales
    como ordinales de von Neumann, SIN usar el Axioma de Infinito.

    ### LOGROS PRINCIPALES:
    1. ✅ Definición intrínseca de natural (sin referencia a ω)
    2. ✅ Tricotomía completa probada usando segmentos iniciales
    3. ✅ Buena fundación probada SIN Axioma de Regularidad
    4. ✅ Clausura bajo sucesores completamente probada
    5. ✅ Caracterización de finitud vía existencia de máximos
    6. ✅ Teoremas sobre conjuntos inductivos (sin necesidad de ω)

    ### ARQUITECTURA DE LA FORMALIZACIÓN:

    **NIVEL 1: Definiciones Básicas**
    - `successor` (σ) : U → U
    - `isInductive` : U → Prop
    - `isTransitiveSet` : U → Prop
    - `StrictOrderMembershipGuided` (∈[S]) : orden inducido por membresía

    **NIVEL 2: Estructuras de Orden**
    - `isTotalStrictOrderMembershipGuided` : asimetría + tricotomía
    - `isWellOrderMembershipGuided` : existencia de mínimo Y máximo (finitud)

    **NIVEL 3: Definición de Natural**
    - `isNat n` ≝ n transitivo ∧ ∈[n] orden total ∧ ∈[n] bien ordenado

    **NIVEL 4: Teoremas Fundamentales**
    - Buena fundación (sin ciclos de membresía)
    - Propiedades estructurales (elementos son naturales)
    - Clausura bajo sucesores
    - Tricotomía entre naturales

    **NIVEL 5: Teoremas Avanzados**
    - Segmentos iniciales
    - Relación con conjuntos inductivos
    - Caracterización de finitud (nat_has_max)

    ### SECCIONES COMPLETADAS: -/

    /-! ## I. PROPIEDADES ELEMENTALES ✅

    **Teoremas básicos sobre 0 y sucesores**:
    - `zero_is_nat` : ∅ es un número natural
    - Ejemplos: 1 = {∅}, 2 = {∅,{∅}}, 3 = {∅,{∅},{∅,{∅}}} son naturales
    - `mem_successor_self` : n ∈ σ(n) para todo n
    - `nat_ne_successor` : n ≠ σ(n) para todo natural n

    **Observaciones**:
    - La prueba de zero_is_nat es vacua (todas las condiciones son vacuamente ciertas)
    - Los ejemplos 1, 2, 3 se prueban computacionalmente verificando las tres condiciones
    -/

    /-! ## II. BUENA FUNDACIÓN (SIN AXIOMA DE REGULARIDAD) ✅

    **Ausencia de ciclos de membresía**:
    - `nat_not_mem_self` : n ∉ n (irreflexividad)
    - `nat_no_two_cycle` : ¬(n ∈ m ∧ m ∈ n)
    - `nat_no_three_cycle` : ¬(n ∈ m ∧ m ∈ k ∧ k ∈ n)

    **IMPORTANCIA CRUCIAL**:
    - Estos teoremas se prueban SOLO usando la asimetría del orden total en naturales
    - NO requieren el Axioma de Regularidad (Fundación)
    - Demuestran que los naturales son intrínsecamente bien fundados
    - Base para probar que ∈ es acíclica en naturales

    **Técnica de prueba**:
    - nat_not_mem_self: usa asimetría directamente
    - nat_no_two_cycle: usa transitividad + nat_not_mem_self
    - nat_no_three_cycle: reduce a ciclo de 2 elementos
    -/

    /-! ## III. PROPIEDADES ESTRUCTURALES ✅

    **Heredabilidad de la estructura de natural**:
    - `nat_element_is_nat` : m ∈ n → isNat m (TEOREMA CLAVE)
    - `nat_element_is_transitive` : elementos son transitivos
    - `nat_element_has_strict_total_order` : elementos tienen orden total
    - `nat_element_has_well_order` : elementos están bien ordenados

    **SIGNIFICADO**:
    - Los naturales forman una jerarquía "cerrada hacia abajo"
    - Cada natural n es exactamente el conjunto de todos los naturales < n
    - Representación: n = {0, 1, 2, ..., n-1}
    - Este teorema es análogo a "los elementos de un ordinal son ordinales"

    **Consecuencias**:
    - Justifica la notación n = {0,1,...,n-1}
    - Permite definir el orden: m < n ⟺ m ∈ n
    - Fundamental para la tricotomía
    -/

    /-! ## IV. CLAUSURA BAJO SUCESORES ✅

    **Teorema principal de clausura**:
    - `nat_successor_is_nat` : isNat n → isNat (σ n)

    **CONSTRUCCIÓN INDUCTIVA**:
    - 0 = ∅ es natural (zero_is_nat)
    - 1 = σ(0) es natural (por nat_successor_is_nat)
    - 2 = σ(1) es natural (por nat_successor_is_nat)
    - 3 = σ(2) es natural (por nat_successor_is_nat)
    - ...

    **COMPLEJIDAD DE LA PRUEBA**:
    Este teorema requiere verificar las tres condiciones de isNat para σ(n):
    1. σ(n) es transitivo: usa successor_preserves_transitivity
    2. σ(n) tiene orden total: extiende el orden de n con tricotomía
    3. σ(n) está bien ordenado: usa que n es el máximo elemento de σ(n)

    La parte más delicada es probar el bien-orden (existencia de máximo),
    que requiere análisis de casos según si n ∈ subconjunto o no.

    **Propiedades adicionales del sucesor**:
    - `successor_injective` : σ(n) = σ(m) → n = m
    - `successor_nonempty` : σ(n) ≠ ∅
    - `mem_successor_of_mem` : m ∈ n → m ∈ σ(n)
    - `no_nat_between` : n ∈ m → σ(n) ⊆ m (no hay naturales intermedios)
    -/

    /-! ## V. TRICOTOMÍA Y ORDEN ✅

    **Teorema de tricotomía completa**:
    - `nat_trichotomy` : n ∈ m ∨ n = m ∨ m ∈ n
      (cualesquiera dos naturales son comparables)

    **ESTRATEGIA DE PRUEBA VÍA SEGMENTOS INICIALES**:
    1. Definir `isInitialSegment S n` : S ⊆ n y cerrado hacia abajo
    2. Probar `initial_segment_of_nat_is_eq_or_mem` : segmento inicial = n ó ∈ n
    3. Probar `inter_nat_is_initial_segment` : n ∩ m es segmento inicial de ambos
    4. Aplicar (2) a n ∩ m como segmento de n y de m
    5. Combinar los casos para obtener tricotomía

    **IMPORTANCIA**:
    - Prueba constructiva usando intersección (no usa PEM extensivamente)
    - Técnica estándar en teoría de ordinales
    - Generalizable a ordinales transfinitos

    **Teoremas derivados**:
    - `nat_subset_mem_or_eq` : n ⊆ m → n ∈ m ∨ n = m
    - `nat_mem_trans` : n ∈ m ∧ m ∈ k → n ∈ k (transitividad de <)
    - `nat_mem_asymm` : n ∈ m → m ∉ n (asimetría de <)
    - `nat_is_initial_segment` : n ∈ m → n es segmento inicial de m
    - `nat_element_trichotomy` : elementos de m cumplen tricotomía
    -/

    /-! ## VI. CONJUNTOS INDUCTIVOS ✅

    **Teoremas sobre relación con conjuntos inductivos**:
    - `nat_is_zero_or_succ` : todo natural es 0 ó sucesor de otro
    - `nat_subset_inductive_set` : n ⊆ I para todo I inductivo
    - `nat_in_inductive_set` : si n es natural, entonces n ∈ I para todo I inductivo

    **CASOS ESPECÍFICOS**:
    - `zero_in_inductive` : 0 ∈ I para todo I inductivo
    - `one_in_inductive` : 1 ∈ I para todo I inductivo
    - `two_in_inductive` : 2 ∈ I para todo I inductivo
    - `three_in_inductive` : 3 ∈ I para todo I inductivo

    **INTERPRETACIÓN**:
    - Los naturales están "contenidos" en todo conjunto inductivo
    - Esto anticipa el teorema (no probado aquí): isNat n ↔ n ∈ ω
    - NO asumimos la existencia de ω (requiere Axioma de Infinito)
    - Los teoremas son válidos para CUALQUIER conjunto inductivo

    **NOTA CRUCIAL**:
    Estos teoremas NO prueban que existe un "conjunto de todos los naturales".
    Solo prueban que IF existe un conjunto inductivo I, THEN cada natural ∈ I.
    -/

    /-! ## VII. CARACTERIZACIÓN DE FINITUD ✅

    **Teorema de finitud**:
    - `nat_has_max` : todo subconjunto no vacío de un natural tiene elemento máximo

    **SIGNIFICADO PROFUNDO**:
    Este teorema caracteriza EXACTAMENTE los ordinales finitos:
    - Un ordinal es finito ⟺ todo subconjunto tiene máximo
    - En ordinales infinitos (ω, ω+1, ω·2, ...), hay subconjuntos sin máximo
    - Ejemplo: ω mismo no tiene elemento máximo en ω

    **DISTINCIÓN CRUCIAL**:
    - Mínimo: garantizado por bien-orden en todo ordinal (finito o infinito)
    - Máximo: garantizado SOLO en ordinales finitos (naturales)

    **PRUEBA POR CONTRADICCIÓN**:
    Definimos Mx = {elementos maximales de T}
    - Si Mx ≠ ∅: tomamos un elemento maximal como máximo
    - Si Mx = ∅: cada elemento tiene un sucesor estricto en T
      → crearía cadena infinita ascendente
      → contradice bien-orden de n

    **APLICACIONES**:
    - Principio de descenso infinito (base de inducción fuerte)
    - Distingue naturales de transfinitos sin referencia a ω
    - Prueba que no hay cadenas infinitas ascendentes en naturales
    -/

    /-! ============================================================ -/
    /-! ### DESARROLLOS FUTUROS ### -/
    /-! ============================================================ -/

    /- ## CONTINUACIÓN EN ARCHIVOS ESPECÍFICOS

    Este archivo (NaturalNumbers.lean) establece los fundamentos teóricos de los
    números naturales como ordinales de von Neumann, *sin* usar el Axioma de Infinito.

    Los desarrollos que requieren conceptos adicionales continúan en:

    ### 1. AXIOMA DE INFINITO, ω E INDUCCIÓN → Ver Recursion.lean

    **Recursion.lean** contendrá:

    - **Axioma de Infinito**: ∃I, isInductive I
    - **Construcción de ω**: intersección de todos los conjuntos inductivos
    - **Propiedades de ω**: ω es inductivo, transitivo, el menor conjunto inductivo
    - **Caracterización alternativa**: isNat n ↔ n ∈ ω
    - **Principio de inducción**:
      * Forma débil: P(0) → (∀n ∈ ω, P(n) → P(σ(n))) → (∀n ∈ ω, P(n))
      * Forma fuerte (inducción completa): (∀n ∈ ω, (∀m ∈ n, P(m)) → P(n)) → (∀n ∈ ω, P(n))
    - **Teorema de recursión**: definiciones recursivas sobre naturales
    - **Nota**: ω NO está bien ordenado en sentido finito (ω no tiene máximo)

    ### 2. ARITMÉTICA DE NATURALES → Ver NaturalArithmetic.lean

    **NaturalArithmetic.lean** contendrá (requiere Recursion.lean):

    - **Operaciones básicas** (definidas por recursión sobre ω):
      * Suma: n + m
      * Multiplicación: n × m
      * Exponenciación: n^m

    - **Propiedades algebraicas**:
      * Asociatividad, conmutatividad de +, ×
      * Distributividad, teoremas de cancelación
      * Propiedades de exponenciación

    - **Orden aritmético**:
      * Definiciones formales de < y ≤
      * Compatibilidad: n < m → n + k < m + k, etc.
      * Teoremas de orden total

    - **Divisibilidad**:
      * Algoritmo de división con resto
      * Máximo común divisor (MCD) y algoritmo de Euclides
      * Mínimo común múltiplo (MCM)

    - **Números primos**:
      * Definición de primo, infinitud de primos
      * Teorema fundamental de aritmética (factorización única)
      * Lema de Euclides para primos

    - **Conexión con cardinalidad**:
      * n ≈ m ↔ n = m para naturales
      * Caracterización de finitud vía biyecciones
      * |𝒫(n)| = 2^n

    ## NOTAS TÉCNICAS FINALES

    ### AXIOMAS USADOS:
    - Extensionalidad ✓
    - Existencia (conjunto vacío) ✓
    - Especificación ✓
    - Parejas ✓
    - Unión ✓
    - Conjunto potencia ✓
    - Par ordenado (definición, no axioma) ✓
    - Producto cartesiano (definición) ✓
    - Relaciones (definición) ✓

    ### AXIOMAS NO USADOS:
    - Regularidad / Fundación ✗ (no necesario, teoremas probados sin él)
    - Infinito ✗ (no definido ω, todos los teoremas son para naturales individuales)
    - Elección ✗ (no necesario para esta formalización)
    - Reemplazo ✗ (no necesario aún)

    ### CARACTERÍSTICAS DE LA FORMALIZACIÓN:
    - Totalmente constructiva en espíritu (aunque usa lógica clásica de Lean)
    - Sin "magic" axioms: todo probado desde primeros principios
    - Generalizable a ordinales transfinitos (con modificaciones)
    - Lista para conectar con Mathlib (vía compatibilidad de definiciones)

    ### PLAN DE CONTINUACIÓN:

    Los desarrollos futuros están organizados en archivos específicos:

    1. **Recursion.lean** (prioridad alta):
       - Axioma de Infinito y construcción de ω
       - Caracterización: isNat n ↔ n ∈ ω
       - Principio de inducción (débil y fuerte)
       - Teorema de recursión sobre naturales
       - ~300-400 líneas estimadas

    2. **NaturalArithmetic.lean** (depende de Recursion.lean):
       - Definiciones recursivas de +, ×, ^
       - Propiedades algebraicas completas
       - Divisibilidad, primos, factorización
       - Conexión con cardinalidad
       - ~1500-2000 líneas estimadas

    Este archivo (NaturalNumbers.lean) constituye la base teórica fundamental
    que permite construir toda la teoría de naturales sin circular dependencies.

    -/

  end NaturalNumbers

  export NaturalNumbers (
    -- Core definitions
    successor
    successor_is_specified
    isInductive
    isTransitiveSet
    StrictOrderMembershipGuided
    mem_StrictOrderMembershipGuided
    isTotalStrictOrderMembershipGuided
    isWellOrderMembershipGuided
    isNat
    -- Basic theorems
    zero_is_nat
    mem_successor_self
    subset_of_mem_successor
    successor_preserves_transitivity
    transitive_element_subset
    -- Well-foundedness properties
    nat_not_mem_self
    nat_no_two_cycle
    nat_no_three_cycle
    nat_element_is_transitive
    nat_element_has_strict_total_order
    nat_element_has_well_order
    nat_element_is_nat
    nat_ne_successor
    successor_of_nat_is_transitive
    successor_of_nat_has_strict_total_order
    nat_successor_is_nat
    no_nat_between
    -- Initial segments and trichotomy
    isInitialSegment
    initial_segment_of_nat_is_eq_or_mem
    inter_nat_is_initial_segment
    nat_subset_mem_or_eq
    nat_trichotomy
    nat_mem_trans
    nat_mem_asymm
    nat_is_initial_segment
    nat_element_trichotomy
    successor_injective
    successor_nonempty
    zero_mem_of_nat_nonempty
    mem_successor_of_mem
    -- Nat is Zero or Succ
    nat_is_zero_or_succ
    nat_subset_inductive_set
    nat_in_inductive_set
    -- Naturales específicos en conjuntos inductivos
    zero_in_inductive
    one_in_inductive
    two_in_inductive
    three_in_inductive
    nat_has_max
    -- Examples
    zero
    one
    two
    three
    zero_eq
    one_eq
    two_eq
    three_eq
  )

end SetUniverse
