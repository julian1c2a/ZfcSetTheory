/-
  # Natural Numbers (von Neumann ordinals)

  This file defines the natural numbers as von Neumann ordinals without introducing the Axiom of Infinity,
  and without induction principle (this will be a theorem)

  ## Main definitions
  - `σ` n : Successor function ∀ (n : U), σ(n) = n ∪ {n}
  - `isInductive` I : A set I is inductive if ∅ ∈ I and ∀ x ∈ I, σ(x) ∈ I
  - `isTransitiveSet` S : The set S is a transitive set if ∀ x ∈ S, x ⊆ S
  - `StrictOrderMembershipGuided` S : ∈[S] ∈ S ×ₛ S, where S is a transitive set,
        - ∀ p ∈ ∈[S], p is a pair (x, y) with x, y ∈ S, and p ∈[S] q iff x ∈ y
            - ∀ x y ∈ S, x ∈[S] y → ¬(y ∈[S] x) (asymmetry)
            - ∀ x y z ∈ S, x ∈[S] y → y ∈[S] z → x ∈[S] z (transitivity)
  - `TotalStrictOrderMembershipGuided` : ∀ x y ∈ S, x ∈[S] y ∨ x = y ∨ y ∈[S] x (trichotomy)
  - `WellOrderMembershipGuided` : ⟨S, ∈[S]⟩ is a well-ordered membership set, if and only if
        - ∀ T ∈ 𝒫 S:
            - T ≠ ∅ → ∃ m ∈ T, ∀ x ∈ T, m = x ∨ m ∈[S] x (existence of minimal element)
            - T ≠ ∅ → ∃ m ∈ T, ∀ x ∈ T, m = x ∨ x ∈[S] m (existence of maximal element)
  - `isNat` n : n is a natural number if and only if:
        - n is a transitive set
        - ∈[n] is a strict total order on n
        - ⟨n, ∈[n]⟩ is well-ordered by ∈[n]

  ## Firsts theorems
  - ∅ is a natural number by the previous definition
  - Examples:
    - 1 =  {∅},  is a natural number by the previous definition
    - 2 = {∅, {∅}},  is a natural number by the previous definition
    - 3 = {∅, {∅}, {∅, {∅}}} is a natural number by the previous definition
  - n is a natural number, then n ∉ n (regularity.1)
  - n m are natural numbers, then ¬(n ∈ m ∨ m ∈ n) (regularity.2)
  - n m are natural numbers, then n ∈ m → ¬(m ∈ n) (asymmetry of membership)
  - n is a natural number, then ∀ m ∈ n, m is a natural number (transitivity)
  - n m k are natural numbers, then n ∈ m ∧ m ∈ k → n ∈ k (transitivity of membership)
  - n m are natural numbers, then n = m ∨ n ∈ m ∨ m ∈ n (trichotomy)
  - n m k are natural numbers, then n ∈ m ∧ m ∈ k → n ∈ k (transitivity of membership)
  - ∈[n] is a well-ordered membership set (well-foundedness of each natural number)
  - isNat n → isNat (σ n) (closure under successor)
  - isNat n → ∀ m ∈ n, isNat m (closure under subsets)
  - ∀ n m, isNat n → isNat m → n ∈ m → ∀ k ∈ m, n ∈ k ∨ n = k (initial segment property)
  - ∀ n m, isNat n → isNat m → σ(n) = σ(m) → n = m (injectivity of successor)
  - ∀ n, isNat n → σ(n) ≠ ∅ (successor is never empty)
  - ∀ n, isNat n → n ∈ σ(n) (each natural number is in its successor)
  - ∀ n m, isNat n → isNat m → n ∈ m → n ∈ σ(m) (membership is preserved by successor)

  ## Main theorems
  - If I is an inductive set, and n is a natural number, then n ∈ I (ω is the smallest inductive set)
  - Induction principle: If P is a first order predicate of the natural number, and P(0) holds, and ∀ n, P(n) → P(σ(n)) holds, then
    ∀ n, Nat(n) → P(n) holds (induction principle) (this need a intermiadate elaboration)
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
    /-- A set I is inductive if ∅ ∈ I and ∀ x ∈ I, σ(x) ∈ I -/
    def isInductive (I : U) : Prop :=
      (∅ : U) ∈ I ∧ ∀ x, x ∈ I → (σ x) ∈ I

    /-! ### Conjunto Transitivo (redefinición correcta) ### -/
    /-- A set S is transitive if every element is also a subset: ∀ x ∈ S, x ⊆ S -/
    def isTransitiveSet (S : U) : Prop :=
      ∀ x, x ∈ S → x ⊆ S

    /-! ### Orden Estricto Guiado por Membresía ### -/
    /-- The strict order relation guided by membership on S:
        ∈[S] = { ⟨x, y⟩ | x ∈ S ∧ y ∈ S ∧ x ∈ y } -/
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
    /-- The relation ∈[S] is a total strict order on S:
        - Asymmetry: x ∈ y → ¬(y ∈ x)
        - Trichotomy: x ∈ y ∨ x = y ∨ y ∈ x -/
    def isTotalStrictOrderMembershipGuided (S : U) : Prop :=
      isTransitiveSet S ∧
      (∀ x y, x ∈ S → y ∈ S → x ∈ y → y ∉ x) ∧
      (∀ x y, x ∈ S → y ∈ S → (x ∈ y ∨ x = y ∨ y ∈ x))

    /-! ### Bien Ordenado Guiado por Membresía ### -/
    /-- ⟨S, ∈[S]⟩ is well-ordered: every non-empty subset has a minimal element -/
    def isWellOrderMembershipGuided (S : U) : Prop :=
      ∀ T, T ⊆ S → T ≠ (∅ : U) →
        (∃ m, m ∈ T ∧ ∀ x, x ∈ T → (m = x ∨ m ∈ x))

    /-! ============================================================ -/
    /-! ### DEFINICIÓN DE NÚMERO NATURAL ### -/
    /-! ============================================================ -/

    /-- n is a natural number if:
        1. n is a transitive set
        2. ∈[n] is a total strict order on n
        3. ⟨n, ∈[n]⟩ is well-ordered -/
    def isNat (n : U) : Prop :=
      isTransitiveSet n ∧
      isTotalStrictOrderMembershipGuided n ∧
      isWellOrderMembershipGuided n

    /-! ============================================================ -/
    /-! ### TEOREMAS FUNDAMENTALES ### -/
    /-! ============================================================ -/

    /-! ### ∅ es un número natural ### -/
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
      · -- ∅ is well-ordered
        intro T hT hT_nonempty
        -- If T ⊆ ∅ and T ≠ ∅, we have a contradiction
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

    /-! ### Teoremas auxiliares sobre sucesores ### -/
    theorem mem_successor_self (n : U) : n ∈ (σ n) := by
      rw [successor_is_specified]
      exact Or.inr rfl

    theorem subset_of_mem_successor (n x : U) :
      x ∈ (σ n) → x ∈ n ∨ x = n := by
      intro hx
      rw [successor_is_specified] at hx
      exact hx

    /-! ### Si n es transitivo, entonces σ(n) es transitivo ### -/
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
    theorem no_three_cycle_in_nat (n m k l : U) (hn : isNat n)
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
      -- Apply well-ordering to get minimal element
      obtain ⟨w, hw_in_S, hw_min⟩ := hn_wo S hS_sub hS_nonempty
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
    /-! ### BUENA FUNDACIÓN DE NATURALES (SIN AXIOMA) ### -/
    /-! ============================================================ -/

    /-! ### Lema: ningún número natural es miembro de sí mismo (irreflexividad) ### -/
    theorem nat_not_mem_self (n : U) :
      isNat n → n ∉ n := by
      intro ⟨_, ⟨_,hasym, _⟩, _⟩ hn_mem
      -- By asymmetry: if n ∈ n then n ∉ n
      have : n ∉ n := hasym n n hn_mem hn_mem hn_mem
      exact this hn_mem

    /-! ### Lema: no existen ciclos de membresía de dos elementos ### -/
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

    /-! ### Lema: no existen ciclos de membresía de tres elementos ### -/
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

    /-! ### Lema: elementos de un número natural son transitivos ### -/
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
              obtain ⟨w, hw_in, hw_min⟩ := hn_wo ({m, k} : U) hmk_sub hmk_nonempty
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

    /-! ### Teorema: el orden estricto en elementos de naturales es total ### -/
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

    theorem nat_element_has_well_order (n m : U)
      (hn : isNat n) (hm_in_n : m ∈ n) :
      isWellOrderMembershipGuided m := by
      obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
      unfold isWellOrderMembershipGuided

      -- m ⊆ n porque n es transitivo
      have hm_sub_n : m ⊆ n := hn_trans m hm_in_n

      -- Para cualquier T ⊆ m no vacío, debemos encontrar un mínimo
      intro T hT_sub_m hT_ne_empty

      -- T ⊆ m y m ⊆ n implica T ⊆ n
      have hT_sub_n : T ⊆ n := by
        intro x hx_in_T
        have hx_in_m : x ∈ m := hT_sub_m x hx_in_T
        exact hm_sub_n x hx_in_m

      -- Como n tiene bien-orden y T ⊆ n, T ≠ ∅, existe un mínimo en T
      obtain ⟨min, hmin_in_T, hmin_is_min⟩ := hn_wo T hT_sub_n hT_ne_empty

      -- Este mínimo también sirve para T respecto al orden en m
      exact ⟨min, hmin_in_T, hmin_is_min⟩

    /-! ### Lema: todo elemento de un natural es un natural ### -/
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
      obtain ⟨hn_trans, ⟨_, hn_asym, hn_trich⟩, hn_wo⟩ := hn

      -- Necesitamos probar 3 cosas: Transitividad, Orden Total Estricto, Bien-Orden
      refine ⟨?_, ?_, ?_⟩

      -- 1. Transitividad
      · exact successor_of_nat_is_transitive n ⟨hn_trans, ⟨hn_trans, hn_asym, hn_trich⟩, hn_wo⟩

      -- 2. Orden Total Estricto
      · exact successor_of_nat_has_strict_total_order n ⟨hn_trans, ⟨hn_trans, hn_asym, hn_trich⟩, hn_wo⟩

      -- 3. Bien-Orden
      · unfold isWellOrderMembershipGuided
        intro A hA_sub hA_nonempty

        -- Definimos B = A ∩ n
        let B := A ∩ n

        -- Análisis por casos: ¿Es B vacío o no?
        by_cases hB_empty : B = (∅ : U)
        · -- Caso 1: B es vacío.
          -- Probamos que A = {n}
          have hA_eq_n : A = {n} := by
            apply ExtSet
            intro x
            constructor
            · intro hx
              -- x ∈ A ⊆ n ∪ {n}
              have hx_succ : x ∈ (σ n) := hA_sub x hx
              rw [successor_is_specified] at hx_succ
              cases hx_succ with
              | inl hx_n =>
                -- Si x ∈ n, entonces x ∈ A ∩ n = B. Pero B = ∅. Contradicción.
                have hx_B : x ∈ B := (BinInter_is_specified A n x).mpr ⟨hx, hx_n⟩
                rw [hB_empty] at hx_B
                exact False.elim (EmptySet_is_empty x hx_B)
              | inr hx_eq_n =>
                rw [Singleton_is_specified]
                exact hx_eq_n
            · intro hx
              rw [Singleton_is_specified] at hx
              rw [hx]
              -- Necesitamos mostrar n ∈ A.
              -- Como A ≠ ∅, sea z ∈ A.
              obtain ⟨z, hz⟩ := nonempty_iff_exists_mem A |>.mp hA_nonempty
              -- z ∈ A ⊆ n ∪ {n}.
              have hz_succ : z ∈ (σ n) := hA_sub z hz
              rw [successor_is_specified] at hz_succ
              cases hz_succ with
              | inl hz_n =>
                -- z ∈ n -> z ∈ B = ∅ -> Falso
                have hz_B : z ∈ B := (BinInter_is_specified A n z).mpr ⟨hz, hz_n⟩
                rw [hB_empty] at hz_B
                exact False.elim (EmptySet_is_empty z hz_B)
              | inr hz_eq_n =>
                -- z = n, y z ∈ A, entonces n ∈ A
                rw [←hz_eq_n]
                exact hz

          -- Como A = {n}, el mínimo es n.
          exists n
          rw [hA_eq_n]
          constructor
          · apply (Singleton_is_specified n n).mpr rfl
          · intro x hx
            rw [Singleton_is_specified] at hx
            left
            exact hx.symm

        · -- Caso 2: B no es vacío.
          -- Usamos el buen orden de n en B.
          have hB_sub_n : B ⊆ n := BinInter_subset A n |>.2
          have hB_nonempty : B ≠ (∅ : U) := hB_empty
          obtain ⟨m, hm_in_B, hm_min⟩ := hn_wo B hB_sub_n hB_nonempty

          -- m es el candidato.
          exists m
          constructor
          · -- m ∈ A
            exact (BinInter_is_specified A n m).mp hm_in_B |>.1
          · -- m es minimal en A
            intro x hx_in_A
            -- Revisamos si x ∈ n o x = n
            have hx_succ := hA_sub x hx_in_A
            rw [successor_is_specified] at hx_succ
            cases hx_succ with
            | inl hx_n =>
              -- x ∈ n -> x ∈ B. Usamos la propiedad de m en B.
              have hx_B : x ∈ B := (BinInter_is_specified A n x).mpr ⟨hx_in_A, hx_n⟩
              exact hm_min x hx_B
            | inr hx_eq_n =>
              -- x = n. Como m ∈ B ⊆ n, m ∈ n = x.
              right
              rw [hx_eq_n]
              exact (BinInter_is_specified A n m).mp hm_in_B |>.2

    /-! ### No hay naturales entre n y σ(n) ### -/
    /-- Si n y m son naturales y n ∈ m, entonces σ(n) ⊆ m.
        Esto significa que σ(n) es el "siguiente" natural después de n,
        sin otros naturales en el medio. -/
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
        obtain ⟨m, hm_in_D, hm_min⟩ := hn_wo D hD_sub_n hD_nonempty

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

    theorem mem_successor_of_mem (n m : U) (_hn : isNat n) (_hm : isNat m) (hm_in_n : m ∈ n) :
      m ∈ σ n
      := by
      rw [successor_is_specified]
      left
      exact hm_in_n

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
    - isNat n => ∈[σ n] es un orden bien fundado
    - isNat n → isNat m → n ∈ m ∨ n = m ∨ m ∈ n
    - Lo siguiente es: isNat n → isNat (σ n)
    -/


    /-! ### NOTA SOBRE TEOREMAS PENDIENTES ###

    ## Estado actual del desarrollo:

    ### ✅ TEOREMAS COMPLETADOS:
    - Propiedades básicas:
      * `zero_is_nat` - ∅ es un número natural
      * Ejemplos: 1, 2, 3 son naturales
      * `mem_successor_self` - n ∈ σ(n)
      * `nat_ne_successor` - n ≠ σ(n)

    - Buena fundación (sin Axioma de Regularidad):
      * `nat_not_mem_self` - n ∉ n (irreflexividad)
      * `nat_no_two_cycle` - ¬(n ∈ m ∧ m ∈ n)
      * `nat_no_three_cycle` - ¬(n ∈ m ∧ m ∈ k ∧ k ∈ n)

    - Propiedades estructurales:
      * `nat_element_is_nat` - m ∈ n → isNat m
      * `nat_element_is_transitive` - elementos son transitivos
      * `nat_element_has_strict_total_order` - elementos tienen orden total
      * `nat_element_has_well_order` - elementos son bien ordenados

    - Clausura y orden:
      * `nat_successor_is_nat` - isNat n → isNat (σ n) ✅
      * `nat_trichotomy` - n ∈ m ∨ n = m ∨ m ∈ n ✅
      * `no_nat_between` - entre n y σ(n) no hay otros naturales
      * `nat_subset_mem_or_eq` - n ⊆ m → n ∈ m ∨ n = m ✅
      * `nat_mem_trans` - n ∈ m → m ∈ k → n ∈ k ✅
      * `nat_mem_asymm` - n ∈ m → m ∉ n ✅

    - Segmentos iniciales:
      * `isInitialSegment` - definición de segmento inicial
      * `initial_segment_of_nat_is_eq_or_mem` - segmento inicial es igual o elemento
      * `inter_nat_is_initial_segment` - intersección es segmento inicial
      * `nat_is_initial_segment` - n ∈ m → n es segmento inicial de m ✅
      * `nat_element_trichotomy` - elementos de m cumplen tricotomía ✅

    - Propiedades del sucesor:
      * `successor_injective` - σ(n) = σ(m) → n = m ✅
      * `successor_nonempty` - σ(n) ≠ ∅ ✅
      * `mem_successor_of_mem` - m ∈ n → m ∈ σ(n) ✅

    ### ❌ TEOREMAS PENDIENTES (requieren más desarrollo):

    2. Teoremas sobre conjuntos inductivos (requieren Axioma de Infinito):
       - Existencia del conjunto ω de todos los naturales
       - ω es inductivo
       - ω es el menor conjunto inductivo
       - Todo natural pertenece a ω
       - Caracterización: `isNat n ↔ n ∈ ω`

    3. Principio de inducción (requiere ω):
       - Forma débil: `P(0) → (∀n, P(n) → P(σ(n))) → (∀n ∈ ω, P(n))`
       - Forma fuerte: usando bien-orden de ω
       - Recursión sobre naturales

    4. Aritmética básica:
       - Suma: n + m
       - Multiplicación: n × m
       - Orden: n < m, n ≤ m
       - Propiedades algebraicas (asociatividad, conmutatividad, distributividad)

    ## Notas técnicas:
    - La totalidad de teoremas están probados SIN el Axioma de Regularidad
    - La tricotomía está completamente probada usando segmentos iniciales
    - El Axioma de Infinito es necesario solo para ω y la inducción
    - Muchos teoremas "pendientes" son derivables de los ya probados
      pero requieren trabajo adicional de formalización
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
    mem_successor_of_mem
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
