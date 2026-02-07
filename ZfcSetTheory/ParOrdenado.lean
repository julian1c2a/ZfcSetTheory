import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.Potencia

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  universe u
  variable {U : Type u}

  namespace OrderedPairAxiom

    /-! ============================================================ -/
    /-! ### PAR ORDENADO (Definición de Kuratowski) ### -/
    /-! ============================================================ -/

    /-! ### Definición de Par Ordenado ###
        (a, b) = {{a}, {a, b}}
        Esta es la definición clásica de Kuratowski (1921) -/
    @[simp]
    noncomputable def OrderedPair (a b : U) : U :=
      PairSet ({a} : U) (PairSet a b)

    notation "⦅" a ", " b "⦆" => OrderedPair a b

    /-! ### El par ordenado está bien definido ### -/
    theorem OrderedPair_is_specified (a b : U) :
      ⦅a, b⦆ = PairSet ({a} : U) (PairSet a b)
        := rfl

    /-! ============================================================ -/
    /-! ### TEOREMA FUNDAMENTAL DE PARES ORDENADOS ### -/
    /-! ============================================================ -/

    /-! ### Igualdad de pares ordenados (→) ###
        Si (a, b) = (c, d) entonces a = c ∧ b = d -/
    theorem OrderedPair_eq_implies (a b c d : U) :
      ⦅a, b⦆ = ⦅c, d⦆ → (a = c ∧ b = d)
        := by
      intro h
      unfold OrderedPair at h
      -- h : {{a}, {a,b}} = {{c}, {c,d}}
      -- Por igualdad de conjuntos, {a} ∈ {{c}, {c,d}}
      have h_singleton_a : ({a} : U) ∈ PairSet ({c} : U) (PairSet c d) := by
        have : ({a} : U) ∈ PairSet ({a} : U) (PairSet a b) := by
          rw [PairSet_is_specified]
          exact Or.inl rfl
        rw [h] at this
        exact this
      -- {a} = {c} ∨ {a} = {c,d}
      rw [PairSet_is_specified] at h_singleton_a
      cases h_singleton_a with
      | inl h_eq_singleton =>
        -- {a} = {c}, entonces a = c
        have ha_eq_c : a = c := by
          have : a ∈ ({a} : U) := (Singleton_is_specified a a).mpr rfl
          rw [h_eq_singleton] at this
          exact (Singleton_is_specified c a).mp this
        constructor
        · exact ha_eq_c
        · -- Ahora probamos b = d
          -- {a,b} ∈ {{c}, {c,d}}
          have h_pair_ab : PairSet a b ∈ PairSet ({c} : U) (PairSet c d) := by
            have : PairSet a b ∈ PairSet ({a} : U) (PairSet a b) := by
              rw [PairSet_is_specified]
              exact Or.inr rfl
            rw [h] at this
            exact this
          rw [PairSet_is_specified] at h_pair_ab
          cases h_pair_ab with
          | inl h_ab_eq_c =>
            -- {a,b} = {c}
            -- Entonces a = c y b = c
            have ha_in : a ∈ PairSet a b := by
              rw [PairSet_is_specified]; exact Or.inl rfl
            rw [h_ab_eq_c] at ha_in
            have ha_eq_c' : a = c := (Singleton_is_specified c a).mp ha_in
            have hb_in : b ∈ PairSet a b := by
              rw [PairSet_is_specified]; exact Or.inr rfl
            rw [h_ab_eq_c] at hb_in
            have hb_eq_c : b = c := (Singleton_is_specified c b).mp hb_in
            -- También d ∈ {c,d} y {c,d} ∈ {{c},{c,d}}
            have h_pair_cd : PairSet c d ∈ PairSet ({c} : U) (PairSet c d) := by
              rw [PairSet_is_specified]; exact Or.inr rfl
            -- Por simetría, {c,d} = {a} ∨ {c,d} = {a,b}
            have h_cd_in : PairSet c d ∈ PairSet ({a} : U) (PairSet a b) := by
              rw [←h]; exact h_pair_cd
            rw [PairSet_is_specified] at h_cd_in
            cases h_cd_in with
            | inl h_cd_eq_a =>
              -- {c,d} = {a}
              have hd_in : d ∈ PairSet c d := by
                rw [PairSet_is_specified]; exact Or.inr rfl
              rw [h_cd_eq_a] at hd_in
              have hd_eq_a : d = a := (Singleton_is_specified a d).mp hd_in
              rw [hb_eq_c, ha_eq_c, hd_eq_a]
            | inr h_cd_eq_ab =>
              -- {c,d} = {a,b}
              have hd_in : d ∈ PairSet c d := by
                rw [PairSet_is_specified]; exact Or.inr rfl
              rw [h_cd_eq_ab] at hd_in
              rw [PairSet_is_specified] at hd_in
              cases hd_in with
              | inl hd_eq_a => rw [hb_eq_c, ha_eq_c, hd_eq_a]
              | inr hd_eq_b => exact hd_eq_b.symm
          | inr h_ab_eq_cd =>
            -- {a,b} = {c,d}
            -- d ∈ {c,d} = {a,b}, así que d = a ∨ d = b
            have hd_in : d ∈ PairSet a b := by
              have : d ∈ PairSet c d := by
                rw [PairSet_is_specified]; exact Or.inr rfl
              rw [←h_ab_eq_cd] at this
              exact this
            rw [PairSet_is_specified] at hd_in
            cases hd_in with
            | inl hd_eq_a =>
              -- d = a = c, entonces c = d
              -- c ∈ {c,d} = {a,b}
              have hc_in : c ∈ PairSet a b := by
                have : c ∈ PairSet c d := by
                  rw [PairSet_is_specified]; exact Or.inl rfl
                rw [←h_ab_eq_cd] at this
                exact this
              rw [PairSet_is_specified] at hc_in
              cases hc_in with
              | inl hc_eq_a =>
                -- c = a, d = a, entonces a = b = c = d
                rw [←ha_eq_c, hd_eq_a]
              | inr hc_eq_b =>
                -- c = b, d = a
                rw [←hc_eq_b, ←hd_eq_a, ha_eq_c, hc_eq_b]
            | inr hd_eq_b => exact hd_eq_b.symm
      | inr h_eq_pair =>
        -- {a} = {c,d}
        -- Entonces c ∈ {a} y d ∈ {a}, así que c = a y d = a
        have hc_in : c ∈ ({a} : U) := by
          have : c ∈ PairSet c d := by
            rw [PairSet_is_specified]; exact Or.inl rfl
          rw [←h_eq_pair] at this
          exact this
        have hd_in : d ∈ ({a} : U) := by
          have : d ∈ PairSet c d := by
            rw [PairSet_is_specified]; exact Or.inr rfl
          rw [←h_eq_pair] at this
          exact this
        have hc_eq_a : c = a := (Singleton_is_specified a c).mp hc_in
        have hd_eq_a : d = a := (Singleton_is_specified a d).mp hd_in
        -- Ahora a = c y debemos probar b = d
        constructor
        · exact hc_eq_a.symm
        · -- {a,b} ∈ {{c},{c,d}} = {{a},{a,a}} = {{a}}
          have h_pair_ab : PairSet a b ∈ PairSet ({c} : U) (PairSet c d) := by
            have : PairSet a b ∈ PairSet ({a} : U) (PairSet a b) := by
              rw [PairSet_is_specified]; exact Or.inr rfl
            rw [h] at this
            exact this
          rw [PairSet_is_specified] at h_pair_ab
          cases h_pair_ab with
          | inl h_ab_eq_c =>
            -- {a,b} = {c} = {a}
            have hb_in : b ∈ PairSet a b := by
              rw [PairSet_is_specified]; exact Or.inr rfl
            rw [h_ab_eq_c] at hb_in
            have hb_eq_c : b = c := (Singleton_is_specified c b).mp hb_in
            rw [hb_eq_c, hd_eq_a, hc_eq_a]
          | inr h_ab_eq_cd =>
            -- {a,b} = {c,d} = {a,a} = {a}
            have hb_in : b ∈ PairSet a b := by
              rw [PairSet_is_specified]; exact Or.inr rfl
            rw [h_ab_eq_cd] at hb_in
            rw [PairSet_is_specified] at hb_in
            cases hb_in with
            | inl hb_eq_c => rw [hb_eq_c, hd_eq_a, hc_eq_a]
            | inr hb_eq_d => rw [hb_eq_d, hd_eq_a, hc_eq_a]

    /-! ### Igualdad de pares ordenados (←) ###
        Si a = c ∧ b = d entonces (a, b) = (c, d) -/
    theorem OrderedPair_eq_of (a b c d : U) :
      (a = c ∧ b = d) → ⦅a, b⦆ = ⦅c, d⦆
        := by
      intro ⟨hac, hbd⟩
      rw [hac, hbd]

    /-! ### Caracterización completa de igualdad de pares ordenados ### -/
    theorem OrderedPair_eq_iff (a b c d : U) :
      ⦅a, b⦆ = ⦅c, d⦆ ↔ (a = c ∧ b = d)
        := by
      constructor
      · exact OrderedPair_eq_implies a b c d
      · exact OrderedPair_eq_of a b c d

    /-! ============================================================ -/
    /-! ### COMPONENTES DEL PAR ORDENADO ### -/
    /-! ============================================================ -/

    /-! ### Primera componente (proyección izquierda) ###
        fst(⦅a, b⦆) = a
        Se puede definir como ⋃ ⋂ ⦅a, b⦆ -/

    -- /-! ### Definición de primera componente ### -/
    -- noncomputable def fst (p : U) : U :=
    --   ⋃ (⋂ p)  -- ⋃ {a} = a cuando p = ⦅a, b⦆

    -- /-! ### Segunda componente (proyección derecha) ###
    --     snd(⦅a, b⦆) = b
    --     Más compleja: requiere distinguir casos -/

    -- noncomputable def snd (p : U) : U :=
    --   sorry -- Definición más elaborada

    -- /-! ### Teoremas de proyección ### -/
    -- theorem fst_pair (a b : U) : fst ⦅a, b⦆ = a := by sorry
    -- theorem snd_pair (a b : U) : snd ⦅a, b⦆ = b := by sorry

    /-! ============================================================ -/
    /-! ### PROPIEDADES ADICIONALES ### -/
    /-! ============================================================ -/

    /-! ### El par ordenado pertenece a 𝒫(𝒫(A ∪ B)) si a ∈ A y b ∈ B ### -/
    -- theorem OrderedPair_in_PowerSet (a b A B : U)
    --   (ha : a ∈ A) (hb : b ∈ B) :
    --     ⦅a, b⦆ ∈ 𝒫 (𝒫 (A ∪ B))
    --       := by sorry

    /-! ### Pares ordenados con componentes iguales ### -/
    theorem OrderedPair_diag (a : U) :
      ⦅a, a⦆ = PairSet ({a} : U) ({a} : U)
        := by
      unfold OrderedPair
      -- PairSet a a = {a} (singleton)
      have h : PairSet a a = ({a} : U) := PairSet_diag a
      rw [h]

  end OrderedPairAxiom
end SetUniverse

export SetUniverse.OrderedPairAxiom (
  OrderedPair
  OrderedPair_is_specified
  OrderedPair_eq_implies
  OrderedPair_eq_of
  OrderedPair_eq_iff
  OrderedPair_diag
  -- fst
  -- snd
  -- fst_pair
  -- snd_pair
)

/-!
## Par Ordenado (Kuratowski)

### Definición:
(a, b) = {{a}, {a, b}}

### Motivación:
A diferencia del par no ordenado {a, b} = {b, a}, necesitamos una construcción
donde el orden importe. La definición de Kuratowski logra esto: (a, b) ≠ (b, a)
cuando a ≠ b.

### Teorema Fundamental:
(a, b) = (c, d) ↔ a = c ∧ b = d

Este teorema es crucial porque garantiza que el par ordenado "recuerda"
el orden de sus componentes.

### Ejemplos:
- (1, 2) = {{1}, {1, 2}}
- (2, 1) = {{2}, {2, 1}} = {{2}, {1, 2}}
- (1, 2) ≠ (2, 1) porque {1} ≠ {2}
- (a, a) = {{a}, {a, a}} = {{a}, {a}} = {{a}}

### Proyecciones (para desarrollo futuro):
- fst((a, b)) = a = ⋃ ⋂ (a, b)
- snd((a, b)) = b (requiere definición más elaborada)

### Siguiente paso:
Definir el producto cartesiano A × B como el conjunto de todos los
pares ordenados (a, b) con a ∈ A y b ∈ B.
-/
