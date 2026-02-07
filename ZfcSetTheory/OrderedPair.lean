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

  namespace OrderedPairExtensions

    /-! ============================================================ -/
    /-! ### EXTENSIONES DEL PAR ORDENADO ### -/
    /-! ============================================================ -/

    /-! Nota: La definición de OrderedPair (Kuratowski) y sus
        teoremas principales ya están en Pairing.lean:
        - OrderedPair, OrderedPair_is_specified
        - fst, snd, fst_of_ordered_pair, snd_of_ordered_pair
        - Eq_of_OrderedPairs_given_projections
        - pair_set_eq_singleton, ordered_pair_self_eq_singleton_singleton
        - isOrderedPair, OrderedPairSet_is_WellConstructed, Eq_OrderedPairs

        Aquí añadimos teoremas adicionales convenientes. -/

    /-! ### Igualdad de pares ordenados (←) ###
        Si a = c ∧ b = d entonces ⟨a, b⟩ = ⟨c, d⟩ -/
    theorem OrderedPair_eq_of (a b c d : U) :
      (a = c ∧ b = d) → ⟨a, b⟩ = ⟨c, d⟩
        := by
      intro h
      rw [h.1, h.2]

    /-! ### Caracterización completa de igualdad de pares ordenados ### -/
    theorem OrderedPair_eq_iff (a b c d : U) :
      ⟨a, b⟩ = ⟨c, d⟩ ↔ (a = c ∧ b = d)
        := by
      constructor
      · exact Eq_of_OrderedPairs_given_projections a b c d
      · exact OrderedPair_eq_of a b c d

    /-! ============================================================ -/
    /-! ### PROPIEDADES ADICIONALES ### -/
    /-! ============================================================ -/

    /-! ### El par ordenado pertenece a 𝒫(𝒫(A ∪ B)) si a ∈ A y b ∈ B ### -/
    theorem OrderedPair_in_PowerSet (a b A B : U)
      (ha : a ∈ A) (hb : b ∈ B) :
        ⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
          := by
      -- ⟨a, b⟩ = {{a}, {a, b}}
      -- Necesitamos {{a}, {a, b}} ⊆ 𝒫(A ∪ B)
      rw [PowerSet_is_specified]
      -- Objetivo: {{a}, {a, b}} ⊆ 𝒫(A ∪ B)
      intro z hz
      -- z ∈ {{a}, {a, b}}, entonces z = {a} ∨ z = {a, b}
      rw [OrderedPair_is_specified] at hz
      rw [PowerSet_is_specified]
      cases hz with
      | inl hz_eq_singleton =>
        -- z = {a}, probamos {a} ⊆ A ∪ B
        rw [hz_eq_singleton]
        intro w hw
        rw [Singleton_is_specified] at hw
        rw [BinUnion_is_specified, hw]
        exact Or.inl ha
      | inr hz_eq_pair =>
        -- z = {a, b}, probamos {a, b} ⊆ A ∪ B
        rw [hz_eq_pair]
        intro w hw
        rw [PairSet_is_specified] at hw
        rw [BinUnion_is_specified]
        cases hw with
        | inl hw_eq_a => rw [hw_eq_a]; exact Or.inl ha
        | inr hw_eq_b => rw [hw_eq_b]; exact Or.inr hb

  end OrderedPairExtensions
end SetUniverse

export SetUniverse.OrderedPairExtensions (
  OrderedPair_eq_of
  OrderedPair_eq_iff
  OrderedPair_in_PowerSet
)

/-!
## Par Ordenado (Kuratowski) - Extensiones

### Definición (en Pairing.lean):
⟨a, b⟩ = {{a}, {a, b}}

### Teoremas heredados de Pairing.lean:
- `OrderedPair`, `OrderedPair_is_specified`
- `fst`, `snd`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
- `Eq_of_OrderedPairs_given_projections`: ⟨a, b⟩ = ⟨c, d⟩ → a = c ∧ b = d
- `pair_set_eq_singleton`: {x, x} = {x}
- `ordered_pair_self_eq_singleton_singleton`: ⟨x, x⟩ = {{x}}
- `isOrderedPair`, `OrderedPairSet_is_WellConstructed`, `Eq_OrderedPairs`

### Teoremas adicionales (definidos aquí):
- `OrderedPair_eq_of`: (a = c ∧ b = d) → ⟨a, b⟩ = ⟨c, d⟩
- `OrderedPair_eq_iff`: ⟨a, b⟩ = ⟨c, d⟩ ↔ (a = c ∧ b = d)

### Siguiente paso:
Definir el producto cartesiano A × B como el conjunto de todos los
pares ordenados ⟨a, b⟩ con a ∈ A y b ∈ B.
-/
