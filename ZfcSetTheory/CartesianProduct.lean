import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.PowerSet
import ZfcSetTheory.OrderedPair

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  universe u
  variable {U : Type u}

  namespace CartesianProduct

    /-! ============================================================ -/
    /-! ### PRODUCTO CARTESIANO ### -/
    /-! ============================================================ -/

    /-! El producto cartesiano A × B es el conjunto de todos los
        pares ordenados ⟨a, b⟩ donde a ∈ A y b ∈ B.

        Definición: A × B = { p ∈ 𝒫(𝒫(A ∪ B)) | isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B }
    -/

    /-! ### Definición del Producto Cartesiano ### -/
    noncomputable def CartesianProduct (A B : U) : U :=
      SpecSet (𝒫 (𝒫 (A ∪ B))) (fun p => isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)

    notation:70 A:71 " ×ₛ " B:71 => CartesianProduct A B

    /-! ### Teorema de Caracterización ### -/
    theorem CartesianProduct_is_specified (A B p : U) :
      p ∈ (A ×ₛ B) ↔ (isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)
        := by
      unfold CartesianProduct
      rw [SpecSet_is_specified]
      constructor
      · intro h
        exact h.2
      · intro h
        obtain ⟨hop, ha, hb⟩ := h
        constructor
        · -- p ∈ 𝒫(𝒫(A ∪ B))
          -- isOrderedPair p significa ∃ a b, p = ⟨a, b⟩
          obtain ⟨a, b, hp_eq⟩ := hop
          rw [hp_eq]
          have ha' : a ∈ A := by rw [hp_eq, fst_of_ordered_pair] at ha; exact ha
          have hb' : b ∈ B := by rw [hp_eq, snd_of_ordered_pair] at hb; exact hb
          exact OrderedPair_in_PowerSet a b A B ha' hb'
        · exact ⟨hop, ha, hb⟩

    /-! ### Caracterización con par ordenado explícito ### -/
    theorem OrderedPair_mem_CartesianProduct (a b A B : U) :
      ⟨ a , b ⟩ ∈ (A ×ₛ B) ↔ (a ∈ A ∧ b ∈ B)
        := by
      rw [CartesianProduct_is_specified]
      constructor
      · intro h
        rw [fst_of_ordered_pair] at h
        rw [snd_of_ordered_pair] at h
        exact ⟨h.2.1, h.2.2⟩
      · intro h
        obtain ⟨ha, hb⟩ := h
        constructor
        · -- isOrderedPair ⟨a, b⟩
          exact ⟨a, b, rfl⟩
        · rw [fst_of_ordered_pair, snd_of_ordered_pair]
          exact ⟨ha, hb⟩

    /-! ### Producto con conjunto vacío ### -/
    theorem CartesianProduct_empty_left (B : U) :
      (∅ ×ₛ B) = ∅
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        have hfst := hp.2.1
        exact False.elim (EmptySet_is_empty (fst p) hfst)
      · intro hp
        exact False.elim (EmptySet_is_empty p hp)

    theorem CartesianProduct_empty_right (A : U) :
      (A ×ₛ ∅) = ∅
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        have hsnd := hp.2.2
        exact False.elim (EmptySet_is_empty (snd p) hsnd)
      · intro hp
        exact False.elim (EmptySet_is_empty p hp)

    /-! ### Monotonía del Producto Cartesiano ### -/
    theorem CartesianProduct_mono (A A' B B' : U)
      (hA : A ⊆ A') (hB : B ⊆ B') :
        (A ×ₛ B) ⊆ (A' ×ₛ B')
          := by
      intro p hp
      rw [CartesianProduct_is_specified] at hp ⊢
      exact ⟨hp.1, hA (fst p) hp.2.1, hB (snd p) hp.2.2⟩

    /-! ### Distributividad con Unión ### -/
    theorem CartesianProduct_distrib_union_left (A B C : U) :
      ((A ∪ B) ×ₛ C) = ((A ×ₛ C) ∪ (B ×ₛ C))
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        rw [BinUnion_is_specified]
        have hfst := hp.2.1
        rw [BinUnion_is_specified] at hfst
        cases hfst with
        | inl hA =>
          left
          rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hA, hp.2.2⟩
        | inr hB =>
          right
          rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hB, hp.2.2⟩
      · intro hp
        rw [BinUnion_is_specified] at hp
        rw [CartesianProduct_is_specified]
        cases hp with
        | inl hAC =>
          rw [CartesianProduct_is_specified] at hAC
          constructor
          · exact hAC.1
          · constructor
            · rw [BinUnion_is_specified]
              exact Or.inl hAC.2.1
            · exact hAC.2.2
        | inr hBC =>
          rw [CartesianProduct_is_specified] at hBC
          constructor
          · exact hBC.1
          · constructor
            · rw [BinUnion_is_specified]
              exact Or.inr hBC.2.1
            · exact hBC.2.2

    theorem CartesianProduct_distrib_union_right (A B C : U) :
      (A ×ₛ (B ∪ C)) = ((A ×ₛ B) ∪ (A ×ₛ C))
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        rw [BinUnion_is_specified]
        have hsnd := hp.2.2
        rw [BinUnion_is_specified] at hsnd
        cases hsnd with
        | inl hB =>
          left
          rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hp.2.1, hB⟩
        | inr hC =>
          right
          rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hp.2.1, hC⟩
      · intro hp
        rw [BinUnion_is_specified] at hp
        rw [CartesianProduct_is_specified]
        cases hp with
        | inl hAB =>
          rw [CartesianProduct_is_specified] at hAB
          constructor
          · exact hAB.1
          · constructor
            · exact hAB.2.1
            · rw [BinUnion_is_specified]
              exact Or.inl hAB.2.2
        | inr hAC =>
          rw [CartesianProduct_is_specified] at hAC
          constructor
          · exact hAC.1
          · constructor
            · exact hAC.2.1
            · rw [BinUnion_is_specified]
              exact Or.inr hAC.2.2

    /-! ### Distributividad con Intersección ### -/
    theorem CartesianProduct_distrib_inter_left (A B C : U) :
      ((A ∩ B) ×ₛ C) = ((A ×ₛ C) ∩ (B ×ₛ C))
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        rw [BinInter_is_specified]
        have hfst := hp.2.1
        rw [BinInter_is_specified] at hfst
        constructor
        · rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hfst.1, hp.2.2⟩
        · rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hfst.2, hp.2.2⟩
      · intro hp
        rw [BinInter_is_specified] at hp
        obtain ⟨hpAC, hpBC⟩ := hp
        rw [CartesianProduct_is_specified] at hpAC hpBC
        rw [CartesianProduct_is_specified]
        constructor
        · exact hpAC.1
        · constructor
          · rw [BinInter_is_specified]
            exact ⟨hpAC.2.1, hpBC.2.1⟩
          · exact hpAC.2.2

    theorem CartesianProduct_distrib_inter_right (A B C : U) :
      (A ×ₛ (B ∩ C)) = ((A ×ₛ B) ∩ (A ×ₛ C))
        := by
      apply ExtSet
      intro p
      constructor
      · intro hp
        rw [CartesianProduct_is_specified] at hp
        rw [BinInter_is_specified]
        have hsnd := hp.2.2
        rw [BinInter_is_specified] at hsnd
        constructor
        · rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hp.2.1, hsnd.1⟩
        · rw [CartesianProduct_is_specified]
          exact ⟨hp.1, hp.2.1, hsnd.2⟩
      · intro hp
        rw [BinInter_is_specified] at hp
        obtain ⟨hpAB, hpAC⟩ := hp
        rw [CartesianProduct_is_specified] at hpAB hpAC
        rw [CartesianProduct_is_specified]
        constructor
        · exact hpAB.1
        · constructor
          · exact hpAB.2.1
          · rw [BinInter_is_specified]
            exact ⟨hpAB.2.2, hpAC.2.2⟩

  end CartesianProduct
end SetUniverse

export SetUniverse.CartesianProduct (
  CartesianProduct
  CartesianProduct_is_specified
  OrderedPair_mem_CartesianProduct
  CartesianProduct_empty_left
  CartesianProduct_empty_right
  CartesianProduct_mono
  CartesianProduct_distrib_union_left
  CartesianProduct_distrib_union_right
  CartesianProduct_distrib_inter_left
  CartesianProduct_distrib_inter_right
)

/-!
## Producto Cartesiano

### Definición:
A ×ₛ B = { p ∈ 𝒫(𝒫(A ∪ B)) | isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B }

### Notación:
- `A ×ₛ B` denota el producto cartesiano de A y B
- Se usa ×ₛ (subíndice s de "set") para evitar conflicto con × de tipos

### Teoremas:
- `CartesianProduct_is_specified`: p ∈ A ×ₛ B ↔ isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B
- `OrderedPair_mem_CartesianProduct`: ⟨a, b⟩ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B
- `CartesianProduct_empty_left`: ∅ ×ₛ B = ∅
- `CartesianProduct_empty_right`: A ×ₛ ∅ = ∅
- `CartesianProduct_mono`: A ⊆ A' → B ⊆ B' → A ×ₛ B ⊆ A' ×ₛ B'
- `CartesianProduct_distrib_union_left`: (A ∪ B) ×ₛ C = (A ×ₛ C) ∪ (B ×ₛ C)
- `CartesianProduct_distrib_union_right`: A ×ₛ (B ∪ C) = (A ×ₛ B) ∪ (A ×ₛ C)
- `CartesianProduct_distrib_inter_left`: (A ∩ B) ×ₛ C = (A ×ₛ C) ∩ (B ×ₛ C)
- `CartesianProduct_distrib_inter_right`: A ×ₛ (B ∩ C) = (A ×ₛ B) ∩ (A ×ₛ C)
-/
