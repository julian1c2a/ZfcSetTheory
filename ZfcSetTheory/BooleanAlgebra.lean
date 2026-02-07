import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  universe u
  variable {U : Type u}

  namespace BooleanAlgebra

    /-! ### Álgebra Booleana - Teoremas que mezclan ∪ y ∩ ### -/

    /-! Absorción -/
    theorem BinUnion_absorb_inter (A B : U) :
      (A ∪ (A ∩ B)) = A := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinUnion_is_specified] at hx
        cases hx with
        | inl hA => exact hA
        | inr hAB =>
          rw [BinInter_is_specified] at hAB
          exact hAB.1
      · intro hA
        rw [BinUnion_is_specified]
        exact Or.inl hA

    theorem BinInter_absorb_union (A B : U) :
      (A ∩ (A ∪ B)) = A := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinInter_is_specified] at hx
        exact hx.1
      · intro hA
        rw [BinInter_is_specified, BinUnion_is_specified]
        exact ⟨hA, Or.inl hA⟩

    /-! ### Distributividad ### -/

    theorem BinUnion_distrib_inter (A B C : U) :
      (A ∪ (B ∩ C)) = ((A ∪ B) ∩ (A ∪ C)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinUnion_is_specified] at hx
        rw [BinInter_is_specified, BinUnion_is_specified, BinUnion_is_specified]
        cases hx with
        | inl hA => exact ⟨Or.inl hA, Or.inl hA⟩
        | inr hBC =>
          rw [BinInter_is_specified] at hBC
          exact ⟨Or.inr hBC.1, Or.inr hBC.2⟩
      · intro hx
        rw [BinInter_is_specified, BinUnion_is_specified, BinUnion_is_specified] at hx
        rw [BinUnion_is_specified]
        cases hx.1 with
        | inl hA => exact Or.inl hA
        | inr hB =>
          cases hx.2 with
          | inl hA => exact Or.inl hA
          | inr hC =>
            rw [BinInter_is_specified]
            exact Or.inr ⟨hB, hC⟩

    theorem BinInter_distrib_union (A B C : U) :
      (A ∩ (B ∪ C)) = ((A ∩ B) ∪ (A ∩ C)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinInter_is_specified, BinUnion_is_specified] at hx
        rw [BinUnion_is_specified]
        cases hx.2 with
        | inl hB =>
          rw [BinInter_is_specified]
          exact Or.inl ⟨hx.1, hB⟩
        | inr hC =>
          exact Or.inr ((BinInter_is_specified A C x).mpr ⟨hx.1, hC⟩)
      · intro hx
        rw [BinUnion_is_specified] at hx
        rw [BinInter_is_specified, BinUnion_is_specified]
        cases hx with
        | inl hAB =>
          rw [BinInter_is_specified] at hAB
          exact ⟨hAB.1, Or.inl hAB.2⟩
        | inr hAC =>
          rw [BinInter_is_specified] at hAC
          exact ⟨hAC.1, Or.inr hAC.2⟩

    /-! ### Leyes de De Morgan ### -/

    theorem DeMorgan_union (A B C : U) :
      (C \ (A ∪ B)) = ((C \ A) ∩ (C \ B)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [Difference_is_specified, BinUnion_is_specified] at hx
        rw [BinInter_is_specified, Difference_is_specified, Difference_is_specified]
        constructor
        · exact ⟨hx.1, fun hA => hx.2 (Or.inl hA)⟩
        · exact ⟨hx.1, fun hB => hx.2 (Or.inr hB)⟩
      · intro hx
        rw [BinInter_is_specified, Difference_is_specified, Difference_is_specified] at hx
        rw [Difference_is_specified, BinUnion_is_specified]
        exact ⟨hx.1.1, fun h => h.elim hx.1.2 hx.2.2⟩

    theorem DeMorgan_inter (A B C : U) :
      (C \ (A ∩ B)) = ((C \ A) ∪ (C \ B)) := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [Difference_is_specified, BinInter_is_specified] at hx
        rw [BinUnion_is_specified]
        by_cases hA : x ∈ A
        · -- x ∈ A, entonces x ∉ B (de lo contrario x ∈ A ∩ B)
          have hnotB : x ∉ B := fun hB => hx.2 ⟨hA, hB⟩
          exact Or.inr ((Difference_is_specified C B x).mpr ⟨hx.1, hnotB⟩)
        · -- x ∉ A
          exact Or.inl ((Difference_is_specified C A x).mpr ⟨hx.1, hA⟩)
      · intro hx
        rw [BinUnion_is_specified] at hx
        rw [Difference_is_specified, BinInter_is_specified]
        cases hx with
        | inl hCA =>
          rw [Difference_is_specified] at hCA
          exact ⟨hCA.1, fun hAB => hCA.2 hAB.1⟩
        | inr hCB =>
          rw [Difference_is_specified] at hCB
          exact ⟨hCB.1, fun hAB => hCB.2 hAB.2⟩

    /-! ### Complemento Relativo ### -/

    theorem Complement_union (A C : U) (h : A ⊆ C) :
      (A ∪ (C \ A)) = C := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinUnion_is_specified] at hx
        cases hx with
        | inl hA => exact h x hA
        | inr hCA =>
          rw [Difference_is_specified] at hCA
          exact hCA.1
      · intro hC
        rw [BinUnion_is_specified]
        by_cases hA : x ∈ A
        · exact Or.inl hA
        · rw [Difference_is_specified]
          exact Or.inr ⟨hC, hA⟩

    theorem Complement_inter (A C : U) :
      (A ∩ (C \ A)) = ∅ := by
      apply ExtSet
      intro x
      constructor
      · intro hx
        rw [BinInter_is_specified, Difference_is_specified] at hx
        exact False.elim (hx.2.2 hx.1)
      · intro hEmpty
        exact False.elim (EmptySet_is_empty x hEmpty)

  end BooleanAlgebra

end SetUniverse

export SetUniverse.BooleanAlgebra (
  BinUnion_absorb_inter
  BinInter_absorb_union
  BinUnion_distrib_inter
  BinInter_distrib_union
  DeMorgan_union
  DeMorgan_inter
  Complement_union
  Complement_inter
)
