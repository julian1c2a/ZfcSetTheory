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

    /-! Álgebra Booleana usando operaciones básicas -/

    theorem BinUnion_comm (A B : U) :
      (A ∪ B) = (B ∪ A) := by
      apply ExtSet
      intro x
      simp [BinUnion_is_specified, or_comm]

    theorem BinUnion_empty_left (A : U) :
      (∅ ∪ A) = A := by
      apply ExtSet
      intro x
      simp only [BinUnion_is_specified]
      exact ⟨fun h => h.resolve_left (EmptySet_is_empty x), Or.inr⟩

    theorem BinUnion_empty_right (A : U) :
      (A ∪ ∅) = A := by
      rw [BinUnion_comm, BinUnion_empty_left]

    theorem BinUnion_idem (A : U) :
      (A ∪ A) = A := by
      apply ExtSet
      intro x
      simp only [BinUnion_is_specified]
      constructor
      · intro h
        cases h with
        | inl hx => exact hx
        | inr hx => exact hx
      · intro hx
        exact Or.inl hx

    /-! Intersección Binaria -/
    theorem BinIntersection_idem (A : U) :
      (A ∩ A) = A := by
      apply ExtSet
      intro x
      simp only [BinIntersection_is_specified]
      constructor
      · intro ⟨hx, _⟩
        exact hx
      · intro hx
        exact ⟨hx, hx⟩

    theorem BinIntersection_empty (A : U) :
      (A ∩ ∅) = ∅ := by
      apply ExtSet
      intro x
      simp only [BinIntersection_is_specified]
      constructor
      · intro ⟨_, hx⟩
        exact hx
      · intro hx
        exact False.elim (EmptySet_is_empty x hx)

    theorem BinIntersection_comm (A B : U) :
      (A ∩ B) = (B ∩ A) := by
      apply ExtSet
      intro x
      simp only [BinIntersection_is_specified]
      constructor
      · intro ⟨hxA, hxB⟩
        exact ⟨hxB, hxA⟩
      · intro ⟨hxB, hxA⟩
        exact ⟨hxA, hxB⟩


    /-! Transitividad -/
    theorem Subseteq_trans (A B C : U) :
      A ⊆ B → B ⊆ C → A ⊆ C := by
      intro h1 h2 x hx
      exact h2 x (h1 x hx)

    theorem Subseteq_reflexive (A : U) :
      A ⊆ A := by
      intro x hx
      exact hx


    /-! Monotonía -/
    theorem Union_monotone (A B C : U) :
      A ⊆ B → (A ∪ C) ⊆ (B ∪ C) := by
      intro h x hx
      simp only [BinUnion_is_specified] at hx ⊢
      rcases hx with hxA | hxC
      · left; exact h x hxA
      · right; exact hxC

    theorem Inter_monotone (A B C : U) :
      A ⊆ B → (A ∩ C) ⊆ (B ∩ C) := by
      intro h x ⟨hx, hc⟩
      exact ⟨h x hx, hc⟩

    /-! Equivalencias -/
    theorem Subseteq_inter_eq (A B : U) :
      (A ⊆ B) ↔ ((A ∩ B) = A) := ⟨
      fun h => by
        apply ExtSet
        intro x
        constructor
        · intro ⟨ha, _⟩; exact ha
        · intro ha; exact ⟨ha, h x ha⟩,
      fun h x hx => by rw [← h]; exact hx⟩

    /-! Diferencia -/
    theorem Diff_self (A : U) :
      (A \ A) = ∅ := by
      apply ExtSet
      intro x
      simp only [Difference_is_specified]
      exact ⟨fun ⟨_, h⟩ => h rfl, EmptySet_is_empty x⟩

    theorem Diff_empty (A : U) :
      (A \ ∅) = A := by
      apply ExtSet
      intro x
      simp only [Difference_is_specified]
      exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, fun h => EmptySet_is_empty x h⟩⟩

  end BooleanAlgebra

end SetUniverse

export SetUniverse.BooleanAlgebra (
  BinUnion_comm
  BinUnion_empty_left
  BinUnion_empty_right
  BinUnion_idem
  BinIntersection_idem
  BinIntersection_empty
  BinIntersection_comm
  Subseteq_trans
  Subseteq_reflexive
  Union_monotone
  Inter_monotone
  Subseteq_inter_eq
  Diff_self
  Diff_empty
)
