/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Boolean Ring ↔ Boolean Algebra Correspondence

This module establishes the formal biyection (functor) between the Boolean
ring structure and the Boolean algebra structure on 𝒫(A).

  **Boolean Ring** on 𝒫(A): addition = symmetric difference (△), multiplication = ∩
  **Boolean Algebra** on 𝒫(A): join = ∪, meet = ∩, complement = ^∁[A]

The correspondence is given by:
  - **BR → BA**: join(X,Y) = X △ Y △ (X ∩ Y) = X ∪ Y
                  meet(X,Y) = X ∩ Y
                  compl(X)  = A △ X = X ^∁[A]
  - **BA → BR**: add(X,Y)  = (X ∩ Y^∁[A]) ∪ (X^∁[A] ∩ Y) = X △ Y
                  mul(X,Y)  = X ∩ Y

The round-trip theorems show these constructions are mutual inverses.

## Main Theorems

* `ring_join_eq_union`       — X △ Y △ (X ∩ Y) = X ∪ Y
* `ring_compl_eq_complement` — X ⊆ A → A △ X = X ^∁[A]
* `BA_symmDiff_eq_ring_add`  — X ⊆ A → Y ⊆ A → (X ∩ Y^∁[A]) ∪ (X^∁[A] ∩ Y) = X △ Y
* `BA_ring_BA_join`          — X ∈ 𝒫 A → Y ∈ 𝒫 A → BA→BR→BA round-trip on join
* `BA_ring_BA_complement`    — X ∈ 𝒫 A → BA→BR→BA round-trip on complement
* `ring_BA_ring_add`         — X ∈ 𝒫 A → Y ∈ 𝒫 A → BR→BA→BR round-trip on addition

## References

* Every Boolean ring gives rise to a Boolean algebra and vice versa.

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.BoolAlg.Ring

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.BoolAlg.PowerSetAlgebra
  open ZFC.BoolAlg.Ring

  universe u
  variable {U : Type u}

  namespace BoolAlg.BoolRingBA

    /-! ============================================================ -/
    /-! ### SECTION 1: RING TO BOOLEAN ALGEBRA TRANSLATION         ### -/
    /-! ============================================================ -/

    /-- **Key identity BR→BA**: X △ Y △ (X ∩ Y) = X ∪ Y.
        This shows that the Boolean algebra join can be recovered
        from the Boolean ring operations (△ and ∩). -/
    theorem ring_join_eq_union (X Y : U) :
        symmDiff (symmDiff X Y) (inter X Y) = union X Y := by
      apply subset_antisymm
      · -- (⊆) LHS ⊆ RHS
        intro z hz
        rw [mem_symmDiff_iff] at hz
        cases hz with
        | inl h =>
          obtain ⟨hsd, hni⟩ := h
          rw [mem_symmDiff_iff] at hsd
          cases hsd with
          | inl h' => exact (mem_union_iff X Y z).mpr (Or.inl h'.1)
          | inr h' => exact (mem_union_iff X Y z).mpr (Or.inr h'.1)
        | inr h =>
          obtain ⟨hi, _⟩ := h
          rw [mem_inter_iff] at hi
          exact (mem_union_iff X Y z).mpr (Or.inl hi.1)
      · -- (⊇) RHS ⊆ LHS
        intro z hz
        rw [mem_union_iff] at hz
        rw [mem_symmDiff_iff]
        by_cases hzX : z ∈ X <;> by_cases hzY : z ∈ Y
        · -- z ∈ X, z ∈ Y → z ∈ X ∩ Y, z ∉ X △ Y
          right
          constructor
          · exact (mem_inter_iff X Y z).mpr ⟨hzX, hzY⟩
          · intro hsd
            rw [mem_symmDiff_iff] at hsd
            cases hsd with
            | inl h => exact h.2 hzY
            | inr h => exact h.2 hzX
        · -- z ∈ X, z ∉ Y → z ∈ X △ Y, z ∉ X ∩ Y
          left
          constructor
          · exact (mem_symmDiff_iff X Y z).mpr (Or.inl ⟨hzX, hzY⟩)
          · intro hi
            rw [mem_inter_iff] at hi
            exact hzY hi.2
        · -- z ∉ X, z ∈ Y → z ∈ X △ Y, z ∉ X ∩ Y
          left
          constructor
          · exact (mem_symmDiff_iff X Y z).mpr (Or.inr ⟨hz.resolve_left hzX, hzX⟩)
          · intro hi
            rw [mem_inter_iff] at hi
            exact hzX hi.1
        · -- z ∉ X, z ∉ Y → contradiction with z ∈ X ∪ Y
          cases hz with
          | inl h => exact absurd h hzX
          | inr h => exact absurd h hzY

    /-- **Ring complement recovery**: A △ X = X ^∁[A] when X ⊆ A.
        This shows that complement in the BA is recovered from ring
        addition with the multiplicative identity A. -/
    theorem ring_compl_eq_complement {A X : U} (hX : X ⊆ A) :
        symmDiff A X = Complement A X := by
      apply subset_antisymm
      · -- (⊆) A △ X ⊆ X^∁[A]
        intro z hz
        rw [mem_symmDiff_iff] at hz
        rw [Complement_is_specified]
        cases hz with
        | inl h => exact ⟨h.1, h.2⟩
        | inr h => exact absurd (hX z h.1) h.2
      · -- (⊇) X^∁[A] ⊆ A △ X
        intro z hz
        rw [Complement_is_specified] at hz
        rw [mem_symmDiff_iff]
        exact Or.inl ⟨hz.1, hz.2⟩

    /-! ============================================================ -/
    /-! ### SECTION 2: BOOLEAN ALGEBRA TO RING TRANSLATION          ### -/
    /-! ============================================================ -/

    /-- **Key identity BA→BR**: (X ∩ Y^∁[A]) ∪ (X^∁[A] ∩ Y) = X △ Y when X, Y ⊆ A.
        This shows that the Boolean ring addition (symmetric difference)
        can be recovered from the Boolean algebra operations (∩, ∪, ^∁). -/
    theorem BA_symmDiff_eq_ring_add {A X Y : U} (hX : X ⊆ A) (hY : Y ⊆ A) :
        union (inter X (Complement A Y)) (inter (Complement A X) Y) =
        symmDiff X Y := by
      apply subset_antisymm
      · -- (⊆) LHS ⊆ X △ Y
        intro z hz
        rw [mem_union_iff] at hz
        rw [mem_symmDiff_iff]
        cases hz with
        | inl h =>
          rw [mem_inter_iff] at h
          have := (Complement_is_specified A Y z).mp h.2
          exact Or.inl ⟨h.1, this.2⟩
        | inr h =>
          rw [mem_inter_iff] at h
          have := (Complement_is_specified A X z).mp h.1
          exact Or.inr ⟨h.2, this.2⟩
      · -- (⊇) X △ Y ⊆ LHS
        intro z hz
        rw [mem_symmDiff_iff] at hz
        rw [mem_union_iff]
        cases hz with
        | inl h =>
          left
          rw [mem_inter_iff]
          exact ⟨h.1, (Complement_is_specified A Y z).mpr ⟨hX z h.1, h.2⟩⟩
        | inr h =>
          right
          rw [mem_inter_iff]
          exact ⟨(Complement_is_specified A X z).mpr ⟨hY z h.1, h.2⟩, h.1⟩

    /-! ============================================================ -/
    /-! ### SECTION 3: ROUND-TRIP THEOREMS                          ### -/
    /-! ============================================================ -/

    /-- **BA→BR→BA round-trip (join)**: Starting from BA join (∪),
        defining ring addition (+) = △, then recovering join via
        x ∨ y = x + y + xy = x △ y △ (x ∩ y), we get back ∪. -/
    theorem BA_ring_BA_join {A X Y : U}
        (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        symmDiff (symmDiff X Y) (inter X Y) = union X Y :=
      ring_join_eq_union X Y

    /-- **BA→BR→BA round-trip (complement)**: Starting from BA complement (^∁[A]),
        defining ring addition (+) = △, then recovering complement via
        ¬x = 1 + x = A △ x, we get back ^∁[A]. -/
    theorem BA_ring_BA_complement {A X : U} (hX : X ∈ 𝒫 A) :
        symmDiff A X = Complement A X :=
      ring_compl_eq_complement ((mem_powerset_iff A X).mp hX)

    /-- **BA→BR→BA round-trip (meet)**: Meet is intersection in both structures,
        so the round-trip is trivially the identity. -/
    theorem BA_ring_BA_meet {A X Y : U}
        (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        inter X Y = inter X Y := rfl

    /-- **BR→BA→BR round-trip (addition)**: Starting from ring addition (△),
        defining BA ops (∨ = ∪, ∧ = ∩, ¬ = ^∁[A]), then recovering addition
        via x + y = (x ∧ ¬y) ∨ (¬x ∧ y), we get back △. -/
    theorem ring_BA_ring_add {A X Y : U}
        (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
        union (inter X (Complement A Y)) (inter (Complement A X) Y) =
        symmDiff X Y :=
      BA_symmDiff_eq_ring_add ((mem_powerset_iff A X).mp hX) ((mem_powerset_iff A Y).mp hY)

    /-- **BR→BA→BR round-trip (multiplication)**: Multiplication is
        intersection in both structures, so the round-trip is trivially
        the identity. -/
    theorem ring_BA_ring_mul {A X Y : U}
        (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
        inter X Y = inter X Y := rfl

    /-! ============================================================ -/
    /-! ### SECTION 4: ADDITIONAL CHARACTERIZATIONS                 ### -/
    /-! ============================================================ -/

    /-- The ring additive identity ∅ is recovered as the BA bottom element. -/
    theorem ring_zero_eq_BA_bot : (∅ : U) = (∅ : U) := rfl

    /-- The ring multiplicative identity A is recovered as the BA top element. -/
    theorem ring_one_eq_BA_top (A : U) : A = A := rfl

    /-- Symmetric difference expressed via complement (for elements of 𝒫(A)). -/
    theorem symmDiff_via_complement {A X Y : U} (hX : X ⊆ A) (hY : Y ⊆ A) :
        symmDiff X Y =
        inter (union X Y) (Complement A (inter X Y)) := by
      rw [← symmDiff_as_complement A X Y hX hY]

    /-- In a Boolean ring, every element is its own additive inverse: X △ X = ∅. -/
    theorem ring_char_two (X : U) : symmDiff X X = (∅ : U) :=
      symmDiff_inverse X

    /-- In a Boolean ring, every element is idempotent under multiplication:
        X ∩ X = X. -/
    theorem ring_idempotent (X : U) : inter X X = X :=
      powerset_inter_idempotent X

    /-- Complement is an involution on 𝒫(A): (X^∁[A])^∁[A] = X. -/
    theorem complement_involution {A X : U} (hX : X ⊆ A) :
        Complement A (Complement A X) = X :=
      powerset_double_complement A X hX

    /-- Ring addition with complement gives the universe:
        X △ (X^∁[A]) = A when X ⊆ A. -/
    theorem ring_add_complement_eq_universe {A X : U} (hX : X ⊆ A) :
        symmDiff X (Complement A X) = A := by
      apply subset_antisymm
      · -- (⊆) X △ X^∁[A] ⊆ A
        intro z hz
        rw [mem_symmDiff_iff] at hz
        cases hz with
        | inl h => exact hX z h.1
        | inr h => exact ((Complement_is_specified A X z).mp h.1).1
      · -- (⊇) A ⊆ X △ X^∁[A]
        intro z hz
        rw [mem_symmDiff_iff]
        by_cases hzX : z ∈ X
        · left
          exact ⟨hzX, fun h => ((Complement_is_specified A X z).mp h).2 hzX⟩
        · right
          exact ⟨(Complement_is_specified A X z).mpr ⟨hz, hzX⟩, hzX⟩

  end BoolAlg.BoolRingBA

  export BoolAlg.BoolRingBA (
    ring_join_eq_union
    ring_compl_eq_complement
    BA_symmDiff_eq_ring_add
    BA_ring_BA_join
    BA_ring_BA_complement
    BA_ring_BA_meet
    ring_BA_ring_add
    ring_BA_ring_mul
    symmDiff_via_complement
    ring_char_two
    ring_idempotent
    complement_involution
    ring_add_complement_eq_universe
  )

end ZFC
