/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Maximum and Minimum on ℤ

  This module defines `maxZ` and `minZ` on ℤ directly from the total order `leZ`,
  without recursion (unlike the ω case which uses the Peano bridge).

  ## Main Definitions

  * `maxZ x y` — maximum of x and y (= y if x ≤ y, else x)
  * `minZ x y` — minimum of x and y (= x if x ≤ y, else y)

  ## Main Theorems

  * `maxZ_in_IntSet`      — closure: x, y ∈ ℤ → maxZ x y ∈ ℤ
  * `leZ_maxZ_left`       — x ≤ maxZ x y
  * `leZ_maxZ_right`      — y ≤ maxZ x y
  * `maxZ_leZ`            — x ≤ z → y ≤ z → maxZ x y ≤ z
  * `maxZ_comm`           — maxZ x y = maxZ y x
  * `maxZ_assoc`          — maxZ x (maxZ y z) = maxZ (maxZ x y) z
  * `maxZ_idem`           — maxZ x x = x
  * `minZ_in_IntSet`      — closure: x, y ∈ ℤ → minZ x y ∈ ℤ
  * `minZ_leZ_left`       — minZ x y ≤ x
  * `minZ_leZ_right`      — minZ x y ≤ y
  * `leZ_minZ`            — z ≤ x → z ≤ y → z ≤ minZ x y
  * `minZ_comm`           — minZ x y = minZ y x
  * `minZ_assoc`          — minZ x (minZ y z) = minZ (minZ x y) z
  * `minZ_idem`           — minZ x x = x

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Int.Order

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Order

  universe u
  variable {U : Type u}

  namespace Int.MaxMin

    -- =========================================================================
    -- §0  Definitions
    -- =========================================================================

    /-- `maxZ x y` is the maximum of `x` and `y` in ℤ. -/
    noncomputable def maxZ (x y : U) : U :=
      if leZ x y then y else x

    /-- `minZ x y` is the minimum of `x` and `y` in ℤ. -/
    noncomputable def minZ (x y : U) : U :=
      if leZ x y then x else y

    -- =========================================================================
    -- §1  Closure
    -- =========================================================================

    theorem maxZ_in_IntSet (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        maxZ x y ∈ (IntSet : U) := by
      unfold maxZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact hy
      · simp only [if_neg h]; exact hx

    theorem minZ_in_IntSet (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        minZ x y ∈ (IntSet : U) := by
      unfold minZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact hx
      · simp only [if_neg h]; exact hy

    -- =========================================================================
    -- §2  Boundedness
    -- =========================================================================

    theorem leZ_maxZ_left (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ x (maxZ x y) := by
      unfold maxZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact h
      · simp only [if_neg h]; exact leZ_refl x hx

    theorem leZ_maxZ_right (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ y (maxZ x y) := by
      unfold maxZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact leZ_refl y hy
      · simp only [if_neg h]
        rcases leZ_total x y hx hy with h_le | h_ge
        · exact absurd h_le h
        · exact h_ge

    theorem maxZ_leZ (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (hxz : leZ x z) (hyz : leZ y z) :
        leZ (maxZ x y) z := by
      unfold maxZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact hyz
      · simp only [if_neg h]; exact hxz

    theorem minZ_leZ_left (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ (minZ x y) x := by
      unfold minZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact leZ_refl x hx
      · simp only [if_neg h]
        rcases leZ_total x y hx hy with h_le | h_ge
        · exact absurd h_le h
        · exact h_ge

    theorem minZ_leZ_right (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ (minZ x y) y := by
      unfold minZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact h
      · simp only [if_neg h]; exact leZ_refl y hy

    theorem leZ_minZ (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (hzx : leZ z x) (hzy : leZ z y) :
        leZ z (minZ x y) := by
      unfold minZ
      by_cases h : leZ x y
      · simp only [if_pos h]; exact hzx
      · simp only [if_neg h]; exact hzy

    -- =========================================================================
    -- §3  Commutativity
    -- =========================================================================

    theorem maxZ_comm (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        maxZ x y = maxZ y x := by
      unfold maxZ
      by_cases hxy : leZ x y <;> by_cases hyx : leZ y x
      · -- x ≤ y and y ≤ x: antisymmetry gives x = y
        have heq := leZ_antisymm x y hx hy hxy hyx
        simp only [if_pos hxy, if_pos hyx, heq]
      · simp only [if_pos hxy, if_neg hyx]
      · simp only [if_neg hxy, if_pos hyx]
      · -- ¬(x ≤ y) and ¬(y ≤ x): impossible by totality
        have htot := leZ_total x y hx hy
        cases htot with
        | inl h => exact absurd h hxy
        | inr h => exact absurd h hyx

    theorem minZ_comm (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        minZ x y = minZ y x := by
      unfold minZ
      by_cases hxy : leZ x y <;> by_cases hyx : leZ y x
      · have heq := leZ_antisymm x y hx hy hxy hyx
        simp only [if_pos hxy, if_pos hyx, heq]
      · simp only [if_pos hxy, if_neg hyx]
      · simp only [if_neg hxy, if_pos hyx]
      · have htot := leZ_total x y hx hy
        cases htot with
        | inl h => exact absurd h hxy
        | inr h => exact absurd h hyx

    -- =========================================================================
    -- §4  Idempotence
    -- =========================================================================

    theorem maxZ_idem (x : U) (hx : x ∈ (IntSet : U)) :
        maxZ x x = x := by
      unfold maxZ
      simp only [if_pos (leZ_refl x hx)]

    theorem minZ_idem (x : U) (hx : x ∈ (IntSet : U)) :
        minZ x x = x := by
      unfold minZ
      simp only [if_pos (leZ_refl x hx)]

    -- =========================================================================
    -- §5  Associativity
    -- =========================================================================

    /-- Private: `maxZ x y` equals `x` or `y`. -/
    private theorem maxZ_is_left_or_right (x y : U) :
        maxZ x y = x ∨ maxZ x y = y := by
      unfold maxZ
      by_cases h : leZ x y
      · exact Or.inr (if_pos h)
      · exact Or.inl (if_neg h)

    /-- Private: `minZ x y` equals `x` or `y`. -/
    private theorem minZ_is_left_or_right (x y : U) :
        minZ x y = x ∨ minZ x y = y := by
      unfold minZ
      by_cases h : leZ x y
      · exact Or.inl (if_pos h)
      · exact Or.inr (if_neg h)

    theorem maxZ_assoc (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U)) :
        maxZ x (maxZ y z) = maxZ (maxZ x y) z := by
      -- maxZ x (maxZ y z) is the max of x, y, z; prove both sides equal that max
      apply leZ_antisymm
      · exact maxZ_in_IntSet x (maxZ y z) hx (maxZ_in_IntSet y z hy hz)
      · exact maxZ_in_IntSet (maxZ x y) z (maxZ_in_IntSet x y hx hy) hz
      · -- maxZ x (maxZ y z) ≤ maxZ (maxZ x y) z
        apply maxZ_leZ x (maxZ y z) (maxZ (maxZ x y) z)
          hx (maxZ_in_IntSet y z hy hz) (maxZ_in_IntSet (maxZ x y) z
            (maxZ_in_IntSet x y hx hy) hz)
        · -- x ≤ maxZ (maxZ x y) z
          exact leZ_trans x (maxZ x y) (maxZ (maxZ x y) z)
            hx (maxZ_in_IntSet x y hx hy) (maxZ_in_IntSet (maxZ x y) z
              (maxZ_in_IntSet x y hx hy) hz)
            (leZ_maxZ_left x y hx hy)
            (leZ_maxZ_left (maxZ x y) z (maxZ_in_IntSet x y hx hy) hz)
        · -- maxZ y z ≤ maxZ (maxZ x y) z
          apply maxZ_leZ y z (maxZ (maxZ x y) z)
            hy hz (maxZ_in_IntSet (maxZ x y) z (maxZ_in_IntSet x y hx hy) hz)
          · -- y ≤ maxZ (maxZ x y) z
            exact leZ_trans y (maxZ x y) (maxZ (maxZ x y) z)
              hy (maxZ_in_IntSet x y hx hy) (maxZ_in_IntSet (maxZ x y) z
                (maxZ_in_IntSet x y hx hy) hz)
              (leZ_maxZ_right x y hx hy)
              (leZ_maxZ_left (maxZ x y) z (maxZ_in_IntSet x y hx hy) hz)
          · -- z ≤ maxZ (maxZ x y) z
            exact leZ_maxZ_right (maxZ x y) z (maxZ_in_IntSet x y hx hy) hz
      · -- maxZ (maxZ x y) z ≤ maxZ x (maxZ y z)
        apply maxZ_leZ (maxZ x y) z (maxZ x (maxZ y z))
          (maxZ_in_IntSet x y hx hy) hz (maxZ_in_IntSet x (maxZ y z) hx
            (maxZ_in_IntSet y z hy hz))
        · -- maxZ x y ≤ maxZ x (maxZ y z)
          apply maxZ_leZ x y (maxZ x (maxZ y z))
            hx hy (maxZ_in_IntSet x (maxZ y z) hx (maxZ_in_IntSet y z hy hz))
          · exact leZ_maxZ_left x (maxZ y z) hx (maxZ_in_IntSet y z hy hz)
          · exact leZ_trans y (maxZ y z) (maxZ x (maxZ y z))
              hy (maxZ_in_IntSet y z hy hz) (maxZ_in_IntSet x (maxZ y z) hx
                (maxZ_in_IntSet y z hy hz))
              (leZ_maxZ_left y z hy hz)
              (leZ_maxZ_right x (maxZ y z) hx (maxZ_in_IntSet y z hy hz))
        · -- z ≤ maxZ x (maxZ y z)
          exact leZ_trans z (maxZ y z) (maxZ x (maxZ y z))
            hz (maxZ_in_IntSet y z hy hz) (maxZ_in_IntSet x (maxZ y z) hx
              (maxZ_in_IntSet y z hy hz))
            (leZ_maxZ_right y z hy hz)
            (leZ_maxZ_right x (maxZ y z) hx (maxZ_in_IntSet y z hy hz))

    theorem minZ_assoc (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U)) :
        minZ x (minZ y z) = minZ (minZ x y) z := by
      apply leZ_antisymm
      · exact minZ_in_IntSet x (minZ y z) hx (minZ_in_IntSet y z hy hz)
      · exact minZ_in_IntSet (minZ x y) z (minZ_in_IntSet x y hx hy) hz
      · -- minZ x (minZ y z) ≤ minZ (minZ x y) z
        apply leZ_minZ (minZ x y) z (minZ x (minZ y z))
          (minZ_in_IntSet x y hx hy) hz (minZ_in_IntSet x (minZ y z) hx
            (minZ_in_IntSet y z hy hz))
        · -- minZ x (minZ y z) ≤ minZ x y
          apply leZ_minZ x y (minZ x (minZ y z))
            hx hy (minZ_in_IntSet x (minZ y z) hx (minZ_in_IntSet y z hy hz))
          · exact minZ_leZ_left x (minZ y z) hx (minZ_in_IntSet y z hy hz)
          · exact leZ_trans (minZ x (minZ y z)) (minZ y z) y
              (minZ_in_IntSet x (minZ y z) hx (minZ_in_IntSet y z hy hz))
              (minZ_in_IntSet y z hy hz) hy
              (minZ_leZ_right x (minZ y z) hx (minZ_in_IntSet y z hy hz))
              (minZ_leZ_left y z hy hz)
        · -- minZ x (minZ y z) ≤ z
          exact leZ_trans (minZ x (minZ y z)) (minZ y z) z
            (minZ_in_IntSet x (minZ y z) hx (minZ_in_IntSet y z hy hz))
            (minZ_in_IntSet y z hy hz) hz
            (minZ_leZ_right x (minZ y z) hx (minZ_in_IntSet y z hy hz))
            (minZ_leZ_right y z hy hz)
      · -- minZ (minZ x y) z ≤ minZ x (minZ y z)
        apply leZ_minZ x (minZ y z) (minZ (minZ x y) z)
          hx (minZ_in_IntSet y z hy hz) (minZ_in_IntSet (minZ x y) z
            (minZ_in_IntSet x y hx hy) hz)
        · -- minZ (minZ x y) z ≤ x
          exact leZ_trans (minZ (minZ x y) z) (minZ x y) x
            (minZ_in_IntSet (minZ x y) z (minZ_in_IntSet x y hx hy) hz)
            (minZ_in_IntSet x y hx hy) hx
            (minZ_leZ_left (minZ x y) z (minZ_in_IntSet x y hx hy) hz)
            (minZ_leZ_left x y hx hy)
        · -- minZ (minZ x y) z ≤ minZ y z
          apply leZ_minZ y z (minZ (minZ x y) z)
            hy hz (minZ_in_IntSet (minZ x y) z (minZ_in_IntSet x y hx hy) hz)
          · exact leZ_trans (minZ (minZ x y) z) (minZ x y) y
              (minZ_in_IntSet (minZ x y) z (minZ_in_IntSet x y hx hy) hz)
              (minZ_in_IntSet x y hx hy) hy
              (minZ_leZ_left (minZ x y) z (minZ_in_IntSet x y hx hy) hz)
              (minZ_leZ_right x y hx hy)
          · exact minZ_leZ_right (minZ x y) z (minZ_in_IntSet x y hx hy) hz

    -- =========================================================================
    -- §6  Equivalences
    -- =========================================================================

    theorem maxZ_eq_right_iff_leZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        maxZ x y = y ↔ leZ x y := by
      unfold maxZ
      constructor
      · intro h
        by_cases hle : leZ x y
        · exact hle
        · simp only [if_neg hle] at h
          rcases leZ_total x y hx hy with h_le | h_ge
          · exact absurd h_le hle
          · rw [← h]; exact leZ_refl x hx
      · intro h; simp only [if_pos h]

    theorem maxZ_eq_left_iff_leZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        maxZ x y = x ↔ leZ y x := by
      rw [maxZ_comm x y hx hy]
      exact maxZ_eq_right_iff_leZ y x hy hx

    theorem minZ_eq_left_iff_leZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        minZ x y = x ↔ leZ x y := by
      unfold minZ
      constructor
      · intro h
        by_cases hle : leZ x y
        · exact hle
        · simp only [if_neg hle] at h
          rcases leZ_total x y hx hy with h_le | h_ge
          · exact absurd h_le hle
          · rw [h]; exact leZ_refl x hx
      · intro h; simp only [if_pos h]

    theorem minZ_eq_right_iff_leZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        minZ x y = y ↔ leZ y x := by
      rw [minZ_comm x y hx hy]
      exact minZ_eq_left_iff_leZ y x hy hx

  end Int.MaxMin

  export Int.MaxMin (
    maxZ
    minZ
    maxZ_in_IntSet
    minZ_in_IntSet
    leZ_maxZ_left
    leZ_maxZ_right
    maxZ_leZ
    minZ_leZ_left
    minZ_leZ_right
    leZ_minZ
    maxZ_comm
    minZ_comm
    maxZ_idem
    minZ_idem
    maxZ_assoc
    minZ_assoc
    maxZ_eq_right_iff_leZ
    maxZ_eq_left_iff_leZ
    minZ_eq_left_iff_leZ
    minZ_eq_right_iff_leZ
  )

end ZFC
