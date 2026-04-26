/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Maximum and Minimum on ℚ

  This module defines `maxQ` and `minQ` on ℚ directly from the total order `leQ`,
  without recursion.

  ## Main Definitions

  * `maxQ x y` — maximum of x and y (= y if x ≤ y, else x)
  * `minQ x y` — minimum of x and y (= x if x ≤ y, else y)

  ## Main Theorems

  * `maxQ_in_RatSet`      — closure: x, y ∈ ℚ → maxQ x y ∈ ℚ
  * `leQ_maxQ_left`       — x ≤ maxQ x y
  * `leQ_maxQ_right`      — y ≤ maxQ x y
  * `maxQ_leQ`            — x ≤ z → y ≤ z → maxQ x y ≤ z
  * `maxQ_comm`           — maxQ x y = maxQ y x
  * `maxQ_assoc`          — maxQ x (maxQ y z) = maxQ (maxQ x y) z
  * `maxQ_idem`           — maxQ x x = x
  * `minQ_in_RatSet`      — closure: x, y ∈ ℚ → minQ x y ∈ ℚ
  * `minQ_leQ_left`       — minQ x y ≤ x
  * `minQ_leQ_right`      — minQ x y ≤ y
  * `leQ_minQ`            — z ≤ x → z ≤ y → z ≤ minQ x y
  * `minQ_comm`           — minQ x y = minQ y x
  * `minQ_assoc`          — minQ x (minQ y z) = minQ (minQ x y) z
  * `minQ_idem`           — minQ x x = x
  * `maxQ_eq_right_iff_leQ` — maxQ x y = y ↔ leQ x y
  * `maxQ_eq_left_iff_leQ`  — maxQ x y = x ↔ leQ y x
  * `minQ_eq_left_iff_leQ`  — minQ x y = x ↔ leQ x y
  * `minQ_eq_right_iff_leQ` — minQ x y = y ↔ leQ y x

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Order

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
  open ZFC.Int.Order
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Order

  universe u
  variable {U : Type u}

  namespace Rat.MaxMin

    -- =========================================================================
    -- §0  Definitions
    -- =========================================================================

    /-- `maxQ x y` is the maximum of `x` and `y` in ℚ. -/
    noncomputable def maxQ (x y : U) : U :=
      if leQ x y then y else x

    /-- `minQ x y` is the minimum of `x` and `y` in ℚ. -/
    noncomputable def minQ (x y : U) : U :=
      if leQ x y then x else y

    -- =========================================================================
    -- §1  Closure
    -- =========================================================================

    theorem maxQ_in_RatSet (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        maxQ x y ∈ (RatSet : U) := by
      unfold maxQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact hy
      · simp only [if_neg h]; exact hx

    theorem minQ_in_RatSet (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        minQ x y ∈ (RatSet : U) := by
      unfold minQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact hx
      · simp only [if_neg h]; exact hy

    -- =========================================================================
    -- §2  Boundedness
    -- =========================================================================

    theorem leQ_maxQ_left (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ x (maxQ x y) := by
      unfold maxQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact h
      · simp only [if_neg h]; exact leQ_refl x hx

    theorem leQ_maxQ_right (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ y (maxQ x y) := by
      unfold maxQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact leQ_refl y hy
      · simp only [if_neg h]
        rcases leQ_total x y hx hy with h_le | h_ge
        · exact absurd h_le h
        · exact h_ge

    theorem maxQ_leQ (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (_hz : z ∈ (RatSet : U))
        (hxz : leQ x z) (hyz : leQ y z) :
        leQ (maxQ x y) z := by
      unfold maxQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact hyz
      · simp only [if_neg h]; exact hxz

    theorem minQ_leQ_left (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ (minQ x y) x := by
      unfold minQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact leQ_refl x hx
      · simp only [if_neg h]
        rcases leQ_total x y hx hy with h_le | h_ge
        · exact absurd h_le h
        · exact h_ge

    theorem minQ_leQ_right (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ (minQ x y) y := by
      unfold minQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact h
      · simp only [if_neg h]; exact leQ_refl y hy

    theorem leQ_minQ (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (_hz : z ∈ (RatSet : U))
        (hzx : leQ z x) (hzy : leQ z y) :
        leQ z (minQ x y) := by
      unfold minQ
      by_cases h : leQ x y
      · simp only [if_pos h]; exact hzx
      · simp only [if_neg h]; exact hzy

    -- =========================================================================
    -- §3  Commutativity
    -- =========================================================================

    theorem maxQ_comm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        maxQ x y = maxQ y x := by
      unfold maxQ
      by_cases hxy : leQ x y <;> by_cases hyx : leQ y x
      · have heq := leQ_antisymm x y hx hy hxy hyx
        simp only [if_pos hxy, if_pos hyx, heq]
      · simp only [if_pos hxy, if_neg hyx]
      · simp only [if_neg hxy, if_pos hyx]
      · have htot := leQ_total x y hx hy
        cases htot with
        | inl h => exact absurd h hxy
        | inr h => exact absurd h hyx

    theorem minQ_comm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        minQ x y = minQ y x := by
      unfold minQ
      by_cases hxy : leQ x y <;> by_cases hyx : leQ y x
      · have heq := leQ_antisymm x y hx hy hxy hyx
        simp only [if_pos hxy, if_pos hyx, heq]
      · simp only [if_pos hxy, if_neg hyx]
      · simp only [if_neg hxy, if_pos hyx]
      · have htot := leQ_total x y hx hy
        cases htot with
        | inl h => exact absurd h hxy
        | inr h => exact absurd h hyx

    -- =========================================================================
    -- §4  Idempotence
    -- =========================================================================

    theorem maxQ_idem (x : U) (hx : x ∈ (RatSet : U)) :
        maxQ x x = x := by
      unfold maxQ
      simp only [if_pos (leQ_refl x hx)]

    theorem minQ_idem (x : U) (hx : x ∈ (RatSet : U)) :
        minQ x x = x := by
      unfold minQ
      simp only [if_pos (leQ_refl x hx)]

    -- =========================================================================
    -- §5  Associativity
    -- =========================================================================

    theorem maxQ_assoc (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        maxQ x (maxQ y z) = maxQ (maxQ x y) z := by
      apply leQ_antisymm
      · exact maxQ_in_RatSet x (maxQ y z) hx (maxQ_in_RatSet y z hy hz)
      · exact maxQ_in_RatSet (maxQ x y) z (maxQ_in_RatSet x y hx hy) hz
      · apply maxQ_leQ x (maxQ y z) (maxQ (maxQ x y) z)
          hx (maxQ_in_RatSet y z hy hz) (maxQ_in_RatSet (maxQ x y) z
            (maxQ_in_RatSet x y hx hy) hz)
        · exact leQ_trans x (maxQ x y) (maxQ (maxQ x y) z)
            hx (maxQ_in_RatSet x y hx hy) (maxQ_in_RatSet (maxQ x y) z
              (maxQ_in_RatSet x y hx hy) hz)
            (leQ_maxQ_left x y hx hy)
            (leQ_maxQ_left (maxQ x y) z (maxQ_in_RatSet x y hx hy) hz)
        · apply maxQ_leQ y z (maxQ (maxQ x y) z)
            hy hz (maxQ_in_RatSet (maxQ x y) z (maxQ_in_RatSet x y hx hy) hz)
          · exact leQ_trans y (maxQ x y) (maxQ (maxQ x y) z)
              hy (maxQ_in_RatSet x y hx hy) (maxQ_in_RatSet (maxQ x y) z
                (maxQ_in_RatSet x y hx hy) hz)
              (leQ_maxQ_right x y hx hy)
              (leQ_maxQ_left (maxQ x y) z (maxQ_in_RatSet x y hx hy) hz)
          · exact leQ_maxQ_right (maxQ x y) z (maxQ_in_RatSet x y hx hy) hz
      · apply maxQ_leQ (maxQ x y) z (maxQ x (maxQ y z))
          (maxQ_in_RatSet x y hx hy) hz (maxQ_in_RatSet x (maxQ y z) hx
            (maxQ_in_RatSet y z hy hz))
        · apply maxQ_leQ x y (maxQ x (maxQ y z))
            hx hy (maxQ_in_RatSet x (maxQ y z) hx (maxQ_in_RatSet y z hy hz))
          · exact leQ_maxQ_left x (maxQ y z) hx (maxQ_in_RatSet y z hy hz)
          · exact leQ_trans y (maxQ y z) (maxQ x (maxQ y z))
              hy (maxQ_in_RatSet y z hy hz) (maxQ_in_RatSet x (maxQ y z) hx
                (maxQ_in_RatSet y z hy hz))
              (leQ_maxQ_left y z hy hz)
              (leQ_maxQ_right x (maxQ y z) hx (maxQ_in_RatSet y z hy hz))
        · exact leQ_trans z (maxQ y z) (maxQ x (maxQ y z))
            hz (maxQ_in_RatSet y z hy hz) (maxQ_in_RatSet x (maxQ y z) hx
              (maxQ_in_RatSet y z hy hz))
            (leQ_maxQ_right y z hy hz)
            (leQ_maxQ_right x (maxQ y z) hx (maxQ_in_RatSet y z hy hz))

    theorem minQ_assoc (x y z : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hz : z ∈ (RatSet : U)) :
        minQ x (minQ y z) = minQ (minQ x y) z := by
      apply leQ_antisymm
      · exact minQ_in_RatSet x (minQ y z) hx (minQ_in_RatSet y z hy hz)
      · exact minQ_in_RatSet (minQ x y) z (minQ_in_RatSet x y hx hy) hz
      · apply leQ_minQ (minQ x y) z (minQ x (minQ y z))
          (minQ_in_RatSet x y hx hy) hz (minQ_in_RatSet x (minQ y z) hx
            (minQ_in_RatSet y z hy hz))
        · apply leQ_minQ x y (minQ x (minQ y z))
            hx hy (minQ_in_RatSet x (minQ y z) hx (minQ_in_RatSet y z hy hz))
          · exact minQ_leQ_left x (minQ y z) hx (minQ_in_RatSet y z hy hz)
          · exact leQ_trans (minQ x (minQ y z)) (minQ y z) y
              (minQ_in_RatSet x (minQ y z) hx (minQ_in_RatSet y z hy hz))
              (minQ_in_RatSet y z hy hz) hy
              (minQ_leQ_right x (minQ y z) hx (minQ_in_RatSet y z hy hz))
              (minQ_leQ_left y z hy hz)
        · exact leQ_trans (minQ x (minQ y z)) (minQ y z) z
            (minQ_in_RatSet x (minQ y z) hx (minQ_in_RatSet y z hy hz))
            (minQ_in_RatSet y z hy hz) hz
            (minQ_leQ_right x (minQ y z) hx (minQ_in_RatSet y z hy hz))
            (minQ_leQ_right y z hy hz)
      · apply leQ_minQ x (minQ y z) (minQ (minQ x y) z)
          hx (minQ_in_RatSet y z hy hz) (minQ_in_RatSet (minQ x y) z
            (minQ_in_RatSet x y hx hy) hz)
        · exact leQ_trans (minQ (minQ x y) z) (minQ x y) x
            (minQ_in_RatSet (minQ x y) z (minQ_in_RatSet x y hx hy) hz)
            (minQ_in_RatSet x y hx hy) hx
            (minQ_leQ_left (minQ x y) z (minQ_in_RatSet x y hx hy) hz)
            (minQ_leQ_left x y hx hy)
        · apply leQ_minQ y z (minQ (minQ x y) z)
            hy hz (minQ_in_RatSet (minQ x y) z (minQ_in_RatSet x y hx hy) hz)
          · exact leQ_trans (minQ (minQ x y) z) (minQ x y) y
              (minQ_in_RatSet (minQ x y) z (minQ_in_RatSet x y hx hy) hz)
              (minQ_in_RatSet x y hx hy) hy
              (minQ_leQ_left (minQ x y) z (minQ_in_RatSet x y hx hy) hz)
              (minQ_leQ_right x y hx hy)
          · exact minQ_leQ_right (minQ x y) z (minQ_in_RatSet x y hx hy) hz

    -- =========================================================================
    -- §6  Equivalences
    -- =========================================================================

    theorem maxQ_eq_right_iff_leQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        maxQ x y = y ↔ leQ x y := by
      unfold maxQ
      constructor
      · intro h
        by_cases hle : leQ x y
        · exact hle
        · simp only [if_neg hle] at h
          rcases leQ_total x y hx hy with h_le | h_ge
          · exact absurd h_le hle
          · rw [← h]; exact leQ_refl x hx
      · intro h; simp only [if_pos h]

    theorem maxQ_eq_left_iff_leQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        maxQ x y = x ↔ leQ y x := by
      rw [maxQ_comm x y hx hy]
      exact maxQ_eq_right_iff_leQ y x hy hx

    theorem minQ_eq_left_iff_leQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        minQ x y = x ↔ leQ x y := by
      unfold minQ
      constructor
      · intro h
        by_cases hle : leQ x y
        · exact hle
        · simp only [if_neg hle] at h
          rcases leQ_total x y hx hy with h_le | h_ge
          · exact absurd h_le hle
          · rw [h]; exact leQ_refl x hx
      · intro h; simp only [if_pos h]

    theorem minQ_eq_right_iff_leQ (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        minQ x y = y ↔ leQ y x := by
      rw [minQ_comm x y hx hy]
      exact minQ_eq_left_iff_leQ y x hy hx

  end Rat.MaxMin

  export Rat.MaxMin (
    maxQ
    minQ
    maxQ_in_RatSet
    minQ_in_RatSet
    leQ_maxQ_left
    leQ_maxQ_right
    maxQ_leQ
    minQ_leQ_left
    minQ_leQ_right
    leQ_minQ
    maxQ_comm
    minQ_comm
    maxQ_idem
    minQ_idem
    maxQ_assoc
    minQ_assoc
    maxQ_eq_right_iff_leQ
    maxQ_eq_left_iff_leQ
    minQ_eq_left_iff_leQ
    minQ_eq_right_iff_leQ
  )

end ZFC
