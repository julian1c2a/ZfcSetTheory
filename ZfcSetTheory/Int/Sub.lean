/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Subtraction Properties

  This module proves algebraic properties of integer subtraction,
  which is defined in Neg.lean as `subZ x y := addZ x (negZ y)`.

  ## Main Theorems

  * `subZ_zero_right` — x - 0 = x
  * `subZ_zero_left` — 0 - y = -y
  * `subZ_negZ_right` — x - (-y) = x + y
  * `negZ_subZ` — -(x - y) = y - x
  * `subZ_addZ_cancel` — (x + y) - y = x
  * `addZ_subZ_cancel` — (x - y) + y = x
  * `subZ_eq_zero_iff` — x - y = 0 ↔ x = y
-/

import ZfcSetTheory.Int.Neg

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
  open ZFC.Nat.Add
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg

  universe u
  variable {U : Type u}

  namespace Int.Sub

    /-- x - 0 = x -/
    theorem subZ_zero_right (x : U) (hx : x ∈ (IntSet : U)) :
        subZ x (zeroZ : U) = x := by
      unfold subZ
      rw [negZ_zero, addZ_zero_right x hx]

    /-- 0 - y = -y -/
    theorem subZ_zero_left (y : U) (hy : y ∈ (IntSet : U)) :
        subZ (zeroZ : U) y = negZ y := by
      unfold subZ
      exact addZ_zero_left (negZ y) (negZ_in_IntSet y hy)

    /-- x - (-y) = x + y -/
    theorem subZ_negZ_right (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        subZ x (negZ y) = addZ x y := by
      unfold subZ
      rw [negZ_negZ y hy]

    /-- -(x - y) = y - x -/
    theorem negZ_subZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        negZ (subZ x y) = subZ y x := by
      unfold subZ
      rw [negZ_addZ x (negZ y) hx (negZ_in_IntSet y hy)]
      rw [negZ_negZ y hy]
      rw [addZ_comm (negZ x) y (negZ_in_IntSet x hx) hy]

    /-- (x + y) - y = x -/
    theorem subZ_addZ_cancel (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        subZ (addZ x y) y = x := by
      unfold subZ
      rw [addZ_assoc x y (negZ y) hx hy (negZ_in_IntSet y hy)]
      rw [addZ_negZ_right y hy]
      exact addZ_zero_right x hx

    /-- (x - y) + y = x -/
    theorem addZ_subZ_cancel (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        addZ (subZ x y) y = x := by
      unfold subZ
      rw [addZ_assoc x (negZ y) y hx (negZ_in_IntSet y hy) hy]
      rw [addZ_negZ_left y hy]
      exact addZ_zero_right x hx

    /-- x - y = 0 ↔ x = y -/
    theorem subZ_eq_zero_iff (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        subZ x y = (zeroZ : U) ↔ x = y := by
      constructor
      · intro h
        have h1 : addZ (subZ x y) y = addZ (zeroZ : U) y := by rw [h]
        rw [addZ_subZ_cancel x y hx hy, addZ_zero_left y hy] at h1
        exact h1
      · intro h
        rw [h]
        exact subZ_self y hy

  end Int.Sub

  export Int.Sub (
    subZ_zero_right
    subZ_zero_left
    subZ_negZ_right
    negZ_subZ
    subZ_addZ_cancel
    addZ_subZ_cancel
    subZ_eq_zero_iff
  )

end ZFC
