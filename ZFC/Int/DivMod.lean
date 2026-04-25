/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Divisibility

  This module defines divisibility on ℤ and proves basic algebraic properties.

  ## Main Definitions

  * `dividesZ` — a divides b in ℤ: ∃ k ∈ ℤ, b = mulZ a k

  ## Main Theorems

  * `dividesZ_refl` — a | a
  * `dividesZ_zero` — a | 0
  * `zero_dividesZ_iff` — 0 | b ↔ b = 0
  * `dividesZ_trans` — a | b → b | c → a | c
  * `dividesZ_negZ_right` — a | b → a | (-b)
  * `dividesZ_negZ_left` — a | b ↔ (-a) | b
  * `dividesZ_mulZ_left` — a | (a · b)
  * `dividesZ_mulZ_right` — a | b → a | (b · c)
  * `one_dividesZ` — 1 | a
  * `dividesZ_add` — a | b → a | c → a | (b + c)
  * `dividesZ_sub` — a | b → a | c → a | (b - c)
  * `dividesZ_mulZ_right_factor` — a | (c · a)
  * `dividesZ_negZ_left_right` — a | b ↔ a | (-b)

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Int.Ring

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
  open ZFC.Int.Mul
  open ZFC.Int.Ring

  universe u
  variable {U : Type u}

  namespace Int.DivMod

    /-- `dividesZ a b` means `b` is a multiple of `a`:
        there exists `k ∈ ℤ` with `b = mulZ a k`. -/
    def dividesZ (a b : U) : Prop :=
      ∃ k : U, k ∈ (IntSet : U) ∧ b = mulZ a k

    /-- Reflexivity: a | a for a ∈ ℤ. -/
    theorem dividesZ_refl (a : U) (ha : a ∈ (IntSet : U)) :
        dividesZ a a := by
      exact ⟨oneZ, oneZ_mem_IntSet, (mulZ_one_right a ha).symm⟩

    /-- Every element divides zero: a | 0. -/
    theorem dividesZ_zero (a : U) (ha : a ∈ (IntSet : U)) :
        dividesZ a (zeroZ : U) := by
      exact ⟨zeroZ, zeroZ_mem_IntSet, (mulZ_zero_right a ha).symm⟩

    /-- Zero divides only zero: 0 | b ↔ b = 0. -/
    theorem zero_dividesZ_iff (b : U) (_hb : b ∈ (IntSet : U)) :
        dividesZ (zeroZ : U) b ↔ b = (zeroZ : U) := by
      constructor
      · intro ⟨k, hk, h_eq⟩
        rw [mulZ_zero_left k hk] at h_eq
        exact h_eq
      · intro h_eq
        rw [h_eq]
        exact dividesZ_zero zeroZ zeroZ_mem_IntSet

    /-- Transitivity: a | b → b | c → a | c. -/
    theorem dividesZ_trans (a b c : U)
        (ha : a ∈ (IntSet : U)) (_hb : b ∈ (IntSet : U)) (_hc : c ∈ (IntSet : U)) :
        dividesZ a b → dividesZ b c → dividesZ a c := by
      intro ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
      exact ⟨mulZ k₁ k₂, mulZ_in_IntSet k₁ k₂ hk₁ hk₂, by
        rw [h₂, h₁, mulZ_assoc a k₁ k₂ ha hk₁ hk₂]⟩

    /-- If a | b then a | (-b). -/
    theorem dividesZ_negZ_right (a b : U)
        (ha : a ∈ (IntSet : U)) (_hb : b ∈ (IntSet : U)) :
        dividesZ a b → dividesZ a (negZ b) := by
      intro ⟨k, hk, h_eq⟩
      exact ⟨negZ k, negZ_in_IntSet k hk, by
        rw [h_eq, mulZ_negZ_right a k ha hk]⟩

    /-- a | b ↔ (-a) | b. -/
    theorem dividesZ_negZ_left (a b : U)
        (ha : a ∈ (IntSet : U)) (_hb : b ∈ (IntSet : U)) :
        dividesZ a b ↔ dividesZ (negZ a) b := by
      constructor
      · intro ⟨k, hk, h_eq⟩
        exact ⟨negZ k, negZ_in_IntSet k hk, by
          rw [h_eq]; exact (negZ_mulZ_negZ a k ha hk).symm⟩
      · intro ⟨k, hk, h_eq⟩
        exact ⟨negZ k, negZ_in_IntSet k hk, by
          rw [h_eq, mulZ_negZ_left a k ha hk, mulZ_negZ_right a k ha hk]⟩

    /-- a divides a · b. -/
    theorem dividesZ_mulZ_left (a b : U)
        (_ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        dividesZ a (mulZ a b) := by
      exact ⟨b, hb, rfl⟩

    /-- If a | b then a | (b · c). -/
    theorem dividesZ_mulZ_right (a b c : U)
        (ha : a ∈ (IntSet : U)) (_hb : b ∈ (IntSet : U)) (hc : c ∈ (IntSet : U)) :
        dividesZ a b → dividesZ a (mulZ b c) := by
      intro ⟨k, hk, h_eq⟩
      exact ⟨mulZ k c, mulZ_in_IntSet k c hk hc, by
        rw [h_eq, mulZ_assoc a k c ha hk hc]⟩

    /-- 1 divides any element: 1 | a for a ∈ ℤ. -/
    theorem one_dividesZ (a : U) (ha : a ∈ (IntSet : U)) :
        dividesZ (oneZ : U) a := by
      exact ⟨a, ha, (mulZ_one_left a ha).symm⟩

    /-- If a | b and a | c then a | (b + c). -/
    theorem dividesZ_add (a b c : U)
        (ha : a ∈ (IntSet : U)) (_hb : b ∈ (IntSet : U)) (_hc : c ∈ (IntSet : U)) :
        dividesZ a b → dividesZ a c → dividesZ a (addZ b c) := by
      intro ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
      exact ⟨addZ k₁ k₂, addZ_in_IntSet k₁ k₂ hk₁ hk₂, by
        rw [h₁, h₂, ← mulZ_addZ_distrib_left a k₁ k₂ ha hk₁ hk₂]⟩

    /-- If a | b and a | c then a | (b - c). -/
    theorem dividesZ_sub (a b c : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) (hc : c ∈ (IntSet : U)) :
        dividesZ a b → dividesZ a c → dividesZ a (subZ b c) := by
      intro h_ab h_ac
      have h_neg : dividesZ a (negZ c) := dividesZ_negZ_right a c ha hc h_ac
      exact dividesZ_add a b (negZ c) ha hb (negZ_in_IntSet c hc)
        h_ab h_neg

    /-- a divides c · a (right factor). -/
    theorem dividesZ_mulZ_right_factor (a c : U)
        (ha : a ∈ (IntSet : U)) (hc : c ∈ (IntSet : U)) :
        dividesZ a (mulZ c a) := by
      exact ⟨c, hc, (mulZ_comm a c ha hc).symm⟩

    /-- a | b ↔ a | (-b). -/
    theorem dividesZ_negZ_left_right (a b : U)
        (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
        dividesZ a b ↔ dividesZ a (negZ b) := by
      constructor
      · exact dividesZ_negZ_right a b ha hb
      · intro h
        have h2 := dividesZ_negZ_right a (negZ b) ha (negZ_in_IntSet b hb) h
        rw [negZ_negZ b hb] at h2
        exact h2

  end Int.DivMod

  export Int.DivMod (
    dividesZ
    dividesZ_refl
    dividesZ_zero
    zero_dividesZ_iff
    dividesZ_trans
    dividesZ_negZ_right
    dividesZ_negZ_left
    dividesZ_mulZ_left
    dividesZ_mulZ_right
    one_dividesZ
    dividesZ_add
    dividesZ_sub
    dividesZ_mulZ_right_factor
    dividesZ_negZ_left_right
  )

end ZFC
