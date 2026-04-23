/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Negation and Subtraction

  This module defines negation on ℤ via QuotientLift of the swap
  operation (a,b) ↦ (b,a), and subtraction as addZ x (negZ y).

  ## Main Definitions

  * `negZ` — negation on ℤ: negZ [(a,b)] = [(b,a)]
  * `subZ` — subtraction on ℤ: subZ x y = addZ x (negZ y)

  ## Main Theorems

  * `negZ_class` — computation rule: negZ [(a,b)] = [(b,a)]
  * `negZ_in_IntSet` — closure: x ∈ ℤ → negZ x ∈ ℤ
  * `addZ_negZ_right` — right inverse: addZ x (negZ x) = 0ℤ
  * `addZ_negZ_left` — left inverse: addZ (negZ x) x = 0ℤ
  * `negZ_negZ` — involution: negZ (negZ x) = x
  * `negZ_zero` — negZ 0ℤ = 0ℤ
  * `negZ_addZ` — homomorphism: negZ (addZ x y) = addZ (negZ x) (negZ y)
  * `subZ_self` — subZ x x = 0ℤ
  * `subZ_in_IntSet` — closure for subtraction

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones §3, §4 y §6 correspondientes.
-/

import ZFC.Int.Add

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

  universe u
  variable {U : Type u}

  namespace Int.Neg

    /-! ### Helper: decomposition of IntSet elements -/

    /-- Every element of ℤ is an equivalence class of some pair (a, b) with a, b ∈ ω -/
    private theorem intClass_exists (z : U) (hz : z ∈ (IntSet : U)) :
        ∃ a b : U, a ∈ (ω : U) ∧ b ∈ (ω : U) ∧ z = intClass a b := by
      unfold IntSet at hz
      rw [mem_QuotientSet] at hz
      obtain ⟨p, hp_mem, hz_eq⟩ := hz
      rw [CartesianProduct_is_specified] at hp_mem
      obtain ⟨⟨a, b, hp_eq⟩, hp_fst, hp_snd⟩ := hp_mem
      subst hp_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hp_fst hp_snd
      exact ⟨a, b, hp_fst, hp_snd, hz_eq⟩

    /-! ### The negation function on ω × ω -/

    /-- The negation function on ω × ω, mapping to IntSet via EqClass -/
    noncomputable def negZ_fn (p : U) : U :=
      intClass (snd p) (fst p)

    /-- negZ_fn maps elements of ω × ω into IntSet -/
    private theorem negZ_fn_closed (p : U) (hp : p ∈ (ω : U) ×ₛ ω) :
        negZ_fn p ∈ (IntSet : U) := by
      rw [CartesianProduct_is_specified] at hp
      obtain ⟨_, hp_fst, hp_snd⟩ := hp
      unfold negZ_fn
      exact intClass_mem_IntSet _ _ hp_snd hp_fst

    /-- negZ_fn respects IntEquivRel (compatibility for QuotientLift) -/
    private theorem negZ_fn_compat (x y : U)
        (hx : x ∈ (ω : U) ×ₛ ω) (hy : y ∈ (ω : U) ×ₛ ω)
        (hR : ⟨x, y⟩ ∈ (IntEquivRel : U)) :
        negZ_fn x = negZ_fn y := by
      rw [CartesianProduct_is_specified] at hx hy
      obtain ⟨⟨a, b, hx_eq⟩, hfa, hsa⟩ := hx
      obtain ⟨⟨c, d, hy_eq⟩, hfc, hsc⟩ := hy
      subst hx_eq; subst hy_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      rw [mem_IntEquivRel] at hR
      obtain ⟨_, _, _, _, hR_eq⟩ := hR
      -- hR_eq : add a d = add b c
      unfold negZ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      -- Goal: intClass b a = intClass d c
      rw [intClass_eq_iff b a d c hsa hfa hsc hfc]
      -- Goal: add b c = add a d
      exact hR_eq.symm

    /-! ### Definition of negation on ℤ -/

    /-- The graph of integer negation, constructed via QuotientLift -/
    noncomputable def negZ_graph : U :=
      QuotientLiftGraph negZ_fn IntEquivRel ((ω : U) ×ₛ ω) IntSet

    /-- Negation on ℤ -/
    noncomputable def negZ (x : U) : U := negZ_graph⦅x⦆

    /-! ### Computation rule -/

    /-- negZ [(a,b)] = [(b,a)] -/
    theorem negZ_class (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) :
        negZ (intClass a b) = intClass b a := by
      unfold negZ negZ_graph
      have h_unfold : intClass a b = EqClass (⟨a, b⟩ : U) IntEquivRel ((ω : U) ×ₛ ω) := rfl
      rw [h_unfold]
      rw [QuotientLift_apply negZ_fn IntEquivRel ((ω : U) ×ₛ ω) IntSet ⟨a, b⟩
          IntEquivRel_is_equivalence
          negZ_fn_closed
          negZ_fn_compat
          ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)]
      unfold negZ_fn
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]

    /-! ### Closure -/

    /-- Negation is closed on ℤ -/
    theorem negZ_in_IntSet (x : U) (hx : x ∈ (IntSet : U)) :
        negZ x ∈ (IntSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      rw [negZ_class a b ha hb]
      exact intClass_mem_IntSet b a hb ha

    /-! ### Algebraic properties -/

    /-- Well-definedness: if [(a,b)] = [(c,d)] then [(b,a)] = [(d,c)] -/
    theorem negZ_well_defined (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U))
        (h : intClass a b = intClass c d) :
        intClass b a = intClass d c := by
      rw [← negZ_class a b ha hb, ← negZ_class c d hc hd, h]

    /-- Right additive inverse: addZ x (negZ x) = zeroZ -/
    theorem addZ_negZ_right (x : U) (hx : x ∈ (IntSet : U)) :
        addZ x (negZ x) = (zeroZ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      rw [negZ_class a b ha hb]
      rw [addZ_class a b b a ha hb hb ha]
      unfold zeroZ
      rw [intClass_eq_iff (add a b) (add b a) ∅ ∅
          (add_in_Omega a b ha hb) (add_in_Omega b a hb ha)
          zero_in_Omega zero_in_Omega]
      -- Goal: add (add a b) ∅ = add (add b a) ∅
      rw [add_zero (add a b) (add_in_Omega a b ha hb)]
      rw [add_zero (add b a) (add_in_Omega b a hb ha)]
      exact add_comm_Omega a b ha hb

    /-- Left additive inverse: addZ (negZ x) x = zeroZ -/
    theorem addZ_negZ_left (x : U) (hx : x ∈ (IntSet : U)) :
        addZ (negZ x) x = (zeroZ : U) := by
      rw [addZ_comm (negZ x) x (negZ_in_IntSet x hx) hx]
      exact addZ_negZ_right x hx

    /-- Negation is an involution: negZ (negZ x) = x -/
    theorem negZ_negZ (x : U) (hx : x ∈ (IntSet : U)) :
        negZ (negZ x) = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      rw [negZ_class a b ha hb]
      rw [negZ_class b a hb ha]

    /-- Negation of zero is zero: negZ 0ℤ = 0ℤ -/
    theorem negZ_zero : negZ (zeroZ : U) = (zeroZ : U) := by
      unfold zeroZ
      rw [negZ_class ∅ ∅ zero_in_Omega zero_in_Omega]

    /-- Negation distributes over addition: negZ (addZ x y) = addZ (negZ x) (negZ y) -/
    theorem negZ_addZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        negZ (addZ x y) = addZ (negZ x) (negZ y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [addZ_class a b c d ha hb hc hd]
      rw [negZ_class (add a c) (add b d)
          (add_in_Omega a c ha hc) (add_in_Omega b d hb hd)]
      rw [negZ_class a b ha hb, negZ_class c d hc hd]
      rw [addZ_class b a d c hb ha hd hc]

    /-! ### Subtraction -/

    /-- Subtraction on ℤ: subZ x y := addZ x (negZ y) -/
    noncomputable def subZ (x y : U) : U := addZ x (negZ y)

    /-- subZ x x = zeroZ -/
    theorem subZ_self (x : U) (hx : x ∈ (IntSet : U)) :
        subZ x x = (zeroZ : U) := by
      unfold subZ
      exact addZ_negZ_right x hx

    /-- Subtraction is closed on ℤ -/
    theorem subZ_in_IntSet (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        subZ x y ∈ (IntSet : U) := by
      unfold subZ
      exact addZ_in_IntSet x (negZ y) hx (negZ_in_IntSet y hy)

  end Int.Neg

end ZFC

export ZFC.Int.Neg (
  negZ
  negZ_class
  negZ_in_IntSet
  negZ_well_defined
  addZ_negZ_right
  addZ_negZ_left
  negZ_negZ
  negZ_zero
  negZ_addZ
  subZ
  subZ_self
  subZ_in_IntSet
)
