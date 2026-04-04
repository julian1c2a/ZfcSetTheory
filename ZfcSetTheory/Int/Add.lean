/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Addition

  This module defines addition on ℤ = QuotientSet (ω × ω) IntEquivRel
  using the QuotientLift₂ infrastructure. The operation lifts the
  pairwise addition (a,b) + (c,d) := (a+c, b+d) from ω×ω to ℤ.

  ## Main Definitions

  * `addZ` — addition on ℤ: addZ x y, defined via QuotientLift₂

  ## Main Theorems

  * `addZ_well_defined` — if [(a₁,b₁)] = [(a₂,b₂)] and [(c₁,d₁)] = [(c₂,d₂)]
      then [(a₁+c₁, b₁+d₁)] = [(a₂+c₂, b₂+d₂)]
  * `addZ_class` — computation rule: addZ [(a,b)] [(c,d)] = [(a+c, b+d)]
  * `addZ_in_IntSet` — closure: x, y ∈ ℤ → addZ x y ∈ ℤ
  * `addZ_comm` — commutativity
  * `addZ_assoc` — associativity
  * `addZ_zero_right` — right identity: addZ x 0ℤ = x
  * `addZ_zero_left` — left identity: addZ 0ℤ x = x
-/

import ZfcSetTheory.Int.Basic

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

  universe u
  variable {U : Type u}

  namespace Int.Add

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

    /-! ### Auxiliary: four-variable commutativity -/

    /-- (a+b) + (c+d) = (a+c) + (b+d) for natural numbers -/
    private theorem add_add_comm (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U)) :
        add (add a b) (add c d) = add (add a c) (add b d) := by
      rw [← add_assoc_Omega a b (add c d) ha hb (add_in_Omega c d hc hd)]
      rw [add_assoc_Omega b c d hb hc hd]
      rw [add_comm_Omega b c hb hc]
      rw [← add_assoc_Omega c b d hc hb hd]
      rw [add_assoc_Omega a c (add b d) ha hc (add_in_Omega b d hb hd)]

    /-! ### Pairwise addition operation on ω × ω -/

    /-- The raw operation on ordered pairs: (a,b) + (c,d) := (a+c, b+d) -/
    noncomputable def addZ_op (p q : U) : U :=
      ⟨add (fst p) (fst q), add (snd p) (snd q)⟩

    /-- addZ_op is closed on ω × ω -/
    private theorem addZ_op_closed (p q : U)
        (hp : p ∈ (ω : U) ×ₛ ω) (hq : q ∈ (ω : U) ×ₛ ω) :
        addZ_op p q ∈ (ω : U) ×ₛ ω := by
      rw [CartesianProduct_is_specified] at hp hq
      obtain ⟨_, hp_fst, hp_snd⟩ := hp
      obtain ⟨_, hq_fst, hq_snd⟩ := hq
      unfold addZ_op
      rw [CartesianProduct_is_specified]
      refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩
      · simp only [fst_of_ordered_pair]
        exact add_in_Omega _ _ hp_fst hq_fst
      · simp only [snd_of_ordered_pair]
        exact add_in_Omega _ _ hp_snd hq_snd

    /-- addZ_op respects IntEquivRel (compatibility condition for QuotientLift₂) -/
    private theorem addZ_op_compat (a₁ a₂ b₁ b₂ : U)
        (ha₁ : a₁ ∈ (ω : U) ×ₛ ω) (ha₂ : a₂ ∈ (ω : U) ×ₛ ω)
        (hb₁ : b₁ ∈ (ω : U) ×ₛ ω) (hb₂ : b₂ ∈ (ω : U) ×ₛ ω)
        (hR₁ : ⟨a₁, a₂⟩ ∈ (IntEquivRel : U))
        (hR₂ : ⟨b₁, b₂⟩ ∈ (IntEquivRel : U)) :
        ⟨addZ_op a₁ b₁, addZ_op a₂ b₂⟩ ∈ (IntEquivRel : U) := by
      -- Decompose as ordered pairs
      rw [CartesianProduct_is_specified] at ha₁ ha₂ hb₁ hb₂
      obtain ⟨⟨a, b, ha₁_eq⟩, hfa₁, hsa₁⟩ := ha₁
      obtain ⟨⟨c, d, ha₂_eq⟩, hfa₂, hsa₂⟩ := ha₂
      obtain ⟨⟨e, f, hb₁_eq⟩, hfb₁, hsb₁⟩ := hb₁
      obtain ⟨⟨g, h, hb₂_eq⟩, hfb₂, hsb₂⟩ := hb₂
      subst ha₁_eq; subst ha₂_eq; subst hb₁_eq; subst hb₂_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      -- Extract equivalence hypotheses
      rw [mem_IntEquivRel] at hR₁ hR₂
      obtain ⟨_, _, _, _, hR₁_eq⟩ := hR₁
      obtain ⟨_, _, _, _, hR₂_eq⟩ := hR₂
      -- hR₁_eq : add a d = add b c
      -- hR₂_eq : add e h = add f g
      -- Goal: ⟨⟨add a e, add b f⟩, ⟨add c g, add d h⟩⟩ ∈ IntEquivRel
      unfold addZ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_IntEquivRel]
      refine ⟨add_in_Omega a e hfa₁ hfb₁, add_in_Omega b f hsa₁ hsb₁,
              add_in_Omega c g hfa₂ hfb₂, add_in_Omega d h hsa₂ hsb₂, ?_⟩
      -- Goal: add (add a e) (add d h) = add (add b f) (add c g)
      rw [add_add_comm a e d h hfa₁ hfb₁ hsa₂ hsb₂]
      rw [hR₁_eq, hR₂_eq]
      rw [add_add_comm b c f g hsa₁ hfa₂ hsb₁ hfb₂]

    /-! ### Definition of addition on ℤ -/

    /-- The graph of integer addition, constructed via QuotientLift₂ -/
    noncomputable def addZ_graph : U :=
      QuotientLift₂Graph addZ_op IntEquivRel ((ω : U) ×ₛ ω)

    /-- Addition on ℤ -/
    noncomputable def addZ (x y : U) : U :=
      addZ_graph⦅⟨x, y⟩⦆

    /-! ### Function property -/

    /-- The addition graph is a function from ℤ × ℤ to ℤ -/
    theorem addZ_graph_is_function :
        IsFunction (addZ_graph : U) ((IntSet : U) ×ₛ IntSet) IntSet := by
      unfold addZ_graph IntSet
      exact QuotientLift₂_well_defined addZ_op IntEquivRel ((ω : U) ×ₛ ω)
        IntEquivRel_is_equivalence addZ_op_closed addZ_op_compat

    /-! ### Computation rule -/

    /-- The computation rule for integer addition:
        addZ [(a,b)] [(c,d)] = [(a+c, b+d)] -/
    theorem addZ_class (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U)) :
        addZ (intClass a b) (intClass c d) =
          intClass (add a c) (add b d) := by
      unfold addZ addZ_graph intClass
      rw [QuotientLift₂_apply addZ_op IntEquivRel ((ω : U) ×ₛ ω) ⟨a, b⟩ ⟨c, d⟩
          IntEquivRel_is_equivalence
          addZ_op_closed
          addZ_op_compat
          ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
          ((OrderedPair_mem_CartesianProduct c d ω ω).mpr ⟨hc, hd⟩)]
      unfold addZ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]

    /-! ### Well-definedness -/

    /-- Well-definedness: if [(a₁,b₁)] = [(a₂,b₂)] and [(c₁,d₁)] = [(c₂,d₂)]
        then [(a₁+c₁, b₁+d₁)] = [(a₂+c₂, b₂+d₂)] -/
    theorem addZ_well_defined (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : U)
        (ha₁ : a₁ ∈ (ω : U)) (hb₁ : b₁ ∈ (ω : U))
        (ha₂ : a₂ ∈ (ω : U)) (hb₂ : b₂ ∈ (ω : U))
        (hc₁ : c₁ ∈ (ω : U)) (hd₁ : d₁ ∈ (ω : U))
        (hc₂ : c₂ ∈ (ω : U)) (hd₂ : d₂ ∈ (ω : U))
        (h₁ : intClass a₁ b₁ = intClass a₂ b₂)
        (h₂ : intClass c₁ d₁ = intClass c₂ d₂) :
        intClass (add a₁ c₁) (add b₁ d₁) =
          intClass (add a₂ c₂) (add b₂ d₂) := by
      rw [← addZ_class a₁ b₁ c₁ d₁ ha₁ hb₁ hc₁ hd₁]
      rw [← addZ_class a₂ b₂ c₂ d₂ ha₂ hb₂ hc₂ hd₂]
      rw [h₁, h₂]

    /-! ### Closure -/

    /-- Addition is closed on ℤ -/
    theorem addZ_in_IntSet (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        addZ x y ∈ (IntSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [addZ_class a b c d ha hb hc hd]
      exact intClass_mem_IntSet (add a c) (add b d)
        (add_in_Omega a c ha hc) (add_in_Omega b d hb hd)

    /-! ### Algebraic properties -/

    /-- Addition on ℤ is commutative -/
    theorem addZ_comm (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        addZ x y = addZ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [addZ_class a b c d ha hb hc hd]
      rw [addZ_class c d a b hc hd ha hb]
      rw [add_comm_Omega a c ha hc, add_comm_Omega b d hb hd]

    /-- Addition on ℤ is associative -/
    theorem addZ_assoc (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (hz : z ∈ (IntSet : U)) :
        addZ (addZ x y) z = addZ x (addZ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := intClass_exists z hz
      subst hx_eq; subst hy_eq; subst hz_eq
      rw [addZ_class a b c d ha hb hc hd]
      rw [addZ_class (add a c) (add b d) e f
          (add_in_Omega a c ha hc) (add_in_Omega b d hb hd) he hf]
      rw [addZ_class c d e f hc hd he hf]
      rw [addZ_class a b (add c e) (add d f) ha hb
          (add_in_Omega c e hc he) (add_in_Omega d f hd hf)]
      rw [← add_assoc_Omega a c e ha hc he, ← add_assoc_Omega b d f hb hd hf]

    /-- 0ℤ is a right identity for addition -/
    theorem addZ_zero_right (x : U) (hx : x ∈ (IntSet : U)) :
        addZ x zeroZ = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      unfold zeroZ
      rw [addZ_class a b ∅ ∅ ha hb zero_in_Omega zero_in_Omega]
      rw [add_zero a ha, add_zero b hb]

    /-- 0ℤ is a left identity for addition -/
    theorem addZ_zero_left (x : U) (hx : x ∈ (IntSet : U)) :
        addZ zeroZ x = x := by
      rw [addZ_comm zeroZ x zeroZ_mem_IntSet hx]
      exact addZ_zero_right x hx

  end Int.Add

end ZFC

export ZFC.Int.Add (
  addZ
  addZ_graph_is_function
  addZ_well_defined
  addZ_class
  addZ_in_IntSet
  addZ_comm
  addZ_assoc
  addZ_zero_right
  addZ_zero_left
)
