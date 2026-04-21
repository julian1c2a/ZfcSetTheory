/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Equivalence Relation on ω × ω

  This module defines the equivalence relation on ω × ω used to construct
  the integers ℤ as a quotient set. Two pairs (a, b) and (c, d) are equivalent
  iff a + d = b + c, representing the intended integer a - b = c - d.

  ## Main Definitions

  * `IntEquivRel` — the relation {⟨⟨a,b⟩,⟨c,d⟩⟩ ∈ (ω×ω)×(ω×ω) | a+d = b+c}

  ## Main Theorems

  * `IntEquivRel_is_relation` — IntEquivRel ⊆ (ω×ω) × (ω×ω)
  * `IntEquivRel_refl` — reflexivity
  * `IntEquivRel_symm` — symmetry
  * `IntEquivRel_trans` — transitivity (uses additive cancellation on ω)
  * `IntEquivRel_is_equivalence` — IntEquivRel is an equivalence on ω × ω
-/

import ZFC.SetOps.Relations
import ZFC.SetOps.Functions
import ZFC.SetOps.CartesianProduct
import ZFC.SetOps.OrderedPair
import ZFC.Nat.Add

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

  universe u
  variable {U : Type u}

  namespace Int.Equiv

    /-! ### The Integer Equivalence Relation -/

    /-- The equivalence relation on ω × ω for constructing integers:
        (a, b) ~ (c, d) iff a + d = b + c (representing a - b = c - d) -/
    noncomputable def IntEquivRel : U :=
      sep (((ω : U) ×ₛ ω) ×ₛ ((ω : U) ×ₛ ω))
        (fun p => add (fst (fst p)) (snd (snd p)) =
                  add (snd (fst p)) (fst (snd p)))

    /-! ### Membership characterization -/

    /-- Characterization of membership in IntEquivRel for ordered pairs -/
    theorem mem_IntEquivRel (a b c d : U) :
        ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∈ (IntEquivRel : U) ↔
          (a ∈ (ω : U) ∧ b ∈ (ω : U) ∧ c ∈ (ω : U) ∧ d ∈ (ω : U) ∧
           add a d = add b c) := by
      unfold IntEquivRel
      rw [mem_sep_iff]
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      constructor
      · intro h
        have h_prod := h.1
        have h_eq := h.2
        rw [OrderedPair_mem_CartesianProduct] at h_prod
        have hab := h_prod.1
        have hcd := h_prod.2
        rw [OrderedPair_mem_CartesianProduct] at hab hcd
        exact ⟨hab.1, hab.2, hcd.1, hcd.2, h_eq⟩
      · intro h
        obtain ⟨ha, hb, hc, hd, h_eq⟩ := h
        exact ⟨(OrderedPair_mem_CartesianProduct _ _ _ _).mpr
          ⟨(OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩,
           (OrderedPair_mem_CartesianProduct c d ω ω).mpr ⟨hc, hd⟩⟩, h_eq⟩

    /-! ### IntEquivRel is a relation on ω × ω -/

    /-- IntEquivRel is a relation on ω × ω -/
    theorem IntEquivRel_is_relation :
        isRelationOn (IntEquivRel : U) ((ω : U) ×ₛ ω) := by
      intro p hp
      unfold IntEquivRel at hp
      rw [mem_sep_iff] at hp
      exact hp.1

    /-! ### Reflexivity -/

    /-- IntEquivRel is reflexive on ω × ω:
        for all (a, b) ∈ ω × ω, (a, b) ~ (a, b) since a + b = b + a -/
    theorem IntEquivRel_refl :
        isReflexiveOn (IntEquivRel : U) ((ω : U) ×ₛ ω) := by
      intro x hx
      rw [CartesianProduct_is_specified] at hx
      obtain ⟨hx_pair, h_fst, h_snd⟩ := hx
      -- x = ⟨fst x, snd x⟩, need ⟨x, x⟩ ∈ IntEquivRel
      -- Goal: ⟨x, x⟩ ∈ IntEquivRel
      -- After unfolding, need: add (fst x) (snd x) = add (snd x) (fst x)
      unfold IntEquivRel
      rw [mem_sep_iff]
      constructor
      · rw [OrderedPair_mem_CartesianProduct]
        constructor <;> (rw [CartesianProduct_is_specified]; exact ⟨hx_pair, h_fst, h_snd⟩)
      · simp only [fst_of_ordered_pair, snd_of_ordered_pair]
        exact add_comm_Omega (fst x) (snd x) h_fst h_snd

    /-! ### Symmetry -/

    /-- IntEquivRel is symmetric on ω × ω:
        if a + d = b + c then c + b = d + a -/
    theorem IntEquivRel_symm :
        isSymmetricOn (IntEquivRel : U) ((ω : U) ×ₛ ω) := by
      intro x y hx hy hxy
      have hx_mem := hx
      have hy_mem := hy
      rw [CartesianProduct_is_specified] at hx hy
      unfold IntEquivRel at hxy ⊢
      rw [mem_sep_iff] at hxy ⊢
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hxy ⊢
      constructor
      · rw [OrderedPair_mem_CartesianProduct]
        exact ⟨hy_mem, hx_mem⟩
      · -- Need: add (fst y) (snd x) = add (snd y) (fst x)
        -- Have: add (fst x) (snd y) = add (snd x) (fst y)
        rw [add_comm_Omega (fst y) (snd x) hy.2.1 hx.2.2,
            add_comm_Omega (snd y) (fst x) hy.2.2 hx.2.1]
        exact hxy.2.symm

    /-! ### Transitivity -/

    /-- IntEquivRel is transitive on ω × ω:
        if a + d = b + c and c + f = d + e then a + f = b + e.
        Proof uses additive cancellation: from a+d = b+c and c+f = d+e,
        we get (a+f)+d = (b+e)+d by rearrangement, then cancel d. -/
    theorem IntEquivRel_trans :
        isTransitiveOn (IntEquivRel : U) ((ω : U) ×ₛ ω) := by
      intro x y z hx hy hz hxy hyz
      have hx_mem := hx
      have hz_mem := hz
      rw [CartesianProduct_is_specified] at hx hy hz
      obtain ⟨_, ha, hb⟩ := hx
      obtain ⟨_, hc, hd⟩ := hy
      obtain ⟨_, he, hf⟩ := hz
      unfold IntEquivRel at hxy hyz ⊢
      rw [mem_sep_iff] at hxy hyz ⊢
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at hxy hyz ⊢
      constructor
      · rw [OrderedPair_mem_CartesianProduct]
        exact ⟨hx_mem, hz_mem⟩
      · -- h1 : add (fst x) (snd y) = add (snd x) (fst y)
        -- h2 : add (fst y) (snd z) = add (snd y) (fst z)
        -- Goal: add (fst x) (snd z) = add (snd x) (fst z)
        -- a=fst x, b=snd x, c=fst y, d=snd y, e=fst z, f=snd z
        -- h1: a+d = b+c, h2: c+f = d+e, Goal: a+f = b+e
        have h1 := hxy.2
        have h2 := hyz.2
        -- Step 1: (a+d)+f = (b+c)+f
        have step : add (add (fst x) (snd y)) (snd z) =
                    add (add (snd x) (fst y)) (snd z) := by rw [h1]
        -- Step 2: reassociate → a+(d+f) = b+(c+f)
        rw [← add_assoc_Omega (fst x) (snd y) (snd z) ha hd hf] at step
        rw [← add_assoc_Omega (snd x) (fst y) (snd z) hb hc hf] at step
        -- Step 3: use h2 (c+f = d+e) → a+(d+f) = b+(d+e)
        rw [h2] at step
        -- Step 4: comm inner adds → a+(f+d) = b+(e+d)
        rw [add_comm_Omega (snd y) (snd z) hd hf] at step
        rw [add_comm_Omega (snd y) (fst z) hd he] at step
        -- Step 5: reassociate → (a+f)+d = (b+e)+d
        rw [add_assoc_Omega (fst x) (snd z) (snd y) ha hf hd] at step
        rw [add_assoc_Omega (snd x) (fst z) (snd y) hb he hd] at step
        -- Step 6: cancel d (= snd y)
        exact add_right_cancel_Omega (snd y) (add (fst x) (snd z)) (add (snd x) (fst z))
          hd (add_in_Omega (fst x) (snd z) ha hf) (add_in_Omega (snd x) (fst z) hb he) step

    /-! ### Equivalence -/

    /-- IntEquivRel is an equivalence relation on ω × ω -/
    theorem IntEquivRel_is_equivalence :
        isEquivalenceOn (IntEquivRel : U) ((ω : U) ×ₛ ω) :=
      ⟨IntEquivRel_is_relation,
       IntEquivRel_refl,
       IntEquivRel_symm,
       IntEquivRel_trans⟩

  end Int.Equiv

end ZFC

export ZFC.Int.Equiv (
  IntEquivRel
  mem_IntEquivRel
  IntEquivRel_is_relation
  IntEquivRel_refl
  IntEquivRel_symm
  IntEquivRel_trans
  IntEquivRel_is_equivalence
)
