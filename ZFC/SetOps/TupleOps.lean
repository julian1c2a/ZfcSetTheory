/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

REFERENCE.md: Este archivo está proyectado en REFERENCE.md. Al modificar, actualizar
las secciones correspondientes.
-/

import ZFC.SetOps.Tuple
import ZFC.Nat.Add
import ZFC.Nat.Sub

/-!
# Tuple Operations

This file defines standard operations on tuples:

* `tupleHead t` — first element t⦅0⦆
* `tupleLast t n` — last element t⦅n⦆
* `constTuple n a Ω` — constant tuple (every index maps to a)
* `tupleUpdate t n Ω i v` — tuple with one index overwritten
* `tupleTail t n Ω` — drop the first element (domain shrinks from σ n to σ(n−1))
* `concat t₁ n₁ t₂ n₂ Ω` — concatenate two tuples (domain σ(n₁ + σ n₂))

Each operation includes an `IsTuple` theorem.
-/

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Nat.Add
  open ZFC.Nat.Sub
  open ZFC.Axiom.Infinity
  universe u
  variable {U : Type u}

  namespace SetOps.TupleOps

    /-! ============================================================ -/
    /-! ### PRIVATE HELPERS ### -/
    /-! ============================================================ -/

    /-- i ∈ n → σ i ∈ σ n, for natural numbers.
        Avoids Peano.Import dependency by direct argument. -/
    private theorem mem_succ_of_lt' (i n : U) (hi : IsNat i) (hn : IsNat n) (h : i ∈ n) :
        σ i ∈ σ n := by
      rw [mem_succ_iff]
      exact nat_subset_mem_or_eq (σ i) n (isNat_succ i hi) hn
        (no_nat_between i n hi hn h)

    /-- σ (predecessor n) = n for any non-zero n ∈ ω. -/
    private theorem succ_predecessor_eq (n : U) (hn : n ∈ (ω : U)) (hne : n ≠ ∅) :
        σ (predecessor n) = n := by
      have := succ_predecessorPos n (mem_Omega_is_Nat n hn) hne
      rwa [predecessorPos_eq_predecessor] at this

    /-- predecessor n ∈ ω for any non-zero n ∈ ω. -/
    private theorem predecessor_mem_omega (n : U) (hn : n ∈ (ω : U)) (hne : n ≠ ∅) :
        predecessor n ∈ (ω : U) := by
      rw [← predecessorPos_eq_predecessor n hne]
      exact Nat_in_Omega _ (predecessorPos_is_nat n (mem_Omega_is_Nat n hn) hne)

    /-- If j ∈ σ n₁ then j ∈ σ (add n₁ (σ n₂)): the first tuple's domain embeds
        into the concatenated domain. -/
    private theorem mem_sigma_n1_implies_mem_sigma_add (j n₁ n₂ : U)
        (hn₁ : n₁ ∈ (ω : U)) (hn₂ : n₂ ∈ (ω : U))
        (hj : j ∈ σ n₁) : j ∈ σ (add n₁ (σ n₂)) := by
      have hadd_omega := add_in_Omega n₁ (σ n₂) hn₁ (succ_in_Omega n₂ hn₂)
      have hn₁_lt_add : n₁ ∈ add n₁ (σ n₂) :=
        add_pos_left_Omega (σ n₂) n₁ (succ_in_Omega n₂ hn₂) hn₁ (succ_nonempty n₂)
      rw [mem_succ_iff] at hj
      apply mem_succ_of_mem
      rcases hj with hj | hj
      · exact mem_trans j n₁ (add n₁ (σ n₂))
          (nat_element_is_nat n₁ j (mem_Omega_is_Nat n₁ hn₁) hj)
          (mem_Omega_is_Nat n₁ hn₁)
          (mem_Omega_is_Nat _ hadd_omega)
          hj hn₁_lt_add
      · exact hj ▸ hn₁_lt_add

    /-- If j ∈ σ (add n₁ (σ n₂)) and j ∉ σ n₁, then sub j (σ n₁) ∈ σ n₂.
        This is the key arithmetic lemma for concat_isTuple. -/
    private theorem sub_mem_sigma_of_not_in_sigma (j n₁ n₂ : U)
        (hn₁ : n₁ ∈ (ω : U)) (hn₂ : n₂ ∈ (ω : U))
        (hj_dom : j ∈ σ (add n₁ (σ n₂)))
        (hnot : j ∉ σ n₁) : sub j (σ n₁) ∈ σ n₂ := by
      have hσn₁ := succ_in_Omega n₁ hn₁
      have hσn₂ := succ_in_Omega n₂ hn₂
      have hadd_omega := add_in_Omega n₁ (σ n₂) hn₁ hσn₂
      -- Step 1: j ∈ ω
      have hj_omega : j ∈ (ω : U) := by
        rw [mem_succ_iff] at hj_dom
        rcases hj_dom with hj | hj
        · exact Omega_is_transitive (add n₁ (σ n₂)) hadd_omega j hj
        · exact hj ▸ hadd_omega
      -- Step 2: j ∉ n₁ and j ≠ n₁ (from hnot and mem_succ_iff)
      have hnot' : ¬(j ∈ n₁ ∨ j = n₁) := by rwa [← mem_succ_iff]
      have hj_not_n₁ : j ∉ n₁ := fun h => hnot' (Or.inl h)
      have hj_ne_n₁ : j ≠ n₁ := fun h => hnot' (Or.inr h)
      -- Step 3: n₁ ∈ j by trichotomy
      have hn₁_nat := mem_Omega_is_Nat n₁ hn₁
      have hj_nat := mem_Omega_is_Nat j hj_omega
      have hn₁_lt_j : n₁ ∈ j := by
        rcases trichotomy j n₁ hj_nat hn₁_nat with h | h | h
        · exact absurd h hj_not_n₁
        · exact absurd h hj_ne_n₁
        · exact h
      -- Step 4: σ n₁ ≤ j (i.e., σ n₁ ∈ j ∨ σ n₁ = j)
      have hσn₁_le_j : σ n₁ ∈ j ∨ σ n₁ = j :=
        nat_subset_mem_or_eq (σ n₁) j (isNat_succ n₁ hn₁_nat) hj_nat
          (no_nat_between n₁ j hn₁_nat hj_nat hn₁_lt_j)
      -- Step 5: add (sub j (σ n₁)) (σ n₁) = j
      have h_sub_omega := sub_in_Omega j (σ n₁) hj_omega hσn₁
      have h_cancel : add (sub j (σ n₁)) (σ n₁) = j :=
        add_k_sub_k_Omega j (σ n₁) hj_omega hσn₁ hσn₁_le_j
      -- Step 6: sub j (σ n₁) ∈ σ n₂ — prove by trichotomy, contradiction in the > case
      have h_sub_nat := mem_Omega_is_Nat _ h_sub_omega
      have hn₂_nat := mem_Omega_is_Nat n₂ hn₂
      rw [mem_succ_iff]
      rcases trichotomy (sub j (σ n₁)) n₂ h_sub_nat hn₂_nat with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · -- n₂ ∈ sub j (σ n₁): derive contradiction
        exfalso
        -- add (σ n₁) n₂ ∈ add (σ n₁) (sub j (σ n₁)) by strict monotonicity
        have h_add_lt : add (σ n₁) n₂ ∈ add (σ n₁) (sub j (σ n₁)) :=
          add_lt_of_lt_Omega (σ n₁) n₂ (sub j (σ n₁)) hσn₁ hn₂ h_sub_omega h
        -- add (σ n₁) (sub j (σ n₁)) = j by commutativity + cancellation
        have h_comm : add (σ n₁) (sub j (σ n₁)) = j := by
          rw [add_comm_Omega _ _ hσn₁ h_sub_omega]; exact h_cancel
        rw [h_comm] at h_add_lt
        -- add n₁ (σ n₂) = add (σ n₁) n₂
        have h_add_eq : add n₁ (σ n₂) = add (σ n₁) n₂ :=
          (add_succ n₁ n₂ hn₁ hn₂).trans (succ_add_Omega n₁ n₂ hn₁ hn₂).symm
        rw [h_add_eq] at hj_dom
        rw [mem_succ_iff] at hj_dom
        rcases hj_dom with hj_case | hj_case
        · -- j ∈ add (σ n₁) n₂ and add (σ n₁) n₂ ∈ j: contradiction
          exact not_mem_of_mem (add (σ n₁) n₂) j
            (mem_Omega_is_Nat _ (add_in_Omega (σ n₁) n₂ hσn₁ hn₂))
            hj_nat ⟨h_add_lt, hj_case⟩
        · -- j = add (σ n₁) n₂, so add (σ n₁) n₂ ∈ add (σ n₁) n₂: contradiction
          rw [hj_case] at h_add_lt
          exact not_mem_self (add (σ n₁) n₂)
            (mem_Omega_is_Nat _ (add_in_Omega (σ n₁) n₂ hσn₁ hn₂))
            h_add_lt

    /-! ============================================================ -/
    /-! ### DEFINITIONS ### -/
    /-! ============================================================ -/

    /-- First element of a tuple (index 0). -/
    noncomputable def tupleHead (t : U) : U := t⦅∅⦆

    /-- Last element of an n-tuple (index n). -/
    noncomputable def tupleLast (t n : U) : U := t⦅n⦆

    /-- Constant tuple: every index in σ n maps to a. -/
    noncomputable def constTuple (n a Ω : U) : U :=
      tupleGraph n Ω (fun _ => a)

    /-- Update tuple t at index i with value v. -/
    noncomputable def tupleUpdate (t n Ω i v : U) : U :=
      tupleGraph n Ω (fun j => if j = i then v else t⦅j⦆)

    /-- Tail of a tuple: drop index 0 and shift remaining indices down by 1.
        Requires n ≠ ∅ so that predecessor n is a valid degree. -/
    noncomputable def tupleTail (t n Ω : U) : U :=
      tupleGraph (predecessor n) Ω (fun i => t⦅σ i⦆)

    /-- Concatenate t₁ (degree n₁) with t₂ (degree n₂).
        Result has degree add n₁ (σ n₂): indices 0..n₁ come from t₁,
        indices n₁+1..n₁+n₂+1 come from t₂ (shifted by σ n₁). -/
    noncomputable def concat (t₁ n₁ t₂ n₂ Ω : U) : U :=
      tupleGraph (add n₁ (σ n₂)) Ω
        (fun j => if j ∈ σ n₁ then t₁⦅j⦆ else t₂⦅sub j (σ n₁)⦆)

    /-! ============================================================ -/
    /-! ### IsTuple THEOREMS ### -/
    /-! ============================================================ -/

    theorem constTuple_isTuple (n a Ω : U) (hn : n ∈ (ω : U)) (ha : a ∈ Ω) :
        IsTuple (constTuple n a Ω) n Ω := by
      unfold constTuple
      exact tupleGraph_isTuple n Ω (fun _ => a) hn (fun _ _ => ha)

    theorem tupleUpdate_isTuple (t n Ω i v : U)
        (ht : IsTuple t n Ω) (hv : v ∈ Ω) :
        IsTuple (tupleUpdate t n Ω i v) n Ω := by
      unfold tupleUpdate
      apply tupleGraph_isTuple n Ω _ ht.1
      intro j hj
      rcases Classical.em (j = i) with h | h
      · rw [if_pos h]; exact hv
      · rw [if_neg h]; exact tuple_apply_mem t n Ω j ht hj

    theorem tupleTail_isTuple (t n Ω : U)
        (ht : IsTuple t n Ω) (hne : n ≠ ∅) :
        IsTuple (tupleTail t n Ω) (predecessor n) Ω := by
      unfold tupleTail
      have hn_omega := ht.1
      have hn_nat := mem_Omega_is_Nat n hn_omega
      have hpred_omega := predecessor_mem_omega n hn_omega hne
      have h_succ_pred := succ_predecessor_eq n hn_omega hne
      apply tupleGraph_isTuple (predecessor n) Ω _ hpred_omega
      intro i hi
      rw [h_succ_pred] at hi
      have hi_nat := nat_element_is_nat n i hn_nat hi
      exact tuple_apply_mem t n Ω (σ i) ht
        (mem_succ_of_lt' i n hi_nat hn_nat hi)

    theorem concat_isTuple (t₁ n₁ t₂ n₂ Ω : U)
        (hn₁ : n₁ ∈ (ω : U)) (hn₂ : n₂ ∈ (ω : U))
        (ht₁ : IsTuple t₁ n₁ Ω) (ht₂ : IsTuple t₂ n₂ Ω) :
        IsTuple (concat t₁ n₁ t₂ n₂ Ω) (add n₁ (σ n₂)) Ω := by
      unfold concat
      apply tupleGraph_isTuple _ Ω _
        (add_in_Omega n₁ (σ n₂) hn₁ (succ_in_Omega n₂ hn₂))
      intro j hj_dom
      rcases Classical.em (j ∈ σ n₁) with h | h
      · rw [if_pos h]
        exact tuple_apply_mem t₁ n₁ Ω j ht₁ h
      · rw [if_neg h]
        exact tuple_apply_mem t₂ n₂ Ω (sub j (σ n₁)) ht₂
          (sub_mem_sigma_of_not_in_sigma j n₁ n₂ hn₁ hn₂ hj_dom h)

    /-! ============================================================ -/
    /-! ### APPLY THEOREMS ### -/
    /-! ============================================================ -/

    /-- Applying a constant tuple always returns a. -/
    theorem constTuple_apply (n a Ω i : U)
        (hn : n ∈ (ω : U)) (hi : i ∈ σ n) (ha : a ∈ Ω) :
        (constTuple n a Ω)⦅i⦆ = a := by
      unfold constTuple
      exact tupleGraph_apply n Ω (fun _ => a) hn i hi (fun _ _ => ha)

    /-- Applying a tupleUpdate at the updated index returns the new value. -/
    theorem tupleUpdate_apply_eq (t n Ω i v : U)
        (ht : IsTuple t n Ω) (hi : i ∈ σ n) (hv : v ∈ Ω) :
        (tupleUpdate t n Ω i v)⦅i⦆ = v := by
      unfold tupleUpdate
      have hvals : ∀ k, k ∈ σ n → (if k = i then v else t⦅k⦆) ∈ Ω := fun k hk => by
        rcases Classical.em (k = i) with h | h
        · rw [if_pos h]; exact hv
        · rw [if_neg h]; exact tuple_apply_mem t n Ω k ht hk
      rw [tupleGraph_apply n Ω (fun k => if k = i then v else t⦅k⦆) ht.1 i hi hvals]
      exact if_pos rfl

    /-- Applying a tupleUpdate at a different index returns the original value. -/
    theorem tupleUpdate_apply_ne (t n Ω i v j : U)
        (ht : IsTuple t n Ω) (hj : j ∈ σ n) (hv : v ∈ Ω) (hne : j ≠ i) :
        (tupleUpdate t n Ω i v)⦅j⦆ = t⦅j⦆ := by
      unfold tupleUpdate
      have hvals : ∀ k, k ∈ σ n → (if k = i then v else t⦅k⦆) ∈ Ω := fun k hk => by
        rcases Classical.em (k = i) with h | h
        · rw [if_pos h]; exact hv
        · rw [if_neg h]; exact tuple_apply_mem t n Ω k ht hk
      rw [tupleGraph_apply n Ω (fun k => if k = i then v else t⦅k⦆) ht.1 j hj hvals,
          if_neg hne]

    /-- Applying tupleTail at index i returns t⦅σ i⦆. -/
    theorem tupleTail_apply (t n Ω i : U)
        (ht : IsTuple t n Ω) (hne : n ≠ ∅) (hi : i ∈ σ (predecessor n)) :
        (tupleTail t n Ω)⦅i⦆ = t⦅σ i⦆ := by
      unfold tupleTail
      have hn_omega := ht.1
      have hn_nat := mem_Omega_is_Nat n hn_omega
      have hpred_omega := predecessor_mem_omega n hn_omega hne
      have h_succ_pred := succ_predecessor_eq n hn_omega hne
      exact tupleGraph_apply (predecessor n) Ω (fun j => t⦅σ j⦆) hpred_omega i hi
        (fun j hj => by
          rw [h_succ_pred] at hj
          exact tuple_apply_mem t n Ω (σ j) ht
            (mem_succ_of_lt' j n (nat_element_is_nat n j hn_nat hj) hn_nat hj))

    /-- Applying concat at an index from the left segment returns t₁⦅j⦆. -/
    theorem concat_apply_left (t₁ n₁ t₂ n₂ Ω j : U)
        (hn₁ : n₁ ∈ (ω : U)) (hn₂ : n₂ ∈ (ω : U))
        (ht₁ : IsTuple t₁ n₁ Ω) (ht₂ : IsTuple t₂ n₂ Ω)
        (hj : j ∈ σ n₁) :
        (concat t₁ n₁ t₂ n₂ Ω)⦅j⦆ = t₁⦅j⦆ := by
      unfold concat
      have hadd : add n₁ (σ n₂) ∈ (ω : U) :=
        add_in_Omega n₁ (σ n₂) hn₁ (succ_in_Omega n₂ hn₂)
      have hj_dom : j ∈ σ (add n₁ (σ n₂)) :=
        mem_sigma_n1_implies_mem_sigma_add j n₁ n₂ hn₁ hn₂ hj
      have hvals : ∀ k, k ∈ σ (add n₁ (σ n₂)) →
          (if k ∈ σ n₁ then t₁⦅k⦆ else t₂⦅sub k (σ n₁)⦆) ∈ Ω := fun k hk => by
        rcases Classical.em (k ∈ σ n₁) with h | h
        · rw [if_pos h]; exact tuple_apply_mem t₁ n₁ Ω k ht₁ h
        · rw [if_neg h]; exact tuple_apply_mem t₂ n₂ Ω _ ht₂
            (sub_mem_sigma_of_not_in_sigma k n₁ n₂ hn₁ hn₂ hk h)
      rw [tupleGraph_apply (add n₁ (σ n₂)) Ω _ hadd j hj_dom hvals, if_pos hj]

    /-- Applying concat at an index from the right segment returns t₂⦅sub j (σ n₁)⦆. -/
    theorem concat_apply_right (t₁ n₁ t₂ n₂ Ω j : U)
        (hn₁ : n₁ ∈ (ω : U)) (hn₂ : n₂ ∈ (ω : U))
        (ht₁ : IsTuple t₁ n₁ Ω) (ht₂ : IsTuple t₂ n₂ Ω)
        (hj_dom : j ∈ σ (add n₁ (σ n₂))) (hj_not : j ∉ σ n₁) :
        (concat t₁ n₁ t₂ n₂ Ω)⦅j⦆ = t₂⦅sub j (σ n₁)⦆ := by
      unfold concat
      have hadd : add n₁ (σ n₂) ∈ (ω : U) :=
        add_in_Omega n₁ (σ n₂) hn₁ (succ_in_Omega n₂ hn₂)
      have hvals : ∀ k, k ∈ σ (add n₁ (σ n₂)) →
          (if k ∈ σ n₁ then t₁⦅k⦆ else t₂⦅sub k (σ n₁)⦆) ∈ Ω := fun k hk => by
        rcases Classical.em (k ∈ σ n₁) with h | h
        · rw [if_pos h]; exact tuple_apply_mem t₁ n₁ Ω k ht₁ h
        · rw [if_neg h]; exact tuple_apply_mem t₂ n₂ Ω _ ht₂
            (sub_mem_sigma_of_not_in_sigma k n₁ n₂ hn₁ hn₂ hk h)
      rw [tupleGraph_apply (add n₁ (σ n₂)) Ω _ hadd j hj_dom hvals, if_neg hj_not]

  end SetOps.TupleOps

  export SetOps.TupleOps (
    tupleHead
    tupleLast
    constTuple
    constTuple_isTuple
    constTuple_apply
    tupleUpdate
    tupleUpdate_isTuple
    tupleUpdate_apply_eq
    tupleUpdate_apply_ne
    tupleTail
    tupleTail_isTuple
    tupleTail_apply
    concat
    concat_isTuple
    concat_apply_left
    concat_apply_right
  )

end ZFC
