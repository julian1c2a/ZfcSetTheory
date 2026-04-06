/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Order

  This module defines the order relations on ℤ = QuotientSet (ω × ω) IntEquivRel
  and proves basic properties.

  ## Approach

  For integers represented as equivalence classes [(a,b)] where a,b ∈ ω,
  the order is defined as:
    [(a,b)] ≤ [(c,d)]  ⟺  a + d ≤ b + c  in ω  (i.e. add a d ∈ add b c ∨ add a d = add b c)
    [(a,b)] < [(c,d)]  ⟺  a + d < b + c  in ω  (i.e. add a d ∈ add b c)

  ## Main Definitions

  * `leZ` — non-strict order on ℤ: leZ x y
  * `ltZ` — strict order on ℤ: ltZ x y
  * `isPositiveZ` — x is positive: ltZ zeroZ x
  * `isNegativeZ` — x is negative: ltZ x zeroZ

  ## Main Theorems

  * `leZ_well_defined` — order is independent of representative choice
  * `leZ_refl` — reflexivity: x ≤ x
  * `leZ_trans` — transitivity: x ≤ y → y ≤ z → x ≤ z
  * `leZ_antisymm` — antisymmetry: x ≤ y → y ≤ x → x = y
  * `leZ_total` — totality: x ≤ y ∨ y ≤ x
  * `ltZ_iff_leZ_and_ne` — x < y ↔ x ≤ y ∧ x ≠ y
  * `addZ_leZ_addZ` — right-compatibility with addition
  * `addZ_leZ_addZ_left` — left-compatibility with addition
  * `leZ_negZ` — x ≤ y → negZ y ≤ negZ x
  * `int_trichotomy_order` — every integer is positive, zero, or negative
  * `mulZ_le_mulZ_nonneg` — multiplication by non-negative preserves order
  * `positiveZ_mul_closed` — positive × positive = positive
  * `negativeZ_mul_positive` — negative × negative = positive
  * `positiveZ_negativeZ_mul_negative` — positive × negative = negative
-/

import ZfcSetTheory.Int.Mul
import ZfcSetTheory.Int.Sub
import ZfcSetTheory.Int.Ring
import ZfcSetTheory.Nat.Mul

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
  open ZFC.Nat.Mul
  open ZFC.Int.Equiv
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Neg
  open ZFC.Int.Mul

  universe u
  variable {U : Type u}

  namespace Int.Order

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

    /-! ### Auxiliary: four-variable rearrangement -/

    /-- (a+b) + (c+d) = (a+c) + (b+d) for natural numbers.
        Rearranges terms in a sum of four naturals. -/
    private theorem add_add_comm (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U)) :
        add (add a b) (add c d) = add (add a c) (add b d) := by
      -- (a+b)+(c+d) = a+(b+(c+d)) by ← assoc
      rw [← add_assoc_Omega a b (add c d) ha hb (add_in_Omega c d hc hd)]
      -- = a+((b+c)+d) by assoc on b,c,d
      rw [add_assoc_Omega b c d hb hc hd]
      -- = a+((c+b)+d) by comm on b,c
      rw [add_comm_Omega b c hb hc]
      -- = a+(c+(b+d)) by ← assoc on c,b,d
      rw [← add_assoc_Omega c b d hc hb hd]
      -- = (a+c)+(b+d) by assoc on a,c,(b+d)
      rw [add_assoc_Omega a c (add b d) ha hc (add_in_Omega b d hb hd)]

    /-! ### Order definitions -/

    /-- Non-strict order on ℤ at the representative level:
        [(a,b)] ≤ [(c,d)] iff a + d ≤ b + c in ω (i.e. add a d ∈ add b c ∨ add a d = add b c) -/
    def leZ_repr (a b c d : U) : Prop :=
      add a d ∈ add b c ∨ add a d = add b c

    /-- Strict order on ℤ at the representative level:
        [(a,b)] < [(c,d)] iff a + d < b + c in ω (i.e. add a d ∈ add b c) -/
    def ltZ_repr (a b c d : U) : Prop :=
      add a d ∈ add b c

    /-! ### Auxiliary: order transfer via cancellation -/

    /-- If add x k ≤ add y k (in ω), then x ≤ y (in ω).
        This is the key cancellation lemma for order proofs. -/
    private theorem le_cancel_right (x y k : U)
        (hx : x ∈ (ω : U)) (hy : y ∈ (ω : U)) (hk : k ∈ (ω : U))
        (h : add x k ∈ add y k ∨ add x k = add y k) :
        x ∈ y ∨ x = y := by
      have hxk := add_in_Omega x k hx hk
      have hyk := add_in_Omega y k hy hk
      have h_tri := natLt_trichotomy x y
                      (mem_Omega_is_Nat _ hx) (mem_Omega_is_Nat _ hy)
      rcases h_tri with h_lt | h_eq | h_gt
      · exact Or.inl h_lt
      · exact Or.inr h_eq
      · -- x > y: add y k ∈ add x k, contradicts h
        exfalso
        have h_gt' := add_lt_of_lt_Omega k y x hk hy hx h_gt
        rw [add_comm_Omega k y hk hy, add_comm_Omega k x hk hx] at h_gt'
        cases h with
        | inl h_mem =>
          exact natLt_asymm (mem_Omega_is_Nat _ hxk) (mem_Omega_is_Nat _ hyk)
            h_mem h_gt'
        | inr h_eq =>
          rw [h_eq] at h_gt'
          exact not_mem_self (add y k) (mem_Omega_is_Nat _ hyk) h_gt'

    /-! ### Well-definedness of leZ_repr -/

    /-- The order leZ_repr is independent of representative choice.
        If [(a₁,b₁)] = [(a₂,b₂)] and [(c₁,d₁)] = [(c₂,d₂)]
        then leZ_repr a₁ b₁ c₁ d₁ ↔ leZ_repr a₂ b₂ c₂ d₂ -/
    theorem leZ_repr_well_defined
        (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : U)
        (ha₁ : a₁ ∈ (ω : U)) (hb₁ : b₁ ∈ (ω : U))
        (ha₂ : a₂ ∈ (ω : U)) (hb₂ : b₂ ∈ (ω : U))
        (hc₁ : c₁ ∈ (ω : U)) (hd₁ : d₁ ∈ (ω : U))
        (hc₂ : c₂ ∈ (ω : U)) (hd₂ : d₂ ∈ (ω : U))
        (h₁ : intClass a₁ b₁ = intClass a₂ b₂)
        (h₂ : intClass c₁ d₁ = intClass c₂ d₂) :
        leZ_repr a₁ b₁ c₁ d₁ ↔ leZ_repr a₂ b₂ c₂ d₂ := by
      -- From h₁: add a₁ b₂ = add b₁ a₂
      rw [intClass_eq_iff a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂] at h₁
      -- From h₂: add c₁ d₂ = add d₁ c₂
      rw [intClass_eq_iff c₁ d₁ c₂ d₂ hc₁ hd₁ hc₂ hd₂] at h₂
      -- Key identities using add_add_comm:
      -- (a₁+d₁)+(b₂+d₂) = (a₁+b₂)+(d₁+d₂) = (b₁+a₂)+(d₁+d₂) = (a₂+d₂)+(b₁+d₁)
      -- (b₁+c₁)+(b₂+d₂) = (b₁+b₂)+(c₁+d₂) = (b₁+b₂)+(d₁+c₂) = (b₂+c₂)+(b₁+d₁)
      have h_bd1 := add_in_Omega b₁ d₁ hb₁ hd₁
      have h_bd2 := add_in_Omega b₂ d₂ hb₂ hd₂

      have h_lhs : add (add a₁ d₁) (add b₂ d₂) =
                   add (add a₂ d₂) (add b₁ d₁) := by
        rw [add_add_comm a₁ d₁ b₂ d₂ ha₁ hd₁ hb₂ hd₂]
        rw [h₁]
        rw [add_add_comm b₁ a₂ d₁ d₂ hb₁ ha₂ hd₁ hd₂]
        rw [add_comm_Omega (add b₁ d₁) (add a₂ d₂) h_bd1
            (add_in_Omega a₂ d₂ ha₂ hd₂)]

      have h_rhs : add (add b₁ c₁) (add b₂ d₂) =
                   add (add b₂ c₂) (add b₁ d₁) := by
        rw [add_add_comm b₁ c₁ b₂ d₂ hb₁ hc₁ hb₂ hd₂]
        rw [h₂]
        rw [add_add_comm b₁ b₂ d₁ c₂ hb₁ hb₂ hd₁ hc₂]
        rw [add_comm_Omega (add b₁ d₁) (add b₂ c₂) h_bd1
            (add_in_Omega b₂ c₂ hb₂ hc₂)]

      unfold leZ_repr
      constructor
      · -- Forward: le(a₁d₁, b₁c₁) → le(a₂d₂, b₂c₂)
        intro h_le
        have h_ad1 := add_in_Omega a₁ d₁ ha₁ hd₁
        have h_bc1 := add_in_Omega b₁ c₁ hb₁ hc₁
        have h_ad2 := add_in_Omega a₂ d₂ ha₂ hd₂
        have h_bc2 := add_in_Omega b₂ c₂ hb₂ hc₂
        cases h_le with
        | inl h_mem =>
          have h_sum := add_lt_of_lt_Omega (add b₂ d₂) (add a₁ d₁) (add b₁ c₁)
                          h_bd2 h_ad1 h_bc1 h_mem
          rw [add_comm_Omega (add b₂ d₂) (add a₁ d₁) h_bd2 h_ad1] at h_sum
          rw [add_comm_Omega (add b₂ d₂) (add b₁ c₁) h_bd2 h_bc1] at h_sum
          rw [h_lhs, h_rhs] at h_sum
          exact le_cancel_right (add a₂ d₂) (add b₂ c₂) (add b₁ d₁)
                  h_ad2 h_bc2 h_bd1 (Or.inl h_sum)
        | inr h_eq =>
          have h_sum_eq : add (add a₂ d₂) (add b₁ d₁) =
                          add (add b₂ c₂) (add b₁ d₁) := by
            rw [← h_lhs, ← h_rhs, h_eq]
          have h_ad2 := add_in_Omega a₂ d₂ ha₂ hd₂
          have h_bc2 := add_in_Omega b₂ c₂ hb₂ hc₂
          exact Or.inr (add_right_cancel_Omega (add b₁ d₁) (add a₂ d₂) (add b₂ c₂)
                  h_bd1 h_ad2 h_bc2 h_sum_eq)
      · -- Backward: le(a₂d₂, b₂c₂) → le(a₁d₁, b₁c₁)
        intro h_le
        have h_ad1 := add_in_Omega a₁ d₁ ha₁ hd₁
        have h_bc1 := add_in_Omega b₁ c₁ hb₁ hc₁
        have h_ad2 := add_in_Omega a₂ d₂ ha₂ hd₂
        have h_bc2 := add_in_Omega b₂ c₂ hb₂ hc₂
        cases h_le with
        | inl h_mem =>
          have h_sum := add_lt_of_lt_Omega (add b₁ d₁) (add a₂ d₂) (add b₂ c₂)
                          h_bd1 h_ad2 h_bc2 h_mem
          rw [add_comm_Omega (add b₁ d₁) (add a₂ d₂) h_bd1 h_ad2] at h_sum
          rw [add_comm_Omega (add b₁ d₁) (add b₂ c₂) h_bd1 h_bc2] at h_sum
          rw [← h_lhs, ← h_rhs] at h_sum
          exact le_cancel_right (add a₁ d₁) (add b₁ c₁) (add b₂ d₂)
                  h_ad1 h_bc1 h_bd2 (Or.inl h_sum)
        | inr h_eq =>
          have h_sum_eq : add (add a₁ d₁) (add b₂ d₂) =
                          add (add b₁ c₁) (add b₂ d₂) := by
            rw [h_lhs, h_rhs, h_eq]
          exact Or.inr (add_right_cancel_Omega (add b₂ d₂) (add a₁ d₁) (add b₁ c₁)
                  h_bd2 h_ad1 h_bc1 h_sum_eq)

    /-! ### Definitions on ℤ -/

    /-- Non-strict order on ℤ: leZ x y holds when for ANY representatives
        (a,b) of x and (c,d) of y, we have add a d ≤ add b c in ω. -/
    def leZ (x y : U) : Prop :=
      ∀ (a b c d : U), a ∈ (ω : U) → b ∈ (ω : U) → c ∈ (ω : U) → d ∈ (ω : U) →
        x = intClass a b → y = intClass c d → leZ_repr a b c d

    /-- Strict order on ℤ: ltZ x y iff leZ x y and x ≠ y -/
    def ltZ (x y : U) : Prop := leZ x y ∧ x ≠ y

    /-! ### Basic characterization -/

    /-- leZ holds iff it holds for SOME representatives -/
    theorem leZ_iff_repr (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ x y ↔ ∃ a b c d : U,
          a ∈ (ω : U) ∧ b ∈ (ω : U) ∧ c ∈ (ω : U) ∧ d ∈ (ω : U) ∧
          x = intClass a b ∧ y = intClass c d ∧ leZ_repr a b c d := by
      constructor
      · intro h_le
        obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
        obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
        exact ⟨a, b, c, d, ha, hb, hc, hd, hx_eq, hy_eq,
               h_le a b c d ha hb hc hd hx_eq hy_eq⟩
      · intro ⟨a, b, c, d, ha, hb, hc, hd, hx_eq, hy_eq, h_repr⟩
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have h₁ : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
        have h₂ : intClass c d = intClass c' d' := by rw [← hy_eq, hy_eq']
        exact (leZ_repr_well_defined a b a' b' c d c' d'
               ha hb ha' hb' hc hd hc' hd' h₁ h₂).mp h_repr

    /-! ### Reflexivity -/

    /-- leZ is reflexive: x ≤ x -/
    theorem leZ_refl (x : U) (_hx : x ∈ (IntSet : U)) : leZ x x := by
      intro a b a' b' ha hb ha' hb' hx_eq hx_eq'
      have h_eq : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
      rw [intClass_eq_iff a b a' b' ha hb ha' hb'] at h_eq
      unfold leZ_repr
      exact Or.inr h_eq

    /-! ### Transitivity -/

    /-- leZ is transitive: x ≤ y → y ≤ z → x ≤ z -/
    theorem leZ_trans (x y z : U)
        (_hx : x ∈ (IntSet : U)) (_hy : y ∈ (IntSet : U)) (_hz : z ∈ (IntSet : U))
        (h₁ : leZ x y) (h₂ : leZ y z) : leZ x z := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x _hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y _hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := intClass_exists z _hz
      intro a' b' e' f' ha' hb' he' hf' hx_eq' hz_eq'
      have h_le1 := h₁ a b c d ha hb hc hd hx_eq hy_eq
      have h_le2 := h₂ c d e f hc hd he hf hy_eq hz_eq
      -- Need: leZ_repr a b e f, then use well-definedness
      have h_le_af : leZ_repr a b e f := by
        unfold leZ_repr at h_le1 h_le2 ⊢
        have had := add_in_Omega a d ha hd
        have hbc := add_in_Omega b c hb hc
        have hcf := add_in_Omega c f hc hf
        have hde := add_in_Omega d e hd he
        have haf := add_in_Omega a f ha hf
        have hbe := add_in_Omega b e hb he
        have hcd := add_in_Omega c d hc hd
        -- (a+f)+(c+d) = (a+d)+(c+f) by add_add_comm a f c d → a d c f? No.
        -- add_add_comm: (x+y)+(z+w) = (x+z)+(y+w)
        -- So (a+f)+(c+d) = (a+c)+(f+d). We need (a+d)+(c+f).
        -- Let's compute: (a+f)+(c+d) = (a+c)+(f+d) = (a+c)+(d+f)
        -- And: (a+d)+(c+f) = (a+c)+(d+f). Same!
        have h_af_cd : add (add a f) (add c d) =
                       add (add a d) (add c f) := by
          rw [add_add_comm a f c d ha hf hc hd]
          rw [add_comm_Omega f d hf hd]
          rw [← add_add_comm a d c f ha hd hc hf]
        -- (b+e)+(c+d) = (b+c)+(e+d) = (b+c)+(d+e)
        have h_be_cd : add (add b e) (add c d) =
                       add (add b c) (add d e) := by
          rw [add_add_comm b e c d hb he hc hd]
          rw [add_comm_Omega e d he hd]
        -- Now: if (a+d) ≤ (b+c) and (c+f) ≤ (d+e), then
        --   (a+d)+(c+f) ≤ (b+c)+(d+e), i.e. (a+f)+(c+d) ≤ (b+e)+(c+d)
        -- Cancel (c+d) to get (a+f) ≤ (b+e)
        cases h_le1 with
        | inl h_mem1 =>
          -- a+d ∈ b+c (strict)
          cases h_le2 with
          | inl h_mem2 =>
            -- c+f ∈ d+e (strict)
            -- (a+d)+(c+f) ∈ (a+d)+(d+e) by monotonicity
            have h1 := add_lt_of_lt_Omega (add a d) (add c f) (add d e)
                          had hcf hde h_mem2
            -- (a+d)+(d+e) ∈ (b+c)+(d+e) by monotonicity
            have h2 := add_lt_of_lt_Omega (add d e) (add a d) (add b c)
                          hde had hbc h_mem1
            rw [add_comm_Omega (add d e) (add a d) hde had] at h2
            rw [add_comm_Omega (add d e) (add b c) hde hbc] at h2
            -- Transitivity: (a+d)+(c+f) ∈ (b+c)+(d+e)
            have h_trans := natLt_trans
              (mem_Omega_is_Nat _ (add_in_Omega _ _ had hcf))
              (mem_Omega_is_Nat _ (add_in_Omega _ _ had hde))
              (mem_Omega_is_Nat _ (add_in_Omega _ _ hbc hde))
              h1 h2
            -- Rewrite using the identities
            rw [← h_af_cd] at h_trans
            rw [← h_be_cd] at h_trans
            exact le_cancel_right (add a f) (add b e) (add c d) haf hbe hcd
                    (Or.inl h_trans)
          | inr h_eq2 =>
            -- c+f = d+e
            -- (a+d)+(c+f) ∈ (b+c)+(c+f) by monotonicity (since a+d ∈ b+c)
            have h1 := add_lt_of_lt_Omega (add c f) (add a d) (add b c)
                          hcf had hbc h_mem1
            rw [add_comm_Omega (add c f) (add a d) hcf had] at h1
            rw [add_comm_Omega (add c f) (add b c) hcf hbc] at h1
            -- h1 : add (add a d) (add c f) ∈ add (add b c) (add c f)
            rw [← h_af_cd] at h1
            -- h1 : add (add a f) (add c d) ∈ add (add b c) (add c f)
            rw [h_eq2, ← h_be_cd] at h1
            exact le_cancel_right (add a f) (add b e) (add c d) haf hbe hcd
                    (Or.inl h1)
        | inr h_eq1 =>
          -- a+d = b+c
          cases h_le2 with
          | inl h_mem2 =>
            -- (a+d)+(c+f) ∈ (a+d)+(d+e) by monotonicity
            have h1 := add_lt_of_lt_Omega (add a d) (add c f) (add d e)
                          had hcf hde h_mem2
            -- h1 : add (add a d) (add c f) ∈ add (add a d) (add d e)
            -- Rewrite using identities BEFORE substituting h_eq1
            rw [← h_af_cd] at h1
            -- h1 : add (add a f) (add c d) ∈ add (add a d) (add d e)
            -- Now for the RHS: (a+d)+(d+e) = (b+c)+(d+e) by h_eq1
            -- and (b+c)+(d+e) = (b+e)+(c+d) by ← h_be_cd
            rw [h_eq1, ← h_be_cd] at h1
            exact le_cancel_right (add a f) (add b e) (add c d) haf hbe hcd
                    (Or.inl h1)
          | inr h_eq2 =>
            -- a+d = b+c and c+f = d+e → a+f = b+e
            -- (a+f)+(c+d) = (a+d)+(c+f) = (b+c)+(d+e) = (b+e)+(c+d)
            have : add (add a f) (add c d) = add (add b e) (add c d) := by
              rw [h_af_cd, h_eq1, h_eq2, h_be_cd]
            exact Or.inr (add_right_cancel_Omega (add c d) (add a f) (add b e)
                    hcd haf hbe this)
      have h_eq1 : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
      have h_eq2 : intClass e f = intClass e' f' := by rw [← hz_eq, hz_eq']
      exact (leZ_repr_well_defined a b a' b' e f e' f'
             ha hb ha' hb' he hf he' hf' h_eq1 h_eq2).mp h_le_af

    /-! ### Antisymmetry -/

    /-- leZ is antisymmetric: x ≤ y → y ≤ x → x = y -/
    theorem leZ_antisymm (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (h₁ : leZ x y) (h₂ : leZ y x) : x = y := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      have h_le1 := h₁ a b c d ha hb hc hd hx_eq hy_eq
      have h_le2 := h₂ c d a b hc hd ha hb hy_eq hx_eq
      unfold leZ_repr at h_le1 h_le2
      have had := add_in_Omega a d ha hd
      have hbc := add_in_Omega b c hb hc
      rw [add_comm_Omega c b hc hb, add_comm_Omega d a hd ha] at h_le2
      cases h_le1 with
      | inl h_mem1 =>
        cases h_le2 with
        | inl h_mem2 =>
          exfalso
          exact natLt_asymm (mem_Omega_is_Nat _ had) (mem_Omega_is_Nat _ hbc)
            h_mem1 h_mem2
        | inr h_eq2 =>
          rw [hx_eq, hy_eq, intClass_eq_iff a b c d ha hb hc hd]
          exact h_eq2.symm
      | inr h_eq1 =>
        rw [hx_eq, hy_eq, intClass_eq_iff a b c d ha hb hc hd]
        exact h_eq1

    /-! ### Totality -/

    /-- leZ is total: x ≤ y ∨ y ≤ x -/
    theorem leZ_total (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        leZ x y ∨ leZ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      have had := add_in_Omega a d ha hd
      have hbc := add_in_Omega b c hb hc
      have h_tri := natLt_trichotomy (add a d) (add b c)
                      (mem_Omega_is_Nat _ had) (mem_Omega_is_Nat _ hbc)
      rcases h_tri with h_lt | h_eq | h_gt
      · left
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have h₁ : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
        have h₂ : intClass c d = intClass c' d' := by rw [← hy_eq, hy_eq']
        exact (leZ_repr_well_defined a b a' b' c d c' d'
               ha hb ha' hb' hc hd hc' hd' h₁ h₂).mp (Or.inl h_lt)
      · left
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have h₁ : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
        have h₂ : intClass c d = intClass c' d' := by rw [← hy_eq, hy_eq']
        exact (leZ_repr_well_defined a b a' b' c d c' d'
               ha hb ha' hb' hc hd hc' hd' h₁ h₂).mp (Or.inr h_eq)
      · right
        intro c' d' a' b' hc' hd' ha' hb' hy_eq' hx_eq'
        have h₁ : intClass c d = intClass c' d' := by rw [← hy_eq, hy_eq']
        have h₂ : intClass a b = intClass a' b' := by rw [← hx_eq, hx_eq']
        have h_gt' : add c b ∈ add d a := by
          rw [add_comm_Omega c b hc hb, add_comm_Omega d a hd ha]; exact h_gt
        exact (leZ_repr_well_defined c d c' d' a b a' b'
               hc hd hc' hd' ha hb ha' hb' h₁ h₂).mp (Or.inl h_gt')

    /-! ### ltZ characterization -/

    /-- ltZ iff leZ and not equal -/
    theorem ltZ_iff_leZ_and_ne (x y : U)
        (_hx : x ∈ (IntSet : U)) (_hy : y ∈ (IntSet : U)) :
        ltZ x y ↔ leZ x y ∧ x ≠ y := by
      rfl

    theorem ltZ_irrefl (x : U) (_hx : x ∈ (IntSet : U)) : ¬ ltZ x x :=
      fun h => h.2 rfl

    theorem ltZ_trans (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_xy : ltZ x y) (h_yz : ltZ y z) : ltZ x z :=
      ⟨leZ_trans x y z hx hy hz h_xy.1 h_yz.1,
       fun h_eq => h_xy.2 (leZ_antisymm x y hx hy h_xy.1 (h_eq ▸ h_yz.1))⟩

    theorem leZ_iff_ltZ_or_eq (x y : U)
        (hx : x ∈ (IntSet : U)) (_hy : y ∈ (IntSet : U)) :
        leZ x y ↔ ltZ x y ∨ x = y :=
      ⟨fun h => by
        by_cases h_eq : x = y
        · exact Or.inr h_eq
        · exact Or.inl ⟨h, h_eq⟩,
       fun h => h.elim (fun hlt => hlt.1) (fun heq => heq ▸ leZ_refl x hx)⟩

    /-! ### Compatibility with addition -/

    /-- Order is compatible with addition: x ≤ y → addZ x z ≤ addZ y z -/
    theorem addZ_leZ_addZ (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_le : leZ x y) : leZ (addZ x z) (addZ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := intClass_exists z hz
      have h_le_repr := h_le a b c d ha hb hc hd hx_eq hy_eq
      subst hx_eq; subst hy_eq; subst hz_eq
      rw [addZ_class a b e f ha hb he hf]
      rw [addZ_class c d e f hc hd he hf]
      intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
      have h₁ : intClass (add a e) (add b f) = intClass a' b' := hx_eq'
      have h₂ : intClass (add c e) (add d f) = intClass c' d' := hy_eq'
      have hae := add_in_Omega a e ha he
      have hbf := add_in_Omega b f hb hf
      have hce := add_in_Omega c e hc he
      have hdf := add_in_Omega d f hd hf
      have h_base : leZ_repr (add a e) (add b f) (add c e) (add d f) := by
        unfold leZ_repr
        have hef := add_in_Omega e f he hf
        have had := add_in_Omega a d ha hd
        have hbc := add_in_Omega b c hb hc
        -- (a+e)+(d+f) = (a+d)+(e+f) by add_add_comm
        have h_l : add (add a e) (add d f) = add (add a d) (add e f) := by
          exact add_add_comm a e d f ha he hd hf
        -- (b+f)+(c+e) = (b+c)+(f+e) = (b+c)+(e+f) by add_add_comm + comm
        have h_r : add (add b f) (add c e) = add (add b c) (add e f) := by
          rw [add_add_comm b f c e hb hf hc he]
          rw [add_comm_Omega f e hf he]
        -- So the question reduces to: (a+d)+(e+f) ≤ (b+c)+(e+f)
        -- which follows from a+d ≤ b+c by monotonicity + cancel
        rw [h_l, h_r]
        unfold leZ_repr at h_le_repr
        cases h_le_repr with
        | inl h_mem =>
          have h_mono := add_lt_of_lt_Omega (add e f) (add a d) (add b c)
                          hef had hbc h_mem
          rw [add_comm_Omega (add e f) (add a d) hef had] at h_mono
          rw [add_comm_Omega (add e f) (add b c) hef hbc] at h_mono
          exact Or.inl h_mono
        | inr h_eq =>
          exact Or.inr (congrArg (add · (add e f)) h_eq)
      exact (leZ_repr_well_defined (add a e) (add b f) a' b' (add c e) (add d f) c' d'
             hae hbf ha' hb' hce hdf hc' hd' h₁ h₂).mp h_base

    /-- Strict order is compatible with addition: x < y → addZ x z < addZ y z -/
    theorem ltZ_addZ_ltZ (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_lt : ltZ x y) : ltZ (addZ x z) (addZ y z) :=
      ⟨addZ_leZ_addZ x y z hx hy hz h_lt.1, fun h_eq =>
        have h1 : Int.Sub.subZ (addZ x z) z = Int.Sub.subZ (addZ y z) z := by rw [h_eq]
        have h2 : Int.Sub.subZ (addZ x z) z = x := Int.Sub.subZ_addZ_cancel x z hx hz
        have h3 : Int.Sub.subZ (addZ y z) z = y := Int.Sub.subZ_addZ_cancel y z hy hz
        h_lt.2 (h2.symm.trans (h1.trans h3))⟩

    /-! ### Compatibility with negation -/

    /-- x ≤ y → negZ y ≤ negZ x -/
    theorem leZ_negZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (h_le : leZ x y) : leZ (negZ y) (negZ x) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      have h_le_repr := h_le a b c d ha hb hc hd hx_eq hy_eq
      subst hx_eq; subst hy_eq
      rw [negZ_class c d hc hd, negZ_class a b ha hb]
      intro d' c' b' a' hd' hc' hb' ha' hy_eq' hx_eq'
      have h₁ : intClass d c = intClass d' c' := hy_eq'
      have h₂ : intClass b a = intClass b' a' := hx_eq'
      have h_base : leZ_repr d c b a := by
        unfold leZ_repr at h_le_repr ⊢
        rw [add_comm_Omega d a hd ha, add_comm_Omega c b hc hb]
        exact h_le_repr
      exact (leZ_repr_well_defined d c d' c' b a b' a'
             hd hc hd' hc' hb ha hb' ha' h₁ h₂).mp h_base

    /-! ### Definitions: positivity and negativity -/

    /-- An integer is positive when it is strictly greater than zero -/
    def isPositiveZ (x : U) : Prop := ltZ (zeroZ : U) x

    /-- An integer is negative when it is strictly less than zero -/
    def isNegativeZ (x : U) : Prop := ltZ x (zeroZ : U)

    /-! ### Trichotomy via order -/

    /-- Helper: intClass n ∅ with n ≠ ∅ is positive -/
    private theorem intClass_pos_is_positive (n : U) (hn : n ∈ (ω : U)) (hn_ne : n ≠ ∅) :
        isPositiveZ (intClass n (∅ : U)) := by
      unfold isPositiveZ ltZ
      constructor
      · -- leZ zeroZ (intClass n ∅)
        unfold zeroZ
        intro a b c d ha hb hc hd h_zero h_n
        unfold leZ_repr
        have h_eq1 : intClass (∅ : U) ∅ = intClass a b := h_zero
        have h_eq2 : intClass n (∅ : U) = intClass c d := h_n
        have h_base : leZ_repr (∅ : U) ∅ n ∅ := by
          unfold leZ_repr
          rw [zero_add (∅ : U) zero_in_Omega, zero_add n hn]
          -- Need: ∅ ∈ n ∨ ∅ = n. Since n ≠ ∅ and n ∈ ω, n = σ m, so ∅ ∈ n
          have h_isNat := mem_Omega_is_Nat n hn
          rcases eq_zero_or_exists_succ n h_isNat with rfl | ⟨m, rfl⟩
          · exact absurd rfl hn_ne
          · have hm_nat := nat_element_is_nat (σ m) m h_isNat (mem_succ_self m)
            exact Or.inl (zero_in_succ_nat m (Nat_in_Omega m hm_nat))
        exact (leZ_repr_well_defined (∅ : U) ∅ a b n ∅ c d
               zero_in_Omega zero_in_Omega ha hb hn zero_in_Omega hc hd
               h_eq1 h_eq2).mp h_base
      · -- zeroZ ≠ intClass n ∅
        unfold zeroZ
        intro h_eq
        have := (intClass_eq_iff (∅ : U) ∅ n ∅ zero_in_Omega zero_in_Omega hn zero_in_Omega).mp h_eq
        -- add ∅ ∅ = add ∅ n → ∅ = n
        rw [add_zero (∅ : U) zero_in_Omega, zero_add n hn] at this
        exact hn_ne this.symm

    /-- Helper: intClass ∅ m with m ≠ ∅ is negative -/
    private theorem intClass_neg_is_negative (m : U) (hm : m ∈ (ω : U)) (hm_ne : m ≠ ∅) :
        isNegativeZ (intClass (∅ : U) m) := by
      unfold isNegativeZ ltZ
      constructor
      · -- leZ (intClass ∅ m) zeroZ
        unfold zeroZ
        intro a b c d ha hb hc hd h_neg h_zero
        unfold leZ_repr
        have h_eq1 : intClass (∅ : U) m = intClass a b := h_neg
        have h_eq2 : intClass (∅ : U) ∅ = intClass c d := h_zero
        have h_base : leZ_repr (∅ : U) m ∅ ∅ := by
          unfold leZ_repr
          rw [add_zero (∅ : U) zero_in_Omega, add_zero m hm]
          have h_isNat := mem_Omega_is_Nat m hm
          rcases eq_zero_or_exists_succ m h_isNat with rfl | ⟨k, rfl⟩
          · exact absurd rfl hm_ne
          · have hk_nat := nat_element_is_nat (σ k) k h_isNat (mem_succ_self k)
            exact Or.inl (zero_in_succ_nat k (Nat_in_Omega k hk_nat))
        exact (leZ_repr_well_defined (∅ : U) m a b (∅ : U) ∅ c d
               zero_in_Omega hm ha hb zero_in_Omega zero_in_Omega hc hd
               h_eq1 h_eq2).mp h_base
      · -- intClass ∅ m ≠ zeroZ
        unfold zeroZ
        intro h_eq
        have := (intClass_eq_iff (∅ : U) m ∅ ∅ zero_in_Omega hm zero_in_Omega zero_in_Omega).mp h_eq
        rw [add_zero (∅ : U) zero_in_Omega, add_zero m hm] at this
        exact hm_ne this.symm

    /-- Every integer is positive, zero, or negative -/
    theorem int_trichotomy_order (x : U) (hx : x ∈ (IntSet : U)) :
        isPositiveZ x ∨ x = (zeroZ : U) ∨ isNegativeZ x := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, hn_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (intClass_pos_is_positive n hn hn_ne)
      · exact Or.inr (Or.inr (intClass_neg_is_negative m hm hm_ne))

    /-! ### Left-compatibility with addition -/

    /-- Order is compatible with left-addition: x ≤ y → addZ z x ≤ addZ z y -/
    theorem addZ_leZ_addZ_left (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_le : leZ x y) : leZ (addZ z x) (addZ z y) := by
      rw [addZ_comm z x hz hx, addZ_comm z y hz hy]
      exact addZ_leZ_addZ x y z hx hy hz h_le

    /-! ### Multiplication and order -/

    /-- Bridge: multiplication monotonicity from PeanoNatLib.
        If n ≤ m in ω, then mul n k ≤ mul m k in ω. -/
    private theorem mul_le_mono_right_Omega (k n m : U)
        (hk : k ∈ (ω : U)) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U))
        (h : n ∈ m ∨ n = m) : mul n k ∈ mul m k ∨ mul n k = mul m k := by
      obtain ⟨p, rfl⟩ := fromPeano_surjective k (mem_Omega_is_Nat k hk)
      obtain ⟨q, rfl⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      obtain ⟨r, rfl⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      rw [← fromPeano_mul q p, ← fromPeano_mul r p]
      have h_le : Peano.Order.Le q r := (fromPeano_le_iff q r).mpr h
      exact (fromPeano_le_iff (Peano.Mul.mul q p) (Peano.Mul.mul r p)).mp
        (Peano.Mul.mul_le_mono_right p h_le)

    /-- Multiplication by a non-negative integer preserves order:
        x ≤ y → 0 ≤ z → mulZ z x ≤ mulZ z y -/
    theorem mulZ_le_mulZ_nonneg (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_le : leZ x y) (h_z_nonneg : leZ (zeroZ : U) z) :
        leZ (mulZ z x) (mulZ z y) := by
      -- Case split on z via trichotomy
      rcases int_trichotomy z hz with rfl | ⟨e, he, he_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
      · -- z = zeroZ
        rw [mulZ_zero_left x hx, mulZ_zero_left y hy]
        exact leZ_refl zeroZ zeroZ_mem_IntSet
      · -- z = intClass e ∅, e ∈ ω, e ≠ ∅ (positive)
        obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
        obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
        have h_le_repr := h_le a b c d ha hb hc hd hx_eq hy_eq
        subst hx_eq; subst hy_eq
        -- mulZ (intClass e ∅) (intClass a b) = intClass (mul e a) (mul e b)
        rw [mulZ_class e ∅ a b he zero_in_Omega ha hb,
            zero_mul_Omega b hb, zero_mul_Omega a ha,
            add_zero (mul e a) (mul_in_Omega e a he ha),
            add_zero (mul e b) (mul_in_Omega e b he hb)]
        -- mulZ (intClass e ∅) (intClass c d) = intClass (mul e c) (mul e d)
        rw [mulZ_class e ∅ c d he zero_in_Omega hc hd,
            zero_mul_Omega d hd, zero_mul_Omega c hc,
            add_zero (mul e c) (mul_in_Omega e c he hc),
            add_zero (mul e d) (mul_in_Omega e d he hd)]
        -- Show: leZ_repr (mul e a) (mul e b) (mul e c) (mul e d)
        intro a' b' c' d' ha' hb' hc' hd' hx_eq' hy_eq'
        have hea := mul_in_Omega e a he ha
        have heb := mul_in_Omega e b he hb
        have hec := mul_in_Omega e c he hc
        have hed := mul_in_Omega e d he hd
        have h_base : leZ_repr (mul e a) (mul e b) (mul e c) (mul e d) := by
          unfold leZ_repr
          -- Rewrite using distributivity: add (mul e a) (mul e d) = mul e (add a d)
          rw [← mul_ldistr_Omega e a d he ha hd,
              ← mul_ldistr_Omega e b c he hb hc]
          -- Use monotonicity: (add a d) ≤ (add b c) → mul e (add a d) ≤ mul e (add b c)
          -- via: mul (add a d) e ≤ mul (add b c) e, then commutativity
          have had := add_in_Omega a d ha hd
          have hbc := add_in_Omega b c hb hc
          have h_mono := mul_le_mono_right_Omega e (add a d) (add b c) he had hbc h_le_repr
          rw [mul_comm_Omega (add a d) e had he,
              mul_comm_Omega (add b c) e hbc he] at h_mono
          exact h_mono
        exact (leZ_repr_well_defined (mul e a) (mul e b) a' b' (mul e c) (mul e d) c' d'
               hea heb ha' hb' hec hed hc' hd' hx_eq' hy_eq').mp h_base
      · -- z = intClass ∅ m, m ≠ ∅ (negative): contradicts z ≥ 0
        exfalso
        have h_neg := intClass_neg_is_negative m hm hm_ne
        exact h_neg.2 (leZ_antisymm (intClass (∅ : U) m) zeroZ
          (intClass_mem_IntSet ∅ m zero_in_Omega hm) zeroZ_mem_IntSet
          h_neg.1 h_z_nonneg)

    /-- Multiplication by nonpositive flips order: leZ x y → leZ z 0 → leZ (mulZ z y) (mulZ z x) -/
    theorem mulZ_le_mulZ_nonpos (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_le : leZ x y) (hz_nonpos : leZ z zeroZ) : leZ (mulZ z y) (mulZ z x) := by
      have hz_neg : negZ z ∈ (IntSet : U) := negZ_in_IntSet z hz
      have h1 : leZ zeroZ (negZ z) := by
        have h : leZ (negZ zeroZ) (negZ z) := leZ_negZ z zeroZ hz zeroZ_mem_IntSet hz_nonpos
        rwa [negZ_zero] at h
      have h2 : leZ (mulZ (negZ z) x) (mulZ (negZ z) y) :=
        mulZ_le_mulZ_nonneg x y (negZ z) hx hy hz_neg h_le h1
      rw [mulZ_negZ_left z x hz hx] at h2
      rw [mulZ_negZ_left z y hz hy] at h2
      have h3 : leZ (negZ (negZ (mulZ z y))) (negZ (negZ (mulZ z x))) :=
        leZ_negZ _ _ (negZ_in_IntSet (mulZ z x) (mulZ_in_IntSet z x hz hx))
                 (negZ_in_IntSet (mulZ z y) (mulZ_in_IntSet z y hz hy)) h2
      rwa [negZ_negZ (mulZ z y) (mulZ_in_IntSet z y hz hy),
           negZ_negZ (mulZ z x) (mulZ_in_IntSet z x hz hx)] at h3

    /-- Strict multiplication by positive preserves strict order: ltZ x y → ltZ 0 z → ltZ (mulZ z x) (mulZ z y) -/
    theorem mulZ_ltZ_mulZ_pos (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
        (h_lt : ltZ x y) (hz_pos : ltZ zeroZ z) : ltZ (mulZ z x) (mulZ z y) := by
      have h_le : leZ (mulZ z x) (mulZ z y) :=
        mulZ_le_mulZ_nonneg x y z hx hy hz h_lt.1 hz_pos.1
      refine ⟨h_le, fun h_eq => h_lt.2 ?_⟩
      exact Int.Ring.mulZ_cancel_left x y z hx hy hz hz_pos.2.symm h_eq

    /-! ### Sign-product closure -/

    /-- Positive times positive is positive -/
    theorem positiveZ_mul_closed (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (h_px : isPositiveZ x) (h_py : isPositiveZ y) :
        isPositiveZ (mulZ x y) := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, hn_ne, rfl⟩ | ⟨n, hn, hn_ne, rfl⟩
      · -- x = zeroZ: contradicts h_px
        exact absurd rfl h_px.2
      · -- x = intClass n ∅ (positive)
        rcases int_trichotomy y hy with rfl | ⟨m, hm, hm_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
        · exact absurd rfl h_py.2
        · -- Both positive: mulZ (intClass n ∅) (intClass m ∅) = intClass (mul n m) ∅
          rw [mulZ_class n ∅ m ∅ hn zero_in_Omega hm zero_in_Omega,
              mul_zero n hn, zero_mul_Omega m hm, zero_mul_Omega ∅ zero_in_Omega,
              add_zero (mul n m) (mul_in_Omega n m hn hm),
              zero_add (∅ : U) zero_in_Omega]
          exact intClass_pos_is_positive (mul n m) (mul_in_Omega n m hn hm)
            (fun h => by
              rcases (mul_eq_zero_iff n m hn hm).mp h with rfl | rfl
              · exact hn_ne rfl
              · exact hm_ne rfl)
        · -- y = intClass ∅ m (negative): contradicts h_py
          have h_neg_y := intClass_neg_is_negative m hm hm_ne
          exact absurd (leZ_antisymm _ zeroZ hy zeroZ_mem_IntSet h_neg_y.1 h_py.1).symm h_py.2
      · -- x = intClass ∅ n (negative): contradicts h_px
        have h_neg := intClass_neg_is_negative n hn hn_ne
        exact absurd (leZ_antisymm _ zeroZ hx zeroZ_mem_IntSet h_neg.1 h_px.1).symm h_px.2

    /-- Negative times negative is positive -/
    theorem negativeZ_mul_positive (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (h_nx : isNegativeZ x) (h_ny : isNegativeZ y) :
        isPositiveZ (mulZ x y) := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, hn_ne, rfl⟩ | ⟨n, hn, hn_ne, rfl⟩
      · -- x = zeroZ: contradicts h_nx
        exact absurd rfl h_nx.2
      · -- x = intClass n ∅ (positive): contradicts h_nx
        have h_pos := intClass_pos_is_positive n hn hn_ne
        exact absurd (leZ_antisymm _ zeroZ hx zeroZ_mem_IntSet h_nx.1 h_pos.1) h_nx.2
      · -- x = intClass ∅ n (negative): actual case
        rcases int_trichotomy y hy with rfl | ⟨m, hm, hm_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
        · exact absurd rfl h_ny.2
        · -- y = intClass m ∅ (positive): contradicts h_ny
          have h_pos := intClass_pos_is_positive m hm hm_ne
          exact absurd (leZ_antisymm _ zeroZ hy zeroZ_mem_IntSet h_ny.1 h_pos.1) h_ny.2
        · -- Both negative: mulZ (intClass ∅ n) (intClass ∅ m) = intClass (mul n m) ∅
          rw [mulZ_class ∅ n ∅ m zero_in_Omega hn zero_in_Omega hm,
              zero_mul_Omega ∅ zero_in_Omega, zero_mul_Omega m hm, mul_zero n hn,
              zero_add (mul n m) (mul_in_Omega n m hn hm),
              zero_add (∅ : U) zero_in_Omega]
          exact intClass_pos_is_positive (mul n m) (mul_in_Omega n m hn hm)
            (fun h => by
              rcases (mul_eq_zero_iff n m hn hm).mp h with rfl | rfl
              · exact hn_ne rfl
              · exact hm_ne rfl)

    /-- Positive times negative is negative -/
    theorem positiveZ_negativeZ_mul_negative (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U))
        (h_px : isPositiveZ x) (h_ny : isNegativeZ y) :
        isNegativeZ (mulZ x y) := by
      rcases int_trichotomy x hx with rfl | ⟨n, hn, hn_ne, rfl⟩ | ⟨n, hn, hn_ne, rfl⟩
      · exact absurd rfl h_px.2
      · -- x = intClass n ∅ (positive)
        rcases int_trichotomy y hy with rfl | ⟨m, hm, hm_ne, rfl⟩ | ⟨m, hm, hm_ne, rfl⟩
        · exact absurd rfl h_ny.2
        · -- y = intClass m ∅ (positive): contradicts h_ny
          have h_pos := intClass_pos_is_positive m hm hm_ne
          exact absurd (leZ_antisymm _ zeroZ hy zeroZ_mem_IntSet h_ny.1 h_pos.1) h_ny.2
        · -- mulZ (intClass n ∅) (intClass ∅ m) = intClass ∅ (mul n m)
          rw [mulZ_class n ∅ ∅ m hn zero_in_Omega zero_in_Omega hm,
              mul_zero n hn, zero_mul_Omega m hm, zero_mul_Omega ∅ zero_in_Omega,
              zero_add (∅ : U) zero_in_Omega,
              add_zero (mul n m) (mul_in_Omega n m hn hm)]
          exact intClass_neg_is_negative (mul n m) (mul_in_Omega n m hn hm)
            (fun h => by
              rcases (mul_eq_zero_iff n m hn hm).mp h with rfl | rfl
              · exact hn_ne rfl
              · exact hm_ne rfl)
      · -- x = intClass ∅ n (negative): contradicts h_px
        have h_neg := intClass_neg_is_negative n hn hn_ne
        exact absurd (leZ_antisymm _ zeroZ hx zeroZ_mem_IntSet h_neg.1 h_px.1).symm h_px.2

  end Int.Order

end ZFC

export ZFC.Int.Order (
  leZ_repr
  ltZ_repr
  leZ_repr_well_defined
  leZ
  ltZ
  leZ_iff_repr
  leZ_refl
  leZ_trans
  leZ_antisymm
  leZ_total
  ltZ_iff_leZ_and_ne
  ltZ_irrefl
  ltZ_trans
  leZ_iff_ltZ_or_eq
  addZ_leZ_addZ
  ltZ_addZ_ltZ
  leZ_negZ
  isPositiveZ
  isNegativeZ
  int_trichotomy_order
  addZ_leZ_addZ_left
  mulZ_le_mulZ_nonneg
  mulZ_le_mulZ_nonpos
  mulZ_ltZ_mulZ_pos
  positiveZ_mul_closed
  negativeZ_mul_positive
  positiveZ_negativeZ_mul_negative
)
