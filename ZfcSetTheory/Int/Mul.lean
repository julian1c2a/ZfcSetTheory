/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  # Integer Multiplication

  This module defines multiplication on ℤ = QuotientSet (ω × ω) IntEquivRel
  using the QuotientLift₂ infrastructure. The operation lifts the formula
  (a,b) * (c,d) := (ac+bd, ad+bc) from ω×ω to ℤ, representing
  (a−b)(c−d) = (ac+bd) − (ad+bc).

  ## Main Definitions

  * `mulZ` — multiplication on ℤ, defined via QuotientLift₂

  ## Main Theorems

  * `mulZ_class` — computation rule: mulZ [(a,b)] [(c,d)] = [(ac+bd, ad+bc)]
  * `mulZ_in_IntSet` — closure
  * `mulZ_comm` — commutativity
  * `mulZ_assoc` — associativity
  * `mulZ_one_right` / `mulZ_one_left` — multiplicative identity
  * `mulZ_zero_right` / `mulZ_zero_left` — absorbing element
  * `mulZ_negZ_left` / `mulZ_negZ_right` — interaction with negation
  * `negZ_mulZ_negZ` — negation cancellation in product
-/

import ZfcSetTheory.Int.Neg
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

  universe u
  variable {U : Type u}

  namespace Int.Mul

    /-! ### Helper: decomposition of IntSet elements -/

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

    /-! ### Arithmetic helper lemmas -/

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

    /-! ### Pairwise multiplication operation on ω × ω -/

    /-- The raw operation on pairs: (a,b) * (c,d) := (ac+bd, ad+bc) -/
    noncomputable def mulZ_op (p q : U) : U :=
      ⟨add (mul (fst p) (fst q)) (mul (snd p) (snd q)),
       add (mul (fst p) (snd q)) (mul (snd p) (fst q))⟩

    /-- mulZ_op is closed on ω × ω -/
    private theorem mulZ_op_closed (p q : U)
        (hp : p ∈ (ω : U) ×ₛ ω) (hq : q ∈ (ω : U) ×ₛ ω) :
        mulZ_op p q ∈ (ω : U) ×ₛ ω := by
      rw [CartesianProduct_is_specified] at hp hq
      obtain ⟨_, hp_fst, hp_snd⟩ := hp
      obtain ⟨_, hq_fst, hq_snd⟩ := hq
      unfold mulZ_op
      rw [CartesianProduct_is_specified]
      refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩
      · simp only [fst_of_ordered_pair]
        exact add_in_Omega _ _ (mul_in_Omega _ _ hp_fst hq_fst)
                               (mul_in_Omega _ _ hp_snd hq_snd)
      · simp only [snd_of_ordered_pair]
        exact add_in_Omega _ _ (mul_in_Omega _ _ hp_fst hq_snd)
                               (mul_in_Omega _ _ hp_snd hq_fst)

    /-- mulZ_op respects IntEquivRel (compatibility for QuotientLift₂).

    Given (a,b)~(c,d) i.e. a+d=b+c, and (e,f)~(g,h) i.e. e+h=f+g,
    we must show (ae+bf, af+be) ~ (cg+dh, ch+dg), i.e.
    (ae+bf)+(ch+dg) = (af+be)+(cg+dh).

    Strategy: cancel (de+cf) from both sides, then transform LHS to RHS
    via a chain of rewrites using h₁–h₄ and add_add_comm. -/
    private theorem mulZ_op_compat (p₁ p₂ q₁ q₂ : U)
        (hp₁ : p₁ ∈ (ω : U) ×ₛ ω) (hp₂ : p₂ ∈ (ω : U) ×ₛ ω)
        (hq₁ : q₁ ∈ (ω : U) ×ₛ ω) (hq₂ : q₂ ∈ (ω : U) ×ₛ ω)
        (hR₁ : ⟨p₁, p₂⟩ ∈ (IntEquivRel : U))
        (hR₂ : ⟨q₁, q₂⟩ ∈ (IntEquivRel : U)) :
        ⟨mulZ_op p₁ q₁, mulZ_op p₂ q₂⟩ ∈ (IntEquivRel : U) := by
      -- Decompose pairs
      rw [CartesianProduct_is_specified] at hp₁ hp₂ hq₁ hq₂
      obtain ⟨⟨a, b, hp₁_eq⟩, ha, hb⟩ := hp₁
      obtain ⟨⟨c, d, hp₂_eq⟩, hc, hd⟩ := hp₂
      obtain ⟨⟨e, f, hq₁_eq⟩, he, hf⟩ := hq₁
      obtain ⟨⟨g, h, hq₂_eq⟩, hg, hh⟩ := hq₂
      subst hp₁_eq; subst hp₂_eq; subst hq₁_eq; subst hq₂_eq
      simp only [fst_of_ordered_pair, snd_of_ordered_pair] at *
      rw [mem_IntEquivRel] at hR₁ hR₂
      obtain ⟨_, _, _, _, hR₁_eq⟩ := hR₁  -- add a d = add b c
      obtain ⟨_, _, _, _, hR₂_eq⟩ := hR₂  -- add e h = add f g
      unfold mulZ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      rw [mem_IntEquivRel]
      -- Membership proofs for all products
      have hae := mul_in_Omega a e ha he
      have hbf := mul_in_Omega b f hb hf
      have haf := mul_in_Omega a f ha hf
      have hbe := mul_in_Omega b e hb he
      have hcg := mul_in_Omega c g hc hg
      have hdh := mul_in_Omega d h hd hh
      have hch := mul_in_Omega c h hc hh
      have hdg := mul_in_Omega d g hd hg
      have hde := mul_in_Omega d e hd he
      have hcf := mul_in_Omega c f hc hf
      have hce := mul_in_Omega c e hc he
      have hdf := mul_in_Omega d f hd hf
      refine ⟨add_in_Omega _ _ hae hbf, add_in_Omega _ _ haf hbe,
              add_in_Omega _ _ hcg hdh, add_in_Omega _ _ hch hdg, ?_⟩
      -- Goal: add (ae+bf) (ch+dg) = add (af+be) (cg+dh)
      -- Derived equations from hR₁ and hR₂:
      have h1 : add (mul a e) (mul d e) = add (mul b e) (mul c e) := by
        rw [← mul_rdistr_Omega a d e ha hd he, ← mul_rdistr_Omega b c e hb hc he, hR₁_eq]
      have h2 : add (mul a f) (mul d f) = add (mul b f) (mul c f) := by
        rw [← mul_rdistr_Omega a d f ha hd hf, ← mul_rdistr_Omega b c f hb hc hf, hR₁_eq]
      have h3 : add (mul c e) (mul c h) = add (mul c f) (mul c g) := by
        rw [← mul_ldistr_Omega c e h hc he hh, ← mul_ldistr_Omega c f g hc hf hg, hR₂_eq]
      have h4 : add (mul d e) (mul d h) = add (mul d f) (mul d g) := by
        rw [← mul_ldistr_Omega d e h hd he hh, ← mul_ldistr_Omega d f g hd hf hg, hR₂_eq]
      -- Cancel (de+cf) from both sides
      apply add_right_cancel_Omega (add (mul d e) (mul c f))
        (add (add (mul a e) (mul b f)) (add (mul c h) (mul d g)))
        (add (add (mul a f) (mul b e)) (add (mul c g) (mul d h)))
        (add_in_Omega _ _ hde hcf)
        (add_in_Omega _ _ (add_in_Omega _ _ hae hbf) (add_in_Omega _ _ hch hdg))
        (add_in_Omega _ _ (add_in_Omega _ _ haf hbe) (add_in_Omega _ _ hcg hdh))
      -- Goal: add ((ae+bf)+(ch+dg)) (de+cf) = add ((af+be)+(cg+dh)) (de+cf)
      -- Chain of rewrites transforming LHS to RHS:
      -- Step 1: assoc — move (de+cf) inward to join (ae+bf)
      rw [← add_assoc_Omega (add (mul a e) (mul b f)) (add (mul c h) (mul d g))
          (add (mul d e) (mul c f))
          (add_in_Omega _ _ hae hbf) (add_in_Omega _ _ hch hdg)
          (add_in_Omega _ _ hde hcf)]
      rw [add_comm_Omega (add (mul c h) (mul d g)) (add (mul d e) (mul c f))
          (add_in_Omega _ _ hch hdg) (add_in_Omega _ _ hde hcf)]
      rw [add_assoc_Omega (add (mul a e) (mul b f)) (add (mul d e) (mul c f))
          (add (mul c h) (mul d g))
          (add_in_Omega _ _ hae hbf) (add_in_Omega _ _ hde hcf)
          (add_in_Omega _ _ hch hdg)]
      -- Now: ((ae+bf)+(de+cf)) + (ch+dg)
      -- Step 2: add_add_comm on (ae+bf)+(de+cf) → (ae+de)+(bf+cf)
      rw [add_add_comm (mul a e) (mul b f) (mul d e) (mul c f) hae hbf hde hcf]
      -- Now: ((ae+de)+(bf+cf)) + (ch+dg)
      -- Step 3: h1 and h2.symm
      rw [h1, ← h2]
      -- Now: ((be+ce)+(af+df)) + (ch+dg)   ... wait, ← h2 gives bf+cf → af+df?
      -- h2: af+df = bf+cf, so ← h2 rewrites bf+cf → af+df. But after h1,
      -- we had (be+ce)+(bf+cf). The ← h2 should rewrite bf+cf to af+df.
      -- Actually no: ← h2 goes from bf+cf to af+df (rw ← h2 replaces RHS by LHS).
      -- h2 says add (mul a f) (mul d f) = add (mul b f) (mul c f).
      -- rw [← h2] replaces add (mul b f) (mul c f) by add (mul a f) (mul d f). ✓
      -- Now: ((be+ce)+(af+df)) + (ch+dg)
      -- Step 4: add_add_comm on (be+ce)+(af+df) → (be+af)+(ce+df)
      rw [add_add_comm (mul b e) (mul c e) (mul a f) (mul d f) hbe hce haf hdf]
      -- Now: ((be+af)+(ce+df)) + (ch+dg)
      -- Step 5: comm on be+af → af+be
      rw [add_comm_Omega (mul b e) (mul a f) hbe haf]
      -- Now: ((af+be)+(ce+df)) + (ch+dg)
      -- Step 6: assoc — move (ch+dg) inward to join (ce+df)
      rw [← add_assoc_Omega (add (mul a f) (mul b e)) (add (mul c e) (mul d f))
          (add (mul c h) (mul d g))
          (add_in_Omega _ _ haf hbe) (add_in_Omega _ _ hce hdf)
          (add_in_Omega _ _ hch hdg)]
      -- Now: (af+be) + ((ce+df)+(ch+dg))
      -- Step 7: add_add_comm on (ce+df)+(ch+dg) → (ce+ch)+(df+dg)
      rw [add_add_comm (mul c e) (mul d f) (mul c h) (mul d g) hce hdf hch hdg]
      -- Now: (af+be) + ((ce+ch)+(df+dg))
      -- Step 8: h3 and h4.symm
      rw [h3, ← h4]
      -- h3: ce+ch = cf+cg. rw [h3] replaces ce+ch by cf+cg. ✓
      -- h4: de+dh = df+dg. ← h4 replaces df+dg by de+dh. ✓
      -- Now: (af+be) + ((cf+cg)+(de+dh))
      -- Step 9: add_add_comm on (cf+cg)+(de+dh) → (cf+de)+(cg+dh)
      rw [add_add_comm (mul c f) (mul c g) (mul d e) (mul d h) hcf hcg hde hdh]
      -- Now: (af+be) + ((cf+de)+(cg+dh))
      -- Step 10: comm on cf+de → de+cf
      rw [add_comm_Omega (mul c f) (mul d e) hcf hde]
      -- Now: (af+be) + ((de+cf)+(cg+dh))
      -- Step 11: comm on (de+cf)+(cg+dh) → (cg+dh)+(de+cf)
      rw [add_comm_Omega (add (mul d e) (mul c f)) (add (mul c g) (mul d h))
          (add_in_Omega _ _ hde hcf) (add_in_Omega _ _ hcg hdh)]
      -- Now: (af+be) + ((cg+dh)+(de+cf))
      -- Step 12: assoc — pull (de+cf) out
      rw [add_assoc_Omega (add (mul a f) (mul b e)) (add (mul c g) (mul d h))
          (add (mul d e) (mul c f))
          (add_in_Omega _ _ haf hbe) (add_in_Omega _ _ hcg hdh)
          (add_in_Omega _ _ hde hcf)]
      -- Now: ((af+be)+(cg+dh)) + (de+cf)  ✓

    /-! ### Definition of multiplication on ℤ -/

    /-- The graph of integer multiplication, constructed via QuotientLift₂ -/
    noncomputable def mulZ_graph : U :=
      QuotientLift₂Graph mulZ_op IntEquivRel ((ω : U) ×ₛ ω)

    /-- Multiplication on ℤ -/
    noncomputable def mulZ (x y : U) : U :=
      mulZ_graph⦅⟨x, y⟩⦆

    /-! ### Function property -/

    /-- The multiplication graph is a function from ℤ × ℤ to ℤ -/
    theorem mulZ_graph_is_function :
        IsFunction (mulZ_graph : U) ((IntSet : U) ×ₛ IntSet) IntSet := by
      unfold mulZ_graph IntSet
      exact QuotientLift₂_well_defined mulZ_op IntEquivRel ((ω : U) ×ₛ ω)
        IntEquivRel_is_equivalence mulZ_op_closed mulZ_op_compat

    /-! ### Computation rule -/

    /-- mulZ [(a,b)] [(c,d)] = [(ac+bd, ad+bc)] -/
    theorem mulZ_class (a b c d : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U)) :
        mulZ (intClass a b) (intClass c d) =
          intClass (add (mul a c) (mul b d)) (add (mul a d) (mul b c)) := by
      unfold mulZ mulZ_graph
      have h1 : intClass a b = EqClass (⟨a, b⟩ : U) IntEquivRel ((ω : U) ×ₛ ω) := rfl
      have h2 : intClass c d = EqClass (⟨c, d⟩ : U) IntEquivRel ((ω : U) ×ₛ ω) := rfl
      rw [h1, h2]
      rw [QuotientLift₂_apply mulZ_op IntEquivRel ((ω : U) ×ₛ ω) ⟨a, b⟩ ⟨c, d⟩
          IntEquivRel_is_equivalence mulZ_op_closed mulZ_op_compat
          ((OrderedPair_mem_CartesianProduct a b ω ω).mpr ⟨ha, hb⟩)
          ((OrderedPair_mem_CartesianProduct c d ω ω).mpr ⟨hc, hd⟩)]
      unfold mulZ_op
      simp only [fst_of_ordered_pair, snd_of_ordered_pair]
      exact rfl

    /-! ### Well-definedness -/

    /-- If [(a,b)] = [(c,d)] then mulZ preserves this equality -/
    theorem mulZ_well_defined (a b c d e f g h : U)
        (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U))
        (hc : c ∈ (ω : U)) (hd : d ∈ (ω : U))
        (he : e ∈ (ω : U)) (hf : f ∈ (ω : U))
        (hg : g ∈ (ω : U)) (hh : h ∈ (ω : U))
        (h₁ : intClass a b = intClass c d)
        (h₂ : intClass e f = intClass g h) :
        intClass (add (mul a e) (mul b f)) (add (mul a f) (mul b e)) =
          intClass (add (mul c g) (mul d h)) (add (mul c h) (mul d g)) := by
      rw [← mulZ_class a b e f ha hb he hf, ← mulZ_class c d g h hc hd hg hh, h₁, h₂]

    /-! ### Closure -/

    /-- Multiplication is closed on ℤ -/
    theorem mulZ_in_IntSet (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        mulZ x y ∈ (IntSet : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [mulZ_class a b c d ha hb hc hd]
      exact intClass_mem_IntSet _ _
        (add_in_Omega _ _ (mul_in_Omega a c ha hc) (mul_in_Omega b d hb hd))
        (add_in_Omega _ _ (mul_in_Omega a d ha hd) (mul_in_Omega b c hb hc))

    /-! ### Algebraic properties -/

    /-- Commutativity: mulZ x y = mulZ y x -/
    theorem mulZ_comm (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        mulZ x y = mulZ y x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [mulZ_class a b c d ha hb hc hd]
      rw [mulZ_class c d a b hc hd ha hb]
      rw [mul_comm_Omega a c ha hc, mul_comm_Omega b d hb hd]
      rw [mul_comm_Omega c b hc hb, mul_comm_Omega d a hd ha]
      rw [add_comm_Omega (mul b c) (mul a d) (mul_in_Omega b c hb hc) (mul_in_Omega a d ha hd)]

    /-- Associativity: mulZ (mulZ x y) z = mulZ x (mulZ y z) -/
    theorem mulZ_assoc (x y z : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U)) :
        mulZ (mulZ x y) z = mulZ x (mulZ y z) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      obtain ⟨e, f, he, hf, hz_eq⟩ := intClass_exists z hz
      subst hx_eq; subst hy_eq; subst hz_eq
      rw [mulZ_class a b c d ha hb hc hd]
      have hac_bd := add_in_Omega _ _ (mul_in_Omega a c ha hc) (mul_in_Omega b d hb hd)
      have had_bc := add_in_Omega _ _ (mul_in_Omega a d ha hd) (mul_in_Omega b c hb hc)
      rw [mulZ_class (add (mul a c) (mul b d)) (add (mul a d) (mul b c)) e f
          hac_bd had_bc he hf]
      rw [mulZ_class c d e f hc hd he hf]
      have hce_df := add_in_Omega _ _ (mul_in_Omega c e hc he) (mul_in_Omega d f hd hf)
      have hcf_de := add_in_Omega _ _ (mul_in_Omega c f hc hf) (mul_in_Omega d e hd he)
      rw [mulZ_class a b (add (mul c e) (mul d f)) (add (mul c f) (mul d e))
          ha hb hce_df hcf_de]
      -- LHS 1st component: (ac+bd)e + (ad+bc)f = ace+bde+adf+bcf
      -- RHS 1st component: a(ce+df) + b(cf+de) = ace+adf+bcf+bde
      -- LHS 2nd component: (ac+bd)f + (ad+bc)e = acf+bdf+ade+bce
      -- RHS 2nd component: a(cf+de) + b(ce+df) = acf+ade+bce+bdf
      -- Both are equal after rearranging via add_add_comm.
      -- First component:
      have hac := mul_in_Omega a c ha hc
      have hbd := mul_in_Omega b d hb hd
      have had := mul_in_Omega a d ha hd
      have hbc := mul_in_Omega b c hb hc
      have hce := mul_in_Omega c e hc he
      have hdf := mul_in_Omega d f hd hf
      have hcf := mul_in_Omega c f hc hf
      have hde := mul_in_Omega d e hd he
      -- Prove both components separately, then combine
      have h_comp1 : add (mul (add (mul a c) (mul b d)) e) (mul (add (mul a d) (mul b c)) f)
          = add (mul a (add (mul c e) (mul d f))) (mul b (add (mul c f) (mul d e))) := by
        rw [mul_rdistr_Omega (mul a c) (mul b d) e hac hbd he]
        rw [mul_rdistr_Omega (mul a d) (mul b c) f had hbc hf]
        rw [mul_assoc_Omega a c e ha hc he]
        rw [mul_assoc_Omega b d e hb hd he]
        rw [mul_assoc_Omega a d f ha hd hf]
        rw [mul_assoc_Omega b c f hb hc hf]
        rw [mul_ldistr_Omega a (mul c e) (mul d f) ha hce hdf]
        rw [mul_ldistr_Omega b (mul c f) (mul d e) hb hcf hde]
        have hace := mul_in_Omega a (mul c e) ha hce
        have hbde := mul_in_Omega b (mul d e) hb hde
        have hadf := mul_in_Omega a (mul d f) ha hdf
        have hbcf := mul_in_Omega b (mul c f) hb hcf
        rw [add_add_comm (mul a (mul c e)) (mul b (mul d e))
            (mul a (mul d f)) (mul b (mul c f)) hace hbde hadf hbcf]
        rw [add_comm_Omega (mul b (mul d e)) (mul b (mul c f)) hbde hbcf]
      have h_comp2 : add (mul (add (mul a c) (mul b d)) f) (mul (add (mul a d) (mul b c)) e)
          = add (mul a (add (mul c f) (mul d e))) (mul b (add (mul c e) (mul d f))) := by
        rw [mul_rdistr_Omega (mul a c) (mul b d) f hac hbd hf]
        rw [mul_rdistr_Omega (mul a d) (mul b c) e had hbc he]
        rw [mul_assoc_Omega a c f ha hc hf]
        rw [mul_assoc_Omega b d f hb hd hf]
        rw [mul_assoc_Omega a d e ha hd he]
        rw [mul_assoc_Omega b c e hb hc he]
        rw [mul_ldistr_Omega a (mul c f) (mul d e) ha hcf hde]
        rw [mul_ldistr_Omega b (mul c e) (mul d f) hb hce hdf]
        have hacf := mul_in_Omega a (mul c f) ha hcf
        have hbdf := mul_in_Omega b (mul d f) hb hdf
        have hade := mul_in_Omega a (mul d e) ha hde
        have hbce := mul_in_Omega b (mul c e) hb hce
        rw [add_add_comm (mul a (mul c f)) (mul b (mul d f))
            (mul a (mul d e)) (mul b (mul c e)) hacf hbdf hade hbce]
        rw [add_comm_Omega (mul b (mul d f)) (mul b (mul c e)) hbdf hbce]
      rw [h_comp1, h_comp2]

    /-- Right multiplicative identity: mulZ x oneZ = x -/
    theorem mulZ_one_right (x : U) (hx : x ∈ (IntSet : U)) :
        mulZ x (oneZ : U) = x := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      unfold oneZ
      rw [mulZ_class a b (σ ∅) ∅ ha hb (succ_in_Omega ∅ zero_in_Omega) zero_in_Omega]
      -- Goal: intClass (add (mul a (σ ∅)) (mul b ∅)) (add (mul a ∅) (mul b (σ ∅))) = intClass a b
      rw [mul_one_Omega a ha, mul_zero b hb, add_zero a ha]
      rw [mul_zero a ha, mul_one_Omega b hb, zero_add b hb]

    /-- Left multiplicative identity: mulZ oneZ x = x -/
    theorem mulZ_one_left (x : U) (hx : x ∈ (IntSet : U)) :
        mulZ (oneZ : U) x = x := by
      rw [mulZ_comm oneZ x oneZ_mem_IntSet hx]
      exact mulZ_one_right x hx

    /-- Right absorbing element: mulZ x zeroZ = zeroZ -/
    theorem mulZ_zero_right (x : U) (hx : x ∈ (IntSet : U)) :
        mulZ x (zeroZ : U) = (zeroZ : U) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      subst hx_eq
      unfold zeroZ
      rw [mulZ_class a b ∅ ∅ ha hb zero_in_Omega zero_in_Omega]
      rw [mul_zero a ha, mul_zero b hb]
      -- intClass (add ∅ ∅) (add ∅ ∅) = intClass ∅ ∅
      rw [add_zero ∅ zero_in_Omega]

    /-- Left absorbing element: mulZ zeroZ x = zeroZ -/
    theorem mulZ_zero_left (x : U) (hx : x ∈ (IntSet : U)) :
        mulZ (zeroZ : U) x = (zeroZ : U) := by
      rw [mulZ_comm zeroZ x zeroZ_mem_IntSet hx]
      exact mulZ_zero_right x hx

    /-- Interaction with negation (left): mulZ (negZ x) y = negZ (mulZ x y) -/
    theorem mulZ_negZ_left (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        mulZ (negZ x) y = negZ (mulZ x y) := by
      obtain ⟨a, b, ha, hb, hx_eq⟩ := intClass_exists x hx
      obtain ⟨c, d, hc, hd, hy_eq⟩ := intClass_exists y hy
      subst hx_eq; subst hy_eq
      rw [negZ_class a b ha hb]
      rw [mulZ_class b a c d hb ha hc hd]
      rw [mulZ_class a b c d ha hb hc hd]
      rw [negZ_class (add (mul a c) (mul b d)) (add (mul a d) (mul b c))
          (add_in_Omega _ _ (mul_in_Omega a c ha hc) (mul_in_Omega b d hb hd))
          (add_in_Omega _ _ (mul_in_Omega a d ha hd) (mul_in_Omega b c hb hc))]
      rw [add_comm_Omega (mul b c) (mul a d) (mul_in_Omega b c hb hc) (mul_in_Omega a d ha hd),
          add_comm_Omega (mul b d) (mul a c) (mul_in_Omega b d hb hd) (mul_in_Omega a c ha hc)]

    /-- Interaction with negation (right): mulZ x (negZ y) = negZ (mulZ x y) -/
    theorem mulZ_negZ_right (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        mulZ x (negZ y) = negZ (mulZ x y) := by
      rw [mulZ_comm x (negZ y) hx (negZ_in_IntSet y hy)]
      rw [mulZ_negZ_left y x hy hx]
      rw [mulZ_comm y x hy hx]

    /-- Negation cancellation: mulZ (negZ x) (negZ y) = mulZ x y -/
    theorem negZ_mulZ_negZ (x y : U)
        (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) :
        mulZ (negZ x) (negZ y) = mulZ x y := by
      rw [mulZ_negZ_left x (negZ y) hx (negZ_in_IntSet y hy)]
      rw [mulZ_negZ_right x y hx hy]
      rw [negZ_negZ (mulZ x y) (mulZ_in_IntSet x y hx hy)]

    /-- Natural multiplication is zero iff a factor is zero, lifted from Peano. -/
    theorem mul_eq_zero_iff (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) :
        mul m n = (∅ : U) ↔ m = ∅ ∨ n = ∅ := by
      obtain ⟨p, hp⟩ := fromPeano_surjective m (mem_Omega_is_Nat m hm)
      obtain ⟨q, hq⟩ := fromPeano_surjective n (mem_Omega_is_Nat n hn)
      subst hp; subst hq
      change mul (fromPeano p) (fromPeano q) = (fromPeano Peano.ℕ₀.zero : U) ↔
             (fromPeano p : U) = fromPeano Peano.ℕ₀.zero ∨
             (fromPeano q : U) = fromPeano Peano.ℕ₀.zero
      rw [← fromPeano_mul p q]
      constructor
      · intro h
        rcases (Peano.Mul.mul_eq_zero p q).mp (fromPeano_injective h) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · intro h
        rcases h with h | h
        · have := fromPeano_injective h; subst this
          exact congrArg fromPeano (Peano.Mul.zero_mul q)
        · have := fromPeano_injective h; subst this
          exact congrArg fromPeano (Peano.Mul.mul_zero p)

  end Int.Mul

end ZFC

export ZFC.Int.Mul (
  mulZ
  mulZ_graph_is_function
  mulZ_well_defined
  mulZ_class
  mulZ_in_IntSet
  mulZ_comm
  mulZ_assoc
  mulZ_one_right
  mulZ_one_left
  mulZ_zero_right
  mulZ_zero_left
  mulZ_negZ_left
  mulZ_negZ_right
  negZ_mulZ_negZ
  mul_eq_zero_iff
)
