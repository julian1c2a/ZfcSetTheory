/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Convergence of Sequences in ℚ

  This module defines convergence and limits for sequences f : ω → ℚ.
  All notions are purely within ℚ — no real numbers are involved.

  ## Main Definitions

  * `convergesToQ f L`   — f converges to L: ε-N definition over ℚ
  * `hasLimitQ f`        — f has some limit in ℚ
  * `IsSubseqOf g f`     — g is a subsequence of f via some strictly increasing φ: ω → ω

  ## Main Theorems

  * `convergesToQ_const`   — the constant sequence at a converges to a
  * `limit_unique`         — limits are unique (if L₁, L₂ are both limits then L₁ = L₂)
  * `subseq_convergent`    — every subsequence of a convergent sequence converges to the same limit
  * `convergesToQ_add`     — f → L₁, g → L₂ implies (f+g) → L₁+L₂

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.Sequences
import ZFC.Rat.Abs
import ZFC.Rat.Field
import ZFC.Nat.MaxMin

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
  open ZFC.Nat.MaxMin
  open ZFC.Int.Basic
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Field
  open ZFC.Rat.Sequences
  -- Importar lemas de monotonía de Field
  open ZFC.Rat.Field (mulQ_leQ_mulQ_of_nonneg_right mulQ_leQ_mulQ_of_nonneg_left)

  universe u
  variable {U : Type u}

  namespace Rat.Convergence

    -- =========================================================================
    -- Section 0: Private helpers
    -- =========================================================================

    /-- oneQ is positive: 0 < 1 in ℚ -/
    private theorem oneQ_pos : isPositiveQ (oneQ : U) := by
      constructor
      · -- leQ zeroQ oneQ via canonical representatives zeroZ/oneZ and oneZ/oneZ
        rw [leQ_iff_repr (zeroQ : U) (oneQ : U) zeroQ_mem_RatSet oneQ_mem_RatSet]
        have hone_i : (oneZ : U) ∈ (IntSet : U) := oneZ_mem_IntSet
        have hone_nz : (oneZ : U) ∈ (NonZeroIntSet : U) := oneZ_mem_NonZeroIntSet
        -- leQ_repr zeroZ oneZ oneZ oneZ = leZ (mulZ (mulZ zeroZ oneZ) (mulZ oneZ oneZ))
        --                                      (mulZ (mulZ oneZ oneZ) (mulZ oneZ oneZ))
        -- = leZ zeroZ oneZ by mulZ_zero_left and mulZ_one_left and square_nonneg
        have h_repr : leQ_repr (zeroZ : U) (oneZ : U) (oneZ : U) (oneZ : U) := by
          unfold leQ_repr
          have h_one : mulZ (oneZ : U) (oneZ : U) = (oneZ : U) :=
            mulZ_one_left (oneZ : U) hone_i
          have h_zero : mulZ (zeroZ : U) (oneZ : U) = (zeroZ : U) :=
            mulZ_zero_left (oneZ : U) hone_i
          have lhs_eq : mulZ (mulZ (zeroZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (zeroZ : U) := by
            simp only [h_one, h_zero]
          have rhs_eq : mulZ (mulZ (oneZ : U) (oneZ : U)) (mulZ (oneZ : U) (oneZ : U)) = (oneZ : U) := by
            simp only [h_one]
          rw [lhs_eq, rhs_eq]
          have sq := square_nonneg (oneZ : U) hone_i
          rwa [h_one] at sq
        exact ⟨(zeroZ : U), (oneZ : U), (oneZ : U), (oneZ : U),
               zeroZ_mem_IntSet, hone_nz, hone_i, hone_nz, rfl, rfl, h_repr⟩
      · exact zeroQ_ne_oneQ

    /-- 2 in ℚ -/
    private noncomputable def twoQ : U := addQ (oneQ : U) (oneQ : U)

    private theorem twoQ_mem_RatSet : (twoQ : U) ∈ (RatSet : U) :=
      addQ_in_RatSet oneQ oneQ oneQ_mem_RatSet oneQ_mem_RatSet

    /-- 1+1 ≠ 0 in ℚ -/
    private theorem twoQ_ne_zeroQ : (twoQ : U) ≠ (zeroQ : U) := by
      intro h
      -- twoQ = zeroQ → addQ oneQ oneQ = zeroQ
      -- addQ_leQ_addQ zeroQ oneQ oneQ: leQ (addQ zeroQ oneQ) (addQ oneQ oneQ)
      -- = leQ oneQ zeroQ (using addQ_zero_left and h)
      -- With leQ zeroQ oneQ (from oneQ_pos), we get oneQ = zeroQ → contradiction
      have h_le : leQ (addQ (zeroQ : U) (oneQ : U)) (addQ (oneQ : U) (oneQ : U)) :=
        addQ_leQ_addQ zeroQ oneQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet oneQ_mem_RatSet
          oneQ_pos.1
      rw [addQ_zero_left oneQ oneQ_mem_RatSet] at h_le
      -- h_le : leQ oneQ (addQ oneQ oneQ); h : twoQ = zeroQ (twoQ is addQ oneQ oneQ)
      have h_two : addQ (oneQ : U) (oneQ : U) = (zeroQ : U) := h
      rw [h_two] at h_le
      -- h_le : leQ oneQ zeroQ; oneQ_pos.1 : leQ zeroQ oneQ
      have h_eq : (oneQ : U) = zeroQ :=
        leQ_antisymm oneQ zeroQ oneQ_mem_RatSet zeroQ_mem_RatSet h_le oneQ_pos.1
      exact zeroQ_ne_oneQ h_eq.symm

    /-- Half of ε: ε / 2 = ε · (1/2) -/
    private noncomputable def halfQ (ε : U) : U := mulQ ε (invQ twoQ)

    private theorem halfQ_mem_RatSet (ε : U) (hε : ε ∈ (RatSet : U)) :
        halfQ ε ∈ (RatSet : U) :=
      mulQ_in_RatSet ε (invQ twoQ) hε (invQ_in_RatSet twoQ twoQ_mem_RatSet)

    /-- invQ(2) + invQ(2) = 1  (because (1/2)·(1+1) = (1/2)·2 = 1) -/
    private theorem inv_twoQ_add :
        addQ (invQ (twoQ : U)) (invQ (twoQ : U)) = (oneQ : U) := by
      have hinv : invQ (twoQ : U) ∈ (RatSet : U) := invQ_in_RatSet twoQ twoQ_mem_RatSet
      -- addQ (invQ twoQ) (invQ twoQ) = mulQ (invQ twoQ) (addQ oneQ oneQ)
      --   by distributing: mulQ x (y+z) = mulQ x y + mulQ x z, then mulQ x 1 = x
      have h1 : addQ (invQ (twoQ : U)) (invQ (twoQ : U)) =
          mulQ (invQ (twoQ : U)) (addQ (oneQ : U) (oneQ : U)) := by
        rw [mulQ_addQ_distrib_left (invQ twoQ) oneQ oneQ
              hinv oneQ_mem_RatSet oneQ_mem_RatSet,
            mulQ_one_right (invQ twoQ) hinv]
      -- mulQ (invQ twoQ) (addQ oneQ oneQ) = mulQ (invQ twoQ) twoQ  (by def of twoQ)
      have h2 : mulQ (invQ (twoQ : U)) (addQ (oneQ : U) (oneQ : U)) =
          mulQ (invQ (twoQ : U)) (twoQ : U) := rfl
      -- mulQ (invQ twoQ) twoQ = oneQ
      have h3 : mulQ (invQ (twoQ : U)) (twoQ : U) = (oneQ : U) :=
        mulQ_invQ_left twoQ twoQ_mem_RatSet twoQ_ne_zeroQ
      rw [h1, h2, h3]

    /-- ε/2 + ε/2 = ε -/
    private theorem half_add_half (ε : U) (hε : ε ∈ (RatSet : U)) :
        addQ (halfQ ε) (halfQ ε) = ε := by
      show addQ (mulQ ε (invQ twoQ)) (mulQ ε (invQ twoQ)) = ε
      rw [← mulQ_addQ_distrib_left ε (invQ twoQ) (invQ twoQ)
            hε (invQ_in_RatSet twoQ twoQ_mem_RatSet) (invQ_in_RatSet twoQ twoQ_mem_RatSet),
          inv_twoQ_add, mulQ_one_right ε hε]

    /-- If ε > 0 then ε/2 > 0 -/
    private theorem halfQ_pos (ε : U) (hε : ε ∈ (RatSet : U)) (hε_pos : isPositiveQ ε) :
        isPositiveQ (halfQ ε) := by
      have hε₂ : halfQ ε ∈ (RatSet : U) := halfQ_mem_RatSet ε hε
      rcases rat_trichotomy_order (halfQ ε) hε₂ with h | h | h
      · exact h
      · -- halfQ ε = zeroQ → ε = 0, contradiction
        exfalso
        have : ε = (zeroQ : U) := by
          have hh := half_add_half ε hε
          rw [h, addQ_zero_left zeroQ zeroQ_mem_RatSet] at hh
          exact hh.symm
        exact hε_pos.2 this.symm
      · -- isNegativeQ (halfQ ε): halfQ ε < 0, so 2·(halfQ ε) < halfQ ε ≤ 0
        exfalso
        -- h : ltQ (halfQ ε) zeroQ, so h.1 : leQ (halfQ ε) zeroQ
        have h_le : leQ (halfQ ε) (zeroQ : U) := h.1
        -- leQ (halfQ ε + halfQ ε) (0 + halfQ ε) = leQ ε (halfQ ε)
        -- Note: addQ_leQ_addQ x y z gives leQ (addQ x z) (addQ y z)
        have h_le2 : leQ (addQ (halfQ ε) (halfQ ε)) (addQ (zeroQ : U) (halfQ ε)) :=
          addQ_leQ_addQ (halfQ ε) (zeroQ : U) (halfQ ε) hε₂ zeroQ_mem_RatSet hε₂ h_le
        rw [addQ_zero_left (halfQ ε) hε₂, half_add_half ε hε] at h_le2
        -- h_le2 : leQ ε (halfQ ε); h_le : leQ (halfQ ε) zeroQ
        have h_le3 : leQ ε (zeroQ : U) :=
          leQ_trans ε (halfQ ε) zeroQ hε hε₂ zeroQ_mem_RatSet h_le2 h_le
        -- hε_pos.1 : leQ zeroQ ε, h_le3 : leQ ε zeroQ → ε = zeroQ
        exact hε_pos.2 (leQ_antisymm ε zeroQ hε zeroQ_mem_RatSet h_le3 hε_pos.1).symm

    /-- |x − y| = |y − x| -/
    private theorem absQ_symm (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        absQ (subQ x y) = absQ (subQ y x) := by
      have hxy : subQ x y ∈ (RatSet : U) :=
        addQ_in_RatSet x (negQ y) hx (negQ_in_RatSet y hy)
      have hyx : subQ y x ∈ (RatSet : U) :=
        addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx)
      -- Show subQ y x = negQ (subQ x y)
      have h_neg : subQ y x = negQ (subQ x y) := by
        -- (subQ x y) + (subQ y x) = 0
        have h_sum : addQ (subQ x y) (subQ y x) = (zeroQ : U) :=
          calc addQ (addQ x (negQ y)) (addQ y (negQ x))
              = addQ x (addQ (negQ y) (addQ y (negQ x))) := by
                rw [addQ_assoc x (negQ y) (addQ y (negQ x)) hx
                      (negQ_in_RatSet y hy) (addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx))]
            _ = addQ x (addQ (addQ (negQ y) y) (negQ x)) := by
                rw [← addQ_assoc (negQ y) y (negQ x) (negQ_in_RatSet y hy) hy (negQ_in_RatSet x hx)]
            _ = addQ x (addQ zeroQ (negQ x)) := by rw [negQ_addQ_left y hy]
            _ = addQ x (negQ x) := by rw [addQ_zero_left (negQ x) (negQ_in_RatSet x hx)]
            _ = zeroQ := negQ_addQ_right x hx
        -- From x + (-y + y + (-x)) = 0 we derive subQ y x = negQ (subQ x y)
        calc subQ y x
            = addQ (zeroQ : U) (subQ y x) := (addQ_zero_left (subQ y x) hyx).symm
          _ = addQ (addQ (negQ (subQ x y)) (subQ x y)) (subQ y x) := by
                rw [negQ_addQ_left (subQ x y) hxy]
          _ = addQ (negQ (subQ x y)) (addQ (subQ x y) (subQ y x)) := by
                rw [addQ_assoc (negQ (subQ x y)) (subQ x y) (subQ y x)
                      (negQ_in_RatSet (subQ x y) hxy) hxy hyx]
          _ = addQ (negQ (subQ x y)) (zeroQ : U) := by rw [h_sum]
          _ = negQ (subQ x y) :=
                addQ_zero_right (negQ (subQ x y)) (negQ_in_RatSet (subQ x y) hxy)
      rw [h_neg, absQ_negQ (subQ x y) hxy]

    /-- Triangle inequality for subtraction: |a − c| ≤ |a − b| + |b − c| -/
    private theorem absQ_triangle_sub (a b c : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U)) :
        leQ (absQ (subQ a c)) (addQ (absQ (subQ a b)) (absQ (subQ b c))) := by
      have hab : subQ a b ∈ (RatSet : U) :=
        addQ_in_RatSet a (negQ b) ha (negQ_in_RatSet b hb)
      have hbc : subQ b c ∈ (RatSet : U) :=
        addQ_in_RatSet b (negQ c) hb (negQ_in_RatSet c hc)
      -- subQ a c = addQ (subQ a b) (subQ b c)
      have h_eq : subQ a c = addQ (subQ a b) (subQ b c) :=
        calc addQ a (negQ c)
            = addQ a (addQ (addQ (negQ b) b) (negQ c)) := by
                rw [negQ_addQ_left b hb, addQ_zero_left (negQ c) (negQ_in_RatSet c hc)]
          _ = addQ a (addQ (negQ b) (addQ b (negQ c))) := by
                rw [addQ_assoc (negQ b) b (negQ c) (negQ_in_RatSet b hb) hb (negQ_in_RatSet c hc)]
          _ = addQ (addQ a (negQ b)) (addQ b (negQ c)) := by
                rw [← addQ_assoc a (negQ b) (addQ b (negQ c)) ha (negQ_in_RatSet b hb)
                      (addQ_in_RatSet b (negQ c) hb (negQ_in_RatSet c hc))]
      rw [h_eq]
      exact absQ_triangle (subQ a b) (subQ b c) hab hbc

    /-- Transitivity: a ≤ b < c → a < c -/
    private theorem leQ_ltQ_trans (a b c : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U))
        (h_ab : leQ a b) (h_bc : ltQ b c) : ltQ a c :=
      ⟨leQ_trans a b c ha hb hc h_ab h_bc.1,
       fun h_ac => h_bc.2 (leQ_antisymm b c hb hc h_bc.1 (h_ac ▸ h_ab))⟩

    /-- a ≤ c, b < d → a + b < c + d -/
    private theorem ltQ_addQ_of_leQ_ltQ (a b c d : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U))
        (hc : c ∈ (RatSet : U)) (hd : d ∈ (RatSet : U))
        (hac : leQ a c) (hbd : ltQ b d) :
        ltQ (addQ a b) (addQ c d) := by
      -- Step 1: leQ (addQ a b) (addQ a d) via addQ_leQ_addQ on the right slot
      have h_le1 : leQ (addQ a b) (addQ a d) := by
        have := addQ_leQ_addQ b d a hb hd ha hbd.1
        rwa [addQ_comm b a hb ha, addQ_comm d a hd ha] at this
      -- Step 2: leQ (addQ a d) (addQ c d) via addQ_leQ_addQ on the left slot
      have h_le2 : leQ (addQ a d) (addQ c d) :=
        addQ_leQ_addQ a c d ha hc hd hac
      constructor
      · exact leQ_trans (addQ a b) (addQ a d) (addQ c d)
          (addQ_in_RatSet a b ha hb) (addQ_in_RatSet a d ha hd)
          (addQ_in_RatSet c d hc hd) h_le1 h_le2
      · -- addQ a b ≠ addQ c d
        intro h_eq
        -- From h_le1 and h_eq: leQ (addQ c d) (addQ a d)
        have h_le_rev : leQ (addQ c d) (addQ a d) := h_eq ▸ h_le1
        -- By antisymmetry: addQ a d = addQ c d
        have h_ad_eq : addQ a d = addQ c d :=
          leQ_antisymm (addQ a d) (addQ c d)
            (addQ_in_RatSet a d ha hd) (addQ_in_RatSet c d hc hd) h_le2 h_le_rev
        -- From h_eq and h_ad_eq: addQ a b = addQ a d
        have h_ab_ad : addQ a b = addQ a d := by rw [h_eq, h_ad_eq.symm]
        -- By addQ left cancellation: b = d
        have h_bd : b = d :=
          calc b
              = addQ zeroQ b := (addQ_zero_left b hb).symm
            _ = addQ (addQ (negQ a) a) b := by rw [negQ_addQ_left a ha]
            _ = addQ (negQ a) (addQ a b) :=
                  addQ_assoc (negQ a) a b (negQ_in_RatSet a ha) ha hb
            _ = addQ (negQ a) (addQ a d) :=
                  congrArg (fun x => addQ (negQ a) x) h_ab_ad
            _ = addQ (addQ (negQ a) a) d :=
                  (addQ_assoc (negQ a) a d (negQ_in_RatSet a ha) ha hd).symm
            _ = addQ zeroQ d := by rw [negQ_addQ_left a ha]
            _ = d := addQ_zero_left d hd
        exact hbd.2 h_bd

    /-- ≤ is transitive in ω: m ≤ n, n ≤ k → m ≤ k  (where ≤ is ∈ ∨ =) -/
    private theorem omega_le_trans (m n k : U) (hm : m ∈ ω) (hn : n ∈ ω) (hk : k ∈ ω)
        (h1 : m ∈ n ∨ m = n) (h2 : n ∈ k ∨ n = k) : m ∈ k ∨ m = k := by
      rcases h1 with hmn | rfl
      · rcases h2 with hnk | rfl
        · exact Or.inl (mem_trans m n k
            (mem_Omega_is_Nat m hm) (mem_Omega_is_Nat n hn) (mem_Omega_is_Nat k hk)
            hmn hnk)
        · exact Or.inl hmn
      · exact h2

    -- =========================================================================
    -- Section 1: Convergence definition
    -- =========================================================================

    /-- f : ω → ℚ converges to L ∈ ℚ:
        ∀ ε > 0, ∃ N ∈ ω, ∀ n ≥ N, |f(n) − L| < ε.
        The ordering is n ≥ N ↔ N ∈ n ∨ N = n (N ≤ n in ω). -/
    def convergesToQ (f L : U) : Prop :=
      ∀ ε : U, ε ∈ (RatSet : U) → isPositiveQ ε →
        ∃ N : U, N ∈ (ω : U) ∧
          ∀ n : U, n ∈ (ω : U) → N ∈ n ∨ N = n →
            ltQ (absQ (subQ (f⦅n⦆) L)) ε

    /-- f has a limit in ℚ -/
    def hasLimitQ (f : U) : Prop :=
      ∃ L : U, L ∈ (RatSet : U) ∧ convergesToQ f L

    -- =========================================================================
    -- Section 2: Basic consequences
    -- =========================================================================

    /-- The limit of a convergent sequence is a rational number.
        (The limit L must be given, and f must converge to it.) -/
    theorem convergesToQ_mem_RatSet (f L : U)
        (hL : L ∈ (RatSet : U)) (_h : convergesToQ f L) :
        L ∈ (RatSet : U) := hL

    -- =========================================================================
    -- Section 3: Constant sequence converges
    -- =========================================================================

    /-- The constant sequence at a converges to a -/
    theorem convergesToQ_const (a : U) (ha : a ∈ (RatSet : U)) :
        convergesToQ (constSeqQ a) a := by
      intro ε hε hε_pos
      refine ⟨∅, zero_in_Omega, fun n hn _h_ge => ?_⟩
      rw [constSeqQ_apply a ha n hn]
      -- Goal: ltQ (absQ (subQ a a)) ε
      have h_sub : subQ a a = (zeroQ : U) := by
        show addQ a (negQ a) = zeroQ
        exact negQ_addQ_right a ha
      have h_abs : absQ (zeroQ : U) = (zeroQ : U) :=
        if_pos (leQ_refl (zeroQ : U) zeroQ_mem_RatSet)
      rw [h_sub, h_abs]
      exact hε_pos

    -- =========================================================================
    -- Section 4: Uniqueness of limits
    -- =========================================================================

    /-- Limits are unique: if f → L₁ and f → L₂ then L₁ = L₂. -/
    theorem limit_unique (f L₁ L₂ : U)
        (hf : IsSeqQ f) (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ f L₂) :
        L₁ = L₂ := by
      apply Classical.byContradiction
      intro h_ne
      -- ε₀ = |L₁ − L₂| > 0
      have hL₁L₂ : subQ L₁ L₂ ∈ (RatSet : U) :=
        addQ_in_RatSet L₁ (negQ L₂) hL₁ (negQ_in_RatSet L₂ hL₂)
      have h_sub_ne : subQ L₁ L₂ ≠ (zeroQ : U) := by
        intro h_eq
        apply h_ne
        have step : addQ (addQ L₁ (negQ L₂)) L₂ = addQ (zeroQ : U) L₂ :=
          congrArg (fun x => addQ x L₂) h_eq
        rw [addQ_assoc L₁ (negQ L₂) L₂ hL₁ (negQ_in_RatSet L₂ hL₂) hL₂,
            negQ_addQ_left L₂ hL₂,
            addQ_zero_right L₁ hL₁,
            addQ_zero_left L₂ hL₂] at step
        exact step
      have hε_pos : isPositiveQ (absQ (subQ L₁ L₂)) :=
        absQ_pos (subQ L₁ L₂) hL₁L₂ h_sub_ne
      let ε := absQ (subQ L₁ L₂)
      have hε : ε ∈ (RatSet : U) := absQ_in_RatSet (subQ L₁ L₂) hL₁L₂
      let ε₂ := halfQ ε
      have hε₂ : ε₂ ∈ (RatSet : U) := halfQ_mem_RatSet ε hε
      have hε₂_pos : isPositiveQ ε₂ := halfQ_pos ε hε hε_pos
      -- Get N₁ and N₂
      obtain ⟨N₁, hN₁, h₁'⟩ := h₁ ε₂ hε₂ hε₂_pos
      obtain ⟨N₂, hN₂, h₂'⟩ := h₂ ε₂ hε₂ hε₂_pos
      -- n = max(N₁, N₂) ≥ both thresholds
      let n := maxOf N₁ N₂
      have hn := maxOf_in_Omega N₁ N₂ hN₁ hN₂
      have hn1 := h₁' n hn (le_maxOf_left N₁ N₂ hN₁ hN₂)
      have hn2 := h₂' n hn (le_maxOf_right N₁ N₂ hN₁ hN₂)
      -- f(n) ∈ RatSet
      have hfn : (f⦅n⦆ : U) ∈ (RatSet : U) := seqTermQ_mem_RatSet f n hf hn
      -- Triangle: ε = |L₁−L₂| ≤ |f(n)−L₁| + |f(n)−L₂|
      have h_tri : leQ ε (addQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (f⦅n⦆) L₂))) := by
        have h_tri_sub :=
          absQ_triangle_sub L₁ (f⦅n⦆) L₂ hL₁ hfn hL₂
        -- |L₁ − f(n)| = |f(n) − L₁|
        rwa [absQ_symm L₁ (f⦅n⦆) hL₁ hfn] at h_tri_sub
      -- |f(n)−L₁| + |f(n)−L₂| < ε₂ + ε₂ = ε
      have h_sum_lt :
          ltQ (addQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (f⦅n⦆) L₂))) ε := by
        have h := ltQ_addQ_of_leQ_ltQ
          (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (f⦅n⦆) L₂)) ε₂ ε₂
          (absQ_in_RatSet _ (addQ_in_RatSet (f⦅n⦆) (negQ L₁) hfn (negQ_in_RatSet L₁ hL₁)))
          (absQ_in_RatSet _ (addQ_in_RatSet (f⦅n⦆) (negQ L₂) hfn (negQ_in_RatSet L₂ hL₂)))
          hε₂ hε₂ hn1.1 hn2
        rwa [show addQ ε₂ ε₂ = ε from half_add_half ε hε] at h
      -- leQ ε X and ltQ X ε → ltQ ε ε → contradiction
      exact ltQ_irrefl ε hε (leQ_ltQ_trans ε _ ε hε
        (addQ_in_RatSet _ _ (absQ_in_RatSet _ (addQ_in_RatSet (f⦅n⦆) (negQ L₁) hfn (negQ_in_RatSet L₁ hL₁)))
          (absQ_in_RatSet _ (addQ_in_RatSet (f⦅n⦆) (negQ L₂) hfn (negQ_in_RatSet L₂ hL₂))))
        hε h_tri h_sum_lt)

    -- =========================================================================
    -- Section 5: Subsequences
    -- =========================================================================

    /-- g is a subsequence of f: there exists a strictly increasing function
        φ : ω → ω such that g(n) = f(φ(n)) for all n ∈ ω. -/
    def IsSubseqOf (g f : U) : Prop :=
      ∃ φ : U, IsFunction φ (ω : U) (ω : U) ∧
        (∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) → m ∈ n → (φ⦅m⦆) ∈ (φ⦅n⦆)) ∧
        (∀ n : U, n ∈ (ω : U) → g⦅n⦆ = f⦅φ⦅n⦆⦆)

    /-- Strictly increasing functions φ: ω → ω satisfy φ(n) ≥ n for all n ∈ ω -/
    private theorem strictly_increasing_ge (φ : U)
        (hφ : IsFunction φ (ω : U) (ω : U))
        (hφ_incr : ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) → m ∈ n → (φ⦅m⦆) ∈ (φ⦅n⦆))
        (n : U) (hn : n ∈ (ω : U)) :
        n ∈ (φ⦅n⦆) ∨ n = (φ⦅n⦆) := by
      -- Inducción sobre n ∈ ω usando omega_induction
      apply omega_induction (fun k => k ∈ (φ⦅k⦆) ∨ k = (φ⦅k⦆))
      · -- Caso base: ∅ ∈ φ(∅) ∨ ∅ = φ(∅)
        have hφ0 : (φ⦅∅⦆) ∈ (ω : U) := hφ.2.2.1 ∅ zero_in_Omega
        have h0_nat : IsNat ∅ := mem_Omega_is_Nat ∅ zero_in_Omega
        have hφ0_nat : IsNat (φ⦅∅⦆) := mem_Omega_is_Nat (φ⦅∅⦆) hφ0
        rcases trichotomy ∅ (φ⦅∅⦆) h0_nat hφ0_nat with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · -- φ(∅) ∈ ∅ es imposible
          exfalso
          exact EmptySet_is_empty (φ⦅∅⦆) h
      · -- Caso inductivo: k ∈ φ(k) ∨ k = φ(k) → σ(k) ∈ φ(σ(k)) ∨ σ(k) = φ(σ(k))
        intro k hk hIH
        have hk_nat : IsNat k := mem_Omega_is_Nat k hk
        have hsk : σ k ∈ (ω : U) := succ_in_Omega k hk
        have hsk_nat : IsNat (σ k) := mem_Omega_is_Nat (σ k) hsk
        have hφk : (φ⦅k⦆) ∈ (ω : U) := hφ.2.2.1 k hk
        have hφsk : (φ⦅σ k⦆) ∈ (ω : U) := hφ.2.2.1 (σ k) hsk
        have hφk_nat : IsNat (φ⦅k⦆) := mem_Omega_is_Nat (φ⦅k⦆) hφk
        have hφsk_nat : IsNat (φ⦅σ k⦆) := mem_Omega_is_Nat (φ⦅σ k⦆) hφsk
        -- φ es estrictamente creciente: k ∈ σ(k) → φ(k) ∈ φ(σ(k))
        have h_incr : (φ⦅k⦆) ∈ (φ⦅σ k⦆) := hφ_incr k (σ k) hk hsk (mem_succ_self k)
        -- Por IH: k ∈ φ(k) ∨ k = φ(k)
        cases hIH with
        | inl hk_in_φk =>
          -- k ∈ φ(k) ∈ φ(σ(k)), así k ∈ φ(σ(k)) por transitividad
          have hk_in_φsk : k ∈ (φ⦅σ k⦆) :=
            mem_trans k (φ⦅k⦆) (φ⦅σ k⦆) hk_nat hφk_nat hφsk_nat hk_in_φk h_incr
          -- σ(k) = k ∪ {k}, así σ(k) ⊆ φ(σ(k)) si k ∈ φ(σ(k))
          have hsk_sub : σ k ⊆ (φ⦅σ k⦆) := by
            intro x hx
            rw [mem_succ_iff] at hx
            cases hx with
            | inl hx_in_k =>
              -- x ∈ k ∈ φ(k) ∈ φ(σ(k)), así x ∈ φ(σ(k)) por transitividad doble
              have hx_in_φk : x ∈ (φ⦅k⦆) :=
                transitive_element_subset k x hk_nat hx_in_k (φ⦅k⦆) hk_in_φk
              exact transitive_element_subset (φ⦅k⦆) x hφk_nat hx_in_φk (φ⦅σ k⦆) h_incr
            | inr hx_eq_k =>
              rw [hx_eq_k]
              exact hk_in_φsk
          -- Por nat_subset_mem_or_eq: σ(k) ⊆ φ(σ(k)) → σ(k) ∈ φ(σ(k)) ∨ σ(k) = φ(σ(k))
          exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆) hsk_nat hφsk_nat hsk_sub
        | inr hk_eq_φk =>
          -- k = φ(k), así φ(k) ∈ φ(σ(k)) se convierte en k ∈ φ(σ(k))
          have hk_in_φsk : k ∈ (φ⦅σ k⦆) := hk_eq_φk ▸ h_incr
          -- Mismo argumento que arriba
          have hsk_sub : σ k ⊆ (φ⦅σ k⦆) := by
            intro x hx
            rw [mem_succ_iff] at hx
            cases hx with
            | inl hx_in_k =>
              have hx_in_φk : x ∈ (φ⦅k⦆) :=
                transitive_element_subset k x hk_nat hx_in_k (φ⦅k⦆) (hk_eq_φk.symm ▸ hk_in_φsk)
              rw [← hk_eq_φk] at hx_in_φk
              exact transitive_element_subset k x hk_nat hx_in_k (φ⦅σ k⦆) hk_in_φsk
            | inr hx_eq_k =>
              rw [hx_eq_k]
              exact hk_in_φsk
          exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆) hsk_nat hφsk_nat hsk_sub
      · exact hn

    /-- Every subsequence of a convergent sequence converges to the same limit.
        Proof sketch: given ε > 0, let N be the threshold from f → L.
        Since φ is strictly increasing we have φ(n) ≥ n for all n ∈ ω
        (proved by induction: φ(0) ≥ 0 trivially; φ(n+1) > φ(n) ≥ n implies φ(n+1) ≥ n+1).
        So for n ≥ N we get φ(n) ≥ n ≥ N, hence |g(n) − L| = |f(φ(n)) − L| < ε. -/
    theorem subseq_convergent (f g L : U)
        (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hconv : convergesToQ f L) (hsub : IsSubseqOf g f) :
        convergesToQ g L := by
      obtain ⟨φ, hφ_fn, hφ_incr, hg_eq⟩ := hsub
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := hconv ε hε hε_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      rw [hg_eq n hn]
      have hφn : (φ⦅n⦆) ∈ (ω : U) := hφ_fn.2.2.1 n hn
      -- Necesitamos N ≤ φ(n), es decir, N ∈ φ(n) ∨ N = φ(n)
      -- Por strictly_increasing_ge: n ≤ φ(n)
      -- Por transitividad: N ≤ n ≤ φ(n) implica N ≤ φ(n)
      have hN_φn : N ∈ (φ⦅n⦆) ∨ N = (φ⦅n⦆) := by
        have hφn_ge_n := strictly_increasing_ge φ hφ_fn hφ_incr n hn
        exact omega_le_trans N n (φ⦅n⦆) hN hn hφn h_ge hφn_ge_n
      exact hN_conv (φ⦅n⦆) hφn hN_φn

    -- =========================================================================
    -- Section 5: Arithmetic of limits
    -- =========================================================================

    /-- If f → L₁ and g → L₂ then (f + g) → L₁ + L₂. -/
    theorem convergesToQ_add (f g L₁ L₂ : U)
        (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ g L₂) :
        convergesToQ (addSeqQ f g) (addQ L₁ L₂) := by
      intro ε hε hε_pos
      let ε₂ := halfQ ε
      have hε₂ : ε₂ ∈ (RatSet : U) := halfQ_mem_RatSet ε hε
      have hε₂_pos : isPositiveQ ε₂ := halfQ_pos ε hε hε_pos
      -- Get thresholds N₁, N₂ for f and g
      obtain ⟨N₁, hN₁, h₁'⟩ := h₁ ε₂ hε₂ hε₂_pos
      obtain ⟨N₂, hN₂, h₂'⟩ := h₂ ε₂ hε₂ hε₂_pos
      let N := maxOf N₁ N₂
      have hN := maxOf_in_Omega N₁ N₂ hN₁ hN₂
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      -- N₁ ≤ N ≤ n and N₂ ≤ N ≤ n
      have hN1n : N₁ ∈ n ∨ N₁ = n :=
        omega_le_trans N₁ N n hN₁ hN hn (le_maxOf_left N₁ N₂ hN₁ hN₂) h_ge
      have hN2n : N₂ ∈ n ∨ N₂ = n :=
        omega_le_trans N₂ N n hN₂ hN hn (le_maxOf_right N₁ N₂ hN₁ hN₂) h_ge
      have hn1 := h₁' n hn hN1n  -- ltQ |f(n)−L₁| ε₂
      have hn2 := h₂' n hn hN2n  -- ltQ |g(n)−L₂| ε₂
      have hfn : (f⦅n⦆ : U) ∈ (RatSet : U) := seqTermQ_mem_RatSet f n hf hn
      have hgn : (g⦅n⦆ : U) ∈ (RatSet : U) := seqTermQ_mem_RatSet g n hg hn
      -- Goal: ltQ (absQ (subQ ((addSeqQ f g)⦅n⦆) (addQ L₁ L₂))) ε
      rw [addSeqQ_apply f g hf hg n hn]
      -- negQ (L₁+L₂) = negQ L₁ + negQ L₂ (distributivity of negation)
      have negQ_distrib : negQ (addQ L₁ L₂) = addQ (negQ L₁) (negQ L₂) := by
        have hNL₁ := negQ_in_RatSet L₁ hL₁
        have hNL₂ := negQ_in_RatSet L₂ hL₂
        have hL₁L₂ := addQ_in_RatSet L₁ L₂ hL₁ hL₂
        have hNL₁L₂ := negQ_in_RatSet (addQ L₁ L₂) hL₁L₂
        have hNL₁NL₂ := addQ_in_RatSet (negQ L₁) (negQ L₂) hNL₁ hNL₂
        have sum_inv : addQ (addQ (negQ L₁) (negQ L₂)) (addQ L₁ L₂) = zeroQ := by
          rw [addQ_assoc (negQ L₁) (negQ L₂) (addQ L₁ L₂) hNL₁ hNL₂ hL₁L₂,
              ← addQ_assoc (negQ L₂) L₁ L₂ hNL₂ hL₁ hL₂,
              addQ_comm (negQ L₂) L₁ hNL₂ hL₁,
              addQ_assoc L₁ (negQ L₂) L₂ hL₁ hNL₂ hL₂,
              negQ_addQ_left L₂ hL₂, addQ_zero_right L₁ hL₁,
              negQ_addQ_left L₁ hL₁]
        symm
        calc addQ (negQ L₁) (negQ L₂)
            = addQ (addQ (negQ L₁) (negQ L₂)) zeroQ :=
                  (addQ_zero_right (addQ (negQ L₁) (negQ L₂)) hNL₁NL₂).symm
          _ = addQ (addQ (negQ L₁) (negQ L₂)) (addQ (addQ L₁ L₂) (negQ (addQ L₁ L₂))) :=
                  congrArg (addQ (addQ (negQ L₁) (negQ L₂)))
                    (negQ_addQ_right (addQ L₁ L₂) hL₁L₂).symm
          _ = addQ (addQ (addQ (negQ L₁) (negQ L₂)) (addQ L₁ L₂)) (negQ (addQ L₁ L₂)) :=
                  (addQ_assoc (addQ (negQ L₁) (negQ L₂)) (addQ L₁ L₂) (negQ (addQ L₁ L₂))
                    hNL₁NL₂ hL₁L₂ hNL₁L₂).symm
          _ = addQ zeroQ (negQ (addQ L₁ L₂)) :=
                  congrArg (fun x => addQ x (negQ (addQ L₁ L₂))) sum_inv
          _ = negQ (addQ L₁ L₂) :=
                  addQ_zero_left (negQ (addQ L₁ L₂)) hNL₁L₂
      -- subQ (f(n)+g(n)) (L₁+L₂) = (f(n)−L₁) + (g(n)−L₂)
      have h_sub_eq : subQ (addQ (f⦅n⦆) (g⦅n⦆)) (addQ L₁ L₂) =
          addQ (subQ (f⦅n⦆) L₁) (subQ (g⦅n⦆) L₂) :=
        calc addQ (addQ (f⦅n⦆) (g⦅n⦆)) (negQ (addQ L₁ L₂))
            = addQ (f⦅n⦆) (addQ (g⦅n⦆) (negQ (addQ L₁ L₂))) := by
                rw [addQ_assoc (f⦅n⦆) (g⦅n⦆) (negQ (addQ L₁ L₂)) hfn hgn
                      (negQ_in_RatSet (addQ L₁ L₂) (addQ_in_RatSet L₁ L₂ hL₁ hL₂))]
          _ = addQ (f⦅n⦆) (addQ (g⦅n⦆) (addQ (negQ L₁) (negQ L₂))) :=
                congrArg (fun x => addQ (f⦅n⦆) (addQ (g⦅n⦆) x)) negQ_distrib
          _ = addQ (addQ (f⦅n⦆) (negQ L₁)) (addQ (g⦅n⦆) (negQ L₂)) := by
                rw [← addQ_assoc (g⦅n⦆) (negQ L₁) (negQ L₂) hgn (negQ_in_RatSet L₁ hL₁) (negQ_in_RatSet L₂ hL₂),
                    addQ_comm (g⦅n⦆) (negQ L₁) hgn (negQ_in_RatSet L₁ hL₁),
                    addQ_assoc (negQ L₁) (g⦅n⦆) (negQ L₂) (negQ_in_RatSet L₁ hL₁) hgn (negQ_in_RatSet L₂ hL₂),
                    ← addQ_assoc (f⦅n⦆) (negQ L₁) (addQ (g⦅n⦆) (negQ L₂)) hfn (negQ_in_RatSet L₁ hL₁)
                      (addQ_in_RatSet (g⦅n⦆) (negQ L₂) hgn (negQ_in_RatSet L₂ hL₂))]
      have hfnL₁ : subQ (f⦅n⦆) L₁ ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅n⦆) (negQ L₁) hfn (negQ_in_RatSet L₁ hL₁)
      have hgnL₂ : subQ (g⦅n⦆) L₂ ∈ (RatSet : U) :=
        addQ_in_RatSet (g⦅n⦆) (negQ L₂) hgn (negQ_in_RatSet L₂ hL₂)
      rw [h_sub_eq]
      -- |a + b| ≤ |a| + |b|
      have h_tri : leQ (absQ (addQ (subQ (f⦅n⦆) L₁) (subQ (g⦅n⦆) L₂)))
          (addQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (g⦅n⦆) L₂))) :=
        absQ_triangle (subQ (f⦅n⦆) L₁) (subQ (g⦅n⦆) L₂) hfnL₁ hgnL₂
      -- |f(n)−L₁| + |g(n)−L₂| < ε₂ + ε₂ = ε
      have h_sum_lt : ltQ (addQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (g⦅n⦆) L₂))) ε := by
        have h := ltQ_addQ_of_leQ_ltQ
          (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (g⦅n⦆) L₂)) ε₂ ε₂
          (absQ_in_RatSet _ hfnL₁) (absQ_in_RatSet _ hgnL₂) hε₂ hε₂ hn1.1 hn2
        rwa [show addQ ε₂ ε₂ = ε from half_add_half ε hε] at h
      exact leQ_ltQ_trans (absQ (addQ (subQ (f⦅n⦆) L₁) (subQ (g⦅n⦆) L₂)))
        (addQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (subQ (g⦅n⦆) L₂))) ε
        (absQ_in_RatSet _ (addQ_in_RatSet _ _ hfnL₁ hgnL₂))
        (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfnL₁) (absQ_in_RatSet _ hgnL₂))
        hε h_tri h_sum_lt

    /-- If f → 0 then (f · g) → 0, provided g is bounded. -/
    theorem convergesToQ_mul_bounded (f g : U)
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (hf_zero : convergesToQ f (zeroQ : U))
        (hg_bounded : ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
          ∀ n : U, n ∈ (ω : U) → leQ (absQ (g⦅n⦆)) M) :
        convergesToQ (mulSeqQ f g) (zeroQ : U) := by
      obtain ⟨M, hM, hM_pos, hM_bound⟩ := hg_bounded
      intro ε hε hε_pos
      -- Tomar ε' = ε / M > 0
      let ε' := divQ ε M
      have hε' : ε' ∈ (RatSet : U) := divQ_in_RatSet ε M hε hM
      have hε'_pos : isPositiveQ ε' := by
        constructor
        · exact divQ_pos_of_pos_pos ε M hε hM hε_pos hM_pos
        · intro h_eq
          have := divQ_eq_zero_iff ε M hε hM |>.mp h_eq
          exact hε_pos.2 this
      -- Obtener N tal que |f(n)| < ε' para n ≥ N
      obtain ⟨N, hN, hN_conv⟩ := hf_zero ε' hε' hε'_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hfn := seqTermQ_mem_RatSet f n hf hn
      have hgn := seqTermQ_mem_RatSet g n hg hn
      -- Goal: |f(n)·g(n) - 0| < ε
      rw [mulSeqQ_apply f g hf hg n hn]
      have h_sub : subQ (mulQ (f⦅n⦆) (g⦅n⦆)) (zeroQ : U) = mulQ (f⦅n⦆) (g⦅n⦆) := by
        show addQ (mulQ (f⦅n⦆) (g⦅n⦆)) (negQ zeroQ) = mulQ (f⦅n⦆) (g⦅n⦆)
        rw [negQ_zero, addQ_zero_right (mulQ (f⦅n⦆) (g⦅n⦆)) (mulQ_in_RatSet (f⦅n⦆) (g⦅n⦆) hfn hgn)]
      rw [h_sub]
      -- |f(n)·g(n)| = |f(n)|·|g(n)| ≤ |f(n)|·M < ε'·M = ε
      have h_abs_mul : absQ (mulQ (f⦅n⦆) (g⦅n⦆)) = mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆)) :=
        absQ_mulQ (f⦅n⦆) (g⦅n⦆) hfn hgn
      rw [h_abs_mul]
      -- |f(n) - 0| < ε'
      have hfn_lt : ltQ (absQ (subQ (f⦅n⦆) zeroQ)) ε' := hN_conv n hn h_ge
      have h_sub_fn : subQ (f⦅n⦆) (zeroQ : U) = (f⦅n⦆) := by
        show addQ (f⦅n⦆) (negQ zeroQ) = (f⦅n⦆)
        rw [negQ_zero, addQ_zero_right (f⦅n⦆) hfn]
      rw [h_sub_fn] at hfn_lt
      -- |g(n)| ≤ M
      have hgn_le : leQ (absQ (g⦅n⦆)) M := hM_bound n hn
      -- |f(n)|·|g(n)| ≤ ε'·M
      have h_prod_le : leQ (mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆))) (mulQ ε' M) := by
        have habs_fn := absQ_in_RatSet (f⦅n⦆) hfn
        have habs_gn := absQ_in_RatSet (g⦅n⦆) hgn
        -- |f(n)| < ε' implica |f(n)| ≤ ε'
        have hfn_le : leQ (absQ (f⦅n⦆)) ε' := hfn_lt.1
        -- Multiplicar por |g(n)| ≥ 0: |f(n)|·|g(n)| ≤ ε'·|g(n)|
        have h1 : leQ (mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆))) (mulQ ε' (absQ (g⦅n⦆))) :=
          mulQ_leQ_mulQ_of_nonneg_right (absQ (f⦅n⦆)) ε' (absQ (g⦅n⦆))
            habs_fn hε' habs_gn hfn_le (absQ_nonneg (g⦅n⦆) hgn)
        -- |g(n)| ≤ M implica ε'·|g(n)| ≤ ε'·M
        have h2 : leQ (mulQ ε' (absQ (g⦅n⦆))) (mulQ ε' M) :=
          mulQ_leQ_mulQ_of_nonneg_left ε' (absQ (g⦅n⦆)) M
            hε' habs_gn hM (hM_bound n hn) hε'_pos.1
        -- Transitividad
        exact leQ_trans (mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆)))
                (mulQ ε' (absQ (g⦅n⦆))) (mulQ ε' M)
                (mulQ_in_RatSet (absQ (f⦅n⦆)) (absQ (g⦅n⦆)) habs_fn habs_gn)
                (mulQ_in_RatSet ε' (absQ (g⦅n⦆)) hε' habs_gn)
                (mulQ_in_RatSet ε' M hε' hM) h1 h2
      -- ε'·M = ε
      have h_eq_ε : mulQ ε' M = ε := by
        unfold ε'
        exact divQ_mul_cancel ε M hε hM hM_pos.2.symm
      rw [h_eq_ε] at h_prod_le
      exact leQ_ltQ_trans (mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆))) ε ε
        (mulQ_in_RatSet (absQ (f⦅n⦆)) (absQ (g⦅n⦆))
          (absQ_in_RatSet (f⦅n⦆) hfn) (absQ_in_RatSet (g⦅n⦆) hgn))
        hε hε h_prod_le (ltQ_irrefl ε hε |> False.elim)

  end Rat.Convergence

end ZFC

export ZFC.Rat.Convergence (
  convergesToQ
  hasLimitQ
  IsSubseqOf
  convergesToQ_const
  limit_unique
  subseq_convergent
  convergesToQ_add
  convergesToQ_mul_bounded
)
