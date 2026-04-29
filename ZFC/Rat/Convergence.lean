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
      have φ_mem : ∀ k, k ∈ (ω : U) → (φ⦅k⦆) ∈ (ω : U) := by
        intro k hk
        have h_unique := hφ.2 k hk
        have h_pair := apply_mem φ k h_unique
        exact ((OrderedPair_mem_CartesianProduct k (φ⦅k⦆) (ω : U) (ω : U)).mp
                (hφ.1 _ h_pair)).2
      let P := fun k : U => k ∈ (φ⦅k⦆) ∨ k = (φ⦅k⦆)
      have hS_eq : sep (ω : U) P = (ω : U) := by
        apply induction_principle
        · intro x hx; exact ((mem_sep_iff (ω : U) x P).mp hx).1
        · rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ?_⟩
          have hφ0 : (φ⦅(∅ : U)⦆) ∈ (ω : U) := φ_mem (∅ : U) zero_in_Omega
          have h0_nat : IsNat (∅ : U) := mem_Omega_is_Nat (∅ : U) zero_in_Omega
          have hφ0_nat : IsNat (φ⦅(∅ : U)⦆) := mem_Omega_is_Nat _ hφ0
          rcases trichotomy (∅ : U) (φ⦅(∅ : U)⦆) h0_nat hφ0_nat with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h (EmptySet_is_empty _)
        · intro k hk_S
          have hk_mem := (mem_sep_iff (ω : U) k P).mp hk_S
          have hk : k ∈ (ω : U) := hk_mem.1
          have hIH := hk_mem.2
          have hk_nat : IsNat k := mem_Omega_is_Nat k hk
          have hsk : σ k ∈ (ω : U) := succ_in_Omega k hk
          have hsk_nat : IsNat (σ k) := mem_Omega_is_Nat (σ k) hsk
          have hφk : (φ⦅k⦆) ∈ (ω : U) := φ_mem k hk
          have hφsk : (φ⦅σ k⦆) ∈ (ω : U) := φ_mem (σ k) hsk
          have hφk_nat : IsNat (φ⦅k⦆) := mem_Omega_is_Nat (φ⦅k⦆) hφk
          have hφsk_nat : IsNat (φ⦅σ k⦆) := mem_Omega_is_Nat (φ⦅σ k⦆) hφsk
          have h_incr : (φ⦅k⦆) ∈ (φ⦅σ k⦆) := hφ_incr k (σ k) hk hsk (mem_succ_self k)
          rw [mem_sep_iff]; refine ⟨hsk, ?_⟩
          cases hIH with
          | inl hk_in_φk =>
            have hk_in_φsk : k ∈ (φ⦅σ k⦆) :=
              mem_trans k (φ⦅k⦆) (φ⦅σ k⦆) hk_nat hφk_nat hφsk_nat hk_in_φk h_incr
            exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆) hsk_nat hφsk_nat (fun x hx => by
              rw [mem_succ_iff] at hx
              cases hx with
              | inl hx_in_k =>
                exact transitive_element_subset (φ⦅σ k⦆) (φ⦅k⦆) hφsk_nat.1 h_incr x
                  (transitive_element_subset (φ⦅k⦆) k hφk_nat.1 hk_in_φk x hx_in_k)
              | inr hx_eq_k => rw [hx_eq_k]; exact hk_in_φsk)
          | inr hk_eq_φk =>
            have hk_in_φsk : k ∈ (φ⦅σ k⦆) := by
              have h := h_incr; rw [← hk_eq_φk] at h; exact h
            exact nat_subset_mem_or_eq (σ k) (φ⦅σ k⦆) hsk_nat hφsk_nat (fun x hx => by
              rw [mem_succ_iff] at hx
              cases hx with
              | inl hx_in_k =>
                exact transitive_element_subset (φ⦅σ k⦆) k hφsk_nat.1 hk_in_φsk x hx_in_k
              | inr hx_eq_k => rw [hx_eq_k]; exact hk_in_φsk)
      have hn_S : n ∈ sep (ω : U) P := by rw [hS_eq]; exact hn
      exact ((mem_sep_iff (ω : U) n P).mp hn_S).2

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
      have hφn : (φ⦅n⦆) ∈ (ω : U) := by
        have h_unique := hφ_fn.2 n hn
        have h_pair := apply_mem φ n h_unique
        exact ((OrderedPair_mem_CartesianProduct n (φ⦅n⦆) (ω : U) (ω : U)).mp
                (hφ_fn.1 _ h_pair)).2
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
      -- ε'·M = ε  (needed for positivity proof and final step)
      have h_eq_ε : mulQ ε' M = ε := divQ_mulQ_cancel ε M hε hM hM_pos.2.symm
      have hε'_pos : isPositiveQ ε' := by
        constructor
        · -- leQ zeroQ ε': if ε' ≤ 0 then ε'·M ≤ 0·M = 0 < ε, contradiction
          rcases leQ_total (zeroQ : U) ε' zeroQ_mem_RatSet hε' with h | h
          · exact h
          · exfalso
            have h1 : leQ (mulQ ε' M) (mulQ (zeroQ : U) M) :=
              mulQ_leQ_mulQ_of_nonneg_right ε' (zeroQ : U) M hε' zeroQ_mem_RatSet hM h hM_pos.1
            rw [mulQ_zero_left M hM, h_eq_ε] at h1
            exact hε_pos.2 (leQ_antisymm ε (zeroQ : U) hε zeroQ_mem_RatSet h1 hε_pos.1).symm
        · intro h_eq
          have h1 : mulQ ε' M = (zeroQ : U) := by
            rw [show ε' = (zeroQ : U) from h_eq.symm]; exact mulQ_zero_left M hM
          exact hε_pos.2 (h_eq_ε.symm.trans h1).symm
      -- Obtener N tal que |f(n)| < ε' para n ≥ N
      obtain ⟨N, hN, hN_conv⟩ := hf_zero ε' hε' hε'_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hfn := seqTermQ_mem_RatSet f n hf hn
      have hgn := seqTermQ_mem_RatSet g n hg hn
      rw [mulSeqQ_apply f g hf hg n hn]
      have h_sub : subQ (mulQ (f⦅n⦆) (g⦅n⦆)) (zeroQ : U) = mulQ (f⦅n⦆) (g⦅n⦆) := by
        show addQ (mulQ (f⦅n⦆) (g⦅n⦆)) (negQ zeroQ) = mulQ (f⦅n⦆) (g⦅n⦆)
        rw [negQ_zero, addQ_zero_right (mulQ (f⦅n⦆) (g⦅n⦆)) (mulQ_in_RatSet (f⦅n⦆) (g⦅n⦆) hfn hgn)]
      rw [h_sub, absQ_mulQ (f⦅n⦆) (g⦅n⦆) hfn hgn]
      -- |f(n) - 0| = |f(n)| < ε'
      have hfn_lt : ltQ (absQ (f⦅n⦆)) ε' := by
        have h := hN_conv n hn h_ge
        rwa [show subQ (f⦅n⦆) (zeroQ : U) = f⦅n⦆ from by
          show addQ (f⦅n⦆) (negQ zeroQ) = f⦅n⦆
          rw [negQ_zero, addQ_zero_right (f⦅n⦆) hfn]] at h
      have hgn_le : leQ (absQ (g⦅n⦆)) M := hM_bound n hn
      have habs_fn := absQ_in_RatSet (f⦅n⦆) hfn
      have habs_gn := absQ_in_RatSet (g⦅n⦆) hgn
      -- |f(n)|·M < ε'·M = ε  (strict because |f(n)| < ε' and M ≠ 0)
      have h_fn_M_lt : ltQ (mulQ (absQ (f⦅n⦆)) M) ε := by
        have h_le : leQ (mulQ (absQ (f⦅n⦆)) M) (mulQ ε' M) :=
          mulQ_leQ_mulQ_of_nonneg_right (absQ (f⦅n⦆)) ε' M habs_fn hε' hM hfn_lt.1 hM_pos.1
        have h_ne : mulQ (absQ (f⦅n⦆)) M ≠ mulQ ε' M := fun h_eq =>
          hfn_lt.2 (mulQ_right_cancel (absQ (f⦅n⦆)) ε' M habs_fn hε' hM hM_pos.2.symm h_eq)
        rw [h_eq_ε] at h_le h_ne
        exact ⟨h_le, h_ne⟩
      -- |f(n)|·|g(n)| ≤ |f(n)|·M < ε
      exact leQ_ltQ_trans (mulQ (absQ (f⦅n⦆)) (absQ (g⦅n⦆))) (mulQ (absQ (f⦅n⦆)) M) ε
        (mulQ_in_RatSet _ _ habs_fn habs_gn) (mulQ_in_RatSet _ _ habs_fn hM) hε
        (mulQ_leQ_mulQ_of_nonneg_left (absQ (f⦅n⦆)) (absQ (g⦅n⦆)) M
          habs_fn habs_gn hM hgn_le (absQ_nonneg (f⦅n⦆) hfn))
        h_fn_M_lt

    -- =========================================================================
    -- Section 6: Further limit arithmetic
    -- =========================================================================

    /-- If f → L then (−f) → −L. -/
    private theorem convergesToQ_neg (f L : U)
        (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f)
        (h : convergesToQ f L) :
        convergesToQ (negSeqQ f) (negQ L) := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := h ε hε hε_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      rw [negSeqQ_apply f hf n hn]
      have hfn  := seqTermQ_mem_RatSet f n hf hn
      have hnfn := negQ_in_RatSet (f⦅n⦆) hfn
      -- |(−f(n)) − (−L)| = |negQ f(n) + negQ(negQ L)| = |negQ f(n) + L|
      --                   = |L + negQ f(n)| = |subQ L f(n)| = |subQ f(n) L|
      have h_eq : absQ (subQ (negQ (f⦅n⦆)) (negQ L)) = absQ (subQ (f⦅n⦆) L) := by
        show absQ (addQ (negQ (f⦅n⦆)) (negQ (negQ L))) = absQ (addQ (f⦅n⦆) (negQ L))
        rw [negQ_negQ L hL, addQ_comm (negQ (f⦅n⦆)) L hnfn hL]
        exact absQ_symm L (f⦅n⦆) hL hfn
      rw [h_eq]
      exact hN_conv n hn h_ge

    /-- If f → L₁ and g → L₂ then (f − g) → L₁ − L₂. -/
    theorem convergesToQ_sub (f g L₁ L₂ : U)
        (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ g L₂) :
        convergesToQ (addSeqQ f (negSeqQ g)) (subQ L₁ L₂) :=
      convergesToQ_add f (negSeqQ g) L₁ (negQ L₂)
        hL₁ (negQ_in_RatSet L₂ hL₂) hf (negSeqQ_isSeqQ g hg) h₁
        (convergesToQ_neg g L₂ hL₂ hg h₂)

    /-- If |f(n) − L| ≤ g(n) for all n and g → 0, then f → L. -/
    theorem convergesToQ_of_dominated (f g L : U)
        (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h_dom : ∀ n : U, n ∈ (ω : U) → leQ (absQ (subQ (f⦅n⦆) L)) (g⦅n⦆))
        (h_g : convergesToQ g (zeroQ : U)) :
        convergesToQ f L := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := h_g ε hε hε_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hfn    := seqTermQ_mem_RatSet f n hf hn
      have hgn    := seqTermQ_mem_RatSet g n hg hn
      have habs   := absQ_in_RatSet (subQ (f⦅n⦆) L)
                       (addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL))
      -- g(n) ≥ 0 since it dominates an absolute value
      have h_gn_nn : leQ (zeroQ : U) (g⦅n⦆) :=
        leQ_trans zeroQ _ (g⦅n⦆) zeroQ_mem_RatSet habs hgn
          (absQ_nonneg _ (addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)))
          (h_dom n hn)
      -- |g(n) − 0| = g(n) < ε
      have h_gn_lt : ltQ (g⦅n⦆) ε := by
        have h := hN_conv n hn h_ge
        rw [show subQ (g⦅n⦆) (zeroQ : U) = g⦅n⦆ from by
              show addQ (g⦅n⦆) (negQ (zeroQ : U)) = g⦅n⦆
              rw [negQ_zero, addQ_zero_right (g⦅n⦆) hgn],
            show absQ (g⦅n⦆) = g⦅n⦆ from if_pos h_gn_nn] at h
        exact h
      exact leQ_ltQ_trans (absQ (subQ (f⦅n⦆) L)) (g⦅n⦆) ε habs hgn hε
        (h_dom n hn) h_gn_lt

    -- =========================================================================
    -- Section 7: Squeeze theorem and eventual equality
    -- =========================================================================

    /-- x ≤ |x| for any rational x -/
    private theorem leQ_le_absQ (x : U) (hx : x ∈ (RatSet : U)) : leQ x (absQ x) := by
      by_cases h : leQ (zeroQ : U) x
      · rw [show absQ x = x from if_pos h]; exact leQ_refl x hx
      · rw [show absQ x = negQ x from if_neg h]
        rcases leQ_total (zeroQ : U) x zeroQ_mem_RatSet hx with h_ge | h_le
        · exact absurd h_ge h
        · have h_nonneg : leQ (zeroQ : U) (negQ x) := by
            have := addQ_leQ_addQ x zeroQ (negQ x)
              hx zeroQ_mem_RatSet (negQ_in_RatSet x hx) h_le
            rwa [negQ_addQ_right x hx, addQ_zero_left (negQ x) (negQ_in_RatSet x hx)] at this
          exact leQ_trans x zeroQ (negQ x) hx zeroQ_mem_RatSet (negQ_in_RatSet x hx)
            h_le h_nonneg

    /-- Negation reverses ≤: x ≤ y → −y ≤ −x -/
    private theorem negQ_anti (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h : leQ x y) : leQ (negQ y) (negQ x) := by
      have hnx := negQ_in_RatSet x hx
      have hny := negQ_in_RatSet y hy
      have h1 := addQ_leQ_addQ x y (negQ x) hx hy hnx h
      rw [negQ_addQ_right x hx] at h1
      have h2 := addQ_leQ_addQ zeroQ (addQ y (negQ x)) (negQ y)
        zeroQ_mem_RatSet (addQ_in_RatSet y (negQ x) hy hnx) hny h1
      rw [addQ_zero_left (negQ y) hny,
          addQ_comm y (negQ x) hy hnx,
          addQ_assoc (negQ x) y (negQ y) hnx hy hny,
          negQ_addQ_right y hy,
          addQ_zero_right (negQ x) hnx] at h2
      exact h2

    /-- Adding −L preserves ≤: x ≤ y → x − L ≤ y − L -/
    private theorem subQ_leQ_subQ (x y L : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) (hL : L ∈ (RatSet : U))
        (h : leQ x y) : leQ (subQ x L) (subQ y L) :=
      addQ_leQ_addQ x y (negQ L) hx hy (negQ_in_RatSet L hL) h

    /-- If −ε < x < ε then |x| < ε. -/
    private theorem absQ_lt_of_bounds (x ε : U)
        (hx : x ∈ (RatSet : U)) (hε : ε ∈ (RatSet : U))
        (h_lo : ltQ (negQ ε) x) (h_hi : ltQ x ε) : ltQ (absQ x) ε := by
      by_cases h : leQ (zeroQ : U) x
      · rwa [show absQ x = x from if_pos h]
      · rw [show absQ x = negQ x from if_neg h]
        -- negQ x < ε: negate h_lo to get negQ x < negQ (negQ ε) = ε
        constructor
        · have := negQ_anti (negQ ε) x (negQ_in_RatSet ε hε) hx h_lo.1
          rwa [negQ_negQ ε hε] at this
        · intro h_eq  -- h_eq : negQ x = ε
          exact h_lo.2 (by rw [← negQ_negQ x hx, h_eq])

    /-- a(n) ≤ f(n) ≤ b(n), a → L, b → L implies f → L. -/
    theorem squeeze_theorem (a f b L : U)
        (hL : L ∈ (RatSet : U)) (ha : IsSeqQ a) (hf : IsSeqQ f) (hb : IsSeqQ b)
        (h_af : ∀ n : U, n ∈ (ω : U) → leQ (a⦅n⦆) (f⦅n⦆))
        (h_fb : ∀ n : U, n ∈ (ω : U) → leQ (f⦅n⦆) (b⦅n⦆))
        (h_a : convergesToQ a L) (h_b : convergesToQ b L) :
        convergesToQ f L := by
      intro ε hε hε_pos
      obtain ⟨Na, hNa, hNa_conv⟩ := h_a ε hε hε_pos
      obtain ⟨Nb, hNb, hNb_conv⟩ := h_b ε hε hε_pos
      let N := maxOf Na Nb
      have hN := maxOf_in_Omega Na Nb hNa hNb
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hNa_n := omega_le_trans Na N n hNa hN hn (le_maxOf_left Na Nb hNa hNb) h_ge
      have hNb_n := omega_le_trans Nb N n hNb hN hn (le_maxOf_right Na Nb hNa hNb) h_ge
      have han  := hNa_conv n hn hNa_n
      have hbn  := hNb_conv n hn hNb_n
      have hfn  := seqTermQ_mem_RatSet f n hf hn
      have han_r := seqTermQ_mem_RatSet a n ha hn
      have hbn_r := seqTermQ_mem_RatSet b n hb hn
      have hnL  := negQ_in_RatSet L hL
      have hfnL := addQ_in_RatSet (f⦅n⦆) (negQ L) hfn hnL
      have hanL := addQ_in_RatSet (a⦅n⦆) (negQ L) han_r hnL
      have hbnL := addQ_in_RatSet (b⦅n⦆) (negQ L) hbn_r hnL
      -- a(n)−L ≤ f(n)−L ≤ b(n)−L
      have h_a_le : leQ (subQ (a⦅n⦆) L) (subQ (f⦅n⦆) L) :=
        subQ_leQ_subQ (a⦅n⦆) (f⦅n⦆) L han_r hfn hL (h_af n hn)
      have h_le_b : leQ (subQ (f⦅n⦆) L) (subQ (b⦅n⦆) L) :=
        subQ_leQ_subQ (f⦅n⦆) (b⦅n⦆) L hfn hbn_r hL (h_fb n hn)
      -- b(n)−L ≤ |b(n)−L| < ε, so b(n)−L < ε
      have hbnL_lt : ltQ (subQ (b⦅n⦆) L) ε :=
        leQ_ltQ_trans (subQ (b⦅n⦆) L) (absQ (subQ (b⦅n⦆) L)) ε hbnL
          (absQ_in_RatSet _ hbnL) hε (leQ_le_absQ _ hbnL) hbn
      -- negQ (a(n)−L) ≤ |a(n)−L| < ε, so negQ ε < a(n)−L
      have hanL_neg_lt : ltQ (negQ ε) (subQ (a⦅n⦆) L) := by
        have h_neg_le : leQ (negQ (subQ (a⦅n⦆) L)) (absQ (subQ (a⦅n⦆) L)) := by
          rw [← absQ_negQ (subQ (a⦅n⦆) L) hanL]
          exact leQ_le_absQ (negQ (subQ (a⦅n⦆) L)) (negQ_in_RatSet _ hanL)
        have h_neg_lt : ltQ (negQ (subQ (a⦅n⦆) L)) ε :=
          leQ_ltQ_trans _ _ ε (negQ_in_RatSet _ hanL) (absQ_in_RatSet _ hanL) hε
            h_neg_le han
        constructor
        · have := negQ_anti (negQ (subQ (a⦅n⦆) L)) ε (negQ_in_RatSet _ hanL) hε h_neg_lt.1
          rwa [negQ_negQ (subQ (a⦅n⦆) L) hanL] at this
        · intro h_eq
          exact h_neg_lt.2 (show negQ (subQ (a⦅n⦆) L) = ε from by
            rw [show subQ (a⦅n⦆) L = negQ ε from h_eq.symm, negQ_negQ ε hε])
      -- negQ ε < a(n)−L ≤ f(n)−L
      have h_lo : ltQ (negQ ε) (subQ (f⦅n⦆) L) := by
        constructor
        · exact leQ_trans (negQ ε) (subQ (a⦅n⦆) L) (subQ (f⦅n⦆) L)
            (negQ_in_RatSet ε hε) hanL hfnL hanL_neg_lt.1 h_a_le
        · intro h_eq
          exact hanL_neg_lt.2 (leQ_antisymm (negQ ε) (subQ (a⦅n⦆) L)
            (negQ_in_RatSet ε hε) hanL hanL_neg_lt.1 (h_eq.symm ▸ h_a_le))
      -- f(n)−L ≤ b(n)−L < ε
      have h_hi : ltQ (subQ (f⦅n⦆) L) ε := by
        constructor
        · exact leQ_trans (subQ (f⦅n⦆) L) (subQ (b⦅n⦆) L) ε hfnL hbnL hε
            h_le_b hbnL_lt.1
        · intro h_eq
          exact hbnL_lt.2 (leQ_antisymm (subQ (b⦅n⦆) L) ε hbnL hε
            hbnL_lt.1 (h_eq ▸ h_le_b))
      exact absQ_lt_of_bounds (subQ (f⦅n⦆) L) ε hfnL hε h_lo h_hi

    /-- If f(n) = g(n) for all n ≥ N₀ and f → L, then g → L. -/
    theorem convergesToQ_of_eventually_eq (f g L : U)
        (_hL : L ∈ (RatSet : U)) (_hf : IsSeqQ f) (_hg : IsSeqQ g)
        (N₀ : U) (hN₀ : N₀ ∈ (ω : U))
        (h_eq : ∀ n : U, n ∈ (ω : U) → N₀ ∈ n ∨ N₀ = n → f⦅n⦆ = g⦅n⦆)
        (hconv : convergesToQ f L) :
        convergesToQ g L := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := hconv ε hε hε_pos
      let N' := maxOf N N₀
      have hN' := maxOf_in_Omega N N₀ hN hN₀
      refine ⟨N', hN', fun n hn h_ge => ?_⟩
      have hNn  := omega_le_trans N  N' n hN  hN' hn (le_maxOf_left  N N₀ hN hN₀) h_ge
      have hN₀n := omega_le_trans N₀ N' n hN₀ hN' hn (le_maxOf_right N N₀ hN hN₀) h_ge
      rw [← h_eq n hn hN₀n]
      exact hN_conv n hn hNn

    -- =========================================================================
    -- Section 8: Helpers and absolute value sequences
    -- =========================================================================

    /-- negQ (subQ x y) = subQ y x -/
    private theorem negQ_subQ (x y : U) (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        negQ (subQ x y) = subQ y x := by
      have hxy := addQ_in_RatSet x (negQ y) hx (negQ_in_RatSet y hy)
      have hyx := addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx)
      have h_sum : addQ (subQ x y) (subQ y x) = (zeroQ : U) :=
        calc addQ (addQ x (negQ y)) (addQ y (negQ x))
            = addQ x (addQ (negQ y) (addQ y (negQ x))) := by
                rw [addQ_assoc x (negQ y) (addQ y (negQ x)) hx (negQ_in_RatSet y hy)
                      (addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx))]
          _ = addQ x (addQ (addQ (negQ y) y) (negQ x)) := by
                rw [← addQ_assoc (negQ y) y (negQ x) (negQ_in_RatSet y hy) hy (negQ_in_RatSet x hx)]
          _ = addQ x (addQ (zeroQ : U) (negQ x)) := by rw [negQ_addQ_left y hy]
          _ = addQ x (negQ x) := by rw [addQ_zero_left (negQ x) (negQ_in_RatSet x hx)]
          _ = (zeroQ : U) := negQ_addQ_right x hx
      symm
      calc subQ y x
          = addQ (zeroQ : U) (subQ y x) := (addQ_zero_left _ hyx).symm
        _ = addQ (addQ (negQ (subQ x y)) (subQ x y)) (subQ y x) := by
              rw [negQ_addQ_left (subQ x y) hxy]
        _ = addQ (negQ (subQ x y)) (addQ (subQ x y) (subQ y x)) := by
              rw [addQ_assoc (negQ (subQ x y)) (subQ x y) (subQ y x)
                    (negQ_in_RatSet _ hxy) hxy hyx]
        _ = addQ (negQ (subQ x y)) (zeroQ : U) := by rw [h_sum]
        _ = negQ (subQ x y) := addQ_zero_right _ (negQ_in_RatSet _ hxy)

    /-- If x ≤ C and −x ≤ C then |x| ≤ C. -/
    private theorem absQ_le_of_bounds (x C : U)
        (hx : x ∈ (RatSet : U)) (hC : C ∈ (RatSet : U))
        (h1 : leQ x C) (h2 : leQ (negQ x) C) : leQ (absQ x) C := by
      by_cases h : leQ (zeroQ : U) x
      · rw [show absQ x = x from if_pos h]; exact h1
      · rw [show absQ x = negQ x from if_neg h]; exact h2

    /-- ||x| − |y|| ≤ |x − y| -/
    private theorem absQ_reverse_triangle (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        leQ (absQ (subQ (absQ x) (absQ y))) (absQ (subQ x y)) := by
      have hxy  := addQ_in_RatSet x (negQ y) hx (negQ_in_RatSet y hy)
      have hAx  := absQ_in_RatSet x hx
      have hAy  := absQ_in_RatSet y hy
      have hC   := absQ_in_RatSet (subQ x y) hxy
      have hd   := addQ_in_RatSet (absQ x) (negQ (absQ y)) hAx (negQ_in_RatSet _ hAy)
      -- Step 1: absQ x − absQ y ≤ |x − y|
      have h_x_eq : addQ (subQ x y) y = x := by
        show addQ (addQ x (negQ y)) y = x
        rw [addQ_assoc x (negQ y) y hx (negQ_in_RatSet y hy) hy,
            negQ_addQ_left y hy, addQ_zero_right x hx]
      have h_tri : leQ (absQ x) (addQ (absQ (subQ x y)) (absQ y)) := by
        have := absQ_triangle (subQ x y) y hxy hy; rwa [h_x_eq] at this
      have h1_add := addQ_leQ_addQ (absQ x) (addQ (absQ (subQ x y)) (absQ y)) (negQ (absQ y))
        hAx (addQ_in_RatSet _ _ hC hAy) (negQ_in_RatSet _ hAy) h_tri
      rw [addQ_assoc (absQ (subQ x y)) (absQ y) (negQ (absQ y)) hC hAy (negQ_in_RatSet _ hAy),
          negQ_addQ_right (absQ y) hAy, addQ_zero_right (absQ (subQ x y)) hC] at h1_add
      -- Step 2: absQ y − absQ x ≤ |y − x| = |x − y|
      have hyx  := addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx)
      have h_y_eq : addQ (subQ y x) x = y := by
        show addQ (addQ y (negQ x)) x = y
        rw [addQ_assoc y (negQ x) x hy (negQ_in_RatSet x hx) hx,
            negQ_addQ_left x hx, addQ_zero_right y hy]
      have h_tri_yx : leQ (absQ y) (addQ (absQ (subQ y x)) (absQ x)) := by
        have := absQ_triangle (subQ y x) x hyx hx; rwa [h_y_eq] at this
      have hCyx := absQ_in_RatSet (subQ y x) hyx
      have h2_add := addQ_leQ_addQ (absQ y) (addQ (absQ (subQ y x)) (absQ x)) (negQ (absQ x))
        hAy (addQ_in_RatSet _ _ hCyx hAx) (negQ_in_RatSet _ hAx) h_tri_yx
      rw [addQ_assoc (absQ (subQ y x)) (absQ x) (negQ (absQ x)) hCyx hAx (negQ_in_RatSet _ hAx),
          negQ_addQ_right (absQ x) hAx, addQ_zero_right (absQ (subQ y x)) hCyx] at h2_add
      exact absQ_le_of_bounds (subQ (absQ x) (absQ y)) (absQ (subQ x y)) hd hC h1_add
        (by rw [negQ_subQ (absQ x) (absQ y) hAx hAy, absQ_symm x y hx hy]; exact h2_add)

    /-- Absolute value sequence: (|f|)(n) = |f(n)| -/
    private noncomputable def absSeqQ (f : U) : U :=
      sep ((ω : U) ×ₛ (RatSet : U)) (fun p => snd p = absQ (f⦅fst p⦆))

    private theorem absSeqQ_mem_iff (f p : U) :
        p ∈ absSeqQ f ↔ p ∈ (ω : U) ×ₛ (RatSet : U) ∧ snd p = absQ (f⦅fst p⦆) := by
      unfold absSeqQ; exact mem_sep_iff _ p _

    private theorem absSeqQ_isSeqQ (f : U) (hf : IsSeqQ f) : IsSeqQ (absSeqQ f) := by
      unfold IsSeqQ
      constructor
      · intro p hp; exact ((absSeqQ_mem_iff f p).mp hp).1
      · intro n hn
        have hfn := seqTermQ_mem_RatSet f n hf hn
        refine ⟨absQ (f⦅n⦆), ?_, ?_⟩
        · show ⟨n, absQ (f⦅n⦆)⟩ ∈ absSeqQ f
          rw [absSeqQ_mem_iff]
          refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
                   ⟨hn, absQ_in_RatSet _ hfn⟩, ?_⟩
          rw [fst_of_ordered_pair, snd_of_ordered_pair]
        · intro z hz
          show z = absQ (f⦅n⦆)
          have h := ((absSeqQ_mem_iff f ⟨n, z⟩).mp hz).2
          rw [fst_of_ordered_pair, snd_of_ordered_pair] at h; exact h

    private theorem absSeqQ_apply (f : U) (hf : IsSeqQ f) (n : U) (hn : n ∈ (ω : U)) :
        (absSeqQ f)⦅n⦆ = absQ (f⦅n⦆) := by
      apply apply_eq _ n _ ((absSeqQ_isSeqQ f hf).2 n hn)
      show ⟨n, absQ (f⦅n⦆)⟩ ∈ absSeqQ f
      rw [absSeqQ_mem_iff]
      refine ⟨(OrderedPair_mem_CartesianProduct n _ (ω : U) RatSet).mpr
               ⟨hn, absQ_in_RatSet _ (seqTermQ_mem_RatSet f n hf hn)⟩, ?_⟩
      rw [fst_of_ordered_pair, snd_of_ordered_pair]

    /-- x ≥ 1 implies x > 0 -/
    private theorem isPositiveQ_of_ge_oneQ (x : U) (hx : x ∈ (RatSet : U))
        (h : leQ (oneQ : U) x) : isPositiveQ x :=
      ⟨leQ_trans zeroQ oneQ x zeroQ_mem_RatSet oneQ_mem_RatSet hx oneQ_pos.1 h,
       fun h_eq => oneQ_pos.2 (leQ_antisymm zeroQ oneQ zeroQ_mem_RatSet oneQ_mem_RatSet
         oneQ_pos.1 (h_eq.symm ▸ h))⟩

    -- =========================================================================
    -- Section 9: More limit arithmetic
    -- =========================================================================

    /-- If f → L then (c·f) → c·L for any rational c. -/
    theorem convergesToQ_const_mul (c f L : U)
        (hc : c ∈ (RatSet : U)) (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f)
        (h : convergesToQ f L) :
        convergesToQ (mulSeqQ (constSeqQ c) f) (mulQ c L) := by
      by_cases h_zero : c = (zeroQ : U)
      · -- c = 0: the product sequence is constantly 0
        subst h_zero
        intro ε hε hε_pos
        refine ⟨(∅ : U), zero_in_Omega, fun n hn _ => ?_⟩
        have hfn := seqTermQ_mem_RatSet f n hf hn
        rw [mulSeqQ_apply (constSeqQ (zeroQ : U)) f
              (constSeqQ_isSeqQ (zeroQ : U) zeroQ_mem_RatSet) hf n hn,
            constSeqQ_apply (zeroQ : U) zeroQ_mem_RatSet n hn,
            mulQ_zero_left (f⦅n⦆) hfn, mulQ_zero_left L hL,
            show subQ (zeroQ : U) (zeroQ : U) = (zeroQ : U) from by
              show addQ (zeroQ : U) (negQ (zeroQ : U)) = (zeroQ : U)
              rw [negQ_zero, addQ_zero_left (zeroQ : U) zeroQ_mem_RatSet],
            show absQ (zeroQ : U) = (zeroQ : U) from
              (absQ_eq_zero_iff (zeroQ : U) zeroQ_mem_RatSet).mpr rfl]
        exact hε_pos
      · -- c ≠ 0: use δ = ε / |c|
        have hAc     := absQ_in_RatSet c hc
        have hAc_pos := absQ_pos c hc h_zero
        have hAc_ne  : absQ c ≠ (zeroQ : U) := hAc_pos.2.symm
        intro ε hε hε_pos
        let δ := divQ ε (absQ c)
        have hδ      := divQ_in_RatSet ε (absQ c) hε hAc
        have h_eq_ε  : mulQ (absQ c) δ = ε := mulQ_divQ_cancel ε (absQ c) hε hAc hAc_ne
        have hδ_pos  : isPositiveQ δ := by
          constructor
          · rcases leQ_total (zeroQ : U) δ zeroQ_mem_RatSet hδ with hge | hle
            · exact hge
            · exfalso
              have h1 := mulQ_leQ_mulQ_of_nonneg_left (absQ c) δ (zeroQ : U)
                           hAc hδ zeroQ_mem_RatSet hle hAc_pos.1
              rw [mulQ_zero_right (absQ c) hAc, h_eq_ε] at h1
              exact hε_pos.2 (leQ_antisymm ε (zeroQ : U) hε zeroQ_mem_RatSet h1 hε_pos.1).symm
          · intro h_eq
            have h1 : mulQ (absQ c) δ = (zeroQ : U) := by
              rw [show δ = (zeroQ : U) from h_eq.symm]; exact mulQ_zero_right (absQ c) hAc
            exact hε_pos.2 (h_eq_ε.symm.trans h1).symm
        obtain ⟨N, hN, hN_conv⟩ := h δ hδ hδ_pos
        refine ⟨N, hN, fun n hn h_ge => ?_⟩
        have hfn   := seqTermQ_mem_RatSet f n hf hn
        have hfnL  := addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
        have hAfnL := absQ_in_RatSet (subQ (f⦅n⦆) L) hfnL
        rw [mulSeqQ_apply (constSeqQ c) f (constSeqQ_isSeqQ c hc) hf n hn,
            constSeqQ_apply c hc n hn,
            show subQ (mulQ c (f⦅n⦆)) (mulQ c L) = mulQ c (subQ (f⦅n⦆) L) from by
              show addQ (mulQ c (f⦅n⦆)) (negQ (mulQ c L)) = mulQ c (addQ (f⦅n⦆) (negQ L))
              rw [negQ_mulQ_right c L hc hL,
                  mulQ_addQ_distrib_left c (f⦅n⦆) (negQ L) hc hfn (negQ_in_RatSet L hL)],
            absQ_mulQ c (subQ (f⦅n⦆) L) hc hfnL]
        have hfnL_lt := hN_conv n hn h_ge
        constructor
        · have h_le := mulQ_leQ_mulQ_of_nonneg_left (absQ c) (absQ (subQ (f⦅n⦆) L)) δ
                         hAc hAfnL hδ hfnL_lt.1 hAc_pos.1
          rwa [h_eq_ε] at h_le
        · intro h_eq
          exact hfnL_lt.2 (mulQ_left_cancel (absQ (subQ (f⦅n⦆) L)) δ (absQ c)
            hAfnL hδ hAc hAc_ne (h_eq.trans h_eq_ε.symm))

    /-- If f → L then |f| → |L|. -/
    theorem convergesToQ_abs (f L : U)
        (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f)
        (h : convergesToQ f L) :
        convergesToQ (absSeqQ f) (absQ L) := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := h ε hε hε_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hfn   := seqTermQ_mem_RatSet f n hf hn
      have hfnL  := addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
      have hAbsL := absQ_in_RatSet L hL
      rw [absSeqQ_apply f hf n hn]
      -- ||f(n)| − |L|| ≤ |f(n) − L| < ε
      exact leQ_ltQ_trans
        (absQ (subQ (absQ (f⦅n⦆)) (absQ L)))
        (absQ (subQ (f⦅n⦆) L)) ε
        (absQ_in_RatSet _ (addQ_in_RatSet _ _ (absQ_in_RatSet _ hfn) (negQ_in_RatSet _ hAbsL)))
        (absQ_in_RatSet _ hfnL) hε
        (absQ_reverse_triangle (f⦅n⦆) L hfn hL)
        (hN_conv n hn h_ge)

    /-- If |f| → 0 then f → 0. -/
    theorem convergesToQ_zero_of_abs (f : U) (hf : IsSeqQ f)
        (h : convergesToQ (absSeqQ f) (zeroQ : U)) :
        convergesToQ f (zeroQ : U) := by
      intro ε hε hε_pos
      obtain ⟨N, hN, hN_conv⟩ := h ε hε hε_pos
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      have hfn   := seqTermQ_mem_RatSet f n hf hn
      have hasn  := seqTermQ_mem_RatSet _ n (absSeqQ_isSeqQ f hf) hn
      have h_nn  : leQ (zeroQ : U) ((absSeqQ f)⦅n⦆) := by
        rw [absSeqQ_apply f hf n hn]; exact absQ_nonneg _ hfn
      have h_raw := hN_conv n hn h_ge
      rw [show subQ ((absSeqQ f)⦅n⦆) (zeroQ : U) = (absSeqQ f)⦅n⦆ from by
            show addQ _ (negQ (zeroQ : U)) = _
            rw [negQ_zero, addQ_zero_right _ hasn],
          show absQ ((absSeqQ f)⦅n⦆) = (absSeqQ f)⦅n⦆ from if_pos h_nn,
          absSeqQ_apply f hf n hn] at h_raw
      rw [show subQ (f⦅n⦆) (zeroQ : U) = f⦅n⦆ from by
            show addQ (f⦅n⦆) (negQ (zeroQ : U)) = f⦅n⦆
            rw [negQ_zero, addQ_zero_right _ hfn]]
      exact h_raw

    /-- f → L ↔ |f − L| → 0. -/
    theorem convergesToQ_iff_abs (f L : U)
        (hL : L ∈ (RatSet : U)) (hf : IsSeqQ f) :
        convergesToQ f L ↔
        convergesToQ (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L)))) (zeroQ : U) := by
      have hcL    := constSeqQ_isSeqQ L hL
      have hncL   := negSeqQ_isSeqQ (constSeqQ L) hcL
      have hfncL  := addSeqQ_isSeqQ f _ hf hncL
      have habseq := absSeqQ_isSeqQ _ hfncL
      -- (|f − L|)(n) = |f(n) − L| for all n
      have h_seq_eq : ∀ n : U, n ∈ (ω : U) →
          (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆ = absQ (subQ (f⦅n⦆) L) := by
        intro n hn
        rw [absSeqQ_apply _ hfncL n hn,
            addSeqQ_apply _ _ hf hncL n hn,
            negSeqQ_apply (constSeqQ L) hcL n hn,
            constSeqQ_apply L hL n hn]
        rfl
      constructor
      · intro hconv ε hε hε_pos
        obtain ⟨N, hN, hN_conv⟩ := hconv ε hε hε_pos
        refine ⟨N, hN, fun n hn h_ge => ?_⟩
        have hfn   := seqTermQ_mem_RatSet f n hf hn
        have hfnL  := addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
        have hasn  := seqTermQ_mem_RatSet _ n habseq hn
        have h_nn  : leQ (zeroQ : U) ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) := by
          rw [h_seq_eq n hn]; exact absQ_nonneg _ hfnL
        rw [show subQ ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) (zeroQ : U) =
                (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆ from by
              show addQ _ (negQ (zeroQ : U)) = _
              rw [negQ_zero, addQ_zero_right _ hasn],
            show absQ ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) =
                 (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆ from if_pos h_nn,
            h_seq_eq n hn]
        exact hN_conv n hn h_ge
      · intro hconv ε hε hε_pos
        obtain ⟨N, hN, hN_conv⟩ := hconv ε hε hε_pos
        refine ⟨N, hN, fun n hn h_ge => ?_⟩
        have hfn   := seqTermQ_mem_RatSet f n hf hn
        have hfnL  := addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
        have hasn  := seqTermQ_mem_RatSet _ n habseq hn
        have h_nn  : leQ (zeroQ : U) ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) := by
          rw [h_seq_eq n hn]; exact absQ_nonneg _ hfnL
        have h_raw := hN_conv n hn h_ge
        rw [show subQ ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) (zeroQ : U) =
                (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆ from by
              show addQ _ (negQ (zeroQ : U)) = _
              rw [negQ_zero, addQ_zero_right _ hasn],
            show absQ ((absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆) =
                 (absSeqQ (addSeqQ f (negSeqQ (constSeqQ L))))⦅n⦆ from if_pos h_nn,
            h_seq_eq n hn] at h_raw
        exact h_raw

    /-- If f → L₁ and g → L₂ then (f·g) → L₁·L₂. -/
    theorem convergesToQ_mul (f g L₁ L₂ : U)
        (hL₁ : L₁ ∈ (RatSet : U)) (hL₂ : L₂ ∈ (RatSet : U))
        (hf : IsSeqQ f) (hg : IsSeqQ g)
        (h₁ : convergesToQ f L₁) (h₂ : convergesToQ g L₂) :
        convergesToQ (mulSeqQ f g) (mulQ L₁ L₂) := by
      intro ε hε hε_pos
      -- Bounding constants M₁ = |L₁| + 1, M₂ = |L₂| + 1
      let M₁ : U := addQ (absQ L₁) oneQ
      let M₂ : U := addQ (absQ L₂) oneQ
      have hAL₁ := absQ_in_RatSet L₁ hL₁
      have hAL₂ := absQ_in_RatSet L₂ hL₂
      have hM₁  : M₁ ∈ (RatSet : U) := addQ_in_RatSet (absQ L₁) oneQ hAL₁ oneQ_mem_RatSet
      have hM₂  : M₂ ∈ (RatSet : U) := addQ_in_RatSet (absQ L₂) oneQ hAL₂ oneQ_mem_RatSet
      have hM₁_pos : isPositiveQ M₁ := isPositiveQ_of_ge_oneQ M₁ hM₁ (by
        have h := addQ_leQ_addQ (zeroQ : U) (absQ L₁) (oneQ : U)
                    zeroQ_mem_RatSet hAL₁ oneQ_mem_RatSet (absQ_nonneg L₁ hL₁)
        rwa [addQ_zero_left (oneQ : U) oneQ_mem_RatSet] at h)
      have hM₂_pos : isPositiveQ M₂ := isPositiveQ_of_ge_oneQ M₂ hM₂ (by
        have h := addQ_leQ_addQ (zeroQ : U) (absQ L₂) (oneQ : U)
                    zeroQ_mem_RatSet hAL₂ oneQ_mem_RatSet (absQ_nonneg L₂ hL₂)
        rwa [addQ_zero_left (oneQ : U) oneQ_mem_RatSet] at h)
      have hM₁_ne : M₁ ≠ (zeroQ : U) := hM₁_pos.2.symm
      have hM₂_ne : M₂ ≠ (zeroQ : U) := hM₂_pos.2.symm
      -- Split-epsilon values ε₁ = (ε/2)/M₂, ε₂ = (ε/2)/M₁
      let hε_half := halfQ ε
      have hhε_half   : hε_half ∈ (RatSet : U) := halfQ_mem_RatSet ε hε
      have hhε_half_p : isPositiveQ hε_half := halfQ_pos ε hε hε_pos
      let ε₁ : U := divQ (halfQ ε) M₂
      let ε₂ : U := divQ (halfQ ε) M₁
      have hε₁ : ε₁ ∈ (RatSet : U) := divQ_in_RatSet (halfQ ε) M₂ hhε_half hM₂
      have hε₂ : ε₂ ∈ (RatSet : U) := divQ_in_RatSet (halfQ ε) M₁ hhε_half hM₁
      -- M₂·ε₁ = ε/2 and M₁·ε₂ = ε/2
      have h_ε₁_eq : mulQ M₂ ε₁ = halfQ ε := mulQ_divQ_cancel (halfQ ε) M₂ hhε_half hM₂ hM₂_ne
      have h_ε₂_eq : mulQ M₁ ε₂ = halfQ ε := mulQ_divQ_cancel (halfQ ε) M₁ hhε_half hM₁ hM₁_ne
      have hε₁_pos : isPositiveQ ε₁ := by
        constructor
        · rcases leQ_total (zeroQ : U) ε₁ zeroQ_mem_RatSet hε₁ with hge | hle
          · exact hge
          · exfalso
            have h1 := mulQ_leQ_mulQ_of_nonneg_left M₂ ε₁ (zeroQ : U)
                         hM₂ hε₁ zeroQ_mem_RatSet hle hM₂_pos.1
            rw [mulQ_zero_right M₂ hM₂, h_ε₁_eq] at h1
            exact hhε_half_p.2
              (leQ_antisymm (halfQ ε) (zeroQ : U) hhε_half zeroQ_mem_RatSet h1 hhε_half_p.1).symm
        · intro h_eq
          have h1 : mulQ M₂ ε₁ = (zeroQ : U) := by
            rw [show ε₁ = (zeroQ : U) from h_eq.symm]; exact mulQ_zero_right M₂ hM₂
          exact hhε_half_p.2 (h_ε₁_eq.symm.trans h1).symm
      have hε₂_pos : isPositiveQ ε₂ := by
        constructor
        · rcases leQ_total (zeroQ : U) ε₂ zeroQ_mem_RatSet hε₂ with hge | hle
          · exact hge
          · exfalso
            have h1 := mulQ_leQ_mulQ_of_nonneg_left M₁ ε₂ (zeroQ : U)
                         hM₁ hε₂ zeroQ_mem_RatSet hle hM₁_pos.1
            rw [mulQ_zero_right M₁ hM₁, h_ε₂_eq] at h1
            exact hhε_half_p.2
              (leQ_antisymm (halfQ ε) (zeroQ : U) hhε_half zeroQ_mem_RatSet h1 hhε_half_p.1).symm
        · intro h_eq
          have h1 : mulQ M₁ ε₂ = (zeroQ : U) := by
            rw [show ε₂ = (zeroQ : U) from h_eq.symm]; exact mulQ_zero_right M₁ hM₁
          exact hhε_half_p.2 (h_ε₂_eq.symm.trans h1).symm
      -- Get convergence thresholds N₁ (for f), N₂ (for g tight), N_b (for g bounded)
      obtain ⟨N₁, hN₁, hN₁_conv⟩ := h₁ ε₁ hε₁ hε₁_pos
      obtain ⟨N₂, hN₂, hN₂_conv⟩ := h₂ ε₂ hε₂ hε₂_pos
      obtain ⟨N_b, hN_b, hN_b_conv⟩ := h₂ (oneQ : U) oneQ_mem_RatSet oneQ_pos
      let N := maxOf (maxOf N₁ N₂) N_b
      have hN₁₂ := maxOf_in_Omega N₁ N₂ hN₁ hN₂
      have hN   := maxOf_in_Omega (maxOf N₁ N₂) N_b hN₁₂ hN_b
      refine ⟨N, hN, fun n hn h_ge => ?_⟩
      -- Extract individual threshold conditions
      have h_ge_N₁₂ := omega_le_trans (maxOf N₁ N₂) N n hN₁₂ hN hn
        (le_maxOf_left (maxOf N₁ N₂) N_b hN₁₂ hN_b) h_ge
      have h_ge_N_b := omega_le_trans N_b N n hN_b hN hn
        (le_maxOf_right (maxOf N₁ N₂) N_b hN₁₂ hN_b) h_ge
      have h_ge_N₁ := omega_le_trans N₁ (maxOf N₁ N₂) n hN₁ hN₁₂ hn
        (le_maxOf_left N₁ N₂ hN₁ hN₂) h_ge_N₁₂
      have h_ge_N₂ := omega_le_trans N₂ (maxOf N₁ N₂) n hN₂ hN₁₂ hn
        (le_maxOf_right N₁ N₂ hN₁ hN₂) h_ge_N₁₂
      -- Sequence terms and their bounds
      have hfn    := seqTermQ_mem_RatSet f n hf hn
      have hgn    := seqTermQ_mem_RatSet g n hg hn
      have hfnL₁  := addQ_in_RatSet (f⦅n⦆) (negQ L₁) hfn (negQ_in_RatSet L₁ hL₁)
      have hgnL₂  := addQ_in_RatSet (g⦅n⦆) (negQ L₂) hgn (negQ_in_RatSet L₂ hL₂)
      have hAfnL₁ := absQ_in_RatSet (subQ (f⦅n⦆) L₁) hfnL₁
      have hAgnL₂ := absQ_in_RatSet (subQ (g⦅n⦆) L₂) hgnL₂
      have hAgn   := absQ_in_RatSet (g⦅n⦆) hgn
      have hfn_lt   : ltQ (absQ (subQ (f⦅n⦆) L₁)) ε₁ := hN₁_conv n hn h_ge_N₁
      have hgn_lt   : ltQ (absQ (subQ (g⦅n⦆) L₂)) ε₂ := hN₂_conv n hn h_ge_N₂
      have hgn_bound : ltQ (absQ (subQ (g⦅n⦆) L₂)) (oneQ : U) := hN_b_conv n hn h_ge_N_b
      -- Bound: |g(n)| ≤ M₂ = |L₂| + 1
      have hAgn_le : leQ (absQ (g⦅n⦆)) M₂ := by
        have h_eq : addQ (subQ (g⦅n⦆) L₂) L₂ = g⦅n⦆ := by
          show addQ (addQ (g⦅n⦆) (negQ L₂)) L₂ = g⦅n⦆
          rw [addQ_assoc (g⦅n⦆) (negQ L₂) L₂ hgn (negQ_in_RatSet L₂ hL₂) hL₂,
              negQ_addQ_left L₂ hL₂, addQ_zero_right (g⦅n⦆) hgn]
        have h_tri_gn : leQ (absQ (g⦅n⦆)) (addQ (absQ (subQ (g⦅n⦆) L₂)) (absQ L₂)) := by
          have := absQ_triangle (subQ (g⦅n⦆) L₂) L₂ hgnL₂ hL₂; rwa [h_eq] at this
        have h_add : leQ (addQ (absQ (subQ (g⦅n⦆) L₂)) (absQ L₂))
                         (addQ (oneQ : U) (absQ L₂)) :=
          addQ_leQ_addQ (absQ (subQ (g⦅n⦆) L₂)) (oneQ : U) (absQ L₂)
            hAgnL₂ oneQ_mem_RatSet hAL₂ hgn_bound.1
        have h_M₂_eq : addQ (oneQ : U) (absQ L₂) = M₂ :=
          addQ_comm (oneQ : U) (absQ L₂) oneQ_mem_RatSet hAL₂
        exact leQ_trans (absQ (g⦅n⦆)) (addQ (absQ (subQ (g⦅n⦆) L₂)) (absQ L₂)) M₂
          hAgn (addQ_in_RatSet _ _ hAgnL₂ hAL₂) hM₂ h_tri_gn (h_M₂_eq ▸ h_add)
      -- |L₁| ≤ M₁
      have h_L₁_le_M₁ : leQ (absQ L₁) M₁ := by
        have h := addQ_leQ_addQ (zeroQ : U) (oneQ : U) (absQ L₁)
                    zeroQ_mem_RatSet oneQ_mem_RatSet hAL₁ oneQ_pos.1
        rw [addQ_zero_left (absQ L₁) hAL₁,
            addQ_comm (oneQ : U) (absQ L₁) oneQ_mem_RatSet hAL₁] at h
        exact h
      -- First bound: |f(n) − L₁|·|g(n)| < ε/2
      have h_fn_gn_lt : ltQ (mulQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (g⦅n⦆))) (halfQ ε) := by
        have h_le := mulQ_leQ_mulQ_of_nonneg_left (absQ (subQ (f⦅n⦆) L₁)) (absQ (g⦅n⦆)) M₂
                       hAfnL₁ hAgn hM₂ hAgn_le (absQ_nonneg _ hfnL₁)
        have h_lt : ltQ (mulQ (absQ (subQ (f⦅n⦆) L₁)) M₂) (mulQ ε₁ M₂) :=
          ⟨mulQ_leQ_mulQ_of_nonneg_right (absQ (subQ (f⦅n⦆) L₁)) ε₁ M₂
             hAfnL₁ hε₁ hM₂ hfn_lt.1 hM₂_pos.1,
           fun h_eq => hfn_lt.2 (mulQ_right_cancel (absQ (subQ (f⦅n⦆) L₁)) ε₁ M₂
             hAfnL₁ hε₁ hM₂ hM₂_ne h_eq)⟩
        have h_ε₁M₂ : mulQ ε₁ M₂ = halfQ ε := by
          rw [mulQ_comm ε₁ M₂ hε₁ hM₂]; exact h_ε₁_eq
        rw [h_ε₁M₂] at h_lt
        exact leQ_ltQ_trans _ _ _ (mulQ_in_RatSet _ _ hAfnL₁ hAgn)
          (mulQ_in_RatSet _ _ hAfnL₁ hM₂) hhε_half h_le h_lt
      -- Second bound: |L₁|·|g(n) − L₂| < ε/2
      have h_L₁_gn_lt : ltQ (mulQ (absQ L₁) (absQ (subQ (g⦅n⦆) L₂))) (halfQ ε) := by
        have h_le := mulQ_leQ_mulQ_of_nonneg_right (absQ L₁) M₁ (absQ (subQ (g⦅n⦆) L₂))
                       hAL₁ hM₁ hAgnL₂ h_L₁_le_M₁ (absQ_nonneg _ hgnL₂)
        have h_lt : ltQ (mulQ M₁ (absQ (subQ (g⦅n⦆) L₂))) (mulQ M₁ ε₂) :=
          ⟨mulQ_leQ_mulQ_of_nonneg_left M₁ (absQ (subQ (g⦅n⦆) L₂)) ε₂
             hM₁ hAgnL₂ hε₂ hgn_lt.1 hM₁_pos.1,
           fun h_eq => hgn_lt.2 (mulQ_left_cancel (absQ (subQ (g⦅n⦆) L₂)) ε₂ M₁
             hAgnL₂ hε₂ hM₁ hM₁_ne h_eq)⟩
        rw [h_ε₂_eq] at h_lt
        exact leQ_ltQ_trans _ _ _ (mulQ_in_RatSet _ _ hAL₁ hAgnL₂)
          (mulQ_in_RatSet _ _ hM₁ hAgnL₂) hhε_half h_le h_lt
      -- Algebraic identity: f(n)·g(n) − L₁·L₂ = (f(n)−L₁)·g(n) + L₁·(g(n)−L₂)
      have h_fngn  := mulQ_in_RatSet (f⦅n⦆) (g⦅n⦆) hfn hgn
      have h_L₁L₂  := mulQ_in_RatSet L₁ L₂ hL₁ hL₂
      have h_L₁gn  := mulQ_in_RatSet L₁ (g⦅n⦆) hL₁ hgn
      have h_T₁    := mulQ_in_RatSet (subQ (f⦅n⦆) L₁) (g⦅n⦆) hfnL₁ hgn
      have h_T₂    := mulQ_in_RatSet L₁ (subQ (g⦅n⦆) L₂) hL₁ hgnL₂
      have h_id : subQ (mulQ (f⦅n⦆) (g⦅n⦆)) (mulQ L₁ L₂) =
                  addQ (mulQ (subQ (f⦅n⦆) L₁) (g⦅n⦆)) (mulQ L₁ (subQ (g⦅n⦆) L₂)) := by
        show addQ (mulQ (f⦅n⦆) (g⦅n⦆)) (negQ (mulQ L₁ L₂)) =
             addQ (mulQ (addQ (f⦅n⦆) (negQ L₁)) (g⦅n⦆)) (mulQ L₁ (addQ (g⦅n⦆) (negQ L₂)))
        rw [mulQ_addQ_distrib_right (f⦅n⦆) (negQ L₁) (g⦅n⦆) hfn (negQ_in_RatSet L₁ hL₁) hgn,
            ← negQ_mulQ_left L₁ (g⦅n⦆) hL₁ hgn,
            mulQ_addQ_distrib_left L₁ (g⦅n⦆) (negQ L₂) hL₁ hgn (negQ_in_RatSet L₂ hL₂),
            ← negQ_mulQ_right L₁ L₂ hL₁ hL₂]
        symm
        rw [addQ_assoc (mulQ (f⦅n⦆) (g⦅n⦆)) (negQ (mulQ L₁ (g⦅n⦆)))
              (addQ (mulQ L₁ (g⦅n⦆)) (negQ (mulQ L₁ L₂)))
              h_fngn (negQ_in_RatSet _ h_L₁gn)
              (addQ_in_RatSet _ _ h_L₁gn (negQ_in_RatSet _ h_L₁L₂)),
            ← addQ_assoc (negQ (mulQ L₁ (g⦅n⦆))) (mulQ L₁ (g⦅n⦆)) (negQ (mulQ L₁ L₂))
              (negQ_in_RatSet _ h_L₁gn) h_L₁gn (negQ_in_RatSet _ h_L₁L₂),
            negQ_addQ_left (mulQ L₁ (g⦅n⦆)) h_L₁gn,
            addQ_zero_left (negQ (mulQ L₁ L₂)) (negQ_in_RatSet _ h_L₁L₂)]
      -- Triangle inequality + absQ_mulQ + combine bounds
      rw [mulSeqQ_apply f g hf hg n hn, h_id]
      have h_tri := absQ_triangle (mulQ (subQ (f⦅n⦆) L₁) (g⦅n⦆)) (mulQ L₁ (subQ (g⦅n⦆) L₂))
                     h_T₁ h_T₂
      rw [absQ_mulQ (subQ (f⦅n⦆) L₁) (g⦅n⦆) hfnL₁ hgn,
          absQ_mulQ L₁ (subQ (g⦅n⦆) L₂) hL₁ hgnL₂] at h_tri
      apply leQ_ltQ_trans _ _ ε
        (absQ_in_RatSet _ (addQ_in_RatSet _ _ h_T₁ h_T₂))
        (addQ_in_RatSet _ _ (mulQ_in_RatSet _ _ hAfnL₁ hAgn) (mulQ_in_RatSet _ _ hAL₁ hAgnL₂))
        hε h_tri
      -- |f(n)−L₁|·|g(n)| + |L₁|·|g(n)−L₂| < ε/2 + ε/2 = ε
      rw [← half_add_half ε hε]
      exact ltQ_addQ_of_leQ_ltQ
        (mulQ (absQ (subQ (f⦅n⦆) L₁)) (absQ (g⦅n⦆)))
        (mulQ (absQ L₁) (absQ (subQ (g⦅n⦆) L₂)))
        (halfQ ε) (halfQ ε)
        (mulQ_in_RatSet _ _ hAfnL₁ hAgn)
        (mulQ_in_RatSet _ _ hAL₁ hAgnL₂)
        hhε_half hhε_half
        h_fn_gn_lt.1 h_L₁_gn_lt

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
  convergesToQ_sub
  convergesToQ_of_dominated
  squeeze_theorem
  convergesToQ_of_eventually_eq
  convergesToQ_const_mul
  convergesToQ_abs
  convergesToQ_zero_of_abs
  convergesToQ_iff_abs
  convergesToQ_mul
)
