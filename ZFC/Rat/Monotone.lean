/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Monotone and Bounded Sequences in ℚ

  This module defines monotonicity and boundedness for sequences
  f : ω → ℚ and establishes their basic properties.

  **Important note on completeness:** ℚ is not order-complete.
  A monotone bounded sequence in ℚ need NOT converge in ℚ
  (e.g., the Newton-Raphson approximations to √2 are decreasing and bounded
  below, converging to √2 ∉ ℚ). Therefore:
  - `nondecreasing_bounded_isCauchy` and `nonincreasing_bounded_isCauchy`
    are stated with `sorry` — they require completeness-style reasoning that
    currently cannot be done purely in ℚ.
  - `convergent_isBounded` is also `sorry` — it requires a finite maximum
    over an initial segment, which needs more infrastructure.

  ## Main Definitions

  * `isNondecreasingQ f`     — f(m) ≤ f(n) whenever m ≤ n
  * `isNonincreasingQ f`     — f(m) ≥ f(n) whenever m ≤ n
  * `isStrictlyIncreasingQ f`— f(m) < f(n) whenever m < n  (m ∈ n in ω)
  * `isStrictlyDecreasingQ f`— f(m) > f(n) whenever m < n
  * `isBoundedAboveByQ f M`  — ∀ n ∈ ω, f(n) ≤ M
  * `isBoundedBelowByQ f M`  — ∀ n ∈ ω, M ≤ f(n)
  * `isBoundedQ f`           — ∃ M > 0 ∈ ℚ, ∀ n ∈ ω, |f(n)| ≤ M

  ## Main Theorems

  * `constSeqQ_isNondecreasing`          — constant sequences are nondecreasing
  * `constSeqQ_isNonincreasing`          — constant sequences are nonincreasing
  * `strictlyIncreasing_isNondecreasing` — strictly increasing → nondecreasing
  * `strictlyDecreasing_isNonincreasing` — strictly decreasing → nonincreasing
  * `nondecreasing_convergent_limit_ge`  — if f↗ and f→L then f(n) ≤ L for all n
  * `nonincreasing_convergent_limit_le`  — if f↘ and f→L then L ≤ f(n) for all n
  * `limit_le_of_bounded_above`          — if f→L and ∀n, f(n)≤M then L≤M
  * `le_limit_of_bounded_below`          — if f→L and ∀n, M≤f(n) then M≤L
  * `nondecreasing_bounded_isCauchy`     — f↗, bounded above → IsCauchyQ f  (sorry)
  * `nonincreasing_bounded_isCauchy`     — f↘, bounded below → IsCauchyQ f  (sorry)
  * `convergent_isBounded`               — convergent → bounded               (sorry)
  * `nondecreasing_convergent_isBoundedAbove` — f↗, f→L → bounded above by L
  * `nonincreasing_convergent_isBoundedBelow` — f↘, f→L → bounded below by L

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.CauchyQ

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
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Sequences
  open ZFC.Rat.Convergence
  open ZFC.Rat.CauchyQ

  universe u
  variable {U : Type u}

  namespace Rat.Monotone

    -- =========================================================================
    -- Private helpers
    -- =========================================================================

    /-- |x − y| = |y − x| (symmetry of distance) -/
    private theorem absQ_symm (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U)) :
        absQ (subQ x y) = absQ (subQ y x) := by
      have hxy : subQ x y ∈ (RatSet : U) :=
        addQ_in_RatSet x (negQ y) hx (negQ_in_RatSet y hy)
      have hyx : subQ y x ∈ (RatSet : U) :=
        addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx)
      have h_neg : subQ y x = negQ (subQ x y) := by
        have h_sum : addQ (subQ x y) (subQ y x) = (zeroQ : U) :=
          calc addQ (addQ x (negQ y)) (addQ y (negQ x))
              = addQ x (addQ (negQ y) (addQ y (negQ x))) := by
                rw [addQ_assoc x (negQ y) (addQ y (negQ x)) hx
                      (negQ_in_RatSet y hy)
                      (addQ_in_RatSet y (negQ x) hy (negQ_in_RatSet x hx))]
            _ = addQ x (addQ (addQ (negQ y) y) (negQ x)) := by
                rw [← addQ_assoc (negQ y) y (negQ x)
                      (negQ_in_RatSet y hy) hy (negQ_in_RatSet x hx)]
            _ = addQ x (addQ zeroQ (negQ x)) := by rw [negQ_addQ_left y hy]
            _ = addQ x (negQ x) := by
                rw [addQ_zero_left (negQ x) (negQ_in_RatSet x hx)]
            _ = zeroQ := negQ_addQ_right x hx
        calc subQ y x
            = addQ (zeroQ : U) (subQ y x) :=
              (addQ_zero_left (subQ y x) hyx).symm
          _ = addQ (addQ (negQ (subQ x y)) (subQ x y)) (subQ y x) := by
              rw [negQ_addQ_left (subQ x y) hxy]
          _ = addQ (negQ (subQ x y)) (addQ (subQ x y) (subQ y x)) := by
              rw [addQ_assoc (negQ (subQ x y)) (subQ x y) (subQ y x)
                    (negQ_in_RatSet (subQ x y) hxy) hxy hyx]
          _ = addQ (negQ (subQ x y)) (zeroQ : U) := by rw [h_sum]
          _ = negQ (subQ x y) :=
              addQ_zero_right (negQ (subQ x y)) (negQ_in_RatSet (subQ x y) hxy)
      rw [h_neg, absQ_negQ (subQ x y) hxy]

    /-- subQ a b = 0 ↔ a = b -/
    private theorem subQ_zero_iff (a b : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) :
        subQ a b = (zeroQ : U) ↔ a = b := by
      constructor
      · intro h_eq
        have h_exp : addQ a (negQ b) = (zeroQ : U) := h_eq
        calc a = addQ a zeroQ := (addQ_zero_right a ha).symm
          _ = addQ a (addQ (negQ b) b) := by rw [negQ_addQ_left b hb]
          _ = addQ (addQ a (negQ b)) b :=
                (addQ_assoc a (negQ b) b ha (negQ_in_RatSet b hb) hb).symm
          _ = addQ zeroQ b := by rw [h_exp]
          _ = b := addQ_zero_left b hb
      · intro h_eq
        subst h_eq
        show addQ a (negQ a) = zeroQ
        exact negQ_addQ_right a ha

    /-- negQ is antitone: x ≤ y → −y ≤ −x -/
    private theorem negQ_antimonotone (x y : U)
        (hx : x ∈ (RatSet : U)) (hy : y ∈ (RatSet : U))
        (h : leQ x y) : leQ (negQ y) (negQ x) := by
      have hnx := negQ_in_RatSet x hx
      have hny := negQ_in_RatSet y hy
      have h1 := addQ_leQ_addQ x y (addQ (negQ x) (negQ y)) hx hy
        (addQ_in_RatSet (negQ x) (negQ y) hnx hny) h
      rw [← addQ_assoc x (negQ x) (negQ y) hx hnx hny,
          negQ_addQ_right x hx,
          addQ_zero_left (negQ y) hny] at h1
      rw [addQ_comm (negQ x) (negQ y) hnx hny,
          ← addQ_assoc y (negQ y) (negQ x) hy hny hnx,
          negQ_addQ_right y hy,
          addQ_zero_left (negQ x) hnx] at h1
      exact h1

    -- =========================================================================
    -- Section 1: Definitions
    -- =========================================================================

    /-- f is nondecreasing: m ≤ n → f(m) ≤ f(n) -/
    def isNondecreasingQ (f : U) : Prop :=
      ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) →
        m ∈ n ∨ m = n → leQ (f⦅m⦆) (f⦅n⦆)

    /-- f is nonincreasing: m ≤ n → f(m) ≥ f(n) -/
    def isNonincreasingQ (f : U) : Prop :=
      ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) →
        m ∈ n ∨ m = n → leQ (f⦅n⦆) (f⦅m⦆)

    /-- f is strictly increasing: m < n (m ∈ n in ω) → f(m) < f(n) -/
    def isStrictlyIncreasingQ (f : U) : Prop :=
      ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) → m ∈ n → ltQ (f⦅m⦆) (f⦅n⦆)

    /-- f is strictly decreasing: m < n → f(m) > f(n) -/
    def isStrictlyDecreasingQ (f : U) : Prop :=
      ∀ m n : U, m ∈ (ω : U) → n ∈ (ω : U) → m ∈ n → ltQ (f⦅n⦆) (f⦅m⦆)

    /-- f is bounded above by M: ∀ n ∈ ω, f(n) ≤ M -/
    def isBoundedAboveByQ (f M : U) : Prop :=
      ∀ n : U, n ∈ (ω : U) → leQ (f⦅n⦆) M

    /-- f is bounded below by M: ∀ n ∈ ω, M ≤ f(n) -/
    def isBoundedBelowByQ (f M : U) : Prop :=
      ∀ n : U, n ∈ (ω : U) → leQ M (f⦅n⦆)

    /-- f is bounded: ∃ M > 0 ∈ ℚ, ∀ n ∈ ω, |f(n)| ≤ M -/
    def isBoundedQ (f : U) : Prop :=
      ∃ M : U, M ∈ (RatSet : U) ∧ isPositiveQ M ∧
        ∀ n : U, n ∈ (ω : U) → leQ (absQ (f⦅n⦆)) M

    -- =========================================================================
    -- Section 2: Basic properties of monotone sequences
    -- =========================================================================

    /-- The constant sequence is nondecreasing. -/
    theorem constSeqQ_isNondecreasing (a : U) (ha : a ∈ (RatSet : U)) :
        isNondecreasingQ (constSeqQ a) := by
      intro m n hm hn _h
      rw [constSeqQ_apply a ha m hm, constSeqQ_apply a ha n hn]
      exact leQ_refl a ha

    /-- The constant sequence is nonincreasing. -/
    theorem constSeqQ_isNonincreasing (a : U) (ha : a ∈ (RatSet : U)) :
        isNonincreasingQ (constSeqQ a) := by
      intro m n hm hn _h
      rw [constSeqQ_apply a ha m hm, constSeqQ_apply a ha n hn]
      exact leQ_refl a ha

    /-- A strictly increasing sequence is nondecreasing (requires IsSeqQ for the reflexive case). -/
    theorem strictlyIncreasing_isNondecreasing (f : U)
        (hf : IsSeqQ f) (h : isStrictlyIncreasingQ f) : isNondecreasingQ f := by
      intro m n hm hn h_le
      rcases h_le with hmn | rfl
      · exact (h m n hm hn hmn).1
      · exact leQ_refl (f⦅m⦆) (seqTermQ_mem_RatSet f m hf hm)

    /-- A strictly decreasing sequence is nonincreasing (requires IsSeqQ for the reflexive case). -/
    theorem strictlyDecreasing_isNonincreasing (f : U)
        (hf : IsSeqQ f) (h : isStrictlyDecreasingQ f) : isNonincreasingQ f := by
      intro m n hm hn h_le
      rcases h_le with hmn | rfl
      · exact (h m n hm hn hmn).1
      · exact leQ_refl (f⦅m⦆) (seqTermQ_mem_RatSet f m hf hm)

    -- =========================================================================
    -- Section 3: Limits bound monotone sequences
    -- =========================================================================

    /-- If f is nondecreasing and converges to L, then f(n) ≤ L for all n.
        Proof: Fix n. Suppose for contradiction f(n) > L.
        Set ε = f(n) − L > 0. Get N s.t. ∀ k ≥ N, |f(k)−L| < ε.
        Take k = max(n, N) ≥ n, so f(k) ≥ f(n) > L, hence f(k)−L ≥ f(n)−L = ε.
        But |f(k)−L| < ε, and since f(k) > L we have absQ(f(k)−L) = f(k)−L ≥ ε.
        Contradiction. -/
    theorem nondecreasing_convergent_limit_ge (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (hmon : isNondecreasingQ f)
        (hconv : convergesToQ f L) :
        ∀ n : U, n ∈ (ω : U) → leQ (f⦅n⦆) L := by
      intro n hn
      -- Proof by contradiction: suppose f(n) > L
      apply Classical.byContradiction
      intro h_not_le
      -- h_not_le : ¬ leQ (f⦅n⦆) L
      -- By totality: leQ L (f⦅n⦆)
      have hfn : f⦅n⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f n hf hn
      have h_gt : ltQ L (f⦅n⦆) := by
        rcases leQ_total L (f⦅n⦆) hL hfn with h | h
        · exact ⟨h, fun heq => h_not_le (heq ▸ leQ_refl L hL)⟩
        · exact absurd h h_not_le
      -- ε = f(n) − L > 0
      have hfnL : subQ (f⦅n⦆) L ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅n⦆) (negQ L) hfn (negQ_in_RatSet L hL)
      have hε_pos : isPositiveQ (subQ (f⦅n⦆) L) := by
        -- ltQ L (f⦅n⦆) means leQ L (f⦅n⦆) ∧ L ≠ f⦅n⦆
        -- subQ f⦅n⦆ L = f⦅n⦆ + (-L); leQ zeroQ (f⦅n⦆ - L) iff leQ L (f⦅n⦆)
        constructor
        · -- leQ zeroQ (subQ (f⦅n⦆) L)
          -- zeroQ = L + (-L), so we need leQ (L + (-L)) (f⦅n⦆ + (-L))
          -- which follows from leQ L (f⦅n⦆) via addQ_leQ_addQ
          have step := addQ_leQ_addQ L (f⦅n⦆) (negQ L)
            hL hfn (negQ_in_RatSet L hL) h_gt.1
          rwa [negQ_addQ_right L hL] at step
        · -- subQ (f⦅n⦆) L ≠ zeroQ
          intro h_eq
          -- h_eq : f(n) - L = 0 → f(n) = L
          exact h_gt.2 ((subQ_zero_iff (f⦅n⦆) L hfn hL).mp h_eq.symm).symm
      -- Get N from convergence with ε = f(n) − L
      obtain ⟨N, hN, hN_conv⟩ := hconv (subQ (f⦅n⦆) L) hfnL hε_pos
      -- k = max(n, N) ≥ both n and N
      let k := maxOf n N
      have hk := maxOf_in_Omega n N hn hN
      have hkn := le_maxOf_left n N hn hN  -- n ≤ k
      have hkN := le_maxOf_right n N hn hN  -- N ≤ k
      -- f(k) ≥ f(n) (nondecreasing)
      have hfk : f⦅k⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f k hf hk
      have h_fk_ge_fn : leQ (f⦅n⦆) (f⦅k⦆) := hmon n k hn hk hkn
      -- f(k) > L (since f(k) ≥ f(n) > L)
      have h_fk_gt_L : ltQ L (f⦅k⦆) :=
        ⟨leQ_trans L (f⦅n⦆) (f⦅k⦆) hL hfn hfk h_gt.1 h_fk_ge_fn,
         fun heq => h_gt.2 (leQ_antisymm L (f⦅n⦆) hL hfn h_gt.1
           (heq ▸ h_fk_ge_fn))⟩
      -- |f(k) − L| = f(k) − L (since f(k) > L)
      have hfkL : subQ (f⦅k⦆) L ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅k⦆) (negQ L) hfk (negQ_in_RatSet L hL)
      have h_abs_eq : absQ (subQ (f⦅k⦆) L) = subQ (f⦅k⦆) L := by
        apply if_pos
        -- leQ zeroQ (subQ (f⦅k⦆) L)
        have step := addQ_leQ_addQ L (f⦅k⦆) (negQ L)
          hL hfk (negQ_in_RatSet L hL) h_fk_gt_L.1
        rwa [negQ_addQ_right L hL] at step
      -- f(k) − L ≥ f(n) − L (since f(k) ≥ f(n))
      have h_diff_ge : leQ (subQ (f⦅n⦆) L) (subQ (f⦅k⦆) L) :=
        addQ_leQ_addQ (f⦅n⦆) (f⦅k⦆) (negQ L) hfn hfk (negQ_in_RatSet L hL) h_fk_ge_fn
      -- From convergence: |f(k) − L| < f(n) − L
      have h_lt := hN_conv k hk hkN
      rw [h_abs_eq] at h_lt
      -- But f(k) − L ≥ f(n) − L, and we need f(n) − L ≤ f(k) − L < f(n) − L. Contradiction.
      exact ltQ_irrefl (subQ (f⦅n⦆) L) hfnL
        ⟨leQ_trans (subQ (f⦅n⦆) L) (subQ (f⦅k⦆) L) (subQ (f⦅n⦆) L)
           hfnL hfkL hfnL h_diff_ge h_lt.1,
         fun heq => h_lt.2 (leQ_antisymm (subQ (f⦅k⦆) L) (subQ (f⦅n⦆) L)
           hfkL hfnL h_lt.1 (heq ▸ h_diff_ge))⟩

    /-- If f is nonincreasing and converges to L, then L ≤ f(n) for all n.
        Proof: dual of `nondecreasing_convergent_limit_ge`. -/
    theorem nonincreasing_convergent_limit_le (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (hmon : isNonincreasingQ f)
        (hconv : convergesToQ f L) :
        ∀ n : U, n ∈ (ω : U) → leQ L (f⦅n⦆) := by
      intro n hn
      apply Classical.byContradiction
      intro h_not_le
      have hfn : f⦅n⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f n hf hn
      have h_gt : ltQ (f⦅n⦆) L := by
        rcases leQ_total (f⦅n⦆) L hfn hL with h | h
        · exact ⟨h, fun heq => h_not_le (heq ▸ leQ_refl L hL)⟩
        · exact absurd h h_not_le
      -- ε = L − f(n) > 0
      have hLfn : subQ L (f⦅n⦆) ∈ (RatSet : U) :=
        addQ_in_RatSet L (negQ (f⦅n⦆)) hL (negQ_in_RatSet (f⦅n⦆) hfn)
      have hε_pos : isPositiveQ (subQ L (f⦅n⦆)) := by
        constructor
        · have step := addQ_leQ_addQ (f⦅n⦆) L (negQ (f⦅n⦆))
            hfn hL (negQ_in_RatSet (f⦅n⦆) hfn) h_gt.1
          rwa [negQ_addQ_right (f⦅n⦆) hfn] at step
        · intro h_eq
          exact h_gt.2 ((subQ_zero_iff L (f⦅n⦆) hL hfn).mp h_eq.symm).symm
      obtain ⟨N, hN, hN_conv⟩ := hconv (subQ L (f⦅n⦆)) hLfn hε_pos
      let k := maxOf n N
      have hk := maxOf_in_Omega n N hn hN
      have hkn := le_maxOf_left n N hn hN
      have hkN := le_maxOf_right n N hn hN
      have hfk : f⦅k⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f k hf hk
      -- f(k) ≤ f(n) (nonincreasing)
      have h_fk_le_fn : leQ (f⦅k⦆) (f⦅n⦆) := hmon n k hn hk hkn
      -- f(k) < L (since f(k) ≤ f(n) < L)
      have h_fk_lt_L : ltQ (f⦅k⦆) L :=
        ⟨leQ_trans (f⦅k⦆) (f⦅n⦆) L hfk hfn hL h_fk_le_fn h_gt.1,
         fun heq => h_gt.2 (leQ_antisymm (f⦅n⦆) L hfn hL h_gt.1
           (heq ▸ h_fk_le_fn))⟩
      -- L − f(k) ≥ L − f(n) (since f(k) ≤ f(n))
      have hLfk : subQ L (f⦅k⦆) ∈ (RatSet : U) :=
        addQ_in_RatSet L (negQ (f⦅k⦆)) hL (negQ_in_RatSet (f⦅k⦆) hfk)
      have h_diff_ge : leQ (subQ L (f⦅n⦆)) (subQ L (f⦅k⦆)) := by
        have h_neg_mono := negQ_antimonotone (f⦅k⦆) (f⦅n⦆) hfk hfn h_fk_le_fn
        have step := addQ_leQ_addQ (negQ (f⦅n⦆)) (negQ (f⦅k⦆)) L
          (negQ_in_RatSet (f⦅n⦆) hfn) (negQ_in_RatSet (f⦅k⦆) hfk) hL h_neg_mono
        rwa [addQ_comm (negQ (f⦅n⦆)) L (negQ_in_RatSet (f⦅n⦆) hfn) hL,
             addQ_comm (negQ (f⦅k⦆)) L (negQ_in_RatSet (f⦅k⦆) hfk) hL] at step
      -- |f(k) − L| = L − f(k)  (via absQ_symm, since L > f(k))
      have h_abs_eq : absQ (subQ (f⦅k⦆) L) = subQ L (f⦅k⦆) := by
        rw [absQ_symm (f⦅k⦆) L hfk hL]
        apply if_pos
        have step := addQ_leQ_addQ (f⦅k⦆) L (negQ (f⦅k⦆))
          hfk hL (negQ_in_RatSet (f⦅k⦆) hfk) h_fk_lt_L.1
        rwa [negQ_addQ_right (f⦅k⦆) hfk] at step
      -- |f(k) − L| < L − f(n) ≤ L − f(k), contradiction
      have h_lt := hN_conv k hk hkN
      rw [h_abs_eq] at h_lt
      exact ltQ_irrefl (subQ L (f⦅n⦆)) hLfn
        ⟨leQ_trans (subQ L (f⦅n⦆)) (subQ L (f⦅k⦆)) (subQ L (f⦅n⦆))
           hLfn hLfk hLfn h_diff_ge h_lt.1,
         fun heq => h_lt.2 (leQ_antisymm (subQ L (f⦅k⦆)) (subQ L (f⦅n⦆))
           hLfk hLfn h_lt.1 (heq ▸ h_diff_ge))⟩

    -- =========================================================================
    -- Section 4: Limits respect bounds
    -- =========================================================================

    /-- If f converges to L and is bounded above by M, then L ≤ M.

        Proof: If L > M, set ε = L − M > 0. By convergence ∃N with |f(N)−L| < ε.
        Since f(N) ≤ M < L, we have L − f(N) ≥ L − M = ε,
        so |f(N) − L| = L − f(N) ≥ ε. Contradiction. -/
    theorem limit_le_of_bounded_above (f L M : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U)) (hM : M ∈ (RatSet : U))
        (hconv : convergesToQ f L)
        (hbound : isBoundedAboveByQ f M) :
        leQ L M := by
      apply Classical.byContradiction
      intro h_not_le
      have h_gt : ltQ M L := by
        rcases leQ_total M L hM hL with h | h
        · exact ⟨h, fun heq => h_not_le (heq ▸ leQ_refl M hM)⟩
        · exact absurd h h_not_le
      -- ε = L − M > 0
      have hLM : subQ L M ∈ (RatSet : U) :=
        addQ_in_RatSet L (negQ M) hL (negQ_in_RatSet M hM)
      have hε_pos : isPositiveQ (subQ L M) := by
        constructor
        · have step := addQ_leQ_addQ M L (negQ M) hM hL (negQ_in_RatSet M hM) h_gt.1
          rwa [negQ_addQ_right M hM] at step
        · intro h_zero
          exact h_gt.2 ((subQ_zero_iff L M hL hM).mp h_zero.symm).symm
      obtain ⟨N, hN, hN_conv⟩ := hconv (subQ L M) hLM hε_pos
      have hfN : f⦅N⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f N hf hN
      have h_fN_le_M : leQ (f⦅N⦆) M := hbound N hN
      -- f(N) ≤ M < L
      have h_fN_lt_L : ltQ (f⦅N⦆) L :=
        ⟨leQ_trans (f⦅N⦆) M L hfN hM hL h_fN_le_M h_gt.1,
         fun heq => h_gt.2 (leQ_antisymm M L hM hL h_gt.1 (heq ▸ h_fN_le_M))⟩
      -- |f(N) − L| = L − f(N)  (via absQ_symm, since L > f(N))
      have hLfN : subQ L (f⦅N⦆) ∈ (RatSet : U) :=
        addQ_in_RatSet L (negQ (f⦅N⦆)) hL (negQ_in_RatSet (f⦅N⦆) hfN)
      have h_abs_eq : absQ (subQ (f⦅N⦆) L) = subQ L (f⦅N⦆) := by
        rw [absQ_symm (f⦅N⦆) L hfN hL]
        apply if_pos
        have step := addQ_leQ_addQ (f⦅N⦆) L (negQ (f⦅N⦆))
          hfN hL (negQ_in_RatSet (f⦅N⦆) hfN) h_fN_lt_L.1
        rwa [negQ_addQ_right (f⦅N⦆) hfN] at step
      -- L − f(N) ≥ L − M = ε  (from f(N) ≤ M)
      have h_diff_ge : leQ (subQ L M) (subQ L (f⦅N⦆)) := by
        have h_neg_mono := negQ_antimonotone (f⦅N⦆) M hfN hM h_fN_le_M
        have step := addQ_leQ_addQ (negQ M) (negQ (f⦅N⦆)) L
          (negQ_in_RatSet M hM) (negQ_in_RatSet (f⦅N⦆) hfN) hL h_neg_mono
        rwa [addQ_comm (negQ M) L (negQ_in_RatSet M hM) hL,
             addQ_comm (negQ (f⦅N⦆)) L (negQ_in_RatSet (f⦅N⦆) hfN) hL] at step
      -- Convergence: |f(N) − L| < ε
      have h_conv_N := hN_conv N hN (Or.inr rfl)
      rw [h_abs_eq] at h_conv_N
      -- Contradiction: ε ≤ L − f(N) < ε
      exact h_conv_N.2 (leQ_antisymm (subQ L (f⦅N⦆)) (subQ L M)
        hLfN hLM h_conv_N.1 h_diff_ge)

    /-- If f converges to L and is bounded below by M, then M ≤ L.

        Proof: dual of `limit_le_of_bounded_above`. -/
    theorem le_limit_of_bounded_below (f L M : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U)) (hM : M ∈ (RatSet : U))
        (hconv : convergesToQ f L)
        (hbound : isBoundedBelowByQ f M) :
        leQ M L := by
      apply Classical.byContradiction
      intro h_not_le
      have h_lt : ltQ L M := by
        rcases leQ_total L M hL hM with h | h
        · exact ⟨h, fun heq => h_not_le (heq ▸ leQ_refl L hL)⟩
        · exact absurd h h_not_le
      -- ε = M − L > 0
      have hML : subQ M L ∈ (RatSet : U) :=
        addQ_in_RatSet M (negQ L) hM (negQ_in_RatSet L hL)
      have hε_pos : isPositiveQ (subQ M L) := by
        constructor
        · have step := addQ_leQ_addQ L M (negQ L) hL hM (negQ_in_RatSet L hL) h_lt.1
          rwa [negQ_addQ_right L hL] at step
        · intro h_zero
          exact h_lt.2 ((subQ_zero_iff M L hM hL).mp h_zero.symm).symm
      obtain ⟨N, hN, hN_conv⟩ := hconv (subQ M L) hML hε_pos
      have hfN : f⦅N⦆ ∈ (RatSet : U) := seqTermQ_mem_RatSet f N hf hN
      have h_M_le_fN : leQ M (f⦅N⦆) := hbound N hN
      -- L < M ≤ f(N)
      have h_L_lt_fN : ltQ L (f⦅N⦆) :=
        ⟨leQ_trans L M (f⦅N⦆) hL hM hfN h_lt.1 h_M_le_fN,
         fun heq => h_lt.2 (leQ_antisymm L M hL hM h_lt.1
           (heq ▸ h_M_le_fN))⟩
      -- f(N) − L ≥ M − L = ε  (from M ≤ f(N))
      have hfNL : subQ (f⦅N⦆) L ∈ (RatSet : U) :=
        addQ_in_RatSet (f⦅N⦆) (negQ L) hfN (negQ_in_RatSet L hL)
      have h_diff_ge : leQ (subQ M L) (subQ (f⦅N⦆) L) :=
        addQ_leQ_addQ M (f⦅N⦆) (negQ L) hM hfN (negQ_in_RatSet L hL) h_M_le_fN
      -- |f(N) − L| = f(N) − L  (since f(N) > L)
      have h_abs_eq : absQ (subQ (f⦅N⦆) L) = subQ (f⦅N⦆) L := by
        apply if_pos
        have step := addQ_leQ_addQ L (f⦅N⦆) (negQ L) hL hfN (negQ_in_RatSet L hL) h_L_lt_fN.1
        rwa [negQ_addQ_right L hL] at step
      -- Convergence: |f(N) − L| < ε
      have h_conv_N := hN_conv N hN (Or.inr rfl)
      rw [h_abs_eq] at h_conv_N
      -- Contradiction: ε ≤ f(N) − L < ε
      exact h_conv_N.2 (leQ_antisymm (subQ (f⦅N⦆) L) (subQ M L)
        hfNL hML h_conv_N.1 h_diff_ge)

    -- =========================================================================
    -- Section 5: Monotone + bounded → Cauchy  (sorry: needs completeness in ℝ)
    -- =========================================================================

    /-- A nondecreasing sequence bounded above is Cauchy.

        This follows from the Monotone Convergence Theorem (MCT), which holds in ℝ
        but NOT in ℚ alone. ℚ is Archimedean but not complete, so a nondecreasing
        bounded sequence in ℚ need not converge (or be Cauchy) in ℚ.
        This theorem will be proved in `ZFC.Real.Completeness` once ℝ is available. -/
    theorem nondecreasing_bounded_isCauchy (f M : U)
        (hf : IsSeqQ f) (hM : M ∈ (RatSet : U))
        (_hmon : isNondecreasingQ f)
        (_hbound : isBoundedAboveByQ f M) :
        IsCauchyQ f := by
      sorry

    /-- A nonincreasing sequence bounded below is Cauchy.

        Dual of `nondecreasing_bounded_isCauchy`. Same sorry rationale. -/
    theorem nonincreasing_bounded_isCauchy (f M : U)
        (hf : IsSeqQ f) (hM : M ∈ (RatSet : U))
        (_hmon : isNonincreasingQ f)
        (_hbound : isBoundedBelowByQ f M) :
        IsCauchyQ f := by
      sorry

    -- =========================================================================
    -- Section 6: Corollaries
    -- =========================================================================

    /-- A nondecreasing convergent sequence is bounded above by its limit. -/
    theorem nondecreasing_convergent_isBoundedAbove (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (hmon : isNondecreasingQ f)
        (hconv : convergesToQ f L) :
        isBoundedAboveByQ f L :=
      nondecreasing_convergent_limit_ge f L hf hL hmon hconv

    /-- A nonincreasing convergent sequence is bounded below by its limit. -/
    theorem nonincreasing_convergent_isBoundedBelow (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (hmon : isNonincreasingQ f)
        (hconv : convergesToQ f L) :
        isBoundedBelowByQ f L :=
      nonincreasing_convergent_limit_le f L hf hL hmon hconv

    /-- Every convergent sequence in ℚ is bounded.
        Proof sketch: if f → L, take ε = 1. Get N s.t. for n ≥ N, |f(n)| ≤ |L| + 1.
        The bound for n < N requires a finite maximum over f(0),...,f(N-1),
        which needs additional finite-set infrastructure. Left as sorry. -/
    theorem convergent_isBounded (f L : U)
        (hf : IsSeqQ f) (hL : L ∈ (RatSet : U))
        (hconv : convergesToQ f L) :
        isBoundedQ f := by
      sorry

  end Rat.Monotone

end ZFC

export ZFC.Rat.Monotone (
  isNondecreasingQ
  isNonincreasingQ
  isStrictlyIncreasingQ
  isStrictlyDecreasingQ
  isBoundedAboveByQ
  isBoundedBelowByQ
  isBoundedQ
  constSeqQ_isNondecreasing
  constSeqQ_isNonincreasing
  strictlyIncreasing_isNondecreasing
  strictlyDecreasing_isNonincreasing
  nondecreasing_convergent_limit_ge
  nonincreasing_convergent_limit_le
  limit_le_of_bounded_above
  le_limit_of_bounded_below
  nondecreasing_bounded_isCauchy
  nonincreasing_bounded_isCauchy
  nondecreasing_convergent_isBoundedAbove
  nonincreasing_convergent_isBoundedBelow
  convergent_isBounded
)
