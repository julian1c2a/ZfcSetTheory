/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT

  # Monotone and Bounded Sequences in ℚ

  This module defines monotonicity and boundedness for sequences
  f : ω → ℚ and establishes their basic properties.

  **Note on the Archimedean argument:** ℚ is not order-complete,
  but every monotone bounded sequence in ℚ IS Cauchy — this follows
  from the Archimedean property alone (no completeness needed).
  (e.g., "Cauchy ⟹ convergent" fails in ℚ for sequences approaching √2,
  but "monotone bounded ⟹ Cauchy" holds in any Archimedean ordered field.)
  - `nondecreasing_bounded_isCauchy` and `nonincreasing_bounded_isCauchy`
    are proved here using `archQ`.
  - `convergent_isBounded` follows immediately from `cauchy_bounded`.

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
  * `convergent_isBounded`               — convergent → bounded
  * `nondecreasing_convergent_isBoundedAbove` — f↗, f→L → bounded above by L
  * `nonincreasing_convergent_isBoundedBelow` — f↘, f→L → bounded below by L
  * `nondecreasing_bounded_isCauchy`     — f↗ + bounded above → Cauchy (archQ)
  * `nonincreasing_bounded_isCauchy`     — f↘ + bounded below → Cauchy (archQ)

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.CauchyQ
import ZFC.Rat.Embedding

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
    -- Section 5: Monotone + bounded → Cauchy  (Archimedean argument)
    -- =========================================================================

    /-- addQ a (subQ b a) = b -/
    private theorem addQ_cancel (a b : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) :
        addQ a (subQ b a) = b := by
      show addQ a (addQ b (negQ a)) = b
      rw [← addQ_assoc a b (negQ a) ha hb (negQ_in_RatSet a ha),
          addQ_comm a b ha hb,
          addQ_assoc b a (negQ a) hb ha (negQ_in_RatSet a ha),
          negQ_addQ_right a ha,
          addQ_zero_right b hb]

    /-- mulQ (intToRat (natToInt (σ k))) ε = addQ (mulQ (intToRat (natToInt k)) ε) ε -/
    private theorem mulQ_intToRat_natToInt_succ (k : U) (hk : k ∈ (ω : U))
        (ε : U) (hε : ε ∈ (RatSet : U)) :
        mulQ (intToRat (natToInt (σ k))) ε =
          addQ (mulQ (intToRat (natToInt k)) ε) ε := by
      have hσ_zero : σ (∅ : U) ∈ (ω : U) := succ_in_Omega ∅ zero_in_Omega
      -- σ k = add k (σ ∅)
      have h_sigma : σ k = add k (σ (∅ : U)) := by
        rw [add_succ k ∅ hk zero_in_Omega, add_zero k hk]
      -- natToInt (σ k) = addZ (natToInt k) oneZ
      have h_ni : natToInt (σ k) = addZ (natToInt k) (oneZ : U) := by
        rw [h_sigma, natToInt_preserves_add k (σ (∅ : U)) hk hσ_zero]
        -- natToInt (σ ∅) = intClass (σ ∅) ∅ = oneZ by definition
        rfl
      -- intToRat (natToInt (σ k)) = addQ (intToRat (natToInt k)) oneQ
      have h_ir : intToRat (natToInt (σ k)) =
          addQ (intToRat (natToInt k)) (oneQ : U) := by
        rw [h_ni,
            intToRat_preserves_add (natToInt k) (oneZ : U)
              (natToInt_mem_IntSet k hk) oneZ_mem_IntSet,
            intToRat_oneZ]
      -- (intToRat k + 1) * ε = intToRat k * ε + 1 * ε = intToRat k * ε + ε
      rw [h_ir,
          mulQ_addQ_distrib_right (intToRat (natToInt k)) (oneQ : U) ε
            (intToRat_mem_RatSet (natToInt k) (natToInt_mem_IntSet k hk))
            oneQ_mem_RatSet hε,
          mulQ_one_left ε hε]

    /-- negQ (addQ a b) = addQ (negQ a) (negQ b) -/
    private theorem negQ_addQ_distrib (a b : U)
        (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) :
        negQ (addQ a b) = addQ (negQ a) (negQ b) := by
      have hab := addQ_in_RatSet a b ha hb
      have hna := negQ_in_RatSet a ha
      have hnb := negQ_in_RatSet b hb
      have hnab := negQ_in_RatSet _ hab
      have hnanb := addQ_in_RatSet _ _ hna hnb
      -- (a+b) + (negQ a + negQ b) = zeroQ
      have h_sum : addQ (addQ a b) (addQ (negQ a) (negQ b)) = zeroQ :=
        calc addQ (addQ a b) (addQ (negQ a) (negQ b))
            = addQ a (addQ b (addQ (negQ a) (negQ b))) :=
              addQ_assoc a b (addQ (negQ a) (negQ b)) ha hb hnanb
          _ = addQ a (addQ (addQ b (negQ a)) (negQ b)) := by
              rw [← addQ_assoc b (negQ a) (negQ b) hb hna hnb]
          _ = addQ a (addQ (addQ (negQ a) b) (negQ b)) := by
              rw [addQ_comm b (negQ a) hb hna]
          _ = addQ a (addQ (negQ a) (addQ b (negQ b))) := by
              rw [addQ_assoc (negQ a) b (negQ b) hna hb hnb]
          _ = addQ a (addQ (negQ a) (zeroQ : U)) := by rw [negQ_addQ_right b hb]
          _ = addQ a (negQ a) := by rw [addQ_zero_right (negQ a) hna]
          _ = zeroQ := negQ_addQ_right a ha
      -- negQ(a+b) is the unique c with (a+b)+c = zeroQ; (negQ a + negQ b) satisfies this too
      symm
      calc addQ (negQ a) (negQ b)
          = addQ (zeroQ : U) (addQ (negQ a) (negQ b)) :=
            (addQ_zero_left _ hnanb).symm
        _ = addQ (addQ (negQ (addQ a b)) (addQ a b)) (addQ (negQ a) (negQ b)) := by
            rw [negQ_addQ_left (addQ a b) hab]
        _ = addQ (negQ (addQ a b)) (addQ (addQ a b) (addQ (negQ a) (negQ b))) := by
            rw [addQ_assoc (negQ (addQ a b)) (addQ a b) (addQ (negQ a) (negQ b))
                  hnab hab hnanb]
        _ = addQ (negQ (addQ a b)) (zeroQ : U) := by rw [h_sum]
        _ = negQ (addQ a b) := addQ_zero_right _ hnab

    /-- A nondecreasing sequence bounded above is Cauchy.
        Proof: by contradiction using the Archimedean property.
        If not Cauchy with ε > 0, then for every N there are m, n ≥ N with
        |f(m)−f(n)| ≥ ε. Using nondecreasing and induction, f(0) + k·ε ≤ f(nₖ)
        for some sequence nₖ. By archQ, k·ε eventually exceeds M − f(0),
        contradicting the upper bound. -/
    theorem nondecreasing_bounded_isCauchy (f M : U)
        (hf : IsSeqQ f) (hM : M ∈ (RatSet : U))
        (hmono : isNondecreasingQ f)
        (hbound : isBoundedAboveByQ f M) :
        IsCauchyQ f := by
      intro ε hε hε_pos
      apply Classical.byContradiction
      intro h_not_exists
      -- f0 = f(0)
      let f0 : U := f⦅(∅ : U)⦆
      have hf0 : f0 ∈ (RatSet : U) := seqTermQ_mem_RatSet f ∅ hf zero_in_Omega
      -- Step A: For all N ∈ ω, ∃ m, n ≥ N with |f(m)−f(n)| ≥ ε
      have h_bad : ∀ N : U, N ∈ (ω : U) →
          ∃ m : U, m ∈ (ω : U) ∧ (N ∈ m ∨ N = m) ∧
          ∃ n : U, n ∈ (ω : U) ∧ (N ∈ n ∨ N = n) ∧
          leQ ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) := by
        intro N hN
        apply Classical.byContradiction
        intro h_good
        apply h_not_exists
        refine ⟨N, hN, ?_⟩
        intro m n hm hn hmN hnN
        apply Classical.byContradiction
        intro h_lt_fail
        apply h_good
        have hfm := seqTermQ_mem_RatSet f m hf hm
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hfmn : subQ (f⦅m⦆) (f⦅n⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅m⦆) (negQ (f⦅n⦆)) hfm (negQ_in_RatSet (f⦅n⦆) hfn)
        have habs := absQ_in_RatSet _ hfmn
        have h_le : leQ ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) := by
          rcases leQ_total ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) hε habs with h | h
          · exact h
          · have heq : absQ (subQ (f⦅m⦆) (f⦅n⦆)) = ε := by
              apply Classical.byContradiction
              intro hne
              exact h_lt_fail ⟨h, hne⟩
            exact heq ▸ leQ_refl ε hε
        exact ⟨m, hm, hmN, n, hn, hnN, h_le⟩
      -- Step B: For any N ∈ ω, ∃ p ≥ N with f(N) + ε ≤ f(p)
      have h_step : ∀ N : U, N ∈ (ω : U) →
          ∃ p : U, p ∈ (ω : U) ∧ (N ∈ p ∨ N = p) ∧
          leQ (addQ (f⦅N⦆) ε) (f⦅p⦆) := by
        intro N hN
        obtain ⟨m, hm, hmN, n, hn, hnN, h_abs⟩ := h_bad N hN
        have hfm := seqTermQ_mem_RatSet f m hf hm
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hfN := seqTermQ_mem_RatSet f N hf hN
        have hfmn : subQ (f⦅m⦆) (f⦅n⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅m⦆) (negQ (f⦅n⦆)) hfm (negQ_in_RatSet (f⦅n⦆) hfn)
        have hfnm : subQ (f⦅n⦆) (f⦅m⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅n⦆) (negQ (f⦅m⦆)) hfn (negQ_in_RatSet (f⦅m⦆) hfm)
        by_cases h_sign : leQ (zeroQ : U) (subQ (f⦅m⦆) (f⦅n⦆))
        · -- f(m) ≥ f(n); |f(m)−f(n)| = f(m)−f(n) ≥ ε; use p = m
          rw [show absQ (subQ (f⦅m⦆) (f⦅n⦆)) = subQ (f⦅m⦆) (f⦅n⦆) from
                if_pos h_sign] at h_abs
          -- f(N) ≤ f(n) (N ≤ n) and ε ≤ f(m) − f(n)
          have hfN_le_fn : leQ (f⦅N⦆) (f⦅n⦆) := hmono N n hN hn hnN
          refine ⟨m, hm, hmN, ?_⟩
          have step1 : leQ (addQ (f⦅N⦆) ε) (addQ (f⦅n⦆) ε) :=
            addQ_leQ_addQ (f⦅N⦆) (f⦅n⦆) ε hfN hfn hε hfN_le_fn
          have step2 : leQ (addQ (f⦅n⦆) ε) (addQ (f⦅n⦆) (subQ (f⦅m⦆) (f⦅n⦆))) := by
            have := addQ_leQ_addQ ε (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆) hε hfmn hfn h_abs
            rwa [addQ_comm ε (f⦅n⦆) hε hfn,
                 addQ_comm (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆) hfmn hfn] at this
          have step3 : addQ (f⦅n⦆) (subQ (f⦅m⦆) (f⦅n⦆)) = f⦅m⦆ :=
            addQ_cancel (f⦅n⦆) (f⦅m⦆) hfn hfm
          rw [← step3]
          exact leQ_trans _ _ _ (addQ_in_RatSet (f⦅N⦆) ε hfN hε)
            (addQ_in_RatSet (f⦅n⦆) ε hfn hε)
            (addQ_in_RatSet (f⦅n⦆) (subQ (f⦅m⦆) (f⦅n⦆)) hfn hfmn) step1 step2
        · -- f(m) < f(n); |f(m)−f(n)| = f(n)−f(m) ≥ ε; use p = n
          have h_fmn_le_zero : leQ (subQ (f⦅m⦆) (f⦅n⦆)) (zeroQ : U) :=
            (leQ_total (zeroQ : U) (subQ (f⦅m⦆) (f⦅n⦆))
              zeroQ_mem_RatSet hfmn).resolve_left h_sign
          -- f(m) ≤ f(n)
          have h_fm_le_fn : leQ (f⦅m⦆) (f⦅n⦆) := by
            have step := addQ_leQ_addQ (subQ (f⦅m⦆) (f⦅n⦆)) (zeroQ : U) (f⦅n⦆)
              hfmn zeroQ_mem_RatSet hfn h_fmn_le_zero
            rw [addQ_zero_left (f⦅n⦆) hfn,
                show addQ (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆) = f⦅m⦆ from by
                  show addQ (addQ (f⦅m⦆) (negQ (f⦅n⦆))) (f⦅n⦆) = f⦅m⦆
                  rw [addQ_assoc (f⦅m⦆) (negQ (f⦅n⦆)) (f⦅n⦆) hfm
                        (negQ_in_RatSet (f⦅n⦆) hfn) hfn,
                      negQ_addQ_left (f⦅n⦆) hfn,
                      addQ_zero_right (f⦅m⦆) hfm]] at step
            exact step
          -- 0 ≤ f(n) − f(m)
          have h_zero_le_fnm : leQ (zeroQ : U) (subQ (f⦅n⦆) (f⦅m⦆)) := by
            have step := addQ_leQ_addQ (f⦅m⦆) (f⦅n⦆) (negQ (f⦅m⦆))
              hfm hfn (negQ_in_RatSet (f⦅m⦆) hfm) h_fm_le_fn
            rw [negQ_addQ_right (f⦅m⦆) hfm] at step
            exact step
          -- |f(m)−f(n)| = f(n)−f(m) ≥ ε
          rw [absQ_symm (f⦅m⦆) (f⦅n⦆) hfm hfn,
              show absQ (subQ (f⦅n⦆) (f⦅m⦆)) = subQ (f⦅n⦆) (f⦅m⦆) from
                if_pos h_zero_le_fnm] at h_abs
          -- f(N) ≤ f(m) (N ≤ m) and ε ≤ f(n) − f(m)
          have hfN_le_fm : leQ (f⦅N⦆) (f⦅m⦆) := hmono N m hN hm hmN
          refine ⟨n, hn, hnN, ?_⟩
          have step1 : leQ (addQ (f⦅N⦆) ε) (addQ (f⦅m⦆) ε) :=
            addQ_leQ_addQ (f⦅N⦆) (f⦅m⦆) ε hfN hfm hε hfN_le_fm
          have step2 : leQ (addQ (f⦅m⦆) ε) (addQ (f⦅m⦆) (subQ (f⦅n⦆) (f⦅m⦆))) := by
            have := addQ_leQ_addQ ε (subQ (f⦅n⦆) (f⦅m⦆)) (f⦅m⦆) hε hfnm hfm h_abs
            rwa [addQ_comm ε (f⦅m⦆) hε hfm,
                 addQ_comm (subQ (f⦅n⦆) (f⦅m⦆)) (f⦅m⦆) hfnm hfm] at this
          have step3 : addQ (f⦅m⦆) (subQ (f⦅n⦆) (f⦅m⦆)) = f⦅n⦆ :=
            addQ_cancel (f⦅m⦆) (f⦅n⦆) hfm hfn
          rw [← step3]
          exact leQ_trans _ _ _ (addQ_in_RatSet (f⦅N⦆) ε hfN hε)
            (addQ_in_RatSet (f⦅m⦆) ε hfm hε)
            (addQ_in_RatSet (f⦅m⦆) (subQ (f⦅n⦆) (f⦅m⦆)) hfm hfnm) step1 step2
      -- Step C: Induction — ∀ k ∈ ω, ∃ p ∈ ω, f0 + k·ε ≤ f(p)
      have h_ind : ∀ k : U, k ∈ (ω : U) →
          ∃ p : U, p ∈ (ω : U) ∧
          leQ (addQ f0 (mulQ (intToRat (natToInt k)) ε)) (f⦅p⦆) := by
        let P : U → Prop := fun k =>
          ∃ p : U, p ∈ (ω : U) ∧ leQ (addQ f0 (mulQ (intToRat (natToInt k)) ε)) (f⦅p⦆)
        let S := sep (ω : U) P
        suffices hS : S = ω by
          intro k hk
          have := (hS ▸ hk : k ∈ S)
          exact ((mem_sep_iff (ω : U) k P).mp this).2
        apply induction_principle S
        · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
        · -- Base k = ∅: p = ∅, f0 + 0·ε = f0 ≤ f(0)
          rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ∅, zero_in_Omega, ?_⟩
          have : intToRat (natToInt (∅ : U)) = (zeroQ : U) := intToRat_zeroZ
          rw [this, mulQ_zero_left ε hε, addQ_zero_right f0 hf0]
          exact leQ_refl f0 hf0
        · -- Inductive step k → σk
          intro k hk
          rw [mem_sep_iff] at hk ⊢
          obtain ⟨hk_w, p_k, hp_k, h_pk_le⟩ := hk
          obtain ⟨q, hq, _, h_q_ge⟩ := h_step p_k hp_k
          have hfpk := seqTermQ_mem_RatSet f p_k hf hp_k
          have hfq  := seqTermQ_mem_RatSet f q hf hq
          have hmulkε : mulQ (intToRat (natToInt k)) ε ∈ (RatSet : U) :=
            mulQ_in_RatSet (intToRat (natToInt k)) ε
              (intToRat_mem_RatSet (natToInt k) (natToInt_mem_IntSet k hk_w)) hε
          have hf0kε : addQ f0 (mulQ (intToRat (natToInt k)) ε) ∈ (RatSet : U) :=
            addQ_in_RatSet f0 (mulQ (intToRat (natToInt k)) ε) hf0 hmulkε
          refine ⟨succ_in_Omega k hk_w, q, hq, ?_⟩
          -- f0 + (σk)·ε = (f0 + k·ε) + ε ≤ f(p_k) + ε ≤ f(q)
          rw [mulQ_intToRat_natToInt_succ k hk_w ε hε,
              show addQ f0 (addQ (mulQ (intToRat (natToInt k)) ε) ε) =
                  addQ (addQ f0 (mulQ (intToRat (natToInt k)) ε)) ε from
                (addQ_assoc f0 (mulQ (intToRat (natToInt k)) ε) ε
                  hf0 hmulkε hε).symm]
          exact leQ_trans _ _ _
            (addQ_in_RatSet (addQ f0 (mulQ (intToRat (natToInt k)) ε)) ε hf0kε hε)
            (addQ_in_RatSet (f⦅p_k⦆) ε hfpk hε)
            hfq
            (addQ_leQ_addQ _ _ ε hf0kε hfpk hε h_pk_le)
            h_q_ge
      -- Step D: archQ gives K with M − f0 ≤ K·ε; use h_ind with σK for contradiction
      have hMf0 : subQ M f0 ∈ (RatSet : U) :=
        addQ_in_RatSet M (negQ f0) hM (negQ_in_RatSet f0 hf0)
      obtain ⟨K, hK, hK_le⟩ := archQ (subQ M f0) ε hMf0 hε hε_pos
      obtain ⟨p, hp, h_fp_ge⟩ := h_ind (σ K) (succ_in_Omega K hK)
      have hfp := seqTermQ_mem_RatSet f p hf hp
      have hmulKε : mulQ (intToRat (natToInt K)) ε ∈ (RatSet : U) :=
        mulQ_in_RatSet (intToRat (natToInt K)) ε
          (intToRat_mem_RatSet (natToInt K) (natToInt_mem_IntSet K hK)) hε
      have hf0Kε : addQ f0 (mulQ (intToRat (natToInt K)) ε) ∈ (RatSet : U) :=
        addQ_in_RatSet f0 (mulQ (intToRat (natToInt K)) ε) hf0 hmulKε
      -- M ≤ f0 + K·ε  (from M − f0 ≤ K·ε)
      have h_M_le : leQ M (addQ f0 (mulQ (intToRat (natToInt K)) ε)) := by
        have step := addQ_leQ_addQ (subQ M f0) (mulQ (intToRat (natToInt K)) ε) f0
          hMf0 hmulKε hf0 hK_le
        rw [show addQ (subQ M f0) f0 = M from by
              show addQ (addQ M (negQ f0)) f0 = M
              rw [addQ_assoc M (negQ f0) f0 hM (negQ_in_RatSet f0 hf0) hf0,
                  negQ_addQ_left f0 hf0, addQ_zero_right M hM],
            addQ_comm (mulQ (intToRat (natToInt K)) ε) f0 hmulKε hf0] at step
        exact step
      -- M < M + ε  (since ε > 0)
      have h_M_lt_Me : ltQ M (addQ M ε) := by
        constructor
        · have := addQ_leQ_addQ (zeroQ : U) ε M zeroQ_mem_RatSet hε hM hε_pos.1
          rwa [addQ_zero_left M hM, addQ_comm ε M hε hM] at this
        · intro heq
          -- M = M + ε → ε = 0, contradiction
          have : (zeroQ : U) = ε := by
            have h1 : addQ (negQ M) M = (zeroQ : U) := negQ_addQ_left M hM
            have h2 : addQ (negQ M) (addQ M ε) = ε := by
              rw [← addQ_assoc (negQ M) M ε (negQ_in_RatSet M hM) hM hε,
                  negQ_addQ_left M hM, addQ_zero_left ε hε]
            rw [← heq] at h2
            exact h1.symm.trans h2
          exact hε_pos.2 this
      -- M + ε ≤ f0 + (σK)·ε
      have hmulσKε : mulQ (intToRat (natToInt (σ K))) ε ∈ (RatSet : U) :=
        mulQ_in_RatSet (intToRat (natToInt (σ K))) ε
          (intToRat_mem_RatSet (natToInt (σ K)) (natToInt_mem_IntSet (σ K)
            (succ_in_Omega K hK))) hε
      have hfσKε : addQ f0 (mulQ (intToRat (natToInt (σ K))) ε) ∈ (RatSet : U) :=
        addQ_in_RatSet f0 (mulQ (intToRat (natToInt (σ K))) ε) hf0 hmulσKε
      have h_Me_le : leQ (addQ M ε) (addQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) := by
        rw [mulQ_intToRat_natToInt_succ K hK ε hε,
            (addQ_assoc f0 (mulQ (intToRat (natToInt K)) ε) ε hf0 hmulKε hε).symm]
        exact addQ_leQ_addQ M (addQ f0 (mulQ (intToRat (natToInt K)) ε)) ε
          hM hf0Kε hε h_M_le
      -- ltQ M (f0 + (σK)·ε): M < M+ε ≤ f0+(σK)·ε
      have h_lt_M : ltQ M (addQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) :=
        ⟨leQ_trans M (addQ M ε) _ hM (addQ_in_RatSet M ε hM hε) hfσKε
          h_M_lt_Me.1 h_Me_le,
         fun heq =>
           h_M_lt_Me.2 (leQ_antisymm M (addQ M ε) hM (addQ_in_RatSet M ε hM hε)
             h_M_lt_Me.1 (heq ▸ h_Me_le))⟩
      -- h_fp_ge: f0 + (σK)·ε ≤ f(p); hbound: f(p) ≤ M
      -- So M < f(p) ≤ M: contradiction via M = f(p) and M ≠ f0+(σK)·ε
      have h_fp_le_M : leQ (f⦅p⦆) M := hbound p hp
      have h_M_eq_fp : M = f⦅p⦆ :=
        leQ_antisymm M (f⦅p⦆) hM hfp
          (leQ_trans M _ (f⦅p⦆) hM hfσKε hfp h_lt_M.1 h_fp_ge)
          h_fp_le_M
      exact h_lt_M.2
        (leQ_antisymm M (addQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) hM hfσKε
          h_lt_M.1
          (h_M_eq_fp ▸ h_fp_ge))

    /-- A nonincreasing sequence bounded below is Cauchy.
        Proof: Archimedean argument (dual of `nondecreasing_bounded_isCauchy`).
        If not Cauchy with ε > 0, then for every N there are m, n ≥ N with
        |f(m)−f(n)| ≥ ε. Using nonincreasing and induction, f(nₖ) ≤ f(0) − k·ε
        for some sequence nₖ. By archQ, k·ε eventually exceeds f(0) − M,
        contradicting the lower bound. -/
    theorem nonincreasing_bounded_isCauchy (f M : U)
        (hf : IsSeqQ f) (hM : M ∈ (RatSet : U))
        (hmono : isNonincreasingQ f)
        (hbound : isBoundedBelowByQ f M) :
        IsCauchyQ f := by
      intro ε hε hε_pos
      apply Classical.byContradiction
      intro h_not_exists
      let f0 : U := f⦅(∅ : U)⦆
      have hf0 : f0 ∈ (RatSet : U) := seqTermQ_mem_RatSet f ∅ hf zero_in_Omega
      -- Step A: For all N ∈ ω, ∃ m, n ≥ N with |f(m)−f(n)| ≥ ε
      have h_bad : ∀ N : U, N ∈ (ω : U) →
          ∃ m : U, m ∈ (ω : U) ∧ (N ∈ m ∨ N = m) ∧
          ∃ n : U, n ∈ (ω : U) ∧ (N ∈ n ∨ N = n) ∧
          leQ ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) := by
        intro N hN
        apply Classical.byContradiction
        intro h_good
        apply h_not_exists
        refine ⟨N, hN, ?_⟩
        intro m n hm hn hmN hnN
        apply Classical.byContradiction
        intro h_lt_fail
        apply h_good
        have hfm := seqTermQ_mem_RatSet f m hf hm
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hfmn : subQ (f⦅m⦆) (f⦅n⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅m⦆) (negQ (f⦅n⦆)) hfm (negQ_in_RatSet (f⦅n⦆) hfn)
        have habs := absQ_in_RatSet _ hfmn
        have h_le : leQ ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) := by
          rcases leQ_total ε (absQ (subQ (f⦅m⦆) (f⦅n⦆))) hε habs with h | h
          · exact h
          · have heq : absQ (subQ (f⦅m⦆) (f⦅n⦆)) = ε := by
              apply Classical.byContradiction
              intro hne
              exact h_lt_fail ⟨h, hne⟩
            exact heq ▸ leQ_refl ε hε
        exact ⟨m, hm, hmN, n, hn, hnN, h_le⟩
      -- Step B: For any N ∈ ω, ∃ p ≥ N with f(p) ≤ f(N) − ε
      have h_step : ∀ N : U, N ∈ (ω : U) →
          ∃ p : U, p ∈ (ω : U) ∧ (N ∈ p ∨ N = p) ∧
          leQ (f⦅p⦆) (subQ (f⦅N⦆) ε) := by
        intro N hN
        obtain ⟨m, hm, hmN, n, hn, hnN, h_abs⟩ := h_bad N hN
        have hfm := seqTermQ_mem_RatSet f m hf hm
        have hfn := seqTermQ_mem_RatSet f n hf hn
        have hfN := seqTermQ_mem_RatSet f N hf hN
        have hfmn : subQ (f⦅m⦆) (f⦅n⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅m⦆) (negQ (f⦅n⦆)) hfm (negQ_in_RatSet (f⦅n⦆) hfn)
        have hfnm : subQ (f⦅n⦆) (f⦅m⦆) ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅n⦆) (negQ (f⦅m⦆)) hfn (negQ_in_RatSet (f⦅m⦆) hfm)
        have hfNε : subQ (f⦅N⦆) ε ∈ (RatSet : U) :=
          addQ_in_RatSet (f⦅N⦆) (negQ ε) hfN (negQ_in_RatSet ε hε)
        -- Helper: a ≤ b − ε from ε ≤ b − a (i.e., a + ε ≤ b)
        by_cases h_sign : leQ (zeroQ : U) (subQ (f⦅m⦆) (f⦅n⦆))
        · -- Case 1: fm ≥ fn; |fm−fn| = fm−fn ≥ ε; use p = n
          rw [show absQ (subQ (f⦅m⦆) (f⦅n⦆)) = subQ (f⦅m⦆) (f⦅n⦆) from
                if_pos h_sign] at h_abs
          -- fn ≤ fm − ε (from ε ≤ fm − fn)
          have h_fn_le : leQ (f⦅n⦆) (subQ (f⦅m⦆) ε) := by
            have step1 := addQ_leQ_addQ ε (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆)
              hε hfmn hfn h_abs
            rw [addQ_comm ε (f⦅n⦆) hε hfn,
                addQ_comm (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆) hfmn hfn,
                addQ_cancel (f⦅n⦆) (f⦅m⦆) hfn hfm] at step1
            -- step1 : leQ (addQ fn ε) fm
            have step2 := addQ_leQ_addQ (addQ (f⦅n⦆) ε) (f⦅m⦆) (negQ ε)
              (addQ_in_RatSet (f⦅n⦆) ε hfn hε) hfm (negQ_in_RatSet ε hε) step1
            rw [show addQ (addQ (f⦅n⦆) ε) (negQ ε) = f⦅n⦆ from by
                  rw [addQ_assoc (f⦅n⦆) ε (negQ ε) hfn hε (negQ_in_RatSet ε hε),
                      negQ_addQ_right ε hε, addQ_zero_right (f⦅n⦆) hfn]] at step2
            exact step2
          -- fm ≤ fN (nonincreasing, N ≤ m)
          have hfm_le_fN : leQ (f⦅m⦆) (f⦅N⦆) := hmono N m hN hm hmN
          -- fn ≤ fm − ε ≤ fN − ε
          refine ⟨n, hn, hnN, leQ_trans _ _ _ hfn
            (addQ_in_RatSet (f⦅m⦆) (negQ ε) hfm (negQ_in_RatSet ε hε)) hfNε
            h_fn_le
            (addQ_leQ_addQ (f⦅m⦆) (f⦅N⦆) (negQ ε) hfm hfN (negQ_in_RatSet ε hε) hfm_le_fN)⟩
        · -- Case 2: fn > fm; |fm−fn| = fn−fm ≥ ε; use p = m
          have h_fmn_le_zero : leQ (subQ (f⦅m⦆) (f⦅n⦆)) (zeroQ : U) :=
            (leQ_total (zeroQ : U) (subQ (f⦅m⦆) (f⦅n⦆))
              zeroQ_mem_RatSet hfmn).resolve_left h_sign
          have h_zero_le_fnm : leQ (zeroQ : U) (subQ (f⦅n⦆) (f⦅m⦆)) := by
            have h_fm_le_fn : leQ (f⦅m⦆) (f⦅n⦆) := by
              have step := addQ_leQ_addQ (subQ (f⦅m⦆) (f⦅n⦆)) (zeroQ : U) (f⦅n⦆)
                hfmn zeroQ_mem_RatSet hfn h_fmn_le_zero
              rw [addQ_zero_left (f⦅n⦆) hfn,
                  show addQ (subQ (f⦅m⦆) (f⦅n⦆)) (f⦅n⦆) = f⦅m⦆ from by
                    show addQ (addQ (f⦅m⦆) (negQ (f⦅n⦆))) (f⦅n⦆) = f⦅m⦆
                    rw [addQ_assoc (f⦅m⦆) (negQ (f⦅n⦆)) (f⦅n⦆) hfm
                          (negQ_in_RatSet (f⦅n⦆) hfn) hfn,
                        negQ_addQ_left (f⦅n⦆) hfn,
                        addQ_zero_right (f⦅m⦆) hfm]] at step
              exact step
            have step := addQ_leQ_addQ (f⦅m⦆) (f⦅n⦆) (negQ (f⦅m⦆))
              hfm hfn (negQ_in_RatSet (f⦅m⦆) hfm) h_fm_le_fn
            rw [negQ_addQ_right (f⦅m⦆) hfm] at step
            exact step
          rw [absQ_symm (f⦅m⦆) (f⦅n⦆) hfm hfn,
              show absQ (subQ (f⦅n⦆) (f⦅m⦆)) = subQ (f⦅n⦆) (f⦅m⦆) from
                if_pos h_zero_le_fnm] at h_abs
          -- fm ≤ fn − ε (from ε ≤ fn − fm)
          have h_fm_le : leQ (f⦅m⦆) (subQ (f⦅n⦆) ε) := by
            have step1 := addQ_leQ_addQ ε (subQ (f⦅n⦆) (f⦅m⦆)) (f⦅m⦆)
              hε hfnm hfm h_abs
            rw [addQ_comm ε (f⦅m⦆) hε hfm,
                addQ_comm (subQ (f⦅n⦆) (f⦅m⦆)) (f⦅m⦆) hfnm hfm,
                addQ_cancel (f⦅m⦆) (f⦅n⦆) hfm hfn] at step1
            have step2 := addQ_leQ_addQ (addQ (f⦅m⦆) ε) (f⦅n⦆) (negQ ε)
              (addQ_in_RatSet (f⦅m⦆) ε hfm hε) hfn (negQ_in_RatSet ε hε) step1
            rw [show addQ (addQ (f⦅m⦆) ε) (negQ ε) = f⦅m⦆ from by
                  rw [addQ_assoc (f⦅m⦆) ε (negQ ε) hfm hε (negQ_in_RatSet ε hε),
                      negQ_addQ_right ε hε, addQ_zero_right (f⦅m⦆) hfm]] at step2
            exact step2
          -- fn ≤ fN (nonincreasing, N ≤ n)
          have hfn_le_fN : leQ (f⦅n⦆) (f⦅N⦆) := hmono N n hN hn hnN
          -- fm ≤ fn − ε ≤ fN − ε
          refine ⟨m, hm, hmN, leQ_trans _ _ _ hfm
            (addQ_in_RatSet (f⦅n⦆) (negQ ε) hfn (negQ_in_RatSet ε hε)) hfNε
            h_fm_le
            (addQ_leQ_addQ (f⦅n⦆) (f⦅N⦆) (negQ ε) hfn hfN (negQ_in_RatSet ε hε) hfn_le_fN)⟩
      -- Step C: Induction — ∀ k ∈ ω, ∃ p ∈ ω, f(p) ≤ f0 − k·ε
      have h_ind : ∀ k : U, k ∈ (ω : U) →
          ∃ p : U, p ∈ (ω : U) ∧
          leQ (f⦅p⦆) (subQ f0 (mulQ (intToRat (natToInt k)) ε)) := by
        let P : U → Prop := fun k =>
          ∃ p : U, p ∈ (ω : U) ∧ leQ (f⦅p⦆) (subQ f0 (mulQ (intToRat (natToInt k)) ε))
        let S := sep (ω : U) P
        suffices hS : S = ω by
          intro k hk
          have := (hS ▸ hk : k ∈ S)
          exact ((mem_sep_iff (ω : U) k P).mp this).2
        apply induction_principle S
        · exact fun x hx => ((mem_sep_iff (ω : U) x P).mp hx).1
        · -- Base k = ∅: p = ∅, f(0) = f0 ≤ f0 − 0·ε = f0
          rw [mem_sep_iff]
          refine ⟨zero_in_Omega, ∅, zero_in_Omega, ?_⟩
          rw [show intToRat (natToInt (∅ : U)) = (zeroQ : U) from intToRat_zeroZ,
              mulQ_zero_left ε hε,
              show subQ f0 (zeroQ : U) = f0 from by
                show addQ f0 (negQ (zeroQ : U)) = f0
                rw [show negQ (zeroQ : U) = (zeroQ : U) from by
                      have := negQ_addQ_right (zeroQ : U) zeroQ_mem_RatSet
                      rw [addQ_zero_left (negQ (zeroQ : U)) (negQ_in_RatSet _ zeroQ_mem_RatSet)]
                        at this
                      exact this,
                    addQ_zero_right f0 hf0]]
          exact leQ_refl f0 hf0
        · -- Inductive step k → σk
          intro k hk
          rw [mem_sep_iff] at hk ⊢
          obtain ⟨hk_w, p_k, hp_k, h_pk_le⟩ := hk
          obtain ⟨q, hq, _, h_q_le⟩ := h_step p_k hp_k
          have hfpk := seqTermQ_mem_RatSet f p_k hf hp_k
          have hfq  := seqTermQ_mem_RatSet f q hf hq
          have hmulkε : mulQ (intToRat (natToInt k)) ε ∈ (RatSet : U) :=
            mulQ_in_RatSet (intToRat (natToInt k)) ε
              (intToRat_mem_RatSet (natToInt k) (natToInt_mem_IntSet k hk_w)) hε
          have hf0kε : subQ f0 (mulQ (intToRat (natToInt k)) ε) ∈ (RatSet : U) :=
            addQ_in_RatSet f0 (negQ (mulQ (intToRat (natToInt k)) ε))
              hf0 (negQ_in_RatSet _ hmulkε)
          have hpkε : subQ (f⦅p_k⦆) ε ∈ (RatSet : U) :=
            addQ_in_RatSet (f⦅p_k⦆) (negQ ε) hfpk (negQ_in_RatSet ε hε)
          refine ⟨succ_in_Omega k hk_w, q, hq, ?_⟩
          -- f(q) ≤ f(p_k) − ε ≤ (f0 − k·ε) − ε = f0 − (k+1)·ε = f0 − (σk)·ε
          rw [mulQ_intToRat_natToInt_succ k hk_w ε hε,
              show subQ f0 (addQ (mulQ (intToRat (natToInt k)) ε) ε) =
                  subQ (subQ f0 (mulQ (intToRat (natToInt k)) ε)) ε from by
                show addQ f0 (negQ (addQ (mulQ (intToRat (natToInt k)) ε) ε)) =
                    addQ (addQ f0 (negQ (mulQ (intToRat (natToInt k)) ε))) (negQ ε)
                rw [negQ_addQ_distrib _ _ hmulkε hε,
                    addQ_assoc f0 (negQ (mulQ (intToRat (natToInt k)) ε)) (negQ ε)
                      hf0 (negQ_in_RatSet _ hmulkε) (negQ_in_RatSet ε hε)]]
          -- f(q) ≤ f(p_k) − ε (h_q_le) and f(p_k) − ε ≤ (f0 − k·ε) − ε (h_pk_le + addQ_leQ)
          exact leQ_trans _ _ _ hfq hpkε
            (addQ_in_RatSet _ (negQ ε) hf0kε (negQ_in_RatSet ε hε)) h_q_le
            (addQ_leQ_addQ (f⦅p_k⦆) (subQ f0 (mulQ (intToRat (natToInt k)) ε))
              (negQ ε) hfpk hf0kε (negQ_in_RatSet ε hε) h_pk_le)
      -- Step D: archQ gives K with f0 − M ≤ K·ε; then h_ind(σK) contradicts hbound.
      have hf0M : subQ f0 M ∈ (RatSet : U) :=
        addQ_in_RatSet f0 (negQ M) hf0 (negQ_in_RatSet M hM)
      obtain ⟨K, hK, hK_le⟩ := archQ (subQ f0 M) ε hf0M hε hε_pos
      obtain ⟨p, hp, h_fp_le⟩ := h_ind (σ K) (succ_in_Omega K hK)
      have hfp := seqTermQ_mem_RatSet f p hf hp
      have hmulKε : mulQ (intToRat (natToInt K)) ε ∈ (RatSet : U) :=
        mulQ_in_RatSet (intToRat (natToInt K)) ε
          (intToRat_mem_RatSet (natToInt K) (natToInt_mem_IntSet K hK)) hε
      have hf0kε_K : subQ f0 (mulQ (intToRat (natToInt K)) ε) ∈ (RatSet : U) :=
        addQ_in_RatSet f0 (negQ (mulQ (intToRat (natToInt K)) ε))
          hf0 (negQ_in_RatSet _ hmulKε)
      -- f0 − K·ε ≤ M  (from f0 − M ≤ K·ε)
      have h_f0Kε_le_M : leQ (subQ f0 (mulQ (intToRat (natToInt K)) ε)) M := by
        have step := addQ_leQ_addQ (subQ f0 M) (mulQ (intToRat (natToInt K)) ε) M
          hf0M hmulKε hM hK_le
        rw [show addQ (subQ f0 M) M = f0 from by
              show addQ (addQ f0 (negQ M)) M = f0
              rw [addQ_assoc f0 (negQ M) M hf0 (negQ_in_RatSet M hM) hM,
                  negQ_addQ_left M hM, addQ_zero_right f0 hf0],
            addQ_comm (mulQ (intToRat (natToInt K)) ε) M hmulKε hM] at step
        -- step: f0 ≤ M + K·ε; want: f0 − K·ε ≤ M (subtract K·ε from both sides)
        have step2 := addQ_leQ_addQ f0 (addQ M (mulQ (intToRat (natToInt K)) ε))
          (negQ (mulQ (intToRat (natToInt K)) ε))
          hf0 (addQ_in_RatSet M _ hM hmulKε) (negQ_in_RatSet _ hmulKε) step
        rw [show addQ (addQ M (mulQ (intToRat (natToInt K)) ε))
              (negQ (mulQ (intToRat (natToInt K)) ε)) = M from by
              rw [addQ_assoc M _ (negQ (mulQ (intToRat (natToInt K)) ε))
                    hM hmulKε (negQ_in_RatSet _ hmulKε),
                  negQ_addQ_right _ hmulKε, addQ_zero_right M hM]] at step2
        exact step2
      -- f0 − (σK)·ε + ε = f0 − K·ε  (algebraic identity used in contradiction)
      have hmulσKε : mulQ (intToRat (natToInt (σ K))) ε ∈ (RatSet : U) :=
        mulQ_in_RatSet (intToRat (natToInt (σ K))) ε
          (intToRat_mem_RatSet (natToInt (σ K))
            (natToInt_mem_IntSet (σ K) (succ_in_Omega K hK))) hε
      have hfσKε : subQ f0 (mulQ (intToRat (natToInt (σ K))) ε) ∈ (RatSet : U) :=
        addQ_in_RatSet f0 (negQ (mulQ (intToRat (natToInt (σ K))) ε))
          hf0 (negQ_in_RatSet _ hmulσKε)
      -- M ≤ f(p) ≤ f0 − (σK)·ε (chain via hbound and h_fp_le)
      have h_M_le_σ : leQ M (subQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) :=
        leQ_trans M (f⦅p⦆) _ hM hfp hfσKε (hbound p hp) h_fp_le
      -- f0 − (σK)·ε + ε = f0 − K·ε
      have h_step_back :
          addQ (subQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) ε =
          subQ f0 (mulQ (intToRat (natToInt K)) ε) := by
        rw [mulQ_intToRat_natToInt_succ K hK ε hε,
            show subQ f0 (addQ (mulQ (intToRat (natToInt K)) ε) ε) =
                subQ (subQ f0 (mulQ (intToRat (natToInt K)) ε)) ε from by
              show addQ f0 (negQ (addQ (mulQ (intToRat (natToInt K)) ε) ε)) =
                  addQ (addQ f0 (negQ (mulQ (intToRat (natToInt K)) ε))) (negQ ε)
              rw [negQ_addQ_distrib _ _ hmulKε hε,
                  addQ_assoc f0 (negQ (mulQ (intToRat (natToInt K)) ε)) (negQ ε)
                    hf0 (negQ_in_RatSet _ hmulKε) (negQ_in_RatSet ε hε)]]
        show addQ (addQ (subQ f0 (mulQ (intToRat (natToInt K)) ε)) (negQ ε)) ε =
            subQ f0 (mulQ (intToRat (natToInt K)) ε)
        rw [addQ_assoc _ (negQ ε) ε hf0kε_K (negQ_in_RatSet ε hε) hε,
            negQ_addQ_left ε hε, addQ_zero_right _ hf0kε_K]
      -- M + ε ≤ f0 − (σK)·ε + ε = f0 − K·ε ≤ M → M + ε ≤ M → ε ≤ 0
      have h_Me_le_M : leQ (addQ M ε) M := by
        have step1 : leQ (addQ M ε) (addQ (subQ f0 (mulQ (intToRat (natToInt (σ K))) ε)) ε) :=
          addQ_leQ_addQ M _ ε hM hfσKε hε h_M_le_σ
        rw [h_step_back] at step1
        exact leQ_trans _ _ _ (addQ_in_RatSet M ε hM hε) hf0kε_K hM step1 h_f0Kε_le_M
      -- get ε ≤ 0 via: M + ε ≤ M means M + (negQ M) + ε ≤ M + (negQ M)
      have h_ε_le_0 : leQ ε (zeroQ : U) := by
        have step := addQ_leQ_addQ (addQ M ε) M (negQ M)
          (addQ_in_RatSet M ε hM hε) hM (negQ_in_RatSet M hM) h_Me_le_M
        rw [negQ_addQ_right M hM,
            show addQ (addQ M ε) (negQ M) = ε from by
              rw [addQ_assoc M ε (negQ M) hM hε (negQ_in_RatSet M hM),
                  addQ_comm ε (negQ M) hε (negQ_in_RatSet M hM),
                  ← addQ_assoc M (negQ M) ε hM (negQ_in_RatSet M hM) hε,
                  negQ_addQ_right M hM, addQ_zero_left ε hε]] at step
        exact step
      -- ε ≤ 0 contradicts ε > 0 (i.e., 0 ≤ ε and 0 ≠ ε)
      exact hε_pos.2 (leQ_antisymm _ _ zeroQ_mem_RatSet hε hε_pos.1 h_ε_le_0)

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
        isBoundedQ f :=
      cauchy_bounded f hf (cauchy_of_convergentQ f L hf hL hconv)

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
  nondecreasing_convergent_isBoundedAbove
  nonincreasing_convergent_isBoundedBelow
  convergent_isBounded
  nondecreasing_bounded_isCauchy
  nonincreasing_bounded_isCauchy
)
