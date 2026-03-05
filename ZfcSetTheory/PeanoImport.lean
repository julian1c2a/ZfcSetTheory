import ZfcSetTheory.NaturalNumbers
import ZfcSetTheory.Infinity
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  This module establishes an isomorphism between the Von Neumann natural numbers
  defined in this project and the Peano natural numbers from the `peanolib` library.
-/

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  open SetUniverse.NaturalNumbers

  universe u
  variable {U : Type u}

  -- =========================================================================
  -- Section 1: The bijection between Peano and Von Neumann naturals
  -- =========================================================================

  /-- Converts a Peano natural number to its Von Neumann representation. -/
  noncomputable def fromPeano : Peano.ℕ₀ → U
    | Peano.ℕ₀.zero    => (∅ : U)
    | Peano.ℕ₀.succ n' => successor (fromPeano n')

  /-- `ΠZ p` : canonical embedding Peano ℕ → Von Neumann ℕ.
      Typed as `\PiZ` in the editor.
      Note: `Π` is a reserved Lean 4 token; `ΠZ` works as a registered notation.
      In theorem headers where `U` cannot be inferred, use the type ascription
      `(ΠZ p : U)` or `(ΠZ : Peano.ℕ₀ → U)`. -/
  scoped notation "ΠZ" => fromPeano

  /-- `ΠZ` maps Peano naturals to Von Neumann naturals. -/
  theorem fromPeano_is_nat (n : Peano.ℕ₀) : isNat (ΠZ n : U) := by
    induction n with
    | zero       => exact zero_is_nat
    | succ n' ih => exact nat_successor_is_nat (ΠZ n') ih

  /-- `ΠZ` is injective. -/
  theorem fromPeano_injective : Function.Injective (ΠZ : Peano.ℕ₀ → U) := by
    -- ih : ∀ ⦃b⦄, ΠZ m' = ΠZ b → m' = b
    -- Lean infers b from the proof, so use `ih proof` not `ih n' proof`.
    intro m
    induction m with
    | zero =>
      intro n h
      cases n with
      | zero   => rfl
      | succ n' => exact absurd h (Ne.symm (successor_nonempty (ΠZ n')))
    | succ m' ih =>
      intro n h
      cases n with
      | zero => exact absurd h (successor_nonempty (ΠZ m'))
      | succ n' =>
        congr 1
        apply ih
        exact successor_injective (ΠZ m') (ΠZ n')
          (fromPeano_is_nat m') (fromPeano_is_nat n') h

  /-- Every Von Neumann natural is in the image of `ΠZ`. -/
  theorem fromPeano_surjective (n : U) (hn : isNat n) :
      ∃ p : Peano.ℕ₀, (ΠZ p : U) = n := by
    -- S = { m ∈ ω | ∃ p : ℕ₀, ΠZ p = m }
    let S := SpecSet (ω : U) (fun m => ∃ p : Peano.ℕ₀, (ΠZ p : U) = m)
    suffices h : S = (ω : U) by
      have hn_in_S : n ∈ S := by rw [h]; exact Nat_in_Omega n hn
      rw [SpecSet_is_specified] at hn_in_S
      exact hn_in_S.2
    apply strong_induction_principle S
      (fun z hz => by rw [SpecSet_is_specified] at hz; exact hz.1)
    intro m hm ih
    rw [SpecSet_is_specified]
    refine ⟨hm, ?_⟩
    rcases nat_is_zero_or_succ m (mem_Omega_is_Nat m hm) with rfl | ⟨k, rfl⟩
    · -- m = ∅ : ΠZ ℕ₀.zero = ∅
      exact ⟨Peano.ℕ₀.zero, rfl⟩
    · -- m = σ k : use IH on k ∈ m
      have hk_in_S : k ∈ S := ih k (mem_successor_self k)
      rw [SpecSet_is_specified] at hk_in_S
      obtain ⟨p, hp⟩ := hk_in_S.2
      -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) = σ k
      exact ⟨Peano.ℕ₀.succ p,
        show successor (ΠZ p : U) = successor k from by rw [hp]⟩

  /-- `ZΠ n h` : inverse isomorphism Von Neumann ℕ → Peano ℕ.
      Typed as `Z\Pi` in the editor. -/
  noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ₀ :=
    Classical.choose (fromPeano_surjective n hn)

  scoped notation "ZΠ" => toPeano

  /-- `ΠZ (ZΠ n hn) = n`. -/
  theorem fromPeano_toPeano (n : U) (hn : isNat n) :
      ΠZ (ZΠ n hn) = n :=
    Classical.choose_spec (fromPeano_surjective n hn)

  /-- `ZΠ (ΠZ p) _ = p`. -/
  theorem toPeano_fromPeano (p : Peano.ℕ₀) :
      ZΠ (ΠZ p : U) (fromPeano_is_nat p) = p :=
    fromPeano_injective (fromPeano_toPeano (ΠZ p) (fromPeano_is_nat p))

  /-- `ZΠ` is injective on Von Neumann naturals. -/
  theorem toPeano_injective {m n : U} (hm : isNat m) (hn : isNat n)
      (h : ZΠ m hm = ZΠ n hn) : m = n := by
    rw [← fromPeano_toPeano m hm, ← fromPeano_toPeano n hn, h]

  /-- `ZΠ` is surjective onto Peano naturals. -/
  theorem toPeano_surjective (p : Peano.ℕ₀) :
      ∃ (n : U) (hn : isNat n), ZΠ n hn = p :=
    ⟨(ΠZ p : U), fromPeano_is_nat p, toPeano_fromPeano p⟩

  -- =========================================================================
  -- Section 2: The bijection is an isomorphism of Peano algebras
  -- =========================================================================

  /-- `ZΠ` maps ∅ to `Peano.ℕ₀.zero`.
      Together with `toPeano_successor`, this shows the bijection is a
      homomorphism of Peano algebras in both directions. -/
  theorem toPeano_zero :
      ZΠ (∅ : U) zero_is_nat = Peano.ℕ₀.zero :=
    -- ΠZ Peano.ℕ₀.zero = ∅ by definition, so fromPeano_toPeano gives
    -- ΠZ (ZΠ ∅ _) = ∅ = ΠZ ℕ₀.zero; injectivity concludes.
    fromPeano_injective (fromPeano_toPeano (∅ : U) zero_is_nat)

  /-- `ZΠ` commutes with successor: the bijection is a homomorphism of
      the successor structure in both directions. -/
  theorem toPeano_successor (n : U) (hn : isNat n) :
      ZΠ (σ n) (nat_successor_is_nat n hn) =
      Peano.ℕ₀.succ (ZΠ n hn) := by
    apply fromPeano_injective
    -- Goal: ΠZ (ZΠ (σ n) _) = ΠZ (ℕ₀.succ (ZΠ n hn))
    rw [fromPeano_toPeano]
    -- Goal: σ n = ΠZ (ℕ₀.succ (ZΠ n hn))
    -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) by definition
    show successor n = successor (ΠZ (ZΠ n hn))
    rw [fromPeano_toPeano]

  -- =========================================================================
  -- Section 3: Recursion transport theorems
  -- =========================================================================

  /-- **Recursion transport (VN → Peano)**: any Von Neumann recursive function
      `F : ω → U` induces a Peano recursive function via `ΠZ`.

      If `apply F ∅ = a` and `apply F (σ n) = apply g (apply F n)` for all `n ∈ ω`,
      then `f p := apply F (ΠZ p)` satisfies `f 𝟘 = a` and
      `f (σ p) = apply g (f p)` for all `p : ℕ₀`. -/
  theorem recursion_transport (F a g : U)
      (hF_zero : apply F (∅ : U) = a)
      (hF_succ : ∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) :
      let f : Peano.ℕ₀ → U := fun p => apply F (ΠZ p : U)
      f Peano.ℕ₀.zero = a ∧ ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p) :=
    ⟨hF_zero, fun p =>
      -- ΠZ (ℕ₀.succ p) = σ (ΠZ p) by definition
      -- ΠZ p ∈ ω by fromPeano_is_nat + Nat_in_Omega
      hF_succ (ΠZ p) (Nat_in_Omega _ (fromPeano_is_nat p))⟩

  /-- **Recursion transport (Peano → VN)**: any Lean function `f : ℕ₀ → U`
      satisfying Peano recursion also satisfies Von Neumann recursion via `ZΠ`.

      If `f 𝟘 = a` and `f (σ p) = apply g (f p)`, then
      `f (ZΠ ∅ _) = a` and
      `f (ZΠ (σ n) _) = apply g (f (ZΠ n _))` for all `n ∈ ω`. -/
  theorem recursion_transport_inv (a g : U) (f : Peano.ℕ₀ → U)
      (hf_zero : f Peano.ℕ₀.zero = a)
      (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p)) :
      f (ZΠ (∅ : U) zero_is_nat) = a ∧
      ∀ (n : U) (hn : n ∈ ω),
        f (ZΠ (σ n) (nat_successor_is_nat n (mem_Omega_is_Nat n hn))) =
        apply g (f (ZΠ n (mem_Omega_is_Nat n hn))) := by
    refine ⟨?_, fun n hn => ?_⟩
    · rw [toPeano_zero]; exact hf_zero
    · rw [toPeano_successor]; exact hf_succ _

  -- =========================================================================
  -- Section 4: Predecessor in ZFC
  -- =========================================================================

  /-- The predecessor of ∅ is ∅ in ZFC: `predecessor ∅ = ⋃∅ = ∅`.
      Analogous to `τ 𝟘 = 𝟘` in the Peano setting. -/
  theorem predecessor_zero : predecessor (∅ : U) = ∅ :=
    Set_is_empty_1 (∅ : U) rfl

  /-!
    The existing `predecessor n = ⋃n` already behaves as the **saturated (τ-like)**
    predecessor:
    - `predecessor ∅ = ∅`               (see `predecessor_zero`)
    - `predecessor (σ k) = k`            (see `predecessor_of_successor`)
    - `isNat (predecessor n)` for n ≠ ∅  (see `predecessor_is_nat`)
    Analogous to `τ` in the Peano setting.
  -/

  /-- Strict predecessor of a non-zero Von Neumann natural.
      Requires an explicit proof that `n ≠ ∅`. Analogous to `ρ` in Peano. -/
  noncomputable def predecessorPos (n : U) (_ : n ≠ ∅) : U := predecessor n

  /-- `predecessorPos n h = predecessor n` (definitional). -/
  theorem predecessorPos_eq_predecessor (n : U) (h : n ≠ ∅) :
      predecessorPos n h = predecessor n := rfl

  /-- `predecessorPos (σ k) h = k`. -/
  theorem predecessorPos_of_successor (k : U) (hk : isNat k) (h : σ k ≠ ∅) :
      predecessorPos (σ k) h = k :=
    predecessor_of_successor hk

  /-- `predecessorPos n h` is a Von Neumann natural. -/
  theorem predecessorPos_is_nat (n : U) (hn : isNat n) (h : n ≠ ∅) :
      isNat (predecessorPos n h) :=
    predecessor_is_nat n hn h

  /-- `σ (predecessorPos n h) = n` for any non-zero Von Neumann natural. -/
  theorem successor_predecessorPos (n : U) (hn : isNat n) (h : n ≠ ∅) :
      σ (predecessorPos n h) = n := by
    obtain ⟨k, hk⟩ := (nat_is_zero_or_succ n hn).resolve_left h
    have hk_nat : isNat k :=
      nat_element_is_nat n k hn (hk ▸ mem_successor_self k)
    calc σ (predecessorPos n h)
        = σ (predecessor n)      := by rw [predecessorPos_eq_predecessor]
      _ = σ (predecessor (σ k))  := by rw [hk]
      _ = σ k                    := by rw [predecessor_of_successor hk_nat]
      _ = n                      := hk.symm

  -- =========================================================================
  -- Section 5: Order on ω
  -- =========================================================================

  /-- Strict order on Von Neumann naturals: `n ≺ m` iff `n ∈ m`. -/
  scoped notation:50 n:51 " ≺ " m:51 => (n ∈ m)

  /-- Non-strict order on Von Neumann naturals: `n ≼ m` iff `n ∈ m ∨ n = m`. -/
  scoped notation:50 n:51 " ≼ " m:51 => (n ∈ m ∨ n = m)

  /-- The strict order on ω is transitive. -/
  theorem natLt_trans {n m k : U} (hn : isNat n) (hm : isNat m) (hk : isNat k)
      (h₁ : n ≺ m) (h₂ : m ≺ k) : n ≺ k :=
    nat_mem_trans n m k hn hm hk h₁ h₂

  /-- The strict order on ω is asymmetric. -/
  theorem natLt_asymm {n m : U} (hn : isNat n) (hm : isNat m)
      (h : n ≺ m) : ¬(m ≺ n) :=
    nat_mem_asymm n m hn hm h

  /-- Trichotomy: for any two naturals, exactly one of `n ≺ m`, `n = m`, `m ≺ n`. -/
  theorem natLt_trichotomy (n m : U) (hn : isNat n) (hm : isNat m) :
      n ≺ m ∨ n = m ∨ m ≺ n :=
    nat_trichotomy n m hn hm

  /-- The non-strict order is reflexive. -/
  theorem natLe_refl (n : U) : n ≼ n := Or.inr rfl

  /-- The non-strict order is transitive. -/
  theorem natLe_trans {n m k : U} (hn : isNat n) (hm : isNat m) (hk : isNat k)
      (h₁ : n ≼ m) (h₂ : m ≼ k) : n ≼ k := by
    cases h₁ with
    | inl h => cases h₂ with
      | inl h' => exact Or.inl (nat_mem_trans n m k hn hm hk h h')
      | inr h' => exact Or.inl (h' ▸ h)
    | inr h => exact h ▸ h₂

  /-- Every non-empty subset of ω has a `≺`-minimum element. -/
  theorem Omega_has_min (T : U) (hT_sub : T ⊆ (ω : U)) (hT_ne : T ≠ ∅) :
      ∃ n, n ∈ T ∧ ∀ m, m ∈ T → n ≼ m := by
    -- S = { n ∈ ω | n ∈ T → ∃ minimum of T }
    let S := SpecSet (ω : U) (fun n =>
      n ∈ T → ∃ p, p ∈ T ∧ ∀ k, k ∈ T → p ≼ k)
    have hS_eq : S = (ω : U) :=
      strong_induction_principle S
        (fun z hz => by rw [SpecSet_is_specified] at hz; exact hz.1)
        (fun n hn ih => by
          rw [SpecSet_is_specified]
          refine ⟨hn, fun hnT => ?_⟩
          by_cases h : ∃ l, l ∈ T ∧ l ∈ n
          · -- Some l ∈ T is smaller than n; apply IH to l
            obtain ⟨l, hlT, hln⟩ := h
            have hl_in_S : l ∈ S := ih l hln
            rw [SpecSet_is_specified] at hl_in_S
            exact hl_in_S.2 hlT
          · -- No element of T is below n: n is the minimum
            have h' : ∀ l, l ∈ T → l ∉ n := fun l hl hln => h ⟨l, hl, hln⟩
            exact ⟨n, hnT, fun k hkT => by
              rcases nat_trichotomy n k
                  (mem_Omega_is_Nat n hn) (mem_Omega_is_Nat k (hT_sub k hkT))
                with hk | hk | hk
              · exact Or.inl hk
              · exact Or.inr hk
              · exact absurd hk (h' k hkT)⟩)
    obtain ⟨x, hxT⟩ := (nonempty_iff_exists_mem T).mp hT_ne
    have hx_in_S : x ∈ S := by rw [hS_eq]; exact hT_sub x hxT
    rw [SpecSet_is_specified] at hx_in_S
    exact hx_in_S.2 hxT

  -- =========================================================================
  -- Section 6: Bridge theorems for order
  -- =========================================================================

  /-- The successor function preserves and reflects membership:
      `n ∈ m ↔ σ n ∈ σ m` for Von Neumann naturals. -/
  theorem succ_mem_succ_iff (n m : U) (hn : isNat n) (hm : isNat m) :
      n ∈ m ↔ σ n ∈ σ m := by
    constructor
    · intro h_nm
      -- n ⊆ m by transitivity of m; then σn = n ∪ {n} ⊆ m ∪ {m} = σm
      have hn_sub_m : n ⊆ m := hm.1 n h_nm
      have h_σn_sub_σm : σ n ⊆ σ m := by
        intro x hx
        rw [successor_is_specified] at hx
        rcases hx with hx | hx
        · exact mem_successor_of_mem x m (hn_sub_m x hx)
        · rw [hx]; exact mem_successor_of_mem n m h_nm
      rcases nat_subset_mem_or_eq (σ n) (σ m)
          (nat_successor_is_nat n hn) (nat_successor_is_nat m hm) h_σn_sub_σm with h | h
      · exact h
      · exact absurd (successor_injective n m hn hm h ▸ h_nm) (nat_not_mem_self n hn)
    · intro h_sn_sm
      rcases nat_trichotomy n m hn hm with h | h | h
      · exact h
      · -- n = m → σn = σm → σn ∈ σn: contradicts irreflexivity
        exact absurd (h ▸ h_sn_sm) (nat_not_mem_self (σ n) (nat_successor_is_nat n hn))
      · -- m ∈ n → σm ∈ σn; combined with σn ∈ σm: asymmetry contradiction
        have hm_sub_n : m ⊆ n := hn.1 m h
        have h_σm_sub_σn : σ m ⊆ σ n := by
          intro x hx
          rw [successor_is_specified] at hx
          rcases hx with hx | hx
          · exact mem_successor_of_mem x n (hm_sub_n x hx)
          · rw [hx]; exact mem_successor_of_mem m n h
        rcases nat_subset_mem_or_eq (σ m) (σ n)
            (nat_successor_is_nat m hm) (nat_successor_is_nat n hn) h_σm_sub_σn with hh | hh
        · exact absurd h_sn_sm (nat_mem_asymm (σ m) (σ n)
              (nat_successor_is_nat m hm) (nat_successor_is_nat n hn) hh)
        · exact absurd (successor_injective m n hm hn hh ▸ h) (nat_not_mem_self m hm)

  /-- `ΠZ` preserves and reflects the strict order:
      `Peano.StrictOrder.Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U)`. -/
  theorem fromPeano_lt_iff (p q : Peano.ℕ₀) :
      Peano.StrictOrder.Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U) := by
    induction q generalizing p with
    | zero =>
      -- Lt p 0 = False definitionally; ΠZ 0 = ∅ so ΠZ p ∉ ∅
      constructor
      · intro h; simp [Peano.StrictOrder.Lt] at h
      · intro h; exact absurd h (EmptySet_is_empty _)
    | succ q' ihq =>
      cases p with
      | zero =>
        -- Lt 0 (σ q') = True; ∅ ∈ σ (ΠZ q') since σ (ΠZ q') ≠ ∅
        constructor
        · intro _
          exact zero_mem_of_nat_nonempty (σ (ΠZ q' : U))
            (nat_successor_is_nat _ (fromPeano_is_nat q'))
            (successor_nonempty _)
        · intro _; trivial
      | succ p' =>
        -- Lt (σ p') (σ q') = Lt p' q' definitionally
        show Peano.StrictOrder.Lt p' q' ↔ σ (ΠZ p' : U) ∈ σ (ΠZ q' : U)
        exact (ihq p').trans (succ_mem_succ_iff _ _ (fromPeano_is_nat p') (fromPeano_is_nat q'))

  /-- `ΠZ` preserves and reflects the non-strict order:
      `Peano.Order.Le p q ↔ (ΠZ p : U) ≼ (ΠZ q : U)`. -/
  theorem fromPeano_le_iff (p q : Peano.ℕ₀) :
      Peano.Order.Le p q ↔ (ΠZ p : U) ≼ (ΠZ q : U) := by
    unfold Peano.Order.Le
    rw [fromPeano_lt_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (congrArg (ΠZ : Peano.ℕ₀ → U) h)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (fromPeano_injective h)

end SetUniverse
