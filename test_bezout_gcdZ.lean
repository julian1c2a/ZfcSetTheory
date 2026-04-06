import ZfcSetTheory.Int.Div
import ZfcSetTheory.Int.Sub

open ZFC
open ZFC.Axiom.Infinity

variable {U : Type _} [SetOps U] [ZFC.Axiom.Infinity U] [ZFC.Axiom.Regularity U] [ZFC.Axiom.Replacement U]

-- (all the proven helpers from before)
theorem natToInt_zero_eq : natToInt (∅ : U) = zeroZ := rfl

theorem natToInt_absZ_eq (a : U) (ha : a ∈ (IntSet : U)) :
    natToInt (absZ a) = mulZ (signZ a) a := by
  have habs_mem : natToInt (absZ a) ∈ (IntSet : U) := natToInt_mem_IntSet (absZ a) (absZ_in_omega a ha)
  have hsign_mem : signZ a ∈ (IntSet : U) := signZ_in_IntSet a ha
  have h_eq : a = mulZ (signZ a) (natToInt (absZ a)) := signZ_mulZ_absZ a ha
  by_cases h_zero : a = zeroZ
  · rw [h_zero, signZ_zero, absZ_zero, natToInt_zero_eq, mulZ_zero_left _ zeroZ_mem_IntSet]
  · have hsq : mulZ (signZ a) (signZ a) = (oneZ : U) := signZ_square a ha h_zero
    have h1 : mulZ (signZ a) a = mulZ (signZ a) (mulZ (signZ a) (natToInt (absZ a))) := congrArg (fun z => mulZ (signZ a) z) h_eq
    have h2 : mulZ (signZ a) (mulZ (signZ a) (natToInt (absZ a))) = mulZ (mulZ (signZ a) (signZ a)) (natToInt (absZ a)) := Eq.symm (mulZ_assoc (signZ a) (signZ a) (natToInt (absZ a)) hsign_mem hsign_mem habs_mem)
    have h3 : mulZ (mulZ (signZ a) (signZ a)) (natToInt (absZ a)) = mulZ oneZ (natToInt (absZ a)) := by rw [hsq]
    have h4 : mulZ oneZ (natToInt (absZ a)) = natToInt (absZ a) := mulZ_one_left (natToInt (absZ a)) habs_mem
    rw [h1, h2, h3, h4]

theorem sub_implies_le (x y : U) (hx : x ∈ (ω : U)) (hy : y ∈ (ω : U)) (h_ne : sub x y ≠ (∅ : U)) : y ∈ x ∨ y = x := by
  have h_in : y ∈ x := (ZFC.Nat.Sub.sub_pos_iff_lt_Omega x y hx hy).mp h_ne
  exact Or.inl h_in

theorem natToInt_sub (x y : U) (hx : x ∈ (ω : U)) (hy : y ∈ (ω : U)) (hle : y ∈ x ∨ y = x) :
    natToInt (sub x y) = subZ (natToInt x) (natToInt y) := by
  have h1 : x = add (sub x y) y := Eq.symm (ZFC.Nat.Sub.add_k_sub_k_Omega x y hx hy hle)
  have hy_int : natToInt y ∈ (IntSet : U) := natToInt_mem_IntSet y hy
  have hx_int : natToInt x ∈ (IntSet : U) := natToInt_mem_IntSet x hx
  have hsub_w : sub x y ∈ (ω : U) := ZFC.Nat.Sub.sub_in_Omega x y hx hy
  have hsub_int : natToInt (sub x y) ∈ (IntSet : U) := natToInt_mem_IntSet (sub x y) hsub_w
  have h2 : natToInt x = addZ (natToInt (sub x y)) (natToInt y) := calc
    natToInt x = natToInt (add (sub x y) y) := congrArg natToInt h1
    _ = addZ (natToInt (sub x y)) (natToInt y) := natToInt_preserves_add _ _ hsub_w hy
  have h3 : subZ (natToInt x) (natToInt y) = subZ (addZ (natToInt (sub x y)) (natToInt y)) (natToInt y) := by
    exact congrArg (fun z => subZ z (natToInt y)) h2
  rw [h3, subZ_addZ_cancel (natToInt (sub x y)) (natToInt y) hsub_int hy_int]

theorem bezoutZ_helper (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U))
    (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) 
    (heq : gcd (absZ a) (absZ b) = sub (mul n (absZ a)) (mul m (absZ b))) :
    ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  sorry
