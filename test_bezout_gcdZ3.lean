import ZfcSetTheory.Int.Div
import ZfcSetTheory.Int.Sub

open ZFC
open ZFC.Axiom.Infinity
open ZFC.Nat.Mul
open ZFC.Nat.Add
open ZFC.Nat.Sub

variable {U : Type _} [SetOps U] [ZFC.Axiom.Infinity U] [ZFC.Axiom.Regularity U] [ZFC.Axiom.Replacement U]

-- Helper 1: zero equality
theorem natToInt_zero_eq : natToInt (∅ : U) = zeroZ := rfl

-- Helper 2: Value absolute
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

-- Helper 3: natToInt sub conversion
theorem natToInt_sub_eq (x y : U) (hx : x ∈ ω) (hy : y ∈ ω) (hle : y ∈ x ∨ y = x) :
    natToInt (sub x y) = subZ (natToInt x) (natToInt y) := by
  have hs_mem : sub x y ∈ ω := sub_in_Omega x y hx hy
  have hadd : add (sub x y) y = x := add_k_sub_k_Omega x y hx hy hle
  have heq : natToInt (add (sub x y) y) = natToInt x := congrArg natToInt hadd
  rw [natToInt_add hs_mem hy] at heq
  have h_int_s := natToInt_mem_IntSet (sub x y) hs_mem
  have h_int_y := natToInt_mem_IntSet y hy
  have h1 : addZ (natToInt (sub x y)) (natToInt y) = natToInt x := heq
  have h2 : addZ (addZ (natToInt (sub x y)) (natToInt y)) (negZ (natToInt y)) = addZ (natToInt x) (negZ (natToInt y)) := congrArg (fun z => addZ z (negZ (natToInt y))) h1
  have h3 : addZ (addZ (natToInt (sub x y)) (natToInt y)) (negZ (natToInt y)) = addZ (natToInt (sub x y)) (addZ (natToInt y) (negZ (natToInt y))) := addZ_assoc _ _ _ h_int_s h_int_y (negZ_mem_IntSet _ h_int_y)
  rw [h3, addZ_neg h_int_y, addZ_zero_right _ h_int_s] at h2
  exact h2


-- Helper 4: Case 1
theorem bezoutZ_case1 (a b : U) (ha : a ∈ IntSet) (hb : b ∈ IntSet)
    (n m : U) (hn : n ∈ ω) (hm : m ∈ ω)
    (heq : gcd (absZ a) (absZ b) = sub (mul n (absZ a)) (mul m (absZ b)))
    (hle : mul m (absZ b) ∈ mul n (absZ a) ∨ mul m (absZ b) = mul n (absZ a)) :
    ∃ s t : U, s ∈ IntSet ∧ t ∈ IntSet ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  have habs_a := absZ_in_omega a ha
  have habs_b := absZ_in_omega b hb
  have h_na := mul_in_Omega n (absZ a) hn habs_a
  have h_mb := mul_in_Omega m (absZ b) hm habs_b

  have h1 : natToInt (gcd (absZ a) (absZ b)) = natToInt (sub (mul n (absZ a)) (mul m (absZ b))) := congrArg natToInt heq
  rw [natToInt_sub_eq _ _ h_na h_mb hle] at h1

  have h_int_n := natToInt_mem_IntSet n hn
  have h_int_m := natToInt_mem_IntSet m hm
  have h_int_abs_a := natToInt_mem_IntSet (absZ a) habs_a
  have h_int_abs_b := natToInt_mem_IntSet (absZ b) habs_b

  rw [natToInt_mul hn habs_a, natToInt_mul hm habs_b] at h1
  rw [natToInt_absZ_eq a ha, natToInt_absZ_eq b hb] at h1

  have hz1 : mulZ (natToInt n) (mulZ (signZ a) a) = mulZ (mulZ (natToInt n) (signZ a)) a := Eq.symm (mulZ_assoc _ _ _ h_int_n (signZ_in_IntSet a ha) ha)
  have hz2 : mulZ (natToInt m) (mulZ (signZ b) b) = mulZ (mulZ (natToInt m) (signZ b)) b := Eq.symm (mulZ_assoc _ _ _ h_int_m (signZ_in_IntSet b hb) hb)

  rw [hz1, hz2] at h1
  
  let s := mulZ (natToInt n) (signZ a)
  let t := negZ (mulZ (natToInt m) (signZ b))
  
  have hs : s ∈ IntSet := mulZ_mem_IntSet _ _ h_int_n (signZ_in_IntSet a ha)
  have hmb_Z : mulZ (natToInt m) (signZ b) ∈ IntSet := mulZ_mem_IntSet _ _ h_int_m (signZ_in_IntSet b hb)
  have ht : t ∈ IntSet := negZ_mem_IntSet _ hmb_Z
  
  use s, t
  refine ⟨hs, ht, ?_⟩
  
  have h_sub_def : subZ (mulZ s a) (mulZ (mulZ (natToInt m) (signZ b)) b) = addZ (mulZ s a) (negZ (mulZ (mulZ (natToInt m) (signZ b)) b)) := rfl
  have h_neg_pull : negZ (mulZ (mulZ (natToInt m) (signZ b)) b) = mulZ (negZ (mulZ (natToInt m) (signZ b))) b := Eq.symm (mulZ_neg_left _ _ hmb_Z hb)
  
  rw [h_sub_def, h_neg_pull] at h1
  exact h1

-- Helper 5: Case 2
theorem bezoutZ_case2 (a b : U) (ha : a ∈ IntSet) (hb : b ∈ IntSet)
    (n m : U) (hn : n ∈ ω) (hm : m ∈ ω)
    (heq : gcd (absZ a) (absZ b) = sub (mul n (absZ b)) (mul m (absZ a)))
    (hle : mul m (absZ a) ∈ mul n (absZ b) ∨ mul m (absZ a) = mul n (absZ b)) :
    ∃ s t : U, s ∈ IntSet ∧ t ∈ IntSet ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  have habs_a := absZ_in_omega a ha
  have habs_b := absZ_in_omega b hb
  have h_nb := mul_in_Omega n (absZ b) hn habs_b
  have h_ma := mul_in_Omega m (absZ a) hm habs_a

  have h1 : natToInt (gcd (absZ a) (absZ b)) = natToInt (sub (mul n (absZ b)) (mul m (absZ a))) := congrArg natToInt heq
  rw [natToInt_sub_eq _ _ h_nb h_ma hle] at h1

  have h_int_n := natToInt_mem_IntSet n hn
  have h_int_m := natToInt_mem_IntSet m hm
  have h_int_abs_a := natToInt_mem_IntSet (absZ a) habs_a
  have h_int_abs_b := natToInt_mem_IntSet (absZ b) habs_b

  rw [natToInt_mul hn habs_b, natToInt_mul hm habs_a] at h1
  rw [natToInt_absZ_eq b hb, natToInt_absZ_eq a ha] at h1

  have hz1 : mulZ (natToInt n) (mulZ (signZ b) b) = mulZ (mulZ (natToInt n) (signZ b)) b := Eq.symm (mulZ_assoc _ _ _ h_int_n (signZ_in_IntSet b hb) hb)
  have hz2 : mulZ (natToInt m) (mulZ (signZ a) a) = mulZ (mulZ (natToInt m) (signZ a)) a := Eq.symm (mulZ_assoc _ _ _ h_int_m (signZ_in_IntSet a ha) ha)

  rw [hz1, hz2] at h1
  
  let s := negZ (mulZ (natToInt m) (signZ a))
  let t := mulZ (natToInt n) (signZ b)
  
  have ht : t ∈ IntSet := mulZ_mem_IntSet _ _ h_int_n (signZ_in_IntSet b hb)
  have hseq_Z : mulZ (natToInt m) (signZ a) ∈ IntSet := mulZ_mem_IntSet _ _ h_int_m (signZ_in_IntSet a ha)
  have hs : s ∈ IntSet := negZ_mem_IntSet _ hseq_Z
  
  use s, t
  refine ⟨hs, ht, ?_⟩
  
  have h_sub_def : subZ (mulZ t b) (mulZ (mulZ (natToInt m) (signZ a)) a) = addZ (mulZ t b) (negZ (mulZ (mulZ (natToInt m) (signZ a)) a)) := rfl
  have h_neg_pull : negZ (mulZ (mulZ (natToInt m) (signZ a)) a) = mulZ (negZ (mulZ (natToInt m) (signZ a))) a := Eq.symm (mulZ_neg_left _ _ hseq_Z ha)
  
  rw [h_sub_def, h_neg_pull] at h1
  
  have h_comm : addZ (mulZ t b) (mulZ s a) = addZ (mulZ s a) (mulZ t b) := addZ_comm _ _ (mulZ_mem_IntSet _ _ ht hb) (mulZ_mem_IntSet _ _ hs ha)
  rw [h_comm] at h1
  exact h1

theorem bezoutZ (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
    ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  have habs_a := absZ_in_omega a ha
  have habs_b := absZ_in_omega b hb
  obtain ⟨n, m, hn, hm, hor⟩ := ZFC.Nat.Gcd.bezout_natform_Omega (absZ a) (absZ b) habs_a habs_b
  rcases hor with h1 | h2
  · have hle : mul m (absZ b) ∈ mul n (absZ a) ∨ mul m (absZ b) = mul n (absZ a) := by
      by_contra hnot
      -- If the subtraction is greater than 0, it means it was valid.
      -- However, in Peano/ZFC Nat, if it's empty, we must handle it.
      -- Actually, ZFC.Nat.Sub_pos implies le.
      -- To avoid rewriting the sub definition entirely, we can use the fact that if a - b = c, and c is gcd...
      sorry 
  · sorry

