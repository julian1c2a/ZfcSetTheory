import ZfcSetTheory
import ZfcSetTheory.Int.Div

open ZFC
open Peano

theorem gcdZ_assoc (a b c : U) (ha : a ∈ IntSet) (hb : b ∈ IntSet) (hc : c ∈ IntSet) :
    gcdZ a (gcdZ b c) = gcdZ (gcdZ a b) c := by
  unfold gcdZ
  have hab : gcdZ a b ∈ ω := gcdZ_in_omega a b ha hb
  have hbc : gcdZ b c ∈ ω := gcdZ_in_omega b c hb hc
  have hgcd_ab : absZ (natToInt (gcdZ a b)) = gcd (absZ a) (absZ b) := Int.Div.absZ_natToInt _ hab
  have hgcd_bc : absZ (natToInt (gcdZ b c)) = gcd (absZ b) (absZ c) := Int.Div.absZ_natToInt _ hbc
  congr 1
  rw [hgcd_bc, hgcd_ab]
  exact Nat.Gcd.gcd_assoc_Omega (absZ a) (absZ b) (absZ c)
    (absZ_in_omega a ha) (absZ_in_omega b hb) (absZ_in_omega c hc)

theorem lcmZ_zero_right (a : U) (ha : a ∈ IntSet) :
    lcmZ a zeroZ = ∅ := by
  unfold lcmZ
  rw [absZ_zero]
  exact Nat.Gcd.lcm_zero_right_Omega (absZ a) (absZ_in_omega a ha)

theorem lcmZ_zero_left (b : U) (hb : b ∈ IntSet) :
    lcmZ zeroZ b = ∅ := by
  unfold lcmZ
  rw [absZ_zero]
  exact Nat.Gcd.lcm_zero_left_Omega (absZ b) (absZ_in_omega b hb)

theorem bezoutZ (a b : U) (ha : a ∈ IntSet) (hb : b ∈ IntSet) :
    ∃ s t : U, s ∈ IntSet ∧ t ∈ IntSet ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  have ha_omega := absZ_in_omega a ha
  have hb_omega := absZ_in_omega b hb
  obtain ⟨n, m, hn, hm, h_bez⟩ := Nat.Gcd.bezout_natform_Omega (absZ a) (absZ b) ha_omega hb_omega
  -- We know gcd (absZ a) (absZ b) = sub (mul n (absZ a)) (mul m (absZ b)) OR sub (mul n (absZ b)) (mul m (absZ a))
  sorry

