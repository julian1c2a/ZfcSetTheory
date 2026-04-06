import ZfcSetTheory.Int.Div
import ZfcSetTheory.Nat.Div
import ZfcSetTheory.Int.Ring
open ZFC
open ZFC.Int.Div
open ZFC.Nat.Div
open ZFC.Int.Ring
open ZFC.Int.Embedding
open ZFC.Int.Abs
open ZFC.Int.Mul
open ZFC.Int.Add
open ZFC.Int.Basic

namespace ZFC.Int.Div

theorem gcdZ_assoc (a b c : U)
    (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) (hc : c ∈ (IntSet : U)) :
    gcdZ a (natToInt (gcdZ b c)) = gcdZ (natToInt (gcdZ a b)) c := by
  unfold gcdZ
  have eq1 : absZ (natToInt (gcd (absZ b) (absZ c))) = gcd (absZ b) (absZ c) :=
    absZ_natToInt _ (gcd_in_Omega (absZ b) (absZ c) (absZ_in_omega b hb) (absZ_in_omega c hc))
  have eq2 : absZ (natToInt (gcd (absZ a) (absZ b))) = gcd (absZ a) (absZ b) :=
    absZ_natToInt _ (gcd_in_Omega (absZ a) (absZ b) (absZ_in_omega a ha) (absZ_in_omega b hb))
  rw [eq1, eq2]
  exact gcd_assoc_Omega (absZ a) (absZ b) (absZ c) (absZ_in_omega a ha) (absZ_in_omega b hb) (absZ_in_omega c hc)

theorem lcmZ_zero_right (a : U) (ha : a ∈ (IntSet : U)) :
    lcmZ a zeroZ = (∅ : U) := by
  unfold lcmZ
  rw [absZ_zero]
  exact ZFC.Nat.Div.lcm_zero_right_Omega _ (absZ_in_omega a ha)

theorem lcmZ_zero_left (a : U) (ha : a ∈ (IntSet : U)) :
    lcmZ zeroZ a = (∅ : U) := by
  unfold lcmZ
  rw [absZ_zero]
  exact ZFC.Nat.Div.lcm_zero_left_Omega _ (absZ_in_omega a ha)

end ZFC.Int.Div
