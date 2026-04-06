import ZfcSetTheory.Int.Div

open ZFC
open ZFC.Axiom.Infinity

variable {U : Type _} [SetOps U] [ZFC.Axiom.Infinity U] [ZFC.Axiom.Regularity U] [ZFC.Axiom.Replacement U]

/-- Bezout's identity for IntSet -/
theorem bezoutZ_proof (a b : U) (ha : a ∈ (IntSet : U)) (hb : b ∈ (IntSet : U)) :
    ∃ s t : U, s ∈ (IntSet : U) ∧ t ∈ (IntSet : U) ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b) := by
  have hab1 : absZ a ∈ (ω : U) := absZ_in_omega a ha
  have hab2 : absZ b ∈ (ω : U) := absZ_in_omega b hb
  obtain ⟨n, m, hn, hm, hor⟩ := ZFC.Nat.Gcd.bezout_natform_Omega (absZ a) (absZ b) hab1 hab2
  sorry
