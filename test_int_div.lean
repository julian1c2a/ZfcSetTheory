import ZfcSetTheory.Peano.Import
import ZfcSetTheory.Nat.Div
import ZfcSetTheory.Nat.Gcd

open ZFC

variable {U : Type _}

theorem divOf_zero (a : U) (ha : a ∈ (ω:U)) : divOf (∅:U) a = ∅ := by
  have h_p : (∅ : U) = fromPeano 𝟘 := rfl
  have hna : IsNat a := mem_Omega_is_Nat a ha
  have ha_p : a = fromPeano (toPeano a hna) := by
    exact (fromPeano_toPeano a hna).symm
  have h_div : fromPeano ((𝟘 / toPeano a hna) : ℕ₀) = divOf (fromPeano 𝟘 : U) (fromPeano (toPeano a hna)) := by
    exact fromPeano_div 𝟘 (toPeano a hna)
  rw [← ha_p] at h_div
  have h_p_eq : (fromPeano 𝟘 : U) = (∅:U) := rfl
  rw [h_p_eq] at h_div
  rw [← h_div]
  let q := toPeano a hna
  have h_cases : q = 𝟘 ∨ q ≠ 𝟘 := by exact Classical.em (q = 𝟘)
  cases h_cases with
  | inl hq =>
    have hq_typed : toPeano a hna = 𝟘 := hq
    rw [hq_typed]
    have h0 : ((𝟘 / 𝟘) : ℕ₀) = 𝟘 := by
      unfold Peano.Div.div
      rw [Peano.Div.divMod]
      rw [dif_pos rfl]
    rw [h0]
    rfl
  | inr hq =>
    have h_p_q : toPeano a hna = q := rfl
    rw [h_p_q]
    have h_lt : Lt 𝟘 q := lt_0_n q hq
    have h0 : ((𝟘 / q) : ℕ₀) = 𝟘 := div_of_lt 𝟘 q h_lt
    rw [h0]
    rfl

theorem lcm_zero_right_Omega (a : U) (ha : a ∈ (ω:U)) : (ZFC.lcm a ∅) = ∅ := by
  unfold ZFC.lcm
  rw [dif_pos ha, dif_pos (zero_in_Omega : (∅:U) ∈ (ω:U))]
  have mul_0 : @ZFC.mul U a ∅ = ∅ := mul_zero a ha
  rw [mul_0]
  have gcd_0 : @ZFC.gcd U a ∅ = a := gcd_zero a ha
  rw [gcd_0]
  exact divOf_zero a ha

theorem lcm_zero_left_Omega (a : U) (ha : a ∈ (ω:U)) : (ZFC.lcm ∅ a) = ∅ := by
  rw [lcm_comm_Omega (∅:U) a zero_in_Omega ha]
  exact lcm_zero_right_Omega a ha
