import ZfcSetTheory.Int.Sub
import ZfcSetTheory.Int.Order
import ZfcSetTheory.Int.Ring
open ZFC
open ZFC.Int.Sub
open ZFC.Int.Order

theorem ltZ_addZ_ltZ (x y z : U)
    (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
    (h_lt : ltZ x y) : ltZ (addZ x z) (addZ y z) :=
  ⟨addZ_leZ_addZ x y z hx hy hz h_lt.1, fun h_eq =>
    have h1 : subZ (addZ x z) z = subZ (addZ y z) z := by rw [h_eq]
    have h2 : subZ (addZ x z) z = x := subZ_addZ_cancel x z hx hz
    have h3 : subZ (addZ y z) z = y := subZ_addZ_cancel y z hy hz
    h_lt.2 (h2.symm.trans (h1.trans h3))⟩

/-- Multiplication by nonpositive flips order: leZ x y → leZ z 0 → leZ (mulZ z y) (mulZ z x) -/
theorem mulZ_le_mulZ_nonpos (x y z : U)
    (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
    (h_le : leZ x y) (hz_nonpos : leZ z zeroZ) : leZ (mulZ z y) (mulZ z x) := by
  have hz_neg : negZ z ∈ (IntSet : U) := negZ_in_IntSet z hz
  have h1 : leZ zeroZ (negZ z) := by
    have h : leZ (negZ zeroZ) (negZ z) := leZ_negZ z zeroZ hz zeroZ_mem_IntSet hz_nonpos
    rwa [negZ_zero] at h
  have h2 : leZ (mulZ (negZ z) x) (mulZ (negZ z) y) :=
    mulZ_le_mulZ_nonneg x y (negZ z) hx hy hz_neg h_le h1
  rw [mulZ_negZ_left z x hz hx] at h2
  rw [mulZ_negZ_left z y hz hy] at h2
  have h3 : leZ (negZ (negZ (mulZ z y))) (negZ (negZ (mulZ z x))) :=
    leZ_negZ _ _ (negZ_in_IntSet (mulZ z x) (mulZ_in_IntSet z x hz hx))
             (negZ_in_IntSet (mulZ z y) (mulZ_in_IntSet z y hz hy)) h2
  rwa [negZ_negZ (mulZ z y) (mulZ_in_IntSet z y hz hy),
       negZ_negZ (mulZ z x) (mulZ_in_IntSet z x hz hx)] at h3

/-- Strict multiplication by positive preserves strict order: ltZ x y → ltZ 0 z → ltZ (mulZ z x) (mulZ z y) -/
theorem mulZ_ltZ_mulZ_pos (x y z : U)
    (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
    (h_lt : ltZ x y) (hz_pos : ltZ zeroZ z) : ltZ (mulZ z x) (mulZ z y) := by
  have h_le : leZ (mulZ z x) (mulZ z y) :=
    mulZ_le_mulZ_nonneg x y z hx hy hz h_lt.1 hz_pos.1
  refine ⟨h_le, fun h_eq => h_lt.2 ?_⟩
  exact mulZ_cancel_left x y z hx hy hz hz_pos.2.symm h_eq
