import ZfcSetTheory.Int.Order
open ZFC

namespace ZFC.Int.Order

theorem ltZ_irrefl (x : U) (_hx : x ∈ (IntSet : U)) : ¬ ltZ x x :=
  fun h => h.2 rfl

theorem ltZ_trans (x y z : U)
    (hx : x ∈ (IntSet : U)) (hy : y ∈ (IntSet : U)) (hz : z ∈ (IntSet : U))
    (h_xy : ltZ x y) (h_yz : ltZ y z) : ltZ x z :=
  ⟨leZ_trans x y z hx hy hz h_xy.1 h_yz.1,
   fun h_eq => h_xy.2 (leZ_antisymm x y hx hy h_xy.1 (h_eq ▸ h_yz.1))⟩

theorem leZ_iff_ltZ_or_eq (x y : U)
    (hx : x ∈ (IntSet : U)) (_hy : y ∈ (IntSet : U)) :
    leZ x y ↔ ltZ x y ∨ x = y :=
  ⟨fun h => by
    by_cases h_eq : x = y
    · exact Or.inr h_eq
    · exact Or.inl ⟨h, h_eq⟩,
   fun h => h.elim (fun hlt => hlt.1) (fun heq => heq ▸ leZ_refl x hx)⟩

end ZFC.Int.Order
