import Lean.Elab.Tactic
theorem test (P : Prop) : P ∨ ¬P := by
  by_contra h
  exact h (Or.inr (fun hp => h (Or.inl hp)))
