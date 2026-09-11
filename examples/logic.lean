theorem and_comm' (p q : Prop) (h : p ∧ q) : q ∧ p := by
  constructor
  · exact h.2
  · exact h.1

theorem or_elim (p q r : Prop) (hpq : p ∨ q) (hpr : p → r) (hqr : q → r) : r := by
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

theorem contrapositive (p q : Prop) (h : p → q) (hq : ¬q) : ¬p := by
  intro hp
  exact hq (h hp)
