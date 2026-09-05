theorem have_by (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h : p := by
    exact hp
  exact ⟨h, hq⟩

theorem first_alt (p : Prop) (hp : p) : p := by
  first
  | exact hp

theorem all_goals_close (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  all_goals assumption

theorem seq_focus (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption
