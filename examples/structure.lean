/-- A `have` whose justification is itself a tactic block. -/
theorem have_by (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h : p := by
    exact hp
  exact ⟨h, hq⟩

/-- A combinator: the children do the work, so only they are narrated. -/
theorem first_alt (p : Prop) (hp : p) : p := by
  first
  | exact hp

theorem all_goals_close (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  all_goals assumption

/-- Nothing observable happens between the tactic and the closed goal. -/
theorem seq_focus (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption
