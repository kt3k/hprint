/-- Adding zero on the left is not definitional in Lean, so it needs induction. -/
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, ih]
