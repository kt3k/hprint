theorem exists_gt (n : Nat) : ∃ m, n < m := by
  refine ⟨n + 1, ?_⟩
  omega

theorem double_of_even (n : Nat) (h : ∃ k, n = 2 * k) : ∃ m, n + n = 2 * m := by
  obtain ⟨k, hk⟩ := h
  refine ⟨n, ?_⟩
  omega

theorem le_of_have (a b : Nat) (hab : a = b) : b = a := by
  have h : a = b := hab
  exact h.symm
