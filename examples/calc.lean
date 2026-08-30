theorem chain (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  calc a = b := h1
    _ = c := h2
    _ = d := h3

theorem append_nil' (l : List Nat) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, ih]
