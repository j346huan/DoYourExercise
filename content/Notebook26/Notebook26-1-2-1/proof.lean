import Mathlib

namespace DoYourExercise.Notebook26

theorem ex_1_2_1 (a b c : ℕ) : a + (b + c) = (a + b) + c := by
  exact (Nat.add_assoc a b c).symm

end DoYourExercise.Notebook26
