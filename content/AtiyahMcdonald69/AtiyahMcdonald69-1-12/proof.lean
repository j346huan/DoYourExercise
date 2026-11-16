import Mathlib.RingTheory.LocalRing.Basic

/-!
Atiyah–Macdonald (1969), Chapter 1, Exercise 12.

A local commutative ring has no idempotent other than zero and one. The proof
uses that either `e` or `1 - e` is a unit, together with `e(1 - e) = 0`.
Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-12
-/

/-- Exercise 1.12: every idempotent of a local commutative ring is zero or one. -/
theorem AtiyahMcdonald69.Ex_1_12.solution {A : Type*} [CommRing A] [IsLocalRing A]
    (e : A) (he : e * e = e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    apply hu.mul_left_cancel
    simp [he]
  · left
    apply hu.mul_left_cancel
    simp [sub_mul, he]

#print axioms AtiyahMcdonald69.Ex_1_12.solution
