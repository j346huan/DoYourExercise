import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
Atiyah–Macdonald (1969), Chapter 1, Exercise 8.

For a nonzero commutative ring `A`, the prime ideals have minimal elements with
respect to inclusion. Mathlib's `Ideal.nonempty_minimalPrimes` packages the
Zorn argument via maximal ideals; `IsMinimalPrime.iff_minimal` removes the
auxiliary lower bound `⊥`.
Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-8
-/

/-- Exercise 1.8: a nonzero commutative ring has a minimal prime ideal. -/
theorem AtiyahMcdonald69.Ex_1_8.solution (A : Type*) [CommRing A] [Nontrivial A] :
    ∃ p : Ideal A, Minimal Ideal.IsPrime p := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal A)) bot_ne_top
  exact ⟨p, (IsMinimalPrime.iff_minimal p).mp hp⟩

#print axioms AtiyahMcdonald69.Ex_1_8.solution
