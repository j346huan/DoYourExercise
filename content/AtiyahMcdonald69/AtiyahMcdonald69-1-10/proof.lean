import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.TFAE

/-!
Atiyah–Macdonald (1969), Chapter 1, Exercise 10.

For a nonzero commutative ring `A`, the following are equivalent: exactly one
prime ideal; every element is a unit or nilpotent; and the quotient by the
nilradical is a field.

Source qualification: this is the intended equivalence used by both the
natural-language reference and the standard interpretation of the exercise.
`Nontrivial A` is an additional necessary restriction. The book's notation
section explicitly allows the zero ring, but condition (ii) is then true while
(i) and (iii) are false. This edge case is documented rather than concealed.
Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-10
-/

namespace AtiyahMcdonald69.Ex_1_10

variable {A : Type*} [CommRing A]

private theorem unit_or_nilpotent_iff [Nontrivial A] :
    (∀ x : A, IsUnit x ∨ IsNilpotent x) ↔
      (Ring.KrullDimLE 0 A ∧ IsLocalRing A) := by
  rw [((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 0 2 rfl rfl)]
  constructor
  · intro h x
    constructor
    · intro hx hu
      exact hx.not_isUnit hu
    · intro hx
      exact (h x).resolve_left hx
  · intro h x
    by_cases hx : IsUnit x
    · exact Or.inl hx
    · exact Or.inr ((h x).mpr hx)

/-- Exercise 1.10, `(i) ↔ (ii)`. -/
theorem part_a [Nontrivial A] :
    (∃! p : Ideal A, p.IsPrime) ↔ ∀ x : A, IsUnit x ∨ IsNilpotent x :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 1 0 rfl rfl).trans
    unit_or_nilpotent_iff.symm

/-- Exercise 1.10, `(i) ↔ (iii)`: a field quotient precisely makes the
nilradical maximal, and a maximal nilradical is the only prime ideal. -/
theorem part_b :
    (∃! p : Ideal A, p.IsPrime) ↔ IsField (A ⧸ nilradical A) := by
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 1 3 rfl rfl)

/-- Complete Exercise 1.10. -/
theorem solution [Nontrivial A] :
    [∃! p : Ideal A, p.IsPrime, ∀ x : A, IsUnit x ∨ IsNilpotent x,
      IsField (A ⧸ nilradical A)].TFAE := by
  tfae_have 1 ↔ 2 := part_a
  tfae_have 1 ↔ 3 := part_b
  tfae_finish

end AtiyahMcdonald69.Ex_1_10

#print axioms AtiyahMcdonald69.Ex_1_10.solution
#print axioms AtiyahMcdonald69.Ex_1_10.part_a
#print axioms AtiyahMcdonald69.Ex_1_10.part_b
