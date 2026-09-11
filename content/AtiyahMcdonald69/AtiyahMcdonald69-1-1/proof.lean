import Mathlib.RingTheory.Nilpotent.Basic

theorem AtiyahMcdonald69.Ex_1_1.solution {A : Type*} [CommRing A] (x : A) (hx : IsNilpotent x) :
  IsUnit (1 + x) ∧ ∀ u : A, IsUnit u → IsUnit (u + x) := by
  constructor
  · exact hx.isUnit_add_left_of_commute isUnit_one (Commute.all x 1)
  · intro u hu
    exact hx.isUnit_add_left_of_commute hu (Commute.all x u)
