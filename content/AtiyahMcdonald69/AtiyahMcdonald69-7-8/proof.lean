/-
Atiyah & Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley 1969.
Chapter 7 (Noetherian Rings), Exercises, no. 8:

  "If A[x] is Noetherian, must A be Noetherian as well?"

Answer: yes.  The reference proof is the one-line argument that `A ≅ A[x]/(x)`
is a quotient of the Noetherian ring `A[x]`, and a quotient of a Noetherian ring
is Noetherian (6.6 / 7.1).  No further hypothesis is needed: `A` is a commutative
ring with identity throughout the book.

Reference: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-8
(source of that page: j346huan/DoYourExercise, commit
80e1ebef1d7621c66aabb3920d981ffd8995ba91).  The reference proof is correct and
complete for this exercise; nothing had to be corrected or generalized, and no
hypothesis is unstated.

We model the quotient map concretely, as evaluation at `0`:
`Polynomial.evalRingHom (0 : A) : A[X] →+* A`, which is surjective, and whose
kernel is the principal ideal `(X)`, so that this quotient is literally
`A[X]/(X)`.  The exercise itself asks only the yes/no question recorded as
`solution` below; the remaining declarations are the concrete pieces of the
construction and one clearly-marked supplementary statement.

Audit note on the argument's shape: the quotient is essential — the only claim
needed is that `A` is a *quotient* of `A[x]`, not a subring.  (The corresponding
statement for subrings is false, as the book itself notes after Prop. 6.6:
`k[x₁, x₂, …]` is a non-Noetherian subring of its field of fractions.)  Nothing
in the exercise or in the reference proof requires more than that.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_7_8

open Polynomial

/-- The quotient map `A[X] → A`, `f ↦ f(0)`, is surjective: every `a : A` is the
image of the constant polynomial `C a`.  Hence `A` is a quotient ring of `A[X]`. -/
theorem eval_zero_surjective (A : Type*) [CommRing A] :
    Function.Surjective (Polynomial.evalRingHom (0 : A)) :=
  fun a => ⟨Polynomial.C a, by simp⟩

/-- The kernel of `f ↦ f(0) : A[X] → A` is the ideal `(X)`, i.e. the quotient
given by evaluation at `0` is `A[X]/(X)`. -/
theorem ker_eval_zero (A : Type*) [CommRing A] :
    RingHom.ker (Polynomial.evalRingHom (0 : A)) = Ideal.span {Polynomial.X} := by
  refine le_antisymm ?_ ?_
  · intro f hf
    have h0 : f.coeff 0 = 0 := by
      simpa [RingHom.mem_ker, Polynomial.coeff_zero_eq_eval_zero] using hf
    exact Ideal.mem_span_singleton.2 (Polynomial.X_dvd_iff.2 h0)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      Polynomial.coe_evalRingHom]
    simp

/-- **Atiyah–Macdonald, Chapter 7, Exercise 8.**
If `A[x]` is a Noetherian ring, then `A` is a Noetherian ring: `A` is a quotient
of `A[x]`, namely `A ≅ A[x]/(x)`, and a quotient of a Noetherian ring is
Noetherian. -/
theorem solution (A : Type*) [CommRing A] [IsNoetherianRing (Polynomial A)] :
    IsNoetherianRing A :=
  isNoetherianRing_of_surjective (Polynomial A) A (Polynomial.evalRingHom (0 : A))
    (eval_zero_surjective A)

/-- Exercise 7.8 with the hypothesis passed as an explicit argument rather than
as a typeclass instance. -/
theorem solution_apply (A : Type*) [CommRing A] (h : IsNoetherianRing (Polynomial A)) :
    IsNoetherianRing A :=
  @solution A _ h

/-- Supplementary (not part of Exercise 7.8, the exercise asks only for the
direction `A[x]` Noetherian `→` `A` Noetherian): for a commutative ring `A`,
`A[x]` is Noetherian if and only if `A` is.  The converse is Hilbert's basis
theorem (7.5). -/
theorem isNoetherianRing_polynomial_iff (A : Type*) [CommRing A] :
    IsNoetherianRing (Polynomial A) ↔ IsNoetherianRing A :=
  ⟨fun h => @solution A _ h, fun h => @Polynomial.isNoetherianRing A _ h⟩

end AtiyahMcdonald69.Ex_7_8

