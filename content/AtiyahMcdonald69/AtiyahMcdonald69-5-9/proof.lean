import Mathlib

/-!
# Atiyah–Macdonald, Exercise 5.9

Let `A` be a subring of a ring `B`, and let `C` be the integral closure of `A` in `B`.
Exercise 5.9 of Atiyah–Macdonald asks to prove that `C[X]` is the integral closure of
`A[X]` in `B[X]`.

We formalise "`C` is the integral closure of `A` in `B`" with Mathlib's characteristic
predicate `IsIntegralClosure C A B`: the canonical map `C → B` is injective and an element
of `B` is integral over `A` if and only if it lies in the image of `C`.

The mathematical content is the coefficientwise criterion for integrality of polynomials
(`Polynomial.isIntegral_iff_isIntegral_coeff`): `f : B[X]` is integral over `A[X]` iff every
coefficient of `f` is integral over `A`.  Since `IsIntegralClosure.isIntegral_iff` identifies
"integral over `A`" with "in the image of `C`", the result follows for an arbitrary `C`
satisfying the characteristic predicate.

* `isIntegral_iff_forall_coeff_mem` : coefficientwise form for `C = integralClosure A B`.
* `isIntegral_polynomial_integralClosure` : `C[X]` is integral over `A[X]` (the book's first
  paragraph).
* `isIntegralClosure_polynomial` : the statement for an arbitrary integral closure `C`.
* `solution` : the exercise, for `C = integralClosure A B`.
* `solution_subring` : the literal "subring" form of the book, for `S : Subring B`.

Atiyah–Macdonald assume that `A` is a *subring* of `B`, i.e. that `A → B` is injective.
The argument below does not use injectivity of `A → B`, so `solution` is stated for an
arbitrary algebra `A → B` (a harmless generalisation, not a weakening: the subring case is
the special case of an injective algebra map).
-/

namespace AtiyahMcdonald69.Ex_5_9

open Polynomial

/- `Polynomial.algebra` is Mathlib's canonical `Algebra R[X] S[X]` structure induced by
`Algebra R S`.  Mathlib keeps it out of the global instance table (to avoid diamonds with the
`Algebra R S[X]` structure), so we enable it locally for this file.  Concretely, its structure
map `A[X] → B[X]` is `Polynomial.map (algebraMap A B)`. -/
attribute [local instance] Polynomial.algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **Exercise 5.9, coefficientwise form.**  A polynomial `f : B[X]` is integral over `A[X]`
if and only if each of its coefficients lies in the integral closure of `A` in `B`. -/
theorem isIntegral_iff_forall_coeff_mem (f : B[X]) :
    IsIntegral A[X] f ↔ ∀ n, f.coeff n ∈ integralClosure A B := by
  simp only [Polynomial.isIntegral_iff_isIntegral_coeff, mem_integralClosure_iff]

/-- **Exercise 5.9, first half** (the book's first paragraph): the polynomial ring over the
integral closure of `A` in `B` is integral over `A[X]`. -/
theorem isIntegral_polynomial_integralClosure :
    Algebra.IsIntegral A[X] (integralClosure A B)[X] := by
  refine ⟨fun f => ?_⟩
  rw [Polynomial.isIntegral_iff_isIntegral_coeff]
  intro n
  exact IsIntegralClosure.isIntegral (R := A) (B := B) (f.coeff n)

/-- **Exercise 5.9.**  If `C` is the integral closure of `A` in `B`, then `C[X]` is the
integral closure of `A[X]` in `B[X]`. -/
theorem isIntegralClosure_polynomial (C : Type*) [CommRing C] [Algebra C B]
    [IsIntegralClosure C A B] : IsIntegralClosure C[X] A[X] B[X] where
  algebraMap_injective := by
    intro p q hpq
    ext n
    apply IsIntegralClosure.algebraMap_injective C A B
    have := congrArg (fun t : B[X] => t.coeff n) hpq
    simpa using this
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have hcoeff : ∀ n, IsIntegral A (x.coeff n) :=
        Polynomial.isIntegral_iff_isIntegral_coeff.mp hx
      have hlift : x ∈ Polynomial.lifts (algebraMap C B) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact (IsIntegralClosure.isIntegral_iff (A := C)).mp (hcoeff n)
      obtain ⟨y, hy⟩ := hlift
      exact ⟨y, by simpa using hy⟩
    · rintro ⟨y, rfl⟩
      rw [Polynomial.isIntegral_iff_isIntegral_coeff]
      intro n
      have h : IsIntegral A (algebraMap C B (y.coeff n)) :=
        (IsIntegralClosure.isIntegral_iff (A := C)).mpr ⟨y.coeff n, rfl⟩
      simpa using h

/-- **Atiyah–Macdonald, Exercise 5.9.**  Let `A` be a subring of a ring `B` and let `C` be
the integral closure of `A` in `B`.  Then `C[X]` is the integral closure of `A[X]` in
`B[X]`. -/
theorem solution : IsIntegralClosure (integralClosure A B)[X] A[X] B[X] :=
  isIntegralClosure_polynomial (integralClosure A B)

/-- Exercise 5.9 in the literal "subring" form of the book: for a subring `S` of `B`, the
polynomial ring `(integralClosure S B)[X]` is the integral closure of `S[X]` in `B[X]`. -/
theorem solution_subring (S : Subring B) :
    IsIntegralClosure (integralClosure S B)[X] S[X] B[X] :=
  solution (A := S) (B := B)

/-- Non-vacuity check: for `A = ℤ` and `B = ℚ` the theorem says that `ℤ[X]` is integrally
closed in `ℚ[X]` (take `C = ℤ`, which is the integral closure of `ℤ` in `ℚ`).  This is the
classical statement that `ℤ[X]` is integrally closed, recovered here as an instance of
Exercise 5.9. -/
example : IsIntegralClosure ℤ[X] ℤ[X] ℚ[X] :=
  isIntegralClosure_polynomial (A := ℤ) (B := ℚ) ℤ

end AtiyahMcdonald69.Ex_5_9

#print axioms AtiyahMcdonald69.Ex_5_9.isIntegral_iff_forall_coeff_mem
#print axioms AtiyahMcdonald69.Ex_5_9.isIntegral_polynomial_integralClosure
#print axioms AtiyahMcdonald69.Ex_5_9.isIntegralClosure_polynomial
#print axioms AtiyahMcdonald69.Ex_5_9.solution
#print axioms AtiyahMcdonald69.Ex_5_9.solution_subring
