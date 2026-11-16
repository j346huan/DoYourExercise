/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 7 (Noetherian rings), Exercise 25.

Statement (AM 7.25):
  Let `A` be a Noetherian ring and `f : A → B` a flat homomorphism of finite type.
  Show that `f^* : Spec B → Spec A` is an open mapping.

Here `f^* = PrimeSpectrum.comap f : PrimeSpectrum B → PrimeSpectrum A`,
`q ↦ f ⁻¹(q)`, and "open mapping" is `IsOpenMap`, i.e. the image of every open
set is open.

The book's verification goes: flat homomorphisms have the going-down property
(exercise 5.11), and a homomorphism of finite type whose induced map on spectra
has the going-down property is open (exercise 7.24); over a Noetherian ring
finite type = finite presentation, which is the form in which the openness
criterion (`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`,
Mathlib's Chevalley theorem for spectra) is available.

Natural proof URL:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-25
-/
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FinitePresentation

namespace AtiyahMcdonald69.Ex_7_25

open PrimeSpectrum

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

/-! ### Going down for flat homomorphisms (AM 5.11)

The going-down property of exercise 5.10 in its ideal-theoretic formulation:
if `p ≤ q` are primes of `A`, and `Q` is a prime of `B` lying over `q`, then there
is a prime `P ≤ Q` of `B` lying over `p`.  Flat homomorphisms have this property
(`Algebra.HasGoingDown.of_flat`); this is the first half of the book's argument
for 7.25. -/
theorem exists_ideal_le_liesOver_of_flat [Algebra A B] [Module.Flat A B]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver q]
    (hpq : p ≤ q) : ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p :=
  Ideal.exists_ideal_le_liesOver_of_le Q hpq

/-- Over a Noetherian ring a homomorphism of finite type is of finite presentation; this
is the reduction that lets 7.25 be deduced from the finite-presentation openness
criterion for `Spec`. -/
theorem finitePresentation_of_finiteType [IsNoetherianRing A] {f : A →+* B}
    (hf : f.FiniteType) : f.FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType.mp hf

/-! ### The algebra form of 7.25 -/

/-- Exercise 7.25, for the structure morphism of a flat algebra of finite type over a
Noetherian ring: `Spec B → Spec A` is an open map. -/
theorem solution_algebra [IsNoetherianRing A] [Algebra A B] [Module.Flat A B]
    [Algebra.FiniteType A B] : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)) := by
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-! ### Exercise 7.25 in the form stated in the book -/

/-- **Atiyah–Macdonald, Exercise 7.25.** Let `A` be a Noetherian ring and
`f : A → B` a flat homomorphism of finite type. Then the induced map
`f^* : Spec B → Spec A`, `q ↦ f ⁻¹(q)`, is an open mapping. -/
theorem solution [IsNoetherianRing A] (f : A →+* B)
    (hflat : f.Flat) (hft : f.FiniteType) :
    IsOpenMap (PrimeSpectrum.comap f) := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hflat
  have : Algebra.FiniteType A B := hft
  have : Algebra.FinitePresentation A B := RingHom.FinitePresentation.of_finiteType.mp hft
  have h : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  simpa only [RingHom.algebraMap_toAlgebra] using h

/-! ### Consistency checks: the hypotheses of 7.25 are satisfiable

`ℤ → ℤ[X]` is flat (the polynomial ring is a free, hence flat, module) and of
finite type, so `Spec ℤ[X] → Spec ℤ` is an open map; and the identity of `ℤ`
gives the degenerate example. -/

example : IsOpenMap (PrimeSpectrum.comap (RingHom.id ℤ)) :=
  solution (RingHom.id ℤ) (RingHom.Flat.id ℤ) (RingHom.FiniteType.id ℤ)

open Polynomial in
example : IsOpenMap (PrimeSpectrum.comap (Polynomial.C : ℤ →+* ℤ[X])) := by
  have flat : Module.Flat ℤ ℤ[X] := Module.Flat.of_free
  simpa [Polynomial.algebraMap_eq] using solution_algebra (A := ℤ) (B := ℤ[X])

#print axioms AtiyahMcdonald69.Ex_7_25.finitePresentation_of_finiteType
#print axioms AtiyahMcdonald69.Ex_7_25.exists_ideal_le_liesOver_of_flat
#print axioms AtiyahMcdonald69.Ex_7_25.solution_algebra
#print axioms AtiyahMcdonald69.Ex_7_25.solution

end AtiyahMcdonald69.Ex_7_25
