/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 6 ("Chain Conditions"),
Exercise 6.9.

Statement (Chapter 6, Exercise 9 of the book):

  "Deduce from exercise 6.8 that a Noetherian ring A has finitely many minimal prime ideals."

Natural-language proof of the exercise:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-9

Source audit.  The extracted scan `.scratch/reference/atiyah-macdonald-original.txt` stops inside
Chapter 6 (at Corollary 6.11), so it does not reach the Chapter 6 exercises; the statement above is
the one recorded by the solutions manual in the same reference directory ("6.9. Deduce from exercise
6.8 that a Noetherian ring A has finitely many minimal prime ideals"), which is also exactly what
the site's proof establishes.  The only ingredients of that proof are the two preceding exercises
plus the book's own Chapter 1, Exercise 20 iv ("the irreducible components of Spec A are the closed
sets V(p) where p is a minimal prime ideal of A"); no generalization or extra hypothesis is
involved, so there is no correction to make.

The intended deduction, formalized below, is:
  * Exercise 6.8: if `A` is Noetherian then `Spec A` is a Noetherian topological space;
  * Exercise 6.7 (second part): a Noetherian topological space has finitely many irreducible
    components;
  * the irreducible components of `Spec A` are exactly the zero loci `V(p)` of the minimal prime
    ideals `p` (`V` reverses inclusions of primes, and every irreducible closed set is a `V(p)`),
  hence the set of minimal prime ideals is finite.

In Mathlib, `minimalPrimes A` is by definition the set of minimal prime ideals of `A`
(`Ideal.IsMinimalPrime`, i.e. `Minimal Ideal.IsPrime p`); see `minimalPrimes_eq_minimals`.
-/
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

namespace AtiyahMcdonald69.Ex_6_9

open TopologicalSpace

/-- Atiyah–Macdonald, Exercise 6.8 (the direction used in Exercise 6.9): the prime spectrum of a
Noetherian ring is a Noetherian topological space. -/
theorem spec_noetherian (A : Type*) [CommRing A] [IsNoetherianRing A] :
    NoetherianSpace (PrimeSpectrum A) :=
  PrimeSpectrum.instNoetherianSpace A

/-- Atiyah–Macdonald, Exercise 6.7 (second assertion): a Noetherian topological space has only
finitely many irreducible components. -/
theorem irreducibleComponents_finite {X : Type*} [TopologicalSpace X] [NoetherianSpace X] :
    (irreducibleComponents X).Finite :=
  NoetherianSpace.finite_irreducibleComponents

/-- The correspondence used in the proof of Exercise 6.9: for a prime ideal `p`, the closed set
`V(p) = {p' | p ≤ p'}` is an irreducible component of `Spec A` if and only if `p` is a minimal
prime ideal of `A`.  (This is Chapter 1, Exercise 20 iv of the book.) -/
theorem zeroLocus_mem_irreducibleComponents_iff (A : Type*) [CommRing A] (p : Ideal A)
    (hp : p.IsPrime) :
    PrimeSpectrum.zeroLocus (p : Set A) ∈ irreducibleComponents (PrimeSpectrum A) ↔
      p ∈ minimalPrimes A := by
  rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents,
    Ideal.IsRadical.radical (Ideal.IsPrime.isRadical hp)]

/-- The precise form of the correspondence used in Exercise 6.9: `p ↦ V(p)` is a bijection from
the set of minimal prime ideals of `A` onto the set of irreducible components of `Spec A`. -/
theorem bijOn_zeroLocus (A : Type*) [CommRing A] :
    Set.BijOn (fun p : Ideal A => PrimeSpectrum.zeroLocus (p : Set A))
      (minimalPrimes A) (irreducibleComponents (PrimeSpectrum A)) := by
  refine ⟨fun p hp => (zeroLocus_mem_irreducibleComponents_iff A p hp.1.1).mpr hp, ?_, ?_⟩
  · -- injectivity on primes: `V(p) = V(q)` iff `p.radical = q.radical`, and primes are radical
    intro p hp q hq hpq
    rw [PrimeSpectrum.zeroLocus_eq_iff,
      Ideal.IsRadical.radical (Ideal.IsPrime.isRadical hp.1.1),
      Ideal.IsRadical.radical (Ideal.IsPrime.isRadical hq.1.1)] at hpq
    exact hpq
  · -- surjectivity: every irreducible component of `Spec A` is `V(p)` for a minimal prime `p`
    intro s hs
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes A] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p, hp, rfl⟩

/-- **Atiyah–Macdonald, Exercise 6.9.**  A Noetherian ring has finitely many minimal prime
ideals.

Proof following the book's intended deduction: `Spec A` is a Noetherian space (Exercise 6.8),
hence it has finitely many irreducible components (Exercise 6.7), and those components are the
zero loci `V(p)` of the minimal prime ideals `p` (Chapter 1, Exercise 20 iv), so there are only
finitely many minimal prime ideals. -/
theorem solution (A : Type*) [CommRing A] [IsNoetherianRing A] :
    (minimalPrimes A).Finite := by
  -- Exercise 6.7 applied to the Noetherian space `Spec A` supplied by Exercise 6.8.
  have h : (irreducibleComponents (PrimeSpectrum A)).Finite :=
    @irreducibleComponents_finite (PrimeSpectrum A) _ (spec_noetherian A)
  -- The irreducible components of `Spec A` are exactly the sets `V(p)` for minimal primes `p`,
  -- i.e. taking vanishing ideals is a bijection from components to minimal primes.
  rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
  exact h.image _

/-- Exercise 6.9 in the book's own wording: the set of minimal prime ideals, i.e. the primes that
are minimal among all primes, is finite. -/
theorem finite_isMinimalPrime (A : Type*) [CommRing A] [IsNoetherianRing A] :
    {p : Ideal A | Minimal Ideal.IsPrime p}.Finite := by
  simpa [minimalPrimes_eq_minimals] using solution A

/-- Cross-check that the formal statement of Exercise 6.9 is the same assertion as the direct
finiteness theorem for minimal primes already available in Mathlib (which is proved by a
Noetherian-induction argument, independently of `Spec`). -/
theorem solution_via_mathlib (A : Type*) [CommRing A] [IsNoetherianRing A] :
    (minimalPrimes A).Finite :=
  minimalPrimes.finite_of_isNoetherianRing A

end AtiyahMcdonald69.Ex_6_9

#print axioms AtiyahMcdonald69.Ex_6_9.solution
#print axioms AtiyahMcdonald69.Ex_6_9.zeroLocus_mem_irreducibleComponents_iff
#print axioms AtiyahMcdonald69.Ex_6_9.bijOn_zeroLocus
#print axioms AtiyahMcdonald69.Ex_6_9.spec_noetherian
#print axioms AtiyahMcdonald69.Ex_6_9.irreducibleComponents_finite
#print axioms AtiyahMcdonald69.Ex_6_9.finite_isMinimalPrime
#print axioms AtiyahMcdonald69.Ex_6_9.solution_via_mathlib
