/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 8 ("Artin rings"),
Exercise 8.2.

Statement (as printed in the book):

  Let `A` be a Noetherian ring. Prove that the following are equivalent:
    i)   `A` is Artinian;
    ii)  `Spec(A)` is discrete and finite;
    iii) `Spec(A)` is discrete.

Formalisation and coverage.
* `A` is an arbitrary commutative ring, `[CommRing A]`; Noetherianness is the hypothesis
  `[IsNoetherianRing A]` of the three equivalence theorems.
* "`A` is Artinian" is `IsArtinianRing A`, i.e. the descending chain condition on ideals.
* `Spec(A)` is the topological space `PrimeSpectrum A` (Zariski topology); "discrete" is
  `DiscreteTopology (PrimeSpectrum A)` and "finite" is `Finite (PrimeSpectrum A)`.
* All three assertions are covered: `solution` states the full `List.TFAE`, and the two
  iff-theorems state `(i) ↔ (ii)` and `(i) ↔ (iii)` separately.

The proof follows the book, with each step as its own lemma:
  i ⇒ ii: in an Artinian ring every prime ideal is maximal (Prop. 8.1), so points of the
          spectrum are closed, and there are only finitely many maximal ideals (Prop. 8.3);
          a finite space all of whose points are closed is discrete.
  ii ⇒ iii: immediate.
  iii ⇒ i: closed points of the spectrum are maximal ideals, so every prime ideal is maximal,
          i.e. `Ring.KrullDimLE 0 A`; a Noetherian ring of Krull dimension `0` is Artinian
          (Theorem 8.5, in Mathlib: Hopkins–Levitzki).

Mathlib landmarks used (checked against the local checkout):
`IsArtinianRing.isMaximal_of_isPrime` (Prop. 8.1: primes of an Artinian ring are maximal),
`IsArtinianRing.instFinitePrimeSpectrum` (Prop. 8.3: finitely many maximal ideals),
`PrimeSpectrum.isClosed_singleton_iff_isMaximal` (Exercise 1.18 (i)),
`discreteTopology_iff_forall_isClosed`, `DiscreteTopology.of_finite_of_isClosed_singleton`,
`Ring.KrullDimLE.mk₀`, `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero` (Theorem 8.5,
Hopkins–Levitzki).  The "finite + all points closed ⇒ discrete" step is derived here, not
cited from a pre-packaged equivalence.

Note on hypotheses: `CommRing A` also admits the trivial ring, which Atiyah–Macdonald
exclude by convention; the statement holds there too (the spectrum is empty, and the ring is
Artinian), so this does not weaken the exercise.  No version of the equivalence is assumed.

The Noetherian hypothesis in `(iii) ⇒ (i)` is essential (informal remark, not formalised
below): for a field `k` let `R = k[x_i : i ∈ ℕ]/(x_i x_j : i, j ∈ ℕ)`, i.e. the square-zero
extension of `k` by the infinite-dimensional vector space with basis the `x_i`.  Every `x_i`
is nilpotent, so every prime ideal contains `m = (x_i)`; `m` is maximal (`R/m ≅ k`) and
every element outside `m` is a unit, so `Spec R = {m}` is a single (hence finite, discrete)
point.  Ideals of `R` are exactly the `k`-subspaces of `m` (as `m² = 0`), so the infinite
dimension of `m` gives both a strictly increasing and a strictly decreasing chain of ideals:
`R` is neither Noetherian nor Artinian.  So `(iii) ⇒ (i)` genuinely needs `[IsNoetherianRing A]`.

Source of the natural-language solution:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8-2
-/
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.TFAE

namespace AtiyahMcdonald69.Ex_8_2

open PrimeSpectrum

variable {A : Type*} [CommRing A]

/-! ### `(iii) ⇒ (i)`: a discrete spectrum forces Krull dimension zero -/

/-- If `Spec(A)` is discrete, every prime ideal of `A` is maximal: a point of a discrete
space is closed, and closed points of the prime spectrum are exactly the maximal ideals
(Atiyah–Macdonald, Exercise 1.18 (i)). -/
theorem isMaximal_of_discreteTopology (h : DiscreteTopology (PrimeSpectrum A))
    (p : PrimeSpectrum A) : p.asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
    (discreteTopology_iff_forall_isClosed.mp h {p})

/-- Consequently a ring with discrete spectrum has Krull dimension at most zero. -/
theorem krullDimLE_zero_of_discreteTopology (h : DiscreteTopology (PrimeSpectrum A)) :
    Ring.KrullDimLE 0 A :=
  Ring.KrullDimLE.mk₀ fun I hI => isMaximal_of_discreteTopology h ⟨I, hI⟩

/-- `(iii) ⇒ (i)`: a Noetherian ring whose spectrum is discrete is Artinian. This is the
implication "every zero-dimensional Noetherian ring is Artinian" (Theorem 8.5) applied after
observing that a discrete spectrum has Krull dimension zero. -/
theorem isArtinianRing_of_discreteTopology [IsNoetherianRing A]
    (h : DiscreteTopology (PrimeSpectrum A)) : IsArtinianRing A :=
  @IsNoetherianRing.isArtinianRing_of_krullDimLE_zero A _ _
    (krullDimLE_zero_of_discreteTopology h)

/-! ### `(i) ⇒ (ii)`: the spectrum of an Artinian ring is finite and discrete -/

/-- In an Artinian ring every prime ideal is maximal (Atiyah–Macdonald, Prop. 8.1), hence
every point of the spectrum is closed. -/
theorem isClosed_singleton_of_isArtinianRing [IsArtinianRing A] (p : PrimeSpectrum A) :
    IsClosed ({p} : Set (PrimeSpectrum A)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr
    (IsArtinianRing.isMaximal_of_isPrime p.asIdeal)

/-- An Artinian ring has only finitely many prime ideals (Atiyah–Macdonald, Prop. 8.3:
finitely many maximal ideals). -/
theorem finite_primeSpectrum_of_isArtinianRing [IsArtinianRing A] :
    Finite (PrimeSpectrum A) :=
  inferInstance

/-- A finite space all of whose points are closed is discrete; this is the last step of
Atiyah–Macdonald's proof of `(i) ⇒ (ii)` ("as a result, every subset is closed"). -/
theorem discreteTopology_of_isArtinianRing [IsArtinianRing A] :
    DiscreteTopology (PrimeSpectrum A) :=
  DiscreteTopology.of_finite_of_isClosed_singleton isClosed_singleton_of_isArtinianRing

/-- `(i) ⇒ (ii)`: the prime spectrum of an Artinian ring is finite and discrete. -/
theorem finite_and_discreteTopology_of_isArtinianRing [IsArtinianRing A] :
    Finite (PrimeSpectrum A) ∧ DiscreteTopology (PrimeSpectrum A) :=
  ⟨finite_primeSpectrum_of_isArtinianRing, discreteTopology_of_isArtinianRing⟩

/-! ### The three equivalent conditions -/

/-- Atiyah–Macdonald, Chapter 8, Exercise 8.2, `(i) ↔ (ii)`: for a Noetherian ring, being
Artinian is equivalent to having finite and discrete spectrum. -/
theorem isArtinianRing_iff_finite_and_discreteTopology [IsNoetherianRing A] :
    IsArtinianRing A ↔ Finite (PrimeSpectrum A) ∧ DiscreteTopology (PrimeSpectrum A) where
  mp h := @finite_and_discreteTopology_of_isArtinianRing A _ h
  mpr h := isArtinianRing_of_discreteTopology h.2

/-- Atiyah–Macdonald, Chapter 8, Exercise 8.2, `(i) ↔ (iii)`: for a Noetherian ring, being
Artinian is equivalent to having discrete spectrum. -/
theorem isArtinianRing_iff_discreteTopology [IsNoetherianRing A] :
    IsArtinianRing A ↔ DiscreteTopology (PrimeSpectrum A) where
  mp h := (@finite_and_discreteTopology_of_isArtinianRing A _ h).2
  mpr := isArtinianRing_of_discreteTopology

/-- **Atiyah–Macdonald, Chapter 8, Exercise 8.2.** For a Noetherian ring `A` the following are
equivalent:

  i) `A` is Artinian;
  ii) `Spec(A)` is discrete and finite;
  iii) `Spec(A)` is discrete.

Source: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8-2 -/
theorem solution [IsNoetherianRing A] :
    [IsArtinianRing A, Finite (PrimeSpectrum A) ∧ DiscreteTopology (PrimeSpectrum A),
      DiscreteTopology (PrimeSpectrum A)].TFAE := by
  tfae_have 1 → 2 := fun h => @finite_and_discreteTopology_of_isArtinianRing A _ h
  tfae_have 2 → 3 := fun h => h.2
  tfae_have 3 → 1 := isArtinianRing_of_discreteTopology
  tfae_finish

end AtiyahMcdonald69.Ex_8_2

-- Statement as a plain implication/conjunction form, with all quantifiers explicit.
#check @AtiyahMcdonald69.Ex_8_2.solution

-- Axiom audit: only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
-- are used -- no `sorryAx`, no `admit`, no custom axiom.
#print axioms AtiyahMcdonald69.Ex_8_2.solution
#print axioms AtiyahMcdonald69.Ex_8_2.isArtinianRing_iff_finite_and_discreteTopology
#print axioms AtiyahMcdonald69.Ex_8_2.isArtinianRing_iff_discreteTopology
