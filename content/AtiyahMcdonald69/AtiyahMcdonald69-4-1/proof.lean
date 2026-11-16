/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 4, Exercise 1.

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-1

**Statement** (book, Ch. IV, Exercises, no. 1):

  If an ideal `𝔞` has a primary decomposition, then `Spec(A/𝔞)` has only finitely many
  irreducible components.

Book definitions used (Ch. IV, p. 50–51): an ideal `q` of `A` is *primary* if `q ≠ (1)` and
`xy ∈ q` implies `x ∈ q` or `y ∈ r(q)` — this is `Ideal.IsPrimary`; and a *primary
decomposition* of `𝔞` is an expression of `𝔞` as an intersection of a *finite* number of
primary ideals (minimality is **not** required).  The primes *belonging to* a decomposition
`𝔞 = ⋂ᵢ qᵢ` are the `r(qᵢ)`, and by Proposition 4.6 the minimal prime ideals of `𝔞` are
exactly the minimal elements of this finite set of primes.  By Chapter I, Exercise 20 the
irreducible components of `Spec(A/𝔞)` are the `V(p)` for `p` a minimal prime of `𝔞`.

**Formalisation.**  The hypothesis is stated as `I = s.inf id` for a finite set `s` of
primary ideals — the same shape as Mathlib's `IsLasker` (`∃ s, s.inf id = N ∧ ∀ J ∈ s,
J.IsPrimary`), see `RingTheory/Lasker.lean`.

* `radical_finset_inf` : the radical of a finite intersection is the intersection of the
  radicals.
* `minimalPrimes_subset_radical_image` : every minimal prime over `I = ⋂_{q ∈ s} q` is
  `r(q)` for some `q ∈ s` (the "isolated primes belong to the decomposition" half of
  Prop. 4.6, valid for any — not necessarily minimal — primary decomposition).
* `minimalPrimes_eq_minimals_radical_image` : Prop. 4.6 in full for isolated primes: the
  minimal primes over `I` are exactly the minimal elements of `{r(q) | q ∈ s}`.
* `finite_minimalPrimes_of_primary_decomposition` : `I` has finitely many minimal primes.
* `finite_minimalPrimes_quotient` : the minimal primes of `A ⧸ I` correspond bijectively to
  the minimal primes over `I` (contraction of the quotient map).
* `finite_irreducibleComponents_zeroLocus` : `V(𝔞) ⊆ Spec A` has finitely many irreducible
  components (Ch. I Ex. 20, `Ideal.minimalPrimes.equivIrreducibleComponents`).
* `solution` : the exercise, `Spec (A ⧸ 𝔞)` has finitely many irreducible components.
* `solution_of_isLasker` : the same for a ring in which *every* ideal has a primary
  decomposition (Mathlib's `IsLasker R R`).
* `solution_of_isMinimalPrimaryDecomposition` : the same starting from a minimal primary
  decomposition in Mathlib's sense (`Submodule.IsMinimalPrimaryDecomposition`).

No hypothesis on `A` other than commutativity is used — in particular no Noetherian
hypothesis, which is the point of the exercise.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_4_1

open PrimeSpectrum

variable {R : Type*} [CommRing R]

/-! ### The radical of a finite intersection -/

/-- The radical of a finite intersection of ideals is the intersection of the radicals:
`r(⋂_{q ∈ s} q) = ⋂_{q ∈ s} r(q)`.  (For infinitely many ideals only `≤` holds.) -/
theorem radical_finset_inf (s : Finset (Ideal R)) :
    (s.inf id).radical = s.inf fun q => q.radical := by
  rw [← Ideal.radicalInfTopHom_apply, map_finset_inf]
  rfl

/-! ### Minimal primes come from the primary components (Proposition 4.6) -/

/-- **Proposition 4.6, "isolated primes belong to the decomposition".**
If `I` is the intersection of a finite family of primary ideals `q ∈ s`, then every minimal
prime ideal over `I` is the radical of one of the `q`.

Argument: `I ≤ p` with `p` prime gives `r(I) ≤ p`; since `r` turns the finite intersection
into the finite intersection of the prime ideals `r(q)`, primarity of `p` singles out some
`q ∈ s` with `r(q) ≤ p`; but `r(q)` is a prime containing `I`, so minimality of `p` forces
`p = r(q)`. -/
theorem minimalPrimes_subset_radical_image (s : Finset (Ideal R))
    (hs : ∀ q ∈ s, q.IsPrimary) :
    (s.inf id).minimalPrimes ⊆ (fun q : Ideal R => q.radical) '' (↑s : Set (Ideal R)) := by
  rintro p ⟨hp, hmin⟩
  obtain ⟨hpq, hle⟩ := hp
  have h1 : (s.inf id).radical ≤ p := hpq.radical_le_iff.mpr hle
  rw [radical_finset_inf] at h1
  obtain ⟨q, hq, hqp⟩ := hpq.inf_le'.mp h1
  have hpq' : p ≤ q.radical :=
    hmin ⟨Ideal.isPrime_radical (hs q hq), (Finset.inf_le hq).trans Ideal.le_radical⟩ hqp
  exact ⟨q, hq, (le_antisymm hpq' hqp).symm⟩

/-- **Proposition 4.6 for isolated primes, in full.**  If `I = ⋂_{q ∈ s} q` is a finite
intersection of primary ideals, then the minimal prime ideals over `I` are exactly the
minimal elements of the finite set `{r(q) | q ∈ s}` of primes belonging to the
decomposition. -/
theorem minimalPrimes_eq_minimals_radical_image (s : Finset (Ideal R))
    (hs : ∀ q ∈ s, q.IsPrimary) :
    (s.inf id).minimalPrimes =
      {p | p ∈ (fun q : Ideal R => q.radical) '' (↑s : Set (Ideal R)) ∧
        ∀ m ∈ (fun q : Ideal R => q.radical) '' (↑s : Set (Ideal R)), m ≤ p → p ≤ m} := by
  ext p
  constructor
  · intro hp
    refine ⟨minimalPrimes_subset_radical_image s hs hp, ?_⟩
    rintro m ⟨r, hr, rfl⟩ hmp
    exact hp.2 ⟨Ideal.isPrime_radical (hs r hr), (Finset.inf_le hr).trans Ideal.le_radical⟩ hmp
  · rintro ⟨hp, hmin⟩
    obtain ⟨q, hq, hpq⟩ := hp
    have hpq' : Ideal.radical q = p := hpq
    subst hpq'
    refine ⟨⟨Ideal.isPrime_radical (hs q hq), (Finset.inf_le hq).trans Ideal.le_radical⟩, ?_⟩
    intro z hz hzp
    -- a prime between `I` and `r(q)` dominates a minimal prime over `I`, which is itself
    -- the radical of a component, so minimality of `r(q)` among the components applies
    obtain ⟨z', hz', hz'z⟩ := @Ideal.exists_minimalPrimes_le R _ (s.inf id) z hz.1 hz.2
    obtain ⟨r, hr, hrp⟩ := minimalPrimes_subset_radical_image s hs hz'
    have hrp' : Ideal.radical r = z' := hrp
    have h1 : Ideal.radical q ≤ Ideal.radical r :=
      hmin (Ideal.radical r) ⟨r, hr, rfl⟩ (by rw [hrp']; exact hz'z.trans hzp)
    rw [hrp'] at h1
    exact h1.trans hz'z

/-! ### Finiteness of the minimal primes -/

/-- If an ideal has a primary decomposition, it has only finitely many minimal primes:
they are among the radicals of the primary components, of which there are finitely many. -/
theorem finite_minimalPrimes_of_primary_decomposition (I : Ideal R)
    (h : ∃ s : Finset (Ideal R), (∀ q ∈ s, q.IsPrimary) ∧ s.inf id = I) :
    I.minimalPrimes.Finite := by
  obtain ⟨s, hs, rfl⟩ := h
  exact (s.finite_toSet.image (fun q : Ideal R => q.radical)).subset
    (minimalPrimes_subset_radical_image s hs)

/-- The same statement for a minimal primary decomposition in Mathlib's sense
(`Submodule.IsMinimalPrimaryDecomposition`, the hypothesis of the first uniqueness theorem
4.5). -/
theorem finite_minimalPrimes_of_isMinimalPrimaryDecomposition {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) : I.minimalPrimes.Finite :=
  finite_minimalPrimes_of_primary_decomposition I ⟨t, fun _ hq => ht.primary hq, ht.inf_eq⟩

/-- The minimal primes of `A ⧸ I` are the contractions of the prime ideals minimal over `I`,
so there are only finitely many of them. -/
theorem finite_minimalPrimes_quotient (I : Ideal R) (h : I.minimalPrimes.Finite) :
    (minimalPrimes (R ⧸ I)).Finite := by
  refine Set.Finite.of_finite_image
    (f := Ideal.comap (Ideal.Quotient.mk I)) ?_ ?_
  · rwa [← Ideal.minimalPrimes_eq_comap]
  · exact Set.injOn_of_injective
      (Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)

/-- The closed set `V(𝔞) ⊆ Spec A` has only finitely many irreducible components.  By
Chapter I, Exercise 20 (`Ideal.minimalPrimes.equivIrreducibleComponents`) its components are
the `V(p)` for `p` minimal over `𝔞`. -/
theorem finite_irreducibleComponents_zeroLocus (I : Ideal R)
    (h : ∃ s : Finset (Ideal R), (∀ q ∈ s, q.IsPrimary) ∧ s.inf id = I) :
    (irreducibleComponents (zeroLocus (I : Set R))).Finite := by
  have hI : Finite ↑I.minimalPrimes :=
    finite_minimalPrimes_of_primary_decomposition I h
  exact Finite.of_equiv _ (Ideal.minimalPrimes.equivIrreducibleComponents I).toEquiv

/-! ### The exercise -/

/-- **Atiyah–Macdonald, Chapter IV, Exercise 1.**
If an ideal `𝔞` of a commutative ring `A` has a primary decomposition, then `Spec (A / 𝔞)`
has only finitely many irreducible components. -/
theorem solution (I : Ideal R)
    (h : ∃ s : Finset (Ideal R), (∀ q ∈ s, q.IsPrimary) ∧ s.inf id = I) :
    (irreducibleComponents (PrimeSpectrum (R ⧸ I))).Finite := by
  have hmin : (minimalPrimes (R ⧸ I)).Finite :=
    finite_minimalPrimes_quotient I (finite_minimalPrimes_of_primary_decomposition I h)
  -- the irreducible components of `Spec (A ⧸ 𝔞)` are the zero loci of its minimal primes
  rw [← zeroLocus_minimalPrimes (R := R ⧸ I)]
  exact hmin.image _

/-- The exercise in the form "every ideal has a primary decomposition" (Mathlib's
`IsLasker R R`): then `Spec (A ⧸ 𝔞)` has finitely many irreducible components for every
`𝔞`. -/
theorem solution_of_isLasker (h : IsLasker R R) (I : Ideal R) :
    (irreducibleComponents (PrimeSpectrum (R ⧸ I))).Finite := by
  obtain ⟨s, hs, hprim⟩ := h I
  exact solution I ⟨s, fun q hq => hprim hq, hs⟩

/-- The exercise, starting from a Mathlib minimal primary decomposition of `𝔞`. -/
theorem solution_of_isMinimalPrimaryDecomposition {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) :
    (irreducibleComponents (PrimeSpectrum (R ⧸ I))).Finite := by
  have hmin : (minimalPrimes (R ⧸ I)).Finite :=
    finite_minimalPrimes_quotient I (finite_minimalPrimes_of_isMinimalPrimaryDecomposition ht)
  rw [← zeroLocus_minimalPrimes (R := R ⧸ I)]
  exact hmin.image _

/-! ### Sanity checks: the hypothesis is satisfiable -/

section Checks

/-- A prime ideal is its own primary decomposition, so the hypothesis holds; the spectrum
of a quotient by a prime ideal is irreducible, hence has exactly one component. -/
example (p : Ideal R) [hp : p.IsPrime] :
    (irreducibleComponents (PrimeSpectrum (R ⧸ p))).Finite :=
  solution p ⟨{p}, fun q hq => by
    rw [Finset.mem_singleton] at hq
    exact hq ▸ hp.isPrimary, by simp⟩

/-- In a field the zero ideal is primary, so `Spec` of the field (a single point) has
finitely many irreducible components. -/
example : (irreducibleComponents (PrimeSpectrum (ℚ ⧸ (⊥ : Ideal ℚ)))).Finite :=
  solution (⊥ : Ideal ℚ) ⟨{⊥}, fun q hq => by
    rw [Finset.mem_singleton] at hq
    exact hq ▸ Ideal.IsPrime.isPrimary (inferInstance : (⊥ : Ideal ℚ).IsPrime), by simp⟩

end Checks

end AtiyahMcdonald69.Ex_4_1

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_4_1.minimalPrimes_subset_radical_image
#print axioms AtiyahMcdonald69.Ex_4_1.minimalPrimes_eq_minimals_radical_image
#print axioms AtiyahMcdonald69.Ex_4_1.finite_minimalPrimes_of_isMinimalPrimaryDecomposition
#print axioms AtiyahMcdonald69.Ex_4_1.finite_minimalPrimes_of_primary_decomposition
#print axioms AtiyahMcdonald69.Ex_4_1.finite_irreducibleComponents_zeroLocus
#print axioms AtiyahMcdonald69.Ex_4_1.solution
#print axioms AtiyahMcdonald69.Ex_4_1.solution_of_isMinimalPrimaryDecomposition
#print axioms AtiyahMcdonald69.Ex_4_1.solution_of_isLasker
