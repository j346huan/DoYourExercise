/-
Copyright: public domain.

# Atiyah–Macdonald, Exercise 4.16

*Statement* (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 4, Exercise 16):

> If `A` is a ring in which every ideal has a primary decomposition, show that every ring of
> fractions `S⁻¹A` has the same property.

The relevant definitions are on page 50–52 of the book:

* an ideal `q` of `A` is **primary** if `q ≠ A` and `xy ∈ q` implies `x ∈ q` or `yⁿ ∈ q` for
  some `n > 0`;
* a **primary decomposition** of an ideal `I` is an expression of `I` as a finite intersection of
  primary ideals, and `I` is **decomposable** if it has one.

Mathlib's `Ideal.IsPrimary` is exactly the first notion (see `Ideal.isPrimary_iff`), and "finite
intersection" is encoded below as an intersection over a `Finset` of ideals, the empty
intersection being `⊤`.  (Mathlib states the second alternative of the definition as
`y ∈ Ideal.radical q`, i.e. `yⁿ ∈ q` for some `n ≥ 0`; for a proper ideal this agrees with the
book's `n > 0`, since `y⁰ = 1 ∈ q` would force `q = A`.)  The empty family must be allowed:
`⊤ = (1)` is not primary, so otherwise no ring at all would satisfy the hypothesis of the
exercise.  (For proper ideals the
decomposition is automatically non-empty; `HasProperPrimaryDecomposition` and
`hasProperPrimaryDecomposition_of_isLocalization` below record this convention-free form.)

The proof is the book's: an ideal of `S⁻¹A` is the extension of its contraction
(`IsLocalization.map_under`), extension along a localization commutes with finite intersections
(`IsLocalization.map_inf`), and a primary ideal of `A` extends either to a primary ideal of
`S⁻¹A` or to the whole ring (Proposition 4.8); the latter components are discarded.

## Main results

* `hasPrimaryDecomposition_of_isLocalization`: Exercise 4.16 for an arbitrary ring of fractions.
* `solution`: the same statement for `Localization S`.
* `isPrimary_map`: Atiyah–Macdonald, Proposition 4.8(ii) (the only ingredient not in Mathlib).
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_4_16

open Ideal

/-- `HasPrimaryDecomposition A` says that every ideal of `A` is a finite intersection of primary
ideals.  The family may be empty, so that `⊤` is always decomposable (its intersection of no
primary ideals); see the module docstring. -/
def HasPrimaryDecomposition (A : Type*) [CommRing A] : Prop :=
  ∀ I : Ideal A, ∃ s : Finset (Ideal A), s.inf id = I ∧ ∀ ⦃q⦄, q ∈ s → q.IsPrimary

/-- Convention-free form of the hypothesis of Exercise 4.16: every *proper* ideal is a non-empty
finite intersection of primary ideals. -/
def HasProperPrimaryDecomposition (A : Type*) [CommRing A] : Prop :=
  ∀ I : Ideal A, I ≠ ⊤ →
    ∃ s : Finset (Ideal A), s.Nonempty ∧ s.inf id = I ∧ ∀ ⦃q⦄, q ∈ s → q.IsPrimary

variable {A S : Type*} [CommRing A] [CommRing S]

/-- Extension of ideals along a localization commutes with finite intersections. -/
lemma map_finset_inf (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (s : Finset (Ideal A)) :
    (s.inf id).map (algebraMap A S) = s.inf fun q => q.map (algebraMap A S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert a s ha ih =>
    simp only [Finset.inf_insert, id_eq]
    rw [IsLocalization.map_inf M S, ih]

/-- Atiyah–Macdonald, Proposition 4.8(ii), in the form needed here: if `q` is a primary ideal of
`A` and `q` survives localization, i.e. `q · S⁻¹A ≠ S⁻¹A`, then `q · S⁻¹A` is primary in
`S⁻¹A`.  (If `q` meets the submonoid `M` then `q · S⁻¹A` is the whole ring, so the hypothesis
cannot be dropped; `IsLocalization.map_algebraMap_ne_top_iff_disjoint` relates it to
`Disjoint M q`.) -/
lemma isPrimary_map (M : Submonoid A) [Algebra A S] [IsLocalization M S] {I : Ideal A}
    (hI : I.IsPrimary) (h : I.map (algebraMap A S) ≠ ⊤) :
    (I.map (algebraMap A S)).IsPrimary := by
  rw [Ideal.isPrimary_iff] at hI ⊢
  obtain ⟨-, hkey⟩ := hI
  refine ⟨h, ?_⟩
  intro x y hxy
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M y
  rw [← IsLocalization.mk'_mul] at hxy
  rw [IsLocalization.mk'_mem_map_algebraMap_iff] at hxy
  obtain ⟨c, hcM, hc⟩ := hxy
  have hc' : (c * a) * b ∈ I := by rwa [mul_assoc]
  rcases hkey hc' with h1 | h2
  · left
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨c, hcM, h1⟩
  · right
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h2
    rw [Ideal.mem_radical_iff]
    refine ⟨n, ?_⟩
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨1, M.one_mem, by rwa [one_mul]⟩

/-- Atiyah–Macdonald, Proposition 4.8(i): if the radical of `I` meets the submonoid `M`, then
`I · S⁻¹A` is the whole ring of fractions.  (No primariness is needed for this direction; it is
the contrapositive of `IsLocalization.map_algebraMap_ne_top_iff_disjoint`.) -/
lemma map_eq_top_of_radical_not_disjoint (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    {I : Ideal A} (h : ¬ Disjoint (M : Set A) (I.radical : Set A)) :
    I.map (algebraMap A S) = ⊤ := by
  obtain ⟨m, hmM, hm⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hm
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn) ?_
  exact IsLocalization.map_units S ⟨m ^ n, M.pow_mem hmM n⟩

/-- Atiyah–Macdonald, Proposition 4.8(ii), in the book's form: if `q` is a primary ideal whose
radical is disjoint from the submonoid `M`, then `q · S⁻¹A` is primary, its radical is
`(radical q) · S⁻¹A`, and it contracts back to `q`.  This shows that the hypothesis
`q · S⁻¹A ≠ S⁻¹A` of `isPrimary_map` is the book's `M ∩ radical q = ∅`. -/
theorem map_isPrimary_of_disjoint_radical (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    {I : Ideal A} (hI : I.IsPrimary) (hM : Disjoint (M : Set A) (I.radical : Set A)) :
    (I.map (algebraMap A S)).IsPrimary ∧
      (I.map (algebraMap A S)).radical = I.radical.map (algebraMap A S) ∧
      (I.map (algebraMap A S)).under A = I := by
  have hdisj : Disjoint (M : Set A) (I : Set A) := Disjoint.mono le_rfl Ideal.le_radical hM
  exact ⟨isPrimary_map M hI ((IsLocalization.map_algebraMap_ne_top_iff_disjoint M S I).mpr hdisj),
    (IsLocalization.map_radical M S I).symm,
    IsLocalization.under_map_of_isPrimary_disjoint M S hI hdisj⟩

/-- Discarding the components whose extension is the unit ideal does not change the
intersection. -/
lemma inf_filter_eq (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (s : Finset (Ideal A)) (p : Ideal A → Prop) [DecidablePred p]
    (h : ∀ q ∈ s, ¬ p q → q.map (algebraMap A S) = ⊤) :
    (s.filter p).inf (fun q => q.map (algebraMap A S))
      = s.inf fun q => q.map (algebraMap A S) := by
  classical
  refine le_antisymm (Finset.le_inf fun q hq => ?_) (Finset.inf_mono (Finset.filter_subset p s))
  by_cases hp : p q
  · exact Finset.inf_le (Finset.mem_filter.mpr ⟨hq, hp⟩)
  · rw [h q hq hp]
    exact le_top

/-- The components of the decomposition of `J` that we keep are primary. -/
lemma image_filter_primary (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (s : Finset (Ideal A)) (hsp : ∀ ⦃q⦄, q ∈ s → q.IsPrimary) :
    ∀ q ∈ (s.filter fun q => q.map (algebraMap A S) ≠ ⊤).image
        (fun q => q.map (algebraMap A S)), q.IsPrimary := by
  intro q hq
  rw [Finset.mem_image] at hq
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  rw [Finset.mem_filter] at hq₀
  exact isPrimary_map M (hsp hq₀.1) hq₀.2

/-- Extending a primary decomposition of the contraction of `J` and discarding the components
that become the unit ideal yields a primary decomposition of `J`. -/
lemma inf_image_filter (M : Submonoid A) [Algebra A S] [IsLocalization M S] (J : Ideal S)
    (s : Finset (Ideal A)) (hs : s.inf id = J.under A) :
    ((s.filter fun q => q.map (algebraMap A S) ≠ ⊤).image
        (fun q => q.map (algebraMap A S))).inf id = J := by
  classical
  rw [Finset.inf_image]
  simp only [Function.comp_def, id_eq]
  rw [inf_filter_eq M s (fun q => q.map (algebraMap A S) ≠ ⊤) fun q _ hq => not_not.mp hq,
    ← map_finset_inf M, hs]
  exact IsLocalization.map_under M S J

/-- **Atiyah–Macdonald, Exercise 4.16.** If every ideal of `A` has a primary decomposition, then
so does every ideal of any ring of fractions `S⁻¹A`. -/
theorem hasPrimaryDecomposition_of_isLocalization (M : Submonoid A) [Algebra A S]
    [IsLocalization M S] (hA : HasPrimaryDecomposition A) : HasPrimaryDecomposition S := by
  classical
  intro J
  obtain ⟨s, hs, hsp⟩ := hA (J.under A)
  exact ⟨_, inf_image_filter M J s hs, image_filter_primary M s hsp⟩

/-- Atiyah–Macdonald, Exercise 4.16 in its original form, for the ring of fractions
`S⁻¹A = Localization S`. -/
theorem solution (S : Submonoid A) (hA : HasPrimaryDecomposition A) :
    HasPrimaryDecomposition (Localization S) :=
  hasPrimaryDecomposition_of_isLocalization S hA

/-- Convention-free form of Exercise 4.16: if every proper ideal of `A` is a (non-empty) finite
intersection of primary ideals, then the same holds for every ring of fractions `S⁻¹A`. -/
theorem hasProperPrimaryDecomposition_of_isLocalization (M : Submonoid A) [Algebra A S]
    [IsLocalization M S] (hA : HasProperPrimaryDecomposition A) :
    HasProperPrimaryDecomposition S := by
  classical
  intro J hJ
  have hunder : J.under A ≠ ⊤ := fun h =>
    hJ (by rw [← IsLocalization.map_under M S J, h, Ideal.map_top])
  obtain ⟨s, -, hs, hsp⟩ := hA (J.under A) hunder
  refine ⟨_, ?_, inf_image_filter M J s hs, image_filter_primary M s hsp⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have h := inf_image_filter M J s hs
  rw [hemp, Finset.inf_empty] at h
  exact hJ h.symm

/-- The hypothesis of the exercise is satisfiable (so the exercise is not vacuous): in a field
every ideal is `⊥` or `⊤`, and `⊥` is primary because it is prime. -/
theorem hasPrimaryDecomposition_of_field (K : Type*) [Field K] :
    HasPrimaryDecomposition K := by
  intro I
  rcases Ideal.eq_bot_or_top I with rfl | rfl
  · refine ⟨{⊥}, by simp, ?_⟩
    intro q hq
    rw [Finset.mem_singleton] at hq
    exact hq ▸ Ideal.isPrime_bot.isPrimary
  · exact ⟨∅, by simp⟩

/-- The main theorem applies to a concrete ring of fractions: if `K` is a field, every ideal of
`K` is primary-decomposable, hence so is every ideal of `K` localized at any submonoid. -/
example (K : Type*) [Field K] (T : Submonoid K) :
    HasPrimaryDecomposition (Localization T) :=
  hasPrimaryDecomposition_of_isLocalization T (hasPrimaryDecomposition_of_field K)

end AtiyahMcdonald69.Ex_4_16

#print axioms AtiyahMcdonald69.Ex_4_16.hasPrimaryDecomposition_of_isLocalization
#print axioms AtiyahMcdonald69.Ex_4_16.solution
#print axioms AtiyahMcdonald69.Ex_4_16.hasProperPrimaryDecomposition_of_isLocalization
#print axioms AtiyahMcdonald69.Ex_4_16.isPrimary_map
#print axioms AtiyahMcdonald69.Ex_4_16.map_isPrimary_of_disjoint_radical
#print axioms AtiyahMcdonald69.Ex_4_16.hasPrimaryDecomposition_of_field
#print axioms AtiyahMcdonald69.Ex_4_16.map_finset_inf
