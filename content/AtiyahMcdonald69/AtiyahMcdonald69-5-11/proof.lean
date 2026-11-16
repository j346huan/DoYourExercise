/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 5.11:

  "Let f : A → B be a flat homomorphism of rings. Then f has the going-down property."

The going-down property is defined in Chapter 5, Exercise 10: whenever
`p₁ ≤ p₂` are prime ideals of `A` and `q` is a prime ideal of `B` with
`q ∩ A = p₂`, there is a prime ideal `q' ≤ q` of `B` with `q' ∩ A = p₁`.

The natural solution (`.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-5-11/proof.tex`)
argues as follows: if `q ⊆ B` contracts to `p ⊆ A`, then `A_p → B_q` is flat and local;
by Exercise 3.18 the induced map `Spec B_q → Spec A_p` is surjective; by Exercise 5.10 (ii)
(the implication (c') ⇒ (b')) the going-down property follows.

The formal counterpart of each step is:
* `flat_localization_localization` and `isLocalHom_localization_localization`: for a prime
  `q` of `B` with `p = q ∩ A`, the localization `A_p → B_q` is flat (Mathlib's instance
  `Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)`, which is
  `Module.Flat.trans` applied to the flatness of localizations) and local (`IsLocalHom`).
* `comap_surjective_localization_of_flat` is Exercise 3.18: for `A → B` flat, the map
  `Spec B_q → Spec A_p` is surjective.  Its proof uses that a flat local homomorphism of local
  rings is faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`) and that faithfully
  flat maps are surjective on prime spectra (`PrimeSpectrum.comap_surjective_of_faithfullyFlat`),
  which together are Exercises 3.16/3.18 of the book.
* `hasGoingDownProperty_of_comap_surjective` is Exercise 5.10 (ii) in unfolded form: condition
  (c') implies the going-down property.  (Mathlib's class-level version of the same criterion is
  `Algebra.HasGoingDown.of_comap_localRingHom_surjective`; the proof below is written out in
  terms of the unfolded statement.)
* `solution` combines them, `solution_algebra` records the conclusion in the form of Mathlib's
  `Algebra.HasGoingDown` class (using `hasGoingDownProperty_iff` to convert), and
  `solution_ringHom` states the exercise for an arbitrary ring homomorphism `f : A →+* B`, as in
  the book.  `solution_chain` records the conclusion of the going-down theorem (5.16) — the form
  in which Chapter 5, Exercise 10 defines "having the going-down property" — for a chain of
  primes, deduced from the single-step form.
-/
import Mathlib

open Ideal

namespace AtiyahMcdonald69.Ex_5_11

/-! ### The going-down property (Chapter 5, Exercise 10) -/

/-- A ring homomorphism `A → B` (encoded as an `A`-algebra structure on `B`) has the
**going-down property** if for every pair of prime ideals `p₁ ≤ p₂` of `A` and every prime
ideal `q` of `B` lying over `p₂`, there is a prime ideal `q' ≤ q` of `B` lying over `p₁`. -/
def HasGoingDownProperty (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (p₁ p₂ : Ideal A) [p₁.IsPrime] [p₂.IsPrime], p₁ ≤ p₂ →
    ∀ (q : Ideal B) [q.IsPrime], q.under A = p₂ →
      ∃ q' : Ideal B, q' ≤ q ∧ q'.IsPrime ∧ q'.under A = p₁

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- First step of the natural solution of Exercise 5.11: for a prime ideal `q` of `B` and
`p = q ∩ A`, the induced homomorphism `A_p → B_q` of localizations is flat. -/
theorem flat_localization_localization [Module.Flat A B] (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    Module.Flat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  inferInstance

/-- First step of the natural solution of Exercise 5.11: for a prime ideal `q` of `B` and
`p = q ∩ A`, the induced homomorphism `A_p → B_q` of localizations is local. -/
theorem isLocalHom_localization_localization (q : Ideal B) [q.IsPrime] :
    IsLocalHom (Localization.localRingHom (q.under A) q (algebraMap A B) rfl) :=
  Localization.isLocalHom_localRingHom (q.under A) q (algebraMap A B) Ideal.LiesOver.over

/-- **Atiyah–Macdonald, Exercise 3.18.**  If `A → B` is flat and `q` is a prime ideal of `B`
lying over `p = q ∩ A`, then the induced map `Spec B_q → Spec A_p` is surjective.

The induced map is `PrimeSpectrum.comap` of the localization `A_p → B_q` of the given
homomorphism. -/
theorem comap_surjective_localization_of_flat [Module.Flat A B]
    (q : Ideal B) [q.IsPrime] :
    Function.Surjective
      (PrimeSpectrum.comap (Localization.localRingHom (q.under A) q (algebraMap A B) rfl)) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  have hflat : Module.Flat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    flat_localization_localization q
  have hloc : IsLocalHom
      (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalHom_localization_localization q
  have : Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- **Atiyah–Macdonald, Exercise 5.10 (ii), (c') ⇒ (b').**  If for every prime ideal `q` of `B`
the localization map `Spec B_q → Spec A_{q ∩ A}` is surjective, then `A → B` has the
going-down property. -/
theorem hasGoingDownProperty_of_comap_surjective
    (H : ∀ (q : Ideal B) [q.IsPrime], Function.Surjective
      (PrimeSpectrum.comap (Localization.localRingHom (q.under A) q (algebraMap A B) rfl))) :
    HasGoingDownProperty A B := by
  intro p₁ p₂ hp₁ hp₂ hle q hq hqeq
  have : (q.under A).IsPrime := Ideal.IsPrime.under A q
  have hle' : p₁ ≤ q.under A := hqeq ▸ hle
  let pl : Ideal (Localization.AtPrime (q.under A)) := p₁.map (algebraMap A _)
  have hpl : pl.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime (q.under A) hle'
  obtain ⟨⟨Q, hQ⟩, hQl⟩ := H q ⟨pl, hpl⟩
  refine ⟨Q.under B, ?_, Ideal.IsPrime.under B Q, ?_⟩
  · calc Q.under B ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime q)).under B :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      _ = q := IsLocalization.AtPrime.under_maximalIdeal ..
  · let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    replace hQl : Q.under (Localization.AtPrime (q.under A)) = pl := by
      simpa [Ideal.under_def, PrimeSpectrum.ext_iff, RingHom.algebraMap_toAlgebra] using hQl
    rw [Ideal.under_under, ← Ideal.under_under (B := Localization.AtPrime (q.under A)) Q, hQl,
      Ideal.under_map_of_isLocalizationAtPrime (q.under A) hle']

/-- Chap. 5, Exercise 10 asks for the going-down property; this shows that our formulation is
the same as Mathlib's `Algebra.HasGoingDown` class. -/
theorem hasGoingDownProperty_iff :
    HasGoingDownProperty A B ↔ Algebra.HasGoingDown A B := by
  constructor
  · intro h
    refine { exists_ideal_le_liesOver_of_lt := ?_ }
    intro p hp q hq hlt
    obtain ⟨P, hPQ, hP, hPp⟩ := h p (q.under A) hlt.le q rfl
    exact ⟨P, hPQ, hP, ⟨hPp.symm⟩⟩
  · intro h p₁ p₂ hp₁ hp₂ hle q hq hqeq
    have hle' : p₁ ≤ q.under A := hqeq ▸ hle
    obtain ⟨P, hPQ, hP, hPover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := p₁) (q := q.under A) (Q := q) hle'
    exact ⟨P, hPQ, hP, hPover.over.symm⟩

/-- **Atiyah–Macdonald, Exercise 5.11.**  A flat ring homomorphism has the going-down
property.

(Mathlib also has this result, as the instance `Algebra.HasGoingDown.of_flat`.  The proof here
does not use it: it follows the book's own route through Exercise 3.18
(`comap_surjective_localization_of_flat`) and Exercise 5.10 (ii)
(`hasGoingDownProperty_of_comap_surjective`).) -/
theorem solution [Module.Flat A B] : HasGoingDownProperty A B :=
  hasGoingDownProperty_of_comap_surjective fun q _ => comap_surjective_localization_of_flat q

/-- Exercise 5.11, recorded in the form of Mathlib's `Algebra.HasGoingDown` class. -/
theorem solution_algebra [Module.Flat A B] : Algebra.HasGoingDown A B :=
  hasGoingDownProperty_iff.mp solution

section RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Atiyah–Macdonald, Exercise 5.11**, in the literal wording of the book: a flat ring
homomorphism `f : R →+* S` has the going-down property (`S` is flat as an `R`-module via `f`). -/
theorem solution_ringHom (f : R →+* S) (hflat : letI := f.toAlgebra; Module.Flat R S) :
    ∀ (p₁ p₂ : Ideal R) [p₁.IsPrime] [p₂.IsPrime], p₁ ≤ p₂ →
      ∀ (q : Ideal S) [q.IsPrime], q.comap f = p₂ →
        ∃ q' : Ideal S, q' ≤ q ∧ q'.IsPrime ∧ q'.comap f = p₁ :=
  letI := f.toAlgebra
  have hflat' : Module.Flat R S := hflat
  fun p₁ p₂ hp₁ hp₂ hle q hq hqeq => by
    have hqeq' : q.under R = p₂ := by
      simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra] using hqeq
    obtain ⟨q', hle', hprime, hunder⟩ :=
      solution (A := R) (B := S) p₁ p₂ hle q hqeq'
    exact ⟨q', hle', hprime, by
      simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra] using hunder⟩

end RingHom

/-- The conclusion of the going-down theorem (5.16) for flat homomorphisms, which is the form in
which Chapter 5, Exercise 10 defines "having the going-down property": every chain of prime
ideals of `A` lifts to a chain of prime ideals of `B` ending at a prescribed prime ideal over
the last element of the chain. -/
theorem solution_chain [Module.Flat A B] (l : LTSeries (PrimeSpectrum A))
    (q : Ideal B) [q.IsPrime] [q.LiesOver l.last.asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum B), L.length = l.length ∧
      L.last = ⟨q, ‹q.IsPrime›⟩ ∧
      List.map (PrimeSpectrum.comap (algebraMap A B)) L.toList = l.toList := by
  have := solution_algebra (A := A) (B := B)
  exact Ideal.exists_ltSeries_of_hasGoingDown l q

end AtiyahMcdonald69.Ex_5_11

#print axioms AtiyahMcdonald69.Ex_5_11.comap_surjective_localization_of_flat
#print axioms AtiyahMcdonald69.Ex_5_11.hasGoingDownProperty_of_comap_surjective
#print axioms AtiyahMcdonald69.Ex_5_11.hasGoingDownProperty_iff
#print axioms AtiyahMcdonald69.Ex_5_11.solution
#print axioms AtiyahMcdonald69.Ex_5_11.solution_algebra
#print axioms AtiyahMcdonald69.Ex_5_11.solution_ringHom
#print axioms AtiyahMcdonald69.Ex_5_11.solution_chain
