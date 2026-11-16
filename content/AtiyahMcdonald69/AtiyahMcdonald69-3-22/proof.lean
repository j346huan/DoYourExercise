/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 3, Exercise 22:

Let `A` be a ring and `p` a prime ideal of `A`. Then the canonical image of `Spec (A_p)` in
`Spec (A)` is equal to the intersection of all the open neighbourhoods of `p` in `Spec (A)`.

Formalization choices.  `A_p` is the actual localization `Localization.AtPrime p` of `A` at the
complement of `p`, the canonical ring homomorphism is `algebraMap A (Localization.AtPrime p)`, and
"canonical image" is the range of the induced map of prime spectra
`PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p)) : Spec (A_p) → Spec A`.

The proof follows the book's solution and is split into its two halves:

* `range_comap_algebraMap_eq_setOf_asIdeal_le`: the canonical image consists exactly of the
  primes `q` with `q ⊆ p`;
* `sInter_open_neighborhoods_eq_setOf_asIdeal_le`: the primes `q ⊆ p` are exactly the primes
  lying in every open neighbourhood of `p`.  Its two ingredients, mirroring the book's argument,
  are `mem_basicOpen_of_asIdeal_le` (a prime `q ⊆ p` lies in every basic neighbourhood
  `D(f) = basicOpen f` of `p`, since `f ∉ p` forces `f ∉ q`) and `exists_basicOpen_not_mem`
  (if `q ⊄ p`, some basic neighbourhood of `p` misses `q`), together with the fact that the
  basic open sets form a basis (`PrimeSpectrum.isTopologicalBasis_basic_opens`).

The last section computes two standard concrete instances: a domain localized at the zero ideal
(image: the generic point) and `ℤ` localized at `(2)` (image: exactly `{(0), (2)}`).

Audit notes.
* The hypothesis that `p` is prime is not removable: `p` has to be a point of `Spec A` for the
  statement to be formulable, and `Localization.AtPrime` is the localization at a prime ideal.
  For a general multiplicatively closed subset `S ⊆ A` the analogous statement is
  `PrimeSpectrum.localization_comap_range`, which says that the canonical image of `Spec(S⁻¹A)`
  is `{q | q ∩ S = ∅} = Spec A \ V(S)`; the present exercise is the case `S = A \ p`, where
  `{q | q ∩ (A \ p) = ∅} = {q | q ⊆ p}`.
* "Neighbourhood" is read as "open neighbourhood", as in the book's solution, which uses the basic
  open neighbourhoods `D(f)`; `sInter_nhds_eq_setOf_asIdeal_le` shows that using all
  neighbourhoods (the filter `nhds p`) gives the same intersection.
-/

import Mathlib

set_option autoImplicit false

namespace AtiyahMcdonald69.Ex_3_22

open PrimeSpectrum

variable {A : Type*} [CommRing A]

/-! ### The primes of `A_p` viewed in `Spec A` -/

/-- The first half of Exercise 3.22: the canonical image of `Spec (A_p)` in `Spec (A)` consists of
the prime ideals `q` contained in `p`. -/
theorem range_comap_algebraMap_eq_setOf_asIdeal_le (p : Ideal A) [hp : p.IsPrime] :
    (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) :
        Set (PrimeSpectrum A)) = {q : PrimeSpectrum A | q.asIdeal ≤ p} := by
  rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p) p.primeCompl]
  refine Set.ext fun q => ?_
  constructor
  · intro h a ha
    by_contra hcon
    have hmem : a ∈ (p.primeCompl : Set A) := by simpa using hcon
    exact (Set.disjoint_left.mp h hmem) ha
  · intro h
    exact Set.disjoint_left.mpr fun a ha hqa => (by simpa using ha : a ∉ p) (h hqa)

/-! ### The basic neighbourhoods `D(f)` of `p` -/

/-- Every basic neighbourhood `D(f)` of `p`, i.e. every `f ∉ p`, contains all primes `q ⊆ p`. -/
theorem mem_basicOpen_of_asIdeal_le (p : Ideal A) [p.IsPrime] {q : PrimeSpectrum A}
    (hq : q.asIdeal ≤ p) {f : A} (hf : f ∉ p) :
    q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
  have hfq : f ∉ q.asIdeal := fun hfq => hf (hq hfq)
  simpa using hfq

/-- If `q ⊄ p`, there is a basic neighbourhood `D(f)` of `p` which does not contain `q`:
take `f ∈ q \ p`. -/
theorem exists_basicOpen_not_mem (p : Ideal A) [p.IsPrime] {q : PrimeSpectrum A}
    (hq : ¬ q.asIdeal ≤ p) :
    ∃ f : A, f ∉ p ∧ q ∉ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
  obtain ⟨f, hfq, hfp⟩ := Set.not_subset.mp hq
  exact ⟨f, hfp, by simpa using hfq⟩

/-- The book's computation, step 1: lying in every open neighbourhood of `p` is the same as
lying in every basic neighbourhood `D(f) = basicOpen f` with `f ∉ p`, because the basic opens form
a basis of the Zariski topology. -/
theorem forall_open_iff_forall_basicOpen (p : Ideal A) [hp : p.IsPrime] (q : PrimeSpectrum A) :
    (∀ U : Set (PrimeSpectrum A), IsOpen U → (⟨p, hp⟩ : PrimeSpectrum A) ∈ U → q ∈ U) ↔
      ∀ f : A, f ∉ p → q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
  constructor
  · intro h f hf
    exact h _ PrimeSpectrum.isOpen_basicOpen (by simpa using hf)
  · intro h U hU hpU
    obtain ⟨V, ⟨g, rfl⟩, hVp, hVU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    exact hVU (h g (by simpa using hVp))

/-- The book's computation, step 2: `⋂_{f ∉ p} D(f) = {q | q ⊆ p}`, since `f ∉ p → f ∉ q` for
every `f ∉ p` if and only if every element of `q` lies in `p`. -/
theorem forall_basicOpen_iff_asIdeal_le (p : Ideal A) [p.IsPrime] (q : PrimeSpectrum A) :
    (∀ f : A, f ∉ p → q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))) ↔
      q.asIdeal ≤ p := by
  constructor
  · intro h a ha
    by_contra hcon
    have ha' : a ∉ q.asIdeal := by simpa using h a hcon
    exact ha' ha
  · intro h f hf
    have hfq : f ∉ q.asIdeal := fun hfq => hf (h hfq)
    simpa using hfq

/-! ### The intersection of the open neighbourhoods of `p` -/

/-- The second half of Exercise 3.22: the primes contained in `p` are exactly the primes lying in
every open neighbourhood of `p`. -/
theorem sInter_open_neighborhoods_eq_setOf_asIdeal_le (p : Ideal A) [hp : p.IsPrime] :
    (⋂₀ {U : Set (PrimeSpectrum A) |
        IsOpen U ∧ (⟨p, hp⟩ : PrimeSpectrum A) ∈ U}) = {q : PrimeSpectrum A | q.asIdeal ≤ p} := by
  refine Set.ext fun q => ?_
  constructor
  · -- `q` lies in every basic neighbourhood `D(f)` of `p`, for `f ∉ p`; hence `q ⊆ p`.
    intro hq
    by_contra hqp
    obtain ⟨f, hfp, hfq⟩ := exists_basicOpen_not_mem p hqp
    exact hfq ((Set.mem_sInter.mp hq) _ ⟨PrimeSpectrum.isOpen_basicOpen, by simpa using hfp⟩)
  · -- every open neighbourhood of `p` contains a basic neighbourhood `D(f)` of `p`.
    intro hq U hU
    obtain ⟨V, ⟨f, rfl⟩, hVp, hVU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hU.2 hU.1
    exact hVU (mem_basicOpen_of_asIdeal_le p hq (by simpa using hVp))

/-! ### The exercise -/

/-- Atiyah–Macdonald, Chapter 3, Exercise 22: the canonical image of `Spec (A_p)` in `Spec (A)` is
the intersection of all the open neighbourhoods of `p`. -/
theorem solution (p : Ideal A) [hp : p.IsPrime] :
    (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) :
        Set (PrimeSpectrum A))
      = ⋂₀ {U : Set (PrimeSpectrum A) |
          IsOpen U ∧ (⟨p, hp⟩ : PrimeSpectrum A) ∈ U} := by
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le,
    sInter_open_neighborhoods_eq_setOf_asIdeal_le]

/-! ### Equivalent forms and consequences -/

/-- Membership form of the first half: a prime `q` is in the canonical image of `Spec (A_p)` if and
only if `q ⊆ p`. -/
theorem mem_range_iff_asIdeal_le (p : Ideal A) [hp : p.IsPrime] (q : PrimeSpectrum A) :
    q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) ↔
      q.asIdeal ≤ p := by
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le]
  rfl

/-- Membership form of the exercise: a prime `q` is in the canonical image of `Spec (A_p)` if and
only if it belongs to every open neighbourhood of `p`. -/
theorem mem_range_iff_forall_isOpen (p : Ideal A) [hp : p.IsPrime] (q : PrimeSpectrum A) :
    q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) ↔
      ∀ U : Set (PrimeSpectrum A), IsOpen U → (⟨p, hp⟩ : PrimeSpectrum A) ∈ U → q ∈ U := by
  rw [mem_range_iff_asIdeal_le]
  show q ∈ {r : PrimeSpectrum A | r.asIdeal ≤ p} ↔ _
  rw [← sInter_open_neighborhoods_eq_setOf_asIdeal_le (p := p), Set.mem_sInter]
  exact ⟨fun h U hU hpU => h U ⟨hU, hpU⟩, fun h U hU => h U hU.1 hU.2⟩

/-- The same with neighbourhoods in the sense of the neighbourhood filter `nhds p` (which need not
be open): every neighbourhood of `p` contains an open neighbourhood of `p`. -/
theorem sInter_nhds_eq_setOf_asIdeal_le (p : Ideal A) [hp : p.IsPrime] :
    (⋂₀ {U : Set (PrimeSpectrum A) |
        U ∈ nhds (⟨p, hp⟩ : PrimeSpectrum A)}) = {q : PrimeSpectrum A | q.asIdeal ≤ p} := by
  refine Set.ext fun q => ?_
  have h₁ : q ∈ (⋂₀ {U : Set (PrimeSpectrum A) | U ∈ nhds (⟨p, hp⟩ : PrimeSpectrum A)}) ↔
      ∀ U : Set (PrimeSpectrum A), U ∈ nhds (⟨p, hp⟩ : PrimeSpectrum A) → q ∈ U := by
    rw [Set.mem_sInter]
    exact Iff.rfl
  have h₂ : (∀ U : Set (PrimeSpectrum A), U ∈ nhds (⟨p, hp⟩ : PrimeSpectrum A) → q ∈ U) ↔
      ∀ U : Set (PrimeSpectrum A), IsOpen U → (⟨p, hp⟩ : PrimeSpectrum A) ∈ U → q ∈ U := by
    constructor
    · intro h U hU1 hU2
      exact h U (hU1.mem_nhds hU2)
    · intro h U hU
      obtain ⟨V, hVU, hVopen, hVpt⟩ := mem_nhds_iff.mp hU
      exact hVU (h V hVopen hVpt)
  exact h₁.trans (h₂.trans
    ((mem_range_iff_forall_isOpen p q).symm.trans (mem_range_iff_asIdeal_le p q)))

/-- The image consists exactly of the primes specializing to `p` (the points `q` whose closure
contains `p`). -/
theorem mem_range_iff_specializes (p : Ideal A) [hp : p.IsPrime] (q : PrimeSpectrum A) :
    q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) ↔
      q ⤳ (⟨p, hp⟩ : PrimeSpectrum A) := by
  rw [mem_range_iff_forall_isOpen, specializes_iff_forall_open]

/-- Order-theoretic form: the image is the down-set of `p` in the specialization order. -/
theorem range_comap_eq_Iic (p : Ideal A) [hp : p.IsPrime] :
    (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) :
        Set (PrimeSpectrum A)) = Set.Iic (⟨p, hp⟩ : PrimeSpectrum A) := by
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le]
  exact Set.ext fun q => PrimeSpectrum.asIdeal_le_asIdeal q ⟨p, hp⟩

/-- The image is stable under generalization: if `q` is in the image, so is every `q' ≤ q`. -/
theorem range_stable_under_generalization (p : Ideal A) [hp : p.IsPrime]
    {q q' : PrimeSpectrum A}
    (hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))))
    (h : q' ≤ q) : q' ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) := by
  rw [mem_range_iff_asIdeal_le] at hq ⊢
  exact le_trans (show q'.asIdeal ≤ q.asIdeal from h) hq

/-- The point `p` itself always lies in the canonical image (`p ⊆ p`); concretely, some prime ideal
of the localization `A_p` (namely the maximal ideal of the local ring `A_p`) contracts to `p`.
Hence the intersection of the open neighbourhoods of `p` is nonempty. -/
theorem mem_range_self (p : Ideal A) [hp : p.IsPrime] :
    (⟨p, hp⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) := by
  rw [mem_range_iff_asIdeal_le]

/-- In a domain, the generic point `(0)` of `Spec A` lies in the image of `Spec (A_p)` for every
prime `p` (`0 ⊆ p`). -/
theorem bot_mem_range [IsDomain A] (p : Ideal A) [hp : p.IsPrime] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime p))) := by
  rw [mem_range_iff_asIdeal_le]
  exact bot_le

/-- Concretely: localizing a domain `A` at the zero ideal, the canonical image in `Spec A` consists
of the single generic point `(0)`. -/
theorem range_comap_bot_eq_singleton [IsDomain A] :
    (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime (⊥ : Ideal A)))) :
        Set (PrimeSpectrum A)) = {⟨⊥, Ideal.isPrime_bot⟩} := by
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le]
  refine Set.ext fun q => ?_
  rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact PrimeSpectrum.ext (le_bot_iff.mp h)
  · intro h
    subst h
    exact le_rfl

/-! ### A concrete computation: `A = ℤ` and `p = (2)` -/

/-- `(2)` is a prime ideal of `ℤ`. -/
instance intTwoPrime : (Ideal.span {(2 : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

/-- In `ℤ`, a prime ideal contained in `(2)` is either `(0)` or `(2)` itself: `ℤ` is a principal
ideal domain, so a nonzero prime ideal is maximal. -/
theorem int_prime_le_span_two (q : Ideal ℤ) [hq : q.IsPrime] (h : q ≤ Ideal.span {(2 : ℤ)}) :
    q = ⊥ ∨ q = Ideal.span {(2 : ℤ)} := by
  by_cases hbot : q = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hmax : q.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hne : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
      intro htop
      rw [Ideal.span_singleton_eq_top] at htop
      exact (by omega : ¬ (2 : ℤ) ∣ 1) (isUnit_iff_dvd_one.mp htop)
    exact hmax.eq_of_le hne h

/-- Concretely: for `A = ℤ` and `p = (2)`, the canonical image of `Spec (ℤ_(2))` in `Spec ℤ`
consists of exactly the two points `(0)` and `(2)`. -/
theorem range_comap_int_span_two :
    (Set.range (PrimeSpectrum.comap
        (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)})))) : Set (PrimeSpectrum ℤ))
      = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ),
          ⟨Ideal.span {(2 : ℤ)}, Ideal.isPrime_span_singleton_of_prime Int.prime_two⟩} := by
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le]
  refine Set.ext fun q => ?_
  rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases int_prime_le_span_two q.asIdeal h with hq | hq
    · exact Or.inl (PrimeSpectrum.ext hq)
    · exact Or.inr (PrimeSpectrum.ext hq)
  · rintro (h | h)
    · subst h
      exact bot_le
    · subst h
      exact le_rfl

/-- Concretely: in `Spec ℤ`, the intersection of all open neighbourhoods of `(2)` is exactly
`{(0), (2)}`. -/
theorem sInter_int_span_two :
    (⋂₀ {U : Set (PrimeSpectrum ℤ) | IsOpen U ∧
        (⟨Ideal.span {(2 : ℤ)},
          Ideal.isPrime_span_singleton_of_prime Int.prime_two⟩ : PrimeSpectrum ℤ) ∈ U})
      = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ),
          ⟨Ideal.span {(2 : ℤ)}, Ideal.isPrime_span_singleton_of_prime Int.prime_two⟩} := by
  have h := range_comap_int_span_two
  rw [range_comap_algebraMap_eq_setOf_asIdeal_le] at h
  rw [sInter_open_neighborhoods_eq_setOf_asIdeal_le]
  exact h

end AtiyahMcdonald69.Ex_3_22

#print axioms AtiyahMcdonald69.Ex_3_22.solution
#print axioms AtiyahMcdonald69.Ex_3_22.range_comap_algebraMap_eq_setOf_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.sInter_open_neighborhoods_eq_setOf_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.mem_basicOpen_of_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.exists_basicOpen_not_mem
#print axioms AtiyahMcdonald69.Ex_3_22.mem_range_iff_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.mem_range_iff_forall_isOpen
#print axioms AtiyahMcdonald69.Ex_3_22.sInter_nhds_eq_setOf_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.forall_open_iff_forall_basicOpen
#print axioms AtiyahMcdonald69.Ex_3_22.forall_basicOpen_iff_asIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_22.mem_range_iff_specializes
#print axioms AtiyahMcdonald69.Ex_3_22.range_comap_eq_Iic
#print axioms AtiyahMcdonald69.Ex_3_22.range_stable_under_generalization
#print axioms AtiyahMcdonald69.Ex_3_22.mem_range_self
#print axioms AtiyahMcdonald69.Ex_3_22.bot_mem_range
#print axioms AtiyahMcdonald69.Ex_3_22.range_comap_bot_eq_singleton
#print axioms AtiyahMcdonald69.Ex_3_22.int_prime_le_span_two
#print axioms AtiyahMcdonald69.Ex_3_22.range_comap_int_span_two
#print axioms AtiyahMcdonald69.Ex_3_22.sInter_int_span_two
