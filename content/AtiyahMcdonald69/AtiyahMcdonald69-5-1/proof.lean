/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), **Exercise 5.1**.

Book statement (Chapter 5, exercises, no. 1):

  "Let `f : A → B` be an integral homomorphism of rings. Show that
  `f* : Spec(B) → Spec(A)` is a closed mapping, i.e. that it maps closed sets to
  closed sets. (This is a geometrical equivalent of (5.10).)"

Dictionary used below:
* `A`, `B` commutative rings;
* an *integral* homomorphism is `f.IsIntegral`, i.e. every element of `B` is integral
  over `f(A)` (AM, §5, just before (5.1));
* `f*` is `PrimeSpectrum.comap f : PrimeSpectrum B → PrimeSpectrum A`;
* the closed sets of `Spec` are the zero loci `V(𝔞) = PrimeSpectrum.zeroLocus 𝔞`.

The main result is `solution`.  Following the book's proof we first show the identity
`f*(V(𝔞)) = V(f⁻¹𝔞)` (`image_zeroLocus_eq`), whose non-trivial half is exactly lying
over (`exists_mem_zeroLocus_comap_eq`, lying over) for the integral extension
`A/f⁻¹𝔞 ⊆ B/𝔞`.  As the parenthetical remark in the book suggests, we also formalize
the geometric form of the going-up theorem: a comap is a closed map **iff** it has the
going-up property (`isClosedMap_iff_hasGoingUp`), and consequently integral
homomorphisms satisfy going-up (`goingUp_of_isIntegral`, AM (5.11), for arbitrary
integral homomorphisms).

Finally, the last section records that the integrality hypothesis is not removable: for
the non-integral localization `ℚ[X] → ℚ[X, X⁻¹]` the induced map is not closed
(`integrality_hypothesis_necessary`).

Note: Mathlib already contains `PrimeSpectrum.isClosedMap_comap_of_isIntegral`.  We do
not use it; the proofs below follow the book's route through lying over, and neither the
equivalence with going-up nor the sharpness example is in Mathlib.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_1

open PrimeSpectrum Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-! ### The easy half: `f*(V(𝔞)) ⊆ V(f⁻¹𝔞)` (no integrality needed) -/

theorem image_zeroLocus_subset (f : A →+* B) (a : Ideal B) :
    comap f '' zeroLocus (a : Set B) ⊆ zeroLocus ((a.comap f : Ideal A) : Set A) := by
  rintro - ⟨q, hq, rfl⟩
  rw [mem_zeroLocus] at hq ⊢
  rw [comap_asIdeal]
  exact Ideal.comap_mono hq

/-! ### Lying over -/

/-- **Lying over**, in the form needed for the exercise: a prime `p` of `A` containing
the contraction of `𝔞` is the contraction of a prime of `B` containing `𝔞`.
(For `𝔞 = 0` this is lying over: the inclusion `A/f⁻¹𝔞 ⊆ B/𝔞` is integral, so every
prime of the subring lies below a prime of the big ring.) -/
theorem exists_mem_zeroLocus_comap_eq (f : A →+* B) (hf : f.IsIntegral) (a : Ideal B)
    {p : PrimeSpectrum A} (hp : p ∈ zeroLocus ((a.comap f : Ideal A) : Set A)) :
    ∃ q ∈ zeroLocus (a : Set B), comap f q = p := by
  rw [mem_zeroLocus] at hp
  algebraize [f]
  obtain ⟨Q, hQ, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (P := p.asIdeal) (I := a) hp
  refine ⟨⟨Q, hQprime⟩, ?_, ?_⟩
  · rw [mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr hQ
  · refine PrimeSpectrum.ext ?_
    rw [comap_asIdeal]
    exact hQcomap

/-- The reduction used in the book's solution: for an ideal `𝔞 ⊆ B`, the homomorphism
`A ⧸ f⁻¹𝔞 →+* B ⧸ 𝔞` induced by `f` is again integral (so that lying over may be
applied to it). -/
theorem isIntegral_quotientMap_comap (f : A →+* B) (hf : f.IsIntegral) (a : Ideal B) :
    (Ideal.quotientMap a f le_rfl).IsIntegral :=
  hf.quotient

/-! ### `f*(V(𝔞)) = V(f⁻¹𝔞)` -/

/-- The book's key identity: for an integral `f : A → B` and any ideal `𝔞 ⊆ B`, the image
of the closed set `V(𝔞)` under `f*` is the closed set `V(f⁻¹𝔞)`. -/
theorem image_zeroLocus_eq (f : A →+* B) (hf : f.IsIntegral) (a : Ideal B) :
    comap f '' zeroLocus (a : Set B) = zeroLocus ((a.comap f : Ideal A) : Set A) := by
  refine Set.Subset.antisymm (image_zeroLocus_subset f a) ?_
  intro p hp
  obtain ⟨q, hq, hqp⟩ := exists_mem_zeroLocus_comap_eq f hf a hp
  exact ⟨q, hq, hqp⟩

/-- **Atiyah–Macdonald, Exercise 5.1.**  An integral ring homomorphism `f : A → B`
induces a closed map `f* : Spec B → Spec A` on prime spectra. -/
theorem solution (f : A →+* B) (hf : f.IsIntegral) : IsClosedMap (comap f) := by
  intro Z hZ
  obtain ⟨a, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
  rw [image_zeroLocus_eq f hf a]
  exact isClosed_zeroLocus _

/-- Exercise 5.1 in ideal-theoretic form: the image of every `V(𝔞)` is a `V(J)`, namely
`V(f⁻¹𝔞)`. -/
theorem exists_ideal_image_eq (f : A →+* B) (hf : f.IsIntegral) (a : Ideal B) :
    ∃ J : Ideal A, comap f '' zeroLocus (a : Set B) = zeroLocus (J : Set A) :=
  ⟨a.comap f, image_zeroLocus_eq f hf a⟩

/-! ### The geometrical form of going-up

The going-up theorem (AM (5.11)) says: if `p₁ ⊆ p₂` are primes of `A` and `q₁` is a prime of `B`
with `q₁ ∩ A = p₁`, then there is a prime `q₂ ⊇ q₁` of `B` with `q₂ ∩ A = p₂`.
This is exactly the statement that for every `q` and every `p ⊇ f⁻¹q` there is `q' ⊇ q`
with `f⁻¹q' = p`, which in turn is exactly closedness of `f*`.  We prove this
equivalence for an arbitrary ring homomorphism; the exercise is the special case of an
integral homomorphism, where lying over (`exists_mem_zeroLocus_comap_eq`) provides the
primes needed to start the going-up.

Remark on the book's parenthetical: the equivalence we establish is with the going-up
property, i.e. with the going-up theorem (5.11).  In the integral case one further gets
going-up from the exercise, so the two statements are indeed equivalent there. -/

/-- The going-up property of a ring homomorphism `f : A → B`. -/
def HasGoingUp (f : A →+* B) : Prop :=
  ∀ (q : PrimeSpectrum B) (p : PrimeSpectrum A), comap f q ≤ p →
    ∃ q' : PrimeSpectrum B, q ≤ q' ∧ comap f q' = p

/-- Closedness of `f*` is equivalent to the going-up property. -/
theorem isClosedMap_iff_hasGoingUp (f : A →+* B) :
    IsClosedMap (comap f) ↔ HasGoingUp f := by
  constructor
  · -- closedness ⇒ going-up: enlarge `V(q)` and use that closed sets are
    -- stable under specialization.
    intro hf q p hqp
    have hZ : IsClosed (zeroLocus (q.asIdeal : Set B)) := isClosed_zeroLocus _
    have hq : q ∈ zeroLocus (q.asIdeal : Set B) := by
      rw [mem_zeroLocus]
    have hmem : comap f q ∈ comap f '' zeroLocus (q.asIdeal : Set B) := ⟨q, hq, rfl⟩
    have hspec : comap f q ⤳ p := (le_iff_specializes _ _).mp hqp
    obtain ⟨q', hq', hq'p⟩ := (hf _ hZ).stableUnderSpecialization hspec hmem
    exact ⟨q', (asIdeal_le_asIdeal _ _).mp (mem_zeroLocus _ _ |>.mp hq'), hq'p⟩
  · -- going-up ⇒ closedness: images of zero loci are stable under specialization.
    intro hf Z hZ
    obtain ⟨a, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
    refine (stableUnderSpecialization_image_iff f _ (isClosed_zeroLocus _)).mp ?_
    rintro _ y hxy ⟨q, hq, rfl⟩
    have hq' : a ≤ q.asIdeal := mem_zeroLocus _ _ |>.mp hq
    obtain ⟨q', hle, hcomap⟩ := hf q y ((le_iff_specializes _ _).mpr hxy)
    exact ⟨q', mem_zeroLocus _ _ |>.mpr (hq'.trans (asIdeal_le_asIdeal _ _ |>.mpr hle)), hcomap⟩

/-- **AM (5.11), going-up**, for an arbitrary integral homomorphism of rings: it is a
consequence of the closedness of `f*` (Exercise 5.1). -/
theorem goingUp_of_isIntegral (f : A →+* B) (hf : f.IsIntegral) : HasGoingUp f :=
  (isClosedMap_iff_hasGoingUp f).mp (solution f hf)

/-- **AM (5.11), going-up**, in the ideal-theoretic form in which the book states it:
given primes `p₁ ⊆ p₂` of `A` and a prime `q₁` of `B` lying over `p₁`, there is a prime
`q₂ ⊇ q₁` of `B` lying over `p₂`.  (`p₁` is automatically prime, being the contraction of
`q₁`; it is kept in the statement to match the book.) -/
theorem goingUp_ideal (f : A →+* B) (hf : f.IsIntegral)
    {p₁ p₂ : Ideal A} (_hp₁ : p₁.IsPrime) (hp₂ : p₂.IsPrime) (hpp : p₁ ≤ p₂)
    {q₁ : Ideal B} (hq₁ : q₁.IsPrime) (hover : q₁.comap f = p₁) :
    ∃ q₂ : Ideal B, q₁ ≤ q₂ ∧ q₂.IsPrime ∧ q₂.comap f = p₂ := by
  obtain ⟨q₂, hle, hcomap⟩ :=
    goingUp_of_isIntegral f hf ⟨q₁, hq₁⟩ ⟨p₂, hp₂⟩ (by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal, hover]
      exact hpp)
  exact ⟨q₂.asIdeal, (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle, q₂.2, by
    rw [← PrimeSpectrum.comap_asIdeal, hcomap]⟩

/-- Restatement of the exercise in the "algebra" language: for an integral algebra
`S` over `R`, the contraction map `Spec S → Spec R` is closed. -/
theorem solution_algebra {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsIntegral R S) : IsClosedMap (comap (algebraMap R S)) :=
  solution _ (Algebra.isIntegral_def.mp h)

/-! ### Sharpness: the integrality hypothesis cannot be dropped

`f* : Spec B → Spec A` need not be closed for a non-integral `f`.  The standard example is
the localization `ℚ[X] → ℚ[X, X⁻¹] = ℚ[X]_X`: its image is the basic open set `D(X)`,
which is not closed in `Spec ℚ[X]`.  We verify both halves — that this map is not integral
(so it is not covered by the exercise) and that its comap is not closed. -/

/-- The ring `ℚ[X, X⁻¹] = ℚ[X]_X`. -/
abbrev RatAwayX : Type := Localization.Away (Polynomial.X : ℚ[X])

theorem not_isIntegral_algebraMap_away : ¬ (algebraMap ℚ[X] RatAwayX).IsIntegral := by
  intro hf
  -- `RatAwayX` is integral over `ℚ[X]` under this assumption, so lying over applies to the
  -- prime `(X)`; but `X` is a unit in `RatAwayX`, so no prime can contain it.
  have hInt : Algebra.IsIntegral ℚ[X] RatAwayX := Algebra.isIntegral_def.mpr hf
  have hunit : IsUnit (algebraMap ℚ[X] RatAwayX (Polynomial.X : ℚ[X])) :=
    IsLocalization.map_units RatAwayX
      ⟨Polynomial.X, Submonoid.mem_powers (Polynomial.X : ℚ[X])⟩
  have hprime : (Ideal.span {(Polynomial.X : ℚ[X])}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X
  -- the kernel of the localization map is trivial, so it is contained in `(X)`
  have hM : Submonoid.powers (Polynomial.X : ℚ[X]) ≤ nonZeroDivisors ℚ[X] := by
    intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x (Polynomial.X : ℚ[X])).mp hx
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n Polynomial.X_ne_zero)
  have hIP : Ideal.comap (algebraMap ℚ[X] RatAwayX) ⊥ ≤ Ideal.span {(Polynomial.X : ℚ[X])} := by
    intro x hx
    have hx0 : algebraMap ℚ[X] RatAwayX x = 0 := hx
    have hx' : x = 0 :=
      (IsLocalization.to_map_eq_zero_iff (M := Submonoid.powers (Polynomial.X : ℚ[X]))
        (S := RatAwayX) hM).mp hx0
    rw [hx']
    exact Ideal.zero_mem _
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℚ[X]) (S := RatAwayX)
      (P := Ideal.span {(Polynomial.X : ℚ[X])}) (I := ⊥) hIP
  have hmem' : (Polynomial.X : ℚ[X]) ∈ Ideal.comap (algebraMap ℚ[X] RatAwayX) Q := by
    rw [hQcomap]
    exact Ideal.mem_span_singleton_self _
  exact hQprime.ne_top (Ideal.eq_top_of_isUnit_mem Q (Ideal.mem_comap.mp hmem') hunit)

theorem not_isClosedMap_algebraMap_away :
    ¬ IsClosedMap (PrimeSpectrum.comap (algebraMap ℚ[X] RatAwayX)) := by
  intro h
  -- the range of `comap` is `D(X)`, so `D(X)` would be closed; but `D(X)` contains the
  -- generic point `(0)` and not its specialization `(X)`, so it is not closed.
  have hclosed : IsClosed (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) :
      Set (PrimeSpectrum ℚ[X])) := by
    rw [← PrimeSpectrum.localization_away_comap_range RatAwayX (Polynomial.X : ℚ[X])]
    simpa using h Set.univ isClosed_univ
  have hprime : (Ideal.span {(Polynomial.X : ℚ[X])}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X
  let x : PrimeSpectrum ℚ[X] := ⟨⊥, inferInstance⟩
  let y : PrimeSpectrum ℚ[X] := ⟨Ideal.span {(Polynomial.X : ℚ[X])}, hprime⟩
  have hx : x ∈ (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) : Set (PrimeSpectrum ℚ[X])) := by
    simp [x]
  have hspec : x ⤳ y := by
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact bot_le
  have hy : y ∈ (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) : Set (PrimeSpectrum ℚ[X])) :=
    hclosed.stableUnderSpecialization hspec hx
  exact (hy : (Polynomial.X : ℚ[X]) ∉ y.asIdeal) (Ideal.subset_span rfl)

/-- The hypothesis of Exercise 5.1 is not removable: there is a ring homomorphism which is
not integral and whose induced map on prime spectra is not closed. -/
theorem integrality_hypothesis_necessary :
    ∃ f : ℚ[X] →+* RatAwayX, ¬ f.IsIntegral ∧ ¬ IsClosedMap (PrimeSpectrum.comap f) :=
  ⟨algebraMap ℚ[X] RatAwayX, not_isIntegral_algebraMap_away, not_isClosedMap_algebraMap_away⟩

end AtiyahMcdonald69.Ex_5_1

#print axioms AtiyahMcdonald69.Ex_5_1.solution
#print axioms AtiyahMcdonald69.Ex_5_1.image_zeroLocus_eq
#print axioms AtiyahMcdonald69.Ex_5_1.image_zeroLocus_subset
#print axioms AtiyahMcdonald69.Ex_5_1.exists_mem_zeroLocus_comap_eq
#print axioms AtiyahMcdonald69.Ex_5_1.isIntegral_quotientMap_comap
#print axioms AtiyahMcdonald69.Ex_5_1.exists_ideal_image_eq
#print axioms AtiyahMcdonald69.Ex_5_1.isClosedMap_iff_hasGoingUp
#print axioms AtiyahMcdonald69.Ex_5_1.goingUp_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_1.goingUp_ideal
#print axioms AtiyahMcdonald69.Ex_5_1.solution_algebra
#print axioms AtiyahMcdonald69.Ex_5_1.not_isIntegral_algebraMap_away
#print axioms AtiyahMcdonald69.Ex_5_1.not_isClosedMap_algebraMap_away
#print axioms AtiyahMcdonald69.Ex_5_1.integrality_hypothesis_necessary
