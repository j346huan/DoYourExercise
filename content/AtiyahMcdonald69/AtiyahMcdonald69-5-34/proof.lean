/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 5 (Integral Dependence and Valuations), Exercise 34:

  Let `A` be a valuation ring and `K` its field of fractions. Let `f : A → B` be a ring
  homomorphism such that `f^* : Spec B → Spec A` is a closed mapping. Then if `g : B → K`
  is any `A`-algebra homomorphism (i.e. if `g ∘ f` is the embedding of `A` in `K`) we have
  `g(B) = A`.

Source of the statement: the text of the original scan
(`.scratch/reference/atiyah-macdonald-original.txt`, Chapter 5 exercises, item 34).

Natural-language solution (advisory):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-34

The natural-language solution restricts the closedness hypothesis to the subring
`C = g(B) ⊆ K` (a quotient of `B`), observes that the closed point `{n}` of `Spec C`
corresponding to a maximal ideal `n` must map to a closed point, i.e. that `n ∩ A` is the
maximal ideal of `A`, and then concludes with Exercise 5.27 (a valuation ring is maximal
with respect to domination).

Below we make the same reduction but replace the appeal to 5.27 by a direct argument: an
element `a` of `A` whose image in `K` is `x⁻¹` for some `x ∈ C`, `x ∉ A`, is a non-unit,
hence lies in the maximal ideal of `A`, hence in the contraction `n ∩ A` of `n`; but then
`α a ∈ n` is a unit of `C` (it is the inverse of `x ∈ C`), which is impossible.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_34

open PrimeSpectrum

/-! ### Two generalities about spectra of rings -/

/-- If `PrimeSpectrum.comap φ` is a closed map, then it sends closed points to closed
points: the contraction of a maximal ideal along `φ` is maximal. -/
theorem isMaximal_comap_of_isClosedMap {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : IsClosedMap (PrimeSpectrum.comap φ)) {n : Ideal S}
    (hn : n.IsMaximal) : (n.comap φ).IsMaximal := by
  classical
  have hclosed : IsClosed (PrimeSpectrum.comap φ '' ({⟨n, hn.isPrime⟩} : Set (PrimeSpectrum S))) :=
    hφ _ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hn)
  rw [Set.image_singleton] at hclosed
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed

/-- For a surjective ring hom `ψ`, the map `Spec T → Spec S` is a closed embedding, hence a
closed map. Consequently `φ^*` closed implies `(ψ ∘ φ)^*` closed. -/
theorem isClosedMap_comap_comp_of_surjective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (φ : R →+* S) (ψ : S →+* T) (hψ : Function.Surjective ψ)
    (hφ : IsClosedMap (PrimeSpectrum.comap φ)) :
    IsClosedMap (PrimeSpectrum.comap (ψ.comp φ)) := by
  rw [PrimeSpectrum.comap_comp]
  exact hφ.comp
    (Topology.IsClosedEmbedding.isClosedMap
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective T ψ hψ))

/-- `x` lies in the image of `R` in `S` iff `x` is "integral" over `R` in the sense of
`IsLocalization.IsInteger`. -/
theorem isInteger_iff_mem_range {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (x : S) : IsLocalization.IsInteger R x ↔ x ∈ Set.range (algebraMap R S) :=
  RingHom.mem_rangeS

/-! ### The key step

Let `A` be a valuation ring with field of fractions `K`, and let `C ⊆ K` be a subring
containing the image of `A`. If `Spec C → Spec A` is a closed map, then `C ⊆ A`.
Equivalently: no subring of `K` strictly bigger than a valuation ring `A` has a closed
contraction map to `Spec A`. -/

theorem subring_subset_of_isClosedMap (A K : Type*) [CommRing A] [IsDomain A]
    [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (C : Subring K) (hAC : ∀ a : A, algebraMap A K a ∈ C)
    (hclosed : IsClosedMap (PrimeSpectrum.comap ((algebraMap A K).codRestrict C hAC))) :
    (C : Set K) ⊆ Set.range (algebraMap A K) := by
  classical
  intro x hx
  by_cases hxA : x ∈ Set.range (algebraMap A K)
  · exact hxA
  exfalso
  -- `x ≠ 0`, since `0` is in the image of `A`.
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxA ⟨0, (algebraMap A K).map_zero⟩
  -- a maximal ideal of `C`; its contraction to `A` is the maximal ideal of `A`
  obtain ⟨n, hn, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal C) bot_ne_top
  have hmax : (n.comap ((algebraMap A K).codRestrict C hAC)).IsMaximal :=
    isMaximal_comap_of_isClosedMap _ hclosed hn
  have hcomap : n.comap ((algebraMap A K).codRestrict C hAC) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hmax
  -- by the valuation dichotomy, either `x` or `x⁻¹` is in `A`; the first case is excluded
  have hxinv : ∃ a : A, algebraMap A K a = x⁻¹ := by
    rcases ValuationRing.isInteger_or_isInteger (R := A) (K := K) x with h | h
    · exact absurd ((isInteger_iff_mem_range x).mp h) hxA
    · exact (isInteger_iff_mem_range x⁻¹).mp h
  obtain ⟨a, ha⟩ := hxinv
  -- such an `a` cannot be a unit of `A`, since then `x` would be in the image of `A`
  have hnonunit : ¬ IsUnit a := by
    rintro ⟨u, rfl⟩
    apply hxA
    refine ⟨↑(u⁻¹), ?_⟩
    have key : algebraMap A K (↑(u⁻¹) : A) * x⁻¹ = 1 := by
      rw [← ha, ← map_mul, Units.inv_mul, map_one]
    have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    exact mul_right_cancel₀ (inv_ne_zero hx0) (key.trans h1.symm)
  -- hence `a` lies in the maximal ideal of `A`, i.e. in `n ∩ A`
  have hamem : a ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnonunit
  have hαa : (algebraMap A K).codRestrict C hAC a ∈ n := by
    have hmem : a ∈ n.comap ((algebraMap A K).codRestrict C hAC) := hcomap.symm ▸ hamem
    exact hmem
  -- but `α a = x⁻¹` is a unit of `C`, as `x ∈ C`
  have hunit : IsUnit ((algebraMap A K).codRestrict C hAC a) := by
    refine isUnit_iff_exists.mpr ⟨⟨x, hx⟩, ?_, ?_⟩
    · exact Subtype.ext (by
        show algebraMap A K a * x = 1
        rw [ha, inv_mul_cancel₀ hx0])
    · exact Subtype.ext (by
        show x * algebraMap A K a = 1
        rw [ha, mul_inv_cancel₀ hx0])
  exact hn.ne_top (Ideal.eq_top_of_isUnit_mem n hαa hunit)

/-! ### Exercise 5.34 -/

/-- **Atiyah–Macdonald, Exercise 5.34.** Let `A` be a valuation ring, `K` its field of
fractions, `f : A →+* B` a ring homomorphism whose induced map
`Spec B → Spec A` is closed, and `g : B →+* K` an `A`-algebra homomorphism
(`g ∘ f = algebraMap A K`). Then `g(B) = A` as subsets of `K`. -/
theorem solution {A K B : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [CommRing B]
    (f : A →+* B) (g : B →+* K) (hg : g.comp f = algebraMap A K)
    (hf : IsClosedMap (PrimeSpectrum.comap f)) :
    Set.range g = Set.range (algebraMap A K) := by
  classical
  -- `C = g(B) ⊆ K` is a subring, and it contains the image of `A` because `g ∘ f = algebraMap`
  have hAC : ∀ a : A, algebraMap A K a ∈ g.range := fun a =>
    ⟨f a, RingHom.congr_fun hg a⟩
  -- `g` factorizes through a surjection `g' : B →+* C`, so that `α = g' ∘ f` is the
  -- corestriction of `algebraMap A K`, and `Spec C → Spec A` is a closed map
  set g' : B →+* g.range := g.codRestrict g.range (fun b => RingHom.mem_range_self g b)
  have hg'surj : Function.Surjective g' := by
    intro y
    obtain ⟨b, hb⟩ := y.2
    exact ⟨b, Subtype.ext hb⟩
  have hα : ((algebraMap A K).codRestrict g.range hAC) = g'.comp f :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun hg a).symm
  have hclosed : IsClosedMap (PrimeSpectrum.comap ((algebraMap A K).codRestrict g.range hAC)) := by
    rw [hα]
    exact isClosedMap_comap_comp_of_surjective f g' hg'surj hf
  refine Set.Subset.antisymm ?_ ?_
  · -- `g(B) ⊆ A` is the substance of the exercise
    rintro x ⟨b, rfl⟩
    exact subring_subset_of_isClosedMap A K g.range hAC hclosed (RingHom.mem_range_self g b)
  · -- `A ⊆ g(B)`, because `g ∘ f` is the embedding of `A` in `K`
    rintro x ⟨a, rfl⟩
    exact ⟨f a, RingHom.congr_fun hg a⟩

/-- Exercise 5.34 in the `A`-algebra form of the book's parenthetical: if `B` is an
`A`-algebra, `f` is its structure map `algebraMap A B` and `g : B →ₐ[A] K` is an
`A`-algebra homomorphism, then `g(B) = A`. (The main form `solution` assumes only
`g ∘ f = algebraMap A K`, which is the weaker and equivalent condition on `g`.) -/
theorem solution_algHom {A K B : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [CommRing B] [Algebra A B]
    (hf : IsClosedMap (PrimeSpectrum.comap (algebraMap A B))) (g : B →ₐ[A] K) :
    Set.range g = Set.range (algebraMap A K) := by
  simpa using solution (algebraMap A B) (g : B →+* K) (by ext a; exact g.commutes a) hf

/-- Exercise 5.34, first half, in elementwise form: every value of `g` is the image of an
element of `A`. -/
theorem solution_image {A K B : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [CommRing B]
    (f : A →+* B) (g : B →+* K) (hg : g.comp f = algebraMap A K)
    (hf : IsClosedMap (PrimeSpectrum.comap f)) (b : B) :
    ∃ a : A, g b = algebraMap A K a := by
  have h := Set.ext_iff.mp (solution f g hg hf) (g b)
  simpa only [Set.mem_range, eq_comm] using h.mp ⟨b, rfl⟩

/-- Exercise 5.34, second half, in elementwise form: every element of `A` is a value of
`g`. -/
theorem solution_surjective {A K B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B]
    (f : A →+* B) (g : B →+* K) (hg : g.comp f = algebraMap A K)
    (hf : IsClosedMap (PrimeSpectrum.comap f)) (a : A) :
    ∃ b : B, g b = algebraMap A K a :=
  Set.ext_iff.mp (solution f g hg hf) (algebraMap A K a) |>.mpr ⟨a, rfl⟩

end AtiyahMcdonald69.Ex_5_34

/-! ### Non-vacuity check

The hypotheses of the exercise are jointly satisfiable: taking `A = K = B = ℚ` (a field is a
valuation ring and is its own field of fractions), `f = g = id`, both hypotheses hold and the
conclusion `g(B) = A` is true. This is recorded here so that `solution` is manifestly not a
vacuous statement. -/

example : Set.range (RingHom.id ℚ) = Set.range (algebraMap ℚ ℚ) :=
  AtiyahMcdonald69.Ex_5_34.solution (RingHom.id ℚ) (RingHom.id ℚ) (by ext; simp) IsClosedMap.id

#print axioms AtiyahMcdonald69.Ex_5_34.solution
#print axioms AtiyahMcdonald69.Ex_5_34.solution_algHom
#print axioms AtiyahMcdonald69.Ex_5_34.solution_image
#print axioms AtiyahMcdonald69.Ex_5_34.solution_surjective
#print axioms AtiyahMcdonald69.Ex_5_34.isMaximal_comap_of_isClosedMap
#print axioms AtiyahMcdonald69.Ex_5_34.subring_subset_of_isClosedMap
