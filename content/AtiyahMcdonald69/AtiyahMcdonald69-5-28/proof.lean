import Mathlib

/-!
# Atiyah–Macdonald, Exercise 5.28

Statement (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 5, Exercise 28):

Let `A` be an integral domain and `K` its field of fractions.  Then the following are
equivalent:

1. `A` is a valuation ring of `K`;
2. any two ideals `𝔞`, `𝔟` of `A` satisfy `𝔞 ⊆ 𝔟` or `𝔟 ⊆ 𝔞`.

Deduce that, for a prime ideal `𝔭` of a valuation ring `A`, both `A_𝔭` and `A ⧸ 𝔭` are
valuation rings of their fields of fractions.

Formalization notes:

* The book's definition of a valuation ring of a field, "for each `x ≠ 0`, either `x ∈ A` or
  `x⁻¹ ∈ A`", is recorded as `IsValuationRingOf A K`; membership in the subring `A` of `K`
  is expressed through `algebraMap A K`, with `IsFractionRing A K` supplying that `K` is the
  field of fractions of `A`.
* The ideal condition is `∀ I J : Ideal A, I ≤ J ∨ J ≤ I` (`≤` on ideals is inclusion).
* The quotient `A / 𝔭` is `A ⧸ 𝔭` and the localization `A_𝔭` is `Localization.AtPrime 𝔭`.  Since
  `A ⊆ A_𝔭 ⊆ K = Frac A`, the field of fractions of `A_𝔭` is canonically the field of fractions
  of `A`; this is the content of the instance
  `IsFractionRing (Localization.AtPrime p) (FractionRing A)`, and it is why the localization
  statement can be phrased with the fraction field `FractionRing A` of `A`.  The inclusion
  `A_𝔭 ⊆ K` itself is recorded as the (canonical) algebra structure `atPrimeAlgebra`, and the
  main theorem states the localization conclusion directly in terms of the given field of
  fractions `K`, exactly as in the book.  For the quotient, `A ⧸ 𝔭` is an integral domain and
  `FractionRing (A ⧸ 𝔭)` is its field of fractions.

Every result is proved here from Mathlib's API; nothing depends on `sorryAx`.
-/

set_option autoImplicit false

namespace AtiyahMcdonald69.Ex_5_28

/-- `A` is a valuation ring of the field `K` in the sense of Atiyah–Macdonald (Chapter 5,
just before Proposition 5.18): every nonzero element of `K`, or its inverse, lies in `A`. -/
def IsValuationRingOf (A : Type*) (K : Type*) [CommRing A] [Field K] [Algebra A K] : Prop :=
  ∀ x : K, x ≠ 0 → (∃ a : A, algebraMap A K a = x) ∨ (∃ a : A, algebraMap A K a = x⁻¹)

variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- The book's definition of a valuation ring of `K` agrees with the intrinsic notion
`ValuationRing A` (every two elements of `A` are comparable for divisibility). -/
theorem isValuationRingOf_iff_valuationRing :
    IsValuationRingOf A K ↔ ValuationRing A := by
  constructor
  · rintro h
    suffices PreValuationRing A from .mk
    refine ⟨fun a b => ?_⟩
    by_cases ha : a = 0
    · exact ⟨0, Or.inr (by simp [ha])⟩
    by_cases hb : b = 0
    · exact ⟨0, Or.inl (by simp [hb])⟩
    have hinj := IsFractionRing.injective A K
    have ha' : algebraMap A K a ≠ 0 := by simpa using ha
    have hb' : algebraMap A K b ≠ 0 := by simpa using hb
    obtain ⟨c, hc⟩ | ⟨c, hc⟩ :=
      h (algebraMap A K a / algebraMap A K b) (div_ne_zero ha' hb')
    · -- `a / b = c`, hence `b * c = a`
      refine ⟨c, Or.inr (hinj ?_)⟩
      rw [map_mul, hc, mul_div_cancel₀ (algebraMap A K a) hb']
    · -- `(a / b)⁻¹ = c`, hence `a * c = b`
      refine ⟨c, Or.inl (hinj ?_)⟩
      rw [map_mul, hc, inv_div]
      exact mul_div_cancel₀ (algebraMap A K b) ha'
  · rintro h x hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx (by simp)
    have ha' : algebraMap A K a ≠ 0 := by simpa using ha0
    have hb' : algebraMap A K b ≠ 0 := by simpa using hb0
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · -- `a * c = b`, so `x = 1 / c` and `x⁻¹ = c`
      refine Or.inr ⟨c, ?_⟩
      have key : algebraMap A K b = algebraMap A K a * algebraMap A K c := by
        rw [← hc, map_mul]
      rw [key, inv_div]
      exact (mul_div_cancel_left₀ (algebraMap A K c) ha').symm
    · -- `b * c = a`, so `x = c`
      refine Or.inl ⟨c, ?_⟩
      have key : algebraMap A K a = algebraMap A K b * algebraMap A K c := by
        rw [← hc, map_mul]
      rw [key, mul_div_cancel_left₀ (algebraMap A K c) hb']

omit [IsDomain A] in
/-- Atiyah–Macdonald Exercise 5.28, (1) ⇒ (2): in a valuation ring of `K`, any two ideals are
comparable by inclusion. -/
theorem ideal_le_or_ge_of_isValuationRingOf (h : IsValuationRingOf A K)
    (I J : Ideal A) : I ≤ J ∨ J ≤ I := by
  by_cases hle : I ≤ J
  · exact Or.inl hle
  obtain ⟨a, haI, haJ⟩ := Set.not_subset.mp hle
  refine Or.inr fun b hbJ => ?_
  by_cases hb : b = 0
  · rw [hb]
    exact I.zero_mem
  have ha0 : a ≠ 0 := by rintro rfl; exact haJ J.zero_mem
  have hinj := IsFractionRing.injective A K
  have ha' : algebraMap A K a ≠ 0 := by simpa using ha0
  have hb' : algebraMap A K b ≠ 0 := by simpa using hb
  obtain ⟨c, hc⟩ | ⟨c, hc⟩ :=
    h (algebraMap A K a / algebraMap A K b) (div_ne_zero ha' hb')
  · -- `a / b = c` forces `a = c * b ∈ J`, contradicting the choice of `a`
    exfalso
    apply haJ
    have h1 : algebraMap A K (c * b) = algebraMap A K a := by
      rw [map_mul, hc, div_mul_cancel₀ (algebraMap A K a) hb']
    have h2 : c * b = a := hinj h1
    rw [← h2]
    exact J.mul_mem_left c hbJ
  · -- `(a / b)⁻¹ = c` forces `b = c * a ∈ I`
    have h1 : algebraMap A K (c * a) = algebraMap A K b := by
      rw [map_mul, hc, inv_div]
      exact div_mul_cancel₀ (algebraMap A K b) ha'
    have h2 : c * a = b := hinj h1
    rw [← h2]
    exact I.mul_mem_left c haI

/-- Atiyah–Macdonald Exercise 5.28, (2) ⇒ (1): if the ideals of `A` are totally ordered by
inclusion, then `A` is a valuation ring of `K`. -/
theorem isValuationRingOf_of_ideal_total
    (h : ∀ I J : Ideal A, I ≤ J ∨ J ≤ I) : IsValuationRingOf A K := by
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap A K b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have ha' : algebraMap A K a ≠ 0 := by simpa using ha0
  obtain hle | hle := h (Ideal.span {a}) (Ideal.span {b})
  · -- `(a) ⊆ (b)`: then `a = d * b`, so `x = d`
    have hamem : a ∈ Ideal.span ({b} : Set A) := hle (Ideal.subset_span (by simp))
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hamem
    refine Or.inl ⟨d, ?_⟩
    have key : algebraMap A K a = algebraMap A K d * algebraMap A K b := by
      rw [← hd, map_mul]
    rw [key, mul_div_cancel_right₀ (algebraMap A K d) hb']
  · -- `(b) ⊆ (a)`: then `b = d * a`, so `x⁻¹ = d`
    have hbmem : b ∈ Ideal.span ({a} : Set A) := hle (Ideal.subset_span (by simp))
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hbmem
    refine Or.inr ⟨d, ?_⟩
    have key : algebraMap A K b = algebraMap A K d * algebraMap A K a := by
      rw [← hd, map_mul]
    rw [key, inv_div]
    exact (mul_div_cancel_right₀ (algebraMap A K d) ha').symm

/-- Atiyah–Macdonald Exercise 5.28, (1) ⇔ (2). -/
theorem isValuationRingOf_iff_ideal_total :
    IsValuationRingOf A K ↔ ∀ I J : Ideal A, I ≤ J ∨ J ≤ I :=
  ⟨ideal_le_or_ge_of_isValuationRingOf, isValuationRingOf_of_ideal_total⟩

/-- For a prime ideal `𝔭` of a domain `A`, the field of fractions of `A` is also the field of
fractions of the localization `A_𝔭` (as `A ⊆ A_𝔭 ⊆ Frac A`). -/
theorem isFractionRing_localization_atPrime (p : Ideal A) [hp : p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) (FractionRing A) :=
  inferInstance

/-- The canonical `A`-algebra structure of `K` over `A_𝔭`: the inclusion `A_𝔭 ⊆ K`, which
exists because `A ⊆ A_𝔭 ⊆ Frac A = K`.  This is what makes `A_𝔭` a subring of the given
field of fractions `K` of `A`. -/
@[instance_reducible]
noncomputable def atPrimeAlgebra (p : Ideal A) [hp : p.IsPrime] :
    Algebra (Localization.AtPrime p) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime p) K p.primeCompl
    (nonZeroDivisors A) p.primeCompl_le_nonZeroDivisors

set_option linter.style.haveILetI false in
/-- With this algebra structure, the given field of fractions `K` of `A` is a field of
fractions of `A_𝔭`. -/
theorem isFractionRing_atPrimeAlgebra (p : Ideal A) [hp : p.IsPrime] :
    @IsFractionRing (Localization.AtPrime p) _ K _ (atPrimeAlgebra (K := K) p) := by
  letI := atPrimeAlgebra (K := K) p
  haveI : IsScalarTower A (Localization.AtPrime p) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) K
      p.primeCompl (nonZeroDivisors A) p.primeCompl_le_nonZeroDivisors
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _

/-- Atiyah–Macdonald Exercise 5.28, first deduction, intrinsic form: the localization of a
valuation ring at a prime ideal is a valuation ring. -/
theorem valuationRing_localization_atPrime (h : IsValuationRingOf A K) (p : Ideal A)
    [hp : p.IsPrime] : ValuationRing (Localization.AtPrime p) := by
  have htotal : ∀ I J : Ideal A, I ≤ J ∨ J ≤ I := isValuationRingOf_iff_ideal_total.mp h
  suffices PreValuationRing (Localization.AtPrime p) from .mk
  refine PreValuationRing.iff_ideal_total.mpr ⟨fun I J => ?_⟩
  rcases htotal (I.under A) (J.under A) with hle | hle
  · exact Or.inl ((IsLocalization.under_le_under_iff p.primeCompl
      (Localization.AtPrime p)).mp hle)
  · exact Or.inr ((IsLocalization.under_le_under_iff p.primeCompl
      (Localization.AtPrime p)).mp hle)

/-- Atiyah–Macdonald Exercise 5.28, first deduction, general form: a localization of a
valuation ring at a prime ideal is a valuation ring of *any* chosen field of fractions of it. -/
theorem localization_atPrime_isValuationRingOf_of_isFractionRing (h : IsValuationRingOf A K)
    (p : Ideal A) [hp : p.IsPrime] (L : Type*) [Field L]
    [Algebra (Localization.AtPrime p) L] [IsFractionRing (Localization.AtPrime p) L] :
    IsValuationRingOf (Localization.AtPrime p) L :=
  isValuationRingOf_iff_valuationRing.mpr (valuationRing_localization_atPrime h p)

set_option linter.style.haveILetI false in
/-- Atiyah–Macdonald Exercise 5.28, first deduction in the book's own terms: for the given
field of fractions `K` of `A` and a prime ideal `𝔭`, the localization `A_𝔭`, viewed as a
subring of `K = Frac A`, is a valuation ring of `K`. -/
theorem localization_atPrime_isValuationRingOf_given (h : IsValuationRingOf A K) (p : Ideal A)
    [hp : p.IsPrime] :
    @IsValuationRingOf (Localization.AtPrime p) K _ _ (atPrimeAlgebra (K := K) p) := by
  letI := atPrimeAlgebra (K := K) p
  haveI := isFractionRing_atPrimeAlgebra (K := K) p
  exact isValuationRingOf_iff_valuationRing.mpr (valuationRing_localization_atPrime h p)

/-- Atiyah–Macdonald Exercise 5.28, first deduction: for a prime ideal `𝔭` of a valuation ring
`A` of `K`, the localization `A_𝔭` is a valuation ring of its field of fractions (canonically
the field of fractions of `A`, as `A ⊆ A_𝔭 ⊆ K`). -/
theorem localization_atPrime_isValuationRingOf (h : IsValuationRingOf A K) (p : Ideal A)
    [hp : p.IsPrime] :
    IsValuationRingOf (Localization.AtPrime p) (FractionRing A) :=
  localization_atPrime_isValuationRingOf_of_isFractionRing h p (FractionRing A)

/-- Atiyah–Macdonald Exercise 5.28, second deduction, intrinsic form: the quotient of a
valuation ring by a prime ideal is a valuation ring. -/
theorem valuationRing_quotient (h : IsValuationRingOf A K) (p : Ideal A) [hp : p.IsPrime] :
    ValuationRing (A ⧸ p) := by
  have htotal : ∀ I J : Ideal A, I ≤ J ∨ J ≤ I := isValuationRingOf_iff_ideal_total.mp h
  have hsurj : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  suffices PreValuationRing (A ⧸ p) from .mk
  refine PreValuationRing.iff_ideal_total.mpr ⟨fun I J => ?_⟩
  rcases htotal (I.comap (Ideal.Quotient.mk p)) (J.comap (Ideal.Quotient.mk p)) with
    hle | hle
  · left
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) hsurj I,
      ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) hsurj J]
    exact Ideal.map_mono hle
  · right
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) hsurj I,
      ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) hsurj J]
    exact Ideal.map_mono hle

/-- Atiyah–Macdonald Exercise 5.28, second deduction, general form: a quotient of a valuation
ring by a prime ideal is a valuation ring of *any* chosen field of fractions of it. -/
theorem quotient_isValuationRingOf_of_isFractionRing (h : IsValuationRingOf A K) (p : Ideal A)
    [hp : p.IsPrime] (L : Type*) [Field L] [Algebra (A ⧸ p) L]
    [IsFractionRing (A ⧸ p) L] : IsValuationRingOf (A ⧸ p) L :=
  isValuationRingOf_iff_valuationRing.mpr (valuationRing_quotient h p)

/-- Atiyah–Macdonald Exercise 5.28, second deduction: for a prime ideal `𝔭` of a valuation ring
`A` of `K`, the quotient `A ⧸ 𝔭` is a valuation ring of its field of fractions. -/
theorem quotient_isValuationRingOf (h : IsValuationRingOf A K) (p : Ideal A) [hp : p.IsPrime] :
    IsValuationRingOf (A ⧸ p) (FractionRing (A ⧸ p)) :=
  quotient_isValuationRingOf_of_isFractionRing h p (FractionRing (A ⧸ p))

/-- Atiyah–Macdonald Exercise 5.28, all parts together. -/
theorem solution (A : Type*) [CommRing A] [IsDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (IsValuationRingOf A K ↔ ∀ I J : Ideal A, I ≤ J ∨ J ≤ I) ∧
      (IsValuationRingOf A K → ∀ (p : Ideal A) [_hp : p.IsPrime],
        @IsValuationRingOf (Localization.AtPrime p) K _ _
            (atPrimeAlgebra (A := A) (K := K) p) ∧
          IsValuationRingOf (A ⧸ p) (FractionRing (A ⧸ p))) := by
  refine ⟨isValuationRingOf_iff_ideal_total, fun h p _hp => ?_⟩
  exact ⟨localization_atPrime_isValuationRingOf_given h p, quotient_isValuationRingOf h p⟩

end AtiyahMcdonald69.Ex_5_28
