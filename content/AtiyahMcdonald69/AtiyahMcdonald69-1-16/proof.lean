import Mathlib

set_option linter.style.haveILetI false

/-!
# Atiyah–Macdonald (1969), Exercise 1.16

Draw pictures of `Spec ℤ`, `Spec ℝ`, `Spec ℂ[X]`, `Spec ℝ[X]`, `Spec ℤ[X]`.

This file formalises the mathematical content of those pictures: the classification of
prime ideals of the five rings, the specialisation order (which prime is in the closure
of which), the (unique) dense point, and the description of the closed subsets.

Everything is proved from Mathlib's ring theory; no classification is assumed.
-/

open Polynomial

namespace AtiyahMcdonald69.Ex_1_16

/-! ## 0. Generalities on `PrimeSpectrum` -/

section General

variable {R : Type*} [CommRing R]

/-- Specialisation in the prime spectrum is reverse inclusion of prime ideals:
`p` specialises to `q` exactly when every element of `p` lies in `q`. -/
theorem specializes_iff_le {p q : PrimeSpectrum R} : p ⤳ q ↔ p.asIdeal ≤ q.asIdeal := by
  rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

/-- The closure of a point is the set of primes containing it. -/
theorem closure_singleton_eq_zeroLocus (p : PrimeSpectrum R) :
    closure ({p} : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) :=
  PrimeSpectrum.closure_singleton p

theorem mem_closure_singleton_iff {p q : PrimeSpectrum R} :
    q ∈ closure ({p} : Set (PrimeSpectrum R)) ↔ p.asIdeal ≤ q.asIdeal := by
  rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

/-- A point of the spectrum is closed iff its prime ideal is maximal. -/
theorem isClosed_singleton_iff (p : PrimeSpectrum R) :
    IsClosed ({p} : Set (PrimeSpectrum R)) ↔ p.asIdeal.IsMaximal :=
  PrimeSpectrum.isClosed_singleton_iff_isMaximal p

/-- `Spec R` is quasi-compact (Atiyah–Macdonald, Exercise 1.17 (v)). -/
theorem quasiCompact : CompactSpace (PrimeSpectrum R) := inferInstance

/-- The closed subsets of `Spec R` are exactly the `V(I)`. -/
theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = PrimeSpectrum.zeroLocus (I : Set R) :=
  PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z

/-- The zero locus of an ideal is the union of the zero loci of the minimal primes over it. -/
theorem zeroLocus_eq_iUnion_minimalPrimes [IsNoetherianRing R] (I : Ideal R) :
    PrimeSpectrum.zeroLocus (I : Set R) =
      ⋃ p : I.minimalPrimes, PrimeSpectrum.zeroLocus ((p : Ideal R) : Set R) := by
  ext q
  simp only [Set.mem_iUnion, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := q.asIdeal) hq
    exact ⟨⟨p, hp⟩, hpq⟩
  · rintro ⟨p, hpq⟩
    exact le_trans (Ideal.IsMinimalPrime.le p.2) hpq

/-- In a Noetherian ring every closed subset of the spectrum is a finite union of
closures of points (stated with a set of points first, for convenience). -/
theorem exists_finite_closure_singleton_of_isClosed [IsNoetherianRing R]
    (Z : Set (PrimeSpectrum R)) (hZ : IsClosed Z) :
    ∃ S : Set (PrimeSpectrum R), S.Finite ∧
      Z = ⋃ p ∈ S, closure ({p} : Set (PrimeSpectrum R)) := by
  classical
  obtain ⟨I, rfl⟩ := (isClosed_iff_zeroLocus Z).mp hZ
  let f : I.minimalPrimes → PrimeSpectrum R := fun p => ⟨p.1, p.2.isPrime⟩
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  refine ⟨Set.range f, @Set.finite_range _ _ f (Set.finite_coe_iff.mp hfin), ?_⟩
  rw [zeroLocus_eq_iUnion_minimalPrimes]
  ext q
  simp only [Set.mem_iUnion, Set.mem_range, PrimeSpectrum.mem_zeroLocus,
    PrimeSpectrum.closure_singleton]
  constructor
  · rintro ⟨p, hpq⟩
    exact ⟨f p, ⟨p, rfl⟩, hpq⟩
  · rintro ⟨P, ⟨p, hp⟩, hPq⟩
    rw [← hp] at hPq
    exact ⟨p, hPq⟩

/-- In a Noetherian ring every closed subset of the spectrum is a finite union of
closures of points. -/
theorem exists_finset_closure_singleton_of_isClosed [IsNoetherianRing R]
    (Z : Set (PrimeSpectrum R)) (hZ : IsClosed Z) :
    ∃ s : Finset (PrimeSpectrum R),
      Z = ⋃ p ∈ (s : Set (PrimeSpectrum R)), closure ({p} : Set (PrimeSpectrum R)) := by
  obtain ⟨S, hS, hZ⟩ := exists_finite_closure_singleton_of_isClosed Z hZ
  refine ⟨hS.toFinset, ?_⟩
  rw [hZ]
  ext q
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hq⟩
    exact ⟨p, (Set.Finite.mem_toFinset hS).mpr hp, hq⟩
  · rintro ⟨p, hp, hq⟩
    exact ⟨p, (Set.Finite.mem_toFinset hS).mp hp, hq⟩

/-- A one-dimensional Noetherian domain: the closed subsets of its spectrum are the whole
space, or finite sets of non-generic points. -/
theorem isClosed_iff_finite_or_univ [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ Z = Set.univ ∨ (Z.Finite ∧ ∀ P ∈ Z, P.asIdeal ≠ ⊥) := by
  classical
  have hpt : ∀ P : PrimeSpectrum R, P.asIdeal ≠ ⊥ → closure ({P} : Set (PrimeSpectrum R)) = {P} := by
    intro P hP
    exact (isClosed_singleton_iff P).mpr (Ideal.IsPrime.isMaximal P.isPrime hP) |>.closure_eq
  constructor
  · intro hZ
    obtain ⟨s, hs⟩ := exists_finset_closure_singleton_of_isClosed Z hZ
    by_cases h : ∃ P ∈ (s : Set (PrimeSpectrum R)), P.asIdeal = ⊥
    · obtain ⟨P, hPs, hP⟩ := h
      refine Or.inl ?_
      rw [hs]
      refine Set.Subset.antisymm (Set.subset_univ _) fun q _ => ?_
      have hle : P.asIdeal ≤ q.asIdeal := by rw [hP]; exact bot_le
      refine Set.mem_iUnion₂.mpr ⟨P, hPs, ?_⟩
      rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
      exact hle
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hs]
        refine Set.Finite.biUnion s.finite_toSet ?_
        intro P hPs
        rw [hpt P (fun hbot => h ⟨P, hPs, hbot⟩)]
        exact Set.finite_singleton P
      · intro Q hQ hQbot
        rw [hs] at hQ
        simp only [Set.mem_iUnion] at hQ
        obtain ⟨P, hPs, hPQ⟩ := hQ
        rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at hPQ
        have hPQ' : P.asIdeal ≤ Q.asIdeal := hPQ
        exact h ⟨P, hPs, le_antisymm (hPQ'.trans_eq hQbot) bot_le⟩
  · rintro (rfl | ⟨hfin, hne⟩)
    · exact isClosed_univ
    · have hZU : Z = ⋃ P ∈ Z, ({P} : Set (PrimeSpectrum R)) := by
        ext q
        simp only [Set.mem_iUnion, Set.mem_singleton_iff]
        exact ⟨fun hq => ⟨q, hq, rfl⟩, fun ⟨P, hP, hPq⟩ => hPq ▸ hP⟩
      rw [hZU]
      exact Set.Finite.isClosed_biUnion hfin
        (fun P hP => (isClosed_singleton_iff P).mpr (Ideal.IsPrime.isMaximal P.isPrime (hne P hP)))

end General

/-! ## 1. Prime ideals in a principal ideal domain -/

section PID

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]

/-- In a principal ideal domain every prime ideal is `0` or is generated by a prime element. -/
theorem isPrime_ideal_iff_isPrime_generator (I : Ideal A) :
    I.IsPrime ↔ I = ⊥ ∨ ∃ a : A, Prime a ∧ I = Ideal.span {a} := by
  constructor
  · intro hI
    have hspan : I = Ideal.span {Submodule.IsPrincipal.generator I} :=
      (Ideal.span_singleton_generator I).symm
    by_cases h0 : Submodule.IsPrincipal.generator I = 0
    · exact Or.inl (by rw [hspan, h0]; simp)
    · exact Or.inr ⟨_, (Ideal.span_singleton_prime h0).mp (hspan ▸ hI), hspan⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact Ideal.isPrime_bot
    · exact Ideal.isPrime_span_singleton_of_prime ha

end PID

/-! ## 2. `Spec ℤ` -/

section Int

theorem isPrime_ideal_int (I : Ideal ℤ) :
    I.IsPrime ↔ I = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ I = Ideal.span {(p : ℤ)} := by
  rw [isPrime_ideal_iff_isPrime_generator]
  constructor
  · rintro (h | ⟨a, hprime, hI⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a.natAbs, (Int.prime_iff_natAbs_prime).mp hprime, ?_⟩
      rw [hI]
      rcases Int.natAbs_eq a with h | h
      · conv_lhs => rw [h]
      · conv_lhs => rw [h]
        rw [Ideal.span_singleton_neg]
  · rintro (h | ⟨p, hp, hI⟩)
    · exact Or.inl h
    · refine Or.inr ⟨(p : ℤ), ?_, hI⟩
      rw [Int.prime_iff_natAbs_prime]
      simpa using hp

/-- The generic point `(0)` of `Spec ℤ`. -/
def intGeneric : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩

/-- The closed point `(p)` of `Spec ℤ`, for a prime number `p`. -/
noncomputable def intPoint (p : ℕ) (hp : p.Prime) : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, Ideal.isPrime_span_singleton_of_prime (by
    rw [Int.prime_iff_natAbs_prime]; simpa using hp)⟩

theorem intPoint_asIdeal (p : ℕ) (hp : p.Prime) :
    (intPoint p hp).asIdeal = Ideal.span {(p : ℤ)} := rfl

theorem intGeneric_asIdeal : intGeneric.asIdeal = ⊥ := rfl

/-- Every point of `Spec ℤ` is `(0)` or one of the `(p)`. -/
theorem int_spec_cases (P : PrimeSpectrum ℤ) :
    P = intGeneric ∨ ∃ (p : ℕ) (hp : p.Prime), P = intPoint p hp := by
  rcases (isPrime_ideal_int P.asIdeal).mp P.isPrime with h | ⟨p, hp, hP⟩
  · exact Or.inl (PrimeSpectrum.ext (by simpa [intGeneric] using h))
  · exact Or.inr ⟨p, hp, PrimeSpectrum.ext (by simpa [intPoint] using hP)⟩

theorem intPoint_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : intPoint p hp = intPoint q hq) : p = q := by
  have h' : (intPoint p hp).asIdeal = (intPoint q hq).asIdeal := by rw [h]
  rw [intPoint_asIdeal, intPoint_asIdeal] at h'
  have hmem : (p : ℤ) ∈ Ideal.span {(q : ℤ)} := h' ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.mem_span_singleton] at hmem
  have hdvd : q ∣ p := by
    rw [← Int.natCast_dvd_natCast]
    exact hmem
  have := (Nat.dvd_prime hp).mp hdvd
  rcases this with h1 | h1
  · exact absurd h1 hq.ne_one
  · exact h1.symm

theorem intGeneric_ne_intPoint (p : ℕ) (hp : p.Prime) : intGeneric ≠ intPoint p hp := by
  intro h
  have h' : (intPoint p hp).asIdeal = intGeneric.asIdeal := by rw [h]
  rw [intPoint_asIdeal, intGeneric_asIdeal] at h'
  have hmem : (p : ℤ) ∈ (⊥ : Ideal ℤ) := h' ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

/-- The specialisation diagram of `Spec ℤ`: `(0)` specialises to every point (`(0)` is dense),
and each `(p)` is a closed point. -/
theorem int_specializes (P Q : PrimeSpectrum ℤ) :
    P ⤳ Q ↔ P = Q ∨ P = intGeneric := by
  rw [specializes_iff_le]
  constructor
  · intro h
    rcases int_spec_cases P with rfl | ⟨p, hp, rfl⟩
    · exact Or.inr rfl
    · rcases int_spec_cases Q with hQ | ⟨q, hq, hQ⟩
      · exfalso
        have hmem : (p : ℤ) ∈ Q.asIdeal := h (Ideal.mem_span_singleton_self _)
        rw [hQ, intGeneric_asIdeal] at hmem
        rw [Ideal.mem_bot] at hmem
        exact hp.ne_zero (by exact_mod_cast hmem)
      · refine Or.inl ?_
        rw [hQ] at h ⊢
        have hmem : (p : ℤ) ∈ Ideal.span {(q : ℤ)} :=
          h (Ideal.mem_span_singleton_self (p : ℤ))
        rw [Ideal.mem_span_singleton] at hmem
        have hdvd : q ∣ p := Int.natCast_dvd_natCast.mp hmem
        have hpq : p = q := by
          rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
          · exact absurd h1 hq.ne_one
          · exact h1.symm
        subst hpq
        exact PrimeSpectrum.ext rfl
  · rintro (rfl | rfl)
    · exact le_refl _
    · intro x hx
      rw [intGeneric_asIdeal, Ideal.mem_bot] at hx
      rw [hx]
      exact zero_mem _

/-- The generic point `(0)` is dense. -/
theorem intGeneric_dense : Dense ({intGeneric} : Set (PrimeSpectrum ℤ)) := by
  rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
  refine Set.Subset.antisymm (Set.subset_univ _) fun q _ => ?_
  rw [PrimeSpectrum.mem_zeroLocus, intGeneric_asIdeal]
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  rw [hx0]
  exact zero_mem _

/-- The closed subsets of `Spec ℤ`: the whole space, or a finite set of non-zero primes. -/
theorem isClosed_int (Z : Set (PrimeSpectrum ℤ)) :
    IsClosed Z ↔ Z = Set.univ ∨ (Z.Finite ∧ intGeneric ∉ Z) := by
  refine (isClosed_iff_finite_or_univ (R := ℤ) Z).trans ?_
  constructor
  · rintro (h | ⟨hfin, hne⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hfin, fun hg => hne intGeneric hg ?_⟩
      rw [intGeneric_asIdeal]
  · rintro (h | ⟨hfin, hgen⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hfin, fun P hP hbot => hgen ?_⟩
      have hP' : P = intGeneric := PrimeSpectrum.ext (by rw [hbot, intGeneric_asIdeal])
      rwa [hP'] at hP

end Int


/-! ## 2b. `Spec ℝ`: the spectrum of a field is a single point -/

section Real

/-- `ℝ` is a field, so its only prime ideal is `(0)`. -/
theorem isPrime_ideal_real (I : Ideal ℝ) : I.IsPrime ↔ I = ⊥ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hx0
    have h1 : (1 : ℝ) ∈ I := by
      simpa using I.mul_mem_right (↑u⁻¹) hxI
    refine h.ne_top ?_
    rwa [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_singleton_le_iff_mem]
  · rintro rfl
    exact Ideal.isPrime_bot

/-- `Spec ℝ` is a single point. -/
theorem real_spec_subsingleton : Subsingleton (PrimeSpectrum ℝ) := by
  constructor
  intro P Q
  refine PrimeSpectrum.ext ?_
  rw [(isPrime_ideal_real P.asIdeal).mp P.isPrime,
    (isPrime_ideal_real Q.asIdeal).mp Q.isPrime]

end Real

/-! ## 3. One-dimensional domains: the generic point, specialisation, closed points -/

section DimOne

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The generic point `(0)` of the spectrum of a domain. -/
def genericPoint (R : Type*) [CommRing R] [IsDomain R] : PrimeSpectrum R :=
  ⟨⊥, Ideal.isPrime_bot⟩

theorem genericPoint_asIdeal : (genericPoint R).asIdeal = ⊥ := rfl

/-- The generic point of the spectrum of a domain is dense. -/
theorem dense_genericPoint : Dense ({genericPoint R} : Set (PrimeSpectrum R)) := by
  rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
  refine Set.Subset.antisymm (Set.subset_univ _) fun q _ => ?_
  rw [PrimeSpectrum.mem_zeroLocus, genericPoint_asIdeal]
  intro x hx
  have hx0 : x ∈ (⊥ : Ideal R) := hx
  rw [Ideal.mem_bot] at hx0
  rw [hx0]
  exact zero_mem _

section

variable [Ring.DimensionLEOne R]

/-- In a one-dimensional domain, every point specialises to itself, and the generic point
specialises to every point. -/
theorem specializes_iff_eq_or_generic (P Q : PrimeSpectrum R) :
    P ⤳ Q ↔ P = Q ∨ P = genericPoint R := by
  rw [specializes_iff_le]
  constructor
  · intro h
    by_cases hbot : P.asIdeal = ⊥
    · exact Or.inr (PrimeSpectrum.ext (by rw [genericPoint_asIdeal]; exact hbot))
    · exact Or.inl (PrimeSpectrum.ext (Ideal.IsMaximal.eq_of_le
        (Ideal.IsPrime.isMaximal P.isPrime hbot) Q.isPrime.ne_top h))
  · rintro (rfl | rfl)
    · exact le_refl _
    · intro x hx
      have hx0 : x ∈ (⊥ : Ideal R) := by
        rw [← genericPoint_asIdeal]
        exact hx
      rw [Ideal.mem_bot] at hx0
      rw [hx0]
      exact zero_mem _

theorem isClosed_iff_finite_or_univ' [IsNoetherianRing R] (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ Z = Set.univ ∨ (Z.Finite ∧ genericPoint R ∉ Z) := by
  refine (isClosed_iff_finite_or_univ Z).trans ?_
  constructor
  · rintro (h | ⟨hfin, hne⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hfin, fun hg => hne _ hg ?_⟩
      rw [genericPoint_asIdeal]
  · rintro (h | ⟨hfin, hg⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hfin, fun P hP hbot => hg ?_⟩
      have hP' : P = genericPoint R := PrimeSpectrum.ext (by rw [hbot, genericPoint_asIdeal])
      rwa [hP'] at hP

end

end DimOne

section RealSpec

/-- Every point of `Spec ℝ` is the generic point. -/
theorem real_spec_eq_generic (P : PrimeSpectrum ℝ) : P = genericPoint ℝ :=
  PrimeSpectrum.ext (((isPrime_ideal_real P.asIdeal).mp P.isPrime).trans
    (genericPoint_asIdeal (R := ℝ)).symm)

theorem real_spec_specializes (P Q : PrimeSpectrum ℝ) : P ⤳ Q := by
  rw [specializes_iff_le, (isPrime_ideal_real P.asIdeal).mp P.isPrime]
  exact bot_le

end RealSpec

/-! ## 4. `Spec ℂ[X]` -/

section ComplexPoly

theorem irreducible_X_sub_C {K : Type*} [Field K] (a : K) : Irreducible (X - C a) :=
  irreducible_of_degree_eq_one (degree_X_sub_C a)

theorem prime_X_sub_C {K : Type*} [Field K] (a : K) : Prime (X - C a) :=
  (irreducible_X_sub_C a).prime

/-- The closed point `(X - a)` of `Spec ℂ[X]`. -/
noncomputable def complexPoint (a : ℂ) : PrimeSpectrum ℂ[X] :=
  ⟨Ideal.span {X - C a}, Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C a)⟩

theorem complexPoint_asIdeal (a : ℂ) :
    (complexPoint a).asIdeal = Ideal.span {X - C a} := rfl

/-- Every prime ideal of `ℂ[X]` is `0` or `(X - a)`: `ℂ` is algebraically closed, so an
irreducible polynomial is linear. -/
theorem isPrime_ideal_complex_poly (I : Ideal ℂ[X]) :
    I.IsPrime ↔ I = ⊥ ∨ ∃ a : ℂ, I = Ideal.span {X - C a} := by
  constructor
  · intro hI
    rcases (isPrime_ideal_iff_isPrime_generator I).mp hI with h | ⟨f, hf, hIf⟩
    · exact Or.inl h
    · right
      have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
      have hunit : IsUnit (C f.leadingCoeff⁻¹ : ℂ[X]) :=
        isUnit_C.mpr (inv_ne_zero hc0).isUnit
      have hg : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf.ne_zero
      have hspan : Ideal.span {f} = Ideal.span {f * C f.leadingCoeff⁻¹} :=
        (Ideal.span_singleton_mul_right_unit hunit f).symm
      have hpr : Prime (f * C f.leadingCoeff⁻¹) :=
        (Ideal.span_singleton_prime hg.ne_zero).mp
          (hspan ▸ (hIf ▸ Ideal.isPrime_span_singleton_of_prime hf))
      have hdeg : (f * C f.leadingCoeff⁻¹).natDegree = 1 :=
        (IsAlgClosed.splits _).natDegree_eq_one_of_irreducible hpr.irreducible
      obtain ⟨a, ha⟩ : ∃ a : ℂ, f * C f.leadingCoeff⁻¹ = X - C a := by
        refine ⟨-((f * C f.leadingCoeff⁻¹).coeff 0), ?_⟩
        conv_lhs => rw [hg.eq_X_add_C hdeg]
        rw [C_neg, sub_neg_eq_add]
      exact ⟨a, by rw [hIf, hspan, ha]⟩
  · rintro (rfl | ⟨a, rfl⟩)
    · exact Ideal.isPrime_bot
    · exact Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C a)

theorem complex_spec_cases (P : PrimeSpectrum ℂ[X]) :
    P = genericPoint ℂ[X] ∨ ∃ a : ℂ, P = complexPoint a := by
  rcases (isPrime_ideal_complex_poly P.asIdeal).mp P.isPrime with h | ⟨a, ha⟩
  · exact Or.inl (PrimeSpectrum.ext (by rw [genericPoint_asIdeal]; exact h))
  · exact Or.inr ⟨a, PrimeSpectrum.ext (by rw [complexPoint_asIdeal]; exact ha)⟩

theorem complex_specializes (P Q : PrimeSpectrum ℂ[X]) :
    P ⤳ Q ↔ P = Q ∨ P = genericPoint ℂ[X] :=
  specializes_iff_eq_or_generic P Q

theorem isClosed_complex_poly (Z : Set (PrimeSpectrum ℂ[X])) :
    IsClosed Z ↔ Z = Set.univ ∨ (Z.Finite ∧ genericPoint ℂ[X] ∉ Z) :=
  isClosed_iff_finite_or_univ' Z

end ComplexPoly

/-! ## 5. `Spec ℝ[X]` -/

section RealPoly

theorem irreducible_quadratic_of_discrim_neg {b c : ℝ} (h : b ^ 2 - 4 * c < 0) :
    Irreducible (X ^ 2 + C b * X + C c) := by
  have hdeg : (X ^ 2 + C b * X + C c).natDegree = 2 := by
    simpa using natDegree_quadratic (a := (1 : ℝ)) (b := b) (c := c) one_ne_zero
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hdeg]; norm_num
  · intro x hx
    rw [IsRoot.def] at hx
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg (2 * x + b)]

/-- The closed point `(X - a)` of `Spec ℝ[X]`. -/
noncomputable def realPoint (a : ℝ) : PrimeSpectrum ℝ[X] :=
  ⟨Ideal.span {X - C a}, Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C a)⟩

/-- The closed point `(X² + bX + c)` of `Spec ℝ[X]`, with negative discriminant. -/
noncomputable def realQuad (b c : ℝ) (h : b ^ 2 - 4 * c < 0) : PrimeSpectrum ℝ[X] :=
  ⟨Ideal.span {X ^ 2 + C b * X + C c},
    Ideal.isPrime_span_singleton_of_prime (irreducible_quadratic_of_discrim_neg h).prime⟩

theorem monic_quadratic_normal_form {g : ℝ[X]} (hg : g.Monic) (hdeg : g.natDegree = 2) :
    g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  have hq := eq_quadratic_of_degree_le_two (p := g)
    (by rw [degree_eq_natDegree hg.ne_zero, hdeg]; simp)
  have hc2 : g.coeff 2 = 1 := by
    have h := hg.coeff_natDegree
    rwa [hdeg] at h
  rw [hq, hc2]
  simp

/-- A monic irreducible real quadratic has negative discriminant. -/
theorem discrim_neg_of_monic_irreducible {g : ℝ[X]} (hg : g.Monic) (hirr : Irreducible g)
    (hdeg : g.natDegree = 2) : g.coeff 1 ^ 2 - 4 * g.coeff 0 < 0 := by
  set b := g.coeff 1 with hb
  set c := g.coeff 0 with hc
  have hnorm : g = X ^ 2 + C b * X + C c := monic_quadratic_normal_form hg hdeg
  by_contra hcon
  have hcon' : 0 ≤ b ^ 2 - 4 * c := not_lt.mp hcon
  have h2 : 2 ≤ g.natDegree := by omega
  have h3 : g.natDegree ≤ 3 := by omega
  have hroots : g.roots = 0 :=
    (hg.irreducible_iff_roots_eq_zero_of_degree_le_three h2 h3).mp hirr
  have hxroot : g.IsRoot ((-b + Real.sqrt (b ^ 2 - 4 * c)) / 2) := by
    have h' : (X ^ 2 + C b * X + C c).IsRoot ((-b + Real.sqrt (b ^ 2 - 4 * c)) / 2) := by
      rw [IsRoot.def]
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      nlinarith [Real.sq_sqrt hcon']
    rwa [hnorm]
  have hmem := (mem_roots hg.ne_zero).mpr hxroot
  rw [hroots] at hmem
  simp at hmem

/-- Every prime ideal of `ℝ[X]` is `0`, `(X - a)`, or `(X² + bX + c)` with `b² - 4c < 0`. -/
theorem isPrime_ideal_real_poly (I : Ideal ℝ[X]) :
    I.IsPrime ↔ I = ⊥ ∨ (∃ a : ℝ, I = Ideal.span {X - C a}) ∨
      (∃ b c : ℝ, b ^ 2 - 4 * c < 0 ∧ I = Ideal.span {X ^ 2 + C b * X + C c}) := by
  constructor
  · intro hI
    rcases (isPrime_ideal_iff_isPrime_generator I).mp hI with h | ⟨f, hf, hIf⟩
    · exact Or.inl h
    · have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
      have hunit : IsUnit (C f.leadingCoeff⁻¹ : ℝ[X]) :=
        isUnit_C.mpr (inv_ne_zero hc0).isUnit
      have hg : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf.ne_zero
      have hspan : Ideal.span {f} = Ideal.span {f * C f.leadingCoeff⁻¹} :=
        (Ideal.span_singleton_mul_right_unit hunit f).symm
      have hpr : Prime (f * C f.leadingCoeff⁻¹) :=
        (Ideal.span_singleton_prime hg.ne_zero).mp
          (hspan ▸ (hIf ▸ Ideal.isPrime_span_singleton_of_prime hf))
      have hirr := hpr.irreducible
      have hle := Irreducible.natDegree_le_two hirr
      have hisPrime : (Ideal.span {f * C f.leadingCoeff⁻¹}).IsPrime :=
        hspan ▸ (hIf ▸ Ideal.isPrime_span_singleton_of_prime hf)
      rcases (show (f * C f.leadingCoeff⁻¹).natDegree = 0 ∨
          (f * C f.leadingCoeff⁻¹).natDegree = 1 ∨
          (f * C f.leadingCoeff⁻¹).natDegree = 2 from by omega) with h0 | h1 | h2
      · have hone : f * C f.leadingCoeff⁻¹ = 1 := hg.natDegree_eq_zero.mp h0
        rw [hone, Ideal.span_singleton_one] at hisPrime
        exact absurd rfl hisPrime.ne_top
      · refine Or.inr (Or.inl ⟨-((f * C f.leadingCoeff⁻¹).coeff 0), ?_⟩)
        rw [hIf, hspan]
        conv_lhs => rw [hg.eq_X_add_C h1]
        rw [C_neg, sub_neg_eq_add]
      · refine Or.inr (Or.inr ⟨(f * C f.leadingCoeff⁻¹).coeff 1,
          (f * C f.leadingCoeff⁻¹).coeff 0, discrim_neg_of_monic_irreducible hg hirr h2, ?_⟩)
        rw [hIf, hspan]
        conv_lhs => rw [monic_quadratic_normal_form hg h2]
  · rintro (rfl | ⟨a, rfl⟩ | ⟨b, c, hbc, rfl⟩)
    · exact Ideal.isPrime_bot
    · exact Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C a)
    · exact Ideal.isPrime_span_singleton_of_prime (irreducible_quadratic_of_discrim_neg hbc).prime

theorem real_spec_cases (P : PrimeSpectrum ℝ[X]) :
    P = genericPoint ℝ[X] ∨ (∃ a : ℝ, P = realPoint a) ∨
      (∃ (b c : ℝ) (h : b ^ 2 - 4 * c < 0), P = realQuad b c h) := by
  rcases (isPrime_ideal_real_poly P.asIdeal).mp P.isPrime with h | ⟨a, ha⟩ | ⟨b, c, hbc, hP⟩
  · exact Or.inl (PrimeSpectrum.ext (by rw [genericPoint_asIdeal]; exact h))
  · exact Or.inr (Or.inl ⟨a, PrimeSpectrum.ext (by simpa [realPoint] using ha)⟩)
  · exact Or.inr (Or.inr ⟨b, c, hbc, PrimeSpectrum.ext (by simpa [realQuad] using hP)⟩)

theorem real_specializes (P Q : PrimeSpectrum ℝ[X]) :
    P ⤳ Q ↔ P = Q ∨ P = genericPoint ℝ[X] :=
  specializes_iff_eq_or_generic P Q

theorem isClosed_real_poly (Z : Set (PrimeSpectrum ℝ[X])) :
    IsClosed Z ↔ Z = Set.univ ∨ (Z.Finite ∧ genericPoint ℝ[X] ∉ Z) :=
  isClosed_iff_finite_or_univ' Z

end RealPoly


/-! ## 6. Prime ideals of `ℤ[X]` (Atiyah–Macdonald, Exercise 1.16) -/

section IntPoly

/-- Reduction of integer polynomials modulo `p`. -/
noncomputable def redMap (p : ℕ) : ℤ[X] →+* (ZMod p)[X] :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod p))

theorem redMap_apply (p : ℕ) (f : ℤ[X]) :
    redMap p f = Polynomial.map (Int.castRingHom (ZMod p)) f := rfl

theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap p) :=
  Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective

theorem redMap_natCast (p : ℕ) : redMap p (p : ℤ[X]) = 0 := by
  rw [redMap_apply, show (p : ℤ[X]) = C (p : ℤ) by simp, Polynomial.map_C]
  simp

theorem natCast_int_poly_eq_C (p : ℕ) : (p : ℤ[X]) = C (p : ℤ) := by simp

/-- The kernel of reduction modulo `p` is the ideal generated by `p`. -/
theorem ker_redMap (p : ℕ) : RingHom.ker (redMap p) = Ideal.span {(p : ℤ[X])} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, natCast_int_poly_eq_C,
    Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro hx n
    have h := congrArg (fun f : (ZMod p)[X] => f.coeff n) hx
    simp only [redMap_apply, Polynomial.coeff_map, Polynomial.coeff_zero] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x.coeff n) p).mp h
  · intro hx
    ext n
    simp only [redMap_apply, Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x.coeff n) p).mpr (hx n)

theorem comap_redMap_bot (p : ℕ) :
    Ideal.comap (redMap p) (⊥ : Ideal (ZMod p)[X]) = Ideal.span {(p : ℤ[X])} :=
  ker_redMap p

/-- Primes of `ℤ[X]` containing `p` correspond to primes of `(ℤ/p)[X]`: the inverse image
of the prime generated by `g` is generated by `p` and any lift `G` of `g`. -/
theorem comap_redMap_span (p : ℕ) (G : ℤ[X]) :
    Ideal.comap (redMap p) (Ideal.span {redMap p G}) = Ideal.span {(p : ℤ[X]), G} := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨Q, hQ⟩ := redMap_surjective p q
    have hzero : redMap p (x - Q * G) = 0 := by
      rw [map_sub, map_mul, hQ, hq]
      ring
    have hmem : x - Q * G ∈ Ideal.span {(p : ℤ[X])} := by
      rw [← ker_redMap p, RingHom.mem_ker]
      exact hzero
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨A, hA⟩ := hmem
    rw [Ideal.mem_span_pair]
    exact ⟨A, Q, by rw [mul_comm A (p : ℤ[X]), ← hA]; ring⟩
  · intro x hx
    rw [Ideal.mem_span_pair] at hx
    obtain ⟨A, B, hAB⟩ := hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨redMap p B, ?_⟩
    rw [← hAB, map_add, map_mul, map_mul, redMap_natCast, mul_zero, zero_add, mul_comm]

/-- Clearing denominators: a rational polynomial becomes an integer polynomial after
multiplication by a non-zero natural number. -/
theorem exists_nat_mul_map (f : ℚ[X]) :
    ∃ (N : ℕ) (g : ℤ[X]), N ≠ 0 ∧ g.map (Int.castRingHom ℚ) = C (N : ℚ) * f := by
  induction f using Polynomial.induction_on with
  | C a =>
      refine ⟨a.den, C a.num, a.den_nz, ?_⟩
      have hden : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
      have hkey : (a.den : ℚ) * a = (a.num : ℚ) := by
        have h := Rat.num_div_den a
        rw [div_eq_iff hden] at h
        linarith [h]
      rw [Polynomial.map_C, ← Polynomial.C_mul, hkey]
      simp
  | add f g hf hg =>
      obtain ⟨N₁, g₁, hN₁, hg₁⟩ := hf
      obtain ⟨N₂, g₂, hN₂, hg₂⟩ := hg
      refine ⟨N₁ * N₂, C (N₂ : ℤ) * g₁ + C (N₁ : ℤ) * g₂, Nat.mul_ne_zero hN₁ hN₂, ?_⟩
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hg₁, hg₂]
      have hcast : ∀ n : ℕ, ((Int.castRingHom ℚ) (n : ℤ)) = (n : ℚ) := fun n => by simp
      simp only [hcast]
      push_cast
      rw [Polynomial.C_mul]
      ring
  | monomial n a ih =>
      obtain ⟨N, g, hN, hg⟩ := ih
      refine ⟨N, g * X, hN, ?_⟩
      simp only [Polynomial.map_mul, Polynomial.map_X, hg, pow_succ]
      ring

/-- If `1` lies in the ideal generated by the reductions of `F` and `x` in `ℚ[X]`, then some
positive integer lies in the ideal generated by `F` and `x` in `ℤ[X]`. -/
theorem exists_natCast_mem_span_of_one_mem (F x : ℤ[X])
    (h : (1 : ℚ[X]) ∈
      Ideal.span {F.map (Int.castRingHom ℚ), x.map (Int.castRingHom ℚ)}) :
    ∃ N : ℕ, N ≠ 0 ∧ (C (N : ℤ) : ℤ[X]) ∈ Ideal.span {F, x} := by
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨N₁, A, hN₁, hA⟩ := exists_nat_mul_map a
  obtain ⟨N₂, B, hN₂, hB⟩ := exists_nat_mul_map b
  refine ⟨N₁ * N₂, Nat.mul_ne_zero hN₁ hN₂, ?_⟩
  have hmap : (Polynomial.map (Int.castRingHom ℚ))
      ((C (N₂ : ℤ) * A) * F + (C (N₁ : ℤ) * B) * x) = C ((N₁ * N₂ : ℕ) : ℚ) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB]
    have hkey : C ((N₁ : ℚ)) * C ((N₂ : ℚ)) *
        (a * Polynomial.map (Int.castRingHom ℚ) F + b * Polynomial.map (Int.castRingHom ℚ) x)
        = C ((N₁ * N₂ : ℕ) : ℚ) := by
      rw [hab, mul_one, ← Polynomial.C_mul]
      push_cast
      rfl
    calc C ((Int.castRingHom ℚ) ↑N₂) * (C ↑N₁ * a) * Polynomial.map (Int.castRingHom ℚ) F +
          C ((Int.castRingHom ℚ) ↑N₁) * (C ↑N₂ * b) * Polynomial.map (Int.castRingHom ℚ) x
        = C ((N₁ : ℚ)) * C ((N₂ : ℚ)) *
            (a * Polynomial.map (Int.castRingHom ℚ) F +
              b * Polynomial.map (Int.castRingHom ℚ) x) := by
          have hcast : ∀ n : ℕ, ((Int.castRingHom ℚ) (n : ℤ)) = (n : ℚ) := fun n => by simp
          simp only [hcast]
          ring
      _ = C ((N₁ * N₂ : ℕ) : ℚ) := hkey
  rw [Ideal.mem_span_pair]
  refine ⟨C (N₂ : ℤ) * A, C (N₁ : ℤ) * B, ?_⟩
  refine Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective ?_
  have hcast : ∀ n : ℕ, ((Int.castRingHom ℚ) (n : ℤ)) = (n : ℚ) := fun n => by simp
  rw [hmap, Polynomial.map_C]
  simp only [hcast]

/-- A non-constant irreducible polynomial over `ℤ` is primitive (Gauss). -/
theorem natDegree_units_zpoly (u : ℤ[X]ˣ) : (↑u : ℤ[X]).natDegree = 0 := by
  have hu : (↑u : ℤ[X]) ≠ 0 := u.isUnit.ne_zero
  have hu' : (↑u⁻¹ : ℤ[X]) ≠ 0 := u⁻¹.isUnit.ne_zero
  have h := Polynomial.natDegree_mul hu hu'
  rw [Units.mul_inv, Polynomial.natDegree_one] at h
  omega

theorem isPrimitive_of_irreducible_of_natDegree_pos {F : ℤ[X]} (hirr : Irreducible F)
    (hdeg : 0 < F.natDegree) : F.IsPrimitive := by
  intro r hr
  obtain ⟨q, hq⟩ := hr
  rcases hirr.isUnit_or_isUnit (a := C r) (b := q) hq with hunit | hunit
  · exact Polynomial.isUnit_C.mp hunit
  · exfalso
    obtain ⟨u, rfl⟩ := hunit
    have hCr : (C r : ℤ[X]) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hq
      rw [hq] at hdeg
      simp at hdeg
    have hdeg' : F.natDegree = (C r : ℤ[X]).natDegree + (↑u : ℤ[X]).natDegree := by
      rw [hq, Polynomial.natDegree_mul hCr u.isUnit.ne_zero]
    rw [Polynomial.natDegree_C, natDegree_units_zpoly] at hdeg'
    omega

/-- An irreducible element of a non-trivial monoid with zero is non-zero. -/
theorem irreducible_ne_zero' {M : Type*} [MonoidWithZero M] [Nontrivial M] {F : M}
    (hF : Irreducible F) : F ≠ 0 := by
  rintro rfl
  rcases hF.isUnit_or_isUnit (a := (0 : M)) (b := 0) (by rw [zero_mul]) with h | h
  · exact one_ne_zero (isUnit_zero_iff.mp h).symm
  · exact one_ne_zero (isUnit_zero_iff.mp h).symm

/-- An irreducible polynomial over `ℤ` is non-zero. -/
theorem irreducible_zpoly_ne_zero {F : ℤ[X]} (hF : Irreducible F) : F ≠ 0 :=
  irreducible_ne_zero' hF

/-- Every non-zero prime ideal of `ℤ[X]` contains a non-zero irreducible element. -/
theorem exists_irreducible_mem_of_ne_bot {I : Ideal ℤ[X]} (hI : I.IsPrime) (hne : I ≠ ⊥) :
    ∃ F : ℤ[X], Irreducible F ∧ F ∈ I := by
  obtain ⟨h, hhI, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨s, hsirr, hassoc⟩ := WfDvdMonoid.exists_factors h hh0
  have hprod : s.prod ∈ I := by
    obtain ⟨u, hu⟩ := hassoc
    have hsu : s.prod = h * (↑u⁻¹ : ℤ[X]) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hsu]
    exact Ideal.mul_mem_right _ I hhI
  have key : ∀ (s : Multiset ℤ[X]), (∀ b ∈ s, Irreducible b) → s.prod ∈ I →
      ∃ F ∈ s, F ∈ I := by
    intro s
    induction s using Multiset.induction with
    | empty =>
        intro _ hmem
        rw [Multiset.prod_zero] at hmem
        refine absurd ?_ hI.ne_top
        rw [eq_top_iff, ← Ideal.span_singleton_one]
        exact Ideal.span_singleton_le_iff_mem I |>.mpr hmem
    | cons a s ih =>
        intro hs hmem
        rw [Multiset.prod_cons] at hmem
        rcases hI.mem_or_mem hmem with ha | hs'
        · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
        · obtain ⟨F, hFs, hFI⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) hs'
          exact ⟨F, Multiset.mem_cons_of_mem hFs, hFI⟩
  obtain ⟨F, hFs, hFI⟩ := key s hsirr hprod
  exact ⟨F, hsirr F hFs, hFI⟩

end IntPoly


/-- Every prime ideal of `K[X]` (`K` a field) is `0` or generated by a monic irreducible
polynomial. -/
theorem isPrime_ideal_field_poly {K : Type*} [Field K] (I : Ideal K[X]) :
    I.IsPrime ↔ I = ⊥ ∨ ∃ f : K[X], f.Monic ∧ Irreducible f ∧ I = Ideal.span {f} := by
  constructor
  · intro hI
    rcases (isPrime_ideal_iff_isPrime_generator I).mp hI with h | ⟨f, hf, hIf⟩
    · exact Or.inl h
    · have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
      have hunit : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
        isUnit_C.mpr (inv_ne_zero hc0).isUnit
      have hg : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf.ne_zero
      have hspan : Ideal.span {f} = Ideal.span {f * C f.leadingCoeff⁻¹} :=
        (Ideal.span_singleton_mul_right_unit hunit f).symm
      have hpr : Prime (f * C f.leadingCoeff⁻¹) :=
        (Ideal.span_singleton_prime hg.ne_zero).mp
          (hspan ▸ (hIf ▸ Ideal.isPrime_span_singleton_of_prime hf))
      exact Or.inr ⟨_, hg, hpr.irreducible, by rw [hIf, hspan]⟩
  · rintro (rfl | ⟨f, _, hfirr, rfl⟩)
    · exact Ideal.isPrime_bot
    · exact Ideal.isPrime_span_singleton_of_prime hfirr.prime

/-- **The prime ideals of `ℤ[X]`**: `(0)`, `(p)`, `(F)` for a primitive irreducible `F` of
positive degree, and `(p, G)` where the reduction of `G` modulo `p` is monic and irreducible
(Atiyah–Macdonald, Exercise 1.16). -/
theorem isPrime_ideal_int_poly (P : Ideal ℤ[X]) :
    P.IsPrime ↔ P = ⊥ ∨
      (∃ p : ℕ, p.Prime ∧ P = Ideal.span {(p : ℤ[X])}) ∨
      (∃ F : ℤ[X], F.IsPrimitive ∧ 0 < F.natDegree ∧ Irreducible F ∧
        P = Ideal.span {F}) ∨
      (∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]),
        (redMap p G).Monic ∧ Irreducible (redMap p G) ∧
          P = Ideal.span {(p : ℤ[X]), G}) := by
  constructor
  · intro hP
    have hu : (P.under ℤ).IsPrime := hP.under ℤ
    rcases (isPrime_ideal_int _).mp hu with hbot | ⟨p, hp, hq⟩
    · -- the contraction of `P` to `ℤ` is `(0)`
      by_cases hP0 : P = ⊥
      · exact Or.inl hP0
      · obtain ⟨F, hFirr, hFP⟩ := exists_irreducible_mem_of_ne_bot hP hP0
        have hFne : F ≠ 0 := irreducible_zpoly_ne_zero hFirr
        have hFdeg : 0 < F.natDegree := by
          rcases Nat.eq_zero_or_pos F.natDegree with h | h
          · exfalso
            have hFc : F = C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
            have hmem : F.coeff 0 ∈ P.under ℤ := by
              rw [Ideal.mem_under]
              rw [hFc] at hFP
              exact hFP
            rw [hbot] at hmem
            have hz : F.coeff 0 = 0 := Ideal.mem_bot.mp hmem
            rw [hFc, hz, Polynomial.C_0] at hFne
            exact hFne rfl
          · exact h
        have hFprim : F.IsPrimitive := isPrimitive_of_irreducible_of_natDegree_pos hFirr hFdeg
        have hspan : P = Ideal.span {F} := by
          refine le_antisymm ?_ (Ideal.span_singleton_le_iff_mem P |>.mpr hFP)
          intro x hxP
          rw [Ideal.mem_span_singleton]
          by_contra hdvd
          have hdvdQ : ¬ (F.map (Int.castRingHom ℚ) ∣ x.map (Int.castRingHom ℚ)) :=
            fun h => hdvd ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast F x hFprim).mpr h)
          have hFirrQ : Irreducible (F.map (Int.castRingHom ℚ)) :=
            (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hFprim).mp hFirr
          have hFneQ : F.map (Int.castRingHom ℚ) ≠ 0 := by
            intro h0
            rw [Polynomial.map_eq_zero_iff Int.cast_injective] at h0
            exact hFne h0
          have hmax : Ideal.IsMaximal (Ideal.span {F.map (Int.castRingHom ℚ)}) :=
            (Ideal.irreducible_iff_isMaximal_span_singleton hFneQ).mp hFirrQ
          have hxnot : x.map (Int.castRingHom ℚ) ∉
              Ideal.span {F.map (Int.castRingHom ℚ)} := by
            intro hmem
            rw [Ideal.mem_span_singleton] at hmem
            exact hdvdQ hmem
          have hsup : Ideal.span {F.map (Int.castRingHom ℚ)} ⊔
              Ideal.span {x.map (Int.castRingHom ℚ)} = ⊤ := by
            by_contra hne
            have hEq : Ideal.span {F.map (Int.castRingHom ℚ)} =
                Ideal.span {F.map (Int.castRingHom ℚ)} ⊔
                  Ideal.span {x.map (Int.castRingHom ℚ)} :=
              hmax.eq_of_le hne le_sup_left
            exact hxnot (by
              rw [hEq]
              exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          have hone : (1 : ℚ[X]) ∈ Ideal.span {F.map (Int.castRingHom ℚ)} ⊔
              Ideal.span {x.map (Int.castRingHom ℚ)} := by rw [hsup]; trivial
          rw [Submodule.mem_sup] at hone
          obtain ⟨y, hy, z, hz, hyz⟩ := hone
          rw [Ideal.mem_span_singleton] at hy hz
          obtain ⟨A, rfl⟩ := hy
          obtain ⟨B, rfl⟩ := hz
          have h1mem : (1 : ℚ[X]) ∈
              Ideal.span {F.map (Int.castRingHom ℚ), x.map (Int.castRingHom ℚ)} := by
            rw [Ideal.mem_span_pair]
            exact ⟨A, B, by rw [mul_comm A, mul_comm B, ← hyz]⟩
          obtain ⟨N, hN, hmemN⟩ := exists_natCast_mem_span_of_one_mem F x h1mem
          have hspan_le : Ideal.span {F, x} ≤ P := by
            refine Ideal.span_le.mpr ?_
            intro y hy
            rcases (by simpa using hy : y = F ∨ y = x) with rfl | rfl
            · exact hFP
            · exact hxP
          have hNP : (C (N : ℤ) : ℤ[X]) ∈ P := hspan_le hmemN
          have hNin : (N : ℤ) ∈ P.under ℤ := by
            rw [Ideal.mem_under]
            simpa using hNP
          rw [hbot] at hNin
          exact hN (by exact_mod_cast Ideal.mem_bot.mp hNin)
        exact Or.inr (Or.inr (Or.inl ⟨F, hFprim, hFdeg, hFirr, hspan⟩))
    · -- the contraction of `P` to `ℤ` is `(p)`
      haveI : Fact p.Prime := ⟨hp⟩
      have hpP : (p : ℤ[X]) ∈ P := by
        have hmem : (p : ℤ) ∈ P.under ℤ := by
          rw [hq]
          exact Ideal.mem_span_singleton_self _
        rwa [Ideal.mem_under] at hmem
      have hker : RingHom.ker (redMap p) ≤ P := by
        rw [ker_redMap p]
        exact Ideal.span_singleton_le_iff_mem P |>.mpr hpP
      have hJprime : (Ideal.map (redMap p) P).IsPrime :=
        Ideal.map_isPrime_of_surjective (redMap_surjective p) hker
      have hPmap : Ideal.comap (redMap p) (Ideal.map (redMap p) P) = P := by
        rw [Ideal.comap_map_of_surjective (redMap p) (redMap_surjective p)]
        rw [show Ideal.comap (redMap p) ⊥ = RingHom.ker (redMap p) from rfl, ker_redMap p]
        exact sup_eq_left.mpr (by rw [← ker_redMap p]; exact hker)
      rcases (isPrime_ideal_field_poly (Ideal.map (redMap p) P)).mp hJprime with
        hJ | ⟨g, hgm, hgirr, hJg⟩
      · refine Or.inr (Or.inl ⟨p, hp, ?_⟩)
        rw [← hPmap, hJ, comap_redMap_bot p]
      · obtain ⟨G, hG⟩ := redMap_surjective p g
        refine Or.inr (Or.inr (Or.inr ⟨p, hp, G, ?_, ?_, ?_⟩))
        · rw [hG]; exact hgm
        · rw [hG]; exact hgirr
        · rw [← hPmap, hJg, ← hG, comap_redMap_span p G]
  · rintro (rfl | ⟨p, hp, rfl⟩ | ⟨F, _, _, hFirr, rfl⟩ | ⟨p, hp, G, _, hGirr, rfl⟩)
    · exact Ideal.isPrime_bot
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [← ker_redMap p]
      exact Ideal.IsPrime.comap (redMap p)
    · exact Ideal.isPrime_span_singleton_of_prime hFirr.prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have hprime : (Ideal.span {redMap p G}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime hGirr.prime
      haveI := hprime
      rw [← comap_redMap_span p G]
      exact Ideal.IsPrime.comap (redMap p)

/-- **The key inclusion of the picture**: `(F) ⊆ (p, G)` iff the reduction of `G` mod `p`
divides the reduction of `F` mod `p`. -/
theorem int_poly_span_inclusion {p : ℕ} {F G : ℤ[X]} :
    Ideal.span {F} ≤ Ideal.span {(p : ℤ[X]), G} ↔ redMap p G ∣ redMap p F := by
  constructor
  · intro h
    have hmem : F ∈ Ideal.span {(p : ℤ[X]), G} := h (Ideal.mem_span_singleton_self F)
    rw [← comap_redMap_span p G, Ideal.mem_comap, Ideal.mem_span_singleton] at hmem
    exact hmem
  · intro h
    rw [Ideal.span_singleton_le_iff_mem, ← comap_redMap_span p G, Ideal.mem_comap,
      Ideal.mem_span_singleton]
    exact h

/-- Closed subsets of `Spec ℤ[X]` are finite unions of closures of points (Noetherianity). -/
theorem isClosed_int_poly (Z : Set (PrimeSpectrum ℤ[X])) (hZ : IsClosed Z) :
    ∃ s : Finset (PrimeSpectrum ℤ[X]),
      Z = ⋃ p ∈ (s : Set (PrimeSpectrum ℤ[X])), closure ({p} : Set (PrimeSpectrum ℤ[X])) :=
  exists_finset_closure_singleton_of_isClosed Z hZ

/-- `(0)` is a dense point of `Spec ℤ[X]`. -/
theorem int_poly_generic_dense : Dense ({genericPoint ℤ[X]} : Set (PrimeSpectrum ℤ[X])) := by
  rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
  refine Set.Subset.antisymm (Set.subset_univ _) fun q _ => ?_
  rw [PrimeSpectrum.mem_zeroLocus, genericPoint_asIdeal]
  intro x hx
  have hx0 : x ∈ (⊥ : Ideal ℤ[X]) := hx
  rw [Ideal.mem_bot] at hx0
  rw [hx0]
  exact zero_mem _

/-- The generic point of `Spec ℤ[X]` specialises to every point. -/
theorem int_poly_generic_specializes (Q : PrimeSpectrum ℤ[X]) :
    genericPoint ℤ[X] ⤳ Q := by
  rw [specializes_iff_le, genericPoint_asIdeal]
  exact bot_le

/-- The row `(p)` of the picture: `(p) ⊆ (q)` only when `p = q`. -/
theorem int_poly_span_natCast_le_span_natCast {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Ideal.span {(p : ℤ[X])} ≤ Ideal.span {(q : ℤ[X])} ↔ p = q := by
  constructor
  · intro h
    have hmem : (p : ℤ[X]) ∈ Ideal.span {(q : ℤ[X])} := h (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_span_singleton, natCast_int_poly_eq_C, natCast_int_poly_eq_C] at hmem
    have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff (q : ℤ) (C (p : ℤ))).mp hmem 0
    simp only [Polynomial.coeff_C] at hcoeff
    have hdvd : q ∣ p := Int.natCast_dvd_natCast.mp hcoeff
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd h1 hq.ne_one
    · exact h1.symm
  · rintro rfl
    exact le_refl _

/-- The closed points `(X - a)` of `Spec ℂ[X]` are closed. -/
theorem complexPoint_isClosed (a : ℂ) :
    IsClosed ({complexPoint a} : Set (PrimeSpectrum ℂ[X])) :=
  (isClosed_singleton_iff _).mpr (Ideal.IsPrime.isMaximal (complexPoint a).isPrime (by
    rw [complexPoint_asIdeal]
    intro hbot
    have hmem : (X - C a : ℂ[X]) ∈ (⊥ : Ideal ℂ[X]) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_bot] at hmem
    have hzero : (X - C a : ℂ[X]) = 0 := by simpa using hmem
    have hdeg : (X - C a : ℂ[X]).degree = 1 := Polynomial.degree_X_sub_C a
    rw [hzero] at hdeg
    exact absurd hdeg (by simp)))

/-- The closed points `(X - a)` and `(X² + bX + c)` of `Spec ℝ[X]` are closed. -/
theorem realPoint_isClosed (a : ℝ) :
    IsClosed ({realPoint a} : Set (PrimeSpectrum ℝ[X])) := by
  refine (isClosed_singleton_iff _).mpr (Ideal.IsPrime.isMaximal (realPoint a).isPrime ?_)
  intro hbot
  have hmem : (X - C a : ℝ[X]) ∈ (⊥ : Ideal ℝ[X]) := by
    rw [← hbot]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  have hzero : (X - C a : ℝ[X]) = 0 := by simpa using hmem
  have hdeg : (X - C a : ℝ[X]).degree = 1 := Polynomial.degree_X_sub_C a
  rw [hzero] at hdeg
  exact absurd hdeg (by simp)

theorem realQuad_isClosed (b c : ℝ) (h : b ^ 2 - 4 * c < 0) :
    IsClosed ({realQuad b c h} : Set (PrimeSpectrum ℝ[X])) := by
  refine (isClosed_singleton_iff _).mpr (Ideal.IsPrime.isMaximal (realQuad b c h).isPrime ?_)
  intro hbot
  have hmem : (X ^ 2 + C b * X + C c : ℝ[X]) ∈ (⊥ : Ideal ℝ[X]) := by
    rw [← hbot]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  have hdeg : (0 : ℝ[X]).natDegree = 2 := by
    rw [← hmem]
    simpa using natDegree_quadratic (a := (1 : ℝ)) (b := b) (c := c) one_ne_zero
  simp at hdeg


/-- `(F) ⊆ (F')` iff `F'` divides `F`. -/
theorem int_poly_span_le_span_iff_dvd {F F' : ℤ[X]} :
    Ideal.span {F} ≤ Ideal.span {F'} ↔ F' ∣ F := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]

/-- Summary of the specialisation picture of `Spec ℤ[X]`: `(0)` is dense and specialises to
everything, `(p)` only to itself among the primes contracting to `(p)`, and `(F) ⊆ (p, G)`
exactly when the reduction of `G` modulo `p` divides that of `F`. -/
theorem int_poly_diagram :
    Dense ({genericPoint ℤ[X]} : Set (PrimeSpectrum ℤ[X])) ∧
      (∀ Q : PrimeSpectrum ℤ[X], genericPoint ℤ[X] ⤳ Q) ∧
      (∀ (F : ℤ[X]) (p : ℕ) (G : ℤ[X]),
        Ideal.span {F} ≤ Ideal.span {(p : ℤ[X]), G} ↔ redMap p G ∣ redMap p F) ∧
      (∀ (p q : ℕ), p.Prime → q.Prime →
        (Ideal.span {(p : ℤ[X])} ≤ Ideal.span {(q : ℤ[X])} ↔ p = q)) ∧
      (∀ (Z : Set (PrimeSpectrum ℤ[X])), IsClosed Z →
        ∃ s : Finset (PrimeSpectrum ℤ[X]),
          Z = ⋃ P ∈ (s : Set (PrimeSpectrum ℤ[X])),
            closure ({P} : Set (PrimeSpectrum ℤ[X]))) := by
  refine ⟨int_poly_generic_dense, int_poly_generic_specializes, ?_, ?_, ?_⟩
  · intro F p G
    exact int_poly_span_inclusion
  · intro p q hp hq
    exact int_poly_span_natCast_le_span_natCast hp hq
  · intro Z hZ
    exact isClosed_int_poly Z hZ


/-- The points `(p, G)` of the picture are closed: their quotient is the field
`(ℤ/p)[x]/(g)`. -/
theorem int_poly_isMaximal_span {p : ℕ} (hp : p.Prime) {G : ℤ[X]}
    (hGirr : Irreducible (redMap p G)) :
    (Ideal.span {(p : ℤ[X]), G}).IsMaximal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hG0 : redMap p G ≠ 0 := irreducible_ne_zero' hGirr
  have hmax : Ideal.IsMaximal (Ideal.span {redMap p G}) :=
    (Ideal.irreducible_iff_isMaximal_span_singleton hG0).mp hGirr
  rw [← comap_redMap_span p G]
  exact Ideal.comap_isMaximal_of_surjective (f := redMap p) (redMap_surjective p)
    (K := Ideal.span {redMap p G}) (H := hmax)


/-- The zero ideal is not maximal in `K[x]` for a field `K`. -/
theorem bot_not_maximal_poly {K : Type*} [Field K] : ¬ (⊥ : Ideal K[X]).IsMaximal := by
  intro hmax
  have hXirr : Irreducible (X : K[X]) := by simpa using irreducible_X_sub_C (0 : K)
  have hprime : (Ideal.span {(X : K[X])}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hXirr.prime
  have hlt : (⊥ : Ideal K[X]) < Ideal.span {(X : K[X])} := by
    rw [bot_lt_iff_ne_bot]
    intro hbot
    have hmem : (X : K[X]) ∈ (⊥ : Ideal K[X]) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_bot] at hmem
    have hnd : (X : K[X]).natDegree = 1 := Polynomial.natDegree_X
    rw [hmem] at hnd
    simp at hnd
  exact hlt.ne (hmax.eq_of_le hprime.ne_top bot_le)

/-- The closed points of `Spec ℂ[x]` are exactly the `(x - a)`. -/
theorem isClosed_singleton_complex_iff (P : PrimeSpectrum ℂ[X]) :
    IsClosed ({P} : Set (PrimeSpectrum ℂ[X])) ↔ ∃ a : ℂ, P = complexPoint a := by
  constructor
  · intro hcl
    have hmax : P.asIdeal.IsMaximal := (isClosed_singleton_iff P).mp hcl
    have hne : P.asIdeal ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmax
      exact bot_not_maximal_poly hmax
    rcases (isPrime_ideal_complex_poly P.asIdeal).mp P.isPrime with h | ⟨a, ha⟩
    · exact absurd h hne
    · exact ⟨a, PrimeSpectrum.ext (by rw [complexPoint_asIdeal]; exact ha)⟩
  · rintro ⟨a, rfl⟩
    exact complexPoint_isClosed a

/-- The closed points of `Spec ℝ[x]` are exactly the `(x - a)` and the `(x² + bx + c)` with
`b² - 4c < 0`. -/
theorem isClosed_singleton_real_iff (P : PrimeSpectrum ℝ[X]) :
    IsClosed ({P} : Set (PrimeSpectrum ℝ[X])) ↔
      (∃ a : ℝ, P = realPoint a) ∨
        (∃ (b c : ℝ) (h : b ^ 2 - 4 * c < 0), P = realQuad b c h) := by
  constructor
  · intro hcl
    have hmax : P.asIdeal.IsMaximal := (isClosed_singleton_iff P).mp hcl
    have hne : P.asIdeal ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmax
      exact bot_not_maximal_poly hmax
    rcases (isPrime_ideal_real_poly P.asIdeal).mp P.isPrime with h | ⟨a, ha⟩ | ⟨b, c, hbc, hP⟩
    · exact absurd h hne
    · exact Or.inl ⟨a, PrimeSpectrum.ext (by simpa [realPoint] using ha)⟩
    · exact Or.inr ⟨b, c, hbc, PrimeSpectrum.ext (by simpa [realQuad] using hP)⟩
  · rintro (⟨a, rfl⟩ | ⟨b, c, h, rfl⟩)
    · exact realPoint_isClosed a
    · exact realQuad_isClosed b c h


/-- The closed points of `Spec ℤ` are exactly the `(p)`. -/
theorem isClosed_singleton_int_iff (P : PrimeSpectrum ℤ) :
    IsClosed ({P} : Set (PrimeSpectrum ℤ)) ↔ ∃ (p : ℕ) (hp : p.Prime), P = intPoint p hp := by
  have hb : ¬ (⊥ : Ideal ℤ).IsMaximal := by
    intro hmax
    have hprime : (Ideal.span {(2 : ℤ)}).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime
        (Int.prime_iff_natAbs_prime.mpr (by norm_num))
    have hlt : (⊥ : Ideal ℤ) < Ideal.span {(2 : ℤ)} := by
      rw [bot_lt_iff_ne_bot]
      intro hb'
      have hmem : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [← hb']
        exact Ideal.mem_span_singleton_self _
      rw [Ideal.mem_bot] at hmem
      omega
    exact hlt.ne (hmax.eq_of_le hprime.ne_top bot_le)
  constructor
  · intro hcl
    have hmax : P.asIdeal.IsMaximal := (isClosed_singleton_iff P).mp hcl
    rcases int_spec_cases P with h | ⟨p, hp, hP⟩
    · rw [h] at hmax
      exact absurd hmax hb
    · exact ⟨p, hp, hP⟩
  · rintro ⟨p, hp, rfl⟩
    exact (isClosed_singleton_iff _).mpr (Ideal.IsPrime.isMaximal (intPoint p hp).isPrime (by
      rw [intPoint_asIdeal]
      intro hbot
      have hmem : (p : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [← hbot]
        exact Ideal.mem_span_singleton_self _
      rw [Ideal.mem_bot] at hmem
      exact hp.ne_zero (by exact_mod_cast hmem)))


/-! ### 6b. The three non-maximal rows of the picture -/

/-- For every non-zero integer there is a prime that does not divide it. -/
theorem exists_prime_not_dvd {n : ℤ} (hn : n ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ ((p : ℤ) ∣ n) := by
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  refine ⟨p, hpprime, ?_⟩
  intro hdvd
  have hdvd' : (p : ℤ) ∣ (n.natAbs : ℤ) := by
    rcases Int.natAbs_eq n with h | h
    · rwa [h] at hdvd
    · rw [h] at hdvd
      exact dvd_neg.mp hdvd
  have hnat : p ∣ n.natAbs := Int.natCast_dvd_natCast.mp hdvd'
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hnat
  omega

/-- Reduction modulo `p` preserves the degree when `p` does not divide the leading
coefficient. -/
theorem natDegree_redMap_eq {p : ℕ} {F : ℤ[X]} (hp : ¬ ((p : ℤ) ∣ F.leadingCoeff))
    (_hF : F ≠ 0) : (redMap p F).natDegree = F.natDegree := by
  rw [redMap_apply, Polynomial.natDegree_map_eq_iff]
  left
  intro hzero
  exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd F.leadingCoeff p).mp hzero)

theorem natDegree_units_poly {K : Type*} [Field K] (u : K[X]ˣ) : (↑u : K[X]).natDegree = 0 := by
  have hu : (↑u : K[X]) ≠ 0 := u.isUnit.ne_zero
  have hu' : (↑u⁻¹ : K[X]) ≠ 0 := u⁻¹.isUnit.ne_zero
  have h := Polynomial.natDegree_mul hu hu'
  rw [Units.mul_inv, Polynomial.natDegree_one] at h
  omega

theorem multiset_dvd_prod {M : Type*} [CommMonoid M] {s : Multiset M} {a : M} (h : a ∈ s) :
    a ∣ s.prod := by
  induction s using Multiset.induction with
  | empty => simp at h
  | cons b s ih =>
    rw [Multiset.prod_cons]
    rcases Multiset.mem_cons.mp h with rfl | h'
    · exact ⟨s.prod, rfl⟩
    · exact (ih h').trans ⟨b, mul_comm _ _⟩

/-- A non-constant polynomial over a field has a monic irreducible divisor. -/
theorem exists_monic_irreducible_dvd_of_natDegree_pos {K : Type*} [Field K] {f : K[X]}
    (hf : 0 < f.natDegree) : ∃ g : K[X], g.Monic ∧ Irreducible g ∧ g ∣ f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨s, hsirr, hassoc⟩ := WfDvdMonoid.exists_factors f hf0
  have hsne : s ≠ 0 := by
    rintro rfl
    rw [Multiset.prod_zero] at hassoc
    obtain ⟨u, hu⟩ := hassoc
    have hdeg : f.natDegree = 0 := by
      rw [← hu, one_mul]
      exact natDegree_units_poly u
    omega
  obtain ⟨g, hgs⟩ := Multiset.exists_mem_of_ne_zero hsne
  have hgirr : Irreducible g := hsirr g hgs
  have hg0 : g ≠ 0 := irreducible_ne_zero' hgirr
  have hgdvd : g ∣ f := by
    refine (multiset_dvd_prod hgs).trans ?_
    obtain ⟨u, hu⟩ := hassoc
    exact ⟨↑u, hu.symm⟩
  have hc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  refine ⟨g * C g.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hg0, ?_, ?_⟩
  · have hunit : IsUnit (C g.leadingCoeff⁻¹ : K[X]) :=
      isUnit_C.mpr (inv_ne_zero hc0).isUnit
    have hspan : Ideal.span {g} = Ideal.span {g * C g.leadingCoeff⁻¹} :=
      (Ideal.span_singleton_mul_right_unit hunit g).symm
    have hprime : (Ideal.span {g * C g.leadingCoeff⁻¹}).IsPrime :=
      hspan ▸ Ideal.isPrime_span_singleton_of_prime hgirr.prime
    exact (Ideal.span_singleton_prime (monic_mul_leadingCoeff_inv hg0).ne_zero).mp hprime |>.irreducible
  · refine (show g * C g.leadingCoeff⁻¹ ∣ g from ⟨C g.leadingCoeff, ?_⟩).trans hgdvd
    rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc0, Polynomial.C_1, mul_one]

/-- **The book's strict containment**: for a primitive irreducible `F` of positive degree there
are a prime `p` not dividing the leading coefficient of `F` and an irreducible factor `g` of
the reduction of `F` mod `p`; lifting `g` to `G ∈ ℤ[x]` gives `(F) ⊊ (p, G)` with `(p, G)`
maximal. -/
theorem int_poly_exists_strict_super {F : ℤ[X]} (hFprim : F.IsPrimitive)
    (hFdeg : 0 < F.natDegree) (_hFirr : Irreducible F) :
    ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]), (redMap p G).Monic ∧
      Irreducible (redMap p G) ∧ Ideal.span {F} < Ideal.span {(p : ℤ[X]), G} := by
  have hF0 : F ≠ 0 := hFprim.ne_zero
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  obtain ⟨p, hpprime, hpdvd⟩ := exists_prime_not_dvd hlc
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hdeg : 0 < (redMap p F).natDegree := by
    rw [natDegree_redMap_eq hpdvd hF0]
    exact hFdeg
  obtain ⟨g, hgmonic, hgirr, hgdvd⟩ :=
    exists_monic_irreducible_dvd_of_natDegree_pos hdeg
  obtain ⟨G, hG⟩ := redMap_surjective p g
  have hGirr : Irreducible (redMap p G) := by rw [hG]; exact hgirr
  have hGmonic : (redMap p G).Monic := by rw [hG]; exact hgmonic
  have hle : Ideal.span {F} ≤ Ideal.span {(p : ℤ[X]), G} := by
    rw [int_poly_span_inclusion, hG]
    exact hgdvd
  have hpnot : (p : ℤ[X]) ∉ Ideal.span {F} := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hpn : (p : ℤ[X]) ≠ 0 := by
      rw [natCast_int_poly_eq_C]
      intro h
      have hc := congrArg (fun f : ℤ[X] => f.coeff 0) h
      simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at hc
      exact hpprime.ne_zero (by exact_mod_cast hc)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hpn hq
    have hdeg' : ((p : ℕ) : ℤ[X]).natDegree = F.natDegree + q.natDegree := by
      rw [hq, Polynomial.natDegree_mul hF0 hq0]
    have hpdeg : ((p : ℕ) : ℤ[X]).natDegree = 0 := by
      rw [natCast_int_poly_eq_C]
      exact Polynomial.natDegree_C _
    omega
  refine ⟨p, hpprime, G, hGmonic, hGirr, lt_of_le_of_ne hle ?_⟩
  intro heq
  exact hpnot (heq.symm ▸ Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩)

/-- `(0)` is not maximal in `Spec ℤ[x]`. -/
theorem int_poly_bot_not_maximal : ¬ (⊥ : Ideal ℤ[X]).IsMaximal := by
  have hXred : Irreducible (redMap 2 (X : ℤ[X])) := by
    rw [redMap_apply, Polynomial.map_X]
    simpa using irreducible_X_sub_C (0 : ZMod 2)
  have hmax : (Ideal.span {(2 : ℤ[X]), (X : ℤ[X])}).IsMaximal :=
    int_poly_isMaximal_span (by norm_num) hXred
  have hlt : (⊥ : Ideal ℤ[X]) < Ideal.span {(2 : ℤ[X]), (X : ℤ[X])} := by
    rw [bot_lt_iff_ne_bot]
    intro hb
    have hmem : (2 : ℤ[X]) ∈ (⊥ : Ideal ℤ[X]) := by
      rw [← hb]
      exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    rw [Ideal.mem_bot] at hmem
    have h2 : (2 : ℤ[X]) ≠ 0 := by
      intro h
      have hc := congrArg (fun f : ℤ[X] => f.coeff 0) h
      norm_num at hc
    exact h2 hmem
  intro hbotmax
  exact hlt.ne (hbotmax.eq_of_le hmax.ne_top hlt.le)

/-- `(p)` is not maximal in `Spec ℤ[x]`. -/
theorem int_poly_span_natCast_not_maximal {p : ℕ} (hp : p.Prime) :
    ¬ (Ideal.span {(p : ℤ[X])}).IsMaximal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXred : Irreducible (redMap p (X : ℤ[X])) := by
    rw [redMap_apply, Polynomial.map_X]
    simpa using irreducible_X_sub_C (0 : ZMod p)
  have hmax : (Ideal.span {(p : ℤ[X]), (X : ℤ[X])}).IsMaximal :=
    int_poly_isMaximal_span hp hXred
  have hXnot : (X : ℤ[X]) ∉ Ideal.span {(p : ℤ[X])} := by
    intro hmem
    rw [Ideal.mem_span_singleton, natCast_int_poly_eq_C, Polynomial.C_dvd_iff_dvd_coeff] at hmem
    have h1 := hmem 1
    simp only [Polynomial.coeff_X_one] at h1
    exact hp.ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp h1))
  have hle : Ideal.span {(p : ℤ[X])} ≤ Ideal.span {(p : ℤ[X]), (X : ℤ[X])} :=
    Ideal.span_singleton_le_iff_mem _ |>.mpr (Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩)
  have hlt : Ideal.span {(p : ℤ[X])} < Ideal.span {(p : ℤ[X]), (X : ℤ[X])} :=
    lt_of_le_of_ne hle fun heq =>
      hXnot (heq.symm ▸ Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩)
  intro hs
  exact hlt.ne (hs.eq_of_le hmax.ne_top hlt.le)

/-- A primitive irreducible `F` of positive degree is not maximal in `Spec ℤ[x]`: the book's
strict containment `(F) ⊊ (p, G)`. -/
theorem int_poly_span_primitive_not_maximal {F : ℤ[X]} (hFprim : F.IsPrimitive)
    (hFdeg : 0 < F.natDegree) (hFirr : Irreducible F) :
    ¬ (Ideal.span {F}).IsMaximal := by
  obtain ⟨p, hp, G, _, hGirr, hlt⟩ := int_poly_exists_strict_super hFprim hFdeg hFirr
  intro hmax
  exact hlt.ne (hmax.eq_of_le (int_poly_isMaximal_span hp hGirr).ne_top hlt.le)

/-- `(0) ⊊ (p)`: the generic point is strictly below the `(p)` row. -/
theorem int_poly_bot_lt_span_natCast {p : ℕ} (hp : p.Prime) :
    (⊥ : Ideal ℤ[X]) < Ideal.span {(p : ℤ[X])} := by
  rw [bot_lt_iff_ne_bot]
  intro hb
  have hmem : (p : ℤ[X]) ∈ (⊥ : Ideal ℤ[X]) := by
    rw [← hb]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  have hpn : (p : ℤ[X]) ≠ 0 := by
    rw [natCast_int_poly_eq_C]
    intro h
    have hc := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    exact hp.ne_zero (by exact_mod_cast hc)
  exact hpn hmem

/-- `(0) ⊊ (F)`: the generic point is strictly below every non-zero principal prime. -/
theorem int_poly_bot_lt_span_primitive {F : ℤ[X]} (hF : F ≠ 0) :
    (⊥ : Ideal ℤ[X]) < Ideal.span {F} := by
  rw [bot_lt_iff_ne_bot]
  intro hb
  have hmem : F ∈ (⊥ : Ideal ℤ[X]) := by
    rw [← hb]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  exact hF hmem

/-- `(p) ⊊ (p, G)` whenever the reduction of `G` is non-zero. -/
theorem int_poly_span_natCast_lt_span_pair {p : ℕ} {G : ℤ[X]} (hG : redMap p G ≠ 0) :
    Ideal.span {(p : ℤ[X])} < Ideal.span {(p : ℤ[X]), G} := by
  have hnot : G ∉ Ideal.span {(p : ℤ[X])} := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨q, hq⟩ := hmem
    apply hG
    calc redMap p G = redMap p ((p : ℤ[X]) * q) := by rw [hq]
      _ = redMap p (p : ℤ[X]) * redMap p q := by rw [map_mul]
      _ = 0 := by rw [redMap_natCast, zero_mul]
  refine lt_of_le_of_ne (Ideal.span_singleton_le_iff_mem _ |>.mpr (Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩)) ?_
  intro heq
  exact hnot (heq.symm ▸ Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩)

/-- A strict inclusion of prime ideals gives a strict specialisation. -/
theorem int_poly_specializes_of_lt {P Q : PrimeSpectrum ℤ[X]} (h : P.asIdeal < Q.asIdeal) :
    P ⤳ Q ∧ ¬ (Q ⤳ P) := by
  refine ⟨specializes_iff_le.mpr h.le, ?_⟩
  intro hQP
  have hle' : Q.asIdeal ≤ P.asIdeal := specializes_iff_le.mp hQP
  exact h.ne (le_antisymm h.le hle')


/-- **The full picture of `Spec ℤ[x]`**, including the three non-maximal rows and the strict
containments that distinguish them: `(0)` is dense and specialises to everything; `(0)`, `(p)`
and primitive irreducible `(F)` are **not** maximal; for `(F)` the book's construction gives a
maximal `(p, G)` with `(F) ⊊ (p, G)`; and every closed set is a finite union of point closures. -/
theorem int_poly_diagram_full :
    Dense ({genericPoint ℤ[X]} : Set (PrimeSpectrum ℤ[X])) ∧
      (∀ Q : PrimeSpectrum ℤ[X], genericPoint ℤ[X] ⤳ Q) ∧
      (∀ (F : ℤ[X]) (p : ℕ) (G : ℤ[X]),
        Ideal.span {F} ≤ Ideal.span {(p : ℤ[X]), G} ↔ redMap p G ∣ redMap p F) ∧
      (¬ (⊥ : Ideal ℤ[X]).IsMaximal) ∧
      (∀ (p : ℕ), p.Prime → ¬ (Ideal.span {(p : ℤ[X])}).IsMaximal) ∧
      (∀ (F : ℤ[X]), F.IsPrimitive → 0 < F.natDegree → Irreducible F →
        ¬ (Ideal.span {F}).IsMaximal) ∧
      (∀ (F : ℤ[X]), F.IsPrimitive → 0 < F.natDegree → Irreducible F →
        ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]), (redMap p G).Monic ∧
          Irreducible (redMap p G) ∧ Ideal.span {F} < Ideal.span {(p : ℤ[X]), G} ∧
          (Ideal.span {(p : ℤ[X]), G}).IsMaximal) ∧
      (∀ (Z : Set (PrimeSpectrum ℤ[X])), IsClosed Z →
        ∃ s : Finset (PrimeSpectrum ℤ[X]),
          Z = ⋃ P ∈ (s : Set (PrimeSpectrum ℤ[X])),
            closure ({P} : Set (PrimeSpectrum ℤ[X]))) := by
  refine ⟨int_poly_generic_dense, int_poly_generic_specializes, ?_,
    int_poly_bot_not_maximal, ?_, ?_, ?_, ?_⟩
  · intro F p G
    exact int_poly_span_inclusion
  · intro p hp
    exact int_poly_span_natCast_not_maximal hp
  · intro F h1 h2 h3
    exact int_poly_span_primitive_not_maximal h1 h2 h3
  · intro F h1 h2 h3
    obtain ⟨p, hp, G, hGm, hGirr, hlt⟩ := int_poly_exists_strict_super h1 h2 h3
    exact ⟨p, hp, G, hGm, hGirr, hlt, int_poly_isMaximal_span hp hGirr⟩
  · intro Z hZ
    exact isClosed_int_poly Z hZ

/-! ## 6c. Point closures and closed points of `Spec ℤ[x]`

The picture of `Spec ℤ[x]` in Atiyah–Macdonald, Exercise 1.16 has four rows — `(0)`, `(p)`,
`(f)` and `(p, g)` — and its arrows record containment of prime ideals.  The material above
proves the classification of the primes of `ℤ[x]`, that the `(p, G)` row is maximal and that the
other three rows are not.  What the picture still asserts and what is added here:

* the closed points of `Spec ℤ[x]` are exactly the points of the bottom row `(p, G)`
  (`int_poly_isClosed_singleton_iff`, the `ℤ[x]` analogue of `isClosed_singleton_int_iff`,
  `isClosed_singleton_complex_iff` and `isClosed_singleton_real_iff`);
* the closure of `(p)` is `(p)` together with all `(p, G)` over `p`
  (`int_poly_span_natCast_le_iff`);
* the closure of `(f)` is `(f)` together with the closed points `(p, G)` with `g ∣ f mod p`
  (`int_poly_span_le_iff`);
* a maximal point specialises only to itself (`int_poly_span_pair_le_iff`);
* `(p)` and `(f)` are incomparable, so no arrow joins the two middle rows
  (`int_poly_span_natCast_not_le_span`, `int_poly_span_not_le_natCast`).
-/

section IntPolyRows

/-- A monic irreducible polynomial over a field has positive degree. -/
theorem natDegree_pos_of_monic_irreducible {K : Type*} [Field K] {g : K[X]}
    (hmon : g.Monic) (hirr : Irreducible g) : 0 < g.natDegree := by
  rcases Nat.eq_zero_or_pos g.natDegree with h | h
  · exfalso
    rw [hmon.natDegree_eq_zero] at h
    rw [h] at hirr
    exact hirr.not_isUnit isUnit_one
  · exact h

/-- A polynomial over a field dividing a non-zero constant has degree zero. -/
theorem natDegree_eq_zero_of_dvd_C {K : Type*} [Field K] {g : K[X]} {c : K} (hc : c ≠ 0)
    (h : g ∣ C c) : g.natDegree = 0 := by
  have hC0 : (C c : K[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hle : g.natDegree ≤ (C c : K[X]).natDegree := Polynomial.natDegree_le_of_dvd h hC0
  rw [Polynomial.natDegree_C] at hle
  omega

/-- `(p)` is not contained in `(F)` for `F` of positive degree: the two middle rows of the
picture are incomparable. -/
theorem int_poly_natCast_not_mem_span {p : ℕ} (hp : p.Prime) {F : ℤ[X]}
    (hdeg : 0 < F.natDegree) : (p : ℤ[X]) ∉ Ideal.span {F} := by
  rw [Ideal.mem_span_singleton]
  intro hdvd
  have hp0 : (p : ℤ[X]) ≠ 0 := by
    rw [natCast_int_poly_eq_C]
    exact Polynomial.C_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp0
  rw [natCast_int_poly_eq_C, Polynomial.natDegree_C] at hle
  omega

/-- A primitive polynomial does not lie in `(p)`: the other direction of the incomparability. -/
theorem int_poly_mem_natCast_not_primitive {p : ℕ} (hp : p.Prime) {F : ℤ[X]}
    (hprim : F.IsPrimitive) : F ∉ Ideal.span {(p : ℤ[X])} := by
  intro hmem
  rw [Ideal.mem_span_singleton, natCast_int_poly_eq_C] at hmem
  have hunit : IsUnit (p : ℤ) := hprim (p : ℤ) hmem
  have hdvd1 : (p : ℤ) ∣ 1 := isUnit_iff_dvd_one.mp hunit
  exact hp.ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdvd1))

/-- **The closure of the `(p)` row**: the primes containing `(p)` are `(p)` itself and the points
`(p, G)` with `g = redMap p G` monic and irreducible. -/
theorem int_poly_span_natCast_le_iff {p : ℕ} (hp : p.Prime) (Q : PrimeSpectrum ℤ[X]) :
    Ideal.span {(p : ℤ[X])} ≤ Q.asIdeal ↔
      Q.asIdeal = Ideal.span {(p : ℤ[X])} ∨
        ∃ (G : ℤ[X]) (_ : (redMap p G).Monic) (_ : Irreducible (redMap p G)),
          Q.asIdeal = Ideal.span {(p : ℤ[X]), G} := by
  constructor
  · intro h
    rcases (isPrime_ideal_int_poly Q.asIdeal).mp Q.isPrime with
      hbot | ⟨q, hq, hQ⟩ | ⟨F, _hFprim, hFdeg, _hFirr, hQ⟩ | ⟨q, hq, G, hGmon, hGirr, hQ⟩
    · rw [hbot] at h
      have hmem : (p : ℤ[X]) ∈ (⊥ : Ideal ℤ[X]) := h (Ideal.mem_span_singleton_self _)
      rw [Ideal.mem_bot, natCast_int_poly_eq_C] at hmem
      have hc := congrArg (fun f : ℤ[X] => f.coeff 0) hmem
      simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at hc
      exact absurd hc (by exact_mod_cast hp.ne_zero)
    · left
      have hle : Ideal.span {(p : ℤ[X])} ≤ Ideal.span {(q : ℤ[X])} := hQ ▸ h
      have hpq : p = q := (int_poly_span_natCast_le_span_natCast hp hq).mp hle
      rw [hQ, hpq]
    · exact absurd (hQ ▸ h (Ideal.mem_span_singleton_self (p : ℤ[X])))
        (int_poly_natCast_not_mem_span hp hFdeg)
    · haveI : Fact q.Prime := ⟨hq⟩
      by_cases hpq : p = q
      · obtain rfl : p = q := hpq
        exact Or.inr ⟨G, hGmon, hGirr, hQ⟩
      · exfalso
        have hle : Ideal.span {(p : ℤ[X])} ≤ Ideal.span {(q : ℤ[X]), G} := hQ ▸ h
        have hmem : (p : ℤ[X]) ∈ Ideal.span {(q : ℤ[X]), G} :=
          hle (Ideal.mem_span_singleton_self _)
        rw [← comap_redMap_span q G, Ideal.mem_comap, Ideal.mem_span_singleton] at hmem
        have hconst : redMap q (p : ℤ[X]) = C (((p : ℤ) : ZMod q)) := by
          rw [natCast_int_poly_eq_C, redMap_apply, Polynomial.map_C]
          simp
        rw [hconst] at hmem
        have hc : (((p : ℤ) : ZMod q)) ≠ 0 := by
          intro hzero
          have hdvd : (q : ℤ) ∣ (p : ℤ) :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) q).mp hzero
          have hdvd' : q ∣ p := Int.natCast_dvd_natCast.mp hdvd
          rcases (Nat.dvd_prime hp).mp hdvd' with h1 | h1
          · exact hq.ne_one h1
          · exact hpq h1.symm
        have hdeg0 : (redMap q G).natDegree = 0 := natDegree_eq_zero_of_dvd_C hc hmem
        have hpos : 0 < (redMap q G).natDegree := natDegree_pos_of_monic_irreducible hGmon hGirr
        omega
  · rintro (hQ | ⟨G, _hGmon, _hGirr, hQ⟩)
    · rw [hQ]
    · rw [hQ]
      exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩)

/-- **The closure of the `(f)` row**: the primes containing a primitive irreducible `F` of positive
degree are `(F)` itself and the closed points `(p, G)` whose reduction divides `f mod p`. -/
theorem int_poly_span_le_iff {F : ℤ[X]} (hFprim : F.IsPrimitive) (_hFdeg : 0 < F.natDegree)
    (hFirr : Irreducible F) (Q : PrimeSpectrum ℤ[X]) :
    Ideal.span {F} ≤ Q.asIdeal ↔
      Q.asIdeal = Ideal.span {F} ∨
        ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]) (_ : (redMap p G).Monic)
          (_ : Irreducible (redMap p G)),
          Q.asIdeal = Ideal.span {(p : ℤ[X]), G} ∧ redMap p G ∣ redMap p F := by
  constructor
  · intro h
    rcases (isPrime_ideal_int_poly Q.asIdeal).mp Q.isPrime with
      hbot | ⟨q, hq, hQ⟩ | ⟨F', _hF'prim, _hF'deg, hF'irr, hQ⟩ | ⟨q, hq, G, hGmon, hGirr, hQ⟩
    · exfalso
      rw [hbot] at h
      exact hFprim.ne_zero (Ideal.mem_bot.mp (h (Ideal.mem_span_singleton_self F)))
    · exfalso
      exact int_poly_mem_natCast_not_primitive hq hFprim
        (hQ ▸ h (Ideal.mem_span_singleton_self F))
    · left
      have hmem : F ∈ Ideal.span {F'} := hQ ▸ h (Ideal.mem_span_singleton_self F)
      have hdvd : F' ∣ F := (Ideal.mem_span_singleton).mp hmem
      have hassoc : Associated F' F := Irreducible.associated_of_dvd hF'irr hFirr hdvd
      rw [hQ, Ideal.span_singleton_eq_span_singleton.mpr hassoc]
    · exact Or.inr ⟨q, hq, G, hGmon, hGirr, hQ, int_poly_span_inclusion.mp (hQ ▸ h)⟩
  · rintro (hQ | ⟨p, _hp, G, _hGmon, _hGirr, hQ, hdvd⟩)
    · rw [hQ]
    · rw [hQ]
      exact int_poly_span_inclusion.mpr hdvd

/-- The `(p, G)` row is closed: a maximal ideal specialises only to itself. -/
theorem int_poly_span_pair_le_iff {p : ℕ} (hp : p.Prime) {G : ℤ[X]}
    (hGirr : Irreducible (redMap p G)) (Q : PrimeSpectrum ℤ[X]) :
    Ideal.span {(p : ℤ[X]), G} ≤ Q.asIdeal ↔ Q.asIdeal = Ideal.span {(p : ℤ[X]), G} := by
  constructor
  · intro h
    exact (Ideal.IsMaximal.eq_of_le (int_poly_isMaximal_span hp hGirr) Q.isPrime.ne_top h).symm
  · rintro hQ
    rw [hQ]

/-- **The closed points of `Spec ℤ[x]`** are exactly the points of the bottom row `(p, G)`. -/
theorem int_poly_isClosed_singleton_iff (P : PrimeSpectrum ℤ[X]) :
    IsClosed ({P} : Set (PrimeSpectrum ℤ[X])) ↔
      ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]) (_ : (redMap p G).Monic)
        (_ : Irreducible (redMap p G)), P.asIdeal = Ideal.span {(p : ℤ[X]), G} := by
  constructor
  · intro hcl
    have hmax : P.asIdeal.IsMaximal := (isClosed_singleton_iff P).mp hcl
    rcases (isPrime_ideal_int_poly P.asIdeal).mp P.isPrime with
      hbot | ⟨p, hp, hP⟩ | ⟨F, hFprim, hFdeg, hFirr, hP⟩ | ⟨p, hp, G, hGmon, hGirr, hP⟩
    · rw [hbot] at hmax
      exact absurd hmax int_poly_bot_not_maximal
    · rw [hP] at hmax
      exact absurd hmax (int_poly_span_natCast_not_maximal hp)
    · rw [hP] at hmax
      exact absurd hmax (int_poly_span_primitive_not_maximal hFprim hFdeg hFirr)
    · exact ⟨p, hp, G, hGmon, hGirr, hP⟩
  · rintro ⟨p, hp, G, _hGmon, hGirr, hP⟩
    refine (isClosed_singleton_iff P).mpr ?_
    rw [hP]
    exact int_poly_isMaximal_span hp hGirr

/-- No arrow joins the `(p)` and `(f)` rows of the picture: `(p) ⊄ (f)`. -/
theorem int_poly_span_natCast_not_le_span {p : ℕ} (hp : p.Prime) {F : ℤ[X]}
    (hFdeg : 0 < F.natDegree) : ¬ (Ideal.span {(p : ℤ[X])} ≤ Ideal.span {F}) :=
  fun h => int_poly_natCast_not_mem_span hp hFdeg (h (Ideal.mem_span_singleton_self _))

/-- No arrow joins the `(f)` and `(p)` rows of the picture: `(f) ⊄ (p)`. -/
theorem int_poly_span_not_le_natCast {p : ℕ} (hp : p.Prime) {F : ℤ[X]} (hFprim : F.IsPrimitive) :
    ¬ (Ideal.span {F} ≤ Ideal.span {(p : ℤ[X])}) :=
  fun h => int_poly_mem_natCast_not_primitive hp hFprim (h (Ideal.mem_span_singleton_self _))

/-- **The four rows of `Spec ℤ[x]` and their closures**, as the book's picture states them: the
generic point specialises to everything, the closure of `(p)` is `(p)` with all `(p, G)`, the
closure of `(f)` is `(f)` with the closed points whose reduction divides `f mod p`, the closed
points are exactly the `(p, G)`, and `(p)` and `(f)` are incomparable. -/
theorem int_poly_picture :
    (∀ Q : PrimeSpectrum ℤ[X], genericPoint ℤ[X] ⤳ Q) ∧
      (∀ (p : ℕ) (_ : p.Prime) (Q : PrimeSpectrum ℤ[X]),
        (Ideal.span {(p : ℤ[X])} ≤ Q.asIdeal) ↔
          (Q.asIdeal = Ideal.span {(p : ℤ[X])} ∨
            ∃ (G : ℤ[X]) (_ : (redMap p G).Monic) (_ : Irreducible (redMap p G)),
              Q.asIdeal = Ideal.span {(p : ℤ[X]), G})) ∧
      (∀ (F : ℤ[X]) (_ : F.IsPrimitive) (_ : 0 < F.natDegree) (_ : Irreducible F)
        (Q : PrimeSpectrum ℤ[X]),
        (Ideal.span {F} ≤ Q.asIdeal) ↔
          (Q.asIdeal = Ideal.span {F} ∨
            ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]) (_ : (redMap p G).Monic)
              (_ : Irreducible (redMap p G)),
              Q.asIdeal = Ideal.span {(p : ℤ[X]), G} ∧ redMap p G ∣ redMap p F)) ∧
      (∀ P : PrimeSpectrum ℤ[X], IsClosed ({P} : Set (PrimeSpectrum ℤ[X])) ↔
        ∃ (p : ℕ) (_ : p.Prime) (G : ℤ[X]) (_ : (redMap p G).Monic)
          (_ : Irreducible (redMap p G)), P.asIdeal = Ideal.span {(p : ℤ[X]), G}) ∧
      (∀ (p : ℕ) (_ : p.Prime) (F : ℤ[X]) (_ : 0 < F.natDegree),
        ¬ (Ideal.span {(p : ℤ[X])} ≤ Ideal.span {F})) ∧
      (∀ (p : ℕ) (_ : p.Prime) (F : ℤ[X]) (_ : F.IsPrimitive),
        ¬ (Ideal.span {F} ≤ Ideal.span {(p : ℤ[X])})) :=
  ⟨int_poly_generic_specializes, fun _p hp Q => int_poly_span_natCast_le_iff hp Q,
    fun _F h1 h2 h3 Q => int_poly_span_le_iff h1 h2 h3 Q, int_poly_isClosed_singleton_iff,
    fun _p hp _F hdeg => int_poly_span_natCast_not_le_span hp hdeg,
    fun _p hp _F hprim => int_poly_span_not_le_natCast hp hprim⟩

end IntPolyRows

/-! ## 6d. Concrete checks that the picture is not vacuous -/

section IntPolyWitnesses

/-- The book's example of an arrow from the `(f)` row to the bottom row: in `ℤ[x]` we have
`x² + 1 = (x + 1)² - 2x`, so `(x² + 1) ⊆ (2, x + 1)`. -/
theorem int_poly_witness_span_le :
    Ideal.span {(X ^ 2 + 1 : ℤ[X])} ≤ Ideal.span {(2 : ℤ[X]), X + 1} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_pair.mpr ⟨-X, X + 1, by ring⟩)

/-- The inclusion above is strict: `2 ∉ (x² + 1)` for degree reasons. -/
theorem int_poly_witness_span_lt :
    Ideal.span {(X ^ 2 + 1 : ℤ[X])} < Ideal.span {(2 : ℤ[X]), X + 1} := by
  refine lt_of_le_of_ne int_poly_witness_span_le ?_
  intro heq
  have h2 : (2 : ℤ[X]) ∈ Ideal.span {(X ^ 2 + 1 : ℤ[X])} := by
    rw [heq]
    exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
  have hdeg : 0 < (X ^ 2 + 1 : ℤ[X]).natDegree := by
    have h2 : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
      simpa using Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : ℤ))
    omega
  exact int_poly_natCast_not_mem_span (p := 2) (by norm_num) hdeg h2

/-- The generic point of `Spec ℤ[x]` is not a closed point. -/
theorem int_poly_generic_not_closed :
    ¬ IsClosed ({genericPoint ℤ[X]} : Set (PrimeSpectrum ℤ[X])) := by
  intro h
  exact int_poly_bot_not_maximal ((isClosed_singleton_iff (genericPoint ℤ[X])).mp h)

end IntPolyWitnesses

#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_witness_span_lt
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_generic_not_closed

#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_natCast_le_iff
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_le_iff
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_pair_le_iff
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_isClosed_singleton_iff
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_natCast_not_le_span
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_not_le_natCast
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_picture

/-! ## 7. Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_int_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_complex_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_real_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_real
#print axioms AtiyahMcdonald69.Ex_1_16.real_spec_subsingleton
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_int
#print axioms AtiyahMcdonald69.Ex_1_16.int_spec_cases
#print axioms AtiyahMcdonald69.Ex_1_16.int_specializes
#print axioms AtiyahMcdonald69.Ex_1_16.intGeneric_dense
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_int
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_complex_poly
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_int_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_complex_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_real_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_real_poly
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_int_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_complex_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_singleton_real_iff
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_real
#print axioms AtiyahMcdonald69.Ex_1_16.real_spec_subsingleton
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_int_poly
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_inclusion
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_generic_dense
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_int_poly
#print axioms AtiyahMcdonald69.Ex_1_16.exists_finset_closure_singleton_of_isClosed
#print axioms AtiyahMcdonald69.Ex_1_16.quasiCompact
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_diagram
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_diagram_full
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_isMaximal_span
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_bot_not_maximal
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_natCast_not_maximal
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_primitive_not_maximal
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_exists_strict_super
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_bot_lt_span_natCast
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_bot_lt_span_primitive
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_span_natCast_lt_span_pair
#print axioms AtiyahMcdonald69.Ex_1_16.int_poly_specializes_of_lt
#print axioms AtiyahMcdonald69.Ex_1_16.specializes_iff_eq_or_generic
#print axioms AtiyahMcdonald69.Ex_1_16.isClosed_iff_finite_or_univ
#print axioms AtiyahMcdonald69.Ex_1_16.isPrime_ideal_field_poly

end AtiyahMcdonald69.Ex_1_16

