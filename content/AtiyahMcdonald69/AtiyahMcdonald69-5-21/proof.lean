import Mathlib
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.MvPolynomial.Localization

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Polynomial

namespace AtiyahMcdonald69.Ex_5_21

/-! ## Atiyah–Macdonald, Chapter 5, Exercise 2 -/

theorem exists_ringHom_comp_eq_of_isIntegral
    {C D : Type*} [CommRing C] [CommRing D] [Nontrivial D]
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (φ : C →+* D) (hφ : φ.IsIntegral) (ρ : C →+* Ω)
    (hker : RingHom.ker φ ≤ RingHom.ker ρ) :
    ∃ ψ : D →+* Ω, ψ.comp φ = ρ := by
  letI : Algebra C D := φ.toAlgebra
  have hφ' : (algebraMap C D).IsIntegral := by rwa [RingHom.algebraMap_toAlgebra]
  haveI : Algebra.IsIntegral C D := algebraMap_isIntegral_iff.mp hφ'
  haveI hkerPrime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ρ) (⊥ : Ideal D) (by
      rw [RingHom.ker_eq_comap_bot]; exact hker)
  haveI := hQprime
  haveI hLies : Q.LiesOver (RingHom.ker ρ) := ⟨hQcomap.symm⟩
  haveI : Algebra.IsIntegral (C ⧸ RingHom.ker ρ) (D ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ρ)
  let ρ' : (C ⧸ RingHom.ker ρ) →+* Ω :=
    Ideal.Quotient.lift (RingHom.ker ρ) ρ (fun a ha => ha)
  have hρ'inj : Function.Injective ρ' :=
    RingHom.lift_injective_of_ker_le_ideal _ _ le_rfl
  letI : Algebra (C ⧸ RingHom.ker ρ) Ω := ρ'.toAlgebra
  haveI : Module.IsTorsionFree (C ⧸ RingHom.ker ρ) Ω := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    exact hρ'inj
  have hfs : FaithfulSMul (C ⧸ RingHom.ker ρ) (D ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (C ⧸ RingHom.ker ρ) (D ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr hfs
  haveI : Algebra.IsAlgebraic (C ⧸ RingHom.ker ρ) (D ⧸ Q) := inferInstance
  let L : (D ⧸ Q) →ₐ[C ⧸ RingHom.ker ρ] Ω := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext c
  have h1 : Ideal.Quotient.mk Q (φ c) =
      algebraMap (C ⧸ RingHom.ker ρ) (D ⧸ Q) (Ideal.Quotient.mk (RingHom.ker ρ) c) := by
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rfl
  have h2 : L (algebraMap (C ⧸ RingHom.ker ρ) (D ⧸ Q) (Ideal.Quotient.mk (RingHom.ker ρ) c))
      = algebraMap (C ⧸ RingHom.ker ρ) Ω (Ideal.Quotient.mk (RingHom.ker ρ) c) :=
    L.commutes _
  have h3 : algebraMap (C ⧸ RingHom.ker ρ) Ω (Ideal.Quotient.mk (RingHom.ker ρ) c) = ρ c := rfl
  show L (Ideal.Quotient.mk Q (φ c)) = ρ c
  rw [h1, h2, h3]

/-! ## Elementary lemmas on leading coefficients -/

lemma leadingCoeff_C_mul {R : Type*} [CommRing R] [IsDomain R] {p : R[X]} {c : R}
    (hc : c ≠ 0) : (C c * p).leadingCoeff = c * p.leadingCoeff := by
  have hdeg : (C c * p).natDegree = p.natDegree := natDegree_C_mul hc
  rw [leadingCoeff, hdeg, coeff_C_mul, ← leadingCoeff]

/-- If `p.map φ = C (φ r) * q` with `q` monic and `φ` injective, then `p.leadingCoeff = r`. -/
lemma leadingCoeff_eq_of_map_eq_C_mul {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) [IsDomain S] {p : R[X]} {q : S[X]}
    (hq : q.Monic) {r : R} (hr : φ r ≠ 0) (h : p.map φ = C (φ r) * q) :
    p.leadingCoeff = r := by
  have hr0 : r ≠ 0 := fun h0 => hr (by rw [h0, map_zero])
  have hcr : C (φ r) * q ≠ 0 := by
    exact mul_ne_zero (fun hc => hr (C_eq_zero.mp hc)) hq.ne_zero
  have hdeg : (p.map φ).natDegree = q.natDegree := by
    rw [h]
    exact natDegree_C_mul (p := q) (a := φ r) hr
  have hzero : ∀ m, q.natDegree < m → p.coeff m = 0 := by
    intro m hm
    have h1 : (p.map φ).coeff m = 0 := by
      rw [h, coeff_C_mul, coeff_eq_zero_of_natDegree_lt hm, mul_zero]
    rw [coeff_map] at h1
    exact hφ (by rw [h1, map_zero])
  have hple : p.natDegree ≤ q.natDegree := natDegree_le_iff_coeff_eq_zero.mpr hzero
  have hgle : q.natDegree ≤ p.natDegree := hdeg ▸ natDegree_map_le
  have hpq : p.natDegree = q.natDegree := le_antisymm hple hgle
  have hcoeffd : φ (p.coeff q.natDegree) = φ r := by
    have h1 : (p.map φ).coeff q.natDegree = φ r := by
      rw [h, coeff_C_mul, hq.coeff_natDegree, mul_one]
    rw [← h1, coeff_map]
  rw [leadingCoeff, hpq]
  exact hφ hcoeffd

/-! ## Finitely generated algebras and localization at the non-zero-divisors -/

lemma finiteType_localization_nonZeroDivisors
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [Algebra A B]
    [Algebra.FiniteType A B] :
    Algebra.FiniteType (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))) := by
  classical
  obtain ⟨m, e, he⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  set T : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors A) with hT
  let K := FractionRing A
  let Bk := Localization T
  haveI : IsLocalization T Bk := inferInstance
  let ψ : MvPolynomial (Fin m) K →ₐ[K] Bk :=
    MvPolynomial.aeval (fun i => algebraMap B Bk (e (MvPolynomial.X i)))
  have key : ∀ p : MvPolynomial (Fin m) A, ψ (p.map (algebraMap A K)) = algebraMap B Bk (e p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        rw [MvPolynomial.map_C]
        show ψ (MvPolynomial.C (algebraMap A K a)) = algebraMap B Bk (e (MvPolynomial.C a))
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← MvPolynomial.algebraMap_eq,
          e.commutes, ← IsScalarTower.algebraMap_apply A K Bk,
          ← IsScalarTower.algebraMap_apply A B Bk]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        rw [map_mul, MvPolynomial.map_X, map_mul, hp, map_mul, map_mul, MvPolynomial.aeval_X]
  refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨m, ψ, ?_⟩
  intro x
  obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj T x
  obtain ⟨a, ha, hat⟩ := t.2
  obtain ⟨p, rfl⟩ := he b
  have ha0 : a ≠ 0 := by
    by_contra h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) h
  have haK : algebraMap A K a ≠ 0 := by
    intro h
    exact ha0 (IsFractionRing.injective A K (by simpa using h))
  have ht : (algebraMap B Bk) (↑t) = algebraMap K Bk (algebraMap A K a) := by
    rw [← hat, ← IsScalarTower.algebraMap_apply A B Bk, ← IsScalarTower.algebraMap_apply A K Bk]
  have htunit : (algebraMap B Bk) (↑t) * algebraMap K Bk ((algebraMap A K a))⁻¹ = 1 := by
    rw [ht, ← map_mul, mul_inv_cancel₀ haK, map_one]
  refine ⟨p.map (algebraMap A K) * MvPolynomial.C ((algebraMap A K a))⁻¹, ?_⟩
  calc ψ (p.map (algebraMap A K) * MvPolynomial.C ((algebraMap A K a))⁻¹)
      = ψ (p.map (algebraMap A K)) * algebraMap K Bk ((algebraMap A K a))⁻¹ := by
        rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    _ = algebraMap B Bk (e p) * algebraMap K Bk ((algebraMap A K a))⁻¹ := by rw [key p]
    _ = (x * algebraMap B Bk ↑t) * algebraMap K Bk ((algebraMap A K a))⁻¹ := by rw [← hbt]
    _ = x * ((algebraMap B Bk) ↑t * algebraMap K Bk ((algebraMap A K a))⁻¹) := by ring
    _ = x * 1 := by rw [htunit]
    _ = x := mul_one x

/-! ## Clearing denominators of a polynomial over a localization -/

lemma exists_map_eq_C_mul {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    (M : Submonoid R) [IsLocalization M R'] (P : R'[X]) :
    ∃ (m : M) (Q : R[X]), Q.map (algebraMap R R') = C (algebraMap R R' (m : R)) * P := by
  classical
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finset M (P.support.image P.coeff)
  have key : ∀ k : P.support, ∃ r : R, algebraMap R R' r = algebraMap R R' (m : R) * P.coeff (k : ℕ) := by
    intro k
    have h1 := hm (P.coeff (k : ℕ)) (Finset.mem_image_of_mem P.coeff k.2)
    rw [IsLocalization.IsInteger, Algebra.smul_def] at h1
    exact h1
  choose num hnum using key
  refine ⟨m, ∑ k : P.support, C (num k) * X ^ (k : ℕ), ?_⟩
  have step : ∀ k : P.support,
      (C (num k) * X ^ (k : ℕ)).map (algebraMap R R')
        = C (algebraMap R R' (m : R)) * (C (P.coeff (k : ℕ)) * X ^ (k : ℕ)) := by
    intro k
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, map_X, hnum k,
      Polynomial.C_mul]
    ring
  have hP : P = ∑ i : P.support, C (P.coeff (i : ℕ)) * X ^ (i : ℕ) := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow P]
    exact (Finset.sum_attach _ _).symm
  rw [Polynomial.map_sum]
  conv_rhs => rw [hP, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => step k

/-! ## Atiyah–Macdonald, Chapter 5, Exercise 21 -/

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [FaithfulSMul A B] [Algebra.FiniteType A B] :
    ∃ s : A, s ≠ 0 ∧ ∀ (Ω : Type*) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω), f s ≠ 0 →
      ∃ g : B →+* Ω, g.comp (algebraMap A B) = f := by
  classical
  haveI hAdom : IsDomain A := IsDomain.of_faithfulSMul A B
  let K := FractionRing A
  let T : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let Bk := Localization T
  haveI hTloc : IsLocalization T Bk := inferInstance
  have hTB : T ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have ha0 : a ≠ 0 := by simpa using ha
    exact fun h => ha0 (FaithfulSMul.algebraMap_injective A B (by simpa using h))
  haveI hBkdom : IsDomain Bk := IsLocalization.isDomain_of_le_nonZeroDivisors Bk hTB
  haveI hFT : Algebra.FiniteType K Bk := finiteType_localization_nonZeroDivisors A B
  obtain ⟨n, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg K Bk
  -- a common denominator for the normalized coordinates
  obtain ⟨d₀, hd₀⟩ := IsLocalization.exist_integer_multiples (M := T) (S := Bk) (R := B)
    (Finset.univ : Finset (Fin n)) (fun i => g (MvPolynomial.X i))
  obtain ⟨t, htmem, htval⟩ := d₀.2
  have htne : t ≠ 0 := by simpa using htmem
  have hy : ∀ i, ∃ u : B, algebraMap B Bk u = algebraMap A Bk t * g (MvPolynomial.X i) := by
    intro i
    obtain ⟨u, hu⟩ := hd₀ i (Finset.mem_univ i)
    refine ⟨u, ?_⟩
    rw [hu, Algebra.smul_def, ← htval, ← IsScalarTower.algebraMap_apply A B Bk]
  choose y hy using hy
  -- a presentation of B as an A-algebra
  obtain ⟨m, e, he⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  -- monic equations for the generators
  have hmon : ∀ j : Fin m, ∃ P : (MvPolynomial (Fin n) K)[X], P.Monic ∧
      P.eval₂ g (algebraMap B Bk (e (MvPolynomial.X j))) = 0 := fun j => hg_int _
  choose P hPmonic hPeval using hmon
  -- the two rescalings of the variables of `K[X]`
  set tK : K := algebraMap A K t with htKdef
  have htK : tK ≠ 0 := by
    rw [htKdef]
    exact fun h => htne (IsFractionRing.injective A K (by simpa using h))
  let σ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (fun i => MvPolynomial.C tK * MvPolynomial.X i)
  let τ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (fun i => MvPolynomial.C tK⁻¹ * MvPolynomial.X i)
  have hσX : ∀ i, σ (MvPolynomial.X i) = MvPolynomial.C tK * MvPolynomial.X i := fun i =>
    MvPolynomial.aeval_X _ i
  have hτX : ∀ i, τ (MvPolynomial.X i) = MvPolynomial.C tK⁻¹ * MvPolynomial.X i := fun i =>
    MvPolynomial.aeval_X _ i
  have hfixσ : ∀ r : K, σ (MvPolynomial.C r) = MvPolynomial.C r := by
    intro r
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
  have hfixτ : ∀ r : K, τ (MvPolynomial.C r) = MvPolynomial.C r := by
    intro r
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
  have hστ : σ.comp τ = AlgHom.id K (MvPolynomial (Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hτX i, map_mul, hfixσ, hσX i, ← mul_assoc, ← MvPolynomial.C_mul,
      inv_mul_cancel₀ htK, MvPolynomial.C_1, one_mul]
  have hτσ : τ.comp σ = AlgHom.id K (MvPolynomial (Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hσX i, map_mul, hfixτ, hτX i, ← mul_assoc, ← MvPolynomial.C_mul,
      mul_inv_cancel₀ htK, MvPolynomial.C_1, one_mul]
  -- the `A`-algebra map `A[Y] → B`, `Y i ↦ y i`
  let ψ : MvPolynomial (Fin n) A →ₐ[A] B := MvPolynomial.aeval y
  have hψX : ∀ i, ψ (MvPolynomial.X i) = y i := fun i => MvPolynomial.aeval_X _ i
  have hψC' : ∀ a : A, ψ (MvPolynomial.C a) = algebraMap A B a := by
    intro a
    rw [← MvPolynomial.algebraMap_eq]
    exact AlgHom.commutes ψ a
  have hψC : ∀ a : A, (ψ : MvPolynomial (Fin n) A →+* B) (MvPolynomial.C a) = algebraMap A B a :=
    hψC'
  -- the comparison of coefficient maps
  have hbridge : (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K)) =
      MvPolynomial.map (algebraMap A K) := rfl
  have hψX' : ∀ i, (ψ : MvPolynomial (Fin n) A →+* B) (MvPolynomial.X i) = y i := hψX
  have hH_coeff : ∀ c : MvPolynomial (Fin n) A,
      algebraMap B Bk ((ψ : MvPolynomial (Fin n) A →+* B) c) =
        g (σ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) c)) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a =>
        have hL : algebraMap B Bk ((ψ : MvPolynomial (Fin n) A →+* B) (MvPolynomial.C a))
            = algebraMap A Bk a := by
          rw [hψC a, IsScalarTower.algebraMap_apply A B Bk a]
        have hR : g (σ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a)))
            = algebraMap A Bk a := by
          have h3 : algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a)
              = MvPolynomial.C (algebraMap A K a) := by rw [hbridge, MvPolynomial.map_C]
          rw [h3, hfixσ, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
            ← IsScalarTower.algebraMap_apply A K Bk]
        rw [hL, hR]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        have hL : algebraMap B Bk ((ψ : MvPolynomial (Fin n) A →+* B) (p * MvPolynomial.X i))
            = g (σ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) p)) *
              (algebraMap A Bk t * g (MvPolynomial.X i)) := by
          rw [map_mul, hψX', map_mul, hy i, hp]
        have hR : g (σ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (p * MvPolynomial.X i)))
            = g (σ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) p)) *
              (algebraMap A Bk t * g (MvPolynomial.X i)) := by
          have h3 : algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (p * MvPolynomial.X i)
              = algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) p * MvPolynomial.X i := by
            rw [hbridge, map_mul, MvPolynomial.map_X]
          rw [h3, map_mul, hσX i, map_mul, map_mul]
          have h4 : g (MvPolynomial.C tK) = algebraMap A Bk t := by
            rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, IsScalarTower.algebraMap_apply A K Bk]
          rw [h4]
        rw [hL, hR]
  have hcm : ((algebraMap B Bk).comp (ψ : MvPolynomial (Fin n) A →+* B)) =
      ((g : MvPolynomial (Fin n) K →+* Bk).comp ((σ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K).comp
        (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K)))) :=
    RingHom.ext hH_coeff
  -- clearing denominators of the rescaled monic equations
  have halg_inj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K)) := by
    rw [hbridge]
    exact MvPolynomial.map_injective _ (IsFractionRing.injective A K)
  haveI hloc : IsLocalization ((nonZeroDivisors A).map MvPolynomial.C)
      (MvPolynomial (Fin n) K) := MvPolynomial.isLocalization (nonZeroDivisors A) K
  have stepA : ∀ j : Fin m, ∃ (Q : (MvPolynomial (Fin n) A)[X]) (a : A), a ≠ 0 ∧
      Q.leadingCoeff = MvPolynomial.C a ∧
      Q.map ((σ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K).comp
        (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K))) =
        C (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a)) *
          P j := by
    intro j
    obtain ⟨mm, Q, hQspec⟩ := exists_map_eq_C_mul (R := MvPolynomial (Fin n) A)
      (R' := MvPolynomial (Fin n) K) (M := (nonZeroDivisors A).map MvPolynomial.C)
      ((P j).map τ.toRingHom)
    obtain ⟨a, ha_mem, ha_eq⟩ := mm.2
    have ha : a ≠ 0 := by simpa using ha_mem
    have hspec' : Q.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K)) =
        C (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a)) *
          ((P j).map τ.toRingHom) := by
      rw [hQspec, ← ha_eq]
    have hCa_ne : algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K)
        (MvPolynomial.C a) ≠ 0 := by
      rw [hbridge, MvPolynomial.map_C]
      intro h
      have hinj : Function.Injective (MvPolynomial.C : K → MvPolynomial (Fin n) K) :=
        MvPolynomial.C_injective (Fin n) K
      have h1 : algebraMap A K a = 0 := by
        apply hinj
        rw [h]
        simp
      exact ha (IsFractionRing.injective A K (by simpa using h1))
    refine ⟨Q, a, ha, leadingCoeff_eq_of_map_eq_C_mul halg_inj
      ((hPmonic j).map τ.toRingHom) hCa_ne hspec', ?_⟩
    rw [← Polynomial.map_map, hspec', Polynomial.map_mul, Polynomial.map_C]
    have hfix' : (σ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K)
        (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a)) =
        algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) (MvPolynomial.C a) := by
      rw [hbridge, MvPolynomial.map_C]
      exact hfixσ _
    rw [hfix']
    have hc : ((σ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K).comp τ.toRingHom)
        = RingHom.id (MvPolynomial (Fin n) K) := by
      refine RingHom.ext (fun x => ?_)
      have hx : (σ.comp τ) x = x := by rw [hστ]; rfl
      exact hx
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  choose Q aQ haQ hlead hσmap using stepA
  -- killing the denominators, in `B`
  have stepB : ∀ j : Fin m, ∃ s' : A, s' ≠ 0 ∧
      algebraMap A B s' * (Q j).eval₂ ψ (e (MvPolynomial.X j)) = 0 := by
    intro j
    have h1 : algebraMap B Bk ((Q j).eval₂ ψ (e (MvPolynomial.X j))) = 0 := by
      rw [hom_eval₂, hcm, ← eval₂_map, hσmap j, eval₂_mul, eval₂_C, hPeval j, mul_zero]
    have h1' : algebraMap B Bk ((Q j).eval₂ ψ (e (MvPolynomial.X j))) = algebraMap B Bk 0 := by
      rw [h1, map_zero]
    obtain ⟨mm, hmm⟩ := (IsLocalization.eq_iff_exists T Bk).mp h1'
    have hmm' : (mm : B) * (Q j).eval₂ ψ (e (MvPolynomial.X j)) = 0 := by
      rw [hmm, mul_zero]
    obtain ⟨s', hs'mem, hs'eq⟩ := mm.2
    refine ⟨s', by simpa using hs'mem, ?_⟩
    rw [← hs'eq] at hmm'
    exact hmm'
  choose s' hs'ne hkill using stepB
  -- a single denominator
  let sA : A := ∏ j : Fin m, (aQ j * s' j)
  have hsA : sA ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => mul_ne_zero (haQ j) (hs'ne j))
  let u : Fin m → A := fun j => ∏ i ∈ Finset.univ.erase j, (aQ i * s' i)
  have hkey : ∀ j, aQ j * u j * s' j = sA := by
    intro j
    have h := Finset.mul_prod_erase (Finset.univ : Finset (Fin m)) (fun i => aQ i * s' i)
      (Finset.mem_univ j)
    dsimp only [sA, u]
    rw [← h]
    ring
  -- the final monic polynomials
  let p : Fin m → (MvPolynomial (Fin n) A)[X] :=
    fun j => C (MvPolynomial.C (u j * s' j)) * Q j
  have hCu_ne : ∀ j, (MvPolynomial.C (u j * s' j) : MvPolynomial (Fin n) A) ≠ 0 := by
    intro j
    rw [Ne, MvPolynomial.C_eq_zero]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (haQ i) (hs'ne i)))
      (hs'ne j)
  have hp_lead : ∀ j, (p j).leadingCoeff ∈ Submonoid.powers (MvPolynomial.C sA) := by
    intro j
    have h1 : (p j).leadingCoeff = MvPolynomial.C (u j * s' j) * (Q j).leadingCoeff :=
      leadingCoeff_C_mul (hCu_ne j)
    rw [h1, hlead j, ← map_mul]
    have h2 : u j * s' j * aQ j = sA := by
      rw [← hkey j]; ring
    rw [h2]
    exact Submonoid.mem_powers _
  have hp_eval : ∀ j, (p j).eval₂ ψ (e (MvPolynomial.X j)) = 0 := by
    intro j
    rw [show (p j) = C (MvPolynomial.C (u j * s' j)) * Q j from rfl, eval₂_mul, eval₂_C, hψC,
      map_mul, mul_assoc, hkill j, mul_zero]
  -- the localizations of the final step
  let sE : MvPolynomial (Fin n) A := MvPolynomial.C sA
  let M' : Submonoid (MvPolynomial (Fin n) A) := Submonoid.powers sE
  let Cc := Localization M'
  let Dd := Localization (M'.map (ψ : MvPolynomial (Fin n) A →+* B))
  haveI hCcloc : IsLocalization M' Cc := inferInstance
  haveI hDdloc : IsLocalization (M'.map (ψ : MvPolynomial (Fin n) A →+* B)) Dd := inferInstance
  let φ : Cc →+* Dd := IsLocalization.map Dd (ψ : MvPolynomial (Fin n) A →+* B)
    (Submonoid.le_comap_map M')
  have hφspec : ∀ c : MvPolynomial (Fin n) A,
      φ (algebraMap (MvPolynomial (Fin n) A) Cc c) =
        algebraMap B Dd ((ψ : MvPolynomial (Fin n) A →+* B) c) := by
    intro c
    exact IsLocalization.map_eq (Submonoid.le_comap_map M') c
  have hψ_inj : Function.Injective (ψ : MvPolynomial (Fin n) A →+* B) := by
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      have hx : τ (σ x) = x := AlgHom.congr_fun hτσ x
      have hy' : τ (σ y) = y := AlgHom.congr_fun hτσ y
      rw [← hx, ← hy', hxy]
    have hcomp_inj : Function.Injective ((algebraMap B Bk).comp (ψ : MvPolynomial (Fin n) A →+* B)) := by
      rw [hcm]
      exact (hg_inj.comp hσ_inj).comp halg_inj
    intro x y hxy
    exact hcomp_inj (by rw [RingHom.comp_apply, RingHom.comp_apply, hxy])
  have hψsE : (ψ : MvPolynomial (Fin n) A →+* B) sE = algebraMap A B sA := hψC sA
  have hMBD : M'.map (ψ : MvPolynomial (Fin n) A →+* B) ≤ nonZeroDivisors B := by
    rintro b ⟨c, hc, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff c sE).mp hc
    rw [← hk, map_pow, hψsE]
    exact pow_ne_zero k (fun h0 => hsA (FaithfulSMul.algebraMap_injective A B (by rw [h0, map_zero])))
  haveI hDddom : IsDomain Dd := IsLocalization.isDomain_of_le_nonZeroDivisors Dd hMBD
  have hφ_inj : Function.Injective φ := by
    have hinjB : Function.Injective (algebraMap B Dd) := IsLocalization.injective Dd hMBD
    intro x y hxy
    have hz : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨⟨a, mm⟩, ha⟩ := IsLocalization.surj M' (x - y)
    have h1 : φ (algebraMap (MvPolynomial (Fin n) A) Cc a) = 0 := by
      rw [← ha, map_mul, hz, zero_mul]
    rw [hφspec a] at h1
    have h2 : (ψ : MvPolynomial (Fin n) A →+* B) a = 0 := hinjB (by rw [h1, map_zero])
    have h3 : a = 0 := hψ_inj (by rw [h2, map_zero])
    have h4 : (x - y) * algebraMap (MvPolynomial (Fin n) A) Cc (mm : MvPolynomial (Fin n) A) = 0 := by
      rw [ha, h3, map_zero]
    obtain ⟨vv, hvv⟩ := (IsLocalization.map_units Cc mm).exists_right_inv
    exact sub_eq_zero.mp (by
      calc x - y = (x - y) * (algebraMap (MvPolynomial (Fin n) A) Cc (mm : MvPolynomial (Fin n) A)) * vv := by
            rw [mul_assoc, hvv, mul_one]
        _ = 0 := by rw [h4, zero_mul])
  -- `B` is generated by its image from `A` and the chosen generators
  have hBcl : Subring.closure (Set.range (algebraMap A B) ∪
      Set.range (fun j : Fin m => e (MvPolynomial.X j))) = ⊤ := by
    rw [eq_top_iff]
    rintro b -
    obtain ⟨Pp, rfl⟩ := he b
    clear he
    induction Pp using MvPolynomial.induction_on with
    | C aa =>
        exact Subring.subset_closure (Or.inl ⟨aa, by
          rw [← MvPolynomial.algebraMap_eq]; exact (e.commutes aa).symm⟩)
    | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
    | mul_X p j hp =>
        rw [map_mul]
        exact Subring.mul_mem _ hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))
  letI : Algebra Cc Dd := φ.toAlgebra
  have hgen : ∀ j : Fin m, IsIntegral Cc (algebraMap B Dd (e (MvPolynomial.X j))) := by
    intro j
    exact RingHom.isIntegralElem_localization_at_leadingCoeff (ψ : MvPolynomial (Fin n) A →+* B)
      (e (MvPolynomial.X j)) (p j) (hp_eval j) M' (hp_lead j)
  have hIntB : ∀ b : B, IsIntegral Cc (algebraMap B Dd b) := by
    intro b
    obtain ⟨Pp, rfl⟩ := he b
    clear he hBcl
    induction Pp using MvPolynomial.induction_on with
    | C aa =>
        have h1 : algebraMap B Dd (algebraMap A B aa) =
            φ (algebraMap (MvPolynomial (Fin n) A) Cc (MvPolynomial.C aa)) := by
          rw [hφspec, hψC]
        rw [show e (MvPolynomial.C aa) = algebraMap A B aa from by
          rw [← MvPolynomial.algebraMap_eq]; exact e.commutes aa, h1]
        exact RingHom.isIntegralElem_map φ
    | add p q hp hq =>
        rw [map_add, map_add]
        exact IsIntegral.add hp hq
    | mul_X p j hp =>
        rw [map_mul, map_mul]
        exact IsIntegral.mul hp (hgen j)
  have hφint : φ.IsIntegral := by
    have hAI : Algebra.IsIntegral Cc Dd := ⟨fun x => by
      obtain ⟨⟨aa, mm⟩, hsurj⟩ := IsLocalization.surj (M'.map (ψ : MvPolynomial (Fin n) A →+* B)) x
      obtain ⟨w, hwmem, hweq⟩ := mm.2
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff w sE).mp hwmem
      have hu : IsUnit (algebraMap (MvPolynomial (Fin n) A) Cc sE) :=
        IsLocalization.Away.algebraMap_isUnit sE
      obtain ⟨vv, hv⟩ := hu.exists_right_inv
      have hv' : φ (algebraMap (MvPolynomial (Fin n) A) Cc sE) * φ vv = 1 := by
        rw [← map_mul, hv, map_one]
      have hAmm : algebraMap B Dd (mm : B) = (φ (algebraMap (MvPolynomial (Fin n) A) Cc sE)) ^ k := by
        rw [← hweq, ← hk, map_pow, map_pow, ← hφspec sE]
      have hx0 : x = algebraMap B Dd aa * (φ vv) ^ k := by
        calc x = x * ((φ (algebraMap (MvPolynomial (Fin n) A) Cc sE)) ^ k * (φ vv) ^ k) := by
              rw [← mul_pow, hv', one_pow, mul_one]
          _ = (x * (φ (algebraMap (MvPolynomial (Fin n) A) Cc sE)) ^ k) * (φ vv) ^ k := by ring
          _ = algebraMap B Dd aa * (φ vv) ^ k := by rw [← hAmm, hsurj]
      rw [hx0]
      exact IsIntegral.mul (hIntB aa) (IsIntegral.pow isIntegral_algebraMap k)⟩
    rwa [show φ = algebraMap Cc Dd from (RingHom.algebraMap_toAlgebra φ).symm,
      algebraMap_isIntegral_iff]
  -- the extension of `f`
  refine ⟨sA, hsA, ?_⟩
  intro Ω _ _ f hfs
  letI : Algebra A Ω := f.toAlgebra
  have hσunit : IsUnit ((MvPolynomial.aeval (fun _ : Fin n => (0 : Ω)) :
      MvPolynomial (Fin n) A →ₐ[A] Ω) sE) := by
    have h1 : (MvPolynomial.aeval (fun _ : Fin n => (0 : Ω)) :
        MvPolynomial (Fin n) A →ₐ[A] Ω) sE = f sA := by
      show (MvPolynomial.aeval (fun _ : Fin n => (0 : Ω)) :
        MvPolynomial (Fin n) A →ₐ[A] Ω) (MvPolynomial.C sA) = f sA
      rw [MvPolynomial.aeval_C, RingHom.algebraMap_toAlgebra]
    rw [h1]
    exact isUnit_iff_ne_zero.mpr hfs
  let ρ : Cc →+* Ω := IsLocalization.Away.lift sE
    (g := (MvPolynomial.aeval (fun _ : Fin n => (0 : Ω))).toRingHom) hσunit
  have hker : RingHom.ker φ ≤ RingHom.ker ρ := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx0 : x = 0 := hφ_inj (by rw [hx, map_zero])
    rw [hx0, map_zero]
  obtain ⟨ψ', hψ'⟩ := exists_ringHom_comp_eq_of_isIntegral φ hφint ρ hker
  refine ⟨ψ'.comp (algebraMap B Dd), ?_⟩
  ext aa
  have h1 : algebraMap B Dd (algebraMap A B aa) =
      φ (algebraMap (MvPolynomial (Fin n) A) Cc (MvPolynomial.C aa)) := by
    rw [hφspec, hψC]
  have h2 : ρ (algebraMap (MvPolynomial (Fin n) A) Cc (MvPolynomial.C aa)) = f aa := by
    rw [← MvPolynomial.algebraMap_eq]
    rw [IsLocalization.Away.lift_eq sE hσunit]
    show (MvPolynomial.aeval (fun _ : Fin n => (0 : Ω)) :
      MvPolynomial (Fin n) A →ₐ[A] Ω) (algebraMap A (MvPolynomial (Fin n) A) aa) = f aa
    rw [AlgHom.commutes, RingHom.algebraMap_toAlgebra]
  show ψ' (algebraMap B Dd (algebraMap A B aa)) = f aa
  rw [h1]
  exact (RingHom.congr_fun hψ' (algebraMap (MvPolynomial (Fin n) A) Cc
    (MvPolynomial.C aa))).trans h2

end AtiyahMcdonald69.Ex_5_21

/-! ## Axiom audit -/

#print axioms AtiyahMcdonald69.Ex_5_21.solution
#print axioms AtiyahMcdonald69.Ex_5_21.exists_ringHom_comp_eq_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_21.finiteType_localization_nonZeroDivisors
#print axioms AtiyahMcdonald69.Ex_5_21.leadingCoeff_eq_of_map_eq_C_mul
