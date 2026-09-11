import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

theorem AtiyahMcdonald69.Ex_1_3.part_a {A : Type*} [CommRing A] {r : ℕ} (f : MvPolynomial (Fin r) A) :
  IsUnit f ↔ IsUnit (MvPolynomial.coeff 0 f) ∧ ∀ d : Fin r →₀ ℕ, d ≠ 0 → IsNilpotent (MvPolynomial.coeff d f) := by
  exact MvPolynomial.isUnit_iff

theorem AtiyahMcdonald69.Ex_1_3.part_b {A : Type*} [CommRing A] {r : ℕ} (f : MvPolynomial (Fin r) A) :
  IsNilpotent f ↔ ∀ d : Fin r →₀ ℕ, IsNilpotent (MvPolynomial.coeff d f) := by
  exact MvPolynomial.isNilpotent_iff

set_option linter.unusedVariables false in
theorem AtiyahMcdonald69.Ex_1_3.part_c_helpers.common_mv_annihilator_coeffs {A : Type*} [CommRing A] {r : ℕ} (f : MvPolynomial (Fin r) A) :
  ∀ {R : Type*} [CommRing R] (n : ℕ) {ι : Type*} (F : ι → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin n) R), g ≠ 0 → (∀ t, F t * g = 0) → ∃ a : R, a ≠ 0 ∧ ∀ t d, a * MvPolynomial.coeff d (F t) = 0 := by
  intro R instR n
  induction n with
  | zero =>
    intro ι F g hg hFg
    refine ⟨MvPolynomial.coeff 0 g, ?_, ?_⟩
    · intro h
      apply hg
      ext d
      have hd : d = 0 := Subsingleton.elim _ _
      simpa [hd] using h
    · intro t d
      have hf : F t = MvPolynomial.C (MvPolynomial.coeff 0 (F t)) := by
        ext e
        have he : e = 0 := Subsingleton.elim _ _
        simp [he]
      have h := congrArg (MvPolynomial.coeff 0) (hFg t)
      rw [hf, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] at h
      have hd : d = 0 := Subsingleton.elim _ _
      simpa [hd, mul_comm] using h
  | succ n ih =>
    intro ι F g hg hFg
    classical
    let e := MvPolynomial.finSuccEquiv R n
    let H := fun t => e (F t)
    have heg : e g ≠ 0 := by
      intro h
      apply hg
      apply e.injective
      simpa using h
    have hHg : ∀ t, H t * e g = 0 := by
      intro t
      change e (F t) * e g = 0
      rw [← map_mul, hFg t, map_zero]
    have hex : ∃ k : ℕ, ∃ q : Polynomial (MvPolynomial (Fin n) R),
        q ≠ 0 ∧ (∀ t, H t * q = 0) ∧ q.natDegree = k :=
      ⟨(e g).natDegree, e g, heg, hHg, rfl⟩
    obtain ⟨Q, hQ, hHQ, hdeg⟩ := Nat.find_spec hex
    have hmin : ∀ q : Polynomial (MvPolynomial (Fin n) R), q ≠ 0 →
        (∀ t, H t * q = 0) → Q.natDegree ≤ q.natDegree := by
      intro q hq hHq
      rw [hdeg]
      exact Nat.find_min' hex ⟨q, hq, hHq, rfl⟩
    have hann : ∀ t i, Q.leadingCoeff * (H t).coeff i = 0 := by
      intro t
      have hall : ∀ i, (H t).coeff i • Q = 0 := by
        apply Nat.strong_decreasing_induction
        · use (H t).natDegree
          intro i hi
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_smul]
        intro l IH
        obtain hlt | heq := (Polynomial.natDegree_smul_le ((H t).coeff l) Q).lt_or_eq
        · by_cases hz : (H t).coeff l • Q = 0
          · exact hz
          · have hc : ∀ j, H j * ((H t).coeff l • Q) = 0 := by
              intro j
              rw [Polynomial.smul_eq_C_mul, mul_left_comm, hHQ j, mul_zero]
            exact False.elim ((not_lt_of_ge (hmin _ hz hc)) hlt)
        suffices (H t).coeff l * Q.leadingCoeff = 0 by
          rwa [← Polynomial.leadingCoeff_eq_zero, ← Polynomial.coeff_natDegree,
            Polynomial.coeff_smul, heq, Polynomial.coeff_natDegree, smul_eq_mul]
        let m := Q.natDegree
        suffices (H t * Q).coeff (l + m) = (H t).coeff l * Q.leadingCoeff by
          rw [← this, hHQ t, Polynomial.coeff_zero]
        rw [Polynomial.coeff_mul]
        apply Finset.sum_eq_single (l, m) _ (by simp)
        simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
        intro i j hij hijne
        obtain hi | rfl | hi := lt_trichotomy i l
        · have hj : m < j := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj, mul_zero]
        · cutsat
        · rw [← Polynomial.coeff_C_mul, ← Polynomial.smul_eq_C_mul, IH _ hi,
            Polynomial.coeff_zero]
      intro i
      have h := congrArg (fun p : Polynomial (MvPolynomial (Fin n) R) => p.coeff Q.natDegree) (hall i)
      simpa [Polynomial.coeff_smul, Polynomial.coeff_natDegree, smul_eq_mul, mul_comm] using h
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha, haF⟩ := ih
      (fun p : ι × ℕ => (H p.1).coeff p.2) Q.leadingCoeff hlc
      (fun p => by simpa [mul_comm] using hann p.1 p.2)
    refine ⟨a, ha, ?_⟩
    intro t d
    have h := haF (t, d 0) (Finsupp.tail d)
    change a * MvPolynomial.coeff (Finsupp.tail d)
      ((MvPolynomial.finSuccEquiv R n (F t)).coeff (d 0)) = 0 at h
    simpa only [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail] using h

theorem AtiyahMcdonald69.Ex_1_3.part_c {A : Type*} [CommRing A] {r : ℕ} (f : MvPolynomial (Fin r) A) :
  (∃ g : MvPolynomial (Fin r) A, g ≠ 0 ∧ f * g = 0) ↔ ∃ a : A, a ≠ 0 ∧ ∀ d : Fin r →₀ ℕ, a * MvPolynomial.coeff d f = 0 := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    obtain ⟨a, ha, hann⟩ := (AtiyahMcdonald69.Ex_1_3.part_c_helpers.common_mv_annihilator_coeffs (A := A) (r := r) (f := f)) r
      (fun _ : Unit => f) g hg (fun _ => hfg)
    exact ⟨a, ha, hann ()⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨MvPolynomial.C a, ?_, ?_⟩
    · intro hz
      apply ha
      simpa using congrArg (MvPolynomial.coeff 0) hz
    · rw [mul_comm]
      ext d
      simpa only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] using h d

set_option linter.unusedVariables false in
theorem AtiyahMcdonald69.Ex_1_3.part_d_helpers.coeff_mul_mem_of_left {A : Type*} [CommRing A] {r : ℕ} (f g : MvPolynomial (Fin r) A) :
  ∀ {R : Type*} [CommRing R] {σ : Type*} (I : Ideal R) (f g : MvPolynomial σ R), (∀ d, MvPolynomial.coeff d f ∈ I) → ∀ d, MvPolynomial.coeff d (f * g) ∈ I := by
  intro R _ σ I f g hf
  have hf' : f ∈ (Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) I) :=
    MvPolynomial.mem_map_C_iff.mpr hf
  exact MvPolynomial.mem_map_C_iff.mp
    ((Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) I).mul_mem_right g hf')

theorem AtiyahMcdonald69.Ex_1_3.part_d {A : Type*} [CommRing A] {r : ℕ} (f g : MvPolynomial (Fin r) A) :
  Ideal.span (Set.range (fun d : Fin r →₀ ℕ => MvPolynomial.coeff d (f * g))) = (⊤ : Ideal A) ↔ Ideal.span (Set.range (fun d : Fin r →₀ ℕ => MvPolynomial.coeff d f)) = (⊤ : Ideal A) ∧ Ideal.span (Set.range (fun d : Fin r →₀ ℕ => MvPolynomial.coeff d g)) = (⊤ : Ideal A) := by
    have left_factor (p q : MvPolynomial (Fin r) A)
        (h : Ideal.span (Set.range (fun d => MvPolynomial.coeff d (p * q))) = ⊤) :
        Ideal.span (Set.range (fun d => MvPolynomial.coeff d p)) = ⊤ := by
      apply top_unique
      rw [← h]
      apply Ideal.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact (AtiyahMcdonald69.Ex_1_3.part_d_helpers.coeff_mul_mem_of_left (A := A) (r := r) (f := f) (g := g))
        (Ideal.span (Set.range (fun e => MvPolynomial.coeff e p))) p q
        (fun e => Ideal.subset_span (Set.mem_range_self e)) d
    constructor
    · intro h
      exact ⟨left_factor f g h, left_factor g f (by simpa [mul_comm] using h)⟩
    · rintro ⟨hf, hg⟩
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      letI : M.IsMaximal := hM
      letI : NoZeroDivisors (MvPolynomial (Fin r) (A ⧸ M)) := inferInstance
      have hz (p : MvPolynomial (Fin r) A) :
          MvPolynomial.map (Ideal.Quotient.mk M) p = 0 ↔
            ∀ d, MvPolynomial.coeff d p ∈ M := by
        constructor
        · intro hp d
          have hd := congrArg (MvPolynomial.coeff d) hp
          simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
            Ideal.Quotient.eq_zero_iff_mem] using hd
        · intro hp
          apply MvPolynomial.ext
          intro d
          simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] using
            (Ideal.Quotient.eq_zero_iff_mem.mpr (hp d))
      have hprod : MvPolynomial.map (Ideal.Quotient.mk M) f *
          MvPolynomial.map (Ideal.Quotient.mk M) g = 0 := by
        rw [← map_mul]
        exact (hz (f * g)).mpr (fun d => hle (Ideal.subset_span (Set.mem_range_self d)))
      rcases mul_eq_zero.mp hprod with hzero | hzero
      · have hle' : Ideal.span (Set.range (fun d => MvPolynomial.coeff d f)) ≤ M :=
          Ideal.span_le.mpr (by
            rintro _ ⟨d, rfl⟩
            exact (hz f).mp hzero d)
        exact hM.ne_top (top_le_iff.mp (hf ▸ hle'))
      · have hle' : Ideal.span (Set.range (fun d => MvPolynomial.coeff d g)) ≤ M :=
          Ideal.span_le.mpr (by
            rintro _ ⟨d, rfl⟩
            exact (hz g).mp hzero d)
        exact hM.ne_top (top_le_iff.mp (hg ▸ hle'))
