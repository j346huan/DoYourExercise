import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 5.19

Natural proof: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-19>

The exercise reads (Chapter 5, Exercise 19, *Integral dependence and valuations*):

> Deduce the result of Exercise 17 from Exercise 18.

Exercise 5.18 (Zariski's lemma): a field `B` which is a finitely generated `k`-algebra is a finite
algebraic extension of `k`.

Exercise 5.17 (weak form of Hilbert's Nullstellensatz): let `X ⊆ kⁿ` be an affine algebraic
variety over an algebraically closed field `k`, and let `I(X) ⊆ k[t₁,…,tₙ]` be the ideal of `X`
(Chapter 1, Exercise 27). If `I(X) ≠ (1)` then `X` is not empty; and every maximal ideal of
`k[t₁,…,tₙ]` is of the form `(t₁-a₁,…,tₙ-aₙ)` with `aᵢ ∈ k`.

Formal dictionary used below (`k[t₁,…,tₙ]` is `MvPolynomial (Fin n) k`):

* points of `kⁿ` are functions `Fin n → k`;
* `aeval a p` is the value `p(a)` of `p` at the point `a`;
* `zeroLocus k I` is the affine algebraic variety `V(I)` of common zeros of `I`;
* `vanishingIdeal k X` is the ideal `I(X)` of polynomials vanishing on `X`;
* a subset `X ⊆ kⁿ` is an affine algebraic variety iff it is the common zero set of a family of
  polynomials, `IsAffineAlgebraicVariety X` below.

The argument follows the natural proof.  If `m` is a maximal ideal of `k[t₁,…,tₙ]`, the quotient
`k[t₁,…,tₙ]/m` is a field which is finitely generated as a `k`-algebra, so by Exercise 5.18 it is
finite over `k`, and since `k` is algebraically closed the structure map `k → k[t₁,…,tₙ]/m` is
bijective; the images of the `tᵢ` give the point `a` and `m = (t₁-a₁,…,tₙ-aₙ)`.  A proper ideal is
contained in a maximal ideal, hence has a common zero; applying this to `I(X)` (which contains the
ideal defining `X`) gives Exercise 5.17.

## Audit of the source statement and of the natural proof

* The book's Exercise 5.17 ends with the sentence *"Deduce that every maximal ideal in the ring
  `k[t₁,…,tₙ]` is of the form `(t₁-a₁,…,tₙ-aₙ)` where `aᵢ ∈ k`"*, which in the scanned text is
  separated from the main statement of Exercise 17 by a page break.  It is part of Exercise 17
  (and the natural proof of Exercise 5.19 uses exactly it), so the formalization below covers both
  sentences of Exercise 17.
* No parameters are omitted by the book: `k` is assumed algebraically closed and `n ≥ 0` is the
  number of variables.  The definitions of "affine algebraic variety in `kⁿ`" and of "`I(X)`" are
  the ones of Chapter 1, Exercise 27: an affine algebraic variety is the set of common zeros of a
  family of polynomials, and `I(X)` is the ideal of all polynomials vanishing on `X`.  These are
  reproduced as `IsAffineAlgebraicVariety` and `affineIdeal`.
* The natural proof is correct.  Its one implicit step is that `I(X)` contains the ideal defining
  `X`, so that `I(X) ≠ (1)` implies that the defining ideal is proper; this is supplied in
  `exercise_5_19_weak_nullstellensatz`.  The natural proof checks that the point `a` produced by
  Exercise 5.18 gives `m = (t₁-a₁,…,tₙ-aₙ)`, and that a proper ideal has a common zero; the file
  also proves the converse (each `(t₁-a₁,…,tₙ-aₙ)` is maximal), as the natural proof notes.
-/


namespace AtiyahMcdonald69.Ex_5_19

open MvPolynomial

/-! ## Exercise 5.18: Zariski's lemma -/

/-- **Atiyah–Macdonald, Exercise 5.18.** A field `B` which is a finitely generated `k`-algebra is a
finite algebraic extension of `k`: `B` is a finite `k`-module and is algebraic (indeed integral)
over `k`. -/
theorem exercise_5_18 (k B : Type*) [Field k] [Field B] [Algebra k B]
    [Algebra.FiniteType k B] : Module.Finite k B ∧ Algebra.IsIntegral k B ∧ Algebra.IsAlgebraic k B :=
  have hfin := finite_of_finite_type_of_isJacobsonRing k B
  have hint : Algebra.IsIntegral k B := Algebra.IsIntegral.of_finite k B
  ⟨hfin, hint, hint.isAlgebraic⟩

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

/-! ## Maximal ideals and points -/

/-- A maximal ideal of `k[t₁,…,tₙ]` has a common zero.  This is the one place where Exercise 5.18
is used: the quotient `k[t₁,…,tₙ]/m` is a field and a finitely generated `k`-algebra, hence
integral over `k` by Exercise 5.18; as `k` is algebraically closed, `k → k[t₁,…,tₙ]/m` is
bijective, which yields a `k`-algebra map `k[t₁,…,tₙ] → k` killing `m`. -/
theorem exists_aeval_eq_zero_of_isMaximal {P : Ideal (MvPolynomial (Fin n) k)} (hP : P.IsMaximal) :
    ∃ a : Fin n → k, ∀ f ∈ P, aeval a f = 0 := by
  let : Field (MvPolynomial (Fin n) k ⧸ P) := Ideal.Quotient.field P
  have halg : Algebra.IsAlgebraic k (MvPolynomial (Fin n) k ⧸ P) := by
    have : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ P) := Algebra.FiniteType.quotient k P
    exact (exercise_5_18 k (MvPolynomial (Fin n) k ⧸ P)).2.2
  let φ : (MvPolynomial (Fin n) k ⧸ P) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_⟩
  have hφ : aeval (fun i => φ (Ideal.Quotient.mk P (X i))) = φ.comp (Ideal.Quotient.mkₐ k P) := by
    ext i
    simp
  intro f hf
  rw [AlgHom.congr_fun hφ f]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hf]

omit [IsAlgClosed k] in
/-- The vanishing ideal of a single point `a` of `kⁿ` is the ideal
`(t₁-a₁,…,tₙ-aₙ)`. -/
theorem vanishingIdeal_singleton_eq_span (a : Fin n → k) :
    vanishingIdeal k {a} =
      Ideal.span (Set.range fun i => (X i - C (a i) : MvPolynomial (Fin n) k)) := by
  set S : Ideal (MvPolynomial (Fin n) k) :=
    Ideal.span (Set.range fun i => (X i - C (a i) : MvPolynomial (Fin n) k)) with hS
  apply le_antisymm
  · intro p hp
    have hmem : ∀ i, (X i - C (a i) : MvPolynomial (Fin n) k) ∈ S := fun i => by
      rw [hS]
      exact Ideal.subset_span (Set.mem_range_self i)
    have hX : ∀ i, (Ideal.Quotient.mk S) (X i) = (Ideal.Quotient.mk S) (C (a i)) := by
      intro i
      have h0 : (Ideal.Quotient.mk S) ((X i - C (a i) : MvPolynomial (Fin n) k)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
      rwa [map_sub, sub_eq_zero] at h0
    have hC : ∀ q : MvPolynomial (Fin n) k,
        aeval (fun i => (C (a i) : MvPolynomial (Fin n) k)) q = C (aeval a q) := by
      intro q
      rw [MvPolynomial.map_aeval (R := k) (g := a)
        (φ := (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))]
      simp
    have hp0 : aeval a p = 0 := (mem_vanishingIdeal_singleton_iff a p).mp hp
    have h1 : (Ideal.Quotient.mkₐ k S) p
        = aeval (fun i => (Ideal.Quotient.mk S) (X i)) p := by
      conv_lhs => rw [MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ k S)]
      rfl
    have h2 : aeval (fun i => (Ideal.Quotient.mk S) (X i)) p
        = aeval (fun i => (Ideal.Quotient.mk S) (C (a i))) p := by rw [funext hX]
    have h3 : aeval (fun i => (Ideal.Quotient.mk S) (C (a i))) p
        = (Ideal.Quotient.mk S) (aeval (fun i => (C (a i) : MvPolynomial (Fin n) k)) p) :=
      (MvPolynomial.comp_aeval_apply (φ := Ideal.Quotient.mkₐ k S) (f := fun i => C (a i))
        p).symm
    have hmk : (Ideal.Quotient.mk S) p = 0 := by
      rw [show (Ideal.Quotient.mk S) p = (Ideal.Quotient.mkₐ k S) p from rfl, h1, h2, h3,
        hC p, hp0]
      simp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · rw [hS]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_vanishingIdeal_iff]
    simp

/-- **Atiyah–Macdonald, Exercise 5.17 (second part)**, deduced from Exercise 5.18: every maximal
ideal of `k[t₁,…,tₙ]`, for `k` algebraically closed, is of the form
`(t₁-a₁,…,tₙ-aₙ)` with `aᵢ ∈ k`. -/
theorem exercise_5_19_isMaximal_iff (P : Ideal (MvPolynomial (Fin n) k)) :
    P.IsMaximal ↔
      ∃ a : Fin n → k,
        P = Ideal.span (Set.range fun i => (X i - C (a i) : MvPolynomial (Fin n) k)) := by
  constructor
  · rintro hP
    obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_isMaximal hP
    refine ⟨a, ?_⟩
    have hle : P ≤ vanishingIdeal k ({a} : Set (Fin n → k)) := fun f hf =>
      (mem_vanishingIdeal_singleton_iff a f).mpr (ha f hf)
    have hmax : (vanishingIdeal k ({a} : Set (Fin n → k))).IsMaximal := inferInstance
    rw [hP.eq_of_le hmax.ne_top hle, vanishingIdeal_singleton_eq_span]
  · rintro ⟨a, rfl⟩
    rw [← vanishingIdeal_singleton_eq_span a]
    infer_instance

/-- Geometric form of Exercise 5.17 (second part): every maximal ideal of `k[t₁,…,tₙ]` is the
vanishing ideal of a point of `kⁿ`, i.e. every maximal ideal "is" a point. -/
theorem exercise_5_19_eq_vanishingIdeal {P : Ideal (MvPolynomial (Fin n) k)} (hP : P.IsMaximal) :
    ∃ a : Fin n → k, P = vanishingIdeal k ({a} : Set (Fin n → k)) := by
  obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_isMaximal hP
  refine ⟨a, ?_⟩
  have hle : P ≤ vanishingIdeal k ({a} : Set (Fin n → k)) := fun f hf =>
    (mem_vanishingIdeal_singleton_iff a f).mpr (ha f hf)
  exact hP.eq_of_le (inferInstance : (vanishingIdeal k ({a} : Set (Fin n → k))).IsMaximal).ne_top hle

/-! ## Exercise 5.17: the weak Nullstellensatz -/

/-- The ideal `I(X)` of an affine algebraic set `X ⊆ kⁿ` (Chapter 1, Exercise 27). -/
def affineIdeal (X : Set (Fin n → k)) : Ideal (MvPolynomial (Fin n) k) :=
  vanishingIdeal k X

/-- `X ⊆ kⁿ` is an affine algebraic variety, in the sense of Chapter 1, Exercise 27 of
Atiyah–Macdonald: it is the set of common zeros of a family of polynomials. -/
def IsAffineAlgebraicVariety (X : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), X = {x | ∀ f ∈ S, aeval x f = 0}

/-- **Atiyah–Macdonald, Exercise 5.17**, reformulation used in the natural proof: every proper ideal
of `k[t₁,…,tₙ]` has a common zero.  It follows from the description of maximal ideals, since a
proper ideal is contained in a maximal one. -/
theorem exercise_5_19_exists_common_zero (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ a : Fin n → k, ∀ f ∈ I, aeval a f = 0 := by
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_isMaximal hP
  exact ⟨a, fun f hf => ha f (hle hf)⟩

/-- **Atiyah–Macdonald, Exercise 5.17 (first part)**, deduced from Exercise 5.18: if `X ⊆ kⁿ` is an
affine algebraic variety over an algebraically closed field and `I(X) ≠ (1)`, then `X` is not
empty. -/
theorem exercise_5_19_weak_nullstellensatz (X : Set (Fin n → k)) (hX : IsAffineAlgebraicVariety X)
    (h : affineIdeal X ≠ ⊤) : X.Nonempty := by
  obtain ⟨S, rfl⟩ := hX
  have hXeq : {x : Fin n → k | ∀ f ∈ S, aeval x f = 0} = zeroLocus k (Ideal.span S) := by
    rw [zeroLocus_span]
  have hspan : Ideal.span S ≠ ⊤ := by
    intro htop
    apply h
    rw [affineIdeal, hXeq, htop, zeroLocus_top]
    exact vanishingIdeal_empty
  obtain ⟨a, ha⟩ := exercise_5_19_exists_common_zero (Ideal.span S) hspan
  exact ⟨a, by rw [hXeq]; exact ha⟩

omit [IsAlgClosed k] in
/-- A non-empty affine algebraic set has a proper vanishing ideal. -/
theorem affineIdeal_ne_top_of_nonempty {X : Set (Fin n → k)} (hX : X.Nonempty) :
    affineIdeal X ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hX
  intro htop
  have h1 : (1 : MvPolynomial (Fin n) k) ∈ affineIdeal X := htop ▸ Submodule.mem_top
  rw [affineIdeal, mem_vanishingIdeal_iff] at h1
  have h2 : aeval a (1 : MvPolynomial (Fin n) k) = 0 := h1 a ha
  rw [map_one] at h2
  exact one_ne_zero h2

/-- **Atiyah–Macdonald, Exercise 5.17 (first part)**, in the form used in the natural proof: the
zero locus of a proper ideal of `k[t₁,…,tₙ]` is not empty. -/
theorem exercise_5_19_zeroLocus_nonempty (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    (zeroLocus k I).Nonempty := by
  obtain ⟨a, ha⟩ := exercise_5_19_exists_common_zero I hI
  exact ⟨a, ha⟩

/-- **Atiyah–Macdonald, Exercise 5.19**: the full content of Exercise 5.17, deduced from Exercise
5.18 — the weak form of Hilbert's Nullstellensatz (if `I(X) ≠ (1)` for an affine algebraic variety
`X ⊆ kⁿ` over an algebraically closed field `k`, then `X` is not empty) together with the
description of the maximal ideals of `k[t₁,…,tₙ]`. -/
theorem exercise_5_19 :
    (∀ X : Set (Fin n → k), IsAffineAlgebraicVariety X → affineIdeal X ≠ ⊤ → X.Nonempty) ∧
      (∀ P : Ideal (MvPolynomial (Fin n) k), P.IsMaximal →
        ∃ a : Fin n → k,
          P = Ideal.span (Set.range fun i => (X i - C (a i) : MvPolynomial (Fin n) k))) :=
  ⟨fun X hX h => exercise_5_19_weak_nullstellensatz X hX h,
    fun P hP => (exercise_5_19_isMaximal_iff P).mp hP⟩

end Main

/-! ## Axiom checks -/

#print axioms exercise_5_18
#print axioms exists_aeval_eq_zero_of_isMaximal
#print axioms vanishingIdeal_singleton_eq_span
#print axioms exercise_5_19_isMaximal_iff
#print axioms exercise_5_19_eq_vanishingIdeal
#print axioms exercise_5_19_exists_common_zero
#print axioms exercise_5_19_weak_nullstellensatz
#print axioms exercise_5_19_zeroLocus_nonempty
#print axioms exercise_5_19

end AtiyahMcdonald69.Ex_5_19
