/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 8 ("Artin rings"),
Exercise 4.

Reference natural-language solution (public dataset):
  `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-8-4/proof.tex`
  https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8.4

## The exercise

Let `A → B` be a ring homomorphism and let `Spec B → Spec A`, `q ↦ q ∩ A`, be the induced map
of prime spectra.  The fibre of this map over a prime `p` of `A` is the set of primes of `B`
lying over `p` (`p.primesOver B`).  The exercise's assertions, recovered from the reference
proof (whose cited inputs are A–M 3.21, 8.2 and 8.3), are:

* (3.21) the fibre over `p` is homeomorphic to `Spec (κ(p) ⊗[A] B)` (the "fibre algebra");
* if `B` is a finite `A`-module, the fibre algebra is a finite dimensional `κ(p)`-vector
  space, and hence each fibre is a finite, discrete set (`B` is "quasi-finite" over `A`);
* the dictionary used for the converse: for `B` a finitely generated `A`-algebra, the fibre
  over `p` is discrete iff the fibre algebra is finite dimensional over `κ(p)`
  (this is A–M 8.2, "Noetherian rings with discrete spectrum are Artinian", combined with
  A–M 8.3, "a finitely generated algebra over a field is Artinian iff it is finite
  dimensional");
* consequently, over an Artinian base ring `A` and for a finitely generated `A`-algebra `B`,
  finiteness of all fibres is equivalent to `B` being a finite `A`-module;
* the finite generation hypothesis cannot be dropped, even for integral extensions: the
  integral extension `ℚ → ℚ̄` has a one-point fibre but `ℚ̄` is not a finite `ℚ`-module
  (subextensions contain roots of the Eisenstein polynomials `tⁿ - 2` for all `n`, so the
  degree over `ℚ` is infinite).

## Formalisation notes

Everything is stated for commutative rings `A`, `B` with `[Algebra A B]`, the fibre over `p`
being the subtype `↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p})`.  The fibre algebra is
Mathlib's `p.asIdeal.Fiber B = κ(p) ⊗[A] B`, and `PrimeSpectrum.preimageHomeomorphFiber`
provides the homeomorphism of A–M 3.21.  The general theory of quasi-finite algebras
(`Algebra.QuasiFinite`) supplies the "finite ⇒ finite fibres" direction; the lemmas
`Module.finite_iff_isArtinianRing` and
`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` are the formal counterparts of
A–M 8.3 and 8.2 used by the book's argument.

No `sorry`/`admit`, no custom axioms; the exercise's own objects are used throughout (no
existential abstractions).  The final part of the exercise is stated with the concrete
integral extension `ℚ → ℚ̄ = AlgebraicClosure ℚ`.
-/
import Mathlib

open Polynomial

namespace AtiyahMcdonald69.Ex_8_4

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-! ## (0) The fibre as the spectrum of the fibre algebra (A–M 3.21) -/

/-- **A–M 3.21 (preliminary to exercise 8.4)**: the fibre of `Spec B → Spec A` over a prime `p`
is homeomorphic to the spectrum of the fibre algebra `p.Fiber B = κ(p) ⊗[A] B`. -/
noncomputable def fibreHomeomorph (p : PrimeSpectrum A) :
    ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) ≃ₜ PrimeSpectrum (p.asIdeal.Fiber B) :=
  PrimeSpectrum.preimageHomeomorphFiber A B p

/-- The primes of `B` lying over a prime `p` of `A` are the primes of the fibre algebra. -/
noncomputable def primesOverEquiv (p : Ideal A) [p.IsPrime] :
    ↥(p.primesOver B) ≃ PrimeSpectrum (p.Fiber B) :=
  (PrimeSpectrum.primesOverOrderIsoFiber A B p).toEquiv

/-! ## (1) A finite module has finite dimensional fibre algebras, hence finite fibres -/

/-- **Exercise 8.4, first assertion, algebraic form**: if `B` is a finite `A`-module then the
fibre algebra `κ(p) ⊗[A] B` is a finite dimensional `κ(p)`-vector space.  (The images of module
generators of `B` span the fibre algebra.) -/
theorem finite_fibreAlgebra (h : Module.Finite A B) (p : Ideal A) [p.IsPrime] :
    Module.Finite p.ResidueField (p.Fiber B) :=
  Algebra.QuasiFinite.finite_fiber p

/-- **Exercise 8.4, first assertion**: if `B` is a finite `A`-module then every fibre of
`Spec B → Spec A` is a finite set. -/
theorem finite_fibre (h : Module.Finite A B) (p : PrimeSpectrum A) :
    (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}).Finite :=
  Algebra.QuasiFinite.finite_comap_preimage_singleton p

/-- **Exercise 8.4, first assertion**: if `B` is a finite `A`-module then every fibre of
`Spec B → Spec A` is a discrete topological space. -/
theorem isDiscrete_fibre (h : Module.Finite A B) (p : PrimeSpectrum A) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) :=
  Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton p

/-- If `B` is a finite `A`-module, then only finitely many primes of `B` lie over a given
ideal of `A`. -/
theorem finite_primesOver (h : Module.Finite A B) (I : Ideal A) : (I.primesOver B).Finite :=
  Algebra.QuasiFinite.finite_primesOver I

/-- **Exercise 8.4, first assertion, quantitative form**: if `f : Fin n → B` generates `B` as an
`A`-module, then the images `1 ⊗ fᵢ` generate the fibre algebra `κ(p) ⊗[A] B` as a
`κ(p)`-module.  (This is the step "its generators span every fibre algebra over the
corresponding residue field" of the reference proof.) -/
theorem fibre_algebra_span_eq_top {n : ℕ} (f : Fin n → B)
    (hf : Submodule.span A (Set.range f) = ⊤) (p : Ideal A) [p.IsPrime] :
    Submodule.span p.ResidueField
      (Set.range fun i => (1 : p.ResidueField) ⊗ₜ[A] f i) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine TensorProduct.induction_on x (Submodule.zero_mem _) ?_ ?_
  · intro a b
    have hb : b ∈ Submodule.span A (Set.range f) := by rw [hf]; exact Submodule.mem_top
    refine Submodule.span_induction (s := Set.range f)
      (p := fun b _ => a ⊗ₜ[A] b ∈
        Submodule.span p.ResidueField (Set.range fun i => (1 : p.ResidueField) ⊗ₜ[A] f i))
      ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨i, rfl⟩
      have h1 : a ⊗ₜ[A] f i = a • ((1 : p.ResidueField) ⊗ₜ[A] f i) := by
        rw [TensorProduct.smul_tmul']
        simp
      rw [h1]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
    · simp
    · intro y z _ _ hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
    · intro c y _ hy
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul p.ResidueField c]
      exact Submodule.smul_mem _ _ hy
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- **Exercise 8.4, quantitative form of the first assertion**: if `B` is generated by `n`
elements as an `A`-module, then every fibre algebra has dimension at most `n` over the residue
field.  (Combined with the Chinese remainder count for finite dimensional algebras, this is the
bound "each fibre has at most `N` points" used in Exercise 8.5.) -/
theorem finrank_fibre_algebra_le {n : ℕ} (f : Fin n → B)
    (hf : Submodule.span A (Set.range f) = ⊤) (p : Ideal A) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber B) ≤ n := by
  have hspan := fibre_algebra_span_eq_top f hf p
  have hsurj : Function.Surjective (Fintype.linearCombination p.ResidueField
      (fun i => (1 : p.ResidueField) ⊗ₜ[A] f i)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  have h := LinearMap.finrank_le_finrank_of_surjective hsurj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

/-! ## (2) The fibre/discreteness dictionary (A–M 8.2 + 8.3) -/

/-- **A–M 8.3**: a finitely generated algebra over a field is a finite module iff it is an
Artinian ring. -/
theorem finite_iff_isArtinianRing {k C : Type*} [Field k] [CommRing C] [Algebra k C]
    [Algebra.FiniteType k C] : Module.Finite k C ↔ IsArtinianRing C :=
  Module.finite_iff_isArtinianRing k C

/-- **A–M 8.2 + 8.3**: a finitely generated algebra over a field has discrete spectrum iff it
is finite dimensional over that field. -/
theorem spectrum_discrete_iff_finite_module {k C : Type*} [Field k] [CommRing C] [Algebra k C]
    [Algebra.FiniteType k C] : DiscreteTopology (PrimeSpectrum C) ↔ Module.Finite k C := by
  constructor
  · intro h
    refine (Module.finite_iff_krullDimLE_zero k C).mpr ?_
    exact (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp h).2
  · intro h
    exact Algebra.QuasiFinite.discreteTopology_primeSpectrum k C

/-- **Exercise 8.4, the dictionary used for the converse**: for a finitely generated
`A`-algebra `B`, the fibre of `Spec B → Spec A` over `p` is discrete iff the fibre algebra is a
finite dimensional `κ(p)`-vector space. -/
theorem fibre_discrete_iff_finite_fibreAlgebra [Algebra.FiniteType A B] (p : PrimeSpectrum A) :
    DiscreteTopology ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) ↔
      Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  rw [(fibreHomeomorph p).discreteTopology_iff]
  exact spectrum_discrete_iff_finite_module

/-! ## (3) The converse over an Artinian base ring -/

/-- **Exercise 8.4, converse for an Artinian base.**  If `A` is Artinian and `B` is a finitely
generated `A`-algebra, then `B` is a finite `A`-module iff every fibre of `Spec B → Spec A` is a
finite set. -/
theorem finite_iff_finite_fibres [IsArtinianRing A] [Algebra.FiniteType A B] :
    Module.Finite A B ↔ ∀ p : PrimeSpectrum A,
      (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}).Finite := by
  rw [← Algebra.QuasiFinite.iff_of_isArtinianRing (R := A) (S := B),
    ← Algebra.QuasiFinite.iff_finite_comap_preimage_singleton (R := A) (S := B)]

/-- **Exercise 8.4, converse for an Artinian base, fibre algebra form**: if `A` is Artinian,
then `B` is a finite `A`-module iff every fibre algebra `κ(p) ⊗[A] B` is a finite dimensional
`κ(p)`-vector space. -/
theorem finite_iff_finite_fibreAlgebra [IsArtinianRing A] :
    Module.Finite A B ↔ ∀ (p : Ideal A) [p.IsPrime], Module.Finite p.ResidueField (p.Fiber B) := by
  constructor
  · intro h p _
    exact finite_fibreAlgebra h p
  · intro h
    exact Algebra.QuasiFinite.iff_of_isArtinianRing.mp ⟨fun p _ => h p⟩

/-- **Exercise 8.4, converse for an Artinian base, discreteness form**: if `A` is Artinian and
`B` is a finitely generated `A`-algebra, then `B` is a finite `A`-module iff every fibre of
`Spec B → Spec A` is discrete. -/
theorem finite_iff_discrete_fibres [IsArtinianRing A] [Algebra.FiniteType A B] :
    Module.Finite A B ↔ ∀ p : PrimeSpectrum A,
      DiscreteTopology ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) := by
  rw [finite_iff_finite_fibreAlgebra]
  constructor
  · intro h p
    exact (fibre_discrete_iff_finite_fibreAlgebra p).mpr (h p.asIdeal)
  · intro h p hp
    exact (fibre_discrete_iff_finite_fibreAlgebra ⟨p, hp⟩).mp (h ⟨p, hp⟩)

/-- Remark: a finitely generated `A`-algebra which is integral over `A` is a finite `A`-module
(A–M, remark before Corollary 5.4).  Thus in the finite type situation the converse of the
first assertion is automatic, which is why the counterexample (4) below must be an infinitely
generated algebra. -/
theorem finite_of_isIntegral_of_finiteType [Algebra.IsIntegral A B] [Algebra.FiniteType A B] :
    Module.Finite A B :=
  Algebra.IsIntegral.finite

/-! ## (4) The converse fails without finite generation: the integral extension `ℚ → ℚ̄` -/

/-- `2` is not a `p`-th power in `ℚ` for any prime `p` (the `2`-adic valuation of a `p`-th power
is divisible by `p`, while the `2`-adic valuation of `2` is `1`). -/
theorem two_not_pow (p : ℕ) (hp : p.Prime) (b : ℚ) : b ^ p ≠ 2 := by
  intro h
  have hself : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (show 1 < 2 by norm_num)
  have h2 : padicValRat 2 (b ^ p) = 1 := by
    rw [h]
    exact hself
  have h1 : padicValRat 2 (b ^ p) = (p : ℤ) * padicValRat 2 b :=
    padicValRat.pow (p := 2) (hp := ⟨Nat.prime_two⟩) b
  rw [h1] at h2
  have hdvd : (p : ℤ) ∣ (1 : ℤ) := ⟨padicValRat 2 b, h2.symm⟩
  have : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.not_dvd_one this

/-- `ℚ̄` is integral over `ℚ`. -/
theorem algebraicClosure_isIntegral : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
  @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _ (AlgebraicClosure.isAlgebraic ℚ)

/-- **The key point of the counterexample**: `ℚ̄` is not a finite `ℚ`-module.  If it were of
finite dimension `d`, a prime `p > d` would give a root `x` of the Eisenstein polynomial
`tᵖ - 2`; the minimal polynomial of `x` then has degree `p > d`, contradicting the tower
bound `deg (minpoly ℚ x) ≤ [ℚ̄ : ℚ]`. -/
theorem not_finite_algebraicClosure : ¬ Module.Finite ℚ (AlgebraicClosure ℚ) := by
  intro h
  obtain ⟨p, hpd, hp⟩ := Nat.exists_infinite_primes (Module.finrank ℚ (AlgebraicClosure ℚ) + 1)
  have hlt : Module.finrank ℚ (AlgebraicClosure ℚ) < p := by omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure ℚ) hp.pos
  have haeval : aeval x (X ^ p - C (2:ℚ)) = 0 := by
    simp [hx]
  have hirr : Irreducible (X ^ p - C (2:ℚ)) :=
    (X_pow_sub_C_irreducible_iff_of_prime hp).mpr (fun b => two_not_pow p hp b)
  have hmin : X ^ p - C (2:ℚ) = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hirr haeval (monic_X_pow_sub_C _ hp.ne_zero)
  have hdeg : (minpoly ℚ x).natDegree = p := by
    rw [← hmin, natDegree_X_pow_sub_C]
  have hle := minpoly.natDegree_le (A := ℚ) (B := AlgebraicClosure ℚ) x
  rw [hdeg] at hle
  exact absurd hle (not_le.mpr hlt)

/-- Every fibre of `Spec ℚ̄ → Spec ℚ` is the whole of `Spec ℚ̄`, a one-point space: `ℚ̄` is a
field, and `Spec ℚ` is a single point as well. -/
theorem algebraicClosure_fibre_eq_univ (p : PrimeSpectrum ℚ) :
    PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p} = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  simp [Subsingleton.elim (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) x) p]

/-- Every fibre of `Spec ℚ̄ → Spec ℚ` is a single point. -/
theorem algebraicClosure_fibre_subsingleton (p : PrimeSpectrum ℚ) :
    (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}).Subsingleton := by
  rw [algebraicClosure_fibre_eq_univ]
  exact Set.subsingleton_univ

/-- Every fibre of `Spec ℚ̄ → Spec ℚ` is finite. -/
theorem algebraicClosure_fibre_finite (p : PrimeSpectrum ℚ) :
    (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}).Finite := by
  exact Set.finite_univ.subset (Set.subset_univ _)

/-- Every fibre of `Spec ℚ̄ → Spec ℚ` is discrete. -/
theorem algebraicClosure_fibre_isDiscrete (p : PrimeSpectrum ℚ) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}) := by
  rw [isDiscrete_iff_discreteTopology]
  exact inferInstance

/-- **Exercise 8.4, counterexample**: the integral extension `ℚ → ℚ̄` has finite (indeed
one-point) fibres, but `ℚ̄` is not a finite `ℚ`-module.  Hence "finite fibres" does not imply
"finite module" for integral extensions, and the finite generation hypothesis in (3) cannot be
dropped. -/
theorem counterexample :
    Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) ∧
      (∀ p : PrimeSpectrum ℚ,
        (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}).Finite ∧
        IsDiscrete (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}) ∧
        (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}).Subsingleton) ∧
      ¬ Module.Finite ℚ (AlgebraicClosure ℚ) :=
  ⟨algebraicClosure_isIntegral,
    fun p => ⟨algebraicClosure_fibre_finite p, algebraicClosure_fibre_isDiscrete p,
      algebraicClosure_fibre_subsingleton p⟩,
    not_finite_algebraicClosure⟩

/-- **Exercise 8.4, the converse is false**: the implication "all fibres of `Spec B → Spec A`
are finite ⇒ `B` is a finite `A`-module" fails in general. -/
theorem converse_fails :
    ¬ ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
        (∀ p : PrimeSpectrum A, (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}).Finite) →
        Module.Finite A B := by
  intro H
  exact not_finite_algebraicClosure (H ℚ (AlgebraicClosure ℚ) algebraicClosure_fibre_finite)

/-! ## The exercise, bundled -/

/-- **Atiyah–Macdonald, Exercise 8.4** (all assertions, including the counterexample). -/
theorem solution :
    -- (0) the fibre is the spectrum of the fibre algebra, and (1) a finite module has
    -- finite dimensional fibre algebras, hence finite and discrete fibres
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.Finite A B →
      (∀ p : PrimeSpectrum A,
        Nonempty (↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) ≃ₜ
          PrimeSpectrum (p.asIdeal.Fiber B))) ∧
      (∀ p : PrimeSpectrum A, Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B)) ∧
      (∀ p : PrimeSpectrum A, (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}).Finite) ∧
      (∀ p : PrimeSpectrum A, IsDiscrete (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}))) ∧
    -- (2) the fibre/discreteness dictionary for finitely generated algebras
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.FiniteType A B →
      ∀ p : PrimeSpectrum A,
        DiscreteTopology ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) ↔
          Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B)) ∧
    -- (3) the converse over an Artinian base ring
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
      IsArtinianRing A → Algebra.FiniteType A B →
        (Module.Finite A B ↔ ∀ p : PrimeSpectrum A,
          (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}).Finite)) ∧
    -- (3') the same converse in fibre-algebra form
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsArtinianRing A →
      (Module.Finite A B ↔
        ∀ (p : Ideal A) [p.IsPrime], Module.Finite p.ResidueField (p.Fiber B))) ∧
    -- (3'') the same converse in discreteness form
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
      IsArtinianRing A → Algebra.FiniteType A B →
        (Module.Finite A B ↔ ∀ p : PrimeSpectrum A,
          DiscreteTopology ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}))) ∧
    -- (3''') integral algebras of finite type are finite, so (4) has to be infinitely generated
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
      Algebra.IsIntegral A B → Algebra.FiniteType A B → Module.Finite A B) ∧
    -- (4) the counterexample showing that finite generation cannot be dropped
    (Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) ∧
      (∀ p : PrimeSpectrum ℚ,
        (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p}).Finite ∧
        IsDiscrete (PrimeSpectrum.comap (algebraMap ℚ (AlgebraicClosure ℚ)) ⁻¹' {p})) ∧
      ¬ Module.Finite ℚ (AlgebraicClosure ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B _ _ _ h
    exact ⟨fun p => ⟨fibreHomeomorph p⟩, fun p => finite_fibreAlgebra h p.asIdeal,
      fun p => finite_fibre h p, fun p => isDiscrete_fibre h p⟩
  · intro A B _ _ _ hfin p
    exact fibre_discrete_iff_finite_fibreAlgebra p
  · intro A B _ _ _ hArt hfin
    exact finite_iff_finite_fibres
  · intro A B _ _ _ hArt
    exact finite_iff_finite_fibreAlgebra
  · intro A B _ _ _ hArt hfin
    exact finite_iff_discrete_fibres
  · intro A B _ _ _ hInt hfin
    exact finite_of_isIntegral_of_finiteType
  · refine ⟨algebraicClosure_isIntegral, fun p =>
      ⟨algebraicClosure_fibre_finite p, algebraicClosure_fibre_isDiscrete p⟩,
      not_finite_algebraicClosure⟩

end AtiyahMcdonald69.Ex_8_4
