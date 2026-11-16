/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 2, Exercise 2.5.

Statement (verbatim, from the local transcription of the book, p. 32, end of Chapter 2):

  "5. Let A[x] be the ring of polynomials in one indeterminate over a ring A.
      Prove that A[x] is a flat A-algebra.  [Use Exercise 4.]"

Chapter 2, Exercise 4 (the input the book points to) is: "Let Mᵢ (i ∈ I) be any family of
A-modules, and let M be their direct sum. Prove that M is flat ⟺ each Mᵢ is flat."
The book's definition of flatness (Chapter 2, after Proposition 2.19) is that the functor
`- ⊗_A M` is exact.

Natural proof formalized here (Do Your Exercise, tag 2.5): as an `A`-module,
`A[x] = ⨁_{i ≥ 0} A·xⁱ`; each `A·xⁱ` is isomorphic to `A`, hence flat; a direct sum of flat
modules is flat (Exercise 4).

Contents and audit of that proof:
* §1 proves the internal direct-sum decomposition `A[x] = ⨁ₙ A·xⁿ` (existence and uniqueness
  of the coefficient expansion; this is where finite support of a polynomial is used), and
  identifies the summands concretely (`mem_powSubmodule_iff`: only the `xⁿ`-coefficient may be
  nonzero).
* §2 builds the corresponding linear equivalence `A[x] ≃ₗ[A] ⨁ₙ A` (the `n`-th coordinate is
  the `n`-th coefficient, and the `n`-th copy of `A` maps onto `A·xⁿ`).
* §3 shows each summand `A·xⁿ ≅ A` is flat.
* §4 records the direct-sum step (book Exercise 4) and specialises it to `ℕ` copies of `A`.
* §5 assembles the proof, giving the literal statement: `A[x]` is a flat `A`-algebra.
* §6 spells out the tensor-product content of the conclusion, i.e. exactness of
  `- ⊗_A A[x]`, for modules in arbitrary universes.
* §7 records the multi-variable generalization and the free-module criterion.

No hidden hypothesis is used anywhere: `A` is an arbitrary commutative ring (no Noetherian,
domain, or finiteness assumption), exactly as in the book.  Note also that Mathlib's
`Module.Flat` is the `rTensor`-injectivity (mono-flat) formulation, which over rings is
equivalent to exactness of `- ⊗ M`; the equivalence in the direction needed here is derived
explicitly in §6, so the book's notion of flatness is what is proved.

Formalization conventions: the book's "ring" means a commutative ring with 1, hence `CommRing`
below; `A[X]` is `Polynomial A` with `X : A[X]`, and its `A`-module structure is the one coming
from the `A`-algebra structure (`algebraMap_eq_C`, `smul_polynomial_eq_C_mul`).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_2_5

open Polynomial

universe u v w

variable {A : Type u} [CommRing A]

noncomputable section

/-! ### 1. The summands `A·xⁿ` of `A[x]` and the internal direct-sum decomposition -/

/-- The `A`-submodule `A·xⁿ` of `A[x]`, the `n`-th summand in the decomposition
`A[x] = ⨁_n A·xⁿ` of the natural proof. -/
def powSubmodule (n : ℕ) : Submodule A A[X] := LinearMap.range (Polynomial.monomial n)

theorem mem_powSubmodule {n : ℕ} {p : A[X]} :
    p ∈ powSubmodule (A := A) n ↔ ∃ a : A, Polynomial.monomial n a = p :=
  Iff.rfl

/-- Concretely, `A·xⁿ` consists of the polynomials whose coefficients at all exponents `≠ n`
vanish. -/
theorem mem_powSubmodule_iff (n : ℕ) (p : A[X]) :
    p ∈ powSubmodule (A := A) n ↔ ∀ m, m ≠ n → p.coeff m = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ m hm
    simp [Polynomial.coeff_monomial, Ne.symm hm]
  · intro h
    have hp : p = ∑ i ∈ p.support, Polynomial.monomial i (p.coeff i) := by
      conv_lhs => rw [← Polynomial.sum_monomial_eq p]
      rw [Polynomial.sum_def]
    have hsum : ∑ i ∈ p.support, Polynomial.monomial i (p.coeff i) =
        Polynomial.monomial n (p.coeff n) := by
      refine Finset.sum_eq_single n ?_ ?_
      · intro i _ hne
        rw [h i hne]
        simp
      · intro hn
        have h0 : p.coeff n = 0 := by
          by_contra hc
          exact hn (Polynomial.mem_support_iff.mpr hc)
        simp [h0]
    rw [hp, hsum]
    exact ⟨p.coeff n, rfl⟩

theorem monomial_mem_powSubmodule (n : ℕ) (a : A) :
    Polynomial.monomial n a ∈ powSubmodule (A := A) n :=
  ⟨a, rfl⟩

theorem X_pow_mem_powSubmodule (n : ℕ) : Polynomial.X ^ n ∈ powSubmodule (A := A) n := by
  rw [Polynomial.X_pow_eq_monomial]
  exact monomial_mem_powSubmodule n 1

/-- The summand `A·xⁿ` is spanned by the monomial `xⁿ`. -/
theorem powSubmodule_eq_span (n : ℕ) :
    powSubmodule (A := A) n = Submodule.span A {Polynomial.X ^ n} := by
  refine le_antisymm ?_ ?_
  · rintro p ⟨a, rfl⟩
    have h : Polynomial.monomial n a = a • Polynomial.X ^ n := by
      rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
    rw [h]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact X_pow_mem_powSubmodule n

theorem powSubmodule_eq_span_singleton (n : ℕ) :
    powSubmodule (A := A) n = Submodule.span A {Polynomial.monomial n (1 : A)} := by
  rw [powSubmodule_eq_span, Polynomial.X_pow_eq_monomial]

/-- **Uniqueness** part of `A[x] = ⨁_n A·xⁿ`: the summands are independent
(a linear relation between monomials has all coefficients zero). -/
theorem iSupIndep_powSubmodule : iSupIndep (powSubmodule (A := A)) := by
  rw [show powSubmodule (A := A) = fun n => Submodule.span A {Polynomial.monomial n (1 : A)}
      from funext (powSubmodule_eq_span_singleton (A := A))]
  exact (Polynomial.basisMonomials A).linearIndependent.iSupIndep_span_singleton

/-- **Existence** part of `A[x] = ⨁_n A·xⁿ`: the summands span `A[x]`. -/
theorem iSup_powSubmodule_eq_top : iSup (powSubmodule (A := A)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun p => ?_
  rw [Polynomial.as_sum_range p]
  refine Submodule.sum_mem _ fun n _ => ?_
  exact Submodule.mem_iSup_of_mem n (monomial_mem_powSubmodule n (p.coeff n))

/-- The decomposition `A[x] = ⨁_{n ≥ 0} A·xⁿ` used by the natural proof, as an internal
direct sum of submodules. -/
theorem polynomial_isInternal : DirectSum.IsInternal (powSubmodule (A := A)) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_powSubmodule, iSup_powSubmodule_eq_top⟩

/-! ### 2. `A[x]` as the direct sum of `ℕ` copies of `A` -/

/-- As an `A`-module, `A[x]` is the direct sum of one copy of `A` for each exponent `n`. -/
def polynomialEquivDirectSum : A[X] ≃ₗ[A] (DirectSum ℕ fun _ => A) :=
  (Polynomial.basisMonomials A).repr.trans (finsuppLEquivDirectSum A A ℕ)

/-- The `n`-th coordinate of `p` in this decomposition is the `n`-th coefficient of `p`. -/
theorem polynomialEquivDirectSum_apply (p : A[X]) (n : ℕ) :
    polynomialEquivDirectSum (A := A) p n = p.coeff n := by
  simp [polynomialEquivDirectSum, Polynomial.basisMonomials, Polynomial.toFinsupp_apply]

/-- The `n`-th copy of `A` is mapped to the summand `A·xⁿ`: on monomials the equivalence is
the obvious identification. -/
theorem polynomialEquivDirectSum_monomial (n : ℕ) (a : A) :
    polynomialEquivDirectSum (A := A) (Polynomial.monomial n a) =
      DirectSum.lof A ℕ (fun _ => A) n a := by
  have hrepr : (Polynomial.basisMonomials A).repr (Polynomial.monomial n a) = Finsupp.single n a := by
    have h : Polynomial.monomial n a = a • (Polynomial.monomial n (1 : A)) := by
      rw [Polynomial.smul_eq_C_mul, ← Polynomial.X_pow_eq_monomial,
        Polynomial.C_mul_X_pow_eq_monomial]
    have hval : (Polynomial.basisMonomials A) n = Polynomial.monomial n (1 : A) := by
      rw [Polynomial.coe_basisMonomials]
    rw [h, map_smul, ← hval, Module.Basis.repr_self]
    simp
  simp only [polynomialEquivDirectSum, LinearEquiv.trans_apply, hrepr,
    finsuppLEquivDirectSum_single]

/-! ### 3. Each summand `A·xⁿ` is isomorphic to `A`, hence flat -/

theorem monomial_injective_linearMap (n : ℕ) :
    Function.Injective (Polynomial.monomial n : A →ₗ[A] A[X]) :=
  Polynomial.monomial_injective n

/-- Multiplication by `xⁿ` identifies `A` with the summand `A·xⁿ`. -/
def powSubmoduleEquiv (n : ℕ) : A ≃ₗ[A] powSubmodule (A := A) n :=
  LinearEquiv.ofInjective (Polynomial.monomial n) (monomial_injective_linearMap n)

/-- Each `A·xⁿ` is flat over `A`, being a copy of `A`. -/
theorem powSubmodule_flat (n : ℕ) : Module.Flat A (powSubmodule (A := A) n) :=
  Module.Flat.of_linearEquiv (powSubmoduleEquiv n).symm

/-! ### 4. Book Exercise 2.4 (input): a direct sum of flat modules is flat -/

/-- Chapter 2, Exercise 4, in the direction used by the proof of Exercise 2.5. -/
theorem flat_directSum {ι : Type v} {M : ι → Type w} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (h : ∀ i, Module.Flat A (M i)) :
    Module.Flat A (DirectSum ι M) :=
  letI := h
  Module.Flat.directSum

/-- The direct sum of `ℕ` copies of `A` is flat. -/
theorem flat_directSum_copies : Module.Flat A (DirectSum ℕ fun _ => A) :=
  flat_directSum fun _ => Module.Flat.self

/-! ### 5. Exercise 2.5: `A[x]` is a flat `A`-algebra -/

/-- **Atiyah–Macdonald, Chapter 2, Exercise 2.5.** For every commutative ring `A`, the
polynomial ring `A[x]` is flat as an `A`-module: the `A`-algebra `A[x]` is flat. -/
theorem polynomial_flat : Module.Flat A A[X] :=
  letI := flat_directSum_copies (A := A)
  Module.Flat.of_linearEquiv (polynomialEquivDirectSum (A := A))

/-- Exercise 2.5 in the book's own form, quantified over all rings `A`. -/
theorem exercise_2_5 (A : Type u) [CommRing A] : Module.Flat A A[X] :=
  polynomial_flat

/-- `A[x]` is a free `A`-module (the monomials form a basis). -/
theorem polynomial_free : Module.Free A A[X] :=
  Module.Free.of_basis (Polynomial.basisMonomials A)

/-- Alternative proof of Exercise 2.5: a free module is flat, and `A[x]` is free. -/
theorem polynomial_flat_of_free : Module.Flat A A[X] :=
  letI := polynomial_free (A := A)
  Module.Flat.of_free

/-- The `A`-module structure of `A[x]` used above is the one given by its `A`-algebra
structure: `A` maps to the constant polynomials. -/
theorem algebraMap_eq_C : algebraMap A A[X] = Polynomial.C := Polynomial.algebraMap_eq

/-- The scalar action is multiplication by constant polynomials, as for any `A`-algebra. -/
theorem smul_polynomial_eq_C_mul (a : A) (p : A[X]) : a • p = Polynomial.C a * p :=
  Polynomial.smul_eq_C_mul a

/-! ### 6. The tensor-product content: `- ⊗_A A[x]` is an exact functor -/

/-- Flatness of `A[x]` in the book's formulation: tensoring an injective map of `A`-modules
with `A[x]` keeps it injective (modules in arbitrary universes). -/
theorem rTensor_polynomial_injective {M : Type v} {N : Type w} [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Injective (f.rTensor A[X]) :=
  letI := polynomial_flat (A := A)
  Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- Flatness of `A[x]` as exactness of `- ⊗_A A[x]`: an exact sequence of `A`-modules stays
exact after tensoring with `A[x]`. -/
theorem tensorProduct_polynomial_exact {M : Type v} {N : Type w} {P : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module A M] [Module A N] [Module A P] (f : M →ₗ[A] N)
    (g : N →ₗ[A] P) (h : Function.Exact f g) :
    Function.Exact (f.rTensor A[X]) (g.rTensor A[X]) :=
  letI := polynomial_flat (A := A)
  Module.Flat.rTensor_exact (A[X]) h

/-- A short exact sequence of `A`-modules remains exact, and stays injective/surjective, after
tensoring with `A[x]`. -/
theorem shortExact_rTensor_polynomial {M : Type v} {N : Type w} {P : Type*} [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module A M] [Module A N] [Module A P] (f : M →ₗ[A] N)
    (g : N →ₗ[A] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    Function.Injective (f.rTensor A[X]) ∧ Function.Surjective (g.rTensor A[X]) ∧
      Function.Exact (f.rTensor A[X]) (g.rTensor A[X]) :=
  ⟨rTensor_polynomial_injective f hf, LinearMap.rTensor_surjective (A[X]) hg,
    tensorProduct_polynomial_exact f g h⟩

/-- In particular, tensoring the inclusion of an ideal `I ≤ A` with `A[x]` stays injective. -/
theorem ideal_rTensor_polynomial_injective (I : Ideal A) :
    Function.Injective (LinearMap.rTensor A[X] (Submodule.subtype I)) :=
  rTensor_polynomial_injective _ (Submodule.subtype_injective I)

/-! ### 7. Generalizations -/

/-- Free modules are flat (the `A[x]`-case is what Exercise 2.5 asks for). -/
theorem flat_of_free {M : Type w} [AddCommGroup M] [Module A M] [Module.Free A M] :
    Module.Flat A M :=
  Module.Flat.of_free

/-- `A[x₁, …, xₙ]` is a flat `A`-module: the multi-variable version of Exercise 2.5. -/
theorem mvPolynomial_flat (σ : Type v) : Module.Flat A (MvPolynomial σ A) :=
  Module.Flat.of_free

/-- Concrete instances, including a ring with zero-divisors and a ring of characteristic `4`. -/
example : Module.Flat ℤ ℤ[X] := polynomial_flat

example : Module.Flat (ZMod 4) (ZMod 4)[X] := polynomial_flat

end

end AtiyahMcdonald69.Ex_2_5

#print axioms AtiyahMcdonald69.Ex_2_5.mem_powSubmodule_iff
#print axioms AtiyahMcdonald69.Ex_2_5.polynomial_isInternal
#print axioms AtiyahMcdonald69.Ex_2_5.polynomialEquivDirectSum_apply
#print axioms AtiyahMcdonald69.Ex_2_5.polynomialEquivDirectSum_monomial
#print axioms AtiyahMcdonald69.Ex_2_5.powSubmodule_flat
#print axioms AtiyahMcdonald69.Ex_2_5.flat_directSum_copies
#print axioms AtiyahMcdonald69.Ex_2_5.polynomial_flat
#print axioms AtiyahMcdonald69.Ex_2_5.exercise_2_5
#print axioms AtiyahMcdonald69.Ex_2_5.polynomial_flat_of_free
#print axioms AtiyahMcdonald69.Ex_2_5.rTensor_polynomial_injective
#print axioms AtiyahMcdonald69.Ex_2_5.tensorProduct_polynomial_exact
#print axioms AtiyahMcdonald69.Ex_2_5.shortExact_rTensor_polynomial
#print axioms AtiyahMcdonald69.Ex_2_5.ideal_rTensor_polynomial_injective
#print axioms AtiyahMcdonald69.Ex_2_5.mvPolynomial_flat
