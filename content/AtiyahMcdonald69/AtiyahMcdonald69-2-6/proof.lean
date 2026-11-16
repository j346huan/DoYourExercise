/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Atiyah–Macdonald formalization swarm, member m9.
-/

import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 2, Exercise 2.6

*Statement (Atiyah–Macdonald, Chapter 2, Exercise 6).* For any `A`-module `M`, let `M[x]`
denote the set of all polynomials in `x` with coefficients in `M`, that is to say expressions of
the form `m₀ + m₁ x + ⋯ + m_r x^r` (`m_i ∈ M`). Defining the product of an element of `A[x]` and
an element of `M[x]` in the obvious way, show that `M[x]` is an `A[x]`-module. Show that
`M[x] ≅ A[x] ⊗_A M`.

This file formalizes the statement for a commutative ring `A` and an `A`-module `M`.

* `Mx A M` is `ℕ →₀ M`, the type of finitely supported families of coefficients, i.e. `M[x]`.
* `instModulePolynomial` is the `A[X]`-module structure on `M[x]` ("the obvious product"): `X`
  acts by shifting the coefficients, `A` acts coefficientwise; this is packaged as
  `smulHom : A[X] →ₐ[A] End_A(M[x])`.
* `C_smul`, `X_smul`, `monomial_smul_single` record the product: `(a x^i) * (m x^j) = (a·m) x^{i+j}`.
* `smul_apply_eq_sum` records the coefficient formula for the product of an arbitrary polynomial
  with an arbitrary element of `M[x]`.
* `toTensor` and `ofTensor` are the two maps `M[x] → A[x] ⊗_A M`, `∑ m_i x^i ↦ ∑ x^i ⊗ m_i`, and
  `A[x] ⊗_A M → M[x]`, `f ⊗ m ↦ f · m` (the latter is induced, via the universal property of the
  tensor product, by the `A`-bilinear map `(f, m) ↦ f · m`). `tensorEquiv` is the resulting
  `A[x]`-linear equivalence `A[x] ⊗_A M ≃ M[x]`.
-/

open scoped TensorProduct

open Polynomial

namespace AtiyahMcdonald69.Ex_2_6

universe u v

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

/-- `M[x]`: polynomials in the indeterminate `x` with coefficients in the `A`-module `M`,
i.e. finitely supported families of coefficients.  The parameter `A` records the module
structure with which `M` is considered. -/
@[nolint unusedArguments]
abbrev Mx (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M] : Type v :=
  ℕ →₀ M

/-- Multiplication by `x` on `M[x]`: shift every coefficient up by one. -/
noncomputable def xsmul : Mx A M →ₗ[A] Mx A M :=
  Finsupp.lmapDomain M A Nat.succ

/-- The structure map `A[x] → End_A(M[x])` of "the obvious product": `x` acts by `xsmul` and
`A` acts coefficientwise.  This is the `A`-algebra homomorphism through which `A[x]` acts on
`M[x]`. -/
noncomputable def smulHom : A[X] →ₐ[A] Module.End A (Mx A M) :=
  Polynomial.aeval (xsmul A M)

/-- **Exercise 2.6, first part.** `M[x]` is an `A[x]`-module, with the product defined by
distributing and setting `(a x^i) * (m x^j) = (a·m) x^{i+j}`. -/
noncomputable instance instModulePolynomial : Module A[X] (Mx A M) :=
  Module.compHom (Mx A M) (smulHom A M).toRingHom

theorem smul_def (p : A[X]) (f : Mx A M) : p • f = smulHom A M p f :=
  rfl

/-- The image of `1` under `smulHom` is the identity endomorphism. -/
@[simp]
theorem smulHom_one : smulHom A M 1 = 1 :=
  map_one _

/-- `smulHom` is a ring homomorphism: the action of a product is the composite action. -/
theorem smulHom_mul (p q : A[X]) :
    smulHom A M (p * q) = smulHom A M p * smulHom A M q :=
  map_mul _ _ _

/-- Constants act coefficientwise: this is the `A`-linear structure of `M[x]`. -/
theorem C_smul (a : A) (f : Mx A M) : (Polynomial.C a) • f = a • f := by
  rw [smul_def, smulHom, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  simp

/-- The indeterminate acts by shifting the coefficients. -/
theorem X_smul (f : Mx A M) : (Polynomial.X : A[X]) • f = xsmul A M f := by
  rw [smul_def, smulHom, Polynomial.aeval_X]

/-- `X` acts on a monomial by shifting it. -/
theorem X_smul_single (j : ℕ) (m : M) :
    (Polynomial.X : A[X]) • (Finsupp.single j m : Mx A M) = Finsupp.single (j + 1) m := by
  rw [X_smul, xsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Powers of `X` act on a monomial by shifting it by that power. -/
theorem X_pow_smul_single (i j : ℕ) (m : M) :
    ((Polynomial.X : A[X]) ^ i) • (Finsupp.single j m : Mx A M) =
      Finsupp.single (j + i) m := by
  revert j m
  induction i with
  | zero => intro j m; simp
  | succ k ih =>
      intro j m
      rw [pow_succ, mul_smul, X_smul_single, ih, Nat.add_assoc, Nat.add_comm 1 k]

/-- **The product of monomials**: `(a x^i) * (m x^j) = (a·m) x^{i+j}`.  This is the formula
that defines "the obvious product" of `A[x]` on `M[x]`. -/
theorem monomial_smul_single (i : ℕ) (a : A) (j : ℕ) (m : M) :
    (Polynomial.monomial i a) • (Finsupp.single j m : Mx A M) =
      Finsupp.single (i + j) (a • m) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul, X_pow_smul_single, C_smul,
    Finsupp.smul_single, Nat.add_comm]

/-- `A[x]` acts on `M[x]` through `A`-linear endomorphisms and the action of `A` is the given
one: this is the compatibility making `M[x]` an `A`-module inside its `A[x]`-module structure. -/
instance instIsScalarTower : IsScalarTower A A[X] (Mx A M) where
  smul_assoc a p f := by
    rw [Polynomial.smul_eq_C_mul, mul_smul, C_smul]

/-- `x^i` acts on `M[x]` by shifting the coefficients by `i`. -/
theorem X_pow_smul_eq_mapDomain (i : ℕ) (f : Mx A M) :
    ((Polynomial.X : A[X]) ^ i) • f = Finsupp.mapDomain (· + i) f := by
  revert f
  induction i with
  | zero =>
      intro f
      rw [pow_zero, one_smul, show (fun x : ℕ => x + 0) = id from rfl]
      exact (Finsupp.mapDomain_id).symm
  | succ k ih =>
      intro f
      rw [pow_succ, mul_smul, ih, X_smul, xsmul, Finsupp.lmapDomain_apply,
        ← Finsupp.mapDomain_comp]
      congr 1
      funext j
      rw [Function.comp_apply, Nat.succ_eq_add_one, Nat.add_assoc]
      omega

/-- The product of a monomial with an arbitrary element of `M[x]`. -/
theorem monomial_smul_eq_mapDomain (i : ℕ) (a : A) (f : Mx A M) :
    (Polynomial.monomial i a) • f = a • Finsupp.mapDomain (· + i) f := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul, X_pow_smul_eq_mapDomain, C_smul]

/-- Coefficient formula for the shift of coefficients by `i`. -/
theorem mapDomain_add_apply (i : ℕ) (f : Mx A M) (n : ℕ) :
    (Finsupp.mapDomain (· + i) f) n = if i ≤ n then f (n - i) else 0 := by
  have hinj : Function.Injective (fun x : ℕ => x + i) := fun a b hab => Nat.add_right_cancel hab
  by_cases h : i ≤ n
  · rw [if_pos h]
    calc (Finsupp.mapDomain (· + i) f) n
        = (Finsupp.mapDomain (· + i) f) ((n - i) + i) := by rw [Nat.sub_add_cancel h]
      _ = f (n - i) := Finsupp.mapDomain_apply hinj f (n - i)
  · rw [if_neg h]
    refine Finsupp.mapDomain_of_notMem_range f n ?_
    rintro ⟨k, hk⟩
    simp only at hk
    omega

/-- The coefficient of `x^n` in the product of the monomial `a x^i` with `f`. -/
theorem monomial_smul_apply (i : ℕ) (a : A) (f : Mx A M) (n : ℕ) :
    ((Polynomial.monomial i a) • f) n = if i ≤ n then a • f (n - i) else 0 := by
  rw [monomial_smul_eq_mapDomain, Finsupp.smul_apply, mapDomain_add_apply]
  by_cases h : i ≤ n <;> simp [h]

/-- **The "obvious product"**, in coordinates: the coefficient of `x^n` in `p · f` is the sum
over `i + j = n` of `(coeff i of p) · (coeff j of f)`. -/
theorem smul_apply_eq_sum_range (p : A[X]) (f : Mx A M) (n : ℕ) :
    (p • f) n = ∑ k ∈ Finset.range (n + 1), p.coeff k • f (n - k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_smul, Finsupp.add_apply, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Polynomial.coeff_add, add_smul]
  | monomial i a =>
      rw [monomial_smul_apply]
      simp only [Polynomial.coeff_monomial]
      by_cases h : i ≤ n
      · rw [if_pos h, Finset.sum_eq_single i]
        · simp
        · intro b _ hbi
          rw [if_neg (Ne.symm hbi), zero_smul]
        · intro hi
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) hi
      · rw [if_neg h, Finset.sum_eq_zero]
        intro k hk
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [if_neg (fun hki => h (by rw [hki]; exact hk')), zero_smul]

/-- **The "obvious product"**, in coordinates: the coefficient of `x^n` in `p · f` is the sum
over the antidiagonal `i + j = n` of `(coeff i of p) · (coeff j of f)`. -/
theorem smul_apply_eq_sum (p : A[X]) (f : Mx A M) (n : ℕ) :
    (p • f) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff ij.1 • f ij.2 := by
  rw [smul_apply_eq_sum_range,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => p.coeff k • f l) n]

/-! ### The isomorphism `M[x] ≃ A[x] ⊗_A M` -/

/-- The `A`-linear map `M[x] → A[x] ⊗_A M`, `∑ m_i x^i ↦ ∑ x^i ⊗ m_i`. -/
noncomputable def toTensor : Mx A M →ₗ[A] A[X] ⊗[A] M :=
  Finsupp.lsum (α := ℕ) (M := M) (N := A[X] ⊗[A] M) (R := A) (R₂ := A) (S := A)
    (σ := RingHom.id A) fun i => TensorProduct.mk A A[X] M ((X : A[X]) ^ i)

theorem toTensor_single (j : ℕ) (m : M) :
    toTensor A M (Finsupp.single j m) = ((Polynomial.X : A[X]) ^ j) ⊗ₜ[A] m :=
  Finsupp.lsum_single (α := ℕ) (M := M) (N := A[X] ⊗[A] M) (R := A) (R₂ := A) (S := A)
    (σ := RingHom.id A) (fun i => TensorProduct.mk A A[X] M ((X : A[X]) ^ i)) j m

/-- The `A`-bilinear map `A[x] × M → M[x]`, `(f, m) ↦ f · m` (where `m` is the constant
polynomial `m x^0`).  By the universal property of the tensor product this induces an
`A`-linear map `A[x] ⊗_A M → M[x]`, namely `ofTensor`; because the bilinear map is `A[x]`-linear
in its first variable, `ofTensor` is even `A[x]`-linear. -/
noncomputable def ofTensor : A[X] ⊗[A] M →ₗ[A[X]] Mx A M :=
  LinearMap.liftBaseChange A[X] (Finsupp.lsingle (M := M) (R := A) (0 : ℕ))

theorem ofTensor_tmul (p : A[X]) (m : M) :
    ofTensor A M (p ⊗ₜ[A] m) = p • (Finsupp.single 0 m : Mx A M) := by
  rw [ofTensor, LinearMap.liftBaseChange_tmul]
  rfl

/-- `toTensor` is inverse to `ofTensor` on the constant polynomials. -/
theorem toTensor_smul_single (p : A[X]) (m : M) :
    toTensor A M (p • (Finsupp.single 0 m : Mx A M)) = p ⊗ₜ[A] m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, TensorProduct.add_tmul]
  | monomial i a =>
      rw [monomial_smul_single, Nat.add_zero, toTensor_single, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Polynomial.smul_eq_C_mul,
        Polynomial.C_mul_X_pow_eq_monomial]

theorem ofTensor_toTensor (f : Mx A M) : ofTensor A M (toTensor A M f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single j m =>
      rw [toTensor_single, ofTensor_tmul, X_pow_smul_single, Nat.zero_add]

theorem toTensor_ofTensor (x : A[X] ⊗[A] M) : toTensor A M (ofTensor A M x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul p m => rw [ofTensor_tmul, toTensor_smul_single]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Exercise 2.6, second part.** The canonical map `A[x] ⊗_A M → M[x]`, `f ⊗ m ↦ f · m`, is an
isomorphism of `A[x]`-modules, with inverse `∑ m_i x^i ↦ ∑ x^i ⊗ m_i`. -/
noncomputable def tensorEquiv : A[X] ⊗[A] M ≃ₗ[A[X]] Mx A M :=
  LinearEquiv.ofBijective (ofTensor A M)
    ⟨fun x y h => by rw [← toTensor_ofTensor A M x, ← toTensor_ofTensor A M y, h],
      fun f => ⟨toTensor A M f, ofTensor_toTensor A M f⟩⟩

@[simp]
theorem tensorEquiv_apply_tmul (p : A[X]) (m : M) :
    tensorEquiv A M (p ⊗ₜ[A] m) = p • (Finsupp.single 0 m : Mx A M) :=
  ofTensor_tmul A M p m

@[simp]
theorem tensorEquiv_symm_apply (f : Mx A M) :
    (tensorEquiv A M).symm f = toTensor A M f := by
  rw [LinearEquiv.symm_apply_eq]
  exact (ofTensor_toTensor A M f).symm

/-- `toTensor` in coordinates: `∑ m_i x^i ↦ ∑ x^i ⊗ m_i`. -/
theorem toTensor_apply (f : Mx A M) :
    toTensor A M f = f.sum (fun i m => ((Polynomial.X : A[X]) ^ i) ⊗ₜ[A] m) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, hf, hg,
        Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by
          rw [TensorProduct.tmul_add])]
  | single j m => rw [toTensor_single, Finsupp.sum_single_index (by simp)]

/-- `ofTensor` is surjective (it is the inverse of `toTensor`). -/
theorem ofTensor_surjective : Function.Surjective (ofTensor A M) :=
  fun f => ⟨toTensor A M f, ofTensor_toTensor A M f⟩

/-- `toTensor` is injective (it is the inverse of `ofTensor`). -/
theorem toTensor_injective : Function.Injective (toTensor A M) :=
  fun x y h => by rw [← ofTensor_toTensor A M x, ← ofTensor_toTensor A M y, h]

@[simp]
theorem tensorEquiv_one_tmul (m : M) :
    tensorEquiv A M ((1 : A[X]) ⊗ₜ[A] m) = Finsupp.single 0 m := by
  rw [tensorEquiv_apply_tmul, one_smul]

/-- The inverse of the canonical isomorphism in coordinates: `∑ m_i x^i ↦ ∑ x^i ⊗ m_i`. -/
theorem tensorEquiv_symm_apply_eq_sum (f : Mx A M) :
    (tensorEquiv A M).symm f = f.sum (fun i m => ((Polynomial.X : A[X]) ^ i) ⊗ₜ[A] m) := by
  rw [tensorEquiv_symm_apply, toTensor_apply]

/-- **Exercise 2.6, second part**, stated in the direction of the textbook: `M[x] ≅ A[x] ⊗_A M`
as `A[x]`-modules. -/
noncomputable def tensorEquiv' : Mx A M ≃ₗ[A[X]] A[X] ⊗[A] M :=
  (tensorEquiv A M).symm

@[simp]
theorem tensorEquiv'_apply (f : Mx A M) :
    tensorEquiv' A M f = f.sum (fun i m => ((Polynomial.X : A[X]) ^ i) ⊗ₜ[A] m) :=
  tensorEquiv_symm_apply_eq_sum A M f

@[simp]
theorem tensorEquiv'_symm_apply_tmul (p : A[X]) (m : M) :
    (tensorEquiv' A M).symm (p ⊗ₜ[A] m) = p • (Finsupp.single 0 m : Mx A M) :=
  ofTensor_tmul A M p m

/-- The two canonical maps are mutually inverse `A[x]`-linear equivalences, in either order. -/
theorem tensorEquiv_trans_tensorEquiv' :
    (tensorEquiv A M).trans (tensorEquiv' A M) = LinearEquiv.refl A[X] (A[X] ⊗[A] M) := by
  ext x
  simp [tensorEquiv']

/-- **Solution of Atiyah–Macdonald, Chapter 2, Exercise 2.6**, both claims in one statement: the
obvious product makes `M[x]` an `A[x]`-module (this is the instance `instModulePolynomial`, whose
values are computed by `C_smul`, `X_smul` and `smul_apply_eq_sum`), and `M[x] ≅ A[x] ⊗_A M` as
`A[x]`-modules. -/
theorem exercise_2_6 : Nonempty (Mx A M ≃ₗ[A[X]] A[X] ⊗[A] M) :=
  ⟨tensorEquiv' A M⟩

end AtiyahMcdonald69.Ex_2_6

/-! ### Axiom audit -/

#print axioms AtiyahMcdonald69.Ex_2_6.instModulePolynomial
#print axioms AtiyahMcdonald69.Ex_2_6.smul_apply_eq_sum
#print axioms AtiyahMcdonald69.Ex_2_6.toTensor_apply
#print axioms AtiyahMcdonald69.Ex_2_6.toTensor_ofTensor
#print axioms AtiyahMcdonald69.Ex_2_6.ofTensor_toTensor
#print axioms AtiyahMcdonald69.Ex_2_6.tensorEquiv
#print axioms AtiyahMcdonald69.Ex_2_6.tensorEquiv'_apply
#print axioms AtiyahMcdonald69.Ex_2_6.exercise_2_6
