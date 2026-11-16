/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 2, Exercise 8:

  i)  If `M` and `N` are flat `A`-modules, then so is `M ⊗[A] N`.
  ii) If `B` is a flat `A`-algebra and `N` is a flat `B`-module, then `N` is flat
      as an `A`-module (for the `A`-module structure obtained by restriction of
      scalars along `A → B`).

Formalization notes.
* The book calls an `A`-module `M` flat when tensoring with it preserves
  exactness; Proposition 2.19 of the book records that this is equivalent to
  `f ⊗ 1` being injective for every injective `f`.  In Mathlib this is
  `Module.Flat`, whose defining field is exactly that mono-flatness property, so
  the formal statements below are the book's statements.
* Part (i) is proved the way the natural proof does it: an element of
  `P ⊗[A] (M ⊗[A] N)` is, via the associativity isomorphism, an element of
  `(P ⊗[A] M) ⊗[A] N`; tensoring an injection with `M` and then with `N` keeps it
  injective, hence tensoring with `M ⊗[A] N` does too.
* Part (ii) is proved by writing `P ⊗[A] N ≅ N ⊗[B] (B ⊗[A] P)` (the "tower"
  isomorphism `cancelBaseChange`), which exhibits `⊗[A] N` as the composite of
  `⊗[A] B` with `⊗[B] N`; the first preserves injectivity because `B` is `A`-flat
  and the second because `N` is `B`-flat.
* `flat_of_flat_algebra` is complemented by `flat_of_flat_algebra_restrict`,
  the literal form of (ii) in which the `A`-module structure on `N` is exactly the
  restriction of scalars `Module.compHom N (algebraMap A B)`; part (ii) is
  therefore not weakened by the `IsScalarTower` hypothesis of the general form.
* The last section records concrete instances over `ℤ`, including the failure of
  the converse of (i): `ℤ/2 ⊗[ℤ] ℚ` is flat (it is the zero module) although
  `ℤ/2` is not a flat `ℤ`-module.
-/
import Mathlib

open scoped TensorProduct

/- `haveI` below installs flatness proofs (propositions) as local typeclass
instances, which is exactly what the arguments need; the stylistic linter advice
to use `have` instead does not apply. -/
set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_2_8

universe u v w

/-! ## Part (i): the tensor product of two flat modules is flat -/

section Part1

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-- Atiyah–Macdonald, Exercise 2.8 (i): if `M` and `N` are flat `A`-modules then
`M ⊗[A] N` is a flat `A`-module. -/
theorem flat_tensorProduct [Module.Flat A M] [Module.Flat A N] :
    Module.Flat A (M ⊗[A] N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have key := LinearMap.rTensor_tensor (R := A) M (N := N) (P := P) (Q := Q) f
  rw [key]
  have h1 : Function.Injective (LinearMap.rTensor M f) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have h2 : Function.Injective (LinearMap.rTensor N (LinearMap.rTensor M f)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (R := A) (M := N)
      (N := P ⊗[A] M) (P := Q ⊗[A] M) (LinearMap.rTensor M f) h1
  exact (LinearEquiv.injective (TensorProduct.assoc A Q M N)).comp
    (h2.comp (LinearEquiv.injective (TensorProduct.assoc A P M N).symm))

/-- The heart of part (i), isolated: tensoring an injective map with
`M ⊗[A] N` is injective. -/
theorem injective_rTensor_tensorProduct [Module.Flat A M] [Module.Flat A N]
    {P Q : Type (max u (max v w))} [AddCommGroup P] [AddCommGroup Q]
    [Module A P] [Module A Q] {f : P →ₗ[A] Q} (hf : Function.Injective f) :
    Function.Injective (f.rTensor (M ⊗[A] N)) := by
  haveI := flat_tensorProduct (A := A) (M := M) (N := N)
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- The exactness formulation of part (i): tensoring any exact sequence with
`M ⊗[A] N` gives an exact sequence. -/
theorem exact_tensorProduct [Module.Flat A M] [Module.Flat A N]
    {P Q R : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module A P] [Module A Q] [Module A R]
    {f : P →ₗ[A] Q} {g : Q →ₗ[A] R} (h : Function.Exact f g) :
    Function.Exact (f.rTensor (M ⊗[A] N)) (g.rTensor (M ⊗[A] N)) := by
  haveI := flat_tensorProduct (A := A) (M := M) (N := N)
  exact Module.Flat.rTensor_exact (M ⊗[A] N) h

end Part1

/-! ## Part (ii): flatness is stable under composing an algebra and a module -/

section Part2

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- Atiyah–Macdonald, Exercise 2.8 (ii): if `B` is a flat `A`-algebra and `N` is a
flat `B`-module, then `N` is flat as an `A`-module.  The hypothesis
`IsScalarTower A B N` says precisely that the `A`-module structure on `N` is the
restriction of scalars of the `B`-module structure along `algebraMap A B`, i.e.
that `N` is "regarded as an `A`-module" in the sense of the book. -/
theorem flat_of_flat_algebra [Module.Flat A B] [Module.Flat B N] :
    Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ I
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B),
    ← EquivLike.injective_comp (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N I),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp,
    TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  iterate 2 apply Module.Flat.lTensor_preserves_injective_linearMap
  exact Subtype.val_injective

/-- The heart of part (ii), isolated: tensoring an injective map of `A`-modules
with the restricted module `N` is injective. -/
theorem injective_rTensor_of_flat_algebra [Module.Flat A B] [Module.Flat B N]
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module A P] [Module A Q]
    {f : P →ₗ[A] Q} (hf : Function.Injective f) :
    Function.Injective (f.rTensor N) := by
  haveI := flat_of_flat_algebra (A := A) (B := B) (N := N)
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- The exactness formulation of part (ii). -/
theorem exact_of_flat_algebra [Module.Flat A B] [Module.Flat B N]
    {P Q R : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module A P] [Module A Q] [Module A R]
    {f : P →ₗ[A] Q} {g : Q →ₗ[A] R} (h : Function.Exact f g) :
    Function.Exact (f.rTensor N) (g.rTensor N) := by
  haveI := flat_of_flat_algebra (A := A) (B := B) (N := N)
  exact Module.Flat.rTensor_exact N h

end Part2

/-! ## Part (ii) in literal restriction-of-scalars form -/

section Restrict

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {N : Type w} [AddCommGroup N] [Module B N]

/-- Part (ii) with the `A`-module structure on `N` given literally by restriction
of scalars along `algebraMap A B`, i.e. `Module.compHom N (algebraMap A B)`: this
is exactly the phrase "`N` regarded as an `A`-module" from the book. -/
theorem flat_of_flat_algebra_restrict [Module.Flat A B] [Module.Flat B N] :
    letI := Module.compHom N (algebraMap A B)
    Module.Flat A N := by
  letI : Module A N := Module.compHom N (algebraMap A B)
  haveI : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  exact flat_of_flat_algebra (A := A) (B := B) (N := N)

end Restrict

/-! ## Concrete examples and a counterexample

Over `A = ℤ` we can compute.  `ℚ` is a flat `ℤ`-module, so `ℚ ⊗[ℤ] ℚ` is flat by
part (i); and `ℤ/2` is *not* a flat `ℤ`-module, while `ℤ/2 ⊗[ℤ] ℚ` is the zero
module and hence flat.  Thus the converse of part (i) fails.  The same example
shows that the flatness of `B` over `A` in part (ii) cannot be dropped: taking
`A = ℤ`, `B = N = ℤ/2`, the `B`-module `N` is flat over `B` but not over `A`. -/

section Concrete

/-- A subsingleton module is flat (it is even free). -/
theorem flat_of_subsingleton {A : Type u} [CommRing A] {M : Type v} [AddCommMonoid M]
    [Module A M] (h : Subsingleton M) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ I x y _
  suffices key : ∀ z : I ⊗[A] M, z = 0 from (key x).trans (key y).symm
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul i m => rw [show m = 0 from h.elim m 0]; simp
  | add x y hx hy => rw [hx, hy, add_zero]

/-- Every element of `ZMod 2 ⊗[ℤ] ℚ` is zero: `ℤ/2` is `2`-torsion and `ℚ` is
`2`-divisible. -/
theorem eq_zero_tmul_zmod_two_rat (a : ZMod 2) (q : ℚ) : a ⊗ₜ[ℤ] q = 0 := by
  have hq : q = (2 : ℤ) • (q / 2) := by rw [zsmul_eq_mul]; ring
  rw [hq, ← TensorProduct.smul_tmul (2 : ℤ) a (q / 2)]
  have h2 : (2 : ℤ) • a = 0 := by
    rw [two_zsmul, ← two_mul]
    have htwo : (2 : ZMod 2) = 0 := by simpa using ZMod.natCast_self 2
    rw [htwo, zero_mul]
  rw [h2]
  simp

/-- `ℤ/2 ⊗[ℤ] ℚ` is the zero module. -/
theorem subsingleton_zmod_two_tensor_rat : Subsingleton (ZMod 2 ⊗[ℤ] ℚ) := by
  constructor
  intro x y
  suffices h : ∀ z : ZMod 2 ⊗[ℤ] ℚ, z = 0 by rw [h x, h y]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a q => exact eq_zero_tmul_zmod_two_rat a q
  | add x y hx hy => rw [hx, hy, add_zero]

/-- `ℤ/2` is not a flat `ℤ`-module: multiplication by `2` is injective on `ℤ` but
not on `ℤ/2`. -/
theorem not_flat_zmod_two : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  have hreg : IsSMulRegular (ZMod 2) ((algebraMap ℤ (ZMod 2)) 2) :=
    @IsSMulRegular.of_flat ℤ (ZMod 2) _ _ _ h 2 (by
      intro a b hab
      simp only [smul_eq_mul] at hab
      exact mul_left_cancel₀ (by norm_num) hab)
  refine one_ne_zero (hreg ?_)
  show ((algebraMap ℤ (ZMod 2)) 2) • (1 : ZMod 2) = ((algebraMap ℤ (ZMod 2)) 2) • (0 : ZMod 2)
  rw [smul_zero, smul_eq_mul, mul_one]
  simpa using ZMod.natCast_self 2

/-- `ℚ ⊗[ℤ] ℚ` is a flat `ℤ`-module, by part (i). -/
theorem flat_rat_tensor_rat : Module.Flat ℤ (ℚ ⊗[ℤ] ℚ) :=
  flat_tensorProduct

/-- The converse of part (i) fails: a tensor product can be flat even though one
of the factors is not. -/
theorem tensorProduct_flat_of_not_flat :
    Module.Flat ℤ (ZMod 2 ⊗[ℤ] ℚ) ∧ ¬ Module.Flat ℤ (ZMod 2) :=
  ⟨flat_of_subsingleton subsingleton_zmod_two_tensor_rat, not_flat_zmod_two⟩

/-- The hypothesis that `B` is a flat `A`-algebra in part (ii) cannot be dropped:
`ℤ/2` is a flat `ℤ/2`-module which is not a flat `ℤ`-module. -/
theorem flat_algebra_hypothesis_needed :
    Module.Flat (ZMod 2) (ZMod 2) ∧ ¬ Module.Flat ℤ (ZMod 2) :=
  ⟨Module.Flat.self, not_flat_zmod_two⟩

end Concrete

/-! ## Axiom audit -/

#print axioms flat_tensorProduct
#print axioms injective_rTensor_tensorProduct
#print axioms exact_tensorProduct
#print axioms flat_of_flat_algebra
#print axioms injective_rTensor_of_flat_algebra
#print axioms exact_of_flat_algebra
#print axioms flat_of_flat_algebra_restrict
#print axioms tensorProduct_flat_of_not_flat
#print axioms flat_algebra_hypothesis_needed

end AtiyahMcdonald69.Ex_2_8
