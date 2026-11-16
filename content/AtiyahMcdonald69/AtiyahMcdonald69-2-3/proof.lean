import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 2.3

Statement (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 2, Exercise 3):

> Let `(A, m, k)` be a local ring. Show that, if `M` and `N` are finitely generated
> `A`-modules satisfying `M ⊗_A N = 0`, then `M = 0` or `N = 0`.

Formal statement: if `A` is a local ring and `M`, `N` are finite `A`-modules with
`Subsingleton (M ⊗[A] N)` (the formal reading of `M ⊗_A N = 0`), then
`Subsingleton M ∨ Subsingleton N`.

Proof route (the one of the textbook, carried out in full):
* `k = A ⧸ m` is the residue field (`IsLocalRing.ResidueField A`).
* Base change to the residue field is an exact `k`-linear identification
  `k ⊗_A (M ⊗_A N) ≅ (k ⊗_A M) ⊗_k (k ⊗_A N)` (`AlgebraTensorModule.distribBaseChange`).
  Hence `(k ⊗_A M) ⊗_k (k ⊗_A N) = 0`.
* Over a field (`subsingleton_left_or_right_of_tensorProduct`, proved here from
  dimension theory: `Module.rank` of a tensor product is the product of the ranks,
  and `Cardinal` has no zero divisors) a vanishing tensor product forces one factor
  to vanish. So `k ⊗_A M = 0` or `k ⊗_A N = 0`.
* Nakayama's lemma in the form `k ⊗_A M = 0 ↔ M = 0` for finite `M` over a local ring
  (`IsLocalRing.subsingleton_tensorProduct`) finishes the proof.

The final section records that the hypothesis that `A` be local cannot be dropped
(`not_local_counterexample`): over `ℤ`, `ℤ/2ℤ ⊗ ℤ/3ℤ = 0` while both factors are
nonzero and finitely generated.
-/

namespace AtiyahMcdonald69.Ex_2_3

open TensorProduct

universe u v w

section FieldCase

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

/-- Dimension of a tensor product of vector spaces is the product of the dimensions
(this is the form of `rank_tensorProduct` used below). -/
theorem rank_tensorProduct_field :
    Module.rank k (V ⊗[k] W) = Cardinal.lift (Module.rank k V) * Cardinal.lift (Module.rank k W) :=
  rank_tensorProduct

/-- **Vanishing of a tensor product of vector spaces.** Over a field, if `V ⊗[k] W = 0`
then `V = 0` or `W = 0`. -/
theorem subsingleton_left_or_right_of_tensorProduct
    (h : Subsingleton (V ⊗[k] W)) : Subsingleton V ∨ Subsingleton W := by
  have h0 : Module.rank k (V ⊗[k] W) = 0 := Module.rank_zero_iff_of_free.mpr h
  rw [rank_tensorProduct_field] at h0
  rw [mul_eq_zero, Cardinal.lift_eq_zero, Cardinal.lift_eq_zero] at h0
  exact h0.imp (fun hV => Module.rank_zero_iff_of_free.mp hV)
    (fun hW => Module.rank_zero_iff_of_free.mp hW)

end FieldCase

section TensorTrivial

variable {A : Type u} [CommSemiring A]

/-- Tensoring on the right with a trivial module gives a trivial module. -/
theorem subsingleton_tensorProduct_right {P : Type v} {Q : Type w}
    [AddCommMonoid P] [Module A P] [AddCommMonoid Q] [Module A Q] [hQ : Subsingleton Q] :
    Subsingleton (P ⊗[A] Q) :=
  inferInstance

end TensorTrivial

section Main

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-- **Base change of a tensor product to the residue field:**
`k ⊗_A (M ⊗_A N) ≅ (k ⊗_A M) ⊗_k (k ⊗_A N)` for `k` the residue field of a local ring `A`. -/
noncomputable def tensorProductResidueFieldEquiv :
    (IsLocalRing.ResidueField A ⊗[A] (M ⊗[A] N)) ≃ₗ[IsLocalRing.ResidueField A]
      ((IsLocalRing.ResidueField A ⊗[A] M) ⊗[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField A ⊗[A] N)) :=
  AlgebraTensorModule.distribBaseChange A (IsLocalRing.ResidueField A) M N

/-- Nakayama's lemma, in the form of Exercise 2.2 + Nakayama: for a finite module `M`
over a local ring `A` with residue field `k`, `k ⊗_A M = 0` iff `M = 0`. -/
theorem subsingleton_residueField_tensorProduct_iff [Module.Finite A M] :
    Subsingleton (IsLocalRing.ResidueField A ⊗[A] M) ↔ Subsingleton M :=
  IsLocalRing.subsingleton_tensorProduct

/-- **Atiyah–Macdonald, Exercise 2.3.** Let `A` be a local ring and let `M`, `N` be
finitely generated `A`-modules. If `M ⊗_A N = 0`, then `M = 0` or `N = 0`. -/
theorem subsingleton_or_subsingleton_of_subsingleton_tensorProduct
    [Module.Finite A M] [Module.Finite A N]
    (h : Subsingleton (M ⊗[A] N)) : Subsingleton M ∨ Subsingleton N := by
  -- step 1: base change to the residue field `k`, and use associativity of the tensor product
  have h₁ : Subsingleton (IsLocalRing.ResidueField A ⊗[A] (M ⊗[A] N)) :=
    subsingleton_tensorProduct_right (hQ := h)
  have h₂ : Subsingleton
      ((IsLocalRing.ResidueField A ⊗[A] M) ⊗[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField A ⊗[A] N)) :=
    (tensorProductResidueFieldEquiv (A := A) (M := M) (N := N)).toEquiv.subsingleton_congr.mp h₁
  -- step 2: over the field `k`, a vanishing tensor product forces one factor to vanish
  rcases subsingleton_left_or_right_of_tensorProduct h₂ with h₃ | h₃
  · exact Or.inl (subsingleton_residueField_tensorProduct_iff.mp h₃)
  · exact Or.inr (subsingleton_residueField_tensorProduct_iff.mp h₃)

/-- Contrapositive form of Exercise 2.3: the tensor product of two nonzero finite modules
over a local ring is nonzero. -/
theorem nontrivial_tensorProduct [Module.Finite A M] [Module.Finite A N]
    (hM : Nontrivial M) (hN : Nontrivial N) : Nontrivial (M ⊗[A] N) := by
  rw [← not_subsingleton_iff_nontrivial]
  rw [← not_subsingleton_iff_nontrivial] at hM hN
  intro h
  exact (subsingleton_or_subsingleton_of_subsingleton_tensorProduct h).elim hM hN

end Main

section Sharpness

open scoped TensorProduct

/-- In `ℤ/2ℤ`, the integer `3` acts as the identity. -/
theorem zsmul_three_zmod_two (x : ZMod 2) : (3 : ℤ) • x = x := by
  rw [zsmul_eq_mul, show ((3 : ℤ) : ZMod 2) = 1 from by decide, one_mul]

/-- In `ℤ/3ℤ`, the integer `3` acts trivially. -/
theorem zsmul_three_zmod_three (y : ZMod 3) : (3 : ℤ) • y = 0 := by
  rw [zsmul_eq_mul, show ((3 : ℤ) : ZMod 3) = 0 from by decide, zero_mul]

/-- Every pure tensor in `ℤ/2ℤ ⊗[ℤ] ℤ/3ℤ` vanishes: `3` acts as `1` on the left factor
and as `0` on the right one. -/
theorem tmul_zmod_two_zmod_three_eq_zero (x : ZMod 2) (y : ZMod 3) :
    x ⊗ₜ[ℤ] y = 0 := by
  calc x ⊗ₜ[ℤ] y = ((3 : ℤ) • x) ⊗ₜ[ℤ] y := by rw [zsmul_three_zmod_two]
    _ = x ⊗ₜ[ℤ] ((3 : ℤ) • y) := TensorProduct.smul_tmul (3 : ℤ) x y
    _ = x ⊗ₜ[ℤ] (0 : ZMod 3) := by rw [zsmul_three_zmod_three]
    _ = 0 := TensorProduct.tmul_zero _ _

/-- `ℤ/2ℤ ⊗[ℤ] ℤ/3ℤ = 0`, although both factors are nonzero finitely generated
`ℤ`-modules. -/
theorem subsingleton_zmod_two_tensor_zmod_three : Subsingleton (ZMod 2 ⊗[ℤ] ZMod 3) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ z : ZMod 2 ⊗[ℤ] ZMod 3, z = 0 := fun z =>
    TensorProduct.induction_on z rfl (fun x y => tmul_zmod_two_zmod_three_eq_zero x y)
      (fun x y hx hy => by rw [hx, hy, add_zero])
  rw [h a, h b]

/-- The unit criterion for local rings, with the `IsLocalRing` argument made explicit
(so that it can be used to *refute* locality). -/
theorem isUnit_or_isUnit_one_sub_of_isLocalRing {R : Type*} [CommRing R]
    [hR : IsLocalRing R] (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  IsLocalRing.isUnit_or_isUnit_one_sub_self a

/-- `ℤ` is not a local ring: `3` and `1 - 3 = -2` are both non-units. -/
theorem not_isLocalRing_int : ¬ IsLocalRing ℤ := by
  intro h
  have h3 : ¬ IsUnit (3 : ℤ) := by
    simp [Int.isUnit_iff]
  have h2 : ¬ IsUnit ((1 : ℤ) - 3) := by
    rw [show (1 : ℤ) - 3 = -2 from by norm_num]
    simp [Int.isUnit_iff]
  rcases isUnit_or_isUnit_one_sub_of_isLocalRing (R := ℤ) (hR := h) (3 : ℤ) with h' | h'
  exacts [h3 h', h2 h']

/-- **Sharpness of the hypothesis of Exercise 2.3.** The conclusion fails over the
non-local ring `ℤ`: `ℤ/2ℤ` and `ℤ/3ℤ` are nonzero finitely generated `ℤ`-modules whose
tensor product vanishes. So the hypothesis that `A` be local cannot be dropped. -/
theorem not_local_counterexample :
    ¬ IsLocalRing ℤ ∧ Nontrivial (ZMod 2) ∧ Nontrivial (ZMod 3) ∧
      Subsingleton (ZMod 2 ⊗[ℤ] ZMod 3) :=
  ⟨not_isLocalRing_int, inferInstance, inferInstance,
    subsingleton_zmod_two_tensor_zmod_three⟩

end Sharpness

end AtiyahMcdonald69.Ex_2_3

/-! ## Axiom audit

The declarations above depend only on the standard axioms of Lean's logic. -/

#print axioms AtiyahMcdonald69.Ex_2_3.subsingleton_or_subsingleton_of_subsingleton_tensorProduct
#print axioms AtiyahMcdonald69.Ex_2_3.nontrivial_tensorProduct
#print axioms AtiyahMcdonald69.Ex_2_3.subsingleton_left_or_right_of_tensorProduct
#print axioms AtiyahMcdonald69.Ex_2_3.not_local_counterexample
