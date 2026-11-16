import Mathlib

/-!
# Atiyah–Macdonald, Exercise 5.3

Statement (M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*,
Chapter 5, Exercise 3):

> Let `f : B → B'` be a homomorphism of `A`-algebras, and let `C` be an `A`-algebra.
> If `f` is integral, prove that `f ⊗ 1 : B ⊗_A C → B' ⊗_A C` is integral.
> (This includes (5.6 ii) as a special case.)

Recall (Chapter 5, p. 60; compare Exercise 5.1) that a ring homomorphism `f : B → B'` is
*integral* if `B'` is integral over the image `f(B)`, i.e. if every element of `B'` is a root of
a monic polynomial whose coefficients lie in `f(B)`.  This is Mathlib's `RingHom.IsIntegral`,
and no algebra structure on the target is needed to state it, which is why we use it as the
hypothesis and as the conclusion.  The `A`-algebra base change `f ⊗ 1` is the map
`Algebra.TensorProduct.map f (AlgHom.id A C) : B ⊗[A] C →ₐ[A] B' ⊗[A] C`.

Main results:

* `tensorProductMap_isIntegral` (also exported as `solution`) : the exercise.
* `isIntegralElem_tmul` : the generator-wise form used by the natural proof: every pure tensor
  `b' ⊗ c` is integral over the image of `f ⊗ 1`.
* `tensorProduct_isIntegral` : (5.6 ii) as the special case mentioned in the book, in tensor
  product form: if `B'` is integral over `A` and `C` is any `A`-algebra, then `B' ⊗[A] C` is
  integral over `C`.  (The classical form of (5.6 ii), `S⁻¹B` integral over `S⁻¹A`, is the case
  `C = S⁻¹A`, using `B ⊗[A] S⁻¹A ≅ S⁻¹B`.)

The proof is the book's: integral elements form a subring; `1 ⊗ c` is in the image of `f ⊗ 1`;
`b' ⊗ 1` is a root of the polynomial obtained by applying `f ⊗ 1` to a monic equation for `b'`;
and every pure tensor is a product `(b' ⊗ 1) * (1 ⊗ c)`.
-/

namespace AtiyahMcdonald69.Ex_5_3

open scoped TensorProduct

variable {A B B' C : Type*} [CommRing A] [CommRing B] [CommRing B'] [CommRing C]
  [Algebra A B] [Algebra A B'] [Algebra A C]

/-- The base change `f ⊗ 1 : B ⊗[A] C → B' ⊗[A] C` of an `A`-algebra homomorphism
`f : B →ₐ[A] B'` along the structure map `A → C`. -/
def tensorProductMap (f : B →ₐ[A] B') : B ⊗[A] C →+* B' ⊗[A] C :=
  (Algebra.TensorProduct.map f (AlgHom.id A C) : B ⊗[A] C →ₐ[A] B' ⊗[A] C).toRingHom

@[simp]
lemma tensorProductMap_tmul (f : B →ₐ[A] B') (b : B) (c : C) :
    tensorProductMap f (b ⊗ₜ[A] c) = f b ⊗ₜ[A] c := rfl

/-- `1 ⊗ c` lies in the image of `f ⊗ 1` (it is the image of `1 ⊗ c`), hence is integral
over that image. -/
lemma isIntegralElem_one_tmul (f : B →ₐ[A] B') (c : C) :
    (tensorProductMap (C := C) f).IsIntegralElem (1 ⊗ₜ[A] c) := by
  simpa using (tensorProductMap (C := C) f).isIntegralElem_map (x := (1 : B) ⊗ₜ[A] c)

/-- `b' ⊗ 1` is integral over the image of `f ⊗ 1` whenever `b'` is integral over the image
of `f`: apply `f ⊗ 1` to a monic equation for `b'`. -/
lemma isIntegralElem_tmul_one (f : B →ₐ[A] B') (hf : (f : B →+* B').IsIntegral) (b' : B') :
    (tensorProductMap (C := C) f).IsIntegralElem (b' ⊗ₜ[A] (1 : C)) := by
  let φ : B' →+* B' ⊗[A] C := Algebra.TensorProduct.includeLeftRingHom
  let ψ : B →+* B ⊗[A] C := Algebra.TensorProduct.includeLeftRingHom
  have h := (hf b').map φ
  have hcomp : (tensorProductMap (C := C) f).comp ψ = φ.comp (f : B →+* B') := by
    ext b
    simp [tensorProductMap, φ, ψ]
  rw [← hcomp] at h
  simpa [φ, ψ] using RingHom.IsIntegralElem.of_comp h

/-- Every pure tensor `b' ⊗ c = (b' ⊗ 1) * (1 ⊗ c)` is integral over the image of `f ⊗ 1`. -/
lemma isIntegralElem_tmul (f : B →ₐ[A] B') (hf : (f : B →+* B').IsIntegral) (b' : B')
    (c : C) : (tensorProductMap (C := C) f).IsIntegralElem (b' ⊗ₜ[A] c) := by
  have hmul :=
    RingHom.IsIntegralElem.mul (tensorProductMap (C := C) f)
      (isIntegralElem_tmul_one f hf b') (isIntegralElem_one_tmul f c)
  simpa using hmul

/-- **Atiyah–Macdonald, Exercise 5.3.**  If `f : B → B'` is an integral homomorphism of
`A`-algebras and `C` is an `A`-algebra, then `f ⊗ 1 : B ⊗[A] C → B' ⊗[A] C` is integral. -/
theorem tensorProductMap_isIntegral (f : B →ₐ[A] B') (hf : (f : B →+* B').IsIntegral) :
    (tensorProductMap (C := C) f).IsIntegral := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact RingHom.isIntegralElem_zero _
  | tmul b' c => exact isIntegralElem_tmul f hf b' c
  | add x y hx hy => exact RingHom.IsIntegralElem.add _ hx hy

/-- **Atiyah–Macdonald, Exercise 5.3** (main statement, unchanged form). -/
theorem solution (f : B →ₐ[A] B') (hf : (f : B →+* B').IsIntegral) :
    ((Algebra.TensorProduct.map f (AlgHom.id A C) : B ⊗[A] C →ₐ[A] B' ⊗[A] C) :
      B ⊗[A] C →+* B' ⊗[A] C).IsIntegral :=
  tensorProductMap_isIntegral f hf

/-- Variant of the exercise with the hypothesis in the form "`B'` is integral over `B`",
where `B'` is regarded as a `B`-algebra through `f` (the book's "`B'` is integral over `f(B)`"). -/
theorem tensorProductMap_isIntegral' (f : B →ₐ[A] B')
    (hf : letI := f.toRingHom.toAlgebra; Algebra.IsIntegral B B') :
    (tensorProductMap (C := C) f).IsIntegral := by
  have hf' : (f : B →+* B').IsIntegral := by
    let inst : Algebra B B' := f.toRingHom.toAlgebra
    intro b'
    exact Algebra.IsIntegral.isIntegral b'
  exact tensorProductMap_isIntegral f hf'

/-- Transporting integrality of a homomorphism backwards along a ring isomorphism of its source. -/
lemma isIntegralElem_comp_ringEquiv {R R' S : Type*} [CommRing R] [CommRing R']
    [Ring S] {g : R →+* S} {x : S} (h : g.IsIntegralElem x) (e : R' ≃+* R) :
    (g.comp (e : R' →+* R)).IsIntegralElem x := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.map (e.symm : R →+* R'), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (g.comp (e : R' →+* R)).comp (e.symm : R →+* R') = g from by
    ext; simp, hp']

/-- **The special case (5.6 ii)** mentioned in the statement of Exercise 5.3, in tensor product
form: if `B'` is an integral `A`-algebra and `C` is any `A`-algebra, then `B' ⊗[A] C` is integral
over `C`, through the canonical map `c ↦ 1 ⊗ c`.  This is obtained from the exercise applied to
`Algebra.ofId A B'`, using `A ⊗[A] C ≃ₐ[A] C`. -/
theorem tensorProduct_isIntegral [Algebra.IsIntegral A B'] :
    (Algebra.TensorProduct.includeRight (R := A) (A := B') (B := C)).toRingHom.IsIntegral := by
  have hf : (Algebra.ofId A B' : A →+* B').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hg : (tensorProductMap (C := C) (Algebra.ofId A B')).IsIntegral :=
    tensorProductMap_isIntegral _ hf
  have heq : (tensorProductMap (C := C) (Algebra.ofId A B')).comp
      ((Algebra.TensorProduct.lid (R := A) (A := C)).symm : C →+* A ⊗[A] C) =
      (Algebra.TensorProduct.includeRight (R := A) (A := B') (B := C)).toRingHom := by
    ext c
    simp [tensorProductMap, Algebra.TensorProduct.lid_symm_apply]
  rw [← heq]
  exact fun y => isIntegralElem_comp_ringEquiv (hg y)
    (Algebra.TensorProduct.lid (R := A) (A := C)).symm.toRingEquiv

/-- Sanity check, exhibiting a genuine (non-tautological) instance of the exercise: the
diagonal map `ℤ → ℤ × ℤ` is integral (`(1, 0)` is a root of `X ^ 2 - X`), hence for the
`ℤ`-algebra `ZMod 5` the base change `(ℤ × ℤ) ⊗[ℤ] ZMod 5 → (ℤ × ℤ) ⊗[ℤ] ZMod 5` is integral. -/
example : (tensorProductMap (C := ZMod 5) (Algebra.ofId ℤ (ℤ × ℤ))).IsIntegral :=
  tensorProductMap_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral x)

#print axioms AtiyahMcdonald69.Ex_5_3.solution
#print axioms AtiyahMcdonald69.Ex_5_3.tensorProductMap_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_3.tensorProductMap_isIntegral'
#print axioms AtiyahMcdonald69.Ex_5_3.tensorProduct_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_3.isIntegralElem_tmul

end AtiyahMcdonald69.Ex_5_3
