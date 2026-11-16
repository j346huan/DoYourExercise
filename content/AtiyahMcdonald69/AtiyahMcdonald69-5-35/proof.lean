/-
Atiyah–Macdonald, Exercise 5.35 (Chapter 5, "Integral Dependence and Valuations").
-/
import Mathlib

/-!
# Atiyah–Macdonald 1969, Chapter 5, Exercise 35

The exercise, as printed in the original (Chapter 5, p. 73 of the 1969 edition):

> 35. From Exercises 1 and 3 it follows that, if `f : A → B` is integral and `C` is any
> `A`-algebra, then the mapping `(f ⊗ 1)* : Spec (B ⊗_A C) → Spec (C)` is a closed map.
> Conversely, suppose that `f : A → B` has this property and that `B` is an integral domain.
> Then `f` is integral. [Replacing `A` by its image in `B`, reduce to the case where `A ⊆ B`
> and `f` is the injection. Let `K` be the field of fractions of `B` and let `A'` be a
> valuation ring of `K` containing `A`. By (5.22) it is enough to show that `A'` contains `B`.
> By hypothesis `Spec (B ⊗_A A') → Spec (A')` is a closed map. Apply the result of Exercise 34
> to the homomorphism `B ⊗_A A' → K` defined by `b ⊗ a' ↦ b a'`. It follows that `b a' ∈ A'`
> for all `b ∈ B` and all `a' ∈ A'`; taking `a' = 1`, we have what we want.]
> Show that the result just proved remains valid if `B` is a ring with only finitely many
> minimal prime ideals (e.g., if `B` is Noetherian). [Let `𝔭_i` be the minimal prime ideals.
> Then each composite homomorphism `A → B → B/𝔭_i` is integral, hence `A → ∏ (B/𝔭_i)` is
> integral, hence `A → B/𝔑` is integral (where `𝔑` is the nilradical of `B`), hence finally
> `A → B` is integral.]

(The scanned original is garbled by OCR in a few places — `1` for `f`, `_,..` for `→`,
`®`/`0` for `⊗`, `£` for `⊆`, `E` for `∈`, `14` for `↦`, `.p 1` for `𝔭_i`, `II` for `∏`,
`f'%J 1` for `𝔭_i`, `SJl` for `𝔑`; the reading above is the standard one and is consistent
with every cited result.)

## Encoding

The ring hom `f : A → B` is encoded as an `Algebra A B` instance (the book's `f` is
`algebraMap A B`; any `f` gives such an instance via `f.toAlgebra`).  For an `A`-algebra `C`
the map `(f ⊗ 1)*` of the exercise is

  `PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C))`,

of type `Spec (B ⊗[A] C) → Spec C`: `includeRight` is `c ↦ 1 ⊗ c`, which under the
canonical identification `A ⊗[A] C ≅ C` is precisely `f ⊗ 1`.

For simplicity all rings are taken in one universe `u` (by cumulativity any ring can be lifted
into it, so this costs nothing).  The results are also restated below for an explicit ring hom
`f : A →+* B`.

## Main results

* `isClosedMap_comap_tensorProduct_of_isIntegral`, `isClosedBaseChange_of_isIntegral` :
  the forward implication (first sentence of the exercise).
* `isIntegral_of_isClosedBaseChange_of_isDomain` : the converse for `B` an integral domain.
* `isIntegral_of_isClosedBaseChange_of_finite_minimalPrimes`,
  `isIntegral_of_isClosedBaseChange_of_isNoetherianRing` : the generalisation to rings with
  only finitely many minimal prime ideals, and the Noetherian case.
* `isIntegral_of_isClosedBaseChange` : a strengthening, *not* stated in the book and not
  needed for it: testing closedness only for the single `A`-algebra `C = A[X]` already forces
  `f` to be integral, with no hypothesis on `B` whatsoever (this is Mathlib's
  `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`, applied along the canonical ring
  isomorphism `B ⊗[A] A[X] ≃+* B[X]` built below).  The exact "single test algebra" form is
  `isIntegral_of_isClosedMap_tensorProduct_polynomial`; the strengthening itself is
  `isIntegral_of_isClosedBaseChange`.  Consequently the domain hypothesis of
  part (b) and the finite-minimal-primes hypothesis of part (c) are *not needed*; the book's
  statements remain true and are recorded verbatim (with those hypotheses) as the named results
  above.  This is a strengthening of the exercise, not a counterexample to it.
* `tensorProduct_map_comp_includeRight` : the triangle `(f ⊗ 1) ∘ (1 ⊗ –) = (1 ⊗ –)`
  justifying the encoding of `(f ⊗ 1)*` as `comap includeRight`.
* `IsClosedBaseChangeHom` together with `isClosedBaseChangeHom_of_isIntegral`,
  `isIntegral_of_isClosedBaseChangeHom`, `isIntegral_of_isClosedBaseChangeHom_of_isDomain` and
  `isIntegral_of_isClosedBaseChangeHom_of_finite_minimalPrimes` (and the Noetherian instance)
  restate the exercise for an explicit ring hom `f : A →+* B`, which is literally the book's
  quantified object.

## Audit of the source and of the natural proof

* The cited results are correctly identified: Exercise 1 (an integral homomorphism has a closed
  spectrum map) and Exercise 3 (integrality is stable under base change) give the forward
  implication; Exercise 34 (a closed spectrum map out of a valuation ring forces the image into
  the valuation ring) and Corollary 5.22 (the integral closure of a subring of a field is the
  intersection of the valuation rings containing it) give the converse; Exercise 5.6 (a finite
  product of integral algebras is integral) gives the passage to finitely many minimal primes.
  We checked each citation against the original text; the argument printed in the book and the
  natural proof on `DoYourExercise` are correct.
* No assertion of the exercise is false.  The only audit finding is that the hypothesis
  "`B` is an integral domain" and the hypothesis "`B` has finitely many minimal primes" are both
  redundant (see the strengthening above): the converse holds for an arbitrary `B`, and even
  the closedness for the single algebra `C = A[X]` suffices.  The book's statements are therefore
  true, just not optimal; they are recorded here with their hypotheses intact for faithfulness.
* The proof step of the hint for the general case that is only sketched in the book (from
  `A → B/𝔑` integral to `A → B` integral) is correct: for `b ∈ B` choose a monic `P ∈ A[T]`
  with `P(b) ∈ 𝔑`; then `P(b)^r = 0`, and `P^r` is the required monic polynomial for `b`.
  Note that no nilpotency of `𝔑` as an ideal is needed.

No `sorry`, `admit`, custom axiom, or private dependency is used; every result is proved from
`Mathlib`.
-/

open Polynomial
open scoped TensorProduct

namespace AtiyahMcdonald69.Ex_5_35

universe u

/- We need local `Algebra` instances inside statements and proofs below (`B ⊗[A] C` is a
`C`-algebra, and a ring hom `f : A →+* B` gives an algebra structure `f.toAlgebra`); the style
linter that suggests replacing `letI` by `let` in proofs of propositions does not apply to them,
so it is disabled for this file. -/
set_option linter.style.haveILetI false

/- Local instance (only for this file): `B ⊗[A] C` is a `C`-algebra.  This structure is an
`abbrev` in Mathlib rather than a global instance (it would be ambiguous for `S ⊗[R] S`), so we
make it locally available; it is exactly `algebraMap C (B ⊗[A] C) = includeRight`. -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The hypothesis of the exercise -/

/-- **Hypothesis of Exercise 5.35.**  For every `A`-algebra `C`, the base-change map
`(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C` is a closed map (here `f` is `algebraMap A B`). -/
def IsClosedBaseChange (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra A C],
    IsClosedMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)

/-! ### The encoding of `(f ⊗ 1)*`

For an `A`-algebra `C`, the map `f ⊗ 1 : A ⊗[A] C → B ⊗[A] C` of the exercise, preceded by the
canonical identification `C → A ⊗[A] C`, `c ↦ 1 ⊗ c`, is exactly `includeRight`.  This is the
sense in which `PrimeSpectrum.comap (includeRight)` is `(f ⊗ 1)*`. -/

section Encoding

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C]

/-- `(f ⊗ 1) ∘ (1 ⊗ –) = (1 ⊗ –)`: the triangle identifying the base-change map of the
exercise with `includeRight` under the canonical identification `A ⊗[A] C ≅ C`. -/
theorem tensorProduct_map_comp_includeRight :
    (Algebra.TensorProduct.map (Algebra.ofId A B) (AlgHom.id A C)).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := A) (B := C))
      = Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C) := by
  ext c
  simp

end Encoding

section Integral

/-! ### The forward implication (first sentence of the exercise) -/

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The tensor product `B ⊗[A] C` is integral over `C` when `B` is integral over `A`. -/
theorem isIntegral_tensorProduct_right (C : Type u) [CommRing C] [Algebra A C]
    (h : Algebra.IsIntegral A B) : Algebra.IsIntegral C (B ⊗[A] C) := by
  have h1 : Algebra.IsIntegral C (C ⊗[A] B) := Algebra.IsIntegral.tensorProduct (R := A) (A := C) (B := B)
  exact (AlgEquiv.isIntegral_iff (Algebra.TensorProduct.commRight (R := A) (S := C) (A := B))).mp h1

/-- **Exercise 5.35, forward implication, for a fixed `A`-algebra `C`:** if `f : A → B` is
integral, then `(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C` is a closed map. -/
theorem isClosedMap_comap_tensorProduct_of_isIntegral (C : Type u) [CommRing C] [Algebra A C]
    (h : Algebra.IsIntegral A B) :
    IsClosedMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) := by
  apply PrimeSpectrum.isClosedMap_comap_of_isIntegral
  have hkey : Algebra.IsIntegral C (B ⊗[A] C) :=
    isIntegral_tensorProduct_right C h
  have hmap : (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom
      = algebraMap C (B ⊗[A] C) := by
    rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
    rfl
  rw [hmap]
  exact algebraMap_isIntegral_iff.mpr hkey

/-- **Exercise 5.35, forward implication:** an integral `f : A → B` gives, for every
`A`-algebra `C`, a closed map `(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C`. -/
theorem isClosedBaseChange_of_isIntegral (h : Algebra.IsIntegral A B) :
    IsClosedBaseChange A B :=
  fun C _ _ => isClosedMap_comap_tensorProduct_of_isIntegral C h

end Integral

/-! ### Auxiliary: the canonical ring isomorphism `B ⊗[A] A[X] ≃+* B[X]`

The closedness hypothesis of the exercise is only needed for one particular algebra `C`,
namely `C = A[X]`, where `B ⊗[A] A[X]` is the polynomial ring `B[X]`.  The next few lemmas
build this isomorphism explicitly (`tensorPolynomialHom` and `tensorPolynomialInv` are mutually
inverse) and identify the resulting map `A[X] → B[X]` with `Polynomial.mapRingHom (algebraMap A B)`. -/

section TensorPolynomial

variable (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The ring hom `B ⊗[A] A[X] →+* B[X]`, `b ⊗ p ↦ C b * p.map (algebraMap A B)`. -/
noncomputable def tensorPolynomialHom : B ⊗[A] A[X] →+* B[X] :=
  (Algebra.TensorProduct.lift (Polynomial.CAlgHom (R := A) (A := B))
    (Polynomial.mapAlgHom (Algebra.ofId A B))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The ring hom `B[X] →+* B ⊗[A] A[X]`, `C b ↦ b ⊗ 1`, `X ↦ 1 ⊗ X`. -/
noncomputable def tensorPolynomialInv : B[X] →+* B ⊗[A] A[X] :=
  Polynomial.eval₂RingHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A[X])) (1 ⊗ₜ X)

lemma one_tmul_C_eq (a : A) :
    (1 : B) ⊗ₜ[A] (C a : A[X]) = (algebraMap A B a) ⊗ₜ[A] (1 : A[X]) := by
  have h := congr($(Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    (R := A) (A := B) (B := A[X])) a)
  simpa using h.symm

lemma tensorPolynomialHom_tmul (b : B) (p : A[X]) :
    tensorPolynomialHom A B (b ⊗ₜ p)
      = C b * Polynomial.mapRingHom (algebraMap A B) p := by
  simp [tensorPolynomialHom]

lemma tensorPolynomialHom_inv_C (b : B) :
    tensorPolynomialHom A B (tensorPolynomialInv A B (C b)) = C b := by
  simp [tensorPolynomialInv, tensorPolynomialHom]

lemma tensorPolynomialHom_inv_X :
    tensorPolynomialHom A B (tensorPolynomialInv A B X) = X := by
  simp [tensorPolynomialInv, tensorPolynomialHom]

lemma tensorPolynomialHom_comp_inv :
    (tensorPolynomialHom A B).comp (tensorPolynomialInv A B) = RingHom.id B[X] := by
  apply Polynomial.ringHom_ext
  · intro b; simpa using tensorPolynomialHom_inv_C A B b
  · simpa using tensorPolynomialHom_inv_X A B

lemma tensorPolynomialHom_inv_apply (p : B[X]) :
    tensorPolynomialHom A B (tensorPolynomialInv A B p) = p := by
  have h := congr($(tensorPolynomialHom_comp_inv A B) p)
  simpa using h

lemma tensorPolynomialInv_mapRingHom (p : A[X]) :
    tensorPolynomialInv A B (Polynomial.mapRingHom (algebraMap A B) p)
      = (1 : B) ⊗ₜ[A] p := by
  have key : (tensorPolynomialInv A B).comp (Polynomial.mapRingHom (algebraMap A B))
      = (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.toRingHom_eq_coe]
      simp [tensorPolynomialInv, one_tmul_C_eq]
    · simp [tensorPolynomialInv]
  have h2 := congr($key p)
  simpa using h2

lemma tensorPolynomialInv_comp_hom (x : B ⊗[A] A[X]) :
    tensorPolynomialInv A B (tensorPolynomialHom A B x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b p =>
      rw [tensorPolynomialHom_tmul, map_mul, tensorPolynomialInv_mapRingHom]
      simp [tensorPolynomialInv]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **The canonical ring isomorphism** `B ⊗[A] A[X] ≃+* B[X]`. -/
noncomputable def tensorPolynomialEquiv : B ⊗[A] A[X] ≃+* B[X] where
  toFun := tensorPolynomialHom A B
  invFun := tensorPolynomialInv A B
  left_inv := tensorPolynomialInv_comp_hom A B
  right_inv := tensorPolynomialHom_inv_apply A B
  map_mul' := map_mul _
  map_add' := map_add _

lemma tensorPolynomialEquiv_includeRight (p : A[X]) :
    tensorPolynomialEquiv A B
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X]) p)
      = Polynomial.mapRingHom (algebraMap A B) p := by
  rw [show Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X]) p = (1 : B) ⊗ₜ p
    from rfl]
  rw [show tensorPolynomialEquiv A B ((1 : B) ⊗ₜ p)
      = tensorPolynomialHom A B ((1 : B) ⊗ₜ p) from rfl,
    tensorPolynomialHom_tmul, map_one, one_mul]

lemma tensorPolynomialEquiv_comp_includeRight :
    (tensorPolynomialEquiv A B).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom
      = Polynomial.mapRingHom (algebraMap A B) := by
  apply Polynomial.ringHom_ext
  · intro a
    simpa using tensorPolynomialEquiv_includeRight A B (C a)
  · simpa using tensorPolynomialEquiv_includeRight A B (X : A[X])

end TensorPolynomial

/-! ### The converse -/

section Converse

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Closedness of `Spec (B ⊗[A] A[X]) → Spec A[X]`, transported along the canonical
isomorphism `B ⊗[A] A[X] ≃+* B[X]`, gives closedness of
`Spec B[X] → Spec A[X]`, i.e. of `comap (mapRingHom (algebraMap A B))`. -/
theorem isClosedMap_comap_mapRingHom_of_isClosedMap_tensorProduct_polynomial
    (h : IsClosedMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom)) :
    IsClosedMap (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap A B))) := by
  have h2 : IsClosedMap (PrimeSpectrum.comap (tensorPolynomialEquiv A B).toRingHom) :=
    (PrimeSpectrum.isHomeomorph_comap_of_bijective (tensorPolynomialEquiv A B).bijective).isClosedMap
  have h3 : IsClosedMap ((PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom) ∘
        (PrimeSpectrum.comap (tensorPolynomialEquiv A B).toRingHom)) := h.comp h2
  rw [show Polynomial.mapRingHom (algebraMap A B)
      = (tensorPolynomialEquiv A B).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom
      from (tensorPolynomialEquiv_comp_includeRight A B).symm, PrimeSpectrum.comap_comp]
  exact h3

/-- The same for the hypothesis of the exercise (closedness for all `A`-algebras). -/
theorem isClosedMap_comap_mapRingHom_of_isClosedBaseChange
    (h : IsClosedBaseChange A B) :
    IsClosedMap (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap A B))) :=
  isClosedMap_comap_mapRingHom_of_isClosedMap_tensorProduct_polynomial (h (A[X]))

/-- **A strictly stronger form of the converse of Exercise 5.35:** it is enough to test the
closedness hypothesis at the single `A`-algebra `C = A[X]`; no hypothesis on `B` is needed. -/
theorem isIntegral_of_isClosedMap_tensorProduct_polynomial
    (h : IsClosedMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A[X])).toRingHom)) :
    Algebra.IsIntegral A B := by
  have hclosed := isClosedMap_comap_mapRingHom_of_isClosedMap_tensorProduct_polynomial h
  have h' := PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom (algebraMap A B) hclosed
  rwa [algebraMap_isIntegral_iff] at h'

/-- **Exercise 5.35, converse, in the generality actually available:** if for every
`A`-algebra `C` the map `(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C` is closed, then `f : A → B` is
integral.  No hypothesis on `B` is needed. -/
theorem isIntegral_of_isClosedBaseChange (h : IsClosedBaseChange A B) :
    Algebra.IsIntegral A B :=
  isIntegral_of_isClosedMap_tensorProduct_polynomial (h (A[X]))

/-- **Exercise 5.35, part (b):** if `B` is an integral domain and `f : A → B` has the property
that `(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C` is a closed map for every `A`-algebra `C`, then `f`
is integral. -/
theorem isIntegral_of_isClosedBaseChange_of_isDomain [IsDomain B]
    (h : IsClosedBaseChange A B) : Algebra.IsIntegral A B :=
  isIntegral_of_isClosedBaseChange h

/-- **Exercise 5.35, part (c):** the converse above remains valid if `B` has only finitely many
minimal prime ideals. -/
theorem isIntegral_of_isClosedBaseChange_of_finite_minimalPrimes
    (h : IsClosedBaseChange A B) (hmin : (minimalPrimes B).Finite) :
    Algebra.IsIntegral A B := by
  have := hmin -- the finiteness hypothesis is not needed by the proof below
  exact isIntegral_of_isClosedBaseChange h

/-- **Exercise 5.35, part (c), Noetherian instance:** a Noetherian `B` has only finitely many
minimal prime ideals, so the converse holds. -/
theorem isIntegral_of_isClosedBaseChange_of_isNoetherianRing [IsNoetherianRing B]
    (h : IsClosedBaseChange A B) : Algebra.IsIntegral A B :=
  isIntegral_of_isClosedBaseChange_of_finite_minimalPrimes h
    (minimalPrimes.finite_of_isNoetherianRing (R := B))

end Converse

/-! ### The exercise phrased with an explicit ring hom `f : A →+* B`

The book quantifies over a ring hom `f : A → B`.  The results above use the equivalent (and
idiomatic) `Algebra A B` encoding of `f`; for completeness we restate the assertions of the
exercise with an explicit `f`. -/

section RingHomForm

/-- **Hypothesis of Exercise 5.35**, phrased for an explicit ring hom `f : A →+* B`:
`(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C` is a closed map for every `A`-algebra `C`. -/
def IsClosedBaseChangeHom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  ∀ (C : Type u) [CommRing C] [Algebra A C],
    IsClosedMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)

/-- **Exercise 5.35, first sentence:** an integral `f : A → B` gives, for every `A`-algebra `C`,
a closed map `(f ⊗ 1)* : Spec (B ⊗[A] C) → Spec C`. -/
theorem isClosedBaseChangeHom_of_isIntegral {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIntegral) : IsClosedBaseChangeHom f := by
  letI : Algebra A B := f.toAlgebra
  intro C _ _
  exact isClosedMap_comap_tensorProduct_of_isIntegral C (algebraMap_isIntegral_iff.mp hf)

/-- **Exercise 5.35, converse, for an explicit ring hom** (strengthened: no hypothesis on
`B`). -/
theorem isIntegral_of_isClosedBaseChangeHom {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (h : IsClosedBaseChangeHom f) : f.IsIntegral := by
  letI : Algebra A B := f.toAlgebra
  have h' : IsClosedBaseChange A B := h
  exact algebraMap_isIntegral_iff.mpr (isIntegral_of_isClosedBaseChange h')

/-- **Exercise 5.35, part (b), for an explicit ring hom:** `B` an integral domain. -/
theorem isIntegral_of_isClosedBaseChangeHom_of_isDomain {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain B] {f : A →+* B} (h : IsClosedBaseChangeHom f) : f.IsIntegral :=
  isIntegral_of_isClosedBaseChangeHom h

/-- **Exercise 5.35, part (c), for an explicit ring hom:** `B` has only finitely many minimal
prime ideals. -/
theorem isIntegral_of_isClosedBaseChangeHom_of_finite_minimalPrimes {A B : Type u}
    [CommRing A] [CommRing B] {f : A →+* B} (h : IsClosedBaseChangeHom f)
    (hmin : (minimalPrimes B).Finite) : f.IsIntegral := by
  have := hmin -- the finiteness hypothesis is not needed by the proof below
  exact isIntegral_of_isClosedBaseChangeHom h

/-- **Exercise 5.35, part (c), Noetherian instance, for an explicit ring hom.** -/
theorem isIntegral_of_isClosedBaseChangeHom_of_isNoetherianRing {A B : Type u}
    [CommRing A] [CommRing B] [IsNoetherianRing B] {f : A →+* B}
    (h : IsClosedBaseChangeHom f) : f.IsIntegral :=
  isIntegral_of_isClosedBaseChangeHom_of_finite_minimalPrimes h
    (minimalPrimes.finite_of_isNoetherianRing (R := B))

end RingHomForm

end AtiyahMcdonald69.Ex_5_35

/-! ### Axiom audit of the main exports -/

#print axioms AtiyahMcdonald69.Ex_5_35.tensorProduct_map_comp_includeRight
#print axioms AtiyahMcdonald69.Ex_5_35.isClosedMap_comap_tensorProduct_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_35.isClosedBaseChange_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedMap_tensorProduct_polynomial
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChange
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChange_of_isDomain
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChange_of_finite_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChange_of_isNoetherianRing
#print axioms AtiyahMcdonald69.Ex_5_35.isClosedBaseChangeHom_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChangeHom
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChangeHom_of_isDomain
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChangeHom_of_finite_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_5_35.isIntegral_of_isClosedBaseChangeHom_of_isNoetherianRing
#print axioms AtiyahMcdonald69.Ex_5_35.tensorPolynomialEquiv_comp_includeRight
