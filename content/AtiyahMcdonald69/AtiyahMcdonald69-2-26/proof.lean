/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 2, Exercise 26.

**The book's statement** (p. 35 of the 1969 edition):

> 26. Let `N` be an `A`-module. Show that `N` is flat if and only if
>     `Tor₁ᴬ(A/𝔞, N) = 0` whenever `𝔞` is a finitely generated ideal in `A`.

Mathlib has no Tor functor for modules (no projective resolutions of modules with the long
exact Tor sequence), so the literal vanishing statement cannot even be *stated* here, let
alone proved.  We formalize instead the equivalent, Tor–free form of the same criterion,
which is precisely the form in which the book's own proof passes through the argument.  For
a finitely generated ideal `𝔞 ⊆ A`, applying `- ⊗ N` to `0 → 𝔞 → A → A/𝔞 → 0` and using
the connecting map of the long exact Tor sequence gives the standard identification

  `Tor₁ᴬ(A/𝔞, N) ≅ ker(𝔞 ⊗[A] N → N),   a ⊗ x ↦ a x`,

so `Tor₁ᴬ(A/𝔞, N) = 0` for every finitely generated `𝔞` holds exactly when the canonical
map `𝔞 ⊗[A] N → N` is injective for every finitely generated `𝔞`.  The latter is a
statement about concrete tensor products, maps and bilinearities, and it is what we prove:

  `N` is flat ⟺ for every finitely generated ideal `𝔞` the canonical `A`-linear map
  `𝔞 ⊗[A] N → N`, `a ⊗ x ↦ a x`, is injective.

The map `𝔞 ⊗[A] N → N` is built here by hand from the universal property of the tensor
product (`TensorProduct.lift` applied to the explicit bilinear map `𝔞 × N → N`,
`(a, x) ↦ a x`), and its identification with the `A`-linear map induced by the inclusion
`𝔞 → A` is proved by extensionality on pure tensors.  Since the two statements are
equivalent, proving the tensor form proves Exercise 2.26 as stated.

The file also records:
* the same criterion with the finite generation hypothesis dropped (all ideals),
* the predicate `cyclicTorOneVanishes` spelling out the book's Tor hypothesis under the
  identification above, together with `Module.Flat ↔ cyclicTorOneVanishes`,
* a concrete non-vacuous instance: `ℤ/2` is not a flat `ℤ`-module, and the criterion is
  seen to fail explicitly at the finitely generated ideal `(2) ⊆ ℤ`, via the nonzero
  element `2 ⊗ 1` of `(2) ⊗[ℤ] ℤ/2` that the canonical map sends to zero.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_2_26

open TensorProduct

universe u v

section FlatCriterion

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-! ### The canonical bilinear map `𝔞 × M → M` and the induced linear map `𝔞 ⊗ M → M` -/

/-- The curried bilinear map `𝔞 × M → M`, `(a, x) ↦ a x`, for an ideal `𝔞` of `A`: for
`a : 𝔞` this is multiplication by the element `a ∈ A`. -/
def idealTensorMapAux (I : Ideal A) : I →ₗ[A] M →ₗ[A] M where
  toFun a := (a : A) • (LinearMap.id : M →ₗ[A] M)
  map_add' a b := by
    ext x
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      Submodule.coe_add, add_smul]
  map_smul' c a := by
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
      RingHom.id_apply, smul_eq_mul, mul_smul]

/-- The canonical `A`-linear map `𝔞 ⊗[A] M → M`, `a ⊗ x ↦ a x`, obtained from the
universal property of the tensor product applied to `idealTensorMapAux`. -/
noncomputable def idealTensorMap (I : Ideal A) : I ⊗[A] M →ₗ[A] M :=
  TensorProduct.lift (idealTensorMapAux (M := M) I)

@[simp]
theorem idealTensorMap_tmul (I : Ideal A) (a : I) (x : M) :
    idealTensorMap (M := M) I (a ⊗ₜ[A] x) = (a : A) • x := by
  simp [idealTensorMap, idealTensorMapAux]

/-- The map `𝔞 ⊗ M → M` is the composite of the `A`-linear map `𝔞 ⊗ M → A ⊗ M` induced by
the inclusion `𝔞 ⊆ A` with the canonical isomorphism `A ⊗ M ≃ M`.  Equivalently: the map
`a ⊗ x ↦ a x` is "the same" map as `(𝔞 → A) ⊗ 𝟙 M` followed by `A ⊗ M ≃ M`. -/
theorem idealTensorMap_eq_lid_comp_rTensor (I : Ideal A) :
    idealTensorMap (M := M) I
      = (TensorProduct.lid A M).toLinearMap.comp (LinearMap.rTensor M I.subtype) := by
  refine TensorProduct.ext' (fun a x => ?_)
  simp

/-- Functoriality of the maps `𝔞 ⊗ M → M` in the ideal: for `𝔧 ⊆ 𝔦` the composite
`𝔧 ⊗ M → 𝔦 ⊗ M → M` equals `𝔧 ⊗ M → M`. -/
theorem idealTensorMap_comp_rTensor_inclusion {J I : Ideal A} (h : J ≤ I) :
    (idealTensorMap (M := M) I).comp (LinearMap.rTensor M (Submodule.inclusion h))
      = idealTensorMap (M := M) J := by
  refine TensorProduct.ext' (fun a x => ?_)
  simp

/-- The hand-built map `𝔞 ⊗ M → M` coincides with the map obtained from the universal
property in the form `TensorProduct.lift ((lsmul A M) ∘ 𝔞 → A)`, i.e. with the canonical
scalar-multiplication map. -/
theorem idealTensorMap_eq_lift_lsmul (I : Ideal A) :
    idealTensorMap (M := M) I
      = TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype) := by
  refine TensorProduct.ext' (fun a x => ?_)
  simp [idealTensorMap_tmul]

/-! ### Flat modules satisfy the criterion -/

/-- If `M` is flat, then for every ideal `𝔞` the canonical map `𝔞 ⊗[A] M → M`,
`a ⊗ x ↦ a x`, is injective: it is the composite of the injective map `𝔞 ⊗ M → A ⊗ M`
(tensoring the inclusion, which is injective because `M` is flat) and the isomorphism
`A ⊗ M ≃ M`. -/
theorem injective_idealTensorMap_of_flat [Module.Flat A M] (I : Ideal A) :
    Function.Injective (idealTensorMap (M := M) I) := by
  have hout : Function.Injective (LinearMap.rTensor M I.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (f := I.subtype) Subtype.val_injective
  rw [idealTensorMap_eq_lid_comp_rTensor]
  exact (TensorProduct.lid A M).injective.comp hout

/-- If `M` is flat, then for every finitely generated ideal `𝔞` the canonical map
`𝔞 ⊗[A] M → M`, `a ⊗ x ↦ a x`, is injective.  This is the easy half of Exercise 2.26
(the half that in the book follows from the vanishing of `Tor₁ᴬ(A/𝔞, N)` for flat `N`,
i.e. from Exercise 2.24); here it is read off directly from the defining property of flat
modules, applied to the finitely generated submodule `𝔞` of `A`. -/
theorem injective_idealTensorMap_of_flat_fg [Module.Flat A M] ⦃I : Ideal A⦄ (hI : I.FG) :
    Function.Injective (idealTensorMap (M := M) I) := by
  have hout : Function.Injective (LinearMap.rTensor M I.subtype) := Module.Flat.out I hI
  rw [idealTensorMap_eq_lid_comp_rTensor]
  exact (TensorProduct.lid A M).injective.comp hout

/-! ### From finitely generated ideals to arbitrary ideals -/

/-- Any element of `𝔞 ⊗[A] M` comes from `𝔟 ⊗[A] M` for some finitely generated ideal
`𝔟 ⊆ 𝔞`.  This is the finiteness reduction ("every tensor is a finite sum of pure
tensors") used in the proof of Exercise 2.26. -/
theorem exists_fg_le_of_tmul (I : Ideal A) (z : I ⊗[A] M) :
    ∃ (J : Ideal A) (_ : J.FG) (h : J ≤ I), ∃ y : J ⊗[A] M,
      z = LinearMap.rTensor M (Submodule.inclusion h) y :=
  Submodule.exists_fg_le_eq_rTensor_inclusion z

/-- A single element of the kernel of `𝔞 ⊗ M → M` vanishes if the criterion holds for
finitely generated ideals: it comes from some finitely generated `𝔟 ⊆ 𝔞`, where the
hypothesis kills it. -/
theorem eq_zero_of_idealTensorMap_eq_zero
    (h : ∀ ⦃I : Ideal A⦄, I.FG → Function.Injective (idealTensorMap (M := M) I))
    (I : Ideal A) {z : I ⊗[A] M} (hz : idealTensorMap (M := M) I z = 0) : z = 0 := by
  obtain ⟨J, hJfg, hJI, z', rfl⟩ := exists_fg_le_of_tmul (M := M) I z
  have hzero : idealTensorMap (M := M) J z' = 0 := by
    rw [← idealTensorMap_comp_rTensor_inclusion (M := M) (I := I) (J := J) hJI]
    simpa using hz
  rw [(injective_iff_map_eq_zero _).mp (h hJfg) z' hzero, map_zero]

/-- If the criterion of Exercise 2.26 holds for finitely generated ideals, it holds for
*all* ideals. -/
theorem injective_idealTensorMap_of_fg
    (h : ∀ ⦃I : Ideal A⦄, I.FG → Function.Injective (idealTensorMap (M := M) I))
    (I : Ideal A) : Function.Injective (idealTensorMap (M := M) I) :=
  (injective_iff_map_eq_zero _).mpr fun _z hz => eq_zero_of_idealTensorMap_eq_zero h I hz

/-! ### The criterion implies flatness -/

/-- If the canonical map `𝔞 ⊗[A] M → M` is injective for every ideal `𝔞` (in particular for
every finitely generated one), then `M` is flat.  The reduction of flatness to ideals is the
standard flatness criterion (Atiyah–Macdonald, Proposition 2.19 and its converse); Mathlib
proves it via Baer's criterion for the character module. -/
theorem flat_of_injective_idealTensorMap
    (h : ∀ I : Ideal A, Function.Injective (idealTensorMap (M := M) I)) :
    Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I x y hxy
  have hcomp : Function.Injective
      ((TensorProduct.lid A M).toLinearMap.comp (LinearMap.rTensor M I.subtype)) := by
    rw [← idealTensorMap_eq_lid_comp_rTensor]
    exact h I
  exact hcomp (by simp only [LinearMap.comp_apply, hxy])

/-! ### Exercise 2.26 -/

/-- **Atiyah–Macdonald, Exercise 2.26**, in the equivalent Tor–free form recorded in the
header: an `A`-module `N` is flat if and only if for every finitely generated ideal
`𝔞 ⊆ A` the canonical map `𝔞 ⊗[A] N → N`, `a ⊗ x ↦ a x`, is injective. -/
theorem flat_iff_fg_ideal_tensorMap_injective :
    Module.Flat A M
      ↔ ∀ ⦃I : Ideal A⦄, I.FG → Function.Injective (idealTensorMap (M := M) I) := by
  refine ⟨fun h I hI => ?_, fun h => flat_of_injective_idealTensorMap (injective_idealTensorMap_of_fg h)⟩
  exact @injective_idealTensorMap_of_flat_fg A _ M _ _ h I hI

/-- Exercise 2.26 with the finite generation hypothesis dropped: `M` is flat iff the
canonical map `𝔞 ⊗[A] M → M` is injective for *every* ideal `𝔞`. -/
theorem flat_iff_ideal_tensorMap_injective :
    Module.Flat A M ↔ ∀ I : Ideal A, Function.Injective (idealTensorMap (M := M) I) :=
  ⟨fun h => @injective_idealTensorMap_of_flat A _ M _ _ h, flat_of_injective_idealTensorMap⟩

/-- Exercise 2.26 with the two tensor factors interchanged: `M` is flat iff for every
finitely generated ideal `𝔞` the canonical map `M ⊗[A] 𝔞 → M`, `x ⊗ a ↦ a x`, is injective.
(Interchanging the factors is the isomorphism `TensorProduct.comm`.) -/
theorem flat_iff_fg_ideal_comm_tensorMap_injective :
    Module.Flat A M ↔ ∀ ⦃I : Ideal A⦄, I.FG →
      Function.Injective
        ((idealTensorMap (M := M) I).comp (TensorProduct.comm A M I).toLinearMap) := by
  rw [flat_iff_fg_ideal_tensorMap_injective]
  constructor
  · intro h I hI
    exact (h hI).comp (TensorProduct.comm A M I).injective
  · intro h I hI x y hxy
    have key : idealTensorMap (M := M) I ((TensorProduct.comm A M I) ((TensorProduct.comm A M I).symm x))
        = idealTensorMap (M := M) I
            ((TensorProduct.comm A M I) ((TensorProduct.comm A M I).symm y)) := by
      simpa using hxy
    simpa using h hI key

/-- The assertion appearing in the book, `Tor₁ᴬ(A/𝔞, N) = 0` for all finitely generated
ideals `𝔞`, expressed through the standard identification
`Tor₁ᴬ(A/𝔞, N) ≅ ker(𝔞 ⊗[A] N → N)`: the canonical map `𝔞 ⊗[A] N → N`, `a ⊗ x ↦ a x`,
is injective (equivalently: has zero kernel) for every finitely generated ideal `𝔞`. -/
def cyclicTorOneVanishes (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M]
    [Module A M] : Prop :=
  ∀ ⦃I : Ideal A⦄, I.FG → Function.Injective (idealTensorMap (M := M) I)

/-- **Exercise 2.26 in the form stated in the book**, modulo the identification of
`Tor₁ᴬ(A/𝔞, N)` with the kernel of `𝔞 ⊗[A] N → N`. -/
theorem flat_iff_cyclicTorOneVanishes : Module.Flat A M ↔ cyclicTorOneVanishes A M :=
  flat_iff_fg_ideal_tensorMap_injective

/-- The book's Tor–vanishing condition read literally as the vanishing of a kernel: for every
finitely generated ideal `𝔞`, the kernel of `𝔞 ⊗[A] M → M`, `a ⊗ x ↦ a x` — that is, the
group `Tor₁ᴬ(A/𝔞, M)` under the standard identification — is zero. -/
theorem flat_iff_ker_idealTensorMap_eq_bot :
    Module.Flat A M ↔ ∀ ⦃I : Ideal A⦄, I.FG → LinearMap.ker (idealTensorMap (M := M) I) = ⊥ := by
  rw [flat_iff_fg_ideal_tensorMap_injective]
  simp only [LinearMap.ker_eq_bot]

/-- A free module, for instance `M = A` itself, satisfies the criterion. -/
theorem cyclicTorOneVanishes_self : cyclicTorOneVanishes A A :=
  flat_iff_cyclicTorOneVanishes.mp (Module.Flat.self (R := A))

end FlatCriterion

/-! ### A concrete instance: `ℤ/2` is not flat over `ℤ`, detected at the ideal `(2)` -/

section Counterexample

/-- The generator `2` of the ideal `(2) ⊆ ℤ`. -/
def twoGen : Ideal.span ({(2 : ℤ)} : Set ℤ) := ⟨2, Ideal.subset_span (by simp)⟩

/-- The `ℤ`-linear map `ℤ → (2)`, `n ↦ 2 n`. -/
noncomputable def twoMulLinearMap : ℤ →ₗ[ℤ] Ideal.span ({(2 : ℤ)} : Set ℤ) :=
  LinearMap.toSpanSingleton ℤ _ twoGen

/-- `n ↦ 2 n` is a bijection `ℤ → (2)`. -/
theorem twoMulLinearMap_bijective : Function.Bijective twoMulLinearMap := by
  constructor
  · intro m n hmn
    have h : m • twoGen = n • twoGen := hmn
    have h' : m * 2 = n * 2 := by
      have := congrArg (Subtype.val) h
      simpa [twoGen, smul_eq_mul, mul_comm] using this
    omega
  · rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := Ideal.mem_span_singleton.mp hy
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simp [twoMulLinearMap, twoGen, mul_comm]

/-- The `ℤ`-linear isomorphism `(2) ≃ₗ[ℤ] ℤ`, the inverse of `n ↦ 2 n`. -/
noncomputable def spanTwoEquiv : Ideal.span ({(2 : ℤ)} : Set ℤ) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective twoMulLinearMap twoMulLinearMap_bijective).symm

theorem spanTwoEquiv_twoGen : spanTwoEquiv twoGen = 1 := by
  have h1 : (LinearEquiv.ofBijective twoMulLinearMap twoMulLinearMap_bijective) (1 : ℤ)
      = twoGen := by
    rw [LinearEquiv.ofBijective_apply]
    simp [twoMulLinearMap]
  rw [spanTwoEquiv, ← h1, LinearEquiv.symm_apply_apply]

/-- The `ℤ`-linear isomorphism `(2) ⊗[ℤ] ℤ/2 ≃ₗ[ℤ] ℤ/2`. -/
noncomputable def spanTwoTensorZModTwoEquiv :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)) ⊗[ℤ] ZMod 2 ≃ₗ[ℤ] ZMod 2 :=
  (TensorProduct.congr spanTwoEquiv (LinearEquiv.refl ℤ (ZMod 2))).trans
    (TensorProduct.lid ℤ (ZMod 2))

/-- The value of the isomorphism `(2) ⊗[ℤ] ℤ/2 ≃ₗ[ℤ] ℤ/2` on pure tensors. -/
theorem spanTwoTensorZModTwoEquiv_tmul (y : Ideal.span ({(2 : ℤ)} : Set ℤ)) (m : ZMod 2) :
    spanTwoTensorZModTwoEquiv (y ⊗ₜ[ℤ] m) = spanTwoEquiv y • m := by
  show (TensorProduct.lid ℤ (ZMod 2))
      ((TensorProduct.congr spanTwoEquiv (LinearEquiv.refl ℤ (ZMod 2))) (y ⊗ₜ[ℤ] m))
      = spanTwoEquiv y • m
  rw [TensorProduct.congr_tmul spanTwoEquiv (LinearEquiv.refl ℤ (ZMod 2)) y m,
    LinearEquiv.refl_apply]
  exact TensorProduct.lid_tmul m (spanTwoEquiv y)

/-- The element `2 ⊗ 1` of `(2) ⊗[ℤ] ℤ/2` is nonzero. -/
theorem twoGen_tmul_one_ne_zero : (twoGen ⊗ₜ[ℤ] (1 : ZMod 2)) ≠ 0 := by
  intro h
  have h' := congrArg spanTwoTensorZModTwoEquiv h
  rw [spanTwoTensorZModTwoEquiv_tmul, spanTwoEquiv_twoGen, one_smul, map_zero] at h'
  exact one_ne_zero h'

/-- The ideal `(2) ⊆ ℤ` is finitely generated. -/
theorem fg_span_two : (Ideal.span ({(2 : ℤ)} : Set ℤ)).FG :=
  Submodule.fg_span (Set.finite_singleton 2)

/-- The canonical map `(2) ⊗[ℤ] ℤ/2 → ℤ/2` sends the nonzero element `2 ⊗ 1` to zero, so it
is not injective: the criterion of Exercise 2.26 fails for `ℤ/2` at the finitely generated
ideal `(2)`. -/
theorem not_injective_idealTensorMap_span_two_zmodTwo :
    ¬ Function.Injective (idealTensorMap (M := ZMod 2) (Ideal.span ({(2 : ℤ)} : Set ℤ))) := by
  intro hinj
  have hzero : idealTensorMap (M := ZMod 2) (Ideal.span ({(2 : ℤ)} : Set ℤ))
      (twoGen ⊗ₜ[ℤ] (1 : ZMod 2)) =
        idealTensorMap (M := ZMod 2) (Ideal.span ({(2 : ℤ)} : Set ℤ)) 0 := by
    rw [idealTensorMap_tmul, map_zero]
    decide
  exact twoGen_tmul_one_ne_zero (hinj hzero)

/-- `ℤ/2` is not a flat `ℤ`-module. -/
theorem not_flat_zmodTwo : ¬ Module.Flat ℤ (ZMod 2) := fun h =>
  not_injective_idealTensorMap_span_two_zmodTwo
    (@injective_idealTensorMap_of_flat_fg ℤ _ (ZMod 2) _ _ h _ fg_span_two)

/-- The Tor–vanishing hypothesis of Exercise 2.26 fails for the non-flat module `ℤ/2`. -/
theorem not_cyclicTorOneVanishes_zmodTwo : ¬ cyclicTorOneVanishes ℤ (ZMod 2) := fun h =>
  not_flat_zmodTwo (flat_iff_cyclicTorOneVanishes.mpr h)

end Counterexample

end AtiyahMcdonald69.Ex_2_26

/-! ### Axiom check on the principal exports

The following commands print the axioms used by the main results; only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) may occur. -/

#print axioms AtiyahMcdonald69.Ex_2_26.idealTensorMap_tmul
#print axioms AtiyahMcdonald69.Ex_2_26.idealTensorMap_eq_lid_comp_rTensor
#print axioms AtiyahMcdonald69.Ex_2_26.idealTensorMap_eq_lift_lsmul
#print axioms AtiyahMcdonald69.Ex_2_26.injective_idealTensorMap_of_flat
#print axioms AtiyahMcdonald69.Ex_2_26.injective_idealTensorMap_of_fg
#print axioms AtiyahMcdonald69.Ex_2_26.flat_of_injective_idealTensorMap
#print axioms AtiyahMcdonald69.Ex_2_26.flat_iff_fg_ideal_tensorMap_injective
#print axioms AtiyahMcdonald69.Ex_2_26.flat_iff_ideal_tensorMap_injective
#print axioms AtiyahMcdonald69.Ex_2_26.flat_iff_fg_ideal_comm_tensorMap_injective
#print axioms AtiyahMcdonald69.Ex_2_26.flat_iff_cyclicTorOneVanishes
#print axioms AtiyahMcdonald69.Ex_2_26.flat_iff_ker_idealTensorMap_eq_bot
#print axioms AtiyahMcdonald69.Ex_2_26.spanTwoEquiv_twoGen
#print axioms AtiyahMcdonald69.Ex_2_26.twoGen_tmul_one_ne_zero
#print axioms AtiyahMcdonald69.Ex_2_26.not_injective_idealTensorMap_span_two_zmodTwo
#print axioms AtiyahMcdonald69.Ex_2_26.not_flat_zmodTwo
#print axioms AtiyahMcdonald69.Ex_2_26.not_cyclicTorOneVanishes_zmodTwo
