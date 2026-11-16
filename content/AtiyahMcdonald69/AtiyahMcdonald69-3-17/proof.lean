/-
Atiyah–Macdonald (1969), *Introduction to Commutative Algebra*,
Chapter 3 (Rings and Modules of Fractions), **Exercise 17**:

  Let `A --f--> B --g--> C` be ring homomorphisms.
  If `g ∘ f` is flat and `g` is faithfully flat, then `f` is flat.

This file formalizes the exercise completely, following the book's own proof
(which is also the "natural solution"): for an injection `M → N` of `A`-modules,
let `K` be the kernel of `B ⊗[A] M → B ⊗[A] N`.  Since `C` is flat over `B`, the
sequence `0 → C ⊗[B] K → C ⊗[B] (B ⊗[A] M) → C ⊗[B] (B ⊗[A] N)` is exact, and
under `C ⊗[B] (B ⊗[A] M) ≅ C ⊗[A] M` the last arrow is the arrow
`C ⊗[A] M → C ⊗[A] N`, which is injective because `g ∘ f` is flat.  Hence
`C ⊗[B] K = 0`, and faithful flatness (Exercise 3.16) gives `K = 0`.
Equivalently: injectivity of `B ⊗[A] -` is reflected by `C ⊗[B] -`, and
`C ⊗[B] (B ⊗[A] -)` is just `C ⊗[A] -`.  Both halves of the book's diagram are
formalized below as `cancelBaseChange_natural` and `lTensor_injective`.

Mathematical dictionary — the statements below concern the actual tensor
products and the actual flatness of ring maps, with no existential shortcuts:

* `RingHom.Flat f` (`Mathlib.RingTheory.RingHom.Flat`) means: the target of `f`
  is flat as a module over its source, i.e. `B` is a flat `A`-module.
* `RingHom.FaithfullyFlat g` (`Mathlib.RingTheory.RingHom.FaithfullyFlat`)
  means: `C` is faithfully flat as a `B`-module, i.e. Exercise 3.16's notion.
* `Module.Flat A B` is equivalent to: for every injective `A`-linear map
  `f : M → N`, the map `f.lTensor B : B ⊗[A] M → B ⊗[A] N` is injective
  (`Module.Flat.iff_lTensor_preserves_injective_linearMap`); this is what the
  book means by "`f` is flat".

Main results:

* `cancelBaseChange_natural`        : coherence of `C ⊗[B] (B ⊗[A] -) ≅ C ⊗[A] -`.
* `lTensor_injective`               : the heart of the proof (tensor-injectivity).
* `flat_of_flat_of_faithfullyFlat`  : Exercise 3.17, algebra formulation.
* `solution` (alias `exercise_3_17`) : Exercise 3.17 verbatim (ring homs).
* `flat_comp`                       : the companion composition statement.
* `faithfullyFlat_hypothesis_necessary` : faithful flatness of `g` cannot be
  weakened to flatness, with the explicit counterexample `ℚ[X] → ℚ → 0`.

Audit of the hypotheses (nothing is omitted in the Lean statements):

* No finiteness, Noetherian, reduced, domain or non-zero hypotheses: `A`, `B`,
  `C` are arbitrary commutative rings (the zero ring is allowed).
* `f` is not assumed injective and `g` is not assumed injective (faithful
  flatness does imply injectivity, see `RingHom.FaithfullyFlat.injective`).
* `g` must be faithfully flat, not merely flat: see §5.  The flatness hypothesis
  on `g ∘ f` cannot be dropped either: with `f` flat and `g` faithfully flat the
  composite `g ∘ f` is automatically flat (`flat_comp`), so the hypotheses are
  sharp.  In particular the theorem is *not* a consequence of the existence of
  some faithfully flat algebra over `B`.
-/
import Mathlib

set_option linter.style.haveILetI false

open TensorProduct
open scoped Polynomial

namespace AtiyahMcdonald69.Ex_3_17

universe u v w u'

/-! ### 1. The coherence identity `C ⊗[B] (B ⊗[A] M) ≅ C ⊗[A] M`

The two ways of tensoring an `A`-linear map `f : M → P` up to `C` agree under the
canonical identification `cancelBaseChange : C ⊗[B] (B ⊗[A] M) ≃ C ⊗[A] M`. -/

section Coherence

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Naturality of `AlgebraTensorModule.cancelBaseChange` in the module: the diagram

`C ⊗[B] (B ⊗[A] M) --(id_C ⊗ (id_B ⊗ f))--> C ⊗[B] (B ⊗[A] P)`

`     | cancelBaseChange                        | cancelBaseChange`

`C ⊗[A] M ---------------(id_C ⊗ f)----------> C ⊗[A] P`

commutes.  (This is `AlgebraTensorModule.lTensor_comp_cancelBaseChange`,
transported to an equality of functions.) -/
theorem cancelBaseChange_natural {M P : Type u'} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (f : M →ₗ[A] P) :
    (⇑(AlgebraTensorModule.lTensor (R := A) (A := B) (M := C) f)) ∘
        (⇑(AlgebraTensorModule.cancelBaseChange A B B C M)) =
      (⇑(AlgebraTensorModule.cancelBaseChange A B B C P)) ∘
        (⇑(LinearMap.lTensor (R := B) C
          (AlgebraTensorModule.lTensor (R := A) (A := B) (M := B) f))) := by
  have h := AlgebraTensorModule.lTensor_comp_cancelBaseChange (R := A) (A := B) (B := B)
    (M := C) (N := M) (Q := P) (f := f)
  simpa [LinearMap.coe_comp] using congrArg DFunLike.coe h

/-! ### 2. The heart: `C ⊗[B] -` reflects injectivity of `B ⊗[A] -`

This is exactly the diagram in the book: the bottom arrow `C ⊗[A] M → C ⊗[A] P` is
injective because `C` is flat over `A`, the vertical arrows are bijections, hence
the top arrow `B ⊗[A] M → B ⊗[A] P` becomes injective after applying `C ⊗[B] -`;
faithful flatness of `C` over `B` (Exercise 3.16(v)) then gives its injectivity. -/

/-- **Exercise 3.17, tensor-injectivity form.**
If `C` is flat over `A` (via `g ∘ f`) and faithfully flat over `B` (via `g`), then
`B ⊗[A] -` preserves injections: for every injective `A`-linear map `f : M → P`,
the map `f.lTensor B : B ⊗[A] M → B ⊗[A] P` is injective. -/
theorem lTensor_injective [Module.Flat A C] [Module.FaithfullyFlat B C]
    {M P : Type u'} [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    (f : M →ₗ[A] P) (hf : Function.Injective f) :
    Function.Injective (f.lTensor B) := by
  -- `f.lTensor B` is the `B`-linear map `AlgebraTensorModule.lTensor B B f`.
  set g : B ⊗[A] M →ₗ[B] B ⊗[A] P :=
    AlgebraTensorModule.lTensor (R := A) (A := B) (M := B) f with hg
  have hg_inj : Function.Injective g := by
    -- Exercise 3.16(v): faithful flatness of `C` over `B` reflects injectivity.
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective (R := B) (M := C) (f := g)]
    -- `g.lTensor C` is the bottom row of the diagram, up to `cancelBaseChange`.
    have hfC : Function.Injective
        (AlgebraTensorModule.lTensor (R := A) (A := B) (M := C) f) := by
      rw [AlgebraTensorModule.coe_lTensor (R := A) (A := B) (M := C) (N := M) (Q := P)]
      exact Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hcoh := cancelBaseChange_natural (A := A) (B := B) (C := C) (M := M) (P := P) f
    rw [← hg] at hcoh
    intro x y hxy
    have h2 : ((⇑(AlgebraTensorModule.cancelBaseChange A B B C P)) ∘
        (⇑(LinearMap.lTensor (R := B) C g))) x =
        ((⇑(AlgebraTensorModule.cancelBaseChange A B B C P)) ∘
        (⇑(LinearMap.lTensor (R := B) C g))) y := by
      simp only [Function.comp_apply]
      rw [hxy]
    rw [← hcoh] at h2
    simp only [Function.comp_apply] at h2
    exact (AlgebraTensorModule.cancelBaseChange A B B C M).injective (hfC h2)
  rwa [← AlgebraTensorModule.coe_lTensor (R := A) (A := B) (M := B) (N := M) (Q := P) (f := f)]

/-! ### 3. Exercise 3.17, algebra formulation -/

/-- **Exercise 3.17** (algebra form). Let `A → B → C` be commutative rings with
`IsScalarTower A B C`.  If `C` is flat over `A` and faithfully flat over `B`,
then `B` is flat over `A`. -/
theorem flat_of_flat_of_faithfullyFlat [Module.Flat A C] [Module.FaithfullyFlat B C] :
    Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M P _ _ _ _ f hf
  exact lTensor_injective (A := A) (B := B) (C := C) f hf

end Coherence

/-! ### 4. Exercise 3.17 in the book's own formulation -/

section RingHomVersion

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- **Atiyah–Macdonald, Exercise 3.17.** Let `f : A →+* B` and `g : B →+* C` be
ring homomorphisms such that `g ∘ f` is flat and `g` is faithfully flat.  Then
`f` is flat. -/
theorem solution (f : A →+* B) (g : B →+* C)
    (hgf : (g.comp f).Flat) (hg : g.FaithfullyFlat) : f.Flat := by
  rw [RingHom.Flat, RingHom.FaithfullyFlat] at *
  algebraize [f, g, g.comp f]
  exact flat_of_flat_of_faithfullyFlat (A := A) (B := B) (C := C)

/-- `exercise_3_17` is `solution` under the exercise's own name. -/
theorem exercise_3_17 (f : A →+* B) (g : B →+* C)
    (hgf : (g.comp f).Flat) (hg : g.FaithfullyFlat) : f.Flat :=
  solution f g hgf hg

/-- The companion composition statement: flatness is stable under composition, so
with `f` flat and `g` faithfully flat the hypothesis that `g ∘ f` is flat is
automatic.  This shows that the two hypotheses of Exercise 3.17 are sharp: the
only one that can be weakened is faithfulness, and it cannot (see §5). -/
theorem flat_comp (f : A →+* B) (g : B →+* C) (hf : f.Flat) (hg : g.Flat) :
    (g.comp f).Flat :=
  hf.comp hg

/-- Exercise 3.16(iv), the faithful-flatness criterion used in the proof:
if `C` is faithfully flat over `B`, then `C ⊗[B] M` is trivial iff `M` is. -/
theorem faithfullyFlat_tensor_subsingleton {B C M : Type*} [CommRing B] [CommRing C]
    [Algebra B C] [Module.FaithfullyFlat B C] [AddCommGroup M] [Module B M] :
    Subsingleton (C ⊗[B] M) ↔ Subsingleton M :=
  Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C

/-- Exercise 3.16(v), the precise form used in the proof: tensoring with a
faithfully flat module reflects injectivity. -/
theorem faithfullyFlat_lTensor_injective_iff {B C M P : Type*} [CommRing B] [CommRing C]
    [Algebra B C] [Module.FaithfullyFlat B C] [AddCommGroup M] [Module B M]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] P) :
    Function.Injective (f.lTensor C) ↔ Function.Injective f :=
  Module.FaithfullyFlat.lTensor_injective_iff_injective (R := B) (M := C) f

end RingHomVersion

/-! ### 5. Sharpness: faithful flatness of `g` cannot be weakened to flatness

`A = ℚ[X]`, `B = ℚ` (a `ℚ[X]`-algebra via `X ↦ 0`), `C = 0` (the zero ring).
Then `f : ℚ[X] → ℚ` is not flat (`X` is a non-zero-divisor of `ℚ[X]`, but acts as
`0` on `ℚ`), the map `g : ℚ → 0` is flat (any map into a trivial ring is), the
composite `g ∘ f` is flat, but `g` is not faithfully flat, since
`0 ⊗[ℚ] ℚ = 0` while `ℚ ≠ 0`.  Hence the conclusion of Exercise 3.17 genuinely
needs faithful flatness of `g`. -/

section Counterexample

/-- The unique ring homomorphism from `R` to the zero ring `ℤ/1`. -/
def toZeroRing (R : Type*) [CommRing R] : R →+* ZMod 1 where
  toFun := fun _ => 0
  map_one' := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' := fun _ _ => Subsingleton.elim _ _
  map_mul' := fun _ _ => Subsingleton.elim _ _

/-- The ring homomorphism `ℚ[X] → ℚ`, `X ↦ 0`. -/
def evalZero : ℚ[X] →+* ℚ := Polynomial.evalRingHom 0

/-- A ring homomorphism into a trivial ring is flat: its target is the zero module. -/
theorem ringHom_flat_of_subsingleton_target {R S : Type*} [CommRing R] [CommRing S]
    [Subsingleton S] (φ : R →+* S) : φ.Flat := by
  rw [RingHom.Flat]
  letI : Algebra R S := φ.toAlgebra
  exact ⟨fun P _ _ _ N _ x y _ => Subsingleton.elim x y⟩

/-- `g = (ℚ → 0)` is not faithfully flat. -/
theorem not_faithfullyFlat_toZeroRing : ¬ (toZeroRing ℚ).FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat]
  letI : Algebra ℚ (ZMod 1) := (toZeroRing ℚ).toAlgebra
  intro h
  have hsub : Subsingleton ℚ := by
    rw [← Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (R := ℚ)
      (M := ZMod 1) (N := ℚ)]
    infer_instance
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-- `f : ℚ[X] → ℚ`, `X ↦ 0`, is not flat: `X` is a non-zero-divisor of `ℚ[X]`
while its image in `ℚ` is zero. -/
theorem not_flat_evalZero : ¬ evalZero.Flat := by
  rw [RingHom.Flat]
  letI : Algebra ℚ[X] ℚ := evalZero.toAlgebra
  intro h
  have hreg : IsSMulRegular ℚ[X] Polynomial.X := fun a b hab =>
    mul_left_cancel₀ Polynomial.X_ne_zero hab
  have h2 : IsSMulRegular ℚ (algebraMap ℚ[X] ℚ Polynomial.X) :=
    IsSMulRegular.of_flat (R := ℚ[X]) (S := ℚ) (x := Polynomial.X) hreg
  have h0 : algebraMap ℚ[X] ℚ Polynomial.X = 0 := by
    change evalZero Polynomial.X = 0
    simp [evalZero]
  rw [h0] at h2
  exact one_ne_zero (h2 (by simp))

/-- **Sharpness of Exercise 3.17.**  There are ring homomorphisms
`f : ℚ[X] → ℚ` and `g : ℚ → 0` such that `g ∘ f` is flat, `g` is flat, `g` is not
faithfully flat and `f` is not flat.  So the hypothesis "`g` faithfully flat"
cannot be replaced by "`g` flat". -/
theorem faithfullyFlat_hypothesis_necessary :
    ∃ (f : ℚ[X] →+* ℚ) (g : ℚ →+* ZMod 1),
      (g.comp f).Flat ∧ g.Flat ∧ ¬ g.FaithfullyFlat ∧ ¬ f.Flat :=
  ⟨evalZero, toZeroRing ℚ, ringHom_flat_of_subsingleton_target _,
    ringHom_flat_of_subsingleton_target _, not_faithfullyFlat_toZeroRing, not_flat_evalZero⟩

end Counterexample

end AtiyahMcdonald69.Ex_3_17
