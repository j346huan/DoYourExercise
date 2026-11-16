import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 3.4

*Statement (Chapter 3, Exercise 4).*  Let `f : A →+* B` be a homomorphism of rings and let
`S` be a multiplicatively closed subset of `A`.  Let `T = f(S)`.  Then `S⁻¹B` and `T⁻¹B`
are isomorphic as `S⁻¹A`-modules.

In the formalization below the ring homomorphism `f` is packaged as the `A`-algebra
structure on `B` (so that `f = algebraMap A B`); this loses no generality, since every ring
homomorphism `f : A →+* B` gives an `A`-algebra structure, and conversely
(`solution_of_ringHom` below states the exercise for an arbitrary `f : A →+* B`).

* `T = f(S)` is the submonoid `imageSubmonoid S = Algebra.algebraMapSubmonoid B S`.
* `S⁻¹B` is the localization of the `A`-module `B` at `S`, namely `LocalizedModule S B`
  (equivalently, the base change `S⁻¹A ⊗[A] B`, see `solutionAlgEquiv`).
* `T⁻¹B` is the localization of the ring `B` at `T`, namely `Localization T B`.

The isomorphism is the map of the book,

  `S⁻¹B → T⁻¹B,  b/s ↦ b/f(s)`,

see `solution_apply_mk`.  Its well definedness (`map_eq_of_mk_eq`) and injectivity
(`mk_eq_zero_of_map_eq_zero`) are the two verifications carried out in the book's proof.
-/

namespace AtiyahMcdonald69.Ex_3_4

open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- `T = f(S)`, where `f = algebraMap A B`: the image in `B` of the multiplicatively closed
subset `S` of `A`. -/
abbrev imageSubmonoid (S : Submonoid A) : Submonoid B := Algebra.algebraMapSubmonoid B S

theorem mem_imageSubmonoid {S : Submonoid A} {b : B} :
    b ∈ imageSubmonoid S ↔ ∃ s ∈ S, algebraMap A B s = b :=
  Submonoid.mem_map

/-! ### The `S⁻¹A`-algebra structure on `T⁻¹B` -/

/-- The canonical ring homomorphism `S⁻¹A →+* T⁻¹B`, `a/s ↦ f(a)/f(s)`, obtained from the
universal property of the localization of `A` at `S`: `f` maps `S` into `T`, and elements of
`T` are invertible in `T⁻¹B`.  This is the algebra structure with respect to which `T⁻¹B` is
an `S⁻¹A`-module in the statement of the exercise. -/
noncomputable def algebraMapLocalization (S : Submonoid A) :
    Localization (M := A) S →+* Localization (M := B) (imageSubmonoid S) :=
  IsLocalization.lift (M := S) (S := Localization (M := A) S)
    (g := (algebraMap B (Localization (M := B) (imageSubmonoid S))).comp (algebraMap A B))
    (fun y =>
      IsLocalization.map_units (Localization (M := B) (imageSubmonoid S))
        (⟨algebraMap A B y.1, Submonoid.mem_map_of_mem _ y.2⟩ : imageSubmonoid S))

/-- `algebraMapLocalization` restricts to `f` on `A`. -/
theorem algebraMapLocalization_algebraMap (S : Submonoid A) (a : A) :
    algebraMapLocalization S (algebraMap A (Localization (M := A) S) a) =
      algebraMap B (Localization (M := B) (imageSubmonoid S)) (algebraMap A B a) :=
  IsLocalization.lift_eq _ a

/-- `f(s)` as an element of `T⁻¹B` is the image of `s/1` under the canonical map
`S⁻¹A → T⁻¹B`. -/
theorem algebraMap_algebraMap_eq (S : Submonoid A) (a : A) :
    algebraMap B (Localization (M := B) (imageSubmonoid S)) (algebraMap A B a) =
      algebraMap (Localization (M := A) S) (Localization (M := B) (imageSubmonoid S))
        (algebraMap A (Localization (M := A) S) a) :=
  (IsScalarTower.algebraMap_apply A B (Localization (M := B) (imageSubmonoid S)) a).symm.trans
    (IsScalarTower.algebraMap_apply A (Localization (M := A) S)
      (Localization (M := B) (imageSubmonoid S)) a)

/-- `algebraMapLocalization` is the canonical `algebraMap`, i.e. the `S⁻¹A`-algebra structure
on `T⁻¹B` is the one induced by `A → B → T⁻¹B`. -/
theorem algebraMapLocalization_eq (S : Submonoid A) :
    algebraMapLocalization S =
      algebraMap (Localization (M := A) S) (Localization (M := B) (imageSubmonoid S)) := by
  apply IsLocalization.ringHom_ext S
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMapLocalization_algebraMap,
    algebraMap_algebraMap_eq]

/-! ### The isomorphism `S⁻¹B ≃ T⁻¹B` -/

/-- **Atiyah–Macdonald, Exercise 3.4.**  `S⁻¹B` and `T⁻¹B` are isomorphic as `S⁻¹A`-modules:
the localization of the `A`-module `B` at `S` is the localization of the ring `B` at
`T = f(S)`.

The map is `b/s ↦ b/f(s)`, see `solution_apply_mk`. -/
noncomputable def solutionLinearEquiv (S : Submonoid A) :
    LocalizedModule S B ≃ₗ[Localization (M := A) S] Localization (M := B) (imageSubmonoid S) :=
  (LocalizedModule.equivTensorProduct S B).trans
    ((Localization.tensorRightAlgEquiv (R := A) (M := S) (S := B)).toLinearEquiv)

/-- Pure tensors as scalar multiples of `1 ⊗ b`. -/
theorem tmul_eq_algebraMap_mul_one_tmul {C : Type*} [CommRing C] [Algebra A C] (x : C)
    (b : B) :
    x ⊗ₜ[A] b = algebraMap C (TensorProduct A C B) x * (1 ⊗ₜ[A] b) := by
  rw [show algebraMap C (TensorProduct A C B) x = x ⊗ₜ[A] (1 : B) from rfl]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The first step in computing `solutionLinearEquiv (b/s)`: it is `(1/s) * (b/1)`. -/
theorem solutionLinearEquiv_apply_mk_aux (S : Submonoid A) (b : B) (s : S) :
    solutionLinearEquiv S (LocalizedModule.mk b s) =
      algebraMap (Localization (M := A) S) (Localization (M := B) (imageSubmonoid S))
          (Localization.mk 1 s) *
        algebraMap B (Localization (M := B) (imageSubmonoid S)) b := by
  rw [solutionLinearEquiv, LinearEquiv.trans_apply, LocalizedModule.equivTensorProduct_apply_mk]
  change (Localization.tensorRightAlgEquiv (R := A) (M := S) (S := B))
      (Localization.mk 1 s ⊗ₜ[A] b) = _
  rw [tmul_eq_algebraMap_mul_one_tmul, map_mul]
  simp

/-- `(1/s) * f(s) = 1` in `T⁻¹B`. -/
theorem mk_one_mul_algebraMap (S : Submonoid A) (s : S) :
    algebraMap (Localization (M := A) S) (Localization (M := B) (imageSubmonoid S))
          (Localization.mk 1 s) *
        algebraMap B (Localization (M := B) (imageSubmonoid S)) (algebraMap A B s) = 1 := by
  rw [algebraMap_algebraMap_eq S s]
  rw [Localization.mk_eq_mk'_apply (M := S) (1 : A) s]
  rw [← map_mul, IsLocalization.mk'_spec]
  simp

/-- **The isomorphism is the map of the book**: `b/s ↦ b/f(s)`. -/
theorem solution_apply_mk (S : Submonoid A) (b : B) (s : S) :
    solutionLinearEquiv S (LocalizedModule.mk b s) =
      IsLocalization.mk' (Localization (M := B) (imageSubmonoid S)) b
        (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S) := by
  have hkey := mk_one_mul_algebraMap (B := B) S s
  have hunit : IsUnit (algebraMap B (Localization (M := B) (imageSubmonoid S))
      (algebraMap A B s)) :=
    IsLocalization.map_units (Localization (M := B) (imageSubmonoid S))
      (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S)
  rw [solutionLinearEquiv_apply_mk_aux S b s]
  refine (IsUnit.mul_left_inj hunit).mp ?_
  rw [mul_assoc, mul_comm (algebraMap B (Localization (M := B) (imageSubmonoid S)) b)
    (algebraMap B (Localization (M := B) (imageSubmonoid S)) (algebraMap A B s)),
    ← mul_assoc, hkey, one_mul,
    IsLocalization.mk'_spec (Localization (M := B) (imageSubmonoid S)) b
      (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S)]

/-- **Atiyah–Macdonald, Exercise 3.4** (existence form). -/
theorem solution (S : Submonoid A) :
    Nonempty (LocalizedModule S B ≃ₗ[Localization (M := A) S]
      Localization (M := B) (imageSubmonoid S)) :=
  ⟨solutionLinearEquiv S⟩

/-- The isomorphism is compatible with the canonical maps `B → S⁻¹B` (`b ↦ b/1`) and
`B → T⁻¹B`: both send `b` to `b/1`. -/
theorem solution_apply_mk_one (S : Submonoid A) (b : B) :
    solutionLinearEquiv S (LocalizedModule.mk b 1) =
      algebraMap B (Localization (M := B) (imageSubmonoid S)) b := by
  rw [solution_apply_mk]
  have h1 : (⟨algebraMap A B (1 : ↥S), Submonoid.mem_map_of_mem _ (1 : ↥S).2⟩ :
      imageSubmonoid S) = 1 := by
    ext
    simp
  rw [h1]
  exact IsLocalization.mk'_one (M := imageSubmonoid S)
    (Localization (M := B) (imageSubmonoid S)) b

/-- **Well definedness** (first half of the book's proof): if `b/s = b'/s'` in `S⁻¹B`, then
`b/f(s) = b'/f(s')` in `T⁻¹B`. -/
theorem map_eq_of_mk_eq (S : Submonoid A) {b b' : B} {s s' : S}
    (h : LocalizedModule.mk b s = LocalizedModule.mk b' s') :
    IsLocalization.mk' (Localization (M := B) (imageSubmonoid S)) b
        (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S) =
      IsLocalization.mk' (Localization (M := B) (imageSubmonoid S)) b'
        (⟨algebraMap A B s', Submonoid.mem_map_of_mem _ s'.2⟩ : imageSubmonoid S) := by
  rw [← solution_apply_mk, ← solution_apply_mk, h]

/-- **Injectivity** (second half of the book's proof): if `b/f(s) = 0` in `T⁻¹B`, then
`b/s = 0` in `S⁻¹B`. -/
theorem mk_eq_zero_of_map_eq_zero (S : Submonoid A) {b : B} {s : S}
    (h : IsLocalization.mk' (Localization (M := B) (imageSubmonoid S)) b
        (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S) = 0) :
    LocalizedModule.mk b s = 0 := by
  have h' : solutionLinearEquiv S (LocalizedModule.mk b s) = solutionLinearEquiv S 0 := by
    rw [map_zero, solution_apply_mk, h]
  exact (solutionLinearEquiv S).injective h'

/-- The same isomorphism at the level of rings: `S⁻¹B = S⁻¹A ⊗[A] B` and `T⁻¹B` are
isomorphic as `S⁻¹A`-algebras. -/
theorem solutionAlgEquiv (S : Submonoid A) :
    Nonempty (TensorProduct A (Localization (M := A) S) B ≃ₐ[Localization (M := A) S]
      Localization (M := B) (imageSubmonoid S)) :=
  ⟨Localization.tensorRightAlgEquiv (R := A) (M := S) (S := B)⟩

/-- The inverse map is `b/f(s) ↦ b/s`. -/
theorem solution_symm_apply_mk (S : Submonoid A) (b : B) (s : S) :
    (solutionLinearEquiv S).symm
        (IsLocalization.mk' (Localization (M := B) (imageSubmonoid S)) b
          (⟨algebraMap A B s, Submonoid.mem_map_of_mem _ s.2⟩ : imageSubmonoid S)) =
      LocalizedModule.mk b s := by
  rw [LinearEquiv.symm_apply_eq, solution_apply_mk]

/-- **Surjectivity** in the form used in the book's proof: every element of `T⁻¹B` is `b/f(s)`
for some `b : B`, `s ∈ S`. -/
theorem exists_mk_eq (S : Submonoid A) (x : Localization (M := B) (imageSubmonoid S)) :
    ∃ (b : B) (s : S), solutionLinearEquiv S (LocalizedModule.mk b s) = x := by
  obtain ⟨b, y, hy⟩ :=
    IsLocalization.exists_mk'_eq (R := B) (M := imageSubmonoid S)
      (S := Localization (M := B) (imageSubmonoid S)) x
  obtain ⟨s, hs, hfs⟩ := Submonoid.mem_map.mp y.2
  refine ⟨b, ⟨s, hs⟩, ?_⟩
  rw [solution_apply_mk, ← hy]
  congr 1
  exact Subtype.ext hfs

end AtiyahMcdonald69.Ex_3_4

/-! ### The exercise for an arbitrary ring homomorphism `f : A →+* B` -/

namespace AtiyahMcdonald69.Ex_3_4

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Under `f.toAlgebra`, the submonoid `Algebra.algebraMapSubmonoid B S` is the image
`T = f(S)` occurring in the exercise. -/
theorem imageSubmonoid_eq_map (f : A →+* B) (S : Submonoid A) :
    letI := f.toAlgebra
    Algebra.algebraMapSubmonoid B S = S.map f := rfl

/-- **The exercise in the form stated in the book**: for an arbitrary ring homomorphism
`f : A →+* B` and multiplicatively closed `S ⊆ A`, the localizations `S⁻¹B` and `T⁻¹B` of
`B` (as an `A`-module, resp. as a ring), where `T = f(S)`, are isomorphic as `S⁻¹A`-modules.

Here `f` enters through the `A`-algebra structure `f.toAlgebra` on `B`, and
`Algebra.algebraMapSubmonoid B S = S.map f = f(S)` is `imageSubmonoid_eq_map`. -/
theorem solution_of_ringHom (f : A →+* B) (S : Submonoid A) :
    letI := f.toAlgebra
    Nonempty (LocalizedModule S B ≃ₗ[Localization (M := A) S]
      Localization (M := B) (Algebra.algebraMapSubmonoid B S)) :=
  ⟨@solutionLinearEquiv A B _ _ f.toAlgebra S⟩

end AtiyahMcdonald69.Ex_3_4

/-! ### Axiom checks on the main exports -/

#print axioms AtiyahMcdonald69.Ex_3_4.solution
#print axioms AtiyahMcdonald69.Ex_3_4.solutionLinearEquiv
#print axioms AtiyahMcdonald69.Ex_3_4.solution_apply_mk
#print axioms AtiyahMcdonald69.Ex_3_4.solution_symm_apply_mk
#print axioms AtiyahMcdonald69.Ex_3_4.solution_apply_mk_one
#print axioms AtiyahMcdonald69.Ex_3_4.map_eq_of_mk_eq
#print axioms AtiyahMcdonald69.Ex_3_4.mk_eq_zero_of_map_eq_zero
#print axioms AtiyahMcdonald69.Ex_3_4.exists_mk_eq
#print axioms AtiyahMcdonald69.Ex_3_4.solutionAlgEquiv
#print axioms AtiyahMcdonald69.Ex_3_4.algebraMapLocalization_eq
#print axioms AtiyahMcdonald69.Ex_3_4.solution_of_ringHom
#print axioms AtiyahMcdonald69.Ex_3_4.imageSubmonoid_eq_map
