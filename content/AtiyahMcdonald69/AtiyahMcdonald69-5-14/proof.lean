import Mathlib

/-!
# Atiyah–Macdonald, Exercise 5.14

*Statement* (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 5, Exercise 14):

> Let `A` be an integrally closed domain, `K` its field of fractions and `L` a finite normal
> separable extension of `K`.  Let `G` be the Galois group of `L` over `K` and let `B` be the
> integral closure of `A` in `L`.  Show that `σ(B) = B` for all `σ ∈ G`, and that `A = B^G`.

Formal rendering.  `A` is a commutative ring which is a domain (`IsDomain A`) and integrally
closed (`IsIntegrallyClosed A`); `K` is a field with `IsFractionRing A K`, i.e. `K = Frac A`;
`L` is a field with `Algebra K L`, finite dimensional over `K` (`FiniteDimensional K L`),
normal and separable (`IsGalois K L`).  `G` is `Gal(L/K) = L ≃ₐ[K] L`, and `B` is
`integralClosure A L`.

We prove:

* `isIntegral_apply_galois` : a `K`-algebra automorphism of `L` preserves integrality over `A`;
* `image_integralClosure` : `σ(B) = B` for every `σ ∈ G` (as subsets of `L`);
* `map_integralClosure_eq` : the same statement for subalgebras, `B.map σ = B`;
* `galoisAction`, `galoisActionHom` : every `σ ∈ G` restricts to an `A`-algebra automorphism of
  `B`, and this is a group homomorphism `G →* (B ≃ₐ[A] B)`;
* `mem_integralClosure_fixed_iff`, `range_algebraMap_eq_fixed` : `A = B^G`;
* `solution` : the conjunction of the two assertions of the exercise;
* `range_algebraMap_eq_fixed_of_field` : for a field `A = K` the exercise reduces to the
  fundamental theorem of Galois theory `L^G = K` (a nontriviality check on the hypotheses).
-/

namespace AtiyahMcdonald69.Ex_5_14

section
variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- **Exercise 5.14, first assertion, elementwise form.**
A `K`-algebra automorphism `σ` of `L` preserves integrality over `A`: it fixes `K` pointwise,
hence is an `A`-algebra homomorphism, and integral elements are mapped to integral elements. -/
theorem isIntegral_apply_galois (σ : L ≃ₐ[K] L) {b : L} (hb : IsIntegral A b) :
    IsIntegral A (σ b) :=
  IsIntegral.map (A := K) (R := A) (σ : L →ₐ[K] L) hb

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- **Exercise 5.14, first assertion.**  `σ(B) = B` for every `σ` in the Galois group `G`.

`⊆`: `σ` carries integral elements to integral elements.  `⊇`: if `b ∈ B` then `b = σ(σ⁻¹ b)`
and `σ⁻¹ b ∈ B`, by the same argument applied to `σ⁻¹`. -/
theorem image_integralClosure (σ : L ≃ₐ[K] L) :
    σ '' (integralClosure A L : Set L) = integralClosure A L := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact isIntegral_apply_galois A K L σ hb
  · intro b hb
    exact ⟨σ.symm b, isIntegral_apply_galois A K L σ.symm hb, σ.apply_symm_apply b⟩

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- **Exercise 5.14, first assertion, subalgebra form.**  `σ` maps the subalgebra `B` of `L`
onto itself. -/
theorem map_integralClosure_eq (σ : L ≃ₐ[K] L) :
    (integralClosure A L).map ((σ.restrictScalars A).toAlgHom) = integralClosure A L := by
  ext x
  simp only [Subalgebra.mem_map, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_restrictScalars]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact isIntegral_apply_galois A K L σ hy
  · intro hx
    exact ⟨σ.symm x, isIntegral_apply_galois A K L σ.symm hx, σ.apply_symm_apply x⟩

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- **Exercise 5.14, first assertion, automorphism form.**  Every `σ` in the Galois group
restricts to an `A`-algebra automorphism of the integral closure `B` of `A` in `L`. -/
noncomputable def galoisAction (σ : L ≃ₐ[K] L) :
    integralClosure A L ≃ₐ[A] integralClosure A L where
  toFun b := ⟨σ b, isIntegral_apply_galois A K L σ b.2⟩
  invFun b := ⟨σ.symm b, isIntegral_apply_galois A K L σ.symm b.2⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_mul' b c := by ext; simp
  map_add' b c := by ext; simp
  commutes' a := by
    apply Subtype.ext
    exact show σ (algebraMap A L a) = algebraMap A L a from by
      rw [IsScalarTower.algebraMap_apply A K L]
      exact σ.commutes (algebraMap A K a)

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The induced action of the Galois group `G` on `B` is a group homomorphism. -/
noncomputable def galoisActionHom :
    Gal(L/K) →* (integralClosure A L ≃ₐ[A] integralClosure A L) where
  toFun := galoisAction A K L
  map_one' := by ext b; rfl
  map_mul' σ τ := by ext b; rfl

omit [IsDomain A] in
/-- **Exercise 5.14, second assertion, elementwise form.**  An element of `B` fixed by the whole
Galois group lies in `A`: since `L/K` is Galois and finite, `L^G = K`, so the element lies in
`K`, and it is integral over `A`, so it lies in `A` because `A` is integrally closed in `K`.
Conversely every element of `A` is fixed by `G`. -/
theorem mem_integralClosure_fixed_iff (b : L) (hb : IsIntegral A b) :
    (∀ σ : L ≃ₐ[K] L, σ b = b) ↔ ∃ a : A, algebraMap A L a = b := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) b).mpr h
    have hk : IsIntegral A k :=
      (isIntegral_algebraMap_iff (R := A) (A := K) (B := L) (algebraMap K L).injective).mp hb
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := K) hk
    exact ⟨a, by rw [IsScalarTower.algebraMap_apply A K L, ha]⟩
  · rintro ⟨a, rfl⟩ σ
    rw [IsScalarTower.algebraMap_apply A K L]
    exact σ.commutes (algebraMap A K a)

omit [IsDomain A] in
/-- **Exercise 5.14, `A = B^G` as an equality of subsets of `L`.** -/
theorem range_algebraMap_eq_fixed :
    Set.range (algebraMap A L) =
      {b : L | b ∈ integralClosure A L ∧ ∀ σ : L ≃ₐ[K] L, σ b = b} := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨isIntegral_algebraMap, fun σ => by
      rw [IsScalarTower.algebraMap_apply A K L]
      exact σ.commutes (algebraMap A K a)⟩
  · rintro ⟨hb, hfix⟩
    exact (mem_integralClosure_fixed_iff A K L b hb).mp hfix

end

/-- **Atiyah–Macdonald, Exercise 5.14.**  Let `A` be an integrally closed domain, `K` its field
of fractions, `L` a finite normal separable extension of `K`, `G` the Galois group of `L` over
`K`, and `B` the integral closure of `A` in `L`.  Then `σ(B) = B` for all `σ ∈ G`, and
`A = B^G`. -/
theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (∀ σ : L ≃ₐ[K] L, σ '' (integralClosure A L : Set L) = integralClosure A L) ∧
      (Set.range (algebraMap A L) =
        {b : L | b ∈ integralClosure A L ∧ ∀ σ : L ≃ₐ[K] L, σ b = b}) :=
  ⟨image_integralClosure A K L, range_algebraMap_eq_fixed A K L⟩

/-- Nontriviality / consistency check: for a field `A = K` the integral closure `B` of `A` in the
finite Galois extension `L` is all of `L`, and the exercise reduces to the fundamental theorem of
Galois theory: the fixed field of the full Galois group `Gal(L/K)` is `K`. -/
theorem range_algebraMap_eq_fixed_of_field (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Set.range (algebraMap K L) = {b : L | ∀ σ : L ≃ₐ[K] L, σ b = b} := by
  have htop : integralClosure K L = (⊤ : Subalgebra K L) := by
    rw [integralClosure_eq_top_iff]
    infer_instance
  have h := (solution K K L).2
  rw [htop] at h
  simpa using h

end AtiyahMcdonald69.Ex_5_14

#print axioms AtiyahMcdonald69.Ex_5_14.isIntegral_apply_galois
#print axioms AtiyahMcdonald69.Ex_5_14.image_integralClosure
#print axioms AtiyahMcdonald69.Ex_5_14.map_integralClosure_eq
#print axioms AtiyahMcdonald69.Ex_5_14.galoisAction
#print axioms AtiyahMcdonald69.Ex_5_14.galoisActionHom
#print axioms AtiyahMcdonald69.Ex_5_14.mem_integralClosure_fixed_iff
#print axioms AtiyahMcdonald69.Ex_5_14.range_algebraMap_eq_fixed
#print axioms AtiyahMcdonald69.Ex_5_14.solution
#print axioms AtiyahMcdonald69.Ex_5_14.range_algebraMap_eq_fixed_of_field
