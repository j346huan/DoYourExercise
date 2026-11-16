/-
Atiyah–Macdonald (1969), Chapter 3, Exercise 27, all four parts.

Statement (with `f_α : A → B_α` an arbitrary family of `A`-algebras and
`f : A → ⨂_A B_α` the structure map of the tensor product):

  (i)   `f^* (Spec B) = ⋂_α f_α^* (Spec B_α)` for an arbitrary family;
  (ii)  `f^* (Spec (∏_α B_α)) = ⋃_α f_α^* (Spec B_α)` for a finite family;
  (iii) the subsets of `Spec A` of the form `f^*(Spec B)` are the closed sets of a topology
        (the constructible topology), which is finer than the Zariski topology;
  (iv)  `Spec A` is quasi-compact for the constructible topology.

Formalisation notes.
* The tensor product of an arbitrary family of `A`-algebras is realized (as in Chapter 2,
  Exercise 23) as the directed colimit `InfT A B = colim_s ⨂[A] i : ↥s, B i` of its finite
  tensor products `FinT A B s`, with structure map `iotaA : A →+* InfT A B`.  The empty family
  is the empty stage `s = ∅`, where `FinT ∅ = A`, so `Spec A → Spec A` has image `univ`.
* Part (i) reverse inclusion is obtained by showing `p^{ec} = p` for the extension of `p`
  along `iotaA`, using
  `Ideal.comap_map_eq_self_iff_of_isPrime`, plus the "capture at a finite stage" lemma
  `exists_stage_algebraMap_mem`; the existence of the prime of the whole tensor product is then
  produced by Mathlib's `Ideal.comap_map_eq_self_iff_of_isPrime`
  (= `Ideal.exists_le_prime_disjoint` with the complementary multiplicative set).
* In Mathlib the order on topologies is reversed from the usual one: `t ≤ s` means that `t` is
  finer than `s` (see `TopologicalSpace.le_def`).  Hence "the constructible topology is finer
  than the Zariski topology" is `ConstructibleTopology A ≤ ‹TopologicalSpace (PrimeSpectrum A)›`,
  proved in `constructibleTopology_le_zariski`.
-/
import Mathlib

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace AtiyahMcdonald69.Ex_3_27

variable {A : Type*} [CommRing A]

/-! ### 1. A product of linear maps is multilinear -/

/-- The product of a finite family of `A`-linear maps into a commutative `A`-algebra `C`,
`x ↦ ∏ i, g i (x i)`, is `A`-multilinear. -/
noncomputable def prodLinearMultilinear {ι' : Type*} [Fintype ι'] {M : ι' → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    {C : Type*} [CommRing C] [Algebra A C] (g : ∀ i, M i →ₗ[A] C) :
    MultilinearMap A M C where
  toFun x := ∏ i, g i (x i)
  map_update_add' := by
    intro _ m i x y
    have key : ∀ v : M i, (∏ j, g j (Function.update m i v j)) =
        g i v * ∏ j ∈ (Finset.univ.erase i), g j (m j) := by
      intro v
      rw [← Finset.mul_prod_erase (Finset.univ) (fun j => g j (Function.update m i v j))
        (Finset.mem_univ i), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [key (x + y), key x, key y, map_add, add_mul]
  map_update_smul' := by
    intro _ m i c x
    have key : ∀ v : M i, (∏ j, g j (Function.update m i v j)) =
        g i v * ∏ j ∈ (Finset.univ.erase i), g j (m j) := by
      intro v
      rw [← Finset.mul_prod_erase (Finset.univ) (fun j => g j (Function.update m i v j))
        (Finset.mem_univ i), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [key (c • x), key x, map_smul, smul_mul_assoc]

/-! ### 2. Finite tensor products and their directed system -/

section Finite

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

/-- The tensor product over `A` of the finite subfamily indexed by `s`. -/
noncomputable abbrev FinT (s : Finset ι) : Type _ := ⨂[A] i : s, B i

instance (s : Finset ι) : CommRing (FinT (A := A) B s) :=
  inferInstanceAs (CommRing (⨂[A] i : s, B i))

instance (s : Finset ι) : Algebra A (FinT (A := A) B s) :=
  inferInstanceAs (Algebra A (⨂[A] i : s, B i))

/-- The `A`-algebra map `B i → ⨂_{j ∈ s} B j` inserting a single factor. -/
noncomputable abbrev singleIn [DecidableEq ι] {s : Finset ι} (i : s) :
    B i →ₐ[A] FinT (A := A) B s :=
  PiTensorProduct.singleAlgHom (R := A) (A := fun j : s => B j) i

/-- The multilinear map underlying the "insert `1`" transition `⨂_{i∈s} B i → ⨂_{i∈s'} B i`. -/
noncomputable def transML [DecidableEq ι] {s s' : Finset ι} (h : s ⊆ s') :
    MultilinearMap A (fun i : s => B i) (FinT (A := A) B s') :=
  prodLinearMultilinear fun i : s => (singleIn (A := A) B ⟨i.1, h i.2⟩).toLinearMap

variable [DecidableEq ι]

theorem transML_apply {s s' : Finset ι} (h : s ⊆ s') (x : ∀ i : s, B i) :
    transML (A := A) B h x = ∏ i : s, singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ (x i) := rfl

theorem transML_one {s s' : Finset ι} {h : s ⊆ s'} :
    transML (A := A) B h 1 = 1 := by
  rw [transML_apply]
  refine Finset.prod_eq_one (fun i _ => ?_)
  have : (PiTensorProduct.tprod A (1 : ∀ i : s', B i)) = (1 : FinT (A := A) B s') :=
    PiTensorProduct.one_def.symm
  simpa using this

theorem transML_mul {s s' : Finset ι} {h : s ⊆ s'} (x y : ∀ i : s, B i) :
    transML (A := A) B h (x * y) = transML (A := A) B h x * transML (A := A) B h y := by
  rw [transML_apply, transML_apply, transML_apply]
  have h1 : (∏ i : s, singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ ((x * y) i)) =
      ∏ i : s, (singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ (x i) *
        singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ (y i)) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Pi.mul_apply, map_mul]
  rw [h1, Finset.prod_mul_distrib]

/-- The canonical `A`-algebra map `⨂_{i∈s} B i → ⨂_{i∈s'} B i` for `s ⊆ s'`. -/
noncomputable def tmap {s s' : Finset ι} (h : s ⊆ s') : FinT (A := A) B s →ₐ[A] FinT (A := A) B s' :=
  PiTensorProduct.liftAlgHom (transML (A := A) B h) (transML_one (B := B)) (transML_mul (B := B))

theorem tmap_tprod {s s' : Finset ι} (h : s ⊆ s') (x : ∀ i : s, B i) :
    tmap (A := A) B h (PiTensorProduct.tprod A x) =
      ∏ i : s, singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ (x i) := by
  rw [tmap, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod]
  rfl

theorem singleIn_eq_tprod {s : Finset ι} (i : s) (b : B i) :
    singleIn (A := A) B (s := s) i b = PiTensorProduct.tprod A (Pi.mulSingle i b) := rfl

theorem tmap_single {s s' : Finset ι} (h : s ⊆ s') (i : s) :
    (tmap (A := A) B h).comp (singleIn (A := A) B i) =
      singleIn (A := A) B (s := s') ⟨i.1, h i.2⟩ := by
  ext b
  rw [AlgHom.comp_apply, singleIn_eq_tprod, tmap_tprod, Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one]
  · intro hh; exact absurd (Finset.mem_univ i) hh

theorem tmap_refl (s : Finset ι) : tmap (A := A) B (le_refl s) = AlgHom.id A (FinT (A := A) B s) := by
  refine PiTensorProduct.algHom_ext (fun i => ?_)
  rw [tmap_single]
  exact AlgHom.ext fun b => rfl

theorem tmap_trans {s s' s'' : Finset ι} (h₁ : s ⊆ s') (h₂ : s' ⊆ s'') :
    (tmap (A := A) B h₂).comp (tmap (A := A) B h₁) = tmap (A := A) B (h₁.trans h₂) := by
  refine PiTensorProduct.algHom_ext (fun i => ?_)
  rw [AlgHom.comp_assoc, tmap_single, tmap_single, tmap_single]

end Finite

/-! ### 3. The colimit of the finite tensor products -/

section Main

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

theorem tprod_eq_prod_single (s : Finset ι) (f : ∀ j : s, B j) :
    PiTensorProduct.tprod A f = ∏ j : s, singleIn (A := A) B (s := s) j (f j) := by
  have h1 : (∏ j : s, Pi.mulSingle j (f j)) = f := by
    classical
    have h := Finset.noncommProd_mulSingle (M := fun i : ↥s => B ↑i) f
    rwa [Finset.noncommProd_eq_prod] at h
  conv_lhs => rw [← h1]
  rw [PiTensorProduct.tprod_prod]
  exact Finset.prod_congr rfl fun j _ => (singleIn_eq_tprod (A := A) B j (f j)).symm

/-- The transition maps as ring homomorphisms. -/
noncomputable abbrev tmapHom {s s' : Finset ι} (h : s ⊆ s') :
    FinT (A := A) B s →+* FinT (A := A) B s' := (tmap (A := A) B h).toRingHom

instance directedSystem :
    DirectedSystem (FinT (A := A) B) (fun s s' h => tmapHom (A := A) B h) where
  map_self := by
    intro i x
    have h := congrArg (fun f : FinT (A := A) B i →ₐ[A] FinT (A := A) B i => f x)
      (tmap_refl (A := A) B i)
    simpa using h
  map_map := by
    intro k j i hij hjk x
    have h := congrArg (fun f : FinT (A := A) B i →ₐ[A] FinT (A := A) B k => f x)
      (tmap_trans (A := A) B hij hjk)
    simpa [AlgHom.comp_apply] using h

/-- The tensor product over `A` of the whole family, as the directed colimit of the finite
tensor products. -/
noncomputable abbrev InfT : Type _ :=
  Ring.DirectLimit (FinT (A := A) B) (fun s s' h => tmapHom (A := A) B h)

noncomputable instance : CommRing (InfT (A := A) B) :=
  inferInstanceAs (CommRing (Ring.DirectLimit (FinT (A := A) B)
    (fun s s' h => tmapHom (A := A) B h)))

/-- The canonical map from a finite stage to the colimit. -/
noncomputable abbrev iota (s : Finset ι) : FinT (A := A) B s →+* InfT (A := A) B :=
  Ring.DirectLimit.of (FinT (A := A) B) (fun s s' h => tmapHom (A := A) B h) s

/-- The structure map `A → ⨂_A B_α`. -/
noncomputable abbrev iotaA : A →+* InfT (A := A) B :=
  (iota (A := A) B ∅).comp (algebraMap A (FinT (A := A) B ∅))

theorem iotaA_eq (s : Finset ι) :
    (iota (A := A) B s).comp (algebraMap A (FinT (A := A) B s)) = iotaA (A := A) B := by
  ext a
  have h : (tmap (A := A) B (Finset.empty_subset s)) (algebraMap A (FinT (A := A) B ∅) a)
      = algebraMap A (FinT (A := A) B s) a := AlgHom.commutes _ a
  show iota (A := A) B s (algebraMap A (FinT (A := A) B s) a) = iotaA (A := A) B a
  rw [← h]
  change iota (A := A) B s ((tmap (A := A) B (Finset.empty_subset s))
      (algebraMap A (FinT (A := A) B ∅) a))
    = iota (A := A) B ∅ (algebraMap A (FinT (A := A) B ∅) a)
  exact Ring.DirectLimit.of_f (G := FinT (A := A) B)
    (f := fun s s' h => tmapHom (A := A) B h) (Finset.empty_subset s)
    (algebraMap A (FinT (A := A) B ∅) a)

end Main

/-! ### 4. Nontriviality of tensor products over a field -/

theorem injective_algebraMap_of_field {K : Type*} [Field K] {R : Type*} [CommRing R] [Nontrivial R]
    [Algebra K R] : Function.Injective (algebraMap K R) := by
  intro a b hab
  by_contra hne
  have h : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h1 : algebraMap K R (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h2 : algebraMap K R (a - b) * algebraMap K R ((a - b)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h, map_one]
  rw [h1, zero_mul] at h2
  exact zero_ne_one h2

theorem nontrivial_tensor_of_field {K : Type*} [Field K] {X Y : Type*} [CommRing X] [CommRing Y]
    [Algebra K X] [Algebra K Y] [Nontrivial X] [Nontrivial Y] : Nontrivial (X ⊗[K] Y) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
    (A := X) (B := Y) (R := K) injective_algebraMap_of_field
/-! ### 7. Images of spectra and the parts of Exercise 27 that are completed -/

section Images

/-- `f^*(Spec C)`: the image of `Spec C → Spec A` for the structure map of an `A`-algebra `C`. -/
def imageOf (C : Type*) [CommRing C] [Algebra A C] : Set (PrimeSpectrum A) :=
  Set.range (PrimeSpectrum.comap (algebraMap A C))

theorem imageOf_subset_of_algHom {C D : Type*} [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (g : C →ₐ[A] D) :
    imageOf (A := A) D ⊆ imageOf (A := A) C := by
  rintro p ⟨q, rfl⟩
  refine ⟨PrimeSpectrum.comap g.toRingHom q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    show g.toRingHom.comp (algebraMap A C) = algebraMap A D from AlgHom.comp_algebraMap g]

theorem imageOf_congr {C D : Type*} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (e : C ≃ₐ[A] D) : imageOf (A := A) C = imageOf (A := A) D :=
  Set.Subset.antisymm (imageOf_subset_of_algHom e.symm) (imageOf_subset_of_algHom e)

end Images

/-! ### 8. Part i), the inclusion `f^*(Spec B) ⊆ ⋂ f_α^*(Spec B_α)` -/

section PartISubset

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- **Exercise 27 i), the inclusion `⊆`**, for the tensor product of an arbitrary family realised
as the colimit of the finite tensor products: the image of `Spec` of the colimit is contained in the
intersection of the images of the factors. -/
theorem part_i_subset :
    Set.range (PrimeSpectrum.comap (iotaA (A := A) B)) ⊆
      Set.iInter fun i => imageOf (A := A) (B i) := by
  rintro p ⟨Q, rfl⟩
  rw [Set.mem_iInter]
  intro i
  have h1 : PrimeSpectrum.comap (algebraMap A (FinT (A := A) B {i}))
      (PrimeSpectrum.comap (iota (A := A) B {i}) Q) =
      PrimeSpectrum.comap (iotaA (A := A) B) Q := by
    rw [← PrimeSpectrum.comap_comp_apply, iotaA_eq]
  rw [← h1]
  exact imageOf_subset_of_algHom (A := A)
    (singleIn (A := A) B (s := {i}) ⟨i, Finset.mem_singleton_self i⟩)
    ⟨PrimeSpectrum.comap (iota (A := A) B {i}) Q, rfl⟩

end PartISubset

/-! ### 9. Part ii): `f^*(Spec ∏ B_i) = ⋃ f_i^*(Spec B_i)` for a finite family -/

section PartII

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

/-- Evaluation at the `i`-th factor of a product of rings. -/
def piEval (i : ι) : (∀ j, B j) →+* B i where
  toFun x := x i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem piEval_apply (i : ι) (x : ∀ j, B j) : piEval B i x = x i := rfl

theorem piEval_comp_algebraMap (i : ι) :
    (piEval B i).comp (algebraMap A (∀ j, B j)) = algebraMap A (B i) :=
  RingHom.ext fun _ => rfl

theorem piEval_surjective [DecidableEq ι] (i : ι) : Function.Surjective (piEval B i) :=
  fun y => ⟨Pi.single i y, by simp⟩

/-- A prime ideal of a finite product of rings is the contraction of a prime of a single factor. -/
theorem exists_prime_factor [Fintype ι] [DecidableEq ι] (Q : PrimeSpectrum (∀ j, B j)) :
    ∃ (i : ι) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (piEval B i) q = Q := by
  classical
  by_cases hι : Nonempty ι
  swap
  · have hone : (1 : ∀ j, B j) ∈ Q.asIdeal := by
      have h10 : (1 : ∀ j, B j) = 0 := funext fun j => absurd ⟨j⟩ hι
      rw [h10]
      exact Q.asIdeal.zero_mem
    exact absurd (Ideal.ext fun x => ⟨fun _ => Submodule.mem_top, fun _ => by
      simpa using Q.asIdeal.mul_mem_right x hone⟩) Q.isPrime.ne_top
  obtain ⟨i₀, hi₀⟩ : ∃ i, (Pi.single i (1 : B i) : ∀ j, B j) ∉ Q.asIdeal := by
    by_contra h
    have h' : ∀ i, (Pi.single i (1 : B i) : ∀ j, B j) ∈ Q.asIdeal := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have hsum : (∑ i : ι, (Pi.single i (1 : B i) : ∀ j, B j)) = 1 := by
      ext x
      simp [Finset.sum_apply]
    have h1 : (1 : ∀ j, B j) ∈ Q.asIdeal := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ => h' i
    exact Q.isPrime.ne_top (Ideal.ext fun x =>
      ⟨fun _ => Submodule.mem_top, fun _ => by simpa using Q.asIdeal.mul_mem_right x h1⟩)
  have hcomp : (1 - (Pi.single i₀ (1 : B i₀) : ∀ j, B j)) ∈ Q.asIdeal := by
    have hz : (Pi.single i₀ (1 : B i₀) : ∀ j, B j) *
        (1 - (Pi.single i₀ (1 : B i₀) : ∀ j, B j)) = 0 := by
      ext j
      by_cases hj : j = i₀
      · subst hj; simp
      · simp [Pi.mul_apply, Pi.single_apply, hj]
    have hmem : (Pi.single i₀ (1 : B i₀) : ∀ j, B j) *
        (1 - (Pi.single i₀ (1 : B i₀) : ∀ j, B j)) ∈ Q.asIdeal := by
      rw [hz]; exact Q.asIdeal.zero_mem
    rcases Q.isPrime.mem_or_mem hmem with h | h
    · exact absurd h hi₀
    · exact h
  have hker : RingHom.ker (piEval B i₀) ≤ Q.asIdeal := by
      intro x hx
      have hxi : x i₀ = 0 := by simpa using hx
      have hx' : x = x * (1 - (Pi.single i₀ (1 : B i₀) : ∀ j, B j)) := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp [Pi.mul_apply, Pi.single_apply, hxi]
        · simp [Pi.mul_apply, Pi.single_apply, hj]
      rw [hx']
      exact Q.asIdeal.mul_mem_left x hcomp
  refine ⟨i₀, ⟨Ideal.map (piEval B i₀) Q.asIdeal,
    Ideal.map_isPrime_of_surjective (piEval_surjective B i₀) hker⟩, ?_⟩
  rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
  rw [Ideal.comap_map_of_surjective _ (piEval_surjective B i₀) _]
  exact sup_eq_left.mpr hker

/-- **Exercise 27 ii)**: for a finite family of `A`-algebras, the image of `Spec` of the product is
the union of the images of the factors. -/
theorem part_ii [Fintype ι] [DecidableEq ι] :
    imageOf (A := A) (∀ i, B i) = Set.iUnion fun i => imageOf (A := A) (B i) := by
  ext p
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨i, q, hq⟩ := exists_prime_factor B Q
    refine Set.mem_iUnion.mpr ⟨i, q, ?_⟩
    rw [← hQ, ← hq, ← piEval_comp_algebraMap (A := A) B i, PrimeSpectrum.comap_comp]
    rfl
  · intro hp
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hp
    refine ⟨PrimeSpectrum.comap (piEval B i) q, ?_⟩
    rw [← hq, ← piEval_comp_algebraMap (A := A) B i, PrimeSpectrum.comap_comp]
    rfl

end PartII

/-! ### 10. The binary base-change step: `κ ⊗ (X ⊗ Y)` from the two fibres -/

section BaseChange

/-- **Binary base change step**: if the two fibres over `κ` are nontrivial, then so is the fibre of
the tensor product.  (This is the ingredient that would drive the induction over finite families;
what is missing is an insertion isomorphism for `PiTensorProduct`,
`⨂[A] i : ↥(insert a s), B i ≃ₗ[A] (⨂[A] i : ↥s, B i) ⊗[A] B a`.) -/
theorem nontrivial_baseChange_tensor {κ : Type*} [Field κ] [Algebra A κ]
    {X Y : Type*} [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    [Nontrivial (κ ⊗[A] X)] [Nontrivial (κ ⊗[A] Y)] :
    Nontrivial (κ ⊗[A] (X ⊗[A] Y)) := by
  have h : Nontrivial ((κ ⊗[A] X) ⊗[κ] (κ ⊗[A] Y)) :=
    nontrivial_tensor_of_field (K := κ) (X := κ ⊗[A] X) (Y := κ ⊗[A] Y)
  have e : κ ⊗[A] (X ⊗[A] Y) ≃ₗ[κ] (κ ⊗[A] X) ⊗[κ] (κ ⊗[A] Y) :=
    TensorProduct.AlgebraTensorModule.distribBaseChange (R := A) (A := κ) (N := X) (Q := Y)
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  exact ⟨e.symm x, e.symm y, fun hc => hxy (e.symm.injective hc)⟩

end BaseChange

/-! ### 11. The insertion step for the finite tensor products -/

section Insert

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- The `j`-th component of the insertion
`⨂[A] j : ↥(insert a s), B j →ₐ[A] FinT s ⊗[A] B a`: for `j = a` it is `1 ⊗ ·`, and for
`j ∈ s` it is `single_j · ⊗ 1`. -/
noncomputable def insertG (s : Finset ι) (a : ι) (j : ↥(insert a s)) :
    B j →ₗ[A] (FinT (A := A) B s ⊗[A] B a) := by
  by_cases hj : j = (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))
  · subst hj
    exact (Algebra.TensorProduct.includeRight (R := A)
      (A := FinT (A := A) B s) (B := B a)).toLinearMap
  · have hmem : j.1 ∈ s := by
      rcases Finset.mem_insert.mp j.2 with h | h
      · exact absurd (Subtype.ext h) hj
      · exact h
    exact ((TensorProduct.mk A (FinT (A := A) B s) (B a)).flip (1 : B a)).comp
      (singleIn (A := A) B (s := s) ⟨j.1, hmem⟩).toLinearMap

theorem insertG_self (s : Finset ι) (a : ι) :
    insertG (A := A) B s a (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)) =
      (Algebra.TensorProduct.includeRight (R := A)
        (A := FinT (A := A) B s) (B := B a)).toLinearMap := by
  unfold insertG
  exact dif_pos rfl

theorem insertG_neg (s : Finset ι) (a : ι) (j : ↥(insert a s))
    (hj : j ≠ (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))) :
    insertG (A := A) B s a j =
      ((TensorProduct.mk A (FinT (A := A) B s) (B a)).flip (1 : B a)).comp
        (singleIn (A := A) B (s := s) ⟨j.1, by
          rcases Finset.mem_insert.mp j.2 with h | h
          · exact absurd (Subtype.ext h) hj
          · exact h⟩).toLinearMap := by
  unfold insertG
  exact dif_neg hj

theorem insertG_one (s : Finset ι) (a : ι) (j : ↥(insert a s)) :
    insertG (A := A) B s a j 1 = 1 := by
  classical
  by_cases hj : j = (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))
  · subst hj
    simp only [insertG_self, AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
      map_one, Algebra.TensorProduct.one_def]
  · rw [insertG_neg (A := A) B s a j hj]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      AlgHom.toLinearMap_apply, map_one, Algebra.TensorProduct.one_def]

theorem insertG_mul (s : Finset ι) (a : ι) (j : ↥(insert a s)) (b b' : B j) :
    insertG (A := A) B s a j (b * b') =
      insertG (A := A) B s a j b * insertG (A := A) B s a j b' := by
  classical
  by_cases hj : j = (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))
  · subst hj
    simp only [insertG_self, AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
      map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [insertG_neg (A := A) B s a j hj]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      AlgHom.toLinearMap_apply, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The multilinear map underlying the insertion. -/
noncomputable def insertML (s : Finset ι) (a : ι) :
    MultilinearMap A (fun j : ↥(insert a s) => B j) (FinT (A := A) B s ⊗[A] B a) :=
  prodLinearMultilinear (insertG (A := A) B s a)

theorem insertML_apply (s : Finset ι) (a : ι) (x : ∀ j : ↥(insert a s), B j) :
    insertML (A := A) B s a x = ∏ j : ↥(insert a s), insertG (A := A) B s a j (x j) := rfl

theorem insertML_one (s : Finset ι) (a : ι) : insertML (A := A) B s a 1 = 1 := by
  rw [insertML_apply]
  exact Finset.prod_eq_one fun j _ => insertG_one (A := A) B s a j

theorem insertML_mul (s : Finset ι) (a : ι) (x y : ∀ j : ↥(insert a s), B j) :
    insertML (A := A) B s a (x * y) =
      insertML (A := A) B s a x * insertML (A := A) B s a y := by
  rw [insertML_apply, insertML_apply, insertML_apply]
  have h1 : (∏ j : ↥(insert a s), insertG (A := A) B s a j ((x * y) j)) =
      ∏ j : ↥(insert a s), (insertG (A := A) B s a j (x j) *
        insertG (A := A) B s a j (y j)) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Pi.mul_apply, insertG_mul]
  rw [h1, Finset.prod_mul_distrib]

/-- **The insertion map** `⨂[A] j : ↥(insert a s), B j →ₐ[A] FinT s ⊗[A] B a`
(`single_j ↦ single_j ⊗ 1` for `j ∈ s`, `single_a ↦ 1 ⊗ ·`). -/
noncomputable def insertAlgHom (s : Finset ι) (a : ι) :
    FinT (A := A) B (insert a s) →ₐ[A] (FinT (A := A) B s ⊗[A] B a) :=
  PiTensorProduct.liftAlgHom (insertML (A := A) B s a)
    (insertML_one (A := A) B s a) (insertML_mul (A := A) B s a)

theorem insertAlgHom_tprod (s : Finset ι) (a : ι) (x : ∀ j : ↥(insert a s), B j) :
    insertAlgHom (A := A) B s a (PiTensorProduct.tprod A x) =
      ∏ j : ↥(insert a s), insertG (A := A) B s a j (x j) :=
  PiTensorProduct.lift.tprod _

theorem insertAlgHom_single (s : Finset ι) (a : ι) (j : ↥(insert a s)) (b : B j) :
    insertAlgHom (A := A) B s a (singleIn (A := A) B (s := insert a s) j b) =
      insertG (A := A) B s a j b := by
  rw [singleIn_eq_tprod, insertAlgHom_tprod, Finset.prod_eq_single j]
  · rw [Pi.mulSingle_eq_same]
  · intro i _ hij
    rw [Pi.mulSingle_eq_of_ne hij, insertG_one]
  · intro hh; exact absurd (Finset.mem_univ j) hh

end Insert

/-! ### 12. Surjectivity of the insertion map -/

section Surj

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- A product of members of the range of the insertion map lies in the range. -/
theorem prod_mem_range_insert (s : Finset ι) (a : ι) (t : Finset ↥s)
    (g : ↥s → (FinT (A := A) B s ⊗[A] B a))
    (hg : ∀ i ∈ t, g i ∈ Set.range (insertAlgHom (A := A) B s a)) :
    (∏ i ∈ t, g i) ∈ Set.range (insertAlgHom (A := A) B s a) := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, map_one _⟩
  | insert i t hit ih =>
      rw [Finset.prod_insert hit]
      obtain ⟨y₁, hy₁⟩ := hg i (Finset.mem_insert_self i t)
      obtain ⟨y₂, hy₂⟩ := ih fun k hk => hg k (Finset.mem_insert_of_mem hk)
      exact ⟨y₁ * y₂, by rw [map_mul, hy₁, hy₂]⟩

theorem range_algMap (s : Finset ι) (a : ι) (r : A) :
    algebraMap A (FinT (A := A) B s ⊗[A] B a) r ∈ Set.range (insertAlgHom (A := A) B s a) :=
  ⟨algebraMap A (FinT (A := A) B (insert a s)) r, AlgHom.commutes _ r⟩

theorem single_tmul_one_mem (s : Finset ι) (a : ι) (ha : a ∉ s) (i : ↥s) (b : B i) :
    (singleIn (A := A) B (s := s) i b) ⊗ₜ[A] (1 : B a) ∈
      Set.range (insertAlgHom (A := A) B s a) := by
  refine ⟨singleIn (A := A) B (s := insert a s) ⟨i.1, Finset.mem_insert_of_mem i.2⟩ b, ?_⟩
  rw [insertAlgHom_single, insertG_neg (A := A) B s a _ (by
    simp only [ne_eq, Subtype.mk.injEq]
    exact fun h => ha (h ▸ i.2))]
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    AlgHom.toLinearMap_apply]

theorem tmul_one_mem (s : Finset ι) (a : ι) (ha : a ∉ s) (t : FinT (A := A) B s) :
    t ⊗ₜ[A] (1 : B a) ∈ Set.range (insertAlgHom (A := A) B s a) := by
  classical
  have hinc : ∀ u : FinT (A := A) B s,
      u ⊗ₜ[A] (1 : B a) = Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := FinT (A := A) B s) (B := B a) u := fun u => rfl
  rw [hinc]
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      have h2 : Algebra.TensorProduct.includeLeft (R := A) (S := A)
          (A := FinT (A := A) B s) (B := B a)
          (r • PiTensorProduct.tprod A f) =
          algebraMap A (FinT (A := A) B s ⊗[A] B a) r *
            Algebra.TensorProduct.includeLeft (R := A) (S := A)
              (A := FinT (A := A) B s) (B := B a) (PiTensorProduct.tprod A f) := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      have h3 : Algebra.TensorProduct.includeLeft (R := A) (S := A)
          (A := FinT (A := A) B s) (B := B a) (PiTensorProduct.tprod A f) =
          ∏ i : ↥s, Algebra.TensorProduct.includeLeft (R := A) (S := A)
            (A := FinT (A := A) B s) (B := B a)
            (singleIn (A := A) B (s := s) i (f i)) := by
        rw [tprod_eq_prod_single, map_prod]
      rw [h2, h3]
      obtain ⟨y₁, hy₁⟩ := range_algMap (A := A) B s a r
      obtain ⟨y₂, hy₂⟩ := prod_mem_range_insert (A := A) B s a Finset.univ _ fun i _ =>
        single_tmul_one_mem (A := A) B s a ha i (f i)
      exact ⟨y₁ * y₂, by
        rw [map_mul, hy₁, hy₂]
        simp only [Algebra.TensorProduct.includeLeft_apply]⟩
  | add x y hx hy =>
      have h4 : Algebra.TensorProduct.includeLeft (R := A) (S := A)
          (A := FinT (A := A) B s) (B := B a) (x + y) =
          Algebra.TensorProduct.includeLeft (R := A) (S := A)
            (A := FinT (A := A) B s) (B := B a) x +
          Algebra.TensorProduct.includeLeft (R := A) (S := A)
            (A := FinT (A := A) B s) (B := B a) y := map_add _ _ _
      rw [h4]
      obtain ⟨y₁, hy₁⟩ := hx
      obtain ⟨y₂, hy₂⟩ := hy
      exact ⟨y₁ + y₂, by rw [map_add, hy₁, hy₂]⟩

/-- The insertion map is surjective. -/
theorem insertAlgHom_surjective (s : Finset ι) (a : ι) (ha : a ∉ s) :
    Function.Surjective (insertAlgHom (A := A) B s a) := by
  classical
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul t b =>
      have h5 : t ⊗ₜ[A] b = (t ⊗ₜ[A] (1 : B a)) * (1 ⊗ₜ[A] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h5]
      obtain ⟨y₁, hy₁⟩ := tmul_one_mem (A := A) B s a ha t
      obtain ⟨y₂, hy₂⟩ : ∃ y, insertAlgHom (A := A) B s a y =
          (1 : FinT (A := A) B s) ⊗ₜ[A] b :=
        ⟨singleIn (A := A) B (s := insert a s) ⟨a, Finset.mem_insert_self a s⟩ b,
          by rw [insertAlgHom_single, insertG_self, AlgHom.toLinearMap_apply,
            Algebra.TensorProduct.includeRight_apply]⟩
      exact ⟨y₁ * y₂, by rw [map_mul, hy₁, hy₂]⟩
  | add x y hx hy =>
      obtain ⟨a₁, ha₁⟩ := hx
      obtain ⟨a₂, ha₂⟩ := hy
      exact ⟨a₁ + a₂, by rw [map_add, ha₁, ha₂]⟩

end Surj

/-! ### 13. The finite-stage fibre lemma -/

section FiniteFibre

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- The insertion step for fibres: if the fibres of the two parts are nontrivial, so is the fibre
of the tensor product over `insert a s`. -/
theorem nontrivial_fibre_insert {κ : Type*} [Field κ] [Algebra A κ]
    (s : Finset ι) (a : ι) (ha : a ∉ s)
    (hs : Nontrivial (κ ⊗[A] FinT (A := A) B s)) (hb : Nontrivial (κ ⊗[A] B a)) :
    Nontrivial (κ ⊗[A] FinT (A := A) B (insert a s)) := by
  classical
  have hmap : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id A κ) (insertAlgHom (A := A) B s a)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c z =>
        obtain ⟨y, hy⟩ := insertAlgHom_surjective (A := A) B s a ha z
        exact ⟨c ⊗ₜ[A] y, by rw [Algebra.TensorProduct.map_tmul, hy, AlgHom.id_apply]⟩
    | add x y hx hy =>
        obtain ⟨a₁, ha₁⟩ := hx
        obtain ⟨a₂, ha₂⟩ := hy
        exact ⟨a₁ + a₂, by rw [map_add, ha₁, ha₂]⟩
  have hnt : Nontrivial (κ ⊗[A] (FinT (A := A) B s ⊗[A] B a)) := by
    obtain ⟨x, y, hxy⟩ := (nontrivial_tensor_of_field (K := κ)
      (X := κ ⊗[A] FinT (A := A) B s) (Y := κ ⊗[A] B a)).exists_pair_ne
    have e := (TensorProduct.AlgebraTensorModule.distribBaseChange (R := A) (A := κ)
      (N := FinT (A := A) B s) (Q := B a)).toEquiv
    exact ⟨e.symm x, e.symm y, fun hc => hxy (e.symm.injective hc)⟩
  exact Function.Surjective.nontrivial hmap

/-- **The finite-stage fibre lemma**: if the fibre over `p` of every factor is nontrivial, then so
is the fibre over `p` of the finite tensor product. -/
theorem nontrivial_fibre_finT (p : PrimeSpectrum A) (s : Finset ι)
    (h : ∀ i ∈ s, Nontrivial (p.asIdeal.ResidueField ⊗[A] B i)) :
    Nontrivial (p.asIdeal.ResidueField ⊗[A] FinT (A := A) B s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      haveI : IsEmpty ↥(∅ : Finset ι) := ⟨fun x => absurd x.2 (Finset.notMem_empty _)⟩
      have h1 : Nontrivial (p.asIdeal.ResidueField ⊗[A] A) :=
        (TensorProduct.rid A p.asIdeal.ResidueField).toEquiv.nontrivial
      have e : p.asIdeal.ResidueField ⊗[A] FinT (A := A) B ∅ ≃ₗ[A]
          (p.asIdeal.ResidueField ⊗[A] A) :=
        TensorProduct.congr (LinearEquiv.refl A _) (PiTensorProduct.isEmptyEquiv ↥(∅ : Finset ι))
      obtain ⟨x, y, hxy⟩ := h1.exists_pair_ne
      exact ⟨e.symm x, e.symm y, fun hc => hxy (e.symm.injective hc)⟩
  | insert a s ha ih =>
      exact nontrivial_fibre_insert (A := A) B s a ha
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s))

/-- **Exercise 27 i) for a finite family**: `p` lies in the image of `Spec` of the finite tensor
product iff it lies in the image for every factor. -/
theorem mem_range_finT_iff (p : PrimeSpectrum A) (s : Finset ι) :
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (FinT (A := A) B s))) ↔
      ∀ i ∈ s, p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (B i))) := by
  classical
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) p (S := FinT (A := A) B s)]
  constructor
  · intro hp i hi
    have hp' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (FinT (A := A) B s))) :=
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) p
        (S := FinT (A := A) B s)).mp hp
    obtain ⟨Q, hQ⟩ := hp'
    refine ⟨PrimeSpectrum.comap (singleIn (A := A) B (s := s) ⟨i, hi⟩).toRingHom Q, ?_⟩
    rw [← hQ, ← PrimeSpectrum.comap_comp_apply,
      show (singleIn (A := A) B (s := s) ⟨i, hi⟩).toRingHom.comp (algebraMap A (B i)) =
        algebraMap A (FinT (A := A) B s) from
        AlgHom.comp_algebraMap (singleIn (A := A) B (s := s) ⟨i, hi⟩)]
  · intro h
    exact nontrivial_fibre_finT (A := A) B p s fun i hi =>
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) p (S := B i)).mpr (h i hi)

end FiniteFibre


/-! ### 14. The `A`-algebra structure on the infinite tensor product -/

section InfAlgebra

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- The structure map `A → ⨂_A B_α` of the whole tensor product. -/
noncomputable instance instAlgebraInfT : Algebra A (InfT (A := A) B) :=
  (iotaA (A := A) B).toAlgebra

theorem algebraMap_infT :
    algebraMap A (InfT (A := A) B) = iotaA (A := A) B :=
  RingHom.algebraMap_toAlgebra _

/-- The compatibility of the colimit maps with the transition maps. -/
theorem iota_tmap {s s' : Finset ι} (h : s ⊆ s') (x : FinT (A := A) B s) :
    iota (A := A) B s' (tmap (A := A) B h x) = iota (A := A) B s x :=
  Ring.DirectLimit.of_f h x

end InfAlgebra

/-! ### 15. The image of an ideal in the finite stages -/

section StageIdeal

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- The image of an ideal `I` of `A` in the finite tensor product over `s`. -/
noncomputable def stageIdeal (I : Ideal A) (s : Finset ι) : Ideal (FinT (A := A) B s) :=
  Ideal.map (algebraMap A (FinT (A := A) B s)) I

/-- The transition maps of the system carry the stage ideal over `s` into the stage ideal over
`s'`. -/
theorem map_tmap_stageIdeal_le {I : Ideal A} {s s' : Finset ι} (h : s ⊆ s') :
    Ideal.map (tmap (A := A) B h).toRingHom (stageIdeal (A := A) B I s) ≤
      stageIdeal (A := A) B I s' := by
  rw [stageIdeal, stageIdeal, Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  change (tmap (A := A) B h) (algebraMap A (FinT (A := A) B s) a) ∈
    stageIdeal (A := A) B I s'
  rw [AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ ha

/-- Every element of `Ideal.map iotaA I` is represented, at some finite stage, by an element of the
corresponding stage ideal. -/
theorem exists_stage_of_mem_map_iotaA (I : Ideal A) :
    ∀ y ∈ Ideal.map (iotaA (A := A) B) I,
      ∃ (s : Finset ι) (y' : FinT (A := A) B s),
        y = iota (A := A) B s y' ∧ y' ∈ stageIdeal (A := A) B I s := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact ⟨∅, algebraMap A (FinT (A := A) B ∅) a,
        (RingHom.congr_fun (iotaA_eq (A := A) B ∅) a).symm, Ideal.mem_map_of_mem _ ha⟩
  | zero => exact ⟨∅, 0, (map_zero _).symm, Ideal.zero_mem _⟩
  | add y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      obtain ⟨s₁, y₁', rfl, h₁⟩ := ih₁
      obtain ⟨s₂, y₂', rfl, h₂⟩ := ih₂
      refine ⟨s₁ ∪ s₂, tmap (A := A) B (Finset.subset_union_left) y₁' +
        tmap (A := A) B (Finset.subset_union_right) y₂', ?_, ?_⟩
      · rw [map_add, iota_tmap, iota_tmap]
      · exact Ideal.add_mem _ (map_tmap_stageIdeal_le (A := A) B Finset.subset_union_left
          (Ideal.mem_map_of_mem _ h₁)) (map_tmap_stageIdeal_le (A := A) B
          Finset.subset_union_right (Ideal.mem_map_of_mem _ h₂))
  | smul a y hy ih =>
      obtain ⟨t, a', rfl⟩ := Ring.DirectLimit.exists_of a
      obtain ⟨s, y', rfl, h'⟩ := ih
      refine ⟨s ∪ t, tmap (A := A) B (Finset.subset_union_right) a' *
        tmap (A := A) B (Finset.subset_union_left) y', ?_, ?_⟩
      · rw [smul_eq_mul, map_mul, iota_tmap, iota_tmap]
      · exact Ideal.mul_mem_left _ _ (map_tmap_stageIdeal_le (A := A) B Finset.subset_union_left
          (Ideal.mem_map_of_mem _ h'))

/-- Reflection of the membership of `iotaA x` in the extension of `I` to a finite stage. -/
theorem exists_stage_algebraMap_mem {I : Ideal A} {x : A}
    (h : iotaA (A := A) B x ∈ Ideal.map (iotaA (A := A) B) I) :
    ∃ s : Finset ι, algebraMap A (FinT (A := A) B s) x ∈ stageIdeal (A := A) B I s := by
  obtain ⟨s, y', heq, hy'⟩ := exists_stage_of_mem_map_iotaA (A := A) B I _ h
  have h1 : iota (A := A) B s (algebraMap A (FinT (A := A) B s) x) = iotaA (A := A) B x :=
    RingHom.congr_fun (iotaA_eq (A := A) B s) x
  have hz : iota (A := A) B s (algebraMap A (FinT (A := A) B s) x - y') = 0 := by
    rw [map_sub, h1, heq, sub_self]
  obtain ⟨j, hij, hzero⟩ := Ring.DirectLimit.of.zero_exact
    (G := FinT (A := A) B) (f' := fun s s' h => tmapHom (A := A) B h) hz
  refine ⟨j, ?_⟩
  have hmem : tmap (A := A) B hij y' ∈ stageIdeal (A := A) B I j :=
    map_tmap_stageIdeal_le (A := A) B hij (Ideal.mem_map_of_mem _ hy')
  have heq2 : tmap (A := A) B hij (algebraMap A (FinT (A := A) B s) x) =
      tmap (A := A) B hij y' := by
    have := hzero
    rwa [map_sub, sub_eq_zero] at this
  rw [AlgHom.commutes] at heq2
  rw [heq2]
  exact hmem

end StageIdeal

/-! ### 16. Part i): the image of `Spec` of the whole tensor product -/

section PartIFull

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- The contraction of the extension of `p` to the whole tensor product is `p`, provided `p` lies
in the image of every factor. -/
theorem comap_map_iotaA_eq_of_mem (p : PrimeSpectrum A)
    (hp : ∀ i, p ∈ imageOf (A := A) (B i)) :
    Ideal.comap (iotaA (A := A) B) (Ideal.map (iotaA (A := A) B) p.asIdeal) = p.asIdeal := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_stage_algebraMap_mem (A := A) B (I := p.asIdeal) hx
    have hp' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (FinT (A := A) B s))) :=
      (mem_range_finT_iff (A := A) B p s).mpr fun i _ => hp i
    obtain ⟨Q, hQ⟩ := hp'
    have hQ' : Ideal.comap (algebraMap A (FinT (A := A) B s)) Q.asIdeal = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hQ
    have hle : stageIdeal (A := A) B p.asIdeal s ≤ Q.asIdeal := by
      rw [stageIdeal, Ideal.map_le_iff_le_comap, hQ']
    exact hQ' ▸ hle hs
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

/-- **Exercise 27 i)**, full statement: the image of `Spec` of the tensor product of an arbitrary
family of `A`-algebras is the intersection of the images of the factors. -/
theorem part_i (p : PrimeSpectrum A) :
    p ∈ imageOf (A := A) (InfT (A := A) B) ↔ ∀ i, p ∈ imageOf (A := A) (B i) := by
  constructor
  · intro hp
    have hp' : p ∈ Set.range (PrimeSpectrum.comap (iotaA (A := A) B)) := by
      rw [← algebraMap_infT]; exact hp
    exact fun i => Set.mem_iInter.mp (part_i_subset (A := A) B hp') i
  · intro hp
    rw [imageOf, algebraMap_infT, PrimeSpectrum.mem_range_comap_iff]
    exact comap_map_iotaA_eq_of_mem (A := A) B p hp

end PartIFull

/-! ### 17. The constructible topology on `Spec A` -/

universe u

set_option warn.classDefReducibility false

section Constructible

/-- For two `A`-algebras `C`, `D`, the image of `Spec (C × D)` is the union of the images. -/
theorem imageOf_prod (A : Type u) [CommRing A] (C D : Type u) [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] :
    imageOf (A := A) (C × D) = imageOf (A := A) C ∪ imageOf (A := A) D := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro p ⟨Q, hQ⟩
    have hmem : ((1 : C), (0 : D)) * ((0 : C), (1 : D)) ∈ Q.asIdeal := by
      rw [show ((1 : C), (0 : D)) * ((0 : C), (1 : D)) = (0 : C × D) by simp]
      exact Q.asIdeal.zero_mem
    have key : ∀ {e : C × D}, e ∈ Q.asIdeal → RingHom.ker (AlgHom.snd A C D).toRingHom ≤ Q.asIdeal →
        ∃ q : PrimeSpectrum D, PrimeSpectrum.comap (AlgHom.snd A C D).toRingHom q = Q := by
      intro e he hker
      refine ⟨⟨Q.asIdeal.map (AlgHom.snd A C D).toRingHom,
        Ideal.map_isPrime_of_surjective (f := (AlgHom.snd A C D).toRingHom)
          (fun y => ⟨(0, y), rfl⟩) hker⟩, ?_⟩
      rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
      rw [Ideal.comap_map_of_surjective (f := (AlgHom.snd A C D).toRingHom)
        (fun y => ⟨(0, y), rfl⟩), sup_eq_left]
      exact hker
    have key' : ∀ {e : C × D}, e ∈ Q.asIdeal → RingHom.ker (AlgHom.fst A C D).toRingHom ≤ Q.asIdeal →
        ∃ q : PrimeSpectrum C, PrimeSpectrum.comap (AlgHom.fst A C D).toRingHom q = Q := by
      intro e he hker
      refine ⟨⟨Q.asIdeal.map (AlgHom.fst A C D).toRingHom,
        Ideal.map_isPrime_of_surjective (f := (AlgHom.fst A C D).toRingHom)
          (fun y => ⟨(y, 0), rfl⟩) hker⟩, ?_⟩
      rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
      rw [Ideal.comap_map_of_surjective (f := (AlgHom.fst A C D).toRingHom)
        (fun y => ⟨(y, 0), rfl⟩), sup_eq_left]
      exact hker
    rcases Q.isPrime.mem_or_mem hmem with h | h
    · have hker : RingHom.ker (AlgHom.snd A C D).toRingHom ≤ Q.asIdeal := by
        intro x hx
        have hx2 : x.2 = 0 := hx
        have hx' : x = ((1 : C), (0 : D)) * x := by ext <;> simp [hx2]
        rw [hx']
        exact Ideal.mul_mem_right (b := x) (I := Q.asIdeal) h
      obtain ⟨q, hq⟩ := key h hker
      refine Or.inr ⟨q, ?_⟩
      rw [← hQ, ← hq, ← PrimeSpectrum.comap_comp_apply (algebraMap A (C × D))
        (AlgHom.snd A C D).toRingHom q]
      exact (congrArg (fun f : A →+* D => PrimeSpectrum.comap f q)
        (AlgHom.comp_algebraMap (AlgHom.snd A C D))).symm
    · have hker : RingHom.ker (AlgHom.fst A C D).toRingHom ≤ Q.asIdeal := by
        intro x hx
        have hx1 : x.1 = 0 := hx
        have hx' : x = ((0 : C), (1 : D)) * x := by ext <;> simp [hx1]
        rw [hx']
        exact Ideal.mul_mem_right (b := x) (I := Q.asIdeal) h
      obtain ⟨q, hq⟩ := key' h hker
      refine Or.inl ⟨q, ?_⟩
      rw [← hQ, ← hq, ← PrimeSpectrum.comap_comp_apply (algebraMap A (C × D))
        (AlgHom.fst A C D).toRingHom q]
      exact (congrArg (fun f : A →+* C => PrimeSpectrum.comap f q)
        (AlgHom.comp_algebraMap (AlgHom.fst A C D))).symm
  · rintro p (hp | hp)
    · exact imageOf_subset_of_algHom (A := A) (AlgHom.fst A C D) hp
    · exact imageOf_subset_of_algHom (A := A) (AlgHom.snd A C D) hp

/-- The subsets of `Spec A` of the form `f^*(Spec B)` for an `A`-algebra `B`, i.e. the images of
`Spec` of `A`-algebras. -/
def ConstructibleClosed (A : Type u) [CommRing A] : Set (Set (PrimeSpectrum A)) :=
  {S | ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), S = imageOf (A := A) C}

theorem empty_mem_constructibleClosed (A : Type u) [CommRing A] :
    ∅ ∈ ConstructibleClosed A := by
  refine ⟨A ⧸ (⊤ : Ideal A), inferInstance, inferInstance, ?_⟩
  haveI : IsEmpty (PrimeSpectrum (A ⧸ (⊤ : Ideal A))) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr inferInstance
  exact (Set.range_eq_empty _).symm

theorem univ_mem_constructibleClosed (A : Type u) [CommRing A] :
    Set.univ ∈ ConstructibleClosed A := by
  refine ⟨A, inferInstance, inferInstance, ?_⟩
  rw [imageOf, show algebraMap A A = RingHom.id A from rfl, PrimeSpectrum.comap_id]
  exact Set.range_id.symm

/-- The union of two constructible closed sets is constructible closed. -/
theorem union_mem_constructibleClosed (A : Type u) [CommRing A]
    {S T : Set (PrimeSpectrum A)} (hS : S ∈ ConstructibleClosed A)
    (hT : T ∈ ConstructibleClosed A) : S ∪ T ∈ ConstructibleClosed A := by
  obtain ⟨C, hCring, hCalg, rfl⟩ := hS
  obtain ⟨D, hDring, hDalg, rfl⟩ := hT
  letI := hCring
  letI := hCalg
  letI := hDring
  letI := hDalg
  exact ⟨C × D, inferInstance, inferInstance, (imageOf_prod A C D).symm⟩

/-- An arbitrary intersection of constructible closed sets is constructible closed: it is the image
of `Spec` of the tensor product of the corresponding algebras. -/
theorem sInter_mem_constructibleClosed (A : Type u) [CommRing A]
    {T : Set (Set (PrimeSpectrum A))} (hT : T ⊆ ConstructibleClosed A) :
    ⋂₀ T ∈ ConstructibleClosed A := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sInter_empty]
    exact univ_mem_constructibleClosed A
  choose C hCring hCalg hCeq using fun S : T => hT S.2
  letI : DecidableEq T := Classical.decEq T
  letI : ∀ S : T, CommRing (C S) := hCring
  letI : ∀ S : T, Algebra A (C S) := hCalg
  have h1 : ⋂₀ T = imageOf (A := A) (InfT (A := A) C) := by
    rw [Set.sInter_eq_iInter, Set.iInter_congr (fun S : T => hCeq S)]
    ext p
    rw [Set.mem_iInter]
    exact (part_i (A := A) C p).symm
  exact ⟨InfT (A := A) C, inferInstance, inferInstance, h1⟩

/-- **Exercise 27 iii)**: the constructible closed sets are the closed sets of a topology. -/
noncomputable def ConstructibleTopology (A : Type u) [CommRing A] :
    TopologicalSpace (PrimeSpectrum A) where
  IsOpen X := Xᶜ ∈ ConstructibleClosed A
  isOpen_univ := by
    show Set.univᶜ ∈ ConstructibleClosed A
    rw [Set.compl_univ]
    exact empty_mem_constructibleClosed A
  isOpen_inter s t hs ht := by
    show (s ∩ t)ᶜ ∈ ConstructibleClosed A
    rw [Set.compl_inter]
    exact union_mem_constructibleClosed A hs ht
  isOpen_sUnion S hS := by
    show (⋃₀ S)ᶜ ∈ ConstructibleClosed A
    rw [Set.compl_sUnion]
    exact sInter_mem_constructibleClosed A (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht)

theorem isClosed_constructibleTopology {A : Type u} [CommRing A]
    {s : Set (PrimeSpectrum A)} :
    @IsClosed (PrimeSpectrum A) (ConstructibleTopology A) s ↔ s ∈ ConstructibleClosed A := by
  constructor
  · intro h
    have h1 : sᶜᶜ ∈ ConstructibleClosed A := h.isOpen_compl
    rwa [compl_compl] at h1
  · intro h
    exact @IsClosed.mk (PrimeSpectrum A) (ConstructibleTopology A) s (by
      show sᶜᶜ ∈ ConstructibleClosed A
      rwa [compl_compl])

/-- Every Zariski closed set is constructibly closed. -/
theorem zeroLocus_mem_constructibleClosed (A : Type u) [CommRing A] (I : Ideal A) :
    PrimeSpectrum.zeroLocus (I : Set A) ∈ ConstructibleClosed A := by
  classical
  refine ⟨A ⧸ I, inferInstance, inferInstance, ?_⟩
  ext p
  rw [imageOf, Set.mem_range, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hp
    have hker : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (A ⧸ I)) ≤ p.asIdeal := by
      intro a ha
      rw [show a ∈ Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (A ⧸ I)) ↔
        Ideal.Quotient.mk I a ∈ (⊥ : Ideal (A ⧸ I)) from Iff.rfl, Ideal.mem_bot,
        Ideal.Quotient.eq_zero_iff_mem] at ha
      exact hp ha
    have hkey : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) p.asIdeal) =
        p.asIdeal := by
      rw [Ideal.comap_map_of_surjective (f := Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
    obtain ⟨q, hqprime, hqcomap⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime (f := Ideal.Quotient.mk I) p.asIdeal).mp hkey
    refine ⟨⟨q, hqprime⟩, ?_⟩
    rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal,
      show algebraMap A (A ⧸ I) = Ideal.Quotient.mk I from Ideal.Quotient.algebraMap_eq I]
    exact hqcomap
  · rintro ⟨q, hq⟩ a ha
    have hq' : (PrimeSpectrum.comap (algebraMap A (A ⧸ I)) q).asIdeal = p.asIdeal := by rw [hq]
    rw [← hq', PrimeSpectrum.comap_asIdeal]
    change algebraMap A (A ⧸ I) a ∈ q.asIdeal
    rw [show algebraMap A (A ⧸ I) a = Ideal.Quotient.mk I a from by
          rw [Ideal.Quotient.algebraMap_eq],
      Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.asIdeal.zero_mem

/-- Every set closed in the Zariski topology is closed in the constructible topology (the explicit
form of "the constructible topology is finer than the Zariski topology"). -/
theorem isClosed_constructible_of_isClosed_zariski (A : Type u) [CommRing A]
    {s : Set (PrimeSpectrum A)}
    (hs : @IsClosed (PrimeSpectrum A) (inferInstance : TopologicalSpace (PrimeSpectrum A)) s) :
    @IsClosed (PrimeSpectrum A) (ConstructibleTopology A) s := by
  rw [isClosed_constructibleTopology]
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal s).mp hs
  rw [hI]
  exact zeroLocus_mem_constructibleClosed A I

/-- **Exercise 27 iii)**, the constructible topology is finer than the Zariski topology. -/
theorem constructibleTopology_le_zariski (A : Type u) [CommRing A] :
    ConstructibleTopology A ≤ (inferInstance : TopologicalSpace (PrimeSpectrum A)) := by
  rw [TopologicalSpace.le_def]
  intro U hU
  show Uᶜ ∈ ConstructibleClosed A
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hU.isClosed_compl
  rw [hI]
  exact zeroLocus_mem_constructibleClosed A I

end Constructible

/-! ### 18. Compactness of the constructible topology -/

section Compact

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
variable [DecidableEq ι]

/-- If the whole tensor product is the zero ring, then so is a finite tensor product. -/
theorem exists_finT_subsingleton (h : Subsingleton (InfT (A := A) B)) :
    ∃ s : Finset ι, Subsingleton (FinT (A := A) B s) := by
  have hone : iota (A := A) B ∅ (1 : FinT (A := A) B ∅) = 0 := by
    rw [map_one]
    exact Subsingleton.elim _ _
  obtain ⟨j, hij, hz⟩ := Ring.DirectLimit.of.zero_exact
    (G := FinT (A := A) B) (f' := fun s s' h => tmapHom (A := A) B h) hone
  refine ⟨j, ⟨fun a b => ?_⟩⟩
  have hz' : (tmap (A := A) B hij) 1 = 0 := hz
  have h1 : (1 : FinT (A := A) B j) = 0 := by
    rw [← map_one (tmap (A := A) B hij), hz']
  calc a = a * 1 := (mul_one a).symm
    _ = a * 0 := by rw [h1]
    _ = 0 := mul_zero a
    _ = b * 0 := (mul_zero b).symm
    _ = b * 1 := by rw [← h1]
    _ = b := mul_one b

/-- The image of `Spec` of a finite tensor product is the intersection of the images of its
factors. -/
theorem imageOf_finT_eq_iInter (s : Finset ι) :
    imageOf (A := A) (FinT (A := A) B s) = ⋂ i ∈ s, imageOf (A := A) (B i) := by
  ext p
  simp only [imageOf, Set.mem_iInter, mem_range_finT_iff]

end Compact

section Fip

variable {A : Type u} [CommRing A]

/-- A nontrivial ring has a prime spectrum. -/
theorem nonempty_primeSpectrum (R : Type u) [CommRing R] [Nontrivial R] :
    Nonempty (PrimeSpectrum R) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial R›)
    (PrimeSpectrum.isEmpty_iff_subsingleton.mp h)

/-- **Exercise 27 iv)**, the key step: a family of constructible closed sets with the finite
intersection property has nonempty intersection. -/
theorem inter_nonempty_of_fip {β : Type*} (t : β → Set (PrimeSpectrum A))
    (ht : ∀ i, t i ∈ ConstructibleClosed A)
    (hfin : ∀ u : Finset β, (⋂ i ∈ u, t i).Nonempty) : (⋂ i, t i).Nonempty := by
  classical
  choose C hCring hCalg hCeq using ht
  letI : DecidableEq β := Classical.decEq β
  letI : ∀ i, CommRing (C i) := hCring
  letI : ∀ i, Algebra A (C i) := hCalg
  have hEq : (⋂ i, t i) = imageOf (A := A) (InfT (A := A) C) := by
    rw [Set.iInter_congr (fun i => hCeq i)]
    ext p
    rw [Set.mem_iInter]
    exact (part_i (A := A) C p).symm
  have hnt : Nontrivial (InfT (A := A) C) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    obtain ⟨s, hs⟩ := exists_finT_subsingleton (A := A) C hsub
    have hempty : (⋂ i ∈ s, t i) = ∅ := by
      have h1 : (⋂ i ∈ s, t i) = imageOf (A := A) (FinT (A := A) C s) := by
        rw [imageOf_finT_eq_iInter]
        exact Set.iInter₂_congr fun i _ => hCeq i
      rw [h1]
      haveI : IsEmpty (PrimeSpectrum (FinT (A := A) C s)) :=
        PrimeSpectrum.isEmpty_iff_subsingleton.mpr hs
      exact Set.range_eq_empty _
    exact (hfin s).ne_empty hempty
  haveI : Nontrivial (InfT (A := A) C) := hnt
  obtain ⟨q⟩ := nonempty_primeSpectrum (InfT (A := A) C)
  rw [hEq]
  exact ⟨PrimeSpectrum.comap (algebraMap A (InfT (A := A) C)) q, q, rfl⟩

/-- **Exercise 27 iv)**: `Spec A` is quasi-compact in the constructible topology. -/
theorem part_iv (A : Type u) [CommRing A] :
    @CompactSpace (PrimeSpectrum A) (ConstructibleTopology A) := by
  letI : TopologicalSpace (PrimeSpectrum A) := ConstructibleTopology A
  refine ⟨?_⟩
  rw [isCompact_iff_finite_subfamily_closed]
  intro β t ht hEmpty
  by_contra hcon
  have hfin : ∀ u : Finset β, (⋂ i ∈ u, t i).Nonempty := by
    intro u
    have h : Set.univ ∩ (⋂ i ∈ u, t i) ≠ ∅ := fun hc => hcon ⟨u, hc⟩
    rw [Set.univ_inter] at h
    exact Set.nonempty_iff_ne_empty.mpr h
  have hne := inter_nonempty_of_fip (A := A) t
    (fun i => isClosed_constructibleTopology.mp (ht i)) hfin
  have hempty : (⋂ i, t i) = ∅ := by
    rw [← Set.univ_inter (⋂ i, t i)]
    exact hEmpty
  rw [hempty] at hne
  exact hne.ne_empty rfl

end Fip

/-- **Exercise 27 iv)**, restated with the compact set visible: `Spec A` is a compact set in the
constructible topology. -/
theorem isCompact_univ_constructibleTopology (A : Type u) [CommRing A] :
    @IsCompact (PrimeSpectrum A) (ConstructibleTopology A) Set.univ :=
  @CompactSpace.isCompact_univ (PrimeSpectrum A) (ConstructibleTopology A) (part_iv A)
end AtiyahMcdonald69.Ex_3_27

#print axioms AtiyahMcdonald69.Ex_3_27.part_i
#print axioms AtiyahMcdonald69.Ex_3_27.part_ii
#print axioms AtiyahMcdonald69.Ex_3_27.exists_stage_algebraMap_mem
#print axioms AtiyahMcdonald69.Ex_3_27.comap_map_iotaA_eq_of_mem
#print axioms AtiyahMcdonald69.Ex_3_27.isClosed_constructibleTopology
#print axioms AtiyahMcdonald69.Ex_3_27.isClosed_constructible_of_isClosed_zariski
#print axioms AtiyahMcdonald69.Ex_3_27.constructibleTopology_le_zariski
#print axioms AtiyahMcdonald69.Ex_3_27.inter_nonempty_of_fip
#print axioms AtiyahMcdonald69.Ex_3_27.part_iv
#print axioms AtiyahMcdonald69.Ex_3_27.isCompact_univ_constructibleTopology
#print AtiyahMcdonald69.Ex_3_27.isCompact_univ_constructibleTopology
