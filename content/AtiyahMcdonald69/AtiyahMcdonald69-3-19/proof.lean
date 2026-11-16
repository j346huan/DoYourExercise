/-
Formalization of Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 3, Exercise 19.

Let `A` be a ring and `M` an `A`-module.  The *support* of `M` is the set of prime
ideals `p` of `A` with `M_p ≠ 0`.  The exercise asks for:

(i)   `M ≠ 0 → Supp M ≠ ∅`;
(ii)  `V(a) = Supp (A/a)`;
(iii) `0 → M' → M → M'' → 0` exact implies `Supp M = Supp M' ∪ Supp M''`;
(iv)  `M = Σ_i M_i` implies `Supp M = ⋃_i Supp M_i`;
(v)   `M` finitely generated implies `Supp M = V(Ann M)`;
(vi)  `M, N` finitely generated implies `Supp (M ⊗ N) = Supp M ∩ Supp N`;
(vii) `M` finitely generated implies `Supp (M/aM) = V(a + Ann M)`;
(viii)`M` finitely generated implies `Supp_B (B ⊗_A M) = f^{*-1}(Supp_A M)`.

The eight parts are formalized below as, respectively,
`support_nonempty`, `support_quotient_self`, `support_of_exact`, `support_iSup`,
`support_eq_zeroLocus_annihilator`, `support_tensorProduct`,
`support_quotient_smul_top` and `support_baseChange`.

The support is `Module.support A M` (Mathlib), i.e. the set of `p : PrimeSpectrum A`
with `Nontrivial (LocalizedModule p.asIdeal.primeCompl M)`, which is literally the
book's definition (an honest localization, not an existential abstraction).
`V(a)` is `PrimeSpectrum.zeroLocus a` and `f^*` is
`PrimeSpectrum.comap (algebraMap A B)`.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open PrimeSpectrum
open scoped Pointwise TensorProduct

namespace AtiyahMcdonald69.Ex_3_19

variable {A : Type*} [CommRing A]

/-! ### Auxiliary lemmas on tensor products -/

section TensorAux

variable {R : Type*} [CommRing R]
variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem nontrivial_of_equiv {X Y : Type*} (e : X ≃ Y) (h : Nontrivial Y) : Nontrivial X := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e.symm a, e.symm b, fun hEq => hab (by simpa using congrArg e hEq)⟩

theorem subsingleton_tensorProduct_left [Subsingleton X] : Subsingleton (X ⊗[R] Y) := by
  have hz : ∀ z : X ⊗[R] Y, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [hz a, hz b]⟩

theorem subsingleton_tensorProduct_right [Subsingleton Y] : Subsingleton (X ⊗[R] Y) := by
  have hz : ∀ z : X ⊗[R] Y, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [hz a, hz b]⟩

theorem nontrivial_of_linearEquiv (e : X ≃ₗ[R] Y) (h : Nontrivial Y) : Nontrivial X :=
  nontrivial_of_equiv e.toEquiv h

theorem nontrivial_left_of_tensor (h : Nontrivial (X ⊗[R] Y)) : Nontrivial X := by
  by_contra hc
  have hs : Subsingleton X := not_nontrivial_iff_subsingleton.mp hc
  obtain ⟨a, b, hab⟩ := h
  exact hab (@Subsingleton.elim _ (@subsingleton_tensorProduct_left R _ X Y _ _ _ _ hs) a b)

theorem nontrivial_right_of_tensor (h : Nontrivial (X ⊗[R] Y)) : Nontrivial Y := by
  by_contra hc
  have hs : Subsingleton Y := not_nontrivial_iff_subsingleton.mp hc
  obtain ⟨a, b, hab⟩ := h
  exact hab (@Subsingleton.elim _ (@subsingleton_tensorProduct_right R _ X Y _ _ _ _ hs) a b)

/-- Over a local ring, the tensor product of two nonzero finite modules is nonzero. -/
theorem tensor_nontrivial_of_isLocalRing [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hM : Nontrivial M) (hN : Nontrivial N) : Nontrivial (M ⊗[R] N) := by
  obtain ⟨I, f, hI, hf⟩ := @Module.exists_surjective_quotient_of_finite R N _ _ _ _ hN
  have hle : I ≤ (Module.annihilator R M).jacobson :=
    le_trans (IsLocalRing.le_maximalIdeal hI) (IsLocalRing.maximalIdeal_le_jacobson _)
  have hne : (⊤ : Submodule R M) ≠ I • ⊤ :=
    @Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator R M _ _ _ hM _ I hle
  have hnontriv : Nontrivial (M ⧸ (I • ⊤ : Submodule R M)) := by
    rw [Submodule.Quotient.nontrivial_iff]
    exact Ne.symm hne
  have hsurj : Function.Surjective (TensorProduct.map (LinearMap.id : M →ₗ[R] M) f) :=
    TensorProduct.map_surjective (g := (LinearMap.id : M →ₗ[R] M)) (g' := f)
      Function.surjective_id hf
  have hsurj2 : Function.Surjective
      ((TensorProduct.tensorQuotEquivQuotSMul M I).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) f)) :=
    (TensorProduct.tensorQuotEquivQuotSMul M I).surjective.comp hsurj
  exact @Function.Surjective.nontrivial _ _ hnontriv _ hsurj2

end TensorAux

/-! ### Localization and tensor product -/

section LocalizedTensor

/-- `(M ⊗ N)_p ≃ M_p ⊗_{A_p} N_p`. -/
noncomputable def localizedTensorEquiv (p : PrimeSpectrum A)
    (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    LocalizedModule p.asIdeal.primeCompl (M ⊗[A] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (LocalizedModule p.asIdeal.primeCompl M ⊗[Localization.AtPrime p.asIdeal]
        LocalizedModule p.asIdeal.primeCompl N) :=
  (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (M ⊗[A] N)).trans <|
    (TensorProduct.AlgebraTensorModule.distribBaseChange (R := A)
      (A := Localization.AtPrime p.asIdeal) (N := M) (Q := N)).trans <|
      TensorProduct.congr (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm
        (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).symm

end LocalizedTensor

/-! ### Part (i): a nonzero module has nonempty support -/

theorem support_nonempty {M : Type*} [AddCommGroup M] [Module A M] [Nontrivial M] :
    (Module.support A M).Nonempty :=
  Module.nonempty_support_of_nontrivial

theorem support_eq_empty_iff {M : Type*} [AddCommGroup M] [Module A M] :
    Module.support A M = ∅ ↔ Subsingleton M :=
  Module.support_eq_empty_iff

/-! ### Part (ii): `Supp (A/a) = V(a)` -/

theorem support_self : Module.support A A = Set.univ := by
  rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr inferInstance,
    PrimeSpectrum.zeroLocus_bot]

theorem ideal_smul_top (a : Ideal A) : (a • ⊤ : Submodule A A) = a := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr m _
    simpa [smul_eq_mul] using Ideal.mul_mem_right m a hr
  · intro x hx
    have h : x • (1 : A) ∈ a • (⊤ : Submodule A A) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa using h

theorem support_quotient_self (a : Ideal A) :
    Module.support A (A ⧸ a) = PrimeSpectrum.zeroLocus a := by
  have h := Module.support_quotient (M := A) a
  rw [ideal_smul_top, support_self, Set.univ_inter] at h
  exact h

/-! ### Part (iii): support is additive on exact sequences -/

theorem support_of_exact {M M' M'' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [AddCommGroup M''] [Module A M'']
    {f : M' →ₗ[A] M} {g : M →ₗ[A] M''}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.support A M = Module.support A M' ∪ Module.support A M'' :=
  Module.support_of_exact h hf hg

/-! ### Part (iv): support of a sum of submodules -/

theorem support_iSup {M : Type*} [AddCommGroup M] [Module A M] {ι : Sort*}
    (N : ι → Submodule A M) (hN : ⨆ i, N i = ⊤) :
    Module.support A M = ⋃ i, Module.support A (N i) := by
  refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun i =>
    Module.support_subset_of_injective (Submodule.subtype (N i)) (Submodule.subtype_injective _))
  intro p hp
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hsub : ∀ i, Subsingleton (LocalizedModule p.asIdeal.primeCompl (↥(N i))) :=
    fun i => Module.notMem_support_iff.mp (hcon i)
  have hbase : ∀ (i : ι) (n : M), n ∈ N i →
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M n = 0 := by
    intro i n hn
    have h0 : LocalizedModule.mkLinearMap p.asIdeal.primeCompl (↥(N i)) ⟨n, hn⟩ = 0 :=
      @Subsingleton.elim _ (hsub i) _ _
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at h0
    obtain ⟨r, hr, hr0⟩ := h0
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
    exact ⟨r, hr, by simpa using hr0⟩
  have hzero : ∀ m : M, LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m = 0 := by
    intro m
    have hm : m ∈ ⨆ i, N i := by rw [hN]; exact Submodule.mem_top
    exact Submodule.iSup_induction
      (motive := fun x => LocalizedModule.mkLinearMap p.asIdeal.primeCompl M x = 0)
      N hm (fun i n hn => hbase i n hn) (map_zero _)
      (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  have hsubM : Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
    refine ⟨fun a b => ?_⟩
    have hx : ∀ x : LocalizedModule p.asIdeal.primeCompl M, x = 0 := by
      intro x
      induction x using LocalizedModule.induction_on with
      | h m s =>
        have h : Localization.mk 1 s • (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m) =
            LocalizedModule.mk m s := by
          rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_smul_mk]
          simp
        rw [← h, hzero m, smul_zero]
    rw [hx a, hx b]
  exact (Module.notMem_support_iff.mpr hsubM) hp

/-! ### Part (v): `Supp M = V(Ann M)` for finitely generated `M` -/

theorem support_eq_zeroLocus_annihilator (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    Module.support A M = PrimeSpectrum.zeroLocus (Module.annihilator A M) :=
  Module.support_eq_zeroLocus

/-! ### Part (vi): `Supp (M ⊗ N) = Supp M ∩ Supp N` -/

theorem support_tensorProduct (M N : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] :
    Module.support A (M ⊗[A] N) = Module.support A M ∩ Module.support A N := by
  ext p
  simp only [Set.mem_inter_iff, Module.mem_support_iff]
  constructor
  · intro h
    have h1 : Nontrivial (LocalizedModule p.asIdeal.primeCompl M ⊗[Localization.AtPrime p.asIdeal]
        LocalizedModule p.asIdeal.primeCompl N) :=
      nontrivial_of_linearEquiv (localizedTensorEquiv p M N).symm h
    exact ⟨nontrivial_left_of_tensor h1, nontrivial_right_of_tensor h1⟩
  · rintro ⟨hM, hN⟩
    exact nontrivial_of_linearEquiv (localizedTensorEquiv p M N)
      (tensor_nontrivial_of_isLocalRing hM hN)

/-! ### Part (vii): `Supp (M/aM) = V(a + Ann M)` -/

theorem support_quotient_smul_top (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : Ideal A) :
    Module.support A (M ⧸ (a • ⊤ : Submodule A M)) =
      PrimeSpectrum.zeroLocus (a + Module.annihilator A M) := by
  rw [Module.support_quotient, Module.support_eq_zeroLocus]
  have h : (a + Module.annihilator A M : Ideal A) = a ⊔ Module.annihilator A M := rfl
  rw [h, PrimeSpectrum.zeroLocus_sup, Set.inter_comm]

/-! ### Part (viii): support under base change -/

section BaseChange

variable {B : Type*} [CommRing B] [Algebra A B]
variable {M : Type*} [AddCommGroup M] [Module A M]

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- The target of the base-change comparison: `B_q ⊗_{A_p} M_p`, where `p = q ∩ A`. -/
noncomputable abbrev baseChangeTarget (q : PrimeSpectrum B) (M : Type*) [AddCommGroup M]
    [Module A M] : Type _ :=
  Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime
    (PrimeSpectrum.comap (algebraMap A B) q).asIdeal]
    LocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl M

/-- The comparison isomorphism `(B ⊗[A] M)_q ≃ B_q ⊗_{A_p} M_p`, where `p = q ∩ A`. -/
noncomputable def baseChangeLocalizationEquiv (q : PrimeSpectrum B) :
    LocalizedModule q.asIdeal.primeCompl (B ⊗[A] M) ≃ baseChangeTarget (A := A) q M :=
  let p := PrimeSpectrum.comap (algebraMap A B) q
  (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl (B ⊗[A] M)).toEquiv.trans <|
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (R := A) (A := B)
      (B := Localization.AtPrime q.asIdeal) (M := Localization.AtPrime q.asIdeal)
      (N := M)).toEquiv.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (R := A)
        (A := Localization.AtPrime p.asIdeal) (B := Localization.AtPrime q.asIdeal)
        (M := Localization.AtPrime q.asIdeal) (N := M)).symm.toEquiv.trans <|
        (TensorProduct.congr (LinearEquiv.refl (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal))
          (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm).toEquiv

/-- The maximal ideal of `A_p` extends into the maximal ideal of `B_q`. -/
theorem maximalIdeal_map_le (q : PrimeSpectrum B) :
    Ideal.map (algebraMap (Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal) (Localization.AtPrime q.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  set p := PrimeSpectrum.comap (algebraMap A B) q with hp
  have hpq : p.asIdeal = q.asIdeal.comap (algebraMap A B) := rfl
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) =
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) p.asIdeal :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)).symm
  have hmap : Ideal.map (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal))
      (Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) p.asIdeal) =
      Ideal.map (algebraMap A (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    have halg : algebraMap A (Localization.AtPrime q.asIdeal) =
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).comp
          (algebraMap A (Localization.AtPrime p.asIdeal)) := IsScalarTower.algebraMap_eq A _ _
    rw [halg, Ideal.map_map]
  rw [hmax, hmap, ← Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)]
  have halg2 : algebraMap A (Localization.AtPrime q.asIdeal) =
      (algebraMap B (Localization.AtPrime q.asIdeal)).comp (algebraMap A B) :=
    IsScalarTower.algebraMap_eq A B _
  rw [halg2, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  rw [Ideal.map_le_iff_le_comap, hpq]

/-- (viii) Support under base change: `Supp_B (B ⊗_A M) = f^{*-1}(Supp_A M)`. -/
theorem support_baseChange (M' : Type*) [AddCommGroup M'] [Module A M'] [Module.Finite A M'] :
    Module.support B (B ⊗[A] M') = PrimeSpectrum.comap (algebraMap A B) ⁻¹'
      Module.support A M' := by
  ext q
  simp only [Set.mem_preimage, Module.mem_support_iff]
  constructor
  · intro h
    exact nontrivial_right_of_tensor (nontrivial_of_equiv (baseChangeLocalizationEquiv (M := M') q).symm h)
  · intro h
    have hLies : q.asIdeal.LiesOver (PrimeSpectrum.comap (algebraMap A B) q).asIdeal := ⟨rfl⟩
    letI algInst : Algebra (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      @Localization.AtPrime.algebraOfLiesOver A B _ _ _
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal _ q.asIdeal _ hLies
    obtain ⟨I, f, hI, hf⟩ := @Module.exists_surjective_quotient_of_finite
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
      (LocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl M') _ _ _ _ h
    have hle : I • (⊤ : Submodule (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
        (Localization.AtPrime q.asIdeal)) ≤
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).restrictScalars
          (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal) := by
      rw [Submodule.smul_le]
      intro i hi s _
      have hgen : algebraMap (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
          (Localization.AtPrime q.asIdeal) i ∈ Ideal.map (algebraMap (Localization.AtPrime
            (PrimeSpectrum.comap (algebraMap A B) q).asIdeal) (Localization.AtPrime q.asIdeal)) I :=
        Ideal.mem_map_of_mem _ hi
      have h2 : algebraMap (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
          (Localization.AtPrime q.asIdeal) i * s ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
        Ideal.mul_mem_right s (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
          ((maximalIdeal_map_le (A := A) q) (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI) hgen))
      show i • s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)
      rw [Algebra.smul_def]
      exact h2
    have hne : (I • (⊤ : Submodule (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
        (Localization.AtPrime q.asIdeal))) ≠ ⊤ := by
      intro htop
      have hone : (1 : Localization.AtPrime q.asIdeal) ∈ I • (⊤ : Submodule (Localization.AtPrime
          (PrimeSpectrum.comap (algebraMap A B) q).asIdeal) (Localization.AtPrime q.asIdeal)) := by
        rw [htop]; exact Submodule.mem_top
      have h1 : (1 : Localization.AtPrime q.asIdeal) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
        (Submodule.restrictScalars_mem (S := Localization.AtPrime
            (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
          (V := IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) (m := 1)).mp (hle hone)
      exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q.asIdeal)).lt_top.ne
        ((Ideal.eq_top_iff_one _).mpr h1)
    have hnontriv : Nontrivial (Localization.AtPrime q.asIdeal ⧸ (I • (⊤ : Submodule
        (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal)
        (Localization.AtPrime q.asIdeal)))) := by
      rw [Submodule.Quotient.nontrivial_iff]
      exact hne
    have hsurj : Function.Surjective (LinearMap.lTensor (Localization.AtPrime q.asIdeal) f) :=
      LinearMap.lTensor_surjective (Localization.AtPrime q.asIdeal) hf
    have hsurj2 : Function.Surjective
        (fun z => (TensorProduct.tensorQuotEquivQuotSMul (Localization.AtPrime q.asIdeal) I)
          ((LinearMap.lTensor (Localization.AtPrime q.asIdeal) f) z)) :=
      (TensorProduct.tensorQuotEquivQuotSMul (Localization.AtPrime q.asIdeal) I).surjective.comp hsurj
    exact nontrivial_of_equiv (baseChangeLocalizationEquiv (M := M') q)
      (@Function.Surjective.nontrivial _ _ hnontriv _ hsurj2)

end BaseChange

/-! ### Part (viii) for an arbitrary ring homomorphism -/

section RingHomVersion

variable {B : Type*} [CommRing B]

/-- Part (viii) in the book's shape: for a ring homomorphism `f : A →+* B`,
`Supp_B (B ⊗_A M) = f^{*-1}(Supp_A M)`. -/
theorem support_baseChange_ringHom (f : A →+* B) (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    letI : Algebra A B := f.toAlgebra
    Module.support B (B ⊗[A] M) = PrimeSpectrum.comap f ⁻¹' Module.support A M := by
  letI : Algebra A B := f.toAlgebra
  have h : Module.support B (B ⊗[A] M) =
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.support A M :=
    support_baseChange (A := A) (B := B) (M' := M)
  have halg : (algebraMap A B : A →+* B) = f := rfl
  rw [h, halg]

end RingHomVersion

end AtiyahMcdonald69.Ex_3_19

/-! ### Audit of the hypotheses

The book's parts (i)--(iv) hold for arbitrary modules; parts (v)--(viii) genuinely need
finite generation, as the following counterexamples show (all easy to check, and none of
them is formalized below since they are only meant to justify the hypotheses):

* (v) without finite generation: for `A = k[x]` with `k` algebraically closed and
  `M = ⨁_{n ∈ k} k[x]/(x - n)` one has `Supp M = {maximal ideals of k[x]}`, which is not
  closed, while `Ann M = 0`, so `V(Ann M) = Spec k[x]`.
* (vi) without finite generation: `A = ℤ`, `M = ℚ`, `N = ℚ/ℤ`.  Then
  `Supp M = Spec ℤ` and `Supp N = Spec ℤ ∖ {(0)}`, but `M ⊗ N = 0` because `ℚ` is
  divisible and `ℚ/ℤ` is torsion, so `Supp (M ⊗ N) = ∅`.
* (vii) without finite generation: `A = ℤ`, `M = ℚ`, `a = pℤ`.  Then `aM = M`, so
  `Supp (M/aM) = ∅`, whereas `V(a + Ann M) = V(pℤ) = {(p)}`.
* (viii) without finite generation: `A = ℤ`, `B = 𝔽_p`, `M = ℚ`.  Then
  `B ⊗_A M = 0`, so the left hand side is empty, while `(p) ∈ Supp_ℤ ℚ`.

Part (i) also has the converse `Supp M = ∅ → M = 0` (`support_eq_empty_iff`), and in (iii)
the hypothesis `0 → M' → M → M'' → 0` exact is formalized as `f` injective, `g` surjective
and `Function.Exact f g`.  In (ii) and (vii) the submodule `a • ⊤` of `M` is the book's
`aM`; in (ii) the quotient `A ⧸ a` is the `A`-module `A/a`.  In (viii) the ring map
`f : A → B` is encoded as an `Algebra A B` structure, `f^*` being
`PrimeSpectrum.comap (algebraMap A B)`; the comparison isomorphism used in the proof is
`(B ⊗_A M)_q ≃ B_q ⊗_{A_p} M_p` (`baseChangeLocalizationEquiv`), which is the book's
`Supp(B ⊗_A M) = f^{*-1}(Supp M)` computation in disguise. -/

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_3_19.support_nonempty
#print axioms AtiyahMcdonald69.Ex_3_19.support_quotient_self
#print axioms AtiyahMcdonald69.Ex_3_19.support_of_exact
#print axioms AtiyahMcdonald69.Ex_3_19.support_iSup
#print axioms AtiyahMcdonald69.Ex_3_19.support_eq_zeroLocus_annihilator
#print axioms AtiyahMcdonald69.Ex_3_19.support_tensorProduct
#print axioms AtiyahMcdonald69.Ex_3_19.support_quotient_smul_top
#print axioms AtiyahMcdonald69.Ex_3_19.support_baseChange
#print axioms AtiyahMcdonald69.Ex_3_19.support_baseChange_ringHom

#print axioms AtiyahMcdonald69.Ex_3_19.support_nonempty
#print axioms AtiyahMcdonald69.Ex_3_19.support_quotient_self
#print axioms AtiyahMcdonald69.Ex_3_19.support_of_exact
#print axioms AtiyahMcdonald69.Ex_3_19.support_iSup
#print axioms AtiyahMcdonald69.Ex_3_19.support_eq_zeroLocus_annihilator
#print axioms AtiyahMcdonald69.Ex_3_19.support_tensorProduct
#print axioms AtiyahMcdonald69.Ex_3_19.support_quotient_smul_top
#print axioms AtiyahMcdonald69.Ex_3_19.support_baseChange
#print axioms AtiyahMcdonald69.Ex_3_19.support_baseChange_ringHom
