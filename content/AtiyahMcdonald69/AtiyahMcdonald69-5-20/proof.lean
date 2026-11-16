import Mathlib

noncomputable section
open Polynomial MvPolynomial
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_5_20

/-! ## Auxiliary lemmas -/

lemma dilation_injective {ι : Type*} {R : Type*} [Field R] (c : ι → R) (hc : ∀ i, c i ≠ 0) :
    Function.Injective
      (MvPolynomial.aeval (fun i => MvPolynomial.C (c i) * MvPolynomial.X i) :
        MvPolynomial ι R →ₐ[R] MvPolynomial ι R) := by
  have key : ∀ P : MvPolynomial ι R,
      (MvPolynomial.aeval (fun i => MvPolynomial.C ((c i)⁻¹) * MvPolynomial.X i))
        ((MvPolynomial.aeval (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)) P) = P := by
    intro P
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have h : (fun i => (MvPolynomial.aeval (fun j => MvPolynomial.C ((c j)⁻¹) * MvPolynomial.X j))
        (MvPolynomial.C (c i) * MvPolynomial.X i)) = MvPolynomial.X := by
      funext i
      simp only [MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_mul, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ (hc i), MvPolynomial.C_1, one_mul]
    rw [h, MvPolynomial.aeval_X_left]
    rfl
  intro P Q hPQ
  have h1 := key P
  have h2 := key Q
  rw [hPQ] at h1
  rw [← h1, h2]

lemma isIntegral_of_units_mul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (u : Rˣ) {z : S} (h : IsIntegral R (algebraMap R S (u : R) * z)) : IsIntegral R z := by
  have h1 : IsIntegral R (algebraMap R S ((u⁻¹ : Rˣ) : R)) := isIntegral_algebraMap
  have h2 : IsIntegral R (algebraMap R S (u : R) * z * algebraMap R S ((u⁻¹ : Rˣ) : R)) :=
    h.mul h1
  have h3 : algebraMap R S (u : R) * z * algebraMap R S ((u⁻¹ : Rˣ) : R) = z := by
    rw [mul_comm (algebraMap R S (u : R)) z, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  rwa [h3] at h2

lemma isIntegral_of_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {S₁ S₂ : Subalgebra R S}
    (h : S₁ ≤ S₂) {z : S} (hz : IsIntegral S₁ z) : IsIntegral S₂ z := by
  obtain ⟨p, hp, hpz⟩ := hz
  let g : S₁ →+* S₂ := Subalgebra.inclusion h
  refine ⟨p.map g, hp.map g, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : ((algebraMap S₂ S).comp g) = (algebraMap S₁ S) := by
    ext x
    rfl
  rw [hcomp]
  exact hpz

lemma isIntegral_of_ringHom {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] (f : S →+* A) (S' : Subalgebra R A) (hf : ∀ x, f x ∈ S') {z : A}
    (hz : f.IsIntegralElem z) : IsIntegral S' z := by
  obtain ⟨p, hp, hpz⟩ := hz
  let g : S →+* S' :=
    { toFun := fun x => ⟨f x, hf x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hcomp : (algebraMap S' A).comp g = f := RingHom.ext (fun x => rfl)
  refine ⟨p.map g, hp.map g, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hpz

/-! ## The generic fibre -/
section Generic

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]

/-- The image in `B` of the nonzero elements of `A`. -/
def M : Submonoid B := (nonZeroDivisors A).map (algebraMap A B).toMonoidHom

lemma algebraMap_injective : Function.Injective (algebraMap A B) :=
  FaithfulSMul.algebraMap_injective A B

lemma mem_M_iff {x : B} : x ∈ M A B ↔ ∃ a ∈ nonZeroDivisors A, algebraMap A B a = x :=
  Submonoid.mem_map

lemma M_le_nonZeroDivisors : M A B ≤ nonZeroDivisors B := by
  intro x hx
  obtain ⟨a, ha, hx'⟩ := (mem_M_iff A B).mp hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rw [← hx']
  intro h
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (algebraMap_injective A B (by rw [h, map_zero]))

/-- The generic fibre of `A ⊆ B`: `B` localized at the image of `A∖{0}`. -/
abbrev R : Type _ := Localization (M A B)

instance : IsDomain (R A B) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R := B) (M := M A B) (R A B)
    (M_le_nonZeroDivisors A B)

lemma isUnit_algebraMap_of_ne_zero {a : A} (ha : a ≠ 0) : IsUnit (algebraMap A (R A B) a) := by
  have h : algebraMap A B a ∈ M A B :=
    (mem_M_iff A B).mpr ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha, rfl⟩
  have h2 : IsUnit (algebraMap B (R A B) (algebraMap A B a)) :=
    IsLocalization.map_units (R A B) ⟨_, h⟩
  rw [IsScalarTower.algebraMap_apply A B (R A B)]
  exact h2

/-- Every element of the generic fibre is a fraction `b / a` with `a : A` nonzero. -/
lemma surj_R (z : R A B) :
    ∃ (b : B) (a : A) (_ : a ≠ 0), z * algebraMap A (R A B) a = algebraMap B (R A B) b := by
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (M A B) z
  obtain ⟨a, ha, ha'⟩ := (mem_M_iff A B).mp m.2
  refine ⟨b, a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
  rw [← ha'] at hm
  rw [IsScalarTower.algebraMap_apply A B (R A B)]
  exact hm

/-- The fraction field of `A`. -/
abbrev K : Type _ := FractionRing A

/-- The `Frac A`-algebra structure on the generic fibre. -/
noncomputable def KtoR : K A →+* R A B :=
  IsLocalization.lift (M := nonZeroDivisors A) (S := K A) (g := algebraMap A (R A B))
    (fun y => isUnit_algebraMap_of_ne_zero A B (mem_nonZeroDivisors_iff_ne_zero.mp y.2))

instance : Algebra (K A) (R A B) := (KtoR A B).toAlgebra

instance : IsScalarTower A (K A) (R A B) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A (R A B) x = KtoR A B (algebraMap A (K A) x)
    exact (IsLocalization.lift_eq _ x).symm)

/-- Naturality of `aeval` for polynomial rings over `A` mapping into the generic fibre. -/
lemma aeval_map_eq {m : ℕ} (F : MvPolynomial (Fin m) A →ₐ[A] B) (P : MvPolynomial (Fin m) A) :
    algebraMap B (R A B) (F P) =
      (MvPolynomial.aeval (fun j => algebraMap B (R A B) (F (MvPolynomial.X j))))
        ((MvPolynomial.map (algebraMap A (K A))) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have h1 : F (MvPolynomial.C a) = algebraMap A B a := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rw [h1, MvPolynomial.map_C, MvPolynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply A B (R A B) a).symm.trans
        (IsScalarTower.algebraMap_apply A (K A) (R A B) a)
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]

/-- The generic fibre is a finitely generated `Frac A`-algebra. -/
lemma finiteType_K_R : Algebra.FiniteType (K A) (R A B) := by
  obtain ⟨m, F, hF⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A B)
  let Ψ : MvPolynomial (Fin m) (K A) →ₐ[K A] R A B :=
    MvPolynomial.aeval fun j => algebraMap B (R A B) (F (MvPolynomial.X j))
  refine Algebra.FiniteType.of_surjective Ψ ?_
  intro z
  obtain ⟨b, a, ha, hz⟩ := surj_R A B z
  obtain ⟨P, rfl⟩ := hF b
  have haK : algebraMap A (K A) a ≠ 0 := fun h => ha (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hz' : z * algebraMap (K A) (R A B) (algebraMap A (K A) a) =
      Ψ ((MvPolynomial.map (algebraMap A (K A))) P) := by
    have hs : algebraMap A (R A B) a = algebraMap (K A) (R A B) (algebraMap A (K A) a) :=
      IsScalarTower.algebraMap_apply A (K A) (R A B) a
    rw [aeval_map_eq A B F P, hs] at hz
    exact hz
  have hΨ : Ψ (MvPolynomial.C (algebraMap A (K A) a)⁻¹ * MvPolynomial.map (algebraMap A (K A)) P) *
      algebraMap (K A) (R A B) (algebraMap A (K A) a) =
      Ψ ((MvPolynomial.map (algebraMap A (K A))) P) := by
    rw [map_mul, MvPolynomial.aeval_C,
      mul_comm (algebraMap (K A) (R A B) (algebraMap A (K A) a)⁻¹), mul_assoc, ← map_mul,
      inv_mul_cancel₀ haK, map_one, mul_one]
  refine ⟨MvPolynomial.C (algebraMap A (K A) a)⁻¹ * MvPolynomial.map (algebraMap A (K A)) P, ?_⟩
  have hb0 : algebraMap (K A) (R A B) (algebraMap A (K A) a) ≠ 0 := by
    intro h
    have h' : algebraMap A (R A B) a = 0 := by
      rw [IsScalarTower.algebraMap_apply A (K A) (R A B)]; exact h
    have h'' : algebraMap B (R A B) (algebraMap A B a) = 0 := by
      rw [← IsScalarTower.algebraMap_apply A B (R A B)]; exact h'
    have h3 : algebraMap A B a = 0 :=
      (IsLocalization.injective (R A B) (M_le_nonZeroDivisors A B)) (by rw [h'', map_zero])
    exact ha (algebraMap_injective A B (h3.trans (map_zero _).symm))
  refine mul_right_cancel₀ hb0 ?_
  rw [hΨ, hz']

end Generic


end AtiyahMcdonald69.Ex_5_20

namespace AtiyahMcdonald69.Ex_5_20

namespace Main

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]

/-- Compatibility of `aeval` with coefficient extension along `A → Frac A`. -/
lemma aeval_algebraMap_eq {m : ℕ} (z : Fin m → R A B) (u : MvPolynomial (Fin m) A) :
    (MvPolynomial.aeval z : MvPolynomial (Fin m) (K A) →ₐ[K A] R A B)
        ((MvPolynomial.map (algebraMap A (K A))) u)
      = (MvPolynomial.aeval z : MvPolynomial (Fin m) A →ₐ[A] R A B) u := by
  induction u using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply A (K A) (R A B) a).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]

set_option maxHeartbeats 10000000 in
theorem solution_generic :
    ∃ (t : A) (ht : t ≠ 0) (d : ℕ) (y : Fin d → B),
      AlgebraicIndependent A y ∧
      ∀ b : B, IsIntegral (Algebra.adjoin A (Set.range (fun i => algebraMap B (R A B) (y i)) ∪
        {↑(((isUnit_algebraMap_of_ne_zero A B ht).unit)⁻¹ : (R A B)ˣ)})) (algebraMap B (R A B) b) := by
  classical
  obtain ⟨m, F, hF⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A B)
  haveI hft : Algebra.FiniteType (K A) (R A B) := finiteType_K_R A B
  have hinjAR : Function.Injective (algebraMap A (R A B)) := by
    intro u v huv
    refine algebraMap_injective A B ((IsLocalization.injective (R A B) (M_le_nonZeroDivisors A B)) ?_)
    rw [← IsScalarTower.algebraMap_apply A B (R A B), huv, IsScalarTower.algebraMap_apply A B (R A B)]
  obtain ⟨d, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg (K A) (R A B)
  set x : Fin d → R A B := fun i => g (MvPolynomial.X i) with hxdef
  have hΨg : (MvPolynomial.aeval x : MvPolynomial (Fin d) (K A) →ₐ[K A] R A B) = g := by
    rw [MvPolynomial.aeval_unique g]; rfl
  have hx_inj : Function.Injective (MvPolynomial.aeval x : MvPolynomial (Fin d) (K A) →ₐ[K A] R A B) := by
    rw [hΨg]; exact hg_inj
  have hx_indep : AlgebraicIndependent (K A) x := hx_inj
  have hxy : ∀ i, ∃ (b : B) (a : A) (_ : a ≠ 0), x i * algebraMap A (R A B) a = algebraMap B (R A B) b :=
    fun i => surj_R A B (x i)
  choose y a ha hy using hxy
  have hy' : ∀ i, algebraMap B (R A B) (y i) =
      algebraMap (K A) (R A B) (algebraMap A (K A) (a i)) * x i := by
    intro i
    rw [← hy i, IsScalarTower.algebraMap_apply A (K A) (R A B)]; ring
  have hainj : Function.Injective (algebraMap A (K A)) := IsFractionRing.injective A (K A)
  have hdil : Function.Injective
      (MvPolynomial.aeval (fun i => MvPolynomial.C (algebraMap A (K A) (a i)) * MvPolynomial.X i) :
        MvPolynomial (Fin d) (K A) →ₐ[K A] MvPolynomial (Fin d) (K A)) :=
    dilation_injective _ (fun i => by simpa using hainj.ne_iff.mpr (ha i))
  have hy_indep_K : AlgebraicIndependent (K A) (fun i => algebraMap B (R A B) (y i)) := by
    have hcomp : (MvPolynomial.aeval (fun i => algebraMap B (R A B) (y i)) :
        MvPolynomial (Fin d) (K A) →ₐ[K A] R A B) =
        (MvPolynomial.aeval x).comp (MvPolynomial.aeval (fun i => MvPolynomial.C (algebraMap A (K A) (a i)) * MvPolynomial.X i)) := by
      ext i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      rw [hy' i]
      simp
    rw [algebraicIndependent_iff_injective_aeval, hcomp, AlgHom.coe_comp]
    exact hx_inj.comp hdil
  have hy_indep_A : AlgebraicIndependent A y :=
    AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom A B (R A B))
      (hy_indep_K.restrictScalars hainj)
  have hx_indep_A : AlgebraicIndependent A x := hx_indep.restrictScalars hainj
  have hmonic : ∀ j : Fin m, ∃ p : Polynomial (MvPolynomial (Fin d) (K A)), p.Monic ∧
      p.eval₂ (g : MvPolynomial (Fin d) (K A) →+* R A B) (algebraMap B (R A B) (F (MvPolynomial.X j))) = 0 :=
    fun j => hg_int _
  choose p hpmono hpeval using hmonic
  -- clearing the `Frac A`-coefficients of the monic equations
  set Φ : MvPolynomial (Fin d) A →ₐ[A] R A B :=
    MvPolynomial.aeval (fun i => algebraMap B (R A B) (y i)) with hΦ
  have hclear : ∀ c : MvPolynomial (Fin d) (K A), ∃ (t₁ : A) (_ : t₁ ≠ 0) (C : MvPolynomial (Fin d) A),
      Φ C = algebraMap A (R A B) t₁ * (MvPolynomial.aeval x) c := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C k =>
        obtain ⟨p', u, hu, hk⟩ := IsFractionRing.div_surjective A k
        refine ⟨u, (mem_nonZeroDivisors_iff_ne_zero.mp hu), MvPolynomial.C p', ?_⟩
        have hu0 : algebraMap A (K A) u ≠ 0 :=
          fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hu) (IsFractionRing.to_map_eq_zero_iff.mp h)
        have h1 : algebraMap A (K A) u * k = algebraMap A (K A) p' := by rw [← hk]; field_simp
        simp only [hΦ, MvPolynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply A (K A) (R A B) u, ← map_mul, h1,
          ← IsScalarTower.algebraMap_apply A (K A) (R A B) p']
    | add p1 p2 ih1 ih2 =>
        obtain ⟨t1, ht1, C1, hC1⟩ := ih1
        obtain ⟨t2, ht2, C2, hC2⟩ := ih2
        refine ⟨t1 * t2, mul_ne_zero ht1 ht2, C1 * MvPolynomial.C t2 + C2 * MvPolynomial.C t1, ?_⟩
        rw [map_add, map_mul, map_mul, hC1, hC2]
        simp only [hΦ, MvPolynomial.aeval_C, map_mul, map_add]
        ring
    | mul_X p1 j ih =>
        obtain ⟨t1, ht1, C1, hC1⟩ := ih
        refine ⟨t1 * a j, mul_ne_zero ht1 (ha j), C1 * MvPolynomial.X j, ?_⟩
        rw [map_mul, hC1]
        simp only [hΦ, MvPolynomial.aeval_X, hy' j,
          IsScalarTower.algebraMap_apply A (K A) (R A B), map_mul]
        ring
  have hclearFin : ∀ Sr : Finset (MvPolynomial (Fin d) (K A)), ∃ (t₁ : A) (_ : t₁ ≠ 0),
      ∀ c ∈ Sr, ∃ C : MvPolynomial (Fin d) A,
        Φ C = algebraMap A (R A B) t₁ * (MvPolynomial.aeval x) c := by
    intro Sr
    induction Sr using Finset.induction with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert c0 s hc0 ih =>
        obtain ⟨t1, ht1, h1⟩ := hclear c0
        obtain ⟨t2, ht2, h2⟩ := ih
        refine ⟨t1 * t2, mul_ne_zero ht1 ht2, fun c hc => ?_⟩
        rcases Finset.mem_insert.mp hc with rfl | hc
        · obtain ⟨C, hC⟩ := h1
          exact ⟨C * MvPolynomial.C t2, by rw [map_mul, hC, map_mul, MvPolynomial.aeval_C]; ring⟩
        · obtain ⟨C, hC⟩ := h2 c hc
          exact ⟨C * MvPolynomial.C t1, by rw [map_mul, hC, map_mul, MvPolynomial.aeval_C]; ring⟩
  -- the finite set of coefficients of the monic equations, and its clearing
  set Sset : Finset (MvPolynomial (Fin d) (K A)) :=
    Finset.univ.biUnion (fun j : Fin m => (p j).support.image (fun i => (p j).coeff i)) with hSset
  obtain ⟨t₁, ht₁, hclearS⟩ := hclearFin Sset
  have hmem : ∀ (j : Fin m) (i : ℕ), i ∈ (p j).support → (p j).coeff i ∈ Sset := by
    intro j i hi
    exact hSset.symm ▸ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  let Cf : MvPolynomial (Fin d) (K A) → MvPolynomial (Fin d) A := fun c =>
    if hc : c ∈ Sset then (hclearS c hc).choose else 0
  have hCf : ∀ c, c ∈ Sset → Φ (Cf c) = algebraMap A (R A B) t₁ * (MvPolynomial.aeval x) c := by
    intro c hc
    simp only [Cf, dif_pos hc]
    exact (hclearS c hc).choose_spec
  -- the cleared polynomial attached to the `j`-th generator
  let Pj : (j : Fin m) → Polynomial (MvPolynomial (Fin d) A) := fun j =>
    ∑ i ∈ (p j).support, Polynomial.monomial i (Cf ((p j).coeff i))
  have hcoeff : ∀ (j : Fin m) (k : ℕ),
      (Pj j).coeff k = if k ∈ (p j).support then Cf ((p j).coeff k) else 0 := by
    intro j k
    simp only [Pj]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hk : k ∈ (p j).support
    · rw [Finset.sum_eq_single (a := k)]
      · simp [hk]
      · intro b hb hbk
        rw [if_neg hbk]
      · intro hk'; exact absurd hk hk'
    · rw [Finset.sum_eq_zero]
      · simp [hk]
      · intro b hb
        rw [if_neg (fun h : b = k => hk (h ▸ hb))]
  have hmemsupp : ∀ j : Fin m, (p j).natDegree ∈ (p j).support := fun j =>
    Polynomial.natDegree_mem_support_of_nonzero (hpmono j).ne_zero
  have hcoeffnat : ∀ j : Fin m, (p j).coeff ((p j).natDegree) = 1 := fun j =>
    (hpmono j).coeff_natDegree
  have hmemS : ∀ j : Fin m, (1 : MvPolynomial (Fin d) (K A)) ∈ Sset := fun j =>
    hcoeffnat j ▸ hmem j _ (hmemsupp j)
  have hlead : ∀ j : Fin m, (Pj j).leadingCoeff = Cf 1 := by
    intro j
    have hdeg : (Pj j).natDegree = (p j).natDegree := by
      apply le_antisymm
      · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
        rw [hcoeff j k, if_neg]
        intro hmem'
        exact absurd (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hmem')) (by omega)
      · refine le_natDegree_of_ne_zero ?_
        rw [hcoeff j ((p j).natDegree), if_pos (hmemsupp j), hcoeffnat j]
        intro hc0
        have h3 := hCf 1 (hmemS j)
        rw [hc0, map_zero, map_one, mul_one] at h3
        exact ht₁ (hinjAR (by rw [h3.symm, map_zero]))
    rw [Polynomial.leadingCoeff, hdeg, hcoeff j ((p j).natDegree), if_pos (hmemsupp j), hcoeffnat j]
  have hleadΦ : ∀ j : Fin m, Φ ((Pj j).leadingCoeff) = algebraMap A (R A B) t₁ := by
    intro j
    rw [hlead j, hCf 1 (hmemS j), map_one, mul_one]
  have heval : ∀ j : Fin m,
      Polynomial.eval₂ Φ (algebraMap B (R A B) (F (MvPolynomial.X j))) (Pj j) = 0 := by
    intro j
    have hzero : ∑ i ∈ (p j).support, (MvPolynomial.aeval x) ((p j).coeff i) *
        (algebraMap B (R A B) (F (MvPolynomial.X j))) ^ i = 0 := by
      have h2 := hpeval j
      rw [Polynomial.eval₂_eq_sum, ← hΨg] at h2
      exact h2
    simp only [Pj]
    rw [Polynomial.eval₂_finsetSum]
    calc ∑ i ∈ (p j).support, Polynomial.eval₂ Φ (algebraMap B (R A B) (F (MvPolynomial.X j)))
          (Polynomial.monomial i (Cf ((p j).coeff i)))
        = ∑ i ∈ (p j).support, algebraMap A (R A B) t₁ * (MvPolynomial.aeval x ((p j).coeff i)) *
            (algebraMap B (R A B) (F (MvPolynomial.X j))) ^ i := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Polynomial.eval₂_monomial]
          rw [show (Φ : MvPolynomial (Fin d) A →+* R A B) (Cf ((p j).coeff i)) =
            algebraMap A (R A B) t₁ * (MvPolynomial.aeval x) ((p j).coeff i) from
            hCf _ (hmem j i hi)]
      _ = algebraMap A (R A B) t₁ * ∑ i ∈ (p j).support, (MvPolynomial.aeval x) ((p j).coeff i) *
            (algebraMap B (R A B) (F (MvPolynomial.X j))) ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [hzero, mul_zero]
  -- integrality of `t₁ * b_j` over `A[y]`
  have hΦrange : ∀ u, Φ u ∈ Algebra.adjoin A (Set.range (fun i => algebraMap B (R A B) (y i))) := by
    intro u
    have h1 : Φ u ∈ Φ.range := ⟨u, rfl⟩
    rwa [MvPolynomial.aeval_range] at h1
  have hΦcomp : Φ = (IsScalarTower.toAlgHom A B (R A B)).comp (MvPolynomial.aeval y) := by
    ext i
    simp [hΦ]
  have hΦinj : Function.Injective Φ := by
    rw [hΦcomp, AlgHom.coe_comp]
    exact (IsLocalization.injective (R A B) (M_le_nonZeroDivisors A B)).comp hy_indep_A
  have hPj0 : ∀ j : Fin m, Pj j ≠ 0 := by
    intro j h0
    have h1 := hleadΦ j
    rw [h0, Polynomial.leadingCoeff_zero, map_zero] at h1
    exact ht₁ (hinjAR (by rw [← h1]; exact (map_zero _).symm))
  have hint : ∀ j : Fin m, IsIntegral (Algebra.adjoin A (Set.range (fun i => algebraMap B (R A B) (y i))))
      (algebraMap A (R A B) t₁ * algebraMap B (R A B) (F (MvPolynomial.X j))) := by
    intro j
    have hC : (Φ : MvPolynomial (Fin d) A →+* R A B).IsIntegralElem
        (algebraMap A (R A B) t₁ * algebraMap B (R A B) (F (MvPolynomial.X j))) := by
      have hleadΦRH : (Φ : MvPolynomial (Fin d) A →+* R A B) ((Pj j).leadingCoeff) =
          algebraMap A (R A B) t₁ := hleadΦ j
      have h := Polynomial.integralNormalization_eval₂_eq_zero (p := Pj j)
        (Φ : MvPolynomial (Fin d) A →+* R A B) (heval j) (fun r hr => hΦinj hr)
      rw [hleadΦRH] at h
      exact ⟨(Pj j).integralNormalization, monic_integralNormalization (hPj0 j), h⟩
    exact isIntegral_of_ringHom (Φ : MvPolynomial (Fin d) A →+* R A B) _ hΦrange hC
  -- pass to the localization `A[y]_t`
  refine ⟨t₁, ht₁, d, y, hy_indep_A, ?_⟩
  set SR : Subalgebra A (R A B) := Algebra.adjoin A (Set.range (fun i => algebraMap B (R A B) (y i)) ∪
    {↑(((isUnit_algebraMap_of_ne_zero A B ht₁).unit)⁻¹ : (R A B)ˣ)}) with hSR
  have hmem_u : (↑(((isUnit_algebraMap_of_ne_zero A B ht₁).unit)⁻¹ : (R A B)ˣ) : R A B) ∈ SR :=
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  have hut : (↑((isUnit_algebraMap_of_ne_zero A B ht₁).unit) : R A B) = algebraMap A (R A B) t₁ :=
    IsUnit.unit_spec _
  have hmul : algebraMap A (R A B) t₁ * ↑(((isUnit_algebraMap_of_ne_zero A B ht₁).unit)⁻¹ : (R A B)ˣ) = 1 := by
    have h1 : (↑((isUnit_algebraMap_of_ne_zero A B ht₁).unit) : R A B) *
        ↑(((isUnit_algebraMap_of_ne_zero A B ht₁).unit)⁻¹ : (R A B)ˣ) = 1 := Units.mul_inv _
    rwa [hut] at h1
  have hunit : IsUnit (⟨algebraMap A (R A B) t₁, Subalgebra.algebraMap_mem SR t₁⟩ : SR) :=
    isUnit_iff_exists_inv.mpr ⟨⟨↑(((isUnit_algebraMap_of_ne_zero A B ht₁).unit)⁻¹ : (R A B)ˣ), hmem_u⟩, by
      ext
      exact hmul⟩
  have hβint : ∀ j : Fin m, IsIntegral SR (algebraMap B (R A B) (F (MvPolynomial.X j))) := by
    intro j
    have h1 : IsIntegral SR (algebraMap A (R A B) t₁ *
        algebraMap B (R A B) (F (MvPolynomial.X j))) :=
      isIntegral_of_le (Algebra.adjoin_mono (Set.subset_union_left)) (hint j)
    have hu : (algebraMap SR (R A B) (hunit.unit : SR)) = algebraMap A (R A B) t₁ := by
      rw [IsUnit.unit_spec]
      rfl
    exact isIntegral_of_units_mul hunit.unit (by rwa [hu])
  have hgen : ∀ β : MvPolynomial (Fin m) A,
      IsIntegral SR ((MvPolynomial.aeval (fun j => algebraMap B (R A B) (F (MvPolynomial.X j)))) β) := by
    intro β
    induction β using MvPolynomial.induction_on with
    | C c =>
        rw [MvPolynomial.aeval_C]
        have h := isIntegral_algebraMap (R := SR) (A := R A B)
          (x := (⟨algebraMap A (R A B) c, Subalgebra.algebraMap_mem SR c⟩ : SR))
        rwa [show (algebraMap SR (R A B) ⟨algebraMap A (R A B) c, Subalgebra.algebraMap_mem SR c⟩)
          = algebraMap A (R A B) c from rfl] at h
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p j hp => rw [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hβint j)
  intro b
  obtain ⟨β, hβ⟩ := hF b
  have hβeq : algebraMap B (R A B) (F β) =
      (MvPolynomial.aeval (fun j => algebraMap B (R A B) (F (MvPolynomial.X j)))) β := by
    conv_lhs => rw [MvPolynomial.aeval_unique F]
    rw [MvPolynomial.map_aeval]
    simp only [Function.comp_apply, ← IsScalarTower.algebraMap_eq A B (R A B)]
    rfl
  rw [← hβ, hβeq]
  exact hgen β

end Main


/-! ## The localization `B_t` -/

/-- `B` localized at `t`. -/
abbrev T (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (t : A) : Type _ :=
  Localization (Submonoid.powers (algebraMap A B t))

section Tsetup

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]

lemma isDomain_T {t : A} (ht : t ≠ 0) : IsDomain (T A B t) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R := B) (M := Submonoid.powers (algebraMap A B t))
    (T A B t) (fun x hx => by
      obtain ⟨n, hn⟩ := hx
      rw [← hn, mem_nonZeroDivisors_iff_ne_zero]
      exact pow_ne_zero n (fun h => ht (algebraMap_injective A B (by rw [h, map_zero]))))

/-- The canonical map from `B_t` into the generic fibre (where `t` is invertible). -/
noncomputable def psi {t : A} (ht : t ≠ 0) : T A B t →+* R A B :=
  IsLocalization.lift (M := Submonoid.powers (algebraMap A B t)) (S := T A B t)
    (g := algebraMap B (R A B)) (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_algebraMap_of_ne_zero A B ht).pow n)

lemma psi_algebraMap {t : A} (ht : t ≠ 0) (b : B) :
    psi (A := A) (B := B) ht (algebraMap B (T A B t) b) = algebraMap B (R A B) b :=
  IsLocalization.lift_eq _ b

lemma psi_injective {t : A} (ht : t ≠ 0) : Function.Injective (psi (A := A) (B := B) ht) := by
  haveI hdom : IsDomain (T A B t) := isDomain_T ht
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (M := Submonoid.powers (algebraMap A B t)) (S := T A B t) x
  have hb : algebraMap B (R A B) b = 0 := by
    have h1 : psi (A := A) (B := B) ht (algebraMap B (T A B t) b) = 0 := by
      have h2 : psi (A := A) (B := B) ht (x * algebraMap B (T A B t) (m : B)) =
          psi (A := A) (B := B) ht (algebraMap B (T A B t) b) := by rw [hm]
      rw [map_mul, hx, zero_mul] at h2
      exact h2.symm
    rwa [psi_algebraMap] at h1
  have hb0 : b = 0 := (IsLocalization.injective (R A B) (M_le_nonZeroDivisors A B)) (by rw [hb, map_zero])
  rw [hb0, map_zero] at hm
  obtain ⟨n, hn⟩ := m.2
  have hunit : IsUnit (algebraMap B (T A B t) (m : B)) := by
    rw [show (m : B) = (algebraMap A B t) ^ n from hn.symm, map_pow]
    exact (IsLocalization.map_units (M := Submonoid.powers (algebraMap A B t)) (S := T A B t)
      ⟨algebraMap A B t, Submonoid.mem_powers _⟩).pow n
  rcases hunit with ⟨u, hu⟩
  rw [← hu] at hm
  exact (mul_eq_zero.mp hm).resolve_right u.ne_zero

lemma map_eval₂_ringHom {C : Type*} [CommRing C] (ψ : T A B t →+* R A B) (f : C →+* T A B t) (z : T A B t) :
    ∀ p : Polynomial C, ψ (Polynomial.eval₂ f z p) = Polynomial.eval₂ (ψ.comp f) (ψ z) p := by
  intro p
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, Polynomial.eval₂_add, hp, hq]
  | monomial n a => simp [Polynomial.eval₂_C]

end Tsetup

section Tmain

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]

/-- The unit `t` in `B_t`. -/
noncomputable def tUnit (t : A) (_ht : t ≠ 0) : (T A B t)ˣ :=
  (IsLocalization.map_units (M := Submonoid.powers (algebraMap A B t)) (S := T A B t)
    ⟨algebraMap A B t, Submonoid.mem_powers _⟩).unit

/-- The element `t⁻¹` in `B_t`. -/
noncomputable def tInv (t : A) (ht : t ≠ 0) : T A B t :=
  (((tUnit A B t ht)⁻¹ : (T A B t)ˣ) : T A B t)

/-- `psi` as an `A`-algebra homomorphism. -/
noncomputable def psiAlg (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] {t : A} (ht : t ≠ 0) :
    T A B t →ₐ[A] R A B :=
  { psi ht with
    commutes' := fun a => by
      show psi ht (algebraMap A (T A B t) a) = algebraMap A (R A B) a
      rw [IsScalarTower.algebraMap_apply A B (T A B t)]
      exact (psi_algebraMap ht (algebraMap A B a)).trans (IsScalarTower.algebraMap_apply A B (R A B) a) }

lemma psiAlg_apply {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] {t : A} (ht : t ≠ 0) (x : T A B t) :
    psiAlg A B ht x = psi ht x := rfl

set_option maxHeartbeats 10000000 in
theorem solution :
    ∃ (t : A) (ht : t ≠ 0) (d : ℕ) (y : Fin d → B),
      AlgebraicIndependent A y ∧
      ∀ z : T A B t, IsIntegral (Algebra.adjoin A (Set.range (fun i => algebraMap B (T A B t) (y i)) ∪
        {tInv A B t ht})) z := by
  classical
  obtain ⟨t, ht, d, y, hindep, hbint⟩ := Main.solution_generic A B
  haveI hdomT : IsDomain (T A B t) := isDomain_T ht
  refine ⟨t, ht, d, y, hindep, ?_⟩
  set St : Subalgebra A (T A B t) := Algebra.adjoin A (Set.range (fun i => algebraMap B (T A B t) (y i)) ∪
    {tInv A B t ht}) with hSt
  set uT : (T A B t)ˣ := tUnit A B t ht with huTdef
  set uR : (R A B)ˣ := (isUnit_algebraMap_of_ne_zero A B ht).unit with huRdef
  have hStdef : St = Algebra.adjoin A (Set.range (fun i => algebraMap B (T A B t) (y i)) ∪
    {((uT⁻¹ : (T A B t)ˣ) : T A B t)}) := rfl
  set SR : Subalgebra A (R A B) := Algebra.adjoin A (Set.range (fun i => algebraMap B (R A B) (y i)) ∪
    {((uR⁻¹ : (R A B)ˣ) : R A B)}) with hSR
  have huT : (↑uT : T A B t) = algebraMap A (T A B t) t := by
    rw [huTdef, tUnit, IsUnit.unit_spec, IsScalarTower.algebraMap_apply A B (T A B t)]
  have huT' : (↑uT : T A B t) = algebraMap B (T A B t) (algebraMap A B t) := by
    rw [huT, IsScalarTower.algebraMap_apply A B (T A B t)]
  have huR : (↑uR : R A B) = algebraMap A (R A B) t := by
    rw [huRdef, IsUnit.unit_spec]
  have hψuT : psi (A := A) (B := B) ht ((uT⁻¹ : (T A B t)ˣ) : T A B t) = ((uR⁻¹ : (R A B)ˣ) : R A B) := by
    have h1 : psi (A := A) (B := B) ht (↑uT : T A B t) = (↑uR : R A B) := by
      rw [huT', huR, IsScalarTower.algebraMap_apply A B (R A B)]
      exact psi_algebraMap ht (algebraMap A B t)
    have h2 : psi (A := A) (B := B) ht ((uT⁻¹ : (T A B t)ˣ) : T A B t) *
        psi (A := A) (B := B) ht (↑uT : T A B t) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    have h3 : ((uR⁻¹ : (R A B)ˣ) : R A B) * (↑uR : R A B) = 1 := Units.inv_mul _
    exact mul_right_cancel₀ (Units.ne_zero uR) (by rw [h2, h3])
  -- the correspondence between the two subalgebras
  have hmapSet : ∀ r : R A B, r ∈ SR ↔ ∃ s ∈ St, psi (A := A) (B := B) ht s = r := by
    intro r
    constructor
    · intro hr
      induction hr using Algebra.adjoin_induction with
      | mem x hx =>
          rcases hx with ⟨i, rfl⟩ | rfl
          · exact ⟨algebraMap B (T A B t) (y i), Algebra.subset_adjoin (Set.mem_union_left _ ⟨i, rfl⟩),
              psi_algebraMap ht (y i)⟩
          · exact ⟨((uT⁻¹ : (T A B t)ˣ) : T A B t),
              Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _)), hψuT⟩
      | algebraMap a =>
          refine ⟨algebraMap A (T A B t) a, Subalgebra.algebraMap_mem St a, ?_⟩
          rw [IsScalarTower.algebraMap_apply A B (T A B t)]
          exact (psi_algebraMap ht (algebraMap A B a)).trans (IsScalarTower.algebraMap_apply A B (R A B) a)
      | add x y _ _ hx hy =>
          obtain ⟨sx, hsx, rfl⟩ := hx
          obtain ⟨sy, hsy, rfl⟩ := hy
          exact ⟨sx + sy, St.add_mem hsx hsy, by rw [map_add]⟩
      | mul x y _ _ hx hy =>
          obtain ⟨sx, hsx, rfl⟩ := hx
          obtain ⟨sy, hsy, rfl⟩ := hy
          exact ⟨sx * sy, St.mul_mem hsx hsy, by rw [map_mul]⟩
    · rintro ⟨s, hs, rfl⟩
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
          rcases hx with ⟨i, rfl⟩ | rfl
          · rw [psi_algebraMap]
            exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨i, rfl⟩)
          · rw [show tInv A B t ht = ((uT⁻¹ : (T A B t)ˣ) : T A B t) from rfl, hψuT]
            exact Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
      | algebraMap a =>
          rw [IsScalarTower.algebraMap_apply A B (T A B t), psi_algebraMap,
            ← IsScalarTower.algebraMap_apply A B (R A B)]
          exact Subalgebra.algebraMap_mem SR a
      | add x y _ _ hx hy => rw [map_add]; exact SR.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact SR.mul_mem hx hy
  -- transfer
  have htransfer : ∀ b : B, IsIntegral St (algebraMap B (T A B t) b) := by
    intro b
    obtain ⟨p, hp, hpz⟩ := hbint b
    -- the inverse ring hom `SR →+* St`
    let ee : ↥SR → ↥St := fun r => ⟨Classical.choose ((hmapSet (r : R A B)).mp r.2),
      (Classical.choose_spec ((hmapSet (r : R A B)).mp r.2)).1⟩
    have ee_spec : ∀ r : ↥SR, psi (A := A) (B := B) ht (ee r : T A B t) = (r : R A B) := fun r =>
      (Classical.choose_spec ((hmapSet (r : R A B)).mp r.2)).2
    let e : ↥SR →+* ↥St :=
      { toFun := ee
        map_one' := by
          apply Subtype.ext
          apply psi_injective ht
          rw [ee_spec]
          show ((1 : ↥SR) : R A B) = psi (A := A) (B := B) ht ((1 : ↥St) : T A B t)
          rw [show ((1 : ↥St) : T A B t) = 1 from rfl, map_one]
          rfl
        map_mul' := fun r s => by
          apply Subtype.ext
          apply psi_injective ht
          rw [ee_spec]
          show (((r : ↥SR) : R A B) * ((s : ↥SR) : R A B)) =
            psi (A := A) (B := B) ht (((ee r : ↥St) : T A B t) * ((ee s : ↥St) : T A B t))
          rw [map_mul, ee_spec, ee_spec]
        map_zero' := by
          apply Subtype.ext
          apply psi_injective ht
          rw [ee_spec]
          show ((0 : ↥SR) : R A B) = psi (A := A) (B := B) ht ((0 : ↥St) : T A B t)
          rw [show ((0 : ↥St) : T A B t) = 0 from rfl, map_zero]
          rfl
        map_add' := fun r s => by
          apply Subtype.ext
          apply psi_injective ht
          rw [ee_spec]
          show (((r : ↥SR) : R A B) + ((s : ↥SR) : R A B)) =
            psi (A := A) (B := B) ht (((ee r : ↥St) : T A B t) + ((ee s : ↥St) : T A B t))
          rw [map_add, ee_spec, ee_spec] }
    have ee_val : ∀ r : ↥SR, psi (A := A) (B := B) ht (e r : T A B t) = (r : R A B) := ee_spec
    refine ⟨p.map e, hp.map e, ?_⟩
    rw [Polynomial.eval₂_map]
    refine psi_injective ht ?_
    rw [map_eval₂_ringHom (ψ := psi (A := A) (B := B) ht) (f := (algebraMap ↥St (T A B t)).comp e)
      (z := algebraMap B (T A B t) b)]
    have hcomp : (psi (A := A) (B := B) ht).comp ((algebraMap ↥St (T A B t)).comp e) =
        (algebraMap ↥SR (R A B)) := by
      ext r
      show psi (A := A) (B := B) ht (((e r : ↥St) : T A B t)) = ((r : ↥SR) : R A B)
      exact ee_val r
    rw [hcomp, psi_algebraMap, hpz, map_zero]
  -- `B_t` is generated over `A[y]_t` by the images of `B`, all of which are integral
  intro z
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (M := Submonoid.powers (algebraMap A B t)) (S := T A B t) z
  obtain ⟨n, hn⟩ := m.2
  have hmt : (algebraMap B (T A B t) (m : B) : T A B t) = (↑uT : T A B t) ^ n := by
    rw [show (m : B) = (algebraMap A B t) ^ n from hn.symm, map_pow, huT']
  have hz : z = algebraMap B (T A B t) b * (((uT⁻¹ : (T A B t)ˣ) : T A B t)) ^ n := by
    have h1 : z * (↑uT : T A B t) ^ n = algebraMap B (T A B t) b := by
      rw [← hmt]
      exact hm
    have h2 : (((uT⁻¹ : (T A B t)ˣ) : T A B t)) ^ n =
        (((uT ^ n)⁻¹ : (T A B t)ˣ) : T A B t) := by
      rw [← Units.val_pow_eq_pow_val, inv_pow]
    rw [h2, ← h1, ← Units.val_pow_eq_pow_val, mul_assoc, Units.mul_inv, mul_one]
  rw [hz]
  refine IsIntegral.mul (htransfer b) ?_
  have hmem : (((uT⁻¹ : (T A B t)ˣ) : T A B t)) ^ n ∈ St := by
    rw [hStdef]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))) n
  have hint2 : IsIntegral St ((((uT⁻¹ : (T A B t)ˣ) : T A B t)) ^ n) := by
    have h := isIntegral_algebraMap (R := St) (A := T A B t) (x := (⟨_, hmem⟩ : St))
    rwa [show (algebraMap ↥St (T A B t) ⟨_, hmem⟩) = (((uT⁻¹ : (T A B t)ˣ) : T A B t)) ^ n from rfl] at h
  exact hint2

end Tmain

end AtiyahMcdonald69.Ex_5_20

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_5_20.solution
#print axioms AtiyahMcdonald69.Ex_5_20.Main.solution_generic
#print axioms AtiyahMcdonald69.Ex_5_20.finiteType_K_R
