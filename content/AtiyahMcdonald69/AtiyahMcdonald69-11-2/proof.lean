import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

namespace AtiyahMcdonald69.Ex_11_2

/-! ## The discrete topology on a field -/

instance (priority := 100) instWithIdealField (K : Type*) [Field K] : WithIdeal K := ⟨⊥⟩

/-- Adic completeness gives topological completeness. -/
instance (priority := 100) instCompleteSpaceOfAdicComplete (B : Type*) [CommRing B] [WithIdeal B]
    [IsAdicComplete (WithIdeal.i (R := B)) B] : CompleteSpace B :=
  ((IsAdic.isAdicComplete_iff (I := WithIdeal.i (R := B)) (R := B) (by rfl)).mp
    ‹IsAdicComplete (WithIdeal.i (R := B)) B›).1

/-- Adic completeness gives separatedness. -/
instance (priority := 100) instT2SpaceOfAdicComplete (B : Type*) [CommRing B] [WithIdeal B]
    [IsAdicComplete (WithIdeal.i (R := B)) B] : T2Space B :=
  ((IsAdic.isAdicComplete_iff (I := WithIdeal.i (R := B)) (R := B) (by rfl)).mp
    ‹IsAdicComplete (WithIdeal.i (R := B)) B›).2

/-- The coefficient map `k → A` of a `k`-algebra is continuous for the adic
topologies; `k` carries the discrete (`⊥`-adic) topology. -/
theorem continuous_algebraMap_field {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [WithIdeal A] : Continuous (algebraMap k A) := by
  refine (WithIdeal.uniformContinuous_of_map_le (f := (algebraMap k A)) ?_).continuous
  show Ideal.map (algebraMap k A) (WithIdeal.i (R := k)) ≤ WithIdeal.i (R := A)
  rw [show WithIdeal.i (R := k) = ⊥ from rfl, Ideal.map_bot]
  exact bot_le

/-- Elements of the preferred ideal are topologically nilpotent. -/
theorem hasEval_of_mem {A : Type*} [CommRing A] [WithIdeal A] {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ WithIdeal.i (R := A)) : HasEval x :=
  { hpow := fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
    tendsto_zero := by
      rw [Filter.cofinite_eq_bot]
      show Filter.map x ⊥ ≤ _
      rw [Filter.map_bot]
      exact bot_le }

/-! ## The substitution homomorphism `k[[t_1,…,t_d]] → A` -/

section Subst

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [WithIdeal A]
  [IsAdicComplete (WithIdeal.i (R := A)) A] {d : ℕ}

/-- **The substitution homomorphism** `k[[t_1,…,t_d]] → A`, `t_i ↦ x_i`. -/
noncomputable def subst (x : Fin d → A) (hx : ∀ i, x i ∈ WithIdeal.i (R := A)) :
    MvPowerSeries (Fin d) k →+* A :=
  eval₂Hom (φ := algebraMap k A) continuous_algebraMap_field (hasEval_of_mem x hx)

theorem subst_apply (x : Fin d → A) (hx : ∀ i, x i ∈ WithIdeal.i (R := A))
    (F : MvPowerSeries (Fin d) k) :
    subst x hx F = eval₂ (algebraMap k A) x F := by
  rw [subst]
  exact congrFun
    (MvPowerSeries.coe_eval₂Hom (φ := algebraMap k A) continuous_algebraMap_field
      (hasEval_of_mem x hx)) F

@[simp]
theorem subst_X (x : Fin d → A) (hx : ∀ i, x i ∈ WithIdeal.i (R := A)) (i : Fin d) :
    subst (k := k) x hx (MvPowerSeries.X i) = x i := by
  rw [subst_apply, MvPowerSeries.eval₂_X (φ := algebraMap k A) (a := x) (s := i)]

@[simp]
theorem subst_C (x : Fin d → A) (hx : ∀ i, x i ∈ WithIdeal.i (R := A)) (c : k) :
    subst (k := k) x hx (MvPowerSeries.C c) = algebraMap k A c := by
  rw [subst_apply, MvPowerSeries.eval₂_C (φ := algebraMap k A) (a := x)]

/-- On polynomials the substitution is ordinary polynomial evaluation. -/
theorem subst_coe (x : Fin d → A) (hx : ∀ i, x i ∈ WithIdeal.i (R := A))
    (p : MvPolynomial (Fin d) k) :
    subst (k := k) x hx (p : MvPowerSeries (Fin d) k) =
      MvPolynomial.eval₂ (algebraMap k A) x p := by
  rw [subst_apply, MvPowerSeries.eval₂_coe (φ := algebraMap k A) (a := x)]

end Subst

end AtiyahMcdonald69.Ex_11_2

namespace AtiyahMcdonald69.Ex_11_2



open Submodule

/-- If `R` is `I`-adically precomplete, so is every finite power `R ^ s`. -/
theorem isPrecomplete_fin_pi {R : Type*} [CommRing R] (I : Ideal R) (s : ℕ) [IsPrecomplete I R] :
    IsPrecomplete I (Fin s → R) := by
  refine ⟨fun f hf => ?_⟩
  have hpi : ∀ n : ℕ, I ^ n • (⊤ : Submodule R (Fin s → R)) =
      Submodule.pi Set.univ (fun _ => I ^ n • (⊤ : Submodule R R)) := by
    intro n
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_pi]
      intro j _
      refine Submodule.smul_induction_on hv ?_ ?_
      · intro i hi m _
        simp only [Pi.smul_apply]
        exact Submodule.smul_mem_smul hi Submodule.mem_top
      · intro x y hx hy
        simp only [Pi.add_apply]
        exact Submodule.add_mem _ hx hy
    · intro v hv
      rw [Submodule.mem_pi] at hv
      have hdecomp : v = ∑ j : Fin s, LinearMap.single R (fun _ : Fin s => R) j (v j) := by
        have h1 : ∀ j : Fin s, (LinearMap.single R (fun _ : Fin s => R) j) (v j) = Pi.single j (v j) :=
          fun j => LinearMap.single_apply ..
        simp only [h1]
        exact (Finset.univ_sum_single v).symm
      rw [hdecomp]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hvj : v j ∈ I ^ n • (⊤ : Submodule R R) := hv j (Set.mem_univ j)
      clear hv
      revert hvj
      intro hvj
      refine Submodule.smul_induction_on hvj ?_ ?_
      · intro i hi m _
        have h1 : (LinearMap.single R (fun _ : Fin s => R) j) (i • m) =
            i • ((LinearMap.single R (fun _ : Fin s => R) j) m) := map_smul _ _ _
        rw [h1]
        exact Submodule.smul_mem_smul hi Submodule.mem_top
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  have hcomp : ∀ j : Fin s, ∃ L : R, ∀ n, f n j - L ∈ I ^ n := by
    intro j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (f := fun n => f n j) (fun {m n} hmn => by
      refine SModEq.sub_mem.mpr ?_
      have h := SModEq.sub_mem.mp (hf hmn)
      rw [hpi m] at h
      rw [Submodule.mem_pi] at h
      exact h j (Set.mem_univ j))
    exact ⟨L, fun n => by simpa using SModEq.sub_mem.mp (hL n)⟩
  choose L hL using hcomp
  refine ⟨L, fun n => SModEq.sub_mem.mpr ?_⟩
  rw [hpi n, Submodule.mem_pi]
  intro j _
  simpa using hL j n

section Finite

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]

/-- An `A`-module that is finitely generated over `A` and killed by the maximal ideal
is finitely generated over the coefficient field `k` (when `k → A ⧸ m` is bijective). -/
theorem moduleFinite_of_smul_maximalIdeal_eq_bot
    (hcoef : Function.Bijective
      (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c)))
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite A M]
    (hbot : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) = ⊥) :
    Module.Finite k M := by
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := A) (M := M))
  have hmem : ∀ a : A, ∀ s ∈ (S : Set M), a • s ∈ Submodule.span k (S : Set M) := by
    intro a s hs
    obtain ⟨c, hc⟩ := hcoef.2 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)
    have hsub : algebraMap k A c - a ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hc
    have hzero : (algebraMap k A c - a) • s = 0 := by
      have h1 : (algebraMap k A c - a) • s ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) :=
        Submodule.smul_mem_smul hsub Submodule.mem_top
      rw [hbot] at h1
      simpa using h1
    have has : a • s = c • s := by
      have h3 : (algebraMap k A c) • s = a • s := by
        have h4 : (algebraMap k A c) • s - a • s = 0 := by
          rw [← sub_smul]; exact hzero
        exact sub_eq_zero.mp h4
      rw [← h3]
      exact IsScalarTower.algebraMap_smul A c s
    rw [has]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hs)
  have hclosed : ∀ a : A, ∀ y ∈ Submodule.span k (S : Set M),
      a • y ∈ Submodule.span k (S : Set M) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact hmem a s hs
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y1 y2 _ _ ih1 ih2 => rw [smul_add]; exact Submodule.add_mem _ ih1 ih2
    | smul c y _ ih =>
        rw [smul_comm]
        exact Submodule.smul_mem _ _ ih
  have hle : ∀ y : M, y ∈ Submodule.span A (S : Set M) → y ∈ Submodule.span k (S : Set M) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span hs
    | zero => exact Submodule.zero_mem _
    | add y1 y2 _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
    | smul a y _ ih => exact hclosed a y ih
  have htop : (⊤ : Submodule k M).FG := by
    refine Submodule.fg_def.mpr ⟨S, hSfin, ?_⟩
    apply le_antisymm le_top
    intro y _
    exact hle y (by rw [hS]; exact Submodule.mem_top)
  have hfin : Module.Finite k ↥(⊤ : Submodule k M) := Module.Finite.of_fg htop
  exact Module.Finite.equiv (Submodule.topEquiv (R := k) (M := M))

end Finite

section QuotientPow

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/-- The image of `m ^ N` in `A ⧸ m ^ (N+1)` is finite over the coefficient field. -/
theorem moduleFinite_image_pow
    (hcoef : Function.Bijective
      (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c)))
    (N : ℕ) :
    Module.Finite k (Submodule.map (Submodule.mkQ (IsLocalRing.maximalIdeal A ^ (N + 1)))
      (IsLocalRing.maximalIdeal A ^ N : Ideal A)) := by
  set P : Submodule A (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) :=
    Submodule.map (Submodule.mkQ (IsLocalRing.maximalIdeal A ^ (N + 1)))
      (IsLocalRing.maximalIdeal A ^ N : Ideal A) with hPdef
  haveI hPA : Module.Finite A P :=
    Module.Finite.of_fg (hPdef ▸ Submodule.FG.map
      (Submodule.mkQ (IsLocalRing.maximalIdeal A ^ (N + 1)))
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A ^ N)))
  have hbot : IsLocalRing.maximalIdeal A • (⊤ : Submodule A P) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro j hj z _
      obtain ⟨w, hw, hwz⟩ := z.2
      have hzero : j • (Submodule.mkQ (IsLocalRing.maximalIdeal A ^ (N + 1)) w) = 0 := by
        rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        have hmem : j * w ∈
            IsLocalRing.maximalIdeal A * IsLocalRing.maximalIdeal A ^ N :=
          Ideal.mul_mem_mul hj hw
        rwa [← pow_succ'] at hmem
      have hcoe : (z : A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) =
          Submodule.mkQ (IsLocalRing.maximalIdeal A ^ (N + 1)) w := hwz.symm
      have : (j • z : ↥P) = 0 := by
        apply Subtype.ext
        show j • (z : A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) = (0 : A ⧸ _)
        rw [hcoe, hzero]
      rw [this]
    · intro a b ha hb
      rw [ha, hb, add_zero]
  exact moduleFinite_of_smul_maximalIdeal_eq_bot (M := ↥P) hcoef hbot


/-- `A ⧸ m` is finite over the coefficient field. -/
theorem moduleFinite_quotient_maximalIdeal
    (hcoef : Function.Bijective
      (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c))) :
    Module.Finite k (A ⧸ IsLocalRing.maximalIdeal A) := by
  let f : k →ₗ[k] (A ⧸ IsLocalRing.maximalIdeal A) :=
    (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal A)).toLinearMap.comp (Algebra.linearMap k A)
  have hf : Function.Bijective f := hcoef
  exact Module.Finite.equiv (LinearEquiv.ofBijective f hf)

/-- `A ⧸ m ^ (N+1)` is finite over the coefficient field. -/
theorem moduleFinite_quotient_maximalIdeal_pow_succ
    (hcoef : Function.Bijective
      (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c))) :
    ∀ N : ℕ, Module.Finite k (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) := by
  intro N
  induction N with
  | zero =>
    show Module.Finite k (A ⧸ IsLocalRing.maximalIdeal A ^ 1)
    rw [pow_one]
    exact moduleFinite_quotient_maximalIdeal hcoef
  | succ N ih =>
    haveI := ih
    set Q : Ideal A := IsLocalRing.maximalIdeal A ^ (N + 1 + 1) with hQdef
    set T : Ideal A := IsLocalRing.maximalIdeal A ^ (N + 1) with hTdef
    set P : Submodule A (A ⧸ Q) := Submodule.map (Submodule.mkQ Q) (T : Submodule A A) with hPdef
    have hP : Module.Finite k P := by
      rw [hPdef, hQdef, hTdef]
      exact moduleFinite_image_pow (A := A) hcoef (N + 1)
    have hP' : Module.Finite k ↥(Submodule.restrictScalars k P) := hP
    haveI := hP'
    have hle : Q ≤ T := by rw [hQdef, hTdef]; exact Ideal.pow_le_pow_right (Nat.le_succ _)
    have hiso : ((A ⧸ Q) ⧸ P) ≃ₗ[k] (A ⧸ T) := by
      rw [hPdef]
      exact (Submodule.quotientQuotientEquivQuotient (R := A) Q T hle).restrictScalars k
    haveI hQfin : Module.Finite k ((A ⧸ Q) ⧸ Submodule.restrictScalars k P) :=
      Module.Finite.equiv hiso.symm
    rw [hQdef]
    exact Module.Finite.of_submodule_quotient (Submodule.restrictScalars k P)



/-- Some power of the maximal ideal is contained in every power of an ideal of definition. -/
theorem exists_pow_maximalIdeal_le_pow (q : Ideal A)
    (hrad : q.radical = IsLocalRing.maximalIdeal A) (n : ℕ) :
    ∃ κ : ℕ, IsLocalRing.maximalIdeal A ^ κ ≤ q ^ n := by
  obtain ⟨κ, hκ⟩ := Ideal.exists_radical_pow_le_of_fg q
    (hrad ▸ Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))
  exact ⟨κ * n, by rw [pow_mul]; exact Ideal.pow_right_mono (hrad ▸ hκ) n⟩

/-- `A ⧸ q` is finite over the coefficient field when `q` is an ideal of definition. -/
theorem moduleFinite_quotient_of_radical_eq
    (hcoef : Function.Bijective
      (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c)))
    (q : Ideal A) (hrad : q.radical = IsLocalRing.maximalIdeal A) :
    Module.Finite k (A ⧸ q) := by
  obtain ⟨κ, hκ⟩ := exists_pow_maximalIdeal_le_pow (A := A) q hrad 1
  rw [pow_one] at hκ
  have hle : IsLocalRing.maximalIdeal A ^ (κ + 1) ≤ q :=
    (Ideal.pow_le_pow_right (Nat.le_succ κ)).trans hκ
  haveI := moduleFinite_quotient_maximalIdeal_pow_succ (A := A) hcoef κ
  have hsurj : Function.Surjective (Submodule.mapQ (IsLocalRing.maximalIdeal A ^ (κ + 1)) q
      (LinearMap.id) (by simpa using hle) :
      (A ⧸ IsLocalRing.maximalIdeal A ^ (κ + 1)) →ₗ[A] (A ⧸ q)) := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective q y
    exact ⟨Submodule.mkQ _ a, by rw [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.mkQ_apply]⟩
  exact Module.Finite.of_surjective (LinearMap.restrictScalars k
    (Submodule.mapQ (IsLocalRing.maximalIdeal A ^ (κ + 1)) q (LinearMap.id)
      (by simpa using hle))) hsurj

end QuotientPow


/-- **Nakayama lemma for complete modules** (finite free source). -/
theorem surjective_of_surjective_mod_ideal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) [IsPrecomplete I R] {s : ℕ}
    (f : (Fin s → R) →ₗ[R] A) [IsHausdorff (I.map (algebraMap R A)) A]
    (h : Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R A)) ∘ₗ f)) :
    Function.Surjective f := by
  haveI : IsPrecomplete I (Fin s → R) := isPrecomplete_fin_pi I s
  haveI : IsHausdorff I A :=
    IsHausdorff.map_algebraMap_iff.mp ‹IsHausdorff (I.map (algebraMap R A)) A›
  exact surjective_of_mkQ_comp_surjective (I := I) (M := Fin s → R) (N := A) (f := f) h

/-- **Finiteness from a finite set of generators modulo the ideal of definition.** -/
theorem moduleFinite_of_surjective_mod_ideal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) [IsPrecomplete I R] {s : ℕ}
    (f : (Fin s → R) →ₗ[R] A) [IsHausdorff (I.map (algebraMap R A)) A]
    (h : Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R A)) ∘ₗ f)) :
    Module.Finite R A :=
  Module.Finite.of_surjective f (surjective_of_surjective_mod_ideal I f h)

section MainFinite

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- **Finiteness of `A` over `k[[t]]`** (module-theoretic form of AM 11.2): if the
quotient `A ⧸ (x)` is finite over `k`, then `A` is a finite module over
`k[[t₁,…,t_d]]` acting by `tᵢ ↦ xᵢ`. -/
theorem moduleFinite_mvPowerSeries_of_quotient_finite {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal A)
    (φ : MvPowerSeries (Fin d) k →+* A)
    (hφX : ∀ i, φ (MvPowerSeries.X i) = x i)
    (hφC : ∀ c, φ (MvPowerSeries.C c) = algebraMap k A c)
    (hfin : Module.Finite k (A ⧸ Ideal.span (Set.range x))) :
    letI : Algebra (MvPowerSeries (Fin d) k) A := φ.toAlgebra
    Module.Finite (MvPowerSeries (Fin d) k) A := by
  let R := MvPowerSeries (Fin d) k
  letI : Algebra R A := φ.toAlgebra
  let I : Ideal R := Ideal.span (Set.range (fun i => MvPowerSeries.X i))
  haveI hI : IsAdicComplete I R := inferInstance
  have hq : I.map (algebraMap R A) = Ideal.span (Set.range x) := by
    rw [show algebraMap R A = φ from rfl]
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hφX i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hφX i⟩
  have hqm : Ideal.span (Set.range x) ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.span_le]
    rintro y ⟨i, rfl⟩
    exact hx i
  haveI hHaus : IsHausdorff (I.map (algebraMap R A)) A := by
    rw [hq]
    refine ⟨fun y hy => ?_⟩
    exact IsHausdorff.haus (I := IsLocalRing.maximalIdeal A)
      (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A) y
      (fun n => SModEq.mono (Submodule.smul_mono (pow_le_pow_left' hqm n) le_rfl) (hy n))
  haveI := hfin
  let s := Module.finrank k (A ⧸ Ideal.span (Set.range x))
  let b := Module.finBasis k (A ⧸ Ideal.span (Set.range x))
  choose a ha using fun i : Fin s => Submodule.mkQ_surjective (Ideal.span (Set.range x)) (b i)
  let f : (Fin s → R) →ₗ[R] A :=
    ∑ i : Fin s, (LinearMap.mulRight R (a i)).comp
      ((Algebra.linearMap R A).comp (LinearMap.proj i))
  have hf_apply : ∀ v : Fin s → R, f v = ∑ i, φ (v i) * a i := by
    intro v
    dsimp only [f]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.mulRight_apply]
    rfl
  have hsurj : Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R A)) ∘ₗ f) := by
    have hIq : I • (⊤ : Submodule R A) =
        Submodule.restrictScalars R (Ideal.span (Set.range x) : Submodule A A) := by
      rw [Ideal.smul_top_eq_map, hq]
    rw [hIq]
    intro y
    refine ⟨fun i => MvPowerSeries.C (b.repr y i), ?_⟩
    rw [LinearMap.coe_comp, Function.comp_apply, hf_apply, map_sum]
    have hkey : ∀ (c : k) (w : A),
        (Submodule.mkQ (Ideal.span (Set.range x))) (algebraMap k A c * w) =
          c • (Submodule.mkQ (Ideal.span (Set.range x)) w) := by
      intro c w
      rw [show algebraMap k A c * w = algebraMap k A c • w from rfl, map_smul]
      exact IsScalarTower.algebraMap_smul A c _
    trans ∑ i, b.repr y i • b i
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hφC, ← ha i]
      exact hkey (b.repr y i) (a i)
    · exact b.sum_repr y
  exact moduleFinite_of_surjective_mod_ideal (I := I) f hsurj

end MainFinite
universe u v

/-- AM (11.20), graded form: no nonzero homogeneous form over the coefficient
field evaluates into the next power of `𝔮 = (x)`.  Equivalently, the natural map
`k[T_1,…,T_d] → gr_𝔮(A)` is injective. -/
def GradedStatement (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (q : Ideal A) : Prop :=
  ∀ (r : ℕ) (p : MvPolynomial (Fin d) k), p.IsHomogeneous r → p ≠ 0 →
    MvPolynomial.eval₂ (algebraMap k A) x p ∉ q ^ (r + 1)

/-- The finiteness half of AM 11.2: `A` is a finite module over
`k[[t_1,…,t_d]]`, the module structure being the one induced by `φ`. -/
def FiniteConclusion (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (φ : MvPowerSeries (Fin d) k →+* A) : Prop :=
  letI : Algebra (MvPowerSeries (Fin d) k) A := φ.toAlgebra
  Module.Finite (MvPowerSeries (Fin d) k) A

/-- The formal statement of Atiyah–Macdonald, Exercise 11.2 (Chapter 11, p. 125). -/
def statement : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
    Function.Bijective
        (fun c : k => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap k A c)) →
    ∀ (d : ℕ), ringKrullDim A = (d : WithBot ℕ∞) → ∀ x : Fin d → A,
      (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal A →
      ∃ φ : MvPowerSeries (Fin d) k →+* A,
        (∀ i, φ (MvPowerSeries.X i) = x i) ∧ Function.Injective φ ∧
          FiniteConclusion k A φ

/-- In a power series ring with no variables, a series is determined by its constant term. -/
lemma mvps_isEmpty_constantCoeff_injective (k : Type*) [CommSemiring k] :
    Function.Injective (MvPowerSeries.constantCoeff (σ := Fin 0) (R := k)) := by
  intro f g hfg
  refine MvPowerSeries.ext fun m => ?_
  have hm : m = 0 := Subsingleton.elim m 0
  subst hm
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hfg

/-- The kernel of the constant-term map is the ideal spanned by the variables. -/
theorem ker_constantCoeff_eq_span_X (k : Type*) [CommRing k] (d : ℕ) :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin d) (R := k)) =
      Ideal.span (Set.range (fun i : Fin d => MvPowerSeries.X i)) := by
  induction d with
  | zero =>
    have hinj := mvps_isEmpty_constantCoeff_injective k
    have hbot : RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 0) (R := k)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    rw [hbot]
    simp
  | succ n ih =>
    refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
    · intro f hf
      simp only [RingHom.mem_ker] at hf
      set e := MvPowerSeries.finSuccEquiv k n with he
      set F : PowerSeries (MvPowerSeries (Fin n) k) := e f with hF
      set c : MvPowerSeries (Fin n) k := PowerSeries.coeff 0 F with hc
      have hc0 : MvPowerSeries.constantCoeff c = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc,
          MvPowerSeries.coeff_coeff_finSuccEquiv, Finsupp.cons_zero_zero,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hf
      have hcspan : c ∈ Ideal.span (Set.range (fun i : Fin n => MvPowerSeries.X i)) := by
        rw [← ih, RingHom.mem_ker]
        exact hc0
      have hdvd : PowerSeries.X ∣ F - PowerSeries.C c := by
        rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      obtain ⟨G, hG⟩ := hdvd
      set ψ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin (n + 1)) k :=
        e.symm.toRingHom.comp PowerSeries.C with hψ
      have hψX : ∀ i : Fin n, ψ (MvPowerSeries.X i) = MvPowerSeries.X i.succ := by
        intro i
        show e.symm (PowerSeries.C (MvPowerSeries.X i)) = MvPowerSeries.X i.succ
        rw [← MvPowerSeries.finSuccEquiv_X_succ i, AlgEquiv.symm_apply_apply]
      have hψmap : Ideal.map ψ (Ideal.span (Set.range (fun i : Fin n => MvPowerSeries.X i)))
          ≤ Ideal.span (Set.range (fun i : Fin (n + 1) => MvPowerSeries.X i)) := by
        rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, hψX]
        exact Ideal.subset_span ⟨i.succ, rfl⟩
      have hc' : ψ c ∈ Ideal.span (Set.range (fun i : Fin (n + 1) => MvPowerSeries.X i)) :=
        hψmap (Ideal.mem_map_of_mem (f := ψ) hcspan)
      have hsymmX : e.symm PowerSeries.X = MvPowerSeries.X (0 : Fin (n + 1)) := by
        rw [← MvPowerSeries.finSuccEquiv_X_zero (R := k) (n := n), AlgEquiv.symm_apply_apply]
      have hsplit : f = ψ c + e.symm PowerSeries.X * e.symm G := by
        have hFG : F = PowerSeries.C c + PowerSeries.X * G := by
          rw [add_comm, ← hG]; abel
        calc f = e.symm F := (AlgEquiv.symm_apply_apply e f).symm
          _ = e.symm (PowerSeries.C c + PowerSeries.X * G) := by rw [hFG]
          _ = ψ c + e.symm PowerSeries.X * e.symm G := by
                rw [map_add, map_mul]; rfl
      rw [hsplit, hsymmX]
      refine Ideal.add_mem _ hc' ?_
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact MvPowerSeries.constantCoeff_X i

/-- The quotient of a multivariate power series ring by its variables is the base ring. -/
noncomputable def quotient_span_X_ringEquiv (k : Type*) [CommRing k] (d : ℕ) :
    (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (fun i : Fin d => MvPowerSeries.X (R := k) i)))
      ≃+* k := by
  have hsurj : Function.Surjective (MvPowerSeries.constantCoeff (σ := Fin d) (R := k)) :=
    fun c => ⟨MvPowerSeries.C c, MvPowerSeries.constantCoeff_C c⟩
  have h : (MvPowerSeries (Fin d) k ⧸
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin d) (R := k))) ≃+* k :=
    RingHom.quotientKerEquivOfSurjective hsurj
  rwa [ker_constantCoeff_eq_span_X] at h

/-- The multivariate power series ring over a field has dimension at most the number of
variables. -/
theorem ringKrullDim_mvPowerSeries_le (k : Type*) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
  classical
  have : IsNoetherianRing (MvPowerSeries (Fin d) k) := inferInstance
  have hdimQ : ringKrullDim
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (fun i : Fin d => MvPowerSeries.X (R := k) i)))
      = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv (quotient_span_X_ringEquiv k d)]
    exact ringKrullDim_eq_zero_of_field k
  have hmem : (↑(Finset.univ.image (fun i : Fin d => MvPowerSeries.X (R := k) i)) :
      Set (MvPowerSeries (Fin d) k)) ⊆ Ring.jacobson (MvPowerSeries (Fin d) k) := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hunit => by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hunit
      exact not_isUnit_zero hunit
  have hspan : Ideal.span (↑(Finset.univ.image (fun i : Fin d => MvPowerSeries.X (R := k) i)) :
      Set (MvPowerSeries (Fin d) k)) =
      Ideal.span (Set.range (fun i : Fin d => MvPowerSeries.X i)) := by
    congr 1
    simp
  have hmain := ringKrullDim_le_ringKrullDim_quotient_add_card
    (s := Finset.univ.image (fun i : Fin d => MvPowerSeries.X (R := k) i)) hmem
  rw [hspan, hdimQ, zero_add] at hmain
  refine hmain.trans ?_
  have hcard : (Finset.univ.image (fun i : Fin d => MvPowerSeries.X (R := k) i)).card ≤ d := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => MvPowerSeries.X (R := k) i)
  exact_mod_cast hcard

/-- The dimension of a ring is at most the dimension of the base modulo the kernel of the
structure map, for an integral (e.g. finite) algebra. -/
theorem ringKrullDim_le_ringKrullDim_quotient_ker {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim (R ⧸ RingHom.ker (algebraMap R A)) := by
  classical
  set K : Ideal R := RingHom.ker (algebraMap R A) with hK
  have hKle : ∀ I : Ideal A, K ≤ I.comap (algebraMap R A) := by
    intro I x hx
    simp only [hK, RingHom.mem_ker] at hx
    simp only [Ideal.mem_comap, hx]
    exact I.zero_mem
  let g : PrimeSpectrum A → PrimeSpectrum (R ⧸ K) := fun P =>
    ⟨(P.asIdeal.comap (algebraMap R A)).map (Ideal.Quotient.mk K),
      Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hKle P.asIdeal)⟩
  have hg : StrictMono g := by
    intro P Q hPQ
    have hPQ' : P.asIdeal < Q.asIdeal := hPQ
    have hcomap : P.asIdeal.comap (algebraMap R A) < Q.asIdeal.comap (algebraMap R A) :=
      Ideal.IsIntegral.comap_lt_comap hPQ'
    refine lt_of_le_of_ne (Ideal.map_mono hcomap.le) ?_
    intro heq
    apply hcomap.ne
    have h1 : (g P).asIdeal = (g Q).asIdeal := congrArg PrimeSpectrum.asIdeal heq
    simp only [g] at h1
    have h2 : Ideal.comap (Ideal.Quotient.mk K)
          (Ideal.map (Ideal.Quotient.mk K) (P.asIdeal.comap (algebraMap R A))) =
        Ideal.comap (Ideal.Quotient.mk K)
          (Ideal.map (Ideal.Quotient.mk K) (Q.asIdeal.comap (algebraMap R A))) :=
      congrArg (Ideal.comap (Ideal.Quotient.mk K)) h1
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (hKle P.asIdeal), sup_eq_left.mpr (hKle Q.asIdeal)] at h2
    exact h2
  exact Order.krullDim_le_of_strictMono g hg

/-- **Injectivity of the structure map** of a complete local ring (with `k ≅ A/𝔪`) that is
a finite module over the power series ring `k[[t₁,…,t_d]]` in `d = dim A` variables. -/
theorem ker_eq_bot_of_moduleFinite {k : Type*} [Field k] {d : ℕ} {A : Type*} [CommRing A]
    [Algebra (MvPowerSeries (Fin d) k) A] [Module.Finite (MvPowerSeries (Fin d) k) A]
    (hdim : ringKrullDim A = ((d : ℕ∞) : WithBot ℕ∞)) :
    RingHom.ker (algebraMap (MvPowerSeries (Fin d) k) A) = ⊥ := by
  classical
  set R := MvPowerSeries (Fin d) k
  set K : Ideal R := RingHom.ker (algebraMap R A) with hK
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsLocalRing R := inferInstance
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have hdimR : ringKrullDim R ≤ ((d : ℕ∞) : WithBot ℕ∞) := ringKrullDim_mvPowerSeries_le k d
  by_contra hne
  -- a nonzero element of the kernel
  obtain ⟨a, haK, ha0⟩ : ∃ a ∈ K, a ≠ 0 := by
    by_contra h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  -- `A` is nontrivial
  haveI : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exfalso
      haveI := h
      rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
      exact WithBot.coe_ne_bot hdim.symm
    · exact h
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : algebraMap R A (1 : R) = 0 := by
      have h2 : (1 : R) ∈ RingHom.ker (algebraMap R A) := by
        rw [← hK, htop]
        exact Submodule.mem_top
      exact RingHom.mem_ker.mpr h2
    have h3 : (1 : A) = 0 := by
      rw [← h1, map_one]
    exact one_ne_zero h3
  have ham : a ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hKne haK
  have hanzd : a ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => (mul_eq_zero.mp hx).resolve_left ha0,
      fun x hx => (mul_eq_zero.mp hx).resolve_right ha0⟩
  -- dimension of the quotient by `a`
  have hC := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors (R := R)
    (r := a) hanzd (p := IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)) ham
  -- upper bound from `(a) ⊆ K`
  have hle : Ideal.span {a} ≤ K := (Ideal.span_singleton_le_iff_mem K).mpr haK
  have hquot : ringKrullDim (R ⧸ K) ≤ ringKrullDim (R ⧸ Ideal.span {a}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)
  -- chain of inequalities
  have hstep1 : ((d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {a}) := by
    rw [← hdim]
    exact (ringKrullDim_le_ringKrullDim_quotient_ker (R := R) (A := A)).trans hquot
  have hstep2 : ringKrullDim (R ⧸ Ideal.span {a}) + 1 ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [hC]
    exact hdimR
  have hbad : 1 + ((d : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
    refine (add_le_add_right hstep1 1).trans ?_
    simpa [add_comm] using hstep2
  have hbad' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hbad
  have : d + 1 ≤ d := by exact_mod_cast hbad'
  omega



/-- **Atiyah–Macdonald, Exercise 11.2**: for a complete Noetherian local ring `A` containing a
field `k` with `k ≅ A/𝔪`, a system of parameters `x : Fin d → A` in `d = dim A` variables
gives a continuous injective `k`-algebra map `k[[t₁,…,t_d]] → A` making `A` a finite module. -/
theorem statement_holds : statement.{u, v} := by
  intro k A _ _ _ _ _ hac hcoef d hd x hrad
  letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
  have hri : WithIdeal.i (R := A) = IsLocalRing.maximalIdeal A := rfl
  have hxq : ∀ i, x i ∈ Ideal.span (Set.range x) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hx : ∀ i, x i ∈ WithIdeal.i (R := A) := by
    intro i
    rw [hri, ← hrad]
    exact Ideal.le_radical (hxq i)
  have hx' : ∀ i, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hri]
    exact hx i
  have hfinq : Module.Finite k (A ⧸ Ideal.span (Set.range x)) :=
    moduleFinite_quotient_of_radical_eq hcoef (Ideal.span (Set.range x)) hrad
  letI : Algebra (MvPowerSeries (Fin d) k) A := (subst (k := k) x hx).toAlgebra
  have hfinmod : Module.Finite (MvPowerSeries (Fin d) k) A :=
    moduleFinite_mvPowerSeries_of_quotient_finite x hx' (subst x hx)
      (fun i => subst_X x hx i) (fun c => subst_C x hx c) hfinq
  have hker : RingHom.ker (algebraMap (MvPowerSeries (Fin d) k) A) = ⊥ :=
    ker_eq_bot_of_moduleFinite hd
  have hinj : Function.Injective (subst (k := k) x hx) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    exact hker
  exact ⟨subst x hx, fun i => subst_X x hx i, hinj, hfinmod⟩


/-! ## Axiom audit -/

#print axioms AtiyahMcdonald69.Ex_11_2.subst
#print axioms AtiyahMcdonald69.Ex_11_2.moduleFinite_quotient_of_radical_eq
#print axioms AtiyahMcdonald69.Ex_11_2.moduleFinite_mvPowerSeries_of_quotient_finite
#print axioms AtiyahMcdonald69.Ex_11_2.ker_constantCoeff_eq_span_X
#print axioms AtiyahMcdonald69.Ex_11_2.quotient_span_X_ringEquiv
#print axioms AtiyahMcdonald69.Ex_11_2.ringKrullDim_mvPowerSeries_le
#print axioms AtiyahMcdonald69.Ex_11_2.ringKrullDim_le_ringKrullDim_quotient_ker
#print axioms AtiyahMcdonald69.Ex_11_2.ker_eq_bot_of_moduleFinite
#print axioms AtiyahMcdonald69.Ex_11_2.statement_holds

end AtiyahMcdonald69.Ex_11_2
