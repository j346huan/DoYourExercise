import Mathlib

/-!
# Atiyah–Macdonald, Exercise 3.2

Let `A` be a (commutative) ring, `𝔞` an ideal of `A` and `S = 1 + 𝔞`.

The exercise (Chapter 3, Exercise 2 of *Introduction to Commutative Algebra*) reads:

> Let `𝔞` be an ideal of a ring `A`, and let `S = 1 + 𝔞`. Show that `S⁻¹𝔞` is contained in the
> Jacobson radical of `S⁻¹A`. Use this result and Nakayama's lemma to give a proof of (2.5)
> which does not depend on determinants.
> [If `M = 𝔞M`, then `S⁻¹M = (S⁻¹𝔞)(S⁻¹M)`, hence by Nakayama we have `S⁻¹M = 0`.
> Now use Exercise 1.]

The formal content below is:

1. `S = 1 + 𝔞` is a multiplicatively closed subset of `A` (`oneAdd` is a `Submonoid`).
2. `S⁻¹𝔞 ⊆ Jac(S⁻¹A)` (`map_oneAdd_le_jacobson`), with the intermediate criterion
   `I ≤ Jac A ↔ ∀ x ∈ I, IsUnit (1 - x)` (`le_jacobson_iff`).
3. Exercise 3.1 (`subsingleton_localized_iff`): for a finitely generated `A`-module `M`,
   `S⁻¹M = 0` iff some `s ∈ S` annihilates `M`.
4. Following the book's route, `𝔞M = M` implies `S⁻¹M = 0`
   (`map_smul_top_eq_top` + `map_oneAdd_le_jacobson` + Nakayama in radical form), hence
   `xM = 0` for some `x ∈ 1 + 𝔞` (`exists_oneAdd_forall_smul_eq_zero`), hence `M = 0` if
   `𝔞 ⊆ Jac A`; that is (2.5) without the determinant trick (`nakayama`).
5. The bundled statement of the exercise: `solution`.

Genuine localizations of rings (`Localization`, `IsLocalization`) and of modules
(`LocalizedModule`, `IsLocalizedModule`) are used; nothing is replaced by a quotient-free
shadow.  The only Nakayama input used in step 4 is the radical form
`eq_bot_of_le_smul_of_le_jacobson`, whose proof below rests on the `1 + J` form of Nakayama
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`), which is proved in Mathlib
by induction on a finite generating set and never invokes the determinant trick.  A second,
independent proof of the radical form through Mathlib's coatomic-lattice Nakayama
(`Submodule.FG.eq_bot_of_le_jacobson_smul`) is recorded as
`eq_bot_of_le_smul_of_le_jacobson_alt`; no Cayley–Hamilton/determinant argument is used
anywhere in this file.

## Audit of the hypotheses

* `S = 1 + 𝔞` is multiplicatively closed for *every* ideal `𝔞` of every ring; no further
  hypothesis is used (`oneAdd`, `oneAdd_mul_mem`, `oneAdd_one_mem`).
* `S⁻¹𝔞 ⊆ Jac(S⁻¹A)` needs no finiteness assumption on `A` or on `𝔞`; it holds for every ideal
  (`map_oneAdd_le_jacobson`).  In particular it holds when `S⁻¹A` is the zero ring, where the
  Jacobson radical is the unit ideal.
* The strengthening `𝔞M = M ⟹ ∃ x ∈ 1 + 𝔞, xM = 0` (`exists_oneAdd_forall_smul_eq_zero`)
  genuinely needs `M` finitely generated, which is why `Module.Finite` is a hypothesis there;
  the same is true of the direction of Exercise 3.1 that is used
  (`subsingleton_localized_iff`, forward direction).  Without finite generation both fail:
  take `A = ℤ_(p)`, `𝔞 = pℤ_(p)` (the maximal ideal, hence contained in the Jacobson radical)
  and `M = ℤ[1/p]/ℤ`, a non-finitely-generated `A`-module.  Then multiplication by `p` is
  surjective on `M`, so `𝔞M = M ≠ 0`, while every `x ∈ 1 + 𝔞` is a unit of `A` and therefore
  acts invertibly on `M`, so no element of `1 + 𝔞` annihilates `M`.  (This counterexample is
  recorded here for the audit only; it is not formalized in this file.)
* In `subsingleton_localized_iff` the finiteness hypothesis is used only for the direction
  `S⁻¹M = 0 ⟹ ∃ s ∈ S, s • n = 0`; the converse implication needs no finiteness.
-/

open scoped Pointwise

namespace AtiyahMcdonald69.Ex_3_2

variable {A : Type*} [CommRing A]

/-! ## 1. The multiplicatively closed subset `1 + 𝔞` -/

/-- For an ideal `I` of a ring `A`, the multiplicatively closed subset `1 + I` of `A`. -/
def oneAdd (I : Ideal A) : Submonoid A where
  carrier := {x | x - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    show x * y - 1 ∈ I
    have h : x * y - 1 = x * (y - 1) + (x - 1) := by ring
    rw [h]
    exact I.add_mem (I.mul_mem_left x hy) hx

@[simp]
theorem mem_oneAdd (I : Ideal A) {x : A} : x ∈ oneAdd I ↔ x - 1 ∈ I := Iff.rfl

theorem mem_oneAdd_iff (I : Ideal A) {x : A} : x ∈ oneAdd I ↔ ∃ a ∈ I, x = a + 1 := by
  rw [mem_oneAdd]
  constructor
  · intro h
    exact ⟨x - 1, h, by ring⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

theorem oneAdd_one_mem (I : Ideal A) : (1 : A) ∈ oneAdd I := (oneAdd I).one_mem

theorem oneAdd_mul_mem (I : Ideal A) {x y : A} (hx : x ∈ oneAdd I) (hy : y ∈ oneAdd I) :
    x * y ∈ oneAdd I := (oneAdd I).mul_mem hx hy

theorem one_add_mem_oneAdd (I : Ideal A) {a : A} (ha : a ∈ I) : a + 1 ∈ oneAdd I := by
  rw [mem_oneAdd]
  simpa using ha

/-! ## 2. A criterion for containment in the Jacobson radical -/

/-- An ideal is contained in the Jacobson radical iff `1 - x` is a unit for every `x` in it.
(A–M, Chapter 1; this is the criterion used in the exercise.) -/
theorem le_jacobson_iff (J : Ideal A) :
    J ≤ Ideal.jacobson (⊥ : Ideal A) ↔ ∀ x ∈ J, IsUnit (1 - x) := by
  constructor
  · intro h x hx
    have h' := (Ideal.mem_jacobson_bot (R := A)).1 (h hx) (-1)
    have e : x * (-1) + 1 = 1 - x := by ring
    rwa [e] at h'
  · intro h x hx
    refine (Ideal.mem_jacobson_bot (R := A)).2 fun y => ?_
    have h' := h (-(y * x)) (J.neg_mem (J.mul_mem_left y hx))
    have e : 1 - -(y * x) = x * y + 1 := by ring
    rwa [e] at h'

/-! ## 3. `S⁻¹𝔞` lies in the Jacobson radical of `S⁻¹A` -/

/-- Atiyah–Macdonald, Exercise 3.2 (first part): `S⁻¹𝔞` is contained in the Jacobson radical of
`S⁻¹A`, where `S = 1 + 𝔞`.  If `z = a/s` with `a ∈ 𝔞` and `s ∈ S`, then
`1 - z = (s - a)/s` with `s - a ∈ 1 + 𝔞 = S`, so `1 - z` is a unit. -/
theorem map_oneAdd_le_jacobson (I : Ideal A) :
    Ideal.map (algebraMap A (Localization (oneAdd I))) I ≤
      Ideal.jacobson (⊥ : Ideal (Localization (oneAdd I))) := by
  set R' := Localization (oneAdd I)
  rw [le_jacobson_iff]
  intro z hz
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (oneAdd I) R').1 hz
  have hzs : z * algebraMap A R' s = algebraMap A R' a := hx
  have hsa : s - a ∈ oneAdd I := by
    rw [mem_oneAdd]
    have e : s - a - 1 = (s - 1) - a := by ring
    rw [e]
    exact I.sub_mem hs ha
  have hunit : IsUnit (algebraMap A R' (s - a)) := IsLocalization.map_units R' ⟨s - a, hsa⟩
  have key : (1 - z) * algebraMap A R' s = algebraMap A R' (s - a) := by
    rw [sub_mul, one_mul, hzs, ← map_sub]
  have hprod : IsUnit ((1 - z) * algebraMap A R' s) := by
    rw [key]
    exact hunit
  exact (IsUnit.mul_iff.1 hprod).1

/-- The same statement with the Jacobson radical written as `Ring.jacobson (S⁻¹A)`. -/
theorem map_oneAdd_le_ring_jacobson (I : Ideal A) :
    Ideal.map (algebraMap A (Localization (oneAdd I))) I ≤
      Ring.jacobson (Localization (oneAdd I)) := by
  rw [← Ideal.jacobson_bot]
  exact map_oneAdd_le_jacobson I

/-! ## 4. Nakayama's lemma in radical form

The exercise uses Nakayama's lemma over the localized ring `S⁻¹A`; the form needed is the
radical one. It is recorded here, with a proof through the `1 + J` form (induction on a finite
generating set, no determinants), together with a second proof through Mathlib's
coatomic-lattice version. -/

/-- Nakayama's lemma in radical form: if `N` is a finitely generated submodule of `M` with
`N ⊆ J • N` and `J` is contained in the Jacobson radical of `R`, then `N = 0`.
This is the form of (2.5) used in Exercise 3.2.  The proof uses only the `1 + J` form of
Nakayama's lemma, obtained by induction on a finite generating set; the determinant trick is
not used. -/
theorem eq_bot_of_le_smul_of_le_jacobson {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (J : Ideal R) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R)) (N : Submodule R M)
    (hN : N.FG) (h : N ≤ J • N) : N = ⊥ := by
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J N hN h
  have hunit : IsUnit r := Ideal.isUnit_of_sub_one_mem_jacobson_bot r (hJ hr)
  obtain ⟨u, hu⟩ := hunit
  refine (Submodule.eq_bot_iff N).mpr fun n hn => ?_
  have h0 : r • n = 0 := hrN n hn
  have h1 : (↑u⁻¹ * ↑u : R) • n = n := by simp
  calc n = (↑u⁻¹ * ↑u : R) • n := h1.symm
    _ = (↑u⁻¹ : R) • ((↑u : R) • n) := by rw [mul_smul]
    _ = (↑u⁻¹ : R) • (r • n) := by rw [hu]
    _ = 0 := by rw [h0, smul_zero]

/-- Second proof of the radical form of Nakayama's lemma, through Mathlib's
`Submodule.FG.eq_bot_of_le_jacobson_smul` (which rests on coatomicity of the lattice of
submodules of a finitely generated module). -/
theorem eq_bot_of_le_smul_of_le_jacobson_alt {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (J : Ideal R) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R))
    (N : Submodule R M) (hN : N.FG) (h : N ≤ J • N) : N = ⊥ := by
  have hJ' : J ≤ Ring.jacobson R := by
    rwa [Ideal.jacobson_bot] at hJ
  exact Submodule.FG.eq_bot_of_le_jacobson_smul hN (h.trans (Submodule.smul_mono_left hJ'))

/-! ## 5. Localizing the relation `𝔞M = M` -/

/-- If `𝔞N = N` then `(S⁻¹𝔞)(S⁻¹N) = S⁻¹N`: localizing the equation `𝔞N = N` gives
`S⁻¹N = (S⁻¹𝔞)(S⁻¹N)` in `S⁻¹N`. -/
theorem map_smul_top_eq_top (I : Ideal A) {N : Type*} [AddCommGroup N] [Module A N]
    (h : I • (⊤ : Submodule A N) = ⊤) :
    Ideal.map (algebraMap A (Localization (oneAdd I))) I •
      (⊤ : Submodule (Localization (oneAdd I)) (LocalizedModule (oneAdd I) N)) = ⊤ := by
  have hmap : Submodule.map (LocalizedModule.mkLinearMap (oneAdd I) N) (I • (⊤ : Submodule A N))
      = I • Submodule.map (LocalizedModule.mkLinearMap (oneAdd I) N) (⊤ : Submodule A N) :=
    Submodule.map_smul'' I ⊤ (LocalizedModule.mkLinearMap (oneAdd I) N)
  rw [h] at hmap
  have hle : (I • Submodule.map (LocalizedModule.mkLinearMap (oneAdd I) N) (⊤ : Submodule A N) :
        Submodule A (LocalizedModule (oneAdd I) N)) ≤
      (Ideal.map (algebraMap A (Localization (oneAdd I))) I •
        (⊤ : Submodule (Localization (oneAdd I))
          (LocalizedModule (oneAdd I) N))).restrictScalars A := by
    rw [Ideal.smul_restrictScalars]
    exact Submodule.smul_mono le_rfl le_top
  have hmap' : ∀ n : N, (LocalizedModule.mkLinearMap (oneAdd I) N) n ∈
      Ideal.map (algebraMap A (Localization (oneAdd I))) I •
        (⊤ : Submodule (Localization (oneAdd I)) (LocalizedModule (oneAdd I) N)) := by
    intro n
    have h1 : (LocalizedModule.mkLinearMap (oneAdd I) N) n ∈
        Submodule.map (LocalizedModule.mkLinearMap (oneAdd I) N) (⊤ : Submodule A N) :=
      Submodule.mem_map_of_mem (f := LocalizedModule.mkLinearMap (oneAdd I) N) Submodule.mem_top
    rw [hmap] at h1
    exact hle h1
  refine top_le_iff.mp ?_
  intro x _
  induction x using LocalizedModule.induction_on with
  | h n s =>
    have hmk : LocalizedModule.mk n s
        = (Localization.mk (1 : A) s) • LocalizedModule.mk n (1 : oneAdd I) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [hmk]
    exact Submodule.smul_mem _ _ (by simpa using hmap' n)

/-! ## 6. Exercise 3.1 -/

/-- Atiyah–Macdonald, Exercise 3.1: for a finitely generated `A`-module `N`,
`S⁻¹N = 0` if and only if some `s ∈ S` annihilates `N`. -/
theorem subsingleton_localized_iff {N : Type*} [AddCommGroup N] [Module A N]
    (S : Submonoid A) [Module.Finite A N] :
    Subsingleton (LocalizedModule S N) ↔ ∃ s : S, ∀ n : N, s • n = 0 := by
  classical
  constructor
  · -- the direction that uses finite generation
    intro h
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := N)
    have key : ∀ m : N, ∃ s : S, s • m = 0 := fun m =>
      (IsLocalizedModule.eq_zero_iff S (LocalizedModule.mkLinearMap S N)).1
        (Subsingleton.elim _ _)
    choose σ hσ using key
    set c : A := ∏ i : Fin n, ((σ (v i) : A)) with hc
    have hcS : c ∈ S := by
      rw [hc]
      have h : ((∏ i : Fin n, σ (v i) : S) : A) = ∏ i : Fin n, ((σ (v i) : A)) := by simp
      rw [← h]
      exact (∏ i : Fin n, σ (v i)).2
    have hgen : ∀ i : Fin n, c • v i = 0 := by
      intro i
      have hsplit : c = (∏ j ∈ Finset.univ.erase i, ((σ (v j) : A))) * ((σ (v i) : A)) := by
        rw [hc, ← Finset.prod_erase_mul Finset.univ (fun j => ((σ (v j) : A)))
          (Finset.mem_univ i)]
      rw [hsplit, mul_smul]
      have hz : ((σ (v i) : A)) • v i = 0 := by
        simpa [Submonoid.smul_def] using hσ (v i)
      rw [hz, smul_zero]
    have hspan : ∀ m ∈ Submodule.span A (Set.range v), c • m = 0 := by
      intro m hm
      have hle : Submodule.span A (Set.range v) ≤ LinearMap.ker (LinearMap.lsmul A N c) := by
        rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        exact LinearMap.mem_ker.mpr (hgen i)
      have h2 := hle hm
      rwa [LinearMap.mem_ker, LinearMap.lsmul_apply] at h2
    refine ⟨⟨c, hcS⟩, fun m => ?_⟩
    have hm : m ∈ Submodule.span A (Set.range v) := by rw [hv]; exact Submodule.mem_top
    have h3 := hspan m hm
    simpa [Submonoid.smul_def] using h3
  · -- the converse direction needs no finiteness
    rintro ⟨s, hs⟩
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := by
      refine LocalizedModule.eq_zero_of_smul_eq_zero (s : A) s.2 x ?_
      induction x using LocalizedModule.induction_on with
      | h m t =>
        rw [LocalizedModule.smul'_mk]
        have h : (s : A) • m = 0 := by simpa [Submonoid.smul_def] using hs m
        rw [h]
        simp
    have hy : y = 0 := by
      refine LocalizedModule.eq_zero_of_smul_eq_zero (s : A) s.2 y ?_
      induction y using LocalizedModule.induction_on with
      | h m t =>
        rw [LocalizedModule.smul'_mk]
        have h : (s : A) • m = 0 := by simpa [Submonoid.smul_def] using hs m
        rw [h]
        simp
    rw [hx, hy]

/-! ## 7. (2.5) without determinants -/

/-- Atiyah–Macdonald, Exercise 3.2: if `N` is a finitely generated `A`-module and `𝔞N = N`,
then some element of `1 + 𝔞` annihilates `N`; this is the strengthened form of (2.5) obtained in
the exercise, without the determinant trick.  The proof is the book's: localize, apply
`S⁻¹𝔞 ⊆ Jac(S⁻¹A)` and Nakayama's lemma over the localized ring, then use Exercise 3.1. -/
theorem exists_oneAdd_forall_smul_eq_zero (I : Ideal A) {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] (h : I • (⊤ : Submodule A N) = ⊤) :
    ∃ x : A, x - 1 ∈ I ∧ ∀ n : N, x • n = 0 := by
  have htop : Ideal.map (algebraMap A (Localization (oneAdd I))) I •
      (⊤ : Submodule (Localization (oneAdd I))
        (LocalizedModule (oneAdd I) N)) = ⊤ :=
    map_smul_top_eq_top I h
  have hbot : (⊤ : Submodule (Localization (oneAdd I))
      (LocalizedModule (oneAdd I) N)) = ⊥ := by
    refine eq_bot_of_le_smul_of_le_jacobson _ (map_oneAdd_le_jacobson I) ⊤
      Module.Finite.fg_top ?_
    rw [htop]
  have hsub : Subsingleton (LocalizedModule (oneAdd I) N) := by
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := by
      have hx' : x ∈ (⊤ : Submodule (Localization (oneAdd I))
          (LocalizedModule (oneAdd I) N)) := Submodule.mem_top
      rw [hbot] at hx'
      simpa using hx'
    have hy : y = 0 := by
      have hy' : y ∈ (⊤ : Submodule (Localization (oneAdd I))
          (LocalizedModule (oneAdd I) N)) := Submodule.mem_top
      rw [hbot] at hy'
      simpa using hy'
    rw [hx, hy]
  obtain ⟨s, hs⟩ := (subsingleton_localized_iff (oneAdd I)).1 hsub
  exact ⟨s, s.2, fun n => by simpa [Submonoid.smul_def] using hs n⟩

/-- Atiyah–Macdonald (2.5): if `𝔞` is contained in the Jacobson radical of `A` and `N` is a
finitely generated `A`-module with `𝔞N = N`, then `N = 0`.  This is the statement reproved in
Exercise 3.2 along the route above, so the determinant trick is not used. -/
theorem nakayama (I : Ideal A) {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) (h : I • (⊤ : Submodule A N) = ⊤) :
    Subsingleton N := by
  obtain ⟨x, hx, hxN⟩ := exists_oneAdd_forall_smul_eq_zero I h
  have hunit : IsUnit x := Ideal.isUnit_of_sub_one_mem_jacobson_bot x (hI hx)
  have hzero : ∀ a : N, a = 0 := by
    intro a
    obtain ⟨u, hu⟩ := hunit
    have h3 : (x * (↑u⁻¹ : A)) • a = a := by
      rw [← hu, ← Units.val_mul]
      simp
    calc a = (x * (↑u⁻¹ : A)) • a := h3.symm
      _ = (↑u⁻¹ : A) • (x • a) := by rw [mul_smul, smul_comm]
      _ = 0 := by rw [hxN a, smul_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- Atiyah–Macdonald, Exercise 3.2, all parts together. -/
theorem solution (I : Ideal A) {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] :
    (∀ x y : A, x ∈ oneAdd I → y ∈ oneAdd I → x * y ∈ oneAdd I) ∧
    (Ideal.map (algebraMap A (Localization (oneAdd I))) I ≤
      Ideal.jacobson (⊥ : Ideal (Localization (oneAdd I)))) ∧
    (Subsingleton (LocalizedModule (oneAdd I) N) ↔ ∃ s : A, s - 1 ∈ I ∧ ∀ n : N, s • n = 0) ∧
    (I • (⊤ : Submodule A N) = ⊤ → ∃ x : A, x - 1 ∈ I ∧ ∀ n : N, x • n = 0) ∧
    (I ≤ Ideal.jacobson (⊥ : Ideal A) → I • (⊤ : Submodule A N) = ⊤ → Subsingleton N) :=
  ⟨fun _ _ => oneAdd_mul_mem I, map_oneAdd_le_jacobson I,
    (subsingleton_localized_iff (oneAdd I)).trans
      ⟨fun ⟨s, hs⟩ => ⟨s, s.2, hs⟩, fun ⟨s, hs, hsn⟩ => ⟨⟨s, hs⟩, hsn⟩⟩,
    fun h => exists_oneAdd_forall_smul_eq_zero I h, fun hI h => nakayama I hI h⟩

end AtiyahMcdonald69.Ex_3_2
