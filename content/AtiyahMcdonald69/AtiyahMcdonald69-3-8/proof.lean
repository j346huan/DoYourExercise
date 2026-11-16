/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 3.8.

Let `S, T` be multiplicatively closed subsets of a commutative ring `A` with `S ⊆ T`, and let
`φ : S⁻¹A → T⁻¹A` be the homomorphism sending `a/s` to `a/s`.  We formalize that the following
five conditions are equivalent:

(i) `φ` is bijective;
(ii) for each `t ∈ T`, `t/1` is a unit of `S⁻¹A`;
(iii) for each `t ∈ T` there exists `x ∈ A` such that `xt ∈ S`;
(iv) `T` is contained in the saturation of `S` (Exercise 3.7);
(v) every prime ideal which meets `T` also meets `S`.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_3_8

open Submonoid

variable {A : Type*} [CommRing A]

/-! ### The canonical map `S⁻¹A → T⁻¹A` -/

lemma le_comap_id (S T : Submonoid A) (h : S ≤ T) : S ≤ T.comap (RingHom.id A) :=
  fun _ hx => by simpa using h hx

/-- For multiplicatively closed subsets `S ⊆ T` of `A`, the canonical ring homomorphism
`φ : S⁻¹A → T⁻¹A` which maps `a/s` to `a/s`. -/
noncomputable def locMap (S T : Submonoid A) (h : S ≤ T) :
    Localization S →+* Localization T :=
  IsLocalization.map (Localization T) (RingHom.id A) (le_comap_id S T h)

/-- `φ` extends the structure maps: `φ(a/1) = a/1`. -/
@[simp]
lemma locMap_algebraMap (S T : Submonoid A) (h : S ≤ T) (a : A) :
    locMap S T h (algebraMap A (Localization S) a) = algebraMap A (Localization T) a := by
  simp [locMap]

/-- On fractions the map `φ` is literally the identity `a/s ↦ a/s`. -/
lemma locMap_mk' (S T : Submonoid A) (h : S ≤ T) (a : A) (s : S) :
    locMap S T h (IsLocalization.mk' (Localization S) a s) =
      IsLocalization.mk' (Localization T) a ⟨s.1, h s.2⟩ := by
  rw [locMap, IsLocalization.map_mk']
  simp

/-! ### The five conditions -/

/-- Condition (i): `φ` is bijective. -/
def Cond1 (S T : Submonoid A) (h : S ≤ T) : Prop := Function.Bijective (locMap S T h)

/-- Condition (ii): for each `t ∈ T`, `t/1` is a unit of `S⁻¹A`. -/
def Cond2 (S T : Submonoid A) : Prop := ∀ t ∈ T, IsUnit (algebraMap A (Localization S) t)

/-- Condition (iii): for each `t ∈ T` there exists `x ∈ A` with `xt ∈ S`. -/
def Cond3 (S T : Submonoid A) : Prop := ∀ t ∈ T, ∃ x : A, x * t ∈ S

/-- Condition (iv): `T` is contained in the saturation of `S`. -/
def Cond4 (S T : Submonoid A) : Prop := T ≤ S.saturation.toSubmonoid

/-- Condition (v): every prime ideal meeting `T` also meets `S`. -/
def Cond5 (S T : Submonoid A) : Prop :=
  ∀ p : Ideal A, p.IsPrime → (∃ t ∈ T, t ∈ p) → ∃ s ∈ S, s ∈ p

/-! ### Exercise 3.7: the saturation of `S` as the complement of the union of the
prime ideals avoiding `S` -/

/-- The saturation of a multiplicatively closed set `S` consists of the elements which lie in no
prime ideal avoiding `S`; this is the description of the saturation given in Exercise 3.7. -/
theorem mem_saturation_iff_forall_not_mem_of_isPrime (S : Submonoid A) (a : A) :
    a ∈ S.saturation ↔ ∀ p : Ideal A, p.IsPrime → Disjoint (S : Set A) (p : Set A) → a ∉ p := by
  constructor
  · intro ha p _ hdis hap
    obtain ⟨x, hx⟩ := Submonoid.mem_saturation_iff'.mp ha
    exact (Set.disjoint_left.mp hdis hx) (p.mul_mem_left x hap)
  · intro h
    by_contra ha
    have hdis : Disjoint ((Ideal.span {a} : Ideal A) : Set A) (S : Set A) := by
      rw [Set.disjoint_left]
      intro y hy hyS
      have hy' : y ∈ Ideal.span {a} := hy
      obtain ⟨c, rfl⟩ := (Ideal.mem_span_singleton' (x := y) (y := a)).mp hy'
      exact ha (Submonoid.mem_saturation_iff'.mpr ⟨c, hyS⟩)
    obtain ⟨p, hp, hle, hpd⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {a}) S hdis
    exact h p hp hpd.symm (hle (Ideal.subset_span (Set.mem_singleton a)))

/-- Exercise 3.7: an element `t` lies in the saturation of `S` exactly when a multiple of `t`
belongs to `S`. -/
theorem mem_saturation_iff_exists_mul_mem (S : Submonoid A) (t : A) :
    t ∈ S.saturation ↔ ∃ x : A, x * t ∈ S :=
  Submonoid.mem_saturation_iff'

/-! ### (i) ⟺ (ii) -/

/-- Condition (i) is equivalent to condition (ii). -/
theorem cond1_iff_cond2 (S T : Submonoid A) (hST : S ≤ T) :
    Cond1 S T hST ↔ Cond2 S T := by
  constructor
  · rintro ⟨hinj, hsurj⟩ t ht
    have hunit : IsUnit (algebraMap A (Localization T) t) :=
      IsLocalization.map_units (Localization T) ⟨t, ht⟩
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
    obtain ⟨b, hb⟩ := hsurj v
    have h1 : locMap S T hST (algebraMap A (Localization S) t * b) = locMap S T hST 1 := by
      rw [map_mul, map_one, hb, locMap_algebraMap, hv]
    have h2 : algebraMap A (Localization S) t * b = 1 := hinj h1
    exact isUnit_iff_exists_inv.mpr ⟨b, h2⟩
  · intro hunits
    have hψ : ∀ a : A, IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
          (fun t => hunits t t.2) (algebraMap A (Localization T) a) =
        algebraMap A (Localization S) a :=
      fun a => IsLocalization.lift_eq _ a
    have hcomp₁ : (IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
          (fun t => hunits t t.2)).comp (locMap S T hST) = RingHom.id (Localization S) := by
      refine IsLocalization.ringHom_ext (M := S) (RingHom.ext fun a => ?_)
      simp
    have hcomp₂ : (locMap S T hST).comp (IsLocalization.lift (M := T)
          (g := algebraMap A (Localization S)) (fun t => hunits t t.2)) =
        RingHom.id (Localization T) := by
      refine IsLocalization.ringHom_ext (M := T) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, RingHom.id_apply, hψ, locMap_algebraMap]
    constructor
    · intro x y hxy
      have h := congrArg (IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
        (fun t => hunits t t.2)) hxy
      have hx : IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
          (fun t => hunits t t.2) ((locMap S T hST) x) = x := RingHom.congr_fun hcomp₁ x
      have hy : IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
          (fun t => hunits t t.2) ((locMap S T hST) y) = y := RingHom.congr_fun hcomp₁ y
      exact hx.symm.trans (h.trans hy)
    · intro y
      refine ⟨IsLocalization.lift (M := T) (g := algebraMap A (Localization S))
        (fun t => hunits t t.2) y, ?_⟩
      exact RingHom.congr_fun hcomp₂ y

/-! ### (ii) ⟺ (iii) -/

/-- Condition (ii) is equivalent to condition (iii). -/
theorem cond2_iff_cond3 (S T : Submonoid A) : Cond2 S T ↔ Cond3 S T := by
  refine forall₂_congr fun t _ => ?_
  rw [IsLocalization.algebraMap_isUnit_iff (M := S)]
  constructor
  · rintro ⟨m, hm, c, hc⟩
    refine ⟨c, ?_⟩
    rw [mul_comm, ← hc]
    exact hm
  · rintro ⟨x, hx⟩
    exact ⟨x * t, hx, x, mul_comm x t⟩

/-! ### (iii) ⟺ (iv) -/

/-- Condition (iii) is equivalent to condition (iv). -/
theorem cond3_iff_cond4 (S T : Submonoid A) : Cond3 S T ↔ Cond4 S T := by
  constructor
  · intro h t ht
    exact Submonoid.mem_saturation_iff'.mpr (h t ht)
  · intro h t ht
    exact Submonoid.mem_saturation_iff'.mp (h ht)

/-! ### (iv) ⟺ (v) -/

/-- Condition (iv) is equivalent to condition (v). -/
theorem cond4_iff_cond5 (S T : Submonoid A) : Cond4 S T ↔ Cond5 S T := by
  constructor
  · intro hT p hp
    rintro ⟨t, htT, htp⟩
    by_contra hcon
    have hdis : Disjoint (S : Set A) (p : Set A) := by
      rw [Set.disjoint_left]
      intro s hsS hsp
      exact hcon ⟨s, hsS, hsp⟩
    exact (mem_saturation_iff_forall_not_mem_of_isPrime S t).mp (hT htT) p hp hdis htp
  · intro hv t htT
    rw [SaturatedSubmonoid.mem_toSubmonoid, mem_saturation_iff_forall_not_mem_of_isPrime]
    intro p hp hdis htp
    obtain ⟨s, hsS, hsp⟩ := hv p hp ⟨t, htT, htp⟩
    exact Set.disjoint_left.mp hdis hsS hsp


/-- The saturation is monotone in the multiplicatively closed set. -/
lemma saturation_mono {S T : Submonoid A} (h : S ≤ T) : S.saturation ≤ T.saturation :=
  (Submonoid.gc_saturation A).monotone_l h

/-- Conditions (i)–(iv) are further equivalent to the equality of the saturations of `S` and `T`:
this is the conceptual content of the exercise, that `φ` is an isomorphism exactly when `S` and
`T` generate the same localization. -/
theorem cond4_iff_saturation_eq (S T : Submonoid A) (hST : S ≤ T) :
    Cond4 S T ↔ S.saturation = T.saturation := by
  constructor
  · intro h
    exact le_antisymm (saturation_mono hST) (Submonoid.saturation_le_iff_le.mpr h)
  · intro h t ht
    have ht' : t ∈ T.saturation.toSubmonoid := Submonoid.le_toSubmonoid_saturation ht
    simpa [h] using ht'

/-! ### Non-vacuity of the conditions

The conditions of the exercise are not trivially true: over `ℤ` with `S = {1}` (the trivial
multiplicatively closed set) and `T` the powers of `2`, condition (iii) fails, since `x * 2 ∈ {1}`
has no solution `x ∈ ℤ`.  Note also that in condition (iii) one cannot ask for `x ∈ S`: with
`A = ℤ`, `S = {4ⁿ}` and `T = {2ⁿ}` condition (iii) holds, but `x * 2 ∈ S` forces `x = 2²ⁿ⁻¹ ∉ S`. -/

example : ¬ Cond3 (⊥ : Submonoid ℤ) (Submonoid.powers 2) := by
  intro h
  obtain ⟨x, hx⟩ := h 2 (Submonoid.mem_powers 2)
  have hx' : x * 2 = 1 := by simpa using hx
  omega


/-! ### The exercise -/

/-- **Atiyah–Macdonald, Exercise 3.8.**  For multiplicatively closed subsets `S ⊆ T` of a
commutative ring `A`, with `φ : S⁻¹A → T⁻¹A` the canonical homomorphism `a/s ↦ a/s`, the five
conditions (i)–(v) of the exercise are equivalent. -/
theorem solution (S T : Submonoid A) (hST : S ≤ T) :
    [Cond1 S T hST, Cond2 S T, Cond3 S T, Cond4 S T, Cond5 S T].TFAE := by
  tfae_have 1 ↔ 2 := cond1_iff_cond2 S T hST
  tfae_have 2 ↔ 3 := cond2_iff_cond3 S T
  tfae_have 3 ↔ 4 := cond3_iff_cond4 S T
  tfae_have 4 ↔ 5 := cond4_iff_cond5 S T
  tfae_finish


/-- All remaining pairwise implications of the exercise, obtained by composing the four links
(i) ⟺ (ii) ⟺ (iii) ⟺ (iv) ⟺ (v). -/
theorem cond1_iff_cond3 (S T : Submonoid A) (hST : S ≤ T) : Cond1 S T hST ↔ Cond3 S T :=
  (cond1_iff_cond2 S T hST).trans (cond2_iff_cond3 S T)

theorem cond1_iff_cond4 (S T : Submonoid A) (hST : S ≤ T) : Cond1 S T hST ↔ Cond4 S T :=
  (cond1_iff_cond3 S T hST).trans (cond3_iff_cond4 S T)

theorem cond1_iff_cond5 (S T : Submonoid A) (hST : S ≤ T) : Cond1 S T hST ↔ Cond5 S T :=
  (cond1_iff_cond4 S T hST).trans (cond4_iff_cond5 S T)

theorem cond2_iff_cond4 (S T : Submonoid A) : Cond2 S T ↔ Cond4 S T :=
  (cond2_iff_cond3 S T).trans (cond3_iff_cond4 S T)

theorem cond2_iff_cond5 (S T : Submonoid A) : Cond2 S T ↔ Cond5 S T :=
  (cond2_iff_cond4 S T).trans (cond4_iff_cond5 S T)

theorem cond3_iff_cond5 (S T : Submonoid A) : Cond3 S T ↔ Cond5 S T :=
  (cond3_iff_cond4 S T).trans (cond4_iff_cond5 S T)


/-- A genuine instance of the theorem: over `ℤ` with `S = {4ⁿ} ⊆ T = {2ⁿ}` the localization map
`ℤ[1/4] → ℤ[1/2]` is bijective, because `4 = 2 · 2` shows `2 ∈ \bar S`. -/
example : Cond1 (Submonoid.powers (4 : ℤ)) (Submonoid.powers (2 : ℤ))
    (by rw [Submonoid.powers_le]; exact ⟨2, by norm_num⟩) :=
  (cond1_iff_cond4 _ _ _).mpr <| by
    intro t ht
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff t 2).mp ht
    refine Submonoid.mem_saturation_iff'.mpr ⟨2 ^ n, ?_⟩
    rw [Submonoid.mem_powers_iff]
    exact ⟨n, by rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]⟩

end AtiyahMcdonald69.Ex_3_8
