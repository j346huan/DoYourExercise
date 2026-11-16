import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 5.31

## The statement in the book

Chapter 5 (*Integral Dependence and Valuations*), Exercise 31 (verbatim from the scan):

> Conversely, let Γ be a totally ordered abelian group (written additively), and let K be a
> field. A *valuation* of K with values in Γ is a mapping `v : K* → Γ` such that
> (1) `v(xy) = v(x) + v(y)`,
> (2) `v(x + y) ≥ min (v(x), v(y))`, for all `x, y ∈ K*`.
> Show that the set of elements `x ∈ K*` such that `v(x) ≥ 0` is a valuation ring of K. This
> ring is called the valuation ring of `v`, and the subgroup `v(K*)` of Γ is the value group
> of `v`. Thus the concepts of valuation ring and valuation are essentially equivalent.

## Formalisation choices (source audit)

* `K*` is `Kˣ` (`Units K`), `Γ` is an additively written totally ordered abelian group
  (`AddCommGroup Γ`, `LinearOrder Γ`, `IsOrderedAddMonoid Γ`; this is exactly the class of
  totally ordered abelian groups: an abelian group with a translation invariant linear order).
* **Ambiguity in axiom (2).** The book quantifies over `x, y ∈ K*` but then writes `v(x+y)`,
  which is undefined when `x + y = 0` (i.e. `x = -y`). The faithful reading adds the
  hypothesis `x + y ≠ 0`; this is what `IsValuation.map_add'` does. (The solution manual
  contains the same slip, printing `x ≠ y` where `x ≠ -y` is meant.)
* "the set of elements `x ∈ K*` such that `v(x) ≥ 0` is a valuation ring of K": A&M's
  Definition (Chapter 5, before 5.18) reads "let B be an integral domain, K its field of
  fractions; B is a valuation ring of K if, for each `x ≠ 0`, either `x ∈ B` or `x⁻¹ ∈ B`".
  So a faithful formalisation must produce
  (a) a subring `A ⊆ K` whose carrier is exactly `{x ∈ K* : v x ≥ 0} ∪ {0}`
      (`valuationSubring_coe`, `mem_valuationSubring_iff`),
  (b) the fact that `K` is the field of fractions of `A` (`instIsFractionRing`), and
  (c) the elementwise condition `x ∈ A ∨ x⁻¹ ∈ A` for `x ≠ 0` (`mem_or_inv_mem`),
  together with the intrinsic Mathlib notion `ValuationRing A` (`instValuationRing`).
* The last sentence of the exercise ("This ring is called the valuation ring of `v`, and the
  subgroup `v(K*)` of Γ is the value group of `v`") is also formalised: the units of `A` are
  exactly the elements of value `0` (`isUnit_iff`, `mem_unitSubgroup_iff_mem_and_inv_mem`), and
  `v` induces the ordered-group isomorphism `K*/A* ≃ v(K*)` (`valueGroupEquiv`,
  `valueGroupEquiv_apply`), with the order characterised by A&M's rule
  `x/y ∈ A ↔ v(x) ≥ v(y)` (`div_mem_iff`).
* Consistently with Proposition 5.18 (i), `A` is a local ring: `not_isUnit_iff` identifies the
  maximal ideal as the elements of positive value (together with `0`), and `isLocalRing`
  proves locality.  Non-vacuity is witnessed by the trivial valuation (`A = K`) and by the
  `p`-adic valuation on `ℚ` (`valuationRing_padic`, `two_mem_not_inv_mem`).
-/

namespace AtiyahMcdonald69.Ex_5_31

/- The context of the whole file is fixed once; a few elementary lemmas do not use every
instance, which is harmless here. -/
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K]
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-! ### The candidate set `{x ∈ K* : v x ≥ 0} ∪ {0}` -/

/-- The extension of a map `v : K* → Γ` to all of `K`, sending `0` to `0`. -/
noncomputable def ext (v : Kˣ → Γ) (x : K) : Γ :=
  letI := Classical.decEq K
  if h : x = 0 then 0 else v (Units.mk0 x h)

@[simp] lemma ext_zero (v : Kˣ → Γ) : ext v 0 = 0 := by
  rw [ext, dif_pos rfl]

lemma ext_of_ne (v : Kˣ → Γ) {x : K} (h : x ≠ 0) : ext v x = v (Units.mk0 x h) := by
  rw [ext, dif_neg h]

lemma ext_congr (v : Kˣ → Γ) {x y : K} (h : x = y) : ext v x = ext v y := by
  rw [h]

lemma ext_coe (v : Kˣ → Γ) (x : Kˣ) : ext v (x : K) = v x := by
  rw [ext_of_ne v x.ne_zero]
  exact congrArg v (Units.ext rfl)

lemma mk0_eq {x y : K} (h : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
    Units.mk0 x hx = Units.mk0 y hy := by
  subst h; rfl

lemma mk0_inv {x : K} (hx : x ≠ 0) {h : x⁻¹ ≠ 0} :
    Units.mk0 x⁻¹ h = (Units.mk0 x hx)⁻¹ := Units.ext rfl

lemma mk0_neg {x : K} (hx : x ≠ 0) {h : -x ≠ 0} :
    Units.mk0 (-x) h = -(Units.mk0 x hx) := Units.ext rfl

lemma mk0_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) {h : x * y ≠ 0} :
    Units.mk0 (x * y) h = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl

lemma mk0_one {h : (1 : K) ≠ 0} : Units.mk0 (1 : K) h = 1 := Units.ext rfl

lemma mk0_neg_one {h : (-1 : K) ≠ 0} : Units.mk0 (-1 : K) h = -1 := Units.ext rfl

/-- A valuation of the field `K` with values in the additively written totally ordered
abelian group `Γ`, in the sense of Atiyah–Macdonald, Chapter 5, Exercise 31. -/
structure IsValuation (v : Kˣ → Γ) : Prop where
  /-- Axiom (1): `v (x * y) = v x + v y`. -/
  map_mul' : ∀ x y : Kˣ, v (x * y) = v x + v y
  /-- Axiom (2): `v (x + y) ≥ min (v x) (v y)`. The hypothesis `x + y ≠ 0` is needed because
  `v` is only defined on `K*`. -/
  map_add' : ∀ (x y : Kˣ) (h : (x : K) + y ≠ 0), min (v x) (v y) ≤ v (Units.mk0 ((x : K) + y) h)

namespace IsValuation

variable {v : Kˣ → Γ}

lemma map_one (h : IsValuation v) : v 1 = 0 := by
  have h1 : v 1 = v 1 + v 1 := by
    have := h.map_mul' 1 1
    simpa using this
  have h2 : v 1 + 0 = v 1 + v 1 := by rw [add_zero]; exact h1
  exact (add_left_cancel h2).symm

lemma map_inv (h : IsValuation v) (x : Kˣ) : v x⁻¹ = - v x := by
  have h1 : v x + v x⁻¹ = 0 := by
    have h2 := h.map_mul' x x⁻¹
    rw [mul_inv_cancel, h.map_one] at h2
    exact h2.symm
  exact eq_neg_of_add_eq_zero_right h1

lemma map_neg_one (h : IsValuation v) : v (-1 : Kˣ) = 0 := by
  have h1 : v (-1 : Kˣ) + v (-1 : Kˣ) = 0 := by
    have h2 := h.map_mul' (-1 : Kˣ) (-1 : Kˣ)
    rw [show (-1 : Kˣ) * (-1) = 1 by ext; simp, h.map_one] at h2
    exact h2.symm
  rcases lt_trichotomy (v (-1 : Kˣ)) 0 with hlt | heq | hgt
  · have h2 : v (-1 : Kˣ) + v (-1 : Kˣ) < 0 := add_neg hlt hlt
    rw [h1] at h2
    exact absurd h2 (lt_irrefl 0)
  · exact heq
  · have h2 : 0 < v (-1 : Kˣ) + v (-1 : Kˣ) := add_pos hgt hgt
    rw [h1] at h2
    exact absurd h2 (lt_irrefl 0)

lemma map_neg (h : IsValuation v) (x : Kˣ) : v (-x) = v x := by
  have h1 : v (-x) = v (-1 : Kˣ) + v x := by
    rw [← h.map_mul' (-1 : Kˣ) x]
    congr 1
    ext
    simp
  rw [h1, h.map_neg_one, zero_add]

lemma ext_one (h : IsValuation v) : ext v 1 = 0 := by
  rw [ext_of_ne v one_ne_zero, mk0_one, h.map_one]

lemma ext_neg_one (h : IsValuation v) : ext v (-1 : K) = 0 := by
  rw [ext_of_ne v (neg_ne_zero.mpr one_ne_zero), mk0_neg_one, h.map_neg_one]

lemma ext_mul (h : IsValuation v) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ext v (x * y) = ext v x + ext v y := by
  rw [ext_of_ne v (mul_ne_zero hx hy), ext_of_ne v hx, ext_of_ne v hy,
    ← h.map_mul' (Units.mk0 x hx) (Units.mk0 y hy), mk0_mul hx hy]

lemma ext_neg (h : IsValuation v) (x : K) : ext v (-x) = ext v x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [ext_of_ne v (neg_ne_zero.mpr hx), ext_of_ne v hx,
      ← h.map_neg (Units.mk0 x hx), mk0_neg hx]

lemma ext_inv (h : IsValuation v) {x : K} (hx : x ≠ 0) :
    ext v x⁻¹ = - ext v x := by
  rw [ext_of_ne v (inv_ne_zero hx), ext_of_ne v hx, ← h.map_inv (Units.mk0 x hx), mk0_inv hx]

lemma ext_add (h : IsValuation v) {x y : K} (hxy : x + y ≠ 0) :
    min (ext v x) (ext v y) ≤ ext v (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    exact min_le_right _ _
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      exact min_le_left _ _
    · rw [ext_of_ne v hx, ext_of_ne v hy, ext_of_ne v hxy]
      simpa using h.map_add' (Units.mk0 x hx) (Units.mk0 y hy) hxy

end IsValuation

open IsValuation

/-! ### The valuation ring of `v` -/

variable {v : Kˣ → Γ}

lemma one_mem_set (h : IsValuation v) : (1 : K) ∈ {x : K | 0 ≤ ext v x} := by
  simp [h.ext_one]

lemma zero_mem_set (v : Kˣ → Γ) : (0 : K) ∈ {x : K | 0 ≤ ext v x} := by
  simp

lemma mul_mem_set (h : IsValuation v) {x y : K} (hx : 0 ≤ ext v x) (hy : 0 ≤ ext v y) :
    0 ≤ ext v (x * y) := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_mul]; simp
  by_cases hy0 : y = 0
  · rw [hy0, mul_zero]; simp
  rw [h.ext_mul hx0 hy0]
  exact add_nonneg hx hy

lemma add_mem_set (h : IsValuation v) {x y : K} (hx : 0 ≤ ext v x) (hy : 0 ≤ ext v y) :
    0 ≤ ext v (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy]; simp
  exact le_trans (le_min hx hy) (h.ext_add hxy)

lemma neg_mem_set (h : IsValuation v) {x : K} (hx : 0 ≤ ext v x) : 0 ≤ ext v (-x) := by
  rw [h.ext_neg]; exact hx

/-- **The ring of Exercise 5.31**: `{x ∈ K* : v x ≥ 0} ∪ {0}`, as a subring of `K`. -/
noncomputable def valuationSubring (v : Kˣ → Γ) (h : IsValuation v) : Subring K where
  carrier := {x : K | 0 ≤ ext v x}
  mul_mem' := fun hx hy => mul_mem_set h hx hy
  one_mem' := one_mem_set h
  add_mem' := fun hx hy => add_mem_set h hx hy
  zero_mem' := zero_mem_set v
  neg_mem' := fun hx => neg_mem_set h hx

@[simp] lemma mem_valuationSubring (h : IsValuation v) (x : K) :
    x ∈ valuationSubring v h ↔ 0 ≤ ext v x := Iff.rfl

lemma mem_valuationSubring_iff (h : IsValuation v) {x : K} (hx : x ≠ 0) :
    x ∈ valuationSubring v h ↔ 0 ≤ v (Units.mk0 x hx) := by
  rw [mem_valuationSubring, ext_of_ne v hx]

/-- The carrier of the constructed ring is literally the set of Atiyah–Macdonald Exercise
5.31: `{x ∈ K* : v x ≥ 0} ∪ {0}`. -/
theorem valuationSubring_coe (h : IsValuation v) :
    (valuationSubring v h : Set K) = {0} ∪ {x : K | ∃ hx : x ≠ 0, 0 ≤ v (Units.mk0 x hx)} := by
  ext x
  constructor
  · intro hx
    change 0 ≤ ext v x at hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl rfl
    · exact Or.inr ⟨hx0, by rwa [ext_of_ne v hx0] at hx⟩
  · rintro (rfl | ⟨hx0, hx⟩)
    · exact zero_mem_set v
    · change 0 ≤ ext v x
      rwa [ext_of_ne v hx0]

/-- Atiyah–Macdonald's condition for a valuation ring of `K`: for every `x ≠ 0`, either
`x` or `x⁻¹` lies in the ring. -/
theorem mem_or_inv_mem (h : IsValuation v) {x : K} (hx : x ≠ 0) :
    x ∈ valuationSubring v h ∨ x⁻¹ ∈ valuationSubring v h := by
  rcases le_total (v (Units.mk0 x hx)) 0 with hle | hge
  · refine Or.inr ?_
    rw [mem_valuationSubring_iff h (inv_ne_zero hx), mk0_inv hx, h.map_inv, neg_nonneg]
    exact hle
  · exact Or.inl ((mem_valuationSubring_iff h hx).mpr hge)

/-! ### `K` is the field of fractions of the constructed ring -/

/-- Atiyah–Macdonald's definition of a valuation ring of `K` presupposes that `K` is the field
of fractions of the ring; for the ring of Exercise 5.31 this holds because for `x ≠ 0` either
`x` or `x⁻¹` lies in it. -/
theorem instIsFractionRing (h : IsValuation v) : IsFractionRing (valuationSubring v h) K := by
  refine isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective ?_ ?_
  · intro x
    by_cases hx : x = 0
    · exact ⟨0, Or.inl (by simp [hx])⟩
    · rcases mem_or_inv_mem h hx with hx' | hx'
      · exact ⟨⟨x, hx'⟩, Or.inl rfl⟩
      · exact ⟨⟨x⁻¹, hx'⟩, Or.inr rfl⟩
  · exact Subtype.coe_injective

/-- **Exercise 5.31, main assertion (intrinsic form)**: the ring of `v` is a valuation ring,
i.e. for any two elements one divides the other. -/
theorem instValuationRing (h : IsValuation v) : ValuationRing (valuationSubring v h) := by
  refine @ValuationRing.mk (valuationSubring v h) _ _ ⟨fun a b => ?_⟩
  by_cases ha : a = 0
  · exact ⟨0, Or.inr (by rw [ha]; simp)⟩
  by_cases hb : b = 0
  · exact ⟨0, Or.inl (by rw [hb]; simp)⟩
  have ha0 : (a : K) ≠ 0 := fun h' => ha (Subtype.ext h')
  have hb0 : (b : K) ≠ 0 := fun h' => hb (Subtype.ext h')
  set z : K := (a : K) * (b : K)⁻¹ with hzdef
  have hz0 : z ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
  rcases mem_or_inv_mem h hz0 with hzA | hzinvA
  · refine ⟨⟨z, hzA⟩, Or.inr ?_⟩
    apply Subtype.ext
    show (b : K) * z = (a : K)
    rw [hzdef]
    field_simp
  · refine ⟨⟨z⁻¹, hzinvA⟩, Or.inl ?_⟩
    apply Subtype.ext
    show (a : K) * z⁻¹ = (b : K)
    rw [hzdef]
    field_simp

/-! ### Units and the value group -/

/-- The units of the valuation ring of `v` are exactly the elements of value `0`. -/
theorem isUnit_iff (h : IsValuation v) (x : valuationSubring v h) :
    IsUnit x ↔ (x : K) ≠ 0 ∧ ext v (x : K) = 0 := by
  constructor
  · intro hx
    obtain ⟨y, hxy, -⟩ := isUnit_iff_exists.mp hx
    have hxyK : (x : K) * (y : K) = 1 := by simpa using congrArg Subtype.val hxy
    have hx0 : (x : K) ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at hxyK; exact zero_ne_one hxyK
    have hy0 : (y : K) ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hxyK; exact zero_ne_one hxyK
    have hmul : ext v (x : K) + ext v (y : K) = 0 := by
      rw [← h.ext_mul hx0 hy0, hxyK, h.ext_one]
    have hle : ext v (x : K) ≤ 0 := by
      have hneg : ext v (x : K) = - ext v (y : K) := eq_neg_of_add_eq_zero_left hmul
      rw [hneg]
      exact neg_nonpos.mpr y.2
    exact ⟨hx0, le_antisymm hle x.2⟩
  · rintro ⟨hx0, hxv⟩
    have hxinv : (x : K)⁻¹ ∈ valuationSubring v h := by
      change 0 ≤ ext v (x : K)⁻¹
      rw [h.ext_inv hx0, hxv, neg_zero]
    refine isUnit_iff_exists.mpr ⟨⟨(x : K)⁻¹, hxinv⟩, ?_, ?_⟩
    · apply Subtype.ext
      show (x : K) * (x : K)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    · apply Subtype.ext
      show (x : K)⁻¹ * (x : K) = 1
      exact inv_mul_cancel₀ hx0

/-- The non-units of the valuation ring are exactly the elements of positive value (together
with `0`); this is the maximal ideal of the local ring `A`. -/
theorem not_isUnit_iff (h : IsValuation v) (x : valuationSubring v h) :
    ¬ IsUnit x ↔ (x : K) = 0 ∨ 0 < ext v (x : K) := by
  constructor
  · intro hx
    rcases eq_or_ne (x : K) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases lt_or_eq_of_le x.2 with hlt | heq
      · exact hlt
      · exact absurd ((isUnit_iff h x).mpr ⟨h0, heq.symm⟩) hx
  · rintro (h0 | hpos)
    · intro hunit
      exact ((isUnit_iff h x).mp hunit).1 h0
    · intro hunit
      exact (ne_of_gt hpos) ((isUnit_iff h x).mp hunit).2

/-- The valuation ring of `v` is a **local** ring (as it must be: valuation rings are local,
Atiyah–Macdonald Proposition 5.18 (i)). -/
theorem isLocalRing (h : IsValuation v) : IsLocalRing (valuationSubring v h) := by
  refine IsLocalRing.of_is_unit_or_is_unit_of_add_one ?_
  intro a b hab
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have ha0 : a ≠ 0 := by
    rintro rfl
    refine hb ?_
    rw [zero_add] at hab
    rw [hab]
    exact isUnit_one
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine ha ?_
    rw [add_zero] at hab
    rw [hab]
    exact isUnit_one
  have haK : (a : K) ≠ 0 := fun h' => ha0 (Subtype.ext h')
  have hbK : (b : K) ≠ 0 := fun h' => hb0 (Subtype.ext h')
  have hapos : 0 < ext v (a : K) := by
    rcases (not_isUnit_iff h a).mp ha with h0 | hpos
    · exact absurd h0 haK
    · exact hpos
  have hbpos : 0 < ext v (b : K) := by
    rcases (not_isUnit_iff h b).mp hb with h0 | hpos
    · exact absurd h0 hbK
    · exact hpos
  have hsum : (a : K) + (b : K) = 1 := by simpa using congrArg Subtype.val hab
  have hle : min (ext v (a : K)) (ext v (b : K)) ≤ ext v ((a : K) + (b : K)) :=
    h.ext_add (by rw [hsum]; exact one_ne_zero)
  rw [hsum] at hle
  have hpos : (0 : Γ) < ext v (1 : K) := lt_of_lt_of_le (lt_min hapos hbpos) hle
  rw [h.ext_one] at hpos
  exact lt_irrefl 0 hpos

/-- The value group of the valuation ring of `v`, as a subgroup of `K*`: the elements of
value `0`. -/
noncomputable def unitSubgroup (v : Kˣ → Γ) (h : IsValuation v) : Subgroup Kˣ where
  carrier := {x : Kˣ | v x = 0}
  mul_mem' := by
    intro x y hx hy
    show v (x * y) = 0
    rw [h.map_mul', hx, hy, add_zero]
  one_mem' := h.map_one
  inv_mem' := by
    intro x hx
    show v x⁻¹ = 0
    rw [h.map_inv, hx, neg_zero]

@[simp] lemma mem_unitSubgroup_iff (h : IsValuation v) (x : Kˣ) :
    x ∈ unitSubgroup v h ↔ v x = 0 := Iff.rfl

/-- The units of the valuation ring, intrinsically: an element of `K*` is a unit of the ring
iff it and its inverse both lie in the ring. -/
theorem mem_unitSubgroup_iff_mem_and_inv_mem (h : IsValuation v) (x : Kˣ) :
    x ∈ unitSubgroup v h ↔
      (x : K) ∈ valuationSubring v h ∧ (x : K)⁻¹ ∈ valuationSubring v h := by
  rw [mem_unitSubgroup_iff]
  constructor
  · intro hx
    constructor
    · change 0 ≤ ext v (x : K); rw [ext_coe v, hx]
    · change 0 ≤ ext v (x : K)⁻¹
      rw [h.ext_inv x.ne_zero, ext_coe v, hx, neg_zero]
  · rintro ⟨h1, h2⟩
    have h1' : 0 ≤ v x := by rw [← ext_coe v x]; exact h1
    have h2' : 0 ≤ v x⁻¹ := by
      have h2'' : 0 ≤ ext v ((x : K)⁻¹) := h2
      rw [← Units.val_inv_eq_inv_val, ext_coe v x⁻¹] at h2''
      exact h2''
    rw [h.map_inv] at h2'
    exact le_antisymm (neg_nonneg.mp h2') h1'

/-- `v` viewed as a homomorphism from `K*` to the multiplicative copy of `Γ`. -/
noncomputable def valHom (v : Kˣ → Γ) (h : IsValuation v) : Kˣ →* Multiplicative Γ where
  toFun x := Multiplicative.ofAdd (v x)
  map_one' := by rw [h.map_one]; rfl
  map_mul' x y := by rw [h.map_mul']; rfl

@[simp] lemma valHom_apply (h : IsValuation v) (x : Kˣ) :
    valHom v h x = Multiplicative.ofAdd (v x) := rfl

lemma ker_valHom (h : IsValuation v) : (valHom v h).ker = unitSubgroup v h := by
  ext x
  rw [MonoidHom.mem_ker, valHom_apply, mem_unitSubgroup_iff]
  constructor
  · intro hx
    have := congrArg Multiplicative.toAdd hx
    simpa using this
  · intro hx
    rw [hx]
    rfl

/-- **The value group `v(K*)`**: `K*/A* ≅ v(K*)`, the first isomorphism theorem applied to
`v`. -/
noncomputable def valueGroupEquiv (h : IsValuation v) :
    Kˣ ⧸ unitSubgroup v h ≃* (valHom v h).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_valHom h).symm).trans
    (QuotientGroup.quotientKerEquivRange (valHom v h))

/-- The value group `v(K*)` of Exercise 5.31 is exactly the range of `v`. -/
theorem ofAdd_mem_range_iff (h : IsValuation v) (γ : Γ) :
    Multiplicative.ofAdd γ ∈ (valHom v h).range ↔ ∃ x : Kˣ, v x = γ := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    rw [valHom_apply] at hx
    exact ⟨x, Multiplicative.ofAdd.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- The class of `x ∈ K*` in `K*/A*` is mapped by the value-group isomorphism to `v(x)`. -/
theorem valueGroupEquiv_apply (h : IsValuation v) (x : Kˣ) :
    ((valueGroupEquiv h (QuotientGroup.mk x) : (valHom v h).range) : Multiplicative Γ)
      = Multiplicative.ofAdd (v x) := by
  simp only [valueGroupEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivRange,
    QuotientGroup.rangeKerLift]
  rfl

/-- Atiyah–Macdonald's order rule: `x/y ∈ A` exactly when `v(x) ≥ v(y)`; this says that the
isomorphism `K*/A* ≅ v(K*)` is an isomorphism of ordered groups. -/
theorem div_mem_iff (h : IsValuation v) (x y : Kˣ) :
    ((x / y : Kˣ) : K) ∈ valuationSubring v h ↔ v y ≤ v x := by
  have hne : ((x / y : Kˣ) : K) ≠ 0 := by
    rw [Units.val_div_eq_div_val]; exact div_ne_zero x.ne_zero y.ne_zero
  have hval : v (Units.mk0 ((x / y : Kˣ) : K) hne) = v x - v y := by
    rw [show Units.mk0 ((x / y : Kˣ) : K) hne = x / y from Units.ext rfl,
      div_eq_mul_inv, h.map_mul', h.map_inv]
    abel
  rw [mem_valuationSubring_iff h hne, hval, sub_nonneg]

/-! ### Consistency checks: non-vacuous examples -/

/-- The trivial valuation: `v x = 0` for all `x ∈ K*`. Its valuation ring is `K` itself, so the
hypotheses of Exercise 5.31 are satisfiable. -/
theorem trivialValuation (K : Type*) [Field K] (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : IsValuation (fun _ : Kˣ => (0 : Γ)) where
  map_mul' _ _ := (add_zero 0).symm
  map_add' _ _ _ := le_of_eq (min_self 0)

theorem valuationSubring_trivial :
    valuationSubring (fun _ : Kˣ => (0 : Γ)) (trivialValuation K Γ) = ⊤ := by
  ext x
  rw [mem_valuationSubring]
  simp [ext]

/-- A non-trivial example: the `p`-adic valuation on `ℚ` is a valuation of `ℚ` with values in
`ℤ` in the sense of Exercise 5.31 (note that Mathlib's `padicValRat.min_le_padicValRat_add`
carries exactly the side condition `q + r ≠ 0` discussed in the header). -/
theorem isValuation_padic (p : ℕ) [Fact p.Prime] :
    IsValuation (fun u : ℚˣ => padicValRat p (u : ℚ)) where
  map_mul' x y := by
    rw [Units.val_mul, padicValRat.mul x.ne_zero y.ne_zero]
  map_add' x y h := padicValRat.min_le_padicValRat_add h

/-- Consequently the `p`-adic valuation ring of `ℚ` — the localisation of `ℤ` at `(p)` — is a
valuation ring. -/
theorem valuationRing_padic (p : ℕ) [Fact p.Prime] :
    ValuationRing (valuationSubring (fun u : ℚˣ => padicValRat p (u : ℚ)) (isValuation_padic p)) :=
  instValuationRing _

/-- Concretely, the `2`-adic valuation ring of `ℚ` is a proper subring of `ℚ`: it contains
`2` but not `1/2` (i.e. `2` is a non-unit there, as expected for the localisation `ℤ_(2)`). -/
theorem two_mem_not_inv_mem :
    (2 : ℚ) ∈ valuationSubring (fun u : ℚˣ => padicValRat 2 (u : ℚ)) (isValuation_padic 2) ∧
      (1 / 2 : ℚ) ∉ valuationSubring (fun u : ℚˣ => padicValRat 2 (u : ℚ))
        (isValuation_padic 2) := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat_of_nat (p := 2) 2
    rw [padicValNat_self] at h
    simpa using h.symm
  have hhalf : padicValRat 2 (1 / 2 : ℚ) = -1 := by
    have h : (1 / 2 : ℚ) = (2 : ℚ)⁻¹ := by norm_num
    rw [h, padicValRat.inv, h2]
  constructor
  · rw [mem_valuationSubring_iff _ (by norm_num : (2 : ℚ) ≠ 0)]
    show 0 ≤ padicValRat 2 (2 : ℚ)
    rw [h2]; norm_num
  · rw [mem_valuationSubring_iff _ (by norm_num : (1 / 2 : ℚ) ≠ 0)]
    show ¬ (0 ≤ padicValRat 2 (1 / 2 : ℚ))
    rw [hhalf]; norm_num

/-- **Atiyah–Macdonald, Exercise 5.31.** Let `Γ` be a totally ordered abelian group and `K` a
field, and let `v : K* → Γ` satisfy `v(xy) = v(x) + v(y)` and
`v(x + y) ≥ min (v(x), v(y))`. Then `{x ∈ K* : v(x) ≥ 0} ∪ {0}` is a valuation ring of `K`:
a subring of `K` with field of fractions `K` in which every non-zero element or its inverse
lies, and it is a valuation ring in the intrinsic sense. -/
theorem solution (v : Kˣ → Γ) (h : IsValuation v) :
    ∃ A : Subring K,
      (A : Set K) = {0} ∪ {x : K | ∃ hx : x ≠ 0, 0 ≤ v (Units.mk0 x hx)} ∧
      (∀ x : K, x ≠ 0 → x ∈ A ∨ x⁻¹ ∈ A) ∧ IsFractionRing A K ∧ ValuationRing A :=
  ⟨valuationSubring v h, valuationSubring_coe h, fun _ hx => mem_or_inv_mem h hx,
    instIsFractionRing h, instValuationRing h⟩

end AtiyahMcdonald69.Ex_5_31
