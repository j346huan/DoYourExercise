/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison-Wesley, 1969),
Chapter 5 (Integral dependence and valuations), Exercise 30.

## The statement in the book

"Let A be a valuation ring of a field K. The group U of units of A is a subgroup of the
multiplicative group K* of K. Let Γ = K*/U. If ξ ≥ η ∈ Γ are represented by x, y ∈ K,
define ξ ≥ η to mean xy⁻¹ ∈ A. Show that this defines a total ordering on Γ which is
compatible with the group structure (i.e. ξ ≥ η ⟹ ξω ≥ ηω for all ω ∈ Γ). In other words,
Γ is a totally ordered abelian group. It is called the value group of A. Let v : K* → Γ be
the canonical homomorphism. Show that v(x + y) ≥ min (v(x), v(y)) for all x, y ∈ K*."

## Source audit

* "valuation ring of K" is used in the book's own sense (Chapter 5, p. 65): a subring `A` of
  `K` such that for every `x ≠ 0` in `K` either `x ∈ A` or `x⁻¹ ∈ A`.  No other structure on
  `A` is assumed; this is the class `IsValuationRingOf` below, and the equivalence with the
  book's wording is `mem_or_inv_mem`.
* The book writes "represented by x, y ∈ K", but representatives live in `K* = Kˣ`, as the
  preceding sentence says (`Γ = K*/U`); `0` has no class in `Γ`.
* The book's last sentence says "for all x, y ∈ K*", yet `v` is only defined on `K*`: if
  `x + y = 0` then `v(x + y)` denotes nothing.  The faithful reading needs `x + y ≠ 0`; that
  is `valuation_add_ge_min`.  The convention `v 0 = ⊤` repairs the statement for *all*
  `x, y ∈ K`, and that repair is also formalized (`valuationWithTop_add_ge_min`).  These are
  the only two imprecisions; nothing else in the exercise needs repair.
* In the current Mathlib the bundled class `LinearOrderedCommGroup` no longer exists: a
  linearly ordered commutative group is `CommGroup` + `LinearOrder` + `IsOrderedMonoid`.  The
  instances below are exactly the book's "Γ is a totally ordered abelian group", and
  `mul_le_mul_left_of_le` is the book's compatibility condition `ξ ≥ η ⟹ ξω ≥ ηω`.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace AtiyahMcdonald69.Ex_5_30

variable {K : Type u} [Field K]

/-! ### The subgroup of units of a subring of a field -/

/-- The group `U` of units of the subring `A` of the field `K`, regarded as a subgroup of
`Kˣ` via `Aˣ → Kˣ`. -/
def unitSubgroup (A : Subring K) : Subgroup Kˣ :=
  (Units.map A.subtype.toMonoidHom).range

/-- An element of `Kˣ` is a unit of `A` if and only if it and its inverse lie in `A`. -/
theorem mem_unitSubgroup_iff (A : Subring K) {u : Kˣ} :
    u ∈ unitSubgroup A ↔ (u : K) ∈ A ∧ ((u : K)⁻¹) ∈ A := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Units.coe_map]; exact (a : A).2
    · rw [← Units.val_inv_eq_inv_val, ← map_inv, Units.coe_map]
      exact ((a⁻¹ : Aˣ) : A).2
  · rintro ⟨h1, h2⟩
    have h0 : (u : K) ≠ 0 := Units.ne_zero u
    refine MonoidHom.mem_range.mpr ⟨Units.mk ⟨(u : K), h1⟩ ⟨((u : K)⁻¹), h2⟩ ?_ ?_, ?_⟩
    · ext; exact mul_inv_cancel₀ h0
    · ext; exact inv_mul_cancel₀ h0
    · ext; rfl

/-! ### The value group `Γ = Kˣ/U` and the canonical homomorphism `v` -/

/-- The value group `Γ = K*/U` of the valuation ring `A`. -/
abbrev valueGroup (A : Subring K) : Type u := Kˣ ⧸ unitSubgroup A

/-- The canonical homomorphism `v : K* → Γ = K*/U`. -/
def valuation (A : Subring K) : Kˣ →* valueGroup A :=
  QuotientGroup.mk' (unitSubgroup A)

theorem valuation_apply (A : Subring K) (x : Kˣ) :
    valuation A x = QuotientGroup.mk x := rfl

/-- `v` is surjective: every class in `Γ` has a representative in `K*`. -/
theorem valuation_surjective (A : Subring K) : Function.Surjective (valuation A) :=
  QuotientGroup.mk'_surjective (unitSubgroup A)

/-- The kernel of `v` is `U`: `v x = 1` iff `x` is a unit of `A`. -/
theorem valuation_eq_one_iff (A : Subring K) {x : Kˣ} :
    valuation A x = 1 ↔ (x : K) ∈ A ∧ ((x : K)⁻¹) ∈ A := by
  rw [valuation_apply, QuotientGroup.eq_one_iff, mem_unitSubgroup_iff]

/-! ### Representatives

Two units of `K` have the same image in `Γ` iff one is the other multiplied by a unit of `A`
(that is the content of the definition of `Γ = K*/U`).  The lemmas below transport
membership in `A` between representatives, which is what makes the order well defined. -/

theorem exists_mul_unit_of_valuation_eq (A : Subring K) {x x' : Kˣ}
    (h : valuation A x = valuation A x') : ∃ z ∈ unitSubgroup A, x * z = x' :=
  (QuotientGroup.mk'_eq_mk' (unitSubgroup A)).mp h

/-- Two representatives of the same class either both lie in `A` or neither does. -/
theorem coe_mem_iff_of_valuation_eq (A : Subring K) {x x' : Kˣ}
    (h : valuation A x = valuation A x') : ((x : K) ∈ A ↔ (x' : K) ∈ A) := by
  obtain ⟨z, hz, rfl⟩ := exists_mul_unit_of_valuation_eq A h
  obtain ⟨hzA, hzA'⟩ := (mem_unitSubgroup_iff A).mp hz
  rw [Units.val_mul]
  refine ⟨fun hx => A.mul_mem hx hzA, fun hx => ?_⟩
  have h' : (x : K) = (x : K) * (z : K) * (z : K)⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero z), mul_one]
  rw [h']
  exact A.mul_mem hx hzA'

/-- Replacing the denominator by another representative does not change whether
`y / x ∈ A`. -/
theorem div_mem_congr_left (A : Subring K) {x x' : Kˣ}
    (h : valuation A x = valuation A x') (y : Kˣ) :
    (y : K) * (x : K)⁻¹ ∈ A ↔ (y : K) * (x' : K)⁻¹ ∈ A := by
  obtain ⟨z, hz, rfl⟩ := exists_mul_unit_of_valuation_eq A h
  obtain ⟨hzA, hzA'⟩ := (mem_unitSubgroup_iff A).mp hz
  have key : (y : K) * (((x * z : Kˣ) : K))⁻¹ = (y : K) * (x : K)⁻¹ * (z : K)⁻¹ := by
    rw [Units.val_mul, mul_inv_rev]
    ring
  rw [key]
  refine ⟨fun hmem => A.mul_mem hmem hzA', fun hmem => ?_⟩
  have h' : (y : K) * (x : K)⁻¹ = (y : K) * (x : K)⁻¹ * (z : K)⁻¹ * (z : K) := by
    rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero z), mul_one]
  rw [h']
  exact A.mul_mem hmem hzA

/-- Replacing the numerator by another representative does not change whether
`y / x ∈ A`. -/
theorem div_mem_congr_right (A : Subring K) {y y' : Kˣ}
    (h : valuation A y = valuation A y') (x : Kˣ) :
    (y : K) * (x : K)⁻¹ ∈ A ↔ (y' : K) * (x : K)⁻¹ ∈ A := by
  obtain ⟨z, hz, rfl⟩ := exists_mul_unit_of_valuation_eq A h
  obtain ⟨hzA, hzA'⟩ := (mem_unitSubgroup_iff A).mp hz
  have key : (y : K) * (z : K) * (x : K)⁻¹ = (y : K) * (x : K)⁻¹ * (z : K) := by ring
  rw [Units.val_mul, key]
  refine ⟨fun hmem => A.mul_mem hmem hzA, fun hmem => ?_⟩
  have h' : (y : K) * (x : K)⁻¹ = (y : K) * (x : K)⁻¹ * (z : K) * (z : K)⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero z), mul_one]
  rw [h']
  exact A.mul_mem hmem hzA'

/-! ### The order on `Γ`

`ξ ≥ η` means `x y⁻¹ ∈ A` for representatives `x` of `ξ`, `y` of `η`. -/

/-- `ξ ≥ η` for `ξ, η ∈ Γ` means `x y⁻¹ ∈ A` for representatives `x` of `ξ`, `y` of `η`. -/
def le (A : Subring K) (ξ η : valueGroup A) : Prop :=
  ∃ x y : Kˣ, valuation A x = ξ ∧ valuation A y = η ∧ (y : K) * (x : K)⁻¹ ∈ A

instance (A : Subring K) : LE (valueGroup A) := ⟨le A⟩

/-- The defining property of the order, in terms of the canonical map `v`. -/
theorem valuation_le_valuation_iff (A : Subring K) {x y : Kˣ} :
    valuation A x ≤ valuation A y ↔ (y : K) * (x : K)⁻¹ ∈ A := by
  refine ⟨?_, fun h => ⟨x, y, rfl, rfl, h⟩⟩
  rintro ⟨x', y', hx, hy, hmem⟩
  exact (div_mem_congr_left A hx y).mp ((div_mem_congr_right A hy x').mp hmem)

/-- The book's formulation: `ξ ≥ η` iff `x y⁻¹ ∈ A` for representatives `x`, `y`. -/
theorem valuation_ge_valuation_iff (A : Subring K) {x y : Kˣ} :
    valuation A x ≥ valuation A y ↔ (x : K) * (y : K)⁻¹ ∈ A :=
  valuation_le_valuation_iff A

/-- The order records membership in `A`: `v x ≥ 1` iff `x ∈ A` (so `A` is exactly the
valuation ring of `v`, cf. Exercise 31).  This pins the orientation of the order to the
book's definition. -/
theorem one_le_valuation_iff (A : Subring K) {x : Kˣ} :
    1 ≤ valuation A x ↔ (x : K) ∈ A := by
  rw [← map_one (valuation A), valuation_le_valuation_iff]
  simp

/-- The relation is reflexive, independently of any hypothesis on `A`. -/
theorem order_refl (A : Subring K) (ξ : valueGroup A) : ξ ≤ ξ := by
  obtain ⟨x, rfl⟩ := valuation_surjective A ξ
  exact ⟨x, x, rfl, rfl, by rw [mul_inv_cancel₀ (Units.ne_zero x)]; exact A.one_mem⟩

/-- The relation is transitive, independently of any hypothesis on `A`. -/
theorem order_trans (A : Subring K) {ξ η θ : valueGroup A} (h1 : ξ ≤ η) (h2 : η ≤ θ) :
    ξ ≤ θ := by
  obtain ⟨x, y, rfl, hy, hxy⟩ := h1
  obtain ⟨y', z, hy', hz, hyz⟩ := h2
  have hyy' : valuation A y = valuation A y' := by rw [hy, hy']
  have h1' : (y' : K) * (x : K)⁻¹ ∈ A := (div_mem_congr_right A hyy' x).mp hxy
  refine ⟨x, z, rfl, hz, ?_⟩
  have key : (z : K) * (y' : K)⁻¹ * ((y' : K) * (x : K)⁻¹) = (z : K) * (x : K)⁻¹ := by
    have h0 : (y' : K) ≠ 0 := Units.ne_zero y'
    calc (z : K) * (y' : K)⁻¹ * ((y' : K) * (x : K)⁻¹)
        = (z : K) * ((y' : K)⁻¹ * (y' : K)) * (x : K)⁻¹ := by ring
      _ = (z : K) * (x : K)⁻¹ := by rw [inv_mul_cancel₀ h0, mul_one]
  rw [← key]
  exact A.mul_mem hyz h1'

/-- The relation is antisymmetric, independently of any hypothesis on `A`: if `x y⁻¹` and
its inverse both lie in `A`, then `x` and `y` differ by a unit of `A`. -/
theorem order_antisymm (A : Subring K) {ξ η : valueGroup A} (h1 : ξ ≤ η) (h2 : η ≤ ξ) :
    ξ = η := by
  obtain ⟨x, y, rfl, hy, hxy⟩ := h1
  obtain ⟨y', x', hy', hx', hyx⟩ := h2
  have hyy' : valuation A y = valuation A y' := by rw [hy, hy']
  have hxx' : valuation A x = valuation A x' := hx'.symm
  have h2' : (x : K) * (y : K)⁻¹ ∈ A :=
    (div_mem_congr_right A hxx' y).mpr ((div_mem_congr_left A hyy' x').mpr hyx)
  have ht0 : (y : K) * (x : K)⁻¹ ≠ 0 :=
    mul_ne_zero (Units.ne_zero y) (inv_ne_zero (Units.ne_zero x))
  have htA' : ((y : K) * (x : K)⁻¹)⁻¹ ∈ A := by
    rw [mul_inv_rev, inv_inv]
    exact h2'
  have hu : Units.mk0 ((y : K) * (x : K)⁻¹) ht0 ∈ unitSubgroup A := by
    rw [mem_unitSubgroup_iff, Units.val_mk0]
    exact ⟨hxy, htA'⟩
  have hu1 : valuation A (Units.mk0 ((y : K) * (x : K)⁻¹) ht0) = 1 := by
    rw [valuation_apply, QuotientGroup.eq_one_iff]; exact hu
  have hunit : Units.mk0 ((y : K) * (x : K)⁻¹) ht0 = y * x⁻¹ := by
    ext
    rw [Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
  have hprod : valuation A y * (valuation A x)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul, ← hunit]
    exact hu1
  have hgoal : valuation A y = valuation A x := mul_inv_eq_one.mp hprod
  rw [← hy]
  exact hgoal.symm

/-- The relation is total when `A` is a valuation ring of `K`: one of `x y⁻¹`, `y x⁻¹` is
in `A`. -/
theorem order_total (A : Subring K) (hA : ∀ x : K, x ≠ 0 → x ∈ A ∨ x⁻¹ ∈ A)
    (ξ η : valueGroup A) : ξ ≤ η ∨ η ≤ ξ := by
  obtain ⟨x, rfl⟩ := valuation_surjective A ξ
  obtain ⟨y, rfl⟩ := valuation_surjective A η
  rcases hA (((y * x⁻¹ : Kˣ) : K)) (Units.ne_zero _) with h | h
  · left
    rw [valuation_le_valuation_iff]
    rwa [Units.val_mul, Units.val_inv_eq_inv_val] at h
  · right
    rw [valuation_le_valuation_iff]
    rwa [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv] at h

/-! ### The hypothesis "`A` is a valuation ring of `K`" -/

/-- A subring `A` of a field `K` is a valuation ring of `K` (Atiyah–Macdonald, Chapter 5) if
for every `x ≠ 0` in `K` either `x ∈ A` or `x⁻¹ ∈ A`.  It is a typeclass so that the order on
the value group can be an instance. -/
class IsValuationRingOf (K : Type u) [Field K] (A : Subring K) : Prop where
  /-- The defining property of a valuation ring of a field. -/
  mem_or_inv_mem : ∀ x : K, x ≠ 0 → x ∈ A ∨ x⁻¹ ∈ A

theorem mem_or_inv_mem (A : Subring K) [IsValuationRingOf K A] {x : K} (hx : x ≠ 0) :
    x ∈ A ∨ x⁻¹ ∈ A :=
  IsValuationRingOf.mem_or_inv_mem x hx

/-- **Exercise 5.30, first part.** `ξ ≥ η ⟺ x y⁻¹ ∈ A` defines a total ordering of
`Γ = K*/U`. -/
noncomputable instance linearOrder (A : Subring K) [IsValuationRingOf K A] :
    LinearOrder (valueGroup A) where
  le := le A
  le_refl := order_refl A
  le_trans := fun a b c h1 h2 => order_trans A h1 h2
  le_antisymm := fun a b h1 h2 => order_antisymm A h1 h2
  le_total := order_total A (fun x hx => mem_or_inv_mem A hx)
  toDecidableLE := Classical.decRel _

/-- **Exercise 5.30, second part.** The order on `Γ` is compatible with the group structure:
`ξ ≥ η ⟹ ξω ≥ ηω` for all `ω ∈ Γ`. -/
theorem mul_le_mul_left_of_le (A : Subring K) {ξ η : valueGroup A} (h : ξ ≤ η)
    (ω : valueGroup A) : ξ * ω ≤ η * ω := by
  obtain ⟨x, y, hx, hy, hmem⟩ := h
  obtain ⟨w, hw⟩ := valuation_surjective A ω
  have key : ((y * w : Kˣ) : K) * (((x * w : Kˣ) : K))⁻¹ = (y : K) * (x : K)⁻¹ := by
    rw [Units.val_mul, Units.val_mul, mul_inv_rev]
    have h0 : (w : K) ≠ 0 := Units.ne_zero w
    calc (y : K) * (w : K) * ((w : K)⁻¹ * (x : K)⁻¹)
        = (y : K) * (x : K)⁻¹ * ((w : K) * (w : K)⁻¹) := by ring
      _ = (y : K) * (x : K)⁻¹ := by rw [mul_inv_cancel₀ h0, mul_one]
  refine ⟨x * w, y * w, ?_, ?_, ?_⟩
  · rw [map_mul, hx, hw]
  · rw [map_mul, hy, hw]
  · rw [key]; exact hmem

/-- **Exercise 5.30, second part.** `Γ` is a totally ordered abelian group (in the unbundled
form of the current Mathlib: commutative group, linear order, monotone multiplication). -/
noncomputable instance isOrderedMonoid (A : Subring K) [IsValuationRingOf K A] :
    IsOrderedMonoid (valueGroup A) where
  mul_le_mul_left _ _ h ω := mul_le_mul_left_of_le A h ω

/-! ### The ultrametric inequality -/

/-- If `v x ≤ v y` then `v x ≤ v (x + y)`: this is the book's step `x/y ∈ A ⟹
(x + y)/y = 1 + x/y ∈ A`. -/
theorem valuation_le_valuation_add_of_le (A : Subring K) {x y : Kˣ}
    (h : (x : K) + (y : K) ≠ 0) (hxy : valuation A x ≤ valuation A y) :
    valuation A x ≤ valuation A (Units.mk0 ((x : K) + (y : K)) h) := by
  have hmem : (y : K) * (x : K)⁻¹ ∈ A := (valuation_le_valuation_iff A).mp hxy
  refine (valuation_le_valuation_iff A).mpr ?_
  have key : ((Units.mk0 ((x : K) + (y : K)) h : Kˣ) : K) * (x : K)⁻¹
      = (y : K) * (x : K)⁻¹ + 1 := by
    rw [Units.val_mk0, add_mul, mul_inv_cancel₀ (Units.ne_zero x), add_comm]
  rw [key]
  exact A.add_mem hmem A.one_mem

/-- If `v y ≤ v x` then `v y ≤ v (x + y)`. -/
theorem valuation_le_valuation_add_of_ge (A : Subring K) {x y : Kˣ}
    (h : (x : K) + (y : K) ≠ 0) (hyx : valuation A y ≤ valuation A x) :
    valuation A y ≤ valuation A (Units.mk0 ((x : K) + (y : K)) h) := by
  have hmem : (x : K) * (y : K)⁻¹ ∈ A := (valuation_le_valuation_iff A).mp hyx
  refine (valuation_le_valuation_iff A).mpr ?_
  have key : ((Units.mk0 ((x : K) + (y : K)) h : Kˣ) : K) * (y : K)⁻¹
      = (x : K) * (y : K)⁻¹ + 1 := by
    rw [Units.val_mk0, add_mul, mul_inv_cancel₀ (Units.ne_zero y), add_comm]
  rw [key]
  exact A.add_mem hmem A.one_mem

/-- **Exercise 5.30, third part, in the book's own (unbundled) form**: `v (x + y)` is at
least one of `v x`, `v y`, hence at least their minimum.  Only the hypothesis on `A` is used,
not the order instances, so the statement can be made with an explicit hypothesis. -/
theorem valuation_add_ge_min_of_hyp (A : Subring K)
    (hA : ∀ x : K, x ≠ 0 → x ∈ A ∨ x⁻¹ ∈ A) {x y : Kˣ}
    (h : (x : K) + (y : K) ≠ 0) :
    valuation A x ≤ valuation A (Units.mk0 ((x : K) + (y : K)) h) ∨
      valuation A y ≤ valuation A (Units.mk0 ((x : K) + (y : K)) h) := by
  rcases order_total A hA (valuation A x) (valuation A y) with hle | hle
  · exact Or.inl (valuation_le_valuation_add_of_le A h hle)
  · exact Or.inr (valuation_le_valuation_add_of_ge A h hle)

/-- **Exercise 5.30, third part.** For `x, y ∈ K*` with `x + y ≠ 0`:
`v(x + y) ≥ min (v x, v y)`. -/
theorem valuation_add_ge_min (A : Subring K) [IsValuationRingOf K A] {x y : Kˣ}
    (h : (x : K) + (y : K) ≠ 0) :
    min (valuation A x) (valuation A y) ≤ valuation A (Units.mk0 ((x : K) + (y : K)) h) := by
  rw [min_le_iff]
  exact valuation_add_ge_min_of_hyp A (fun x hx => mem_or_inv_mem A hx) h

/-! ### The inequality for all of `K`, with `v 0 = ⊤`

The book's "for all `x, y ∈ K*`" cannot be read literally, since `v` is undefined at `0` and
`x + y = 0` does occur.  The standard repair is `v 0 = ⊤`, which makes the inequality true
without exception. -/

/-- `v` extended to `K` by `v 0 = ⊤`. -/
noncomputable def valuationWithTop (A : Subring K) (x : K) : WithTop (valueGroup A) := by
  classical
  exact if h : x = 0 then ⊤ else valuation A (Units.mk0 x h)

theorem valuationWithTop_zero (A : Subring K) : valuationWithTop A 0 = ⊤ := by
  simp [valuationWithTop]

theorem valuationWithTop_of_ne_zero (A : Subring K) {x : K} (hx : x ≠ 0) :
    valuationWithTop A x = valuation A (Units.mk0 x hx) := by
  simp [valuationWithTop, hx]

/-- With the convention `v 0 = ⊤` the ultrametric inequality holds for all `x, y ∈ K`. -/
theorem valuationWithTop_add_ge_min (A : Subring K) [IsValuationRingOf K A] (x y : K) :
    min (valuationWithTop A x) (valuationWithTop A y) ≤ valuationWithTop A (x + y) := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_add, valuationWithTop_zero]
    simp
  by_cases hy : y = 0
  · subst hy
    rw [add_zero, valuationWithTop_zero]
    simp
  rw [valuationWithTop_of_ne_zero A hx, valuationWithTop_of_ne_zero A hy]
  by_cases hxy : x + y = 0
  · rw [valuationWithTop, dif_pos hxy]
    exact le_top
  · rw [valuationWithTop_of_ne_zero A hxy, ← WithTop.coe_min]
    exact WithTop.coe_le_coe.mpr (valuation_add_ge_min A hxy)

/-! ### Axiom check

Every export below uses only the standard axioms of Lean's logic and Mathlib
(`propext`, `Classical.choice`, `Quotient.sound`); none uses `sorryAx`. -/

#print axioms mem_unitSubgroup_iff
#print axioms valuation_eq_one_iff
#print axioms valuation_le_valuation_iff
#print axioms one_le_valuation_iff
#print axioms order_total
#print axioms linearOrder
#print axioms mul_le_mul_left_of_le
#print axioms isOrderedMonoid
#print axioms valuation_le_valuation_add_of_le
#print axioms valuation_add_ge_min_of_hyp
#print axioms valuation_add_ge_min
#print axioms valuationWithTop_add_ge_min

end AtiyahMcdonald69.Ex_5_30
