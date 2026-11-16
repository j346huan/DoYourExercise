import Mathlib

set_option linter.unusedSectionVars false

/-!
# Atiyah–Macdonald (1969), Exercise 5.33

Let `Γ` be a totally ordered abelian group (written additively), let `k` be a field, and let
`A = k[Γ]` be the group algebra of `Γ` over `k`: the free `k`-vector space on symbols `X_α`
(`α ∈ Γ`) with `X_α X_β = X_{α+β}`.

The exercise asks to show

1. that `A` is an integral domain;
2. that, for `u = λ₁ X_{α₁} + ⋯ + λₙ X_{αₙ}` (all `λᵢ ≠ 0`, `α₁ < ⋯ < αₙ`), the map
   `v₀(u) = α₁` satisfies conditions (1) and (2) of Exercise 5.31, namely
   `v₀(uv) = v₀(u) + v₀(v)` and `v₀(u+v) ≥ min (v₀ u) (v₀ v)`;
3. that `v₀` extends uniquely to a valuation `v` of the field of fractions `K = k(Γ)`,
   and that the value group of `v` is all of `Γ`.

In Lean the monomials `X_α` are `AddMonoidAlgebra.single α 1`, the group algebra is
`AddMonoidAlgebra k Γ`, and `v₀(u)` (defined only for `u ≠ 0` in the book) is
`least u hu = u.coeff.support.min' _`.

## Source notes

* The book writes the symbol `X^α` for the basis element; here it is `single α 1`.
* `v₀` is only defined on `A \ {0}` in the book, so it is formalized as the dependent map
  `least : (u : k[Γ]) → u ≠ 0 → Γ`.
* Exercise 5.31 states condition (2) as `v(x+y) ≥ min (v x) (v y)` for all `x y ∈ K*`.
  For `x + y = 0` the left hand side is undefined (`0 ∉ K*`), so the only faithful reading
  is: for `x y ∈ K*` with `x + y ≠ 0`.  We state it in that form (`IsValuation.map_add_le`).
  The restriction is forced, not a convenience: if one set `v 0 = 0` and required the
  inequality at `x + y = 0`, then `min (v x) (v (-x)) = v x ≤ 0` for every `x` (as
  `v(-x) = v x` follows from multiplicativity), and applying this to `x⁻¹` gives `v x ≥ 0`;
  hence only the zero map would survive.
* "The value group of `v` is precisely `Γ`" is formalized as `∀ γ, ∃ x, v x = γ`.
-/

open AddMonoidAlgebra Finsupp

namespace AtiyahMcdonald69.Ex_5_33

variable {k Γ : Type*} [Field k] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-! ## The group algebra `k[Γ]`

The book's symbols `X_α` (`α ∈ Γ`) are the monomials below: they multiply by
`X_α X_β = X_{α+β}` and every element of `k[Γ]` is a `k`-linear combination of them. -/

/-- The basis element `X_α` of the group algebra `k[Γ]` (the book's notation). -/
noncomputable def X (α : Γ) : AddMonoidAlgebra k Γ := AddMonoidAlgebra.single α 1

/-- The defining relation `X_α X_β = X_{α+β}` of the group algebra. -/
theorem X_mul_X (α β : Γ) :
    (X α : AddMonoidAlgebra k Γ) * X β = X (α + β) := by
  simp [X, AddMonoidAlgebra.single_mul_single]

theorem X_ne_zero (α : Γ) : (X α : AddMonoidAlgebra k Γ) ≠ 0 := by
  intro h
  rw [X, AddMonoidAlgebra.single_eq_zero] at h
  exact one_ne_zero h

/-- Every element of `k[Γ]` is a `k`-linear combination `∑ r_α X_α` of the monomials. -/
theorem eq_sum_smul_X (u : AddMonoidAlgebra k Γ) :
    u.coeff.sum (fun α r => r • (X α : AddMonoidAlgebra k Γ)) = u := by
  have h : (fun α r => r • (X α : AddMonoidAlgebra k Γ)) =
      (fun α r => AddMonoidAlgebra.single α r) := by
    funext α r
    rw [X, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [h, AddMonoidAlgebra.sum_coeff_single]

/-! ## The least exponent of an element of the group algebra -/

/-- `v₀(u)`: the least exponent occurring with nonzero coefficient in `u ≠ 0`
(Atiyah–Macdonald's `α₁`). -/
noncomputable def least (u : AddMonoidAlgebra k Γ) (hu : u ≠ 0) : Γ :=
  u.coeff.support.min' (Finsupp.support_nonempty_iff.mpr (by simpa using hu))

omit [IsOrderedAddMonoid Γ] in
lemma least_mem (u : AddMonoidAlgebra k Γ) (hu : u ≠ 0) :
    least u hu ∈ u.coeff.support :=
  Finset.min'_mem _ _

omit [IsOrderedAddMonoid Γ] in
lemma least_le (u : AddMonoidAlgebra k Γ) (hu : u ≠ 0) {a : Γ}
    (ha : a ∈ u.coeff.support) : least u hu ≤ a :=
  Finset.min'_le _ _ ha

omit [IsOrderedAddMonoid Γ] in
lemma coeff_least_ne_zero (u : AddMonoidAlgebra k Γ) (hu : u ≠ 0) :
    u.coeff (least u hu) ≠ 0 :=
  mem_support_iff.mp (least_mem u hu)

omit [IsOrderedAddMonoid Γ] in
lemma least_congr {u v : AddMonoidAlgebra k Γ} (h : u = v) (hu : u ≠ 0) (hv : v ≠ 0) :
    least u hu = least v hv := by
  cases h
  rfl

lemma least_one : least (1 : AddMonoidAlgebra k Γ) one_ne_zero = 0 := by
  have hsupp : (1 : AddMonoidAlgebra k Γ).coeff.support = {0} :=
    AddMonoidAlgebra.support_coeff_one
  have hne : (1 : AddMonoidAlgebra k Γ).coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (by simp)
  refine le_antisymm ?_ ?_
  · refine least_le _ _ ?_
    rw [hsupp]
    exact Finset.mem_singleton_self 0
  · refine Finset.le_min' _ hne 0 ?_
    intro a ha
    rw [hsupp, Finset.mem_singleton] at ha
    rw [ha]

lemma least_single (γ : Γ) (h : AddMonoidAlgebra.single γ (1 : k) ≠ 0) :
    least (AddMonoidAlgebra.single γ (1 : k)) h = γ := by
  have hsupp : (AddMonoidAlgebra.single γ (1 : k)).coeff.support = {γ} := by
    rw [AddMonoidAlgebra.coeff_single, Finsupp.support_single γ one_ne_zero]
  have hne : (AddMonoidAlgebra.single γ (1 : k)).coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (by simp)
  refine le_antisymm ?_ ?_
  · refine least_le _ _ ?_
    rw [hsupp]
    exact Finset.mem_singleton_self γ
  · refine Finset.le_min' _ hne γ ?_
    intro a ha
    rw [hsupp, Finset.mem_singleton] at ha
    rw [ha]

/-- `v₀(X_α) = α`. -/
theorem least_X (α : Γ) : least (X α : AddMonoidAlgebra k Γ) (X_ne_zero α) = α :=
  least_single α (X_ne_zero α)

/-- The leading exponents give the unique way of writing the leading exponent of a product
as a sum of an exponent of `u` and an exponent of `v`. -/
lemma uniqueAdd_support (u v : AddMonoidAlgebra k Γ) (hu : u ≠ 0) (hv : v ≠ 0) :
    UniqueAdd u.coeff.support v.coeff.support (least u hu) (least v hv) := by
  intro a b ha hb hab
  have h1 : least u hu ≤ a := least_le u hu ha
  have h2 : least v hv ≤ b := least_le v hv hb
  have key : least u hu + b ≤ least u hu + least v hv := by
    rw [← hab]
    exact add_le_add_left h1 b
  have hb' : b ≤ least v hv := by
    have := add_le_add_right key (-(least u hu))
    simpa using this
  have hb0 : b = least v hv := le_antisymm hb' h2
  subst hb0
  exact ⟨add_right_cancel hab, rfl⟩

/-- The coefficient of `X_{α₁}X_{β₁}` in `uv` is the product of the two leading
coefficients; in particular it is nonzero. -/
lemma coeff_mul_least (u v : AddMonoidAlgebra k Γ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v).coeff (least u hu + least v hv) =
      u.coeff (least u hu) * v.coeff (least v hv) :=
  AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd (uniqueAdd_support u v hu hv)

lemma mul_ne_zero_of_ne_zero (u v : AddMonoidAlgebra k Γ) (hu : u ≠ 0) (hv : v ≠ 0) :
    u * v ≠ 0 := by
  intro h
  have h1 := coeff_mul_least u v hu hv
  rw [h] at h1
  have h2 : u.coeff (least u hu) * v.coeff (least v hv) ≠ 0 :=
    mul_ne_zero (coeff_least_ne_zero u hu) (coeff_least_ne_zero v hv)
  exact h2 h1.symm

lemma noZeroDivisors_groupAlgebra : NoZeroDivisors (AddMonoidAlgebra k Γ) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    rcases eq_or_ne a 0 with h1 | h1
    · exact Or.inl h1
    rcases eq_or_ne b 0 with h2 | h2
    · exact Or.inr h2
    · exact absurd h (mul_ne_zero_of_ne_zero a b h1 h2)

/-- **Exercise 5.33, first assertion**: the group algebra of a totally ordered abelian
group over a field is an integral domain. -/
theorem isDomain_groupAlgebra : IsDomain (AddMonoidAlgebra k Γ) :=
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨noZeroDivisors_groupAlgebra, inferInstance⟩

/-- **Exercise 5.33, condition (1) of Exercise 5.31**: `v₀` is multiplicative. -/
theorem least_mul (u v : AddMonoidAlgebra k Γ) (hu : u ≠ 0) (hv : v ≠ 0) :
    least (u * v) (mul_ne_zero_of_ne_zero u v hu hv) = least u hu + least v hv := by
  have hmulne : u * v ≠ 0 := mul_ne_zero_of_ne_zero u v hu hv
  have hne : (u * v).coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (by simpa using hmulne)
  refine le_antisymm ?_ ?_
  · have hmem : least u hu + least v hv ∈ (u * v).coeff.support := by
      rw [mem_support_iff, coeff_mul_least u v hu hv]
      exact mul_ne_zero (coeff_least_ne_zero u hu) (coeff_least_ne_zero v hv)
    exact Finset.min'_le _ _ hmem
  · refine Finset.le_min' _ hne (least u hu + least v hv) ?_
    intro c hc
    have hsub := AddMonoidAlgebra.support_coeff_mul_subset (x := u) (y := v) hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hsub
    exact add_le_add (least_le u hu ha) (least_le v hv hb)

/-- **Exercise 5.33, condition (2) of Exercise 5.31**: the ultrametric inequality. -/
theorem least_add_le (u v : AddMonoidAlgebra k Γ) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u + v ≠ 0) : min (least u hu) (least v hv) ≤ least (u + v) huv := by
  have hmem : least (u + v) huv ∈ (u + v).coeff.support := least_mem _ _
  rw [AddMonoidAlgebra.coeff_add] at hmem
  rcases Finset.mem_union.mp (Finsupp.support_add hmem) with h | h
  · exact (min_le_left _ _).trans (least_le u hu h)
  · exact (min_le_right _ _).trans (least_le v hv h)

/-! ## The extension of `v₀` to the field of fractions -/

attribute [local instance] isDomain_groupAlgebra

section FractionField

/-- The group algebra `A = k[Γ]`. -/
local notation "A" => AddMonoidAlgebra k Γ
/-- The field of fractions `K = k(Γ)` of the group algebra. -/
local notation "K" => FractionRing (AddMonoidAlgebra k Γ)

lemma algebraMap_ne_zero_of_ne_zero {u : A} (hu : u ≠ 0) : algebraMap A K u ≠ 0 := by
  intro h
  exact hu (IsFractionRing.injective A K (by simpa using h))

/-- A numerator of `x` in the fraction field (chosen once and for all). -/
noncomputable def reprNum (x : K) : A :=
  (IsFractionRing.div_surjective A x).choose

/-- A denominator of `x` in the fraction field (chosen once and for all). -/
noncomputable def reprDen (x : K) : A :=
  (IsFractionRing.div_surjective A x).choose_spec.choose

lemma reprDen_mem (x : K) : reprDen x ∈ nonZeroDivisors A :=
  (IsFractionRing.div_surjective A x).choose_spec.choose_spec.1

lemma reprDen_ne_zero (x : K) : reprDen x ≠ 0 :=
  nonZeroDivisors.ne_zero (reprDen_mem x)

lemma repr_eq (x : K) :
    algebraMap A K (reprNum x) / algebraMap A K (reprDen x) = x :=
  (IsFractionRing.div_surjective A x).choose_spec.choose_spec.2

lemma reprNum_ne_zero (x : K) (hx : x ≠ 0) : reprNum x ≠ 0 := by
  intro h
  apply hx
  rw [← repr_eq x, h, map_zero, zero_div]

/-- The values of `v₀` at two representations of the same element of the fraction field
agree. -/
lemma least_sub_eq_of_div_eq {a b c d : A}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : algebraMap A K a / algebraMap A K b = algebraMap A K c / algebraMap A K d) :
    least a ha - least b hb = least c hc - least d hd := by
  have hb' : algebraMap A K b ≠ 0 := algebraMap_ne_zero_of_ne_zero hb
  have hd' : algebraMap A K d ≠ 0 := algebraMap_ne_zero_of_ne_zero hd
  have hcross : algebraMap A K a * algebraMap A K d = algebraMap A K c * algebraMap A K b :=
    (div_eq_div_iff hb' hd').mp h
  rw [← map_mul, ← map_mul] at hcross
  have hcross' : a * d = c * b := IsFractionRing.injective A K hcross
  have key : least a ha + least d hd = least c hc + least b hb := by
    rw [← least_mul a d ha hd, ← least_mul c b hc hb]
    exact least_congr hcross' _ _
  exact sub_eq_sub_iff_add_eq_add.mpr key

/-- The valuation `v(x) = v₀(a) - v₀(b)` for `x = a/b`, defined on `Kˣ`. -/
noncomputable def vOnUnit (x : Kˣ) : Γ :=
  least (reprNum (x : K)) (reprNum_ne_zero _ (Units.ne_zero x)) -
    least (reprDen (x : K)) (reprDen_ne_zero _)

lemma vOnUnit_eq_div {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (x : Kˣ)
    (h : algebraMap A K a / algebraMap A K b = (x : K)) :
    vOnUnit x = least a ha - least b hb :=
  least_sub_eq_of_div_eq (reprNum_ne_zero _ (Units.ne_zero x)) (reprDen_ne_zero _) ha hb
    (by rw [repr_eq, h])

/-- `v` is multiplicative on `Kˣ`. -/
lemma vOnUnit_mul (x y : Kˣ) : vOnUnit (x * y) = vOnUnit x + vOnUnit y := by
  have hx : (x : K) ≠ 0 := Units.ne_zero x
  have hy : (y : K) ≠ 0 := Units.ne_zero y
  have ha : reprNum (x : K) ≠ 0 := reprNum_ne_zero _ hx
  have hb : reprDen (x : K) ≠ 0 := reprDen_ne_zero _
  have hc : reprNum (y : K) ≠ 0 := reprNum_ne_zero _ hy
  have hd : reprDen (y : K) ≠ 0 := reprDen_ne_zero _
  have hxy : algebraMap A K (reprNum (x : K) * reprNum (y : K)) /
        algebraMap A K (reprDen (x : K) * reprDen (y : K)) = ((x * y : Kˣ) : K) := by
    rw [map_mul, map_mul, Units.val_mul, ← div_mul_div_comm, repr_eq, repr_eq]
  rw [vOnUnit_eq_div (mul_ne_zero ha hc) (mul_ne_zero hb hd) (x * y) hxy,
    least_mul (reprNum (x : K)) (reprNum (y : K)) ha hc,
    least_mul (reprDen (x : K)) (reprDen (y : K)) hb hd,
    vOnUnit_eq_div ha hb x (repr_eq _), vOnUnit_eq_div hc hd y (repr_eq _)]
  abel

/-- The ultrametric inequality for `v` on `Kˣ`. -/
lemma vOnUnit_add_le (x y : Kˣ) (h : ((x : K) + (y : K)) ≠ 0) :
    min (vOnUnit x) (vOnUnit y) ≤ vOnUnit (Units.mk0 ((x : K) + (y : K)) h) := by
  have hx : (x : K) ≠ 0 := Units.ne_zero x
  have hy : (y : K) ≠ 0 := Units.ne_zero y
  have ha : reprNum (x : K) ≠ 0 := reprNum_ne_zero _ hx
  have hb : reprDen (x : K) ≠ 0 := reprDen_ne_zero _
  have hc : reprNum (y : K) ≠ 0 := reprNum_ne_zero _ hy
  have hd : reprDen (y : K) ≠ 0 := reprDen_ne_zero _
  have hxdiv : algebraMap A K (reprNum (x : K)) / algebraMap A K (reprDen (x : K)) = (x : K) :=
    repr_eq _
  have hydiv : algebraMap A K (reprNum (y : K)) / algebraMap A K (reprDen (y : K)) = (y : K) :=
    repr_eq _
  have hb' : algebraMap A K (reprDen (x : K)) ≠ 0 := algebraMap_ne_zero_of_ne_zero hb
  have hd' : algebraMap A K (reprDen (y : K)) ≠ 0 := algebraMap_ne_zero_of_ne_zero hd
  have key : algebraMap A K (reprNum (x : K) * reprDen (y : K) +
        reprNum (y : K) * reprDen (x : K)) /
      algebraMap A K (reprDen (x : K) * reprDen (y : K)) =
      algebraMap A K (reprNum (x : K)) / algebraMap A K (reprDen (x : K)) +
        algebraMap A K (reprNum (y : K)) / algebraMap A K (reprDen (y : K)) := by
    rw [div_add_div _ _ hb' hd', map_add, map_mul, map_mul, map_mul,
      mul_comm (algebraMap A K (reprNum (y : K)))]
  have hsum : algebraMap A K (reprNum (x : K) * reprDen (y : K) +
        reprNum (y : K) * reprDen (x : K)) /
      algebraMap A K (reprDen (x : K) * reprDen (y : K)) = ((x : K) + (y : K)) := by
    rw [key, hxdiv, hydiv]
  have hbd : reprDen (x : K) * reprDen (y : K) ≠ 0 := mul_ne_zero hb hd
  have hnum : reprNum (x : K) * reprDen (y : K) + reprNum (y : K) * reprDen (x : K) ≠ 0 := by
    intro h0
    apply h
    rw [← hsum, h0, map_zero, zero_div]
  have h1 : vOnUnit (Units.mk0 ((x : K) + (y : K)) h) =
      least (reprNum (x : K) * reprDen (y : K) + reprNum (y : K) * reprDen (x : K)) hnum -
        least (reprDen (x : K) * reprDen (y : K)) hbd :=
    vOnUnit_eq_div hnum hbd _ hsum
  have h2 : min (least (reprNum (x : K) * reprDen (y : K)) (mul_ne_zero ha hd))
      (least (reprNum (y : K) * reprDen (x : K)) (mul_ne_zero hc hb)) ≤
      least (reprNum (x : K) * reprDen (y : K) + reprNum (y : K) * reprDen (x : K)) hnum :=
    least_add_le _ _ (mul_ne_zero ha hd) (mul_ne_zero hc hb) hnum
  have hx' : vOnUnit x = least (reprNum (x : K)) ha - least (reprDen (x : K)) hb :=
    vOnUnit_eq_div ha hb x hxdiv
  have hy' : vOnUnit y = least (reprNum (y : K)) hc - least (reprDen (y : K)) hd :=
    vOnUnit_eq_div hc hd y hydiv
  have hmin : min (least (reprNum (x : K)) ha - least (reprDen (x : K)) hb)
      (least (reprNum (y : K)) hc - least (reprDen (y : K)) hd) =
      min (least (reprNum (x : K) * reprDen (y : K)) (mul_ne_zero ha hd))
          (least (reprNum (y : K) * reprDen (x : K)) (mul_ne_zero hc hb)) -
        least (reprDen (x : K) * reprDen (y : K)) hbd := by
    have e1 : least (reprNum (x : K)) ha - least (reprDen (x : K)) hb =
        (least (reprNum (x : K)) ha + least (reprDen (y : K)) hd) -
          (least (reprDen (x : K)) hb + least (reprDen (y : K)) hd) := by abel
    have e2 : least (reprNum (y : K)) hc - least (reprDen (y : K)) hd =
        (least (reprNum (y : K)) hc + least (reprDen (x : K)) hb) -
          (least (reprDen (x : K)) hb + least (reprDen (y : K)) hd) := by abel
    rw [e1, e2, min_sub_sub_right, least_mul (reprNum (x : K)) (reprDen (y : K)) ha hd,
      least_mul (reprNum (y : K)) (reprDen (x : K)) hc hb,
      least_mul (reprDen (x : K)) (reprDen (y : K)) hb hd]
  rw [h1, hx', hy', hmin]
  exact sub_le_sub_right h2 _

/-- The unit of `k(Γ)` attached to a nonzero element of `k[Γ]`. -/
noncomputable def unitOf (u : A) (hu : u ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap A K u) (algebraMap_ne_zero_of_ne_zero hu)

/-- The extension of `v₀` to `Kˣ` agrees with `v₀` on `k[Γ]`. -/
lemma vOnUnit_unitOf (u : A) (hu : u ≠ 0) : vOnUnit (unitOf u hu) = least u hu := by
  have h : algebraMap A K u / algebraMap A K (1 : A) = ((unitOf u hu : Kˣ) : K) := by
    rw [map_one, div_one, unitOf, Units.val_mk0]
  rw [vOnUnit_eq_div hu one_ne_zero _ h, least_one, sub_zero]

/-- The value group of `v` is all of `Γ`. -/
lemma vOnUnit_surjective : Function.Surjective (vOnUnit (k := k) (Γ := Γ)) := by
  intro γ
  refine ⟨unitOf (X γ : AddMonoidAlgebra k Γ) (X_ne_zero γ), ?_⟩
  rw [vOnUnit_unitOf, least_X]

/-- **Uniqueness of the extension**: a multiplicative map `Kˣ → Γ` that agrees with `v₀` on
the image of `k[Γ] \ {0}` is `v`. -/
lemma vOnUnit_unique (w : Kˣ → Γ) (hmul : ∀ x y, w (x * y) = w x + w y)
    (hext : ∀ (u : A) (hu : u ≠ 0), w (unitOf u hu) = least u hu) : w = vOnUnit := by
  funext x
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective A (x : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hx : (x : K) ≠ 0 := Units.ne_zero x
  have ha0 : a ≠ 0 := by
    intro h0
    apply hx
    rw [← hdiv, h0, map_zero, zero_div]
  have hmulx : x * unitOf b hb0 = unitOf a ha0 := by
    refine Units.ext ?_
    rw [Units.val_mul, unitOf, Units.val_mk0, unitOf, Units.val_mk0, ← hdiv]
    exact div_mul_cancel₀ _ (algebraMap_ne_zero_of_ne_zero hb0)
  have h1 := congrArg w hmulx
  rw [hmul, hext a ha0, hext b hb0] at h1
  have hwx : w x = least a ha0 - least b hb0 := eq_sub_iff_add_eq.mpr h1
  rw [hwx, vOnUnit_eq_div ha0 hb0 x hdiv]

/-- Atiyah–Macdonald's notion (Exercise 5.31) of a valuation of the field of fractions
`k(Γ)` with values in the totally ordered abelian group `Γ`: a map on `Kˣ` that is
multiplicative and satisfies the ultrametric inequality.

The book states the inequality for `x, y ∈ K*`; since `x + y` may be `0`, the only faithful
reading is with the hypothesis `x + y ≠ 0`, which we make explicit.  (This side condition is
forced: with the convention `v 0 = 0`, requiring the inequality also at `x + y = 0` forces
`v x ≤ 0` for all `x`, and applying this to `x⁻¹` gives `v x ≥ 0`, so only `v ≡ 0` survives.) -/
structure IsValuation (v : Kˣ → Γ) : Prop where
  /-- Condition (1) of Exercise 5.31. -/
  map_mul : ∀ x y, v (x * y) = v x + v y
  /-- Condition (2) of Exercise 5.31. -/
  map_add_le : ∀ (x y : Kˣ) (h : ((x : K) + (y : K)) ≠ 0),
    min (v x) (v y) ≤ v (Units.mk0 ((x : K) + (y : K)) h)

/-- **Exercise 5.33, second assertion**: `v₀` extends uniquely to a valuation `v` of the
field of fractions `K` of `k[Γ]`, and the value group of `v` is exactly `Γ`. -/
theorem exists_unique_valuation :
    ∃ v : Kˣ → Γ,
      IsValuation v ∧
      (∀ (u : A) (hu : u ≠ 0), v (unitOf u hu) = least u hu) ∧
      (∀ γ : Γ, ∃ x : Kˣ, v x = γ) ∧
      (∀ w : Kˣ → Γ, IsValuation w →
        (∀ (u : A) (hu : u ≠ 0), w (unitOf u hu) = least u hu) → w = v) :=
  ⟨vOnUnit, ⟨vOnUnit_mul, vOnUnit_add_le⟩, vOnUnit_unitOf, vOnUnit_surjective,
    fun w hw hwext => vOnUnit_unique w hw.map_mul hwext⟩

/-! ## Sanity checks: the definitions compute the intended values -/

/-- With `Γ = ℤ`, `k = ℚ`, the least exponent of `X_1 + X_3` is `1` (not `3`). -/
private lemma least_X1_add_X3 (h : (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ) ≠ 0) :
    least (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ) h = 1 := by
  have h1 : (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ).coeff 1 = 1 := by
    simp [X, AddMonoidAlgebra.coeff_add]
  have hmem1 : (1:ℤ) ∈ (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ).coeff.support := by
    rw [mem_support_iff, h1]
    exact one_ne_zero
  have hle : ∀ a ∈ (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ).coeff.support, (1:ℤ) ≤ a := by
    intro a ha
    rw [AddMonoidAlgebra.coeff_add] at ha
    rcases Finset.mem_union.mp (Finsupp.support_add ha) with h' | h'
    · rw [X, AddMonoidAlgebra.coeff_single, Finsupp.support_single (1:ℤ) one_ne_zero,
        Finset.mem_singleton] at h'
      omega
    · rw [X, AddMonoidAlgebra.coeff_single, Finsupp.support_single (3:ℤ) one_ne_zero,
        Finset.mem_singleton] at h'
      omega
  exact le_antisymm (least_le _ _ hmem1) (Finset.le_min' _ ⟨1, hmem1⟩ 1 hle)

/-- `v((X_1 + X_3)·X_2) = 1 + 2 = 3` for `Γ = ℤ`, `k = ℚ`: the constructed valuation is
multiplicative in a non-vacuous example. -/
example (ha : (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ) ≠ 0)
    (hb : (X (2:ℤ) : AddMonoidAlgebra ℚ ℤ) ≠ 0) :
    vOnUnit (unitOf (X (1:ℤ) + X (3:ℤ) : AddMonoidAlgebra ℚ ℤ) ha *
      unitOf (X (2:ℤ) : AddMonoidAlgebra ℚ ℤ) hb) = 3 := by
  rw [vOnUnit_mul, vOnUnit_unitOf, vOnUnit_unitOf, least_X1_add_X3, least_X]
  norm_num

/-- **Atiyah–Macdonald (1969), Exercise 5.33**, all assertions in one statement. -/
theorem exercise_5_33 :
    IsDomain (AddMonoidAlgebra k Γ) ∧
    (∀ (u v : A) (hu : u ≠ 0) (hv : v ≠ 0),
      least (u * v) (mul_ne_zero_of_ne_zero u v hu hv) = least u hu + least v hv) ∧
    (∀ (u v : A) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0),
      min (least u hu) (least v hv) ≤ least (u + v) huv) ∧
    (∃ v : Kˣ → Γ,
      IsValuation v ∧
      (∀ (u : A) (hu : u ≠ 0), v (unitOf u hu) = least u hu) ∧
      (∀ γ : Γ, ∃ x : Kˣ, v x = γ) ∧
      (∀ w : Kˣ → Γ, IsValuation w →
        (∀ (u : A) (hu : u ≠ 0), w (unitOf u hu) = least u hu) → w = v)) :=
  ⟨isDomain_groupAlgebra, least_mul, least_add_le, exists_unique_valuation⟩

end FractionField

end AtiyahMcdonald69.Ex_5_33
