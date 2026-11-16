/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [local instance] Classical.propDecidable

/-!
# Atiyah–Macdonald (1969), Exercise 5.32

*Statement (book).*  Let `Γ` be a totally ordered abelian group.  A subgroup `Δ` of `Γ` is
*isolated* in `Γ` if, whenever `0 ≤ β ≤ α` and `α ∈ Δ`, we have `β ∈ Δ`.  Let `A` be a
valuation ring of a field `K`, with value group `Γ` (Exercise 5.31).  If `𝔭` is a prime
ideal of `A`, show that `v(A - 𝔭)` is the set of elements `≥ 0` in an isolated subgroup `Δ`
of `Γ`, and that the mapping so defined of `Spec(A)` into the set of isolated subgroups of
`Γ` is bijective.  If `𝔭` is a prime ideal of `A`, what are the value groups of the
valuation rings `A/𝔭` and `A_𝔭`?

*Answers.*  `Δ = v(A - 𝔭) · v(A - 𝔭)⁻¹`; the inverse bijection sends `Δ` to
`𝔭 = {0} ∪ {a ∈ A \ {0} : v(a) ∉ Δ}`; the value groups of `A/𝔭` and `A_𝔭` are `Δ` and
`Γ/Δ` respectively.

*Formalisation.*  We work with the data of Exercise 5.31: a valuation `v : K → Γ₀` of a
field onto its value group, with `Γ₀ = WithZero Γ` (`Γ` a totally ordered abelian group,
written multiplicatively as in Mathlib), and a ring `O` with `v.Integers O`, i.e. `O` is the
valuation ring of `v`.  (For a valuation ring `A` of `K` one takes `O = A` and
`v = ValuationRing.valuation A K`, whose value group is `ValuationRing.ValueGroup A K` and
which satisfies `v.Integers A`; the codomain is then identified with
`WithZero (ValuationRing.ValueGroup A K)ˣ` via `WithZero.withZeroUnitsEquiv`.)  This
correspondence between valuation rings and valuations is exactly the content of Exercise
5.31, so the statements below are the book's statements for the book's objects.

Sign convention: Mathlib's `v x ≤ 1` corresponds to A–M's `v(x) ≥ 0`; the isolation
condition `0 ≤ β ≤ α` is invariant under inverting values, and is written here as
`1 ≤ β → β ≤ α → α ∈ Δ → β ∈ Δ`.  Accordingly the book's "elements `≥ 0` of `Δ`" are the
elements `≤ 1` of `Δ` below.

The main results are `primeValueSet_eq_deltaOfPrime`, `isIsolated_deltaOfPrime`
(first assertion), `bijective_deltaOfPrime` / `primeSpectrumEquivIsolatedSubgroup`
(second assertion), `valueGroup_quotient` (the value group of `A/𝔭` is `Δ`) and
`valueGroup_localization` (the value group of `A_𝔭` is `Γ/Δ`).
-/

namespace AtiyahMcdonald69.Ex_5_32

open Set

universe u v w

/-! ### Isolated subgroups of a totally ordered abelian group -/

section Isolated

variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- A subgroup `Δ` of a totally ordered abelian group `Γ` is *isolated* if
`0 ≤ β ≤ α` and `α ∈ Δ` imply `β ∈ Δ` (A–M, Exercise 5.32); written multiplicatively:
`1 ≤ β ≤ α` and `α ∈ Δ` imply `β ∈ Δ`.  This condition is invariant under `γ ↦ γ⁻¹`. -/
class IsIsolated (Δ : Subgroup Γ) : Prop where
  /-- `1 ≤ β ≤ α ∈ Δ` implies `β ∈ Δ`. -/
  mem_of_le : ∀ {α β : Γ}, 1 ≤ β → β ≤ α → α ∈ Δ → β ∈ Δ

namespace IsIsolated

variable {Δ : Subgroup Γ}

/-- An isolated subgroup is convex: if `α ≤ β ≤ 1` and `α ∈ Δ` then `β ∈ Δ`. -/
theorem mem_of_le_of_le_one (hΔ : IsIsolated Δ) {α β : Γ} (hα : α ∈ Δ) (hαβ : α ≤ β)
    (hβ : β ≤ 1) : β ∈ Δ := by
  have h1 : 1 ≤ β⁻¹ := by
    simpa using (inv_le_inv_iff (a := (1 : Γ)) (b := β)).mpr hβ
  have h2 : β⁻¹ ≤ α⁻¹ := (inv_le_inv_iff (a := β) (b := α)).mpr hαβ
  have h3 : α⁻¹ ∈ Δ := Subgroup.inv_mem Δ hα
  have h4 : β⁻¹ ∈ Δ := hΔ.mem_of_le h1 h2 h3
  simpa using Subgroup.inv_mem Δ h4

/-- Convexity, phrased for `WithZero Γ`: if `γ ∈ Δ` and `γ ≤ x ≤ 1` then `x` is the
coercion of an element of `Δ`. -/
theorem mem_of_le_of_le_one₀ (hΔ : IsIsolated Δ) {x : WithZero Γ} {γ : Γ} (hγ : γ ∈ Δ)
    (hx : (γ : WithZero Γ) ≤ x) (hx1 : x ≤ 1) : ∃ δ : Γ, δ ∈ Δ ∧ (δ : WithZero Γ) = x := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    exact WithZero.not_coe_le_zero γ hx
  refine ⟨WithZero.unzero hx0, hΔ.mem_of_le_of_le_one hγ ?_ ?_, WithZero.coe_unzero hx0⟩
  · rw [← WithZero.coe_le_coe, WithZero.coe_unzero hx0]
    exact hx
  · rw [← WithZero.coe_le_coe, WithZero.coe_unzero hx0, WithZero.coe_one]
    exact hx1

end IsIsolated

end Isolated

/-! ### Valuations and their valuation rings -/

section ValuationSetup

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

theorem v_eq_zero_iff {v : Valuation K (WithZero Γ)} {x : K} : v x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  by_contra hx
  have h1 : v x * (v x)⁻¹ = 1 := by
    rw [← Valuation.map_inv, ← Valuation.map_mul, mul_inv_cancel₀ hx, Valuation.map_one]
  rw [h, inv_zero, mul_zero] at h1
  exact zero_ne_one h1

variable {O : Type w} [CommRing O] [Algebra O K]

/-- The set `v(O - 𝔭)` of values of elements of `O` outside the ideal `𝔭`. -/
def primeValueSet (v : Valuation K (WithZero Γ)) (p : Ideal O) : Set Γ :=
  {γ | ∃ a : O, a ∉ p ∧ v (algebraMap O K a) = (γ : WithZero Γ)}

/-- The subgroup of `Γ` generated by `v(O - 𝔭)`: explicitly the set of quotients
`v a / v b` with `a b ∉ 𝔭` (written multiplicatively as `v a = γ * v b`). -/
def deltaOfPrime (v : Valuation K (WithZero Γ)) (p : Ideal O) (hp : p.IsPrime) : Subgroup Γ where
  carrier := {γ | ∃ a b : O, a ∉ p ∧ b ∉ p ∧ v (algebraMap O K a) = (γ : WithZero Γ) * v (algebraMap O K b)}
  one_mem' := by
    have h1 : (1 : O) ∉ p := fun h => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr h)
    refine ⟨1, 1, h1, h1, ?_⟩
    rw [map_one, map_one, WithZero.coe_one, one_mul]
  mul_mem' := by
    rintro γ δ ⟨a, b, ha, hb, h⟩ ⟨c, d, hc, hd, h'⟩
    refine ⟨a * c, b * d, ?_, ?_, ?_⟩
    · exact fun hmem => (hp.mem_or_mem hmem).elim ha hc
    · exact fun hmem => (hp.mem_or_mem hmem).elim hb hd
    · calc v (algebraMap O K (a * c))
          = v (algebraMap O K a) * v (algebraMap O K c) := by simp only [map_mul]
        _ = (↑γ * ↑δ) * (v (algebraMap O K b) * v (algebraMap O K d)) := by
              rw [h, h']
              exact mul_mul_mul_comm _ _ _ _
        _ = (↑(γ * δ)) * v (algebraMap O K (b * d)) := by
              rw [WithZero.coe_mul, ← Valuation.map_mul, ← map_mul]
  inv_mem' := by
    rintro γ ⟨a, b, ha, hb, h⟩
    refine ⟨b, a, hb, ha, ?_⟩
    calc v (algebraMap O K b)
        = (↑γ)⁻¹ * (↑γ * v (algebraMap O K b)) := by
            rw [← mul_assoc, inv_mul_cancel₀ (WithZero.coe_ne_zero), one_mul]
      _ = (↑γ)⁻¹ * v (algebraMap O K a) := by rw [← h]
      _ = (↑(γ⁻¹)) * v (algebraMap O K a) := by rw [WithZero.coe_inv]

variable {v : Valuation K (WithZero Γ)}

/-- An element of `O` outside `𝔭` has its value in `Δ` and `≤ 1`. -/
theorem mem_deltaOfPrime_of_valuation_eq (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    {a : O} (ha : a ∉ p) {γ : Γ} (h : v (algebraMap O K a) = (γ : WithZero Γ)) :
    γ ∈ deltaOfPrime v p hp ∧ γ ≤ 1 := by
  have h1 : (1 : O) ∉ p := fun hmem => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr hmem)
  refine ⟨⟨a, 1, ha, h1, ?_⟩, ?_⟩
  · rw [← h, map_one, Valuation.map_one, mul_one]
  · rw [← WithZero.coe_le_one, ← h]
    exact hv.map_le_one a

/-- Every element of `v(O - 𝔭)` is a nonnegative (here: `≤ 1`) element of `Δ`. -/
theorem primeValueSet_subset_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) :
    primeValueSet v p ⊆ {γ : Γ | γ ∈ deltaOfPrime v p hp ∧ γ ≤ 1} := by
  rintro γ ⟨a, ha, h⟩
  exact mem_deltaOfPrime_of_valuation_eq hv p hp ha h

/-- The converse of `primeValueSet_subset_deltaOfPrime`: an element of `Δ` that is `≤ 1`
(that is, `≥ 0` in the book's convention) is the value of an element of `O` outside `𝔭`. -/
theorem mem_primeValueSet_of_mem_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    {γ : Γ} (hγ : γ ∈ deltaOfPrime v p hp) (h1 : γ ≤ 1) : γ ∈ primeValueSet v p := by
  obtain ⟨a, b, ha, hb, h⟩ := hγ
  have hb0 : b ≠ 0 := fun h0 => hb (h0 ▸ p.zero_mem)
  have hbK : v (algebraMap O K b) ≠ 0 := by
    rw [ne_eq, v_eq_zero_iff]
    intro h0
    exact hb0 (hv.hom_inj (by simpa using h0))
  have hdiv : v (algebraMap O K a / algebraMap O K b) = (γ : WithZero Γ) := by
    rw [Valuation.map_div, h]
    exact mul_div_cancel_right₀ _ hbK
  have hle : v (algebraMap O K a / algebraMap O K b) ≤ 1 := by
    rw [hdiv, WithZero.coe_le_one]
    exact h1
  obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
  refine ⟨c, ?_, ?_⟩
  · intro hcp
    apply ha
    have hbK' : algebraMap O K b ≠ 0 := fun h0 => hb0 (hv.hom_inj (by simpa using h0))
    have hab : algebraMap O K a = algebraMap O K (b * c) := by
      rw [map_mul, hc]
      exact (mul_div_cancel₀ (algebraMap O K a) hbK').symm
    rw [hv.hom_inj hab, mul_comm]
    exact Ideal.mul_mem_right b p hcp
  · rw [hc, hdiv]

/-- `v(O - 𝔭)` is convex inside `{γ | γ ≤ 1}`. -/
theorem primeValueSet_convex (hv : v.Integers O) (p : Ideal O)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ))
    {s β : Γ} (hs : s ∈ primeValueSet v p) (h : s ≤ β) (hβ : β ≤ 1) :
    β ∈ primeValueSet v p := by
  obtain ⟨a, ha, hav⟩ := hs
  obtain ⟨y, hy⟩ := hsurj β
  have hy1 : v y ≤ 1 := by rw [hy, WithZero.coe_le_one]; exact hβ
  obtain ⟨b, hb⟩ := hv.exists_of_le_one hy1
  have hbK : algebraMap O K b ≠ 0 := by
    intro h0
    have h1 : v y = 0 := by rw [← hb, h0, map_zero]
    rw [hy] at h1
    exact WithZero.coe_ne_zero h1
  refine ⟨b, ?_, ?_⟩
  · intro hbp
    apply ha
    have hzle : v (algebraMap O K a / y) ≤ 1 := by
      rw [Valuation.map_div, hy, hav, div_le_iff₀ (WithZero.zero_lt_coe β), one_mul,
        WithZero.coe_le_coe]
      exact h
    obtain ⟨z, hz⟩ := hv.exists_of_le_one hzle
    have hab : algebraMap O K a = algebraMap O K (z * b) := by
      rw [map_mul, hz, ← hb]
      field_simp
    rw [hv.hom_inj hab]
    exact Ideal.mul_mem_left p z hbp
  · rw [hb, hy]

/-- `Δ` is convex: `α ∈ Δ`, `α ≤ β ≤ 1` imply `β ∈ Δ`. -/
theorem deltaOfPrime_convex (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ))
    {α β : Γ} (hα : α ∈ deltaOfPrime v p hp) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    β ∈ deltaOfPrime v p hp := by
  have hβ1 : β ≤ 1 := hβ
  have hα1 : α ≤ 1 := le_trans hαβ hβ1
  have hS : α ∈ primeValueSet v p := mem_primeValueSet_of_mem_deltaOfPrime hv p hp hα hα1
  exact (primeValueSet_subset_deltaOfPrime hv p hp
    (primeValueSet_convex hv p hsurj hS hαβ hβ1)).1

/-- **A–M 5.32 (first assertion)**: for a prime `𝔭`, the values `v(O - 𝔭)` form the set of
elements `≤ 1` (the book's `≥ 0`) of an isolated subgroup `Δ` of `Γ`. -/
theorem isIsolated_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    IsIsolated (deltaOfPrime v p hp) := by
  refine ⟨fun {α β} h1 h2 hα => ?_⟩
  have hconv : ∀ {x y : Γ}, x ∈ deltaOfPrime v p hp → x ≤ y → y ≤ 1 → y ∈ deltaOfPrime v p hp :=
    fun hx hxy hy => deltaOfPrime_convex hv p hp hsurj hx hxy hy
  have hinv : α⁻¹ ∈ deltaOfPrime v p hp := Subgroup.inv_mem _ hα
  have hle : α⁻¹ ≤ β⁻¹ := (inv_le_inv_iff (a := α) (b := β)).mpr h2
  have hle1 : β⁻¹ ≤ 1 := by simpa using (inv_le_inv_iff (a := β) (b := (1 : Γ))).mpr h1
  have hmem : β⁻¹ ∈ deltaOfPrime v p hp := hconv hinv hle hle1
  simpa using Subgroup.inv_mem _ hmem

/-- **A–M 5.32 (first assertion), equality form**: `v(O - 𝔭)` is exactly the set of
elements `≤ 1` of the isolated subgroup `Δ`. -/
theorem primeValueSet_eq_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) :
    primeValueSet v p = {γ : Γ | γ ∈ deltaOfPrime v p hp ∧ γ ≤ 1} := by
  refine Set.Subset.antisymm (primeValueSet_subset_deltaOfPrime hv p hp) ?_
  rintro γ ⟨hγ, h1⟩
  exact mem_primeValueSet_of_mem_deltaOfPrime hv p hp hγ h1

/-- The ideal of `O` attached to a subgroup `Δ ≤ Γ`: `{a | v a ∉ Δ}`
(A–M: `𝔭 = {0} ∪ {a ∈ A \ {0} : v(a) ∉ Δ}`). -/
noncomputable def idealOfDelta (hv : v.Integers O) (Δ : Subgroup Γ)
    (hΔ : IsIsolated Δ) : Ideal O where
  carrier := {a | ¬ ∃ γ : Γ, γ ∈ Δ ∧ v (algebraMap O K a) = (γ : WithZero Γ)}
  zero_mem' := by
    rintro ⟨γ, -, h⟩
    have h0 : (γ : WithZero Γ) = 0 := by simpa using h.symm
    exact WithZero.coe_ne_zero h0
  add_mem' := by
    intro a b ha hb
    rintro ⟨γ, hγ, hab⟩
    have ha1 : v (algebraMap O K a) ≤ 1 := hv.map_le_one a
    have hb1 : v (algebraMap O K b) ≤ 1 := hv.map_le_one b
    have hsum : (γ : WithZero Γ) ≤ max (v (algebraMap O K a)) (v (algebraMap O K b)) := by
      rw [← hab, map_add]
      exact Valuation.map_add v _ _
    rcases le_total (v (algebraMap O K a)) (v (algebraMap O K b)) with hle | hle
    · have hb' : (γ : WithZero Γ) ≤ v (algebraMap O K b) :=
        le_trans hsum (max_le hle le_rfl)
      obtain ⟨δ, hδ, hδx⟩ := IsIsolated.mem_of_le_of_le_one₀ hΔ hγ hb' hb1
      exact hb ⟨δ, hδ, by rw [← hδx]⟩
    · have ha' : (γ : WithZero Γ) ≤ v (algebraMap O K a) :=
        le_trans hsum (max_le le_rfl hle)
      obtain ⟨δ, hδ, hδx⟩ := IsIsolated.mem_of_le_of_le_one₀ hΔ hγ ha' ha1
      exact ha ⟨δ, hδ, by rw [← hδx]⟩
  smul_mem' := by
    intro c x hx
    rintro ⟨γ, hγ, hcx⟩
    have hc1 : v (algebraMap O K c) ≤ 1 := hv.map_le_one c
    have hx1 : v (algebraMap O K x) ≤ 1 := hv.map_le_one x
    have hcx' : v (algebraMap O K c * algebraMap O K x) = (γ : WithZero Γ) := by
      rw [← map_mul, ← smul_eq_mul]
      exact hcx
    have hle : (γ : WithZero Γ) ≤ v (algebraMap O K x) := by
      rw [← hcx']
      calc v (algebraMap O K c * algebraMap O K x)
          = v (algebraMap O K c) * v (algebraMap O K x) := by simp only [map_mul]
        _ ≤ 1 * v (algebraMap O K x) :=
            mul_le_mul_of_nonneg_right hc1 (zero_le : (0 : WithZero Γ) ≤ v (algebraMap O K x))
        _ = v (algebraMap O K x) := one_mul _
    obtain ⟨δ, hδ, hδx⟩ := IsIsolated.mem_of_le_of_le_one₀ hΔ hγ hle hx1
    exact hx ⟨δ, hδ, hδx.symm⟩

/-- The ideal attached to an isolated subgroup is prime. -/
theorem isPrime_idealOfDelta (hv : v.Integers O) (Δ : Subgroup Γ) (hΔ : IsIsolated Δ) :
    (idealOfDelta hv Δ hΔ).IsPrime := by
  refine Ideal.IsPrime.mk ?_ ?_
  · intro htop
    have h1 : (1 : O) ∈ idealOfDelta hv Δ hΔ := (Ideal.eq_top_iff_one _).mp htop
    exact h1 ⟨1, Subgroup.one_mem Δ,
      by rw [map_one, Valuation.map_one, WithZero.coe_one]⟩
  · intro a b hab
    by_contra h
    rw [not_or] at h
    have ha : ∃ γ : Γ, γ ∈ Δ ∧ v (algebraMap O K a) = (γ : WithZero Γ) := by
      simpa [idealOfDelta] using h.1
    have hb : ∃ γ : Γ, γ ∈ Δ ∧ v (algebraMap O K b) = (γ : WithZero Γ) := by
      simpa [idealOfDelta] using h.2
    obtain ⟨γ₁, hγ₁, hv₁⟩ := ha
    obtain ⟨γ₂, hγ₂, hv₂⟩ := hb
    refine hab ⟨γ₁ * γ₂, Subgroup.mul_mem _ hγ₁ hγ₂, ?_⟩
    rw [map_mul, Valuation.map_mul v, hv₁, hv₂, WithZero.coe_mul]

/-- For `γ ∈ Δ` with `γ ≤ 1` there is `a ∉ 𝔭_Δ` with `v a = γ`. -/
theorem exists_notMem_idealOfDelta_of_mem (hv : v.Integers O) (Δ : Subgroup Γ) (hΔ : IsIsolated Δ)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ))
    {γ : Γ} (hγ : γ ∈ Δ) (h1 : γ ≤ 1) :
    ∃ a : O, a ∉ idealOfDelta hv Δ hΔ ∧ v (algebraMap O K a) = (γ : WithZero Γ) := by
  obtain ⟨x, hx⟩ := hsurj γ
  have hx1 : v x ≤ 1 := by rw [hx, WithZero.coe_le_one]; exact h1
  obtain ⟨a, ha⟩ := hv.exists_of_le_one hx1
  refine ⟨a, ?_, ?_⟩
  · intro hmem
    exact hmem ⟨γ, hγ, by rw [ha, hx]⟩
  · rw [ha, hx]

/-- The two constructions are inverse: the prime attached to `Δ` recovers `Δ`. -/
theorem deltaOfPrime_idealOfDelta (hv : v.Integers O) (Δ : Subgroup Γ) (hΔ : IsIsolated Δ)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    deltaOfPrime v (idealOfDelta hv Δ hΔ) (isPrime_idealOfDelta hv Δ hΔ) = Δ := by
  refine le_antisymm ?_ ?_
  · rintro γ ⟨a, b, ha, hb, h⟩
    have ha' : ∃ δ : Γ, δ ∈ Δ ∧ v (algebraMap O K a) = (δ : WithZero Γ) := by
      by_contra hc
      exact ha (by simpa [idealOfDelta] using hc)
    obtain ⟨δ₁, hδ₁, hv₁⟩ := ha'
    have hb' : ∃ δ : Γ, δ ∈ Δ ∧ v (algebraMap O K b) = (δ : WithZero Γ) := by
      by_contra hc
      exact hb (by simpa [idealOfDelta] using hc)
    obtain ⟨δ₂, hδ₂, hv₂⟩ := hb'
    have hγeq : γ = δ₁ / δ₂ := by
      apply WithZero.coe_inj.mp
      rw [WithZero.coe_div]
      have h' : (δ₁ : WithZero Γ) = (γ : WithZero Γ) * (δ₂ : WithZero Γ) := by
        rw [← hv₁, ← hv₂]
        exact h
      rw [h', mul_div_cancel_right₀ _ (WithZero.coe_ne_zero (a := δ₂))]
    rw [hγeq]
    exact Subgroup.div_mem _ hδ₁ hδ₂
  · intro γ hγ
    have key : ∀ {η : Γ}, η ∈ Δ → η ≤ 1 → ∃ a : O, a ∉ idealOfDelta hv Δ hΔ ∧
        v (algebraMap O K a) = (η : WithZero Γ) :=
      fun hη hη1 => exists_notMem_idealOfDelta_of_mem hv Δ hΔ hsurj hη hη1
    have hγ' : γ * 1 ∈ Δ := by simpa using hγ
    rcases le_or_gt γ 1 with hle | hlt
    · obtain ⟨a, ha, hav⟩ := key hγ hle
      refine ⟨a, 1, ha, ?_, ?_⟩
      · intro hmem
        exact hmem ⟨1, Subgroup.one_mem Δ,
          by rw [map_one, Valuation.map_one, WithZero.coe_one]⟩
      · rw [hav, map_one, Valuation.map_one, mul_one]
    · -- `1 ≤ γ`: use `1` and `γ⁻¹`
      have h1γ : (1 : Γ) ≤ γ := le_of_lt hlt
      have h1mem : (1 : Γ) ∈ Δ := Subgroup.one_mem Δ
      obtain ⟨b, hb, hbv⟩ := key h1mem le_rfl
      have hinv : γ⁻¹ ∈ Δ := Subgroup.inv_mem _ hγ
      have hinv1 : γ⁻¹ ≤ 1 := by
        simpa using (inv_le_inv_iff (a := γ) (b := (1 : Γ))).mpr h1γ
      obtain ⟨a, ha, hav⟩ := key hinv hinv1
      refine ⟨b, a, hb, ha, ?_⟩
      rw [hbv, hav, ← WithZero.coe_mul, mul_inv_cancel]

end ValuationSetup

/-! ### The bijection `Spec(O) ≃ {isolated subgroups}` -/

section Bijection

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- The two constructions are inverse: the subgroup attached to `𝔭` recovers `𝔭`. -/
theorem idealOfDelta_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    idealOfDelta hv (deltaOfPrime v p hp) (isIsolated_deltaOfPrime hv p hp hsurj) = p := by
  ext a
  constructor
  · intro ha
    by_contra hap
    have hmem : ∃ γ : Γ, γ ∈ deltaOfPrime v p hp ∧ v (algebraMap O K a) = (γ : WithZero Γ) := by
      have ha0 : v (algebraMap O K a) ≠ 0 := by
        rw [ne_eq, v_eq_zero_iff]
        intro h0
        have hz : a = 0 := hv.hom_inj (by rw [h0, map_zero])
        exact hap (hz ▸ p.zero_mem)
      refine ⟨WithZero.unzero ha0, ?_, (WithZero.coe_unzero ha0).symm⟩
      exact (mem_deltaOfPrime_of_valuation_eq hv p hp hap (WithZero.coe_unzero ha0).symm).1
    exact ha hmem
  · intro hap
    rintro ⟨γ, hγ, hav⟩
    have hγ1 : γ ≤ 1 := by
      rw [← WithZero.coe_le_one, ← hav]
      exact hv.map_le_one a
    obtain ⟨c, hc, hcv⟩ := mem_primeValueSet_of_mem_deltaOfPrime hv p hp hγ hγ1
    have hcK : algebraMap O K c ≠ 0 := by
      intro h0
      have h1 : v (algebraMap O K c) = 0 := by rw [h0, map_zero]
      rw [hcv] at h1
      exact WithZero.coe_ne_zero h1
    have hwc : v (algebraMap O K a / algebraMap O K c) = 1 := by
      rw [Valuation.map_div, hav, hcv]
      exact div_self (WithZero.coe_ne_zero (a := γ))
    obtain ⟨u, hu⟩ := hv.exists_of_le_one (le_of_eq hwc)
    have hvu : v (algebraMap O K u) = 1 := by rw [hu, hwc]
    have hunit : IsUnit u := (Valuation.Integers.isUnit_iff_valuation_eq_one hv).mpr hvu
    obtain ⟨u', hu'⟩ := hunit.exists_right_inv
    have hac : algebraMap O K a = algebraMap O K c * algebraMap O K u := by
      rw [hu]
      exact (mul_div_cancel₀ (algebraMap O K a) hcK).symm
    have hcaeq : c = a * u' := by
      apply hv.hom_inj
      rw [map_mul, hac, mul_assoc, ← map_mul, hu', map_one, mul_one]
    rw [hcaeq] at hc
    exact hc (by rw [mul_comm]; exact Ideal.mul_mem_left p u' hap)

/-- **A–M 5.32 (second assertion)**: `𝔭 ↦ v(O - 𝔭) - v(O - 𝔭)` is a bijection from the prime
spectrum of `O` onto the set of isolated subgroups of the value group `Γ`. -/
noncomputable def primeSpectrumEquivIsolatedSubgroup (hv : v.Integers O)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    PrimeSpectrum O ≃ {Δ : Subgroup Γ // IsIsolated Δ} where
  toFun p := ⟨deltaOfPrime v p.asIdeal p.2, isIsolated_deltaOfPrime hv p.asIdeal p.2 hsurj⟩
  invFun Δ := ⟨idealOfDelta hv Δ.1 Δ.2, isPrime_idealOfDelta hv Δ.1 Δ.2⟩
  left_inv p := PrimeSpectrum.ext (idealOfDelta_deltaOfPrime hv p.asIdeal p.2 hsurj)
  right_inv Δ := Subtype.ext (deltaOfPrime_idealOfDelta hv Δ.1 Δ.2 hsurj)

/-- **A–M 5.32 (second assertion), bijectivity form.** -/
theorem bijective_deltaOfPrime (hv : v.Integers O)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    Function.Bijective fun p : PrimeSpectrum O =>
      (⟨deltaOfPrime v p.asIdeal p.2, isIsolated_deltaOfPrime hv p.asIdeal p.2 hsurj⟩ :
        {Δ : Subgroup Γ // IsIsolated Δ}) :=
  (primeSpectrumEquivIsolatedSubgroup hv hsurj).bijective

end Bijection

/-! ### The quotient order on `Γ/Δ` -/

section OrderedQuotient

variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

namespace QuotientOrder

/-! For an isolated subgroup `Δ` of a totally ordered abelian group `Γ` we put the
*quotient order* on `Γ/Δ`: `x ≤ y` iff `y = γ * x` for some `γ ≥ 1`.  This is the value
group `Γ/Δ` of the valuation ring `A_𝔭` of A–M Exercise 5.32. -/

variable {Δ : Subgroup Γ} [hΔ : IsIsolated Δ]

instance instLE : LE (Γ ⧸ Δ) :=
  ⟨fun x y => ∃ γ : Γ, 1 ≤ γ ∧ QuotientGroup.mk γ * x = y⟩

theorem le_def {x y : Γ ⧸ Δ} :
    x ≤ y ↔ ∃ γ : Γ, 1 ≤ γ ∧ QuotientGroup.mk γ * x = y := Iff.rfl

theorem mk_le_mk {γ δ : Γ} (h : γ ≤ δ) :
    (QuotientGroup.mk γ : Γ ⧸ Δ) ≤ QuotientGroup.mk δ := by
  refine ⟨γ⁻¹ * δ, ?_, ?_⟩
  · simpa using mul_le_mul_left h γ⁻¹
  · rw [← QuotientGroup.mk_mul]
    congr 1
    rw [mul_assoc, mul_comm δ γ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem le_refl (x : Γ ⧸ Δ) : x ≤ x := by
  refine ⟨1, le_rfl, ?_⟩
  rw [QuotientGroup.mk_one, one_mul]

theorem le_trans {x y z : Γ ⧸ Δ} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  obtain ⟨γ₁, hγ₁, e₁⟩ := h1
  obtain ⟨γ₂, hγ₂, e₂⟩ := h2
  refine ⟨γ₁ * γ₂, one_le_mul hγ₁ hγ₂, ?_⟩
  rw [QuotientGroup.mk_mul, mul_assoc, ← e₂, ← e₁, mul_left_comm]

theorem le_antisymm {x y : Γ ⧸ Δ} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  obtain ⟨γ₁, hγ₁, e₁⟩ := h1
  obtain ⟨γ₂, hγ₂, e₂⟩ := h2
  have h3 : QuotientGroup.mk (γ₁ * γ₂) * x = 1 * x := by
    rw [QuotientGroup.mk_mul, mul_assoc, mul_left_comm, e₁, e₂, one_mul]
  have h4 : QuotientGroup.mk (γ₁ * γ₂) = (1 : Γ ⧸ Δ) := mul_right_cancel h3
  have hmem : γ₁ * γ₂ ∈ Δ := by
    rw [QuotientGroup.eq_one_iff] at h4
    exact h4
  have hle : γ₁ ≤ γ₁ * γ₂ := by simpa using mul_le_mul_left hγ₂ γ₁
  have hγ₁Δ : γ₁ ∈ Δ := hΔ.mem_of_le hγ₁ hle hmem
  have hone : QuotientGroup.mk γ₁ = (1 : Γ ⧸ Δ) := by
    rw [QuotientGroup.eq_one_iff]
    exact hγ₁Δ
  rw [hone, one_mul] at e₁
  exact e₁

theorem le_total (x y : Γ ⧸ Δ) : x ≤ y ∨ y ≤ x := by
  revert y
  refine QuotientGroup.induction_on x ?_
  intro γ y
  refine QuotientGroup.induction_on y ?_
  intro δ
  by_cases h : (1 : Γ) ≤ γ⁻¹ * δ
  · left
    refine ⟨γ⁻¹ * δ, h, ?_⟩
    rw [← QuotientGroup.mk_mul]
    congr 1
    rw [mul_assoc, mul_comm δ γ, ← mul_assoc, inv_mul_cancel, one_mul]
  · right
    have h1 : 1 ≤ δ⁻¹ * γ := by
      have h2 : 1 ≤ (γ⁻¹ * δ)⁻¹ := by
        simpa using (inv_le_inv_iff (a := (1 : Γ)) (b := γ⁻¹ * δ)).mpr (le_of_lt (lt_of_not_ge h))
      simpa [mul_inv_rev] using h2
    refine ⟨δ⁻¹ * γ, h1, ?_⟩
    rw [← QuotientGroup.mk_mul]
    congr 1
    rw [mul_assoc, mul_comm γ δ, ← mul_assoc, inv_mul_cancel, one_mul]

noncomputable instance instLinearOrder : LinearOrder (Γ ⧸ Δ) where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  le_total := le_total
  toDecidableLE := Classical.decRel _

instance instIsOrderedMonoid : IsOrderedMonoid (Γ ⧸ Δ) where
  mul_le_mul_left := by
    intro x y hxy c
    obtain ⟨γ, hγ, e⟩ := hxy
    exact ⟨γ, hγ, by rw [← mul_assoc, e]⟩
  mul_le_mul_right := by
    intro x y hxy c
    obtain ⟨γ, hγ, e⟩ := hxy
    exact ⟨γ, hγ, by rw [mul_left_comm, e]⟩

/-- The canonical map `Γ → Γ/Δ`. -/
def mkHom : Γ →* Γ ⧸ Δ := QuotientGroup.mk' Δ

@[simp] theorem mkHom_apply (γ : Γ) : (mkHom (Δ := Δ) γ : Γ ⧸ Δ) = QuotientGroup.mk γ := rfl

/-- The canonical map `Γ ∪ {0} → (Γ/Δ) ∪ {0}`. -/
def quotientHom : WithZero Γ →*₀ WithZero (Γ ⧸ Δ) :=
  WithZero.map' (mkHom (Δ := Δ))

theorem coe_quotientHom (γ : Γ) :
    quotientHom (Δ := Δ) (γ : WithZero Γ) = (mkHom (Δ := Δ) γ : WithZero (Γ ⧸ Δ)) := rfl

theorem mk_le_one_iff {ξ : Γ} : (QuotientGroup.mk ξ : Γ ⧸ Δ) ≤ 1 ↔ ∃ δ : Γ, δ ∈ Δ ∧ ξ ≤ δ := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ * ξ, ?_, ?_⟩
    · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact h
    · simpa using mul_le_mul_left hγ ξ
  · rintro ⟨δ, hδ, hle⟩
    refine ⟨δ / ξ, ?_, ?_⟩
    · simpa [div_eq_mul_inv] using mul_le_mul_left hle ξ⁻¹
    · rw [← QuotientGroup.mk_mul, div_mul_cancel, QuotientGroup.eq_one_iff]
      exact hδ

theorem quotientHom_monotone : Monotone (quotientHom (Δ := Δ)) := by
  intro x y hxy
  match x, y with
  | 0, _ => exact bot_le
  | (γ : Γ), 0 => exact absurd hxy (WithZero.not_coe_le_zero γ)
  | (γ : Γ), (δ : Γ) =>
    rw [coe_quotientHom, coe_quotientHom, WithZero.coe_le_coe]
    exact mk_le_mk (WithZero.coe_le_coe.mp hxy)

end QuotientOrder

end OrderedQuotient

/-! ### The value group of `A_𝔭` is `Γ/Δ` -/

section LocalizationValueGroup

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- The localization `A_𝔭` of `O` at the prime `𝔭`, as a subring of `K`. -/
def localizationSubring (p : Ideal O) (hp : p.IsPrime) : Subring K where
  carrier := {x | ∃ a : O, ∃ s : O, s ∉ p ∧ x * algebraMap O K s = algebraMap O K a}
  zero_mem' := ⟨0, 1, fun h => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr h), by simp⟩
  one_mem' := ⟨1, 1, fun h => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr h), by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * t + b * s, s * t, ?_, ?_⟩
    · exact fun hmem => (hp.mem_or_mem hmem).elim hs ht
    · rw [map_add, map_mul, map_mul, map_mul, add_mul]
      congr 1
      · rw [← mul_assoc, hx]
      · rw [mul_comm (algebraMap O K s), ← mul_assoc, hy]
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    exact ⟨-a, s, hs, by rw [map_neg, neg_mul, hx]⟩
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * b, s * t, ?_, ?_⟩
    · exact fun hmem => (hp.mem_or_mem hmem).elim hs ht
    · rw [map_mul, map_mul, ← hx, ← hy]
      ring

theorem mem_localizationSubring_iff {p : Ideal O} {hp : p.IsPrime} {x : K} :
    x ∈ localizationSubring (O := O) p hp ↔
      ∃ a : O, ∃ s : O, s ∉ p ∧ x * algebraMap O K s = algebraMap O K a := Iff.rfl

end LocalizationValueGroup

/-! ### The value group of `A_𝔭` is `Γ/Δ` -/

section DeltaOfPrimeLemmas

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- An element of `O` outside `𝔭` has its value in `Δ(𝔭)`. -/
theorem exists_mem_deltaOfPrime (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {s : O}
    (hs : s ∉ p) : ∃ δ : Γ, δ ∈ deltaOfPrime v p hp ∧ v (algebraMap O K s) = (δ : WithZero Γ) := by
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ p.zero_mem)
  have hv0 : v (algebraMap O K s) ≠ 0 := by
    rw [ne_eq, v_eq_zero_iff]
    intro h0
    exact hs0 (hv.hom_inj (by simpa using h0))
  refine ⟨WithZero.unzero hv0, ?_, (WithZero.coe_unzero hv0).symm⟩
  exact (mem_deltaOfPrime_of_valuation_eq hv p hp hs (WithZero.coe_unzero hv0).symm).1

/-- Division form of membership in `Δ(𝔭)`. -/
theorem deltaOfPrime_eq_div (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {γ : Γ}
    (hγ : γ ∈ deltaOfPrime v p hp) :
    ∃ a b : O, a ∉ p ∧ b ∉ p ∧
      (γ : WithZero Γ) = v (algebraMap O K a) / v (algebraMap O K b) := by
  obtain ⟨a, b, ha, hb, h⟩ := hγ
  have hb0 : b ≠ 0 := fun h0 => hb (h0 ▸ p.zero_mem)
  have hvb : v (algebraMap O K b) ≠ 0 := by
    rw [ne_eq, v_eq_zero_iff]
    intro h0
    exact hb0 (hv.hom_inj (by simpa using h0))
  refine ⟨a, b, ha, hb, ?_⟩
  rw [eq_div_iff hvb]
  exact h.symm

end DeltaOfPrimeLemmas

section ValueGroupLocalization

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- The composite valuation `K → Γ/Δ`, where `Δ` is an isolated subgroup. -/
noncomputable def quotientValuation (Δ : Subgroup Γ) [IsIsolated Δ] :
    Valuation K (WithZero (Γ ⧸ Δ)) :=
  v.map (QuotientOrder.quotientHom (Δ := Δ)) (QuotientOrder.quotientHom_monotone (Δ := Δ))

theorem quotientValuation_apply (Δ : Subgroup Γ) [IsIsolated Δ] (x : K) :
    quotientValuation (v := v) (Δ := Δ) x = QuotientOrder.quotientHom (Δ := Δ) (v x) := rfl

/-- For `x ≠ 0`, `w x ≤ 1` iff `v x ≤ δ` for some `δ ∈ Δ`. -/
theorem quotientValuation_le_one_iff (Δ : Subgroup Γ) [IsIsolated Δ] {x : K} (hx : x ≠ 0) :
    quotientValuation (v := v) (Δ := Δ) x ≤ 1 ↔ ∃ δ : Γ, δ ∈ Δ ∧ v x ≤ (δ : WithZero Γ) := by
  have hv0 : v x ≠ 0 := by rw [ne_eq, v_eq_zero_iff]; exact hx
  obtain ⟨ξ, hξ : (ξ : WithZero Γ) = v x⟩ : ∃ ξ : Γ, (ξ : WithZero Γ) = v x :=
    ⟨WithZero.unzero hv0, WithZero.coe_unzero hv0⟩
  have key : quotientValuation (v := v) (Δ := Δ) x =
      ((QuotientGroup.mk ξ : Γ ⧸ Δ) : WithZero (Γ ⧸ Δ)) := by
    rw [quotientValuation_apply, ← hξ, QuotientOrder.coe_quotientHom]
    rfl
  rw [key, ← WithZero.coe_one, WithZero.coe_le_coe, QuotientOrder.mk_le_one_iff]
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, by rw [← hξ, WithZero.coe_le_coe]; exact h⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, by rw [← hξ] at h; exact WithZero.coe_le_coe.mp h⟩

/-- The composite valuation is surjective onto `Γ/Δ`. -/
theorem quotientValuation_surjective (Δ : Subgroup Γ) [IsIsolated Δ]
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    Function.Surjective (quotientValuation (v := v) (Δ := Δ)) := by
  intro y
  match y with
  | 0 => exact ⟨0, map_zero _⟩
  | (z : Γ ⧸ Δ) =>
    refine ⟨Classical.choose (hsurj (Quotient.out z)), ?_⟩
    rw [quotientValuation_apply, Classical.choose_spec (hsurj (Quotient.out z)),
      QuotientOrder.coe_quotientHom]
    congr 1
    exact Quotient.out_eq z

/-- **A–M 5.32, value group of `A_𝔭`**: the composite valuation `K → Γ/Δ` has integer ring
exactly the localization `A_𝔭 ⊆ K`.  Hence the value group of `A_𝔭` is `Γ/Δ`. -/
theorem quotientValuation_integer (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ))
    [IsIsolated (deltaOfPrime v p hp)] :
    (quotientValuation (v := v) (Δ := deltaOfPrime v p hp)).integer =
      localizationSubring (O := O) p hp := by
  ext x
  rw [Valuation.mem_integer_iff]
  constructor
  · intro hx1
    by_cases hx0 : x = 0
    · rw [hx0]
      exact (localizationSubring (O := O) p hp).zero_mem
    · obtain ⟨δ, hδ, hle⟩ :=
        (quotientValuation_le_one_iff (v := v) (Δ := deltaOfPrime v p hp) hx0).mp hx1
      obtain ⟨b, c, hb, hc, hδeq⟩ := deltaOfPrime_eq_div (v := v) hv p hp hδ
      have hc0 : (algebraMap O K c) ≠ 0 := by
        intro h0
        have hc' : c = 0 := hv.hom_inj (by simp [h0])
        rw [hc'] at hc
        exact hc p.zero_mem
      have hbne : b ≠ 0 := fun h0 => hb (h0 ▸ p.zero_mem)
      have hbK : (algebraMap O K b) ≠ 0 := by
        intro h0
        have hb' : b = 0 := hv.hom_inj (by simp [h0])
        rw [hb'] at hb
        exact hb p.zero_mem
      have hbpos : (0 : WithZero Γ) < v (algebraMap O K b) := by
        rw [WithZero.pos_iff_ne_zero]
        intro h0
        exact hbK (v_eq_zero_iff.mp h0)
      have h1 : v (x * algebraMap O K c) ≤ v (algebraMap O K b) := by
        have hvc : v (algebraMap O K c) ≠ 0 := by
          rw [ne_eq, v_eq_zero_iff]; exact hc0
        calc v (x * algebraMap O K c)
            = v x * v (algebraMap O K c) := Valuation.map_mul v _ _
          _ ≤ (v (algebraMap O K b) / v (algebraMap O K c)) * v (algebraMap O K c) := by
              rw [hδeq] at hle
              exact mul_le_mul_of_nonneg_right hle zero_le
          _ = v (algebraMap O K b) := div_mul_cancel₀ _ hvc
      have hle' : v (x * algebraMap O K c / algebraMap O K b) ≤ 1 := by
        rw [Valuation.map_div, div_le_iff₀ hbpos, one_mul]
        exact h1
      obtain ⟨a₀, ha₀⟩ := hv.exists_of_le_one hle'
      have heq : x * algebraMap O K c = algebraMap O K a₀ * algebraMap O K b := by
        rw [ha₀, div_mul_cancel₀ _ hbK]
      rw [mem_localizationSubring_iff]
      exact ⟨a₀ * b, c, hc, by rw [map_mul, heq, mul_comm]⟩
  · intro hxmem
    obtain ⟨a, s, hs, hxs⟩ := hxmem
    have hsne : s ≠ 0 := fun h0 => hs (h0 ▸ p.zero_mem)
    have hs0 : (algebraMap O K s) ≠ 0 := by
      intro h0
      have hs' : s = 0 := hv.hom_inj (by simp [h0])
      rw [hs'] at hs
      exact hs p.zero_mem
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
      exact zero_le
    · have hxval : v x = v (algebraMap O K a) / v (algebraMap O K s) := by
        have hxeq : x = algebraMap O K a / algebraMap O K s := by
          rw [eq_div_iff hs0]
          exact hxs
        rw [hxeq, Valuation.map_div]
      obtain ⟨δ₀, hδ₀, hvs⟩ := exists_mem_deltaOfPrime (v := v) hv p hp hs
      have hδinv : δ₀⁻¹ ∈ deltaOfPrime v p hp := Subgroup.inv_mem _ hδ₀
      rw [quotientValuation_le_one_iff (v := v) (Δ := deltaOfPrime v p hp) hx0]
      refine ⟨δ₀⁻¹, hδinv, ?_⟩
      rw [WithZero.coe_inv, hxval]
      have hstep : v (algebraMap O K a) / v (algebraMap O K s) ≤ 1 / v (algebraMap O K s) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hv.map_le_one a) zero_le
      calc v (algebraMap O K a) / v (algebraMap O K s)
          ≤ 1 / v (algebraMap O K s) := hstep
        _ = (v (algebraMap O K s))⁻¹ := by rw [one_div]
        _ = ((δ₀ : WithZero Γ))⁻¹ := by rw [← hvs]
        _ = ((δ₀⁻¹ : Γ) : WithZero Γ) := by rw [WithZero.coe_inv]

/-- **A–M 5.32 (third assertion), `A_𝔭` part**: the value group of `A_𝔭` is `Γ/Δ`. -/
theorem valueGroup_localization (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    letI : IsIsolated (deltaOfPrime v p hp) := isIsolated_deltaOfPrime hv p hp hsurj
    ∃ w : Valuation K (WithZero (Γ ⧸ deltaOfPrime v p hp)),
      Function.Surjective w ∧ w.integer = localizationSubring (O := O) p hp := by
  haveI : IsIsolated (deltaOfPrime v p hp) := isIsolated_deltaOfPrime hv p hp hsurj
  exact ⟨quotientValuation (v := v) (Δ := deltaOfPrime v p hp),
    quotientValuation_surjective _ hsurj, quotientValuation_integer hv p hp hsurj⟩

end ValueGroupLocalization

/-! ### The value group of `A/𝔭` is `Δ` -/

section QuotientValueGroup

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- A non-unit of `O` inside `𝔭` has smaller value than an element outside `𝔭`. -/
theorem valuation_lt_of_mem_of_notMem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    {r a : O} (hr : r ∈ p) (ha : a ∉ p) :
    v (algebraMap O K r) < v (algebraMap O K a) := by
  have hvr : ¬ ∃ γ : Γ, γ ∈ deltaOfPrime v p hp ∧ v (algebraMap O K r) = (γ : WithZero Γ) := by
    rintro ⟨γ, hγ, hγv⟩
    have hγ1 : γ ≤ 1 := by
      rw [← WithZero.coe_le_one, ← hγv]
      exact hv.map_le_one r
    obtain ⟨c, hc, hcv⟩ := mem_primeValueSet_of_mem_deltaOfPrime hv p hp hγ hγ1
    have hcK : (algebraMap O K c) ≠ 0 := by
      intro h0
      have hc' : c = 0 := hv.hom_inj (by simp [h0])
      rw [hc'] at hc
      exact hc p.zero_mem
    have hwc : v (algebraMap O K r / algebraMap O K c) = 1 := by
      rw [Valuation.map_div, hγv, hcv]
      exact div_self (WithZero.coe_ne_zero (a := γ))
    obtain ⟨u, hu⟩ := hv.exists_of_le_one (le_of_eq hwc)
    have hvu : v (algebraMap O K u) = 1 := by rw [hu, hwc]
    have hunit : IsUnit u := (Valuation.Integers.isUnit_iff_valuation_eq_one hv).mpr hvu
    obtain ⟨u', hu'⟩ := hunit.exists_right_inv
    have hcrel : algebraMap O K r = algebraMap O K c * algebraMap O K u := by
      rw [hu]
      exact (mul_div_cancel₀ (algebraMap O K r) hcK).symm
    have hceq : c = r * u' := by
      apply hv.hom_inj
      rw [map_mul, hcrel, mul_assoc, ← map_mul, hu', map_one, mul_one]
    rw [hceq] at hc
    exact hc (Ideal.mul_mem_right u' p hr)
  rcases lt_or_ge (v (algebraMap O K r)) (v (algebraMap O K a)) with h | h
  · exact h
  · exact absurd (exists_mem_deltaOfPrime (v := v) hv p hp ha) (by
      rintro ⟨γ, hγ, hγv⟩
      have hle : (γ : WithZero Γ) ≤ v (algebraMap O K r) := by rw [← hγv]; exact h
      obtain ⟨δ, hδ, hδeq⟩ :=
        IsIsolated.mem_of_le_of_le_one₀ (Δ := deltaOfPrime v p hp)
          (inferInstance : IsIsolated (deltaOfPrime v p hp)) hγ hle (hv.map_le_one r)
      exact hvr ⟨δ, hδ, hδeq.symm⟩)

/-- The value of an element of `O` outside `𝔭`, as an element of `Δ`. -/
noncomputable def deltaVal (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O}
    (ha : a ∉ p) : deltaOfPrime v p hp :=
  ⟨WithZero.unzero (by
      intro h
      have h0 : algebraMap O K a = 0 := (v_eq_zero_iff (v := v)).mp h
      have ha0 : a = 0 := hv.hom_inj (by rw [h0, map_zero])
      exact ha (ha0 ▸ p.zero_mem)),
   (mem_deltaOfPrime_of_valuation_eq hv p hp ha (WithZero.coe_unzero _).symm).1⟩

theorem coe_deltaVal (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O} (ha : a ∉ p) :
    ((deltaVal hv p hp ha : deltaOfPrime v p hp) : WithZero Γ) = v (algebraMap O K a) :=
  WithZero.coe_unzero _

theorem deltaVal_le_one (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O} (ha : a ∉ p) :
    (deltaVal hv p hp ha : Γ) ≤ 1 := by
  rw [← WithZero.coe_le_one, coe_deltaVal hv p hp ha]
  exact hv.map_le_one a

/-- The `Δ`-valued value function on representatives. -/
noncomputable def repFun (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) (a : O) :
    WithZero (deltaOfPrime v p hp) :=
  if ha : a ∈ p then 0 else ((deltaVal hv p hp ha : deltaOfPrime v p hp) : WithZero (deltaOfPrime v p hp))

theorem repFun_of_mem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O} (ha : a ∈ p) :
    repFun hv p hp a = 0 := dif_pos ha

theorem repFun_of_notMem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O}
    (ha : a ∉ p) :
    repFun hv p hp a = ((deltaVal hv p hp ha : deltaOfPrime v p hp) : WithZero (deltaOfPrime v p hp)) :=
  dif_neg ha

/-- `repFun` is constant on residue classes modulo `𝔭`. -/
theorem repFun_eq_of_sub_mem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    {a b : O} (h : a - b ∈ p) : repFun hv p hp a = repFun hv p hp b := by
  by_cases ha : a ∈ p
  · rw [repFun_of_mem hv p hp ha]
    by_cases hb : b ∈ p
    · rw [repFun_of_mem hv p hp hb]
    · exfalso
      apply hb
      have h1 : b = a - (a - b) := by ring
      rw [h1]
      exact p.sub_mem ha h
  · by_cases hb : b ∈ p
    · exfalso
      apply ha
      have h1 : a = b + (a - b) := by ring
      rw [h1]
      exact p.add_mem hb h
    · rw [repFun_of_notMem hv p hp ha, repFun_of_notMem hv p hp hb, WithZero.coe_inj]
      apply Subtype.ext
      apply WithZero.coe_inj.mp
      have hva : v (algebraMap O K a) = v (algebraMap O K b) := by
        have hlt : v (algebraMap O K (a - b)) < v (algebraMap O K b) :=
          valuation_lt_of_mem_of_notMem hv p hp hsurj h hb
        have hsum : algebraMap O K a = algebraMap O K b + algebraMap O K (a - b) := by
          rw [← map_add]
          congr 1
          ring
        rw [hsum, Valuation.map_add_eq_of_lt_left (v := v) hlt]
      rw [coe_deltaVal hv p hp ha, coe_deltaVal hv p hp hb]
      exact hva

end QuotientValueGroup

section QuotientRingValuation

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

/-- The value function of `A/𝔭` on representatives, with values in `Γ ∪ {0}`. -/
noncomputable def repVal (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) (a : O) :
    WithZero Γ :=
  if ha : a ∈ p then 0 else v (algebraMap O K a)

theorem repVal_of_mem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O} (ha : a ∈ p) :
    repVal hv p hp a = 0 := dif_pos ha

theorem repVal_of_notMem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O}
    (ha : a ∉ p) : repVal hv p hp a = v (algebraMap O K a) := dif_neg ha

theorem repVal_zero_iff (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) {a : O} :
    repVal hv p hp a = 0 ↔ a ∈ p := by
  constructor
  · intro h
    by_contra ha
    rw [repVal_of_notMem hv p hp ha] at h
    have ha0 : a = 0 := hv.hom_inj (by rw [(v_eq_zero_iff (v := v)).mp h, map_zero])
    rw [ha0] at ha
    exact ha p.zero_mem
  · intro ha
    exact repVal_of_mem hv p hp ha

theorem repVal_one (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) :
    repVal hv p hp (1 : O) = 1 := by
  have h1 : (1 : O) ∉ p := fun h => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr h)
  rw [repVal_of_notMem hv p hp h1, map_one, Valuation.map_one]

/-- `repVal` is constant on residue classes modulo `𝔭`. -/
theorem repVal_eq_of_sub_mem (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    {a b : O} (h : a - b ∈ p) : repVal hv p hp a = repVal hv p hp b := by
  by_cases ha : a ∈ p
  · rw [repVal_of_mem hv p hp ha]
    by_cases hb : b ∈ p
    · rw [repVal_of_mem hv p hp hb]
    · exfalso
      apply hb
      have h1 : b = a - (a - b) := by ring
      rw [h1]
      exact p.sub_mem ha h
  · by_cases hb : b ∈ p
    · exfalso
      apply ha
      have h1 : a = b + (a - b) := by ring
      rw [h1]
      exact p.add_mem hb h
    · rw [repVal_of_notMem hv p hp ha, repVal_of_notMem hv p hp hb]
      have hlt : v (algebraMap O K (a - b)) < v (algebraMap O K b) :=
        valuation_lt_of_mem_of_notMem hv p hp hsurj h hb
      have hsum : algebraMap O K a = algebraMap O K b + algebraMap O K (a - b) := by
        rw [← map_add]
        congr 1
        ring
      rw [hsum, Valuation.map_add_eq_of_lt_left (v := v) hlt]

theorem repVal_mul (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) (a b : O) :
    repVal hv p hp (a * b) = repVal hv p hp a * repVal hv p hp b := by
  by_cases ha : a ∈ p
  · rw [repVal_of_mem hv p hp ha,
      repVal_of_mem hv p hp (Ideal.mul_mem_right b p ha), zero_mul]
  · by_cases hb : b ∈ p
    · rw [repVal_of_mem hv p hp hb,
        repVal_of_mem hv p hp (Ideal.mul_mem_left p a hb), mul_zero]
    · have hab : a * b ∉ p := fun h => (hp.mem_or_mem h).elim ha hb
      rw [repVal_of_notMem hv p hp ha, repVal_of_notMem hv p hp hb,
        repVal_of_notMem hv p hp hab, map_mul, Valuation.map_mul]

theorem repVal_add_le (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    (a b : O) :
    repVal hv p hp (a + b) ≤ max (repVal hv p hp a) (repVal hv p hp b) := by
  by_cases hab : a + b ∈ p
  · rw [repVal_of_mem hv p hp hab]
    exact bot_le
  · by_cases ha : a ∈ p
    · have hb : b ∉ p := fun h => hab (p.add_mem ha h)
      have hlt : v (algebraMap O K a) < v (algebraMap O K b) :=
        valuation_lt_of_mem_of_notMem hv p hp hsurj ha hb
      have hsum : algebraMap O K (a + b) = algebraMap O K b + algebraMap O K a := by
        rw [map_add]
        ring
      rw [repVal_of_notMem hv p hp hab, repVal_of_mem hv p hp ha, repVal_of_notMem hv p hp hb,
        hsum, Valuation.map_add_eq_of_lt_left (v := v) hlt]
      exact le_max_right _ _
    · by_cases hb : b ∈ p
      · have hlt : v (algebraMap O K b) < v (algebraMap O K a) :=
          valuation_lt_of_mem_of_notMem hv p hp hsurj hb ha
        have hsum : algebraMap O K (a + b) = algebraMap O K a + algebraMap O K b := map_add _ _ _
        rw [repVal_of_notMem hv p hp hab, repVal_of_mem hv p hp hb, repVal_of_notMem hv p hp ha,
          hsum, Valuation.map_add_eq_of_lt_left (v := v) hlt]
        exact le_max_left _ _
      · rw [repVal_of_notMem hv p hp hab, repVal_of_notMem hv p hp ha, repVal_of_notMem hv p hp hb,
          map_add]
        exact Valuation.map_add v _ _

end QuotientRingValuation

section QuotientValuationFinal

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

theorem repVal_out_mk (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    (a : O) : repVal hv p hp (Quotient.out (Ideal.Quotient.mk p a)) = repVal hv p hp a := by
  apply repVal_eq_of_sub_mem hv p hp hsurj
  have h : Ideal.Quotient.mk p (Quotient.out (Ideal.Quotient.mk p a)) = Ideal.Quotient.mk p a :=
    Ideal.Quotient.mk_out _
  exact (Ideal.Quotient.eq).mp h

/-- The valuation on `A/𝔭` with values in `Γ ∪ {0}`; its values on nonzero elements are
exactly the elements of `Δ`. -/
noncomputable def quotientRingValuation (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)] :
    Valuation (O ⧸ p) (WithZero Γ) where
  toFun := fun x => repVal hv p hp (Quotient.out x)
  map_zero' := by
    have h0 : Ideal.Quotient.mk p (Quotient.out (0 : O ⧸ p)) = (0 : O ⧸ p) := Ideal.Quotient.mk_out _
    have h0' : Ideal.Quotient.mk p (Quotient.out (0 : O ⧸ p)) = Ideal.Quotient.mk p (0 : O) := by
      rw [h0, map_zero]
    exact repVal_of_mem hv p hp (by simpa using (Ideal.Quotient.eq).mp h0')
  map_one' := by
    have h1 : (1 : O) ∉ p := fun h => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr h)
    have h1' : Ideal.Quotient.mk p (Quotient.out (1 : O ⧸ p)) = Ideal.Quotient.mk p (1 : O) := by
      rw [Ideal.Quotient.mk_out, map_one]
    rw [repVal_eq_of_sub_mem hv p hp hsurj ((Ideal.Quotient.eq).mp h1'), repVal_one hv p hp]
  map_mul' := by
    intro x y
    have hsub : Quotient.out (x * y) - Quotient.out x * Quotient.out y ∈ p := by
      apply (Ideal.Quotient.eq).mp
      rw [Ideal.Quotient.mk_out, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]
    rw [repVal_eq_of_sub_mem hv p hp hsurj hsub, repVal_mul]
  map_add_le_max' := by
    intro x y
    have hsub : Quotient.out (x + y) - (Quotient.out x + Quotient.out y) ∈ p := by
      apply (Ideal.Quotient.eq).mp
      rw [Ideal.Quotient.mk_out, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]
    rw [repVal_eq_of_sub_mem hv p hp hsurj hsub]
    exact repVal_add_le hv p hp hsurj _ _

/-- The induced valuation on the fraction field of `A/𝔭`. -/
noncomputable def quotientFieldValuation (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)] :
    Valuation (FractionRing (O ⧸ p)) (WithZero Γ) :=
  Valuation.extendToLocalization (quotientRingValuation hv p hp hsurj)
    (fun x hx => by
      haveI : IsDomain (O ⧸ p) := inferInstance
      have hx0 : (x : O ⧸ p) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp hx
      intro hzero
      apply hx0
      have hmem : Quotient.out (x : O ⧸ p) ∈ p := (repVal_zero_iff hv p hp).mp hzero
      rw [← Ideal.Quotient.mk_out (I := p) (x : O ⧸ p)]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem)
    (FractionRing (O ⧸ p))

theorem quotientFieldValuation_algebraMap (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    (a : O ⧸ p) :
    quotientFieldValuation hv p hp hsurj (algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) a) =
      quotientRingValuation hv p hp hsurj a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

end QuotientValuationFinal

section QuotientValueGroupMain

variable {K : Type u} [Field K]
variable {Γ : Type v} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
variable {O : Type w} [CommRing O] [Algebra O K]
variable {v : Valuation K (WithZero Γ)}

theorem quotientRingValuation_mk (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) [IsIsolated (deltaOfPrime v p hp)]
    (a : O) :
    quotientRingValuation hv p hp hsurj (Ideal.Quotient.mk p a) = repVal hv p hp a :=
  repVal_out_mk hv p hp hsurj a

theorem repVal_le_one (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime) (a : O) :
    repVal hv p hp a ≤ 1 := by
  by_cases ha : a ∈ p
  · rw [repVal_of_mem hv p hp ha]
    exact bot_le
  · rw [repVal_of_notMem hv p hp ha]
    exact hv.map_le_one a

/-- **A–M 5.32 (third assertion), `A/𝔭` part**: on the fraction field of `A/𝔭` there is a
valuation whose integer ring is `A/𝔭` itself and whose values on nonzero elements are
exactly the isolated subgroup `Δ`: the value group of `A/𝔭` is `Δ`. -/
theorem valueGroup_quotient (hv : v.Integers O) (p : Ideal O) (hp : p.IsPrime)
    (hsurj : ∀ γ : Γ, ∃ x : K, v x = (γ : WithZero Γ)) :
    letI : IsIsolated (deltaOfPrime v p hp) := isIsolated_deltaOfPrime hv p hp hsurj
    ∃ U : Valuation (FractionRing (O ⧸ p)) (WithZero Γ),
      (∀ γ : Γ, (∃ x, U x = (γ : WithZero Γ)) ↔ γ ∈ deltaOfPrime v p hp) ∧
      U.integer = (algebraMap (O ⧸ p) (FractionRing (O ⧸ p))).range := by
  haveI : IsIsolated (deltaOfPrime v p hp) := isIsolated_deltaOfPrime hv p hp hsurj
  haveI : IsDomain (O ⧸ p) := inferInstance
  refine ⟨quotientFieldValuation hv p hp hsurj, ?_, ?_⟩
  · intro γ
    constructor
    · rintro ⟨x, hx⟩
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [map_zero] at hx
        exact WithZero.coe_ne_zero hx.symm
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (O ⧸ p) x
      have hb0 : b ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp hb
      have hbn : Quotient.out b ∉ p := by
        intro hmem
        apply hb0
        have h : Ideal.Quotient.mk p (Quotient.out b) = (0 : O ⧸ p) :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
        rw [← Ideal.Quotient.mk_out (I := p) b, h]
      have hbval : quotientRingValuation hv p hp hsurj b = repVal hv p hp (Quotient.out b) := by
        conv_lhs => rw [← Ideal.Quotient.mk_out (I := p) b]
        exact quotientRingValuation_mk hv p hp hsurj (Quotient.out b)
      have hbne : repVal hv p hp (Quotient.out b) ≠ 0 := by
        rw [ne_eq, repVal_zero_iff]
        exact hbn
      have hUx : quotientFieldValuation hv p hp hsurj x =
          quotientRingValuation hv p hp hsurj a / quotientRingValuation hv p hp hsurj b := by
        rw [← hab, Valuation.map_div, quotientFieldValuation_algebraMap hv p hp hsurj,
          quotientFieldValuation_algebraMap hv p hp hsurj]
      -- `a ≠ 0`
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_div] at hUx
        rw [hUx] at hx
        exact WithZero.coe_ne_zero hx.symm
      have han : Quotient.out a ∉ p := by
        intro hmem
        apply ha0
        have h : Ideal.Quotient.mk p (Quotient.out a) = (0 : O ⧸ p) :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
        rw [← Ideal.Quotient.mk_out (I := p) a, h]
      have hav : quotientRingValuation hv p hp hsurj a = repVal hv p hp (Quotient.out a) := by
        conv_lhs => rw [← Ideal.Quotient.mk_out (I := p) a]
        exact quotientRingValuation_mk hv p hp hsurj (Quotient.out a)
      obtain ⟨γ₁, hγ₁, hγ₁v⟩ := exists_mem_deltaOfPrime hv p hp han
      obtain ⟨γ₂, hγ₂, hγ₂v⟩ := exists_mem_deltaOfPrime hv p hp hbn
      rw [hav, hbval, repVal_of_notMem hv p hp han, repVal_of_notMem hv p hp hbn, hγ₁v,
        hγ₂v] at hUx
      have hγeq : γ = γ₁ / γ₂ := by
        have h2 : ((γ : Γ) : WithZero Γ) = ((γ₁ / γ₂ : Γ) : WithZero Γ) := by
          rw [WithZero.coe_div]
          rw [hx] at hUx
          exact hUx
        exact WithZero.coe_inj.mp h2
      rw [hγeq]
      exact Subgroup.div_mem _ hγ₁ hγ₂
    · intro hγ
      obtain ⟨a, b, ha, hb, hγab⟩ := deltaOfPrime_eq_div hv p hp hγ
      have hb0 : (Ideal.Quotient.mk p b) ≠ 0 := by
        intro h
        exact hb ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      have ha0 : (Ideal.Quotient.mk p a) ≠ 0 := by
        intro h
        exact ha ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      refine ⟨algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) /
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p b), ?_⟩
      rw [Valuation.map_div, quotientFieldValuation_algebraMap hv p hp hsurj,
        quotientFieldValuation_algebraMap hv p hp hsurj, quotientRingValuation_mk,
        quotientRingValuation_mk, repVal_of_notMem hv p hp ha, repVal_of_notMem hv p hp hb,
        hγab]
  · ext x
    constructor
    · -- `U x ≤ 1` implies `x` is the image of an element of `A/𝔭`
      intro hx1
      rw [Valuation.mem_integer_iff] at hx1
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (O ⧸ p) x
      have hb0 : b ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp hb
      have hbn : Quotient.out b ∉ p := by
        intro hmem
        apply hb0
        have h : Ideal.Quotient.mk p (Quotient.out b) = (0 : O ⧸ p) :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
        rw [← Ideal.Quotient.mk_out (I := p) b, h]
      by_cases ha0 : a = 0
      · have hxzero : x = 0 := by
          rw [← hab, ha0, map_zero, zero_div]
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact hxzero.symm
      · have han : Quotient.out a ∉ p := by
          intro hmem
          apply ha0
          have h : Ideal.Quotient.mk p (Quotient.out a) = (0 : O ⧸ p) :=
            (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
          rw [← Ideal.Quotient.mk_out (I := p) a, h]
        have hUx : quotientFieldValuation hv p hp hsurj x =
            repVal hv p hp (Quotient.out a) / repVal hv p hp (Quotient.out b) := by
          rw [← hab, Valuation.map_div, quotientFieldValuation_algebraMap hv p hp hsurj,
            quotientFieldValuation_algebraMap hv p hp hsurj]
          rw [show quotientRingValuation hv p hp hsurj a = repVal hv p hp (Quotient.out a) from by
              conv_lhs => rw [← Ideal.Quotient.mk_out (I := p) a]
              exact quotientRingValuation_mk hv p hp hsurj (Quotient.out a),
            show quotientRingValuation hv p hp hsurj b = repVal hv p hp (Quotient.out b) from by
              conv_lhs => rw [← Ideal.Quotient.mk_out (I := p) b]
              exact quotientRingValuation_mk hv p hp hsurj (Quotient.out b)]
        rw [hUx, repVal_of_notMem hv p hp han, repVal_of_notMem hv p hp hbn] at hx1
        have hbpos : (0 : WithZero Γ) < v (algebraMap O K (Quotient.out b)) := by
          rw [WithZero.pos_iff_ne_zero]
          intro h0
          have hb0' : Quotient.out b = 0 :=
            hv.hom_inj (by rw [(v_eq_zero_iff (v := v)).mp h0, map_zero])
          rw [hb0'] at hbn
          exact hbn p.zero_mem
        have hbK : v (algebraMap O K (Quotient.out b)) ≠ 0 := ne_of_gt hbpos
        have hle : v (algebraMap O K (Quotient.out a)) ≤ v (algebraMap O K (Quotient.out b)) := by
          rw [div_le_iff₀ hbpos, one_mul] at hx1
          exact hx1
        have hquot : v (algebraMap O K (Quotient.out a) / algebraMap O K (Quotient.out b)) ≤ 1 := by
          rw [Valuation.map_div, div_le_iff₀ hbpos, one_mul]
          exact hle
        obtain ⟨c, hc⟩ := hv.exists_of_le_one hquot
        have hbK' : (algebraMap O K (Quotient.out b)) ≠ 0 := by
          intro h0
          exact (ne_of_gt hbpos) (by rw [h0, map_zero])
        have hbc : algebraMap O K (Quotient.out a) =
            algebraMap O K (Quotient.out b) * algebraMap O K c := by
          rw [hc]
          exact (mul_div_cancel₀ _ hbK').symm
        have hbc' : Quotient.out a = Quotient.out b * c := hv.hom_inj (by rw [map_mul]; exact hbc)
        refine ⟨Ideal.Quotient.mk p c, ?_⟩
        rw [← hab]
        have hone : Ideal.Quotient.mk p (Quotient.out a) =
            Ideal.Quotient.mk p (Quotient.out b) * Ideal.Quotient.mk p c := by
          rw [hbc', map_mul]
        rw [← Ideal.Quotient.mk_out (I := p) a, ← Ideal.Quotient.mk_out (I := p) b, hone,
          map_mul]
        have hbk0 : (algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p (Quotient.out b))) ≠ 0 := by
          intro h0
          have h1 : Ideal.Quotient.mk p (Quotient.out b) = 0 :=
            IsFractionRing.injective (O ⧸ p) (FractionRing (O ⧸ p)) (by rw [h0, map_zero])
          exact hbn ((Ideal.Quotient.eq_zero_iff_mem).mp h1)
        rw [mul_comm (algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p (Quotient.out b))),
          mul_div_cancel_right₀ _ hbk0]
    · rintro ⟨a, rfl⟩
      rw [Valuation.mem_integer_iff, quotientFieldValuation_algebraMap hv p hp hsurj]
      exact repVal_le_one hv p hp (Quotient.out a)

end QuotientValueGroupMain

/-! ### Axiom checks (no `sorry`, no extra axioms) -/

#print axioms AtiyahMcdonald69.Ex_5_32.primeValueSet_eq_deltaOfPrime
#print axioms AtiyahMcdonald69.Ex_5_32.isIsolated_deltaOfPrime
#print axioms AtiyahMcdonald69.Ex_5_32.primeSpectrumEquivIsolatedSubgroup
#print axioms AtiyahMcdonald69.Ex_5_32.bijective_deltaOfPrime
#print axioms AtiyahMcdonald69.Ex_5_32.valueGroup_quotient
#print axioms AtiyahMcdonald69.Ex_5_32.valueGroup_localization
