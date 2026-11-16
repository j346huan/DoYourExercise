/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 1, Exercise 1 (p. 10):

  "Let x be a nilpotent element of a ring A. Show that 1 + x is a unit of A.
   Deduce that the sum of a nilpotent element and a unit is a unit."

The statement was checked against the local book transcriptions:
* `.scratch/reference/atiyah-macdonald-original.txt`, Chapter 1 exercises, item 1:
  "1. Let x be a nilpotent element of a ring A. Show that 1 + x is a unit of A.
   Deduce that the sum of a nilpotent element and a unit is a unit."
* `.scratch/dl/amcd.tex`, "Page 10, Exercise 1.1": same text, with the solution
  "If x is nilpotent, then ∑_{n≥0} xⁿ is the inverse of 1 - x. If u is a unit and x is
  nilpotent, then u + x = u (1 + x/u) is a unit."

Formalization notes.
* As in the book, `A` is a commutative ring with `1` (Mathlib `CommRing A`).  No
  `Nontrivial A` hypothesis is added, so the zero ring is covered: there `x = 0` is
  nilpotent (indeed `x ^ 0 = 0`) and `1 + x = 0 = 1` is a unit.
* Commutativity is genuinely used in the deduction: for a unit `u` with inverse `u⁻¹`
  the element `u⁻¹ * x` is nilpotent, hence `u * (1 + u⁻¹ * x) = u + x` is a product
  of units.  (In a noncommutative ring `(u⁻¹ * x)ⁿ ≠ u⁻ⁿ * xⁿ` in general.)
* Everything is proved from the geometric-series identity
  `(1 + x) * ∑_{i<n} (-x)^i = 1 - (-x)^n`, i.e. the book's hint that `∑ xⁿ` is the
  inverse of `1 - x`; the Mathlib lemma `IsNilpotent.isUnit_one_add` is not used.
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace AtiyahMcdonald69.Ex_1_1

variable {A : Type*} [CommRing A]

/-! ### The geometric-series identity -/

/-- `(1 + x) * (1 - x + x² - ⋯ + (-x)^{n-1}) = 1 - (-x)^n`. -/
theorem one_add_mul_geom_sum_neg (x : A) (n : ℕ) :
    (1 + x) * ∑ i ∈ Finset.range n, (-x) ^ i = 1 - (-x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- If `x ^ n = 0`, then `1 + x` has the explicit inverse `∑_{i<n} (-x)^i`. -/
theorem mul_geom_sum_eq_one (x : A) (n : ℕ) (hn : x ^ n = 0) :
    (1 + x) * (∑ i ∈ Finset.range n, (-x) ^ i) = 1 := by
  have hneg : (-x) ^ n = 0 := by rw [neg_pow, hn, mul_zero]
  rw [one_add_mul_geom_sum_neg, hneg, sub_zero]

/-- The same identity with the factors swapped. -/
theorem geom_sum_mul_eq_one (x : A) (n : ℕ) (hn : x ^ n = 0) :
    (∑ i ∈ Finset.range n, (-x) ^ i) * (1 + x) = 1 := by
  rw [mul_comm, mul_geom_sum_eq_one x n hn]

/-- The book's explicit hint for `1 - x`: `(1 - x) * (1 + x + ⋯ + x^{n-1}) = 1 - x^n`. -/
theorem one_sub_mul_geom_sum (x : A) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, x ^ i = 1 - x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- If `x ^ n = 0`, then `1 - x` has the explicit inverse `∑_{i<n} x^i`. -/
theorem mul_geom_sum_eq_one_sub (x : A) (n : ℕ) (hn : x ^ n = 0) :
    (1 - x) * (∑ i ∈ Finset.range n, x ^ i) = 1 := by
  rw [one_sub_mul_geom_sum, hn, sub_zero]

/-- The same identity for `1 - x` with the factors swapped. -/
theorem geom_sum_mul_eq_one_sub (x : A) (n : ℕ) (hn : x ^ n = 0) :
    (∑ i ∈ Finset.range n, x ^ i) * (1 - x) = 1 := by
  rw [mul_comm, mul_geom_sum_eq_one_sub x n hn]

/-! ### Part 1: `1 + x` is a unit for nilpotent `x` -/

/-- **Exercise 1.1, first claim.**  If `x` is nilpotent then `1 + x` is a unit. -/
theorem isUnit_one_add (x : A) (hx : IsNilpotent x) : IsUnit (1 + x) := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨⟨1 + x, ∑ i ∈ Finset.range n, (-x) ^ i,
    mul_geom_sum_eq_one x n hn, geom_sum_mul_eq_one x n hn⟩, rfl⟩

/-- The book's preliminary remark in its original form: "if `x` is nilpotent, then
`∑_{n≥0} xⁿ` is the inverse of `1 - x`", so `1 - x` is a unit. -/
theorem isUnit_one_sub (x : A) (hx : IsNilpotent x) : IsUnit (1 - x) := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨⟨1 - x, ∑ i ∈ Finset.range n, x ^ i,
    mul_geom_sum_eq_one_sub x n hn, geom_sum_mul_eq_one_sub x n hn⟩, rfl⟩

/-! ### Part 2: the sum of a nilpotent element and a unit is a unit -/

/-- A multiple of a nilpotent element is nilpotent. -/
theorem isNilpotent_mul_left (x y : A) (hx : IsNilpotent x) : IsNilpotent (y * x) := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [mul_pow, hn, mul_zero]⟩

/-- A unit multiple of a nilpotent element is nilpotent. -/
theorem isNilpotent_mul_of_isUnit (x u : A) (hx : IsNilpotent x) (hu : IsUnit u) :
    IsNilpotent (u * x) := by
  obtain ⟨v, rfl⟩ := hu
  exact isNilpotent_mul_left x (↑v : A) hx

/-- **Exercise 1.1, second claim** ("the sum of a nilpotent element and a unit is a
unit"), in the order `nilpotent + unit`. -/
theorem isUnit_add_of_isNilpotent_of_isUnit (x u : A) (hx : IsNilpotent x)
    (hu : IsUnit u) : IsUnit (x + u) := by
  obtain ⟨v, rfl⟩ := hu
  -- `v⁻¹ * x` is nilpotent, so `1 + v⁻¹ * x` is a unit, and `v * (1 + v⁻¹ * x) = v + x`.
  have hnil : IsNilpotent ((↑v⁻¹ : A) * x) :=
    isNilpotent_mul_of_isUnit x (↑v⁻¹ : A) hx v⁻¹.isUnit
  have h1 : IsUnit (1 + (↑v⁻¹ : A) * x) := isUnit_one_add _ hnil
  have h2 : IsUnit ((↑v : A) * (1 + (↑v⁻¹ : A) * x)) := v.isUnit.mul h1
  have heq : (↑v : A) * (1 + (↑v⁻¹ : A) * x) = (↑v : A) + x := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [heq] at h2
  simpa only [add_comm] using h2

/-- **Exercise 1.1, second claim**, in the order `unit + nilpotent`. -/
theorem isUnit_add_of_isUnit_of_isNilpotent (x u : A) (hx : IsNilpotent x)
    (hu : IsUnit u) : IsUnit (u + x) := by
  simpa only [add_comm] using isUnit_add_of_isNilpotent_of_isUnit x u hx hu

/-! ### The exercise, as stated in the book -/

/-- **Atiyah–Macdonald, Chapter 1, Exercise 1**, both claims together:
`1 + x` is a unit for nilpotent `x`, and the sum of a nilpotent element and a unit is a
unit (stated here for `unit + nilpotent`). -/
theorem solution (x : A) (hx : IsNilpotent x) :
    IsUnit (1 + x) ∧ ∀ u : A, IsUnit u → IsUnit (u + x) :=
  ⟨isUnit_one_add x hx, fun u hu => isUnit_add_of_isUnit_of_isNilpotent x u hx hu⟩

/-- The second claim of the exercise in the book's order, `nilpotent + unit`. -/
theorem solution_add (x : A) (hx : IsNilpotent x) :
    ∀ u : A, IsUnit u → IsUnit (x + u) :=
  fun u hu => isUnit_add_of_isNilpotent_of_isUnit x u hx hu

/-! ### Edge cases: the zero ring, and a ring with a nonzero nilpotent -/

section EdgeCases

/-- In the zero ring `0` is nilpotent (`0 ^ 1 = 0`) and `1 + 0 = 1 = 0` is a unit, so both
claims of the exercise hold there; no `Nontrivial` hypothesis is used. -/
example : IsUnit (1 + (0 : PUnit)) := isUnit_one_add 0 ⟨1, Subsingleton.elim _ _⟩

example : IsUnit ((0 : PUnit) + 1) :=
  solution_add 0 ⟨1, Subsingleton.elim _ _⟩ 1 isUnit_one

/-- In `ℤ/8` the element `2` is nilpotent (`2 ^ 3 = 0`), so `1 + 2 = 3` is a unit, with
explicit inverse `1 - 2 + 4 = 3`, matching `(1 + x) * ∑_{i<3} (-x)^i = 1`. -/
example : IsUnit ((1 : ZMod 8) + 2) := isUnit_one_add 2 ⟨3, by decide⟩

example : IsUnit ((2 : ZMod 8) + 1) :=
  solution_add 2 ⟨3, by decide⟩ 1 isUnit_one

example : ((1 : ZMod 8) + 2) * ∑ i ∈ Finset.range 3, (-2 : ZMod 8) ^ i = 1 :=
  mul_geom_sum_eq_one 2 3 (by decide)

/-- The `1 - x` form of the same computation: `(1 - 2) * (1 + 2 + 4) = -1 * 7 = 1` in
`ℤ/8`. -/
example : ((1 : ZMod 8) - 2) * ∑ i ∈ Finset.range 3, (2 : ZMod 8) ^ i = 1 :=
  mul_geom_sum_eq_one_sub 2 3 (by decide)

end EdgeCases

/-! ### Axiom check -/

#print axioms one_add_mul_geom_sum_neg
#print axioms mul_geom_sum_eq_one
#print axioms geom_sum_mul_eq_one
#print axioms one_sub_mul_geom_sum
#print axioms mul_geom_sum_eq_one_sub
#print axioms geom_sum_mul_eq_one_sub
#print axioms isUnit_one_add
#print axioms isUnit_one_sub
#print axioms isNilpotent_mul_left
#print axioms isNilpotent_mul_of_isUnit
#print axioms isUnit_add_of_isNilpotent_of_isUnit
#print axioms isUnit_add_of_isUnit_of_isNilpotent
#print axioms solution
#print axioms solution_add

end AtiyahMcdonald69.Ex_1_1
