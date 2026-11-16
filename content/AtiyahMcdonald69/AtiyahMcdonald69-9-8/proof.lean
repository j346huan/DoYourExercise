/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 9 (Discrete Valuation Rings and Dedekind Domains), Exercise 8:

  Let `a`, `b`, `c` be three ideals in a Dedekind domain. Prove that
      a ∩ (b + c) = (a ∩ b) + (a ∩ c),
      a + (b ∩ c) = (a + b) ∩ (a + c).

Coverage: both displayed identities, for *all* ideals `a b c` (the exercise does
not assume them nonzero, and the statement is true without that assumption),
over any `A` satisfying Mathlib's `IsDedekindDomain A`.

`IsDedekindDomain A` in Mathlib is "Noetherian, integrally closed in its field
of fractions, Krull dimension at most one" plus "is a domain".  A–M's (9.3)
definition asks for dimension one, so Mathlib's hypothesis is slightly more
general: it also admits fields (dimension zero).  This is a genuine
generalisation, not a weakening: the proof below treats the field case
separately (all ideals are `⊥` or `⊤`), so the formal statement implies the
exercise exactly as stated in the book.

Math approach (following the natural-language solution):
* finite sums and intersections of ideals commute with localization
  (`Ideal.map_sup`, `IsLocalization.map_inf`), and equality of ideals can be
  tested after localizing at all maximal ideals
  (`Ideal.eq_of_localization_maximal`);
* at a maximal ideal `P ≠ ⊥` of a Dedekind domain, `A_P` is a discrete
  valuation ring, hence a valuation ring, hence its ideals are totally ordered
  (`Std.Total (Ideal A_P) (· ≤ ·)`), and a totally ordered lattice is
  distributive; the two displayed identities are exactly the two distributive
  laws (meet over join and join over meet);
* if `P = ⊥` is maximal then `A` is a field, where both identities are trivial.

Source of the natural-language proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-9-8
(repository j346huan/DoYourExercise, commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91)
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_9_8

open Ideal

/-! ### Two elementary lattice lemmas -/

/-- In a lattice whose order is total, `⊓` distributes over `⊔`. -/
theorem inf_sup_eq_of_total {α : Type*} [Lattice α] (h : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (a b c : α) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  rcases h b c with hbc | hbc
  · rw [sup_eq_right.mpr hbc, sup_eq_right.mpr (inf_le_inf_left a hbc)]
  · rw [sup_eq_left.mpr hbc, sup_eq_left.mpr (inf_le_inf_left a hbc)]

/-- In a lattice whose order is total, `⊔` distributes over `⊓`. -/
theorem sup_inf_eq_of_total {α : Type*} [Lattice α] (h : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (a b c : α) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rcases h b c with hbc | hbc
  · rw [inf_eq_left.mpr hbc, inf_eq_left.mpr (sup_le_sup_left hbc a)]
  · rw [inf_eq_right.mpr hbc, inf_eq_right.mpr (sup_le_sup_left hbc a)]

/-- In a field every ideal is `⊥` or `⊤`, which makes the first distributive law trivial. -/
theorem inf_sup_eq_of_divisionSemiring {K : Type*} [DivisionSemiring K] (a b c : Ideal K) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  rcases Ideal.eq_bot_or_top a with rfl | rfl <;>
    rcases Ideal.eq_bot_or_top b with rfl | rfl <;>
    rcases Ideal.eq_bot_or_top c with rfl | rfl <;> simp

/-- In a field every ideal is `⊥` or `⊤`, which makes the second distributive law trivial. -/
theorem sup_inf_eq_of_divisionSemiring {K : Type*} [DivisionSemiring K] (a b c : Ideal K) :
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rcases Ideal.eq_bot_or_top a with rfl | rfl <;>
    rcases Ideal.eq_bot_or_top b with rfl | rfl <;>
    rcases Ideal.eq_bot_or_top c with rfl | rfl <;> simp

/-! ### The ideals of a valuation ring are totally ordered -/

/-- The ideals of a valuation ring are totally ordered. -/
theorem ideal_le_total_of_valuationRing {R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (I J : Ideal R) : I ≤ J ∨ J ≤ I :=
  Std.Total.total I J

/-- The localization at a maximal ideal `P ≠ ⊥` of a Dedekind domain is a valuation ring,
hence its ideals are totally ordered. -/
theorem ideal_le_total_localization {A : Type*} [CommRing A] [IsDedekindDomain A]
    {P : Ideal A} (hP : P.IsMaximal) (hPbot : P ≠ ⊥) :
    ∀ I J : Ideal (Localization.AtPrime P), I ≤ J ∨ J ≤ I := by
  have hprime : IsPrime P := hP.isPrime
  have hdom : IsDomain (Localization.AtPrime P) := inferInstance
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hPbot _
  have hval : ValuationRing (Localization.AtPrime P) := inferInstance
  exact fun I J => ideal_le_total_of_valuationRing I J

/-! ### Exercise 9.8 -/

/-- **Atiyah–Macdonald, Exercise 9.8, first identity.**
In a Dedekind domain, intersection distributes over addition of ideals. -/
theorem inf_sup_eq (A : Type*) [CommRing A] [IsDedekindDomain A] (a b c : Ideal A) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  by_cases hA : IsField A
  · -- A field: every ideal is `⊥` or `⊤`.
    let f : Field A := hA.toField
    exact inf_sup_eq_of_divisionSemiring a b c
  · -- Reduce to the localizations at all maximal ideals.
    refine Ideal.eq_of_localization_maximal fun P hP => ?_
    have hPbot : P ≠ ⊥ := fun h => hA (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
    have htot := ideal_le_total_localization hP hPbot
    simp only [Ideal.map_sup, IsLocalization.map_inf P.primeCompl]
    exact inf_sup_eq_of_total htot _ _ _

/-- **Atiyah–Macdonald, Exercise 9.8, second identity.**
In a Dedekind domain, addition distributes over intersection of ideals. -/
theorem sup_inf_eq (A : Type*) [CommRing A] [IsDedekindDomain A] (a b c : Ideal A) :
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  by_cases hA : IsField A
  · let f : Field A := hA.toField
    exact sup_inf_eq_of_divisionSemiring a b c
  · refine Ideal.eq_of_localization_maximal fun P hP => ?_
    have hPbot : P ≠ ⊥ := fun h => hA (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
    have htot := ideal_le_total_localization hP hPbot
    simp only [Ideal.map_sup, IsLocalization.map_inf P.primeCompl]
    exact sup_inf_eq_of_total htot _ _ _

/-- **Atiyah–Macdonald, Exercise 9.8** (both identities). -/
theorem solution (A : Type*) [CommRing A] [IsDedekindDomain A] (a b c : Ideal A) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) ∧ a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
  ⟨inf_sup_eq A a b c, sup_inf_eq A a b c⟩

end AtiyahMcdonald69.Ex_9_8
