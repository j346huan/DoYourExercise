/-
Copyright (c) 2026 The Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Ideal

/-!
# Atiyah–Macdonald (1969), Chapter IX, Exercise 1

## The exercise

M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley 1969,
Chapter IX (Discrete Valuation Rings and Dedekind Domains), Exercises, p. 99:

> 1. Let `A` be a Dedekind domain, `S` a multiplicatively closed subset of `A`. Show that
> `S⁻¹A` is either a Dedekind domain or the field of fractions of `A`.
> Suppose that `S ≠ A - {0}`, and let `H`, `H'` be the ideal class groups of `A` and `S⁻¹A`
> respectively. Show that extension of ideals induces a surjective homomorphism `H → H'`.

The statement is split into the assertions proved below:

* `isDedekindDomain_localization` — `S⁻¹A` is a Dedekind domain (Mathlib's notion, see below);
* `isField_iff_isFractionRing` — `S⁻¹A` is a field **iff** it is (canonically) the field of
  fractions of `A`; together with `exists_nonzero_prime_of_not_isField` this says that the two
  alternatives of the exercise are exactly "a Dedekind domain of dimension one" and "the field of
  fractions of `A`";
* `classGroup_extendedHom_surjective` — the abstract form of the second part: for any `A`-algebra
  `B` that is a localization of `A` at `S`, extension of ideals induces a surjective homomorphism
  `ClassGroup A →* ClassGroup B`;
* `classGroup_extension_surjective` — the same for `B = S⁻¹A`, with the exercise's hypothesis
  `S ≠ A - {0}`, and `solution` combining everything.

## Faithfulness and scope adaptations

* `S` multiplicatively closed with `0 ∉ S` is expressed as `S ≤ nonZeroDivisors A` (for a domain
  this is exactly `0 ∉ S`). This hypothesis is necessary as stated in the book: if `0 ∈ S` then
  `S⁻¹A` is the zero ring, which is neither a Dedekind domain nor a field. (In the book `S` is only
  assumed multiplicatively closed; the claim itself forces `0 ∉ S`.)
* Mathlib's `IsDedekindDomain A` means: `A` is a domain, Noetherian, integrally closed, and of
  Krull dimension `≤ 1` (every nonzero prime is maximal). A field satisfies this, so it is the
  union of the two alternatives of the exercise; the precise splitting of the two cases is given by
  `isField_iff_isFractionRing` and `exists_nonzero_prime_of_not_isField`.
* `H` and `H'` are Mathlib's `ClassGroup A` and `ClassGroup B`: invertible fractional ideals
  modulo principal fractional ideals, i.e. exactly the ideal class group `I/P` of Chapter IX of the
  book. In a Dedekind domain every nonzero fractional ideal is invertible (Theorem 9.8 of the book),
  which is why the class of every nonzero ideal is available in Mathlib's `ClassGroup`
  (`ClassGroup.mk0`). "Extension of ideals" is Mathlib's `ClassGroup.extendedHom`, the group
  homomorphism induced by pushing fractional ideals forward along `A → B`.
* The exercise's hypothesis `S ≠ A - {0}` is carried along as `hSne : S ≠ nonZeroDivisors A` in
  `classGroup_extension_surjective`. It is *not* needed for the argument (the source proof remarks
  that surjectivity also holds when the target class group is trivial), and the general statement
  `classGroup_extendedHom_surjective` is proved without it.

Natural-language source proof (j346huan/DoYourExercise, commit 80e1ebef):
`AtiyahMcdonald69-9-1`, <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-9-1>

The source proof runs: `S⁻¹A` is Noetherian and integrally closed, and by the prime correspondence
every nonzero prime of `S⁻¹A` is maximal, so it is a Dedekind domain unless it is a field, in which
case it is `Frac A`; extension preserves products and sends a principal fractional ideal `(x)` to
`xB`, hence induces a homomorphism of class groups, which is surjective because every nonzero
fractional ideal `J` of `S⁻¹A` is finitely generated, say `J = ∑ B xᵢ` with `xᵢ ∈ Frac A`, and then
`J` is the extension of the fractional ideal `∑ A xᵢ` of `A`.

Our formal proof of surjectivity follows the same idea in the shape that is most convenient with
Mathlib's library: every class of `ClassGroup B` has a representative which is a nonzero *integral*
ideal `J` (`ClassGroup.mk0_surjective`); its contraction `A ∩ J` is a nonzero ideal of `A` whose
extension is `J` (`IsLocalization.map_under`), so the class of `J` is the image of the class of
`A ∩ J`. This is the `A`-module version of the book's "`J = J₀·B` for an ideal `J₀` of `A`" argument,
and it is slightly stronger than what is needed (surjectivity already holds on ideals, not just on
ideal classes).
-/

set_option linter.style.haveILetI false

open scoped nonZeroDivisors

open IsLocalization

namespace AtiyahMcdonald69.Ex_9_1

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

/-! ### Preliminary: localization at nonzero divisors -/

/-- The localization of an integral domain at a submonoid of the nonzero divisors is an integral
domain. -/
lemma isDomain_localization (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    IsDomain (Localization S) :=
  IsLocalization.isDomain_localization hS

omit [IsDedekindDomain A] in
/-- The algebra map `A → S⁻¹A` is injective when `0 ∉ S`. -/
lemma injective_algebraMap_localization (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    Function.Injective (algebraMap A (Localization S)) :=
  IsLocalization.injective (Localization S) hS

/-- `S⁻¹A` is torsion free over `A` when `0 ∉ S`: both are domains and `A → S⁻¹A` is injective. -/
lemma isTorsionFree_localization (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    Module.IsTorsionFree A (Localization S) := by
  haveI : IsDomain (Localization S) := isDomain_localization S hS
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rcases eq_or_ne r 0 with hr | hr
  · exact Or.inl hr
  rcases eq_or_ne m 0 with hm | hm
  · exact Or.inr hm
  exfalso
  have hrm : algebraMap A (Localization S) r * m = 0 := by
    simpa [Algebra.smul_def] using h
  have hne : algebraMap A (Localization S) r ≠ 0 := fun hz =>
    hr (injective_algebraMap_localization S hS (by simpa using hz))
  exact mul_ne_zero hne hm hrm

/-! ### Part 1: `S⁻¹A` is a Dedekind domain, or the field of fractions of `A` -/

/-- **Atiyah–Macdonald, Chapter IX, Exercise 1 (first assertion).**
The localization `S⁻¹A` of a Dedekind domain at a multiplicatively closed subset `S` with `0 ∉ S`
is a Dedekind domain (Noetherian, integrally closed, of Krull dimension at most one; fields are
included in this notion, see `isField_iff_isFractionRing` for the precise dichotomy). -/
theorem isDedekindDomain_localization (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    IsDedekindDomain (Localization S) := by
  haveI : IsDomain (Localization S) := isDomain_localization S hS
  exact IsLocalization.isDedekindDomain A hS (Localization S)

/-- **Atiyah–Macdonald, Chapter IX, Exercise 1 (first assertion), exceptional case.**
`S⁻¹A` is a field if and only if it is the field of fractions of `A`: in that case every nonzero
element of `A` becomes invertible, so `S⁻¹A` is the localization of `A` at all nonzero elements. -/
theorem isField_iff_isFractionRing (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    IsField (Localization S) ↔ IsFractionRing A (Localization S) := by
  constructor
  · intro h
    haveI : IsDomain (Localization S) := h.isDomain
    letI : Field (Localization S) := h.toField
    refine IsLocalization.of_le S (nonZeroDivisors A) hS fun r hr => ?_
    have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    exact hr0 (injective_algebraMap_localization S hS (by simpa using hz))
  · intro h
    haveI : Nontrivial (Localization S) := IsFractionRing.nontrivial A (Localization S)
    exact ⟨⟨0, 1, zero_ne_one⟩, mul_comm,
      fun {a} ha => ⟨IsFractionRing.inv A a, IsFractionRing.mul_inv_cancel A a ha⟩⟩

/-- **The two alternatives of the exercise are exactly "dimension one" and "field".**
If `S⁻¹A` is not a field, it has a nonzero prime ideal, i.e. it is a Dedekind domain of Krull
dimension one in the sense of Atiyah–Macdonald, not a degenerate one. -/
theorem exists_nonzero_prime_of_not_isField (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
    (h : ¬ IsField (Localization S)) :
    ∃ p : Ideal (Localization S), p ≠ ⊥ ∧ p.IsPrime := by
  haveI : IsDomain (Localization S) := isDomain_localization S hS
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
  obtain ⟨u, rfl⟩ : IsUnit a := by
    by_contra hnu
    have htop : Ideal.span {a} ≠ ⊤ := fun htop => hnu (Ideal.span_singleton_eq_top.mp htop)
    obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ htop
    have hne : m ≠ ⊥ := by
      intro hbot
      have hmem : a ∈ (⊥ : Ideal (Localization S)) :=
        hbot ▸ hle (Ideal.mem_span_singleton_self a)
      exact ha (by simpa using hmem)
    exact hcon m hne hmax.isPrime
  exact ⟨(u⁻¹ : (Localization S)ˣ), u.mul_inv⟩

/-- **Atiyah–Macdonald, Chapter IX, Exercise 1 (first assertion), dichotomy form.**
`S⁻¹A` is either a Dedekind domain of Krull dimension exactly one, or the field of fractions of
`A`: the two alternatives of the exercise, with Atiyah–Macdonald's convention that a Dedekind domain
has dimension one (so a field is not one). -/
theorem dedekind_or_isFractionRing (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    (IsDedekindDomain (Localization S) ∧
        ∃ p : Ideal (Localization S), p ≠ ⊥ ∧ p.IsPrime) ∨
      IsFractionRing A (Localization S) := by
  by_cases h : IsField (Localization S)
  · exact Or.inr ((isField_iff_isFractionRing S hS).mp h)
  · exact Or.inl ⟨isDedekindDomain_localization S hS, exists_nonzero_prime_of_not_isField S hS h⟩

/-! ### Part 2: extension of ideals induces a surjective map of class groups -/

/-- **Atiyah–Macdonald, Chapter IX, Exercise 1 (second assertion), abstract form.**
Let `B` be an `A`-algebra which is the localization of the Dedekind domain `A` at a multiplicatively
closed subset `S` not containing `0`. Then extension of ideals (pushing fractional ideals forward
along `A → B`) induces a surjective homomorphism `ClassGroup A →* ClassGroup B` of ideal class
groups: every class of `B` has a nonzero integral representative `J`, and `J` is the extension of
its contraction `A ∩ J`. -/
theorem classGroup_extendedHom_surjective {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [Module.IsTorsionFree A B] (S : Submonoid A) [IsLocalization S B]
    (hS : S ≤ nonZeroDivisors A) :
    Function.Surjective (ClassGroup.extendedHom A B) := by
  haveI : IsDedekindDomain B := IsLocalization.isDedekindDomain A hS B
  intro y
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective y
  set I : Ideal A := (J : Ideal B).under A with hI
  have hIJ : Ideal.map (algebraMap A B) I = (J : Ideal B) := by
    rw [hI]
    exact IsLocalization.map_under S B (J : Ideal B)
  have hI0 : I ≠ 0 := by
    intro h0
    have hJ0 : (J : Ideal B) = ⊥ := by rw [← hIJ, h0]; simp
    have hmem : (⊥ : Ideal B) ∈ (Ideal B)⁰ := by rw [← hJ0]; exact J.2
    exact zero_notMem_nonZeroDivisors (M₀ := Ideal B) hmem
  refine ⟨ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩
  rw [← hJ, ClassGroup.extendedHom_mk0]
  congr 1
  exact Subtype.ext hIJ

set_option linter.unusedVariables false in
/-- **Atiyah–Macdonald, Chapter IX, Exercise 1 (second assertion).**
If `S ≠ A - {0}`, extension of ideals induces a surjective homomorphism
`H = ClassGroup A →* H' = ClassGroup S⁻¹A` of ideal class groups.
The extra hypothesis `S ≠ A - {0}` is exactly the book's; it is not used by the argument. -/
theorem classGroup_extension_surjective (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
    (hSne : S ≠ nonZeroDivisors A) :
    letI : IsDomain (Localization S) := isDomain_localization S hS
    letI : IsDedekindDomain (Localization S) := isDedekindDomain_localization S hS
    letI : Module.IsTorsionFree A (Localization S) := isTorsionFree_localization S hS
    Function.Surjective (ClassGroup.extendedHom A (Localization S)) := by
  haveI : IsDomain (Localization S) := isDomain_localization S hS
  haveI : IsDedekindDomain (Localization S) := isDedekindDomain_localization S hS
  haveI : Module.IsTorsionFree A (Localization S) := isTorsionFree_localization S hS
  exact classGroup_extendedHom_surjective S hS

/-- **Atiyah–Macdonald (1969), Chapter IX, Exercise 1**, in full.

Let `A` be a Dedekind domain and `S` a multiplicatively closed subset of `A` with `0 ∉ S`. Then
`S⁻¹A` is a Dedekind domain, it is a field exactly when it is the field of fractions of `A` (and if
it is not a field it has a nonzero prime ideal, i.e. dimension one); and extension of ideals induces
a surjective homomorphism `ClassGroup A →* ClassGroup S⁻¹A` of ideal class groups (stated here with
the book's hypothesis `S ≠ A - {0}`). -/
theorem solution (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
    (hSne : S ≠ nonZeroDivisors A) :
    letI : IsDomain (Localization S) := isDomain_localization S hS
    letI : IsDedekindDomain (Localization S) := isDedekindDomain_localization S hS
    letI : Module.IsTorsionFree A (Localization S) := isTorsionFree_localization S hS
    IsDedekindDomain (Localization S) ∧
      (IsField (Localization S) ↔ IsFractionRing A (Localization S)) ∧
      Function.Surjective (ClassGroup.extendedHom A (Localization S)) := by
  haveI : IsDomain (Localization S) := isDomain_localization S hS
  haveI : IsDedekindDomain (Localization S) := isDedekindDomain_localization S hS
  haveI : Module.IsTorsionFree A (Localization S) := isTorsionFree_localization S hS
  exact ⟨isDedekindDomain_localization S hS, isField_iff_isFractionRing S hS,
    classGroup_extension_surjective S hS hSne⟩

/-! ### Sanity checks: concrete instances

The hypotheses are satisfiable: `ℤ` is a Dedekind domain and the powers of `2` form a submonoid of
its nonzero divisors. Moreover for `A = ℚ[X]` the trivial submonoid `⊥ = {1}` satisfies
`⊥ ≠ A - {0}` (as `X` is a nonzero divisor but not `1`), so the full exercise, including its
hypothesis `S ≠ A - {0}`, is non-vacuous. -/

/-- A concrete instance of the first assertion: localizing `ℤ` at the powers of `2`. -/
example : IsDedekindDomain (Localization (Submonoid.powers (2 : ℤ))) :=
  isDedekindDomain_localization _
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (by norm_num)))

/-- The hypothesis `S ≠ A - {0}` of the exercise is satisfiable: for `A = ℚ[X]` and `S = {1}`,
`X` is a nonzero divisor but not `1`. -/
example : (⊥ : Submonoid (Polynomial ℚ)) ≠ nonZeroDivisors (Polynomial ℚ) := by
  intro h
  have hX : Polynomial.X ∈ (⊥ : Submonoid (Polynomial ℚ)) := by
    rw [h]
    exact mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero
  have hX1 : (Polynomial.X : Polynomial ℚ) = 1 := by simpa using hX
  have hval := congrArg (Polynomial.eval (0 : ℚ)) hX1
  simp at hval

end AtiyahMcdonald69.Ex_9_1
