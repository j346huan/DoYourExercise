import Mathlib

set_option linter.style.haveILetI false

/-!
# Atiyah–Macdonald, Chapter 5, Exercise 25

Source: M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*,
Addison-Wesley, 1969, Chapter 5, Exercise 25 (p. 71).

Statement (verbatim): "Let `A` be a ring. Show that the following are equivalent:
  i) `A` is a Jacobson ring;
  ii) Every finitely generated `A`-algebra `B` which is a field is finite over `A`."

Disambiguation: this is *Chapter 5*, Exercise 25 (p. 71, in the exercise list following
Corollary 5.24).  The differently numbered Chapter 3, Exercise 25 (tensor products of
spectra, `h*(T) = f*(Y) ∩ g*(Z)`) is a different problem and is not what is formalised
here.

Here "Jacobson ring" is the notion introduced in Chapter 5, Exercise 23: a ring in which
every prime ideal is an intersection of maximal ideals (equivalently: in every quotient
ring the nilradical equals the Jacobson radical).  Mathlib's `IsJacobsonRing` is the same
notion, and `isJacobsonRing_iff_sInf_maximal` records the "intersection of maximal
ideals" characterisation; `isJacobsonRing_iff_isJacobsonRingAM` below bridges the two
spellings.

"Finite over `A`" means finitely generated as an `A`-module (`Module.Finite A B`).

Route for `ii) => i)`.  This is an audited simplification of the natural proof from
<https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-25>; the natural
proof routes through Exercises 5.21 and 5.23, which is unnecessary.  Given a prime ideal
`P` and `x` not in `P`, put `y = x mod P` in the domain `A ⧸ P` and let `S = (A ⧸ P)_y`,
a finitely generated `A`-algebra.  If `m` is a maximal ideal of `S`, then `k = S ⧸ m` is a
field that is a finitely generated `A`-algebra, hence finite over `A` by ii), hence
integral over `A`.  The contraction of the maximal ideal `⊥` of `k` is therefore a maximal
ideal `M` of `A` (contractions of maximal ideals under integral extensions are maximal);
it contains `P` (as `P` is the kernel of `A → A ⧸ P`) and does not contain `x` (as the
image of `x` in `k` is a unit).  Thus for every prime `P`, `P.jacobson = P`, i.e. `A` is
Jacobson.

Route for `i) => ii)`.  This is Zariski's lemma in the relative form ("Noether
normalization + integrality", Atiyah-Macdonald 5.21/5.24); it is Mathlib's
`finite_of_finite_type_of_isJacobsonRing`.

Note on universes: `i) => ii)` is proved in `cond_of_isJacobsonRing` for `A`-algebras in
an arbitrary universe, but `ii) => i)` uses algebras constructed from `A` (quotients and
localisations of `A`), hence living in the same universe as `A`.  This is the standard
universe convention and is mathematically immaterial.

Audit of the natural proof (the `proof.tex` behind the URL above).  Its argument for
`i) => ii)` (pass to the image of `A` in `B`, so that `A` is a domain with zero Jacobson
radical; use Exercise 5.21 to find `s ≠ 0`; pick a maximal ideal `m` avoiding `s`; extend
`A → A/m` to `B → closure`; injectivity forces `m = 0`, so `A` is a field and `B` is
algebraic, hence finite, over it) is correct, and we do not need any extra hypotheses.
Its argument for `ii) => i)` (for a non-maximal prime `p`, localise `A/p` at `0 ≠ f`; the
result is not a field by 5.7, so it has a nonzero prime avoiding `f`; then invoke 5.23
(iii) and the (hard) implication (iii) => (i) of that exercise) is also correct, but it
unnecessarily depends on Exercise 5.23.  Our Lean proof replaces the last step by a direct
argument: a maximal ideal of `(A/p)_f` together with the finiteness hypothesis produces at
once a maximal ideal of `A` above `p` and avoiding `x`, via the going-up property for
integral extensions.  No statement is weakened; the zero ring is covered (the hypothesis
and the conclusion are both vacuous/true there).
-/

namespace AtiyahMcdonald69.Ex_5_25

open Ideal

universe u v

/-- Condition ii) of Atiyah-Macdonald, Chapter 5, Exercise 25, for `A`-algebras that live in
the same universe as `A`: every finitely generated `A`-algebra `B` that is a field is
finite (= finitely generated) as an `A`-module. -/
def Cond (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [Field B] [Algebra A B] [Algebra.FiniteType A B], Module.Finite A B

/-- Condition i) of Atiyah-Macdonald, Chapter 5, Exercise 23: every prime ideal of `A` is an
intersection of maximal ideals (the notion of a Jacobson ring referred to in Exercise 5.25). -/
def IsJacobsonRingAM (A : Type u) [CommRing A] : Prop :=
  ∀ P : Ideal A, P.IsPrime → ∃ M : Set (Ideal A), (∀ J ∈ M, J.IsMaximal) ∧ P = sInf M

/-- Mathlib's `IsJacobsonRing` agrees with the "every prime ideal is an intersection of
maximal ideals" formulation of Atiyah-Macdonald, Chapter 5, Exercise 23 (i). -/
theorem isJacobsonRing_iff_isJacobsonRingAM {A : Type u} [CommRing A] :
    IsJacobsonRing A ↔ IsJacobsonRingAM A := by
  constructor
  · intro h P hP
    obtain ⟨M, hM, hMeq⟩ := isJacobsonRing_iff_sInf_maximal.mp h hP
    let M' : Set (Ideal A) := {J | J ∈ M ∧ J.IsMaximal}
    have hM'max : ∀ J ∈ M', J.IsMaximal := fun J hJ => hJ.2
    refine ⟨M', hM'max, ?_⟩
    rw [hMeq]
    have h1 : sInf M ≤ sInf M' := by
      refine le_sInf fun J hJ => ?_
      exact sInf_le hJ.1
    have h2 : sInf M' ≤ sInf M := by
      refine le_sInf fun J hJ => ?_
      rcases hM J hJ with hJmax | hJtop
      · exact sInf_le (show J ∈ M' from ⟨hJ, hJmax⟩)
      · rw [hJtop]
        exact le_top
    exact le_antisymm h1 h2
  · intro h
    rw [isJacobsonRing_iff_sInf_maximal]
    intro I hI
    obtain ⟨M, hM, hMeq⟩ := h I hI
    exact ⟨M, fun J hJ => Or.inl (hM J hJ), hMeq⟩

/-- Key step of `ii) => i)`: if every finitely generated `A`-algebra that is a field is finite
over `A`, then for every prime ideal `P` and every `x` not in `P` there is a maximal ideal
`M` with `P ≤ M` and `x ∉ M` (so that `P` is the intersection of the maximal ideals above
it). -/
theorem exists_maximal_ge_not_mem {A : Type u} [CommRing A] (hcond : Cond A) {P : Ideal A}
    (hP : P.IsPrime) {x : A} (hx : x ∉ P) :
    ∃ M : Ideal A, P ≤ M ∧ M.IsMaximal ∧ x ∉ M := by
  classical
  haveI hPprime : P.IsPrime := hP
  set y : A ⧸ P := Ideal.Quotient.mk P x with hy
  have hy0 : y ≠ 0 := by
    rw [hy, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  haveI hyDom : IsDomain (Localization.Away y) := Localization.Away.isDomain hy0
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Localization.Away y)
  letI hmMax : m.IsMaximal := hm
  letI : Field (Localization.Away y ⧸ m) := Ideal.Quotient.field m
  haveI hfin : Module.Finite A (Localization.Away y ⧸ m) := hcond _
  haveI hint : Algebra.IsIntegral A (Localization.Away y ⧸ m) := inferInstance
  haveI hbot : (⊥ : Ideal (Localization.Away y ⧸ m)).IsMaximal :=
    Ring.isField_iff_maximal_bot.mp (Field.toIsField _)
  refine ⟨(⊥ : Ideal (Localization.Away y ⧸ m)).comap (algebraMap A _), ?_, ?_, ?_⟩
  · -- `P` is contained in the contraction, because `P` is the kernel of `A → A ⧸ P`
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot]
    have h1 : algebraMap A (Localization.Away y) a
        = algebraMap (A ⧸ P) (Localization.Away y) (Ideal.Quotient.mk P a) := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ P)]
      rfl
    rw [IsScalarTower.algebraMap_apply A (Localization.Away y), h1,
      show Ideal.Quotient.mk P a = 0 from by
        rw [Ideal.Quotient.eq_zero_iff_mem]; exact ha]
    simp
  · -- the contraction of the maximal ideal `⊥` of the field `k` is maximal, as `k` is
    -- integral over `A`
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ⊥
  · -- `x` is not in the contraction, as its image is a unit
    intro hxM
    rw [Ideal.mem_comap, Ideal.mem_bot] at hxM
    have h1 : algebraMap A (Localization.Away y) x
        = algebraMap (A ⧸ P) (Localization.Away y) y := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ P)]
      rfl
    rw [IsScalarTower.algebraMap_apply A (Localization.Away y), h1] at hxM
    exact IsUnit.ne_zero
      ((IsLocalization.map_units (Localization.Away y) ⟨y, Submonoid.mem_powers y⟩).map
        (algebraMap (Localization.Away y) (Localization.Away y ⧸ m))) hxM

/-- Condition i) implies condition ii), for `A`-algebras in an arbitrary universe
(relative Zariski lemma, Atiyah-Macdonald Corollary 5.24 in the form of Exercise 5.21). -/
theorem cond_of_isJacobsonRing {A : Type u} [CommRing A] (hA : IsJacobsonRing A)
    (B : Type v) [Field B] [Algebra A B] [Algebra.FiniteType A B] :
    Module.Finite A B :=
  finite_of_finite_type_of_isJacobsonRing A B

/-- Condition ii) implies condition i): if every finitely generated `A`-algebra that is a
field is finite over `A`, then `A` is a Jacobson ring. -/
theorem isJacobsonRing_of_cond {A : Type u} [CommRing A] (hcond : Cond A) :
    IsJacobsonRing A := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ le_jacobson
  intro x hx
  by_contra hxP
  obtain ⟨M, hPM, hMmax, hxM⟩ := exists_maximal_ge_not_mem hcond hP hxP
  exact hxM ((Ideal.mem_sInf.mp hx) ⟨hPM, hMmax⟩)

/-- Atiyah-Macdonald, Chapter 5, Exercise 25: `A` is a Jacobson ring if and only if every
finitely generated `A`-algebra that is a field is finite over `A`. -/
theorem isJacobsonRing_iff_cond {A : Type u} [CommRing A] :
    IsJacobsonRing A ↔ Cond A :=
  ⟨cond_of_isJacobsonRing, isJacobsonRing_of_cond⟩

/-- Atiyah-Macdonald, Chapter 5, Exercise 25, final form. -/
theorem solution (A : Type u) [CommRing A] :
    IsJacobsonRing A ↔
      ∀ (B : Type u) [Field B] [Algebra A B] [Algebra.FiniteType A B], Module.Finite A B :=
  isJacobsonRing_iff_cond

/-- Non-vacuity check: over a field `K`, condition ii) holds (this is Zariski's lemma: a
finitely generated `K`-algebra that is a field is a finite field extension of `K`), so the
equivalence of Exercise 5.25 is not a vacuous reformulation. -/
theorem cond_of_field (K : Type u) [Field K] : Cond K :=
  isJacobsonRing_iff_cond.mp inferInstance

end AtiyahMcdonald69.Ex_5_25

#print axioms AtiyahMcdonald69.Ex_5_25.isJacobsonRing_iff_isJacobsonRingAM
#print axioms AtiyahMcdonald69.Ex_5_25.exists_maximal_ge_not_mem
#print axioms AtiyahMcdonald69.Ex_5_25.cond_of_isJacobsonRing
#print axioms AtiyahMcdonald69.Ex_5_25.isJacobsonRing_of_cond
#print axioms AtiyahMcdonald69.Ex_5_25.isJacobsonRing_iff_cond
#print axioms AtiyahMcdonald69.Ex_5_25.solution
#print axioms AtiyahMcdonald69.Ex_5_25.cond_of_field
