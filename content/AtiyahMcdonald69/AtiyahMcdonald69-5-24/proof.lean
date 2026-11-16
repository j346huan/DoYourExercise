/-
Atiyah--Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 5, Exercise 24.

Statement (as printed in the source, verbatim):

  "24. Let `A` be a Jacobson ring (Exercise 23) and `B` an `A`-algebra. Show that if `B` is
   either (i) integral over `A` or (ii) finitely generated as an `A`-algebra, then `B` is
   Jacobson. [Use Exercise 22 for (ii).] In particular, every finitely generated ring, and
   every finitely generated algebra over a field, is a Jacobson ring."

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-24

Audit of the natural proof / formalization notes.
* Exercise 23 defines a Jacobson ring by "every prime ideal is an intersection of maximal
  ideals".  Mathlib's `IsJacobsonRing` class is the (equivalent) radical-ideal formulation;
  the equivalence is proved below as `isJacobsonRing_iff_prime_eq_sInf_maximal`, so the
  statement formalized here is the source's statement and not a weakening of it.
* (i): the natural proof combines Exercise 5.5 (`J(B) ∩ A = 0` for integral `B`) with a
  minimal-degree monic equation.  Mathlib proves the same proposition by a different route
  (`exists_ideal_over_maximal_of_isIntegral`); the exercise asks for the proposition, so this
  is used where it covers the intended theorem.
* (ii): the natural proof invokes Exercise 22 (the Jacobson radical descends along a finitely
  generated extension of domains).  Mathlib's route goes through the Nullstellensatz
  (`isJacobsonRing_of_finiteType`).
* The two "In particular" claims do *not* follow from (i) and (ii) alone: they need the base
  rings (a field, and `ℤ`) to be Jacobson themselves, and Mathlib has no such instance for
  `ℤ`.  `ℤ`'s Jacobson property is therefore proved from scratch here
  (`jacobson_bot_int`, `isJacobsonRing_int`), following the natural proof's argument: every
  nonzero prime of `ℤ` is maximal, and no nonzero integer lies in the intersection of all
  maximal ideals (for `x ≠ 0` pick a prime `p > |x|`; then `x ∉ (p)`).
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Int

namespace AtiyahMcdonald69.Ex_5_24

open Ideal

/-! ## The definition of a Jacobson ring (Exercise 23) -/

/-- Atiyah--Macdonald's definition (Exercise 23): every prime ideal is the intersection of the
maximal ideals containing it.  This is the form in which Exercise 24 states its conclusions. -/
theorem isJacobsonRing_iff_prime_eq_sInf_maximal {A : Type*} [CommRing A] :
    IsJacobsonRing A ↔
      ∀ P : Ideal A, P.IsPrime → P = sInf {m : Ideal A | P ≤ m ∧ m.IsMaximal} := by
  rw [isJacobsonRing_iff_prime_eq]
  refine forall_congr' fun P => imp_congr_right fun _ => ?_
  rw [Ideal.jacobson]
  exact ⟨Eq.symm, Eq.symm⟩

/-- Atiyah--Macdonald Exercise 23, condition (ii): in a Jacobson ring every ideal has the same
nilradical and Jacobson radical (equivalently: in every homomorphic image the nilradical and the
Jacobson radical agree). -/
theorem radical_eq_jacobson {A : Type*} [CommRing A] [IsJacobsonRing A] (I : Ideal A) :
    I.radical = I.jacobson :=
  Ideal.radical_eq_jacobson I

/-- Exercise 23, condition (ii), as a characterization: a ring is Jacobson exactly when, in every
homomorphic image, the nilradical and the Jacobson radical coincide. -/
theorem isJacobsonRing_iff_radical_eq_jacobson {A : Type*} [CommRing A] :
    IsJacobsonRing A ↔ ∀ I : Ideal A, I.radical = I.jacobson := by
  refine ⟨fun _ I => Ideal.radical_eq_jacobson I, fun h => isJacobsonRing_iff.mpr ?_⟩
  intro I hI
  rw [← h I]
  exact hI.radical

/-! ## Exercise 24, part (i): integral algebras -/

/-- **Exercise 5.24 (i).**  If `A` is a Jacobson ring and `B` is an `A`-algebra which is integral
over `A`, then `B` is a Jacobson ring. -/
theorem isJacobsonRing_of_integral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsJacobsonRing A] [Algebra.IsIntegral A B] : IsJacobsonRing B :=
  _root_.isJacobsonRing_of_isIntegral (R := A) (S := B)

/-- Exercise 5.24 (i) with the structure map given as an arbitrary ring homomorphism:
if `f : A →+* B` is integral and `A` is Jacobson, then `B` is Jacobson. -/
theorem isJacobsonRing_of_ringHom_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IsIntegral) [IsJacobsonRing A] : IsJacobsonRing B :=
  _root_.isJacobsonRing_of_isIntegral' f hf

/-- Exercise 5.24 (i) in the source's own terms: every prime ideal of `B` is the intersection of
the maximal ideals containing it. -/
theorem prime_eq_sInf_maximal_of_integral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsJacobsonRing A] [Algebra.IsIntegral A B] {q : Ideal B} (hq : q.IsPrime) :
    q = sInf {m : Ideal B | q ≤ m ∧ m.IsMaximal} :=
  isJacobsonRing_iff_prime_eq_sInf_maximal.1 (isJacobsonRing_of_integral (A := A)) q hq

/-! ## Exercise 24, part (ii): finitely generated algebras -/

/-- **Exercise 5.24 (ii).**  If `A` is a Jacobson ring and `B` is a finitely generated
`A`-algebra, then `B` is a Jacobson ring. -/
theorem isJacobsonRing_of_fg {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B :=
  _root_.isJacobsonRing_of_finiteType (A := A) (B := B)

/-- Exercise 5.24 (ii) with the structure map given as an arbitrary ring homomorphism:
if `f : A →+* B` is of finite type and `A` is Jacobson, then `B` is Jacobson. -/
theorem isJacobsonRing_of_ringHom_finiteType {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FiniteType) [IsJacobsonRing A] : IsJacobsonRing B :=
  _root_.RingHom.FiniteType.isJacobsonRing (f := f) hf

/-- Exercise 5.24 (ii) in the source's own terms: every prime ideal of `B` is the intersection
of the maximal ideals containing it. -/
theorem prime_eq_sInf_maximal_of_fg {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsJacobsonRing A] [Algebra.FiniteType A B] {q : Ideal B} (hq : q.IsPrime) :
    q = sInf {m : Ideal B | q ≤ m ∧ m.IsMaximal} :=
  isJacobsonRing_iff_prime_eq_sInf_maximal.1 (isJacobsonRing_of_fg (A := A)) q hq

/-! ## The base rings: `ℤ` and fields are Jacobson -/

/-- The Jacobson radical of `ℤ` is trivial: a nonzero integer `x` never lies in all maximal
ideals, since for a prime `p > x.natAbs` the maximal ideal `(p)` misses `x`. -/
theorem jacobson_bot_int : (⊥ : Ideal ℤ).jacobson = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
  have : Fact (Nat.Prime p) := ⟨hpprime⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hxmem : x ∈ Ideal.span {(p : ℤ)} := mem_sInf.mp hx ⟨bot_le, hmax⟩
  rw [Ideal.mem_span_singleton] at hxmem
  have hdvd : p ∣ x.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hxmem
    rwa [Int.natAbs_natCast] at h
  have hpos : 0 < x.natAbs := Int.natAbs_pos.mpr hx0
  have hle : p ≤ x.natAbs := Nat.le_of_dvd hpos hdvd
  omega

/-- The same statement in the literal form used by the natural proof: the intersection of all
maximal ideals of `ℤ` is `(0)`. -/
theorem ring_jacobson_int : Ring.jacobson ℤ = ⊥ := by
  rw [← Ideal.jacobson_bot]
  exact jacobson_bot_int

/-- Every nonzero prime ideal of `ℤ` is maximal. -/
theorem isMaximal_of_isPrime_ne_bot_int {P : Ideal ℤ} (hP : P.IsPrime) (hbot : P ≠ ⊥) :
    P.IsMaximal :=
  Ideal.IsPrime.isMaximal hP hbot

/-- **`ℤ` is a Jacobson ring.**  For a prime `P` of `ℤ`: if `P = ⊥` this is
`jacobson_bot_int`, and otherwise `P` is maximal, so it equals its own Jacobson radical. -/
theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    simpa using jacobson_bot_int
  · have : P.IsMaximal := isMaximal_of_isPrime_ne_bot_int hP hbot
    exact jacobson_eq_self_of_isMaximal

/-- A field is a Jacobson ring: its only prime ideal is `⊥`, which is maximal. -/
theorem isJacobsonRing_field (K : Type*) [Field K] : IsJacobsonRing K := inferInstance

/-! ## The two "in particular" corollaries -/

/-- **Every finitely generated ring is Jacobson**: a ring which is finitely generated as a
`ℤ`-algebra is a Jacobson ring. -/
theorem isJacobsonRing_of_finiteType_int (B : Type*) [CommRing B] [Algebra.FiniteType ℤ B] :
    IsJacobsonRing B := by
  have : IsJacobsonRing ℤ := isJacobsonRing_int
  exact _root_.isJacobsonRing_of_finiteType (A := ℤ) (B := B)

/-- **Every finitely generated algebra over a field is Jacobson.** -/
theorem isJacobsonRing_of_finiteType_field (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] : IsJacobsonRing B := by
  have : IsJacobsonRing k := isJacobsonRing_field k
  exact _root_.isJacobsonRing_of_finiteType (A := k) (B := B)

/-- Concretely: `ℤ[X₁,…,Xₙ]` is a Jacobson ring. -/
theorem isJacobsonRing_mvPolynomial_int (n : ℕ) :
    IsJacobsonRing (MvPolynomial (Fin n) ℤ) := by
  have : IsJacobsonRing ℤ := isJacobsonRing_int
  infer_instance

/-- Concretely: `k[X₁,…,Xₙ]` for a field `k` is a Jacobson ring. -/
theorem isJacobsonRing_mvPolynomial_field (k : Type*) [Field k] (n : ℕ) :
    IsJacobsonRing (MvPolynomial (Fin n) k) :=
  isJacobsonRing_of_finiteType_field k (MvPolynomial (Fin n) k)

/-- Concretely: a ring which is a quotient of a polynomial ring in finitely many variables over
`ℤ` is Jacobson. -/
theorem isJacobsonRing_of_surjective_mvPolynomial_int (B : Type*) [CommRing B] (n : ℕ)
    (f : MvPolynomial (Fin n) ℤ →+* B) (hf : Function.Surjective f) : IsJacobsonRing B := by
  have : IsJacobsonRing ℤ := isJacobsonRing_int
  have : IsJacobsonRing (MvPolynomial (Fin n) ℤ) := inferInstance
  exact _root_.isJacobsonRing_of_surjective ⟨f, hf⟩

/-- Concretely: a ring which is a quotient of a polynomial ring in finitely many variables over
a field is Jacobson. -/
theorem isJacobsonRing_of_surjective_mvPolynomial_field (k B : Type*) [Field k] [CommRing B]
    (n : ℕ) (f : MvPolynomial (Fin n) k →+* B) (hf : Function.Surjective f) :
    IsJacobsonRing B := by
  have : IsJacobsonRing k := isJacobsonRing_field k
  have : IsJacobsonRing (MvPolynomial (Fin n) k) := inferInstance
  exact _root_.isJacobsonRing_of_surjective ⟨f, hf⟩

end AtiyahMcdonald69.Ex_5_24

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_iff_prime_eq_sInf_maximal
#print axioms AtiyahMcdonald69.Ex_5_24.radical_eq_jacobson
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_integral
#print axioms AtiyahMcdonald69.Ex_5_24.prime_eq_sInf_maximal_of_integral
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_fg
#print axioms AtiyahMcdonald69.Ex_5_24.prime_eq_sInf_maximal_of_fg
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_iff_radical_eq_jacobson
#print axioms AtiyahMcdonald69.Ex_5_24.jacobson_bot_int
#print axioms AtiyahMcdonald69.Ex_5_24.ring_jacobson_int
#print axioms AtiyahMcdonald69.Ex_5_24.isMaximal_of_isPrime_ne_bot_int
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_int
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_field
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_finiteType_int
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_finiteType_field
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_surjective_mvPolynomial_int
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_surjective_mvPolynomial_field
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_ringHom_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_of_ringHom_finiteType
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_mvPolynomial_int
#print axioms AtiyahMcdonald69.Ex_5_24.isJacobsonRing_mvPolynomial_field
