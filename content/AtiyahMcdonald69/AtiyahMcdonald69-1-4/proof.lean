import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Polynomial
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 4

The exercise reads: *in the ring `A[x]`, the Jacobson radical is equal to the nilradical.*

The natural-language proof has two steps.

* The nilradical is contained in every maximal ideal: every maximal ideal is prime, and a
  nilpotent element lies in every prime ideal.
* Conversely, if `f` belongs to the Jacobson radical then `1 + x * f` is a unit; a polynomial is
  a unit exactly when its constant coefficient is a unit and all its other coefficients are
  nilpotent, so all coefficients of `f` are nilpotent, and a polynomial is nilpotent exactly
  when all its coefficients are nilpotent.

Both steps are formalised below, with no hypothesis on the coefficient ring `A` beyond
commutativity (in particular the trivial ring, and zero polynomials, are allowed).

The first inclusion is `nilradical_le_jacobson_bot`. The second is
`jacobson_bot_le_nilradical`, which follows the book's route using the unit criterion
`Polynomial.isUnit_C_add_X_mul_iff` (the case of Exercise 1.2 (i) that is needed here).
A second, longer proof of the same inclusion, `jacobson_bot_le_nilradical_of_coeff`, reduces
modulo the prime ideals of `A` and does not use the unit criterion at all.

## Main results

* `AtiyahMcdonald69.Ex_1_4.jacobson_bot_eq_nilradical` :
  `Ideal.jacobson (⊥ : Ideal A[X]) = nilradical A[X]`.
* `AtiyahMcdonald69.Ex_1_4.ring_jacobson_eq_nilradical` :
  `Ring.jacobson A[X] = nilradical A[X]`.
* `AtiyahMcdonald69.Ex_1_4.nilradical_le_jacobson_bot` and
  `AtiyahMcdonald69.Ex_1_4.jacobson_bot_le_nilradical` : the two inclusions.
* `AtiyahMcdonald69.Ex_1_4.mem_jacobson_bot_iff_isNilpotent` : elementwise form.
* `AtiyahMcdonald69.Ex_1_4.mem_jacobson_bot_iff_coeff_mem_nilradical` : coefficientwise form.

Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-4
-/

namespace AtiyahMcdonald69.Ex_1_4

open Polynomial

universe u

variable (A : Type u) [CommRing A]

/-! ### The first inclusion: the nilradical lies in the Jacobson radical -/

/-- A nilpotent element of a commutative ring lies in every prime ideal, hence in every maximal
ideal: the nilradical is contained in the Jacobson radical. -/
theorem nilradical_le_jacobson_bot : nilradical A ≤ Ideal.jacobson (⊥ : Ideal A) :=
  Ideal.radical_le_jacobson

/-! ### The second inclusion, along the lines of the book -/

/-- If `f` lies in the Jacobson radical of `A[x]` then `1 + x * f` is a unit: this is the
elementwise form of the Jacobson radical of the zero ideal. -/
theorem isUnit_mul_X_add_one_of_mem_jacobson_bot {f : A[X]}
    (hf : f ∈ Ideal.jacobson (⊥ : Ideal A[X])) : IsUnit (f * X + 1) :=
  Ideal.mem_jacobson_bot.mp hf X

/-- **The second inclusion, book route.** If `1 + x * f` is a unit then, by the polynomial unit
criterion, all coefficients of `f` are nilpotent; hence `f` is nilpotent. -/
theorem isNilpotent_of_mem_jacobson_bot {f : A[X]}
    (hf : f ∈ Ideal.jacobson (⊥ : Ideal A[X])) : IsNilpotent f := by
  have hunit : IsUnit (C (1 : A) + X * f) := by
    simpa [C_1, mul_comm X f, add_comm] using isUnit_mul_X_add_one_of_mem_jacobson_bot A hf
  exact (Polynomial.isUnit_C_add_X_mul_iff.mp hunit).2

/-- Every element of the Jacobson radical of `A[x]` is nilpotent. -/
theorem jacobson_bot_le_nilradical :
    Ideal.jacobson (⊥ : Ideal A[X]) ≤ nilradical A[X] := by
  intro f hf
  rw [mem_nilradical]
  exact isNilpotent_of_mem_jacobson_bot A hf

/-! ### The same inclusion by reduction modulo the primes of `A`

This proof uses neither the polynomial unit criterion nor any statement of Exercise 1.2. -/

/-- The image of an element of the Jacobson radical under a surjective ring homomorphism again
lies in the Jacobson radical of the target. -/
theorem map_mem_jacobson_bot {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {x : R} (hx : x ∈ Ideal.jacobson (⊥ : Ideal R)) :
    φ x ∈ Ideal.jacobson (⊥ : Ideal S) := by
  have h : Ideal.comap φ (Ideal.jacobson (⊥ : Ideal S)) = (Ideal.comap φ ⊥).jacobson :=
    Ideal.comap_jacobson_of_surjective hφ
  have hx' : x ∈ (Ideal.comap φ ⊥).jacobson := Ideal.jacobson_mono bot_le hx
  rw [← h] at hx'
  exact Ideal.mem_comap.mp hx'

/-- An element of the Jacobson radical of a polynomial ring over an integral domain is zero:
`1 + x * g` is a unit, hence a constant, so `x * g` is a constant and `g = 0`. -/
theorem eq_zero_of_mem_jacobson_bot_of_isDomain {D : Type*} [CommRing D] [IsDomain D]
    {g : D[X]} (hg : g ∈ Ideal.jacobson (⊥ : Ideal D[X])) : g = 0 := by
  have hunit : IsUnit (g * X + 1) := Ideal.mem_jacobson_bot.mp hg X
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp hunit
  ext n
  have h : (g * X + 1).coeff (n + 1) = 0 := by
    rw [← hc]
    simp
  rw [coeff_add, coeff_mul_X, coeff_one] at h
  simpa using h

/-- In a polynomial ring over an integral domain the Jacobson radical is trivial. -/
theorem jacobson_bot_eq_bot_of_isDomain (D : Type*) [CommRing D] [IsDomain D] :
    Ideal.jacobson (⊥ : Ideal D[X]) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Submodule.mem_bot]
  exact eq_zero_of_mem_jacobson_bot_of_isDomain hg

/-- Every coefficient of an element of the Jacobson radical of `A[x]` lies in every prime ideal
of `A`: reduce modulo the prime, where the assertion becomes the trivial domain case. -/
theorem coeff_mem_of_isPrime {p : Ideal A} [p.IsPrime] {f : A[X]}
    (hf : f ∈ Ideal.jacobson (⊥ : Ideal A[X])) (i : ℕ) : f.coeff i ∈ p := by
  have hmap : Polynomial.map (Ideal.Quotient.mk p) f ∈
      Ideal.jacobson (⊥ : Ideal (A ⧸ p)[X]) :=
    map_mem_jacobson_bot (Polynomial.mapRingHom (Ideal.Quotient.mk p))
      (Polynomial.map_surjective (Ideal.Quotient.mk p)
        (Ideal.Quotient.mk_surjective (I := p))) hf
  have hzero : Polynomial.map (Ideal.Quotient.mk p) f = 0 :=
    eq_zero_of_mem_jacobson_bot_of_isDomain hmap
  have hcoeff : Ideal.Quotient.mk p (f.coeff i) = 0 := by
    have h1 : (Polynomial.map (Ideal.Quotient.mk p) f).coeff i = 0 := by
      rw [hzero]
      simp
    rwa [Polynomial.coeff_map] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff

/-- **The second inclusion, reduction route.** All coefficients of an element of the Jacobson
radical are nilpotent, hence the element is nilpotent. -/
theorem jacobson_bot_le_nilradical_of_coeff :
    Ideal.jacobson (⊥ : Ideal A[X]) ≤ nilradical A[X] := by
  intro f hf
  rw [mem_nilradical, Polynomial.isNilpotent_iff]
  intro i
  rw [nilpotent_iff_mem_prime]
  intro p hp
  exact @coeff_mem_of_isPrime A _ p hp f hf i

/-! ### The equality, and equivalent forms -/

/-- **Atiyah–Macdonald, Chapter 1, Exercise 4.** In the polynomial ring `A[x]` the Jacobson
radical equals the nilradical. -/
theorem jacobson_bot_eq_nilradical :
    Ideal.jacobson (⊥ : Ideal A[X]) = nilradical A[X] :=
  le_antisymm (jacobson_bot_le_nilradical A) (nilradical_le_jacobson_bot A[X])

/-- Exercise 1.4, stated with `Ring.jacobson`, the intersection of all maximal ideals. -/
theorem ring_jacobson_eq_nilradical : Ring.jacobson A[X] = nilradical A[X] := by
  rw [← Ideal.jacobson_bot, jacobson_bot_eq_nilradical]

/-- Exercise 1.4, elementwise form: the elements of the Jacobson radical of `A[x]` are exactly
the nilpotent elements. -/
theorem mem_jacobson_bot_iff_isNilpotent {f : A[X]} :
    f ∈ Ideal.jacobson (⊥ : Ideal A[X]) ↔ IsNilpotent f := by
  rw [jacobson_bot_eq_nilradical, mem_nilradical]

/-- Exercise 1.4, coefficientwise form: a polynomial lies in the Jacobson radical of `A[x]`
exactly when all of its coefficients are nilpotent. -/
theorem mem_jacobson_bot_iff_coeff_mem_nilradical {f : A[X]} :
    f ∈ Ideal.jacobson (⊥ : Ideal A[X]) ↔ ∀ i, f.coeff i ∈ nilradical A := by
  rw [mem_jacobson_bot_iff_isNilpotent, Polynomial.isNilpotent_iff]
  simp only [mem_nilradical]

end AtiyahMcdonald69.Ex_1_4

#print axioms AtiyahMcdonald69.Ex_1_4.jacobson_bot_eq_nilradical
#print axioms AtiyahMcdonald69.Ex_1_4.ring_jacobson_eq_nilradical
#print axioms AtiyahMcdonald69.Ex_1_4.nilradical_le_jacobson_bot
#print axioms AtiyahMcdonald69.Ex_1_4.jacobson_bot_le_nilradical
#print axioms AtiyahMcdonald69.Ex_1_4.jacobson_bot_le_nilradical_of_coeff
#print axioms AtiyahMcdonald69.Ex_1_4.mem_jacobson_bot_iff_isNilpotent
#print axioms AtiyahMcdonald69.Ex_1_4.mem_jacobson_bot_iff_coeff_mem_nilradical
