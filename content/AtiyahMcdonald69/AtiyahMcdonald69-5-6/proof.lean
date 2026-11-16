/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 5.6

**Statement (book, p. 67).** *Let $B_1,\dots,B_n$ be integral $A$-algebras. Show that
$\prod_{i=1}^{n} B_i$ is an integral $A$-algebra.*

In Atiyah–Macdonald an element of an $A$-algebra $B$ is *integral over* $A$ when it is a
root of a monic polynomial with coefficients in $A$ (§5, p. 60), and $B$ is an *integral
$A$-algebra* when every element of $B$ is integral over $A$.  This is exactly Mathlib's
`IsIntegral A x` / `Algebra.IsIntegral A B`.  The product $\prod_i B_i$ is the type
`∀ i, B i` of dependent functions, with the componentwise ring structure and the
componentwise $A$-algebra structure (`Pi.algebra`).

## Contents

* `aeval_prod_eq_zero`, `monic_prod` — the monic polynomial exhibited by the standard
  proof: if `p i` (monic) kills the `i`-th component of `x`, then `∏ i, p i` is monic and
  kills `x`.
* `isIntegral_pi_iff`, `algebra_isIntegral_pi_iff` — the componentwise criterion: an
  element of a finite product is integral over `A` iff every component is, so the product
  is an integral `A`-algebra iff every factor is.
* `algebra_isIntegral_pi`, `solution` — Exercise 5.6 itself.
* `not_isIntegral_nat_pi`, `not_algebra_isIntegral_nat_pi` — an explicit counterexample
  showing that the finiteness of the family is essential: an infinite product of copies of
  the integral $\mathbb{Z}$-algebra $\mathbb{Z}$ need not be integral over $\mathbb{Z}$.
-/
import Mathlib

open Polynomial

namespace AtiyahMcdonald69.Ex_5_6

/-! ## The monic polynomial of the standard proof -/

section KeyLemma

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Fintype ι]
variable {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

/-- If `p i` kills the `i`-th component of `x`, then `∏ i, p i` kills `x`; combined with
`monic_prod` this is the monic polynomial exhibited by the standard solution of
Exercise 5.6.

The evaluation of a polynomial at a point of a product algebra is computed componentwise,
so the `i`-th component of `(∏ j, p j)(x)` is `∏ j, p j (x i)`, which vanishes because of
the factor `p i (x i)`.  Note that the product of the polynomials is indexed by the *finite*
type `ι`; this is where finiteness enters (compare the counterexample at the end of the
file). -/
theorem aeval_prod_eq_zero (x : ∀ i, B i) (p : ι → A[X])
    (hx : ∀ i, Polynomial.aeval (x i) (p i) = 0) :
    Polynomial.aeval x (∏ i, p i) = 0 := by
  rw [Polynomial.aeval_pi_apply]
  funext i
  rw [map_prod (g := (Polynomial.aeval (x i) : A[X] →ₐ[A] B i)) p Finset.univ]
  simpa using Finset.prod_eq_zero (Finset.mem_univ i) (hx i)

/-- `∏ i, p i` is monic when each `p i` is. -/
theorem monic_prod (p : ι → A[X]) (hp : ∀ i, (p i).Monic) : (∏ i, p i).Monic :=
  monic_prod_of_monic Finset.univ p fun i _ => hp i

/-- An element of a finite product of `A`-algebras is integral over `A` if and only if all
of its components are.  (The right-to-left implication is the content of the standard
proof of Exercise 5.6; the left-to-right one uses the projection `A`-algebra maps.) -/
theorem isIntegral_pi_iff {x : ∀ i, B i} :
    IsIntegral A x ↔ ∀ i, IsIntegral A (x i) := by
  constructor
  · intro h i
    simpa using h.map (Pi.evalAlgHom A B i)
  · intro h
    choose p hp hpx using h
    exact ⟨∏ i, p i, monic_prod p hp, aeval_prod_eq_zero x p hpx⟩

/-- **Exercise 5.6**, in the general form for a finite index type: a finite product of
integral `A`-algebras is an integral `A`-algebra. -/
theorem algebra_isIntegral_pi (h : ∀ i, Algebra.IsIntegral A (B i)) :
    Algebra.IsIntegral A (∀ i, B i) :=
  Algebra.IsIntegral.mk fun x => isIntegral_pi_iff.mpr fun i => (h i).isIntegral (x i)

/-- Conversely, a finite product can only be an integral `A`-algebra if every factor is:
integrality passes to the quotient algebras `B i` of `∏ i, B i`.  So for a finite family,
`∏ i, B i` is an integral `A`-algebra exactly when each `B i` is. -/
theorem algebra_isIntegral_pi_iff :
    Algebra.IsIntegral A (∀ i, B i) ↔ ∀ i, Algebra.IsIntegral A (B i) := by
  refine ⟨fun h i => Algebra.IsIntegral.mk fun x => ?_, algebra_isIntegral_pi⟩
  classical
  have hx : IsIntegral A (Pi.single i x : ∀ i, B i) := (h.isIntegral _)
  simpa using hx.map (Pi.evalAlgHom A B i)

end KeyLemma

/-! ## Exercise 5.6 with the book's indexing `B₁, …, Bₙ` -/

section Book

/-- **Atiyah–Macdonald, Exercise 5.6.**  Let `B₁, …, Bₙ` be integral `A`-algebras.  Then
the product `∏ i, Bᵢ` is an integral `A`-algebra.

(The book states the result for `n ≥ 1`; the empty product, i.e. the zero ring, is also
integral over `A`, so no positivity hypothesis is needed.) -/
theorem solution (A : Type*) [CommRing A] (n : ℕ) (B : Fin n → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (hB : ∀ i, Algebra.IsIntegral A (B i)) :
    Algebra.IsIntegral A (∀ i, B i) :=
  algebra_isIntegral_pi hB

end Book

/-! ## Non-vacuity: a concrete instance of the statement -/

example : Algebra.IsIntegral ℤ (Fin 2 → ℤ) :=
  solution ℤ 2 (fun _ => ℤ) fun _ => Algebra.IsIntegral.mk fun x => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℤ) (x := x)

/-! ## The finiteness hypothesis is essential

The standard proof multiplies the monic annihilating polynomials of the finitely many
coordinates, and it is not an artefact of the proof: over an infinite index set the
statement is false.  Take `A = B n = ℤ` and the element `x n = n` of the product
`∏_{n ∈ ℕ} ℤ`.  If a monic `p ∈ ℤ[X]` killed `x`, then every natural number would be a
root of `p`, so `p` would have infinitely many roots, forcing `p = 0`, contradicting
monicity. -/

section InfiniteCounterexample

/-- The element `(0, 1, 2, …)` of `∏_{n ∈ ℕ} ℤ` is not integral over `ℤ`. -/
theorem not_isIntegral_nat_pi : ¬ IsIntegral ℤ (fun n : ℕ => (n : ℤ)) := by
  rintro ⟨p, hp, hpx⟩
  have hpx' : Polynomial.aeval (x := fun n : ℕ => (n : ℤ)) p = 0 := hpx
  have hroot : Set.range (fun n : ℕ => (n : ℤ)) ⊆ {x : ℤ | p.IsRoot x} := by
    rintro _ ⟨n, rfl⟩
    have h := congrFun hpx' n
    rw [Polynomial.aeval_pi_apply] at h
    simpa [Polynomial.IsRoot] using h
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p
      (Set.Infinite.mono hroot
        (Set.infinite_range_of_injective (f := fun n : ℕ => (n : ℤ))
          fun _ _ h => Nat.cast_injective h))
  exact hp.ne_zero hpzero

/-- Consequently, the infinite product of integral `ℤ`-algebras `∏_{n ∈ ℕ} ℤ` is *not* an
integral `ℤ`-algebra: the finiteness hypothesis in Exercise 5.6 cannot be dropped. -/
theorem not_algebra_isIntegral_nat_pi : ¬ Algebra.IsIntegral ℤ (ℕ → ℤ) :=
  fun h => not_isIntegral_nat_pi (h.isIntegral (fun n : ℕ => (n : ℤ)))

end InfiniteCounterexample

end AtiyahMcdonald69.Ex_5_6

#print axioms AtiyahMcdonald69.Ex_5_6.aeval_prod_eq_zero
#print axioms AtiyahMcdonald69.Ex_5_6.isIntegral_pi_iff
#print axioms AtiyahMcdonald69.Ex_5_6.algebra_isIntegral_pi
#print axioms AtiyahMcdonald69.Ex_5_6.algebra_isIntegral_pi_iff
#print axioms AtiyahMcdonald69.Ex_5_6.solution
#print axioms AtiyahMcdonald69.Ex_5_6.not_isIntegral_nat_pi
#print axioms AtiyahMcdonald69.Ex_5_6.not_algebra_isIntegral_nat_pi
