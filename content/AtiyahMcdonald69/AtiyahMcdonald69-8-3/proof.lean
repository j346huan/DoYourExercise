/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 8 (Artin rings), Exercise 8.3.

**Exercise statement (Atiyah–Macdonald, Ch. 8, Exercise 3), verbatim form.**
"Let `k` be a field and `A` a finitely generated `k`-algebra. Prove that the following are
equivalent: (1) `A` is Artinian. (2) `A` is a finite `k`-algebra."
Here "finite `k`-algebra" means finitely generated as a `k`-module, equivalently
`dim_k A < ∞`.

**Formal statement.** `solution` below: for every field `k` and every commutative ring `A`
with `[Algebra k A]` and `[Algebra.FiniteType k A]` (that is: `A` is a finitely generated
`k`-algebra), we have `IsArtinianRing A ↔ Module.Finite k A`.
`Module.Finite k A` is exactly "`A` is a finite `k`-algebra"; the companion theorem
`solution_finiteDimensional` restates the same equivalence with `FiniteDimensional k A`,
the "finite-dimensional `k`-vector space" phrasing of the exercise.
Coverage: the exercise is a single assertion (one iff); *both* directions are proved
(`finite_of_isArtinianRing`, `isArtinianRing_of_finite`) and the iff is assembled from
them. No hypothesis of the exercise is dropped and none is added: `A` may be the zero
ring, and then both sides hold.

Source of the natural-language proof (tag `8.3` mapped to `8-3`):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8-3
(local copy: `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-8-3/proof.tex`)

**Mathematical approach.**
* (⇐, `isArtinianRing_of_finite`) Ideals of `A` are `k`-subspaces, and a finite-dimensional
  `k`-vector space has the descending chain condition on subspaces, so `A` is Artinian:
  `IsArtinianRing.of_finite`.
* (⇒, `finite_of_isArtinianRing`) Let `J = Ring.jacobson A`. Since `A` is Artinian, `J` is
  the nilradical and is nilpotent, and `A ⧸ J` is reduced Artinian. By the structure
  theorem for reduced Artinian rings (`IsArtinianRing.quotNilradicalEquivPi`),
  `A ⧸ nilradical A` is a *finite product of fields*, namely the residue fields `A ⧸ m`
  for the (finitely many) maximal ideals `m`. Each `A ⧸ m` is a finitely generated
  `k`-algebra that happens to be a field, hence finite over `k` by Zariski's lemma
  (the weak Nullstellensatz, `finite_of_finite_type_of_isJacobsonRing`). A finite product
  of finite `k`-modules is finite over `k`, so `A ⧸ J` is finite over `k`. Finally `A` is
  semiprimary (Artinian) with nilpotent Jacobson radical, and finiteness of `A ⧸ J` over
  `k` lifts to finiteness of `A` over `k` (`IsSemiprimaryRing.finite_of_isArtinian`),
  an induction down the filtration `A ⊇ J ⊇ J² ⊇ ⋯ ⊇ J^N = 0` whose successive
  quotients are modules over the semisimple ring `A ⧸ J`.

The source proof decomposes `A` into finitely many Artinian *local* rings, passes to the
local case with `m^N = 0`, writes `A = k[x₁,…,x_r]` and bounds a `k`-spanning set by
monomials of bounded degree using monic `f_i` with `f_i(x_i) ∈ m`. The formal proof takes
the equivalent product-of-fields form of the same structure theorem and the standard
nilpotent-lifting lemma; the local-case computation is the special case in which the
product of residue fields has a single factor. Nothing is weakened: all inputs
(finite generation over `k`, Zariski's lemma, nilpotence of the radical, the structure
theorem) are the ones used by the source argument.

**Scope adaptations:** none.

Cross-check: Mathlib's `Module.finite_iff_isArtinianRing` is a general form of the same
equivalence (for finite type algebras over an Artinian base ring); the proofs below do not
use it, they assemble the result from the three ingredients named above.
-/

import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Artinian.Module

namespace AtiyahMcdonald69.Ex_8_3

-- A temporary `Field` instance on the quotients by maximal ideals, as in Mathlib.
attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-! ### Zariski's lemma (weak Nullstellensatz) -/

/-- Zariski's lemma: the residue field of a maximal ideal of a finitely generated
`k`-algebra is finite over `k`. -/
theorem finite_residueField [Algebra.FiniteType k A] (m : MaximalSpectrum A) :
    Module.Finite k (A ⧸ m.asIdeal) :=
  finite_of_finite_type_of_isJacobsonRing k (A ⧸ m.asIdeal)

/-! ### The structure theorem: `A ⧸ nilradical A` is a finite product of residue fields -/

/-- An Artinian finitely generated `k`-algebra modulo its nilradical is a finite product of
fields, each finite over `k`; hence it is a finite `k`-module. -/
theorem finite_quotient_nilradical [Algebra.FiniteType k A] [IsArtinianRing A] :
    Module.Finite k (A ⧸ nilradical A) := by
  classical
  have hfin : ∀ m : MaximalSpectrum A, Module.Finite k (A ⧸ m.asIdeal) :=
    fun m => finite_residueField m
  have hpi : Module.Finite k (∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) := Module.Finite.pi
  exact Module.Finite.equiv
    ((IsArtinianRing.quotNilradicalEquivPi A).restrictScalars k).toLinearEquiv.symm

/-- In an Artinian ring the Jacobson radical is the nilradical; in particular it is
nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`). -/
theorem jacobson_eq_nilradical [IsArtinianRing A] : Ring.jacobson A = nilradical A :=
  Ring.jacobson_eq_nilradical_of_krullDimLE_zero A

theorem finite_quotient_jacobson [Algebra.FiniteType k A] [IsArtinianRing A] :
    Module.Finite k (A ⧸ Ring.jacobson A) := by
  rw [jacobson_eq_nilradical]
  exact finite_quotient_nilradical

/-! ### Lifting finiteness through the nilpotent radical -/

/-- **(⇒) of Exercise 8.3.** An Artinian finitely generated `k`-algebra is a finite
`k`-module: `A ⧸ J` is finite over `k` (`finite_quotient_jacobson`) and finiteness lifts
back through the nilpotent ideal `J` by the semiprimary induction on
`A ⊇ J ⊇ J² ⊇ ⋯ ⊇ J^N = 0`. -/
theorem finite_of_isArtinianRing [Algebra.FiniteType k A] [IsArtinianRing A] :
    Module.Finite k A := by
  have hq : Module.Finite k (A ⧸ Ring.jacobson A) := finite_quotient_jacobson
  exact IsSemiprimaryRing.finite_of_isArtinian k A A

/-! ### The easy direction: finite over `k` implies Artinian -/

/-- **(⇐) of Exercise 8.3.** A finite `k`-algebra has the descending chain condition on
ideals (ideals are `k`-subspaces of a finite-dimensional space), so it is Artinian. -/
theorem isArtinianRing_of_finite (h : Module.Finite k A) : IsArtinianRing A :=
  IsArtinianRing.of_finite k A

/-! ### Exercise 8.3 -/

/-- **Atiyah–Macdonald, Exercise 8.3.** Let `k` be a field and `A` a finitely generated
`k`-algebra. Then `A` is Artinian if and only if `A` is a finite `k`-algebra. -/
theorem solution (k : Type*) (A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : IsArtinianRing A ↔ Module.Finite k A :=
  ⟨fun _ => finite_of_isArtinianRing, fun h => isArtinianRing_of_finite h⟩

/-- Exercise 8.3 in the textbook's "finite-dimensional vector space" phrasing: a finitely
generated `k`-algebra is Artinian if and only if `dim_k A` is finite. -/
theorem solution_finiteDimensional (k : Type*) (A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : IsArtinianRing A ↔ FiniteDimensional k A :=
  solution k A

end AtiyahMcdonald69.Ex_8_3
