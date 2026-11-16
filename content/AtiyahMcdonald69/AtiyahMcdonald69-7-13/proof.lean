/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 7.13.
<https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-13>

Statement (Chapter 7, exercise 13 of the 1969 book):

  Let `f : A → B` be a ring homomorphism of finite type. Show that the fibres of
  `f* : Spec B → Spec A` are Noetherian subspaces of `Spec B`.

Recovering the quantifiers: `A` and `B` are arbitrary commutative rings (nothing is
assumed Noetherian), `f` is an arbitrary ring homomorphism making `B` a finitely
generated `A`-algebra, and the claim is about *every* point `p` of `Spec A`
simultaneously.  The fibre of `f*` over `p` is the subspace
`(f*)⁻¹{p} = PrimeSpectrum.comap f ⁻¹' {p}` of `Spec B`, with the induced topology.

The proof is the one in the book: the fibre over `p` is homeomorphic to
`Spec (κ(p) ⊗[A] B)`, where `κ(p)` is the residue field of the local ring `A_p`;
that fibre ring is a finitely generated algebra over the field `κ(p)` (base change),
hence Noetherian by Hilbert's basis theorem, hence its spectrum is a Noetherian
space (exercise 6.8), and Noetherian-ness transfers across the homeomorphism.

Verification: `/opt/lean/bin/lean -DwarningAsError=true answer.lean`
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

open TopologicalSpace

namespace AtiyahMcdonald69.Ex_7_13

universe u v

/-! ### Exercise 6.8 (the dependency used in the proof)

The spectrum of a Noetherian ring is a Noetherian topological space. -/

theorem noetherianSpace_primeSpectrum (R : Type u) [CommRing R] [IsNoetherianRing R] :
    NoetherianSpace (PrimeSpectrum R) :=
  PrimeSpectrum.instNoetherianSpace R

section Fiber

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-! ### The fibre ring `κ(p) ⊗[A] B` and the homeomorphism of the fibre with its spectrum -/

/-- The fibre of `f* : Spec B → Spec A` over `p`, namely the subspace
`PrimeSpectrum.comap f ⁻¹' {p}` of `Spec B`, is homeomorphic to the spectrum of the
fibre ring `κ(p) ⊗[A] B = p.asIdeal.Fiber B`. -/
noncomputable def fiberHomeomorph (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} ≃ₜ
      PrimeSpectrum (p.asIdeal.Fiber B) :=
  PrimeSpectrum.preimageHomeomorphFiber A B p

open scoped TensorProduct in
/-- The same homeomorphism with the fibre ring written as the tensor product
`κ(p) ⊗[A] B` (`Ideal.Fiber p B` is by definition this tensor product). -/
noncomputable def fiberHomeomorph_tensorProduct (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} ≃ₜ
      PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] B) :=
  fiberHomeomorph p

/-- The fibre of `f*` over `p` is, set-theoretically, the set of primes of `B` lying over
`p`. -/
theorem fiber_eq_setOf_under (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
      = {q : PrimeSpectrum B | q.asIdeal.under A = p.asIdeal} := by
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Ideal.under_def,
    PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]

/-- The fibre ring `κ(p) ⊗[A] B` is a finitely generated `κ(p)`-algebra: if `B` is
generated as an `A`-algebra by `b₁, …, bₙ`, then `κ(p) ⊗[A] B` is generated as a
`κ(p)`-algebra by their images `1 ⊗ b₁, …, 1 ⊗ bₙ`. -/
theorem fiberRing_finiteType (p : PrimeSpectrum A) [Algebra.FiniteType A B] :
    Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
  inferInstance

/-- The exercise's generating step, in explicit form: if `b₁, …, bₙ` generate `B` as an
`A`-algebra, then their images `1 ⊗ bᵢ` generate the fibre ring `κ(p) ⊗[A] B` as a
`κ(p)`-algebra; equivalently, the fibre ring is a quotient of a polynomial ring in
finitely many variables over the field `κ(p)`. -/
theorem fiberRing_exists_surjective_mvPolynomial (p : PrimeSpectrum A)
    [Algebra.FiniteType A B] :
    ∃ (n : ℕ) (g : MvPolynomial (Fin n) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber B),
      Function.Surjective g :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (fiberRing_finiteType p)

/-- Hilbert's basis theorem: the fibre ring `κ(p) ⊗[A] B`, being a finitely generated
algebra over the field `κ(p)`, is a Noetherian ring. -/
theorem fiberRing_isNoetherianRing (p : PrimeSpectrum A) [Algebra.FiniteType A B] :
    IsNoetherianRing (p.asIdeal.Fiber B) :=
  Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField (p.asIdeal.Fiber B)

/-- Exercise 7.13, algebra form: if `B` is a finitely generated `A`-algebra, then for
every `p : Spec A` the fibre of `Spec B → Spec A` over `p` is a Noetherian subspace of
`Spec B`. -/
theorem fiber_noetherianSpace (p : PrimeSpectrum A) [Algebra.FiniteType A B] :
    NoetherianSpace (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) :=
  (noetherianSpace_iff_of_homeomorph (fiberHomeomorph p)).mpr
    (@noetherianSpace_primeSpectrum (p.asIdeal.Fiber B) _ (fiberRing_isNoetherianRing p))

end Fiber

section RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Atiyah–Macdonald, Exercise 7.13: for a ring homomorphism `f : A → B` of finite type
and any prime `p` of `A`, the fibre `(f*)⁻¹{p}` of `f* : Spec B → Spec A` is a
Noetherian subspace of `Spec B`. -/
theorem solution (f : A →+* B) (hf : f.FiniteType) (p : PrimeSpectrum A) :
    NoetherianSpace (PrimeSpectrum.comap f ⁻¹' {p}) :=
  @fiber_noetherianSpace A B _ _ f.toAlgebra p hf

end RingHom

end AtiyahMcdonald69.Ex_7_13

/-! ### Axiom check: the solution uses only the standard axioms. -/

#print axioms AtiyahMcdonald69.Ex_7_13.noetherianSpace_primeSpectrum
#print axioms AtiyahMcdonald69.Ex_7_13.fiberHomeomorph
#print axioms AtiyahMcdonald69.Ex_7_13.fiberHomeomorph_tensorProduct
#print axioms AtiyahMcdonald69.Ex_7_13.fiber_eq_setOf_under
#print axioms AtiyahMcdonald69.Ex_7_13.fiberRing_finiteType
#print axioms AtiyahMcdonald69.Ex_7_13.fiberRing_exists_surjective_mvPolynomial
#print axioms AtiyahMcdonald69.Ex_7_13.fiberRing_isNoetherianRing
#print axioms AtiyahMcdonald69.Ex_7_13.fiber_noetherianSpace
#print axioms AtiyahMcdonald69.Ex_7_13.solution
