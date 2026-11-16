/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison-Wesley, 1969),
Chapter 9 ("Discrete valuation rings and Dedekind domains"), Exercise 5.

**Statement of the exercise** (Chapter 9, Exercise 5, p. 99 of the book):

> Let `M` be a finitely-generated module over a Dedekind domain.
> Prove that `M` is flat ⟺ `M` is torsion-free.

Torsion-freeness is meant in the sense of the book: for `a ≠ 0` and `m : M`,
`a • m = 0` implies `m = 0`; equivalently the torsion submodule `T(M)` is zero
(see `solution_torsion`).  `IsDedekindDomain A` is Mathlib's rendering of the book's
definition (9.3): a Noetherian domain of Krull dimension at most one which is
integrally closed.

**Approach** — the book's own proof, as recorded in the natural-language solution:

* `⇒` (easy direction).  A flat module is torsion-free: tensor the injection
  `A --(·a)--> A` (for `a ≠ 0`) with `M`.  Flatness keeps it injective, and under the
  canonical isomorphism `A ⊗ M ≃ M` it becomes the map `m ↦ a • m`, which is therefore
  injective on `M`.  (Formalized as `smul_right_injective_of_flat`, spelled out with
  `Module.Flat.rTensor_preserves_injective_linearMap` and the canonical isomorphism
  `TensorProduct.lid`; `isTorsionFree_of_flat` and `torsion_eq_bot_of_flat` are its
  consequences.)
* `⇐` (hard direction).  If `M` is finitely generated and torsion-free, then for every
  maximal ideal `P` the localization `M_P` is a finitely generated torsion-free module
  over `A_P` (Exercise 3.13 of the book), and `A_P` is a discrete valuation ring, hence
  a principal ideal domain; a finitely generated torsion-free module over a PID is free
  (Exercise 7.15).  Thus `M_P` is free, hence flat, for every maximal ideal `P`, and a
  module that is flat after localizing at every maximal ideal is flat (Exercise 7.16
  and Proposition 3.10).  (Formalized as `free_of_finite_of_isTorsionFree_localized`,
  `flat_of_localized_free`, and `flat_of_finite_of_isTorsionFree`.)

**Formalization notes.**

* The book's hypothesis that `M` is finitely generated is kept in `solution`, which is
  proved from the three steps of the book's argument above (each a separate lemma).
* `solution_torsion` restates the same theorem using the torsion submodule `T(M)`, the
  formulation the book uses; `solution_smul` restates it in the elementwise form
  "`a • m = 0` with `a ≠ 0` forces `m = 0`".
* `solution_general` records a strengthening that is true but is *not* part of the
  book's exercise (the book assumes `M` is finitely generated): over a Dedekind domain
  every module, finitely generated or not, is flat if and only if it is torsion-free.
  It is Mathlib's `IsDedekindDomain.flat_iff_torsion_eq_bot`.
* No `sorry`, no custom axioms, no extra hypotheses.
* Statement recovered verbatim from J. D. K. Carlson, *Exercises to Atiyah and
  Macdonald's Introduction to Commutative Algebra* (Chapter 9, Exercise 5):
  <https://math.sci.uwo.ca/~jcarlso6/intro_comm_alg(2019).pdf>; independently
  corroborated by M. Kosters, arXiv:1109.6733, Theorem 4.1 (who attributes the
  equivalence "torsion-free ⟺ flat" for finitely generated modules over a Dedekind
  domain to Exercise 9.5) and by A. Papaioannou's solutions to the same exercise.
* Source of the natural-language proof:
  https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-9-5
  (j346huan/DoYourExercise, commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91).
-/
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Basic

namespace AtiyahMcdonald69.Ex_9_5

open scoped nonZeroDivisors

/-! ## Step 1: a flat module is torsion-free -/

/-- (Exercise 9.5, easy direction.)  If `M` is a flat module over a domain then
multiplication by any `a ≠ 0` is injective on `M`: tensor the injection
`A --(·a)--> A` with the flat module `M`.  This is the book's argument, spelled out. -/
theorem smul_right_injective_of_flat {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Flat A M] {a : A} (ha : a ≠ 0) :
    Function.Injective fun m : M => a • m := by
  -- `· * a : A → A` is injective because `A` is a domain and `a ≠ 0`
  have hinj : Function.Injective (LinearMap.toSpanSingleton A A a) := by
    rw [← LinearMap.ker_eq_bot]
    simpa using LinearMap.ker_toSpanSingleton A ha
  -- tensoring with the flat module `M` preserves this injectivity
  have h : Function.Injective ((LinearMap.rTensor M (LinearMap.toSpanSingleton A A a) :
      TensorProduct A A M →ₗ[A] TensorProduct A A M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  -- and modulo the canonical isomorphism `A ⊗ M ≃ M` this map is `m ↦ a • m`
  have h2 : (fun m : M => a • m) = (TensorProduct.lid A M) ∘
      (LinearMap.rTensor M (LinearMap.toSpanSingleton A A a)) ∘
        (TensorProduct.lid A M).symm := by
    ext m
    simp
  rw [h2]
  exact (TensorProduct.lid A M).injective.comp (h.comp (TensorProduct.lid A M).symm.injective)

/-- (Exercise 9.5, easy direction, concluding torsion-freeness.) -/
theorem isTorsionFree_of_flat {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Flat A M] : Module.IsTorsionFree A M where
  isSMulRegular _r hr := smul_right_injective_of_flat (isRegular_iff_ne_zero.mp hr)

/-- (Exercise 9.5, easy direction, in the `T(M)` language of the book.)  A flat module
over a domain has trivial torsion submodule. -/
theorem torsion_eq_bot_of_flat {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Flat A M] : Submodule.torsion A M = ⊥ :=
  Submodule.isTorsionFree_iff_torsion_eq_bot.mp isTorsionFree_of_flat

/-! ## Step 2: a finitely generated torsion-free module is locally free -/

/-- (Exercise 9.5, hard direction, first half; uses Exercises 3.13 and 7.15 of the
book.)  A finitely generated torsion-free module over a Dedekind domain becomes free
after localizing at any maximal ideal: the localization is a finitely generated
torsion-free module over the localization of `A` at that ideal, which is a discrete
valuation ring, hence a principal ideal domain. -/
theorem free_of_finite_of_isTorsionFree_localized {A M : Type*} [CommRing A]
    [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] (P : Ideal A) [P.IsMaximal] :
    Module.Free (Localization P.primeCompl) (LocalizedModule P.primeCompl M) :=
  Module.free_of_finite_type_torsion_free'

/-! ## Step 3: local freeness implies flatness (Exercise 7.16 with Proposition 3.10) -/

/-- (Exercise 9.5, hard direction, second half.)  A module which is free, hence flat,
after localization at every maximal ideal is flat. -/
theorem flat_of_localized_free {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      Module.Free (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Flat A M :=
  Module.flat_of_localized_maximal M fun P _ =>
    Module.Flat.trans A (Localization P.primeCompl) (LocalizedModule P.primeCompl M)

/-- (Exercise 9.5, hard direction.)  A finitely generated torsion-free module over a
Dedekind domain is flat. -/
theorem flat_of_finite_of_isTorsionFree {A M : Type*} [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] :
    Module.Flat A M :=
  flat_of_localized_free fun P _ => free_of_finite_of_isTorsionFree_localized P

/-! ## The exercise -/

/-- **Atiyah–Macdonald, Exercise 9.5.**  Let `A` be a Dedekind domain and let `M` be a
finitely generated `A`-module.  Then `M` is flat over `A` if and only if `M` is
torsion-free. -/
theorem solution (A : Type*) [CommRing A] [IsDedekindDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M :=
  ⟨fun _ => isTorsionFree_of_flat, fun _ => flat_of_finite_of_isTorsionFree⟩

/-- **Atiyah–Macdonald, Exercise 9.5**, in the `T(M) = 0` formulation of the book: a
finitely generated module over a Dedekind domain is flat if and only if its torsion
submodule vanishes. -/
theorem solution_torsion (A : Type*) [CommRing A] [IsDedekindDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.Flat A M ↔ Submodule.torsion A M = ⊥ :=
  (solution A M).trans Submodule.isTorsionFree_iff_torsion_eq_bot

/-- Torsion-freeness of a module over a domain, written in the elementwise form used by
the book: no nonzero scalar annihilates a nonzero element. -/
theorem isTorsionFree_iff_forall_smul_eq_zero {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] :
    Module.IsTorsionFree A M ↔ ∀ (a : A) (m : M), a ≠ 0 → a • m = 0 → m = 0 := by
  constructor
  · intro h a m ha hm
    exact (IsRegular.of_ne_zero ha).smul_eq_zero_iff_right.mp hm
  · intro h
    refine ⟨fun r hr => ?_⟩
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    intro x y hxy
    have hxy' : r • x = r • y := hxy
    have h1 : r • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
    exact sub_eq_zero.mp (h r (x - y) hr0 h1)

/-- **Atiyah–Macdonald, Exercise 9.5**, in the elementwise form in which the book states
torsion-freeness: `M` is flat iff annihilating a nonzero element of `M` by a nonzero
scalar is impossible. -/
theorem solution_smul (A : Type*) [CommRing A] [IsDedekindDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.Flat A M ↔ ∀ (a : A) (m : M), a ≠ 0 → a • m = 0 → m = 0 :=
  (solution A M).trans isTorsionFree_iff_forall_smul_eq_zero

/-- **Strengthening of Exercise 9.5**, explicitly *not* part of the book's statement
(which assumes `M` finitely generated): over a Dedekind domain, every module is flat if
and only if it is torsion-free.  This is Mathlib's
`IsDedekindDomain.flat_iff_torsion_eq_bot`. -/
theorem solution_general (A : Type*) [CommRing A] [IsDedekindDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Module.IsTorsionFree A M :=
  IsDedekindDomain.flat_iff_torsion_eq_bot.trans
    Submodule.isTorsionFree_iff_torsion_eq_bot.symm

/-- Sanity check: the hypotheses of the exercise are satisfiable; the statement applies
in particular to `A = ℤ`. -/
example : Module.Flat ℤ ℤ ↔ Module.IsTorsionFree ℤ ℤ := solution ℤ ℤ

end AtiyahMcdonald69.Ex_9_5

/-! ## Axiom check: no `sorry`, no custom axioms, no extra hypotheses -/

#print axioms AtiyahMcdonald69.Ex_9_5.smul_right_injective_of_flat
#print axioms AtiyahMcdonald69.Ex_9_5.torsion_eq_bot_of_flat
#print axioms AtiyahMcdonald69.Ex_9_5.free_of_finite_of_isTorsionFree_localized
#print axioms AtiyahMcdonald69.Ex_9_5.flat_of_localized_free
#print axioms AtiyahMcdonald69.Ex_9_5.flat_of_finite_of_isTorsionFree
#print axioms AtiyahMcdonald69.Ex_9_5.solution
#print axioms AtiyahMcdonald69.Ex_9_5.solution_torsion
#print axioms AtiyahMcdonald69.Ex_9_5.solution_smul
#print axioms AtiyahMcdonald69.Ex_9_5.solution_general
