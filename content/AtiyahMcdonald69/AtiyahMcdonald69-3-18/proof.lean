/-
Copyright (c) 2026 The Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter III, Exercise 18

## The exercise

M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley 1969,
Chapter III (*Rings and Modules of Fractions*), Exercises, p. 46:

> 18. Let `f : A → B` be a flat homomorphism of rings, let `q` be a prime ideal of `B` and let
> `p = qᶜ`. Then `f* : Spec(B_q) → Spec(A_p)` is surjective.
> [For `B_p` is flat over `A_p` by (3.10), and `B_q` is a local ring of `B_p`, hence is flat over
> `B_p`. Hence `B_q` is flat over `A_p` and satisfies condition (3) of Exercise 16.]

## Formalisation

The canonical ring homomorphism `f* : A_p →+* B_q` is `AtiyahMcdonald69.Ex_3_18.localizedMap f q`,
i.e. Mathlib's `Localization.localRingHom`; it is the unique ring homomorphism making the square
with `f`, `A → A_p` and `B → B_q` commute (`localizedMap_algebraMap`). The exercise is
`comap_localizedMap_surjective` / `solution`.

The proof follows the bracketed proof of the book, with each step named:

* `flat_tensorProduct_atPrime`: (3.10), the base-change step: `B ⊗_A A_p` is a flat
  `A_p`-module.
* `localizedMap_flat`: `B_q` is flat over `A_p`. In the book this is the chain
  "`B_p = B ⊗_A A_p` is flat over `A_p` by base change (3.10), and `B_q = (B_p)_{q B_p}` is a
  localization of `B_p`, hence flat over `B_p`, hence over `A_p`". Formally this is Mathlib's
  `RingHom.Flat.localRingHom`, whose proof performs exactly this tower argument.
* `localizedMap_maximalIdeal_le` and `localizedMap_maximalIdeal_map_ne_top`: the maximal ideal
  `pA_p` of the local ring `A_p` extends to `pB_q ⊆ qB_q`, and `qB_q ≠ (1)` because `q` is prime;
  this is condition (iii) of Exercise 3.16, made explicit.
* `faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top`: condition (iii) of Exercise 3.16 for a
  local base ring: flat + the maximal ideal does not extend to the unit ideal ⇒ faithfully flat.
* `PrimeSpectrum.comap_surjective_of_faithfullyFlat`: faithfully flat ⇒ surjective on spectra.

## Main exported results

* `solution`, `comap_localizedMap_surjective`, `solution_of_eq` (book phrasing, with `p` named),
  `solution_algebra` (algebra formulation): the exercise.
* `exists_isPrime_comap_eq`: ideal-theoretic form — every prime of `A_p` is the contraction of a
  prime of `B_q`.
* `exists_isPrime_le_comap_eq`: going-down form — every prime `p' ≤ qᶜ` of `A` is the contraction
  of a prime `q' ≤ q` of `B`.
* `localizedMap_algebraMap`, `localizedMap_unique`, `comap_localizedMap_comp`: the map `f*` of the
  exercise is the canonical, unique one, and is the restriction of `Spec B → Spec A`.
* `localizedMap_flat`, `flat_tensorProduct_atPrime`, `faithfullyFlat_localizedMap`,
  `localizedMap_maximalIdeal_comap`: the structural facts used in the proof.
* `solution_int_rat`: non-vacuity check (`ℤ →+* ℚ`, `q = p = (0)`).
* `not_surjective_int_zmod_two`, `int_castRingHom_zmod_two_not_flat`: the flatness hypothesis
  cannot be removed (counterexample `ℤ →+* ZMod 2`, `q = (0)`, `p = (2)`).
* `faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top`: the criterion (iii) of Exercise 3.16.

The `#print axioms` commands at the end show that every one of these depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Faithfulness, scope and omitted hypotheses

* Nothing is weakened: `f.Flat` is flatness of `f` in the sense of the book (i.e. `B` is a flat
  `A`-module through `f`), `q` is an honest prime ideal of `B` and `p = qᶜ = q.comap f` is the
  contraction (prime, by `Ideal.IsPrime.comap`), and `Spec(B_q) → Spec(A_p)` is induced by the
  honest localisation map between the honest localisations `Localization.AtPrime q` and
  `Localization.AtPrime (q.comap f)`. No Noetherian or finiteness hypothesis is used anywhere;
  the statement is false without flatness, see `not_surjective_int_zmod_two`.
* `q` is required to be prime for `B_q` to make sense and for `p = qᶜ` to be prime; `p` is then
  automatically prime, so no further hypothesis on `p` is needed.
* The natural-language solution
  (j346huan/DoYourExercise, `AtiyahMcdonald69-3-18`) argues: "Since `A_p` has only one maximal
  ideal, condition (iii) of 3.16 holds." This is correct, and it is exactly the step
  `localizedMap_maximalIdeal_map_lt_top` + `faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top`
  below: the extension of the unique maximal ideal `pA_p` into `B_q` is contained in the maximal
  ideal `qB_q`, so it is proper. (The solution's phrase "`B_q` is a localization of `B_p`" is
  justified because `A ∖ p` maps into `B ∖ q`.) Note that the extension `pB_q` can be a proper
  non-maximal ideal, so faithfulness is not automatic from flatness alone.
-/

namespace AtiyahMcdonald69
namespace Ex_3_18

universe u v

open scoped TensorProduct

section RingHomData

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- The canonical ring homomorphism `A_p →+* B_q` for `p = qᶜ`, where `f : A →+* B` is a ring
homomorphism and `q` is a prime ideal of `B`. This is the map underlying the map on prime spectra
`f* : Spec(B_q) → Spec(A_p)` of Exercise 3.18. -/
noncomputable def localizedMap (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    Localization.AtPrime (q.comap f) →+* Localization.AtPrime q :=
  Localization.localRingHom (I := q.comap f) q f rfl

/-- `localizedMap f q` is compatible with `f`, `A → A_p` and `B → B_q`: it is the canonical map
induced by the universal property of localisation. -/
lemma localizedMap_algebraMap (f : A →+* B) (q : Ideal B) [q.IsPrime] (a : A) :
    localizedMap f q (algebraMap A (Localization.AtPrime (q.comap f)) a) =
      algebraMap B (Localization.AtPrime q) (f a) :=
  Localization.localRingHom_to_map _ _ _ _ _

/-- The map `A_p →+* B_q` is a local ring homomorphism: it is induced by a map of local rings at
matching primes. -/
instance isLocalHom_localizedMap (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    IsLocalHom (localizedMap f q) :=
  Localization.isLocalHom_localRingHom (q.comap f) q f rfl

/-- The maximal ideal of `B_q` contracts to the maximal ideal of `A_p`: the map on spectra
`f* : Spec(B_q) → Spec(A_p)` sends the closed point to the closed point. -/
lemma localizedMap_maximalIdeal_comap (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).comap (localizedMap f q) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f)) :=
  IsLocalRing.maximalIdeal_comap _

/-- The extension of the maximal ideal `pA_p` of `A_p` to `B_q` is contained in `qB_q`: the
computation `pA_p · B_q = pB_q ⊆ qB_q`. -/
lemma localizedMap_maximalIdeal_le (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f))).map (localizedMap f q) ≤
      Ideal.map (algebraMap B (Localization.AtPrime q)) q := by
  have hcomp : (localizedMap f q).comp (algebraMap A (Localization.AtPrime (q.comap f))) =
      (algebraMap B (Localization.AtPrime q)).comp f := by
    ext a
    exact localizedMap_algebraMap f q a
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr le_rfl)

/-- Condition (iii) of Exercise 3.16 for the local homomorphism `A_p →+* B_q`: the extension
`pB_q` of the maximal ideal `pA_p` is contained in `qB_q`, which is proper because `q` is prime. -/
lemma localizedMap_maximalIdeal_map_ne_top (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f))).map (localizedMap f q) ≠ ⊤ := by
  intro htop
  have h1 : Ideal.map (algebraMap B (Localization.AtPrime q)) q = ⊤ :=
    top_le_iff.mp (htop ▸ localizedMap_maximalIdeal_le f q)
  rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1

/-- The maximal ideal of `A_p` maps into the proper maximal ideal of `B_q`. -/
lemma localizedMap_maximalIdeal_map_lt_top (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f))).map (localizedMap f q) < ⊤ :=
  lt_top_iff_ne_top.mpr (localizedMap_maximalIdeal_map_ne_top f q)

end RingHomData

section FaithfullyFlatCriterion

/-- Faithful flatness criterion of Exercise 3.16, condition (iii), for a local base ring: if `S` is
a flat algebra over a local ring `R` and the maximal ideal of `R` does not extend to the unit
ideal of `S`, then `S` is faithfully flat over `R`.

This is the form in which the criterion is used in the proof of Exercise 3.18: for a local ring,
every proper ideal is contained in the maximal ideal, so it suffices to check the maximal ideal. -/
theorem faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≠ ⊤) :
    Module.FaithfullyFlat R S := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop ↦ h ?_⟩
  have hle : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hmono : I • (⊤ : Submodule R S) ≤
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) :=
    Submodule.smul_mono hle le_rfl
  rw [htop] at hmono
  simpa using hmono

end FaithfullyFlatCriterion

section MainTheorem

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- Atiyah–Macdonald (3.10) in the form used in the bracket of Exercise 3.18: base change of the
flat `A`-algebra `B` to `A_p` is flat over `A_p`, i.e. `B ⊗_A A_p` (equivalently `A_p ⊗_A B`) is
a flat `A_p`-module. (Together with flatness of the further localisation `B_p → B_q` this gives
`localizedMap_flat`.) -/
theorem flat_tensorProduct_atPrime [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] B) :=
  Module.Flat.baseChange A (Localization.AtPrime p) B

/-- `B_q` is flat over `A_p`: base change of the flat map `f` to `A_p`, followed by the further
localisation `B_p → B_q` (see the bracket of Exercise 3.18, using (3.10)). -/
lemma localizedMap_flat (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime] :
    (localizedMap f q).Flat :=
  hf.localRingHom q (q.comap f) rfl

/-- `B_q` is faithfully flat over `A_p`: it is flat, the maximal ideal of the local ring `A_p`
extends into the proper ideal `qB_q`, and hence condition (iii) of Exercise 3.16 holds. -/
theorem faithfullyFlat_localizedMap (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime] :
    (localizedMap f q).FaithfullyFlat := by
  let _ : Algebra (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) :=
    (localizedMap f q).toAlgebra
  have hflat : Module.Flat (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) :=
    localizedMap_flat f hf q
  have hproper : (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f))).map
      (algebraMap (Localization.AtPrime (q.comap f)) (Localization.AtPrime q)) ≠ ⊤ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact localizedMap_maximalIdeal_map_ne_top f q
  exact faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top hproper

/-- Exercise 3.18 for the canonical localisation map `localizedMap f q`. -/
theorem comap_localizedMap_surjective (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime] :
    Function.Surjective (PrimeSpectrum.comap (localizedMap f q)) := by
  let _ : Algebra (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) :=
    (localizedMap f q).toAlgebra
  have hff : Module.FaithfullyFlat (Localization.AtPrime (q.comap f))
      (Localization.AtPrime q) := faithfullyFlat_localizedMap f hf q
  simpa [RingHom.algebraMap_toAlgebra] using
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := Localization.AtPrime (q.comap f)) (B := Localization.AtPrime q))

/-- **Exercise 3.18** (Atiyah–Macdonald, Chapter III): if `f : A →+* B` is a flat homomorphism of
rings, `q` is a prime ideal of `B` and `p = qᶜ`, then `f* : Spec(B_q) → Spec(A_p)` is surjective.

Here `f*` is the map on prime spectra induced by the canonical local ring homomorphism
`A_p →+* B_q`, i.e. by `Localization.localRingHom (q.comap f) q f rfl`. -/
theorem solution (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime] :
    Function.Surjective
      (PrimeSpectrum.comap (Localization.localRingHom (I := q.comap f) q f rfl)) := by
  simpa [localizedMap] using comap_localizedMap_surjective f hf q

/-- The map `A_p →+* B_q` of Exercise 3.18 is the *unique* ring homomorphism compatible with `f`:
this is what makes `f* : Spec(B_q) → Spec(A_p)` well defined. -/
theorem localizedMap_unique (f : A →+* B) (q : Ideal B) [q.IsPrime]
    (ψ : Localization.AtPrime (q.comap f) →+* Localization.AtPrime q)
    (hψ : ∀ a : A, ψ (algebraMap A (Localization.AtPrime (q.comap f)) a) =
      algebraMap B (Localization.AtPrime q) (f a)) :
    ψ = localizedMap f q := by
  refine IsLocalization.ringHom_ext (q.comap f).primeCompl ?_
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, hψ, localizedMap_algebraMap]

/-- The map `Spec(B_q) → Spec(A_p)` of Exercise 3.18 is the restriction of `f* : Spec B → Spec A`
along the localisation maps: the evident square of spectra commutes. (This is the precise sense in
which `f*` in the exercise is *the* map induced by `f`.) -/
lemma comap_localizedMap_comp (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime (q.comap f)))) ∘
        (PrimeSpectrum.comap (localizedMap f q)) =
      (PrimeSpectrum.comap f) ∘ (PrimeSpectrum.comap (algebraMap B (Localization.AtPrime q))) := by
  rw [← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp]
  congr 1
  ext a
  exact localizedMap_algebraMap f q a

/-- Exercise 3.18 in the exact phrasing of the book, with the prime ideal `p = qᶜ` named
explicitly. -/
theorem solution_of_eq (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime]
    (p : Ideal A) [p.IsPrime] (hp : p = q.comap f) :
    Function.Surjective (PrimeSpectrum.comap (Localization.localRingHom p q f hp)) := by
  subst hp
  exact solution f hf q

/-- Sanity check (non-vacuity): the hypotheses are satisfiable, e.g. for the flat map
`ℤ →+* ℚ` and `q = (0)`, `p = (0)`, where the statement says that `Spec ℚ → Spec ℚ` is
surjective. -/
theorem solution_int_rat : Function.Surjective
    (PrimeSpectrum.comap (localizedMap (Int.castRingHom ℚ) (⊥ : Ideal ℚ))) :=
  comap_localizedMap_surjective _
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ ℚ)) ⊥

/-- Exercise 3.18 in the algebra formulation: a flat `A`-algebra `B`, a prime `q` of `B` and
`p = qᶜ`. -/
theorem solution_algebra [Algebra A B] [Module.Flat A B] (q : Ideal B) [q.IsPrime] :
    Function.Surjective (PrimeSpectrum.comap (Localization.localRingHom
      (I := q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :=
  solution (algebraMap A B) (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A B›) q

/-- The ideal-theoretic content of Exercise 3.18: every prime ideal of `A_p` is the contraction of
a prime ideal of `B_q`. -/
theorem exists_isPrime_comap_eq (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime]
    (P : Ideal (Localization.AtPrime (q.comap f))) [P.IsPrime] :
    ∃ Q : Ideal (Localization.AtPrime q), Q.IsPrime ∧ Q.comap (localizedMap f q) = P := by
  obtain ⟨Q, hQ⟩ := comap_localizedMap_surjective f hf q ⟨P, inferInstance⟩
  exact ⟨Q.asIdeal, Q.isPrime, by simpa using congrArg PrimeSpectrum.asIdeal hQ⟩

/-- The corresponding going-down statement for the flat homomorphism `f` itself, which is what
makes the map on spectra surjective: a prime `p' ≤ p = qᶜ` of `A` is the contraction of a prime
`q' ≤ q` of `B`. (That the fibres of `Spec(B_q) → Spec(A_p)` are non-empty is exactly this
statement for all `p' ≤ p`.) -/
theorem exists_isPrime_le_comap_eq (f : A →+* B) (hf : f.Flat) (q : Ideal B) [q.IsPrime]
    (p' : Ideal A) [p'.IsPrime] (hle : p' ≤ q.comap f) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q ≤ q ∧ Q.comap f = p' := by
  let _ : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hf
  have : q.LiesOver (q.comap f) := ⟨rfl⟩
  obtain ⟨Q, hQle, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := A) (S := B) (p := p') (q := q.comap f)
      (Q := q) hle
  exact ⟨Q, hQprime, hQle, by simpa [Ideal.under, RingHom.algebraMap_toAlgebra] using hQover.over.symm⟩

end MainTheorem

section Counterexample

/-- The prime ideal `p = qᶜ ⊆ ℤ` for `q = (0) ⊆ ZMod 2`, i.e. `p = (2)`. -/
abbrev twoIdeal : Ideal ℤ := (⊥ : Ideal (ZMod 2)).comap (Int.castRingHom (ZMod 2))

/-- `ℤ_(2)`: `ℤ` localised at the prime `(2)`. -/
abbrev IntTwo : Type := Localization.AtPrime twoIdeal

/-- In `ℤ_(2)` the element `2/1` is nonzero: `ℤ → ℤ_(2)` is injective because `ℤ` is a domain. -/
lemma twoIdeal_algebraMap_two_ne_zero : algebraMap ℤ IntTwo 2 ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap ℤ IntTwo) :=
    IsLocalization.injective IntTwo (Ideal.primeCompl_le_nonZeroDivisors twoIdeal)
  have h2 : (2 : ℤ) = 0 := hinj (by simpa using h)
  norm_num at h2

/-- Flatness cannot be dropped from Exercise 3.18: for the (non-flat) quotient map
`ℤ →+* ZMod 2`, the prime ideal `q = (0)` of `ZMod 2` and its contraction `p = qᶜ = (2)`, the
induced map `Spec((ZMod 2)_(0)) → Spec(ℤ_(2))` is *not* surjective. Indeed the prime `(0)` of
`ℤ_(2)` would have to be the contraction of a prime of `(ZMod 2)_(0)`, hence would contain the
image `2/1` of `2 ∈ p`, and `2/1 ≠ 0` in `ℤ_(2)`. -/
theorem not_surjective_int_zmod_two :
    ¬ Function.Surjective (PrimeSpectrum.comap
      (localizedMap (Int.castRingHom (ZMod 2)) (⊥ : Ideal (ZMod 2)))) := by
  intro hsurj
  obtain ⟨Q, hQ⟩ := hsurj (⟨⊥, inferInstance⟩ : PrimeSpectrum IntTwo)
  have hcomap : Q.asIdeal.comap (localizedMap (Int.castRingHom (ZMod 2))
      (⊥ : Ideal (ZMod 2))) = ⊥ := by
    simpa using congrArg PrimeSpectrum.asIdeal hQ
  have hmem : algebraMap ℤ IntTwo 2 ∈ (⊥ : Ideal IntTwo) := by
    rw [← hcomap, Ideal.mem_comap, localizedMap_algebraMap]
    have h2 : (Int.castRingHom (ZMod 2)) 2 = (0 : ZMod 2) := by decide
    rw [h2, map_zero]
    exact Submodule.zero_mem _
  exact twoIdeal_algebraMap_two_ne_zero (by simpa using hmem)

/-- `ℤ →+* ZMod 2` is not flat: otherwise Exercise 3.18 (which we proved above) would make
`Spec((ZMod 2)_(0)) → Spec(ℤ_(2))` surjective, contradicting `not_surjective_int_zmod_two`. -/
theorem int_castRingHom_zmod_two_not_flat : ¬ (Int.castRingHom (ZMod 2)).Flat := fun hf ↦
  not_surjective_int_zmod_two (solution _ hf ⊥)

end Counterexample

#print axioms AtiyahMcdonald69.Ex_3_18.solution
#print axioms AtiyahMcdonald69.Ex_3_18.comap_localizedMap_surjective
#print axioms AtiyahMcdonald69.Ex_3_18.solution_algebra
#print axioms AtiyahMcdonald69.Ex_3_18.faithfullyFlat_localizedMap
#print axioms AtiyahMcdonald69.Ex_3_18.exists_isPrime_comap_eq
#print axioms AtiyahMcdonald69.Ex_3_18.exists_isPrime_le_comap_eq
#print axioms AtiyahMcdonald69.Ex_3_18.localizedMap_flat
#print axioms AtiyahMcdonald69.Ex_3_18.flat_tensorProduct_atPrime
#print axioms AtiyahMcdonald69.Ex_3_18.faithfullyFlat_of_flat_of_map_maximalIdeal_ne_top
#print axioms AtiyahMcdonald69.Ex_3_18.localizedMap_unique
#print axioms AtiyahMcdonald69.Ex_3_18.comap_localizedMap_comp
#print axioms AtiyahMcdonald69.Ex_3_18.solution_of_eq
#print axioms AtiyahMcdonald69.Ex_3_18.solution_int_rat
#print axioms AtiyahMcdonald69.Ex_3_18.not_surjective_int_zmod_two
#print axioms AtiyahMcdonald69.Ex_3_18.int_castRingHom_zmod_two_not_flat
#print axioms AtiyahMcdonald69.Ex_3_18.localizedMap_maximalIdeal_comap
#print axioms AtiyahMcdonald69.Ex_3_18.localizedMap_maximalIdeal_le
#print axioms AtiyahMcdonald69.Ex_3_18.localizedMap_maximalIdeal_map_ne_top

end Ex_3_18
end AtiyahMcdonald69
