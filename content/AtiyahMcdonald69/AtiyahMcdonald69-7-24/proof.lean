/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 7, Exercise 24.

Public source of the exercise and its natural-language proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-24
(source commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91)

Statement (as recovered from the source `proof.tex` and from the textbook):

  Let `A` be a Noetherian ring and let `f : A → B` be a ring homomorphism of finite type.
  Then the induced map `f^* : Spec B → Spec A` is an open mapping (i.e. sends open sets to
  open sets) if and only if `f` has the going-down property
  (for primes `p ≤ p'` of `A` and a prime `q'` of `B` over `p'` there is a prime `q ≤ q'` of `B`
  over `p`).

Mathlib rendering of the data:
* the ring homomorphism `f : A → B` is `algebraMap A B` of an `Algebra A B` structure,
* `f` is of finite type is `Algebra.FiniteType A B`,
* `f` has going-down is `Algebra.HasGoingDown A B`
  (its field `exists_ideal_le_liesOver_of_lt` is literally the going-down property),
* `f^*` is `PrimeSpectrum.comap (algebraMap A B)`, and "open mapping" is `IsOpenMap`.

Proof structure (the source `proof.tex` proceeds by 7.23 (Chevalley: the image is constructible),
7.20, 7.22 and 5.10(ii); the formal proof below is organised differently but proves the same
proposition):

* `⇐` ("going down ⟹ open") is Chevalley's theorem in the form
  `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` (Stacks 00I1): an open
  map is a constructible map that lifts generalizations.  It is stated for finitely *presented*
  algebras; over a Noetherian ring finite type implies finite presentation, which is exactly
  where the Noetherian hypothesis of the exercise is used.
* `⇒` ("open ⟹ going down") needs no Noetherian or finite type hypothesis and is proved here
  from scratch.  If `p ≤ p' = q' ∩ A` are primes, openness says that for every basic open
  `D(g) ∋ q'` the image `f^*(D(g))` is an open set containing `p'`, hence it contains the
  generization `p` of `p'`; so for every `g ∉ q'` there is a prime `P` of `B` over `p` with
  `g ∉ P`.  A prime avoidance argument (`Ideal.exists_le_prime_disjoint`) applied to the ideal
  `p·B` and the submonoid of products of elements of `A ∖ p` with elements of `B ∖ q'` then
  yields a prime `P ≤ q'` over `p`.
-/

import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.FinitePresentation

open PrimeSpectrum

namespace AtiyahMcdonald69.Ex_7_24

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-! ### The going-down direction

If `Spec B → Spec A` is open, then `A → B` has going down. -/

/-- Openness of `f^*` produces, for every basic open neighbourhood `D(g)` of a prime `Q` of `B`,
a prime `P` of `B` over `p` that meets `D(g)`, i.e. with `g ∉ P`.

This is the pointwise form of "the image of the open map `f^*` is closed under generization". -/
theorem exists_isPrime_under_eq_and_notMem_of_isOpenMap
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)))
    {p : Ideal A} [p.IsPrime] {Q : Ideal B} [Q.IsPrime] (hpQ : p ≤ Q.under A)
    {g : B} (hg : g ∉ Q) :
    ∃ P : Ideal B, P.IsPrime ∧ P.under A = p ∧ g ∉ P := by
  have hq : (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen g := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact hg
  have hle : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) ≤
      PrimeSpectrum.comap (algebraMap A B) ⟨Q, ‹Q.IsPrime›⟩ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    simpa using hpQ
  have hspec : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) ⤳
      PrimeSpectrum.comap (algebraMap A B) ⟨Q, ‹Q.IsPrime›⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have hmem : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) ∈
      PrimeSpectrum.comap (algebraMap A B) '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) :=
    hspec.mem_open (hopen _ (PrimeSpectrum.basicOpen g).isOpen)
      ⟨⟨Q, ‹Q.IsPrime›⟩, hq, rfl⟩
  obtain ⟨q, hqg, hqeq⟩ := hmem
  refine ⟨q.asIdeal, q.2, ?_, ?_⟩
  · have h := congrArg PrimeSpectrum.asIdeal hqeq
    simpa using h
  · exact (PrimeSpectrum.mem_basicOpen g q).mp hqg

/-- Prime avoidance step: if every element of `B ∖ Q` is avoided by some prime of `B` lying over
`p`, then some prime of `B` lying over `p` is contained in `Q`. -/
theorem exists_isPrime_le_and_under_eq (p : Ideal A) [p.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (H : ∀ g : B, g ∉ Q → ∃ P : Ideal B, P.IsPrime ∧ P.under A = p ∧ g ∉ P) :
    ∃ P : Ideal B, P.IsPrime ∧ P ≤ Q ∧ P.under A = p := by
  classical
  have h1Q : (1 : B) ∉ Q := by
    intro h
    exact ‹Q.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem Q h isUnit_one)
  -- `H` at `1` provides a prime over `p`, so `p` is the contraction of its extension.
  obtain ⟨P₀, hP₀prime, hP₀under, -⟩ := H 1 h1Q
  have hcomap : (p.map (algebraMap A B)).comap (algebraMap A B) = p :=
    (Ideal.comap_map_eq_self_iff_of_isPrime p).mpr ⟨P₀, hP₀prime, hP₀under⟩
  -- The multiplicative set to avoid: products of images of elements outside `p` with elements
  -- outside `Q`.
  have hdisj : Disjoint ((p.map (algebraMap A B) : Ideal B) : Set B)
      (((p.primeCompl.map (algebraMap A B)) ⊔ Q.primeCompl : Submonoid B) : Set B) := by
    rw [Set.disjoint_left]
    intro x hxI hxS
    obtain ⟨s₁, hs₁, s₂, hs₂, hx⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨a, ha, haeq⟩ := Submonoid.mem_map.mp hs₁
    rw [Ideal.mem_primeCompl_iff] at ha hs₂
    have hx' : algebraMap A B a * s₂ ∈ p.map (algebraMap A B) := by
      rw [haeq, hx]; exact hxI
    obtain ⟨P', hP'prime, hP'under, hs₂P'⟩ := H s₂ hs₂
    have hle : p.map (algebraMap A B) ≤ P' := by
      rw [Ideal.map_le_iff_le_comap]
      exact hP'under.ge
    have hmem : algebraMap A B a * s₂ ∈ P' := hle hx'
    have hnot : algebraMap A B a ∉ P' := by
      intro hcon
      have hmem : a ∈ P'.under A := hcon
      rw [hP'under] at hmem
      exact ha hmem
    rcases hP'prime.mem_or_mem hmem with h | h
    · exact hnot h
    · exact hs₂P' h
  obtain ⟨P, hPprime, hIP, hdisjP⟩ :=
    Ideal.exists_le_prime_disjoint (p.map (algebraMap A B))
      ((p.primeCompl.map (algebraMap A B)) ⊔ Q.primeCompl) hdisj
  refine ⟨P, hPprime, ?_, ?_⟩
  · -- `P ≤ Q` since `P` avoids `B ∖ Q`
    intro x hxP
    by_contra hxQ
    have hxS : x ∈ ((p.primeCompl.map (algebraMap A B)) ⊔ Q.primeCompl : Submonoid B) :=
      Submonoid.mem_sup_right (by rwa [Ideal.mem_primeCompl_iff])
    exact (Set.disjoint_left.mp hdisjP hxP) hxS
  · -- `P` lies over `p`
    refine le_antisymm ?_ ?_
    · have hd : Disjoint (P : Set B)
          (((p.primeCompl.map (algebraMap A B) : Submonoid B)) : Set B) :=
        hdisjP.mono_right (by
          intro x hx
          exact Submonoid.mem_sup_left hx)
      have := (Ideal.disjoint_map_primeCompl_iff_comap_le (f := algebraMap A B) (p := p)
        (I := P)).mp hd
      simpa using this
    · rw [Ideal.map_le_iff_le_comap] at hIP
      exact hIP

/-- If `f^* : Spec B → Spec A` is an open mapping, then `f` has the going-down property. -/
theorem hasGoingDown_of_isOpenMap
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap A B))) :
    Algebra.HasGoingDown A B where
  exists_ideal_le_liesOver_of_lt := by
    rintro p hp Q hQ hlt
    obtain ⟨P, hP, hPQ, hunder⟩ :=
      exists_isPrime_le_and_under_eq p Q
        (fun g hg => exists_isPrime_under_eq_and_notMem_of_isOpenMap hopen hlt.le hg)
    exact ⟨P, hPQ, hP, ⟨hunder.symm⟩⟩

/-! ### Atiyah–Macdonald, Exercise 7.24 -/

/-- **Atiyah–Macdonald, Exercise 7.24.** Let `A` be a Noetherian ring and let `f : A → B` be a
ring homomorphism of finite type (rendered as `algebraMap A B` for an `Algebra A B` structure with
`Algebra.FiniteType A B`). Then `f^* : Spec B → Spec A` is an open mapping if and only if `f` has
the going-down property.

Public statement and natural-language proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-24 -/
theorem solution (A B : Type*) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A B)) ↔ Algebra.HasGoingDown A B := by
  have hfp : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨hasGoingDown_of_isOpenMap,
    fun h => @PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation A B _ _ _ h hfp⟩


/-! ### The exercise stated for a ring homomorphism

The textbook states the result for a ring homomorphism `f : A → B`.  Below the going-down
property is spelled out literally as in Atiyah–Macdonald. -/

section RingHomVersion

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Atiyah–Macdonald's going-down property for a ring homomorphism `f : A → B`: for primes
`p ≤ p'` of `A` and a prime `Q` of `B` lying over `p'`, there is a prime `P ≤ Q` of `B` lying
over `p`. -/
def IsGoingDown (f : A →+* B) : Prop :=
  ∀ (p p' : Ideal A), p.IsPrime → p'.IsPrime → p ≤ p' → ∀ (Q : Ideal B), Q.IsPrime →
    Q.comap f = p' → ∃ P : Ideal B, P.IsPrime ∧ P ≤ Q ∧ P.comap f = p

set_option linter.style.haveILetI false in
/-- For the algebra structure attached to a ring homomorphism, this is Mathlib's going-down
property for algebras. -/
theorem isGoingDown_iff_hasGoingDown (f : A →+* B) :
    IsGoingDown f ↔ @Algebra.HasGoingDown A B _ _ f.toAlgebra := by
  letI : Algebra A B := f.toAlgebra
  have hmap : (algebraMap A B : A →+* B) = f := RingHom.algebraMap_toAlgebra f
  constructor
  · rintro H
    refine ⟨fun {p} hp Q hQ hlt => ?_⟩
    obtain ⟨P, hP, hPQ, hPcomap⟩ :=
      H p (Q.under A) hp (Ideal.IsPrime.under A Q) hlt.le Q hQ (by rw [Ideal.under_def, hmap])
    exact ⟨P, hPQ, hP, ⟨hPcomap.symm⟩⟩
  · intro Hinst p p' hp hp' hle Q hQ hQeq
    letI : Algebra.HasGoingDown A B := Hinst
    have hunder : Q.under A = p' := by rw [Ideal.under_def, hmap]; exact hQeq
    letI : Q.LiesOver p' := ⟨hunder.symm⟩
    obtain ⟨P, hPQ, hP, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := p') Q hle
    exact ⟨P, hP, hPQ, by rw [← hmap]; exact hlies.over.symm⟩

/-- **Atiyah–Macdonald, Exercise 7.24**, stated literally for a ring homomorphism:
if `A` is Noetherian and `f : A → B` is of finite type, then `f^* : Spec B → Spec A` is an
open mapping if and only if `f` has the going-down property.

https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-24 -/
theorem solution_ringHom (f : A →+* B) [IsNoetherianRing A] (hf : f.FiniteType) :
    IsOpenMap (PrimeSpectrum.comap f) ↔ IsGoingDown f := by
  have hmap : @algebraMap A B _ _ f.toAlgebra = f := RingHom.algebraMap_toAlgebra f
  rw [isGoingDown_iff_hasGoingDown, ← hmap]
  exact @solution A B _ _ _ f.toAlgebra hf

end RingHomVersion

end AtiyahMcdonald69.Ex_7_24

/-! ### Verification

The two public forms of the exercise, and their axiom footprint (no `sorryAx`, no new axioms). -/

#print axioms AtiyahMcdonald69.Ex_7_24.solution
#print axioms AtiyahMcdonald69.Ex_7_24.solution_ringHom
