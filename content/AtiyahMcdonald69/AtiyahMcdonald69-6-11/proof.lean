/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 6 (Chain Conditions), Exercise 6.11.

Book statement (Exercise 6.11):

  "Let `f : A → B` be a ring homomorphism and suppose that `Spec(B)` is Noetherian.
   Prove that `f* : Spec(B) → Spec(A)` is a closed mapping if and only if `f` has the
   going-up property."

Natural-language reference proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-11

Source audit notes.
* The going-up property is the one introduced in Chapter 5 for the going-up theorem: for
  prime ideals `p₁ ≤ p₂` of `A` and a prime `q₁` of `B` with `q₁ ∩ A = p₁`, there is a prime
  `q₂ ⊇ q₁` with `q₂ ∩ A = p₂`.  It is formalised below as `HasGoingUp f`; for an
  `A`-algebra `B` it coincides with Mathlib's `Algebra.HasGoingUp A B`
  (`hasGoingUp_algebraMap_iff`).
* Checked against the book: Chapter 5, Exercise 10 introduces exactly this notion ("A ring
  homomorphism `f : A → B` is said to have the going-up property ... if the conclusion of
  the going-up theorem (5.11) holds for `B` and its subring `f(A)`") and asks for
  "(a) `f*` is a closed mapping ⟺ (b) `f` has the going-up property", adding
  "(See also Chapter 6, Exercise 11.)".  So Exercise 6.11 is the same equivalence
  (restated, and there with `Spec(B)` Noetherian).
* The hypothesis "`Spec(B)` is Noetherian" is part of the book's exercise and is kept in
  the statement `solution` below, verbatim.  The reference proof uses it only implicitly
  (through "every closed subset of `Spec(B)` is a finite union `⋃ V(qᵢ)`", which is
  Exercise 6.7 = "a Noetherian space is a finite union of irreducible closed subspaces"),
  so that argument is complete once the hypothesis is stated: no error, only a hypothesis
  used without being restated.  It is however *not needed*: going-up alone already makes
  `f*` closed, because the image of a closed set is then stable under specialisation
  (this is the unconditional assertion of Exercise 5.10 (a) ⟺ (b)).  The stronger form is
  proved below as `isClosedMap_comap_iff_hasGoingUp`.  So there is no counterexample or
  correction to isolate here: `solution` is the book's exact claim, proved, and the
  hypothesis turns out to be removable rather than necessary.
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.HasGoingUp

open PrimeSpectrum

set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_6_11

variable {A : Type*} {B : Type*} [CommRing A] [CommRing B]

/-- The going-up property of a ring homomorphism `f : A → B` (Atiyah–Macdonald, Chapter 5):
whenever `p₁ ≤ p₂` are prime ideals of `A` and `q₁` is a prime ideal of `B` with
`q₁ ∩ A = p₁` (that is, `q₁.comap f = p₁`), there is a prime ideal `q₂ ⊇ q₁` of `B` with
`q₂ ∩ A = p₂`. -/
def HasGoingUp (f : A →+* B) : Prop :=
  ∀ (p₁ p₂ : Ideal A), p₁.IsPrime → p₂.IsPrime → p₁ ≤ p₂ →
    ∀ (q₁ : Ideal B), q₁.IsPrime → q₁.comap f = p₁ →
      ∃ q₂ : Ideal B, q₂.IsPrime ∧ q₁ ≤ q₂ ∧ q₂.comap f = p₂

/-- `HasGoingUp` rewritten as "specialisations lift along `Spec f`". -/
lemma hasGoingUp_iff_lifts {f : A →+* B} :
    HasGoingUp f ↔ ∀ (p : PrimeSpectrum A) (q : PrimeSpectrum B),
      PrimeSpectrum.comap f q ≤ p →
        ∃ q' : PrimeSpectrum B, q ≤ q' ∧ PrimeSpectrum.comap f q' = p := by
  constructor
  · rintro h p q hpq
    have hp : (PrimeSpectrum.comap f q).asIdeal ≤ p.asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hpq
    obtain ⟨q₂, hq₂, hle, heq⟩ :=
      h (PrimeSpectrum.comap f q).asIdeal p.asIdeal (PrimeSpectrum.comap f q).2 p.2 hp
        q.asIdeal q.2 rfl
    exact ⟨⟨q₂, hq₂⟩, (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle,
      PrimeSpectrum.ext (by rw [PrimeSpectrum.comap_asIdeal]; exact heq)⟩
  · rintro h p₁ p₂ hp₁ hp₂ hle q₁ hq₁ hcomap
    have hle' : PrimeSpectrum.comap f (⟨q₁, hq₁⟩ : PrimeSpectrum B) ≤ ⟨p₂, hp₂⟩ :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
        (by rw [PrimeSpectrum.comap_asIdeal, hcomap]; exact hle)
    obtain ⟨q', hq'ge, hq'eq⟩ := h ⟨p₂, hp₂⟩ ⟨q₁, hq₁⟩ hle'
    refine ⟨q'.asIdeal, q'.2, (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hq'ge, ?_⟩
    rw [← PrimeSpectrum.comap_asIdeal]
    exact congrArg PrimeSpectrum.asIdeal hq'eq

/-- Exercise 6.11, `⇐`: the going-up property makes `f* : Spec B → Spec A` a closed map.
The image of a closed set `Z` is then stable under specialisation, hence closed. -/
theorem isClosedMap_comap_of_hasGoingUp (f : A →+* B) (hgo : HasGoingUp f) :
    IsClosedMap (PrimeSpectrum.comap f) := by
  rw [hasGoingUp_iff_lifts] at hgo
  intro Z hZ
  refine PrimeSpectrum.isClosed_image_of_stableUnderSpecialization f Z hZ ?_
  rintro y y' hyy' hy
  obtain ⟨q, hqZ, rfl⟩ := hy
  obtain ⟨q', hq'ge, hq'eq⟩ :=
    hgo y' q ((PrimeSpectrum.le_iff_specializes (PrimeSpectrum.comap f q) y').mpr hyy')
  exact ⟨q', hZ.stableUnderSpecialization ((PrimeSpectrum.le_iff_specializes q q').mp hq'ge) hqZ,
    hq'eq⟩

/-- Exercise 6.11, `⇒`: if `f* : Spec B → Spec A` is a closed map then `f` has going-up.
The closure of a point `p₁` of `Spec A` is `V(p₁)`, and it is contained in the closed set
`f*(V(q₁))`, which contains `f⁻¹(q₁) = p₁`. -/
theorem hasGoingUp_of_isClosedMap_comap (f : A →+* B)
    (hclosed : IsClosedMap (PrimeSpectrum.comap f)) : HasGoingUp f := by
  rw [hasGoingUp_iff_lifts]
  intro p q hpq
  have himg : IsClosed (PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q.asIdeal : Set B)) :=
    hclosed _ (PrimeSpectrum.isClosed_zeroLocus _)
  have hmem : PrimeSpectrum.comap f q ∈
      PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q.asIdeal : Set B) :=
    ⟨q, by rw [PrimeSpectrum.mem_zeroLocus], rfl⟩
  have hcls : closure ({PrimeSpectrum.comap f q} : Set (PrimeSpectrum A)) ⊆
      PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q.asIdeal : Set B) :=
    himg.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
  have hp : p ∈ closure ({PrimeSpectrum.comap f q} : Set (PrimeSpectrum A)) := by
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hpq
  obtain ⟨q', hq'Z, hq'p⟩ := hcls hp
  refine ⟨q', ?_, hq'p⟩
  rw [PrimeSpectrum.mem_zeroLocus] at hq'Z
  exact (PrimeSpectrum.asIdeal_le_asIdeal q q').mp hq'Z

/-- Exercise 6.11 with the book's hypothesis dropped: it is not needed for the equivalence,
because going-up alone makes the image of every closed set stable under specialisation.
(Kept as a separate theorem; the book's exact statement is `solution` below.) -/
theorem isClosedMap_comap_iff_hasGoingUp (f : A →+* B) :
    IsClosedMap (PrimeSpectrum.comap f) ↔ HasGoingUp f :=
  ⟨hasGoingUp_of_isClosedMap_comap f, isClosedMap_comap_of_hasGoingUp f⟩

/-- **Atiyah–Macdonald, Chapter 6, Exercise 6.11.**  Let `f : A → B` be a ring homomorphism
and suppose that `Spec(B)` is a Noetherian topological space.  Then
`f* : Spec(B) → Spec(A)`, `q ↦ f⁻¹(q)`, is a closed mapping if and only if `f` has the
going-up property. -/
theorem solution (f : A →+* B) [TopologicalSpace.NoetherianSpace (PrimeSpectrum B)] :
    IsClosedMap (PrimeSpectrum.comap f) ↔ HasGoingUp f :=
  isClosedMap_comap_iff_hasGoingUp f

/-- The book's going-up property for `algebraMap A B` is Mathlib's `Algebra.HasGoingUp A B`. -/
lemma hasGoingUp_algebraMap_iff [Algebra A B] :
    HasGoingUp (algebraMap A B) ↔ Algebra.HasGoingUp A B := by
  constructor
  · intro h
    have key : ∀ {q : Ideal A} [q.IsPrime] (P : Ideal B) [P.IsPrime],
        P.under A < q → ∃ Q : Ideal B, P ≤ Q ∧ Q.IsPrime ∧ Q.LiesOver q := by
      intro q hq P hP hlt
      obtain ⟨Q, hQ, hPQ, hQq⟩ :=
        h (P.under A) q (Ideal.IsPrime.under (A := A) (P := P)) hq hlt.le P hP rfl
      exact ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩
    exact ⟨key⟩
  · rintro ⟨h⟩ p₁ p₂ hp₁ hp₂ hle q₁ hq₁ hcomap
    haveI : q₁.LiesOver p₁ := ⟨hcomap.symm⟩
    haveI : q₁.IsPrime := hq₁
    haveI : p₂.IsPrime := hp₂
    haveI : Algebra.HasGoingUp A B := ⟨h⟩
    obtain ⟨Q, hQ₁, hQ₂, hQ₃⟩ :=
      Ideal.exists_ideal_ge_liesOver_of_le (p := p₁) (q := p₂) q₁ hle
    exact ⟨Q, hQ₂, hQ₁, (Q.over_def p₂).symm⟩

/-- Consistency check for the definitions: an integral `R`-algebra `S` has the going-up
property (Mathlib's `Algebra.HasGoingUp` instance), hence `Spec S → Spec R` is a closed map;
this is Chapter 5, Exercise 1, recovered from Exercise 6.11. -/
theorem isClosedMap_comap_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    IsClosedMap (PrimeSpectrum.comap (algebraMap R S)) :=
  (isClosedMap_comap_iff_hasGoingUp (algebraMap R S)).mpr
    ((hasGoingUp_algebraMap_iff (A := R) (B := S)).mpr inferInstance)

end AtiyahMcdonald69.Ex_6_11
