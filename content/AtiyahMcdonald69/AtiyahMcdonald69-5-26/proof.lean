import Mathlib

set_option autoImplicit false

/-!
# Atiyah–Macdonald (1969), Chapter 5, Exercise 26

The exercise (page 71 of the book) reads:

> Let `X` be a topological space. A subset of `X` is *locally closed* if it is the intersection of
> an open set and a closed set, or equivalently if it is open in its closure.
>
> Show that the three conditions below on a subset `X₀` of `X` are equivalent:
> (1) every non-empty locally closed subset of `X` meets `X₀`;
> (2) for every closed set `Z` in `X` we have `closure (X₀ ∩ Z) = Z`;
> (3) the mapping `U ↦ U ∩ X₀` of the collection of open sets of `X` onto the collection of open
> sets of `X₀` is bijective.
>
> A subset `X₀` satisfying these conditions is said to be *very dense* in `X`.
>
> If `A` is a ring, show that the following are equivalent:
> (i) `A` is a Jacobson ring;
> (ii) the set of maximal ideals of `A` is very dense in `Spec A`;
> (iii) every locally closed subset of `Spec A` consisting of a single point is closed.

## Contents of this file

Topological part:
* `IsLocallyClosedSet` — the book's definition, and
  `isLocallyClosedSet_iff_exists_open_inter_closure` — the book's equivalent description;
* `VeryDenseCond1`, `VeryDenseCond2`, `VeryDenseCond3` — the three conditions (3 is stated both as
  a bijection onto the relatively open subsets of `X₀`, `VeryDenseCond3`, and literally as a
  bijection onto the open sets of the subspace `X₀`, `openRestrictionSubtype`;
  `veryDenseCond3_iff_bijective_openRestrictionSubtype`);
* `veryDense_tfae` — the equivalence of (1), (2) and (3);
* `VeryDense` — the book's notion, defined by condition (2).

Algebraic part, following the natural solution (which uses Exercise 5.23 for the notion of a
Jacobson ring):
* `maxPoints` — the set of maximal ideals of `A` as a subset of `Spec A`, and
  `maxPoints_eq_closedPoints` — it is the set of closed points;
* `vanishingIdeal_maxPoints_inter_zeroLocus`, `closure_maxPoints_inter_zeroLocus` — the closure of
  the maximal ideals containing `I` is `V (jacobson I)` (the book's computation of
  `closure (V(I) ∩ Max(A))`, i.e. "every quotient has equal Jacobson radical and nilradical");
* `isJacobsonRing_iff_veryDense_maxPoints` — (i) `⟺` (ii);
* `primeEqSInfLargerPrimes_of_isJacobsonRing` — (i) `⟹` 5.23 (iii);
  `exists_prime_ge_max_notMem_powers`, `exists_isMaximal_ge_notMem_of_primeEqSInfLargerPrimes`,
  `isJacobsonRing_of_primeEqSInfLargerPrimes` — the hard direction 5.23 (iii) `⟹` (i), including
  the Zorn/maximality argument;
* `exists_basicOpen_of_isLocallyClosedSet_singleton` — a locally closed singleton `{p}` is of the
  form `V(p) ∩ D(f)` with `f ∉ p`;
* `primeEqSInfLargerPrimes_of_locallyClosedSingletonsClosed`,
  `locallyClosedSingletonsClosed_of_isJacobsonRing` — (iii) `⟺` (i);
* `jacobson_tfae` — the equivalence of (i), (ii) and (iii).

`A` is a *Jacobson ring* in the sense of the book (Exercise 5.23): a ring in which every prime
ideal is an intersection of maximal ideals.  Mathlib's class `IsJacobsonRing` is defined by the
equivalent condition that every radical ideal equals its Jacobson radical;
`isJacobsonRing_iff_prime_eq_sInf_maximal` records the book's form.

Only `Mathlib` is imported; the file contains no `sorry`, `admit`, or new axioms, and the main
results depend only on `propext`, `Classical.choice` and `Quot.sound` (see the end of the file).

The statement was checked against the book's own text (page 71) and the argument follows the
natural solution published for exercise 5.26 by *Do Your Exercise* (which uses Exercise 5.23 for
the notion of a Jacobson ring); the pieces of 5.23 that the solution cites are proved here, because
files of this project may not import one another.
-/

namespace AtiyahMcdonald69.Ex_5_26

open Topology

section Prelim

variable {X : Type*}

/-- Two subsets of `X` have the same trace on `X₀` iff their preimages in the subtype `X₀` agree. -/
theorem preimage_subtype_val_eq_iff (X₀ : Set X) (U V : Set X) :
    (Subtype.val : X₀ → X) ⁻¹' U = (Subtype.val : X₀ → X) ⁻¹' V ↔ X₀ ∩ U = X₀ ∩ V := by
  constructor
  · intro h
    ext x
    by_cases hx : x ∈ X₀
    · have hx' := congrArg (fun s : Set X₀ => (⟨x, hx⟩ : X₀) ∈ s) h
      have hx'' : (x ∈ U ↔ x ∈ V) := by simpa using hx'
      simpa only [Set.mem_inter_iff, hx, true_and] using hx''
    · simp [Set.mem_inter_iff, hx]
  · intro h
    ext x
    have hx' := congrArg (fun s : Set X => (x : X) ∈ s) h
    simpa [x.2] using hx'

end Prelim

section Topological

variable {X : Type*} [TopologicalSpace X]

/-- Atiyah–Macdonald, Chapter 5, Exercise 26: a subset of a topological space is *locally closed*
if it is the intersection of an open set and a closed set. -/
def IsLocallyClosedSet (S : Set X) : Prop := ∃ U C : Set X, IsOpen U ∧ IsClosed C ∧ S = U ∩ C

/-- The book's equivalent description of a locally closed set: it is open in its closure. -/
theorem isLocallyClosedSet_iff_exists_open_inter_closure (S : Set X) :
    IsLocallyClosedSet S ↔ ∃ U : Set X, IsOpen U ∧ S = U ∩ closure S := by
  constructor
  · rintro ⟨U, C, hU, hC, hS⟩
    refine ⟨U, hU, ?_⟩
    subst hS
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      exact ⟨hx.1, subset_closure hx⟩
    · rintro x ⟨hxU, hx⟩
      have hsub : closure (U ∩ C) ⊆ C := hC.closure_subset_iff.mpr Set.inter_subset_right
      exact ⟨hxU, hsub hx⟩
  · rintro ⟨U, hU, hS⟩
    exact ⟨U, closure S, hU, isClosed_closure, hS⟩

/-- Condition (1) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
def VeryDenseCond1 (X₀ : Set X) : Prop :=
  ∀ S : Set X, IsLocallyClosedSet S → S.Nonempty → (S ∩ X₀).Nonempty

/-- Condition (2) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
def VeryDenseCond2 (X₀ : Set X) : Prop :=
  ∀ Z : Set X, IsClosed Z → closure (X₀ ∩ Z) = Z

/-- The open sets of the subspace `X₀`, as subsets of `X` that are traces of open sets. -/
def relativelyOpen (X₀ : Set X) : Set (Set X) :=
  { V | V ⊆ X₀ ∧ ∃ U : Set X, IsOpen U ∧ V = X₀ ∩ U }

/-- The map `U ↦ U ∩ X₀` from the open sets of `X` to the relatively open subsets of `X₀`. -/
def openRestriction (X₀ : Set X) (U : {U : Set X // IsOpen U}) :
    {V : Set X // V ∈ relativelyOpen X₀} :=
  ⟨X₀ ∩ U.1, ⟨Set.inter_subset_left, U.1, U.2, rfl⟩⟩

/-- Condition (3) of Atiyah–Macdonald, Chapter 5, Exercise 26: `U ↦ U ∩ X₀` is a bijection from
the open sets of `X` onto the collection of open sets of `X₀`. -/
def VeryDenseCond3 (X₀ : Set X) : Prop := Function.Bijective (openRestriction X₀)

/-- The map `U ↦ U ∩ X₀`, now regarded as a map from the open sets of `X` to the open subsets of
the subspace `X₀` (the literal formulation of condition (3) in the book). -/
def openRestrictionSubtype (X₀ : Set X) (U : {U : Set X // IsOpen U}) :
    {V : Set X₀ // IsOpen V} :=
  ⟨Subtype.val ⁻¹' U.1, U.2.preimage continuous_subtype_val⟩

/-- Condition (3) is equivalent to its literal book formulation, with the open sets of `X` mapped
bijectively onto the open sets of the subspace `X₀`. -/
theorem veryDenseCond3_iff_bijective_openRestrictionSubtype (X₀ : Set X) :
    Function.Bijective (openRestrictionSubtype X₀) ↔ VeryDenseCond3 X₀ := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · rintro ⟨U, hU⟩ ⟨V, hV⟩ hUV
      have hpre : (Subtype.val : X₀ → X) ⁻¹' U = (Subtype.val : X₀ → X) ⁻¹' V := by
        rw [preimage_subtype_val_eq_iff]
        exact congrArg Subtype.val hUV
      have hEq : openRestrictionSubtype X₀ ⟨U, hU⟩ = openRestrictionSubtype X₀ ⟨V, hV⟩ :=
        Subtype.ext hpre
      exact Subtype.ext (by simpa using congrArg Subtype.val (hinj hEq))
    · rintro ⟨W, hWsub, U, hU, hWU⟩
      exact ⟨⟨U, hU⟩, Subtype.ext hWU.symm⟩
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro U V hUV
      have hpre : (Subtype.val : X₀ → X) ⁻¹' U.1 = (Subtype.val : X₀ → X) ⁻¹' V.1 :=
        congrArg Subtype.val hUV
      have hinter : X₀ ∩ U.1 = X₀ ∩ V.1 := (preimage_subtype_val_eq_iff X₀ U.1 V.1).mp hpre
      exact Subtype.ext (by simpa using congrArg Subtype.val (hinj (Subtype.ext hinter)))
    · intro V
      obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp V.2
      exact ⟨⟨U, hU⟩, Subtype.ext hUV⟩

/-- `X₀` is *very dense* in `X`: the second of the three equivalent conditions of
Atiyah–Macdonald, Chapter 5, Exercise 26. -/
def VeryDense (X₀ : Set X) : Prop := VeryDenseCond2 X₀

theorem veryDenseCond1_iff_veryDenseCond2 (X₀ : Set X) :
    VeryDenseCond1 X₀ ↔ VeryDenseCond2 X₀ := by
  constructor
  · intro H Z hZ
    refine Set.Subset.antisymm ?_ ?_
    · exact hZ.closure_subset_iff.mpr Set.inter_subset_right
    · intro x hxZ
      rw [mem_closure_iff]
      intro U hU hxU
      have hne : (U ∩ Z).Nonempty := ⟨x, hxU, hxZ⟩
      have hmem := H (U ∩ Z) ⟨U, Z, hU, hZ, rfl⟩ hne
      have heq : (U ∩ Z) ∩ X₀ = U ∩ (X₀ ∩ Z) := by
        ext z
        simp only [Set.mem_inter_iff]
        tauto
      rwa [heq] at hmem
  · rintro H S ⟨U, C, hU, hC, hS⟩ hne
    by_contra hcon
    have hdisj : S ∩ X₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
    have hsub : X₀ ∩ C ⊆ Uᶜ := by
      rintro x ⟨hxX, hxC⟩ hxU
      have hmem : x ∈ S ∩ X₀ := by
        rw [hS]
        exact ⟨⟨hxU, hxC⟩, hxX⟩
      rw [hdisj] at hmem
      exact hmem
    have hEq : X₀ ∩ C = X₀ ∩ (C ∩ Uᶜ) := by
      apply Set.Subset.antisymm
      · intro x hx
        exact ⟨hx.1, hx.2, hsub hx⟩
      · intro x hx
        exact ⟨hx.1, hx.2.1⟩
    have h1 : closure (X₀ ∩ C) = C := H C hC
    have h2 : closure (X₀ ∩ (C ∩ Uᶜ)) = C ∩ Uᶜ := H (C ∩ Uᶜ) (hC.inter hU.isClosed_compl)
    have hCU : C = C ∩ Uᶜ := by
      calc C = closure (X₀ ∩ C) := h1.symm
        _ = closure (X₀ ∩ (C ∩ Uᶜ)) := by rw [hEq]
        _ = C ∩ Uᶜ := h2
    have hSU : S = ∅ := by
      rw [hS, hCU, Set.inter_comm C Uᶜ, ← Set.inter_assoc, Set.inter_compl_self,
        Set.empty_inter]
    rw [hSU] at hne
    exact Set.not_nonempty_empty hne

theorem veryDenseCond2_iff_veryDenseCond3 (X₀ : Set X) :
    VeryDenseCond2 X₀ ↔ VeryDenseCond3 X₀ := by
  constructor
  · intro H
    constructor
    · -- injectivity
      intro U V hUV
      have hiff : ∀ x ∈ X₀, (x ∈ U.1 ↔ x ∈ V.1) := by
        intro x hx
        have h := congrArg (fun W : {W : Set X // W ∈ relativelyOpen X₀} => x ∈ W.1) hUV
        have h' : x ∈ (openRestriction X₀ U).1 ↔ x ∈ (openRestriction X₀ V).1 := by
          rw [hUV]
        simpa only [openRestriction, Set.mem_inter_iff, hx, true_and] using h'
      have hcompl : X₀ ∩ U.1ᶜ = X₀ ∩ V.1ᶜ := by
        ext x
        constructor
        · rintro ⟨hx, hxU⟩
          exact ⟨hx, fun hxV => hxU ((hiff x hx).mpr hxV)⟩
        · rintro ⟨hx, hxV⟩
          exact ⟨hx, fun hxU => hxV ((hiff x hx).mp hxU)⟩
      have e1 : closure (X₀ ∩ U.1ᶜ) = U.1ᶜ := H U.1ᶜ U.2.isClosed_compl
      have e2 : closure (X₀ ∩ V.1ᶜ) = V.1ᶜ := H V.1ᶜ V.2.isClosed_compl
      have hc : U.1ᶜ = V.1ᶜ := by rw [← e1, ← e2, hcompl]
      exact Subtype.ext (by simpa using congrArg compl hc)
    · -- surjectivity: restriction of an open set is open in `X₀` by definition
      rintro ⟨V, ⟨hVsub, U, hU, rfl⟩⟩
      exact ⟨⟨U, hU⟩, rfl⟩
  · intro h3
    have h1 : VeryDenseCond1 X₀ := by
      rintro S ⟨U, C, hU, hC, hS⟩ hne
      by_contra hcon
      have hdisj : S ∩ X₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
      have hsub : X₀ ∩ U ⊆ Cᶜ := by
        rintro x ⟨hxX, hxU⟩ hxC
        have hmem : x ∈ S ∩ X₀ := by
          rw [hS]
          exact ⟨⟨hxU, hxC⟩, hxX⟩
        rw [hdisj] at hmem
        exact hmem
      have hEq : X₀ ∩ U = X₀ ∩ (U ∩ Cᶜ) := by
        apply Set.Subset.antisymm
        · intro x hx
          exact ⟨hx.1, hx.2, hsub hx⟩
        · intro x hx
          exact ⟨hx.1, hx.2.1⟩
      have hU' : IsOpen (U ∩ Cᶜ) := hU.inter hC.isOpen_compl
      have hEq' : openRestriction X₀ ⟨U, hU⟩ = openRestriction X₀ ⟨U ∩ Cᶜ, hU'⟩ := by
        simp only [openRestriction]
        exact Subtype.ext hEq
      have hinj := h3.1
      have hthis := hinj hEq'
      have hUC : U = U ∩ Cᶜ := by simpa using congrArg Subtype.val hthis
      have hSU : S = ∅ := by
        rw [hS, hUC, Set.inter_assoc, Set.inter_comm Cᶜ C, Set.inter_compl_self,
          Set.inter_empty]
      rw [hSU] at hne
      exact Set.not_nonempty_empty hne
    exact (veryDenseCond1_iff_veryDenseCond2 X₀).mp h1

/-- Atiyah–Macdonald, Chapter 5, Exercise 26, first part: the three conditions characterizing a
very dense subset are equivalent. -/
theorem veryDense_tfae (X₀ : Set X) :
    (VeryDenseCond1 X₀ ↔ VeryDenseCond2 X₀) ∧ (VeryDenseCond2 X₀ ↔ VeryDenseCond3 X₀) :=
  ⟨veryDenseCond1_iff_veryDenseCond2 X₀, veryDenseCond2_iff_veryDenseCond3 X₀⟩



section Ring

variable {A : Type*} [CommRing A]

/-- The set of maximal ideals of `A`, viewed as points of the prime spectrum. -/
def maxPoints (A : Type*) [CommRing A] : Set (PrimeSpectrum A) := {p | p.asIdeal.IsMaximal}

theorem maxPoints_eq_closedPoints : maxPoints A = closedPoints (PrimeSpectrum A) := by
  ext p
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).symm

/-- The vanishing ideal of the set of maximal ideals containing `I` is the Jacobson radical. -/
theorem vanishingIdeal_maxPoints_inter_zeroLocus (I : Ideal A) :
    PrimeSpectrum.vanishingIdeal (maxPoints A ∩ PrimeSpectrum.zeroLocus I) = I.jacobson := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨hmI, hmmax⟩
    rw [PrimeSpectrum.mem_vanishingIdeal] at hf
    have hmax' : Ideal.IsMaximal m := hmmax
    have hI' : I ≤ m := hmI
    exact hf ⟨m, hmmax.isPrime⟩ ⟨hmax', hI'⟩
  · intro f hf
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro p ⟨hpI, hpmax⟩
    rw [Ideal.jacobson, Submodule.mem_sInf] at hf
    have hmax' : p.asIdeal.IsMaximal := hpI
    have hI' : I ≤ p.asIdeal := hpmax
    exact hf p.asIdeal ⟨hI', hmax'⟩

/-- The closure of the set of maximal ideals containing `I` is the zero locus of the Jacobson
radical of `I`. -/
theorem closure_maxPoints_inter_zeroLocus (I : Ideal A) :
    closure (maxPoints A ∩ PrimeSpectrum.zeroLocus I) =
      PrimeSpectrum.zeroLocus (I.jacobson) := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_maxPoints_inter_zeroLocus]

/-- (i) `⟺` (ii) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
theorem isJacobsonRing_iff_veryDense_maxPoints :
    IsJacobsonRing A ↔ VeryDense (maxPoints A) := by
  constructor
  · intro hA Z hZ
    obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
    rw [closure_maxPoints_inter_zeroLocus, ← Ideal.radical_eq_jacobson, PrimeSpectrum.zeroLocus_radical]
  · intro hVD
    refine isJacobsonRing_iff_prime_eq.mpr fun P hP => ?_
    have h := hVD (PrimeSpectrum.zeroLocus P) (PrimeSpectrum.isClosed_zeroLocus (P : Set A))
    rw [closure_maxPoints_inter_zeroLocus] at h
    have hrad : (P.jacobson).radical = P.radical := PrimeSpectrum.zeroLocus_eq_iff.mp h
    rw [Ideal.IsRadical.radical (Ideal.isRadical_jacobson P), hP.radical] at hrad
    exact hrad

/-- Condition (iii) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
def LocallyClosedSingletonsClosed (A : Type*) [CommRing A] : Prop :=
  ∀ p : PrimeSpectrum A, IsLocallyClosedSet ({p} : Set (PrimeSpectrum A)) →
    IsClosed ({p} : Set (PrimeSpectrum A))

/-- A locally closed singleton in the spectrum is cut out by a single function `f ∉ p`. -/
theorem exists_basicOpen_of_isLocallyClosedSet_singleton {p : PrimeSpectrum A}
    (hp : IsLocallyClosedSet ({p} : Set (PrimeSpectrum A))) :
    ∃ f : A, f ∉ p.asIdeal ∧
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.basicOpen f = {p} := by
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := hp
  have hpUZ : p ∈ U ∩ Z := by rw [← hUZ]; exact rfl
  obtain ⟨B, hB, hpB, hBU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpUZ.1 hU
  obtain ⟨f, rfl⟩ := hB
  have hfp : f ∉ p.asIdeal := by simpa using hpB
  refine ⟨f, hfp, ?_⟩
  have hsubZ : ({p} : Set (PrimeSpectrum A)) ⊆ Z := hUZ ▸ Set.inter_subset_right
  refine Set.Subset.antisymm ?_ ?_
  · rintro q ⟨hq, hqf⟩
    have hqZ : q ∈ Z := by
      refine hZ.closure_subset_iff.mpr hsubZ ?_
      rw [PrimeSpectrum.closure_singleton]
      exact hq
    have hqU : q ∈ U := hBU hqf
    have hmem : q ∈ U ∩ Z := ⟨hqU, hqZ⟩
    rw [← hUZ] at hmem
    simpa using hmem
  · intro q hq
    have hqp : q = p := by simpa using hq
    subst hqp
    exact ⟨by simp, hpB⟩



/-! ## Book Exercise 5.23 (iii): non-maximal primes as intersections of the larger primes -/

/-- Book condition 5.23 (iii), used in Exercise 5.26: every non-maximal prime ideal is the
intersection of the prime ideals strictly containing it. -/
def PrimeEqSInfLargerPrimes (A : Type*) [CommRing A] : Prop :=
  ∀ p : Ideal A, p.IsPrime → ¬ p.IsMaximal → p = sInf {q : Ideal A | q.IsPrime ∧ p < q}

/-- A Jacobson ring satisfies 5.23 (iii): a prime ideal that is not maximal is the intersection of
the prime ideals strictly containing it. -/
theorem primeEqSInfLargerPrimes_of_isJacobsonRing [IsJacobsonRing A] :
    PrimeEqSInfLargerPrimes A := by
  intro p hp hmax
  refine le_antisymm ?_ ?_
  · exact le_sInf fun q hq => le_of_lt hq.2
  · have h1 : sInf {q : Ideal A | q.IsPrime ∧ p < q} ≤ p.jacobson := by
      rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro m ⟨hmle, hmmax⟩
      refine sInf_le ⟨hmmax.isPrime, ?_⟩
      exact lt_of_le_of_ne hmle (fun h => hmax (h ▸ hmmax))
    rwa [isJacobsonRing_iff_prime_eq.mp ‹IsJacobsonRing A› p hp] at h1

/-- Given a prime ideal `p` and an element `x ∉ p`, there is a prime ideal `q ⊇ p` containing no
power of `x` that is maximal with this property: every prime ideal strictly containing `q` contains
`x`.  (Zorn's lemma, applied to the ideals disjoint from the multiplicative set of powers of `x`.) -/
theorem exists_prime_ge_max_notMem_powers {p : Ideal A} (hp : p.IsPrime) {x : A} (hx : x ∉ p) :
    ∃ q : Ideal A, p ≤ q ∧ q.IsPrime ∧ x ∉ q ∧ ∀ r : Ideal A, q < r → r.IsPrime → x ∈ r := by
  classical
  have hpT : p ∈ {q : Ideal A | Disjoint (q : Set A) ((Submonoid.powers x : Submonoid A) : Set A)} := by
    refine Set.disjoint_left.mpr ?_
    rintro a ha hpows
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a x).mp hpows
    rw [← hn] at ha
    exact hx (hp.mem_of_pow_mem n ha)
  have hchain : ∀ c ⊆ {q : Ideal A |
        Disjoint (q : Set A) ((Submonoid.powers x : Submonoid A) : Set A)},
      IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {q : Ideal A |
        Disjoint (q : Set A) ((Submonoid.powers x : Submonoid A) : Set A)}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchainc y hy
    rcases c.eq_empty_or_nonempty with hc0 | ⟨y₀, hy₀⟩
    · exact ⟨p, hpT, fun z hz => absurd hz (by simp [hc0])⟩
    · have hne : Nonempty c := ⟨⟨y₀, hy₀⟩⟩
      refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      refine Set.disjoint_left.mpr fun a ha hpows => ?_
      have hdir : DirectedOn (· ≤ ·) c := by
        intro x hx y hy
        rcases hchainc.total hx hy with h | h
        · exact ⟨y, hy, h, le_rfl⟩
        · exact ⟨x, hx, le_rfl, h⟩
      obtain ⟨z, hzc, hz⟩ :=
        (Submodule.mem_sSup_of_directed ⟨y₀, hy₀⟩ hdir).mp ha
      exact Set.disjoint_left.mp (hc hzc) hz hpows
  obtain ⟨q, hpq, hqmax⟩ := zorn_le_nonempty₀ _ hchain p hpT
  have hqdisj : Disjoint (q : Set A) ((Submonoid.powers x : Submonoid A) : Set A) := hqmax.1
  have hprime : q.IsPrime := by
    refine Ideal.isPrime_of_maximally_disjoint q (Submonoid.powers x) hqdisj ?_
    intro r hr hdisj
    have hle : r ≤ q := hqmax.2 hdisj (le_of_lt hr)
    exact absurd hr (not_lt_of_ge hle)
  have hxq : x ∉ q := fun hxq =>
    Set.disjoint_left.mp hqdisj hxq (Submonoid.mem_powers x)
  refine ⟨q, hpq, hprime, hxq, ?_⟩
  intro r hr hrprime
  by_contra hxr
  have hrT : r ∈ {q : Ideal A |
      Disjoint (q : Set A) ((Submonoid.powers x : Submonoid A) : Set A)} := by
    refine Set.disjoint_left.mpr ?_
    rintro a ha hpows
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a x).mp hpows
    rw [← hn] at ha
    exact hxr (hrprime.mem_of_pow_mem n ha)
  have hle : r ≤ q := hqmax.2 hrT (le_of_lt hr)
  exact absurd hr (not_lt_of_ge hle)

/-- If every non-maximal prime ideal is the intersection of the prime ideals strictly containing
it, then every element outside a prime ideal escapes a maximal ideal containing it. -/
theorem exists_isMaximal_ge_notMem_of_primeEqSInfLargerPrimes
    (hbook : PrimeEqSInfLargerPrimes A) {p : Ideal A} (hp : p.IsPrime) {x : A} (hx : x ∉ p) :
    ∃ M : Ideal A, p ≤ M ∧ M.IsMaximal ∧ x ∉ M := by
  obtain ⟨q, hpq, hprime, hxq, hall⟩ := exists_prime_ge_max_notMem_powers hp hx
  refine ⟨q, hpq, ?_, hxq⟩
  by_contra hqmax
  have hqeq : q = sInf {r : Ideal A | r.IsPrime ∧ q < r} := hbook q hprime hqmax
  have hxmem : x ∈ sInf {r : Ideal A | r.IsPrime ∧ q < r} := by
    rw [Submodule.mem_sInf]
    rintro r ⟨hr, hqr⟩
    exact hall r hqr hr
  rw [← hqeq] at hxmem
  exact hxq hxmem

/-- Conversely, 5.23 (iii) forces every prime ideal to be an intersection of maximal ideals, i.e.
the ring is Jacobson. -/
theorem isJacobsonRing_of_primeEqSInfLargerPrimes (hbook : PrimeEqSInfLargerPrimes A) :
    IsJacobsonRing A := by
  refine isJacobsonRing_iff_prime_eq.mpr fun p hp => ?_
  refine Ideal.eq_jacobson_iff_notMem.mpr ?_
  intro x hx
  obtain ⟨M, hle, hmax, hxM⟩ :=
    exists_isMaximal_ge_notMem_of_primeEqSInfLargerPrimes hbook hp hx
  exact ⟨M, ⟨hle, hmax⟩, hxM⟩

/-- The book's condition that every prime ideal is an intersection of maximal ideals (Exercise
5.23 (i)), which is the definition of a Jacobson ring used in the book. -/
theorem isJacobsonRing_iff_prime_eq_sInf_maximal :
    IsJacobsonRing A ↔
      ∀ p : Ideal A, p.IsPrime → p = sInf {m : Ideal A | m.IsMaximal ∧ p ≤ m} := by
  constructor
  · intro hA p hp
    have hset : {J : Ideal A | p ≤ J ∧ J.IsMaximal} = {m : Ideal A | m.IsMaximal ∧ p ≤ m} := by
      ext m
      simp only [Set.mem_ofPred_eq]
      tauto
    have h1 : p.jacobson = p := isJacobsonRing_iff_prime_eq.mp hA p hp
    conv_lhs => rw [← h1]
    rw [Ideal.jacobson, hset]
  · intro h
    refine isJacobsonRing_iff_prime_eq.mpr fun p hp => ?_
    have hset : {J : Ideal A | p ≤ J ∧ J.IsMaximal} = {m : Ideal A | m.IsMaximal ∧ p ≤ m} := by
      ext m
      simp only [Set.mem_ofPred_eq]
      tauto
    rw [Ideal.jacobson, hset, ← h p hp]

/-! ## Exercise 5.26 (iii): locally closed singletons and the Jacobson property -/

/-- If every locally closed singleton of `Spec A` is closed, then every non-maximal prime ideal is
the intersection of the prime ideals strictly containing it: otherwise an element
`f ∈ ⋂_{q > p} q` with `f ∉ p` cuts out the locally closed singleton `{p}` as
`V(p) ∩ D(f)`. -/
theorem primeEqSInfLargerPrimes_of_locallyClosedSingletonsClosed
    (hiii : LocallyClosedSingletonsClosed A) : PrimeEqSInfLargerPrimes A := by
  intro p hp hmax
  refine le_antisymm ?_ ?_
  · exact le_sInf fun q hq => le_of_lt hq.2
  · by_contra hcon
    have hex : ∃ f ∈ sInf {q : Ideal A | q.IsPrime ∧ p < q}, f ∉ p := by
      by_contra hall
      apply hcon
      intro x hx
      by_contra hxp
      exact hall ⟨x, hx, hxp⟩
    obtain ⟨f, hf, hfp⟩ := hex
    set P : PrimeSpectrum A := ⟨p, hp⟩ with hP
    have heq : PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.basicOpen f = {P} := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro q ⟨hq, hqf⟩
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hle : p ≤ q.asIdeal := hq
        have hlt : p < q.asIdeal := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h.symm))
        have hmemq : q.asIdeal ∈ {r : Ideal A | r.IsPrime ∧ p < r} := ⟨q.2, hlt⟩
        have hfq : f ∈ q.asIdeal := sInf_le hmemq hf
        exact (PrimeSpectrum.mem_basicOpen f q).mp hqf hfq
      · intro q hq
        have hqp : q = P := by simpa using hq
        subst hqp
        refine ⟨?_, ?_⟩
        · exact (PrimeSpectrum.mem_zeroLocus P (p : Set A)).mpr le_rfl
        · exact (PrimeSpectrum.mem_basicOpen f P).mpr hfp
    have hloc' : IsLocallyClosedSet
        (PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.basicOpen f) :=
      ⟨PrimeSpectrum.basicOpen f, PrimeSpectrum.zeroLocus (p : Set A),
        PrimeSpectrum.isOpen_basicOpen, PrimeSpectrum.isClosed_zeroLocus _, Set.inter_comm _ _⟩
    have hloc : IsLocallyClosedSet ({P} : Set (PrimeSpectrum A)) := heq ▸ hloc'
    have hclosed : IsClosed ({P} : Set (PrimeSpectrum A)) := hiii P hloc
    exact hmax ((PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp hclosed)

/-- A Jacobson ring has closed locally closed singletons in its spectrum: a locally closed
singleton `{p}` is of the form `V(p) ∩ D(f)` with `f ∉ p`, and every prime strictly containing `p`
contains `f`, contradicting that `p` is an intersection of strictly larger primes. -/
theorem locallyClosedSingletonsClosed_of_isJacobsonRing [IsJacobsonRing A] :
    LocallyClosedSingletonsClosed A := by
  intro P hloc
  obtain ⟨f, hf, heq⟩ := exists_basicOpen_of_isLocallyClosedSet_singleton hloc
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  by_contra hmax
  have hbook := primeEqSInfLargerPrimes_of_isJacobsonRing (A := A) P.asIdeal P.2 hmax
  have hfmem : f ∈ sInf {q : Ideal A | q.IsPrime ∧ P.asIdeal < q} := by
    rw [Submodule.mem_sInf]
    rintro q ⟨hq, hpq⟩
    by_contra hfq
    have hmem : (⟨q, hq⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (P.asIdeal : Set A) ∩ PrimeSpectrum.basicOpen f :=
      ⟨(PrimeSpectrum.mem_zeroLocus ⟨q, hq⟩ (P.asIdeal : Set A)).mpr (le_of_lt hpq),
        (PrimeSpectrum.mem_basicOpen f ⟨q, hq⟩).mpr hfq⟩
    rw [heq] at hmem
    have hqP : (⟨q, hq⟩ : PrimeSpectrum A) = P := by simpa using hmem
    have hidx : q = P.asIdeal := congrArg PrimeSpectrum.asIdeal hqP
    rw [hidx] at hpq
    exact absurd hpq (lt_irrefl _)
  rw [← hbook] at hfmem
  exact hf hfmem

/-- (i) `⟺` (iii) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
theorem isJacobsonRing_iff_locallyClosedSingletonsClosed :
    IsJacobsonRing A ↔ LocallyClosedSingletonsClosed A :=
  ⟨fun _ => locallyClosedSingletonsClosed_of_isJacobsonRing,
    fun h => isJacobsonRing_of_primeEqSInfLargerPrimes
      (primeEqSInfLargerPrimes_of_locallyClosedSingletonsClosed h)⟩

/-- (ii) `⟺` (iii) of Atiyah–Macdonald, Chapter 5, Exercise 26. -/
theorem veryDense_maxPoints_iff_locallyClosedSingletonsClosed :
    VeryDense (maxPoints A) ↔ LocallyClosedSingletonsClosed A :=
  (isJacobsonRing_iff_veryDense_maxPoints (A := A)).symm.trans
    isJacobsonRing_iff_locallyClosedSingletonsClosed

/-- **Atiyah–Macdonald, Chapter 5, Exercise 26** (algebraic part): for a commutative ring `A` the
following are equivalent:
(i) `A` is a Jacobson ring;
(ii) the set of maximal ideals of `A` is very dense in `Spec A`;
(iii) every locally closed subset of `Spec A` consisting of a single point is closed. -/
theorem jacobson_tfae (A : Type*) [CommRing A] :
    (IsJacobsonRing A ↔ VeryDense (maxPoints A)) ∧
      (VeryDense (maxPoints A) ↔ LocallyClosedSingletonsClosed A) :=
  ⟨isJacobsonRing_iff_veryDense_maxPoints,
    isJacobsonRing_iff_veryDense_maxPoints.symm.trans
      isJacobsonRing_iff_locallyClosedSingletonsClosed⟩

/-- Very density of the set of maximal ideals is precisely Mathlib's condition for `Spec A` to be a
Jacobson space (the closed points are dense in every closed subset). -/
theorem veryDense_maxPoints_iff_jacobsonSpace :
    VeryDense (maxPoints A) ↔ JacobsonSpace (PrimeSpectrum A) := by
  rw [maxPoints_eq_closedPoints, jacobsonSpace_iff]
  constructor
  · intro h Z hZ
    rw [Set.inter_comm Z (closedPoints (PrimeSpectrum A))]
    exact h Z hZ
  · intro h Z hZ
    rw [Set.inter_comm (closedPoints (PrimeSpectrum A)) Z]
    exact h hZ

end Ring

/-! ## Axiom check

The main results of the file depend only on the standard logical axioms. -/

#print axioms AtiyahMcdonald69.Ex_5_26.isLocallyClosedSet_iff_exists_open_inter_closure
#print axioms AtiyahMcdonald69.Ex_5_26.veryDenseCond3_iff_bijective_openRestrictionSubtype
#print axioms AtiyahMcdonald69.Ex_5_26.veryDense_tfae
#print axioms AtiyahMcdonald69.Ex_5_26.isJacobsonRing_iff_prime_eq_sInf_maximal
#print axioms AtiyahMcdonald69.Ex_5_26.isJacobsonRing_iff_veryDense_maxPoints
#print axioms AtiyahMcdonald69.Ex_5_26.isJacobsonRing_iff_locallyClosedSingletonsClosed
#print axioms AtiyahMcdonald69.Ex_5_26.veryDense_maxPoints_iff_locallyClosedSingletonsClosed
#print axioms AtiyahMcdonald69.Ex_5_26.jacobson_tfae
#print axioms AtiyahMcdonald69.Ex_5_26.veryDense_maxPoints_iff_jacobsonSpace
