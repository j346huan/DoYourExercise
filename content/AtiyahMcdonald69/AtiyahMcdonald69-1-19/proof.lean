/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 1, Exercise 19 (p. 13).

Statement (book, p. 13).  A topological space `X` is said to be *irreducible* if `X ≠ ∅` and
if every pair of non-empty open sets in `X` intersect, or equivalently if every non-empty open
set is dense in `X`.  Show that `Spec(A)` is irreducible if and only if the nilradical of `A`
is a prime ideal.

Statement sources: the book text (Chapter 1, p. 13), the solution archive
`AtiyahMcdonald69-1-19` (whose declared dependency is Exercise 1.17), and
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-19

The declared statement is formalised below with the book's own definition of irreducibility
(`IsIrreducibleSpace`), the book's equivalent dense-open formulation, and the book's closed-set
observation.  The two implications of the exercise are proved separately
(`isIrreducibleSpace_primeSpectrum_of_isPrime`, `isPrime_nilradical_of_isIrreducibleSpace`) and
combined in `solution`.
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_1_19

universe u

/-! ## Irreducible topological spaces: the book's definition and its equivalent forms -/

/-- Atiyah–Macdonald, p. 13: a topological space `X` is irreducible if `X ≠ ∅` and every pair of
non-empty open sets in `X` intersect. -/
def IsIrreducibleSpace (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty X ∧ ∀ U V : Set X, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    (U ∩ V).Nonempty

variable {X : Type u} [TopologicalSpace X]

/-- The book's "or equivalently if every non-empty open set is dense in `X`". -/
theorem isIrreducibleSpace_iff_forall_dense :
    IsIrreducibleSpace X ↔ Nonempty X ∧ ∀ U : Set X, IsOpen U → U.Nonempty → Dense U := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun U hU hUne => (dense_iff_inter_open (s := U)).mpr fun V hV hVne =>
      h V U hV hU hVne hUne⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun U V hU hV hUne hVne => (h V hV hVne).inter_open_nonempty U hU hUne⟩

/-- The book's observation: `X` is irreducible if and only if `X ≠ ∅` and `X = C ∪ D` with
`C`, `D` closed forces `C = X` or `D = X`. -/
theorem isIrreducibleSpace_iff_forall_closed :
    IsIrreducibleSpace X ↔
      Nonempty X ∧ ∀ C D : Set X, IsClosed C → IsClosed D → C ∪ D = Set.univ →
        C = Set.univ ∨ D = Set.univ := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun C D hC hD hCD => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hCne, hDne⟩ := hcon
    obtain ⟨x, hxC⟩ := (Set.ne_univ_iff_exists_notMem C).mp hCne
    obtain ⟨y, hyD⟩ := (Set.ne_univ_iff_exists_notMem D).mp hDne
    obtain ⟨z, hz⟩ :=
      h Cᶜ Dᶜ (isOpen_compl_iff.mpr hC) (isOpen_compl_iff.mpr hD) ⟨x, hxC⟩ ⟨y, hyD⟩
    have hzCD : z ∈ C ∪ D := by
      rw [hCD]
      exact Set.mem_univ z
    rw [Set.mem_union] at hzCD
    exact hzCD.elim hz.1 hz.2
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun U V hU hV hUne hVne => ?_⟩
    by_contra hcon
    have hinter : U ∩ V = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
    have hunion : (Uᶜ : Set X) ∪ Vᶜ = Set.univ := by
      simp [← Set.compl_inter, hinter]
    rcases h Uᶜ Vᶜ (isClosed_compl_iff.mpr hU) (isClosed_compl_iff.mpr hV) hunion with hU' | hV'
    · have hUempty : U = ∅ := by rw [← compl_compl U, hU', Set.compl_univ]
      exact Set.not_nonempty_empty (hUempty ▸ hUne)
    · have hVempty : V = ∅ := by rw [← compl_compl V, hV', Set.compl_univ]
      exact Set.not_nonempty_empty (hVempty ▸ hVne)

/-- The book's notion agrees with Mathlib's `IrreducibleSpace`, which is the same condition on
`Set.univ`. -/
theorem isIrreducibleSpace_iff_irreducibleSpace :
    IsIrreducibleSpace X ↔ IrreducibleSpace X := by
  constructor
  · rintro ⟨hne, h⟩
    rw [irreducibleSpace_def]
    exact ⟨⟨hne.some, trivial⟩,
      (PreirreducibleSpace.of_forall_nonempty_inter h).isPreirreducible_univ⟩
  · intro h
    obtain ⟨hne, hpre⟩ := (irreducibleSpace_def X).mp h
    obtain ⟨x, -⟩ := hne
    refine ⟨⟨x⟩, fun U V hU hV hUne hVne => ?_⟩
    have hU' : ((⊤ : Set X) ∩ U).Nonempty := by simpa using hUne
    have hV' : ((⊤ : Set X) ∩ V).Nonempty := by simpa using hVne
    have := hpre U V hU hV hU' hV'
    simpa using this

/-! ## The spectrum of a commutative ring -/

variable {A : Type u} [CommRing A]

/-- Exercise 1.17 (ii), the declared dependency of Exercise 1.19: `X_f` is empty if and only if
`f` is nilpotent.  In the language of Mathlib, `X_f = basicOpen f`. -/
theorem basicOpen_eq_empty_iff (f : A) :
    ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)) = ∅ ↔ f ∈ nilradical A := by
  rw [← TopologicalSpace.Opens.coe_bot, TopologicalSpace.Opens.coe_inj,
    PrimeSpectrum.basicOpen_eq_bot_iff, mem_nilradical]

/-- Exercise 1.17 (ii) in the form used below: `X_f ≠ ∅` if and only if `f` is not nilpotent. -/
theorem basicOpen_nonempty_iff (f : A) :
    ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)).Nonempty ↔ f ∉ nilradical A := by
  rw [Set.nonempty_iff_ne_empty, Ne, basicOpen_eq_empty_iff]

/-- `Spec(A)` is irreducible when the nilradical of `A` is a prime ideal: the `⟸` direction of
Exercise 1.19, following the book's proof with the basic open sets `X_f`. -/
theorem isIrreducibleSpace_primeSpectrum_of_isPrime (h : (nilradical A).IsPrime) :
    IsIrreducibleSpace (PrimeSpectrum A) := by
  obtain ⟨M, hMmax, -⟩ := Ideal.exists_le_maximal (nilradical A) h.ne_top
  refine ⟨⟨⟨M, hMmax.isPrime⟩⟩, ?_⟩
  intro U V hU hV hUne hVne
  obtain ⟨p, hpU⟩ := hUne
  obtain ⟨q, hqV⟩ := hVne
  obtain ⟨v, ⟨f, rfl⟩, hpv, hvU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
  obtain ⟨w, ⟨g, rfl⟩, hqw, hwV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hV
  have hf : f ∉ nilradical A := fun hfN => hpv (nilradical_le_prime p.asIdeal hfN)
  have hg : g ∉ nilradical A := fun hgN => hqw (nilradical_le_prime q.asIdeal hgN)
  have hfg : f * g ∉ nilradical A := h.mul_notMem hf hg
  obtain ⟨r, hr⟩ := (basicOpen_nonempty_iff (A := A) (f * g)).mpr hfg
  have hr' : r ∈ ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
      Set (PrimeSpectrum A)) ∩
      ((PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)) := by
    simpa [PrimeSpectrum.basicOpen_mul] using hr
  exact ⟨r, hvU hr'.1, hwV hr'.2⟩

/-- The nilradical of `A` is prime when `Spec(A)` is irreducible: the `⟹` direction of
Exercise 1.19, following the book's proof with the basic open sets `X_f`. -/
theorem isPrime_nilradical_of_isIrreducibleSpace (h : IsIrreducibleSpace (PrimeSpectrum A)) :
    (nilradical A).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨p⟩ := h.1
    have hle : nilradical A ≤ p.asIdeal := nilradical_le_prime p.asIdeal
    rw [htop] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  · intro f g hfg
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hf, hg⟩ := hcon
    have h1 : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)).Nonempty := (basicOpen_nonempty_iff f).mpr hf
    have h2 : ((PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)).Nonempty := (basicOpen_nonempty_iff g).mpr hg
    obtain ⟨r, hr⟩ := h.2 _ _ PrimeSpectrum.isOpen_basicOpen PrimeSpectrum.isOpen_basicOpen h1 h2
    have hnot : f * g ∉ r.asIdeal := by
      have hmem : r ∈ (PrimeSpectrum.basicOpen (f * g) :
          TopologicalSpace.Opens (PrimeSpectrum A)) := by
        rw [PrimeSpectrum.basicOpen_mul]
        exact hr
      exact (PrimeSpectrum.mem_basicOpen (f * g) r).mp hmem
    exact hnot (nilradical_le_prime r.asIdeal hfg)

/-- **Atiyah–Macdonald, Chapter 1, Exercise 1.19.**  `Spec(A)` is irreducible if and only if
the nilradical of `A` is a prime ideal. -/
theorem solution : IsIrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime :=
  ⟨isPrime_nilradical_of_isIrreducibleSpace, isIrreducibleSpace_primeSpectrum_of_isPrime⟩

/-- The same assertion phrased with Mathlib's class `IrreducibleSpace` instead of the book's
explicit open-set definition; the two notions agree by `isIrreducibleSpace_iff_irreducibleSpace`. -/
theorem solution_irreducibleSpace :
    IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime :=
  (isIrreducibleSpace_iff_irreducibleSpace (X := PrimeSpectrum A)).symm.trans solution

/-- The Hint of Exercise 1.19 in ideal form: conditions (b) and (c) of the Hint are equivalent.
The hypothesis `Nontrivial A` is the book's standing convention `1 ≠ 0`; it is needed here
because for the zero ring the nilradical is the unit ideal while the right-hand side holds
vacuously. -/
theorem nilradical_isPrime_iff_forall_ideal_mul [Nontrivial A] :
    (nilradical A).IsPrime ↔
      ∀ a b : Ideal A, a * b ≤ nilradical A → a ≤ nilradical A ∨ b ≤ nilradical A := by
  constructor
  · intro h a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨haN, hbN⟩ := hcon
    obtain ⟨f, hfa, hfN⟩ := SetLike.not_le_iff_exists.mp haN
    obtain ⟨g, hgb, hgN⟩ := SetLike.not_le_iff_exists.mp hbN
    exact hgN ((h.mem_or_mem (hab (Ideal.mul_mem_mul hfa hgb))).resolve_left hfN)
  · intro h
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : A) ∈ nilradical A := by
        rw [htop]
        exact Submodule.mem_top
      rw [mem_nilradical] at h1
      obtain ⟨n, hn⟩ := h1
      simp at hn
    · intro f g hfg
      have hspan : Ideal.span ({f} : Set A) * Ideal.span ({g} : Set A) ≤ nilradical A := by
        rw [Ideal.span_singleton_mul_span_singleton]
        exact (Ideal.span_singleton_le_iff_mem (I := nilradical A)).mpr hfg
      rcases h _ _ hspan with hle | hle
      · exact Or.inl ((Ideal.span_singleton_le_iff_mem (I := nilradical A)).mp hle)
      · exact Or.inr ((Ideal.span_singleton_le_iff_mem (I := nilradical A)).mp hle)


/-! ## The Hint of Exercise 1.19 -/

/-- The Hint's notion: a space is reducible when it has two nonempty disjoint open subsets. -/
def IsReducibleSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ Disjoint U V

/-- The Hint of Exercise 1.19, (a) ⇔ (b): `Spec(A)` is reducible if and only if there are ideals
`a`, `b` which are not contained in the nilradical but whose product is. -/
theorem isReducibleSpace_primeSpectrum_iff_exists_ideals :
    IsReducibleSpace (PrimeSpectrum A) ↔
      ∃ a b : Ideal A, ¬ a ≤ nilradical A ∧ ¬ b ≤ nilradical A ∧ a * b ≤ nilradical A := by
  constructor
  · rintro ⟨U, V, hU, hV, ⟨p, hpU⟩, ⟨q, hqV⟩, hdisj⟩
    obtain ⟨u, ⟨f, rfl⟩, hpf, hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    obtain ⟨v, ⟨g, rfl⟩, hqg, hgV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hV
    have hfN : f ∉ nilradical A := fun hf => hpf (nilradical_le_prime p.asIdeal hf)
    have hgN : g ∉ nilradical A := fun hg => hqg (nilradical_le_prime q.asIdeal hg)
    have hfgN : f * g ∈ nilradical A := by
      rw [← basicOpen_eq_empty_iff]
      refine Set.eq_empty_iff_forall_notMem.mpr fun r hr => ?_
      have hr' : r ∈ ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
          Set (PrimeSpectrum A)) ∩ ((PrimeSpectrum.basicOpen g :
            TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.basicOpen_mul] using hr
      exact Set.disjoint_left.mp hdisj (hfU hr'.1) (hgV hr'.2)
    refine ⟨Ideal.span ({f} : Set A), Ideal.span ({g} : Set A), ?_, ?_, ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hfN
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hgN
    · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
      exact hfgN
  · rintro ⟨a, b, haN, hbN, habN⟩
    obtain ⟨f, hfa, hfN⟩ := SetLike.not_le_iff_exists.mp haN
    obtain ⟨g, hgb, hgN⟩ := SetLike.not_le_iff_exists.mp hbN
    refine ⟨((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) :
      Set (PrimeSpectrum A)), ((PrimeSpectrum.basicOpen g :
        TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)),
      PrimeSpectrum.isOpen_basicOpen, PrimeSpectrum.isOpen_basicOpen,
      (basicOpen_nonempty_iff f).mpr hfN, (basicOpen_nonempty_iff g).mpr hgN, ?_⟩
    rw [Set.disjoint_left]
    intro r hrf hrg
    have hmem : r ∈ (PrimeSpectrum.basicOpen (f * g) :
        TopologicalSpace.Opens (PrimeSpectrum A)) := by
      rw [PrimeSpectrum.basicOpen_mul]
      exact ⟨hrf, hrg⟩
    have hnot : f * g ∉ r.asIdeal := (PrimeSpectrum.mem_basicOpen (f * g) r).mp hmem
    exact hnot (nilradical_le_prime r.asIdeal (habN (Ideal.mul_mem_mul hfa hgb)))

end AtiyahMcdonald69.Ex_1_19
