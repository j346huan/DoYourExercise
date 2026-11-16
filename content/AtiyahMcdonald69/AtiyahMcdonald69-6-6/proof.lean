/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 6, Exercise 6 (p. 79).

The book's statement:

  "Prove that the following are equivalent:
     (i)  `X` is Noetherian.
     (ii) Every open subspace of `X` is quasi-compact.
     (iii) Every subspace of `X` is quasi-compact."

with the hint for (ii) ⇒ (i): "the chain `U₁ ⊂ U₂ ⊂ ⋯` of open subsets covers the open
subset `U₁ ∪ U₂ ∪ ⋯`".

The notion of a Noetherian space is introduced in the preceding exercise (Chapter 6,
Exercise 5, p. 79): "A topological space `X` is said to be Noetherian if the open subsets of
`X` satisfy the ascending chain condition (or, equivalently, the maximal condition). Since
closed subsets are complements of open subsets, it comes to the same thing to say that the
closed subsets of `X` satisfy the descending chain condition."

Formalisation.  We compare

  (i)   `NoetherianSpace X`                     -- a.c.c. for open sets (Mathlib's class)
  (ii)  `∀ U, IsOpen U → CompactSpace U`        -- every open subspace is quasi-compact
  (iii) `∀ Y : Set X, CompactSpace Y`           -- every subspace is quasi-compact

and prove the three-way equivalence, with each implication as a separately named result and
the whole exercise as the single theorem `solution`.  Mathlib's `IsCompact`/`CompactSpace`
is the finite-subcover property with no separation hypothesis, i.e. exactly the book's
"quasi-compact"; see the remark at the end of the file for why the distinction matters.

Proofs follow the book, including its hints:
* (i) ⇒ (ii): if an open `U` were not quasi-compact, the open sets `U ∩ ⋃_{i ∈ t} V i`
  (over finite `t`) would have no maximal element (the book's "maximal condition" hint),
  contradicting a.c.c. for open sets.
* (ii) ⇒ (i): an increasing sequence of open sets covers its union (the book's hint); that
  union is an open subspace, hence quasi-compact, so finitely many members already cover it
  and the sequence stabilises.
* (ii) ⇒ (iii): an open cover of `Y` by the `V i` also covers the open subspace `⋃ i, V i`,
  so finitely many `V i` cover `⋃ i, V i`, hence cover `Y`.
* (iii) ⇒ (ii): immediate.
-/
import Mathlib

open Topology TopologicalSpace
open List

namespace AtiyahMcdonald69.Ex_6_6

variable {X : Type*} [TopologicalSpace X]

/-! ### The definition of a Noetherian topological space -/

/-- The ascending chain condition for open sets: every monotone sequence of open sets is
eventually constant.  This is the book's definition of a Noetherian topological space. -/
def AscendingChainConditionOpen (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : ℕ →o Opens X, ∃ N, ∀ n, N ≤ n → U N = U n

/-- The ascending chain condition for open sets is exactly Mathlib's `NoetherianSpace`
(well-foundedness of the reverse inclusion order on open sets). -/
theorem ascendingChainConditionOpen_iff_noetherianSpace :
    AscendingChainConditionOpen X ↔ NoetherianSpace X := by
  unfold AscendingChainConditionOpen
  show (∀ U : ℕ →o Opens X, ∃ N, ∀ n, N ≤ n → U N = U n) ↔ WellFoundedGT (Opens X)
  exact (wellFoundedGT_iff_monotone_chain_condition (α := Opens X)).symm

/-- The bundled form of the ascending chain condition, unwound into a statement about
sequences of open *subsets*, which is how the book phrases it. -/
theorem ascendingChainConditionOpen_iff_forall_sets :
    AscendingChainConditionOpen X ↔
      ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → Monotone U →
        ∃ N, ∀ n, N ≤ n → U N = U n := by
  constructor
  · intro h U hU hmono
    obtain ⟨N, hN⟩ := h ⟨fun n => ⟨U n, hU n⟩, fun m n hmn => hmono hmn⟩
    exact ⟨N, fun n hn => congrArg (fun V : Opens X => (V : Set X)) (hN n hn)⟩
  · intro h U
    obtain ⟨N, hN⟩ := h (fun n => (U n : Set X)) (fun n => (U n).isOpen)
      fun m n hmn => SetLike.coe_subset_coe.mpr (U.monotone hmn)
    exact ⟨N, fun n hn => Opens.ext (hN n hn)⟩

/-- The **maximal condition** for open sets, the equivalent form of the definition that the
proof of (i) ⇒ (ii) uses: every nonempty family of open sets has a maximal element. -/
theorem exists_maximal_open [NoetherianSpace X] (S : Set (Opens X)) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, ¬ m < s :=
  (IsWellFounded.wf (r := (· > ·)) (α := Opens X)).has_min S hS

/-- A Noetherian space satisfies the descending chain condition for closed sets
(equivalently: it has no infinite strictly descending chain of closed subsets). -/
theorem noetherian_iff_wellFoundedLT_closeds :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (noetherianSpace_TFAE X).out 0 1

/-! ### (i) implies (ii): open subspaces of a Noetherian space are compact -/

/-- **(i) ⇒ (ii).**  In a Noetherian space every open set is quasi-compact.

Suppose that some open cover `V` of an open set `U` had no finite subcover.  Then the open
sets `U ∩ ⋃_{i ∈ t} V i`, indexed by finite `t`, would form a family with no maximal
element: for any `t` there is a point of `U ∩ V i` outside `⋃_{j ∈ t} V j`, so inserting `i`
in `t` strictly increases the set.  This contradicts the ascending chain condition. -/
theorem isCompact_of_noetherianSpace [NoetherianSpace X] {U : Set X} (hU : IsOpen U) :
    IsCompact U := by
  classical
  rw [isCompact_iff_finite_subcover]
  intro ι V hV hcover
  -- the open sets `W t = U ∩ ⋃_{i ∈ t} V i`
  let W : Finset ι → Opens X := fun t =>
    ⟨U ∩ ⋃ i ∈ t, V i, hU.inter (isOpen_biUnion fun i _ => hV i)⟩
  have hW : ∀ t : Finset ι, ((W t : Opens X) : Set X) = U ∩ ⋃ i ∈ t, V i := fun _ => rfl
  obtain ⟨a, ha, hmin⟩ := (IsWellFounded.wf (r := (· > ·)) (α := Opens X)).has_min
    (Set.range W) (Set.range_nonempty W)
  obtain ⟨t₀, rfl⟩ := ha
  -- for every `t` the set `W t` is not strictly larger than `W t₀`
  have hmax : ∀ t : Finset ι, ¬ W t₀ < W t := fun t ht => hmin (W t) (Set.mem_range_self t) ht
  have key : ∀ i : ι, U ∩ V i ⊆ ⋃ j ∈ t₀, V j := by
    intro i
    by_contra hnot
    rw [Set.not_subset] at hnot
    obtain ⟨z, hz, hz'⟩ := hnot
    have hzW : z ∈ ((W (insert i t₀) : Opens X) : Set X) := by
      rw [hW]
      exact ⟨hz.1, Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self i t₀, hz.2⟩⟩
    have hlt : W t₀ < W (insert i t₀) := by
      rw [SetLike.lt_iff_le_and_exists]
      refine ⟨?_, z, hzW, ?_⟩
      · refine SetLike.coe_subset_coe.mp fun w hw => ?_
        rw [hW] at hw ⊢
        obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hw.2
        exact ⟨hw.1, Set.mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hwj⟩⟩
      · intro hz₀
        have hz₀' : z ∈ ((W t₀ : Opens X) : Set X) := hz₀
        rw [hW] at hz₀'
        exact hz' hz₀'.2
    exact hmax (insert i t₀) hlt
  refine ⟨t₀, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
  exact key i ⟨hx, hi⟩

/-! ### (ii) implies (i): if every open subspace is compact, the space is Noetherian -/

/-- **(ii) ⇒ (i).**  If every open subspace is quasi-compact then the open sets satisfy the
ascending chain condition: an increasing sequence of open sets covers its union `U`, which
is an open subspace and hence quasi-compact, so finitely many of the members cover `U` and
the sequence is eventually constant. -/
theorem noetherianSpace_of_isCompact_open
    (h : ∀ U : Set X, IsOpen U → IsCompact U) : NoetherianSpace X := by
  rw [← ascendingChainConditionOpen_iff_noetherianSpace]
  intro U
  have hU : IsOpen (⋃ n, (U n : Set X)) := isOpen_iUnion fun n => (U n).isOpen
  obtain ⟨t, ht⟩ := (h _ hU).elim_finite_subcover (fun n : ℕ => (U n : Set X))
    (fun n => (U n).isOpen) (fun x hx => hx)
  refine ⟨t.sup id, fun m hm => ?_⟩
  refine le_antisymm (U.monotone hm) ?_
  intro x hx
  have hx' : x ∈ ⋃ n ∈ t, (U n : Set X) := ht (Set.mem_iUnion.mpr ⟨m, hx⟩)
  obtain ⟨n, hnt, hxn⟩ := Set.mem_iUnion₂.mp hx'
  exact SetLike.coe_subset_coe.mpr (U.monotone (Finset.le_sup hnt)) hxn

/-! ### (ii) and (iii) are equivalent -/

/-- **(ii) ⇒ (iii).**  If every open subspace is quasi-compact, then every subspace is: an
open cover of `Y` by the `V i` also covers the open subspace `⋃ i, V i`, so finitely many
`V i` cover that open subspace, hence cover `Y`. -/
theorem isCompact_of_isCompact_open (h : ∀ U : Set X, IsOpen U → IsCompact U) (Y : Set X) :
    IsCompact Y := by
  rw [isCompact_iff_finite_subcover]
  intro ι V hV hcover
  obtain ⟨t, ht⟩ := (h _ (isOpen_iUnion hV)).elim_finite_subcover V hV (fun x hx => hx)
  exact ⟨t, hcover.trans ht⟩

/-! ### The three conditions are equivalent -/

/-- **(i) ⇔ (ii)**: `X` is Noetherian if and only if every open subspace is quasi-compact. -/
theorem noetherian_iff_isCompact_open :
    NoetherianSpace X ↔ ∀ U : Set X, IsOpen U → IsCompact U := by
  constructor
  · intro hX U hU
    exact @isCompact_of_noetherianSpace X _ hX U hU
  · exact noetherianSpace_of_isCompact_open

/-- **(ii) ⇔ (iii)**: every open subspace is quasi-compact if and only if every subspace
is quasi-compact. -/
theorem isCompact_open_iff_isCompact :
    (∀ U : Set X, IsOpen U → IsCompact U) ↔ ∀ Y : Set X, IsCompact Y :=
  ⟨isCompact_of_isCompact_open, fun h U _ => h U⟩

/-- **(i) ⇔ (iii)**: `X` is Noetherian if and only if every subspace is quasi-compact. -/
theorem noetherian_iff_isCompact :
    NoetherianSpace X ↔ ∀ Y : Set X, IsCompact Y :=
  noetherian_iff_isCompact_open.trans isCompact_open_iff_isCompact

/-- **(i) ⇔ (ii)**, stated for subspaces: `X` is Noetherian if and only if every open
subspace (with the subspace topology) is compact. -/
theorem noetherian_iff_open_subspace_compact :
    NoetherianSpace X ↔ ∀ U : Set X, IsOpen U → CompactSpace U := by
  rw [noetherian_iff_isCompact_open]
  simp only [isCompact_iff_compactSpace]

/-- **(ii) ⇔ (iii)**, stated for subspaces. -/
theorem open_subspace_compact_iff_subspace_compact :
    (∀ U : Set X, IsOpen U → CompactSpace U) ↔ ∀ Y : Set X, CompactSpace Y := by
  simpa only [isCompact_iff_compactSpace] using isCompact_open_iff_isCompact (X := X)

/-- **(i) ⇔ (iii)**, stated for subspaces: `X` is Noetherian if and only if every subspace
(with the subspace topology) is compact. -/
theorem noetherian_iff_subspace_compact :
    NoetherianSpace X ↔ ∀ Y : Set X, CompactSpace Y := by
  rw [noetherian_iff_isCompact]
  simp only [isCompact_iff_compactSpace]

/-- **Atiyah–Macdonald, Chapter 6, Exercise 6.**  For a topological space `X` the following
are equivalent: (i) `X` is Noetherian (a.c.c. for open sets), (ii) every open subspace of
`X` is compact, (iii) every subspace of `X` is compact. -/
theorem solution :
    TFAE [NoetherianSpace X, (∀ U : Set X, IsOpen U → CompactSpace U),
      ∀ Y : Set X, CompactSpace Y] := by
  tfae_have 1 ↔ 2 := noetherian_iff_open_subspace_compact
  tfae_have 2 ↔ 3 := open_subspace_compact_iff_subspace_compact
  tfae_finish

/-! ### A remark on the word "compact"

The book's word in the exercise is "quasi-compact", i.e. the finite-subcover property with
no separation hypothesis; this is Mathlib's `IsCompact`/`CompactSpace` and is what is used
above.  Some circulated solutions texts paraphrase the exercise with "compact" rather than
"quasi-compact".  Taken literally as "compact Hausdorff" the exercise would be *false*:
applied to the open subspace `univ`, the implication (i) ⇒ (ii) would force every Noetherian
space to be Hausdorff, whereas the two-point indiscrete space is Noetherian but not
Hausdorff.  That counterexample is recorded below.  It concerns the terminology only, not
the book's assertion.
-/

/-- An indiscrete space is Noetherian: its only open sets are `∅` and `univ`, so every
subset is compact. -/
theorem indiscrete_noetherianSpace (X : Type*) [TopologicalSpace X] [IndiscreteTopology X] :
    NoetherianSpace X := by
  rw [noetherian_iff_isCompact]
  intro Y
  rw [isCompact_iff_finite_subcover]
  intro ι V hV hcover
  by_cases hY : Y = ∅
  · exact ⟨∅, by simp [hY]⟩
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hY
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    refine ⟨{i}, ?_⟩
    have hVi : V i = Set.univ := by
      rcases (IndiscreteTopology.isOpen_iff (V i)).mp (hV i) with h | h
      · exact absurd (h ▸ hi) (by simp)
      · exact h
    intro y _
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_singleton_self i, by rw [hVi]; exact Set.mem_univ y⟩

/-- An indiscrete space with two distinct points is not Hausdorff. -/
theorem indiscrete_not_t2Space (X : Type*) [TopologicalSpace X] [IndiscreteTopology X]
    {x y : X} (hxy : x ≠ y) : ¬ T2Space X := by
  intro h
  obtain ⟨u, v, hu, hv, hxu, hyv, hdisj⟩ := @t2_separation X _ h x y hxy
  rw [IndiscreteTopology.isOpen_iff] at hv
  have hv' : v = Set.univ := by rcases hv with h | h; exacts [absurd (h ▸ hyv) (by simp), h]
  exact hdisj.le_bot ⟨hxu, by rw [hv']; exact Set.mem_univ _⟩

/-- A Noetherian space need not be Hausdorff: the two-point indiscrete space is a
counterexample.  Hence "compact" in the exercise cannot mean "compact Hausdorff". -/
theorem noetherian_not_imp_t2 :
    ¬ ∀ (X : Type) (_ : TopologicalSpace X), NoetherianSpace X → T2Space X := by
  intro h
  exact @indiscrete_not_t2Space (Fin 2) ⊤ (@IndiscreteTopology.mk (Fin 2) ⊤ rfl) 0 1 (by decide)
    (h (Fin 2) ⊤ (@indiscrete_noetherianSpace (Fin 2) ⊤ (@IndiscreteTopology.mk (Fin 2) ⊤ rfl)))

end AtiyahMcdonald69.Ex_6_6

/-! ### Axiom audit

Every result below depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; in particular there is no `sorryAx` and no added axiom. -/

#print axioms AtiyahMcdonald69.Ex_6_6.ascendingChainConditionOpen_iff_noetherianSpace
#print axioms AtiyahMcdonald69.Ex_6_6.ascendingChainConditionOpen_iff_forall_sets
#print axioms AtiyahMcdonald69.Ex_6_6.exists_maximal_open
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_iff_wellFoundedLT_closeds
#print axioms AtiyahMcdonald69.Ex_6_6.isCompact_of_noetherianSpace
#print axioms AtiyahMcdonald69.Ex_6_6.noetherianSpace_of_isCompact_open
#print axioms AtiyahMcdonald69.Ex_6_6.isCompact_of_isCompact_open
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_iff_isCompact_open
#print axioms AtiyahMcdonald69.Ex_6_6.isCompact_open_iff_isCompact
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_iff_isCompact
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_iff_open_subspace_compact
#print axioms AtiyahMcdonald69.Ex_6_6.open_subspace_compact_iff_subspace_compact
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_iff_subspace_compact
#print axioms AtiyahMcdonald69.Ex_6_6.solution
#print axioms AtiyahMcdonald69.Ex_6_6.indiscrete_noetherianSpace
#print axioms AtiyahMcdonald69.Ex_6_6.indiscrete_not_t2Space
#print axioms AtiyahMcdonald69.Ex_6_6.noetherian_not_imp_t2
