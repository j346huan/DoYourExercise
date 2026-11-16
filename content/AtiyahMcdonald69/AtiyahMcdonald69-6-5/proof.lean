/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 6, Exercise 5.

The exercise reads (verbatim, as transcribed in Carlson's solutions to Chapter 6):

  "A topological space X is said to be Noetherian if the open subsets of X satisfy the ascending
   chain condition (or, equivalently, the maximal condition). Since closed subsets are complements
   of open subsets, it comes to the same thing to say that the closed subsets of X satisfy the
   descending chain condition (or, equivalently, the minimal condition).
   Show that, if X is Noetherian, then every subspace of X is Noetherian, and that X is compact."

Remarks on the statement.
* "Compact" is used in the finite-subcover sense (what some texts call quasi-compact); no
  separation axiom is assumed, and the book's own proof produces a finite subcover of an
  arbitrary open cover.  This is exactly Mathlib's `CompactSpace`.
* The exercise poses no question whose answer is false; both assertions are theorems.
* The two parenthetical equivalences in the definition (maximal condition for open sets,
  descending chain condition for closed sets) are proved here as well, so the file covers the
  whole of the exercise text.

Content of this file (all self-contained; the only imports are Mathlib):
* `IsNoetherianTopologicalSpace` : the definition, as an ascending chain condition;
* `wellFoundedGT_opens` : the chain condition as well-foundedness (`NoetherianSpace`);
* `exists_maximal_isOpen` : the maximal condition for open subsets;
* `isNoetherianTopologicalSpace_iff_isClosed` : the descending chain condition for closed sets;
* `exists_finite_subcover`, `isCompact_univ_of_noetherian`, `compactSpace_of_noetherian` :
  compactness of a Noetherian space;
* `subspace_noetherian` : every subspace of a Noetherian space is Noetherian;
* `solution` : the two assertions of the exercise together;
* `isNoetherianTopologicalSpace_iff_noetherianSpace` : agreement with Mathlib's
  `TopologicalSpace.NoetherianSpace`, as a consistency check.

See `notes.md` for the source audit and a comparison with the book's argument.
-/
import Mathlib

set_option autoImplicit false

open Set TopologicalSpace

namespace AtiyahMcdonald69.Ex_6_5

variable {X : Type*} [TopologicalSpace X]

/-- A topological space is Noetherian if its open subsets satisfy the ascending chain condition:
every increasing sequence of open subsets of `X` is eventually constant.  This is the definition
given in Atiyah–Macdonald, Chapter 6, Exercise 5. -/
def IsNoetherianTopologicalSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → Monotone U → ∃ N, ∀ n, N ≤ n → U n = U N

/-- The ascending chain condition for open sets, as a well-foundedness statement: this is
`TopologicalSpace.NoetherianSpace`, the form in which Mathlib states the Noetherian condition.
The point of the lemma is the passage from "increasing sequences stabilise" to the maximal
condition used below. -/
theorem wellFoundedGT_opens (h : IsNoetherianTopologicalSpace X) : WellFoundedGT (Opens X) := by
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro a
  obtain ⟨N, hN⟩ :=
    h (fun n => (a n : Set X)) (fun n => (a n).isOpen) (fun i j hij => a.mono hij)
  exact ⟨N, fun m hm => Opens.ext (hN m hm).symm⟩

/-- The maximal condition for open subsets, stated in Atiyah–Macdonald as an equivalent form of
the ascending chain condition: every non-empty family of open subsets has a maximal member. -/
theorem exists_maximal_isOpen (h : IsNoetherianTopologicalSpace X) {S : Set (Set X)}
    (hS : S.Nonempty) (hSo : ∀ U ∈ S, IsOpen U) :
    ∃ U ∈ S, ∀ U' ∈ S, U ⊆ U' → U' = U := by
  classical
  set S' : Set (Opens X) := {W | (W : Set X) ∈ S} with hS'def
  have hS' : S'.Nonempty := by
    obtain ⟨U, hU⟩ := hS
    exact ⟨⟨U, hSo U hU⟩, hU⟩
  obtain ⟨W, hW, hmax⟩ := (wellFoundedGT_opens h).wf.has_min S' hS'
  refine ⟨(W : Set X), hW, fun U' hU' hsub => ?_⟩
  set W' : Opens X := ⟨U', hSo U' hU'⟩ with hW'def
  have hle : W ≤ W' := hsub
  have heq : W = W' := by
    by_contra hne
    exact hmax W' hU' (lt_of_le_of_ne hle hne)
  exact congrArg (fun V : Opens X => (V : Set X)) heq.symm

/-- The ascending chain condition on open subsets is equivalent to the descending chain
condition on closed subsets, as observed in Atiyah–Macdonald's formulation of the definition. -/
theorem isNoetherianTopologicalSpace_iff_isClosed :
    IsNoetherianTopologicalSpace X ↔
      ∀ F : ℕ → Set X, (∀ n, IsClosed (F n)) → Antitone F → ∃ N, ∀ n, N ≤ n → F n = F N := by
  constructor
  · intro h F hF hFanti
    obtain ⟨N, hN⟩ :=
      h (fun n => (F n)ᶜ) (fun n => (hF n).isOpen_compl)
        (fun i j hij => Set.compl_subset_compl.mpr (hFanti hij))
    exact ⟨N, fun n hn => by simpa using congrArg compl (hN n hn)⟩
  · intro h U hUo hUmono
    obtain ⟨N, hN⟩ :=
      h (fun n => (U n)ᶜ) (fun n => (hUo n).isClosed_compl)
        (fun i j hij => Set.compl_subset_compl.mpr (hUmono hij))
    exact ⟨N, fun n hn => by simpa using congrArg compl (hN n hn)⟩

/-- A Noetherian topological space is compact, in the explicit finite-subcover form: every open
cover of `X`, indexed by an arbitrary type, has a finite subcover.  No separation axiom is used
or needed. -/
theorem exists_finite_subcover (h : IsNoetherianTopologicalSpace X) {ι : Type*} (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hcov : univ ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, univ ⊆ ⋃ i ∈ t, U i := by
  classical
  have hfam : ∀ W ∈ {W : Set X | ∃ t : Finset ι, W = ⋃ i ∈ t, U i}, IsOpen W := by
    rintro W ⟨t, rfl⟩
    exact isOpen_biUnion fun i _ => hUo i
  obtain ⟨W, hWmem, hWmax⟩ :=
    exists_maximal_isOpen (S := {W : Set X | ∃ t : Finset ι, W = ⋃ i ∈ t, U i}) h
      ⟨∅, ∅, by simp⟩ hfam
  obtain ⟨t, ht⟩ := hWmem
  have hWtop : W = univ := by
    by_contra hne
    have hex : ∃ x, x ∉ W := by
      by_contra h'
      exact hne (Set.eq_univ_of_forall fun x => by
        by_contra hx
        exact h' ⟨x, hx⟩)
    obtain ⟨x, hx⟩ := hex
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
    have hmem : W ∪ U i ∈ {W : Set X | ∃ t : Finset ι, W = ⋃ j ∈ t, U j} := by
      refine ⟨insert i t, ?_⟩
      rw [ht]
      ext x
      constructor
      · rintro (hx | hx)
        · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
          exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩
        · exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self i t, hx⟩
      · intro hx
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inr hxj
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, hj, hxj⟩)
    have hne' : W ∪ U i ≠ W := fun heq => hx (heq ▸ Set.mem_union_right W hi)
    exact hne' (hWmax (W ∪ U i) hmem Set.subset_union_left)
  exact ⟨t, by rw [← ht, hWtop]⟩

/-- A Noetherian topological space is compact: `univ` is a compact set. -/
theorem isCompact_univ_of_noetherian (h : IsNoetherianTopologicalSpace X) :
    IsCompact (univ : Set X) :=
  isCompact_of_finite_subcover fun {_} U hUo hcov => exists_finite_subcover h U hUo hcov

/-- Atiyah–Macdonald, Chapter 6, Exercise 5 (second assertion): a Noetherian topological space is
compact. -/
theorem compactSpace_of_noetherian (h : IsNoetherianTopologicalSpace X) : CompactSpace X :=
  ⟨isCompact_univ_of_noetherian h⟩

/-- Atiyah–Macdonald, Chapter 6, Exercise 5 (first assertion): every subspace `Y` of a Noetherian
topological space `X` is Noetherian (for the subspace topology on `Y`). -/
theorem subspace_noetherian (h : IsNoetherianTopologicalSpace X) (Y : Set X) :
    IsNoetherianTopologicalSpace Y := by
  intro U hUo hUmono
  choose V hVo hVU using fun n => isOpen_induced_iff.mp (hUo n)
  have hWo : ∀ n, IsOpen (⋃ i ∈ Iic n, V i) := fun n => isOpen_biUnion fun i _ => hVo i
  have hWmono : Monotone (fun n => ⋃ i ∈ Iic n, V i) := by
    intro a b hab x hx
    simp only [Set.mem_iUnion, Set.mem_Iic] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, le_trans hi hab, hxi⟩
  obtain ⟨N, hN⟩ := h (fun n => ⋃ i ∈ Iic n, V i) hWo hWmono
  have hp : ∀ m, (↑) ⁻¹' (⋃ i ∈ Iic m, V i) = U m := by
    intro m
    have h1 : (↑) ⁻¹' (⋃ i ∈ Iic m, V i) = ⋃ i ∈ Iic m, U i := by
      simp only [Set.preimage_iUnion, hVU]
    rw [h1]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · simp only [Set.mem_iUnion, Set.mem_Iic] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact hUmono hi hxi
    · exact Set.mem_iUnion₂_of_mem (le_refl m) hx
  exact ⟨N, fun n hn => by rw [← hp n, ← hp N, hN n hn]⟩

/-- Atiyah–Macdonald, Chapter 6, Exercise 5, both assertions: if `X` is a Noetherian topological
space, then every subspace of `X` is Noetherian and `X` is compact. -/
theorem solution (h : IsNoetherianTopologicalSpace X) :
    (∀ Y : Set X, IsNoetherianTopologicalSpace Y) ∧ CompactSpace X :=
  ⟨subspace_noetherian h, compactSpace_of_noetherian h⟩

/-- Consistency with the form of the Noetherian condition used in Mathlib: the ascending chain
condition for open subsets is `TopologicalSpace.NoetherianSpace`. -/
theorem isNoetherianTopologicalSpace_iff_noetherianSpace :
    IsNoetherianTopologicalSpace X ↔ TopologicalSpace.NoetherianSpace X := by
  constructor
  · intro h
    rw [TopologicalSpace.noetherianSpace_iff_isCompact]
    intro s
    exact isCompact_iff_compactSpace.mpr (compactSpace_of_noetherian (subspace_noetherian h s))
  · intro h U hUo hUmono
    obtain ⟨N, hN⟩ := @WellFoundedGT.monotone_chain_condition (Opens X) _ h
      ⟨fun n => ⟨U n, hUo n⟩, fun i j hij => hUmono hij⟩
    exact ⟨N, fun n hn => (congrArg (fun V : Opens X => (V : Set X)) (hN n hn)).symm⟩

/-! ### The two assertions stated with Mathlib's Noetherian condition

These restatements are immediate from `isNoetherianTopologicalSpace_iff_noetherianSpace`, but
they make the deliverable directly usable with `TopologicalSpace.NoetherianSpace`, whose own
docstring says it is "defined to be spaces whose open sets satisfies ACC". -/

/-- Exercise 6.5, first assertion, for Mathlib's `TopologicalSpace.NoetherianSpace`. -/
theorem subspace_noetherianSpace (h : TopologicalSpace.NoetherianSpace X) (Y : Set X) :
    TopologicalSpace.NoetherianSpace Y :=
  isNoetherianTopologicalSpace_iff_noetherianSpace.mp
    (subspace_noetherian (isNoetherianTopologicalSpace_iff_noetherianSpace.mpr h) Y)

/-- Exercise 6.5, second assertion, for Mathlib's `TopologicalSpace.NoetherianSpace`. -/
theorem compactSpace_of_noetherianSpace (h : TopologicalSpace.NoetherianSpace X) :
    CompactSpace X :=
  compactSpace_of_noetherian (isNoetherianTopologicalSpace_iff_noetherianSpace.mpr h)

/-! ### Sanity checks on the statement (not part of the book exercise)

These check that the hypothesis of `solution` is satisfiable by a genuinely infinite space, that
the conclusion is then a real statement about it, and that the hypothesis is a genuine
restriction on the space (so nothing here is vacuous). -/

/-- The hypothesis is satisfiable: every cofinite space is Noetherian. -/
example : IsNoetherianTopologicalSpace (CofiniteTopology ℕ) :=
  isNoetherianTopologicalSpace_iff_noetherianSpace.mpr inferInstance

/-- ... and the exercise then does give compactness of an infinite space. -/
example : CompactSpace (CofiniteTopology ℕ) :=
  compactSpace_of_noetherian
    (isNoetherianTopologicalSpace_iff_noetherianSpace.mpr inferInstance)

/-- The hypothesis is a genuine restriction: `ℝ` with its usual topology is not Noetherian,
because `(-∞, 0) ⊂ (-∞, 1) ⊂ (-∞, 2) ⊂ ⋯` is a strictly increasing chain of open sets. -/
example : ¬ IsNoetherianTopologicalSpace ℝ := by
  intro h
  obtain ⟨N, hN⟩ :=
    h (fun n => Set.Iio (n : ℝ)) (fun n => isOpen_Iio)
      (fun i j hij => Set.Iio_subset_Iio (by exact_mod_cast hij))
  have h1 : Set.Iio ((N : ℝ) + 1) = Set.Iio (N : ℝ) := by
    simpa using hN (N + 1) (Nat.le_succ N)
  have h2 : (N : ℝ) ∈ Set.Iio ((N : ℝ) + 1) := by
    rw [Set.mem_Iio]
    linarith
  rw [h1] at h2
  exact absurd h2 (lt_irrefl (N : ℝ))

#print axioms exists_maximal_isOpen
#print axioms isNoetherianTopologicalSpace_iff_isClosed
#print axioms exists_finite_subcover
#print axioms compactSpace_of_noetherian
#print axioms subspace_noetherian
#print axioms solution
#print axioms isNoetherianTopologicalSpace_iff_noetherianSpace
#print axioms subspace_noetherianSpace
#print axioms compactSpace_of_noetherianSpace

end AtiyahMcdonald69.Ex_6_5
