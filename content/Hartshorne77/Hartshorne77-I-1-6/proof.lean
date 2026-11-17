import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Exercise I.1.6

## The statement in the source

Chapter I, §1, Exercise 1.6 (verbatim):

> Any nonempty open subset of an irreducible topological space is dense and irreducible.
> If `Y` is a subset of a topological space `X`, which is irreducible in its induced
> topology, then the closure `Ȳ` is also irreducible.

The solution sketch given in the source runs as follows: in an irreducible space any two
nonempty open subsets meet; a nonempty open `U ⊆ X` therefore meets every nonempty open
subset of `X`, hence is dense; and two nonempty open subsets of `U` are also open in `X`,
hence meet, so `U` is irreducible.  If `Y` is irreducible and `Ȳ = F ∪ G` with `F, G`
closed, then `Y = (Y ∩ F) ∪ (Y ∩ G)`, so `Y ⊆ F` or `Y ⊆ G`; taking closures gives
`Ȳ = F` or `Ȳ = G`.

## Formalisation choices

* Mathlib's `IsIrreducible s` means that `s` is nonempty and every two relatively open
  subsets of `s` meet, i.e. `Nonempty ∧ IsPreirreducible`.  This is precisely
  Hartshorne's notion for a subset with its induced topology; in particular the empty set
  is *not* irreducible, as the book stipulates.
* For a subset `U ⊆ X`, `Dense U` means `closure U = univ`, i.e. `U` is dense in `X`.
* `IrreducibleSpace ↥Y` is the "irreducible in its induced topology" reading;
  `isIrreducible_iff_irreducibleSpace` shows that it agrees with `IsIrreducible Y`.

Everything below is pure point-set topology, valid for an arbitrary topological space; no
algebraic-geometry hypothesis (no field, no Zariski topology) is needed for this exercise.
Section 7 records that the statement is non-vacuous and that its hypotheses are sharp.
-/

namespace Hartshorne77.Ex_I_1_6

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## 1. Any two nonempty open subsets of an irreducible space intersect -/

/-- In an irreducible topological space, any two nonempty open subsets intersect.

This is the topological content of irreducibility, and the first step of the solution of
Hartshorne I.1.6: `U ∩ V ≠ ∅` whenever `U, V` are nonempty and open. -/
theorem nonempty_inter_of_isOpen [IrreducibleSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    (U ∩ V).Nonempty :=
  nonempty_preirreducible_inter hU hV hUne hVne

/-- The same fact under the weaker hypothesis `PreirreducibleSpace X` (no nonemptiness of
the ambient space is needed). -/
theorem nonempty_inter_of_isOpen_of_preirreducible [PreirreducibleSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    (U ∩ V).Nonempty :=
  nonempty_preirreducible_inter hU hV hUne hVne

/-- Contrapositive form: in an irreducible space there are no two disjoint nonempty open
subsets. -/
theorem not_disjoint_of_isOpen [IrreducibleSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    ¬ Disjoint U V :=
  Set.not_disjoint_iff_nonempty_inter.mpr (nonempty_inter_of_isOpen hU hV hUne hVne)

/-! ## 2. Part (a): a nonempty open subset of an irreducible space is dense and
irreducible -/

/-- **Hartshorne I.1.6, first assertion, density part.**  A nonempty open subset `U` of an
irreducible topological space `X` is dense in `X`: it meets every nonempty open subset
of `X`. -/
theorem dense_of_nonempty_isOpen [IrreducibleSpace X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : Dense U :=
  hU.dense hne

/-- The density statement written as an equality of closed sets: the closure of a nonempty
open subset of an irreducible space is the whole space. -/
theorem closure_eq_univ_of_nonempty_isOpen [IrreducibleSpace X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : closure U = univ :=
  dense_iff_closure_eq.mp (dense_of_nonempty_isOpen hU hne)

/-- **Hartshorne I.1.6, first assertion, irreducibility part**, proved directly from the
source's argument: any two nonempty open subsets of `U` are open in `X`, hence intersect,
so `U` is irreducible. -/
theorem isIrreducible_of_nonempty_isOpen [IrreducibleSpace X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : IsIrreducible U := by
  refine ⟨hne, ?_⟩
  intro u v hu hv hUu hUv
  -- `U ∩ u` and `U ∩ v` are nonempty open subsets of `X`, so they meet
  obtain ⟨x, hx⟩ :=
    nonempty_inter_of_isOpen (hU.inter hu) (hU.inter hv) hUu hUv
  exact ⟨x, by simp only [Set.mem_inter_iff] at hx ⊢; tauto⟩

/-- **Hartshorne I.1.6, first assertion**, with `U` regarded as a topological space with
its induced topology: a nonempty open subset of an irreducible space is an irreducible
topological space. -/
theorem irreducibleSpace_of_nonempty_isOpen [IrreducibleSpace X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : IrreducibleSpace U :=
  isIrreducible_iff_irreducibleSpace.mp (isIrreducible_of_nonempty_isOpen hU hne)

/-- **Hartshorne I.1.6, first assertion**, both conclusions together. -/
theorem dense_and_isIrreducible_of_nonempty_isOpen [IrreducibleSpace X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : Dense U ∧ IsIrreducible U :=
  ⟨dense_of_nonempty_isOpen hU hne, isIrreducible_of_nonempty_isOpen hU hne⟩

/-! ## 3. Part (b): the closure of an irreducible subset is irreducible -/

/-- **Hartshorne I.1.6, second assertion.**  If `Y ⊆ X` is irreducible in its induced
topology, then its closure in `X` is irreducible.

The proof follows the source: if `closure Y ⊆ F ∪ G` with `F, G` closed, then
`Y ⊆ F ∪ G`, so irreducibility of `Y` gives `Y ⊆ F` or `Y ⊆ G`, and since `F`, `G` are
closed this gives `closure Y ⊆ F` or `closure Y ⊆ G`. -/
theorem isIrreducible_closure {Y : Set X} (hY : IsIrreducible Y) :
    IsIrreducible (closure Y) := by
  refine ⟨closure_nonempty_iff.mpr hY.nonempty, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro F G hF hG hcov
  have h := (isPreirreducible_iff_isClosed_union_isClosed.mp hY.isPreirreducible)
    F G hF hG (Subset.trans subset_closure hcov)
  rcases h with hF' | hG'
  · exact Or.inl (hF.closure_subset_iff.mpr hF')
  · exact Or.inr (hG.closure_subset_iff.mpr hG')

/-- Part (b) as an equivalence: a set is irreducible exactly when its closure is (so the
closure operation does not change irreducibility of a subset).  The forward implication is
Hartshorne I.1.6, the reverse is the trivial direction. -/
theorem isIrreducible_closure_iff {Y : Set X} :
    IsIrreducible (closure Y) ↔ IsIrreducible Y :=
  isIrreducible_iff_closure

/-- **Hartshorne I.1.6, second assertion**, in the "induced topology" formulation: the
closure of an irreducible subset is an irreducible topological space. -/
theorem irreducibleSpace_closure {Y : Set X} (hY : IsIrreducible Y) :
    IrreducibleSpace (closure Y) :=
  isIrreducible_iff_irreducibleSpace.mp (isIrreducible_closure hY)

/-- The second assertion with the hypothesis written literally as "irreducible in its
induced topology". -/
theorem isIrreducible_closure_of_irreducibleSpace {Y : Set X} [IrreducibleSpace Y] :
    IsIrreducible (closure Y) :=
  isIrreducible_closure (isIrreducible_iff_irreducibleSpace.mpr ‹IrreducibleSpace Y›)

/-! ## 4. The exercise as a single statement -/

/-- **Hartshorne I.1.6**, both assertions, in the exact shape of the source statement:

1. every nonempty open subset of an irreducible topological space is dense and
   irreducible;
2. the closure of a subset that is irreducible in its induced topology is irreducible. -/
theorem hartshorne_ex_1_6 (hX : IrreducibleSpace X) :
    (∀ U : Set X, IsOpen U → U.Nonempty → Dense U ∧ IsIrreducible U) ∧
      ∀ Y : Set X, IsIrreducible Y → IsIrreducible (closure Y) := by
  refine ⟨fun U hU hne => dense_and_isIrreducible_of_nonempty_isOpen hU hne, ?_⟩
  intro Y hY
  exact isIrreducible_closure hY

/-- **Hartshorne I.1.6**, both assertions with irreducibility stated for the subspace
topology (the literal reading of "irreducible in its induced topology"). -/
theorem hartshorne_ex_1_6_subspace (hX : IrreducibleSpace X) :
    (∀ U : Set X, IsOpen U → U.Nonempty → Dense U ∧ IrreducibleSpace U) ∧
      ∀ Y : Set X, IrreducibleSpace Y → IrreducibleSpace (closure Y) := by
  refine ⟨fun U hU hne =>
    ⟨dense_of_nonempty_isOpen hU hne, irreducibleSpace_of_nonempty_isOpen hU hne⟩, ?_⟩
  intro Y hY
  exact irreducibleSpace_closure (isIrreducible_iff_irreducibleSpace.mpr hY)

/-! ## 5. Converse characterisations

The density assertion of part (a) actually characterises irreducibility.  These converses
are not needed for the exercise but show that nothing was weakened in the formulation. -/

/-- A space is preirreducible if and only if every nonempty open subset is dense. -/
theorem preirreducibleSpace_iff_forall_dense_open (X : Type*) [TopologicalSpace X] :
    PreirreducibleSpace X ↔ ∀ ⦃U : Set X⦄, IsOpen U → U.Nonempty → Dense U :=
  preirreducibleSpace_iff_open_dense X

/-- For a nonempty space: it is irreducible if and only if every nonempty open subset is
dense. -/
theorem irreducibleSpace_iff_forall_dense_open [Nonempty X] :
    IrreducibleSpace X ↔ ∀ ⦃U : Set X⦄, IsOpen U → U.Nonempty → Dense U := by
  refine ⟨fun _ U hU hne => dense_of_nonempty_isOpen hU hne, fun h => ?_⟩
  have hpre : PreirreducibleSpace X := (preirreducibleSpace_iff_open_dense X).mpr h
  exact { toPreirreducibleSpace := hpre, toNonempty := inferInstance }

/-! ## 6. A relative version, for use in later exercises

The same argument applies to a nonempty relatively open piece `Y ∩ U` of an irreducible
set `Y`: it is irreducible and dense in `Y`.  (Hartshorne uses this form in Exercise
I.1.10: "`Xᵢ ∩ U` is irreducible and dense in `Xᵢ`".) -/

/-- If `Y` is irreducible and `U` is open with `Y ∩ U ≠ ∅`, then `Y ∩ U` is dense in `Y`:
`Y ⊆ closure (Y ∩ U)`. -/
theorem subset_closure_inter_of_isIrreducible {Y U : Set X} (hY : IsIrreducible Y)
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) : Y ⊆ closure (Y ∩ U) :=
  subset_closure_inter_of_isPreirreducible_of_isOpen hY.isPreirreducible hU hne

/-- If `Y` is irreducible and `U` is open with `Y ∩ U ≠ ∅`, then `Y ∩ U` is irreducible. -/
theorem isIrreducible_inter_of_isIrreducible {Y U : Set X} (hY : IsIrreducible Y)
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) : IsIrreducible (Y ∩ U) := by
  refine ⟨hne, ?_⟩
  intro u v hu hv h1 h2
  -- `U ∩ u` and `U ∩ v` are nonempty open subsets of `Y`, hence meet inside `Y`
  have h1' : (Y ∩ (U ∩ u)).Nonempty :=
    h1.mono (by rintro y ⟨⟨hyY, hyU⟩, hyu⟩; exact ⟨hyY, hyU, hyu⟩)
  have h2' : (Y ∩ (U ∩ v)).Nonempty :=
    h2.mono (by rintro y ⟨⟨hyY, hyU⟩, hyv⟩; exact ⟨hyY, hyU, hyv⟩)
  obtain ⟨x, hx⟩ :=
    hY.isPreirreducible (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv) h1' h2'
  exact ⟨x, by simp only [Set.mem_inter_iff] at hx ⊢; tauto⟩

/-- Relative version, both conclusions: a nonempty relatively open piece of an irreducible
set is irreducible and dense in it. -/
theorem isIrreducible_and_subset_closure_inter {Y U : Set X} (hY : IsIrreducible Y)
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    IsIrreducible (Y ∩ U) ∧ Y ⊆ closure (Y ∩ U) :=
  ⟨isIrreducible_inter_of_isIrreducible hY hU hne,
    subset_closure_inter_of_isIrreducible hY hU hne⟩

/-! ## 7. Sanity checks: the statement is non-vacuous and its hypotheses are sharp -/

/-- **Non-vacuity.**  The cofinite topology on `ℕ` is irreducible, and `ℕ \ {0}` is a
nonempty open subset of it, so part (a) genuinely applies and yields that `ℕ \ {0}` is
dense and irreducible. -/
theorem instance_cofinite_nat :
    Dense ({x : CofiniteTopology ℕ | x ≠ CofiniteTopology.of 0}) ∧
      IsIrreducible ({x : CofiniteTopology ℕ | x ≠ CofiniteTopology.of 0}) := by
  have hopen : IsOpen ({x : CofiniteTopology ℕ | x ≠ CofiniteTopology.of 0}) := by
    rw [CofiniteTopology.isOpen_iff']
    right
    simp
  have hne : ({x : CofiniteTopology ℕ | x ≠ CofiniteTopology.of 0}).Nonempty :=
    ⟨CofiniteTopology.of 1, by simp⟩
  exact dense_and_isIrreducible_of_nonempty_isOpen hopen hne

/-- **Nonemptiness is needed** in part (a) for the irreducibility conclusion: Hartshorne's
convention is that the empty set is not irreducible. -/
theorem not_isIrreducible_empty : ¬ IsIrreducible (∅ : Set X) := by
  intro h
  obtain ⟨x, hx⟩ := h.nonempty
  exact hx

/-- **Nonemptiness is needed** in part (a) for the density conclusion (in a nonempty
space). -/
theorem not_dense_empty [Nonempty X] : ¬ Dense (∅ : Set X) := by
  intro h
  rw [dense_iff_closure_eq, closure_empty] at h
  have : Classical.arbitrary X ∈ (∅ : Set X) := h ▸ mem_univ _
  exact this

/-- **Openness is needed** in part (a): in the irreducible space `CofiniteTopology ℕ` the
nonempty subset `{0, 1}` is not open and is neither dense nor irreducible. -/
theorem exists_nonempty_not_open_not_dense_not_irreducible :
    ∃ U : Set (CofiniteTopology ℕ), U.Nonempty ∧ ¬ IsOpen U ∧ ¬ Dense U ∧ ¬ IsIrreducible U := by
  refine ⟨{CofiniteTopology.of 0, CofiniteTopology.of 1},
    ⟨CofiniteTopology.of 0, by simp⟩, ?_, ?_, ?_⟩
  · -- not open: its complement is infinite
    intro hop
    rw [CofiniteTopology.isOpen_iff'] at hop
    have hinf :
        ({CofiniteTopology.of 0, CofiniteTopology.of 1}ᶜ : Set (CofiniteTopology ℕ)).Infinite :=
      Set.infinite_of_injective_forall_mem (f := fun n : ℕ => CofiniteTopology.of (n + 2))
        (fun _ _ h => by simpa using h) (fun n => by simp)
    rcases hop with h | h
    · have hmem : (CofiniteTopology.of 0) ∈
          ({CofiniteTopology.of 0, CofiniteTopology.of 1} : Set (CofiniteTopology ℕ)) := by simp
      rw [h] at hmem
      exact hmem
    · exact hinf h
  · -- not dense: it is closed and not everything
    intro hd
    have hcl : IsClosed ({CofiniteTopology.of 0, CofiniteTopology.of 1} :
        Set (CofiniteTopology ℕ)) := by
      rw [CofiniteTopology.isClosed_iff]; right; simp
    rw [dense_iff_closure_eq, hcl.closure_eq] at hd
    have hmem : CofiniteTopology.of 2 ∈
        ({CofiniteTopology.of 0, CofiniteTopology.of 1} : Set (CofiniteTopology ℕ)) :=
      hd ▸ mem_univ _
    simp at hmem
  · -- not irreducible: it is the union of the two closed points `{0}` and `{1}`
    intro h
    have hcl0 : IsClosed ({CofiniteTopology.of 0} : Set (CofiniteTopology ℕ)) := by
      rw [CofiniteTopology.isClosed_iff]; right; simp
    have hcl1 : IsClosed ({CofiniteTopology.of 1} : Set (CofiniteTopology ℕ)) := by
      rw [CofiniteTopology.isClosed_iff]; right; simp
    have hcov : ({CofiniteTopology.of 0, CofiniteTopology.of 1} : Set (CofiniteTopology ℕ)) ⊆
        ({CofiniteTopology.of 0} : Set _) ∪ {CofiniteTopology.of 1} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at hx ⊢
      tauto
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp h.isPreirreducible)
      _ _ hcl0 hcl1 hcov with h0 | h1
    · have hmem : CofiniteTopology.of 1 ∈ ({CofiniteTopology.of 0} : Set _) := h0 (by simp)
      simp at hmem
    · have hmem : CofiniteTopology.of 0 ∈ ({CofiniteTopology.of 1} : Set _) := h1 (by simp)
      simp at hmem

/-! ## 8. Axiom check -/

#print axioms nonempty_inter_of_isOpen
#print axioms nonempty_inter_of_isOpen_of_preirreducible
#print axioms not_disjoint_of_isOpen
#print axioms dense_of_nonempty_isOpen
#print axioms closure_eq_univ_of_nonempty_isOpen
#print axioms isIrreducible_of_nonempty_isOpen
#print axioms irreducibleSpace_of_nonempty_isOpen
#print axioms dense_and_isIrreducible_of_nonempty_isOpen
#print axioms isIrreducible_closure
#print axioms isIrreducible_closure_iff
#print axioms irreducibleSpace_closure
#print axioms isIrreducible_closure_of_irreducibleSpace
#print axioms hartshorne_ex_1_6
#print axioms hartshorne_ex_1_6_subspace
#print axioms preirreducibleSpace_iff_forall_dense_open
#print axioms irreducibleSpace_iff_forall_dense_open
#print axioms subset_closure_inter_of_isIrreducible
#print axioms isIrreducible_inter_of_isIrreducible
#print axioms isIrreducible_and_subset_closure_inter
#print axioms instance_cofinite_nat
#print axioms not_isIrreducible_empty
#print axioms not_dense_empty
#print axioms exists_nonempty_not_open_not_dense_not_irreducible

end Hartshorne77.Ex_I_1_6
