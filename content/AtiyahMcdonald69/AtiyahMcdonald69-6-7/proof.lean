/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter 6 "Chain Conditions", Exercise 7.

Natural-language solution used as a reference:
  https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-7

## The exercise

The notion is introduced in Chapter 6, Exercise 5 of the book:

  "A topological space `X` is said to be *Noetherian* if the open subsets of `X` satisfy the
   ascending chain condition (or, equivalently, the maximal condition). Since closed subsets
   are complements of open subsets, it comes to the same thing to say that the closed subsets
   of `X` satisfy the descending chain condition (or, equivalently, the minimal condition)."

Chapter 6, Exercise 7 then reads:

  "A Noetherian space is a finite union of irreducible closed subspaces. Hence the set of
   irreducible components of a Noetherian space is finite."

*Irreducible* is Chapter 1, Exercise 19 (the space is nonempty and any two nonempty open
subsets meet); the *irreducible components* are the maximal irreducible subspaces, which are
closed (Chapter 1, Exercise 20).

## Faithfulness of the formalization

* `NoetherianSpace α` is Mathlib's `WellFoundedGT (Opens α)`, i.e. the *maximal condition* on
  open subsets, which is verbatim the book's definition. The lemma
  `noetherian_iff_closeds_dcc` records the equivalence with the descending chain (minimal)
  condition on closed subsets, which is the form in which the book applies it.
* `IsIrreducible s` is Mathlib's rendering of "the subspace `s` is irreducible": `s` is
  nonempty and any two open sets meeting `s` meet each other inside `s` — the book's condition.
* `irreducibleComponents α` is Mathlib's `{s | Maximal IsIrreducible s}`, precisely the set of
  maximal irreducible subspaces of Chapter 1, Exercise 20.

Both assertions are proved below: `exists_finite_irreducible_closed_cover` (first sentence) and
`irreducibleComponents_finite` (the "hence"). `solution` packages the two of them.

## Source audit

The reference proof is correct and no hypothesis is missing (the argument is the standard
minimal-counterexample one, and it is the book's own proof). Two steps are left implicit there
and are made explicit below:

* the minimal closed set `Y` that is not a finite union of irreducible closed subsets is
  nonempty, because `∅` *is* such a union, namely the empty one (`⋃₀ ∅ = ∅`); this is what
  lets one apply reducibility, which for the empty set would fail since `∅` is not irreducible;
* the two proper closed subsets produced by reducibility are strictly smaller than `Y`, which
  is what makes the minimality hypothesis applicable.

The conclusion "hence finitely many irreducible components" uses that an irreducible set
contained in a finite union of closed sets is contained in one of them
(`isIrreducible_iff_sUnion_isClosed`) and that irreducible components are the *maximal*
irreducible subsets (Chapter 1, Exercise 20), so that containment forces equality.

The argument is carried out for an arbitrary closed subset (`..._of_isClosed`), which is the
form in which the book reuses it (e.g. in Exercise 6.11), and specialised to `X` itself. Both
`IsIrreducible s` and the subspace reading `IrreducibleSpace s` are provided.
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible

open Topology TopologicalSpace

namespace AtiyahMcdonald69.Ex_6_7

variable {α : Type*} [TopologicalSpace α]

/-! ### The notion of a Noetherian space -/

/-- Chapter 6, Exercise 5: the ascending chain (= maximal) condition on the open subsets, which
is the book's definition of a Noetherian space, is equivalent to the descending chain
(= minimal) condition on the closed subsets. -/
theorem noetherian_iff_closeds_dcc :
    NoetherianSpace α ↔ WellFoundedLT (Closeds α) :=
  (TopologicalSpace.noetherianSpace_TFAE α).out 0 1

/-! ### The first assertion: a Noetherian space is a finite union of irreducible closed sets

The proof is the book's minimal-counterexample argument, run as a well-founded induction on
the closed subsets (the descending chain condition supplies the minimal element). -/

/-- The union of a finite family of closed subsets is the supremum of that family in
`Closeds α`. -/
theorem coe_finset_sup_eq_iUnion (S : Finset (Closeds α)) :
    ((S.sup id : Closeds α) : Set α) = ⋃ u ∈ (S : Set (Closeds α)), (u : Set α) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => simp [Finset.sup_insert, ih, Closeds.coe_sup]

/-- Every closed subset of a Noetherian space is a finite union of irreducible closed
subsets, in the form of a finite family of elements of `Closeds α`. -/
theorem exists_finset_irreducible_closeds [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ t ∈ S, IsIrreducible (t : Set α)) ∧ s = S.sup id := by
  classical
  apply wellFounded_lt.induction s
  clear s
  intro s IH
  rcases eq_or_ne s ⊥ with rfl | h₀
  · -- the empty closed set is the empty union
    exact ⟨∅, by simp⟩
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · -- an irreducible closed set is the union of the one-member family consisting of itself
      refine ⟨{s}, ?_, by simp⟩
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
    · -- a reducible closed set splits into two strictly smaller closed subsets
      simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases IH (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hS₁, h₁⟩
      rcases IH (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hS₂, h₂⟩
      refine ⟨S₁ ∪ S₂, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_union.1 ht with h' | h'
        · exact hS₁ t h'
        · exact hS₂ t h'
      · rw [Finset.sup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]
        rw [← SetLike.coe_subset_coe, Closeds.coe_sup]
        exact h

/-- The argument of the first assertion, in the form in which the book's minimal
counterexample runs: *every* closed subset of a Noetherian space is a finite union of
irreducible closed subsets. -/
theorem exists_finite_irreducible_closed_cover_of_isClosed [NoetherianSpace α] {Z : Set α}
    (hZ : IsClosed Z) :
    ∃ S : Set (Set α), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
      ⋃₀ S = Z := by
  obtain ⟨S, hS, htop⟩ := exists_finset_irreducible_closeds (α := α) ⟨Z, hZ⟩
  refine ⟨(fun u : Closeds α => (u : Set α)) '' (S : Set _), S.finite_toSet.image _, ?_, ?_, ?_⟩
  · rintro t ⟨u, -, rfl⟩
    exact u.2
  · rintro t ⟨u, hu, rfl⟩
    exact hS u (by simpa using hu)
  · calc ⋃₀ ((fun u : Closeds α => (u : Set α)) '' (S : Set (Closeds α)))
        = ⋃ u ∈ (S : Set (Closeds α)), (u : Set α) :=
          Set.sUnion_image (fun u : Closeds α => (u : Set α)) (S : Set (Closeds α))
      _ = ((S.sup id : Closeds α) : Set α) := (coe_finset_sup_eq_iUnion S).symm
      _ = Z := by rw [← htop]; rfl

/-- **Exercise 6.7, first assertion**: a Noetherian space is a finite union of irreducible
closed subspaces. -/
theorem exists_finite_irreducible_closed_cover [NoetherianSpace α] :
    ∃ S : Set (Set α), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
      ⋃₀ S = Set.univ := by
  simpa using
    exists_finite_irreducible_closed_cover_of_isClosed (Z := Set.univ) (isClosed_univ : IsClosed (Set.univ : Set α))

/-- The first assertion read literally with subspaces: `X` is a finite union of closed subsets
which, with the induced topology, are irreducible spaces (Chapter 1, Exercise 19). -/
theorem exists_finite_irreducibleSpace_closed_cover [NoetherianSpace α] :
    ∃ S : Set (Set α), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IrreducibleSpace t) ∧
      ⋃₀ S = Set.univ := by
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ := exists_finite_irreducible_closed_cover (α := α)
  exact ⟨S, hSf, hSc, fun t ht => isIrreducible_iff_irreducibleSpace.1 (hSi t ht), hSU⟩

/-! ### The second assertion: finitely many irreducible components -/

/-- **Exercise 6.7, second assertion**: a Noetherian space has only finitely many irreducible
components. An irreducible set contained in a finite union of closed sets lies in one of them,
and maximality then forces equality. -/
theorem irreducibleComponents_finite [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    exists_finite_irreducible_closed_cover_of_isClosed (Z := Set.univ)
      (isClosed_univ : IsClosed (Set.univ : Set α))
  refine hSf.subset fun Z hZ => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hZ.1 S hSc (hSU.symm ▸ Set.subset_univ _) with
    ⟨t, htS, ht⟩
  rwa [ht.antisymm (hZ.2 (hSi t htS) ht)]

/-- **Exercise 6.7**, both assertions together. -/
theorem solution [NoetherianSpace α] :
    (∃ S : Set (Set α), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
        ⋃₀ S = Set.univ) ∧
      (irreducibleComponents α).Finite :=
  ⟨exists_finite_irreducible_closed_cover, irreducibleComponents_finite⟩

end AtiyahMcdonald69.Ex_6_7
