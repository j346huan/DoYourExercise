/-
Copyright (c) 2026 Hartshorne formalization campaign. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: m7
-/
import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Exercise I.1.7

`X` is an arbitrary topological space.  Hartshorne defines (Definition 1.4.6) `X` to be
*noetherian* if it satisfies the descending chain condition on closed subsets.  Exercise I.1.7
asks for the following.

(a) The following conditions are equivalent:
  (i)   `X` is noetherian (descending chain condition on closed subsets);
  (ii)  every nonempty family of closed subsets has a minimal element;
  (iii) `X` satisfies the ascending chain condition for open subsets;
  (iv)  every nonempty family of open subsets has a maximal element.
(b) A noetherian topological space is quasi-compact, i.e. every open cover has a finite
    subcover.
(c) Any subset of a noetherian topological space is noetherian in its induced topology.
(d) A noetherian topological space which is also Hausdorff is a finite set with the discrete
    topology.

The statements are formalised literally, point-set, without assuming compactness, finiteness or
discreteness.  The proof of (a) is the standard one: the equivalences (i) ↔ (iii) and
(ii) ↔ (iv) are complementation, while (i) ↔ (ii) and (iii) ↔ (iv) use the fact that a family
without a minimal (respectively maximal) member contains a strictly decreasing (respectively
increasing) sequence.  Part (b) is proved from (a)(iv) by taking a maximal element among the
finite unions of members of the cover (it yields the stronger statement that every subset of a
noetherian space is compact); part (c) transfers the minimal-element condition (a)(ii) to the
family of ambient closed sets whose trace lies in a given family of closed sets of the subspace;
part (d) shows that every subset of a noetherian Hausdorff space is closed (using compactness of
subsets) and reads off finiteness from a finite subcover of the cover by singletons.

The exercise is a statement about an arbitrary topological space: no algebraically closed field
`k`, no variety and no irreducibility or nonvanishing hypothesis occurs in it, so none has been
dropped.  Conversely no compactness, finiteness or discreteness is assumed.

Finally, `dcc_iff_noetherianSpace` records that condition (i) is exactly Mathlib's
`TopologicalSpace.NoetherianSpace` (defined as `WellFoundedGT (Opens X)`, i.e. the ascending chain
condition on open sets), which certifies that the notion of a noetherian space formalised here is
the standard one.

## Source of the statement

The transcription `.scratch/reference/hartshorne-1977.txt` of the 1977 text is defective: it omits
the entire exercise list of Chapter I, §1.  The statement was therefore transcribed from the book
scan and cross-checked against an independent solutions transcript
(`hartshorne-ag-solutions.wikidot.com/chapter-1-section-1`); the wording of (a)–(d) above is
verbatim in content and the order of (i)–(iv) is the book's.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter I, §1, Definition 1.4.6 and
  Exercise 1.7.
-/

namespace Hartshorne77.Ex_I_1_7

open Set

universe u

/-! ### Order-theoretic preparation

A family of sets with no minimal member contains a strictly decreasing sequence (and dually). -/

section Chains

variable {X : Type u}

/-- If every member of a nonempty family `F` of sets strictly contains a further member of `F`,
then `F` contains a strictly decreasing sequence. -/
theorem exists_strictAnti_of_forall_exists_ssubset {F : Set (Set X)} (hF : F.Nonempty)
    (h : ∀ a ∈ F, ∃ b ∈ F, b ⊂ a) :
    ∃ Y : ℕ → Set X, (∀ n, Y n ∈ F) ∧ StrictAnti Y := by
  classical
  obtain ⟨a₀, ha₀⟩ := hF
  -- a choice function picking a strictly smaller member of `F`
  let g : Set X → Set X := fun a => if ha : a ∈ F then Classical.choose (h a ha) else a
  have hg_mem : ∀ a ∈ F, g a ∈ F := by
    intro a ha
    have hg : g a = Classical.choose (h a ha) := by simp only [g, dif_pos ha]
    rw [hg]
    exact (Classical.choose_spec (h a ha)).1
  have hg_ssubset : ∀ a ∈ F, g a ⊂ a := by
    intro a ha
    have hg : g a = Classical.choose (h a ha) := by simp only [g, dif_pos ha]
    rw [hg]
    exact (Classical.choose_spec (h a ha)).2
  have hmem : ∀ n, (g^[n]) a₀ ∈ F := by
    intro n
    induction n with
    | zero => simpa using ha₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hg_mem _ ih
  exact ⟨fun n => (g^[n]) a₀, hmem, strictAnti_nat_of_succ_lt fun n => by
    rw [Function.iterate_succ_apply']
    exact hg_ssubset _ (hmem n)⟩

/-- If every member of a nonempty family `F` of sets is strictly contained in a further member
of `F`, then `F` contains a strictly increasing sequence. -/
theorem exists_strictMono_of_forall_exists_ssubset {F : Set (Set X)} (hF : F.Nonempty)
    (h : ∀ a ∈ F, ∃ b ∈ F, a ⊂ b) :
    ∃ U : ℕ → Set X, (∀ n, U n ∈ F) ∧ StrictMono U := by
  classical
  obtain ⟨a₀, ha₀⟩ := hF
  let g : Set X → Set X := fun a => if ha : a ∈ F then Classical.choose (h a ha) else a
  have hg_mem : ∀ a ∈ F, g a ∈ F := by
    intro a ha
    have hg : g a = Classical.choose (h a ha) := by simp only [g, dif_pos ha]
    rw [hg]
    exact (Classical.choose_spec (h a ha)).1
  have hg_ssubset : ∀ a ∈ F, a ⊂ g a := by
    intro a ha
    have hg : g a = Classical.choose (h a ha) := by simp only [g, dif_pos ha]
    rw [hg]
    exact (Classical.choose_spec (h a ha)).2
  have hmem : ∀ n, (g^[n]) a₀ ∈ F := by
    intro n
    induction n with
    | zero => simpa using ha₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hg_mem _ ih
  exact ⟨fun n => (g^[n]) a₀, hmem, strictMono_nat_of_lt_succ fun n => by
    rw [Function.iterate_succ_apply']
    exact hg_ssubset _ (hmem n)⟩

/-- The family of finite unions of members of a fixed family `U` of subsets is closed under
adjoining one further member. -/
theorem finiteUnion_mem_insert {ι : Type u} (U : ι → Set X) {u : Set X}
    (hu : ∃ T : Finset ι, u = ⋃ i ∈ T, U i) (i : ι) :
    ∃ T : Finset ι, u ∪ U i = ⋃ j ∈ T, U j := by
  classical
  obtain ⟨T, rfl⟩ := hu
  exact ⟨insert i T, by rw [Finset.set_biUnion_insert, union_comm]⟩

end Chains

variable {X : Type u} [TopologicalSpace X]

/-! ### The four conditions of part (a) -/

/-- **(a)(i)** (Definition 1.4.6): `X` satisfies the descending chain condition for closed
subsets: every antitone sequence of closed subsets of `X` is eventually constant. -/
def DescendingChainConditionClosed (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ Y : ℕ → Set X, (∀ n, IsClosed (Y n)) → Antitone Y → ∃ r, ∀ n, r ≤ n → Y n = Y r

/-- **(a)(ii)**: every nonempty family of closed subsets of `X` has a minimal element. -/
def EveryNonemptyClosedFamilyHasMinimal (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ F : Set (Set X), F.Nonempty → (∀ s ∈ F, IsClosed s) →
    ∃ m ∈ F, ∀ s ∈ F, s ⊆ m → m ⊆ s

/-- **(a)(iii)**: `X` satisfies the ascending chain condition for open subsets. -/
def AscendingChainConditionOpen (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → Monotone U → ∃ r, ∀ n, r ≤ n → U n = U r

/-- **(a)(iv)**: every nonempty family of open subsets of `X` has a maximal element. -/
def EveryNonemptyOpenFamilyHasMaximal (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ F : Set (Set X), F.Nonempty → (∀ s ∈ F, IsOpen s) →
    ∃ m ∈ F, ∀ s ∈ F, m ⊆ s → s ⊆ m

/-! ### (a): the four conditions are equivalent -/

/-- **(a): (i) ↔ (ii).** -/
theorem dcc_iff_minimal_closed :
    DescendingChainConditionClosed X ↔ EveryNonemptyClosedFamilyHasMinimal X := by
  constructor
  · -- (i) → (ii): a family without a minimal member yields a strictly decreasing sequence.
    intro hX F hF hFc
    by_contra hmin
    have hno : ∀ a ∈ F, ∃ b ∈ F, b ⊂ a := by
      intro a ha
      by_contra hnab
      apply hmin
      refine ⟨a, ha, ?_⟩
      intro s hs hsa
      by_contra hnot
      exact hnab ⟨s, hs, ⟨hsa, hnot⟩⟩
    obtain ⟨Y, hYF, hYanti⟩ := exists_strictAnti_of_forall_exists_ssubset hF hno
    obtain ⟨r, hr⟩ := hX Y (fun n => hFc _ (hYF n)) hYanti.antitone
    have h₁ : Y (r + 1) = Y r := hr (r + 1) (Nat.le_succ r)
    have h₂ : Y (r + 1) ⊂ Y r := hYanti (Nat.lt_succ_self r)
    exact h₂.2 (by rw [h₁])
  · -- (ii) → (i): the members of a non-stabilising chain have no minimal member.
    intro hF Y hYc hYanti
    by_contra hstab
    simp only [not_exists, not_forall] at hstab
    obtain ⟨m, hmF, hmin⟩ := hF (Set.range Y) ⟨Y 0, Set.mem_range_self 0⟩
      (fun s hs => by obtain ⟨n, rfl⟩ := hs; exact hYc n)
    obtain ⟨r, rfl⟩ := hmF
    obtain ⟨n, hrn, hne⟩ := hstab r
    exact hne (le_antisymm (hYanti hrn) (hmin (Y n) (Set.mem_range_self n) (hYanti hrn)))

/-- **(a): (iii) ↔ (iv).** -/
theorem acc_iff_maximal_open :
    AscendingChainConditionOpen X ↔ EveryNonemptyOpenFamilyHasMaximal X := by
  constructor
  · -- (iii) → (iv)
    intro hX F hF hFo
    by_contra hmax
    have hno : ∀ a ∈ F, ∃ b ∈ F, a ⊂ b := by
      intro a ha
      by_contra hnab
      apply hmax
      refine ⟨a, ha, ?_⟩
      intro s hs has
      by_contra hnot
      exact hnab ⟨s, hs, ⟨has, hnot⟩⟩
    obtain ⟨U, hUF, hUmono⟩ := exists_strictMono_of_forall_exists_ssubset hF hno
    obtain ⟨r, hr⟩ := hX U (fun n => hFo _ (hUF n)) hUmono.monotone
    have h₁ : U (r + 1) = U r := hr (r + 1) (Nat.le_succ r)
    have h₂ : U r ⊂ U (r + 1) := hUmono (Nat.lt_succ_self r)
    exact h₂.2 (by rw [h₁])
  · -- (iv) → (iii)
    intro hF U hUo hUmono
    by_contra hstab
    simp only [not_exists, not_forall] at hstab
    obtain ⟨m, hmF, hmax⟩ := hF (Set.range U) ⟨U 0, Set.mem_range_self 0⟩
      (fun s hs => by obtain ⟨n, rfl⟩ := hs; exact hUo n)
    obtain ⟨r, rfl⟩ := hmF
    obtain ⟨n, hrn, hne⟩ := hstab r
    exact hne (le_antisymm (hmax (U n) (Set.mem_range_self n) (hUmono hrn)) (hUmono hrn))

/-- **(a): (i) ↔ (iii)**, by taking complements. -/
theorem dcc_iff_acc :
    DescendingChainConditionClosed X ↔ AscendingChainConditionOpen X := by
  constructor
  · intro hX U hUo hUmono
    obtain ⟨r, hr⟩ := hX (fun n => (U n)ᶜ) (fun n => (hUo n).isClosed_compl)
      (fun m n hmn => compl_subset_compl.mpr (hUmono hmn))
    exact ⟨r, fun n hn => compl_inj_iff.mp (hr n hn)⟩
  · intro hX Y hYc hYanti
    obtain ⟨r, hr⟩ := hX (fun n => (Y n)ᶜ) (fun n => (hYc n).isOpen_compl)
      (fun m n hmn => compl_subset_compl.mpr (hYanti hmn))
    exact ⟨r, fun n hn => compl_inj_iff.mp (hr n hn)⟩

/-- **(a): (ii) ↔ (iv)**, by taking complements. -/
theorem minimal_closed_iff_maximal_open :
    EveryNonemptyClosedFamilyHasMinimal X ↔ EveryNonemptyOpenFamilyHasMaximal X := by
  constructor
  · intro hF G hG hGo
    obtain ⟨m, hmG, hmin⟩ := hF (compl '' G) (hG.image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact (hGo s hs).isClosed_compl)
    obtain ⟨s, hsG, rfl⟩ := hmG
    refine ⟨s, hsG, ?_⟩
    intro t htG hst
    have hcompl : tᶜ ∈ compl '' G := ⟨t, htG, rfl⟩
    have hsub : tᶜ ⊆ sᶜ := compl_subset_compl.mpr hst
    exact compl_subset_compl.mp (hmin tᶜ hcompl hsub)
  · intro hF G hG hGc
    obtain ⟨m, hmG, hmax⟩ := hF (compl '' G) (hG.image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact (hGc s hs).isOpen_compl)
    obtain ⟨s, hsG, rfl⟩ := hmG
    refine ⟨s, hsG, ?_⟩
    intro t htG hts
    have hcompl : tᶜ ∈ compl '' G := ⟨t, htG, rfl⟩
    have hsub : sᶜ ⊆ tᶜ := compl_subset_compl.mpr hts
    exact compl_subset_compl.mp (hmax tᶜ hcompl hsub)

/-- **(a): (i) ↔ (iv).** -/
theorem dcc_iff_maximal_open :
    DescendingChainConditionClosed X ↔ EveryNonemptyOpenFamilyHasMaximal X :=
  dcc_iff_minimal_closed.trans minimal_closed_iff_maximal_open

/-- **Exercise I.1.7 (a).** For a topological space `X` the following four conditions are
equivalent: (i) the descending chain condition for closed subsets; (ii) every nonempty family of
closed subsets has a minimal element; (iii) the ascending chain condition for open subsets;
(iv) every nonempty family of open subsets has a maximal element. -/
theorem exercise_a :
    (DescendingChainConditionClosed X ↔ EveryNonemptyClosedFamilyHasMinimal X) ∧
    (EveryNonemptyClosedFamilyHasMinimal X ↔ AscendingChainConditionOpen X) ∧
    (AscendingChainConditionOpen X ↔ EveryNonemptyOpenFamilyHasMaximal X) ∧
    (DescendingChainConditionClosed X ↔ EveryNonemptyOpenFamilyHasMaximal X) :=
  ⟨dcc_iff_minimal_closed, dcc_iff_minimal_closed.symm.trans dcc_iff_acc,
    acc_iff_maximal_open, dcc_iff_maximal_open⟩

/-! ### (b): a noetherian space is quasi-compact -/

/-- **(b)**, in the form used below: in a noetherian space every subset is quasi-compact, i.e.
every cover by open sets has a finite subcover. -/
theorem isCompact_of_dcc (hX : DescendingChainConditionClosed X) (s : Set X) : IsCompact s := by
  classical
  have hmax : EveryNonemptyOpenFamilyHasMaximal X := dcc_iff_maximal_open.mp hX
  refine isCompact_of_finite_subcover fun {ι : Type u} U hUo hsU => ?_
  -- the family of finite unions of members of the cover
  obtain ⟨m, hmF, hmaxm⟩ := hmax {u : Set X | ∃ T : Finset ι, u = ⋃ i ∈ T, U i}
    ⟨∅, ∅, by simp⟩ (by rintro u ⟨T, rfl⟩; exact isOpen_biUnion fun i _ => hUo i)
  -- the maximal member contains every member of the cover, hence contains `s`
  have hUi : ∀ i, U i ⊆ m := by
    intro i
    exact (union_subset_iff.mp (hmaxm (m ∪ U i) (finiteUnion_mem_insert U hmF i)
      subset_union_left)).2
  obtain ⟨T, rfl⟩ := hmF
  exact ⟨T, hsU.trans (iUnion_subset hUi)⟩

/-- **Exercise I.1.7 (b).** A noetherian topological space is quasi-compact, i.e. every open
cover has a finite subcover. -/
theorem exercise_b (hX : DescendingChainConditionClosed X) : CompactSpace X :=
  ⟨by simpa using isCompact_of_dcc hX univ⟩

/-! ### (c): subspaces of noetherian spaces are noetherian -/

/-- **(c)**, in the form (ii): the condition that every nonempty family of closed sets has a
minimal element passes to subspaces. -/
theorem minimal_closed_subspace (hX : EveryNonemptyClosedFamilyHasMinimal X) (Y : Set X) :
    EveryNonemptyClosedFamilyHasMinimal Y := by
  classical
  intro G hG hGc
  -- closed sets of the subspace are traces of closed sets of `X`
  have hrep : ∀ W ∈ G, ∃ F : Set X, IsClosed F ∧ Subtype.val ⁻¹' F = W :=
    fun W hW => isClosed_induced_iff.mp (hGc W hW)
  choose F hFc hFW using hrep
  -- the family of all closed sets of `X` whose trace lies in `G`
  obtain ⟨W₀, hW₀⟩ := hG
  obtain ⟨F₀, hF₀, hmin⟩ := hX {F : Set X | IsClosed F ∧ Subtype.val ⁻¹' F ∈ G}
    ⟨F W₀ hW₀, hFc W₀ hW₀, by rw [hFW W₀ hW₀]; exact hW₀⟩
    (fun F hF => hF.1)
  refine ⟨Subtype.val ⁻¹' F₀, hF₀.2, ?_⟩
  intro W hW hsub
  obtain ⟨F₁, hF₁c, hF₁W⟩ := isClosed_induced_iff.mp (hGc W hW)
  have hmem : IsClosed (F₀ ∩ F₁) ∧ Subtype.val ⁻¹' (F₀ ∩ F₁) ∈ G := by
    refine ⟨hF₀.1.inter hF₁c, ?_⟩
    rw [preimage_inter, hF₁W, inter_eq_right.mpr hsub]
    exact hW
  have hle : F₀ ⊆ F₀ ∩ F₁ := hmin (F₀ ∩ F₁) hmem inter_subset_left
  rw [← hF₁W]
  exact (preimage_mono hle).trans (by rw [preimage_inter]; exact inter_subset_right)

/-- **Exercise I.1.7 (c).** Any subset of a noetherian topological space is noetherian in its
induced topology. -/
theorem exercise_c (hX : DescendingChainConditionClosed X) (Y : Set X) :
    DescendingChainConditionClosed Y :=
  dcc_iff_minimal_closed.mpr (minimal_closed_subspace (dcc_iff_minimal_closed.mp hX) Y)

/-! ### (d): a noetherian Hausdorff space is finite and discrete -/

/-- **Exercise I.1.7 (d).** A noetherian topological space which is also Hausdorff is a finite set
with the discrete topology. -/
theorem exercise_d (hX : DescendingChainConditionClosed X) [T2Space X] :
    Finite X ∧ DiscreteTopology X := by
  classical
  -- every subset of a noetherian Hausdorff space is closed
  have hall : ∀ s : Set X, IsClosed s := by
    intro s
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    -- for `y ∈ s` and `x ∉ s`, separate `y` from `x` by disjoint open sets
    choose U V hUo hVo hyU hxV hUV using fun y : s =>
      t2_separation (show (y : X) ≠ x from fun h => hx (h ▸ y.2))
    -- the `U y` cover the compact set `s`
    obtain ⟨t, ht⟩ := (isCompact_of_dcc hX s).elim_finite_subcover U (fun y => hUo y)
      (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩)
    refine ⟨⋂ y ∈ t, V y, ?_, isOpen_biInter_finset fun y _ => hVo y, mem_iInter₂.mpr fun y _ => hxV y⟩
    intro z hz hzs
    obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.mp (ht hzs)
    exact disjoint_left.mp (hUV y) hzy (mem_iInter₂.mp hz y hyt)
  refine ⟨?_, discreteTopology_iff_forall_isClosed.mpr hall⟩
  -- the singleton open cover of the compact space `X` has a finite subcover
  obtain ⟨t, ht⟩ := (isCompact_of_dcc hX univ).elim_finite_subcover (fun x : X => ({x} : Set X))
    (fun x => by simpa using (hall {x}ᶜ).isOpen_compl)
    (fun x _ => mem_iUnion.mpr ⟨x, rfl⟩)
  exact Finite.of_finite_univ ((t.finite_toSet.biUnion fun x _ => Set.finite_singleton x).subset
    fun x _ => ht (mem_univ x))


/-! ### Compatibility with Mathlib's `TopologicalSpace.NoetherianSpace` -/

/-- Condition (a)(i) is Mathlib's `TopologicalSpace.NoetherianSpace`, which is defined as
`WellFoundedGT (Opens X)` (equivalently, `noetherianSpace_iff_opens`: every open subset is
compact).  This is recorded to certify that the notion of a noetherian space formalised above is
the standard one. -/
theorem dcc_iff_noetherianSpace :
    DescendingChainConditionClosed X ↔ TopologicalSpace.NoetherianSpace X := by
  rw [TopologicalSpace.noetherianSpace_iff_opens]
  constructor
  · intro h s
    exact isCompact_of_dcc h s
  · intro h
    rw [dcc_iff_acc]
    intro U hUo hUmono
    have hcomp : IsCompact (⋃ n, U n) := h ⟨⋃ n, U n, isOpen_iUnion hUo⟩
    obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover U hUo subset_rfl
    refine ⟨t.sup id, fun n hn => ?_⟩
    have h₂ : (⋃ i ∈ t, U i) ⊆ U (t.sup id) :=
      Set.iUnion₂_subset fun i hi => hUmono (Finset.le_sup (f := id) hi)
    exact ((Set.subset_iUnion U n).trans (ht.trans h₂)).antisymm (hUmono hn)


/-! ### Cross-checks against Mathlib's `NoetherianSpace` API

These are proved again from Mathlib's theorems about its own notion of a noetherian space,
independently of the direct proofs above, as a check that the statements of (b), (c) and (d) are
the standard ones. -/

theorem crosscheck_b (hX : DescendingChainConditionClosed X) : CompactSpace X :=
  @TopologicalSpace.NoetherianSpace.compactSpace X _ (dcc_iff_noetherianSpace.mp hX)

theorem crosscheck_c (hX : DescendingChainConditionClosed X) (Y : Set X) :
    DescendingChainConditionClosed Y :=
  dcc_iff_noetherianSpace.mpr
    (@TopologicalSpace.NoetherianSpace.set X _ (dcc_iff_noetherianSpace.mp hX) Y)

theorem crosscheck_d (hX : DescendingChainConditionClosed X) [T2Space X] :
    Finite X ∧ DiscreteTopology X :=
  ⟨@TopologicalSpace.NoetherianSpace.finite X _ (dcc_iff_noetherianSpace.mp hX) _,
    @TopologicalSpace.NoetherianSpace.discrete X _ (dcc_iff_noetherianSpace.mp hX) _⟩

/-! ### Axiom dependencies

Every declaration above depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. -/

#print axioms Hartshorne77.Ex_I_1_7.exists_strictAnti_of_forall_exists_ssubset
#print axioms Hartshorne77.Ex_I_1_7.exists_strictMono_of_forall_exists_ssubset
#print axioms Hartshorne77.Ex_I_1_7.finiteUnion_mem_insert
#print axioms Hartshorne77.Ex_I_1_7.dcc_iff_minimal_closed
#print axioms Hartshorne77.Ex_I_1_7.acc_iff_maximal_open
#print axioms Hartshorne77.Ex_I_1_7.dcc_iff_acc
#print axioms Hartshorne77.Ex_I_1_7.minimal_closed_iff_maximal_open
#print axioms Hartshorne77.Ex_I_1_7.dcc_iff_maximal_open
#print axioms Hartshorne77.Ex_I_1_7.exercise_a
#print axioms Hartshorne77.Ex_I_1_7.isCompact_of_dcc
#print axioms Hartshorne77.Ex_I_1_7.exercise_b
#print axioms Hartshorne77.Ex_I_1_7.minimal_closed_subspace
#print axioms Hartshorne77.Ex_I_1_7.exercise_c
#print axioms Hartshorne77.Ex_I_1_7.exercise_d
#print axioms Hartshorne77.Ex_I_1_7.dcc_iff_noetherianSpace
#print axioms Hartshorne77.Ex_I_1_7.crosscheck_b
#print axioms Hartshorne77.Ex_I_1_7.crosscheck_c
#print axioms Hartshorne77.Ex_I_1_7.crosscheck_d

end Hartshorne77.Ex_I_1_7
