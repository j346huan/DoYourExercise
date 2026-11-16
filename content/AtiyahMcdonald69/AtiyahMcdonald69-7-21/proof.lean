/-
# Atiyah–Macdonald (1969), Chapter 7, Exercise 21

Source: M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*,
Addison–Wesley, 1969.  Exercise 7.21 (with `F` as in Exercise 7.20):

> Let `X` be a Noetherian space and `E ⊆ X`. Show that `E ∈ F` iff, for each irreducible
> closed `X₀ ⊆ X`, either `Cl(E ∩ X₀) ≠ X₀` or `E ∩ X₀` contains a non-empty open subset of `X₀`.

Exercise 7.20 introduces `F` as the smallest collection of subsets of `X` which contains all
open subsets of `X` and is closed with respect to the formation of finite intersections and
complements.

Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-21
-/
import Mathlib

set_option autoImplicit false

namespace AtiyahMcdonald69.Ex_7_21

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ## The collection `F` of Exercise 7.20

`F` is the smallest collection of subsets of `X` containing all open subsets of `X` and closed
under finite intersections and complements.  Such a collection is closed under finite unions as
well (the union `s ∪ t` is the complement of the intersection of the complements), contains `∅`
and `univ`, hence it is exactly a Boolean subalgebra of `Set X`, and the smallest one containing
the open sets is `BooleanSubalgebra.closure {U | IsOpen U}`. -/

/-- **Atiyah–Macdonald, Exercise 7.20**: the smallest collection of subsets of `X` which contains
all open subsets of `X` and is closed with respect to the formation of finite intersections and
complements, packaged as a Boolean subalgebra of `Set X`. -/
def F (X : Type*) [TopologicalSpace X] : BooleanSubalgebra (Set X) :=
  BooleanSubalgebra.closure {U : Set X | IsOpen U}

theorem isOpen_mem_F {E : Set X} (hE : IsOpen E) : E ∈ F X :=
  BooleanSubalgebra.mem_closure_of_mem (s := {U : Set X | IsOpen U}) hE

theorem isClosed_mem_F {E : Set X} (hE : IsClosed E) : E ∈ F X := by
  have h : Eᶜ ∈ F X := isOpen_mem_F (X := X) hE.isOpen_compl
  simpa using (BooleanSubalgebra.compl_mem (L := F X) h)

theorem mem_F_empty : (∅ : Set X) ∈ F X :=
  BooleanSubalgebra.bot_mem (L := F X)

theorem mem_F_univ : (univ : Set X) ∈ F X :=
  BooleanSubalgebra.top_mem (L := F X)

theorem mem_F_union {E E' : Set X} (hE : E ∈ F X) (hE' : E' ∈ F X) : E ∪ E' ∈ F X :=
  BooleanSubalgebra.sup_mem (L := F X) hE hE'

theorem mem_F_inter {E E' : Set X} (hE : E ∈ F X) (hE' : E' ∈ F X) : E ∩ E' ∈ F X :=
  BooleanSubalgebra.inf_mem (L := F X) hE hE'

theorem mem_F_compl {E : Set X} (hE : E ∈ F X) : Eᶜ ∈ F X :=
  BooleanSubalgebra.compl_mem (L := F X) hE

theorem mem_F_sdiff {E E' : Set X} (hE : E ∈ F X) (hE' : E' ∈ F X) : E \ E' ∈ F X :=
  BooleanSubalgebra.sdiff_mem (L := F X) hE hE'

/-- Every locally closed set, i.e. every intersection of an open and a closed set, belongs to `F`. -/
theorem isLocallyClosed_mem_F {E : Set X} (hE : IsLocallyClosed E) : E ∈ F X := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hE
  exact mem_F_inter (isOpen_mem_F hU) (isClosed_mem_F hZ)

/-- `F` is stable under taking preimages along continuous maps. -/
theorem mem_F_preimage {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf : Continuous f)
    {E : Set X} (hE : E ∈ F X) : f ⁻¹' E ∈ F Y := by
  have key : ∀ S : Set X, S ∈ F X → f ⁻¹' S ∈ F Y := by
    intro S hS
    let L : BooleanSubalgebra (Set X) :=
      { carrier := {S : Set X | f ⁻¹' S ∈ F Y}
        supClosed' := by
          intro a ha b hb
          show f ⁻¹' (a ∪ b) ∈ F Y
          have h : f ⁻¹' a ∪ f ⁻¹' b ∈ F Y := mem_F_union (X := Y) ha hb
          rwa [← preimage_union] at h
        infClosed' := by
          intro a ha b hb
          show f ⁻¹' (a ∩ b) ∈ F Y
          have h : f ⁻¹' a ∩ f ⁻¹' b ∈ F Y := mem_F_inter (X := Y) ha hb
          rwa [← preimage_inter] at h
        compl_mem' := by
          intro a ha
          show f ⁻¹' aᶜ ∈ F Y
          have h : (f ⁻¹' a)ᶜ ∈ F Y := mem_F_compl (X := Y) ha
          rwa [← preimage_compl] at h
        bot_mem' := by
          show f ⁻¹' (∅ : Set X) ∈ F Y
          have h : (∅ : Set Y) ∈ F Y := mem_F_empty (X := Y)
          rwa [← preimage_empty] at h }
    exact (BooleanSubalgebra.closure_le (L := L)).2
      (fun U hU => isOpen_mem_F (X := Y) (hf.isOpen_preimage U hU)) hS
  exact key E hE

/-- In an irreducible space, a finite closed cover of the whole space has a member which already
covers the whole space. -/
theorem exists_univ_subset_of_iUnion_closed [IrreducibleSpace X] {ι : Type*} (t : Finset ι)
    {Z : ι → Set X} (hZ : ∀ i ∈ t, IsClosed (Z i)) (h : (univ : Set X) ⊆ ⋃ i ∈ t, Z i) :
    ∃ i ∈ t, (univ : Set X) ⊆ Z i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : (⋃ i ∈ (∅ : Finset ι), Z i) = (∅ : Set X) := by simp
    rw [h0, subset_empty_iff] at h
    exact absurd h (IrreducibleSpace.isIrreducible_univ X).nonempty.ne_empty
  | insert a t ha ih =>
    have hins : (⋃ i ∈ insert a t, Z i) = Z a ∪ ⋃ i ∈ t, Z i := by
      ext z
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ⟨i, hi, hz⟩
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact Or.inl hz
        · exact Or.inr ⟨i, hi, hz⟩
      · rintro (hz | ⟨i, hi, hz⟩)
        · exact ⟨a, Finset.mem_insert_self a t, hz⟩
        · exact ⟨i, Finset.mem_insert_of_mem hi, hz⟩
    rw [hins] at h
    have hZa : IsClosed (Z a) := hZ a (Finset.mem_insert_self a t)
    have hZt : IsClosed (⋃ i ∈ t, Z i) :=
      isClosed_biUnion_finset (fun i hi => hZ i (Finset.mem_insert_of_mem hi))
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1
      (IrreducibleSpace.isIrreducible_univ X).isPreirreducible) (Z a) (⋃ i ∈ t, Z i) hZa hZt h
      with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a t, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hZ i (Finset.mem_insert_of_mem hi)) h2
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩


/-- **Atiyah–Macdonald, Exercise 7.20 (a)**: the elements of `F` are exactly the finite unions of
locally closed subsets of `X`. -/
theorem mem_F_iff_exists_finset_isLocallyClosed {E : Set X} :
    E ∈ F X ↔ ∃ t : Finset (Set X), (∀ S ∈ t, IsLocallyClosed S) ∧ E = ⋃₀ (t : Set (Set X)) := by
  constructor
  · intro hE
    obtain ⟨t, ht⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff
      (s := {U : Set X | IsOpen U})
      (⟨fun a ha b hb => ha.union hb, fun a ha b hb => ha.inter hb⟩ : IsSublattice _)
      (show (⊥ : Set X) ∈ {U : Set X | IsOpen U} from isOpen_empty)
      (show (⊤ : Set X) ∈ {U : Set X | IsOpen U} from isOpen_univ)).1 hE
    set g : ({U : Set X // IsOpen U} × {U : Set X // IsOpen U}) → Set X :=
      fun x => x.1.1 \ x.2.1 with hg
    refine ⟨t.image g, ?_, ?_⟩
    · intro S hS
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hS
      exact ⟨x.1.1, (x.2.1)ᶜ, x.1.2, x.2.2.isClosed_compl, sdiff_eq⟩
    · rw [ht]
      refine le_antisymm ?_ ?_
      · refine Finset.sup_le (fun x hx => ?_)
        exact subset_sUnion_of_mem (Finset.mem_image_of_mem g hx)
      · refine sUnion_subset (fun y hy => ?_)
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        exact Finset.le_sup (f := g) hx
  · rintro ⟨t, ht, rfl⟩
    induction t using Finset.induction_on with
    | empty => simpa using mem_F_empty (X := X)
    | insert a t ha ih =>
      have h1 : IsLocallyClosed a := ht a (Finset.mem_insert_self a t)
      have h2 : ∀ S ∈ t, IsLocallyClosed S := fun S hS => ht S (Finset.mem_insert_of_mem hS)
      have hins : (⋃₀ (↑(insert a t) : Set (Set X))) = a ∪ ⋃₀ (↑t : Set (Set X)) := by
        rw [Finset.coe_insert, sUnion_insert]
      rw [hins]
      exact mem_F_union (isLocallyClosed_mem_F h1) (ih h2)


/-- `F` is the *smallest* collection of subsets of `X` which contains all open subsets of `X` and
is closed under the formation of finite intersections and complements: every such collection
contains `F`. -/
theorem mem_F_of_mem_collection {C : Set (Set X)}
    (hopen : ∀ U : Set X, IsOpen U → U ∈ C)
    (hinter : ∀ s t : Set X, s ∈ C → t ∈ C → s ∩ t ∈ C)
    (hcompl : ∀ s : Set X, s ∈ C → sᶜ ∈ C)
    {E : Set X} (hE : E ∈ F X) : E ∈ C := by
  have htop : (univ : Set X) ∈ C := hopen univ isOpen_univ
  have hbot : (∅ : Set X) ∈ C := by
    simpa using hcompl univ htop
  let L : BooleanSubalgebra (Set X) :=
    { carrier := C
      supClosed' := by
        intro a ha b hb
        show a ∪ b ∈ C
        have h : a ∪ b = (aᶜ ∩ bᶜ)ᶜ := by
          rw [compl_inter, compl_compl, compl_compl]
        rw [h]
        exact hcompl _ (hinter _ _ (hcompl a ha) (hcompl b hb))
      infClosed' := fun a ha b hb => hinter a b ha hb
      compl_mem' := fun ha => hcompl _ ha
      bot_mem' := hbot }
  exact (BooleanSubalgebra.closure_le (L := L)).2 (fun U hU => hopen U hU) hE

/-! ## Exercise 7.20 (b)

If `X` is irreducible and `E ∈ F`, then `E` is dense in `X` if and only if `E` contains a
non-empty open subset of `X`.  This is the form in which Exercise 7.20 is used in Exercise 7.21.
The proof uses the normal form for the elements of `F` supplied by
`BooleanSubalgebra.mem_closure_iff_sup_sdiff`: every element of `F` is a finite union of sets of
the form `U \ V = U ∩ Vᶜ` with `U`, `V` open.  If such a piece is dense, its closed part `Vᶜ`
must be all of `X`, so the piece is the non-empty open set `U`. -/

/-- **Atiyah–Macdonald, Exercise 7.20 (b)**: in an irreducible space, an element of `F` is dense if
and only if it contains a non-empty open subset. -/
theorem dense_iff_exists_isOpen_subset_of_mem_F [IrreducibleSpace X] {E : Set X}
    (hE : E ∈ F X) : Dense E ↔ ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ E := by
  constructor
  · intro hd
    obtain ⟨t, ht⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff
      (s := {U : Set X | IsOpen U})
      (⟨fun a ha b hb => ha.union hb, fun a ha b hb => ha.inter hb⟩ : IsSublattice _)
      (show (⊥ : Set X) ∈ {U : Set X | IsOpen U} from isOpen_empty)
      (show (⊤ : Set X) ∈ {U : Set X | IsOpen U} from isOpen_univ)).1 hE
    set g : ({U : Set X // IsOpen U} × {U : Set X // IsOpen U}) → Set X :=
      fun x => x.1.1 \ x.2.1 with hg
    have hEs : E ⊆ ⋃ x ∈ t, closure (g x) := by
      rw [ht]
      refine Finset.sup_le (fun x hx => ?_)
      intro z hz
      exact mem_iUnion₂.2 ⟨x, hx, subset_closure hz⟩
    have hcover : (univ : Set X) ⊆ ⋃ x ∈ t, closure (g x) := by
      rw [← hd.closure_eq]
      exact closure_minimal hEs (isClosed_biUnion_finset (fun x _ => isClosed_closure))
    obtain ⟨x, hx, hxuniv⟩ :=
      exists_univ_subset_of_iUnion_closed t (fun x _ => isClosed_closure) hcover
    -- `g x = x.1.1 \ x.2.1` is dense, so its closed part `(x.2.1)ᶜ` must be all of `X`
    have hsub : g x ⊆ (x.2.1)ᶜ := by
      intro z hz
      have hz' : g x = x.1.1 ∩ (x.2.1)ᶜ := sdiff_eq
      rw [hz'] at hz
      exact hz.2
    have hVempty : x.2.1 = ∅ := by
      have hcl : closure (g x) ⊆ (x.2.1)ᶜ := closure_minimal hsub x.2.2.isClosed_compl
      have h2 : x.2.1 ⊆ (∅ : Set X) := by
        intro y hy
        exact hcl (hxuniv (mem_univ y)) hy
      rwa [subset_empty_iff] at h2
    have hgx : g x = x.1.1 := by
      rw [hg]
      simp only [hVempty, sdiff_empty]
    have hne : (g x).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      have huniv : (univ : Set X).Nonempty := (IrreducibleSpace.isIrreducible_univ X).nonempty
      rw [hcon, closure_empty, subset_empty_iff] at hxuniv
      exact huniv.ne_empty hxuniv
    exact ⟨g x, by rw [hgx]; exact x.1.2, hne, by rw [ht]; exact Finset.le_sup hx⟩
  · rintro ⟨U, hU, hUne, hUE⟩
    exact (hU.dense hUne).mono hUE

/-! ## Exercise 7.21 -/

/-- **Atiyah–Macdonald, Exercise 7.21.** Let `X` be a Noetherian space and `E ⊆ X`. Then `E`
belongs to `F` if and only if for each irreducible closed subset `X₀ ⊆ X` either
`Cl(E ∩ X₀) ≠ X₀`, or `E ∩ X₀` contains a non-empty open subset of `X₀`. -/
theorem exercise_7_21 [NoetherianSpace X] (E : Set X) :
    E ∈ F X ↔ ∀ X₀ : Set X, IsClosed X₀ → IsIrreducible X₀ →
      closure (E ∩ X₀) ≠ X₀ ∨ ∃ U : Set X₀, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, (x : X) ∈ E := by
  constructor
  · intro hE X₀ hX₀ hIrr
    by_cases hcl : closure (E ∩ X₀) = X₀
    · right
      have : IrreducibleSpace X₀ := Subtype.irreducibleSpace hIrr
      have hpre : (Subtype.val : X₀ → X) ⁻¹' E ∈ F X₀ :=
        mem_F_preimage (X := X) (Y := X₀) (f := Subtype.val) continuous_subtype_val hE
      have himg : (Subtype.val : X₀ → X) '' ((Subtype.val : X₀ → X) ⁻¹' E) = E ∩ X₀ := by
        rw [Subtype.image_preimage_coe, Set.inter_comm]
      have hdense : Dense ((Subtype.val : X₀ → X) ⁻¹' E) := by
        rw [Subtype.dense_iff, himg, hcl]
      obtain ⟨U, hU, hUne, hUE⟩ := (dense_iff_exists_isOpen_subset_of_mem_F hpre).1 hdense
      exact ⟨U, hU, hUne, fun x hx => hUE hx⟩
    · exact Or.inl hcl
  · intro H
    have key : ∀ C : Closeds X, E ∩ (C : Set X) ∈ F X := by
      intro C
      induction C using WellFoundedLT.induction with
      | ind C IH =>
        by_cases hCne : (C : Set X).Nonempty
        · by_cases hIrr : IsIrreducible (C : Set X)
          · rcases H (C : Set X) C.isClosed hIrr with hcl | ⟨U, hU, hUne, hUE⟩
            · -- `E ∩ X₀` is not dense in `X₀ = C`
              have hDclosed : IsClosed (closure (E ∩ (C : Set X))) := isClosed_closure
              have hDsub : closure (E ∩ (C : Set X)) ⊆ (C : Set X) :=
                closure_minimal inter_subset_right C.isClosed
              have hDne : (⟨closure (E ∩ (C : Set X)), hDclosed⟩ : Closeds X) ≠ C := by
                intro h
                exact hcl (congrArg (fun D : Closeds X => (D : Set X)) h)
              have hlt : (⟨closure (E ∩ (C : Set X)), hDclosed⟩ : Closeds X) < C :=
                lt_of_le_of_ne hDsub hDne
              have hIH := IH ⟨closure (E ∩ (C : Set X)), hDclosed⟩ hlt
              have heq : E ∩ (C : Set X) = E ∩ closure (E ∩ (C : Set X)) := by
                refine subset_antisymm ?_ ?_
                · rintro x ⟨hxE, hxC⟩
                  exact ⟨hxE, subset_closure ⟨hxE, hxC⟩⟩
                · rintro x ⟨hxE, hxD⟩
                  exact ⟨hxE, hDsub hxD⟩
              rw [heq]
              exact hIH
            · -- `E ∩ X₀` contains a non-empty open subset of `X₀ = C`
              obtain ⟨V, hV, hVU⟩ := IsInducing.subtypeVal.isOpen_iff.1 hU
              have hWF : ((C : Set X) ∩ V) ∈ F X := by
                have hLC : IsLocallyClosed (V ∩ (C : Set X)) :=
                  ⟨V, (C : Set X), hV, C.isClosed, rfl⟩
                simpa only [inter_comm] using isLocallyClosed_mem_F hLC
              have hWsubE : ((C : Set X) ∩ V) ⊆ E := by
                rintro x ⟨hxC, hxV⟩
                refine hUE ⟨x, hxC⟩ ?_
                rw [← hVU]
                exact hxV
              have hdiff_eq : (C : Set X) \ ((C : Set X) ∩ V) = (C : Set X) ∩ Vᶜ := by
                ext x
                constructor
                · rintro ⟨hxC, hx⟩
                  exact ⟨hxC, fun hxV => hx ⟨hxC, hxV⟩⟩
                · rintro ⟨hxC, hxV⟩
                  exact ⟨hxC, fun h => hxV h.2⟩
              have hdiff_closed : IsClosed ((C : Set X) \ ((C : Set X) ∩ V)) := by
                rw [hdiff_eq]
                exact C.isClosed.inter hV.isClosed_compl
              have hdiff_ne : ((C : Set X) \ ((C : Set X) ∩ V)) ≠ (C : Set X) := by
                intro heq
                obtain ⟨x, hxU⟩ := hUne
                have hxC : (x : X) ∈ (C : Set X) := x.2
                have hxV' : x ∈ (Subtype.val : ↑↑C → X) ⁻¹' V := hVU ▸ hxU
                have hxV : (x : X) ∈ V := hxV'
                have hxmem : (x : X) ∈ (C : Set X) \ ((C : Set X) ∩ V) := by
                  rw [heq]
                  exact hxC
                exact hxmem.2 ⟨hxC, hxV⟩
              have hdiff_lt :
                  (⟨(C : Set X) \ ((C : Set X) ∩ V), hdiff_closed⟩ : Closeds X) < C := by
                refine lt_of_le_of_ne sdiff_subset ?_
                intro h
                exact hdiff_ne (congrArg (fun D : Closeds X => (D : Set X)) h)
              have hIH := IH ⟨(C : Set X) \ ((C : Set X) ∩ V), hdiff_closed⟩ hdiff_lt
              have hunion : E ∩ (C : Set X) =
                  (E ∩ ((C : Set X) \ ((C : Set X) ∩ V))) ∪ ((C : Set X) ∩ V) := by
                ext x
                constructor
                · rintro ⟨hxE, hxC⟩
                  by_cases hxW : x ∈ (C : Set X) ∩ V
                  · exact Or.inr hxW
                  · exact Or.inl ⟨hxE, hxC, hxW⟩
                · rintro (⟨hxE, hx⟩ | hxW)
                  · exact ⟨hxE, hx.1⟩
                  · exact ⟨hWsubE hxW, hxW.1⟩
              rw [hunion]
              exact mem_F_union hIH hWF
          · -- `X₀ = C` is reducible
            have hnotpre : ¬ IsPreirreducible (C : Set X) := fun hp => hIrr ⟨hCne, hp⟩
            rw [isPreirreducible_iff_isClosed_union_isClosed] at hnotpre
            rw [not_forall] at hnotpre
            obtain ⟨z₁, hnotpre⟩ := hnotpre
            rw [not_forall] at hnotpre
            obtain ⟨z₂, hnotpre⟩ := hnotpre
            rw [Classical.not_imp] at hnotpre
            obtain ⟨hz₁, hnotpre⟩ := hnotpre
            rw [Classical.not_imp] at hnotpre
            obtain ⟨hz₂, hnotpre⟩ := hnotpre
            rw [Classical.not_imp] at hnotpre
            obtain ⟨hsub, hnotpre⟩ := hnotpre
            rw [not_or] at hnotpre
            obtain ⟨hz₁', hz₂'⟩ := hnotpre
            have h1closed : IsClosed ((C : Set X) ∩ z₁) := C.isClosed.inter hz₁
            have h2closed : IsClosed ((C : Set X) ∩ z₂) := C.isClosed.inter hz₂
            have h1ne : ((C : Set X) ∩ z₁) ≠ (C : Set X) := by
              intro h
              refine hz₁' (fun x hx => ?_)
              have hx' : x ∈ (C : Set X) ∩ z₁ := by rw [h]; exact hx
              exact hx'.2
            have h2ne : ((C : Set X) ∩ z₂) ≠ (C : Set X) := by
              intro h
              refine hz₂' (fun x hx => ?_)
              have hx' : x ∈ (C : Set X) ∩ z₂ := by rw [h]; exact hx
              exact hx'.2
            have h1lt : (⟨(C : Set X) ∩ z₁, h1closed⟩ : Closeds X) < C := by
              refine lt_of_le_of_ne inter_subset_left ?_
              intro h
              exact h1ne (congrArg (fun D : Closeds X => (D : Set X)) h)
            have h2lt : (⟨(C : Set X) ∩ z₂, h2closed⟩ : Closeds X) < C := by
              refine lt_of_le_of_ne inter_subset_left ?_
              intro h
              exact h2ne (congrArg (fun D : Closeds X => (D : Set X)) h)
            have hIH1 := IH ⟨(C : Set X) ∩ z₁, h1closed⟩ h1lt
            have hIH2 := IH ⟨(C : Set X) ∩ z₂, h2closed⟩ h2lt
            have hunion : E ∩ (C : Set X) =
                (E ∩ ((C : Set X) ∩ z₁)) ∪ (E ∩ ((C : Set X) ∩ z₂)) := by
              ext x
              constructor
              · rintro ⟨hxE, hxC⟩
                rcases hsub hxC with hx | hx
                · exact Or.inl ⟨hxE, hxC, hx⟩
                · exact Or.inr ⟨hxE, hxC, hx⟩
              · rintro (⟨hxE, hx⟩ | ⟨hxE, hx⟩)
                · exact ⟨hxE, hx.1⟩
                · exact ⟨hxE, hx.1⟩
            rw [hunion]
            exact mem_F_union hIH1 hIH2
        · -- `C = ∅`
          have hCempty : (C : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.1 hCne
          rw [hCempty, inter_empty]
          exact mem_F_empty
    simpa using key ⊤

/-- The second alternative of Exercise 7.21, "`E ∩ X₀` contains a non-empty open subset of `X₀`",
written with an open subset `V` of the ambient space `X` (an open subset of `X₀` is `X₀ ∩ V`). -/
theorem exists_isOpen_subset_iff {X₀ : Set X} (E : Set X) :
    (∃ V : Set X, IsOpen V ∧ (X₀ ∩ V).Nonempty ∧ X₀ ∩ V ⊆ E) ↔
      ∃ U : Set X₀, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, (x : X) ∈ E := by
  constructor
  · rintro ⟨V, hV, hne, hsub⟩
    refine ⟨(Subtype.val : X₀ → X) ⁻¹' V, hV.preimage continuous_subtype_val, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hx.1⟩, hx.2⟩
    · intro x hx
      exact hsub ⟨x.2, hx⟩
  · rintro ⟨U, hU, hne, hsub⟩
    obtain ⟨V, hV, hVU⟩ := IsInducing.subtypeVal.isOpen_iff.1 hU
    refine ⟨V, hV, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      have hx' : x ∈ (Subtype.val : X₀ → X) ⁻¹' V := hVU ▸ hx
      exact ⟨(x : X), x.2, hx'⟩
    · rintro y ⟨hyX, hyV⟩
      have hy' : (⟨y, hyX⟩ : X₀) ∈ (Subtype.val : X₀ → X) ⁻¹' V := hyV
      exact hsub ⟨y, hyX⟩ (hVU ▸ hy')

/-- **Atiyah–Macdonald, Exercise 7.21**, with "open subset of `X₀`" written as `X₀ ∩ V` for an
open subset `V` of `X`: `E ∈ F` if and only if for each irreducible closed `X₀ ⊆ X` either
`Cl(E ∩ X₀) ≠ X₀` or `X₀ ∩ V ⊆ E` for some open `V` with `X₀ ∩ V ≠ ∅`. -/
theorem exercise_7_21_ambient [NoetherianSpace X] (E : Set X) :
    E ∈ F X ↔ ∀ X₀ : Set X, IsClosed X₀ → IsIrreducible X₀ →
      closure (E ∩ X₀) ≠ X₀ ∨ ∃ V : Set X, IsOpen V ∧ (X₀ ∩ V).Nonempty ∧ X₀ ∩ V ⊆ E := by
  have key := exercise_7_21 E
  constructor
  · intro h X₀ hX₀ hI
    rcases key.1 h X₀ hX₀ hI with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ((exists_isOpen_subset_iff (X₀ := X₀) E).2 h2)
  · intro h
    refine key.2 (fun X₀ hX₀ hI => ?_)
    rcases h X₀ hX₀ hI with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ((exists_isOpen_subset_iff (X₀ := X₀) E).1 h2)


/-- **Atiyah–Macdonald, Exercise 7.21**, with the irreducibility of `X₀` expressed as irreducibility
of the subspace `↥X₀` (equivalent to `IsIrreducible X₀` by `isIrreducible_iff_irreducibleSpace`). -/
theorem exercise_7_21_subspace [NoetherianSpace X] (E : Set X) :
    E ∈ F X ↔ ∀ X₀ : Set X, IsClosed X₀ → IrreducibleSpace X₀ →
      closure (E ∩ X₀) ≠ X₀ ∨ ∃ U : Set X₀, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, (x : X) ∈ E := by
  constructor
  · intro h X₀ hX₀ hI
    exact (exercise_7_21 E).1 h X₀ hX₀ (isIrreducible_iff_irreducibleSpace.2 hI)
  · intro h
    exact (exercise_7_21 E).2 (fun X₀ hX₀ hI =>
      h X₀ hX₀ (isIrreducible_iff_irreducibleSpace.1 hI))

/-- Full statement of Atiyah–Macdonald, Exercise 7.21 (alias of `exercise_7_21`). -/
theorem solution [NoetherianSpace X] (E : Set X) :
    E ∈ F X ↔ ∀ X₀ : Set X, IsClosed X₀ → IsIrreducible X₀ →
      closure (E ∩ X₀) ≠ X₀ ∨ ∃ U : Set X₀, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, (x : X) ∈ E :=
  exercise_7_21 E

end AtiyahMcdonald69.Ex_7_21

#print axioms AtiyahMcdonald69.Ex_7_21.solution
#print axioms AtiyahMcdonald69.Ex_7_21.exercise_7_21_subspace
#print axioms AtiyahMcdonald69.Ex_7_21.mem_F_of_mem_collection
#print axioms AtiyahMcdonald69.Ex_7_21.exercise_7_21
#print axioms AtiyahMcdonald69.Ex_7_21.mem_F_iff_exists_finset_isLocallyClosed
#print axioms AtiyahMcdonald69.Ex_7_21.dense_iff_exists_isOpen_subset_of_mem_F
