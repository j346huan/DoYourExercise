import Mathlib.Topology.Irreducible
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sets.Closeds

/-!
# Atiyah–Macdonald (1969), Chapter 7, Exercise 22

*Statement (Exercise 7.22 of Atiyah–Macdonald).* Let `X` be a Noetherian topological
space and let `E` be a subset of `X`. Then `E` is open in `X` if and only if, for each
irreducible closed subset `X₀` of `X`, either `E ∩ X₀ = ∅` or `E ∩ X₀` contains a
non-empty open subset of `X₀`.

Here "open subset of `X₀`" is meant in the subspace topology of `X₀` (this is what makes
the statement true: a non-empty relatively open subset).  Since the relatively open
subsets of `X₀` are exactly the sets `U ∩ X₀` with `U` open in `X`, the condition can be
written as `E ∩ X₀ = ∅ ∨ ∃ U, IsOpen U ∧ (U ∩ X₀).Nonempty ∧ U ∩ X₀ ⊆ E`, which is the
form used in `solution` below.

The proof is the textbook one.  For the converse, suppose that `E` is not open and let
`F` be a closed set, minimal among those for which `E ∩ F` is not open in `F` (it exists
because `X` is Noetherian).  Then `F` is irreducible, and the hypothesis applied to `F`
produces a non-empty relatively open `U ∩ F ⊆ E`; as `F \ U` is a proper closed subset of
`F`, minimality makes `E ∩ (F \ U)` open in `F \ U`, and gluing the open set `U` with the
closed set `F \ U` shows that `E ∩ F` is open in `F`, a contradiction.

Natural language proof (not authoritative):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-22
-/

open Set Topology TopologicalSpace

namespace AtiyahMcdonald69.Ex_7_22

variable {X : Type*} [TopologicalSpace X]

/-- `RelOpenIn E F` says that `E ∩ F` is an open subset of the subspace `F`, i.e. that
`E` is relatively open in `F`.  Concretely, `E ∩ F = U ∩ F` for some open `U ⊆ X`. -/
def RelOpenIn (E F : Set X) : Prop := ∃ U : Set X, IsOpen U ∧ U ∩ F = E ∩ F

/-- The empty set is relatively open in anything. -/
theorem relOpenIn_empty (E : Set X) : RelOpenIn E ∅ :=
  ⟨∅, isOpen_empty, by simp⟩

/-- `E` is relatively open in the whole space iff it is open. -/
theorem relOpenIn_univ {E : Set X} : RelOpenIn E univ ↔ IsOpen E := by
  simp only [RelOpenIn, inter_univ]
  exact ⟨fun ⟨_, hU, h⟩ => h ▸ hU, fun h => ⟨E, h, rfl⟩⟩

/-- Gluing of relative openness along a cover by the two closed sets `z₁` and `z₂`:
if `F` is closed, `F ⊆ z₁ ∪ z₂` and `E` is relatively open in `F ∩ z₁` and in
`F ∩ z₂`, then `E` is relatively open in `F`. -/
theorem relOpenIn_of_isClosed_union {E F z₁ z₂ : Set X} (hF : IsClosed F)
    (hz₁ : IsClosed z₁) (hz₂ : IsClosed z₂) (hcov : F ⊆ z₁ ∪ z₂)
    (h₁ : RelOpenIn E (F ∩ z₁)) (h₂ : RelOpenIn E (F ∩ z₂)) : RelOpenIn E F := by
  obtain ⟨U₁, hU₁, e₁⟩ := h₁
  obtain ⟨U₂, hU₂, e₂⟩ := h₂
  -- on `F ∩ zᵢ` the sets `Uᵢ` and `E` agree
  have mem₁ : ∀ x ∈ F, x ∈ z₁ → (x ∈ U₁ ↔ x ∈ E) := by
    intro x hxF hxz
    have h1 : x ∈ U₁ ∩ (F ∩ z₁) ↔ x ∈ E ∩ (F ∩ z₁) := by rw [e₁]
    simpa [hxF, hxz, and_assoc] using h1
  have mem₂ : ∀ x ∈ F, x ∈ z₂ → (x ∈ U₂ ↔ x ∈ E) := by
    intro x hxF hxz
    have h1 : x ∈ U₂ ∩ (F ∩ z₂) ↔ x ∈ E ∩ (F ∩ z₂) := by rw [e₂]
    simpa [hxF, hxz, and_assoc] using h1
  -- the two closed pieces
  have key₁ : U₁ᶜ ∩ F ∩ z₁ = Eᶜ ∩ F ∩ z₁ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨hxU, hxF⟩, hxz⟩
      exact ⟨⟨fun hxE => hxU ((mem₁ x hxF hxz).2 hxE), hxF⟩, hxz⟩
    · rintro ⟨⟨hxE, hxF⟩, hxz⟩
      exact ⟨⟨fun hxU => hxE ((mem₁ x hxF hxz).1 hxU), hxF⟩, hxz⟩
  have key₂ : U₂ᶜ ∩ F ∩ z₂ = Eᶜ ∩ F ∩ z₂ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨hxU, hxF⟩, hxz⟩
      exact ⟨⟨fun hxE => hxU ((mem₂ x hxF hxz).2 hxE), hxF⟩, hxz⟩
    · rintro ⟨⟨hxE, hxF⟩, hxz⟩
      exact ⟨⟨fun hxU => hxE ((mem₂ x hxF hxz).1 hxU), hxF⟩, hxz⟩
  set D : Set X := (U₁ᶜ ∩ F ∩ z₁) ∪ (U₂ᶜ ∩ F ∩ z₂) with hDdef
  have hDclosed : IsClosed D :=
    (((hU₁.isClosed_compl.inter hF).inter hz₁).union
      ((hU₂.isClosed_compl.inter hF).inter hz₂))
  have hDF : D ∩ F = Eᶜ ∩ F := by
    ext x
    simp only [hDdef, mem_inter_iff, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨hx | hx, hxF⟩
      · obtain ⟨⟨hxU, -⟩, hxz⟩ := hx
        exact ⟨fun hxE => hxU ((mem₁ x hxF hxz).2 hxE), hxF⟩
      · obtain ⟨⟨hxU, -⟩, hxz⟩ := hx
        exact ⟨fun hxE => hxU ((mem₂ x hxF hxz).2 hxE), hxF⟩
    · rintro ⟨hxE, hxF⟩
      rcases hcov hxF with hxz | hxz
      · exact ⟨Or.inl ⟨⟨fun hxU => hxE ((mem₁ x hxF hxz).1 hxU), hxF⟩, hxz⟩, hxF⟩
      · exact ⟨Or.inr ⟨⟨fun hxU => hxE ((mem₂ x hxF hxz).1 hxU), hxF⟩, hxz⟩, hxF⟩
  refine ⟨Dᶜ, hDclosed.isOpen_compl, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_compl_iff]
  constructor
  · rintro ⟨hxD, hxF⟩
    refine ⟨?_, hxF⟩
    by_contra hxE
    apply hxD
    have hx' : x ∈ Eᶜ ∩ F := ⟨hxE, hxF⟩
    exact (hDF.symm ▸ hx').1
  · rintro ⟨hxE, hxF⟩
    refine ⟨?_, hxF⟩
    intro hxD
    have hx' : x ∈ Eᶜ ∩ F := hDF ▸ (⟨hxD, hxF⟩ : x ∈ D ∩ F)
    have hxE' : x ∉ E := hx'.1
    exact hxE' hxE

/-- If `U` is open, `U ∩ F ⊆ E` and `E` is relatively open in `F \ U`, then `E` is
relatively open in `F`.  This is the gluing along the open set `U` and its (relatively)
closed complement used in the last step of the argument. -/
theorem relOpenIn_of_open_diff {E F U : Set X} (hU : IsOpen U) (hUF : U ∩ F ⊆ E)
    (h : RelOpenIn E (F \ U)) : RelOpenIn E F := by
  obtain ⟨V, hV, hVeq⟩ := h
  refine ⟨U ∪ V, hU.union hV, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_union]
  constructor
  · rintro ⟨hx | hx, hxF⟩
    · exact ⟨hUF ⟨hx, hxF⟩, hxF⟩
    · by_cases hxU : x ∈ U
      · exact ⟨hUF ⟨hxU, hxF⟩, hxF⟩
      · have hxC : x ∈ F \ U := ⟨hxF, hxU⟩
        have hx' : x ∈ V ∩ (F \ U) := ⟨hx, hxC⟩
        rw [hVeq] at hx'
        exact ⟨hx'.1, hxF⟩
  · rintro ⟨hxE, hxF⟩
    by_cases hxU : x ∈ U
    · exact ⟨Or.inl hxU, hxF⟩
    · refine ⟨Or.inr ?_, hxF⟩
      have hx' : x ∈ E ∩ (F \ U) := ⟨hxE, ⟨hxF, hxU⟩⟩
      rw [← hVeq] at hx'
      exact hx'.1

/-- **Atiyah–Macdonald, Chapter 7, Exercise 22.**  A subset `E` of a Noetherian
topological space `X` is open if and only if for every irreducible closed subset `X₀`
of `X`, either `E ∩ X₀` is empty or it contains a non-empty subset that is open in the
subspace `X₀`. -/
theorem solution [TopologicalSpace.NoetherianSpace X] (E : Set X) :
    IsOpen E ↔ ∀ X₀ : Set X, IsClosed X₀ → IsIrreducible X₀ →
      E ∩ X₀ = ∅ ∨ ∃ U : Set X, IsOpen U ∧ (U ∩ X₀).Nonempty ∧ U ∩ X₀ ⊆ E := by
  constructor
  · -- if `E` is open, restrict it to `X₀`
    intro hE X₀ _ _
    by_cases hemp : E ∩ X₀ = ∅
    · exact Or.inl hemp
    · exact Or.inr ⟨E, hE, nonempty_iff_ne_empty.2 hemp, inter_subset_left⟩
  · -- conversely, argue by minimal counterexample among the closed sets
    intro h
    by_contra hE
    -- the family of closed sets on which `E` fails to be relatively open
    have hSne : {F : Closeds X | ¬ RelOpenIn E (F : Set X)}.Nonempty :=
      ⟨⊤, by
        show ¬ RelOpenIn E ((⊤ : Closeds X) : Set X)
        rw [Closeds.coe_top]
        exact fun hc => hE (relOpenIn_univ.1 hc)⟩
    obtain ⟨F, hFmem, hFmin⟩ :=
      wellFounded_lt.has_min (α := Closeds X) {F : Closeds X | ¬ RelOpenIn E (F : Set X)}
        hSne
    have hFnot : ¬ RelOpenIn E (F : Set X) := hFmem
    -- `F` is nonempty
    have hFne : (F : Set X).Nonempty := by
      rw [Closeds.coe_nonempty]
      intro hFbot
      exact hFnot (by rw [hFbot, Closeds.coe_bot]; exact relOpenIn_empty E)
    -- `F` is irreducible
    have hirr : IsIrreducible (F : Set X) := by
      refine ⟨hFne, ?_⟩
      rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hz₁ hz₂ hcov
      by_cases hle : (F : Set X) ⊆ z₁
      · exact Or.inl hle
      right
      by_contra hle₂
      have hlt₁ : (⟨(F : Set X) ∩ z₁, F.isClosed.inter hz₁⟩ : Closeds X) < F := by
        rw [lt_iff_le_and_ne]
        refine ⟨fun x hx => hx.1, ?_⟩
        intro hEq
        exact hle (by
          intro x hx
          have hx' : x ∈ ((⟨(F : Set X) ∩ z₁, F.isClosed.inter hz₁⟩ : Closeds X) : Set X) := by
            rw [hEq]; exact hx
          exact hx'.2)
      have hlt₂ : (⟨(F : Set X) ∩ z₂, F.isClosed.inter hz₂⟩ : Closeds X) < F := by
        rw [lt_iff_le_and_ne]
        refine ⟨fun x hx => hx.1, ?_⟩
        intro hEq
        exact hle₂ (by
          intro x hx
          have hx' : x ∈ ((⟨(F : Set X) ∩ z₂, F.isClosed.inter hz₂⟩ : Closeds X) : Set X) := by
            rw [hEq]; exact hx
          exact hx'.2)
      have hro₁ : RelOpenIn E ((F : Set X) ∩ z₁) := by
        by_contra hh
        exact hFmin ⟨(F : Set X) ∩ z₁, F.isClosed.inter hz₁⟩ hh hlt₁
      have hro₂ : RelOpenIn E ((F : Set X) ∩ z₂) := by
        by_contra hh
        exact hFmin ⟨(F : Set X) ∩ z₂, F.isClosed.inter hz₂⟩ hh hlt₂
      exact hFnot (relOpenIn_of_isClosed_union F.isClosed hz₁ hz₂ hcov hro₁ hro₂)
    -- the hypothesis, applied to the irreducible closed set `F`
    rcases h (F : Set X) F.isClosed hirr with hemp | ⟨U, hUopen, hUne, hUsub⟩
    · refine hFnot ⟨∅, isOpen_empty, by simp [hemp]⟩
    · -- `F ∩ Uᶜ` is a proper closed subset of `F`, so minimality applies to it
      have hCclosed : IsClosed ((F : Set X) ∩ Uᶜ) := F.isClosed.inter hUopen.isClosed_compl
      have hClt : (⟨(F : Set X) ∩ Uᶜ, hCclosed⟩ : Closeds X) < F := by
        rw [lt_iff_le_and_ne]
        refine ⟨fun x hx => hx.1, ?_⟩
        intro hEq
        obtain ⟨x, hxU, hxF⟩ := hUne
        have hx' : x ∈ ((⟨(F : Set X) ∩ Uᶜ, hCclosed⟩ : Closeds X) : Set X) := by
          rw [hEq]; exact hxF
        exact hx'.2 hxU
      have hCro : RelOpenIn E ((F : Set X) ∩ Uᶜ) := by
        by_contra hh
        exact hFmin ⟨(F : Set X) ∩ Uᶜ, hCclosed⟩ hh hClt
      refine hFnot (relOpenIn_of_open_diff hUopen ?_ ?_)
      · -- `U ∩ F ⊆ E`
        intro x hx
        exact hUsub ⟨hx.1, hx.2⟩
      · -- `F \ U = F ∩ Uᶜ`
        have hEq : (F : Set X) \ U = (F : Set X) ∩ Uᶜ := by
          ext x
          simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
        simpa only [hEq] using hCro

/-- The condition "`E ∩ X₀` contains a non-empty open subset of `X₀`", with openness read
in the subspace topology of `X₀`, is equivalent to the ambient form used in `solution`. -/
theorem exists_relOpen_subset_iff (E X₀ : Set X) :
    (∃ U : Set X, IsOpen U ∧ (U ∩ X₀).Nonempty ∧ U ∩ X₀ ⊆ E) ↔
      ∃ V : Set X₀, IsOpen V ∧ V.Nonempty ∧ (Subtype.val '' V : Set X) ⊆ E := by
  constructor
  · rintro ⟨U, hU, hUne, hUsub⟩
    refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, ?_, ?_⟩
    · obtain ⟨x, hxU, hx0⟩ := hUne
      exact ⟨⟨x, hx0⟩, hxU⟩
    · rintro x ⟨y, hy, rfl⟩
      exact hUsub ⟨hy, y.2⟩
  · rintro ⟨V, hV, hVne, hVsub⟩
    obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.1 hV
    refine ⟨U, hU, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hVne
      refine ⟨y, ?_, y.2⟩
      show y ∈ Subtype.val ⁻¹' U
      rw [hUV]
      exact hy
    · rintro x ⟨hxU, hx0⟩
      exact hVsub ⟨⟨x, hx0⟩, by rw [← hUV]; exact hxU, rfl⟩

/-- **Atiyah–Macdonald, Chapter 7, Exercise 22**, in the literal wording of the book:
`E` is open in the Noetherian space `X` if and only if, for each irreducible closed
`X₀ ⊆ X`, either `E ∩ X₀ = ∅` or `E ∩ X₀` contains a non-empty subset that is open in
the subspace `X₀`. -/
theorem solution_subspace [TopologicalSpace.NoetherianSpace X] (E : Set X) :
    IsOpen E ↔ ∀ X₀ : Set X, IsClosed X₀ → IsIrreducible X₀ →
      E ∩ X₀ = ∅ ∨ ∃ V : Set X₀, IsOpen V ∧ V.Nonempty ∧ (Subtype.val '' V : Set X) ⊆ E := by
  rw [solution E]
  simp only [exists_relOpen_subset_iff]


end AtiyahMcdonald69.Ex_7_22

#print axioms AtiyahMcdonald69.Ex_7_22.solution_subspace
#print axioms AtiyahMcdonald69.Ex_7_22.solution
#print axioms AtiyahMcdonald69.Ex_7_22.relOpenIn_of_isClosed_union
#print axioms AtiyahMcdonald69.Ex_7_22.relOpenIn_of_open_diff
