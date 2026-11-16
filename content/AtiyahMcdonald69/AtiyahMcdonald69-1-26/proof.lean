import Mathlib

/- Natural-language solution: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-26 -/


/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 1.26

Let `X` be a compact Hausdorff space and let `C(X)` be the ring of real-valued continuous
functions on `X`.  For `x : X`, let `m x = {f : C(X) | f x = 0}` be the set of functions
vanishing at `x`.

We prove (following the hints of the book):

* `m_isMaximal` : `m x` is a maximal ideal of `C(X)`;
* `mu_surjective` : every maximal ideal of `C(X)` is of the form `m x`, i.e. the map
  `mu : x ↦ m x` from `X` to the set of maximal ideals is surjective;
* `mu_injective` : `mu` is injective;
* `mu_isHomeomorph` / `muHomeomorph` : `mu` is a homeomorphism of `X` onto the maximal spectrum
  `MaximalSpectrum C(X, ℝ)` endowed with the Zariski topology, i.e. the subspace topology
  induced by the inclusion of the maximal spectrum into the prime spectrum
  `PrimeSpectrum C(X, ℝ)` (this is Mathlib's definition of the topology on `MaximalSpectrum`).

The arguments are the book's: `m x` is the kernel of evaluation at `x` (a surjection onto `ℝ`);
if a maximal ideal `M` had no common zero, then by compactness it contains `f₁, …, fₙ` with
`∑ fᵢ²` everywhere positive, hence a unit, forcing `M = C(X)`; Urysohn's lemma separates points
(and a point from a closed set), giving injectivity, and shows that the families
`{x | f x ≠ 0}` and `{M | f ∉ M}` are corresponding bases of the two topologies.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Function

namespace AtiyahMcdonald69.Ex_1_26

variable {X : Type*} [TopologicalSpace X]

/-! ### The ideal of functions vanishing at a point -/

/-- `m x` is the ideal of continuous real-valued functions on `X` which vanish at the point `x`. -/
def m (x : X) : Ideal C(X, ℝ) where
  carrier := {f : C(X, ℝ) | f x = 0}
  add_mem' {f g} hf hg := by
    have hf' : f x = 0 := hf
    have hg' : g x = 0 := hg
    simp [hf', hg']
  zero_mem' := rfl
  smul_mem' c f hf := by
    have hf' : f x = 0 := hf
    simp [hf']

@[simp]
theorem mem_m {x : X} {f : C(X, ℝ)} : f ∈ m x ↔ f x = 0 := Iff.rfl

/-- `m x` is a maximal ideal: it is the kernel of the (surjective) evaluation map at `x`. -/
theorem m_isMaximal (x : X) : (m x).IsMaximal := by
  let ev : C(X, ℝ) →+* ℝ :=
    { toFun := fun f => f x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h : m x = RingHom.ker ev := by
    ext f
    rfl
  rw [h]
  exact RingHom.ker_isMaximal_of_surjective ev fun r => ⟨ContinuousMap.const X r, rfl⟩

/-! ### Surjectivity: every maximal ideal is `m x` for some `x` -/

variable [CompactSpace X] [T2Space X]

/-- Every maximal ideal of `C(X, ℝ)` is the ideal of functions vanishing at some point.

If a maximal ideal `M` had empty common zero set, then the open sets `{x | f x ≠ 0}` for
`f ∈ M` would cover `X`; by compactness `M` would contain `f₁, …, fₙ` with `∑ fᵢ²` everywhere
positive, hence a unit, so `M = C(X)`, a contradiction. -/
theorem exists_m_eq_of_isMaximal (I : Ideal C(X, ℝ)) (hI : I.IsMaximal) :
    ∃ x : X, m x = I := by
  by_contra h
  -- No maximal ideal strictly inside `m x`, so for every `x` some `f ∈ I` does not vanish at `x`.
  have hpt : ∀ x : X, ∃ f : C(X, ℝ), f ∈ I ∧ f x ≠ 0 := by
    intro x
    by_contra hx
    push Not at hx
    have hle : I ≤ m x := fun f hf => mem_m.mpr (hx f hf)
    have hne : m x ≠ ⊤ := by
      intro htop
      have h1 : (1 : C(X, ℝ)) ∈ m x := htop ▸ Submodule.mem_top
      have h2 : ((1 : C(X, ℝ)) : X → ℝ) x = 0 := mem_m.mp h1
      simp at h2
    exact h ⟨x, (hI.eq_of_le hne hle).symm⟩
  -- The sets `{x | f x ≠ 0}`, `f ∈ I`, cover `X`.
  have hcover : (univ : Set X) ⊆ ⋃ i : I, {x : X | (i : C(X, ℝ)) x ≠ 0} := by
    intro x _
    obtain ⟨f, hf, hfx⟩ := hpt x
    exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hfx⟩
  have hUopen : ∀ i : I, IsOpen {x : X | (i : C(X, ℝ)) x ≠ 0} := fun i =>
    isOpen_ne.preimage (map_continuous (i : C(X, ℝ)))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : I => {x : X | (i : C(X, ℝ)) x ≠ 0})
    hUopen hcover
  -- The finite sum of squares `g = ∑ fᵢ²` lies in `I` and is everywhere positive.
  set g : C(X, ℝ) := ∑ i ∈ t, (i : C(X, ℝ)) ^ 2 with hg
  have hgI : g ∈ I := by
    refine Submodule.sum_mem _ ?_
    intro i _
    exact I.pow_mem_of_mem i.2 2 (by norm_num)
  have hgpos : ∀ x : X, 0 < g x := by
    intro x
    obtain ⟨i, hi, hix⟩ : ∃ i ∈ t, (i : C(X, ℝ)) x ≠ 0 := by
      simpa only [mem_iUnion, exists_prop, mem_ofPred_eq] using ht (mem_univ x)
    have hx : g x = ∑ j ∈ t, ((j : C(X, ℝ)) x) ^ 2 := by
      simp [hg]
    rw [hx]
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, hi, sq_pos_of_ne_zero hix⟩
  -- Hence `g` is a unit, and a maximal ideal containing a unit is the whole ring.
  have hunit : IsUnit g :=
    (ContinuousMap.isUnit_iff_forall_ne_zero g).mpr fun x => (hgpos x).ne'
  exact hI.ne_top (Ideal.eq_top_of_isUnit_mem (I := I) hgI hunit)

/-! ### The map `x ↦ m x` and its injectivity -/

/-- The map `x ↦ m x` from `X` to the maximal spectrum of `C(X, ℝ)`. -/
def mu (x : X) : MaximalSpectrum C(X, ℝ) := ⟨m x, m_isMaximal x⟩

@[simp]
theorem mu_asIdeal (x : X) : (mu x).asIdeal = m x := rfl

theorem mu_surjective : Surjective (mu (X := X)) := by
  rintro ⟨I, hI⟩
  obtain ⟨x, hx⟩ := exists_m_eq_of_isMaximal I hI
  exact ⟨x, MaximalSpectrum.ext hx⟩

/-- Distinct points are separated by a continuous real-valued function (Urysohn), so the
ideals `m x` are pairwise distinct. -/
theorem mu_injective : Injective (mu (X := X)) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hfzero, hfone, -⟩ :=
    exists_continuous_zero_one_of_isClosed (s := {x}) (t := {y}) isClosed_singleton
      isClosed_singleton (Set.disjoint_singleton.mpr hne)
  have hx : f ∈ m x := mem_m.mpr (hfzero (mem_singleton x))
  have hy : f ∈ m y := by
    rw [← mu_asIdeal, ← hxy]
    exact hx
  have h0 : f y = 0 := mem_m.mp hy
  have h1 : f y = 1 := hfone (mem_singleton y)
  rw [h1] at h0
  exact one_ne_zero h0

theorem mu_bijective : Bijective (mu (X := X)) := ⟨mu_injective, mu_surjective⟩

/-! ### The homeomorphism onto the maximal spectrum -/

/-- The set of points where `f` does not vanish. -/
def U (f : C(X, ℝ)) : Set X := {x : X | f x ≠ 0}

/-- The set of maximal ideals which do not contain `f`, viewed as a subset of the maximal
spectrum: this is the basic open set `D(f)` of the Zariski topology. -/
def Ut (f : C(X, ℝ)) : Set (MaximalSpectrum C(X, ℝ)) :=
  MaximalSpectrum.toPrimeSpectrum ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum C(X, ℝ)))

@[simp]
theorem mem_Ut {f : C(X, ℝ)} {M : MaximalSpectrum C(X, ℝ)} : M ∈ Ut f ↔ f ∉ M.asIdeal :=
  Iff.rfl

theorem isOpen_U (f : C(X, ℝ)) : IsOpen (U f) :=
  Continuous.isOpen_preimage (map_continuous f) {y : ℝ | y ≠ 0} isOpen_ne

theorem isOpen_Ut (f : C(X, ℝ)) : IsOpen (Ut f) :=
  Continuous.isOpen_preimage MaximalSpectrum.toPrimeSpectrum_continuous
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum C(X, ℝ))) PrimeSpectrum.isOpen_basicOpen

/-- The sets `{x | f x ≠ 0}` form a basis of the topology of `X`. -/
theorem isTopologicalBasis_U : TopologicalSpace.IsTopologicalBasis (Set.range (U (X := X))) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro V ⟨f, rfl⟩
    exact isOpen_U f
  · intro x V hxV hV
    -- Separate `{x}` from the complement of `V`, inside `V`.
    obtain ⟨W, hWopen, hxW, hWV⟩ :=
      normal_exists_closure_subset (isClosed_singleton (x := x)) hV (by simpa using hxV)
    obtain ⟨f, hfzero, hfone, -⟩ :=
      exists_continuous_zero_one_of_isClosed (s := Vᶜ) (t := closure W) hV.isClosed_compl
        isClosed_closure (by
          rw [Set.disjoint_left]
          intro y hy hyW
          exact hy (hWV hyW))
    refine ⟨U f, ⟨f, rfl⟩, ?_, ?_⟩
    · have hfx : f x = 1 := hfone (subset_closure (by simpa using hxW))
      show f x ≠ 0
      rw [hfx]
      exact one_ne_zero
    · intro y hy
      by_contra hyV
      exact hy (hfzero (Set.mem_compl hyV))

/-- The basic open sets `D(f) = {M | f ∉ M}` form a basis of the Zariski topology on the
maximal spectrum (which by definition is the subspace topology from the prime spectrum). -/
theorem isTopologicalBasis_Ut :
    TopologicalSpace.IsTopologicalBasis (Set.range (Ut (X := X))) := by
  have h := TopologicalSpace.IsTopologicalBasis.induced
    (s := PrimeSpectrum.zariskiTopology)
    (MaximalSpectrum.toPrimeSpectrum : MaximalSpectrum C(X, ℝ) → PrimeSpectrum C(X, ℝ))
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := C(X, ℝ)))
  rw [← Set.range_comp] at h
  exact h

theorem mu_preimage_U (f : C(X, ℝ)) : (mu (X := X)) ⁻¹' Ut f = U f := by
  ext x
  simp [mu, U]

theorem mu_image_U (f : C(X, ℝ)) : (mu (X := X)) '' U f = Ut f := by
  ext M
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [U] using hx
  · intro hM
    obtain ⟨x, rfl⟩ := mu_surjective M
    exact ⟨x, by simpa [U] using hM, rfl⟩

theorem continuous_mu : Continuous (mu (X := X)) := by
  refine TopologicalSpace.IsTopologicalBasis.continuous_iff isTopologicalBasis_Ut |>.mpr ?_
  rintro W ⟨f, rfl⟩
  rw [mu_preimage_U]
  exact isOpen_U f

theorem isOpenMap_mu : IsOpenMap (mu (X := X)) := by
  refine TopologicalSpace.IsTopologicalBasis.isOpenMap_iff isTopologicalBasis_U |>.mpr ?_
  rintro V ⟨f, rfl⟩
  rw [mu_image_U]
  exact isOpen_Ut f

theorem mu_isHomeomorph : IsHomeomorph (mu (X := X)) :=
  ⟨continuous_mu, isOpenMap_mu, mu_bijective⟩

/-- The map `x ↦ m x` is a homeomorphism of `X` onto the maximal spectrum of `C(X, ℝ)`. -/
def muHomeomorph : X ≃ₜ MaximalSpectrum C(X, ℝ) :=
  IsHomeomorph.homeomorph (mu (X := X)) mu_isHomeomorph

@[simp]
theorem muHomeomorph_apply (x : X) : muHomeomorph x = mu x := rfl

/-- Atiyah–Macdonald, Chapter 1, Exercise 1.26, all parts:
`m x` is maximal; `mu` is surjective; `mu` is injective; and `mu` is a homeomorphism of `X`
onto the maximal spectrum of `C(X, ℝ)`. -/
theorem solution :
    (∀ x : X, (m x).IsMaximal) ∧ Surjective (mu (X := X)) ∧ Injective (mu (X := X)) ∧
      ∃ e : X ≃ₜ MaximalSpectrum C(X, ℝ), ⇑e = (mu (X := X)) :=
  ⟨m_isMaximal, mu_surjective, mu_injective, muHomeomorph, rfl⟩

end AtiyahMcdonald69.Ex_1_26
