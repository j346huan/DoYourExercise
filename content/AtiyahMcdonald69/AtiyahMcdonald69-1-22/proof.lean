import Mathlib

-- `letI` is the only way to install the ring structures provided by an existential hypothesis.
set_option linter.style.haveILetI false

/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 1.22

**Statement** (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 1, Exercise 22).

* Suppose that `A₁, …, Aₙ` are rings and `A = ∏ⱼ Aⱼ`. Show that `Spec A` is the disjoint union
  of open (and closed) subspaces `Xⱼ`, where `Xⱼ` is canonically homeomorphic with `Spec Aⱼ`.
* Conversely, prove that the following are equivalent for any ring `A`:
  (a) `X = Spec A` is disconnected;
  (b) `A ≅ A₁ × A₂` where `A₁`, `A₂` are nonzero rings;
  (c) `A` has an idempotent `e ≠ 0, 1`.
  Deduce that the spectrum of a local ring is always connected.

Reference proof (natural solution): <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-22>

Formalization choices:
* `Xⱼ` is defined as the range of the canonical map `Spec Aⱼ → Spec (∏ⱼ Aⱼ)`.
* "Disconnected" is the textbook notion: a union of two disjoint nonempty open sets
  (`Disconnected` below); `connected` is Mathlib's `ConnectedSpace`.
* "nonzero ring" is `Nontrivial` (the book's convention that `0 ≠ 1`).
-/

namespace AtiyahMcdonald69.Ex_1_22

universe u

/-! ## Part 1: the spectrum of a finite product -/

section Product

variable {n : ℕ} (A : Fin n → Type u) [∀ i, CommRing (A i)]

/-- `X A j` is the subset of `Spec (∀ i, A i)` of primes coming from `Spec (A j)` under the
canonical map `Spec (A j) → Spec (∏ i, A i)`, `q ↦ (Pi.evalRingHom A j)⁻¹ q`. -/
def X (j : Fin n) : Set (PrimeSpectrum (∀ i, A i)) :=
  Set.range (PrimeSpectrum.comap (Pi.evalRingHom A j))

/-- The coordinate idempotents have pairwise vanishing products. -/
lemma single_one_mul_single_one_eq_zero {i j : Fin n} (h : i ≠ j) :
    Pi.single i (1 : A i) * Pi.single j (1 : A j) = (0 : ∀ i, A i) := by
  ext k
  rw [Pi.mul_apply, Pi.zero_apply]
  rcases eq_or_ne k i with rfl | hki
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hki, zero_mul]

/-- The coordinate idempotents sum to `1`. -/
lemma sum_single_one : (∑ j : Fin n, Pi.single j (1 : A j)) = (1 : ∀ i, A i) := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, Pi.one_apply]
  · intro b _ hb
    exact Pi.single_eq_of_ne (Ne.symm hb) (1 : A b)
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- `Xⱼ` is the basic open set on the `j`-th coordinate idempotent. -/
lemma X_eq_basicOpen (j : Fin n) :
    X A j = (PrimeSpectrum.basicOpen (Pi.single j (1 : A j)) :
      Set (PrimeSpectrum (∀ i, A i))) := by
  have h := PrimeSpectrum.comap_evalRingHom_basicOpen (R := A) j (1 : A j)
  rw [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] at h
  simp only [X, ← h, Set.image_univ]

lemma mem_X_iff (j : Fin n) (p : PrimeSpectrum (∀ i, A i)) :
    p ∈ X A j ↔ Pi.single j (1 : A j) ∉ p.asIdeal := by
  rw [X_eq_basicOpen]
  exact Iff.rfl

lemma isOpen_X (j : Fin n) : IsOpen (X A j) := by
  rw [X_eq_basicOpen]
  exact PrimeSpectrum.isOpen_basicOpen

lemma isClosed_X (j : Fin n) : IsClosed (X A j) := by
  have h := PrimeSpectrum.isClosed_range_comap_of_surjective (A j) (Pi.evalRingHom A j)
    (fun x => ⟨Pi.single j x, by simp⟩)
  simpa only [X] using h

lemma disjoint_X {i j : Fin n} (h : i ≠ j) : Disjoint (X A i) (X A j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  rw [mem_X_iff] at hpi hpj
  have hmem : Pi.single i (1 : A i) * Pi.single j (1 : A j) ∈ p.asIdeal := by
    rw [single_one_mul_single_one_eq_zero A h]
    exact p.asIdeal.zero_mem
  rcases p.isPrime.mem_or_mem hmem with h' | h'
  · exact hpi h'
  · exact hpj h'

lemma iUnion_X : (⋃ j : Fin n, X A j) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ j, Pi.single j (1 : A j) ∈ p.asIdeal := fun j => by
    have h := hcon j
    rwa [mem_X_iff, not_not] at h
  have hone : (1 : ∀ i, A i) ∈ p.asIdeal := by
    rw [← sum_single_one A]
    exact Ideal.sum_mem _ fun j _ => hmem j
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- Each prime of the product lies in exactly one of the `Xⱼ`: it omits exactly one coordinate
idempotent. -/
lemma existsUnique_mem_X (p : PrimeSpectrum (∀ i, A i)) : ∃! j : Fin n, p ∈ X A j := by
  have hp : p ∈ ⋃ j, X A j := by rw [iUnion_X A]; exact Set.mem_univ p
  rw [Set.mem_iUnion] at hp
  obtain ⟨j, hj⟩ := hp
  refine ⟨j, hj, fun k hk => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_X A hne) hk hj

/-- The canonical map `Spec (A j) → X j` is a homeomorphism. -/
noncomputable def XHomeomorph (j : Fin n) : PrimeSpectrum (A j) ≃ₜ X A j :=
  (PrimeSpectrum.isEmbedding_comap_of_surjective (A j) (Pi.evalRingHom A j)
    (fun x => ⟨Pi.single j x, by simp⟩)).toHomeomorph

@[simp]
lemma XHomeomorph_apply (j : Fin n) (p : PrimeSpectrum (A j)) :
    (XHomeomorph A j p : PrimeSpectrum (∀ i, A i)) =
      PrimeSpectrum.comap (Pi.evalRingHom A j) p := rfl

/-- **Atiyah–Macdonald, Ch. 1, Ex. 22, first part.**  The spectrum of a finite product of rings
is the disjoint union of the open and closed subspaces `Xⱼ`, each canonically homeomorphic to
`Spec Aⱼ`. -/
theorem spec_pi_decomposition :
    (∀ j, IsOpen (X A j)) ∧ (∀ j, IsClosed (X A j)) ∧
      (∀ i j, i ≠ j → Disjoint (X A i) (X A j)) ∧
      (⋃ j, X A j = Set.univ) ∧
      (∀ j, ∃ e : PrimeSpectrum (A j) ≃ₜ X A j,
        ∀ p, (e p : PrimeSpectrum (∀ i, A i)) =
          PrimeSpectrum.comap (Pi.evalRingHom A j) p) :=
  ⟨isOpen_X A, isClosed_X A, fun _ _ => disjoint_X A, iUnion_X A,
    fun j => ⟨XHomeomorph A j, XHomeomorph_apply A j⟩⟩

/-- **Part 1, disjoint-union form.**  For a finite family of rings, the spectrum of the product
is the topological disjoint union of the spectra of the factors. -/
theorem spec_pi_homeomorph_sigma :
    Nonempty ((Σ j : Fin n, PrimeSpectrum (A j)) ≃ₜ PrimeSpectrum (∀ i, A i)) :=
  ⟨PrimeSpectrum.sigmaToPiHomeo A⟩

/-- The disjoint-union homeomorphism restricts to the canonical homeomorphism on each summand. -/
lemma sigmaToPiHomeo_sigmaMk (j : Fin n) (p : PrimeSpectrum (A j)) :
    PrimeSpectrum.sigmaToPiHomeo A ⟨j, p⟩ =
      (XHomeomorph A j p : PrimeSpectrum (∀ i, A i)) := rfl

end Product

/-! ## Part 2: `Spec A` is disconnected iff `A` splits as a product of two nonzero rings -/

/-- A topological space is *disconnected* if it is the union of two disjoint nonempty open
subsets. -/
def Disconnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧
    U ∪ V = Set.univ

/-- Negation of disconnectedness is preconnectedness. -/
lemma isPreconnected_univ_of_not_disconnected {X : Type*} [TopologicalSpace X]
    (h : ¬ Disconnected X) : IsPreconnected (Set.univ : Set X) := by
  intro u v hu hv huv hune hvne
  by_contra hcon
  refine h ⟨u, v, hu, hv, ?_, ?_, ?_, ?_⟩
  · simpa using hune
  · simpa using hvne
  · rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp (by simpa using hcon)
  · exact Set.univ_subset_iff.mp huv

lemma preconnectedSpace_of_not_disconnected {X : Type*} [TopologicalSpace X]
    (h : ¬ Disconnected X) : PreconnectedSpace X :=
  PreconnectedSpace.mk (isPreconnected_univ_of_not_disconnected h)

lemma not_disconnected_of_preconnectedSpace {X : Type*} [TopologicalSpace X]
    (h : PreconnectedSpace X) : ¬ Disconnected X := by
  intro hd
  obtain ⟨U, V, hUo, hVo, hUne, hVne, hdisj, hcov⟩ := hd
  have hp := preconnectedSpace_iff_univ.mp h
  have h₁ : (Set.univ ∩ (U ∩ V)).Nonempty :=
    hp U V hUo hVo (by rw [hcov]) (by simpa using hUne) (by simpa using hVne)
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj] at h₁
  simp at h₁

/-- For a nonempty space, `Disconnected` is the negation of Mathlib's `ConnectedSpace`. -/
lemma disconnected_iff_not_connectedSpace {X : Type*} [TopologicalSpace X] [Nonempty X] :
    Disconnected X ↔ ¬ ConnectedSpace X := by
  constructor
  · intro h hc
    exact not_disconnected_of_preconnectedSpace hc.toPreconnectedSpace h
  · intro h
    by_contra hd
    exact h { toPreconnectedSpace := preconnectedSpace_of_not_disconnected hd, toNonempty := inferInstance }

/-- `Disconnected` is the negation of Mathlib's `PreconnectedSpace`. -/
lemma preconnectedSpace_iff_not_disconnected {X : Type*} [TopologicalSpace X] :
    PreconnectedSpace X ↔ ¬ Disconnected X :=
  ⟨not_disconnected_of_preconnectedSpace, preconnectedSpace_of_not_disconnected⟩

/-- A nilpotent idempotent is zero. -/
lemma IsIdempotentElem.eq_zero_of_isNilpotent {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (hn : IsNilpotent e) : e = 0 := by
  obtain ⟨n, hn'⟩ := hn
  rcases n with _ | m
  · rw [pow_zero] at hn'
    calc e = 1 * e := (one_mul e).symm
      _ = 0 * e := by rw [hn']
      _ = 0 := zero_mul e
  · rw [he.pow_eq (Nat.succ_ne_zero m)] at hn'
    exact hn'

/-- A basic open set defined by a nonzero idempotent is nonempty. -/
lemma basicOpen_nonempty_of_isIdempotentElem {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  have hbot : PrimeSpectrum.basicOpen e = ⊥ :=
    SetLike.coe_injective (by rw [hemp, TopologicalSpace.Opens.coe_bot])
  exact h0 (he.eq_zero_of_isNilpotent ((PrimeSpectrum.basicOpen_eq_bot_iff e).mp hbot))

/-- Clopen subsets of `Spec R` and idempotents of `R` correspond, so a separation of `Spec R`
produces a nontrivial idempotent. -/
lemma exists_idempotent_of_disconnected (R : Type u) [CommRing R]
    (h : Disconnected (PrimeSpectrum R)) :
    ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  obtain ⟨U, V, hUo, hVo, hUne, hVne, hdisj, hcov⟩ := h
  have hUV : Uᶜ = V := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ U ∪ V := by rw [hcov]; exact Set.mem_univ x
      rcases hx' with h' | h'
      · exact absurd h' hx
      · exact h'
    · intro hx hxU
      exact Set.disjoint_left.mp hdisj hxU hx
  have hUcl : IsClosed U := by
    have hVo' : IsOpen Uᶜ := hUV.symm ▸ hVo
    exact isOpen_compl_iff.mp hVo'
  obtain ⟨e, he, hUe⟩ := PrimeSpectrum.isClopen_iff.mp ⟨hUcl, hUo⟩
  refine ⟨e, he, ?_, ?_⟩
  · intro h0
    obtain ⟨x, hx⟩ := hUne
    have hx' : x ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
      rw [← hUe]; exact hx
    rw [h0, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot] at hx'
    exact hx'
  · intro h1
    obtain ⟨x, hx⟩ := hVne
    have hxU : x ∈ U := by
      rw [hUe, h1, PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]
      exact Set.mem_univ x
    exact Set.disjoint_left.mp hdisj hxU hx

/-- A nontrivial idempotent cuts `Spec R` into two disjoint nonempty open pieces. -/
lemma disconnected_of_idempotent (R : Type u) [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    Disconnected (PrimeSpectrum R) := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  refine ⟨(PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)),
    (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PrimeSpectrum.isOpen_basicOpen
  · exact PrimeSpectrum.isOpen_basicOpen
  · exact basicOpen_nonempty_of_isIdempotentElem he h0
  · refine basicOpen_nonempty_of_isIdempotentElem he.one_sub ?_
    rw [sub_ne_zero]
    exact Ne.symm h1
  · rw [Set.disjoint_left]
    intro p hp hq
    have hmem : e * (1 - e) ∈ p.asIdeal := by
      rw [hmul]; exact p.asIdeal.zero_mem
    rcases p.isPrime.mem_or_mem hmem with h' | h'
    · exact hp h'
    · exact hq h'
  · refine Set.eq_univ_of_forall fun p => ?_
    by_cases hp : e ∈ p.asIdeal
    · refine Set.mem_union_right _ ?_
      intro hpe
      have hone : (1 : R) ∈ p.asIdeal := by
        have h := p.asIdeal.add_mem hp hpe
        rwa [add_sub_cancel] at h
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    · exact Set.mem_union_left _ hp

theorem disconnected_iff_idempotent (R : Type u) [CommRing R] :
    Disconnected (PrimeSpectrum R) ↔ ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 :=
  ⟨exists_idempotent_of_disconnected R,
    fun ⟨_, he, h0, h1⟩ => disconnected_of_idempotent R he h0 h1⟩

/-- A nontrivial idempotent generates a proper ideal. -/
lemma span_singleton_ne_top_of_isIdempotentElem {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h1 : e ≠ 1) : Ideal.span {e} ≠ ⊤ := by
  intro htop
  have hmem : (1 : R) ∈ Ideal.span {e} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  apply h1
  calc e = e * 1 := (mul_one e).symm
    _ = e * (a * e) := by rw [ha]
    _ = (e * e) * a := by ring
    _ = e * a := by rw [he.eq]
    _ = a * e := by ring
    _ = 1 := ha

/-- If `e` is a nonzero idempotent, the ideal `(1 - e)` is proper. -/
lemma span_singleton_one_sub_ne_top_of_isIdempotentElem {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) : Ideal.span {1 - e} ≠ ⊤ := by
  intro htop
  have hmem : (1 : R) ∈ Ideal.span {1 - e} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have h1e : (1 : R) - e = 1 := by
    calc 1 - e = (1 - e) * 1 := (mul_one _).symm
      _ = (1 - e) * (a * (1 - e)) := by rw [ha]
      _ = ((1 - e) * (1 - e)) * a := by ring
      _ = (1 - e) * a := by rw [he.one_sub.eq]
      _ = a * (1 - e) := by ring
      _ = 1 := ha
  exact h0 (sub_eq_self.mp h1e)

/-- **Concrete form of (c) ⇒ (b).**  A nontrivial idempotent `e` splits `R` as
`R ≃+* (R ⧸ (e)) × (R ⧸ (1 - e))`, and both quotient rings are nonzero. -/
theorem prod_quotient_equiv_of_idempotent (R : Type u) [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    Nontrivial (R ⧸ Ideal.span {e}) ∧ Nontrivial (R ⧸ Ideal.span {1 - e}) ∧
      Nonempty (R ≃+* (R ⧸ Ideal.span {e}) × (R ⧸ Ideal.span {1 - e})) := by
  have hsum : e + (1 - e) = 1 := add_sub_cancel e 1
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  exact ⟨Ideal.Quotient.nontrivial_iff.mpr (span_singleton_ne_top_of_isIdempotentElem he h1),
    Ideal.Quotient.nontrivial_iff.mpr (span_singleton_one_sub_ne_top_of_isIdempotentElem he h0),
    ⟨(AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub hsum hmul).toRingEquiv⟩⟩

/-- A nontrivial idempotent writes `R` as a product of two nonzero rings. -/
theorem prod_decomposition_of_idempotent (R : Type u) [CommRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ∃ (R₁ R₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (_ : Nontrivial R₁)
      (_ : Nontrivial R₂), Nonempty (R ≃+* R₁ × R₂) := by
  obtain ⟨h₁, h₂, ⟨φ⟩⟩ := prod_quotient_equiv_of_idempotent R he h0 h1
  exact ⟨R ⧸ Ideal.span {e}, R ⧸ Ideal.span {1 - e}, inferInstance, inferInstance, h₁, h₂,
    ⟨φ⟩⟩

/-- The spectrum of a product of two nonzero rings is disconnected. -/
lemma disconnected_prod (S T : Type u) [CommRing S] [CommRing T] [Nontrivial S]
    [Nontrivial T] : Disconnected (PrimeSpectrum (S × T)) := by
  have hidem₁ : IsIdempotentElem ((0, 1) : S × T) := by
    show ((0, 1) : S × T) * (0, 1) = (0, 1)
    simp
  have hne₁ : ((0, 1) : S × T) ≠ 0 := by
    intro h
    have h2 := congrArg Prod.snd h
    simp at h2
  have hidem₂ : IsIdempotentElem ((1, 0) : S × T) := by
    show ((1, 0) : S × T) * (1, 0) = (1, 0)
    simp
  have hne₂ : ((1, 0) : S × T) ≠ 0 := by
    intro h
    have h2 := congrArg Prod.fst h
    simp at h2
  refine ⟨(PrimeSpectrum.basicOpen ((0, 1) : S × T) : Set (PrimeSpectrum (S × T))),
    (PrimeSpectrum.basicOpen ((1, 0) : S × T) : Set (PrimeSpectrum (S × T))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PrimeSpectrum.isOpen_basicOpen
  · exact PrimeSpectrum.isOpen_basicOpen
  · exact basicOpen_nonempty_of_isIdempotentElem hidem₁ hne₁
  · exact basicOpen_nonempty_of_isIdempotentElem hidem₂ hne₂
  · rw [Set.disjoint_left]
    intro p hp hq
    have hprod : ((0, 1) : S × T) * (1, 0) = 0 := by
      show ((0, 1) * (1, 0) : S × T) = 0
      simp
    have hmem : ((0, 1) : S × T) * (1, 0) ∈ p.asIdeal := by
      rw [hprod]; exact p.asIdeal.zero_mem
    rcases p.isPrime.mem_or_mem hmem with h' | h'
    · exact hp h'
    · exact hq h'
  · refine Set.eq_univ_of_forall fun p => ?_
    by_cases hp : ((0, 1) : S × T) ∈ p.asIdeal
    · refine Set.mem_union_right _ ?_
      intro hp2
      have hsum : ((0, 1) : S × T) + (1, 0) = 1 := by simp
      have hone : (1 : S × T) ∈ p.asIdeal := by
        rw [← hsum]
        exact p.asIdeal.add_mem hp hp2
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    · exact Set.mem_union_left _ hp

/-- Disconnectedness is transported backwards along a homeomorphism. -/
lemma disconnected_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : Disconnected Y) : Disconnected X := by
  obtain ⟨U, V, hUo, hVo, hUne, hVne, hdisj, hcov⟩ := h
  refine ⟨e ⁻¹' U, e ⁻¹' V, hUo.preimage e.continuous, hVo.preimage e.continuous,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hUne
    exact ⟨e.symm y, by simpa using hy⟩
  · obtain ⟨y, hy⟩ := hVne
    exact ⟨e.symm y, by simpa using hy⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp hdisj hx hx'
  · rw [← Set.preimage_union, hcov, Set.preimage_univ]

theorem disconnected_iff_prod (R : Type u) [CommRing R] :
    Disconnected (PrimeSpectrum R) ↔
      ∃ (R₁ R₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (_ : Nontrivial R₁)
        (_ : Nontrivial R₂), Nonempty (R ≃+* R₁ × R₂) := by
  constructor
  · intro h
    obtain ⟨e, he, h0, h1⟩ := (disconnected_iff_idempotent R).mp h
    exact prod_decomposition_of_idempotent R he h0 h1
  · rintro ⟨R₁, R₂, hc₁, hc₂, hn₁, hn₂, ⟨φ⟩⟩
    letI := hc₁
    letI := hc₂
    letI := hn₁
    letI := hn₂
    have hprod : Disconnected (PrimeSpectrum (R₁ × R₂)) := disconnected_prod R₁ R₂
    exact disconnected_preimage_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv φ) hprod

/-- A local ring has only the idempotents `0` and `1`. -/
lemma eq_zero_or_one_of_isIdempotentElem (R : Type u) [CommRing R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hunit | hunit
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he.one_sub))

/-- **Atiyah–Macdonald, Ch. 1, Ex. 22, second part**: the spectrum of a local ring is
connected. -/
theorem localRing_primeSpectrum_connected (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) := by
  have h : ¬ Disconnected (PrimeSpectrum R) := by
    rw [disconnected_iff_idempotent]
    rintro ⟨e, he, h0, h1⟩
    rcases eq_zero_or_one_of_isIdempotentElem R he with h' | h'
    · exact h0 h'
    · exact h1 h'
  exact { toPreconnectedSpace := preconnectedSpace_of_not_disconnected h, toNonempty := inferInstance }

/-- The three conditions of the exercise are pairwise equivalent; here are the remaining two
implications, so that (a), (b) and (c) are explicitly equivalent. -/
theorem prod_decomposition_iff_idempotent (R : Type u) [CommRing R] :
    (∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1) ↔
      ∃ (R₁ R₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (_ : Nontrivial R₁)
        (_ : Nontrivial R₂), Nonempty (R ≃+* R₁ × R₂) :=
  (disconnected_iff_idempotent R).symm.trans (disconnected_iff_prod R)

/-! ### Sanity checks (non-vacuity of the statements) -/

/-- For one ring, `X₀` is the whole spectrum. -/
example (S : Type u) [CommRing S] : X (fun _ : Fin 1 => S) 0 = Set.univ := by
  rw [X_eq_basicOpen]
  have hone : (Pi.single (0 : Fin 1) (1 : S) : Fin 1 → S) = 1 := by
    funext i
    fin_cases i
    simp
  rw [hone, PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]

/-- `Spec (ℤ/2 × ℤ/3)` is disconnected. -/
example : Disconnected (PrimeSpectrum (ZMod 2 × ZMod 3)) := disconnected_prod _ _

/-- The spectrum of the local ring `ℚ` is connected. -/
example : ConnectedSpace (PrimeSpectrum ℚ) := localRing_primeSpectrum_connected ℚ

end AtiyahMcdonald69.Ex_1_22
