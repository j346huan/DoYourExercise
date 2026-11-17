import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
/-!
# Hartshorne (1977), Algebraic Geometry, Chapter I, Exercise 2.10

"The cone over a projective variety."

Let `Y ⊆ P^n` be a nonempty algebraic set and let `θ : A^{n+1} \ {0} → P^n` be the map sending the
point with affine coordinates `(a₀,…,aₙ)` to the point with homogeneous coordinates
`(a₀ : … : aₙ)`.  The affine cone over `Y` is `C(Y) = θ⁻¹(Y) ∪ {0}`.

(a) `C(Y)` is an algebraic set in `A^{n+1}` whose ideal is `I(Y)`, considered as an ordinary ideal
    of `k[x₀,…,xₙ]`.
(b) `C(Y)` is irreducible if and only if `Y` is.
(c) `dim C(Y) = dim Y + 1`.

The field `k` is algebraically closed, as everywhere in Hartshorne's Chapter I.  Projective space is
the classical one: the set of lines through the origin of `k^{n+1}`, i.e. of nonzero vectors modulo
multiplication by a nonzero scalar.
-/

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ## Homogeneous polynomials and scaling -/

/-- A homogeneous polynomial of degree `d` scales by `c ^ d` when the coordinates are scaled
by `c`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : k) (a : σ → k) :
    MvPolynomial.eval (fun i => c * a i) f = c ^ d * MvPolynomial.eval a f := by
  conv_lhs => rw [as_sum f]
  conv_rhs => rw [as_sum f]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := (hf.degree_eq_sum_deg_support hm).symm
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum m.support (fun i => m i) c, hdeg]
  ring

/-! ## The classical projective space -/

/-- The classical projective space `P^n` over `k`: the set of lines through the origin in
`k^{n+1}`, i.e. of nonzero vectors modulo multiplication by a nonzero scalar. -/
abbrev Proj (k : Type u) [Field k] (n : ℕ) : Type u := Projectivization k (Fin (n + 1) → k)

namespace Proj

/-- The point of `P^n` represented by a nonzero vector. -/
abbrev mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : Proj k n := Projectivization.mk k v hv

/-- A homogeneous polynomial vanishes at a projective point. -/
def IsZeroAt (f : MvPolynomial (Fin (n + 1)) k) (x : Proj k n) : Prop :=
  MvPolynomial.eval x.rep f = 0

/-- Vanishing of a homogeneous polynomial does not depend on the chosen representative of the
projective point. -/
theorem isZeroAt_mk_iff {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hf : f.IsHomogeneous d)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    IsZeroAt f (mk v hv) ↔ MvPolynomial.eval v f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) v hv
  have hrep : (mk v hv).rep = fun i => (a : k) * v i := by
    rw [← ha]; rfl
  rw [IsZeroAt, hrep, eval_smul_of_isHomogeneous hf (a : k)]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero d (Units.ne_zero a))
  · intro h
    rw [h, mul_zero]

/-- The set of homogeneous polynomials (each with a chosen degree). -/
abbrev HomogPoly (k : Type u) [Field k] (n : ℕ) : Type u :=
  {f : MvPolynomial (Fin (n + 1)) k // ∃ d, f.IsHomogeneous d}

/-- The projective zero locus of a set of homogeneous polynomials. -/
def zeroLocus (S : Set (HomogPoly k n)) : Set (Proj k n) :=
  {x | ∀ f ∈ S, IsZeroAt f.1 x}

theorem mem_zeroLocus_iff {S : Set (HomogPoly k n)} {x : Proj k n} :
    x ∈ zeroLocus S ↔ ∀ f ∈ S, IsZeroAt f.1 x := Iff.rfl

theorem zeroLocus_anti_mono {S T : Set (HomogPoly k n)} (h : S ⊆ T) :
    zeroLocus T ⊆ zeroLocus S :=
  fun _ hx f hf => hx f (h hf)

theorem zeroLocus_empty : zeroLocus (∅ : Set (HomogPoly k n)) = Set.univ := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_empty_iff_false, IsEmpty.forall_iff,
    Set.mem_univ]
  simp

theorem zeroLocus_union (S T : Set (HomogPoly k n)) :
    zeroLocus (S ∪ T) = zeroLocus S ∩ zeroLocus T := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

theorem zeroLocus_iUnion {ι : Type*} (S : ι → Set (HomogPoly k n)) :
    zeroLocus (⋃ i, S i) = ⋂ i, zeroLocus (S i) := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_sUnion (A : Set (Set (HomogPoly k n))) :
    zeroLocus (⋃₀ A) = ⋂₀ (zeroLocus '' A) := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_sUnion, Set.mem_sInter, Set.mem_image]
  constructor
  · rintro h Z ⟨S, hS, rfl⟩ f hf
    exact h f ⟨S, hS, hf⟩
  · rintro h f ⟨S, hS, hf⟩
    exact h (zeroLocus S) ⟨S, hS, rfl⟩ f hf

theorem zeroLocus_univ : zeroLocus (Set.univ : Set (HomogPoly k n)) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  refine hj ?_
  have h := hx ⟨MvPolynomial.X j, 1, MvPolynomial.isHomogeneous_X (R := k) j⟩ (Set.mem_univ _)
  simpa [IsZeroAt] using h

/-- The set of products of one member of `S` with one member of `T`. -/
def mulSet (S T : Set (HomogPoly k n)) : Set (HomogPoly k n) :=
  {h | ∃ f ∈ S, ∃ g ∈ T, h.1 = f.1 * g.1}

theorem zeroLocus_mulSet (S T : Set (HomogPoly k n)) :
    zeroLocus (mulSet S T) = zeroLocus S ∪ zeroLocus T := by
  ext x
  rw [Set.mem_union, mem_zeroLocus_iff]
  constructor
  · intro hx
    by_cases h : ∀ f ∈ S, IsZeroAt f.1 x
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨f, hf, hfx⟩ := h
      intro g hg
      obtain ⟨df, hdf⟩ := f.2
      obtain ⟨dg, hdg⟩ := g.2
      have h2 : IsZeroAt (f.1 * g.1) x :=
        hx ⟨f.1 * g.1, df + dg, hdf.mul hdg⟩ ⟨f, hf, g, hg, rfl⟩
      rw [IsZeroAt, map_mul] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hfx
      · exact h3
  · rintro (h | h)
    · intro h' hf'
      obtain ⟨f', hf', g', hg', heq⟩ := hf'
      rw [IsZeroAt, heq, map_mul, h f' hf', zero_mul]
    · intro h' hf'
      obtain ⟨f', hf', g', hg', heq⟩ := hf'
      rw [IsZeroAt, heq, map_mul, h g' hg', mul_zero]

/-- The Zariski topology on `P^n`: closed sets are zero loci of sets of homogeneous
polynomials. -/
noncomputable abbrev zariskiTopology : TopologicalSpace (Proj k n) :=
  TopologicalSpace.ofClosed (Set.range (zeroLocus (k := k) (n := n)))
    ⟨Set.univ, zeroLocus_univ⟩
    (by
      intro A hA
      refine ⟨⋃₀ {S : Set (HomogPoly k n) | zeroLocus S ∈ A}, ?_⟩
      rw [zeroLocus_sUnion]
      congr 1
      ext Z
      constructor
      · rintro ⟨S, hS, rfl⟩
        exact hS
      · intro hZ
        obtain ⟨S, rfl⟩ := hA hZ
        exact ⟨S, hZ, rfl⟩)
    (by
      rintro A ⟨S, rfl⟩ B ⟨T, rfl⟩
      exact ⟨mulSet S T, zeroLocus_mulSet S T⟩)

/-- A set of projective points is closed for the Zariski topology iff it is the zero locus of a
set of homogeneous polynomials. -/
def IsProjClosed (Z : Set (Proj k n)) : Prop := ∃ S : Set (HomogPoly k n), zeroLocus S = Z

end Proj

/-- The projective Zariski topology. -/
noncomputable abbrev projTopologicalSpace (k : Type u) [Field k] (n : ℕ) : TopologicalSpace (Proj k n) :=
  Proj.zariskiTopology

attribute [instance] projTopologicalSpace

namespace Proj

theorem isOpen_iff (U : Set (Proj k n)) :
    IsOpen U ↔ Uᶜ ∈ Set.range (zeroLocus (k := k) (n := n)) := Iff.rfl

theorem isClosed_iff (Z : Set (Proj k n)) :
    IsClosed Z ↔ Z ∈ Set.range (zeroLocus (k := k) (n := n)) := by
  constructor
  · intro h
    have h1 : (Zᶜ)ᶜ ∈ Set.range (zeroLocus (k := k) (n := n)) := (isOpen_iff Zᶜ).1 h.isOpen_compl
    rwa [compl_compl] at h1
  · intro h
    exact ⟨(isOpen_iff Zᶜ).2 (by rwa [compl_compl])⟩

theorem isClosed_of_isProjClosed {Z : Set (Proj k n)} (hZ : IsProjClosed Z) : IsClosed Z :=
  (isClosed_iff Z).2 hZ

theorem isProjClosed_zeroLocus (S : Set (HomogPoly k n)) : IsProjClosed (zeroLocus S) :=
  ⟨S, rfl⟩

theorem isProjClosed_iff_isClosed (Z : Set (Proj k n)) : IsProjClosed Z ↔ IsClosed Z :=
  (isClosed_iff Z).symm

end Proj

end Hartshorne77.Ex_I_2_11

/-! ## The affine cone and the vanishing ideal -/

namespace Hartshorne77.Ex_I_2_11
universe u
variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

/-- The affine cone over a set of projective points: the union of the lines through the origin
lying over `Y`, together with the origin. -/
def cone (Y : Set (Proj k n)) : Set (Fin (n + 1) → k) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, mk v hv ∈ Y}

/-- `I(Y)`: the homogeneous ideal of `Y`, i.e. the ideal generated by all homogeneous polynomials
vanishing on `Y`. -/
noncomputable def vanishingIdeal (Y : Set (Proj k n)) : Ideal (MvPolynomial (Fin (n + 1)) k) :=
  Ideal.span {f | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x}

theorem subset_vanishingIdeal {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (h : ∀ x ∈ Y, IsZeroAt f x) : f ∈ vanishingIdeal Y :=
  Ideal.subset_span ⟨d, hf, h⟩

theorem vanishingIdeal_mem_iff {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} :
    f ∈ vanishingIdeal Y ↔
      f ∈ Ideal.span {g | ∃ d, g.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt g x} :=
  Iff.rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem vanishingIdeal_isHomogeneous (Y : Set (Proj k n)) :
    (vanishingIdeal Y).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := by
  have h := Ideal.homogeneous_span (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
    {f : MvPolynomial (Fin (n + 1)) k | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x}
    (fun f hf => by
      obtain ⟨d, hd, -⟩ := hf
      exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule d f).2 hd⟩)
  exact h

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem eval_zero_of_isHomogeneous_pos {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) :
    MvPolynomial.eval (0 : Fin (n + 1) → k) f = 0 := by
  have h := eval_smul_of_isHomogeneous hf (0 : k) (fun _ : Fin (n + 1) => (1 : k))
  simpa [zero_pow hd.ne'] using h

/-- If `f` is homogeneous of degree `0` and vanishes at some projective point then `f = 0`. -/
theorem eq_zero_of_isHomogeneous_zero {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous 0)
    {x : Proj k n} (hx : IsZeroAt f x) : f = 0 := by
  have hC : f = MvPolynomial.C (f.coeff 0) := by
    have h := hf.totalDegree_le
    rw [Nat.le_zero] at h
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
  rw [hC] at hx ⊢
  simpa [IsZeroAt] using hx

/-- A homogeneous polynomial vanishing on `Y` vanishes at the origin of the cone. -/
theorem eval_zero_of_mem_gens {Y : Set (Proj k n)} (hY : Y.Nonempty)
    {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ x ∈ Y, IsZeroAt f x) : MvPolynomial.eval (0 : Fin (n + 1) → k) f = 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    obtain ⟨x, hx⟩ := hY
    rw [eq_zero_of_isHomogeneous_zero hf (h x hx)]
    simp
  · exact eval_zero_of_isHomogeneous_pos hd hf

/-- The cone over `Y` is contained in the affine zero locus of `I(Y)`. -/
theorem cone_subset_zeroLocus {Y : Set (Proj k n)} (hY : Y.Nonempty) :
    cone Y ⊆ MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) := by
  intro v hv
  rw [MvPolynomial.mem_zeroLocus_iff]
  have hgen : ∀ f ∈ {f : MvPolynomial (Fin (n + 1)) k | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x},
      MvPolynomial.eval v f = 0 := by
    rintro f ⟨d, hd, hf⟩
    rcases hv with rfl | ⟨hvne, hvY⟩
    · exact eval_zero_of_mem_gens hY hd hf
    · exact (isZeroAt_mk_iff hd hvne).1 (hf _ hvY)
  have hle : vanishingIdeal Y ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [vanishingIdeal, Ideal.span_le]
    intro f hf
    simpa using hgen f hf
  intro f hf
  simpa using hle hf

/-- Conversely, the affine zero locus of `I(Y)` is contained in the cone over `Y`. -/
theorem zeroLocus_subset_cone {Y : Set (Proj k n)} (hY : IsProjClosed Y) :
    MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) ⊆ cone Y := by
  obtain ⟨S, rfl⟩ := hY
  intro v hv
  rcases eq_or_ne v 0 with rfl | hvne
  · exact Or.inl rfl
  · refine Or.inr ⟨hvne, ?_⟩
    have hv' : ∀ p ∈ vanishingIdeal (zeroLocus S), MvPolynomial.eval v p = 0 := by
      intro p hp
      simp only [MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval] at hv
      exact hv p hp
    intro g hg
    have hgen : g.1 ∈ vanishingIdeal (zeroLocus S) := by
      obtain ⟨d, hd⟩ := g.2
      refine subset_vanishingIdeal hd fun x hx => by simpa [IsZeroAt] using hx g hg
    obtain ⟨d, hd⟩ := g.2
    exact (isZeroAt_mk_iff hd hvne).2 (hv' g.1 hgen)

/-- **(a)** The cone over a closed set is the affine algebraic set defined by the ideal `I(Y)`. -/
theorem cone_eq_zeroLocus {Y : Set (Proj k n)} (hY : IsProjClosed Y) (hne : Y.Nonempty) :
    cone Y = MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) :=
  Set.Subset.antisymm (cone_subset_zeroLocus hne) (zeroLocus_subset_cone hY)

end Proj

end Hartshorne77.Ex_I_2_11

/-! ## Affine dimension theory (accepted Hartshorne I.1.8 infrastructure) -/

namespace Hartshorne77.Ex_I_2_11
section Krull

variable {A : Type*} [CommRing A]

/-- In a Noetherian domain, a prime minimal over a nonzero principal ideal has height one. -/
theorem Ideal.height_eq_one_of_mem_minimalPrimes [IsNoetherianRing A] [IsDomain A]
    {t : A} (ht : t ≠ 0) {p : Ideal A} (hp : p ∈ (Ideal.span {t}).minimalPrimes) :
    p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
  have h1 : (1 : ℕ∞) ≤ (Ideal.span {t}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  refine le_trans h1 ?_
  rw [Ideal.height_eq_inf_minimalPrimes]
  exact iInf₂_le p hp

/-- The image of a prime minimal over `I` in `A ⧸ I` has height zero. -/
theorem Ideal.height_map_quotient_eq_zero [IsNoetherianRing A] {I P : Ideal A}
    (h : P ∈ I.minimalPrimes) : (P.map (Ideal.Quotient.mk I)).height = 0 := by
  have hP : P.IsPrime := h.isPrime
  have : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime h.le
  have key : P.map (Ideal.Quotient.mk I) ∈ minimalPrimes (A ⧸ I) := by
    rw [Ideal.minimalPrimes_eq_comap] at h
    obtain ⟨Q, hQ, hQP⟩ := h
    rw [← hQP]
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
    exact hQ
  rw [Ideal.height_eq_zero_iff]
  exact key

/-- Height and dimension are preserved by integral injective extensions of domains. -/
theorem Ideal.height_eq_height_under_of_isIntegral {B S : Type*} [CommRing B] [CommRing S]
    [IsDomain B] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S] [FaithfulSMul B S]
    [IsNoetherianRing B] [IsNoetherianRing S] [Algebra.HasGoingDown B S] {P : Ideal S} [P.IsPrime] :
    P.height = (P.under B).height := by
  have : P.LiesOver (P.under B) := ⟨rfl⟩
  have h2 : (P.map (Ideal.Quotient.mk ((P.under B).map (algebraMap B S)))).height = 0 :=
    Ideal.height_map_quotient_eq_zero (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := B) P)
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under B) P, h2, add_zero]

end Krull

section IntegralDim

variable {B S : Type*} [CommRing B] [CommRing S] [IsDomain B] [IsDomain S] [Algebra B S]
  [Algebra.IsIntegral B S] [FaithfulSMul B S] [IsNoetherianRing B] [IsNoetherianRing S]
  [Algebra.HasGoingDown B S]

/-- Integral injective extensions of Noetherian domains have the same Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective : ringKrullDim S = ringKrullDim B := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := P)
    rw [h]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro q hq
    obtain ⟨Q, -, hQprime, hQeq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := S) q (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B S)]; exact bot_le)
    haveI := hQprime
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := Q)
    show q.height ≤ ringKrullDim S
    rw [← hQeq, ← h]
    exact Ideal.height_le_ringKrullDim_of_isPrime

end IntegralDim

section Concat

variable {A : Type*} [CommRing A]

/-- Concatenation of chains: if `p` is a prime of height one in a domain, then passing to
`A ⧸ p` lowers heights by at most one. -/
theorem Ideal.height_map_quotient_add_one_le [IsNoetherianRing A] [IsDomain A] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1) :
    (q.map (Ideal.Quotient.mk p)).height + 1 ≤ q.height := by
  have hp0 : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hp
    exact zero_ne_one hp
  haveI : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨lq, hlq, hlenq⟩ := Ideal.exists_ltSeries_length_eq_height (q.map (Ideal.Quotient.mk p))
  set F : LTSeries (PrimeSpectrum A) :=
    lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk p))
      (RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective) with hF
  have hbot : (⊥ : PrimeSpectrum A) < F.head := by
    have hple : p ≤ F.head.asIdeal := by
      rw [hF]
      show p ≤ Ideal.comap (Ideal.Quotient.mk p) _
      rw [← Ideal.map_le_iff_le_comap]
      simp
    exact (bot_lt_iff_ne_bot.mpr hp0).trans_le hple
  let G : LTSeries (PrimeSpectrum A) := F.cons ⊥ hbot
  have hFlast : F.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    rw [hF]
    change PrimeSpectrum.comap (Ideal.Quotient.mk p) (RelSeries.last lq) = _
    rw [hlq]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hcomap : Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (A ⧸ p)) = p := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, sup_of_le_left hpq]
  have hlenF : F.length = lq.length := by simp [F]
  have hlenG : G.length = F.length + 1 := by simp [G]
  have hGlast : G.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    change (F.cons ⊥ hbot).last = _
    rw [RelSeries.last_cons, hFlast]
  have hlen : G.length = (q.map (Ideal.Quotient.mk p)).height + 1 := by
    rw [hlenG, hlenF, ← hlenq]
    push_cast
    ring
  rw [← hlen]
  have h := Order.length_le_height (p := G) (x := (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A))
    (le_of_eq hGlast)
  rwa [← PrimeSpectrum.height_eq_orderHeight] at h

end Concat
section PointHeight

variable (k : Type*) [Field k]

/-- Substitution sending `X i` to the constant `a i` for `i < j`, and fixing the other variables. -/
noncomputable def substBelow {s : ℕ} (j : ℕ) (a : Fin s → k) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  MvPolynomial.aeval fun i => if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k)
    else MvPolynomial.X i

lemma substBelow_X {s : ℕ} (j : ℕ) (a : Fin s → k) (i : Fin s) :
    substBelow k j a (MvPolynomial.X i) =
      if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i := by
  simp [substBelow]

lemma substBelow_zero {s : ℕ} (a : Fin s → k) : substBelow k 0 a = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substBelow_X]

lemma substBelow_succ {s : ℕ} (j : ℕ) (a : Fin s → k) :
    substBelow k (j + 1) a = (MvPolynomial.aeval fun (i : Fin s) =>
      if (i : ℕ) = j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i).comp
      (substBelow k j a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, substBelow_X, substBelow_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega), MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  · rw [if_neg h]
    by_cases h2 : (i : ℕ) = j
    · rw [MvPolynomial.aeval_X, if_pos h2, if_pos (by omega)]
    · rw [MvPolynomial.aeval_X, if_neg h2, if_neg (by omega)]

lemma ker_substBelow_antitone {s : ℕ} (j : ℕ) (a : Fin s → k) :
    RingHom.ker (substBelow k j a) ≤ RingHom.ker (substBelow k (j + 1) a) := by
  intro f hf
  simp only [RingHom.mem_ker] at hf ⊢
  rw [substBelow_succ, AlgHom.comp_apply, hf, map_zero]

lemma X_sub_C_mem_ker_substBelow_succ {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∈
      RingHom.ker (substBelow k (j + 1) a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_pos (show ((⟨j, hj⟩ : Fin s) : ℕ) < j + 1 from by simp)]
  simp

lemma X_sub_C_notMem_ker_substBelow {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∉
      RingHom.ker (substBelow k j a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_neg (show ¬ ((⟨j, hj⟩ : Fin s) : ℕ) < j from by simp)]
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => a ⟨j, hj⟩ + 1)) h
  simp at h2

end PointHeight

section Height

variable (k : Type*) [Field k]

/-- The ideal of polynomials vanishing at a point of affine `s`-space has height `s`. -/
theorem vanishingIdeal_singleton_height (s : ℕ) (a : Fin s → k) :
    (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height = ↑s := by
  have hker : RingHom.ker (substBelow k s a) = MvPolynomial.vanishingIdeal k {a} := by
    have heq : substBelow k s a =
        (Algebra.ofId k (MvPolynomial (Fin s) k)).comp (MvPolynomial.aeval a) := by
      rw [MvPolynomial.comp_aeval]
      apply MvPolynomial.algHom_ext
      intro i
      rw [substBelow_X, if_pos i.isLt, MvPolynomial.aeval_X, Algebra.ofId_apply,
        MvPolynomial.algebraMap_eq]
    have hinj : Function.Injective (algebraMap k (MvPolynomial (Fin s) k)) :=
      FaithfulSMul.algebraMap_injective k _
    rw [heq]
    ext p
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Algebra.ofId_apply,
      MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : (MvPolynomial.aeval a) p = 0 := hinj (by simpa using h)
      intro x hx
      rw [hx]
      exact h0
    · intro h
      rw [h a rfl, map_zero]
  have hlower : (↑s : ℕ∞) ≤ (MvPolynomial.vanishingIdeal k {a} :
      Ideal (MvPolynomial (Fin s) k)).height := by
    rw [← hker]
    have key : ∀ j ≤ s, (↑j : ℕ∞) ≤ (RingHom.ker (substBelow k j a)).height := by
      intro j
      induction j with
      | zero => intro _; exact bot_le
      | succ m ih =>
        intro hm
        have hms : m < s := by omega
        have h1 : (RingHom.ker (substBelow k m a)).IsPrime := RingHom.ker_isPrime _
        have h2 : (RingHom.ker (substBelow k (m + 1) a)).IsPrime := RingHom.ker_isPrime _
        have hlt : RingHom.ker (substBelow k m a) < RingHom.ker (substBelow k (m + 1) a) :=
          lt_of_le_of_ne (ker_substBelow_antitone k m a)
            (fun heq => X_sub_C_notMem_ker_substBelow k m hms a (heq ▸
              X_sub_C_mem_ker_substBelow_succ k m hms a))
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have him := ih (by omega : m ≤ s)
        calc (↑(m + 1) : ℕ∞) = (↑m : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (substBelow k m a)).height + 1 := by gcongr
          _ ≤ (RingHom.ker (substBelow k (m + 1) a)).height := hstep
    exact key s le_rfl
  have hupper : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height ≤ ↑s := by
    haveI : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).IsMaximal :=
      inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := MvPolynomial.vanishingIdeal k {a})
      (Ideal.IsMaximal.ne_top ‹(MvPolynomial.vanishingIdeal k {a} :
        Ideal (MvPolynomial (Fin s) k)).IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  exact le_antisymm hupper hlower

end Height

section DimensionDrop

variable {A : Type*} [CommRing A]

/-- Quotient by a prime of height one decreases the Krull dimension by at most one. -/
theorem ringKrullDim_quotient_add_one_le_of_height_eq_one [IsNoetherianRing A] [IsDomain A]
    {p : Ideal A} [hp : p.IsPrime] (h1 : p.height = 1) [FiniteRingKrullDim (A ⧸ p)] :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by
  have key : ∀ (M : Ideal (A ⧸ p)), M.IsMaximal → (↑(M.height + 1) : WithBot ℕ∞) ≤ ringKrullDim A := by
    intro M hM
    haveI := hM
    have hcomap : (Ideal.comap (Ideal.Quotient.mk p) M).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hpcomap : p ≤ Ideal.comap (Ideal.Quotient.mk p) M := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
      exact bot_le
    have hmap : (Ideal.comap (Ideal.Quotient.mk p) M).map (Ideal.Quotient.mk p) = M :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
    have h := Ideal.height_map_quotient_add_one_le (p := p)
      (q := Ideal.comap (Ideal.Quotient.mk p) M) hpcomap h1
    rw [hmap] at h
    have h' : (↑(M.height + 1) : WithBot ℕ∞) ≤ ↑((Ideal.comap (Ideal.Quotient.mk p) M).height) := by
      rw [WithBot.coe_le_coe]
      exact h
    exact h'.trans (Ideal.height_le_ringKrullDim_of_ne_top hcomap.ne_top)
  obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := A ⧸ p)
  calc ringKrullDim (A ⧸ p) + 1 = (↑M.height : WithBot ℕ∞) + 1 := by rw [← hMh]
    _ = ↑(M.height + 1) := by rw [WithBot.coe_add]; norm_cast
    _ ≤ ringKrullDim A := key M hMmax

end DimensionDrop

section Hypersurface

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A hypersurface in affine `s`-space has dimension one less than `s`. -/
theorem MvPolynomial.ringKrullDim_quotient_span_singleton {s : ℕ}
    {g : MvPolynomial (Fin s) k} (hg : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime] :
    ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1
      = ringKrullDim (MvPolynomial (Fin s) k) := by
  haveI hBnoeth : IsNoetherianRing (MvPolynomial (Fin s) k) := inferInstance
  have hgu : ¬ IsUnit g := fun h => hgp.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have htop : Ideal.span {g} ≠ ⊤ := hgp.ne_top
  haveI hquo : Nontrivial (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr htop
  have hh : (Ideal.span {g}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg) hgu
  have hmaxB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  haveI hfin : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top
        (by rw [hmaxB]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le (Ideal.span {g}))
  refine le_antisymm (ringKrullDim_quotient_add_one_le_of_height_eq_one hh) ?_
  obtain ⟨m, hmmax, hgm⟩ := Ideal.exists_le_maximal (Ideal.span {g}) htop
  haveI := hmmax
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hmmax
  have hms : m.height = ↑s := by
    rw [ha]
    exact vanishingIdeal_singleton_height k s a
  have hkey : (↑m.height : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by
    haveI : (Ideal.map (Ideal.Quotient.mk (Ideal.span {g})) m).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hgm
    have h1 : m.height ≤ (m.map (Ideal.Quotient.mk (Ideal.span {g}))).height +
        (Ideal.span {g}).spanFinrank :=
      Ideal.height_le_height_add_spanFinrank_of_le hgm
    have h2 : (Ideal.span {g}).spanFinrank ≤ 1 := by
      simpa using Submodule.spanFinrank_span_le_encard ({g} : Set (MvPolynomial (Fin s) k))
    have h4 : (↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
      Ideal.height_le_ringKrullDim_of_isPrime
    have h1' : (↑m.height : WithBot ℕ∞) ≤
        ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := by
      exact_mod_cast h1
    calc (↑m.height : WithBot ℕ∞)
        ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := h1'
      _ ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + 1 := by
          gcongr
          exact_mod_cast h2
      _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by gcongr
  calc ringKrullDim (MvPolynomial (Fin s) k) = (↑s : WithBot ℕ∞) := hmaxB
    _ = (↑m.height : WithBot ℕ∞) := by rw [hms]; norm_num
    _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := hkey

end Hypersurface

section MainAlgebra

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **Hartshorne I.1.8, algebraic form.**  Let `S` be a finitely generated domain over an
algebraically closed field `k`, let `t ∈ S` be nonzero and not a unit, and let `p` be a prime
minimal over `(t)`.  Then `dim S/p = dim S - 1`, i.e. `dim S/p + 1 = dim S`. -/
theorem ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes
    {S : Type*} [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    {t : S} (ht : t ≠ 0) (htu : ¬ IsUnit t) {p : Ideal S} [hp : p.IsPrime]
    (hpm : p ∈ (Ideal.span {t}).minimalPrimes) :
    ringKrullDim (S ⧸ p) + 1 = ringKrullDim S := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have h1 : p.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes ht hpm
  -- Noether normalization
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k S
  let : Algebra (MvPolynomial (Fin s) k) S := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) S = g.toRingHom := RingHom.algebraMap_toAlgebra _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) S := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hginj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) S := by
    have : Module.Finite (MvPolynomial (Fin s) k) S := hgfin
    infer_instance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) k) S := inferInstance
  have hB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hS : ringKrullDim S = ↑s := by
    rw [ringKrullDim_eq_of_integral_injective (B := MvPolynomial (Fin s) k), hB]
  -- upper bound
  haveI : FiniteRingKrullDim (S ⧸ p) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top (by rw [hS]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le p)
  have hupper : ringKrullDim (S ⧸ p) + 1 ≤ ringKrullDim S :=
    ringKrullDim_quotient_add_one_le_of_height_eq_one h1
  -- the contraction `q` of `p` to the polynomial ring
  set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq
  haveI hqprime : q.IsPrime := Ideal.IsPrime.under _ p
  have hq1 : q.height = 1 := by
    rw [hq, ← Ideal.height_eq_height_under_of_isIntegral (B := MvPolynomial (Fin s) k) (P := p), h1]
  -- `q` is principal
  have hqne : q ≠ ⊥ := fun h => by
    rw [h] at hq1
    exact absurd hq1 (by simp)
  obtain ⟨h, hh⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq1
  have hqspan : q = Ideal.span {h} := hh
  have hhne : h ≠ 0 := by
    rintro rfl
    exact hqne (by rw [hqspan, Ideal.span_singleton_eq_bot])
  haveI hqspanprime : (Ideal.span {h}).IsPrime := hqspan ▸ hqprime
  have hgen : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = ringKrullDim (MvPolynomial (Fin s) k) := by
    rw [hqspan]
    exact MvPolynomial.ringKrullDim_quotient_span_singleton k hhne
  -- lower bound via chain lifting
  haveI : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ q) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · have h2 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = (↑s : WithBot ℕ∞) := by
        rw [hgen, hB]
      intro htop'
      rw [htop'] at h2
      exact absurd h2.symm (by
        intro h; exact ENat.natCast_ne_top s (WithBot.coe_injective h))
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · exfalso
      rw [hs0] at hS
      have hp0 : (↑p.height : WithBot ℕ∞) ≤ (↑(0 : ℕ) : WithBot ℕ∞) := by
        rw [← hS]
        exact Ideal.height_le_ringKrullDim_of_isPrime
      have hp0' : p.height ≤ (0 : ℕ∞) := by simpa using hp0
      rw [h1] at hp0'
      simp at hp0'
    · exact hs
  have hs1 : (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := by
    have h3 : s = (s - 1) + 1 := (Nat.sub_add_cancel hspos).symm
    rw [h3]
    push_cast
    ring
  have hsm1 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) = (↑(s - 1) : WithBot ℕ∞) := by
    have h2 := hgen
    rw [hB] at h2
    rw [hs1] at h2
    exact ENat.WithBot.add_one_cancel.mp h2
  have hlow : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) ≤ ringKrullDim (S ⧸ p) := by
    rw [hsm1]
    haveI hLO : p.LiesOver q := ⟨hq⟩
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : FaithfulSMul (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : Algebra.HasGoingUp (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin s) k ⧸ q)
    haveI := hMmax
    obtain ⟨l, hl, hlen⟩ := Ideal.exists_ltSeries_length_eq_height M
    have hMheight : M.height = (↑(s - 1) : ℕ∞) := by
      have h : (↑M.height : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by
        rw [hMh, hsm1]
      exact WithBot.coe_injective h
    have hlen' : l.length = s - 1 := by
      have h : (↑l.length : ℕ∞) = ↑(s - 1) := by rw [hlen, hMheight]
      exact Nat.cast_injective h
    have hhead : (RelSeries.head l).asIdeal.IsPrime := (RelSeries.head l).isPrime
    obtain ⟨Q, -, hQprime, hQover⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := MvPolynomial (Fin s) k ⧸ q)
        (S := S ⧸ p) ((RelSeries.head l).asIdeal) (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
    haveI := hQprime
    haveI hQlo : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQover.symm⟩
    obtain ⟨L, hLlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    have hL : L.length = s - 1 := by rw [hLlen, hlen']
    have hL' : (↑L.length : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by rw [hL]
    calc (↑(s - 1) : WithBot ℕ∞) = (↑L.length : WithBot ℕ∞) := hL'.symm
      _ ≤ ↑(⨆ p : LTSeries (PrimeSpectrum (S ⧸ p)), (↑p.length : ℕ∞)) := by
          exact WithBot.coe_le_coe.mpr
            (le_iSup (fun p : LTSeries (PrimeSpectrum (S ⧸ p)) => (↑p.length : ℕ∞)) L)
      _ = ringKrullDim (S ⧸ p) := by
          rw [← Order.krullDim_eq_iSup_length]
          rfl
  refine le_antisymm hupper ?_
  rw [hS]
  calc (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := hs1
    _ ≤ ringKrullDim (S ⧸ p) + 1 := by
        have h2 := hlow
        rw [hsm1] at h2
        exact add_le_add h2 (le_refl (1 : WithBot ℕ∞))

end MainAlgebra

section Zariski

variable (k : Type*) [Field k] (n : ℕ)

/-- The zero loci of the ideals of `k[X_1,…,X_n]`, i.e. the closed sets of the Zariski topology
on affine `n`-space `k^n`. -/
def zarClosed : Set (Set (Fin n → k)) :=
  {s | ∃ I : Ideal (MvPolynomial (Fin n) k), s = MvPolynomial.zeroLocus k I}

lemma zarClosed_empty : (∅ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊤, by simp⟩

lemma zarClosed_univ : (Set.univ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊥, by rw [MvPolynomial.zeroLocus_bot]; exact rfl⟩

lemma zeroLocus_mul (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k (I * J) =
      MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra h
    simp only [Set.mem_union, not_or] at h
    obtain ⟨h1, h2⟩ := h
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at h1 h2
    obtain ⟨p, hp, hp0⟩ := h1
    obtain ⟨q, hq, hq0⟩ := h2
    have hpq : (MvPolynomial.aeval x) (p * q) = 0 := hx (p * q) (Ideal.mul_mem_mul hp hq)
    rw [map_mul] at hpq
    rcases mul_eq_zero.mp hpq with h | h
    · exact hp0 h
    · exact hq0 h
  · intro x hx
    rcases hx with h | h
    · exact fun p hp => h p (Ideal.mul_le_left hp)
    · exact fun p hp => h p (Ideal.mul_le_right hp)

lemma zarClosed_sInter {A : Set (Set (Fin n → k))} (hA : A ⊆ zarClosed k n) :
    ⋂₀ A ∈ zarClosed k n := by
  refine ⟨MvPolynomial.vanishingIdeal k (⋂₀ A),
    le_antisymm (MvPolynomial.zeroLocus_vanishingIdeal_le _) ?_⟩
  intro x hx s hs
  obtain ⟨I, hI⟩ := hA hs
  rw [hI]
  intro p hp
  exact hx p fun y hy => by
    have hy' : y ∈ MvPolynomial.zeroLocus k I := hI ▸ (hy s hs)
    exact hy' p hp

lemma zarClosed_union {s t : Set (Fin n → k)} (hs : s ∈ zarClosed k n)
    (ht : t ∈ zarClosed k n) : s ∪ t ∈ zarClosed k n := by
  obtain ⟨I, rfl⟩ := hs
  obtain ⟨J, rfl⟩ := ht
  exact ⟨I * J, (zeroLocus_mul k n I J).symm⟩

/-- The Zariski topology on affine `n`-space over `k`. -/
noncomputable instance : TopologicalSpace (Fin n → k) :=
  TopologicalSpace.ofClosed (zarClosed k n) (zarClosed_empty k n)
    (fun A hA => zarClosed_sInter k n hA) (fun a ha b hb => zarClosed_union k n ha hb)

lemma isOpen_iff_zarClosed {s : Set (Fin n → k)} : IsOpen s ↔ sᶜ ∈ zarClosed k n :=
  Iff.rfl

lemma isClosed_iff_zarClosed {s : Set (Fin n → k)} : IsClosed s ↔ s ∈ zarClosed k n := by
  rw [← isOpen_compl_iff, isOpen_iff_zarClosed, compl_compl]

lemma isClosed_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    IsClosed (MvPolynomial.zeroLocus k I) := by
  rw [isClosed_iff_zarClosed]
  exact ⟨I, rfl⟩

end Zariski

section Dictionary

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

lemma vanishingIdeal_singleton_mem_zeroLocus_iff (x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    p ∈ MvPolynomial.vanishingIdeal k {x} ↔ (MvPolynomial.aeval x) p = 0 :=
  MvPolynomial.mem_vanishingIdeal_singleton_iff x p

/-- The zero locus of a prime ideal is an irreducible closed set. -/
lemma zeroLocus_irreducible {P : Ideal (MvPolynomial (Fin n) k)} (hP : P.IsPrime) :
    IsIrreducible (MvPolynomial.zeroLocus k P) := by
  haveI := hP
  have hIV : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) = P :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
  constructor
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) P
    rw [hempty, MvPolynomial.vanishingIdeal_empty] at h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ P := by
      rw [← hP.radical, ← h]
      exact Submodule.mem_top
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z1 z2 hz1 hz2 hsub
    rw [isClosed_iff_zarClosed] at hz1 hz2
    obtain ⟨I, hI⟩ := hz1
    obtain ⟨J, hJ⟩ := hz2
    have hIJ : I * J ≤ P := by
      rw [← hIV, ← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, zeroLocus_mul]
      rw [hI, hJ] at hsub
      exact hsub
    rcases (Ideal.IsPrime.mul_le hP).mp hIJ with h | h
    · left
      rw [hI]
      exact MvPolynomial.zeroLocus_anti_mono h
    · right
      rw [hJ]
      exact MvPolynomial.zeroLocus_anti_mono h

/-- The vanishing ideal of an irreducible closed set is prime. -/
lemma vanishingIdeal_isPrime {Z : Set (Fin n → k)} (hZc : IsClosed Z) (hZi : IsIrreducible Z) :
    (MvPolynomial.vanishingIdeal k Z).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ MvPolynomial.vanishingIdeal k Z := h ▸ Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have hz1 : ((1 : MvPolynomial (Fin n) k) : MvPolynomial (Fin n) k) ∈
          MvPolynomial.vanishingIdeal k Z := h1
      have := (MvPolynomial.mem_vanishingIdeal_iff).mp hz1 z hz
      simp at this
    rw [hempty] at hZi
    exact hZi.1.ne_empty rfl
  · intro x y hxy
    by_contra h
    simp only [not_or] at h
    obtain ⟨hx, hy⟩ := h
    have hcover : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {x}) ∪
        MvPolynomial.zeroLocus k (Ideal.span {y}) := by
      intro z hz
      have hxyz : (MvPolynomial.aeval z) (x * y) = 0 := hxy z hz
      rw [map_mul] at hxyz
      rcases mul_eq_zero.mp hxyz with h' | h'
      · left
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
      · right
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hZi.2) _ _
      (isClosed_zeroLocus k n (Ideal.span {x})) (isClosed_zeroLocus k n (Ideal.span {y})) hcover
      with h' | h'
    · exact hx fun z hz => h' hz x (Ideal.mem_span_singleton_self x)
    · exact hy fun z hz => h' hz y (Ideal.mem_span_singleton_self y)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_radical (I : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
  refine le_antisymm (MvPolynomial.zeroLocus_anti_mono Ideal.le_radical) ?_
  calc MvPolynomial.zeroLocus k I ⊆
        MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) :=
        MvPolynomial.zeroLocus_vanishingIdeal_le _
    _ ⊆ MvPolynomial.zeroLocus k I.radical :=
        MvPolynomial.zeroLocus_anti_mono (MvPolynomial.radical_le_vanishingIdeal_zeroLocus I)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_vanishingIdeal_of_isClosed {Z : Set (Fin n → k)} (hZ : IsClosed Z) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z) = Z := by
  rw [isClosed_iff_zarClosed] at hZ
  obtain ⟨I, rfl⟩ := hZ
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, zeroLocus_radical]

end Dictionary

section Dimension

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- The dimension of an affine algebraic set, as the supremum of the lengths of chains of
irreducible closed subsets (Hartshorne I.1). -/
noncomputable def varietyDim (Y : Set (Fin n → k)) : WithBot ℕ∞ :=
  Order.krullDim {Z : Set (Fin n → k) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z}

/-- The dimension of the affine algebraic set defined by an ideal equals the Krull dimension of the
coordinate ring. -/
theorem varietyDim_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    varietyDim k n (MvPolynomial.zeroLocus k I) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
  have key : ∀ (Z : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z}), I ≤ MvPolynomial.vanishingIdeal k Z.1 := by
    rintro ⟨Z, hZ, -, -⟩
    rw [← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
    exact hZ
  set F : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧
      IsClosed Z} → (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    fun Z => OrderDual.toDual
      ⟨⟨MvPolynomial.vanishingIdeal k Z.1, vanishingIdeal_isPrime k n Z.2.2.2 Z.2.2.1⟩, key Z⟩ with hF
  set G : (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ →
      {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧ IsClosed Z} :=
    fun p => ⟨MvPolynomial.zeroLocus k (OrderDual.ofDual p).1.asIdeal,
      ⟨fun x hx => by
        rw [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
        exact fun q hq => hx q ((OrderDual.ofDual p).2 hq),
       zeroLocus_irreducible k n (OrderDual.ofDual p).1.isPrime,
       isClosed_zeroLocus k n _⟩⟩ with hG
  have hFinj : Function.Injective F := by
    intro Z1 Z2 heq
    have h1 : MvPolynomial.vanishingIdeal k Z1.1 = MvPolynomial.vanishingIdeal k Z2.1 := by
      have := congrArg (fun x => (OrderDual.ofDual x : ↥(PrimeSpectrum.zeroLocus
        (I : Set (MvPolynomial (Fin n) k)))).1.asIdeal) heq
      simpa [hF] using this
    have hZ1 := zeroLocus_vanishingIdeal_of_isClosed k n Z1.2.2.2
    have hZ2 := zeroLocus_vanishingIdeal_of_isClosed k n Z2.2.2.2
    exact Subtype.ext (by rw [← hZ1, ← hZ2, h1])
  have hFmono : Monotone F := by
    intro Z1 Z2 hle
    simp only [hF, OrderDual.toDual_le_toDual]
    exact Subtype.mk_le_mk.mpr
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (MvPolynomial.vanishingIdeal_anti_mono hle))
  have hGinj : Function.Injective G := by
    intro p1 p2 heq
    have h1 : MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal =
        MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal := by
      have := congrArg Subtype.val heq
      simpa [hG] using this
    have h2 : (OrderDual.ofDual p1).1.asIdeal = (OrderDual.ofDual p2).1.asIdeal := by
      have e1 : (OrderDual.ofDual p1).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      have e2 : (OrderDual.ofDual p2).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      rw [e1, e2, h1]
    have : (OrderDual.ofDual p1).1 = (OrderDual.ofDual p2).1 := PrimeSpectrum.ext h2
    have : OrderDual.ofDual p1 = OrderDual.ofDual p2 := Subtype.ext this
    exact OrderDual.ofDual.injective this
  have hGmono : Monotone G := by
    intro p1 p2 hle
    have hlt : OrderDual.ofDual p2 ≤ OrderDual.ofDual p1 := hle
    have h2 : (OrderDual.ofDual p2).1.asIdeal ≤ (OrderDual.ofDual p1).1.asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt
    exact MvPolynomial.zeroLocus_anti_mono h2
  have hmain : Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} ≤
      Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    Order.krullDim_le_of_strictMono F (hFmono.strictMono_of_injective hFinj)
  have hmain2 : Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ ≤
      Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
        IsIrreducible Z ∧ IsClosed Z} :=
    Order.krullDim_le_of_strictMono G (hGmono.strictMono_of_injective hGinj)
  have hiso : Order.krullDim ↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  show Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} = ringKrullDim (MvPolynomial (Fin n) k ⧸ I)
  rw [le_antisymm hmain hmain2, Order.krullDim_orderDual]
  exact hiso

end Dimension

section Main

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- **Hartshorne, Algebraic Geometry, Exercise I.1.8.**  Let `Y` be an irreducible affine variety
of dimension `r` in `A^n` and let `H = V(f)` be a hypersurface, with `Y ⊄ H`.  Then every
irreducible component `Z` of `Y ∩ H` has dimension `r - 1`; equivalently `dim Z + 1 = dim Y`. -/
theorem hartshorne_exercise_I_1_8
    (Y : Set (Fin n → k)) (f : MvPolynomial (Fin n) k)
    (hYc : IsClosed Y) (hYi : IsIrreducible Y) (hf : f ≠ 0)
    (hne : ∃ y ∈ Y, (MvPolynomial.aeval y) f ≠ 0)
    (Z : Set (Fin n → k)) (hZY : Z ⊆ Y)
    (hZf : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}))
    (hZi : IsIrreducible Z) (hZc : IsClosed Z)
    (hZmax : ∀ W : Set (Fin n → k), W ⊆ Y → W ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) →
      IsIrreducible W → IsClosed W → Z ⊆ W → W ⊆ Z) :
    varietyDim k n Z + 1 = varietyDim k n Y := by
  set IY := MvPolynomial.vanishingIdeal k Y with hIY
  set q := MvPolynomial.vanishingIdeal k Z with hq
  haveI hYprime : IY.IsPrime := vanishingIdeal_isPrime k n hYc hYi
  haveI hqprime : q.IsPrime := vanishingIdeal_isPrime k n hZc hZi
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ IY) := Ideal.Quotient.isDomain _
  have hIYq : IY ≤ q := MvPolynomial.vanishingIdeal_anti_mono hZY
  have hfq : f ∈ q := fun z hz => hZf hz f (Ideal.mem_span_singleton_self f)
  have hYeq : MvPolynomial.zeroLocus k IY = Y := zeroLocus_vanishingIdeal_of_isClosed k n hYc
  -- ## `q` is minimal over `IY ⊔ (f)`
  have hmin : q ∈ (IY ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqprime, sup_le hIYq ((Ideal.span_singleton_le_iff_mem _).mpr hfq)⟩, ?_⟩
    rintro q' ⟨hq'prime, hq'le⟩ hq'q
    haveI := hq'prime
    have h1 : IY ≤ q' := le_trans le_sup_left hq'le
    have hspanle : (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)) ≤ IY ⊔ Ideal.span {f} :=
      le_sup_of_le_right (le_refl (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)))
    have hWY : MvPolynomial.zeroLocus k q' ⊆ Y := by
      rw [← hYeq]
      exact MvPolynomial.zeroLocus_anti_mono h1
    have hWf : MvPolynomial.zeroLocus k q' ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) :=
      MvPolynomial.zeroLocus_anti_mono (le_trans hspanle hq'le)
    have hWirr : IsIrreducible (MvPolynomial.zeroLocus k q') := zeroLocus_irreducible k n hq'prime
    have hWc : IsClosed (MvPolynomial.zeroLocus k q') := isClosed_zeroLocus k n _
    have hZW : Z ⊆ MvPolynomial.zeroLocus k q' := by
      rw [← zeroLocus_vanishingIdeal_of_isClosed k n hZc]
      exact MvPolynomial.zeroLocus_anti_mono hq'q
    have hWZ : MvPolynomial.zeroLocus k q' ⊆ Z := hZmax _ hWY hWf hWirr hWc hZW
    have h4 : q ≤ q' := by
      have h5 : MvPolynomial.vanishingIdeal k Z ≤ MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k q') :=
        MvPolynomial.vanishingIdeal_anti_mono (k := k) (K := k) hWZ
      have h6 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k q') = q' :=
        MvPolynomial.IsPrime.vanishingIdeal_zeroLocus q'
      rw [h6, ← hq] at h5
      exact h5
    exact h4
  -- ## pass to the coordinate ring of `Y`
  set t : MvPolynomial (Fin n) k ⧸ IY := Ideal.Quotient.mk IY f with ht
  set P : Ideal (MvPolynomial (Fin n) k ⧸ IY) := q.map (Ideal.Quotient.mk IY) with hP
  haveI hPprime : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIYq
  have hcomap : Ideal.comap (Ideal.Quotient.mk IY) P = q := by
    rw [hP, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hb : Ideal.comap (Ideal.Quotient.mk IY) (⊥ : Ideal (MvPolynomial (Fin n) k ⧸ IY)) = IY := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hb, sup_of_le_left hIYq]
  have ht0 : t ≠ 0 := by
    intro h0
    have hmem : f ∈ IY := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← ht]
      exact h0
    obtain ⟨y, hy, hfy⟩ := hne
    exact hfy (mem_vanishingIdeal_iff.mp hmem y hy)
  have htP : t ∈ P := by
    rw [ht, hP]
    exact Ideal.mem_map_of_mem _ hfq
  have htunit : ¬ IsUnit t := by
    intro hunit
    have hspan : Ideal.span {t} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr htP
    have hPtop : P = ⊤ := top_le_iff.mp (hspan ▸ hle)
    have hqtop : q = ⊤ := by
      have h1 : Ideal.comap (Ideal.Quotient.mk IY) P = ⊤ := by rw [hPtop]; simp
      rw [hcomap] at h1
      exact h1
    have h1q : (1 : MvPolynomial (Fin n) k) ∈ q := by rw [hqtop]; exact Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have h2 := (MvPolynomial.mem_vanishingIdeal_iff.mp h1q) z hz
      simp at h2
    exact hZi.1.ne_empty hempty
  have hPmin : P ∈ (Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨hPprime, (Ideal.span_singleton_le_iff_mem _).mpr htP⟩, ?_⟩
    rintro P' ⟨hP'prime, hP'le⟩ hP'P
    haveI := hP'prime
    have hq'le : (IY ⊔ Ideal.span {f}) ≤ Ideal.comap (Ideal.Quotient.mk IY) P' := by
      refine sup_le ?_ ?_
      · exact Ideal.le_comap_of_map_le (by
          rw [Ideal.map_quotient_self]
          exact bot_le)
      · refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
        have h8 : t ∈ P' := hP'le (Ideal.mem_span_singleton_self t)
        rwa [ht] at h8
    have hq'q : Ideal.comap (Ideal.Quotient.mk IY) P' ≤ q := by
      rw [← hcomap]
      exact Ideal.comap_mono hP'P
    have hqle : q ≤ Ideal.comap (Ideal.Quotient.mk IY) P' :=
      hmin.2 ⟨Ideal.IsPrime.comap (Ideal.Quotient.mk IY), hq'le⟩ hq'q
    have hfin : P ≤ P' := by
      have h7 : P ≤ (Ideal.comap (Ideal.Quotient.mk IY) P').map (Ideal.Quotient.mk IY) := by
        rw [hP]
        exact Ideal.map_mono hqle
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h7
    exact hfin
  -- ## the algebraic input
  have hmain := ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes k ht0 htunit hPmin
  -- ## the two dimensions
  have hZq : MvPolynomial.zeroLocus k q = Z := zeroLocus_vanishingIdeal_of_isClosed k n hZc
  have h1 : varietyDim k n Z = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) := by
    rw [← hZq]
    exact varietyDim_zeroLocus k n q
  have h2 : varietyDim k n Y = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := by
    rw [← hYeq]
    exact varietyDim_zeroLocus k n IY
  have hiso : ringKrullDim (MvPolynomial (Fin n) k ⧸ q) =
      ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) := by
    have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) = q := by
      ext x
      show (Ideal.Quotient.mk P) ((Ideal.Quotient.mk IY) x) = 0 ↔ x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hcomap, Ideal.mem_comap]
    have hiso' : (MvPolynomial (Fin n) k ⧸ q) ≃+* ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
    exact ringKrullDim_eq_of_ringEquiv hiso'
  calc varietyDim k n Z + 1 = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) + 1 := by rw [h1]
    _ = ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) + 1 := by rw [hiso]
    _ = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := hmain
    _ = varietyDim k n Y := h2.symm

end Main

/-! ## Part 2: homogeneous components and the strong vanishing ideal -/

section HomogScaling

variable {σ : Type*} {k : Type*} [Field k]

/-- Evaluating a polynomial at the point `c • a` obtained by scaling `a`. -/
theorem eval_smul_eq_sum_homogeneousComponent (f : MvPolynomial σ k) (c : k) (a : σ → k) :
    MvPolynomial.eval (fun i => c * a i) f =
      ∑ d ∈ Finset.range (f.totalDegree + 1),
        c ^ d * MvPolynomial.eval a (MvPolynomial.homogeneousComponent d f) := by
  have hL : MvPolynomial.eval (fun i => c * a i) f =
      ∑ m ∈ f.support, c ^ m.degree * (MvPolynomial.coeff m f * m.prod fun i e => a i ^ e) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    ring
  rw [hL, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (f.totalDegree + 1))
    (g := fun m : σ →₀ ℕ => m.degree)
    (f := fun m => c ^ m.degree * (MvPolynomial.coeff m f * m.prod fun i e => a i ^ e))
    (fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (MvPolynomial.le_totalDegree hm)))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [MvPolynomial.eval_monomial, hm.2]

/-- If a polynomial vanishes at every nonzero scalar multiple of a vector `a`, then each of its
homogeneous components vanishes at `a`. -/
theorem homogeneousComponent_eval_eq_zero [Infinite k] {f : MvPolynomial σ k} {a : σ → k}
    (h : ∀ c : k, c ≠ 0 → MvPolynomial.eval (fun i => c * a i) f = 0) (d : ℕ) :
    MvPolynomial.eval a (MvPolynomial.homogeneousComponent d f) = 0 := by
  classical
  have hcoeff : ∀ (s : Finset ℕ) (y : ℕ → k) (d : ℕ),
      Polynomial.coeff (∑ e ∈ s, Polynomial.C (y e) * Polynomial.X ^ e) d =
        if d ∈ s then y d else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro y d
        simp
    | insert a s ha ih =>
        intro y d
        rw [Finset.sum_insert ha, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul_X_pow]
        by_cases hda : d = a
        · subst hda
          simp [ha]
        · simp [hda, Finset.mem_insert]
  have hzero : ∀ c : k, c ≠ 0 →
      Polynomial.eval c (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = 0 := by
    intro c hc
    rw [Polynomial.eval_finsetSum]
    have hterm : ∀ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.eval c (Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) =
          c ^ e * MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f) := by
      intro e _
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_comm _ _
    rw [Finset.sum_congr rfl hterm, ← eval_smul_eq_sum_homogeneousComponent f c a]
    exact h c hc
  have hinf : ({x : k | Polynomial.eval x (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = Polynomial.eval x (0 : Polynomial k)}).Infinite := by
    refine Set.Infinite.mono ?_ (Set.Finite.infinite_compl (Set.finite_singleton (0 : k)))
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    simpa using hzero c hc
  have hP0 : (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = 0 :=
    Polynomial.eq_of_infinite_eval_eq _ 0 hinf
  have hd := hcoeff (Finset.range (f.totalDegree + 1))
    (fun e => MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) d
  rw [hP0, Polynomial.coeff_zero] at hd
  by_cases hle : d ≤ f.totalDegree
  · rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))] at hd
    exact hd.symm
  · push Not at hle
    rw [if_neg (by rw [Finset.mem_range]; omega)] at hd
    have hzero' : MvPolynomial.homogeneousComponent d f = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero (φ := f) (n := d) (by omega)
    simp [hzero']

end HomogScaling

/-! ### The strong vanishing ideal of a projective set -/

section VanishOn

variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

/-- The ideal of polynomials vanishing at every nonzero vector whose line lies in `Y`. -/
noncomputable def vanishOnIdeal (Y : Set (Proj k n)) : Ideal (MvPolynomial (Fin (n + 1)) k) where
  carrier := {f | ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk v hv ∈ Y → MvPolynomial.eval v f = 0}
  add_mem' := by
    intro a b ha hb v hv hmem
    simp only [map_add, ha v hv hmem, hb v hv hmem, add_zero]
  zero_mem' := by
    intro v hv hmem
    simp
  smul_mem' := by
    intro c a ha v hv hmem
    simp only [smul_eq_mul, MvPolynomial.eval_mul, ha v hv hmem, mul_zero]

theorem mem_vanishOnIdeal_iff {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} :
    f ∈ (vanishOnIdeal Y : Set (MvPolynomial (Fin (n + 1)) k)) ↔
      ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk v hv ∈ Y → MvPolynomial.eval v f = 0 :=
  Iff.rfl

/-- `mk` is invariant under nonzero scaling. -/
theorem mk_smul {c : k} (hc : c ≠ 0) {v : Fin (n + 1) → k} (hv : v ≠ 0) (hcv : c • v ≠ 0) :
    mk (c • v) hcv = mk v hv := by
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc, rfl⟩

/-- The generators of the vanishing ideal belong to the strong vanishing ideal. -/
theorem vanishingIdeal_le_vanishOnIdeal (Y : Set (Proj k n)) :
    vanishingIdeal Y ≤ vanishOnIdeal Y := by
  rw [vanishingIdeal, Ideal.span_le]
  rintro f ⟨d, hf, hvan⟩
  rw [mem_vanishOnIdeal_iff]
  intro v hv hmem
  exact (isZeroAt_mk_iff hf hv).1 (hvan _ hmem)

/-- Homogeneous components of a polynomial vanishing on `Y` vanish on `Y`. -/
theorem homogeneousComponent_mem_vanishOnIdeal [Infinite k] {Y : Set (Proj k n)}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f ∈ vanishOnIdeal Y) (d : ℕ) :
    MvPolynomial.homogeneousComponent d f ∈ vanishOnIdeal Y := by
  refine mem_vanishOnIdeal_iff.mpr ?_
  intro v hv hmem
  refine homogeneousComponent_eval_eq_zero (fun c hc => ?_) d
  have hscale : (fun i => c * v i) = c • v := rfl
  rw [hscale]
  have hmem' : mk (c • v) (smul_ne_zero hc hv) ∈ Y := by
    rw [mk_smul hc hv]
    exact hmem
  exact (mem_vanishOnIdeal_iff.mp hf) _ (smul_ne_zero hc hv) hmem'

/-- The strong vanishing ideal is generated by homogeneous polynomials. -/
theorem vanishOnIdeal_le_vanishingIdeal [Infinite k] (Y : Set (Proj k n)) :
    vanishOnIdeal Y ≤ vanishingIdeal Y := by
  intro f hf
  have hgen : ∀ e : ℕ, MvPolynomial.homogeneousComponent e f ∈ vanishingIdeal Y := by
    intro e
    have hh : (MvPolynomial.homogeneousComponent e f).IsHomogeneous e :=
      MvPolynomial.homogeneousComponent_isHomogeneous e f
    have hv : ∀ x ∈ Y, IsZeroAt (MvPolynomial.homogeneousComponent e f) x := by
      intro x hx
      rw [IsZeroAt]
      exact homogeneousComponent_mem_vanishOnIdeal hf e _ x.rep_nonzero (by simpa using hx)
    exact subset_vanishingIdeal (d := e) hh hv
  have hsum : (∑ e ∈ Finset.range (f.totalDegree + 1),
      MvPolynomial.homogeneousComponent e f) = f := MvPolynomial.sum_homogeneousComponent f
  rw [← hsum]
  exact Ideal.sum_mem _ fun e _ => hgen e

theorem vanishOnIdeal_eq_vanishingIdeal [Infinite k] (Y : Set (Proj k n)) :
    vanishOnIdeal Y = vanishingIdeal Y :=
  le_antisymm (vanishOnIdeal_le_vanishingIdeal Y) (vanishingIdeal_le_vanishOnIdeal Y)

end Proj

end VanishOn

/-! ### Primeness of the vanishing ideal of an irreducible closed set -/

section ConeDictionary

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

theorem vanishOnIdeal_ne_top [Infinite k] {Y : Set (Proj k n)} (hY : Y.Nonempty) :
    vanishOnIdeal Y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hY
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  intro htop
  have hmem : MvPolynomial.X j ∈ vanishOnIdeal Y := by rw [htop]; exact Submodule.mem_top
  have := (mem_vanishOnIdeal_iff.mp hmem) x.rep x.rep_nonzero (by simpa using hx)
  rw [MvPolynomial.eval_X] at this
  exact hj this

/-- The vanishing ideal of an irreducible closed set is prime. -/
theorem vanishOnIdeal_isPrime [Infinite k] {Y : Set (Proj k n)} (hYi : IsIrreducible Y) :
    (vanishOnIdeal Y).IsPrime := by
  have hhom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (vanishOnIdeal Y) := by
    rw [vanishOnIdeal_eq_vanishingIdeal Y]
    exact vanishingIdeal_isHomogeneous Y
  rw [Ideal.IsHomogeneous.isPrime_iff hhom]
  refine ⟨vanishOnIdeal_ne_top hYi.1, ?_⟩
  intro f g hf hg hfg
  obtain ⟨df, hdf⟩ := hf
  obtain ⟨dg, hdg⟩ := hg
  have hclosed_f : IsClosed {x : Proj k n | IsZeroAt f x} := by
    rw [isClosed_iff]
    exact ⟨{⟨f, df, hdf⟩}, by
      ext x
      exact ⟨fun h => h _ rfl, fun h y hy => by rw [Set.mem_singleton_iff.mp hy]; exact h⟩⟩
  have hclosed_g : IsClosed {x : Proj k n | IsZeroAt g x} := by
    rw [isClosed_iff]
    exact ⟨{⟨g, dg, hdg⟩}, by
      ext x
      exact ⟨fun h => h _ rfl, fun h y hy => by rw [Set.mem_singleton_iff.mp hy]; exact h⟩⟩
  have hcover : Y ⊆ {x : Proj k n | IsZeroAt f x} ∪ {x : Proj k n | IsZeroAt g x} := by
    intro x hx
    have h0 : MvPolynomial.eval x.rep (f * g) = 0 :=
      mem_vanishOnIdeal_iff.mp hfg _ x.rep_nonzero (by simpa using hx)
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp hYi.2)
    _ _ hclosed_f hclosed_g hcover
  rcases hsplit with hYf | hYg
  · refine Or.inl (mem_vanishOnIdeal_iff.mpr ?_)
    intro v hv hmem
    exact (isZeroAt_mk_iff hdf hv).1 (hYf hmem)
  · refine Or.inr (mem_vanishOnIdeal_iff.mpr ?_)
    intro v hv hmem
    exact (isZeroAt_mk_iff hdg hv).1 (hYg hmem)

/-- The vanishing ideal of an irreducible closed set is prime. -/
theorem vanishingIdeal_isPrime_of_isIrreducible [Infinite k] {Y : Set (Proj k n)}
    (hYi : IsIrreducible Y) : (vanishingIdeal Y).IsPrime := by
  rw [← vanishOnIdeal_eq_vanishingIdeal Y]
  exact vanishOnIdeal_isPrime hYi

end Proj

end ConeDictionary

/-! ### Basic geometry of the cone -/

section ConeGeom

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem cone_empty : cone (∅ : Set (Proj k n)) = {0} := by
  ext v
  simp [cone]

theorem cone_union (A B : Set (Proj k n)) : cone (A ∪ B) = cone A ∪ cone B := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem | hmem⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨hv, hmem⟩)
    · exact Or.inr (Or.inr ⟨hv, hmem⟩)
  · rintro (h | h)
    · rcases h with rfl | ⟨hv, hm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hv, Or.inl hm⟩
    · rcases h with rfl | ⟨hv, hm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hv, Or.inr hm⟩

theorem cone_mono {A B : Set (Proj k n)} (h : A ⊆ B) : cone A ⊆ cone B := by
  rintro v (rfl | ⟨hv, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨hv, h hm⟩

theorem cone_univ : cone (Set.univ : Set (Proj k n)) = Set.univ := by
  ext v
  simp only [cone, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  by_cases hv : v = 0
  · exact Or.inl hv
  · exact Or.inr ⟨hv, trivial⟩

/-- The cone over a closed set is closed. -/
theorem isClosed_cone [Infinite k] {A : Set (Proj k n)} (hA : IsClosed A) :
    IsClosed (cone A) := by
  rcases Set.eq_empty_or_nonempty A with rfl | hne
  · rw [cone_empty]
    have hz : ({0} : Set (Fin (n + 1) → k)) =
        MvPolynomial.zeroLocus k (Ideal.span (Set.range (fun i : Fin (n + 1) =>
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)))) := by
      ext v
      rw [Set.mem_singleton_iff, MvPolynomial.mem_zeroLocus_iff]
      constructor
      · rintro rfl
        have hle : Ideal.span (Set.range (fun i : Fin (n + 1) =>
            (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)))
            ≤ RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          rintro q ⟨i, rfl⟩
          simp
        intro p hp
        exact hle hp
      · intro h
        funext i
        have hx := h (MvPolynomial.X i) (Ideal.subset_span ⟨i, rfl⟩)
        rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X] at hx
        exact hx
    rw [hz]
    exact isClosed_zeroLocus k (n + 1) _
  · rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed A).mpr hA) hne]
    exact isClosed_zeroLocus k (n + 1) (vanishingIdeal A)

/-- Cone over an irreducible nonempty closed set is irreducible. -/
theorem isIrreducible_cone [Infinite k] {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) : IsIrreducible (cone Y) := by
  have hp : (vanishingIdeal Y).IsPrime := vanishingIdeal_isPrime_of_isIrreducible hYi
  rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed Y).mpr hYc) hYi.1]
  exact zeroLocus_irreducible k (n + 1) hp

/-- The cone is irreducible iff the projective set is irreducible (for nonempty closed sets). -/
theorem isIrreducible_cone_iff [Infinite k] {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hne : Y.Nonempty) : IsIrreducible (cone Y) ↔ IsIrreducible Y := by
  refine ⟨?_, isIrreducible_cone hYc⟩
  intro hcone
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have hcover : cone Y ⊆ cone A ∪ cone B := by
    rw [← cone_union]
    exact cone_mono hsub
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp hcone.2)
    (cone A) (cone B) (isClosed_cone hA) (isClosed_cone hB) hcover
  rcases hsplit with h | h
  · refine Or.inl ?_
    intro x hx
    have hx' : x.rep ∈ cone A := h (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm
  · refine Or.inr ?_
    intro x hx
    have hx' : x.rep ∈ cone B := h (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm

end Proj

end ConeGeom

/-! ## Part 3: finite irreducible decompositions in noetherian topological spaces
(from the accepted Hartshorne I.2.5 infrastructure, model independent) -/

/-! ## 5. Finite irreducible decompositions in noetherian topological spaces

Hartshorne proves (I.1, Prop. 1.5; Ex. I.2.5(b)) that in a noetherian topological space every
closed subset is a finite union of irreducible closed subsets, no one containing another, and
that this decomposition is unique.  We prove this in an arbitrary topological space satisfying
the descending chain condition for closed subsets, then apply it to `P^n`. -/

section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- **Irreducible closed subset**, in Hartshorne's sense: nonempty and not the union of two
proper closed subsets. -/
def IsIrredClosed (Z : Set X) : Prop :=
  Z.Nonempty ∧ IsClosed Z ∧
    ∀ A B : Set X, IsClosed A → IsClosed B → Z ⊆ A ∪ B → Z ⊆ A ∨ Z ⊆ B

/-- Hartshorne's definition ("cannot be written as the union of two proper closed subsets")
rephrased: `Z` is irreducible iff there are no two closed subsets, neither containing `Z`,
whose union contains `Z`. -/
theorem isIrredClosed_iff_not_union {Z : Set X} :
    IsIrredClosed Z ↔ Z.Nonempty ∧ IsClosed Z ∧
      ¬ ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Z ⊆ A ∪ B ∧ ¬ Z ⊆ A ∧ ¬ Z ⊆ B := by
  constructor
  · rintro ⟨hne, hc, hirr⟩
    refine ⟨hne, hc, ?_⟩
    rintro ⟨A, B, hA, hB, hcov, hAn, hBn⟩
    rcases hirr A B hA hB hcov with h | h
    · exact hAn h
    · exact hBn h
  · rintro ⟨hne, hc, hno⟩
    refine ⟨hne, hc, ?_⟩
    intro A B hA hB hcov
    by_contra hc'
    push Not at hc'
    exact hno ⟨A, B, hA, hB, hcov, hc'.1, hc'.2⟩

/-- The descending chain condition for closed subsets: Hartshorne's definition of a noetherian
topological space. -/
def HasDCCClosed (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ F : ℕ → Set X, (∀ i, IsClosed (F i)) → (∀ i, F (i + 1) ⊆ F i) → ∃ N, ∀ i, N ≤ i → F i = F N

/-- In a space with the descending chain condition, every nonempty family of closed subsets has
a minimal element. -/
theorem exists_minimal_closed (dcc : HasDCCClosed X) {F : Set (Set X)} (hne : F.Nonempty)
    (hF : ∀ Z ∈ F, IsClosed Z) :
    ∃ Z ∈ F, ∀ W ∈ F, W ⊆ Z → Z ⊆ W := by
  classical
  by_contra h
  push Not at h
  have hstep : ∀ x : {Z // Z ∈ F}, ∃ y : {Z // Z ∈ F}, y.1 ⊆ x.1 ∧ ¬ x.1 ⊆ y.1 := by
    rintro ⟨Z, hZ⟩
    obtain ⟨W, hW, hWZ, hZW⟩ := h Z hZ
    exact ⟨⟨W, hW⟩, hWZ, hZW⟩
  let nxt : {Z // Z ∈ F} → {Z // Z ∈ F} := fun x => (hstep x).choose
  have nxt_sub : ∀ x, (nxt x).1 ⊆ x.1 := fun x => (hstep x).choose_spec.1
  have nxt_not_sub : ∀ x, ¬ x.1 ⊆ (nxt x).1 := fun x => (hstep x).choose_spec.2
  obtain ⟨x₀, hx₀⟩ := hne
  let seq : ℕ → {Z // Z ∈ F} := fun i => Nat.rec ⟨x₀, hx₀⟩ (fun _ x => nxt x) i
  have hseq_succ : ∀ i, seq (i + 1) = nxt (seq i) := fun i => rfl
  have hanti : ∀ i, (seq (i + 1)).1 ⊆ (seq i).1 := fun i => by
    rw [hseq_succ]
    exact nxt_sub (seq i)
  have hclosed : ∀ i, IsClosed (seq i).1 := fun i => hF _ (seq i).2
  obtain ⟨N, hN⟩ := dcc (fun i => (seq i).1) hclosed hanti
  have h1 : (seq (N + 1)).1 = (seq N).1 := hN (N + 1) (Nat.le_succ N)
  refine nxt_not_sub (seq N) ?_
  rw [← hseq_succ, h1]

omit [TopologicalSpace X] in
/-- Every finite nonempty family of sets has a member which is maximal for inclusion. -/
theorem exists_maximal_subset_of_finite {E : Set (Set X)} (hE : E.Finite) (hne : E.Nonempty) :
    ∃ W ∈ E, ∀ W' ∈ E, W ⊆ W' → W' ⊆ W := by
  classical
  revert hne
  refine Set.Finite.induction_on
    (motive := fun s _ => s.Nonempty → ∃ W ∈ s, ∀ W' ∈ s, W ⊆ W' → W' ⊆ W) E hE ?_ ?_
  · intro hne
    exact absurd hne (by simp)
  · intro a s ha hs ih hne
    by_cases hsne : s.Nonempty
    · obtain ⟨W, hWs, hmax⟩ := ih hsne
      by_cases hWa : W ⊆ a
      · refine ⟨a, Set.mem_insert a s, ?_⟩
        intro W' hW' haW'
        rcases hW' with rfl | hW's
        · exact subset_rfl
        · have hWW' : W ⊆ W' := hWa.trans haW'
          have hW'W : W' ⊆ W := hmax W' hW's hWW'
          exact hW'W.trans hWa
      · refine ⟨W, Set.mem_insert_of_mem _ hWs, ?_⟩
        intro W' hW' hWW'
        rcases hW' with rfl | hW's
        · exact absurd hWW' hWa
        · exact hmax W' hW's hWW'
    · refine ⟨a, Set.mem_insert a s, ?_⟩
      intro W' hW' haW'
      rw [Set.mem_insert_iff] at hW'
      rcases hW' with rfl | hWs
      · exact subset_rfl
      · exact absurd ⟨W', hWs⟩ hsne

end NoetherianTop


section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- **Existence of a finite irreducible decomposition**: in a space with the descending chain
condition, every closed subset is a finite union of irreducible closed subsets.  The proof is
the minimal-counterexample argument: if some closed set had no such decomposition, a minimal
one would be reducible, `Z = (Z ∩ A) ∪ (Z ∩ B)` with both parts proper closed subsets, and the
decompositions of the two proper parts would combine to one of `Z`. -/
theorem exists_finite_irred_cover (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D := by
  classical
  by_contra hcon
  -- the family of closed sets without a finite irreducible decomposition
  set F : Set (Set X) :=
    {Y | IsClosed Y ∧ ¬ ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Y = ⋃₀ D}
    with hFdef
  have hFne : F.Nonempty := ⟨Z, hZ, hcon⟩
  have hFclosed : ∀ W ∈ F, IsClosed W := fun W hW => hW.1
  obtain ⟨Z₀, hZ₀F, hmin⟩ := exists_minimal_closed dcc hFne hFclosed
  obtain ⟨hZ₀c, hZ₀bad⟩ := hZ₀F
  have hZ₀ne : Z₀.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hZ₀bad ⟨∅, Set.finite_empty, by simp, by rw [Set.sUnion_empty]; exact h⟩
  -- `Z₀` is not irreducible, so it is the union of two proper closed pieces
  have hred : ¬ ∀ A B : Set X, IsClosed A → IsClosed B → Z₀ ⊆ A ∪ B → Z₀ ⊆ A ∨ Z₀ ⊆ B := by
    intro hAB
    exact hZ₀bad ⟨{Z₀}, Set.finite_singleton Z₀, by
      rintro W hW
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hZ₀ne, hZ₀c, hAB⟩, by simp⟩
  push Not at hred
  obtain ⟨A, B, hA, hB, hcov, hAn, hBn⟩ := hred
  have hZ₁c : IsClosed (Z₀ ∩ A) := IsClosed.inter hZ₀c hA
  have hZ₂c : IsClosed (Z₀ ∩ B) := IsClosed.inter hZ₀c hB
  have hZ₁proper : Z₀ ∩ A ⊆ Z₀ ∧ ¬ Z₀ ⊆ Z₀ ∩ A := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hsub
    exact hAn (fun x hx => (hsub hx).2)
  have hZ₂proper : Z₀ ∩ B ⊆ Z₀ ∧ ¬ Z₀ ⊆ Z₀ ∩ B := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hsub
    exact hBn (fun x hx => (hsub hx).2)
  have hdec : ∀ W : Set X, W ∈ F → W ⊆ Z₀ → W ≠ Z₀ → False := by
    intro W hW hsub hne
    exact hne (le_antisymm hsub (hmin W hW hsub))
  have hdec₁ : ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z₀ ∩ A = ⋃₀ D := by
    by_contra h
    exact hdec _ ⟨hZ₁c, h⟩ Set.inter_subset_left (fun heq => hZ₁proper.2 (heq.symm ▸ subset_rfl))
  have hdec₂ : ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z₀ ∩ B = ⋃₀ D := by
    by_contra h
    exact hdec _ ⟨hZ₂c, h⟩ Set.inter_subset_left (fun heq => hZ₂proper.2 (heq.symm ▸ subset_rfl))
  obtain ⟨D₁, hD₁fin, hD₁irr, hD₁cov⟩ := hdec₁
  obtain ⟨D₂, hD₂fin, hD₂irr, hD₂cov⟩ := hdec₂
  have hZ₀eq : Z₀ = (Z₀ ∩ A) ∪ (Z₀ ∩ B) := by
    refine le_antisymm ?_ (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  refine hZ₀bad ⟨D₁ ∪ D₂, hD₁fin.union hD₂fin, ?_, ?_⟩
  · intro W hW
    rcases hW with hW | hW
    · exact hD₁irr W hW
    · exact hD₂irr W hW
  · rw [hZ₀eq, Set.sUnion_union, hD₁cov, hD₂cov]

/-- **A canonical (antichain) finite irreducible decomposition**: keeping only the maximal
members of a finite irreducible cover gives a decomposition no member of which contains
another. -/
theorem exists_antichain_irred_cover (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D ∧
      (∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' → W = W') := by
  classical
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := exists_finite_irred_cover dcc hZ
  set D' : Set (Set X) := {W ∈ D | ∀ W' ∈ D, W ⊆ W' → W = W'} with hD'def
  have hD'sub : D' ⊆ D := fun W hW => hW.1
  refine ⟨D', hDfin.subset hD'sub, fun W hW => hDirr W hW.1, ?_, ?_⟩
  · refine le_antisymm ?_ (Set.sUnion_subset fun W hW => hDcov ▸ Set.subset_sUnion_of_mem hW.1)
    intro x hx
    have hxD : x ∈ ⋃₀ D := hDcov ▸ hx
    obtain ⟨W, hWD, hxW⟩ := Set.mem_sUnion.1 hxD
    have hEfin : ({V ∈ D | x ∈ V}).Finite := hDfin.subset (fun V hV => hV.1)
    have hEne : ({V ∈ D | x ∈ V}).Nonempty := ⟨W, hWD, hxW⟩
    obtain ⟨W', ⟨hW'D, hxW'⟩, hmax⟩ := exists_maximal_subset_of_finite hEfin hEne
    refine Set.mem_sUnion.2 ⟨W', ⟨hW'D, ?_⟩, hxW'⟩
    intro V hVD hWV
    exact le_antisymm hWV (hmax V ⟨hVD, hWV hxW'⟩ hWV)
  · intro W hW W' hW' hsub
    exact hW.2 W' hW'.1 hsub

/-- A finite irreducible decomposition of `Z`: a finite union `Z = ⋃₀ D` of irreducible closed
subsets, no one containing another. -/
def IsIrredDecomposition (D : Set (Set X)) (Z : Set X) : Prop :=
  D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D ∧
    (∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' → W = W')

/-- **Existence part of Hartshorne Ex. I.2.5(b)**. -/
theorem exists_irredDecomposition (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D, IsIrredDecomposition D Z :=
  exists_antichain_irred_cover dcc hZ

/-- An irreducible closed set contained in a finite union of closed sets is contained in one of
them. -/
theorem IsIrredClosed.exists_subset_of_finite_sUnion {W : Set X} (hW : IsIrredClosed W)
    {E : Set (Set X)} (hEfin : E.Finite) (hEclosed : ∀ V ∈ E, IsClosed V)
    (hsub : W ⊆ ⋃₀ E) : ∃ V ∈ E, W ⊆ V := by
  classical
  revert hsub hEclosed
  refine Set.Finite.induction_on (motive := fun s _ =>
    (∀ V ∈ s, IsClosed V) → W ⊆ ⋃₀ s → ∃ V ∈ s, W ⊆ V) E hEfin ?_ ?_
  · intro _ hsub
    obtain ⟨x, hx⟩ := hW.1
    exact absurd (hsub hx) (by simp)
  · intro a s ha hs ih hEcl hsub
    rw [Set.sUnion_insert] at hsub
    have hscl : IsClosed (⋃₀ s) := by
      rw [Set.sUnion_eq_biUnion]
      exact hs.isClosed_biUnion fun V hV => hEcl V (Set.mem_insert_of_mem a hV)
    rcases hW.2.2 a (⋃₀ s) (hEcl a (Set.mem_insert a s)) hscl hsub with hWa | hWs
    · exact ⟨a, Set.mem_insert a s, hWa⟩
    · obtain ⟨V, hV, hWV⟩ := ih (fun V hV => hEcl V (Set.mem_insert_of_mem a hV)) hWs
      exact ⟨V, Set.mem_insert_of_mem a hV, hWV⟩

/-- **Uniqueness part of Hartshorne Ex. I.2.5(b)**: two finite unions of irreducible closed
subsets, no one containing another, with the same union, coincide. -/
theorem irredDecomposition_unique {D D' : Set (Set X)} {Z : Set X}
    (hD : IsIrredDecomposition D Z) (hD' : IsIrredDecomposition D' Z) : D = D' := by
  classical
  obtain ⟨hDfin, hDirr, hDcov, hDanti⟩ := hD
  obtain ⟨hD'fin, hD'irr, hD'cov, hD'anti⟩ := hD'
  -- key: a member of one decomposition is contained in a member of the other
  have key : ∀ W : Set X, W ∈ D → ∃ W' ∈ D', W ⊆ W' := by
    intro W hW
    have hWZ : W ⊆ Z := by rw [hDcov]; exact Set.subset_sUnion_of_mem hW
    have hWZ' : W ⊆ ⋃₀ D' := by rw [← hD'cov]; exact hWZ
    exact (hDirr W hW).exists_subset_of_finite_sUnion hD'fin (fun V hV => (hD'irr V hV).2.1) hWZ'
  have key' : ∀ W : Set X, W ∈ D' → ∃ W' ∈ D, W ⊆ W' := by
    intro W hW
    have hWZ : W ⊆ Z := by rw [hD'cov]; exact Set.subset_sUnion_of_mem hW
    have hWZ' : W ⊆ ⋃₀ D := by rw [← hDcov]; exact hWZ
    exact (hD'irr W hW).exists_subset_of_finite_sUnion hDfin (fun V hV => (hDirr V hV).2.1) hWZ'
  refine Set.Subset.antisymm ?_ ?_
  · intro W hW
    obtain ⟨W', hW'D', hWW'⟩ := key W hW
    obtain ⟨W'', hW''D, hW'W''⟩ := key' W' hW'D'
    have hWW'' : W ⊆ W'' := hWW'.trans hW'W''
    have hEq : W = W'' := hDanti W hW W'' hW''D hWW''
    have hW'W : W' ⊆ W := hEq.symm ▸ hW'W''
    have hW'W_eq : W' = W := le_antisymm hW'W hWW'
    rw [← hW'W_eq]
    exact hW'D'
  · intro W hW
    obtain ⟨W', hW'D, hWW'⟩ := key' W hW
    obtain ⟨W'', hW''D', hW'W''⟩ := key W' hW'D
    have hWW'' : W ⊆ W'' := hWW'.trans hW'W''
    have hEq : W = W'' := hD'anti W hW W'' hW''D' hWW''
    have hW'W : W' ⊆ W := hEq.symm ▸ hW'W''
    have hW'W_eq : W' = W := le_antisymm hW'W hWW'
    rw [← hW'W_eq]
    exact hW'D

/-- **Hartshorne Ex. I.2.5(b)**, existence and uniqueness together. -/
theorem existsUnique_irredDecomposition (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D, IsIrredDecomposition D Z ∧ ∀ D', IsIrredDecomposition D' Z → D' = D := by
  obtain ⟨D, hD⟩ := exists_irredDecomposition dcc hZ
  exact ⟨D, hD, fun D' hD' => irredDecomposition_unique hD' hD⟩

end NoetherianTop


section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- Our notion of irreducible closed subset agrees with Mathlib's `IsIrreducible` (and hence
with Hartshorne's "not the union of two proper closed subsets"). -/
theorem isIrredClosed_iff_isIrreducible {Z : Set X} :
    IsIrredClosed Z ↔ IsClosed Z ∧ IsIrreducible Z := by
  refine ⟨fun h => ⟨h.2.1, h.1, ?_⟩, fun h => ⟨h.2.1, h.1, ?_⟩⟩
  · exact isPreirreducible_iff_isClosed_union_isClosed.2 h.2.2
  · exact isPreirreducible_iff_isClosed_union_isClosed.1 h.2.2

end NoetherianTop

/-! ## Part 4: chain dimension as a supremum of chain lengths -/

section IrrChainDim

variable {X : Type*} [TopologicalSpace X]

/-- The chain dimension of a set `Z` in a topological space: the supremum of the lengths of chains
of irreducible closed subsets of `Z`, as an element of `ℕ∞`. -/
noncomputable def irrChainDim (Z : Set X) : ℕ∞ :=
  ⨆ (l : LTSeries {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W}), (l.length : ℕ∞)

theorem irrChainDim_mono {Z Z' : Set X} (h : Z ⊆ Z') : irrChainDim Z ≤ irrChainDim Z' := by
  refine iSup_le fun l => ?_
  let hmap : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W} :=
    l.map (fun W => ⟨W.1, W.2.1.trans h, W.2.2.1, W.2.2.2⟩) (fun a b hab => hab)
  calc (l.length : ℕ∞) = (hmap.length : ℕ∞) := rfl
    _ ≤ ⨆ (l' : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W}), (l'.length : ℕ∞) :=
        le_iSup (fun l' : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W} =>
          (l'.length : ℕ∞)) hmap

theorem irrChainDim_le_iff {Z : Set X} {c : ℕ∞} :
    irrChainDim Z ≤ c ↔ ∀ l : LTSeries {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W},
      (l.length : ℕ∞) ≤ c :=
  iSup_le_iff

/-- **A finite closed cover computes the dimension.** -/
theorem irrChainDim_iUnion {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : ∀ i, IsClosed (A i)) :
    irrChainDim (⋃ i, A i) = ⨆ i, irrChainDim (A i) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [irrChainDim_le_iff]
    intro l
    -- the last element of the chain lies in one member of the cover
    have hlastirr : IsIrreducible (l (Fin.last l.length)).1 := (l (Fin.last l.length)).2.2.1
    have hlastsub : (l (Fin.last l.length)).1 ⊆ ⋃₀ (Set.range A) := by
      rw [Set.sUnion_range]
      exact (l (Fin.last l.length)).2.1
    obtain ⟨W, ⟨i0, rfl⟩, hWi⟩ := IsIrredClosed.exists_subset_of_finite_sUnion
      ((isIrredClosed_iff_isIrreducible).mpr ⟨(l (Fin.last l.length)).2.2.2, hlastirr⟩)
      (Set.finite_range A) (fun W hW => by obtain ⟨i, rfl⟩ := hW; exact hA i) hlastsub
    -- every element of the chain is contained in that member
    have hall : ∀ j : Fin (l.length + 1), (l j).1 ⊆ A i0 := by
      intro j
      have hle : (l j).1 ⊆ (l (Fin.last l.length)).1 := by
        rcases RelSeries.rel_or_eq_of_le l (Fin.le_last j) with h' | h'
        · exact le_of_lt h'
        · rw [h']
      exact hle.trans hWi
    -- restrict the chain to that member
    let l' : LTSeries {W : Set X // W ⊆ A i0 ∧ IsIrreducible W ∧ IsClosed W} :=
      { length := l.length
        toFun := fun j => ⟨(l j).1, hall j, (l j).2.2.1, (l j).2.2.2⟩
        step := fun j => l.step j }
    have hlen : (l.length : ℕ∞) = (l'.length : ℕ∞) := rfl
    rw [hlen]
    exact le_iSup_of_le i0 (le_iSup (fun l : LTSeries {W : Set X // W ⊆ A i0 ∧ IsIrreducible W ∧ IsClosed W} => (l.length : ℕ∞)) l')
  · refine iSup_le fun i => irrChainDim_mono (Set.subset_iUnion A i)

end IrrChainDim

/-! ## Part 5: dimensions of projective algebraic sets and of their cones -/

section Dims

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- The dimension of a projective algebraic set: the supremum of the lengths of chains of
irreducible closed subsets. -/
noncomputable def projDim (Y : Set (Proj k n)) : ℕ∞ := irrChainDim Y

/-- The dimension of the affine cone over a projective set. -/
noncomputable def coneDim (Y : Set (Proj k n)) : ℕ∞ := irrChainDim (Proj.cone Y)

theorem projDim_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) : projDim Y ≤ projDim Z :=
  irrChainDim_mono h

theorem coneDim_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) : coneDim Y ≤ coneDim Z :=
  irrChainDim_mono (Proj.cone_mono h)

/-- Singletons are closed in the affine Zariski topology. -/
theorem isClosed_singleton_affine {m : ℕ} (z : Fin m → k) :
    IsClosed ({z} : Set (Fin m → k)) := by
  rw [isClosed_iff_zarClosed k m]
  refine ⟨Ideal.span (Set.range (fun i : Fin m => MvPolynomial.X i - MvPolynomial.C (z i))), ?_⟩
  ext v
  rw [Set.mem_singleton_iff, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hzv
    rw [hzv]
    have hle : Ideal.span (Set.range (fun i : Fin m =>
        MvPolynomial.X i - MvPolynomial.C (z i))) ≤ RingHom.ker (MvPolynomial.aeval z) := by
      refine Ideal.span_le.mpr ?_
      rintro q ⟨i, rfl⟩
      simp
    intro p hp
    exact hle hp
  · intro h
    funext i
    have hv := h _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [MvPolynomial.aeval_eq_eval, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hv
    exact sub_eq_zero.mp hv

/-- The vertex of the cone is closed. -/
theorem isClosed_singleton_zero : IsClosed ({0} : Set (Fin (n + 1) → k)) :=
  isClosed_singleton_affine 0

theorem isIrreducible_singleton_affine {m : ℕ} (z : Fin m → k) :
    IsIrreducible ({z} : Set (Fin m → k)) :=
  ⟨⟨z, rfl⟩, isPreirreducible_singleton⟩

/-- Turning an `ℕ∞`-valued dimension into the `WithBot ℕ∞` dimension of I.1.8. -/
theorem varietyDim_eq_coe_irrChainDim {m : ℕ} {Z : Set (Fin m → k)} (hZ : Z.Nonempty) :
    varietyDim k m Z = (irrChainDim Z : WithBot ℕ∞) := by
  obtain ⟨z, hz⟩ := hZ
  haveI : Nonempty {W : Set (Fin m → k) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨{z}, Set.singleton_subset_iff.mpr hz, isIrreducible_singleton_affine z,
      isClosed_singleton_affine z⟩⟩
  rw [varietyDim, Order.krullDim_eq_iSup_length, irrChainDim,
    WithBot.coe_iSup (OrderTop.bddAbove _)]

/-- An affine space has dimension `m`. -/
theorem varietyDim_univ {m : ℕ} :
    varietyDim k m (Set.univ : Set (Fin m → k)) = (m : WithBot ℕ∞) := by
  have h := varietyDim_zeroLocus k m (⊥ : Ideal (MvPolynomial (Fin m) k))
  rw [MvPolynomial.zeroLocus_bot, Set.top_eq_univ] at h
  rw [h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial (Fin m) k)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- The full projective space has cone the whole affine space. -/
theorem coneDim_univ : coneDim (Set.univ : Set (Proj k n)) = (n + 1 : ℕ∞) := by
  have h1 : varietyDim k (n + 1) (Set.univ : Set (Fin (n + 1) → k)) =
      ((coneDim (Set.univ : Set (Proj k n))) : WithBot ℕ∞) := by
    rw [coneDim, ← Proj.cone_univ]
    exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
  rw [varietyDim_univ] at h1
  exact WithBot.coe_injective h1.symm

/-- The dimension of the cone over the empty set (a single point) is zero. -/
theorem coneDim_empty : coneDim (∅ : Set (Proj k n)) = 0 := by
  have h1 : varietyDim k (n + 1) ({0} : Set (Fin (n + 1) → k)) =
      ((coneDim (∅ : Set (Proj k n))) : WithBot ℕ∞) := by
    rw [coneDim, Proj.cone_empty]
    exact varietyDim_eq_coe_irrChainDim ⟨0, rfl⟩
  have h2 : varietyDim k (n + 1) ({0} : Set (Fin (n + 1) → k)) = 0 := by
    haveI : Subsingleton {W : Set (Fin (n + 1) → k) //
        W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W} := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have key : ∀ c : {W : Set (Fin (n + 1) → k) //
          W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W}, c.1 = {0} := by
        intro c
        obtain ⟨v, hv⟩ := c.2.2.1.1
        have hv0 : v = 0 := by simpa using c.2.1 hv
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨hv0 ▸ hv, fun w hw => ?_⟩
        simpa using c.2.1 hw
      rw [key a, key b]
    haveI : Nonempty {W : Set (Fin (n + 1) → k) //
        W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W} :=
      ⟨⟨{0}, subset_refl _, isIrreducible_singleton_affine 0, isClosed_singleton_zero⟩⟩
    rw [varietyDim]
    exact Order.krullDim_eq_zero
  rw [h2] at h1
  exact WithBot.coe_injective (by simpa using h1.symm)

end Dims

/-! ### Extending chains -/

section ChainExtend

variable {X : Type*} [TopologicalSpace X]

/-- Appending a strictly larger irreducible closed set lengthens a chain by one. -/
theorem irrChainDim_add_one_le {Z Y : Set X} (hZY : Z ⊆ Y) (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hne : Z ≠ Y) :
    irrChainDim Z + 1 ≤ irrChainDim Y := by
  haveI hQ : Nonempty {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨Z, subset_refl Z, hZi, hZc⟩⟩
  rw [irrChainDim, irrChainDim, ENat.iSup_add]
  refine iSup_le fun l => ?_
  let phi : {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} →
      {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    fun W => ⟨W.1, W.2.1.trans hZY, W.2.2.1, W.2.2.2⟩
  have hphi : StrictMono phi := fun a b hab => hab
  let Yq : {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨Y, fun x hx => hx, hYi, hYc⟩
  have hrel : (l.map phi hphi).last < Yq := by
    have hlast : (l.map phi hphi).last = phi (l (Fin.last l.length)) := rfl
    rw [hlast]
    refine ⟨(l (Fin.last l.length)).2.1.trans hZY, ?_⟩
    intro hEq
    exact hne (le_antisymm hZY (hEq.trans (l (Fin.last l.length)).2.1))
  let p : LTSeries {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    (l.map phi hphi).snoc Yq hrel
  have hlen : (p.length : ℕ∞) = (l.length : ℕ∞) + 1 := by simp [p]
  rw [← hlen]
  exact le_iSup (fun p : LTSeries {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} =>
    (p.length : ℕ∞)) p

end ChainExtend

/-! ## Part 6: `P^n` and affine space are noetherian -/

section AffineDCC

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Affine space with the Zariski topology satisfies the descending chain condition. -/
theorem affine_dcc (m : ℕ) : HasDCCClosed (Fin m → k) := by
  intro F hF hanti
  have hmono : Monotone fun i => MvPolynomial.vanishingIdeal k (F i) :=
    monotone_nat_of_le_succ fun i => MvPolynomial.vanishingIdeal_anti_mono (hanti i)
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun i => MvPolynomial.vanishingIdeal k (F i), hmono⟩ : ℕ →o Ideal (MvPolynomial (Fin m) k))
  refine ⟨N, fun i hi => ?_⟩
  have hI : MvPolynomial.vanishingIdeal k (F i) = MvPolynomial.vanishingIdeal k (F N) :=
    (hN i hi).symm
  rw [← zeroLocus_vanishingIdeal_of_isClosed k m (hF i),
    ← zeroLocus_vanishingIdeal_of_isClosed k m (hF N), hI]

end AffineDCC

section ProjForms

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem vanishingIdeal_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) :
    vanishingIdeal Z ≤ vanishingIdeal Y := by
  rw [vanishingIdeal, vanishingIdeal, Ideal.span_le]
  rintro f ⟨d, hd, hvan⟩
  exact subset_vanishingIdeal hd fun x hx => hvan x (h hx)

/-- The homogeneous members of the vanishing ideal. -/
noncomputable def vanishingForms (Z : Set (Proj k n)) : Set (HomogPoly k n) :=
  {f | f.1 ∈ vanishingIdeal Z}

theorem mem_zeroLocus_vanishingForms_iff {Z : Set (Proj k n)} {x : Proj k n} :
    x ∈ zeroLocus (vanishingForms Z) ↔
      ∀ f : MvPolynomial (Fin (n + 1)) k, (∃ d, f.IsHomogeneous d) → f ∈ vanishingIdeal Z →
        MvPolynomial.eval x.rep f = 0 := by
  constructor
  · rintro h f ⟨d, hd⟩ hf
    exact h ⟨f, d, hd⟩ hf
  · rintro h f hf
    exact h f.1 f.2 hf

theorem vanishingIdeal_eq_top_of_empty : vanishingIdeal (∅ : Set (Proj k n)) = ⊤ := by
  refine Ideal.eq_top_iff_one _ |>.mpr ?_
  exact subset_vanishingIdeal (MvPolynomial.isHomogeneous_one ..)
    (fun x hx => by simp at hx)

/-- `V(I(Z)) = Z` for closed `Z`. -/
theorem zeroLocus_vanishingForms_eq (Z : Set (Proj k n)) (hZ : IsClosed Z) :
    zeroLocus (vanishingForms Z) = Z := by
  have key : ∀ f : MvPolynomial (Fin (n + 1)) k, f ∈ vanishingIdeal Z → ∀ v hv,
      mk v hv ∈ Z → MvPolynomial.eval v f = 0 := by
    intro f hf v hv hmem
    have hf' : f ∈ vanishOnIdeal Z := by
      rw [vanishOnIdeal_eq_vanishingIdeal Z]; exact hf
    exact mem_vanishOnIdeal_iff.mp hf' v hv hmem
  refine le_antisymm ?_ ?_
  · rintro x hx
    rw [mem_zeroLocus_vanishingForms_iff] at hx
    rcases Set.eq_empty_or_nonempty Z with rfl | hZne
    · -- `1 ∈ I(∅)`, contradiction
      have hI : vanishingIdeal (∅ : Set (Proj k n)) = ⊤ := vanishingIdeal_eq_top_of_empty
      have hone : MvPolynomial.eval x.rep (1 : MvPolynomial (Fin (n + 1)) k) = 0 :=
        hx 1 ⟨0, MvPolynomial.isHomogeneous_one ..⟩ (by rw [hI]; exact Submodule.mem_top)
      simp at hone
    · have hcone : x.rep ∈ MvPolynomial.zeroLocus k (vanishingIdeal Z) := by
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [MvPolynomial.aeval_eq_eval, ← MvPolynomial.sum_homogeneousComponent p, map_sum]
        refine Finset.sum_eq_zero fun e _ => ?_
        have hmem : MvPolynomial.homogeneousComponent e p ∈ vanishingIdeal Z := by
          rw [← vanishOnIdeal_eq_vanishingIdeal Z]
          exact homogeneousComponent_mem_vanishOnIdeal (by rwa [vanishOnIdeal_eq_vanishingIdeal Z]) e
        exact hx _ ⟨e, MvPolynomial.homogeneousComponent_isHomogeneous e p⟩ hmem
      rw [← cone_eq_zeroLocus ((isProjClosed_iff_isClosed Z).mpr hZ) hZne] at hcone
      rcases hcone with h0 | ⟨_, hmem⟩
      · exact absurd h0 x.rep_nonzero
      · simpa using hmem
  · intro x hx f hf
    exact key f.1 hf x.rep x.rep_nonzero (by simpa using hx)

end Proj

end ProjForms

/-! ## Part 7: the projective space is noetherian, hyperplane sections of cones -/

section ProjNoetherian

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

/-- `P^n` satisfies the descending chain condition for closed subsets. -/
theorem dcc_closed (F : ℕ → Set (Proj k n)) (hF : ∀ i, IsClosed (F i))
    (hanti : ∀ i, F (i + 1) ⊆ F i) : ∃ N, ∀ i, N ≤ i → F i = F N := by
  have hmono : Monotone fun i => vanishingIdeal (F i) :=
    monotone_nat_of_le_succ fun i => vanishingIdeal_mono (hanti i)
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun i => vanishingIdeal (F i), hmono⟩ : ℕ →o Ideal (MvPolynomial (Fin (n + 1)) k))
  refine ⟨N, fun i hi => ?_⟩
  have hI : vanishingForms (F i) = vanishingForms (F N) := by
    have h2 : vanishingIdeal (F N) = vanishingIdeal (F i) := hN i hi
    simp only [vanishingForms, h2]
  rw [← zeroLocus_vanishingForms_eq (F i) (hF i), ← zeroLocus_vanishingForms_eq (F N) (hF N)]
  rw [hI]

/-- `P^n` is a noetherian topological space in Hartshorne's sense. -/
theorem hasDCCClosed : HasDCCClosed (Proj k n) := dcc_closed

/-- Finite irreducible decomposition of a closed subset of `P^n`. -/
theorem exists_finite_irred_cover_closed {Z : Set (Proj k n)} (hZ : IsClosed Z) :
    ∃ D : Set (Set (Proj k n)), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D :=
  exists_finite_irred_cover hasDCCClosed hZ

/-- The coordinate function `x_i`. -/
noncomputable def coord (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k := MvPolynomial.X i

theorem coord_isHomogeneous (i : Fin (n + 1)) : (coord (k := k) i).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X (R := k) i

/-- The coordinate form as a homogeneous polynomial. -/
noncomputable def coordForm (i : Fin (n + 1)) : HomogPoly k n :=
  ⟨coord (k := k) i, 1, coord_isHomogeneous i⟩

theorem eval_coord (v : Fin (n + 1) → k) (i : Fin (n + 1)) :
    MvPolynomial.eval v (coord (k := k) i) = v i := by
  simp [coord]

/-- The defining form of the coordinate hyperplane. -/
noncomputable def hyperplaneForms (i : Fin (n + 1)) : Set (HomogPoly k n) :=
  {coordForm (k := k) i}

/-- The coordinate hyperplane `x_i = 0`. -/
noncomputable def hyperplane (i : Fin (n + 1)) : Set (Proj k n) :=
  zeroLocus (hyperplaneForms (k := k) i)

theorem mem_hyperplaneForms {i : Fin (n + 1)} {f : HomogPoly k n} :
    f ∈ hyperplaneForms (k := k) i ↔ f = coordForm (k := k) i :=
  Iff.rfl

theorem hyperplane_eq_compreh (i : Fin (n + 1)) :
    hyperplane i = {x | IsZeroAt (coord (k := k) i) x} := by
  ext x
  show (∀ f ∈ hyperplaneForms (k := k) i, IsZeroAt f.1 x) ↔ IsZeroAt (coord (k := k) i) x
  constructor
  · intro hx
    exact hx _ (mem_hyperplaneForms.mpr rfl)
  · intro hx f hf
    rw [mem_hyperplaneForms] at hf
    rw [hf]
    exact hx

theorem isClosed_hyperplane (i : Fin (n + 1)) : IsClosed (hyperplane (k := k) (n := n) i) :=
  (isClosed_iff (k := k) (n := n) (hyperplane (k := k) (n := n) i)).mpr
    ⟨hyperplaneForms (k := k) i, rfl⟩

theorem mem_hyperplane_mk_iff {i : Fin (n + 1)} {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    mk v hv ∈ hyperplane i ↔ v i = 0 := by
  rw [hyperplane_eq_compreh]
  exact isZeroAt_mk_iff (coord_isHomogeneous i) hv |>.trans (by simp [eval_coord])

/-- The cone over a hyperplane section of `Y` is the hyperplane section of the cone. -/
theorem cone_inter_hyperplane (Y : Set (Proj k n)) (i : Fin (n + 1)) :
    cone (Y ∩ hyperplane i) =
      cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {coord (k := k) i}) := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem⟩)
    · refine ⟨Or.inl rfl, ?_⟩
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro p hp
      have hle : Ideal.span {coord (k := k) i} ≤
          RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
        refine Ideal.span_le.mpr ?_
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        show MvPolynomial.aeval (0 : Fin (n + 1) → k) (coord (k := k) i) = 0
        rw [MvPolynomial.aeval_eq_eval, eval_coord]
        simp
      rw [MvPolynomial.aeval_eq_eval]
      exact hle hp
    · refine ⟨Or.inr ⟨hv, hmem.1⟩, ?_⟩
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro p hp
      rw [MvPolynomial.aeval_eq_eval]
      have hle : Ideal.span {coord (k := k) i} ≤ RingHom.ker (MvPolynomial.aeval v) := by
        refine Ideal.span_le.mpr ?_
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        show MvPolynomial.aeval v (coord (k := k) i) = 0
        rw [MvPolynomial.aeval_eq_eval, eval_coord]
        exact (mem_hyperplane_mk_iff hv).mp hmem.2
      exact hle hp
  · rintro ⟨hv1, hv2⟩
    rcases hv1 with h0 | ⟨hv, hmem⟩
    · exact Or.inl h0
    · refine Or.inr ⟨hv, hmem, ?_⟩
      refine (mem_hyperplane_mk_iff hv).mpr ?_
      have h := (MvPolynomial.mem_zeroLocus_iff.mp hv2) (coord (k := k) i)
        (Ideal.mem_span_singleton_self _)
      rwa [MvPolynomial.aeval_eq_eval, eval_coord] at h

/-- Cones are strictly monotone on projective sets. -/
theorem cone_ssubset {Y Z : Set (Proj k n)} (h : Y ⊆ Z) (hne : Y ≠ Z) : cone Y ⊂ cone Z := by
  refine ⟨cone_mono h, fun hsub => ?_⟩
  have hZY : Z ⊆ Y := by
    intro x hx
    have hx' : x.rep ∈ cone Z := Or.inr ⟨x.rep_nonzero, by simpa using hx⟩
    rcases hsub hx' with h0 | ⟨_, hm⟩
    · exact absurd h0 x.rep_nonzero
    · simpa using hm
  exact hne (Set.Subset.antisymm h hZY)

/-- Some coordinate function does not vanish on a nonempty projective set. -/
theorem exists_coord_notMem_vanishingIdeal {Y : Set (Proj k n)} (hne : Y.Nonempty) :
    ∃ i : Fin (n + 1), coord (k := k) i ∉ vanishingIdeal Y := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  have hv : MvPolynomial.eval x.rep (coord (k := k) j) = 0 := by
    refine (mem_vanishOnIdeal_iff.mp ?_) x.rep x.rep_nonzero (by simpa using hx)
    rw [vanishOnIdeal_eq_vanishingIdeal Y]
    exact h j
  exact hj (by simpa [eval_coord] using hv)

end Proj

end ProjNoetherian

/-! ### The cone over a union, and dimensions of finite decompositions -/

section Decomposition

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem cone_iUnion {ι : Type*} [Nonempty ι] (A : ι → Set (Proj k n)) :
    cone (⋃ i, A i) = ⋃ i, cone (A i) := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem⟩)
    · exact Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, Or.inl rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact Set.mem_iUnion.mpr ⟨i, Or.inr ⟨hv, hi⟩⟩
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact cone_mono (Set.subset_iUnion A i) hi

end Proj

/-- The cone dimension is computed by any finite closed cover. -/
theorem coneDim_eq_iSup_decomposition {Y : Set (Proj k n)} {D : Set (Set (Proj k n))}
    (hDfin : D.Finite) (hDne : D.Nonempty) (hDirr : ∀ W ∈ D, IsIrredClosed W)
    (hDcov : Y = ⋃₀ D) :
    coneDim Y = ⨆ W : D, coneDim (W : Set (Proj k n)) := by
  haveI : Fintype D := hDfin.fintype
  haveI : Nonempty D := hDne.to_subtype
  have hcl : ∀ W : D, IsClosed (W : Set (Proj k n)) := fun W => (hDirr W.1 W.2).2.1
  rw [coneDim, hDcov, Set.sUnion_eq_iUnion, Proj.cone_iUnion,
    irrChainDim_iUnion (fun W : D => Proj.cone (W : Set (Proj k n)))
      (fun W => Proj.isClosed_cone (hcl W))]
  rfl

/-- The projective dimension is computed by any finite closed cover. -/
theorem projDim_eq_iSup_decomposition {Y : Set (Proj k n)} {D : Set (Set (Proj k n))}
    (hDfin : D.Finite) (hDirr : ∀ W ∈ D, IsIrredClosed W) (hDcov : Y = ⋃₀ D) :
    projDim Y = ⨆ W : D, projDim (W : Set (Proj k n)) := by
  haveI : Fintype D := hDfin.fintype
  have hcl : ∀ W : D, IsClosed (W : Set (Proj k n)) := fun W => (hDirr W.1 W.2).2.1
  rw [projDim, hDcov, Set.sUnion_eq_iUnion,
    irrChainDim_iUnion (fun W : D => (W : Set (Proj k n))) hcl]
  rfl

end Decomposition

/-! ## Part 8: comparison of the dimensions -/

section Comparison

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- Monotonicity of the `WithBot`-valued dimension. -/
theorem varietyDim_mono {m : ℕ} {Z Z' : Set (Fin m → k)} (h : Z ⊆ Z') :
    varietyDim k m Z ≤ varietyDim k m Z' := by
  rw [varietyDim, varietyDim]
  refine Order.krullDim_le_of_strictMono
    (fun W : {W : Set (Fin m → k) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} =>
      (⟨W.1, W.2.1.trans h, W.2.2⟩ :
        {W : Set (Fin m → k) // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W}))
    (fun a b hab => hab)

/-- **The lower bound**: the cone over a nonempty closed set has dimension at least one more
than the set itself. -/
theorem projDim_add_one_le_coneDim {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    projDim Y + 1 ≤ coneDim Y := by
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := Proj.exists_finite_irred_cover_closed (k := k) (n := n) hYc
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with rfl | h
    · exfalso
      rw [hDcov] at hne
      simp at hne
    · exact h
  obtain ⟨W, hWD⟩ := hDne
  have hWirr : IsIrreducible W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).2
  have hWcl : IsClosed W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).1
  haveI hQ : Nonempty {Z : Set (Proj k n) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z} :=
    ⟨⟨W, by rw [hDcov]; exact Set.subset_sUnion_of_mem hWD, hWirr, hWcl⟩⟩
  rw [projDim, coneDim, irrChainDim, irrChainDim, ENat.iSup_add]
  refine iSup_le fun l => ?_
  let phi : {Z : Set (Proj k n) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z} →
      {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    fun Z => ⟨Proj.cone Z.1, Proj.cone_mono Z.2.1,
      Proj.isIrreducible_cone Z.2.2.2 Z.2.2.1, Proj.isClosed_cone Z.2.2.2⟩
  have hphi : StrictMono phi := fun a b hab => Proj.cone_ssubset (le_of_lt hab) (ne_of_lt hab)
  let lc := l.map phi hphi
  have hhead : lc.head = phi (l 0) := rfl
  let V0 : {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    ⟨{0}, fun v hv => by rw [Set.mem_singleton_iff] at hv; subst hv; exact Or.inl rfl,
      isIrreducible_singleton_affine 0, isClosed_singleton_zero⟩
  have hrel : V0 < lc.head := by
    rw [hhead]
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Or.inl rfl
    · intro hsub
      obtain ⟨x, hx⟩ := (l 0).2.2.1.1
      have hmem : x.rep ∈ Proj.cone (l 0).1 :=
        Or.inr ⟨x.rep_nonzero, by simpa using hx⟩
      have h0 : x.rep = 0 := by
        have := hsub hmem
        rwa [Set.mem_singleton_iff] at this
      exact x.rep_nonzero h0
  let p : LTSeries {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    lc.cons V0 hrel
  have hlen : (p.length : ℕ∞) = (l.length : ℕ∞) + 1 := by
    have h1 : lc.length = l.length := by simp [lc]
    have h2 : p.length = lc.length + 1 := by simp [p]
    rw [h2, h1]
    push_cast
    ring
  rw [← hlen]
  exact le_iSup (fun p : LTSeries {V : Set (Fin (n + 1) → k) //
    V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} => (p.length : ℕ∞)) p

end Comparison

/-! ## Part 9: the upper bound -/

section UpperBound

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

theorem coord_ne_zero (i : Fin (n + 1)) : Proj.coord (k := k) i ≠ 0 := by
  intro h
  have := Proj.eval_coord (fun j => if j = i then (1 : k) else 0) i
  rw [h] at this
  simpa using this

/-- The affine space over a single point has dimension zero. -/
theorem varietyDim_singleton_zero {m : ℕ} :
    varietyDim k m ({0} : Set (Fin m → k)) = 0 := by
  haveI : Subsingleton {W : Set (Fin m → k) //
      W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W} := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have key : ∀ c : {W : Set (Fin m → k) //
        W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W}, c.1 = {0} := by
      intro c
      obtain ⟨v, hv⟩ := c.2.2.1.1
      have hv0 : v = 0 := by simpa using c.2.1 hv
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hv0 ▸ hv, fun w hw => ?_⟩
      simpa using c.2.1 hw
    rw [key a, key b]
  haveI : Nonempty {W : Set (Fin m → k) //
      W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨{0}, subset_refl _, isIrreducible_singleton_affine 0, isClosed_singleton_affine 0⟩⟩
  rw [varietyDim]
  exact Order.krullDim_eq_zero

/-- The cone dimension is bounded by the number of variables. -/
theorem coneDim_le_succ {Y : Set (Proj k n)} (hYc : IsClosed Y) :
    coneDim Y ≤ (n + 1 : ℕ∞) := by
  rcases Set.eq_empty_or_nonempty Y with rfl | hne
  · rw [coneDim_empty]; simp
  · have h1 : varietyDim k (n + 1) (Proj.cone Y) = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
      rw [coneDim]
      exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
    have h2 : Proj.cone Y = MvPolynomial.zeroLocus k (Proj.vanishingIdeal Y) :=
      Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne
    have h3 : varietyDim k (n + 1) (Proj.cone Y) =
        ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) := by
      rw [h2, varietyDim_zeroLocus]
    have h4 : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) ≤
        ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
      refine (ringKrullDim_quotient_le (Proj.vanishingIdeal Y)).trans_eq ?_
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    have h5 : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← h1, h3]
      exact h4
    exact WithBot.coe_le_coe.mp h5

/-- **The upper bound**, by strong induction on a bound for `projDim Y`. -/
theorem coneDim_le_projDim_add_one_of_le : ∀ (N : ℕ) (Y : Set (Proj k n)), IsClosed Y →
    IsIrreducible Y → Y.Nonempty → projDim Y ≤ (N : ℕ∞) → coneDim Y ≤ projDim Y + 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro Y hYc hYi hne hbound
    obtain ⟨i, hi⟩ := Proj.exists_coord_notMem_vanishingIdeal (k := k) (n := n) hne
    have hHcl : IsClosed (Proj.hyperplane (k := k) (n := n) i) := Proj.isClosed_hyperplane i
    have hY'cl : IsClosed (Y ∩ Proj.hyperplane (k := k) (n := n) i) := hYc.inter hHcl
    have hYnotH : ¬ (Y ⊆ Proj.hyperplane (k := k) (n := n) i) := by
      intro hsub
      have hmem : Proj.coord (k := k) i ∈ Proj.vanishOnIdeal Y := by
        refine Proj.mem_vanishOnIdeal_iff.mpr ?_
        intro v hv hmem
        have hv0 := (Proj.mem_hyperplane_mk_iff hv).mp (hsub hmem)
        simpa [Proj.eval_coord] using hv0
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal Y] at hmem
      exact hi hmem
    have hYnsub : ∃ y ∈ Proj.cone Y, (MvPolynomial.aeval y) (Proj.coord (k := k) i) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hmem : Proj.coord (k := k) i ∈ Proj.vanishOnIdeal Y := by
        refine Proj.mem_vanishOnIdeal_iff.mpr ?_
        intro v hv hmem
        have hv' : (MvPolynomial.aeval v) (Proj.coord (k := k) i) = 0 := hcon v (Or.inr ⟨hv, hmem⟩)
        rwa [MvPolynomial.aeval_eq_eval] at hv'
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal Y] at hmem
      exact hi hmem
    have hconeYirr : IsIrreducible (Proj.cone Y) := Proj.isIrreducible_cone hYc hYi
    have hconeYcl : IsClosed (Proj.cone Y) := Proj.isClosed_cone hYc
    have hbridge : varietyDim k (n + 1) (Proj.cone Y) = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
      rw [coneDim]
      exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
    by_cases hY'ne : (Y ∩ Proj.hyperplane (k := k) (n := n) i).Nonempty
    · -- ## the hyperplane section is nonempty
      have hAffCl : IsClosed (Proj.cone Y ∩
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i})) := by
        rw [← Proj.cone_inter_hyperplane Y i]
        exact Proj.isClosed_cone hY'cl
      obtain ⟨D, hDfin, hDirr, hDcov, hDanti⟩ :=
        exists_irredDecomposition (affine_dcc (n + 1)) hAffCl
      have h0mem : (0 : Fin (n + 1) → k) ∈ Proj.cone Y ∩
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := by
        refine ⟨Or.inl rfl, ?_⟩
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        have hle : Ideal.span {Proj.coord (k := k) i} ≤
            RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          intro q hq
          rw [Set.mem_singleton_iff] at hq
          subst hq
          show MvPolynomial.aeval (0 : Fin (n + 1) → k) (Proj.coord (k := k) i) = 0
          rw [MvPolynomial.aeval_eq_eval, Proj.eval_coord]
          rfl
        rw [MvPolynomial.aeval_eq_eval]
        exact hle hp
      have hDne : D.Nonempty := by
        rcases Set.eq_empty_or_nonempty D with rfl | h
        · exfalso; rw [hDcov] at h0mem; simp at h0mem
        · exact h
      obtain ⟨W, hWD⟩ := hDne
      have hWirr : IsIrreducible W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).2
      have hWcl : IsClosed W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).1
      have hWsub : W ⊆ Proj.cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := by
        rw [hDcov]; exact Set.subset_sUnion_of_mem hWD
      have hZmax : ∀ W' : Set (Fin (n + 1) → k),
          W' ⊆ Proj.cone Y → W' ⊆ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) →
          IsIrreducible W' → IsClosed W' → W ⊆ W' → W' ⊆ W := by
        intro W' h1 h2 h3 h4 h5
        have hW'sub : W' ⊆ ⋃₀ D := by rw [← hDcov]; exact fun x hx => ⟨h1 hx, h2 hx⟩
        obtain ⟨W'', hW''D, hW'W''⟩ := IsIrredClosed.exists_subset_of_finite_sUnion
          (isIrredClosed_iff_isIrreducible.mpr ⟨h4, h3⟩) hDfin
          (fun V hV => (isIrredClosed_iff_isIrreducible.mp (hDirr V hV)).1) hW'sub
        rw [hDanti W hWD W'' hW''D (h5.trans hW'W'')]
        exact hW'W''
      have hI18 := hartshorne_exercise_I_1_8 k (n + 1) (Proj.cone Y) (Proj.coord (k := k) i)
        hconeYcl hconeYirr (coord_ne_zero i) hYnsub W (fun x hx => (hWsub hx).1)
        (fun x hx => (hWsub hx).2) hWirr hWcl hZmax
      have hbridge' : varietyDim k (n + 1) (Proj.cone (Y ∩ Proj.hyperplane (k := k) (n := n) i)) =
          ((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) : ℕ∞) : WithBot ℕ∞) := by
        rw [coneDim]
        exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
      have hstep1 : coneDim Y ≤ coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 := by
        have hmono : varietyDim k (n + 1) W ≤
            varietyDim k (n + 1) (Proj.cone (Y ∩ Proj.hyperplane (k := k) (n := n) i)) := by
          refine varietyDim_mono ?_
          rw [Proj.cone_inter_hyperplane Y i]
          exact hWsub
        rw [hbridge'] at hmono
        have hI18' : varietyDim k (n + 1) W + 1 = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
          rw [hI18, hbridge]
        have hgoal : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤
            ((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) : ℕ∞) : WithBot ℕ∞) + 1 := by
          rw [← hI18']
          exact add_le_add hmono le_rfl
        have hgoal' : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤
            (((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 : ℕ∞)) : WithBot ℕ∞) := by
          simpa using hgoal
        exact WithBot.coe_le_coe.mp hgoal'
      -- ## the projective decomposition of `Y ∩ H`
      obtain ⟨D', hD'fin, hD'irr, hD'cov⟩ :=
        Proj.exists_finite_irred_cover_closed (k := k) (n := n) hY'cl
      have hD'ne : D'.Nonempty := by
        rcases Set.eq_empty_or_nonempty D' with rfl | h
        · exfalso; rw [hD'cov] at hY'ne; simp at hY'ne
        · exact h
      haveI : Nonempty D' := hD'ne.to_subtype
      have hproj' : projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) =
          ⨆ Z : D', projDim (Z : Set (Proj k n)) :=
        projDim_eq_iSup_decomposition hD'fin hD'irr hD'cov
      have hcone' : coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) =
          ⨆ Z : D', coneDim (Z : Set (Proj k n)) :=
        coneDim_eq_iSup_decomposition hD'fin hD'ne hD'irr hD'cov
      have hsmaller : ∀ Z ∈ D', projDim Z + 1 ≤ projDim Y := by
        intro Z hZ
        have hZirr : IsIrreducible Z := (isIrredClosed_iff_isIrreducible.mp (hD'irr Z hZ)).2
        have hZcl : IsClosed Z := (isIrredClosed_iff_isIrreducible.mp (hD'irr Z hZ)).1
        have hZY' : Z ⊆ Y := by
          refine (Set.subset_sUnion_of_mem hZ).trans ?_
          rw [← hD'cov]
          exact Set.inter_subset_left
        have hZne : Z ≠ Y := by
          intro heq
          refine hYnotH ?_
          rw [← heq]
          refine (Set.subset_sUnion_of_mem hZ).trans ?_
          rw [← hD'cov]
          exact Set.inter_subset_right
        exact irrChainDim_add_one_le hZY' hYc hYi hZcl hZirr hZne
      have hIH : ∀ Z : D', coneDim (Z : Set (Proj k n)) ≤ projDim (Z : Set (Proj k n)) + 1 := by
        intro Z
        have hsmall : projDim (Z : Set (Proj k n)) + 1 ≤ projDim Y := hsmaller Z.1 Z.2
        have hZirr : IsIrreducible (Z : Set (Proj k n)) :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).2
        have hZcl : IsClosed (Z : Set (Proj k n)) :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).1
        have hZne : (Z : Set (Proj k n)).Nonempty :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).2.1
        have hNZ' : projDim (Z : Set (Proj k n)) + 1 ≤ ((N : ℕ∞)) := hsmall.trans hbound
        have hNpos : 0 < N := by
          rcases Nat.eq_zero_or_pos N with h0 | h
          · exfalso
            rw [h0] at hNZ'
            simp at hNZ'
          · exact h
        have hNZ : projDim (Z : Set (Proj k n)) ≤ ((N - 1 : ℕ) : ℕ∞) := by
          have h2 : ((N : ℕ∞)) = ((N - 1 : ℕ) : ℕ∞) + 1 := by
            have h3 : N = (N - 1) + 1 := (Nat.sub_add_cancel hNpos).symm
            rw [h3]
            push_cast
            ring
          rw [h2] at hNZ'
          exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hNZ'
        exact IH (N - 1) (Nat.sub_lt hNpos Nat.one_pos) Z.1 hZcl hZirr hZne hNZ
      have hfin : coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 ≤ projDim Y + 1 := by
        have h1 : (⨆ Z : D', coneDim (Z : Set (Proj k n))) ≤
            ⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1) :=
          iSup_le fun Z => (hIH Z).trans
            (le_iSup (fun Z : D' => projDim (Z : Set (Proj k n)) + 1) Z)
        have h2 : (⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1)) =
            projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 := by
          rw [← ENat.iSup_add, hproj']
        have h3 : projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 ≤ projDim Y := by
          rw [hproj', ENat.iSup_add]
          exact iSup_le fun Z => hsmaller Z.1 Z.2
        rw [hcone']
        calc (⨆ Z : D', coneDim (Z : Set (Proj k n))) + 1
            ≤ (⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1)) + 1 := add_le_add h1 le_rfl
          _ = (projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1) + 1 := by rw [h2]
          _ ≤ projDim Y + 1 := add_le_add h3 le_rfl
      exact hstep1.trans hfin
    · -- ## the hyperplane section is empty
      have hY'empty : Y ∩ Proj.hyperplane (k := k) (n := n) i = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hY'ne
      have hcone0 : Proj.cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) =
          {0} := by
        rw [← Proj.cone_inter_hyperplane Y i, hY'empty, Proj.cone_empty]
      have hZmax : ∀ W' : Set (Fin (n + 1) → k),
          W' ⊆ Proj.cone Y → W' ⊆ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) →
          IsIrreducible W' → IsClosed W' → ({0} : Set (Fin (n + 1) → k)) ⊆ W' → W' ⊆ {0} := by
        intro W' h1 h2 h3 h4 h5
        rw [← hcone0]
        exact fun x hx => ⟨h1 hx, h2 hx⟩
      have hsub0 : ({0} : Set (Fin (n + 1) → k)) ⊆ Proj.cone Y := fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl rfl
      have hsub0' : ({0} : Set (Fin (n + 1) → k)) ⊆
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := fun x hx => by
        rw [Set.mem_singleton_iff] at hx; subst hx
        have hle : Ideal.span {Proj.coord (k := k) i} ≤
            RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          intro q hq
          rw [Set.mem_singleton_iff] at hq
          subst hq
          show MvPolynomial.aeval (0 : Fin (n + 1) → k) (Proj.coord (k := k) i) = 0
          rw [MvPolynomial.aeval_eq_eval, Proj.eval_coord]
          rfl
        rw [MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval]
        exact hle
      have hI18 := hartshorne_exercise_I_1_8 k (n + 1) (Proj.cone Y) (Proj.coord (k := k) i)
        hconeYcl hconeYirr (coord_ne_zero i) hYnsub ({0} : Set (Fin (n + 1) → k)) hsub0 hsub0'
        (isIrreducible_singleton_affine 0) (isClosed_singleton_affine (0 : Fin (n + 1) → k)) hZmax
      rw [varietyDim_singleton_zero] at hI18
      rw [hbridge] at hI18
      have hone : (coneDim Y : ℕ∞) = 1 := by
        have : ((coneDim Y : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
          rw [← hI18]; norm_num
        exact WithBot.coe_injective this
      rw [hone]
      simp

/-- The irreducible case of the cone dimension formula. -/
theorem coneDim_eq_projDim_add_one_of_irreducible {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) : coneDim Y = projDim Y + 1 := by
  refine le_antisymm ?_ (projDim_add_one_le_coneDim hYc hne)
  refine coneDim_le_projDim_add_one_of_le (n + 1) Y hYc hYi hne ?_
  have h := (projDim_add_one_le_coneDim hYc hne).trans (coneDim_le_succ hYc)
  have h2 : ((n + 1 : ℕ∞)) = ((n : ℕ∞)) + 1 := by simp
  rw [h2] at h
  have hle : projDim Y ≤ ((n : ℕ∞)) :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp h
  refine hle.trans ?_
  exact Nat.cast_le.mpr (Nat.le_succ n)

end UpperBound

/-! ## Part 10: part (b) and the full exercise -/

section Final

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem isIrreducible_of_isIrreducible_cone {Y : Set (Proj k n)}
    (hne : Y.Nonempty) (h : IsIrreducible (cone Y)) : IsIrreducible Y := by
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have hcover : cone Y ⊆ cone A ∪ cone B := by
    rw [← cone_union]
    exact cone_mono hsub
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp h.2)
    (cone A) (cone B) (isClosed_cone hA) (isClosed_cone hB) hcover
  rcases hsplit with h' | h'
  · refine Or.inl ?_
    intro x hx
    have hx' : x.rep ∈ cone A := h' (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm
  · refine Or.inr ?_
    intro x hx
    have hx' : x.rep ∈ cone B := h' (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm

/-- **(b)**, algebraic form: the cone is irreducible iff `I(Y)` is prime. -/
theorem isIrreducible_cone_iff_isPrime {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hne : Y.Nonempty) :
    IsIrreducible (cone Y) ↔ (vanishingIdeal Y).IsPrime := by
  constructor
  · intro hirr
    have memcone : ∀ f : MvPolynomial (Fin (n + 1)) k,
        f ∈ (MvPolynomial.vanishingIdeal k (cone Y) : Set (MvPolynomial (Fin (n + 1)) k)) ↔
          ∀ v ∈ cone Y, MvPolynomial.aeval v f = 0 :=
      fun f => MvPolynomial.mem_vanishingIdeal_iff
    have h1 : vanishingIdeal Y = MvPolynomial.vanishingIdeal k (cone Y) := by
      refine le_antisymm ?_ ?_
      · rw [vanishingIdeal, Ideal.span_le]
        rintro f ⟨d, hd, hvan⟩
        rw [memcone]
        intro v hv
        rw [MvPolynomial.aeval_eq_eval]
        rcases hv with h0 | ⟨hvne, hmem⟩
        · subst h0
          rcases Nat.eq_zero_or_pos d with hd0 | hdpos
          · subst hd0
            obtain ⟨x, hx⟩ := hne
            rw [eq_zero_of_isHomogeneous_zero hd (hvan x hx)]
            simp
          · exact eval_zero_of_isHomogeneous_pos hdpos hd
        · exact (isZeroAt_mk_iff hd hvne).1 (hvan _ hmem)
      · intro f hf
        have hmem : f ∈ (vanishOnIdeal Y : Set (MvPolynomial (Fin (n + 1)) k)) :=
          (mem_vanishOnIdeal_iff (k := k) (Y := Y) (f := f)).mpr (fun v hv hmem => by
            rw [← MvPolynomial.aeval_eq_eval]
            exact (memcone f).mp hf v (Or.inr ⟨hv, hmem⟩))
        rw [vanishOnIdeal_eq_vanishingIdeal Y] at hmem
        exact hmem
    rw [h1]
    exact vanishingIdeal_isPrime (k := k) (n := n + 1) (isClosed_cone hYc) hirr
  · intro hp
    rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed Y).mpr hYc) hne]
    exact zeroLocus_irreducible k (n + 1) hp

/-- **(b)**: the cone over `Y` is irreducible iff `Y` is. -/
theorem isIrreducible_cone_iff' {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    IsIrreducible (cone Y) ↔ IsIrreducible Y :=
  ⟨isIrreducible_of_isIrreducible_cone hne, isIrreducible_cone hYc⟩

/-- `I(Y)` is prime iff `Y` is irreducible (for nonempty closed `Y`). -/
theorem vanishingIdeal_isPrime_iff {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    (vanishingIdeal Y).IsPrime ↔ IsIrreducible Y := by
  rw [← isIrreducible_cone_iff_isPrime hYc hne]
  exact isIrreducible_cone_iff' hYc hne

end Proj

/-- **(c)** for an irreducible projective variety. -/
theorem coneDim_eq_projDim_add_one_irreducible {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) : coneDim Y = projDim Y + 1 :=
  coneDim_eq_projDim_add_one_of_irreducible hYc hYi hne

/-- **(c)** for an arbitrary projective algebraic set, via its irreducible components. -/
theorem coneDim_eq_projDim_add_one {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    coneDim Y = projDim Y + 1 := by
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := Proj.exists_finite_irred_cover_closed (k := k) (n := n) hYc
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with rfl | h
    · exfalso; rw [hDcov] at hne; simp at hne
    · exact h
  haveI : Nonempty D := hDne.to_subtype
  have hcone : coneDim Y = ⨆ W : D, coneDim (W : Set (Proj k n)) :=
    coneDim_eq_iSup_decomposition hDfin hDne hDirr hDcov
  have hproj : projDim Y = ⨆ W : D, projDim (W : Set (Proj k n)) :=
    projDim_eq_iSup_decomposition hDfin hDirr hDcov
  rw [hcone, hproj, ENat.iSup_add]
  refine iSup_congr fun W => ?_
  exact coneDim_eq_projDim_add_one_irreducible
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).1
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).2
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).2.1

/-- **Hartshorne, Algebraic Geometry, Exercise I.2.10.** -/
theorem hartshorne_exercise_I_2_10 {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    -- (a) the cone is the affine zero locus of `I(Y)`
    Proj.cone Y = MvPolynomial.zeroLocus k (Proj.vanishingIdeal Y) ∧
    -- (b) the cone is irreducible iff `I(Y)` is prime, iff `Y` is irreducible
    (IsIrreducible (Proj.cone Y) ↔ (Proj.vanishingIdeal Y).IsPrime) ∧
    (IsIrreducible (Proj.cone Y) ↔ IsIrreducible Y) ∧
    -- (c) dimension of the cone = dimension of the homogeneous coordinate ring
    -- = dimension of `Y` plus one
    varietyDim k (n + 1) (Proj.cone Y) = ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) ∧
    varietyDim k (n + 1) (Proj.cone Y) = (((coneDim Y : ℕ∞) : WithBot ℕ∞)) ∧
    ((coneDim Y : ℕ∞) : WithBot ℕ∞) = ((projDim Y + 1 : ℕ∞) : WithBot ℕ∞) ∧
    (coneDim Y = projDim Y + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne
  · exact Proj.isIrreducible_cone_iff_isPrime hYc hne
  · exact Proj.isIrreducible_cone_iff' hYc hne
  · rw [Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne,
      varietyDim_zeroLocus]
  · rw [coneDim]
    exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
  · rw [coneDim_eq_projDim_add_one hYc hne]
  · exact coneDim_eq_projDim_add_one hYc hne

end Final

#print axioms Hartshorne77.Ex_I_2_11.hartshorne_exercise_I_2_10
#print axioms Hartshorne77.Ex_I_2_11.coneDim_eq_projDim_add_one
#print axioms Hartshorne77.Ex_I_2_11.coneDim_eq_projDim_add_one_irreducible
#print axioms Hartshorne77.Ex_I_2_11.projDim_add_one_le_coneDim
#print axioms Hartshorne77.Ex_I_2_11.Proj.cone_eq_zeroLocus
#print axioms Hartshorne77.Ex_I_2_11.Proj.isIrreducible_cone_iff_isPrime
#print axioms Hartshorne77.Ex_I_2_11.Proj.isIrreducible_cone_iff'
#print axioms Hartshorne77.Ex_I_2_11.Proj.vanishingIdeal_isPrime_iff

end Hartshorne77.Ex_I_2_11


set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u

variable {k : Type u} [Field k]

/-! ## Part 1: linear forms -/

section LinearForms

variable (k) (m : ℕ)

/-- The space of linear forms in `k[x₀,…,x_{m-1}]`: the span of the coordinate functions. -/
noncomputable def linSpace : Submodule k (MvPolynomial (Fin m) k) :=
  Submodule.span k (Set.range fun i : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) k))

variable {k m}

theorem X_mem_linSpace (i : Fin m) :
    (MvPolynomial.X i : MvPolynomial (Fin m) k) ∈ linSpace k m :=
  Submodule.subset_span (Set.mem_range_self i)

theorem isHomogeneous_one_smul (a : k) {f : MvPolynomial (Fin m) k} (hf : f.IsHomogeneous 1) :
    (a • f).IsHomogeneous 1 := by
  rw [MvPolynomial.smul_eq_C_mul]
  simpa using (MvPolynomial.isHomogeneous_C (Fin m) a).mul hf

theorem linSpace_isHomogeneous {f : MvPolynomial (Fin m) k} (hf : f ∈ linSpace k m) :
    f.IsHomogeneous 1 := by
  refine Submodule.span_induction (p := fun x _ => x.IsHomogeneous 1) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i, rfl⟩
    exact MvPolynomial.isHomogeneous_X k i
  · exact MvPolynomial.isHomogeneous_zero (Fin m) k 1
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro a x _ hx
    exact isHomogeneous_one_smul a hx

/-- A homogeneous polynomial of degree one is the linear combination of the variables given by
its coefficients. -/
theorem eq_sum_coeff_smul_X {f : MvPolynomial (Fin m) k} (hf : f.IsHomogeneous 1) :
    f = ∑ i, f.coeff (Finsupp.single i 1) • (MvPolynomial.X i : MvPolynomial (Fin m) k) := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_sum]
  by_cases hd : ∃ i : Fin m, Finsupp.single i 1 = d
  · obtain ⟨i₀, rfl⟩ := hd
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X]
      rw [if_neg]
      · simp
      · intro h
        rw [Finsupp.single_eq_single_iff] at h
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hb h1
        · exact one_ne_zero h1
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · push Not at hd
    rw [Finset.sum_eq_zero]
    · have hnotmem : d ∉ f.support := by
        intro hmem
        have h1 : d.sum (fun x n => n) = 1 := (hf.degree_eq_sum_deg_support hmem).symm
        obtain ⟨a, ha⟩ := (Finsupp.sum_eq_one_iff d).mp h1
        exact hd a ha.symm
      simpa [MvPolynomial.mem_support_iff] using hnotmem
    · intro i _
      simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X]
      rw [if_neg (fun h => hd i h)]
      simp

theorem linSpace_eq_set : (linSpace k m : Set (MvPolynomial (Fin m) k)) = {f | f.IsHomogeneous 1} := by
  ext f
  constructor
  · exact linSpace_isHomogeneous
  · intro hf
    rw [eq_sum_coeff_smul_X hf]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (X_mem_linSpace i)

theorem linSpace_neg {f : MvPolynomial (Fin m) k} (hf : f ∈ linSpace k m) : -f ∈ linSpace k m :=
  Submodule.neg_mem _ hf

theorem linSpace_sub {f g : MvPolynomial (Fin m) k} (hf : f ∈ linSpace k m)
    (hg : g ∈ linSpace k m) : f - g ∈ linSpace k m :=
  Submodule.sub_mem _ hf hg

/-- The coordinate vector of a linear form. -/
noncomputable def coeffVec : linSpace k m →ₗ[k] (Fin m → k) where
  toFun f := fun i => (f : MvPolynomial (Fin m) k).coeff (Finsupp.single i 1)
  map_add' f g := by
    ext i
    simp [MvPolynomial.coeff_add]
  map_smul' a f := by
    ext i
    simp [MvPolynomial.coeff_smul]

theorem coeffVec_injective : Function.Injective (coeffVec (k := k) (m := m)) := by
  intro f g h
  have hf : ((f : MvPolynomial (Fin m) k)).IsHomogeneous 1 := linSpace_isHomogeneous f.2
  have hg : ((g : MvPolynomial (Fin m) k)).IsHomogeneous 1 := linSpace_isHomogeneous g.2
  refine Subtype.ext ?_
  rw [eq_sum_coeff_smul_X hf, eq_sum_coeff_smul_X hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (f : MvPolynomial (Fin m) k).coeff (Finsupp.single i 1) =
    (g : MvPolynomial (Fin m) k).coeff (Finsupp.single i 1) from congrFun h i]

/-- The linear form with coordinate vector `c`. -/
noncomputable def linForm (c : Fin m → k) : MvPolynomial (Fin m) k :=
  ∑ i, c i • (MvPolynomial.X i : MvPolynomial (Fin m) k)

theorem linForm_mem_linSpace (c : Fin m → k) : linForm (k := k) c ∈ linSpace k m :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (X_mem_linSpace i)

theorem coeff_linForm (c : Fin m → k) (i : Fin m) :
    (linForm c).coeff (Finsupp.single i 1) = c i := by
  classical
  rw [linForm, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X]
    rw [if_neg]
    · simp
    · intro h
      rw [Finsupp.single_eq_single_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hb h1
      · exact one_ne_zero h1
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeffVec_surjective : Function.Surjective (coeffVec (k := k) (m := m)) := by
  intro c
  refine ⟨⟨linForm c, linForm_mem_linSpace c⟩, ?_⟩
  ext i
  exact coeff_linForm c i

/-- Linear forms are determined by, and freely given by, their coordinate vectors. -/
noncomputable def coeffEquiv : linSpace k m ≃ₗ[k] (Fin m → k) :=
  LinearEquiv.ofBijective (coeffVec) ⟨coeffVec_injective, coeffVec_surjective⟩

end LinearForms

/-! ## Part 2: the shear automorphism -/

section Shear

variable {m : ℕ}

theorem linForm_eq_erase_add (j : Fin m) (c : Fin m → k) :
    linForm c = (∑ i ∈ Finset.univ.erase j, c i • (MvPolynomial.X i : MvPolynomial (Fin m) k))
      + c j • (MvPolynomial.X j) := by
  rw [linForm, ← Finset.sum_erase_add _ (fun i => c i • (MvPolynomial.X i : MvPolynomial (Fin m) k))
    (Finset.mem_univ j)]

theorem linFormErase_mem (j : Fin m) (c : Fin m → k) :
    (∑ i ∈ Finset.univ.erase j, c i • (MvPolynomial.X i : MvPolynomial (Fin m) k)) ∈ linSpace k m :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (X_mem_linSpace i)

/-- Substitution replacing the `j`-th variable by the linear form `linForm c`. -/
noncomputable def shearHom (j : Fin m) (c : Fin m → k) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.aeval (fun i => if i = j then linForm c else MvPolynomial.X i)

/-- Substitution solving `linForm c` for the `j`-th variable. -/
noncomputable def shearInvHom (j : Fin m) (c : Fin m → k) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.aeval (fun i => if i = j then
    (c j)⁻¹ • (MvPolynomial.X j - ∑ l ∈ Finset.univ.erase j,
      c l • (MvPolynomial.X l : MvPolynomial (Fin m) k)) else MvPolynomial.X i)

theorem shearHom_X_self (j : Fin m) (c : Fin m → k) :
    shearHom j c (MvPolynomial.X j) = linForm c := by
  simp [shearHom]

theorem shearHom_X_ne {i j : Fin m} (h : i ≠ j) (c : Fin m → k) :
    shearHom j c (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [shearHom, h]

theorem shearInvHom_X_self (j : Fin m) (c : Fin m → k) :
    shearInvHom j c (MvPolynomial.X j) =
      (c j)⁻¹ • (MvPolynomial.X j - ∑ l ∈ Finset.univ.erase j,
        c l • (MvPolynomial.X l : MvPolynomial (Fin m) k)) := by
  simp [shearInvHom]

theorem shearInvHom_X_ne {i j : Fin m} (h : i ≠ j) (c : Fin m → k) :
    shearInvHom j c (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [shearInvHom, h]

theorem shearHom_erase (j : Fin m) (c : Fin m → k) :
    shearHom j c (∑ l ∈ Finset.univ.erase j,
      c l • (MvPolynomial.X l : MvPolynomial (Fin m) k))
      = ∑ l ∈ Finset.univ.erase j, c l • (MvPolynomial.X l : MvPolynomial (Fin m) k) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_erase] at hi
  rw [map_smul, shearHom_X_ne hi.1]

theorem shearInvHom_erase (j : Fin m) (c : Fin m → k) :
    shearInvHom j c (∑ l ∈ Finset.univ.erase j,
      c l • (MvPolynomial.X l : MvPolynomial (Fin m) k))
      = ∑ l ∈ Finset.univ.erase j, c l • (MvPolynomial.X l : MvPolynomial (Fin m) k) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_erase] at hi
  rw [map_smul, shearInvHom_X_ne hi.1]

theorem shearHom_comp_shearInvHom (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0) :
    (shearHom j c).comp (shearInvHom j c) = AlgHom.id k (MvPolynomial (Fin m) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  by_cases h : i = j
  · subst h
    rw [shearInvHom_X_self, map_smul, map_sub, shearHom_X_self, shearHom_erase,
      linForm_eq_erase_add, add_sub_cancel_left, inv_smul_smul₀ hc]
  · rw [shearInvHom_X_ne h, shearHom_X_ne h]

theorem shearInvHom_comp_shearHom (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0) :
    (shearInvHom j c).comp (shearHom j c) = AlgHom.id k (MvPolynomial (Fin m) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  by_cases h : i = j
  · subst h
    rw [shearHom_X_self, linForm_eq_erase_add, map_add, map_smul, shearInvHom_erase,
      shearInvHom_X_self, smul_smul, mul_inv_cancel₀ hc, one_smul]
    abel
  · rw [shearHom_X_ne h, shearInvHom_X_ne h]

/-- The shear automorphism: it replaces the `j`-th coordinate function by `linForm c`, where
`c j ≠ 0`, and fixes all other variables. -/
noncomputable def shearEquiv (j : Fin m) (c : Fin m → k) (hc : c j ≠ 0) :
    MvPolynomial (Fin m) k ≃ₐ[k] MvPolynomial (Fin m) k :=
  AlgEquiv.ofAlgHom (shearHom j c) (shearInvHom j c)
    (shearHom_comp_shearInvHom j hc) (shearInvHom_comp_shearHom j hc)

theorem shearEquiv_X_self (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0) :
    shearEquiv j c hc (MvPolynomial.X j) = linForm c := by
  rw [shearEquiv, AlgEquiv.ofAlgHom_apply, shearHom_X_self]

theorem shearEquiv_X_ne {i j : Fin m} (h : i ≠ j) {c : Fin m → k} (hc : c j ≠ 0) :
    shearEquiv j c hc (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [shearEquiv, AlgEquiv.ofAlgHom_apply, shearHom_X_ne h]

theorem shearEquiv_symm_X_self (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0) :
    (shearEquiv j c hc).symm (MvPolynomial.X j) = shearInvHom j c (MvPolynomial.X j) := by
  rw [shearEquiv]
  rfl

theorem linForm_isHomogeneous (c : Fin m → k) : (linForm (k := k) c).IsHomogeneous 1 := by
  rw [linForm]
  exact MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i => c i • (MvPolynomial.X i : MvPolynomial (Fin m) k)) 1
    (fun i _ => isHomogeneous_one_smul (c i) (MvPolynomial.isHomogeneous_X k i))

theorem shearInvHom_X_self_mem (j : Fin m) (c : Fin m → k) :
    shearInvHom j c (MvPolynomial.X j) ∈ linSpace k m := by
  rw [shearInvHom_X_self]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (X_mem_linSpace j) (linFormErase_mem j c))

end Shear

/-! ## Part 3: killing variables, the kernel of `killCompl` -/

section KillCompl

variable {σ τ : Type*} [Fintype τ] [DecidableEq τ]

theorem killCompl_X_of_mem {e : σ → τ} (he : Function.Injective e) {i : τ}
    (hi : i ∈ Set.range e) :
    MvPolynomial.killCompl (R := k) he (MvPolynomial.X i) =
      MvPolynomial.X ((Equiv.ofInjective e he).symm ⟨i, hi⟩) := by
  classical
  unfold MvPolynomial.killCompl
  rw [MvPolynomial.aeval_X, dif_pos hi]

theorem killCompl_X_of_notMem {e : σ → τ} (he : Function.Injective e) {i : τ}
    (hi : i ∉ Set.range e) : MvPolynomial.killCompl (R := k) he (MvPolynomial.X i) = 0 := by
  classical
  unfold MvPolynomial.killCompl
  rw [MvPolynomial.aeval_X, dif_neg hi]

theorem killCompl_surjective {e : σ → τ} (he : Function.Injective e) :
    Function.Surjective (MvPolynomial.killCompl (R := k) he) :=
  fun p => ⟨MvPolynomial.rename e p, MvPolynomial.killCompl_rename_app he p⟩

/-- The kernel of `killCompl` is the ideal generated by the variables which are not in the range
of the index map. -/
theorem ker_killCompl {e : σ → τ} (he : Function.Injective e) :
    RingHom.ker (MvPolynomial.killCompl (R := k) he) =
      Ideal.span (MvPolynomial.X '' (Set.range e)ᶜ : Set (MvPolynomial τ k)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro d hd
    by_contra hcon
    push Not at hcon
    have hsupp : ↑d.support ⊆ Set.range e := by
      intro i hi
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hi) (hcon i hne)
    have hmap : Finsupp.mapDomain e (Finsupp.comapDomain e d fun a _ b _ hab => he hab) = d :=
      Finsupp.mapDomain_comapDomain e he d hsupp
    have h1 : (MvPolynomial.killCompl (R := k) he f).coeff
        (Finsupp.comapDomain e d fun a _ b _ hab => he hab) = 0 := by
      rw [hf]; simp
    rw [MvPolynomial.coeff_killCompl] at h1
    rw [hmap] at h1
    exact (Finsupp.mem_support_iff.mp hd) h1
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact killCompl_X_of_notMem he hi

end KillCompl

/-! ## Part 4: transport of primality and dimension along ring isomorphisms -/

section Transport

variable {A B : Type*} [CommRing A] [CommRing B]

/-- An isomorphism of rings induces an isomorphism of the quotients by corresponding ideals. -/
noncomputable def quotRingEquiv (e : A ≃+* B) (I : Ideal A) : A ⧸ I ≃+* B ⧸ Ideal.map e I :=
  Ideal.quotientEquiv I (Ideal.map e I) e rfl

/-- Images of prime ideals under ring isomorphisms are prime. -/
theorem IsPrime_map_ringEquiv {e : A ≃+* B} {I : Ideal A} (hI : I.IsPrime) :
    (Ideal.map e I).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  have hdom : IsDomain (A ⧸ I) := by
    haveI := hI
    infer_instance
  exact (quotRingEquiv e I).toMulEquiv.isDomain_iff.mp hdom

/-- The Krull dimension of the quotient only depends on the isomorphism class of the ideal. -/
theorem ringKrullDim_quot_ringEquiv {e : A ≃+* B} (I : Ideal A) :
    ringKrullDim (A ⧸ I) = ringKrullDim (B ⧸ Ideal.map e I) :=
  ringKrullDim_eq_of_ringEquiv (quotRingEquiv e I)

/-- Primality is invariant under an isomorphism of the quotient rings. -/
theorem isPrime_iff_of_quotient_ringEquiv {I : Ideal A} {J : Ideal B}
    (e : A ⧸ I ≃+* B ⧸ J) : I.IsPrime ↔ J.IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime (I := I),
    ← Ideal.Quotient.isDomain_iff_prime (I := J)]
  exact e.toMulEquiv.isDomain_iff

/-- Quotients by the inverse image of an ideal under a surjective algebra map. -/
noncomputable def quotientEquivOfSurjective_comap {A B : Type*} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] {φ : A →ₐ[k] B} (hφ : Function.Surjective φ) (J : Ideal B) (I : Ideal A)
    (hI : I = Ideal.comap φ J) : (A ⧸ I) ≃ₐ[k] (B ⧸ J) := by
  subst hI
  have hsurj : Function.Surjective ⇑((Ideal.Quotient.mkₐ k J).comp φ) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨a, rfl⟩
  have hker : RingHom.ker ((Ideal.Quotient.mkₐ k J).comp φ) = Ideal.comap φ J := by
    ext x
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker]
  exact Ideal.quotientKerAlgEquivOfSurjective hsurj

end Transport

/-! ## Part 5: substitution of a single variable, and elimination of a linear equation -/

section Elim

variable {m : ℕ}

/-- Substitution of an arbitrary polynomial for the `j`-th variable. -/
noncomputable def substHom (j : Fin m) (g : MvPolynomial (Fin m) k) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.aeval (fun i => if i = j then g else MvPolynomial.X i)

theorem substHom_X_self (j : Fin m) (g : MvPolynomial (Fin m) k) :
    substHom j g (MvPolynomial.X j) = g := by
  simp [substHom]

theorem substHom_X_ne {i j : Fin m} (h : i ≠ j) (g : MvPolynomial (Fin m) k) :
    substHom j g (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [substHom, h]

/-- The variables of `Fin m` other than `j`, embedded in `Fin m`. -/
noncomputable def otherRename (j : Fin m) :
    MvPolynomial {i : Fin m // i ≠ j} k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.rename (R := k) (fun i : {i : Fin m // i ≠ j} => (i : Fin m))

/-- Deleting the `j`-th variable. -/
noncomputable def otherKill (j : Fin m) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial {i : Fin m // i ≠ j} k :=
  MvPolynomial.killCompl (R := k) (σ := {i : Fin m // i ≠ j}) (τ := Fin m)
    (f := fun i : {i : Fin m // i ≠ j} => (i : Fin m)) Subtype.val_injective

theorem range_otherRename (j : Fin m) :
    Set.range (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) = {j}ᶜ := by
  ext i
  simp [eq_comm]

theorem otherKill_otherRename (j : Fin m) (p : MvPolynomial {i : Fin m // i ≠ j} k) :
    otherKill j (otherRename j p) = p :=
  MvPolynomial.killCompl_rename_app (R := k) (σ := {i : Fin m // i ≠ j})
    (f := fun i : {i : Fin m // i ≠ j} => (i : Fin m)) Subtype.val_injective p

theorem otherRename_X (j : Fin m) (i : {i : Fin m // i ≠ j}) :
    otherRename j (MvPolynomial.X i : MvPolynomial {i : Fin m // i ≠ j} k) =
      (MvPolynomial.X (i : Fin m) : MvPolynomial (Fin m) k) := by
  simp [otherRename]

theorem otherKill_X_self (j : Fin m) :
    otherKill j (MvPolynomial.X j : MvPolynomial (Fin m) k) = 0 := by
  classical
  unfold otherKill MvPolynomial.killCompl
  rw [MvPolynomial.aeval_X]
  exact dif_neg (by
    rintro ⟨⟨a, ha⟩, h⟩
    exact ha h)

theorem otherKill_eq_span (j : Fin m) :
    RingHom.ker (otherKill (k := k) j) = Ideal.span {MvPolynomial.X j} := by
  rw [otherKill, ker_killCompl]
  have hcompl : (Set.range (fun i : {i : Fin m // i ≠ j} => (i : Fin m)))ᶜ = {j} := by
    ext i
    simp [eq_comm]
  rw [hcompl, Set.image_singleton]

/-- Substitution of a polynomial in the other variables fixes those variables. -/
theorem substHom_otherRename (j : Fin m) (G : MvPolynomial (Fin m) k)
    (p : MvPolynomial {i : Fin m // i ≠ j} k) :
    substHom j G (otherRename j p) = otherRename j p := by
  have h : (substHom j G).comp (otherRename (k := k) j) = (otherRename (k := k) j).comp
      (AlgHom.id k (MvPolynomial {i : Fin m // i ≠ j} k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, otherRename_X]
    exact substHom_X_ne i.2 G
  exact AlgHom.congr_fun h p

/-- Translation of the `j`-th variable by a polynomial in the other variables. -/
noncomputable def transEquiv (j : Fin m) (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    MvPolynomial (Fin m) k ≃ₐ[k] MvPolynomial (Fin m) k :=
  AlgEquiv.ofAlgHom (substHom j (MvPolynomial.X j + otherRename j g₀))
    (substHom j (MvPolynomial.X j - otherRename j g₀)) (by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      by_cases h : i = j
      · subst h
        rw [substHom_X_self, map_sub, substHom_X_self, substHom_otherRename]
        abel
      · rw [substHom_X_ne h, substHom_X_ne h]) (by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      by_cases h : i = j
      · subst h
        rw [substHom_X_self, map_add, substHom_X_self, substHom_otherRename]
        abel
      · rw [substHom_X_ne h, substHom_X_ne h])

theorem transEquiv_X_self (j : Fin m) (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    transEquiv j g₀ (MvPolynomial.X j) = MvPolynomial.X j + otherRename j g₀ := by
  rw [transEquiv, AlgEquiv.ofAlgHom_apply, substHom_X_self]

theorem transEquiv_X_ne {i j : Fin m} (h : i ≠ j)
    (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    transEquiv j g₀ (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [transEquiv, AlgEquiv.ofAlgHom_apply, substHom_X_ne h]

theorem transEquiv_apply_sub (j : Fin m) (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    transEquiv j g₀ (MvPolynomial.X j - otherRename j g₀) = MvPolynomial.X j := by
  rw [transEquiv, AlgEquiv.ofAlgHom_apply, map_sub, substHom_X_self, substHom_otherRename,
    add_sub_cancel_right]

theorem transEquiv_symm_X_self (j : Fin m) (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    (transEquiv j g₀).symm (MvPolynomial.X j) = MvPolynomial.X j - otherRename j g₀ := by
  conv_lhs => rw [← transEquiv_apply_sub j g₀]
  rw [AlgEquiv.symm_apply_apply]

/-- The preimage of the ideal generated by a single element under a ring equivalence. -/
theorem comap_span_singleton_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (a : B) : Ideal.comap e (Ideal.span {a}) = Ideal.span {e.symm a} := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    rw [← map_mul, ← hc, RingEquiv.symm_apply_apply]
  · rintro ⟨d, rfl⟩
    exact ⟨e d, by rw [map_mul, RingEquiv.apply_symm_apply]⟩

/-- The preimage of the ideal generated by a single element under an algebra equivalence. -/
theorem comap_span_singleton_algEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) (a : B) :
    Ideal.comap e (Ideal.span {a}) = Ideal.span {e.symm a} := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    rw [← map_mul, ← hc, AlgEquiv.symm_apply_apply]
  · rintro ⟨d, rfl⟩
    exact ⟨e d, by rw [map_mul, AlgEquiv.apply_symm_apply]⟩

/-- **Elimination of a linear equation.** The kernel of the substitution `x_j ↦ G`, where `G` is a
polynomial in the other variables, is the ideal generated by `x_j - G`. -/
theorem ker_substHom_otherRename (j : Fin m) (g₀ : MvPolynomial {i : Fin m // i ≠ j} k) :
    RingHom.ker (substHom (k := k) j (otherRename j g₀)) =
      Ideal.span {MvPolynomial.X j - otherRename j g₀} := by
  refine le_antisymm ?_ ?_
  · intro h hh
    rw [RingHom.mem_ker] at hh
    have htrans : ∀ y : MvPolynomial (Fin m) k,
        otherKill j (transEquiv j g₀ y) = otherKill j (substHom j (otherRename j g₀) y) := by
      intro y
      have h1 : (otherKill j).comp (transEquiv (k := k) j g₀).toAlgHom =
          (otherKill j).comp (substHom j (otherRename j g₀)) := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [AlgHom.comp_apply, AlgHom.comp_apply]
        by_cases h : i = j
        · subst h
          have s1 : ((transEquiv (k := k) i g₀).toAlgHom :
              MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k) (MvPolynomial.X i) =
              MvPolynomial.X i + otherRename i g₀ := transEquiv_X_self i g₀
          rw [s1, substHom_X_self, map_add, otherKill_X_self, otherKill_otherRename, zero_add]
        · have s1 : ((transEquiv (k := k) j g₀).toAlgHom :
              MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k) (MvPolynomial.X i) =
              MvPolynomial.X i := transEquiv_X_ne h g₀
          rw [s1, substHom_X_ne h]
      exact AlgHom.congr_fun h1 y
    have hmem : transEquiv j g₀ h ∈ RingHom.ker (otherKill (k := k) j) := by
      rw [RingHom.mem_ker]
      rw [htrans h, hh]
      simp
    rw [otherKill_eq_span] at hmem
    have h2 : h ∈ Ideal.comap (transEquiv (k := k) j g₀) (Ideal.span {MvPolynomial.X j}) :=
      hmem
    rw [comap_span_singleton_algEquiv] at h2
    simp only [transEquiv_symm_X_self] at h2
    exact h2
  · rw [Ideal.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    show substHom j (otherRename j g₀) (MvPolynomial.X j - otherRename j g₀) = 0
    rw [map_sub, substHom_X_self, substHom_otherRename, sub_self]

end Elim

/-! ## Part 6: linearity of the basic operations -/

section Linearity

variable {m : ℕ}

theorem otherKill_X_ne {j i : Fin m} (h : i ≠ j) :
    otherKill j (MvPolynomial.X i : MvPolynomial (Fin m) k) =
      (MvPolynomial.X ⟨i, h⟩ : MvPolynomial {i : Fin m // i ≠ j} k) := by
  classical
  unfold otherKill MvPolynomial.killCompl
  rw [MvPolynomial.aeval_X]
  rw [dif_pos (show i ∈ Set.range (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) from
    ⟨⟨i, h⟩, rfl⟩)]
  apply congrArg MvPolynomial.X
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  rw [Equiv.ofInjective_apply]

theorem shearHom_mem_linSpace (j : Fin m) (c : Fin m → k) {f : MvPolynomial (Fin m) k}
    (hf : f ∈ linSpace k m) : shearHom j c f ∈ linSpace k m := by
  rw [eq_sum_coeff_smul_X (linSpace_isHomogeneous hf)]
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  by_cases h : i = j
  · subst h
    rw [shearHom_X_self]
    exact Submodule.smul_mem _ _ (linForm_mem_linSpace c)
  · rw [shearHom_X_ne h]
    exact Submodule.smul_mem _ _ (X_mem_linSpace i)

theorem shearInvHom_mem_linSpace (j : Fin m) (c : Fin m → k) {f : MvPolynomial (Fin m) k}
    (hf : f ∈ linSpace k m) : shearInvHom j c f ∈ linSpace k m := by
  rw [eq_sum_coeff_smul_X (linSpace_isHomogeneous hf)]
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  by_cases h : i = j
  · rw [h]
    exact Submodule.smul_mem _ _ (shearInvHom_X_self_mem j c)
  · rw [shearInvHom_X_ne h]
    exact Submodule.smul_mem _ _ (X_mem_linSpace i)

theorem shearEquiv_mem_linSpace (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0)
    {f : MvPolynomial (Fin m) k} (hf : f ∈ linSpace k m) :
    shearEquiv j c hc f ∈ linSpace k m := by
  rw [shearEquiv, AlgEquiv.ofAlgHom_apply]
  exact shearHom_mem_linSpace j c hf

theorem shearEquiv_symm_mem_linSpace (j : Fin m) {c : Fin m → k} (hc : c j ≠ 0)
    {f : MvPolynomial (Fin m) k} (hf : f ∈ linSpace k m) :
    (shearEquiv j c hc).symm f ∈ linSpace k m := by
  have h := shearInvHom_mem_linSpace (k := k) j c hf
  have h2 : (shearEquiv j c hc).symm f = shearInvHom j c f := by
    have : ((shearEquiv j c hc).symm : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k) =
        shearInvHom j c := rfl
    exact AlgHom.congr_fun this f
  rw [h2]
  exact h

end Linearity

/-! ## Part 8: the statement of Hartshorne I.2.11 -/

/-- A linear form in `m` variables: a homogeneous polynomial of degree one. -/
def LinearForm (k : Type u) [Field k] (m : ℕ) : Type u :=
  {f : MvPolynomial (Fin m) k // f.IsHomogeneous 1}

/-- An ideal is generated by linear forms. -/
def LinGenerated {k : Type u} [Field k] {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k)) : Prop :=
  ∃ W : Submodule k (MvPolynomial (Fin m) k), W ≤ linSpace k m ∧ Ideal.span (W : Set _) = I

/-- A linear variety in `P^n`: an intersection of hyperplanes. -/
def IsLinearVariety {k : Type u} [Field k] {n : ℕ} (Y : Set (Proj k n)) : Prop :=
  ∃ W : Submodule k (MvPolynomial (Fin (n + 1)) k), W ≤ linSpace k (n + 1) ∧
    Y = {x | ∀ f ∈ W, Proj.IsZeroAt f x}

/-- **Hartshorne, Algebraic Geometry (1977), Exercise I.2.11**, "Linear varieties in `P^n`",
with `k` algebraically closed, `Y, Z ⊆ P^n` projective varieties (irreducible closed subsets).

(a) `I(Y)` is generated by linear polynomials if and only if `Y` is an intersection of
    hyperplanes.
(b) If `Y` is a linear variety of dimension `r`, then `I(Y)` is minimally generated by `n - r`
    linear polynomials.
(c) If `Y, Z` are linear varieties of dimensions `r, s` with `r + s ≥ n`, then `Y ∩ Z ≠ ∅`;
    and if `Y ∩ Z ≠ ∅`, then `Y ∩ Z` is a linear variety of dimension `≥ r + s - n`.

The predicate `LinearForm` records linear polynomials, `LinGenerated` records generation of an
ideal by linear polynomials (equivalently by a linear subspace of the space of linear forms,
which is `linSpace`), `IsLinearVariety` records being an intersection of hyperplanes, `projDim`
is the chain dimension of a subset of `P^n` (Hartshorne's `dim`), and `Proj.vanishingIdeal` is
the homogeneous ideal `I(Y)`. -/
def hartshorne_exercise_I_2_11_statement {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) : Prop :=
  ∀ (Y Z : Set (Proj k n)), IsClosed Y → IsIrreducible Y → IsClosed Z → IsIrreducible Z →
    (LinGenerated (Proj.vanishingIdeal Y) ↔ IsLinearVariety Y) ∧
    (∀ r : ℕ, LinGenerated (Proj.vanishingIdeal Y) → projDim Y = (r : ℕ∞) →
      (∃ S : Finset (LinearForm k (n + 1)), S.card = n - r ∧
        Ideal.span (Subtype.val '' (S : Set (LinearForm k (n + 1)))) = Proj.vanishingIdeal Y) ∧
      (∀ S : Finset (LinearForm k (n + 1)),
        Ideal.span (Subtype.val '' (S : Set (LinearForm k (n + 1)))) = Proj.vanishingIdeal Y →
          n - r ≤ S.card)) ∧
    (∀ r s : ℕ, LinGenerated (Proj.vanishingIdeal Y) → LinGenerated (Proj.vanishingIdeal Z) →
      projDim Y = (r : ℕ∞) → projDim Z = (s : ℕ∞) →
        (n ≤ r + s → (Y ∩ Z).Nonempty) ∧
        ((Y ∩ Z).Nonempty →
          LinGenerated (Proj.vanishingIdeal (Y ∩ Z)) ∧ r + s - n ≤ projDim (Y ∩ Z)))
end Hartshorne77.Ex_I_2_11

/-! ## Part 9: the linearly-independent-forms theorem (LIN) -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u
variable {k : Type u} [Field k]

section LinFormLaws

variable {m : ℕ}

theorem linForm_add' (a b : Fin m → k) :
    linForm (k := k) (a + b) = linForm a + linForm b := by
  simp only [linForm, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem linForm_smul' (c : k) (a : Fin m → k) :
    linForm (k := k) (c • a) = c • linForm (k := k) a := by
  simp only [linForm, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem linForm_zero' : linForm (k := k) (m := m) 0 = 0 := by
  simp [linForm]

/-- `linForm` as a `k`-linear map. -/
noncomputable def linFormLM : (Fin m → k) →ₗ[k] MvPolynomial (Fin m) k where
  toFun := linForm
  map_add' := linForm_add'
  map_smul' := linForm_smul'

theorem linForm_sum {ι : Type*} (t : Finset ι) (a : ι → Fin m → k) :
    linForm (k := k) (∑ i ∈ t, a i) = ∑ i ∈ t, linForm (a i) :=
  map_sum (linFormLM (k := k) (m := m)) a t

theorem linForm_single (i : Fin m) :
    linForm (k := k) (Pi.single i (1 : k)) = (MvPolynomial.X i : MvPolynomial (Fin m) k) := by
  rw [linForm, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem linForm_coeffVec (f : linSpace k m) :
    linForm (k := k) (coeffVec f) = (f : MvPolynomial (Fin m) k) := by
  rw [eq_sum_coeff_smul_X (linSpace_isHomogeneous f.2)]
  rfl

theorem linForm_eq_zero_iff {c : Fin m → k} : linForm (k := k) c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext i
    have h' := congrArg (fun p : MvPolynomial (Fin m) k => p.coeff (Finsupp.single i 1)) h
    simpa [coeff_linForm] using h'
  · rintro rfl
    exact linForm_zero'

theorem sum_single_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → k) :
    (∑ i, c i • (Pi.single i (1 : k) : ι → k)) = c := by
  rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end LinFormLaws

section CoeffSub

variable {m : ℕ}

/-- The coefficient subspace of a space of linear forms, as a subspace of `k^m`. -/
noncomputable def coeffSub (W : Submodule k (MvPolynomial (Fin m) k)) (hW : W ≤ linSpace k m) :
    Submodule k (Fin m → k) :=
  LinearMap.range ((coeffVec (k := k) (m := m)).comp (Submodule.inclusion hW))

theorem coeffSub_inj (W : Submodule k (MvPolynomial (Fin m) k)) (hW : W ≤ linSpace k m) :
    Function.Injective ⇑((coeffVec (k := k) (m := m)).comp (Submodule.inclusion hW)) := by
  intro x y hxy
  have h2 : ((Submodule.inclusion hW) x : MvPolynomial (Fin m) k) =
      ((Submodule.inclusion hW) y : MvPolynomial (Fin m) k) :=
    congrArg Subtype.val (coeffVec_injective hxy)
  exact Subtype.ext (by simpa using h2)

theorem coeffSub_finrank (W : Submodule k (MvPolynomial (Fin m) k)) (hW : W ≤ linSpace k m) :
    Module.finrank k (coeffSub W hW) = Module.finrank k W := by
  rw [coeffSub]
  exact LinearMap.finrank_range_of_inj (coeffSub_inj W hW)

theorem linForm_mem_of_mem_coeffSub (W : Submodule k (MvPolynomial (Fin m) k))
    (hW : W ≤ linSpace k m) {v : Fin m → k} (hv : v ∈ coeffSub W hW) :
    linForm (k := k) v ∈ W := by
  rw [coeffSub, LinearMap.mem_range] at hv
  obtain ⟨w, hw⟩ := hv
  rw [← hw, LinearMap.comp_apply, linForm_coeffVec]
  exact w.2

theorem coeffSub_mem_of_mem (W : Submodule k (MvPolynomial (Fin m) k)) (hW : W ≤ linSpace k m)
    {w : MvPolynomial (Fin m) k} (hw : w ∈ W) :
    coeffVec (k := k) ⟨w, hW hw⟩ ∈ coeffSub W hW :=
  ⟨⟨w, hw⟩, rfl⟩

end CoeffSub

section Projection

/-- A subspace of `k^m` is the kernel of a linear map `k^m → k^(m - dim)`. -/
theorem exists_proj_ker {m : ℕ} (V : Submodule k (Fin m → k)) :
    ∃ P : (Fin m → k) →ₗ[k] (Fin (m - Module.finrank k V) → k),
      LinearMap.ker P = V ∧ LinearMap.range P = ⊤ := by
  have hfr : Module.finrank k (Fin m → k) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hq : Module.finrank k ((Fin m → k) ⧸ V) = m - Module.finrank k V := by
    have h := Submodule.finrank_quotient_add_finrank (R := k) (M := Fin m → k) V
    omega
  have hfr' : Module.finrank k (Fin (m - Module.finrank k V) → k)
      = m - Module.finrank k V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : ((Fin m → k) ⧸ V) ≃ₗ[k] (Fin (m - Module.finrank k V) → k) :=
    LinearEquiv.ofFinrankEq ((Fin m → k) ⧸ V) (Fin (m - Module.finrank k V) → k)
      (by rw [hq, hfr'])
  refine ⟨e.toLinearMap.comp V.mkQ, ?_, ?_⟩
  · rw [LinearMap.ker_comp,
      show LinearMap.ker (e.toLinearMap) = ⊥ from LinearMap.ker_eq_bot.mpr e.injective,
      Submodule.comap_bot, Submodule.ker_mkQ]
  · exact LinearMap.range_eq_top.mpr (e.surjective.comp (Submodule.mkQ_surjective V))

/-- Every subspace of `k^m` is the kernel of a projection onto a complement, with a linear
section. -/
theorem exists_proj_section {m : ℕ} (V : Submodule k (Fin m → k)) :
    ∃ (P : (Fin m → k) →ₗ[k] (Fin (m - Module.finrank k V) → k))
      (s : (Fin (m - Module.finrank k V) → k) →ₗ[k] (Fin m → k)),
      LinearMap.ker P = V ∧ P ∘ₗ s = LinearMap.id := by
  obtain ⟨P, hker, hsurj⟩ := exists_proj_ker (k := k) V
  obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective hsurj
  exact ⟨P, s, hker, hs⟩

end Projection

end Hartshorne77.Ex_I_2_11


/-! ## Part 10: the coordinate-change maps and the main theorem -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

variable {k : Type u} [Field k]

section Hom

variable {m r : ℕ}

/-- An algebra map out of a polynomial ring is determined on linear forms by its values on the
variables, whenever those values are given by one linear map. -/
theorem algHom_linForm {B : Type*} [CommSemiring B] [Algebra k B]
    (f : MvPolynomial (Fin m) k →ₐ[k] B) (g : (Fin m → k) →ₗ[k] B)
    (h : ∀ i : Fin m, f (MvPolynomial.X i) = g (Pi.single i (1 : k))) (c : Fin m → k) :
    f (linForm c) = g c := by
  conv_lhs => rw [linForm]
  rw [map_sum]
  conv_rhs => rw [← sum_single_smul (k := k) c]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h i]

/-- The coordinate change `x_i ↦ ∑_l (P e_i)_l y_l` attached to a linear map `P` on coefficient
vectors. -/
noncomputable def psiHom (P : (Fin m → k) →ₗ[k] (Fin r → k)) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin r) k :=
  MvPolynomial.aeval fun i => linForm (P (Pi.single i (1 : k)))

theorem psiHom_X (P : (Fin m → k) →ₗ[k] (Fin r → k)) (i : Fin m) :
    psiHom P (MvPolynomial.X i) = linForm (P (Pi.single i (1 : k))) :=
  MvPolynomial.aeval_X _ i

theorem psiHom_linForm (P : (Fin m → k) →ₗ[k] (Fin r → k)) (c : Fin m → k) :
    psiHom P (linForm c) = linForm (P c) :=
  algHom_linForm (psiHom P) ((linFormLM (k := k) (m := r)).comp P)
    (fun i => by rw [psiHom_X]; rfl) c

/-- The map on coordinate rings induced by a linear section `s`: `y_l ↦ [linForm (s e_l)]`. -/
noncomputable def phiHom (J : Ideal (MvPolynomial (Fin m) k))
    (s : (Fin r → k) →ₗ[k] (Fin m → k)) :
    MvPolynomial (Fin r) k →ₐ[k] (MvPolynomial (Fin m) k ⧸ J) :=
  MvPolynomial.aeval fun l => Ideal.Quotient.mk J (linForm (s (Pi.single l (1 : k))))

theorem phiHom_X (J : Ideal (MvPolynomial (Fin m) k)) (s : (Fin r → k) →ₗ[k] (Fin m → k))
    (l : Fin r) :
    phiHom J s (MvPolynomial.X l) =
      Ideal.Quotient.mk J (linForm (s (Pi.single l (1 : k)))) :=
  MvPolynomial.aeval_X _ l

theorem phiHom_linForm (J : Ideal (MvPolynomial (Fin m) k))
    (s : (Fin r → k) →ₗ[k] (Fin m → k)) (c : Fin r → k) :
    phiHom J s (linForm c) = Ideal.Quotient.mk J (linForm (s c)) :=
  algHom_linForm (phiHom J s)
    (((Ideal.Quotient.mkₐ k J).toLinearMap).comp ((linFormLM (k := k) (m := m)).comp s))
    (fun l => by rw [phiHom_X]; rfl) c

/-- The algebra map on quotient rings induced by `psiHom`, when the ideal is killed by it. -/
noncomputable def psiBar (P : (Fin m → k) →ₗ[k] (Fin r → k))
    (J : Ideal (MvPolynomial (Fin m) k)) (hJ : ∀ a ∈ J, psiHom P a = 0) :
    (MvPolynomial (Fin m) k ⧸ J) →ₐ[k] MvPolynomial (Fin r) k :=
  Ideal.Quotient.liftₐ J (psiHom P) hJ

@[simp]
theorem psiBar_mk (P : (Fin m → k) →ₗ[k] (Fin r → k))
    (J : Ideal (MvPolynomial (Fin m) k)) (hJ : ∀ a ∈ J, psiHom P a = 0)
    (p : MvPolynomial (Fin m) k) :
    psiBar P J hJ (Ideal.Quotient.mk J p) = psiHom P p := by
  have h := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp J (psiHom P) hJ) p
  simpa [psiBar, Ideal.Quotient.mkₐ_eq_mk] using h

end Hom

section LINMain

variable {m : ℕ}

theorem linAux {r : ℕ} (W : Submodule k (MvPolynomial (Fin m) k)) (hW : W ≤ linSpace k m)
    (P : (Fin m → k) →ₗ[k] (Fin r → k)) (s : (Fin r → k) →ₗ[k] (Fin m → k))
    (hker : LinearMap.ker P = coeffSub W hW) (hs : P ∘ₗ s = LinearMap.id) :
    (Ideal.span (W : Set (MvPolynomial (Fin m) k))).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin m) k ⧸ Ideal.span (W : Set (MvPolynomial (Fin m) k))) =
        (r : ℕ∞) := by
  classical
  set J := Ideal.span (W : Set (MvPolynomial (Fin m) k)) with hJ
  have hPs : ∀ x, P (s x) = x := fun x => LinearMap.congr_fun hs x
  have hVmem : ∀ i : Fin m, s (P (Pi.single i (1 : k))) - Pi.single i (1 : k) ∈ coeffSub W hW := by
    intro i
    rw [← hker, LinearMap.mem_ker, map_sub, hPs, sub_self]
  have hWker : ∀ f ∈ W, psiHom P f = 0 := by
    intro f hf
    have hfl : f = linForm (coeffVec (k := k) ⟨f, hW hf⟩) := by rw [linForm_coeffVec]
    rw [hfl, psiHom_linForm]
    have h0 : P (coeffVec (k := k) ⟨f, hW hf⟩) = 0 := by
      have hmem : coeffVec (k := k) ⟨f, hW hf⟩ ∈ LinearMap.ker P := by
        rw [hker]
        exact coeffSub_mem_of_mem W hW hf
      exact LinearMap.mem_ker.mp hmem
    rw [h0, linForm_zero']
  have hJker : ∀ a ∈ J, psiHom P a = 0 := by
    intro a ha
    rw [hJ] at ha
    have hle : Ideal.span (W : Set (MvPolynomial (Fin m) k)) ≤
        RingHom.ker (psiHom P : MvPolynomial (Fin m) k →+* MvPolynomial (Fin r) k) :=
      Ideal.span_le.mpr (fun f hf => RingHom.mem_ker.mp (hWker f hf))
    exact RingHom.mem_ker.mpr (hle ha)
  have hcomp₂ : (psiBar P J hJker).comp (phiHom J s) = AlgHom.id k (MvPolynomial (Fin r) k) := by
    apply MvPolynomial.algHom_ext
    intro l
    show psiBar P J hJker (phiHom J s (MvPolynomial.X l)) = MvPolynomial.X l
    rw [phiHom_X, psiBar_mk, psiHom_linForm, hPs, linForm_single]
  have hcomp₁ : (phiHom J s).comp (psiBar P J hJker) =
      AlgHom.id k (MvPolynomial (Fin m) k ⧸ J) := by
    have hgen : ((phiHom J s).comp (psiBar P J hJker)).comp (Ideal.Quotient.mkₐ k J) =
        Ideal.Quotient.mkₐ k J := by
      apply MvPolynomial.algHom_ext
      intro i
      show phiHom J s (psiBar P J hJker (Ideal.Quotient.mk J (MvPolynomial.X i))) =
        Ideal.Quotient.mk J (MvPolynomial.X i)
      rw [psiBar_mk, psiHom_X, phiHom_linForm]
      have hw : linForm (s (P (Pi.single i (1 : k))) - Pi.single i (1 : k)) ∈ W :=
        linForm_mem_of_mem_coeffSub W hW (hVmem i)
      have hsub : linForm (s (P (Pi.single i (1 : k)))) =
          linForm (Pi.single i (1 : k)) +
            linForm (s (P (Pi.single i (1 : k))) - Pi.single i (1 : k)) := by
        rw [← linForm_add']
        congr 1
        abel
      rw [hsub, linForm_single, map_add]
      have hzero : Ideal.Quotient.mk J
          (linForm (s (P (Pi.single i (1 : k))) - Pi.single i (1 : k))) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span hw
      rw [hzero, add_zero]
    ext z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact AlgHom.congr_fun hgen p
  have e : (MvPolynomial (Fin m) k ⧸ J) ≃ₐ[k] MvPolynomial (Fin r) k :=
    AlgEquiv.ofAlgHom (psiBar P J hJker) (phiHom J s) hcomp₂ hcomp₁
  refine ⟨?_, ?_⟩
  · haveI : IsDomain (MvPolynomial (Fin r) k) := inferInstance
    haveI : IsDomain (MvPolynomial (Fin m) k ⧸ J) :=
      (MulEquiv.isDomain_iff e.toRingEquiv.toMulEquiv).mpr inferInstance
    exact (Ideal.Quotient.isDomain_iff_prime (I := J)).mp inferInstance
  · rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp

/-- **LIN**, subspace form: the ideal generated by a space of linear forms is prime, and the
coordinate ring has Krull dimension `m - dim W`. -/
theorem linSpaceIdeal_isPrime_and_dim (W : Submodule k (MvPolynomial (Fin m) k))
    (hW : W ≤ linSpace k m) :
    (Ideal.span (W : Set (MvPolynomial (Fin m) k))).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin m) k ⧸ Ideal.span (W : Set (MvPolynomial (Fin m) k))) =
        ((m - Module.finrank k W : ℕ) : ℕ∞) := by
  obtain ⟨P, s, hker, hs⟩ := exists_proj_section (k := k) (coeffSub W hW)
  have h := linAux W hW P s hker hs
  rw [coeffSub_finrank W hW] at h
  exact h

end LINMain

end Hartshorne77.Ex_I_2_11


/-! ## Part 11: zero loci of spaces of linear forms -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u
variable {k : Type u} [Field k]

section LinearZeroLocus

variable {n : ℕ}

/-- The projective zero set of a space of linear forms. -/
def linZeroLocus (W : Submodule k (MvPolynomial (Fin (n + 1)) k)) : Set (Proj k n) :=
  {x | ∀ f ∈ W, Proj.IsZeroAt f x}

theorem mem_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)} {x : Proj k n} :
    x ∈ linZeroLocus (k := k) W ↔ ∀ f ∈ W, Proj.IsZeroAt f x := Iff.rfl

theorem isLinearVariety_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) : IsLinearVariety (linZeroLocus W) :=
  ⟨W, hW, rfl⟩

theorem isProjClosed_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) : Proj.IsProjClosed (linZeroLocus W) := by
  refine ⟨{g : Proj.HomogPoly k n | g.1 ∈ W}, ?_⟩
  ext x
  exact ⟨fun h f hf => h ⟨f, 1, linSpace_isHomogeneous (hW hf)⟩ hf,
    fun h g hg => h g.1 hg⟩

theorem isClosed_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) : IsClosed (linZeroLocus W) :=
  Proj.isClosed_of_isProjClosed (isProjClosed_linZeroLocus hW)

theorem linZeroLocus_anti_mono {W W' : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (h : W ≤ W') : linZeroLocus W' ⊆ linZeroLocus W :=
  fun _ hx f hf => hx f (h hf)

theorem linZeroLocus_sup {W U : Submodule k (MvPolynomial (Fin (n + 1)) k)} :
    linZeroLocus (W ⊔ U) = linZeroLocus W ∩ linZeroLocus U := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact ⟨linZeroLocus_anti_mono le_sup_left hx, linZeroLocus_anti_mono le_sup_right hx⟩
  · rintro x ⟨h1, h2⟩ f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    have hha : Proj.IsZeroAt a x := h1 a ha
    have hhb : Proj.IsZeroAt b x := h2 b hb
    show MvPolynomial.eval x.rep (a + b) = 0
    rw [map_add, hha, hhb, add_zero]

theorem zero_mem_cone_linZeroLocus (W : Submodule k (MvPolynomial (Fin (n + 1)) k)) :
    (0 : Fin (n + 1) → k) ∈ Proj.cone (linZeroLocus (k := k) (n := n) W) :=
  Or.inl rfl

/-- The cone over the projective zero set of a space of linear forms is the affine zero locus of
the ideal generated by that space. -/
theorem cone_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) :
    Proj.cone (linZeroLocus W) =
      MvPolynomial.zeroLocus k (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))) := by
  ext v
  constructor
  · rintro (rfl | ⟨hvne, hmem⟩)
    · rw [MvPolynomial.mem_zeroLocus_iff]
      intro f hf
      rw [MvPolynomial.aeval_eq_eval]
      refine Ideal.span_le.mpr (fun w hw => RingHom.mem_ker.mpr ?_) hf
      exact Proj.eval_zero_of_isHomogeneous_pos Nat.zero_lt_one
        (linSpace_isHomogeneous (hW hw))
    · rw [MvPolynomial.mem_zeroLocus_iff]
      intro f hf
      rw [MvPolynomial.aeval_eq_eval]
      refine Ideal.span_le.mpr (fun w hw => RingHom.mem_ker.mpr ?_) hf
      exact (Proj.isZeroAt_mk_iff (linSpace_isHomogeneous (hW hw)) hvne).1 (hmem w hw)
  · intro hv
    rcases eq_or_ne v 0 with rfl | hvne
    · exact Or.inl rfl
    · refine Or.inr ⟨hvne, ?_⟩
      intro g hg
      have hg' : MvPolynomial.eval v g = 0 := by
        rw [← MvPolynomial.aeval_eq_eval]
        exact (MvPolynomial.mem_zeroLocus_iff.mp hv) g (Ideal.subset_span hg)
      exact (Proj.isZeroAt_mk_iff (linSpace_isHomogeneous (hW hg)) hvne).2 hg'

/-- The vanishing ideal of the zero set of a space of linear forms is the ideal generated by that
space (Nullstellensatz + primality). -/
theorem vanishingIdeal_linZeroLocus [IsAlgClosed k]
    {W : Submodule k (MvPolynomial (Fin (n + 1)) k)} (hW : W ≤ linSpace k (n + 1))
    (hne : (linZeroLocus W).Nonempty) :
    Proj.vanishingIdeal (linZeroLocus W) =
      Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)) := by
  have hprime : (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))).IsPrime :=
    (linSpaceIdeal_isPrime_and_dim W hW).1
  refine le_antisymm ?_ ?_
  · rw [Proj.vanishingIdeal, Ideal.span_le]
    rintro g ⟨d, hd, hvan⟩
    have hmem : g ∈ MvPolynomial.vanishingIdeal k
        (MvPolynomial.zeroLocus k (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)))) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro v hv
      have hvc : v ∈ Proj.cone (linZeroLocus W) := by
        rw [cone_linZeroLocus hW]
        exact hv
      rw [MvPolynomial.aeval_eq_eval]
      rcases hvc with h0 | ⟨hvne, hvY⟩
      · rw [h0]
        exact Proj.eval_zero_of_mem_gens hne hd hvan
      · exact (Proj.isZeroAt_mk_iff hd hvne).1 (hvan _ hvY)
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
    rwa [Ideal.IsRadical.radical hprime.isRadical] at hmem
  · rw [Ideal.span_le]
    intro f hf
    exact Proj.subset_vanishingIdeal (linSpace_isHomogeneous (hW hf))
      (fun x hx => hx f hf)

/-- A closed set whose vanishing ideal is generated by a space of linear forms is the zero set of
that space. -/
theorem linZeroLocus_of_vanishingIdeal_eq {Y : Set (Proj k n)} (hYc : IsClosed Y)
    {W : Submodule k (MvPolynomial (Fin (n + 1)) k)} (hW : W ≤ linSpace k (n + 1))
    (hI : Proj.vanishingIdeal Y = Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))) :
    Y = linZeroLocus W := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx f hf
    have hmem : f ∈ Proj.vanishOnIdeal Y :=
      Proj.vanishingIdeal_le_vanishOnIdeal Y (by rw [hI]; exact Ideal.subset_span hf)
    exact (Proj.mem_vanishOnIdeal_iff).mp hmem x.rep x.rep_nonzero (by simpa using hx)
  · intro x hx
    obtain ⟨S, hS⟩ := (Proj.isClosed_iff Y).mp hYc
    have hxI : ∀ f ∈ Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)),
        MvPolynomial.eval x.rep f = 0 := by
      refine Ideal.span_le.mpr (fun w hw => RingHom.mem_ker.mpr ?_)
      exact hx w hw
    rw [← hS]
    intro g hg
    have hgI : g.1 ∈ Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)) := by
      rw [← hI]
      obtain ⟨d, hd⟩ := g.2
      refine Proj.subset_vanishingIdeal hd (fun y hy => ?_)
      rw [← hS] at hy
      exact hy g hg
    exact hxI g.1 hgI

theorem finrank_linSpace (m : ℕ) : Module.finrank k (linSpace k m) = m := by
  have h := (coeffEquiv (k := k) (m := m)).finrank_eq
  rw [h, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end LinearZeroLocus

end Hartshorne77.Ex_I_2_11


/-! ## Part 12: the dimension theorem for linear varieties, clauses (a) and (b) -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u
variable {k : Type u} [Field k]

theorem coeffVec_linForm (m : ℕ) (c : Fin m → k) :
    coeffVec (k := k) ⟨linForm c, linForm_mem_linSpace c⟩ = c := by
  ext i
  exact coeff_linForm c i

theorem ideal_span_coe_span {m : ℕ} (S : Set (MvPolynomial (Fin m) k)) :
    Ideal.span ((Submodule.span k S : Submodule k (MvPolynomial (Fin m) k)) :
        Set (MvPolynomial (Fin m) k)) = Ideal.span S := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    intro f hf
    exact Submodule.span_induction (R := k) (p := fun f _ => f ∈ Ideal.span S)
      (fun x hx => Ideal.subset_span hx) (Ideal.span S).zero_mem
      (fun x y _ _ hx hy => (Ideal.span S).add_mem hx hy)
      (fun c x _ hx => by
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left (Ideal.span S) _ hx) hf
  · rw [Ideal.span_le]
    intro f hf
    exact Ideal.subset_span (Submodule.subset_span hf)

section ExMain

variable {n : ℕ} [IsAlgClosed k]

/-- The cone dimension of a projective set whose cone is the affine zero locus of an ideal
generated by a space of linear forms. -/
theorem coneDim_eq_finrank {Y : Set (Proj k n)} {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1))
    (h : Proj.cone Y =
      MvPolynomial.zeroLocus k (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)))) :
    coneDim Y = (((n + 1) - Module.finrank k W : ℕ) : ℕ∞) := by
  have hconene : (Proj.cone Y).Nonempty := ⟨0, Or.inl rfl⟩
  have e1 : varietyDim k (n + 1) (Proj.cone Y) =
      ((irrChainDim (Proj.cone Y) : ℕ∞) : WithBot ℕ∞) := varietyDim_eq_coe_irrChainDim hconene
  have e2 : varietyDim k (n + 1) (MvPolynomial.zeroLocus k
      (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)))) =
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸
        Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))) :=
    varietyDim_zeroLocus (k := k) (n := n + 1) _
  have hcoe : ((irrChainDim (Proj.cone Y) : ℕ∞) : WithBot ℕ∞) =
      (((n + 1) - Module.finrank k W : ℕ) : WithBot ℕ∞) := by
    rw [← e1, h, e2]
    exact (linSpaceIdeal_isPrime_and_dim W hW).2
  have h1 : irrChainDim (Proj.cone Y) = (((n + 1) - Module.finrank k W : ℕ) : ℕ∞) :=
    WithBot.coe_injective hcoe
  show irrChainDim (Proj.cone Y) = _
  exact h1

/-- For a linear projective variety with `I(Y)` generated by the space `W`, the finrank of `W` is
`n - r` where `r = dim Y`. -/
theorem finrank_of_projDim {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty)
    {W : Submodule k (MvPolynomial (Fin (n + 1)) k)} (hW : W ≤ linSpace k (n + 1))
    (hI : Proj.vanishingIdeal Y = Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)))
    {r : ℕ} (hdim : projDim Y = (r : ℕ∞)) :
    Module.finrank k W = n - r := by
  have hYeq : Y = linZeroLocus W := linZeroLocus_of_vanishingIdeal_eq hYc hW hI
  have hcone : Proj.cone Y =
      MvPolynomial.zeroLocus k (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))) := by
    rw [hYeq]
    exact cone_linZeroLocus hW
  have hc := coneDim_eq_finrank hW hcone
  have hc2 : coneDim Y = ((r + 1 : ℕ) : ℕ∞) := by
    rw [coneDim_eq_projDim_add_one hYc hne, hdim]
    push_cast
    ring
  have hnat : (n + 1) - Module.finrank k W = r + 1 := by
    apply Nat.cast_injective (R := ℕ∞)
    rw [← hc, hc2]
  have hle : Module.finrank k W ≤ n + 1 := by
    rw [← coeffSub_finrank W hW]
    have h := Submodule.finrank_le (R := k) (M := Fin (n + 1) → k) (coeffSub W hW)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

/-- A finite set of polynomials spans a space of dimension at most its cardinality. -/
theorem finrank_span_finset_le_card {m : ℕ} (s : Finset (MvPolynomial (Fin m) k)) :
    Module.finrank k (Submodule.span k (s : Set (MvPolynomial (Fin m) k))) ≤ s.card := by
  classical
  haveI : Fintype ↥(s : Set (MvPolynomial (Fin m) k)) := s.finite_toSet.fintype
  have h := finrank_span_le_card (R := k) (s := (s : Set (MvPolynomial (Fin m) k)))
  simpa using h

/-- A basis of the coefficient space of a space of linear forms gives a finite set of linear forms
with the same span. -/
theorem exists_finset_linearForm_span {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) :
    ∃ S : Finset (LinearForm k (n + 1)), S.card = Module.finrank k W ∧
      Ideal.span (Subtype.val '' (S : Set (LinearForm k (n + 1)))) =
        Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)) := by
  classical
  haveI : Module.Finite k ↥(coeffSub W hW) := inferInstance
  let b : Module.Basis (Fin (Module.finrank k ↥(coeffSub W hW))) k ↥(coeffSub W hW) :=
    Module.finBasis k ↥(coeffSub W hW)
  let F : Fin (Module.finrank k ↥(coeffSub W hW)) → LinearForm k (n + 1) :=
    fun i => ⟨linForm (b i).1, linForm_isHomogeneous (b i).1⟩
  have hFmem : ∀ i, (F i).1 ∈ W := fun i => linForm_mem_of_mem_coeffSub W hW (b i).2
  have hinj : Function.Injective F := by
    intro i j hij
    have h1 : linForm (b i).1 = linForm (b j).1 := congrArg Subtype.val hij
    have h2 : (b i).1 = (b j).1 := by
      have hsub : (⟨linForm (b i).1, linForm_mem_linSpace (b i).1⟩ : linSpace k (n + 1)) =
          ⟨linForm (b j).1, linForm_mem_linSpace (b j).1⟩ := Subtype.ext h1
      have h3 := congrArg (fun p : linSpace k (n + 1) => coeffVec p) hsub
      rwa [coeffVec_linForm, coeffVec_linForm] at h3
    exact b.injective (Subtype.ext h2)
  refine ⟨Finset.univ.map ⟨F, hinj⟩, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, coeffSub_finrank W hW]
  · have hset : (Subtype.val '' ((Finset.univ.map ⟨F, hinj⟩ : Finset (LinearForm k (n + 1))) :
        Set (LinearForm k (n + 1)))) = Set.range (fun i => (F i).1) := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hg
        exact Set.mem_range_self i
      · rintro ⟨i, rfl⟩
        exact ⟨F i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩
    rw [hset]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro f ⟨i, rfl⟩
      exact Ideal.subset_span (hFmem i)
    · rw [Ideal.span_le]
      intro w hw
      have hcoe : coeffVec (k := k) ⟨w, hW hw⟩ ∈ coeffSub W hW := coeffSub_mem_of_mem W hW hw
      have hrep : (∑ i, b.repr ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ i • b i) =
          ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ := b.sum_repr _
      have hsum : (∑ i, b.repr ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ i • (b i).1) =
          coeffVec (k := k) ⟨w, hW hw⟩ := by
        have h := congrArg (fun v : ↥(coeffSub W hW) => (v : Fin (n + 1) → k)) hrep
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
      have hw' : w = ∑ i, b.repr ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ i • (F i).1 := by
        calc w = linForm (coeffVec (k := k) ⟨w, hW hw⟩) := by rw [linForm_coeffVec]
          _ = linForm (∑ i, b.repr ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ i • (b i).1) := by
                rw [hsum]
          _ = ∑ i, b.repr ⟨coeffVec (k := k) ⟨w, hW hw⟩, hcoe⟩ i • (F i).1 := by
                rw [linForm_sum]
                exact Finset.sum_congr rfl fun i _ => by rw [linForm_smul']
      rw [hw']
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left (Ideal.span (Set.range fun i => (F i).1)) _
        (Ideal.subset_span ⟨i, rfl⟩)

/-- **(a)** of Hartshorne I.2.11: `I(Y)` is generated by linear polynomials iff `Y` is an
intersection of hyperplanes, for a projective variety `Y`. -/
theorem clause_a {Y : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y) :
    LinGenerated (Proj.vanishingIdeal Y) ↔ IsLinearVariety Y := by
  constructor
  · rintro ⟨W, hW, hI⟩
    have hYeq : Y = linZeroLocus W := linZeroLocus_of_vanishingIdeal_eq hYc hW hI.symm
    exact ⟨W, hW, hYeq⟩
  · rintro ⟨W, hW, hYeq⟩
    have hY' : Y = linZeroLocus W := hYeq
    have hne : (linZeroLocus W).Nonempty := hY' ▸ hYi.nonempty
    exact ⟨W, hW, (vanishingIdeal_linZeroLocus hW hne).symm.trans (by rw [← hY'])⟩

/-- **(b)** of Hartshorne I.2.11: a linear variety of dimension `r` in `P^n` is cut out by
`n - r` linear polynomials, and `n - r` is the minimal number. -/
theorem clause_b {Y : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y) (r : ℕ)
    (hlin : LinGenerated (Proj.vanishingIdeal Y)) (hdim : projDim Y = (r : ℕ∞)) :
    (∃ S : Finset (LinearForm k (n + 1)), S.card = n - r ∧
      Ideal.span (Subtype.val '' (S : Set (LinearForm k (n + 1)))) = Proj.vanishingIdeal Y) ∧
    (∀ S : Finset (LinearForm k (n + 1)),
      Ideal.span (Subtype.val '' (S : Set (LinearForm k (n + 1)))) = Proj.vanishingIdeal Y →
        n - r ≤ S.card) := by
  classical
  obtain ⟨W, hW, hI⟩ := hlin
  have hne : Y.Nonempty := hYi.nonempty
  have hfr : Module.finrank k W = n - r := finrank_of_projDim hYc hne hW hI.symm hdim
  constructor
  · obtain ⟨S, hcard, hspan⟩ := exists_finset_linearForm_span hW
    exact ⟨S, by rw [hcard, hfr], by rw [hspan, hI]⟩
  · intro S hS
    set U : Submodule k (MvPolynomial (Fin (n + 1)) k) :=
      Submodule.span k (Subtype.val '' (S : Set (LinearForm k (n + 1)))) with hU
    have hUle : U ≤ linSpace k (n + 1) := by
      rw [hU]
      refine Submodule.span_le.mpr ?_
      rintro f ⟨g, -, rfl⟩
      rw [linSpace_eq_set]
      exact g.2
    have hIU : Ideal.span (U : Set (MvPolynomial (Fin (n + 1)) k)) = Proj.vanishingIdeal Y := by
      rw [hU, ideal_span_coe_span, ← hS]
    have hfrU : Module.finrank k U = n - r := finrank_of_projDim hYc hne hUle hIU.symm hdim
    have hle : Module.finrank k U ≤ (S.image (fun g : LinearForm k (n + 1) => g.1)).card := by
      have h1 := finrank_span_finset_le_card (k := k)
        (s := S.image (fun g : LinearForm k (n + 1) => g.1))
      rw [Finset.coe_image] at h1
      exact h1
    have hcard : (S.image (fun g : LinearForm k (n + 1) => g.1)).card ≤ S.card :=
      Finset.card_image_le
    omega

end ExMain

end Hartshorne77.Ex_I_2_11


/-! ## Part 13: clause (c) of Hartshorne I.2.11 -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u
variable {k : Type u} [Field k]

section ExMainC

variable {n : ℕ} [IsAlgClosed k]

/-- The space of linear forms is finite-dimensional. -/
theorem moduleFinite_linSpace (m : ℕ) : Module.Finite k ↥(linSpace k m) :=
  Module.Finite.equiv (coeffEquiv (k := k) (m := m)).symm

/-- A subspace of the space of linear forms is finite-dimensional. -/
theorem moduleFinite_of_le_linSpace {m : ℕ} {W : Submodule k (MvPolynomial (Fin m) k)}
    (hW : W ≤ linSpace k m) : Module.Finite k ↥W := by
  haveI : Module.Finite k ↥(linSpace k m) := moduleFinite_linSpace m
  exact Module.Finite.of_injective (Submodule.inclusion hW) (Submodule.inclusion_injective hW)

/-- The projective zero set of a space of linear forms of rank at most `n` is nonempty. -/
theorem linZeroLocus_nonempty_of_finrank_le {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) (hfr : Module.finrank k W ≤ n) :
    (linZeroLocus W).Nonempty := by
  classical
  set J := Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k)) with hJ
  have hcone : Proj.cone (linZeroLocus W) = MvPolynomial.zeroLocus k J := cone_linZeroLocus hW
  have hdim : varietyDim k (n + 1) (Proj.cone (linZeroLocus W)) =
      (((n + 1) - Module.finrank k W : ℕ) : WithBot ℕ∞) := by
    rw [hcone, varietyDim_zeroLocus]
    exact (linSpaceIdeal_isPrime_and_dim W hW).2
  by_contra hne
  have hempty : linZeroLocus (k := k) (n := n) W = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  rw [hempty, Proj.cone_empty, varietyDim_singleton_zero] at hdim
  rw [← WithBot.coe_zero] at hdim
  have hk0 : ((n + 1) - Module.finrank k W : ℕ) = 0 :=
    ENat.natCast_inj.mp (WithBot.coe_inj.mp hdim.symm)
  omega

/-- The dimension of the projective zero set of a space of linear forms, in the range where it is
nonempty. -/
theorem projDim_linZeroLocus {W : Submodule k (MvPolynomial (Fin (n + 1)) k)}
    (hW : W ≤ linSpace k (n + 1)) (hfr : Module.finrank k W ≤ n) :
    projDim (linZeroLocus W) = ((n - Module.finrank k W : ℕ) : ℕ∞) := by
  have hcone : Proj.cone (linZeroLocus W) =
      MvPolynomial.zeroLocus k (Ideal.span (W : Set (MvPolynomial (Fin (n + 1)) k))) :=
    cone_linZeroLocus hW
  have hcd : coneDim (linZeroLocus W) = (((n + 1) - Module.finrank k W : ℕ) : ℕ∞) :=
    coneDim_eq_finrank hW hcone
  have hne : (linZeroLocus W).Nonempty := linZeroLocus_nonempty_of_finrank_le hW hfr
  have hc : IsClosed (linZeroLocus W) := isClosed_linZeroLocus hW
  have h1 : coneDim (linZeroLocus W) = projDim (linZeroLocus W) + 1 :=
    coneDim_eq_projDim_add_one hc hne
  rw [hcd] at h1
  have harith : ((n + 1) - Module.finrank k W : ℕ) = (n - Module.finrank k W) + 1 := by omega
  rw [harith, Nat.cast_add, Nat.cast_one] at h1
  exact WithTop.add_right_cancel (by exact ENat.natCast_ne_top 1) h1.symm

/-- The projective dimension of any subset of `P^n` is at most `n`. -/
theorem projDim_le (Y : Set (Proj k n)) : projDim Y ≤ (n : ℕ∞) := by
  have h1 : projDim (Set.univ : Set (Proj k n)) = (n : ℕ∞) := by
    have h := coneDim_eq_projDim_add_one (Y := (Set.univ : Set (Proj k n))) isClosed_univ
      Set.univ_nonempty
    rw [coneDim_univ] at h
    have h2 : ((n : ℕ∞) + 1) = projDim (Set.univ : Set (Proj k n)) + 1 := by
      simpa using h
    exact WithTop.add_right_cancel (by exact ENat.natCast_ne_top 1) h2.symm
  calc projDim Y ≤ projDim (Set.univ : Set (Proj k n)) := projDim_mono (Set.subset_univ Y)
    _ = (n : ℕ∞) := h1

/-- **(c)** of Hartshorne I.2.11: linear varieties `Y, Z ⊆ P^n` of dimensions `r, s` with
`r + s ≥ n` meet, and their intersection is again a linear variety of dimension at least
`r + s - n`. -/
theorem clause_c {Y Z : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y)
    (hZc : IsClosed Z) (hZi : IsIrreducible Z) (r s : ℕ)
    (hYl : LinGenerated (Proj.vanishingIdeal Y)) (hZl : LinGenerated (Proj.vanishingIdeal Z))
    (hYd : projDim Y = (r : ℕ∞)) (hZd : projDim Z = (s : ℕ∞)) :
    (n ≤ r + s → (Y ∩ Z).Nonempty) ∧
      ((Y ∩ Z).Nonempty → LinGenerated (Proj.vanishingIdeal (Y ∩ Z)) ∧
        ((r + s - n : ℕ) : ℕ∞) ≤ projDim (Y ∩ Z)) := by
  classical
  obtain ⟨W, hW, hIW⟩ := hYl
  obtain ⟨V, hV, hIV⟩ := hZl
  have hYne : Y.Nonempty := hYi.nonempty
  have hZne : Z.Nonempty := hZi.nonempty
  have hYeq : Y = linZeroLocus W := linZeroLocus_of_vanishingIdeal_eq hYc hW hIW.symm
  have hZeq : Z = linZeroLocus V := linZeroLocus_of_vanishingIdeal_eq hZc hV hIV.symm
  have hfrW : Module.finrank k W = n - r := finrank_of_projDim hYc hYne hW hIW.symm hYd
  have hfrV : Module.finrank k V = n - s := finrank_of_projDim hZc hZne hV hIV.symm hZd
  have hr : r ≤ n := ENat.natCast_le_natCast.mp (hYd ▸ projDim_le Y)
  have hs : s ≤ n := ENat.natCast_le_natCast.mp (hZd ▸ projDim_le Z)
  have hU : W ⊔ V ≤ linSpace k (n + 1) := sup_le hW hV
  have hYZ : Y ∩ Z = linZeroLocus (W ⊔ V) := by rw [hYeq, hZeq, linZeroLocus_sup]
  -- rank bound: `dim (W ⊔ V) ≤ (n - r) + (n - s)`
  have hsup : Module.finrank k ↥(W ⊔ V) ≤ n - r + (n - s) := by
    haveI : Module.Finite k ↥W := moduleFinite_of_le_linSpace hW
    haveI : Module.Finite k ↥V := moduleFinite_of_le_linSpace hV
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K := k) W V
    rw [hfrW, hfrV] at h
    have h0 : 0 ≤ Module.finrank k ↥(W ⊓ V) := Nat.zero_le _
    omega
  constructor
  · intro hrs
    have hle : Module.finrank k ↥(W ⊔ V) ≤ n := by omega
    rw [hYZ]
    exact linZeroLocus_nonempty_of_finrank_le hU hle
  · intro hne
    have hne' : (linZeroLocus (W ⊔ V)).Nonempty := by rw [← hYZ]; exact hne
    constructor
    · rw [hYZ]
      exact ⟨W ⊔ V, hU, (vanishingIdeal_linZeroLocus hU hne').symm⟩
    · by_cases hrs : r + s ≤ n
      · have hzero : r + s - n = 0 := by omega
        rw [hzero, Nat.cast_zero]
        simp
      · have hrs' : n < r + s := not_le.mp hrs
        have hle : Module.finrank k ↥(W ⊔ V) ≤ n := by omega
        rw [hYZ, projDim_linZeroLocus hU hle]
        have hge : r + s - n ≤ n - Module.finrank k ↥(W ⊔ V) := by omega
        exact ENat.natCast_le_natCast.mpr hge

end ExMainC

end Hartshorne77.Ex_I_2_11


/-! ## Part 15: the generators furnished by clause (b) are linearly independent -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u
variable {k : Type u} [Field k]

section Indep

variable {m n : ℕ} [IsAlgClosed k]

/-- A `k`-basis of a space `W` of linear forms gives a linearly independent family of linear forms
which generates the ideal generated by `W`. -/
theorem exists_linearIndependent_linearForm_span {W : Submodule k (MvPolynomial (Fin m) k)}
    (hW : W ≤ linSpace k m) (hfin : Module.Finite k ↥W) :
    ∃ (q : ℕ) (g : Fin q → MvPolynomial (Fin m) k), q = Module.finrank k W ∧
      LinearIndependent k g ∧
      Ideal.span (Set.range g) = Ideal.span (W : Set (MvPolynomial (Fin m) k)) ∧
      ∀ i, g i ∈ linSpace k m := by
  classical
  haveI := hfin
  let b : Module.Basis (Fin (Module.finrank k W)) k ↥W := Module.finBasis k ↥W
  let g : Fin (Module.finrank k W) → MvPolynomial (Fin m) k := fun i => (b i).1
  have hgW : ∀ i, g i ∈ W := fun i => (b i).2
  refine ⟨Module.finrank k W, g, rfl, ?_, ?_, fun i => hW (hgW i)⟩
  · have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro c hc
    refine hb c ?_
    apply Subtype.ext
    have hcoe : ((∑ i, c i • b i : ↥W) : MvPolynomial (Fin m) k) = ∑ i, c i • g i := by
      simp only [Submodule.coe_sum, Submodule.coe_smul, g]
    rw [hcoe]
    exact hc
  · refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span (hgW i)
    · rw [Ideal.span_le]
      intro w hw
      have hsum : (∑ i, b.repr (⟨w, hw⟩ : ↥W) i • g i) = w := by
        have h := congrArg (fun x : ↥W => (x : MvPolynomial (Fin m) k))
          (b.sum_repr (⟨w, hw⟩ : ↥W))
        simpa only [Submodule.coe_sum, Submodule.coe_smul, g] using h
      rw [← hsum]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left (Ideal.span (Set.range g)) _
        (Ideal.subset_span ⟨i, rfl⟩)

/-- Clause (b) with independence: a linear variety of dimension `r` in `P^n` has its vanishing
ideal generated by `n - r` linearly independent linear forms. -/
theorem exists_linearIndependent_generators {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (r : ℕ) (hlin : LinGenerated (Proj.vanishingIdeal Y))
    (hdim : projDim Y = (r : ℕ∞)) :
    ∃ (q : ℕ) (g : Fin q → MvPolynomial (Fin (n + 1)) k), q = n - r ∧
      LinearIndependent k g ∧ Ideal.span (Set.range g) = Proj.vanishingIdeal Y ∧
      ∀ i, g i ∈ linSpace k (n + 1) := by
  obtain ⟨W, hW, hIW⟩ := hlin
  haveI hfin : Module.Finite k ↥W := moduleFinite_of_le_linSpace hW
  obtain ⟨q, g, hq, hli, hspan, hmem⟩ := exists_linearIndependent_linearForm_span hW hfin
  have hfr : Module.finrank k W = n - r := finrank_of_projDim hYc hYi.nonempty hW hIW.symm hdim
  exact ⟨q, g, by rw [hq, hfr], hli, by rw [hspan, hIW], hmem⟩

end Indep

end Hartshorne77.Ex_I_2_11


/-! ## Part 14: Hartshorne I.2.11, linear varieties in `P^n` -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open MvPolynomial

namespace Hartshorne77.Ex_I_2_11

universe u

/-- **Hartshorne, Algebraic Geometry (1977), Exercise I.2.11**: linear varieties in `P^n`.

(a) For a projective variety `Y ⊆ P^n`, the vanishing ideal `I(Y)` is generated by linear
polynomials iff `Y` is an intersection of hyperplanes.
(b) If in addition `dim Y = r`, then `I(Y)` is minimally generated by `n - r` linear polynomials:
there is a set of `n - r` linear forms generating `I(Y)`, and no generating set of `I(Y)` by
linear forms has fewer than `n - r` elements.
(c) If `Y, Z` are linear varieties of dimensions `r, s` with `r + s ≥ n`, then `Y ∩ Z` is
nonempty; if `Y ∩ Z ≠ ∅` then `I(Y ∩ Z)` is generated by linear polynomials and
`dim (Y ∩ Z) ≥ r + s - n`. -/
theorem hartshorne_exercise_I_2_11 {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) :
    hartshorne_exercise_I_2_11_statement (k := k) n := by
  intro Y Z hYc hYi hZc hZi
  refine ⟨clause_a hYc hYi, ?_, ?_⟩
  · exact clause_b hYc hYi
  · exact clause_c hYc hYi hZc hZi

end Hartshorne77.Ex_I_2_11

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_2_11.hartshorne_exercise_I_2_11
#print axioms Hartshorne77.Ex_I_2_11.clause_a
#print axioms Hartshorne77.Ex_I_2_11.clause_b
#print axioms Hartshorne77.Ex_I_2_11.clause_c
#print axioms Hartshorne77.Ex_I_2_11.linSpaceIdeal_isPrime_and_dim
#print axioms Hartshorne77.Ex_I_2_11.projDim_linZeroLocus
#print axioms Hartshorne77.Ex_I_2_11.vanishingIdeal_linZeroLocus
#print axioms Hartshorne77.Ex_I_2_11.exists_linearIndependent_generators
#print axioms Hartshorne77.Ex_I_2_11.exists_linearIndependent_linearForm_span
#print axioms Hartshorne77.Ex_I_2_11.coeffSub_finrank
#print axioms Hartshorne77.Ex_I_2_11.finrank_of_projDim

