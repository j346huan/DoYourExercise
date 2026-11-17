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

namespace Hartshorne77.Ex_I_2_6

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

end Hartshorne77.Ex_I_2_6

/-! ## The affine cone and the vanishing ideal -/

namespace Hartshorne77.Ex_I_2_6
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

end Hartshorne77.Ex_I_2_6

/-! ## Affine dimension theory (accepted Hartshorne I.1.8 infrastructure) -/

namespace Hartshorne77.Ex_I_2_6
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

#print axioms Hartshorne77.Ex_I_2_6.hartshorne_exercise_I_2_10
#print axioms Hartshorne77.Ex_I_2_6.coneDim_eq_projDim_add_one
#print axioms Hartshorne77.Ex_I_2_6.coneDim_eq_projDim_add_one_irreducible
#print axioms Hartshorne77.Ex_I_2_6.projDim_add_one_le_coneDim
#print axioms Hartshorne77.Ex_I_2_6.Proj.cone_eq_zeroLocus
#print axioms Hartshorne77.Ex_I_2_6.Proj.isIrreducible_cone_iff_isPrime
#print axioms Hartshorne77.Ex_I_2_6.Proj.isIrreducible_cone_iff'
#print axioms Hartshorne77.Ex_I_2_6.Proj.vanishingIdeal_isPrime_iff

end Hartshorne77.Ex_I_2_6

/-! # Hartshorne, *Algebraic Geometry* (1977), Chapter I, Exercise 2.6

SOURCE STATEMENT (verbatim, cross-checked against
<https://hartshorne-ag-solutions.wikidot.com/chapter-1-section-2>; the local OCR
`.scratch/reference/hartshorne-1977.txt` is defective exactly here, its §2 exercise block is
scrambled and exercises 2.1–2.12 are partly missing, so it is not usable as the source):

> 2.6. If `Y` is a projective variety with homogeneous coordinate ring `S(Y)`, show that
> `dim S(Y) = dim Y + 1`. [*Hint*: Let `φ_i : U_i → A^n` be the homeomorphism of (2.2), let `Y_i`
> be the affine variety `φ_i(Y ∩ U_i)`, and let `A(Y_i)` be its affine coordinate ring. Show that
> `A(Y_i)` can be identified with the subring of elements of degree `0` of the localized ring
> `S(Y)_{x_i}`. Then show that `S(Y)_{x_i} ≅ A(Y_i)[x_i, x_i^{-1}]`. Now use (1.7), (1.8A), and
> (Ex. 1.10), and look at transcendence degrees. Conclude also that `dim Y = dim Y_i` whenever
> `Y_i` is nonempty.]

Standing hypotheses of Chapter I: `k` is an algebraically closed field; a *projective variety* is
a nonempty irreducible closed subset of `P^n`; `S = k[x_0,…,x_n]`; `S(Y) = S/I(Y)` with `I(Y)` the
homogeneous ideal generated by the homogeneous polynomials vanishing on `Y`; `dim` is the
supremum of the lengths of chains of irreducible closed subsets (Hartshorne I.1, p. 5); `P^n` is
the classical set of lines through the origin of `k^{n+1}`.

WHAT IS FORMALIZED (nothing below is stated for `Proj` of a graded ring or for prime spectra):

* `dehom i`, the dehomogenization `x_i ↦ 1, x_j ↦ y_j` of `S` onto the affine coordinate ring
  `k[y_0,…,y_{n-1}]` of the chart `A^n ≅ U_i`, and `homIncl i` (`y_j ↦ x_{i.succAbove j}`);
  `eval_dehom` is the identity `f(b) = f_β(b,1)` making the dehomogenization compatible with
  evaluation, `ker_dehom` that its kernel is `(x_i - 1)`.
* `affinePiece Y i ⊆ A^n`, the affine variety `Y_i = φ_i(Y ∩ U_i)` of the hint: the set of `b`
  with `(b : 1 : b) ∈ Y` (`chartMap`).
* `chartOpen i` (`U_i`), `chartCoord i` (`φ_i`) and `chartMap i` (`φ_i^{-1}`), with
  `chartMap_chartCoord` / `chartCoord_chartMap` the two inverse laws and
  `chartMap_image_affinePiece : chartMap i '' (affinePiece Y i) = Y ∩ U_i`, which states exactly
  that `affinePiece Y i = φ_i (Y ∩ U_i)` is the affine variety `Y_i` of the statement.
* `affinePiece_eq_zeroLocus`: `Y_i` is the affine algebraic set defined by the dehomogenized
  homogeneous coordinate ring, i.e. `A(Y_i) = S(Y)/(x_i - 1) = (dehom i)(S(Y))`.
* `dehomQuotientEquiv`: `k[y] ⧸ (dehom i)(I(Y)) ≃ₐ[k] S ⧸ (I(Y) + (x_i - 1))`, the algebraic
  content of `S(Y)_{x_i} = A(Y_i)[x_i, x_i^{-1}]` in the chart form: `A(Y_i)` is the coordinate
  ring of the hyperplane section `C(Y) ∩ {x_i = 1}` of the affine cone.
* `dim_homogeneousCoordinateRing`: `dim S(Y) = dim Y + 1` (`= projDim Y + 1`).
* `hartshorne_exercise_I_2_6`: both conclusions of the exercise, namely `dim S(Y) = dim Y + 1`
  and `dim Y = dim Y_i` for every nonempty affine piece `Y_i`.

CLAUSE-BY-CLAUSE COVERAGE (the two conclusions of the printed exercise):

1. `dim S(Y) = dim Y + 1`
     `hartshorne_exercise_I_2_6` (first component),
     `dim_homogeneousCoordinateRing`:
       `ringKrullDim (k[x_0,…,x_n] ⧸ I(Y)) = projDim Y + 1`,
     where `projDim Y` is the chain dimension of `Y ⊆ P^n` and `ringKrullDim` is the Krull
     dimension of the homogeneous coordinate ring `S(Y) = S ⧸ I(Y)`.
2. `dim Y = dim Y_i` whenever `Y_i = φ_i(Y ∩ U_i)` is nonempty
     `hartshorne_exercise_I_2_6` (second component), `varietyDim_affinePiece`:
       `varietyDim (affinePiece Y i) = projDim Y` for every `i` with `affinePiece Y i ≠ ∅`.

Auxiliary results proved on the way (all new, all axiom-clean):
`chartMap_image_affinePiece` (`φ_i(Y ∩ U_i) = Y_i`),
`eval_dehom` (`f(b,1) = (dehom i f)(b)`), `ker_dehom` (`ker (dehom i) = (x_i - 1)`),
`sub_homIncl_dehom_mem` (`f - (f dehomogenized then re-homogenized) ∈ (x_i - 1)`),
`affinePiece_eq_zeroLocus` (`A(Y_i) = (dehom i)(S(Y))`), `dehomQuotientEquiv`
(`k[y] ⧸ (dehom i)(I) ≃+* S ⧸ (I + (x_i - 1))`, the chart form of
`S(Y)_{x_i} ≅ A(Y_i)[x_i, x_i^{-1}]`), and `varietyDim_slice_add_one`
(`dim (C(Y) ∩ {x_i = 1}) + 1 = dim C(Y)`, from Hartshorne I.1.8).

No edge case of the printed statement needs repair: `Variety` is irreducible and hence nonempty
(Hartshorne I.1, p. 3), `dim` of a ring is the Krull dimension (I.1), and for `Y = P^n` the
statement reads `dim k[x_0,…,x_n] = n + 1 = dim P^n + 1`, which holds for every `n ≥ 0`.
-/

namespace Hartshorne77.Ex_I_2_6

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ## The dehomogenization `x_i ↦ 1` of the homogeneous coordinate ring -/

/-- The index substitution `x_i ↦ 1`, `x_j ↦ y_j` used to dehomogenize at `x_i`. -/
noncomputable def dehomIndex (i : Fin (n + 1)) : Fin (n + 1) → MvPolynomial (Fin n) k :=
  Fin.insertNth i (1 : MvPolynomial (Fin n) k) (fun l => MvPolynomial.X l)

/-- **Dehomogenization at the coordinate `x_i`**, i.e. the substitution `x_i ↦ 1` and
`x_j ↦ y_j` (`j ≠ i`) from `S = k[x_0,…,x_n]` to `k[y_0,…,y_{n-1}]`. -/
noncomputable def dehom (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (dehomIndex (k := k) i)

/-- Homogenization of indices: `y_l ↦ x_{i.succAbove l}`. -/
noncomputable def homIncl (i : Fin (n + 1)) :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  MvPolynomial.rename (Fin.succAbove i)

theorem dehomIndex_self {i : Fin (n + 1)} : dehomIndex (k := k) i i = 1 :=
  Fin.insertNth_apply_same i _ _

theorem dehomIndex_succAbove {i : Fin (n + 1)} (l : Fin n) :
    dehomIndex (k := k) i (i.succAbove l) = MvPolynomial.X l :=
  Fin.insertNth_apply_succAbove i _ _ l

theorem homIncl_X {i : Fin (n + 1)} (l : Fin n) :
    homIncl (k := k) i (MvPolynomial.X l) = MvPolynomial.X (i.succAbove l) :=
  MvPolynomial.rename_X _ _

/-- Dehomogenization kills `x_i - 1`. -/
theorem dehom_X_self {i : Fin (n + 1)} : dehom (k := k) i (MvPolynomial.X i) = 1 := by
  rw [dehom, MvPolynomial.aeval_X, dehomIndex_self]

theorem dehom_X_succAbove {i : Fin (n + 1)} (l : Fin n) :
    dehom (k := k) i (MvPolynomial.X (i.succAbove l)) = MvPolynomial.X l := by
  rw [dehom, MvPolynomial.aeval_X, dehomIndex_succAbove]

/-- Re-homogenizing a dehomogenized polynomial returns it. -/
theorem dehom_homIncl (i : Fin (n + 1)) (g : MvPolynomial (Fin n) k) :
    dehom (k := k) i (homIncl (k := k) i g) = g := by
  have h : (dehom (k := k) i).comp (homIncl (k := k) i) = AlgHom.id k (MvPolynomial (Fin n) k) := by
    refine MvPolynomial.algHom_ext fun l => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply, homIncl_X, dehom_X_succAbove]
  exact DFunLike.congr_fun h g

theorem homIncl_dehom_X {i : Fin (n + 1)} {j : Fin (n + 1)} (hj : j ≠ i) :
    homIncl (k := k) i (dehom (k := k) i (MvPolynomial.X j)) = MvPolynomial.X j := by
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
  rw [dehom_X_succAbove, homIncl_X]

/-- Dehomogenization is surjective onto the coordinate ring of the affine chart. -/
theorem dehom_surjective (i : Fin (n + 1)) : Function.Surjective (dehom (k := k) i) := by
  intro g
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [dehom]⟩
  | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add (dehom (k := k) i) _ _⟩
  | mul_X p l hp =>
      obtain ⟨p', rfl⟩ := hp
      exact ⟨p' * MvPolynomial.X (i.succAbove l), by rw [map_mul, dehom_X_succAbove]⟩

/-- **Dehomogenization is compatible with evaluation**: the value of `f` at the chart point with
coordinates `b` and `x_i = 1` is the value of the dehomogenized polynomial at `b`. -/
theorem eval_dehom (i : Fin (n + 1)) (b : Fin n → k) (f : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial.eval b (dehom (k := k) i f) =
      MvPolynomial.eval (Fin.insertNth (α := fun _ => k) i 1 b) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dehom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      have hcoord : Fin.insertNth (α := fun _ => k) i 1 b j
          = MvPolynomial.eval b (dehomIndex (k := k) i j) := by
        rcases eq_or_ne j i with hji | hj
        · rw [hji, dehomIndex_self, Fin.insertNth_apply_same]; simp
        · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hj
          rw [← hl, dehomIndex_succAbove, Fin.insertNth_apply_succAbove]; simp
      have hXj : dehom (k := k) i (MvPolynomial.X j) = dehomIndex (k := k) i j := by
        rw [dehom, MvPolynomial.aeval_X]
      calc MvPolynomial.eval b (dehom (k := k) i (p * MvPolynomial.X j))
          = MvPolynomial.eval b (dehom (k := k) i p * dehomIndex (k := k) i j) := by
            rw [map_mul, hXj]
        _ = MvPolynomial.eval b (dehom (k := k) i p)
              * MvPolynomial.eval b (dehomIndex (k := k) i j) := by
            rw [MvPolynomial.eval_mul]
        _ = MvPolynomial.eval (Fin.insertNth (α := fun _ => k) i 1 b) p
              * Fin.insertNth (α := fun _ => k) i 1 b j := by rw [hp, hcoord]
        _ = MvPolynomial.eval (Fin.insertNth (α := fun _ => k) i 1 b) (p * MvPolynomial.X j) := by
            rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]

/-- Every polynomial differs from the re-homogenization of its dehomogenization by a multiple of
`x_i - 1`. -/
theorem sub_homIncl_dehom_mem (i : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) k) :
    f - homIncl (k := k) i (dehom (k := k) i f) ∈ Ideal.span {MvPolynomial.X i - 1} := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dehom]
  | add p q hp hq =>
      have heq : p + q - homIncl (k := k) i (dehom (k := k) i (p + q))
          = (p - homIncl (k := k) i (dehom (k := k) i p))
            + (q - homIncl (k := k) i (dehom (k := k) i q)) := by
        rw [map_add, map_add]; ring
      rw [heq]; exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      rcases eq_or_ne j i with hji | hj
      · rw [hji]
        have hd : dehom (k := k) i (p * MvPolynomial.X i) = dehom (k := k) i p := by
          rw [map_mul, dehom_X_self, mul_one]
        have heq : p * MvPolynomial.X i - homIncl (k := k) i (dehom (k := k) i (p * MvPolynomial.X i))
            = (p - homIncl (k := k) i (dehom (k := k) i p)) * MvPolynomial.X i
              + homIncl (k := k) i (dehom (k := k) i p) * (MvPolynomial.X i - 1) := by
          rw [hd]; ring
        rw [heq]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
          (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      · have hX : homIncl (k := k) i (dehom (k := k) i (MvPolynomial.X j)) = MvPolynomial.X j :=
          homIncl_dehom_X hj
        have hmul : homIncl (k := k) i (dehom (k := k) i (p * MvPolynomial.X j))
            = homIncl (k := k) i (dehom (k := k) i p) * MvPolynomial.X j := by
          rw [map_mul, map_mul, hX]
        rw [hmul]
        have heq : p * MvPolynomial.X j - homIncl (k := k) i (dehom (k := k) i p) * MvPolynomial.X j
            = (p - homIncl (k := k) i (dehom (k := k) i p)) * MvPolynomial.X j := by ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ hp

/-- The kernel of the dehomogenization at `x_i` is the principal ideal `(x_i - 1)`. -/
theorem ker_dehom (i : Fin (n + 1)) :
    RingHom.ker (dehom (k := k) i) = Ideal.span {MvPolynomial.X i - 1} := by
  refine le_antisymm ?_ ?_
  · intro f hf
    have h0 : dehom (k := k) i f = 0 := hf
    have h := sub_homIncl_dehom_mem (k := k) (n := n) i f
    rw [h0, map_zero] at h
    simpa using h
  · rw [Ideal.span_le]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    simp [dehom_X_self]

/-! ## The affine pieces of a projective set -/

/-- The chart point of `A^n` with coordinates `b`, placed in `P^n` as the point whose `i`-th
homogeneous coordinate is `1` (the inverse of the chart homeomorphism `φ_i` of (2.2)). -/
def chartPoint (i : Fin (n + 1)) (b : Fin n → k) : Fin (n + 1) → k :=
  Fin.insertNth (α := fun _ => k) i 1 b

theorem chartPoint_apply_self (i : Fin (n + 1)) (b : Fin n → k) : chartPoint i b i = 1 :=
  Fin.insertNth_apply_same i _ _

theorem chartPoint_apply_succAbove (i : Fin (n + 1)) (b : Fin n → k) (l : Fin n) :
    chartPoint i b (i.succAbove l) = b l :=
  Fin.insertNth_apply_succAbove i _ _ l

theorem chartPoint_ne_zero (i : Fin (n + 1)) (b : Fin n → k) : chartPoint i b ≠ 0 := by
  intro h
  have h1 := congrFun h i
  rw [chartPoint_apply_self] at h1
  exact one_ne_zero h1

/-- The inverse chart map `A^n → P^n`, `b ↦ (b_0 : … : 1 : … : b_{n-1})`. -/
noncomputable def chartMap (i : Fin (n + 1)) (b : Fin n → k) : Proj k n :=
  Proj.mk (chartPoint i b) (chartPoint_ne_zero i b)

/-- **The affine piece `Y_i = φ_i(Y ∩ U_i)`**: the set of coordinates `b ∈ A^n` whose chart point
with `x_i = 1` lies on `Y`. -/
noncomputable def affinePiece (Y : Set (Proj k n)) (i : Fin (n + 1)) : Set (Fin n → k) :=
  {b | chartMap (k := k) i b ∈ Y}

theorem mem_affinePiece_iff {Y : Set (Proj k n)} {i : Fin (n + 1)} {b : Fin n → k} :
    b ∈ affinePiece Y i ↔ chartMap (k := k) i b ∈ Y := Iff.rfl

theorem affinePiece_univ (i : Fin (n + 1)) :
    affinePiece (Set.univ : Set (Proj k n)) i = Set.univ := by
  ext b
  exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩

/-- The dehomogenization of an ideal of `S`: its image in the affine coordinate ring of the
chart. -/
noncomputable def dehomIdeal (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (i : Fin (n + 1)) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span ((fun g => dehom (k := k) i g) '' (I : Set (MvPolynomial (Fin (n + 1)) k)))

theorem mem_dehomIdeal_zeroLocus_iff (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (i : Fin (n + 1)) (b : Fin n → k) :
    b ∈ MvPolynomial.zeroLocus k (dehomIdeal (k := k) I i) ↔
      ∀ g ∈ I, MvPolynomial.eval (chartPoint i b) g = 0 := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h g hg
    have h1 : MvPolynomial.aeval b (dehom (k := k) i g) = 0 :=
      h _ (Ideal.subset_span ⟨g, hg, rfl⟩)
    rw [MvPolynomial.aeval_eq_eval, eval_dehom] at h1
    exact h1
  · intro h f hf
    have hle : dehomIdeal (k := k) I i ≤ RingHom.ker (MvPolynomial.aeval b) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, hg, rfl⟩
      show MvPolynomial.aeval b (dehom (k := k) i g) = 0
      rw [MvPolynomial.aeval_eq_eval, eval_dehom]
      exact h g hg
    exact hle hf


/-! ## The affine pieces really are the chart images `φ_i(Y ∩ U_i)` -/

/-- The standard affine open `U_i = {x_i ≠ 0} ⊆ P^n` of (2.2). -/
noncomputable def chartOpen (i : Fin (n + 1)) : Set (Proj k n) :=
  {p | p.rep i ≠ 0}

theorem mem_chartOpen_iff {i : Fin (n + 1)} {p : Proj k n} : p ∈ chartOpen i ↔ p.rep i ≠ 0 :=
  Iff.rfl

/-- The chart point `(b_0 : … : 1 : … : b_{n-1})` lies in `U_i`. -/
theorem chartMap_mem_chartOpen (i : Fin (n + 1)) (b : Fin n → k) :
    chartMap (k := k) i b ∈ chartOpen i := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) (chartPoint i b)
    (chartPoint_ne_zero i b)
  have hrep : (chartMap (k := k) i b).rep = fun j => (a : k) * chartPoint i b j := by
    rw [chartMap]
    rw [← ha]
    rfl
  show (chartMap (k := k) i b).rep i ≠ 0
  rw [hrep]
  simp only [chartPoint_apply_self, mul_one]
  exact Units.ne_zero a

/-- The chart coordinates `φ_i(p) = (x_0/x_i, …, x̂_i, …, x_n/x_i)`. -/
noncomputable def chartCoord (i : Fin (n + 1)) (p : Proj k n) : Fin n → k :=
  fun l => (p.rep i)⁻¹ * p.rep (i.succAbove l)

/-- `φ_i` inverts the chart point map on `U_i`. -/
theorem chartMap_chartCoord {i : Fin (n + 1)} {p : Proj k n} (hp : p.rep i ≠ 0) :
    chartMap (k := k) i (chartCoord i p) = p := by
  conv_rhs => rw [← Projectivization.mk_rep (K := k) p]
  rw [chartMap]
  refine (Projectivization.mk_eq_mk_iff k (chartPoint i (chartCoord i p)) p.rep
    (chartPoint_ne_zero i _) p.rep_nonzero).mpr ?_
  refine ⟨(Units.mk0 (p.rep i) hp)⁻¹, ?_⟩
  funext j
  rcases eq_or_ne j i with hji | hj
  · subst hji
    rw [chartPoint_apply_self, Pi.smul_apply]
    show ((p.rep j)⁻¹) * p.rep j = 1
    exact inv_mul_cancel₀ hp
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hj
    rw [← hl, chartPoint_apply_succAbove, Pi.smul_apply]
    show ((p.rep i)⁻¹) * p.rep (i.succAbove l) = chartCoord i p l
    rfl

/-- `φ_i` sends the chart point of `b` back to `b`. -/
theorem chartCoord_chartMap (i : Fin (n + 1)) (b : Fin n → k) :
    chartCoord i (chartMap (k := k) i b) = b := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) (chartPoint i b)
    (chartPoint_ne_zero i b)
  have hrep : (chartMap (k := k) i b).rep = fun j => (a : k) * chartPoint i b j := by
    rw [chartMap]
    rw [← ha]
    rfl
  funext l
  show ((chartMap (k := k) i b).rep i)⁻¹ * (chartMap (k := k) i b).rep (i.succAbove l) = b l
  rw [hrep]
  simp only [chartPoint_apply_self, mul_one, chartPoint_apply_succAbove]
  rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero a), one_mul]

/-- **`Y_i = φ_i(Y ∩ U_i)`**: the chart image of the affine piece `Y_i` is exactly the part of `Y`
in the standard affine open `U_i` of (2.2). -/
theorem chartMap_image_affinePiece (Y : Set (Proj k n)) (i : Fin (n + 1)) :
    chartMap (k := k) i '' (affinePiece Y i) = Y ∩ chartOpen i := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb, chartMap_mem_chartOpen i b⟩
  · rintro ⟨hpY, hpU⟩
    refine ⟨chartCoord i p, ?_, chartMap_chartCoord hpU⟩
    have hm : chartMap (k := k) i (chartCoord i p) ∈ Y := by
      rw [chartMap_chartCoord hpU]; exact hpY
    exact hm

/-! ## `Y_i` is the affine algebraic set of the dehomogenized coordinate ring -/

section AffinePieceZeroLocus

variable [IsAlgClosed k]

/-- **`Y_i` is cut out by the dehomogenized vanishing ideal**: `Y_i = φ_i(Y ∩ U_i)` is the affine
algebraic set whose coordinate ring is the dehomogenization of `S(Y)` at `x_i`. -/
theorem affinePiece_eq_zeroLocus {Y : Set (Proj k n)} (hYc : IsClosed Y) (i : Fin (n + 1)) :
    affinePiece Y i = MvPolynomial.zeroLocus k (dehomIdeal (Proj.vanishingIdeal Y) i) := by
  ext b
  rw [mem_affinePiece_iff, mem_dehomIdeal_zeroLocus_iff]
  constructor
  · intro hb g hg
    have hg' : g ∈ Proj.vanishOnIdeal Y := by
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal]
      exact hg
    exact Proj.mem_vanishOnIdeal_iff.mp hg' (chartPoint i b) (chartPoint_ne_zero i b) hb
  · intro h
    rw [← Proj.zeroLocus_vanishingForms_eq Y hYc, Proj.mem_zeroLocus_vanishingForms_iff]
    rintro f ⟨d, hd⟩ hfI
    show MvPolynomial.eval (chartMap (k := k) i b).rep f = 0
    exact (Proj.isZeroAt_mk_iff (d := d) hd (chartPoint_ne_zero i b)).2 (h f hfI)

/-- **Hartshorne I.2.6, first conclusion**: the dimension of the homogeneous coordinate ring of a
nonempty closed projective set is one more than its dimension. -/
theorem dim_homogeneousCoordinateRing {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hne : Y.Nonempty) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y)
      = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1 := by
  have h1 : varietyDim k (n + 1) (Proj.cone Y)
      = ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) := by
    rw [Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne,
      varietyDim_zeroLocus]
  have h2 : ((coneDim Y : ℕ∞) : WithBot ℕ∞) = varietyDim k (n + 1) (Proj.cone Y) :=
    (varietyDim_eq_coe_irrChainDim (Z := Proj.cone Y) ⟨0, Or.inl rfl⟩).symm
  rw [← h1, ← h2, coneDim_eq_projDim_add_one hYc hne, WithBot.coe_add]
  norm_num

end AffinePieceZeroLocus


/-! ## The dehomogenized coordinate ring is the coordinate ring of the hyperplane section -/

section DehomQuotient

variable [IsAlgClosed k] (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (i : Fin (n + 1))

/-- The ideal `I + (x_i - 1)` cutting the hyperplane section `C ∩ {x_i = 1}` of the affine cone
`C = V(I) ⊆ A^{n+1}`. -/
noncomputable def sliceIdeal : Ideal (MvPolynomial (Fin (n + 1)) k) :=
  I ⊔ Ideal.span {MvPolynomial.X i - 1}

theorem sliceIdeal_def :
    sliceIdeal I i = I ⊔ Ideal.span {MvPolynomial.X i - 1} := rfl

/-- The chart coordinate ring maps to the quotient by `I + (x_i - 1)`. -/
noncomputable def chartQuotMap :
    MvPolynomial (Fin n) k →+* (MvPolynomial (Fin (n + 1)) k ⧸ sliceIdeal I i) :=
  (Ideal.Quotient.mk (sliceIdeal I i)).comp
    (homIncl (k := k) i : MvPolynomial (Fin n) k →+* MvPolynomial (Fin (n + 1)) k)

theorem chartQuotMap_apply (g : MvPolynomial (Fin n) k) :
    chartQuotMap I i g = Ideal.Quotient.mk (sliceIdeal I i) (homIncl (k := k) i g) := rfl

/-- The dehomogenized ideal is killed by the map to `S ⧸ (I + (x_i - 1))`. -/
theorem dehomIdeal_le_ker_chartQuotMap : dehomIdeal I i ≤ RingHom.ker (chartQuotMap I i) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  show chartQuotMap I i (dehom (k := k) i g) = 0
  rw [chartQuotMap_apply, Ideal.Quotient.eq_zero_iff_mem]
  have h := sub_homIncl_dehom_mem (k := k) (n := n) i g
  have heq : homIncl (k := k) i (dehom (k := k) i g)
      = g - (g - homIncl (k := k) i (dehom (k := k) i g)) := by ring
  rw [heq]
  exact Submodule.mem_sup.mpr
    ⟨g, hg, -(g - homIncl (k := k) i (dehom (k := k) i g)), neg_mem h, by ring⟩

/-- `k[y] ⧸ (dehom i)(I) → S ⧸ (I + (x_i - 1))`, induced by the re-homogenization. -/
noncomputable def dehomQuotMap :
    (MvPolynomial (Fin n) k ⧸ dehomIdeal I i) →+*
      (MvPolynomial (Fin (n + 1)) k ⧸ sliceIdeal I i) :=
  Ideal.Quotient.lift (dehomIdeal I i) (chartQuotMap I i) (dehomIdeal_le_ker_chartQuotMap I i)

theorem dehomQuotMap_mk (g : MvPolynomial (Fin n) k) :
    dehomQuotMap I i (Ideal.Quotient.mk (dehomIdeal I i) g)
      = Ideal.Quotient.mk (sliceIdeal I i) (homIncl (k := k) i g) :=
  Ideal.Quotient.lift_mk (dehomIdeal I i) (chartQuotMap I i)
    (dehomIdeal_le_ker_chartQuotMap I i)

theorem dehomQuotMap_eq_zero {z : MvPolynomial (Fin n) k ⧸ dehomIdeal I i}
    (hz : dehomQuotMap I i z = 0) : z = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hz' : homIncl (k := k) i g ∈ sliceIdeal I i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [dehomQuotMap_mk] using hz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz'
  have hb' : dehom (k := k) i b = 0 := by
    have hb'' : b ∈ RingHom.ker (dehom (k := k) i) := by
      rw [ker_dehom]
      exact hb
    exact hb''
  have key : g = dehom (k := k) i a := by
    have hone : dehom (k := k) i (homIncl (k := k) i g) = dehom (k := k) i (a + b) := by
      rw [hab]
    rw [dehom_homIncl, map_add, hb', add_zero] at hone
    exact hone
  rw [key]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨a, ha, rfl⟩

theorem dehomQuotMap_injective : Function.Injective (dehomQuotMap I i) :=
  (injective_iff_map_eq_zero (dehomQuotMap I i)).mpr (fun z => dehomQuotMap_eq_zero I i)

theorem dehomQuotMap_surjective : Function.Surjective (dehomQuotMap I i) := by
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  have key : ∃ g : MvPolynomial (Fin n) k, homIncl (k := k) i g - f ∈ sliceIdeal I i := by
    induction f using MvPolynomial.induction_on with
    | C a =>
        refine ⟨MvPolynomial.C a, ?_⟩
        simp
    | add p q hp hq =>
        obtain ⟨gp, hgp⟩ := hp
        obtain ⟨gq, hgq⟩ := hq
        refine ⟨gp + gq, ?_⟩
        rw [map_add]
        have heq : homIncl (k := k) i gp + homIncl (k := k) i gq - (p + q)
            = (homIncl (k := k) i gp - p) + (homIncl (k := k) i gq - q) := by ring
        rw [heq]
        exact Ideal.add_mem _ hgp hgq
    | mul_X p j hp =>
        obtain ⟨gp, hgp⟩ := hp
        rcases eq_or_ne j i with hji | hj
        · rw [hji]
          refine ⟨gp, ?_⟩
          have heq : homIncl (k := k) i gp - p * MvPolynomial.X i
              = (homIncl (k := k) i gp - p)
                + p * (-(MvPolynomial.X i - 1)) := by ring
          rw [heq]
          refine Ideal.add_mem _ hgp ?_
          exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_sup_right
            (Ideal.mem_span_singleton_self _)))
        · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hj
          rw [← hl]
          refine ⟨gp * MvPolynomial.X l, ?_⟩
          have heq : homIncl (k := k) i (gp * MvPolynomial.X l)
              - p * MvPolynomial.X (i.succAbove l)
              = (homIncl (k := k) i gp - p) * MvPolynomial.X (i.succAbove l) := by
            rw [map_mul, homIncl_X]; ring
          rw [heq]
          exact Ideal.mul_mem_right _ _ hgp
  obtain ⟨g, hg⟩ := key
  refine ⟨Ideal.Quotient.mk (dehomIdeal I i) g, ?_⟩
  rw [dehomQuotMap_mk]
  have hzero : Ideal.Quotient.mk (sliceIdeal I i) (homIncl (k := k) i g)
      - Ideal.Quotient.mk (sliceIdeal I i) f = 0 := by
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  exact sub_eq_zero.mp hzero

/-- **The algebraic form of `S(Y)_{x_i} = A(Y_i)[x_i, x_i^{-1}]`**: the dehomogenized coordinate
ring of the chart is the coordinate ring of the hyperplane section `C ∩ {x_i = 1}` of the cone. -/
noncomputable def dehomQuotientEquiv :
    (MvPolynomial (Fin n) k ⧸ dehomIdeal I i) ≃+*
      (MvPolynomial (Fin (n + 1)) k ⧸ sliceIdeal I i) :=
  RingEquiv.ofBijective (dehomQuotMap I i)
    ⟨dehomQuotMap_injective I i, dehomQuotMap_surjective I i⟩

theorem ringKrullDim_dehomIdeal :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ dehomIdeal I i)
      = ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ sliceIdeal I i) :=
  ringKrullDim_eq_of_ringEquiv (dehomQuotientEquiv I i)

end DehomQuotient



/-! ## Dimension of the hyperplane section of the cone, and the affine pieces -/

section SliceDim

variable [IsAlgClosed k]

/-- **The hyperplane section `C(Y) ∩ {x_i = 1}` of the cone has dimension `dim C(Y) - 1`.**  By
Hartshorne I.1.8 every irreducible component `Z` of the section satisfies
`dim Z + 1 = dim C(Y)`; the section is the finite union of its components, so its dimension is
the common dimension of the components. -/
theorem varietyDim_slice_add_one {Y : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y)
    (i : Fin (n + 1))
    (hWne : (MvPolynomial.zeroLocus k (sliceIdeal (Proj.vanishingIdeal Y) i)).Nonempty) :
    varietyDim k (n + 1) (MvPolynomial.zeroLocus k (sliceIdeal (Proj.vanishingIdeal Y) i)) + 1
      = varietyDim k (n + 1) (Proj.cone Y) := by
  classical
  set I : Ideal (MvPolynomial (Fin (n + 1)) k) := Proj.vanishingIdeal Y with hI
  set f : MvPolynomial (Fin (n + 1)) k := MvPolynomial.X i - 1 with hf
  set W : Set (Fin (n + 1) → k) := MvPolynomial.zeroLocus k (sliceIdeal I i) with hW
  set C : Set (Fin (n + 1) → k) := Proj.cone Y with hC
  have hCeq : C = MvPolynomial.zeroLocus k I :=
    Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hYi.1
  have hCc : IsClosed C := by rw [hCeq]; exact isClosed_zeroLocus k (n + 1) I
  have hCi : IsIrreducible C := Proj.isIrreducible_cone hYc hYi
  have hzero : (0 : Fin (n + 1) → k) ∈ C := by rw [hC]; exact Or.inl rfl
  have hWne' : W.Nonempty := hW ▸ hWne
  have hWc : IsClosed W := by rw [hW]; exact isClosed_zeroLocus k (n + 1) _
  have hfne : f ≠ 0 := by
    rw [hf]
    intro h
    have h1 : MvPolynomial.eval (0 : Fin (n + 1) → k) (MvPolynomial.X i - 1) = 0 := by
      rw [h]; simp
    simp at h1
  have hneC : ∃ y ∈ C, MvPolynomial.aeval y f ≠ 0 := by
    refine ⟨0, hzero, ?_⟩
    rw [hf, MvPolynomial.aeval_eq_eval]
    simp
  obtain ⟨D, hDfin, hDirr, hDcov, hDanti⟩ :=
    exists_antichain_irred_cover (affine_dcc (k := k) (n + 1)) hWc
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with h | h
    · rw [h, Set.sUnion_empty] at hDcov
      exact absurd (hDcov ▸ hWne') (by simp)
    · exact h
  haveI : Nonempty D := hDne.to_subtype
  haveI : Fintype D := hDfin.fintype
  have hdim : ∀ W' ∈ D, varietyDim k (n + 1) W' + 1 = varietyDim k (n + 1) C := by
    intro W' hW'D
    have hW'ic := hDirr W' hW'D
    have hW'c : IsClosed W' := hW'ic.2.1
    have hW'i : IsIrreducible W' := (isIrredClosed_iff_isIrreducible.mp hW'ic).2
    have hW'W : W' ⊆ W := hDcov ▸ Set.subset_sUnion_of_mem hW'D
    have hW'C : W' ⊆ C := by
      have h1 : W' ⊆ MvPolynomial.zeroLocus k I := by
        rw [hW, sliceIdeal_def] at hW'W
        exact hW'W.trans (MvPolynomial.zeroLocus_anti_mono le_sup_left)
      rwa [hCeq]
    have hW'f : W' ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) := by
      refine hW'W.trans ?_
      rw [hW, sliceIdeal_def]
      exact MvPolynomial.zeroLocus_anti_mono le_sup_right
    refine hartshorne_exercise_I_1_8 k (n + 1) C f hCc hCi hfne hneC W'
      hW'C hW'f hW'i hW'c ?_
    intro W'' hW''C hW''f hW''i hW''c hsub
    have hW''W : W'' ⊆ W := by
      have hmemC : ∀ x ∈ W'', x ∈ MvPolynomial.zeroLocus k I := fun x hx => by
        rw [← hCeq]; exact hW''C hx
      have hmemf : ∀ x ∈ W'', MvPolynomial.aeval x f = 0 := fun x hx =>
        (MvPolynomial.mem_zeroLocus_iff.mp (hW''f hx)) f (Ideal.mem_span_singleton_self f)
      intro x hx
      rw [hW, MvPolynomial.mem_zeroLocus_iff]
      intro g hg
      rw [sliceIdeal_def, Submodule.mem_sup] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      rw [map_add]
      have h1 : MvPolynomial.aeval x a = 0 :=
        (MvPolynomial.mem_zeroLocus_iff.mp (hmemC x hx)) a ha
      have h2 : MvPolynomial.aeval x b = 0 := by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
        rw [map_mul, hmemf x hx, zero_mul]
      rw [h1, h2, add_zero]
    have hW''sU : W'' ⊆ ⋃₀ D := by rw [← hDcov]; exact hW''W
    obtain ⟨D', hD'D, hW''D'⟩ :=
      IsIrredClosed.exists_subset_of_finite_sUnion
        ((isIrredClosed_iff_isIrreducible).mpr ⟨hW''c, hW''i⟩) hDfin
        (fun V hV => (hDirr V hV).2.1) hW''sU
    have hW'D' : W' = D' := hDanti W' hW'D D' hD'D (hsub.trans hW''D')
    rw [hW'D']
    exact hW''D'
  obtain ⟨W₀, hW₀D⟩ := hDne
  have hW₀ic := hDirr W₀ hW₀D
  have hCchain : ∀ W' ∈ D, ((irrChainDim (W' : Set (Fin (n + 1) → k)) + 1 : ℕ∞) : WithBot ℕ∞)
      = ((irrChainDim (C : Set (Fin (n + 1) → k)) : ℕ∞) : WithBot ℕ∞) := by
    intro W' hW'D
    have h := hdim W' hW'D
    rw [varietyDim_eq_coe_irrChainDim (hDirr W' hW'D).1,
      varietyDim_eq_coe_irrChainDim (Z := C) ⟨0, hzero⟩] at h
    rwa [WithBot.coe_add]
  have hsame : ∀ W' ∈ D, irrChainDim (W' : Set (Fin (n + 1) → k)) = irrChainDim W₀ := by
    intro W' hW'D
    have e : irrChainDim (W' : Set (Fin (n + 1) → k)) + 1
        = irrChainDim (C : Set (Fin (n + 1) → k)) := WithBot.coe_injective (hCchain W' hW'D)
    have e₀ : irrChainDim W₀ + 1 = irrChainDim (C : Set (Fin (n + 1) → k)) :=
      WithBot.coe_injective (hCchain W₀ hW₀D)
    refine le_antisymm ?_ ?_
    · exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (le_of_eq (e.trans e₀.symm))
    · exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (le_of_eq (e₀.trans e.symm))
  have hsup : irrChainDim (W : Set (Fin (n + 1) → k)) = irrChainDim W₀ := by
    have h1 : irrChainDim (W : Set (Fin (n + 1) → k))
        = ⨆ W' : D, irrChainDim (W' : Set (Fin (n + 1) → k)) := by
      rw [hDcov, Set.sUnion_eq_iUnion]
      exact irrChainDim_iUnion (fun W' : D => (W' : Set (Fin (n + 1) → k)))
        (fun W' => (hDirr W'.1 W'.2).2.1)
    rw [h1]
    have hconst : ∀ W' : D, irrChainDim (W' : Set (Fin (n + 1) → k)) = irrChainDim W₀ :=
      fun W' => hsame W'.1 W'.2
    simp only [hconst]
    exact iSup_const
  have hW0eq : irrChainDim W₀ + 1 = irrChainDim (C : Set (Fin (n + 1) → k)) :=
    WithBot.coe_injective (hCchain W₀ hW₀D)
  have hL : ((irrChainDim (W : Set (Fin (n + 1) → k)) : ℕ∞) : WithBot ℕ∞) + 1
      = ((irrChainDim (W : Set (Fin (n + 1) → k)) + 1 : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add]
    norm_num
  rw [varietyDim_eq_coe_irrChainDim hWne',
    varietyDim_eq_coe_irrChainDim (Z := C) ⟨0, hzero⟩, hL, hsup, hW0eq]

/-- **Hartshorne I.2.6, second conclusion**: every nonempty affine piece `Y_i = φ_i(Y ∩ U_i)` of a
projective variety has the same dimension as `Y`. -/
theorem varietyDim_affinePiece {Y : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y)
    (i : Fin (n + 1)) (hne : (affinePiece Y i).Nonempty) :
    varietyDim k n (affinePiece Y i) = ((projDim Y : ℕ∞) : WithBot ℕ∞) := by
  have hWne : (MvPolynomial.zeroLocus k (sliceIdeal (Proj.vanishingIdeal Y) i)).Nonempty := by
    obtain ⟨b, hb⟩ := hne
    refine ⟨chartPoint i b, ?_⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    have hb' : ∀ g ∈ Proj.vanishingIdeal Y, MvPolynomial.eval (chartPoint i b) g = 0 :=
      (mem_dehomIdeal_zeroLocus_iff _ i b).mp (by rw [← affinePiece_eq_zeroLocus hYc i]; exact hb)
    intro g hg
    rw [sliceIdeal_def, Submodule.mem_sup] at hg
    obtain ⟨a, ha, c, hc, rfl⟩ := hg
    rw [map_add]
    have h1 : MvPolynomial.aeval (chartPoint i b) a = 0 := by
      rw [MvPolynomial.aeval_eq_eval]; exact hb' a ha
    have h2 : MvPolynomial.aeval (chartPoint i b) c = 0 := by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
      rw [map_mul]
      have h3 : MvPolynomial.aeval (chartPoint i b)
          (MvPolynomial.X i - 1 : MvPolynomial (Fin (n + 1)) k) = 0 := by
        simp [MvPolynomial.aeval_X, chartPoint_apply_self]
      rw [h3, zero_mul]
    rw [h1, h2, add_zero]
  have h1 : varietyDim k n (affinePiece Y i)
      = varietyDim k (n + 1)
          (MvPolynomial.zeroLocus k (sliceIdeal (Proj.vanishingIdeal Y) i)) := by
    rw [affinePiece_eq_zeroLocus hYc i, varietyDim_zeroLocus, ringKrullDim_dehomIdeal,
      varietyDim_zeroLocus]
  have h2 := varietyDim_slice_add_one hYc hYi i hWne
  have h3 : varietyDim k (n + 1) (Proj.cone Y) = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1 := by
    rw [varietyDim_eq_coe_irrChainDim (Z := Proj.cone Y) ⟨0, Or.inl rfl⟩]
    show ((coneDim Y : ℕ∞) : WithBot ℕ∞) = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1
    rw [coneDim_eq_projDim_add_one hYc hYi.1]
    exact WithBot.coe_add _ _
  have h5 : varietyDim k n (affinePiece Y i) + 1 = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1 := by
    rw [h1, h2, h3]
  have h5' : ((irrChainDim (affinePiece Y i) : ℕ∞) : WithBot ℕ∞) + 1
      = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1 := by
    rw [← varietyDim_eq_coe_irrChainDim hne]
    exact h5
  have h5'' : ((irrChainDim (affinePiece Y i) + 1 : ℕ∞) : WithBot ℕ∞)
      = ((projDim Y + 1 : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add, WithBot.coe_add]
    exact h5'
  have h4 : irrChainDim (affinePiece Y i) + 1 = projDim Y + 1 := WithBot.coe_injective h5''
  have h6 : irrChainDim (affinePiece Y i) = projDim Y :=
    le_antisymm ((ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (le_of_eq h4))
      ((ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (le_of_eq h4.symm))
  rw [varietyDim_eq_coe_irrChainDim hne, h6]

/-- **Hartshorne, *Algebraic Geometry* (1977), Exercise I.2.6.**  Let `Y ⊆ P^n` be a projective
variety (a nonempty irreducible closed subset) with homogeneous coordinate ring `S(Y)`.  Then

* `dim S(Y) = dim Y + 1`, and
* `dim Y = dim Y_i` for every nonempty affine piece `Y_i = φ_i(Y ∩ U_i)`.

Here `dim Y` is `projDim Y` (chains of irreducible closed subsets), `dim S(Y)` is the Krull
dimension of `S ⧸ I(Y)`, and `dim Y_i` is `varietyDim` of the affine set `affinePiece Y i`. -/
theorem hartshorne_exercise_I_2_6 {Y : Set (Proj k n)} (hYc : IsClosed Y) (hYi : IsIrreducible Y) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y)
        = ((projDim Y : ℕ∞) : WithBot ℕ∞) + 1 ∧
      ∀ (i : Fin (n + 1)), (affinePiece Y i).Nonempty →
        varietyDim k n (affinePiece Y i) = ((projDim Y : ℕ∞) : WithBot ℕ∞) :=
  ⟨dim_homogeneousCoordinateRing hYc hYi.1, fun i h => varietyDim_affinePiece hYc hYi i h⟩

end SliceDim




/-! ## Axiom audit of the results of Exercise I.2.6 -/

#print axioms Hartshorne77.Ex_I_2_6.hartshorne_exercise_I_2_6
#print axioms Hartshorne77.Ex_I_2_6.dim_homogeneousCoordinateRing
#print axioms Hartshorne77.Ex_I_2_6.varietyDim_affinePiece
#print axioms Hartshorne77.Ex_I_2_6.varietyDim_slice_add_one
#print axioms Hartshorne77.Ex_I_2_6.affinePiece_eq_zeroLocus
#print axioms Hartshorne77.Ex_I_2_6.ringKrullDim_dehomIdeal
#print axioms Hartshorne77.Ex_I_2_6.dehomQuotientEquiv
#print axioms Hartshorne77.Ex_I_2_6.dehomQuotMap_injective
#print axioms Hartshorne77.Ex_I_2_6.dehomQuotMap_surjective
#print axioms Hartshorne77.Ex_I_2_6.eval_dehom
#print axioms Hartshorne77.Ex_I_2_6.ker_dehom
#print axioms Hartshorne77.Ex_I_2_6.sub_homIncl_dehom_mem
#print axioms Hartshorne77.Ex_I_2_6.mem_dehomIdeal_zeroLocus_iff
#print axioms Hartshorne77.Ex_I_2_6.Proj.cone_eq_zeroLocus
#print axioms Hartshorne77.Ex_I_2_6.Proj.vanishingIdeal_isPrime_of_isIrreducible
#print axioms Hartshorne77.Ex_I_2_6.coneDim_eq_projDim_add_one
#print axioms Hartshorne77.Ex_I_2_6.hartshorne_exercise_I_1_8
#print axioms Hartshorne77.Ex_I_2_6.varietyDim_zeroLocus
#print axioms Hartshorne77.Ex_I_2_6.chartMap_image_affinePiece
#print axioms Hartshorne77.Ex_I_2_6.chartMap_chartCoord
#print axioms Hartshorne77.Ex_I_2_6.chartCoord_chartMap

end Hartshorne77.Ex_I_2_6
