import Mathlib

set_option linter.dupNamespace false

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

namespace Hartshorne77.Ex_I_2_13

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

end Hartshorne77.Ex_I_2_13

/-! ## The affine cone and the vanishing ideal -/

namespace Hartshorne77.Ex_I_2_13
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

end Hartshorne77.Ex_I_2_13

/-! ## Affine dimension theory (accepted Hartshorne I.1.8 infrastructure) -/

namespace Hartshorne77.Ex_I_2_13
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










end Hartshorne77.Ex_I_2_13

namespace Hartshorne77.Ex_I_2_13

/-!
# Hartshorne (1977), Algebraic Geometry, Chapter I, Exercise 2.13

Let `Y ⊆ P^5` be the image of the 2-uple embedding of `P^2` in `P^5` (the Veronese surface).
If `Z ⊆ Y` is a closed curve (a curve is a variety of dimension 1), then there exists a
hypersurface `V ⊆ P^5` such that `V ∩ Y = Z`.

This file proves that statement for the classical point-set projective space over an
algebraically closed field, using the infrastructure of the accepted I.2.10 answer
(projective space, Zariski topology, vanishing ideals, affine cones, chain dimension).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## The Veronese (2-uple) embedding -/

/-- The exponent vectors of the six quadratic monomials in three variables, in the order
`x₀², x₀x₁, x₀x₂, x₁², x₁x₂, x₂²`. -/
noncomputable def verIdx (i : Fin 6) : Fin 3 →₀ ℕ :=
  ![Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1, Finsupp.single 1 2,
    Finsupp.single 1 1 + Finsupp.single 2 1, Finsupp.single 2 2] i

/-- Each quadratic monomial has total degree two. -/
theorem verIdx_sum (i : Fin 6) : ∑ j : Fin 3, verIdx i j = 2 := by
  fin_cases i <;> simp [verIdx, Fin.sum_univ_three]

/-- The index of the monomial `x_i * x_j`; the table is symmetric. -/
def mIdx : Fin 3 → Fin 3 → Fin 6 := ![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]]

/-- The exponent vector of `x_i * x_j` is `e_i + e_j`. -/
theorem verIdx_mIdx (i j r : Fin 3) :
    verIdx (mIdx i j) r = (if r = i then 1 else 0) + (if r = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases r <;> simp [verIdx, mIdx]

/-- The six quadratic monomials of `k[x₀,x₁,x₂]`. -/
noncomputable def quad (i : Fin 6) : MvPolynomial (Fin 3) k :=
  MvPolynomial.monomial (verIdx i) 1

/-- The 2-uple embedding on affine representatives:
`x ↦ (x₀², x₀x₁, x₀x₂, x₁², x₁x₂, x₂²)`. -/
noncomputable def ver (x : Fin 3 → k) : Fin 6 → k := fun i => ∏ j : Fin 3, x j ^ (verIdx i j)

theorem eval_quad (x : Fin 3 → k) (i : Fin 6) :
    MvPolynomial.eval x (quad (k := k) i) = ver (k := k) x i := by
  rw [quad, MvPolynomial.eval_monomial, one_mul, ver,
    Finsupp.prod_fintype _ _ (fun j => by simp)]

theorem verIdx_mIdx_self (i : Fin 3) : verIdx (mIdx i i) = Finsupp.single i 2 := by
  ext r
  rw [verIdx_mIdx, Finsupp.single_apply]
  split_ifs <;> omega

theorem verIdx_mIdx_ne {i j : Fin 3} (hij : i ≠ j) :
    verIdx (mIdx i j) = Finsupp.single i 1 + Finsupp.single j 1 := by
  ext r
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simp_all [verIdx, mIdx, Finsupp.single_apply]

theorem ver_mIdx (x : Fin 3 → k) (i j : Fin 3) : ver x (mIdx i j) = x i * x j := by
  have h : ∀ r : Fin 3, x r ^ (verIdx (mIdx i j) r) =
      (if i = r then x r else 1) * (if j = r then x r else 1) := by
    intro r
    rw [verIdx_mIdx, pow_add]
    by_cases h1 : i = r <;> by_cases h2 : j = r <;> simp [h1, h2, eq_comm]
  simp only [ver, h, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, if_true]

theorem ver_smul (c : k) (x : Fin 3 → k) : ver (c • x) = c ^ 2 • ver x := by
  funext i
  have h1 : (∏ j : Fin 3, c ^ verIdx i j) = c ^ 2 := by
    rw [Finset.prod_pow_eq_pow_sum, verIdx_sum]
  simp only [Pi.smul_apply, smul_eq_mul, ver, mul_pow, Finset.prod_mul_distrib, h1]

theorem ver_ne_zero {x : Fin 3 → k} (hx : x ≠ 0) : ver x ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  intro h
  have h1 := congrFun h (mIdx j j)
  rw [ver_mIdx] at h1
  exact hj (by simpa using h1)

/-- The Veronese map `v₂ : P² → P⁵` on projective points. -/
noncomputable def V : Proj k 2 → Proj k 5 :=
  Projectivization.lift (fun x => Proj.mk (ver (k := k) x.1) (ver_ne_zero x.2)) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t hab
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hab
      exact ha hab
    refine (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr ⟨t ^ 2, ?_⟩
    rw [hab, ver_smul])

theorem V_mk (x : Fin 3 → k) (hx : x ≠ 0) :
    V (k := k) (Proj.mk x hx) = Proj.mk (ver (k := k) x) (ver_ne_zero hx) := rfl

/-- `Y`, the Veronese surface in `P⁵`. -/
noncomputable def Y : Set (Proj k 5) := Set.range (V (k := k))

/-! ## The substitution `θ` -/

/-- The ring map sending the `i`-th coordinate of `P⁵` to the `i`-th quadratic monomial. -/
noncomputable def theta : MvPolynomial (Fin 6) k →ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.aeval (fun i : Fin 6 => quad (k := k) i)

theorem theta_X (i : Fin 6) : theta (k := k) (MvPolynomial.X i) = quad (k := k) i :=
  MvPolynomial.aeval_X _ _

/-- Evaluation commutes with `θ`: `g(v(x)) = (θ g)(x)`. -/
theorem aeval_ver (x : Fin 3 → k) (g : MvPolynomial (Fin 6) k) :
    MvPolynomial.aeval (ver (k := k) x) g = MvPolynomial.aeval x (theta (k := k) g) := by
  have h : (MvPolynomial.aeval x).comp (theta (k := k)) =
      MvPolynomial.aeval (ver (k := k) x) := by
    rw [theta, MvPolynomial.comp_aeval]
    congr 1
    funext i
    rw [MvPolynomial.aeval_eq_eval, eval_quad]
  rw [← h]
  rfl


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

theorem theta_mul (g h : MvPolynomial (Fin 6) k) :
    theta (k := k) (g * h) = theta (k := k) g * theta (k := k) h :=
  map_mul _ _ _

theorem theta_C (a : k) : theta (k := k) (MvPolynomial.C a) = MvPolynomial.C a :=
  (theta (k := k)).commutes a

/-- `ver_mIdx` in the shape of the representative vectors of `P²`. -/
theorem ver_mIdx_2 (x : Fin (2 + 1) → k) (i j : Fin (2 + 1)) :
    ver (k := k) x (mIdx i j) = x i * x j := ver_mIdx x i j

/-! ## Injectivity of the Veronese map -/

theorem V_injective : Function.Injective (V (k := k)) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | h x hx =>
    induction q using Projectivization.ind with
    | h y hy =>
      rw [V_mk, V_mk] at hpq
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hpq
      obtain ⟨j, hj⟩ : ∃ j : Fin 3, y j ≠ 0 := by
        by_contra h
        push Not at h
        exact hy (funext h)
      have hxj : x j ≠ 0 := by
        have h := congrFun ha (mIdx j j)
        simp only [Pi.smul_apply, smul_eq_mul, ver_mIdx_2] at h
        intro h0
        rw [h0, mul_zero] at h
        have ha0 : a = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · rcases mul_eq_zero.mp h' with h'' | h''
            · exact absurd h'' hj
            · exact absurd h'' hj
        exact ver_ne_zero (k := k) hx (by rw [← ha, ha0, zero_smul])
      refine (Projectivization.mk_eq_mk_iff' k x y hx hy).mpr ⟨a * y j / x j, ?_⟩
      funext k'
      have hk := congrFun ha (mIdx j k')
      simp only [Pi.smul_apply, smul_eq_mul, ver_mIdx_2] at hk
      have hgoal : a * y j / x j * y k' = x k' := by
        rw [div_mul_eq_mul_div, div_eq_iff hxj]
        calc a * y j * y k' = a * (y j * y k') := by rw [mul_assoc]
          _ = x j * x k' := hk
          _ = x k' * x j := mul_comm _ _
      simpa [Pi.smul_apply, smul_eq_mul] using hgoal

/-! ## Even-degree forms are polynomials in the quadratic monomials -/

/-- The quadratic monomial at a diagonal index. -/
theorem quad_self (i : Fin 3) :
    quad (k := k) (mIdx i i) = MvPolynomial.monomial (Finsupp.single i 2) 1 := by
  rw [quad, verIdx_mIdx_self]

/-- The quadratic monomial at a mixed index. -/
theorem quad_ne {i j : Fin 3} (hij : i ≠ j) :
    quad (k := k) (mIdx i j) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
  rw [quad, verIdx_mIdx_ne hij]

/-- Any exponent vector of total degree at least two can be reduced by a quadratic monomial. -/
theorem exists_split_monomial (m : Fin 3 →₀ ℕ) (h : 2 ≤ Finsupp.degree m) :
    (∃ i : Fin 3, 2 ≤ m i) ∨ (∃ i j : Fin 3, i ≠ j ∧ 1 ≤ m i ∧ 1 ≤ m j) := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have h3 : ∀ i j : Fin 3, i ≠ j → m i = 0 ∨ m j = 0 := by
    intro i j hij
    rcases Nat.eq_zero_or_pos (m i) with hi | hi
    · exact Or.inl hi
    · rcases Nat.eq_zero_or_pos (m j) with hj | hj
      · exact Or.inr hj
      · have hlt : m j < 1 := h2 i j hij hi
        omega
  have hle : ∀ i : Fin 3, m i ≤ 1 := by
    intro i
    have := h1 i
    omega
  have hd : Finsupp.degree m = ∑ i : Fin 3, m i := Finsupp.degree_eq_sum m
  rw [hd, Fin.sum_univ_three] at h
  rcases h3 0 1 (by decide) with h01 | h01 <;>
    rcases h3 0 2 (by decide) with h02 | h02 <;>
    rcases h3 1 2 (by decide) with h12 | h12 <;>
    have h0 := hle 0 <;> have h1' := hle 1 <;> have h2' := hle 2 <;> omega

/-- A monomial of even degree `2d` is a product of `d` quadratic monomials. -/
theorem exists_homog_theta_monomial : ∀ (d : ℕ) (m : Fin 3 →₀ ℕ),
    Finsupp.degree m = 2 * d →
    ∃ g : MvPolynomial (Fin 6) k,
      g.IsHomogeneous d ∧ theta (k := k) g = MvPolynomial.monomial m 1
  | 0, m, hm => by
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hm
    refine ⟨1, ?_, ?_⟩
    · simpa using (MvPolynomial.isHomogeneous_one (σ := Fin 6) (R := k))
    · rw [hm0, map_one]
      simp
  | (d + 1), m, hm => by
    have hdeg : Finsupp.degree m = 2 * d + 2 := by rw [hm]; ring
    have h2 : 2 ≤ Finsupp.degree m := by omega
    rcases exists_split_monomial m h2 with ⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩
    · -- one exponent is at least two
      set m' : Fin 3 →₀ ℕ := Finsupp.single i (m i - 2) + Finsupp.erase i m with hm'_def
      have hmeq : m = Finsupp.single i 2 + m' := by
        ext r
        simp only [hm'_def, Finsupp.add_apply]
        by_cases hri : r = i
        · obtain rfl := hri
          simp [Finsupp.erase_same]
          omega
        · rw [Finsupp.single_eq_of_ne hri, Finsupp.single_eq_of_ne hri, Finsupp.erase_ne hri]
          simp
      have hdeg' : Finsupp.degree m' = 2 * d := by
        have h := congrArg Finsupp.degree hmeq
        rw [map_add, Finsupp.degree_single, hdeg] at h
        omega
      obtain ⟨g', hg'hom, hg'eq⟩ := exists_homog_theta_monomial d m' hdeg'
      refine ⟨MvPolynomial.X (mIdx i i) * g', ?_, ?_⟩
      · have hX : (MvPolynomial.X (mIdx i i) : MvPolynomial (Fin 6) k).IsHomogeneous 1 :=
          MvPolynomial.isHomogeneous_X _ _
        simpa [Nat.add_comm] using hX.mul hg'hom
      · rw [theta_mul, theta_X, hg'eq, quad_self, MvPolynomial.monomial_mul, one_mul, hmeq]
    · -- two exponents are at least one
      set m' : Fin 3 →₀ ℕ := Finsupp.single i (m i - 1) + Finsupp.single j (m j - 1) +
        Finsupp.erase i (Finsupp.erase j m) with hm'_def
      have hmeq : m = Finsupp.single i 1 + Finsupp.single j 1 + m' := by
        ext r
        simp only [hm'_def, Finsupp.add_apply]
        by_cases hri : r = i
        · obtain rfl := hri
          simp [Finsupp.single_eq_of_ne hij, Finsupp.erase_same]
          omega
        · by_cases hrj : r = j
          · obtain rfl := hrj
            simp [Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.erase_ne (Ne.symm hij),
              Finsupp.erase_same]
            omega
          · rw [Finsupp.single_eq_of_ne hri, Finsupp.single_eq_of_ne hrj,
              Finsupp.single_eq_of_ne hri, Finsupp.single_eq_of_ne hrj,
              Finsupp.erase_ne hri, Finsupp.erase_ne hrj]
            simp
      have hdeg' : Finsupp.degree m' = 2 * d := by
        have h := congrArg Finsupp.degree hmeq
        rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single, hdeg] at h
        omega
      obtain ⟨g', hg'hom, hg'eq⟩ := exists_homog_theta_monomial d m' hdeg'
      refine ⟨MvPolynomial.X (mIdx i j) * g', ?_, ?_⟩
      · have hX : (MvPolynomial.X (mIdx i j) : MvPolynomial (Fin 6) k).IsHomogeneous 1 :=
          MvPolynomial.isHomogeneous_X _ _
        simpa [Nat.add_comm] using hX.mul hg'hom
      · rw [theta_mul, theta_X, hg'eq, quad_ne hij, MvPolynomial.monomial_mul, one_mul, hmeq]

/-- Every homogeneous form of degree `2d` is `θ` of a homogeneous form of degree `d`. -/
theorem exists_homog_theta_of_even (F : MvPolynomial (Fin 3) k) (d : ℕ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ g : MvPolynomial (Fin 6) k, g.IsHomogeneous d ∧ theta (k := k) g = F := by
  classical
  have hmem : ∀ v ∈ F.support, Finsupp.degree v = 2 * d := by
    intro v hv
    have hdeg := hF.degree_eq_sum_deg_support hv
    have hsupp : (∑ i : Fin 3, v i) = ∑ i ∈ v.support, v i := by
      rw [Finset.sum_subset (Finset.subset_univ v.support) (fun i _ hi => by
        simp [Finsupp.notMem_support_iff.mp hi])]
    rw [Finsupp.degree_eq_sum, hsupp, ← hdeg]
  have hex : ∀ v ∈ F.support, ∃ g : MvPolynomial (Fin 6) k,
      g.IsHomogeneous d ∧ theta (k := k) g = MvPolynomial.monomial v 1 :=
    fun v hv => exists_homog_theta_monomial d v (hmem v hv)
  choose G hGhom hGeq using hex
  set gfun : (Fin 3 →₀ ℕ) → MvPolynomial (Fin 6) k :=
    fun v => if hv : v ∈ F.support then G v hv else 0 with hgfun
  refine ⟨∑ v ∈ F.support, MvPolynomial.C (MvPolynomial.coeff v F) * gfun v, ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum F.support
      (fun v => MvPolynomial.C (MvPolynomial.coeff v F) * gfun v) d ?_
    intro v hv
    rw [show gfun v = G v hv from dif_pos hv]
    exact (hGhom v hv).C_mul _
  · rw [map_sum]
    have hterm : ∀ v ∈ F.support,
        theta (k := k) (MvPolynomial.C (MvPolynomial.coeff v F) * gfun v) =
          MvPolynomial.monomial v (MvPolynomial.coeff v F) := by
      intro v hv
      rw [show gfun v = G v hv from dif_pos hv, theta_mul, theta_C, hGeq v hv,
        MvPolynomial.C_mul_monomial, mul_one]
    rw [Finset.sum_congr rfl hterm]
    exact F.as_sum.symm

/-- The square of a homogeneous form of degree `e` is `θ` of a homogeneous form of degree `e`. -/
theorem exists_theta_sq (f : MvPolynomial (Fin 3) k) {e : ℕ} (hf : f.IsHomogeneous e) :
    ∃ g : MvPolynomial (Fin 6) k, g.IsHomogeneous e ∧ theta (k := k) g = f ^ 2 := by
  have h2 : (f ^ 2).IsHomogeneous (2 * e) := by
    have h := hf.pow 2
    simpa [Nat.mul_comm] using h
  exact exists_homog_theta_of_even (f ^ 2) e h2



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## `θ` preserves homogeneity -/

theorem quad_isHomogeneous (i : Fin 6) : (quad (k := k) i).IsHomogeneous 2 := by
  rw [quad]
  exact MvPolynomial.isHomogeneous_monomial 1 (by
    rw [Finsupp.degree_eq_sum]
    exact verIdx_sum i)

theorem theta_isHomogeneous {g : MvPolynomial (Fin 6) k} {d : ℕ} (hg : g.IsHomogeneous d) :
    (theta (k := k) g).IsHomogeneous (2 * d) := by
  have h := hg.aeval (fun i : Fin 6 => quad (k := k) i) (fun i => quad_isHomogeneous i)
  simpa [theta] using h

/-- The induced map of sets of homogeneous polynomials. -/
noncomputable def thetaH (g : Proj.HomogPoly k 5) : Proj.HomogPoly k 2 :=
  ⟨theta (k := k) g.1, by
    obtain ⟨d, hd⟩ := g.2
    exact ⟨2 * d, theta_isHomogeneous hd⟩⟩

theorem thetaH_val (g : Proj.HomogPoly k 5) : (thetaH (k := k) g).1 = theta (k := k) g.1 := rfl

/-! ## Vanishing of `g` at `V x` is vanishing of `θ g` at `x` -/

theorem eval_ver (x : Fin 3 → k) (g : MvPolynomial (Fin 6) k) :
    MvPolynomial.eval (ver (k := k) x) g = MvPolynomial.eval x (theta (k := k) g) := by
  simpa only [MvPolynomial.aeval_eq_eval] using aeval_ver (k := k) x g

theorem isZeroAt_V_iff {g : MvPolynomial (Fin 6) k} {d : ℕ} (hg : g.IsHomogeneous d)
    {x : Proj k 2} :
    Proj.IsZeroAt g (V (k := k) x) ↔ Proj.IsZeroAt (theta (k := k) g) x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [V_mk, Proj.isZeroAt_mk_iff hg, Proj.isZeroAt_mk_iff (theta_isHomogeneous hg)]
    exact eval_ver (k := k) v g ▸ Iff.rfl

/-! ## Continuity of the Veronese map -/

theorem continuous_V : Continuous (V (k := k)) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨S, rfl⟩ := (Proj.isClosed_iff Z).mp hZ
  have hpre : V (k := k) ⁻¹' Proj.zeroLocus S = Proj.zeroLocus (thetaH (k := k) '' S) := by
    ext x
    rw [Set.mem_preimage, Proj.mem_zeroLocus_iff, Proj.mem_zeroLocus_iff]
    constructor
    · intro h f hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mp (h g hg)
    · intro h g hg
      exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr
        (h (thetaH (k := k) g) ⟨g, hg, rfl⟩)
  rw [hpre]
  exact Proj.isClosed_of_isProjClosed (Proj.isProjClosed_zeroLocus _)



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## The image of a closed set under the Veronese map -/

/-- The set of homogeneous forms `g` on `P⁵` whose pullback vanishes on `X`. -/
noncomputable def thetaSet (X : Set (Proj k 2)) : Set (Proj.HomogPoly k 5) :=
  {g | ∀ x ∈ X, Proj.IsZeroAt (theta (k := k) g.1) x}

theorem mem_thetaSet {X : Set (Proj k 2)} {g : Proj.HomogPoly k 5} :
    g ∈ thetaSet (k := k) X ↔ ∀ x ∈ X, Proj.IsZeroAt (theta (k := k) g.1) x := Iff.rfl

/-- A form vanishing on a closed set vanishes at each of its points. -/
theorem isZeroAt_of_mem_vanishingForms {X : Set (Proj k 2)} (hX : IsClosed X)
    {f : Proj.HomogPoly k 2} (hf : f ∈ Proj.vanishingForms X) {x : Proj k 2} (hx : x ∈ X) :
    Proj.IsZeroAt f.1 x := by
  have h1 : x ∈ Proj.zeroLocus (Proj.vanishingForms X) := by
    rw [Proj.zeroLocus_vanishingForms_eq X hX]; exact hx
  exact (Proj.mem_zeroLocus_iff.mp h1) f hf

theorem isZeroAt_mul_iff {f : MvPolynomial (Fin 3) k} {x : Proj k 2} :
    Proj.IsZeroAt (f * f) x ↔ Proj.IsZeroAt f x := by
  rw [Proj.IsZeroAt, map_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact h'
  · intro h; rw [h, zero_mul]

theorem image_closed {X : Set (Proj k 2)} (hX : IsClosed X) :
    V (k := k) '' X = Proj.zeroLocus (thetaSet (k := k) X) ∩ Y (k := k) := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    intro g hg
    exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr (hg x hx)
  · rintro ⟨hzT, x, rfl⟩
    by_contra hx
    have hxX : x ∉ X := fun h => hx ⟨x, h, rfl⟩
    have hx' : x ∉ Proj.zeroLocus (Proj.vanishingForms X) := by
      rwa [Proj.zeroLocus_vanishingForms_eq X hX]
    rw [Proj.mem_zeroLocus_iff] at hx'
    push Not at hx'
    obtain ⟨f, hf, hfx⟩ := hx'
    obtain ⟨d, hd⟩ := f.2
    obtain ⟨g, hg_hom, hg_eq⟩ := exists_theta_sq (k := k) f.1 (e := d) hd
    have hgT : (⟨g, d, hg_hom⟩ : Proj.HomogPoly k 5) ∈ thetaSet (k := k) X := by
      intro y hy
      have h1 : Proj.IsZeroAt f.1 y := isZeroAt_of_mem_vanishingForms hX hf hy
      have h2 : theta (k := k) g = f.1 * f.1 := by rw [hg_eq, pow_two]
      rw [h2]
      exact isZeroAt_mul_iff.mpr h1
    have h3 : Proj.IsZeroAt g (V (k := k) x) := hzT ⟨g, d, hg_hom⟩ hgT
    have h4 : Proj.IsZeroAt (theta (k := k) g) x :=
      (isZeroAt_V_iff (k := k) (d := d) hg_hom).mp h3
    refine hfx (isZeroAt_mul_iff.mp ?_)
    have h4' : Proj.IsZeroAt (f.1 ^ 2) x := by
      rw [← hg_eq]
      exact h4
    rwa [pow_two] at h4' 

/-! ## Preimages and images of closed sets -/

theorem preimage_image (X : Set (Proj k 2)) : V (k := k) ⁻¹' (V (k := k) '' X) = X := by
  ext x
  exact ⟨fun h => by
    obtain ⟨y, hy, hxy⟩ := h
    rwa [← V_injective (k := k) hxy], fun h => ⟨x, h, rfl⟩⟩

theorem image_preimage {W : Set (Proj k 5)} (hW : W ⊆ Y (k := k)) :
    V (k := k) '' (V (k := k) ⁻¹' W) = W := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hW hy
    exact ⟨x, hy, rfl⟩

theorem mem_zeroLocus_thetaSet_iff {X : Set (Proj k 2)} (hX : IsClosed X) {x : Proj k 2} :
    V (k := k) x ∈ Proj.zeroLocus (thetaSet (k := k) X) ↔ x ∈ X := by
  constructor
  · intro hx
    by_contra hxX
    have hx' : x ∉ Proj.zeroLocus (Proj.vanishingForms X) := by
      rwa [Proj.zeroLocus_vanishingForms_eq X hX]
    rw [Proj.mem_zeroLocus_iff] at hx'
    push Not at hx'
    obtain ⟨f, hf, hfx⟩ := hx'
    obtain ⟨d, hd⟩ := f.2
    obtain ⟨g, hg_hom, hg_eq⟩ := exists_theta_sq (k := k) f.1 (e := d) hd
    have hgT : (⟨g, d, hg_hom⟩ : Proj.HomogPoly k 5) ∈ thetaSet (k := k) X := by
      intro y hy
      have h1 : Proj.IsZeroAt f.1 y := isZeroAt_of_mem_vanishingForms hX hf hy
      have h2 : theta (k := k) g = f.1 * f.1 := by rw [hg_eq, pow_two]
      rw [h2]
      exact isZeroAt_mul_iff.mpr h1
    have h3 : Proj.IsZeroAt g (V (k := k) x) := hx ⟨g, d, hg_hom⟩ hgT
    have h4 : Proj.IsZeroAt (theta (k := k) g) x :=
      (isZeroAt_V_iff (k := k) (d := d) hg_hom).mp h3
    refine hfx (isZeroAt_mul_iff.mp ?_)
    have h4' : Proj.IsZeroAt (f.1 ^ 2) x := by
      rw [← hg_eq]
      exact h4
    rwa [pow_two] at h4'
  · intro hx g hg
    exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr (hg x hx)

theorem image_subset_zeroLocus {X : Set (Proj k 2)} :
    V (k := k) '' X ⊆ Proj.zeroLocus (thetaSet (k := k) X) := by
  rintro y ⟨x, hx, rfl⟩ g hg
  exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr (hg x hx)

theorem closure_image_inter {X : Set (Proj k 2)} (hX : IsClosed X) :
    closure (V (k := k) '' X) ∩ Y (k := k) = V (k := k) '' X := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hy1, hy2⟩
    have h1 : y ∈ Proj.zeroLocus (thetaSet (k := k) X) :=
      closure_minimal (image_subset_zeroLocus (k := k))
        (Proj.isClosed_of_isProjClosed (Proj.isProjClosed_zeroLocus _)) hy1
    obtain ⟨x, rfl⟩ := hy2
    exact ⟨x, (mem_zeroLocus_thetaSet_iff (k := k) hX).mp h1, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨subset_closure ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩

/-- The preimage of an irreducible closed subset of `Y` is irreducible. -/
theorem isIrreducible_preimage_image {W : Set (Proj k 5)} (hWcl : IsClosed W)
    (hWirr : IsIrreducible W) (hWY : W ⊆ Y (k := k)) :
    IsIrreducible (V (k := k) ⁻¹' W) := by
  have hne : (V (k := k) ⁻¹' W).Nonempty := by
    obtain ⟨y, hy⟩ := hWirr.1
    obtain ⟨x, rfl⟩ := hWY hy
    exact ⟨x, hy⟩
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have hcover : W ⊆ Proj.zeroLocus (thetaSet (k := k) A) ∪
      Proj.zeroLocus (thetaSet (k := k) B) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hWY hy
    rcases hsub hy with hxA | hxB
    · left
      intro g hg
      exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr (hg x hxA)
    · right
      intro g hg
      exact (isZeroAt_V_iff (k := k) (d := g.2.choose) g.2.choose_spec).mpr (hg x hxB)
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hWirr.2) _ _
    (Proj.isClosed_of_isProjClosed (Proj.isProjClosed_zeroLocus _))
    (Proj.isClosed_of_isProjClosed (Proj.isProjClosed_zeroLocus _)) hcover with h | h
  · left
    intro x hx
    have h1 : V (k := k) x ∈ Proj.zeroLocus (thetaSet (k := k) A) := h hx
    exact (mem_zeroLocus_thetaSet_iff (k := k) hA).mp h1
  · right
    intro x hx
    have h1 : V (k := k) x ∈ Proj.zeroLocus (thetaSet (k := k) B) := h hx
    exact (mem_zeroLocus_thetaSet_iff (k := k) hB).mp h1

/-! ## Dimensions agree along the Veronese map -/

theorem irrChainDim_preimage_V {Z : Set (Proj k 5)} (hZcl : IsClosed Z) (hZY : Z ⊆ Y (k := k)) :
    irrChainDim (V (k := k) ⁻¹' Z) = irrChainDim Z := by
  refine le_antisymm ?_ ?_
  · rw [irrChainDim_le_iff]
    intro l
    have hmap : ∀ W : {W : Set (Proj k 2) // W ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible W ∧ IsClosed W},
        closure (V (k := k) '' W.1) ⊆ Z ∧ IsIrreducible (closure (V (k := k) '' W.1)) ∧
          IsClosed (closure (V (k := k) '' W.1)) := by
      rintro ⟨W, hWZ, hirr, hcl⟩
      refine ⟨?_, ?_, isClosed_closure⟩
      · refine closure_minimal ?_ hZcl
        rintro y ⟨x, hx, rfl⟩
        exact hWZ hx
      · exact (hirr.image (V (k := k)) continuous_V.continuousOn).closure
    have hstrict : StrictMono (fun W : {W : Set (Proj k 2) //
        W ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible W ∧ IsClosed W} =>
        (⟨closure (V (k := k) '' W.1), hmap W⟩ :
          {W : Set (Proj k 5) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W})) := by
      intro a b hab
      have hab' : a.1 ⊂ b.1 := hab
      refine ⟨closure_mono (Set.image_mono hab'.1), ?_⟩
      intro hsub
      have h2 : b.1 ⊆ a.1 := by
        intro x hx
        have hx'' : V (k := k) x ∈ closure (V (k := k) '' b.1) :=
          subset_closure ⟨x, hx, rfl⟩
        have hx3 : V (k := k) x ∈ closure (V (k := k) '' a.1) := hsub hx''
        have hx4 : V (k := k) x ∈ V (k := k) '' a.1 := by
          rw [← closure_image_inter (k := k) (X := a.1) a.2.2.2]
          exact ⟨hx3, ⟨x, rfl⟩⟩
        obtain ⟨y, hy, hxy⟩ := hx4
        rw [V_injective (k := k) hxy] at hy
        exact hy
      exact hab'.2 h2
    let l' : LTSeries {W : Set (Proj k 5) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} :=
      l.map (fun W => ⟨closure (V (k := k) '' W.1), hmap W⟩) hstrict
    calc (l.length : ℕ∞) = (l'.length : ℕ∞) := by simp [l']
      _ ≤ irrChainDim Z := by
        rw [irrChainDim]
        exact le_iSup (fun l'' : LTSeries {W : Set (Proj k 5) //
          W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} => (l''.length : ℕ∞)) l'
  · rw [irrChainDim_le_iff]
    intro l
    have hmap : ∀ W : {W : Set (Proj k 5) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W},
        V (k := k) ⁻¹' W.1 ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible (V (k := k) ⁻¹' W.1) ∧
          IsClosed (V (k := k) ⁻¹' W.1) := by
      rintro ⟨W, hWZ, hirr, hcl⟩
      exact ⟨Set.preimage_mono hWZ,
        isIrreducible_preimage_image hcl hirr (fun y hy => hZY (hWZ hy)),
        hcl.preimage continuous_V⟩
    have hstrict : StrictMono (fun W : {W : Set (Proj k 5) //
        W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} =>
        (⟨V (k := k) ⁻¹' W.1, hmap W⟩ :
          {W : Set (Proj k 2) // W ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible W ∧ IsClosed W})) := by
      intro a b hab
      have hab' : a.1 ⊂ b.1 := hab
      refine ⟨Set.preimage_mono hab'.1, ?_⟩
      intro hsub
      have h2 : b.1 ⊆ a.1 := by
        intro y hy
        have h1 : y ∈ V (k := k) '' (V (k := k) ⁻¹' b.1) := by
          rw [image_preimage (k := k) (hW := fun y hy => hZY (b.2.1 hy))]
          exact hy
        obtain ⟨x, hx, rfl⟩ := h1
        have hx' : x ∈ V (k := k) ⁻¹' a.1 := hsub hx
        rw [← image_preimage (k := k) (W := a.1) (fun y hy => hZY (a.2.1 hy))]
        exact ⟨x, hx', rfl⟩
      exact hab'.2 h2
    let l' : LTSeries {W : Set (Proj k 2) // W ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible W ∧ IsClosed W} :=
      l.map (fun W => ⟨V (k := k) ⁻¹' W.1, hmap W⟩) hstrict
    calc (l.length : ℕ∞) = (l'.length : ℕ∞) := by simp [l']
      _ ≤ irrChainDim (V (k := k) ⁻¹' Z) := by
        rw [irrChainDim]
        exact le_iSup (fun l'' : LTSeries {W : Set (Proj k 2) //
          W ⊆ V (k := k) ⁻¹' Z ∧ IsIrreducible W ∧ IsClosed W} => (l''.length : ℕ∞)) l'

theorem projDim_preimage_V {Z : Set (Proj k 5)} (hZcl : IsClosed Z) (hZY : Z ⊆ Y (k := k)) :
    projDim (V (k := k) ⁻¹' Z) = projDim Z :=
  irrChainDim_preimage_V hZcl hZY



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

section Components
variable {σ : Type*} [DecidableEq σ]

/-- The lowest-degree component of a product, under lower bounds for the support degrees. -/
theorem coeff_mul_lowest {φ ψ : MvPolynomial σ k} {a b : ℕ}
    (hφ : ∀ m ∈ φ.support, a ≤ Finsupp.degree m)
    (hψ : ∀ m ∈ ψ.support, b ≤ Finsupp.degree m)
    {n : σ →₀ ℕ} (hn : Finsupp.degree n = a + b) :
    MvPolynomial.coeff n (φ * ψ) =
      MvPolynomial.coeff n (MvPolynomial.homogeneousComponent a φ *
        MvPolynomial.homogeneousComponent b ψ) := by
  have hzeroφ : ∀ m : σ →₀ ℕ, Finsupp.degree m < a → MvPolynomial.coeff m φ = 0 := by
    intro m hm
    by_contra h
    exact absurd (hφ m (MvPolynomial.mem_support_iff.mpr h)) (by omega)
  have hzeroψ : ∀ m : σ →₀ ℕ, Finsupp.degree m < b → MvPolynomial.coeff m ψ = 0 := by
    intro m hm
    by_contra h
    exact absurd (hψ m (MvPolynomial.mem_support_iff.mpr h)) (by omega)
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e.1 + e.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp he
  have hdeg : Finsupp.degree e.1 + Finsupp.degree e.2 = a + b := by
    rw [← map_add, he']
    exact hn
  by_cases h1 : Finsupp.degree e.1 = a
  · rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent,
      if_pos h1, if_pos (show Finsupp.degree e.2 = b by omega)]
  · have h2 : ¬ Finsupp.degree e.2 = b := by omega
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent,
      if_neg h1, if_neg h2]
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · rw [hzeroφ e.1 hlt]
      simp
    · rw [hzeroψ e.2 (by omega)]
      simp

/-- The top-degree component of a product, under upper bounds for the support degrees. -/
theorem coeff_mul_top {φ ψ : MvPolynomial σ k} {a b : ℕ}
    (hφ : ∀ m ∈ φ.support, Finsupp.degree m ≤ a)
    (hψ : ∀ m ∈ ψ.support, Finsupp.degree m ≤ b)
    {n : σ →₀ ℕ} (hn : Finsupp.degree n = a + b) :
    MvPolynomial.coeff n (φ * ψ) =
      MvPolynomial.coeff n (MvPolynomial.homogeneousComponent a φ *
        MvPolynomial.homogeneousComponent b ψ) := by
  have hzeroφ : ∀ m : σ →₀ ℕ, a < Finsupp.degree m → MvPolynomial.coeff m φ = 0 := by
    intro m hm
    by_contra h
    exact absurd (hφ m (MvPolynomial.mem_support_iff.mpr h)) (by omega)
  have hzeroψ : ∀ m : σ →₀ ℕ, b < Finsupp.degree m → MvPolynomial.coeff m ψ = 0 := by
    intro m hm
    by_contra h
    exact absurd (hψ m (MvPolynomial.mem_support_iff.mpr h)) (by omega)
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e.1 + e.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp he
  have hdeg : Finsupp.degree e.1 + Finsupp.degree e.2 = a + b := by
    rw [← map_add, he']
    exact hn
  by_cases h1 : Finsupp.degree e.1 = a
  · rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent,
      if_pos h1, if_pos (show Finsupp.degree e.2 = b by omega)]
  · have h2 : ¬ Finsupp.degree e.2 = b := by omega
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent,
      if_neg h1, if_neg h2]
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · rw [hzeroψ e.2 (by omega)]
      simp
    · rw [hzeroφ e.1 hgt]
      simp

end Components



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The smallest degree of a monomial occurring in a nonzero polynomial. -/
noncomputable def lowDeg (φ : MvPolynomial (Fin 6) k) (h : φ ≠ 0) : ℕ :=
  (φ.support.image Finsupp.degree).min' (by
    refine Finset.image_nonempty.mpr ?_
    by_contra h'
    exact h (by
      have h2 : φ.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
      exact MvPolynomial.as_sum φ ▸ by simp [h2]))

theorem lowDeg_le {φ : MvPolynomial (Fin 6) k} (h : φ ≠ 0) {m : Fin 6 →₀ ℕ}
    (hm : m ∈ φ.support) : lowDeg φ h ≤ Finsupp.degree m :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

theorem coeff_eq_zero_of_lt_lowDeg {φ : MvPolynomial (Fin 6) k} (h : φ ≠ 0) {m : Fin 6 →₀ ℕ}
    (hm : Finsupp.degree m < lowDeg φ h) : MvPolynomial.coeff m φ = 0 := by
  by_contra hc
  exact absurd (lowDeg_le h (MvPolynomial.mem_support_iff.mpr hc)) (by omega)

/-- Splitting off the lowest homogeneous components of the two factors of a homogeneous product. -/
theorem split_lowest {g φ ψ : MvPolynomial (Fin 6) k} {d : ℕ} (hg : g.IsHomogeneous d)
    (hgf : g = φ * ψ) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ∃ (a b : ℕ) (A B : MvPolynomial (Fin 6) k),
      A.IsHomogeneous a ∧ B.IsHomogeneous b ∧ A * B = g ∧ A ≠ 0 ∧ B ≠ 0 ∧
        a + b = d ∧ A ∣ g ∧ B ∣ g := by
  set a := lowDeg φ hφ with ha
  set b := lowDeg ψ hψ with hb
  set A := MvPolynomial.homogeneousComponent a φ with hA
  set B := MvPolynomial.homogeneousComponent b ψ with hB
  have hAle : ∀ m ∈ φ.support, a ≤ Finsupp.degree m := fun m hm => lowDeg_le hφ hm
  have hBle : ∀ m ∈ ψ.support, b ≤ Finsupp.degree m := fun m hm => lowDeg_le hψ hm
  have hAhom : A.IsHomogeneous a := MvPolynomial.homogeneousComponent_isHomogeneous a φ
  have hBhom : B.IsHomogeneous b := MvPolynomial.homogeneousComponent_isHomogeneous b ψ
  have hAne : A ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hma⟩ := Finset.mem_image.mp (Finset.min'_mem (φ.support.image Finsupp.degree) _)
    have h1 : m ∈ (MvPolynomial.homogeneousComponent a φ).support := by
      rw [MvPolynomial.support_homogeneousComponent]
      exact Finset.mem_filter.mpr ⟨hm, hma⟩
    rw [← hA, h0] at h1
    simp at h1
  have hBne : B ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hma⟩ := Finset.mem_image.mp (Finset.min'_mem (ψ.support.image Finsupp.degree) _)
    have h1 : m ∈ (MvPolynomial.homogeneousComponent b ψ).support := by
      rw [MvPolynomial.support_homogeneousComponent]
      exact Finset.mem_filter.mpr ⟨hm, hma⟩
    rw [← hB, h0] at h1
    simp at h1
  have hABne : A * B ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hAne h'
    · exact hBne h'

  have hABhom : (A * B).IsHomogeneous (a + b) := hAhom.mul hBhom
  -- the degrees add up to `d`
  have hab : a + b = d := by
    obtain ⟨m, hm⟩ : (A * B).support.Nonempty := by
      by_contra h'
      exact hABne (by
        have h2 : (A * B).support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
        exact MvPolynomial.as_sum (A * B) ▸ by simp [h2])
    have hmdeg : Finsupp.degree m = a + b := by
      rw [Finsupp.degree_apply]
      exact (hABhom.degree_eq_sum_deg_support hm).symm
    have h1 : MvPolynomial.coeff m (A * B) = MvPolynomial.coeff m (φ * ψ) :=
      (coeff_mul_lowest hAle hBle (n := m) hmdeg).symm
    rw [← hgf] at h1
    have h2 : MvPolynomial.coeff m g ≠ 0 := by
      rw [← h1]
      exact MvPolynomial.mem_support_iff.mp hm
    by_contra hcon
    have h4 : ¬ Finsupp.degree m = d := by
      rw [hmdeg]
      exact hcon
    exact h2 (hg.coeff_eq_zero h4)
  have hAB : A * B = g := by
    ext n
    by_cases hn : Finsupp.degree n = d
    · have h2 : MvPolynomial.coeff n (A * B) = MvPolynomial.coeff n (φ * ψ) :=
        (coeff_mul_lowest hAle hBle (n := n) (by rw [hab]; exact hn)).symm
      rw [hgf]
      exact h2
    · have h1 : MvPolynomial.coeff n (A * B) = 0 :=
        hABhom.coeff_eq_zero (by rw [hab]; exact hn)
      have h2 : MvPolynomial.coeff n g = 0 := hg.coeff_eq_zero hn
      rw [h1, h2]
  refine ⟨a, b, A, B, hAhom, hBhom, hAB, hAne, hBne, hab, ⟨B, hAB.symm⟩, ⟨A, ?_⟩⟩
  rw [mul_comm, ← hAB]



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Splitting off the top homogeneous components of the two factors of a homogeneous product. -/
theorem split_highest {g φ ψ : MvPolynomial (Fin 6) k} {d : ℕ} (hg : g.IsHomogeneous d)
    (hgf : g = φ * ψ) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ∃ (a b : ℕ) (A B : MvPolynomial (Fin 6) k),
      A.IsHomogeneous a ∧ B.IsHomogeneous b ∧ A * B = g ∧ A ≠ 0 ∧ B ≠ 0 ∧
        a + b = d ∧ A ∣ g ∧ B ∣ g ∧ a = φ.totalDegree ∧ b = ψ.totalDegree := by
  set a := φ.totalDegree with ha
  set b := ψ.totalDegree with hb
  set A := MvPolynomial.homogeneousComponent a φ with hA
  set B := MvPolynomial.homogeneousComponent b ψ with hB
  have hAle : ∀ m ∈ φ.support, Finsupp.degree m ≤ a := fun m hm =>
    MvPolynomial.le_totalDegree hm
  have hBle : ∀ m ∈ ψ.support, Finsupp.degree m ≤ b := fun m hm =>
    MvPolynomial.le_totalDegree hm
  have hAhom : A.IsHomogeneous a := MvPolynomial.homogeneousComponent_isHomogeneous a φ
  have hBhom : B.IsHomogeneous b := MvPolynomial.homogeneousComponent_isHomogeneous b ψ
  have htopA : ∃ m ∈ φ.support, Finsupp.degree m = φ.totalDegree := by
    have hne : φ.support.Nonempty := by
      by_contra h'
      exact hφ (by
        have h2 : φ.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
        exact MvPolynomial.as_sum φ ▸ by simp [h2])
    obtain ⟨m, hm, hms⟩ := Finset.exists_mem_eq_sup φ.support hne
      (fun s => s.sum fun _ e => e)
    exact ⟨m, hm, by
      rw [MvPolynomial.totalDegree, hms, Finsupp.degree_apply]
      rfl⟩
  have htopB : ∃ m ∈ ψ.support, Finsupp.degree m = ψ.totalDegree := by
    have hne : ψ.support.Nonempty := by
      by_contra h'
      exact hψ (by
        have h2 : ψ.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
        exact MvPolynomial.as_sum ψ ▸ by simp [h2])
    obtain ⟨m, hm, hms⟩ := Finset.exists_mem_eq_sup ψ.support hne
      (fun s => s.sum fun _ e => e)
    exact ⟨m, hm, by
      rw [MvPolynomial.totalDegree, hms, Finsupp.degree_apply]
      rfl⟩
  have hAne : A ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hma⟩ := htopA
    have h1 : m ∈ (MvPolynomial.homogeneousComponent a φ).support := by
      rw [MvPolynomial.support_homogeneousComponent]
      exact Finset.mem_filter.mpr ⟨hm, hma⟩
    rw [← hA, h0] at h1
    simp at h1
  have hBne : B ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hma⟩ := htopB
    have h1 : m ∈ (MvPolynomial.homogeneousComponent b ψ).support := by
      rw [MvPolynomial.support_homogeneousComponent]
      exact Finset.mem_filter.mpr ⟨hm, hma⟩
    rw [← hB, h0] at h1
    simp at h1
  have hABne : A * B ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hAne h'
    · exact hBne h'
  have hABhom : (A * B).IsHomogeneous (a + b) := hAhom.mul hBhom
  have hab : a + b = d := by
    obtain ⟨m, hm⟩ : (A * B).support.Nonempty := by
      by_contra h'
      exact hABne (by
        have h2 : (A * B).support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
        exact MvPolynomial.as_sum (A * B) ▸ by simp [h2])
    have hmdeg : Finsupp.degree m = a + b := by
      rw [Finsupp.degree_apply]
      exact (hABhom.degree_eq_sum_deg_support hm).symm
    have h1 : MvPolynomial.coeff m (A * B) = MvPolynomial.coeff m (φ * ψ) :=
      (coeff_mul_top hAle hBle (n := m) hmdeg).symm
    rw [← hgf] at h1
    have h2 : MvPolynomial.coeff m g ≠ 0 := by
      rw [← h1]
      exact MvPolynomial.mem_support_iff.mp hm
    by_contra hcon
    have h4 : ¬ Finsupp.degree m = d := by
      rw [hmdeg]
      exact hcon
    exact h2 (hg.coeff_eq_zero h4)
  have hAB : A * B = g := by
    ext n
    by_cases hn : Finsupp.degree n = d
    · have h2 : MvPolynomial.coeff n (A * B) = MvPolynomial.coeff n (φ * ψ) :=
        (coeff_mul_top hAle hBle (n := n) (by rw [hab]; exact hn)).symm
      rw [hgf]
      exact h2
    · have h1 : MvPolynomial.coeff n (A * B) = 0 :=
        hABhom.coeff_eq_zero (by rw [hab]; exact hn)
      have h2 : MvPolynomial.coeff n g = 0 := hg.coeff_eq_zero hn
      rw [h1, h2]
  refine ⟨a, b, A, B, hAhom, hBhom, hAB, hAne, hBne, hab, ⟨B, hAB.symm⟩, ⟨A, ?_⟩, rfl, rfl⟩
  rw [mul_comm, ← hAB]



set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

theorem isClosed_isZeroAt (A : MvPolynomial (Fin 6) k) {e : ℕ} (hA : A.IsHomogeneous e) :
    IsClosed {x : Proj k 5 | Proj.IsZeroAt A x} :=
  Proj.isClosed_of_isProjClosed ⟨{f : Proj.HomogPoly k 5 | f.1 = A}, by
    ext x
    constructor
    · intro hx
      exact hx ⟨A, e, hA⟩ rfl
    · intro hx f hf
      rw [show f.1 = A from hf]
      exact hx⟩

theorem isIrreducible_split {Z : Set (Proj k 5)} (hZi : IsIrreducible Z)
    {A B : MvPolynomial (Fin 6) k} {a b : ℕ} (hA : A.IsHomogeneous a)
    (hB : B.IsHomogeneous b)
    (hcover : ∀ x ∈ Z, Proj.IsZeroAt (A * B) x) :
    (∀ x ∈ Z, Proj.IsZeroAt A x) ∨ (∀ x ∈ Z, Proj.IsZeroAt B x) := by
  have hsub : Z ⊆ {x | Proj.IsZeroAt A x} ∪ {x | Proj.IsZeroAt B x} := by
    intro x hx
    have h1 : Proj.IsZeroAt (A * B) x := hcover x hx
    rw [Proj.IsZeroAt, map_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hZi.2) _ _
    (isClosed_isZeroAt A hA) (isClosed_isZeroAt B hB) hsub with h | h
  · exact Or.inl fun x hx => h hx
  · exact Or.inr fun x hx => h hx

/-- A homogeneous polynomial of positive degree has an irreducible homogeneous divisor
that vanishes on a given irreducible closed set contained in its zero locus. -/
theorem exists_prime_homog_divisor {g : MvPolynomial (Fin 6) k} {d : ℕ}
    (hg : g.IsHomogeneous d) (hgne : g ≠ 0) (hd : 0 < d) {Z : Set (Proj k 5)}
    (hZi : IsIrreducible Z) (hZg : ∀ x ∈ Z, Proj.IsZeroAt g x) :
    ∃ (e : ℕ) (h : MvPolynomial (Fin 6) k), 0 < e ∧ h.IsHomogeneous e ∧ h ∣ g ∧
      Prime h ∧ (∀ x ∈ Z, Proj.IsZeroAt h x) := by
  classical
  set S : Set ℕ := {e | ∃ h : MvPolynomial (Fin 6) k,
    0 < e ∧ h.IsHomogeneous e ∧ h ∣ g ∧ (∀ x ∈ Z, Proj.IsZeroAt h x)} with hS
  have hSne : S.Nonempty := ⟨d, g, hd, hg, dvd_rfl, hZg⟩
  obtain ⟨h, hepos, hhh, hhdvd, hhZ⟩ := Nat.find_spec hSne
  have hemin : ∀ e' < Nat.find hSne, e' ∉ S := fun e' h' => Nat.find_min hSne h'
  have hhne : h ≠ 0 := by
    rintro rfl
    exact hgne (zero_dvd_iff.mp hhdvd)
  have hunit_eval : ∀ (u : (MvPolynomial (Fin 6) k)ˣ) (x : Proj k 5),
      MvPolynomial.eval x.rep (u : MvPolynomial (Fin 6) k) ≠ 0 := by
    intro u x
    have h1 : MvPolynomial.eval x.rep (u : MvPolynomial (Fin 6) k) *
        MvPolynomial.eval x.rep ((u⁻¹ : (MvPolynomial (Fin 6) k)ˣ) :
          MvPolynomial (Fin 6) k) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hnotunit : ¬ IsUnit h := by
    rintro ⟨u, rfl⟩
    obtain ⟨x, hx⟩ := hZi.1
    have h1 : Proj.IsZeroAt (u : MvPolynomial (Fin 6) k) x := hhZ x hx
    rw [Proj.IsZeroAt] at h1
    exact (hunit_eval u x) h1
  have hprime : Prime h := by
    rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
    rw [irreducible_iff]
    refine ⟨hnotunit, ?_⟩
    intro φ ψ hφψ
    by_contra hcon
    push Not at hcon
    obtain ⟨hφnu, hψnu⟩ := hcon
    have hφne : φ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hφψ
      exact hhne hφψ
    have hψne : ψ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hφψ
      exact hhne hφψ
    have hunitC : ∀ c : k, c ≠ 0 → IsUnit (MvPolynomial.C c : MvPolynomial (Fin 6) k) := by
      intro c hc0
      refine ⟨⟨MvPolynomial.C c, MvPolynomial.C c⁻¹, ?_, ?_⟩, rfl⟩
      · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
      · rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    have hφdeg : 1 ≤ φ.totalDegree := by
      rcases Nat.eq_zero_or_pos φ.totalDegree with h0 | h0
      · exfalso
        have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
        have hc0 : MvPolynomial.coeff 0 φ ≠ 0 := by
          rintro h'
          exact hφne (by rw [hc, h', MvPolynomial.C_0])
        exact hφnu (hc ▸ hunitC _ hc0)
      · omega
    have hψdeg : 1 ≤ ψ.totalDegree := by
      rcases Nat.eq_zero_or_pos ψ.totalDegree with h0 | h0
      · exfalso
        have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
        have hc0 : MvPolynomial.coeff 0 ψ ≠ 0 := by
          rintro h'
          exact hψne (by rw [hc, h', MvPolynomial.C_0])
        exact hψnu (hc ▸ hunitC _ hc0)
      · omega
    -- the low split
    obtain ⟨a, b, A, B, hAhom, hBhom, hAB, hAne, hBne, hab, hAdvd, hBdvd⟩ :=
      split_lowest hhh hφψ hφne hψne
    -- the top split, used when the low split is degenerate
    have top_case : False := by
      obtain ⟨a', b', A', B', hA'hom, hB'hom, hA'B', hA'ne, hB'ne, ha'b', hA'dvd, hB'dvd,
        ha'eq, hb'eq⟩ := split_highest hhh hφψ hφne hψne
      have ha'ge : 1 ≤ a' := by
        rw [ha'eq]; exact hφdeg
      have hb'ge : 1 ≤ b' := by
        rw [hb'eq]; exact hψdeg
      rcases isIrreducible_split hZi hA'hom hB'hom (fun x hx => by
        rw [hA'B']; exact hhZ x hx) with hZA' | hZB'
      · refine hemin a' ?_ ⟨A', ha'ge, hA'hom, hA'dvd.trans hhdvd, hZA'⟩
        rw [← ha'b']
        exact Nat.lt_add_of_pos_right hb'ge
      · refine hemin b' ?_ ⟨B', hb'ge, hB'hom, hB'dvd.trans hhdvd, hZB'⟩
        rw [← ha'b']
        exact Nat.lt_add_of_pos_left ha'ge
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · exact top_case.elim
    · rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · exact top_case.elim
      · rcases isIrreducible_split hZi hAhom hBhom (fun x hx => by rw [hAB]; exact hhZ x hx) with
          hZA | hZB
        · refine hemin a ?_ ⟨A, hapos, hAhom, hAdvd.trans hhdvd, hZA⟩
          rw [← hab]
          exact Nat.lt_add_of_pos_right hbpos
        · refine hemin b ?_ ⟨B, hbpos, hBhom, hBdvd.trans hhdvd, hZB⟩
          rw [← hab]
          exact Nat.lt_add_of_pos_left hapos
  exact ⟨Nat.find hSne, h, hepos, hhh, hhdvd, hprime, hhZ⟩



/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise 2.8

## The book statement

Exercise I.2.8 of Hartshorne's *Algebraic Geometry* (Chapter I, §2, "Projective Varieties"):

> "A projective variety `Y ⊆ P^n` has dimension `n - 1` if and only if it is the zero set of a
> single irreducible homogeneous polynomial `f` of positive degree.  `Y` is called a hypersurface
> in `P^n`."

Every clause and standing hypothesis of the book is used:

* `k` is an algebraically closed field (Chapter I, §1 standing hypothesis). It enters through the
  Nullstellensatz dictionary (affine and projective) and is needed for it.
* `P^n` is the classical projective space of lines through the origin in `k^{n+1}`
  (`Projectivization k (Fin (n+1) → k)`), with the Zariski topology whose closed sets are the
  zero loci of homogeneous polynomials.
* "projective variety" = irreducible closed subset of `P^n` (Hartshorne I.1). In Mathlib this is
  `IsClosed Y`, `IsIrreducible Y` (which already includes `Y.Nonempty`).
* `dim` is Hartshorne's intrinsic topological dimension: the supremum of the lengths of chains of
  nonempty irreducible closed subsets (Hartshorne I.1, Prop. 1.10). Here this is `projDim`, defined
  by `irrChainDim` as the supremum of lengths of `LTSeries` of irreducible closed subsets; no
  transcendence degree or other substitute invariant is used.
* "zero set of a single irreducible homogeneous polynomial of positive degree" is
  `Proj.zeroSet f` for `f` irreducible, `f.IsHomogeneous d` with `0 < d`.

The formulation `projDim Y + 1 = (n : ℕ∞)` is used for `dim Y = n - 1`; both are equivalent for
`n ≥ 1`, and the addition form is the correct transcription also for `n = 0`
(`hartshorne_exercise_I_2_8_sub` records the literal `n - 1` form under `1 ≤ n`).  When `n = 0`,
`P^0` is a single point, `dim P^0 = 0 ≠ -1`, and no projective zero set of a positive-degree
homogeneous polynomial is nonempty (a positive-degree form in `k[x₀]` vanishes only at the origin
of `k¹`), so both sides of the equivalence are false and it holds.

## Provenance of the statement

The statement above is a reconstruction of the book's exercise, cross-checked against three
independent renderings:

* the bundled natural proof `Hartshorne77-I-2-8/proof.tex`, whose argument is exactly the standard
  one for this statement (`dim Y = n - 1` ⟺ `ht I(Y) = 1` ⟺, `k[x₀,…,xₙ]` being a UFD,
  `I(Y) = (f)` for an irreducible homogeneous `f` of positive degree);
* the public solution rendering <https://hartshornesolutions.blogspot.com/2015/06/chapter-1-exercise-28-hypersurfaces-and.html>,
  which quotes the boxed exercise text: "A projective variety `Y ⊆ P^n` has dimension `n-1` if and
  only if it is the zero set of a single irreducible homogeneous polynomial `f` of positive degree.
  `Y` is called a hypersurface in `P^n`.";
* numbering cross-check: the neighbouring exercises I.2.6, I.2.7, I.2.9, I.2.10 in the same
  sources are `dim S(Y) = dim Y + 1`, `dim P^n = n` / `dim Y = dim Ȳ`, projective closure, and the
  cone over a projective variety, matching the local OCR files of `Hartshorne77-I-2-6/7/9/10`.

The exercise has no lettered parts; the closing sentence "`Y` is called a hypersurface in `P^n`" is a
definition, formalised as `IsHypersurface`.

## Content and provenance

* Sections up to (and including) the affine/projective infrastructure block are the accepted
  Hartshorne I.2.10 formalisation (cone of a projective algebraic set, `dim C(Y) = dim Y + 1`,
  chain dimension, and the affine hypersurface theorem of I.1.8 with its ring-theoretic dimension
  lemmas), copied verbatim; only the namespace differs.
* Everything from `I.2.8 proper` onward is new for this exercise.

## Coverage map (clause by clause)

| book clause | formal counterpart |
|---|---|
| `Y ⊆ P^n` is a projective variety | hypotheses `IsClosed Y`, `IsIrreducible Y` (hence `Y.Nonempty`) |
| `dim` is topological dimension | `projDim Y = irrChainDim Y`, `irrChainDim = ⨆ l : LTSeries {Z // Z ⊆ Y, IsIrreducible Z, IsClosed Z}, l.length` |
| `f` homogeneous of degree `d > 0` | `f.IsHomogeneous d`, `0 < d` |
| `f` irreducible | `Irreducible f` |
| `Y = Z(f)` | `Y = Proj.zeroSet f` |
| `dim Y = n - 1` | `projDim Y + 1 = (n : ℕ∞)` (`= (n-1 : ℕ)` for `1 ≤ n`) |
| `⇒` (dimension forces a hypersurface) | `exists_irreducible_homogeneous_of_projDim` |
| `⇐` (a hypersurface has dimension `n - 1`) | `Proj.projDim_zeroSet` |

## Proof outline

`⇐`: `C(Z(f)) = V(f) ⊆ A^{n+1}` (`Proj.cone_zeroSet`); `V(f)` is an affine hypersurface whose
coordinate ring `k[x₀,…,xₙ]/(f)` has dimension `n` (`Proj.irrChainDim_cone_zeroSet`, from
`ringKrullDim_quotient_span_singleton`), so `dim Z(f) = dim C(Z(f)) - 1 = n - 1`
(`coneDim_eq_projDim_add_one`).

`⇒`: `C(Y) = V(I(Y))` is irreducible of dimension `n = (n+1) - 1`, so `I(Y)` is a prime ideal with
`dim k[x]/(I(Y)) = n`.  Pick `0 ≠ t ∈ I(Y)` and a prime `q ⊆ I(Y)` minimal over `(t)`: the
principal ideal theorem gives `ht q = 1` and the dimension formula gives `dim k[x]/q = n`.
Since `V(I(Y)) ⊆ V(q)` are irreducible closed of the same chain dimension, `V(q) = V(I(Y))`, so
`q = I(Y)` and `ht I(Y) = 1`.  Over the UFD `k[x₀,…,xₙ]` height-one primes are principal
(`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`): `I(Y) = (h)`.  As `I(Y)` is homogeneous,
every homogeneous component of `h` lies in `(h)`, and the top component `h_d = a·h` has the same
total degree as `h`; the top component of a product is the product of top components, so `a` is a
constant and `h` is homogeneous (`homogeneousComponent_mul_totalDegree`).  Its degree is positive
(otherwise `h` would be a unit) and `h` is prime, hence irreducible.  Finally `Y = Z(h)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MvPolynomial

namespace I28

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

end I28

/-! ## The affine cone and the vanishing ideal -/

namespace I28
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

end I28

/-! ## Affine dimension theory (accepted Hartshorne I.1.8 infrastructure) -/

namespace I28
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

end Final


end I28

namespace I28

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-! ### I.2.8 proper: the projective zero locus of a single homogeneous polynomial -/

namespace Proj

/-- The projective zero set of a single polynomial: the set of projective points at which it
vanishes.  For homogeneous `f` this is the zero set of the book. -/
def zeroSet (f : MvPolynomial (Fin (n + 1)) k) : Set (Proj k n) :=
  {x | IsZeroAt f x}

theorem mem_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {x : Proj k n} :
    x ∈ zeroSet f ↔ IsZeroAt f x := Iff.rfl

theorem zeroSet_eq_zeroLocus {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : zeroSet f = zeroLocus ({⟨f, d, hf⟩} : Set (HomogPoly k n)) := by
  ext x
  rw [mem_zeroSet, mem_zeroLocus_iff]
  exact ⟨fun hx => by rintro g rfl; exact hx, fun hx => hx ⟨f, d, hf⟩ rfl⟩

theorem isProjClosed_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : IsProjClosed (zeroSet f) := by
  rw [zeroSet_eq_zeroLocus hf]
  exact isProjClosed_zeroLocus _

theorem isClosed_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : IsClosed (zeroSet f) :=
  (isProjClosed_iff_isClosed _).mp (isProjClosed_zeroSet hf)

/-- The affine cone over the projective hypersurface `Z(f)` is the affine hypersurface `V(f)`.
This is where the classical point model of `P^n` (lines through the origin) is used. -/
theorem cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) :
    cone (zeroSet f) = MvPolynomial.zeroLocus k (Ideal.span {f}) := by
  ext v
  rw [MvPolynomial.mem_zeroLocus_iff]
  simp only [MvPolynomial.aeval_eq_eval]
  constructor
  · rintro (rfl | ⟨hvne, hvt⟩) g hg
    · rw [Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [map_mul, Proj.eval_zero_of_isHomogeneous_pos hd hf, zero_mul]
    · rw [Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [map_mul, (isZeroAt_mk_iff hf hvne).mp hvt, zero_mul]
  · intro hv
    have hfv : (eval v) f = 0 := hv f (Ideal.mem_span_singleton_self f)
    rcases eq_or_ne v 0 with rfl | hvne
    · exact Or.inl rfl
    · exact Or.inr ⟨hvne, (isZeroAt_mk_iff hf hvne).mpr hfv⟩

/-- The affine hypersurface `V(f) ⊆ A^{n+1}` has dimension `n`. -/
theorem varietyDim_cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) :
    varietyDim k (n + 1) (cone (zeroSet f)) =
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) := by
  rw [cone_zeroSet hd hf, varietyDim_zeroLocus]

/-- `ringKrullDim k[x₀,…,xₙ] = n + 1`. -/
theorem ringKrullDim_mvPolynomial (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = (s : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- For irreducible homogeneous `f` of positive degree, the cone over `Z(f)` has chain
dimension `n`: it is the affine hypersurface `V(f)`, whose coordinate ring
`k[x₀,…,xₙ]/(f)` has dimension `n`. -/
theorem irrChainDim_cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    irrChainDim (cone (zeroSet f)) = (n : ℕ∞) := by
  have hfne : f ≠ 0 := hirr.ne_zero
  haveI hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hfne).mpr (irreducible_iff_prime.mp hirr)
  have hne : (cone (zeroSet f)).Nonempty := ⟨0, Or.inl rfl⟩
  have hcoe : varietyDim k (n + 1) (cone (zeroSet f)) =
      ((irrChainDim (cone (zeroSet f)) : ℕ∞) : WithBot ℕ∞) :=
    varietyDim_eq_coe_irrChainDim hne
  have hring : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) + 1 =
      (n : WithBot ℕ∞) + 1 := by
    rw [MvPolynomial.ringKrullDim_quotient_span_singleton k hfne, ringKrullDim_mvPolynomial]
    push_cast
    ring
  have h1 : ((irrChainDim (cone (zeroSet f)) : ℕ∞) : WithBot ℕ∞) + 1 =
      ((n : ℕ∞) : WithBot ℕ∞) + 1 := by
    rw [← hcoe, varietyDim_cone_zeroSet hd hf, hring]
    norm_num
  exact WithBot.coe_injective (ENat.WithBot.add_one_cancel.mp h1)

/-- **I.2.8, `⇐` direction.**  The zero set of an irreducible homogeneous polynomial of positive
degree has dimension `n - 1` (stated as `dim + 1 = n`). -/
theorem projDim_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) (hne : (zeroSet f).Nonempty) :
    projDim (zeroSet f) + 1 = (n : ℕ∞) := by
  have hcd := coneDim_eq_projDim_add_one (isClosed_zeroSet hf) hne
  rw [coneDim] at hcd
  rw [← hcd]
  exact irrChainDim_cone_zeroSet hd hf hirr

end Proj


/-! ### The `⇒` direction: a variety of dimension `n-1` is a hypersurface -/

/-- The top homogeneous component of a product is the product of the top homogeneous
components.  (Pure coefficient bookkeeping in a commutative semiring.) -/
theorem homogeneousComponent_mul_totalDegree {R : Type*} [CommSemiring R]
    (a b : MvPolynomial (Fin (n + 1)) R) :
    homogeneousComponent (a.totalDegree + b.totalDegree) (a * b) =
      homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b := by
  ext u
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hu : Finsupp.degree u = a.totalDegree + b.totalDegree
  · rw [if_pos hu]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases hv : x.1 ∈ a.support
    · by_cases hw : x.2 ∈ b.support
      · have hv' : Finsupp.degree x.1 ≤ a.totalDegree := MvPolynomial.le_totalDegree hv
        have hw' : Finsupp.degree x.2 ≤ b.totalDegree := MvPolynomial.le_totalDegree hw
        have hadd : Finsupp.degree x.1 + Finsupp.degree x.2 =
            a.totalDegree + b.totalDegree := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hx, hu]
        rw [if_pos (by omega), if_pos (by omega)]
      · have h0 : MvPolynomial.coeff x.2 b = 0 := Finsupp.notMem_support_iff.mp hw
        simp [h0, MvPolynomial.coeff_homogeneousComponent]
    · have h0 : MvPolynomial.coeff x.1 a = 0 := Finsupp.notMem_support_iff.mp hv
      simp [h0, MvPolynomial.coeff_homogeneousComponent]
  · rw [if_neg hu]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hv : MvPolynomial.coeff x.1 (homogeneousComponent a.totalDegree a) = 0
    · simp [hv]
    · by_cases hw : MvPolynomial.coeff x.2 (homogeneousComponent b.totalDegree b) = 0
      · simp [hw]
      · exfalso
        apply hu
        have h1 : Finsupp.degree x.1 = a.totalDegree := by
          by_contra h
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h] at hv
          exact hv rfl
        have h2 : Finsupp.degree x.2 = b.totalDegree := by
          by_contra h
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h] at hw
          exact hw rfl
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx, map_add, h1, h2]

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {R : Type*} [CommSemiring R]
    {h : MvPolynomial (Fin (n + 1)) R} (hh : h ≠ 0) :
    homogeneousComponent h.totalDegree h ≠ 0 := by
  intro hzero
  have hne : h.support.Nonempty := MvPolynomial.support_nonempty.mpr hh
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup h.support hne (fun s => Finsupp.degree s)
  have hdeg : Finsupp.degree d = h.totalDegree := by
    rw [← hsup]
    rfl
  have hcoeff : MvPolynomial.coeff d h ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h0 : MvPolynomial.coeff d (homogeneousComponent h.totalDegree h) = 0 := by simp [hzero]
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg] at h0
  exact hcoeff h0

/-! ### The `⇒` direction: a projective variety of dimension `n-1` is a hypersurface -/

section Hypersurface

variable (Y : Set (Proj k n))

/-- **I.2.8, `⇒` direction.**  Let `Y ⊆ P^n` be a projective variety (nonempty, irreducible,
closed) with `dim Y + 1 = n`.  Then `Y = Z(f)` for a single irreducible homogeneous polynomial
`f` of positive degree.

Route: the affine cone `C(Y) = V(I(Y)) ⊆ A^{n+1}` is irreducible of dimension `n = m - 1`; the
ideal `I(Y)` is prime.  Choosing `0 ≠ t ∈ I(Y)` and a prime `q ⊆ I(Y)` minimal over `(t)`, the
principal ideal theorem and the dimension formula for cones give `dim A^{n+1}/q = dim A^{n+1}/I(Y)`,
so `V(I(Y)) ⊆ V(q)` are irreducible closed of equal chain dimension, forcing `V(q) = V(I(Y))` and
hence `q = I(Y)`: thus `ht I(Y) = 1`.  Over the UFD `k[x₀,…,xₙ]` a height-one prime is principal,
`I(Y) = (h)`, and since `I(Y)` is homogeneous, `h` may be taken homogeneous of positive degree. -/
theorem exists_irreducible_homogeneous_of_projDim
    (hYc : IsClosed Y) (hYi : IsIrreducible Y) (hne : Y.Nonempty)
    (hdim : projDim Y + 1 = (n : ℕ∞)) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
      0 < d ∧ f.IsHomogeneous d ∧ Irreducible f ∧ Y = Proj.zeroSet f := by
  classical
  set p : Ideal (MvPolynomial (Fin (n + 1)) k) := Proj.vanishingIdeal Y with hpdef
  haveI hp : p.IsPrime := Proj.vanishingIdeal_isPrime_of_isIrreducible hYi
  have hcone : Proj.cone Y = MvPolynomial.zeroLocus k p :=
    Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne
  have hcone_ne : (Proj.cone Y).Nonempty := ⟨0, Or.inl rfl⟩
  have hconeDim : irrChainDim (Proj.cone Y) = (n : ℕ∞) :=
    (coneDim_eq_projDim_add_one hYc hne).trans hdim
  have hvd : varietyDim k (n + 1) (Proj.cone Y) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [varietyDim_eq_coe_irrChainDim hcone_ne, hconeDim]
  have hring : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ p) = (n : WithBot ℕ∞) := by
    rw [← varietyDim_zeroLocus k (n + 1) p, ← hcone]
    exact hvd
  -- `I(Y) ≠ 0`, since otherwise the cone would be all of `A^{n+1}`
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h1 : varietyDim k (n + 1) (Proj.cone Y) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hcone, hbot, MvPolynomial.zeroLocus_bot, Set.top_eq_univ, varietyDim_univ]
    rw [hvd] at h1
    have h2 : (n : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
    have h3 : n = n + 1 := ENat.natCast_inj.mp h2
    omega
  obtain ⟨t, htp, ht0⟩ : ∃ t, t ∈ p ∧ t ≠ 0 := by
    have hlt : (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) < p :=
      lt_of_le_of_ne bot_le (Ne.symm hpne)
    obtain ⟨t, htp, htbot⟩ := SetLike.exists_of_lt hlt
    exact ⟨t, htp, by simpa using htbot⟩
  -- a prime `q ⊆ I(Y)` minimal over `(t)`, of height one
  obtain ⟨q, hqmin, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := Ideal.span {t}) (J := p)
      ((Ideal.span_singleton_le_iff_mem p).mpr htp)
  haveI hqprime : q.IsPrime := hqmin.isPrime
  have hqht : q.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes ht0 hqmin
  have htu : ¬ IsUnit t := fun hu => hp.ne_top (Ideal.eq_top_of_isUnit_mem p htp hu)
  have hqdim : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) + 1 =
      ringKrullDim (MvPolynomial (Fin (n + 1)) k) :=
    ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes k ht0 htu hqmin
  have hqdim' : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) = (n : WithBot ℕ∞) := by
    rw [Proj.ringKrullDim_mvPolynomial] at hqdim
    have h' : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) + 1 =
        (n : WithBot ℕ∞) + 1 := by
      rw [hqdim]
      push_cast
      ring
    exact ENat.WithBot.add_one_cancel.mp h'
  -- the affine varieties `V(I(Y)) ⊆ V(q)` are irreducible closed of equal chain dimension `n`
  have hZirr : IsIrreducible (MvPolynomial.zeroLocus k p) :=
    zeroLocus_irreducible k (n + 1) hp
  have hZcl : IsClosed (MvPolynomial.zeroLocus k p) := isClosed_zeroLocus k (n + 1) p
  have hWirr : IsIrreducible (MvPolynomial.zeroLocus k q) :=
    zeroLocus_irreducible k (n + 1) hqprime
  have hWcl : IsClosed (MvPolynomial.zeroLocus k q) := isClosed_zeroLocus k (n + 1) q
  have hZW : MvPolynomial.zeroLocus k p ⊆ MvPolynomial.zeroLocus k q :=
    MvPolynomial.zeroLocus_anti_mono hqle
  have hZne : (MvPolynomial.zeroLocus k p).Nonempty := by
    rw [← hcone]; exact hcone_ne
  have hWne : (MvPolynomial.zeroLocus k q).Nonempty := hZne.mono hZW
  have hdimZ : irrChainDim (MvPolynomial.zeroLocus k p) = (n : ℕ∞) := by
    have h1 : varietyDim k (n + 1) (MvPolynomial.zeroLocus k p) = ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [varietyDim_zeroLocus]; exact hring
    have h2 := varietyDim_eq_coe_irrChainDim hZne
    rw [h1] at h2
    exact WithBot.coe_injective h2.symm
  have hdimW : irrChainDim (MvPolynomial.zeroLocus k q) = (n : ℕ∞) := by
    have h1 : varietyDim k (n + 1) (MvPolynomial.zeroLocus k q) = ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [varietyDim_zeroLocus]; exact hqdim'
    have h2 := varietyDim_eq_coe_irrChainDim hWne
    rw [h1] at h2
    exact WithBot.coe_injective h2.symm
  have hp1 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k p) = p := by
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hp.radical]
  have hq1 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k q) = q := by
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hqprime.radical]
  -- a strictly larger irreducible closed set has strictly larger chain dimension
  have hqp : q = p := by
    by_contra hne'
    have hZneW : MvPolynomial.zeroLocus k p ≠ MvPolynomial.zeroLocus k q := by
      intro heq
      apply hne'
      rw [← hp1, ← hq1, heq]
    have hstep := irrChainDim_add_one_le hZW hWcl hWirr hZcl hZirr hZneW
    rw [hdimZ, hdimW] at hstep
    exact absurd ((ENat.add_one_le_iff (by simp)).mp hstep) (lt_irrefl _)
  have hpht : p.height = 1 := by rw [← hqp]; exact hqht
  -- over a UFD a height-one prime is principal
  obtain ⟨h, hh⟩ :=
    (Submodule.isPrincipal_iff p).mp (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hpht)
  have hhne : h ≠ 0 := by
    intro h0
    apply hpne
    rw [hh, h0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hhmem : h ∈ p := by
    rw [hh]
    exact Submodule.mem_span_singleton_self h
  -- each homogeneous component of `h` lies in `p = (h)`
  have hcomp : ∀ i, homogeneousComponent i h ∈ p := fun i =>
    (MvPolynomial.mem_iff_homogeneousComponent_mem (I := p)
      (Proj.vanishingIdeal_isHomogeneous Y) h).mp hhmem i
  obtain ⟨a, ha⟩ : ∃ a, homogeneousComponent h.totalDegree h = a * h := by
    have h1 := hcomp h.totalDegree
    rw [hh] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    exact ⟨c, by rw [← hc, smul_eq_mul]⟩
  have hDne : homogeneousComponent h.totalDegree h ≠ 0 :=
    homogeneousComponent_totalDegree_ne_zero hhne
  have ha0 : a ≠ 0 := by
    intro h0
    exact hDne (by rw [ha, h0, zero_mul])
  -- the top component of `a * h` is `a * h_D`; for `h_D` to be homogeneous `a` must be constant
  have ha_const : a.totalDegree = 0 := by
    by_contra hk
    have hkey := homogeneousComponent_mul_totalDegree a h
    rw [← ha] at hkey
    have hzero : homogeneousComponent (a.totalDegree + h.totalDegree)
        (homogeneousComponent h.totalDegree h) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem
        (homogeneousComponent_isHomogeneous h.totalDegree h), if_neg (by omega)]
    rw [hzero] at hkey
    exact mul_ne_zero (homogeneousComponent_totalDegree_ne_zero ha0)
      (homogeneousComponent_totalDegree_ne_zero hhne) hkey.symm
  obtain ⟨c, hc⟩ : ∃ c : k, a = MvPolynomial.C c := by
    obtain h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ha_const
    exact ⟨_, h⟩
  have hcne : c ≠ 0 := by
    intro h0
    exact ha0 (by rw [hc, h0, MvPolynomial.C_0])
  have hhhom : h.IsHomogeneous h.totalDegree := by
    have h1 : MvPolynomial.C c⁻¹ * homogeneousComponent h.totalDegree h = h := by
      rw [ha, hc, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hcne, MvPolynomial.C_1,
        one_mul]
    have h2 : (MvPolynomial.C c⁻¹ * homogeneousComponent h.totalDegree h).IsHomogeneous
        h.totalDegree := by
      simpa using (MvPolynomial.isHomogeneous_C _ c⁻¹).mul
        (homogeneousComponent_isHomogeneous h.totalDegree h)
    rwa [h1] at h2
  have hDpos : 0 < h.totalDegree := by
    rcases Nat.eq_zero_or_pos h.totalDegree with h0 | hpos
    · exfalso
      have hconst : h = MvPolynomial.C (MvPolynomial.coeff 0 h) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
      have hcoeff_ne : MvPolynomial.coeff 0 h ≠ 0 := by
        intro hc0
        exact hhne (by rw [hconst, hc0, MvPolynomial.C_0])
      have hunit : IsUnit h := by
        rw [hconst]
        exact IsUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k)
          (isUnit_iff_ne_zero.mpr hcoeff_ne)
      apply hp.ne_top
      rw [hh]
      exact Ideal.span_singleton_eq_top.mpr hunit
    · exact hpos
  have hprime : Prime h := by
    refine ⟨hhne, ?_, ?_⟩
    · intro hu
      exact hp.ne_top (by rw [hh]; exact Ideal.span_singleton_eq_top.mpr hu)
    · intro a b hab
      have h1 : a * b ∈ p := by
        rw [hh]
        exact Ideal.mem_span_singleton.mpr hab
      rcases hp.mem_or_mem h1 with h2 | h2
      · exact Or.inl (by rw [hh] at h2; exact Ideal.mem_span_singleton.mp h2)
      · exact Or.inr (by rw [hh] at h2; exact Ideal.mem_span_singleton.mp h2)
  refine ⟨h.totalDegree, h, hDpos, hhhom, hprime.irreducible, ?_⟩
  -- `Y = Z(h)`
  ext x
  constructor
  · intro hx
    have hmem : h ∈ Proj.vanishOnIdeal Y := by
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal]; exact hhmem
    have hx' : Proj.mk x.rep x.rep_nonzero = x := Projectivization.mk_rep x
    exact Proj.mem_vanishOnIdeal_iff.mp hmem x.rep x.rep_nonzero (by rwa [← hx'] at hx)
  · intro hx
    have hx' : x ∈ Proj.zeroLocus (Proj.vanishingForms Y) := by
      rw [Proj.mem_zeroLocus_iff]
      rintro ⟨g, dg, hg⟩ hgmem
      have hgmem' : g ∈ p := hgmem
      rw [hh] at hgmem'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgmem'
      show MvPolynomial.eval x.rep g = 0
      rw [← hc, smul_eq_mul, map_mul,
        show MvPolynomial.eval x.rep h = 0 from hx, mul_zero]
    rwa [Proj.zeroLocus_vanishingForms_eq Y hYc] at hx'

/-- Hartshorne's terminology in I.2.8: `Y` is a *hypersurface* in `P^n` when it is the zero set of a
single irreducible homogeneous polynomial of positive degree. -/
def IsHypersurface (Y : Set (Proj k n)) : Prop :=
  ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
    0 < d ∧ f.IsHomogeneous d ∧ Irreducible f ∧ Y = Proj.zeroSet f

/-- **Hartshorne (1977), *Algebraic Geometry*, Exercise I.2.8.**

A projective variety `Y ⊆ P^n` has dimension `n - 1` if and only if it is the zero set of a single
irreducible homogeneous polynomial `f` of positive degree.

Here `dim Y = n - 1` is rendered as `projDim Y + 1 = n` in `ℕ∞`; the two are equivalent for
`n ≥ 1`, and the chosen form is the correct one also for `n = 0`, where `P^0` is a point, no
projective zero set of a positive-degree homogeneous polynomial is nonempty, and neither side
holds. -/
theorem hartshorne_exercise_I_2_8 (Y : Set (Proj k n)) (hYc : IsClosed Y) (hYi : IsIrreducible Y)
    (hne : Y.Nonempty) :
    (projDim Y + 1 = (n : ℕ∞)) ↔ IsHypersurface Y := by
  constructor
  · intro hdim
    exact exists_irreducible_homogeneous_of_projDim Y hYc hYi hne hdim
  · rintro ⟨d, f, hd, hf, hirr, rfl⟩
    exact Proj.projDim_zeroSet hd hf hirr hne

/-- `(n - 1 : ℕ)` cast to `ℕ∞`, plus one, is `n` (for `n ≥ 1`). -/
theorem natCast_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) := by
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← h]
  push_cast
  ring

/-- **I.2.8** in the literal book wording `dim Y = n - 1` (for `n ≥ 1`). -/
theorem hartshorne_exercise_I_2_8_sub (hn : 1 ≤ n) (Y : Set (Proj k n)) (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) :
    (projDim Y = ((n - 1 : ℕ) : ℕ∞)) ↔ IsHypersurface Y := by
  rw [← hartshorne_exercise_I_2_8 Y hYc hYi hne]
  constructor
  · intro h
    rw [h]
    exact natCast_sub_one_add_one hn
  · intro h
    rw [← natCast_sub_one_add_one hn] at h
    exact WithTop.add_right_cancel (by simp : (1 : ℕ∞) ≠ ⊤) h

end Hypersurface
/-! ### Axiom audit -/

#print axioms hartshorne_exercise_I_2_8
#print axioms hartshorne_exercise_I_2_8_sub
#print axioms exists_irreducible_homogeneous_of_projDim
#print axioms Proj.projDim_zeroSet
#print axioms Proj.irrChainDim_cone_zeroSet
#print axioms Proj.cone_zeroSet
#print axioms Proj.varietyDim_cone_zeroSet
#print axioms Proj.ringKrullDim_mvPolynomial
#print axioms homogeneousComponent_mul_totalDegree
#print axioms homogeneousComponent_totalDegree_ne_zero
#print axioms coneDim_eq_projDim_add_one
#print axioms Proj.cone_eq_zeroLocus
#print axioms Proj.vanishingIdeal_isPrime_of_isIrreducible
#print axioms hartshorne_exercise_I_1_8
#print axioms ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes
#print axioms Ideal.height_eq_one_of_mem_minimalPrimes
#print axioms MvPolynomial.ringKrullDim_quotient_span_singleton
#print axioms UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
#print axioms irrChainDim_add_one_le
#print axioms varietyDim_zeroLocus

end I28


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

open MvPolynomial



variable {k : Type u} [Field k] [IsAlgClosed k]

theorem isZeroAt_mul_iff' {a b : MvPolynomial (Fin 6) k} {x : Proj k 5} :
    Proj.IsZeroAt (a * b) x ↔ Proj.IsZeroAt a x ∨ Proj.IsZeroAt b x := by
  rw [Proj.IsZeroAt, map_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]

/-- The cone over the zero set of a homogeneous form of positive degree is the corresponding
affine hypersurface. -/
theorem cone_isZeroAt {h : MvPolynomial (Fin 6) k} {e : ℕ} (he : 0 < e) (hh : h.IsHomogeneous e) :
    Proj.cone {x : Proj k 5 | Proj.IsZeroAt h x} = MvPolynomial.zeroLocus k (Ideal.span {h}) := by
  ext v
  constructor
  · intro hv
    rw [MvPolynomial.mem_zeroLocus_iff]
    simp only [MvPolynomial.aeval_eq_eval]
    intro p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rcases hv with rfl | ⟨hvne, hvV⟩
    · rw [map_mul, Proj.eval_zero_of_isHomogeneous_pos he hh, zero_mul]
    · rw [map_mul, (Proj.isZeroAt_mk_iff hh hvne).mp hvV, zero_mul]
  · intro hv
    rw [MvPolynomial.mem_zeroLocus_iff] at hv
    simp only [MvPolynomial.aeval_eq_eval] at hv
    by_cases h0 : v = 0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, (Proj.isZeroAt_mk_iff hh h0).mpr (hv h (Ideal.mem_span_singleton_self h))⟩

/-- **Hartshorne (1977), Algebraic Geometry, Chapter I, Exercise 2.13.**

Let `Y ⊆ P⁵` be the image of the 2-uple embedding of `P²` in `P⁵` (the Veronese surface).  If
`Z ⊆ Y` is a closed curve (`Z` irreducible of dimension one), then there is a hypersurface
`V ⊆ P⁵` (an irreducible closed subset of dimension `5 - 1 = 4`) with `V ∩ Y = Z`. -/
theorem hartshorne_exercise_I_2_13 {Z : Set (Proj k 5)} (hZcl : IsClosed Z)
    (hZY : Z ⊆ Y (k := k)) (hZi : IsIrreducible Z) (hdim : projDim Z = 1) :
    ∃ V : Set (Proj k 5), IsClosed V ∧ IsIrreducible V ∧ projDim V = 4 ∧
      V ∩ Y (k := k) = Z := by
  classical
  -- the curve pulled back to `P²`
  set C : Set (Proj k 2) := V (k := k) ⁻¹' Z with hCdef
  have hCcl : IsClosed C := hZcl.preimage continuous_V
  have hCi : IsIrreducible C := isIrreducible_preimage_image hZcl hZi hZY
  have hCd : projDim C = 1 := by rw [projDim_preimage_V hZcl hZY, hdim]
  -- Exercise I.2.8: a plane curve is cut out by one irreducible homogeneous form
  have hI28dim : I28.projDim C + 1 = ((2 : ℕ) : ℕ∞) := by
    rw [show I28.projDim C = projDim C from rfl, hCd]
    norm_num
  obtain ⟨d, f, hd, hfhom, hfirr, hCf⟩ :=
    I28.exists_irreducible_homogeneous_of_projDim (k := k) (n := 2) (Y := C) hCcl hCi hCi.1 hI28dim
  have hCZ : ∀ x : Proj k 2, x ∈ C ↔ Proj.IsZeroAt f x := by
    intro x
    rw [hCf]
    exact I28.Proj.mem_zeroSet
  have hfne : f ≠ 0 := hfirr.ne_zero
  -- the form `g` with `θ g = f²`
  obtain ⟨g, hghom, hgeq⟩ := exists_theta_sq (k := k) f hfhom
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hgeq
    exact hfne ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hgeq.symm)
  -- `Z(g) ∩ Y = Z`
  have hZgY : {z : Proj k 5 | Proj.IsZeroAt g z} ∩ Y (k := k) = Z := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hz, hzY⟩
      obtain ⟨x, rfl⟩ := hzY
      have h1 : Proj.IsZeroAt (theta (k := k) g) x := (isZeroAt_V_iff (k := k) hghom).mp hz
      rw [hgeq, pow_two] at h1
      have hfx : Proj.IsZeroAt f x := isZeroAt_mul_iff.mp h1
      have hxC : x ∈ C := (hCZ x).mpr hfx
      have hz' : V (k := k) x ∈ V (k := k) '' C := ⟨x, hxC, rfl⟩
      rwa [image_preimage (k := k) hZY] at hz'
    · intro z hz
      obtain ⟨x, rfl⟩ := hZY hz
      have hxC : x ∈ C := by rw [hCdef]; exact hz
      have hfx : Proj.IsZeroAt f x := (hCZ x).mp hxC
      have h1 : Proj.IsZeroAt (theta (k := k) g) x := by
        rw [hgeq, pow_two]
        exact isZeroAt_mul_iff.mpr hfx
      exact ⟨(isZeroAt_V_iff (k := k) hghom).mpr h1, ⟨x, rfl⟩⟩
  have hZg : ∀ z ∈ Z, Proj.IsZeroAt g z := by
    intro z hz
    have h1 : z ∈ {z : Proj k 5 | Proj.IsZeroAt g z} ∩ Y (k := k) := hZgY ▸ hz
    exact h1.1
  -- an irreducible homogeneous divisor vanishing on `Z`
  obtain ⟨e, h, he, hhh, hhdvd, hhprime, hhZ⟩ :=
    exists_prime_homog_divisor hghom hgne hd hZi hZg
  have hhne : h ≠ 0 := hhprime.ne_zero
  -- the hypersurface
  have hVcl : IsClosed {x : Proj k 5 | Proj.IsZeroAt h x} := isClosed_isZeroAt h hhh
  have hVne : ({x : Proj k 5 | Proj.IsZeroAt h x}).Nonempty :=
    ⟨_, hhZ _ hZi.1.choose_spec⟩
  have hVirr : IsIrreducible {x : Proj k 5 | Proj.IsZeroAt h x} := by
    have hcone := cone_isZeroAt (k := k) he hhh
    have hprime : (Ideal.span {h}).IsPrime := (Ideal.span_singleton_prime hhne).mpr hhprime
    have h1 : IsIrreducible (Proj.cone {x : Proj k 5 | Proj.IsZeroAt h x}) := by
      rw [hcone]
      exact zeroLocus_irreducible k 6 hprime
    exact Proj.isIrreducible_of_isIrreducible_cone hVne h1
  have hVdim : projDim {x : Proj k 5 | Proj.IsZeroAt h x} = 4 := by
    have hsub := I28.hartshorne_exercise_I_2_8_sub (k := k) (n := 5) (by norm_num)
      {x : Proj k 5 | Proj.IsZeroAt h x} hVcl hVirr hVne
    have hhyp : I28.IsHypersurface {x : Proj k 5 | Proj.IsZeroAt h x} :=
      ⟨e, h, he, hhh, hhprime.irreducible, rfl⟩
    have h1 : I28.projDim {x : Proj k 5 | Proj.IsZeroAt h x} = ((5 - 1 : ℕ) : ℕ∞) :=
      hsub.mpr hhyp
    rw [show projDim {x : Proj k 5 | Proj.IsZeroAt h x}
        = I28.projDim {x : Proj k 5 | Proj.IsZeroAt h x} from rfl, h1]
    norm_num
  have hVY : {x : Proj k 5 | Proj.IsZeroAt h x} ∩ Y (k := k) = Z := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hz, hzY⟩
      have h1 : z ∈ {z : Proj k 5 | Proj.IsZeroAt g z} ∩ Y (k := k) := by
        refine ⟨?_, hzY⟩
        obtain ⟨c, hc⟩ := hhdvd
        rw [hc]
        exact isZeroAt_mul_iff'.mpr (Or.inl hz)
      rwa [hZgY] at h1
    · intro z hz
      exact ⟨hhZ z hz, hZY hz⟩
  exact ⟨_, hVcl, hVirr, hVdim, hVY⟩



-- Axiom audit
#print axioms Hartshorne77.Ex_I_2_13.V_injective
#print axioms Hartshorne77.Ex_I_2_13.exists_theta_sq
#print axioms Hartshorne77.Ex_I_2_13.image_closed
#print axioms Hartshorne77.Ex_I_2_13.irrChainDim_preimage_V
#print axioms Hartshorne77.Ex_I_2_13.projDim_preimage_V
#print axioms Hartshorne77.Ex_I_2_13.split_lowest
#print axioms Hartshorne77.Ex_I_2_13.split_highest
#print axioms Hartshorne77.Ex_I_2_13.exists_prime_homog_divisor
#print axioms Hartshorne77.Ex_I_2_13.I28.exists_irreducible_homogeneous_of_projDim
#print axioms Hartshorne77.Ex_I_2_13.I28.hartshorne_exercise_I_2_8_sub
#print axioms Hartshorne77.Ex_I_2_13.hartshorne_exercise_I_2_13

end Hartshorne77.Ex_I_2_13
