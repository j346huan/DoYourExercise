/-
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise 2.12:
  the d-uple embedding.

This file is a standalone formalization (`import Mathlib` only) of Exercise I.2.12.

## Source statement (book text)

The text of the exercise, as printed in Hartshorne (1977), p. 13 (reconstructed from the
bundled OCR `.scratch/reference/hartshorne-1977.txt` together with the public renderings of the
exercise list) reads:

> **2.12. The d-uple embedding.** For `d > 0`, let `M₀, M₁, …, M_N` be all the monomials of
> degree `d` in the `n + 1` variables `x₀, …, x_n`, where `N = (n+d choose d) - 1`.  We define a
> mapping `ρ_d : ℙⁿ → ℙ^N` by sending the point `P = (a₀,…,a_n)` to the point
> `ρ_d(P) = (M₀(a),…,M_N(a))`, obtained by substituting the `a_i` in the monomials `M_j`.  This is
> called the *d-uple embedding* of `ℙⁿ` in `ℙ^N`.  For example, if `n = 1`, `d = 2`, then
> `N = 2`, and the image `Y` of the 2-uple embedding of `ℙ¹` in `ℙ²` is a conic.
>
> (a) Let `θ : k[y₀,…,y_N] → k[x₀,…,x_n]` be the homomorphism defined by sending `y_i` to `M_i`,
>     and let `𝔞 = ker θ`.  Then `𝔞` is a homogeneous prime ideal, and so `Z(𝔞)` is a projective
>     variety in `ℙ^N`.
> (b) Show that the image of `ρ_d` is exactly `Z(𝔞)`.  (One inclusion is easy.  The other will
>     require some calculation.)
> (c) Now show that `ρ_d` is a homeomorphism of `ℙⁿ` onto the projective variety `Z(𝔞)`.
> (d) Show that the twisted cubic curve in `ℙ³` (Ex. 2.9) is equal to the 3-uple embedding of `ℙ¹`
>     in `ℙ³`, for suitable choice of coordinates.

Standing hypotheses of Chapter I (Hartshorne, p. 1 and p. 10): `k` is a fixed algebraically
closed field, `ℙⁿ` is the classical projective space of lines through the origin in `k^{n+1}`
(classes of nonzero `(n+1)`-tuples under `(a₀,…,a_n) ∼ (λa₀,…,λa_n)`, `λ ≠ 0`),
`S = k[x₀,…,x_n]` is the homogeneous coordinate ring with the standard grading (`deg x_i = 1`),
and `Z(T) ⊆ ℙⁿ` for a set `T` of homogeneous polynomials is the common zero locus.  The exercise
carries no hypothesis beyond these; the field `k` itself enters only through `k^×`-scaling, and
every clause below is in fact proved here for an arbitrary field `k` (which is more general than
the standing hypothesis, hence also covers it).

## Formalization choices

* `ℙⁿ` is *not* replaced by `Proj` of a graded ring or by a prime spectrum: the genuine classical
  point set is used throughout — `Pp k ι` is the quotient of `{v : ι → k // v ≠ 0}` by the
  action of `k^×` (see `Pp.mk_eq_mk_iff`).
* The monomials of degree `d` in `n+1` variables are indexed by their exponent vectors,
  `Dmon n d = {m : (Fin (n+1) →₀ ℕ) // m.degree = d}`; thus the target `ℙ^N` of the exercise is
  `Pp k (Dmon n d)`, whose number of coordinates is `Nat.card (Dmon n d)`, and Hartshorne's
  `N = (n+d choose d) - 1` is `Nat.card (Dmon n d) - 1` (the stars-and-bars count of monomials).
  No result below depends on the numerical value of that count.
* Homogeneity of a polynomial is Mathlib's `MvPolynomial.IsHomogeneous` (all monomials of `f`
  have total degree `n`).  "The ideal `𝔞` is homogeneous" is formalized in *unfolded* form: every
  homogeneous component of every element of `𝔞` lies in `𝔞` (`veroneseIdeal_homogeneousComponent_mem`).
  This is exactly the definition of Mathlib's `Ideal.IsHomogeneous (homogeneousSubmodule _ _ 1)`
  (`SetLike.IsHomogeneous`), and it is the form consumed by parts (b)–(d).
-/
import Mathlib

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_2_12

variable {k : Type*} [Field k]

/-! ## 1. Projective space over an arbitrary coordinate set -/

section Projective

variable {ι : Type*}

/-- Two nonzero vectors of `k^ι` define the same projective point iff they differ by a nonzero
scalar. -/
def projRel (v w : {v : ι → k // v ≠ 0}) : Prop := ∃ c : k, c ≠ 0 ∧ v.1 = c • w.1

theorem projRel_equivalence : Equivalence (projRel (k := k) (ι := ι)) where
  refl v := ⟨1, one_ne_zero, by simp⟩
  symm := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  trans := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨c, hc, h₁⟩ ⟨d, hd, h₂⟩
    exact ⟨c * d, mul_ne_zero hc hd, by rw [h₁, h₂, smul_smul]⟩

/-- The setoid defining `ℙ^ι`, the projective space whose homogeneous coordinates are indexed
by `ι`. -/
def projSetoid (k : Type*) [Field k] (ι : Type*) : Setoid {v : ι → k // v ≠ 0} :=
  ⟨projRel, projRel_equivalence⟩

/-- `ℙ^ι`: the classical projective space of lines through the origin in `k^ι`, as the quotient
of the nonzero vectors by `k^×`.  For `ι = Fin (n+1)` this is Hartshorne's `ℙⁿ`. -/
def Pp (k : Type*) [Field k] (ι : Type*) : Type _ := Quotient (projSetoid k ι)

namespace Pp

/-- The projective point of a nonzero vector. -/
def mk {v : ι → k} (hv : v ≠ 0) : Pp k ι := Quotient.mk _ ⟨v, hv⟩

theorem mk_eq_mk_iff {v w : ι → k} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (ι := ι) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w :=
  Quotient.eq

theorem mk_eq_mk_iff' {v w : ι → k} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (ι := ι) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ c • v = w := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem mk_smul {c : k} (hc : c ≠ 0) {v : ι → k} (hv : v ≠ 0) :
    mk (k := k) (ι := ι) (show c • v ≠ 0 from smul_ne_zero hc hv) = mk hv := by
  rw [mk_eq_mk_iff]
  exact ⟨c, hc, rfl⟩

theorem exists_mk (p : Pp k ι) : ∃ (v : ι → k) (hv : v ≠ 0), mk hv = p := by
  induction p using Quotient.inductionOn with
  | h x => exact ⟨x.1, x.2, rfl⟩

/-! ### Homogeneous polynomials and vanishing at a projective point -/

/-- **Homogeneity of evaluation**: for a homogeneous polynomial `f` of degree `d` and any scalar
`c`, `f (c • v) = c ^ d * f v`. -/
theorem eval_smul_of_isHomogeneous {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : k) (v : ι → k) :
    MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul]
  have hdeg : d = ∑ i ∈ s.support, s i := hf.degree_eq_sum_deg_support hs
  have h1 : (∏ i ∈ s.support, (c * v i) ^ (s i)) =
      (∏ i ∈ s.support, c ^ (s i)) * (∏ i ∈ s.support, (v i) ^ (s i)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => mul_pow c (v i) (s i))
  have h2 : (∏ i ∈ s.support, c ^ (s i)) = c ^ d := by
    rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
  rw [h1, h2]
  ring

/-- `f` vanishes at the projective point `p` if it vanishes at every representative. -/
def FormVanishesAt (f : MvPolynomial ι k) (p : Pp k ι) : Prop :=
  ∀ (v : ι → k) (hv : v ≠ 0), mk hv = p → MvPolynomial.eval v f = 0

theorem formVanishesAt_mk {f : MvPolynomial ι k} {v : ι → k} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) → MvPolynomial.eval v f = 0 :=
  fun h => h v hv rfl

/-- Vanishing of a homogeneous polynomial at a projective point does not depend on the chosen
representative. -/
theorem formVanishesAt_mk_iff {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    {v : ι → k} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) ↔ MvPolynomial.eval v f = 0 := by
  refine ⟨formVanishesAt_mk hv, ?_⟩
  intro h w hw hwp
  obtain ⟨c, hc, hwv⟩ := (mk_eq_mk_iff hw hv).1 hwp
  rw [hwv, eval_smul_of_isHomogeneous hf, h, mul_zero]

/-- The projective zero locus `Z(T)` of a set `T` of polynomials: the set of points at which
every polynomial of `T` vanishes.  For sets of homogeneous polynomials this is Hartshorne's
`Z(T) ⊆ ℙⁿ`. -/
def zeroLocus (T : Set (MvPolynomial ι k)) : Set (Pp k ι) :=
  {p | ∀ f ∈ T, FormVanishesAt f p}

theorem mem_zeroLocus_iff {T : Set (MvPolynomial ι k)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) {v : ι → k} (hv : v ≠ 0) :
    mk hv ∈ zeroLocus T ↔ ∀ f ∈ T, MvPolynomial.eval v f = 0 := by
  constructor
  · intro h f hf
    exact formVanishesAt_mk hv (h f hf)
  · intro h f hf
    obtain ⟨d, hd⟩ := hT f hf
    rw [formVanishesAt_mk_iff hd hv]
    exact h f hf

theorem zeroLocus_empty : zeroLocus (∅ : Set (MvPolynomial ι k)) = Set.univ := by
  ext p
  simp [zeroLocus]

theorem zeroLocus_mono {T T' : Set (MvPolynomial ι k)} (h : T ⊆ T') :
    zeroLocus T' ⊆ zeroLocus T :=
  fun _ hp f hf => hp f (h hf)

theorem zeroLocus_iUnion {τ : Type*} (T : τ → Set (MvPolynomial ι k)) :
    zeroLocus (⋃ i, T i) = ⋂ i, zeroLocus (T i) := by
  ext p
  simp only [zeroLocus, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_union (T T' : Set (MvPolynomial ι k)) :
    zeroLocus (T ∪ T') = zeroLocus T ∩ zeroLocus T' := by
  ext p
  simp only [zeroLocus, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

theorem isHomogeneous_one' : (1 : MvPolynomial ι k).IsHomogeneous 0 :=
  MvPolynomial.isHomogeneous_one (σ := ι) (R := k)

theorem zeroLocus_one_eq_empty :
    zeroLocus ({(1 : MvPolynomial ι k)} : Set (MvPolynomial ι k)) = ∅ := by
  have h1 : ∀ f ∈ ({(1 : MvPolynomial ι k)} : Set (MvPolynomial ι k)), ∃ d, f.IsHomogeneous d := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, MvPolynomial.isHomogeneous_one (σ := ι) (R := k)⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff h1 hv]
  simp

/-- `Z(T₁) ∪ Z(T₂) = Z({fg : f ∈ T₁, g ∈ T₂})`: over a field a product vanishes iff one of the
factors does.  This is what makes the zero loci the closed sets of a topology. -/
theorem zeroLocus_image2_mul_union {T T' : Set (MvPolynomial ι k)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) (hT' : ∀ f ∈ T', ∃ d, f.IsHomogeneous d) :
    zeroLocus (Set.image2 (· * ·) T T') = zeroLocus T ∪ zeroLocus T' := by
  have hTT' : ∀ h ∈ Set.image2 (· * ·) T T', ∃ d, h.IsHomogeneous d := by
    rintro _ ⟨f, hf, g, hg, rfl⟩
    obtain ⟨d, hd⟩ := hT f hf
    obtain ⟨e, he⟩ := hT' g hg
    exact ⟨d + e, hd.mul he⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff hTT' hv, Set.mem_union, mem_zeroLocus_iff hT hv,
    mem_zeroLocus_iff hT' hv]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hfT, hfv⟩, ⟨g, hgT, hgv⟩⟩ := hc
    have h0 := h (f * g) ⟨f, hfT, g, hgT, rfl⟩
    rw [map_mul] at h0
    exact mul_ne_zero hfv hgv h0
  · rintro (h | h) h₁ h₂
    · obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
      rw [map_mul, h p₁ hp₁, zero_mul]
    · obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
      rw [map_mul, h p₂ hp₂, mul_zero]

/-! ### The Zariski topology -/

set_option warn.classDefReducibility false in
/-- **The Zariski topology on `ℙ^ι`**: a set is open iff it is the complement of the zero locus
`Z(T)` of a set `T` of homogeneous polynomials. -/
def zariskiTopology : TopologicalSpace (Pp k ι) where
  IsOpen U := ∃ T : Set (MvPolynomial ι k), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
    U = (zeroLocus T)ᶜ
  isOpen_univ := by
    have h1 : ∀ f ∈ ({(1 : MvPolynomial ι k)} : Set (MvPolynomial ι k)), ∃ d, f.IsHomogeneous d := by
      intro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨0, MvPolynomial.isHomogeneous_one (σ := ι) (R := k)⟩
    exact ⟨{1}, h1, by rw [zeroLocus_one_eq_empty, Set.compl_empty]⟩
  isOpen_inter := by
    rintro U V ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
    refine ⟨Set.image2 (· * ·) T T', ?_, ?_⟩
    · rintro _ ⟨f, hf, g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hT f hf
      obtain ⟨e, he⟩ := hT' g hg
      exact ⟨d + e, hd.mul he⟩
    · rw [zeroLocus_image2_mul_union hT hT', Set.compl_union]
  isOpen_sUnion := by
    intro A hA
    have hA' : ∀ a : A, ∃ T : Set (MvPolynomial ι k), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
        (a : Set (Pp k ι)) = (zeroLocus T)ᶜ := fun a => hA a a.2
    choose T hT hTA using hA'
    refine ⟨⋃ a : A, T a, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, hfa⟩ := Set.mem_iUnion.1 hf
      exact hT a f hfa
    · rw [zeroLocus_iUnion, Set.sUnion_eq_iUnion, Set.compl_iInter]
      exact Set.iUnion_congr fun a => hTA a

instance : TopologicalSpace (Pp k ι) := zariskiTopology (k := k) (ι := ι)

/-- The closed sets of `ℙ^ι` are exactly the zero loci of sets of homogeneous polynomials. -/
theorem isClosed_iff_exists_zeroLocus {Z : Set (Pp k ι)} :
    IsClosed Z ↔ ∃ T : Set (MvPolynomial ι k), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
      Z = zeroLocus T := by
  constructor
  · intro h
    obtain ⟨T, hT, hU⟩ := h.isOpen_compl
    exact ⟨T, hT, by rw [← compl_compl Z, hU, compl_compl]⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩

theorem isClosed_zeroLocus {T : Set (MvPolynomial ι k)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) : IsClosed (zeroLocus T) :=
  isClosed_iff_exists_zeroLocus.2 ⟨T, hT, rfl⟩

end Pp

end Projective

/-! ## 2. The monomials of degree `d`, the substitution `θ`, and the ideal `𝔞 = ker θ` -/

variable {n d : ℕ}

/-- The exponent vectors of the monomials of degree `d` in the `n + 1` variables
`x₀, …, x_n`.  It indexes the homogeneous coordinates `y₀, …, y_N` of `ℙ^N` of the exercise;
its cardinality is Hartshorne's `N + 1 = (n+d choose d)`. -/
def Dmon (n d : ℕ) : Type := {m : Fin (n + 1) →₀ ℕ // m.degree = d}

namespace Dmon

variable {n d : ℕ}

theorem sum_eq (m : Dmon n d) : (∑ j : Fin (n + 1), m.1 j) = d := by
  have h2 : (∑ j ∈ (m.1).support, m.1 j) = ∑ j : Fin (n + 1), m.1 j := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro j _ hj
    simpa [Finsupp.mem_support_iff] using hj
  have h3 : (∑ j ∈ (m.1).support, m.1 j) = d := by
    rw [← Finsupp.degree_apply (R := ℕ) (d := m.1)]
    exact m.2
  rw [← h2, h3]

/-- The monomial `x_i ^ d`. -/
def pure (i : Fin (n + 1)) : Dmon n d := ⟨Finsupp.single i d, Finsupp.degree_single i d⟩

@[simp] theorem pure_val (i : Fin (n + 1)) : (pure (n := n) (d := d) i).1 =
    Finsupp.single i d := rfl

/-- The monomial `x_i ^ (d-1) · x_j`, for `d > 0`. -/
def mix (hd : 0 < d) (i j : Fin (n + 1)) : Dmon n d :=
  ⟨Finsupp.single i (d - 1) + Finsupp.single j 1, by
    have h : (Finsupp.single i (d - 1) + Finsupp.single j 1 : Fin (n + 1) →₀ ℕ).degree
        = (d - 1) + 1 := by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    rw [h]; omega⟩

@[simp] theorem mix_val (hd : 0 < d) (i j : Fin (n + 1)) :
    (mix hd i j : Dmon n d).1 = Finsupp.single i (d - 1) + Finsupp.single j 1 := rfl

theorem mix_self (hd : 0 < d) (i : Fin (n + 1)) : mix hd i i = pure (n := n) (d := d) i := by
  refine Subtype.ext ?_
  rw [mix_val, pure_val, ← Finsupp.single_add]
  congr 1
  omega

end Dmon

/-- The monomial `M_m = x^m ∈ k[x₀,…,x_n]`. -/
def mon (m : Dmon n d) : MvPolynomial (Fin (n + 1)) k := MvPolynomial.monomial m.1 1

theorem mon_isHomogeneous (m : Dmon n d) : (mon (k := k) m).IsHomogeneous d :=
  MvPolynomial.isHomogeneous_monomial 1 m.2

/-- Hartshorne's homomorphism `θ : k[y₀,…,y_N] → k[x₀,…,x_n]`, `y_m ↦ M_m`. -/
def theta : MvPolynomial (Dmon n d) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  MvPolynomial.aeval mon

@[simp] theorem theta_X (m : Dmon n d) : theta (MvPolynomial.X m) = mon (k := k) m := by
  simp [theta]

/-- Hartshorne's ideal `𝔞 = ker θ`. -/
def veroneseIdeal : Ideal (MvPolynomial (Dmon n d) k) :=
  RingHom.ker (theta (k := k) (n := n) (d := d))

theorem mem_veroneseIdeal_iff {f : MvPolynomial (Dmon n d) k} :
    f ∈ veroneseIdeal (k := k) (n := n) (d := d) ↔ theta f = 0 := by
  rw [veroneseIdeal, RingHom.mem_ker]

/-- `𝔞` is a prime ideal. -/
theorem veroneseIdeal_isPrime : (veroneseIdeal (k := k) (n := n) (d := d)).IsPrime :=
  RingHom.ker_isPrime _

/-! ### Homogeneity of `θ` and of the ideal `𝔞` -/

theorem theta_isHomogeneous {f : MvPolynomial (Dmon n d) k} {e : ℕ} (hf : f.IsHomogeneous e) :
    (theta (k := k) (n := n) (d := d) f).IsHomogeneous (d * e) :=
  hf.aeval mon (fun m => mon_isHomogeneous (k := k) m)

/-- A sum of homogeneous polynomials whose degrees are pairwise distinct is zero only if every
summand is zero. -/
theorem eq_zero_of_sum_homogeneous {τ υ : Type*} (s : Finset τ)
    (f : τ → MvPolynomial υ k) (m : τ → ℕ)
    (hm : ∀ i ∈ s, (f i).IsHomogeneous (m i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, m i = m j → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  have key : ∀ i ∈ s, MvPolynomial.homogeneousComponent (m i) (∑ j ∈ s, f j) = f i := by
    intro i hi
    have hsplit : MvPolynomial.homogeneousComponent (m i) (∑ j ∈ s, f j)
        = ∑ j ∈ s, MvPolynomial.homogeneousComponent (m i) (f j) :=
      map_sum (MvPolynomial.homogeneousComponent (m i)) f s
    rw [hsplit]
    refine (Finset.sum_eq_single (s := s)
      (f := fun j => MvPolynomial.homogeneousComponent (m i) (f j)) i ?_ ?_).trans ?_
    · intro j hj hji
      have hzero : MvPolynomial.homogeneousComponent (m i) (f j) = 0 := by
        have h1 : MvPolynomial.homogeneousComponent (m i) (f j)
            = if m i = m j then f j else 0 :=
          MvPolynomial.homogeneousComponent_of_mem (p := f j) (hm j hj)
        rw [h1]
        simp [show m i ≠ m j from fun h => hji (hne i hi j hj h).symm]
      rw [hzero]
    · intro h; exact absurd hi h
    · exact MvPolynomial.homogeneousComponent_eq_self (hm i hi)
  intro i hi
  have h := key i hi
  rw [hsum, map_zero] at h
  exact h.symm

/-- **Homogeneity of `𝔞`**: every homogeneous component of an element of `𝔞` lies in `𝔞`. -/
theorem veroneseIdeal_homogeneousComponent_mem (hd : 0 < d) {f : MvPolynomial (Dmon n d) k}
    (hf : f ∈ veroneseIdeal (k := k) (n := n) (d := d)) (e : ℕ) :
    MvPolynomial.homogeneousComponent e f ∈ veroneseIdeal (k := k) (n := n) (d := d) := by
  rw [mem_veroneseIdeal_iff] at hf ⊢
  have hsum0 : (∑ i ∈ Finset.range (f.totalDegree + 1),
      theta (k := k) (n := n) (d := d) (MvPolynomial.homogeneousComponent i f)) = 0 := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hf]
  have hhom : ∀ i ∈ Finset.range (f.totalDegree + 1),
      (theta (k := k) (n := n) (d := d) (MvPolynomial.homogeneousComponent i f)).IsHomogeneous
        (d * i) := by
    intro i _
    exact theta_isHomogeneous (e := i) (f := MvPolynomial.homogeneousComponent i f)
      (MvPolynomial.homogeneousComponent_isHomogeneous (n := i) (φ := f))
  have hne : ∀ i ∈ Finset.range (f.totalDegree + 1), ∀ j ∈ Finset.range (f.totalDegree + 1),
      d * i = d * j → i = j := by
    intro i _ j _ h
    exact Nat.mul_left_cancel hd h
  have hz := eq_zero_of_sum_homogeneous (Finset.range (f.totalDegree + 1)) _ _ hhom hne hsum0
  by_cases he : e ≤ f.totalDegree
  · exact hz e (Finset.mem_range.2 (by omega))
  · rw [show MvPolynomial.homogeneousComponent e f = 0 from
      MvPolynomial.homogeneousComponent_eq_zero (φ := f) (n := e) (by omega)]
    simp

/-- **Exercise I.2.12 (a)**: `𝔞 = ker θ` is a homogeneous prime ideal, so `Z(𝔞)` is a closed
projective subvariety of `ℙ^N`. -/
theorem part_a (hd : 0 < d) :
    (veroneseIdeal (k := k) (n := n) (d := d)).IsPrime ∧
      ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), ∀ e,
        MvPolynomial.homogeneousComponent e f ∈ veroneseIdeal (k := k) (n := n) (d := d) :=
  ⟨veroneseIdeal_isPrime, fun f hf e => veroneseIdeal_homogeneousComponent_mem (f := f) hd hf e⟩

/-! ## 3. Products of monomials and two general computations -/

/-- A product of monomials is the monomial of the sum of the exponent vectors. -/
theorem monomial_prod {σ τ : Type*} (s : Finset τ) (e : τ → σ →₀ ℕ) :
    (∏ x ∈ s, MvPolynomial.monomial (e x) (1 : k)) = MvPolynomial.monomial (∑ x ∈ s, e x) 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, ih, MvPolynomial.monomial_mul]
      simp

/-- `∑_j α_j • δ_j = α` for a finitely supported family of natural numbers. -/
theorem sum_smul_single_one {ι : Type*} [Fintype ι] (α : ι →₀ ℕ) :
    (∑ j, α j • Finsupp.single j (1 : ℕ)) = α := by
  ext k
  simp

/-- `c ^ m = c * c ^ (m-1)` for `m > 0`. -/
theorem pow_eq_mul_pow_sub_one {c : k} {m : ℕ} (hm : 0 < m) : c ^ m = c * c ^ (m - 1) := by
  rw [show m = (m - 1) + 1 from by omega, pow_succ']
  congr 2

/-- The value of `∑_j δ_j * (α_j · e)` at a point. -/
theorem finsetSum_single_mul_apply {ι : Type*} [Fintype ι] (α : ι →₀ ℕ) (e : ℕ) (k : ι) :
    (∑ j, Finsupp.single j (α j * e)) k = α k * e := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · rw [Finsupp.single_eq_same]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- `∑_j α_j • (e • δ_j) = e • α`. -/
theorem sum_smul_single_mul {ι : Type*} [Fintype ι] (α : ι →₀ ℕ) (e : ℕ) :
    (∑ j, α j • Finsupp.single j e) = e • α := by
  ext k
  rw [Finsupp.smul_apply, smul_eq_mul]
  rw [show (∑ j : ι, α j • Finsupp.single j e) = ∑ j, Finsupp.single j (α j * e) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finsupp.smul_single]
    simp]
  rw [finsetSum_single_mul_apply, mul_comm]

/-- The exponent identity behind the second relation. -/
theorem exp_identity_aux {n d : ℕ} (_hd : 0 < d) (i : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ)
    (hα : ∑ j, α j = d) :
    (d - 1) • Finsupp.single i d + α
      = ∑ j : Fin (n + 1), α j • (Finsupp.single i (d - 1) + Finsupp.single j 1) := by
  have hA : (∑ j : Fin (n + 1), α j • Finsupp.single j (1 : ℕ)) = α := sum_smul_single_one α
  have hB : ∀ j : Fin (n + 1), α j • (Finsupp.single i (d - 1) + Finsupp.single j 1)
      = Finsupp.single i (α j * (d - 1)) + α j • Finsupp.single j 1 := by
    intro j
    rw [smul_add, Finsupp.smul_single, Finsupp.smul_single]
    simp
  rw [Finset.sum_congr rfl (fun j _ => hB j), Finset.sum_add_distrib, hA]
  have hsingle : (∑ j : Fin (n + 1), Finsupp.single i (α j * (d - 1)))
      = Finsupp.single i (∑ j : Fin (n + 1), α j * (d - 1)) :=
    (map_sum (Finsupp.singleAddHom i) (fun j => α j * (d - 1)) Finset.univ).symm
  rw [hsingle, ← Finset.sum_mul, hα]
  have hfin : Finsupp.single i (d * (d - 1)) = (d - 1) • Finsupp.single i d := by
    rw [Finsupp.smul_single]
    simp [mul_comm]
  rw [hfin]

/-- The exponent identity behind the second relation, in the form used below. -/
theorem exp_identity {n d : ℕ} (hd : 0 < d) (i : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ)
    (hα : ∑ j, α j = d) :
    α + (d - 1) • Finsupp.single i d
      = ∑ j : Fin (n + 1), α j • (Finsupp.single i (d - 1) + Finsupp.single j 1) := by
  simpa only [add_comm] using exp_identity_aux hd i α hα

/-! ## 4. The map `ρ_d : ℙⁿ → ℙ^N` -/

/-- The lift of `ρ_d` to vectors: `a ↦ (M_m(a))_m ∈ k^{N+1}`. -/
def rhoLift (a : Fin (n + 1) → k) : Dmon n d → k :=
  fun m => MvPolynomial.eval a (mon (k := k) m)

theorem rhoLift_smul (c : k) (a : Fin (n + 1) → k) :
    rhoLift (k := k) (n := n) (d := d) (c • a)
      = c ^ d • rhoLift (k := k) (n := n) (d := d) a := by
  funext m
  simp only [rhoLift, Pi.smul_apply, smul_eq_mul]
  exact Pp.eval_smul_of_isHomogeneous (mon_isHomogeneous (k := k) m) c a

theorem rhoLift_pure (a : Fin (n + 1) → k) (i : Fin (n + 1)) :
    rhoLift (k := k) (n := n) (d := d) a (Dmon.pure (n := n) (d := d) i) = a i ^ d := by
  rw [rhoLift, mon, Dmon.pure_val, MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_single_index]
  simp

theorem rhoLift_ne_zero (_hd : 0 < d) {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    rhoLift (k := k) (n := n) (d := d) a ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact ha (funext h')
  intro h
  have h2 := congrFun h (Dmon.pure (n := n) (d := d) i)
  rw [rhoLift_pure] at h2
  exact pow_ne_zero d hi h2

/-- **The d-uple embedding** `ρ_d : ℙⁿ → ℙ^N`, `(a) ↦ (M_0(a) : … : M_N(a))`. -/
def rho (hd : 0 < d) (p : Pp k (Fin (n + 1))) : Pp k (Dmon n d) :=
  Quotient.liftOn p (fun v => Pp.mk (rhoLift_ne_zero (k := k) hd v.2)) (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, hvc⟩
    have hvc' : v = c • w := hvc
    have h1 : rhoLift (k := k) (n := n) (d := d) v
        = c ^ d • rhoLift (k := k) (n := n) (d := d) w := by
      rw [hvc', rhoLift_smul]
    exact Quotient.sound ⟨c ^ d, pow_ne_zero d hc, h1⟩)

theorem rho_mk (hd : 0 < d) {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    rho (k := k) hd (Pp.mk hv) = Pp.mk (rhoLift_ne_zero (k := k) hd hv) :=
  rfl

/-- The substitution identity `f(M(a)) = (θ f)(a)`: evaluation of `ρ_d`. -/
theorem eval_aeval' {σ τ : Type*} (v : τ → k) (g : σ → MvPolynomial τ k)
    (f : MvPolynomial σ k) :
    MvPolynomial.eval v (MvPolynomial.aeval g f) =
      MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]

theorem eval_rhoLift (a : Fin (n + 1) → k) (f : MvPolynomial (Dmon n d) k) :
    MvPolynomial.eval (rhoLift (k := k) (n := n) (d := d) a) f
      = MvPolynomial.eval a (theta (k := k) (n := n) (d := d) f) := by
  have h := eval_aeval' (k := k) (σ := Dmon n d) (τ := Fin (n + 1)) a
    (mon (k := k) (n := n) (d := d)) f
  exact h.symm

/-! ## 5. The two relations in `𝔞` -/

/-- The relation `Y_α ^ d = ∏_j Y_{x_j^d} ^ (α_j)`. -/
def rel1 (α : Dmon n d) : MvPolynomial (Dmon n d) k :=
  MvPolynomial.X α ^ d - ∏ j : Fin (n + 1), MvPolynomial.X (Dmon.pure j) ^ (α.1 j)

/-- The relation `Y_α · Y_{x_i^d} ^ (d-1) = ∏_j Y_{x_i^{d-1} x_j} ^ (α_j)`. -/
def rel2 (hd : 0 < d) (α : Dmon n d) (i : Fin (n + 1)) : MvPolynomial (Dmon n d) k :=
  MvPolynomial.X α * MvPolynomial.X (Dmon.pure i) ^ (d - 1) -
    ∏ j : Fin (n + 1), MvPolynomial.X (Dmon.mix hd i j) ^ (α.1 j)

theorem theta_X_pow (m : Dmon n d) (e : ℕ) :
    theta (k := k) (MvPolynomial.X m ^ e)
      = MvPolynomial.monomial (e • m.1) 1 := by
  rw [map_pow, theta_X]
  simp [mon, MvPolynomial.monomial_pow]

theorem theta_prod_X_pow (g : Fin (n + 1) → Dmon n d) (p : Fin (n + 1) → ℕ) :
    theta (k := k) (∏ j : Fin (n + 1), MvPolynomial.X (g j) ^ p j)
      = MvPolynomial.monomial (∑ j, p j • (g j).1) 1 := by
  rw [map_prod]
  simp only [theta_X_pow]
  exact monomial_prod (k := k) Finset.univ (fun j => p j • (g j).1)

theorem rel1_mem (α : Dmon n d) :
    rel1 (k := k) α ∈ veroneseIdeal (k := k) (n := n) (d := d) := by
  rw [mem_veroneseIdeal_iff, rel1, map_sub, theta_X_pow, theta_prod_X_pow]
  simp only [Dmon.pure_val]
  rw [sum_smul_single_mul]
  simp

theorem rel2_mem (hd : 0 < d) (α : Dmon n d) (i : Fin (n + 1)) :
    rel2 (k := k) hd α i ∈ veroneseIdeal (k := k) (n := n) (d := d) := by
  rw [mem_veroneseIdeal_iff, rel2, map_sub, map_mul, theta_X, theta_X_pow, theta_prod_X_pow]
  simp only [Dmon.pure_val, Dmon.mix_val, mon]
  rw [MvPolynomial.monomial_mul, exp_identity hd i α.1 α.sum_eq]
  simp

/-! ## 6. The projective variety `Z(𝔞)` and part (b): `im ρ_d = Z(𝔞)` -/

/-- `Z(𝔞) ⊆ ℙ^N`, the zero locus of the ideal `𝔞 = ker θ`. -/
def Zver : Set (Pp k (Dmon n d)) :=
  Pp.zeroLocus (veroneseIdeal (k := k) (n := n) (d := d) : Set (MvPolynomial (Dmon n d) k))

/-- Membership in `Z(𝔞)` in terms of a representative, for a homogeneous ideal. -/
theorem mem_Zver_iff (hI : ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), ∀ e,
      MvPolynomial.homogeneousComponent e f ∈ veroneseIdeal (k := k) (n := n) (d := d))
    {v : Dmon n d → k} (hv : v ≠ 0) :
    Pp.mk hv ∈ Zver (k := k) (n := n) (d := d) ↔
      ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), MvPolynomial.eval v f = 0 := by
  constructor
  · intro h f hf
    exact Pp.formVanishesAt_mk hv (h f hf)
  · intro h f hf w hw hwp
    obtain ⟨c, hc, hwv⟩ := (Pp.mk_eq_mk_iff hw hv).1 hwp
    have hstep : ∀ e, MvPolynomial.eval w (MvPolynomial.homogeneousComponent e f) = 0 := by
      intro e
      rw [hwv, Pp.eval_smul_of_isHomogeneous
        (MvPolynomial.homogeneousComponent_isHomogeneous (n := e) (φ := f))]
      rw [h _ (hI f hf e), mul_zero]
    have hsum := MvPolynomial.sum_homogeneousComponent f
    calc MvPolynomial.eval w f
        = MvPolynomial.eval w (∑ e ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.homogeneousComponent e f) := by rw [hsum]
      _ = ∑ e ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.eval w (MvPolynomial.homogeneousComponent e f) :=
          map_sum (MvPolynomial.eval w) _ _
      _ = 0 := Finset.sum_eq_zero (fun e _ => hstep e)

theorem eval_rel1 (v : Dmon n d → k) (α : Dmon n d) :
    MvPolynomial.eval v (rel1 (k := k) α)
      = v α ^ d - ∏ j : Fin (n + 1), (v (Dmon.pure (n := n) (d := d) j)) ^ (α.1 j) := by
  simp [rel1]

theorem eval_rel2 (hd : 0 < d) (v : Dmon n d → k) (α : Dmon n d) (i : Fin (n + 1)) :
    MvPolynomial.eval v (rel2 (k := k) hd α i)
      = v α * v (Dmon.pure (n := n) (d := d) i) ^ (d - 1)
        - ∏ j : Fin (n + 1), (v (Dmon.mix (n := n) hd i j)) ^ (α.1 j) := by
  simp [rel2]

/-- The image of `ρ_d` is contained in `Z(𝔞)`: the easy inclusion of part (b). -/
theorem range_rho_subset_Zver (hd : 0 < d) :
    Set.range (rho (k := k) (n := n) (d := d) hd) ⊆ Zver (k := k) (n := n) (d := d) := by
  rintro p ⟨q, rfl⟩
  obtain ⟨a, ha, rfl⟩ := Pp.exists_mk q
  rw [rho_mk]
  rw [mem_Zver_iff (fun f hf e => veroneseIdeal_homogeneousComponent_mem hd hf e)
    (rhoLift_ne_zero (k := k) hd ha)]
  intro f hf
  rw [eval_rhoLift, mem_veroneseIdeal_iff.1 hf, map_zero]

/-- **The hard inclusion of part (b)**: every point of `Z(𝔞)` is of the form
`(M_0(a) : … : M_N(a))` for some `a`. -/
theorem Zver_subset_range (hd : 0 < d) :
    Zver (k := k) (n := n) (d := d) ⊆ Set.range (rho (k := k) (n := n) (d := d) hd) := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := Pp.exists_mk p
  have hvanish := (mem_Zver_iff (fun f hf e => veroneseIdeal_homogeneousComponent_mem hd hf e)
    hv).1 hp
  -- Step 1: some coordinate `v (x_i^d)` is nonzero.
  have hex : ∃ i : Fin (n + 1), v (Dmon.pure (n := n) (d := d) i) ≠ 0 := by
    by_contra h'
    push Not at h'
    have hzero : ∀ α : Dmon n d, v α = 0 := by
      intro α
      have h := hvanish (rel1 (k := k) α) (rel1_mem α)
      rw [eval_rel1] at h
      have hd0 : α.1 ≠ 0 := by
        intro h0
        have hdeg : α.1.degree = 0 := by rw [h0]; simp
        have hdeg2 : α.1.degree = d := α.2
        omega
      obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.2 hd0
      have hj0 : α.1 j ≠ 0 := Finsupp.mem_support_iff.1 hj
      have hprod : (∏ j : Fin (n + 1), (v (Dmon.pure (n := n) (d := d) j)) ^ (α.1 j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h' j]; exact zero_pow hj0)
      rw [hprod, sub_zero] at h
      exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hd)).1 h
    exact hv (funext hzero)
  obtain ⟨i, hi⟩ := hex
  -- Step 2: the candidate preimage `a`, normalized so that `a_i = 1`.
  let av : Fin (n + 1) → k := fun j => v (Dmon.mix hd i j) / v (Dmon.pure i)
  have hmix : ∀ j, v (Dmon.mix hd i j) = av j * v (Dmon.pure i) := by
    intro j
    show v (Dmon.mix hd i j) = (v (Dmon.mix hd i j) / v (Dmon.pure i)) * v (Dmon.pure i)
    field_simp
  have havi : av i = 1 := by
    show v (Dmon.mix hd i i) / v (Dmon.pure i) = 1
    rw [Dmon.mix_self]
    exact div_self hi
  have havne : av ≠ 0 := by
    intro h0
    rw [h0] at havi
    exact zero_ne_one havi
  -- Step 3: the coordinates of `v` are the monomials in `av`, up to the scalar
  -- `v (x_i^d)`.
  have hkey : ∀ α : Dmon n d,
      v α = v (Dmon.pure i) * ∏ j : Fin (n + 1), (av j) ^ (α.1 j) := by
    intro α
    have h := hvanish (rel2 (k := k) hd α i) (rel2_mem hd α i)
    rw [eval_rel2] at h
    have hprod : (∏ j : Fin (n + 1), (v (Dmon.mix hd i j)) ^ (α.1 j))
        = (∏ j : Fin (n + 1), (av j) ^ (α.1 j)) * (v (Dmon.pure i)) ^ d := by
      calc (∏ j : Fin (n + 1), (v (Dmon.mix hd i j)) ^ (α.1 j))
          = ∏ j : Fin (n + 1), (av j * v (Dmon.pure i)) ^ (α.1 j) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            rw [hmix]
        _ = ∏ j : Fin (n + 1), ((av j) ^ (α.1 j) * (v (Dmon.pure i)) ^ (α.1 j)) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            rw [mul_pow]
        _ = (∏ j : Fin (n + 1), (av j) ^ (α.1 j))
              * (∏ j : Fin (n + 1), (v (Dmon.pure i)) ^ (α.1 j)) := Finset.prod_mul_distrib
        _ = (∏ j : Fin (n + 1), (av j) ^ (α.1 j)) * (v (Dmon.pure i)) ^ d := by
            rw [Finset.prod_pow_eq_pow_sum, α.sum_eq]
    rw [hprod] at h
    have hc : v (Dmon.pure i) ^ (d - 1) ≠ 0 := pow_ne_zero _ hi
    have h0 : v α * v (Dmon.pure i) ^ (d - 1)
        = (∏ j : Fin (n + 1), (av j) ^ (α.1 j)) * v (Dmon.pure i) ^ d := sub_eq_zero.1 h
    have h' : v α * v (Dmon.pure i) ^ (d - 1)
        = ((∏ j : Fin (n + 1), (av j) ^ (α.1 j)) * v (Dmon.pure i)) * v (Dmon.pure i) ^ (d - 1) := by
      rw [h0, pow_eq_mul_pow_sub_one hd]
      ring
    rw [mul_right_cancel₀ hc h', mul_comm]
  -- Step 4: the projective points agree.
  have hcoord : ∀ α : Dmon n d,
      rhoLift (k := k) (n := n) (d := d) av α = ∏ j : Fin (n + 1), (av j) ^ (α.1 j) := by
    intro α
    rw [rhoLift, mon, MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro j _ hj
    rw [show α.1 j = 0 by simpa [Finsupp.mem_support_iff] using hj]
    simp
  refine ⟨Pp.mk havne, ?_⟩
  rw [rho_mk]
  rw [Pp.mk_eq_mk_iff']
  refine ⟨v (Dmon.pure i), hi, ?_⟩
  funext α
  rw [Pi.smul_apply, smul_eq_mul, hcoord, ← hkey α]

/-- **Exercise I.2.12 (b)**: the image of `ρ_d` is exactly `Z(𝔞)`. -/
theorem part_b (hd : 0 < d) :
    Set.range (rho (k := k) (n := n) (d := d) hd) = Zver (k := k) (n := n) (d := d) :=
  Set.Subset.antisymm (range_rho_subset_Zver hd) (Zver_subset_range hd)

/-! ## 7. Affine charts of the Veronese variety -/

/-- Step 1 of the calculation of part (b), as a standalone statement: along `Z(𝔞)` some
coordinate `y_{x_i^d}` is nonzero. -/
theorem exists_pure_ne_zero (hd : 0 < d) {v : Dmon n d → k} (hv : v ≠ 0)
    (hvanish : ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), MvPolynomial.eval v f = 0) :
    ∃ i : Fin (n + 1), v (Dmon.pure (n := n) (d := d) i) ≠ 0 := by
  by_contra h'
  push Not at h'
  have hzero : ∀ α : Dmon n d, v α = 0 := by
    intro α
    have h := hvanish (rel1 (k := k) α) (rel1_mem α)
    rw [eval_rel1] at h
    have hd0 : α.1 ≠ 0 := by
      intro h0
      have hdeg : α.1.degree = 0 := by rw [h0]; simp
      have hdeg2 : α.1.degree = d := α.2
      omega
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.2 hd0
    have hj0 : α.1 j ≠ 0 := Finsupp.mem_support_iff.1 hj
    have hprod : (∏ j : Fin (n + 1), (v (Dmon.pure (n := n) (d := d) j)) ^ (α.1 j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h' j]; exact zero_pow hj0)
    rw [hprod, sub_zero] at h
    exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hd)).1 h
  exact hv (funext hzero)

/-- The affine coordinates of a point of `Z(𝔞)` in the chart `y_{x_i^d} ≠ 0`:
`a_j = b_{x_i^{d-1}x_j} / b_{x_i^d}`. -/
def chartVec (hd : 0 < d) (v : Dmon n d → k) (i : Fin (n + 1)) : Fin (n + 1) → k :=
  fun j => v (Dmon.mix hd i j) / v (Dmon.pure i)

theorem chartVec_self (hd : 0 < d) (v : Dmon n d → k) {i : Fin (n + 1)}
    (hi : v (Dmon.pure i) ≠ 0) : chartVec hd v i i = 1 := by
  show v (Dmon.mix hd i i) / v (Dmon.pure i) = 1
  rw [Dmon.mix_self]
  exact div_self hi

theorem chartVec_ne_zero (hd : 0 < d) (v : Dmon n d → k) {i : Fin (n + 1)}
    (hi : v (Dmon.pure i) ≠ 0) : chartVec hd v i ≠ 0 := by
  intro h0
  have h1 := chartVec_self hd v hi
  rw [h0] at h1
  exact zero_ne_one h1

/-- The second relation, read as: on the chart `y_{x_i^d} ≠ 0` the coordinates of a point of
`Z(𝔞)` are the monomials in the affine coordinates, up to the scalar `b_{x_i^d}`. -/
theorem coord_eq_chartVec (hd : 0 < d) {v : Dmon n d → k}
    (hvanish : ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), MvPolynomial.eval v f = 0)
    {i : Fin (n + 1)} (hi : v (Dmon.pure i) ≠ 0) (α : Dmon n d) :
    v α = v (Dmon.pure i) * ∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j) := by
  have h := hvanish (rel2 (k := k) hd α i) (rel2_mem hd α i)
  rw [eval_rel2] at h
  have hmix : ∀ j, v (Dmon.mix hd i j) = chartVec hd v i j * v (Dmon.pure i) := by
    intro j
    show v (Dmon.mix hd i j)
      = (v (Dmon.mix hd i j) / v (Dmon.pure i)) * v (Dmon.pure i)
    field_simp
  have hprod : (∏ j : Fin (n + 1), (v (Dmon.mix hd i j)) ^ (α.1 j))
      = (∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j)) * (v (Dmon.pure i)) ^ d := by
    calc (∏ j : Fin (n + 1), (v (Dmon.mix hd i j)) ^ (α.1 j))
        = ∏ j : Fin (n + 1), (chartVec hd v i j * v (Dmon.pure i)) ^ (α.1 j) := by
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rw [hmix]
      _ = ∏ j : Fin (n + 1),
            ((chartVec hd v i j) ^ (α.1 j) * (v (Dmon.pure i)) ^ (α.1 j)) := by
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rw [mul_pow]
      _ = (∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j))
            * (∏ j : Fin (n + 1), (v (Dmon.pure i)) ^ (α.1 j)) := Finset.prod_mul_distrib
      _ = (∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j)) * (v (Dmon.pure i)) ^ d := by
          rw [Finset.prod_pow_eq_pow_sum, α.sum_eq]
  rw [hprod] at h
  have hc : v (Dmon.pure i) ^ (d - 1) ≠ 0 := pow_ne_zero _ hi
  have h0 : v α * v (Dmon.pure i) ^ (d - 1)
      = (∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j)) * v (Dmon.pure i) ^ d :=
    sub_eq_zero.1 h
  have h' : v α * v (Dmon.pure i) ^ (d - 1)
      = ((∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j)) * v (Dmon.pure i))
        * v (Dmon.pure i) ^ (d - 1) := by
    rw [h0, pow_eq_mul_pow_sub_one hd]
    ring
  rw [mul_right_cancel₀ hc h', mul_comm]

/-- The coordinates of `ρ_d` applied to the chart point. -/
theorem rhoLift_chartVec (hd : 0 < d) (v : Dmon n d → k) (i : Fin (n + 1)) (α : Dmon n d) :
    rhoLift (k := k) (n := n) (d := d) (chartVec hd v i) α
      = ∏ j : Fin (n + 1), (chartVec hd v i j) ^ (α.1 j) := by
  rw [rhoLift, mon, MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro j _ hj
  rw [show α.1 j = 0 by simpa [Finsupp.mem_support_iff] using hj]
  simp

/-- On the chart `y_{x_i^d} ≠ 0`, `ρ_d` of the affine coordinates returns the point. -/
theorem rho_chartVec (hd : 0 < d) {v : Dmon n d → k} (hv : v ≠ 0)
    (hvanish : ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), MvPolynomial.eval v f = 0)
    {i : Fin (n + 1)} (hi : v (Dmon.pure i) ≠ 0) :
    rho (k := k) hd (Pp.mk (chartVec_ne_zero hd v hi)) = Pp.mk hv := by
  rw [rho_mk, Pp.mk_eq_mk_iff']
  refine ⟨v (Dmon.pure i), hi, ?_⟩
  funext α
  rw [Pi.smul_apply, smul_eq_mul, rhoLift_chartVec, ← coord_eq_chartVec hd hvanish hi α]

/-! ### The substitution `Hsub` and its two evaluation formulae -/

/-- The substitution `y_{x_i^{d-1}x_j} ↦ y_j` applied to a polynomial `h ∈ k[x₀,…,x_n]`. -/
def Hsub (hd : 0 < d) (i : Fin (n + 1)) (h : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Dmon n d) k :=
  MvPolynomial.aeval (fun j => MvPolynomial.X (Dmon.mix hd i j)) h

theorem Hsub_isHomogeneous (hd : 0 < d) (i : Fin (n + 1)) {h : MvPolynomial (Fin (n + 1)) k}
    {D : ℕ} (hh : h.IsHomogeneous D) : (Hsub (k := k) hd i h).IsHomogeneous D := by
  simpa [Hsub] using hh.aeval _
    (fun j => MvPolynomial.isHomogeneous_X (σ := Dmon n d) (R := k) (Dmon.mix hd i j))

theorem eval_Hsub (hd : 0 < d) (i : Fin (n + 1)) (v : Dmon n d → k)
    (h : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial.eval v (Hsub (k := k) hd i h)
      = MvPolynomial.eval (fun j => v (Dmon.mix hd i j)) h := by
  rw [Hsub]
  simpa using eval_aeval' v (fun j => MvPolynomial.X (Dmon.mix hd i j)) h

theorem rhoLift_mix (hd : 0 < d) (a : Fin (n + 1) → k) (i j : Fin (n + 1)) :
    rhoLift (k := k) (n := n) (d := d) a (Dmon.mix hd i j) = a i ^ (d - 1) * a j := by
  rw [rhoLift, mon, Dmon.mix_val]
  rw [show MvPolynomial.monomial (Finsupp.single i (d - 1) + Finsupp.single j 1) (1 : k)
      = MvPolynomial.monomial (Finsupp.single i (d - 1)) 1
        * MvPolynomial.monomial (Finsupp.single j 1) 1 from by
    rw [MvPolynomial.monomial_mul]; simp]
  rw [map_mul, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  rw [one_mul, Finsupp.prod_single_index (h_zero := by simp),
    Finsupp.prod_single_index (h_zero := by simp), pow_one]
  ring

theorem eval_Hsub_rhoLift (hd : 0 < d) (i : Fin (n + 1)) (a : Fin (n + 1) → k)
    {h : MvPolynomial (Fin (n + 1)) k} {D : ℕ} (hh : h.IsHomogeneous D) :
    MvPolynomial.eval (rhoLift (k := k) (n := n) (d := d) a) (Hsub (k := k) hd i h)
      = (a i ^ (d - 1)) ^ D * MvPolynomial.eval a h := by
  rw [eval_Hsub]
  have hvec : (fun j => rhoLift (k := k) (n := n) (d := d) a (Dmon.mix hd i j))
      = (a i ^ (d - 1)) • a := by
    funext j
    rw [rhoLift_mix]
    simp [smul_eq_mul]
  rw [hvec]
  exact Pp.eval_smul_of_isHomogeneous hh _ a

theorem eval_Hsub_chartVec (hd : 0 < d) (v : Dmon n d → k) {i : Fin (n + 1)}
    (hi : v (Dmon.pure i) ≠ 0) {h : MvPolynomial (Fin (n + 1)) k} {D : ℕ}
    (hh : h.IsHomogeneous D) :
    MvPolynomial.eval v (Hsub (k := k) hd i h)
      = (v (Dmon.pure i)) ^ D * MvPolynomial.eval (chartVec hd v i) h := by
  rw [eval_Hsub]
  have hvec : (fun j => v (Dmon.mix hd i j)) = (v (Dmon.pure i)) • chartVec hd v i := by
    funext j
    show v (Dmon.mix hd i j) = v (Dmon.pure i) * (v (Dmon.mix hd i j) / v (Dmon.pure i))
    field_simp
  rw [hvec]
  exact Pp.eval_smul_of_isHomogeneous hh _ _

/-! ## 8. Part (c): `ρ_d` is a homeomorphism onto `Z(𝔞)` -/

/-- Projective space over a nonempty coordinate set is nonempty. -/
instance Pp.instNonempty {ι : Type*} [Nonempty ι] : Nonempty (Pp k ι) :=
  ⟨Pp.mk (v := fun _ => (1 : k)) (by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact zero_ne_one (congrFun h i).symm)⟩

theorem theta_image_homogeneous {S : Set (MvPolynomial (Dmon n d) k)}
    (hS : ∀ f ∈ S, ∃ D, f.IsHomogeneous D) :
    ∀ f ∈ theta (k := k) (n := n) (d := d) '' S, ∃ D, f.IsHomogeneous D := by
  rintro _ ⟨g, hgT, rfl⟩
  obtain ⟨D, hD⟩ := hS g hgT
  exact ⟨d * D, theta_isHomogeneous hD⟩

/-- The pullback formula for closed sets: `ρ_d⁻¹ Z(S) = Z(θ S)`. -/
theorem rho_preimage_zeroLocus (hd : 0 < d) {S : Set (MvPolynomial (Dmon n d) k)}
    (hS : ∀ f ∈ S, ∃ D, f.IsHomogeneous D) :
    rho (k := k) (n := n) (d := d) hd ⁻¹' (Pp.zeroLocus (ι := Dmon n d) S)
      = Pp.zeroLocus (ι := Fin (n + 1)) (theta (k := k) (n := n) (d := d) '' S) := by
  ext p
  obtain ⟨a, ha, rfl⟩ := Pp.exists_mk p
  rw [Set.mem_preimage, rho_mk,
    Pp.mem_zeroLocus_iff (ι := Dmon n d) hS (rhoLift_ne_zero (k := k) hd ha),
    Pp.mem_zeroLocus_iff (ι := Fin (n + 1)) (v := a)
      (theta_image_homogeneous hS) ha]
  constructor
  · intro h f hf
    obtain ⟨g, hgS, rfl⟩ := hf
    rw [← eval_rhoLift]
    exact h g hgS
  · intro h g hgS
    have h1 : (MvPolynomial.eval a) (theta (k := k) (n := n) (d := d) g) = 0 :=
      h _ ⟨g, hgS, rfl⟩
    rw [eval_rhoLift]
    exact h1

theorem rho_continuous (hd : 0 < d) :
    Continuous (rho (k := k) (n := n) (d := d) hd) := by
  refine continuous_iff_isClosed.2 ?_
  intro Z hZ
  obtain ⟨S, hS, rfl⟩ := Pp.isClosed_iff_exists_zeroLocus.1 hZ
  rw [rho_preimage_zeroLocus hd hS]
  exact Pp.isClosed_zeroLocus (theta_image_homogeneous hS)

/-- `ρ_d` as a map onto `Z(𝔞)`. -/
def rhoSet (hd : 0 < d) (p : Pp k (Fin (n + 1))) : Zver (k := k) (n := n) (d := d) :=
  ⟨rho (k := k) (n := n) (d := d) hd p, range_rho_subset_Zver hd ⟨p, rfl⟩⟩

theorem rhoSet_continuous (hd : 0 < d) : Continuous (rhoSet (k := k) (n := n) (d := d) hd) :=
  Continuous.subtype_mk (rho_continuous hd) _

/-- The chart coordinates of a point of `𝔸ⁿ` are recovered from the image point: on the chart
`a_i ≠ 0`, `chartVec (ρ_d a) i = a_i⁻¹ • a`. -/
theorem chartVec_rhoLift (hd : 0 < d) (a : Fin (n + 1) → k) {i : Fin (n + 1)} (hi : a i ≠ 0) :
    chartVec hd (rhoLift (k := k) (n := n) (d := d) a) i = (a i)⁻¹ • a := by
  funext j
  rw [chartVec, Pi.smul_apply, smul_eq_mul, rhoLift_mix, rhoLift_pure]
  have hpow : a i ^ d = a i ^ (d - 1) * a i := by
    conv_lhs => rw [show d = (d - 1) + 1 from by omega]
    rw [pow_succ]
  rw [hpow]
  field_simp

theorem chartVec_smul (hd : 0 < d) (v : Dmon n d → k) {c : k} (hc : c ≠ 0)
    (i : Fin (n + 1)) : chartVec hd (c • v) i = chartVec hd v i := by
  funext j
  show (c • v) (Dmon.mix hd i j) / (c • v) (Dmon.pure i)
    = v (Dmon.mix hd i j) / v (Dmon.pure i)
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  field_simp

/-- **Injectivity of `ρ_d`**. -/
theorem rho_injective (hd : 0 < d) :
    Function.Injective (rho (k := k) (n := n) (d := d) hd) := by
  intro p q hpq
  obtain ⟨a, ha, rfl⟩ := Pp.exists_mk p
  obtain ⟨b, hb, rfl⟩ := Pp.exists_mk q
  have hva : rhoLift (k := k) (n := n) (d := d) a ≠ 0 := rhoLift_ne_zero (k := k) hd ha
  have hvb : rhoLift (k := k) (n := n) (d := d) b ≠ 0 := rhoLift_ne_zero (k := k) hd hb
  have h1 : Pp.mk hva = Pp.mk hvb := hpq
  obtain ⟨c, hc, hcab⟩ := (Pp.mk_eq_mk_iff hva hvb).1 h1
  have hQ : ∃ i, a i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact ha (funext h')
  obtain ⟨i, hi⟩ := hQ
  have hbi : b i ≠ 0 := by
    intro h0
    have h2 : rhoLift (k := k) (n := n) (d := d) a (Dmon.pure i) = 0 := by
      rw [hcab, Pi.smul_apply, rhoLift_pure, h0, smul_eq_mul,
        zero_pow (Nat.pos_iff_ne_zero.mp hd), mul_zero]
    rw [rhoLift_pure] at h2
    exact pow_ne_zero d hi h2
  have hcv : chartVec hd (rhoLift (k := k) (n := n) (d := d) a) i
      = chartVec hd (rhoLift (k := k) (n := n) (d := d) b) i := by
    rw [hcab, chartVec_smul hd _ hc]
  rw [chartVec_rhoLift hd a hi, chartVec_rhoLift hd b hbi] at hcv
  rw [Pp.mk_eq_mk_iff]
  refine ⟨a i * (b i)⁻¹, mul_ne_zero hi (inv_ne_zero hbi), ?_⟩
  calc a = a i • ((a i)⁻¹ • a) := by rw [smul_smul, mul_inv_cancel₀ hi, one_smul]
    _ = a i • ((b i)⁻¹ • b) := by rw [hcv]
    _ = (a i * (b i)⁻¹) • b := by rw [smul_smul]

/-- `ρ_d` is surjective onto `Z(𝔞)` (part (b)). -/
theorem rhoSet_surjective (hd : 0 < d) :
    Function.Surjective (rhoSet (k := k) (n := n) (d := d) hd) := by
  intro q
  obtain ⟨p, hp⟩ := Zver_subset_range hd q.2
  exact ⟨p, Subtype.ext hp⟩

theorem rhoSet_injective (hd : 0 < d) :
    Function.Injective (rhoSet (k := k) (n := n) (d := d) hd) := by
  intro p q hpq
  exact rho_injective hd (congrArg Subtype.val hpq)

/-- The image of a closed set under `ρ_d` is closed: the substitutions `Hsub i` transport the
equations of the closed set to equations on `Z(𝔞)`. -/
theorem rhoSet_image_zeroLocus (hd : 0 < d) {T : Set (MvPolynomial (Fin (n + 1)) k)}
    (hT : ∀ f ∈ T, ∃ D, f.IsHomogeneous D) :
    rhoSet (k := k) (n := n) (d := d) hd '' (Pp.zeroLocus (ι := Fin (n + 1)) T)
      = {q : Zver (k := k) (n := n) (d := d) |
          (q : Pp k (Dmon n d)) ∈
            Pp.zeroLocus (ι := Dmon n d) (⋃ i, Hsub (k := k) hd i '' T)} := by
  have hS : ∀ f ∈ (⋃ i : Fin (n + 1), Hsub (k := k) hd i '' T), ∃ D, f.IsHomogeneous D := by
    intro f hf
    obtain ⟨i, h, hhT, rfl⟩ := Set.mem_iUnion.1 hf
    obtain ⟨D, hD⟩ := hT h hhT
    exact ⟨D, Hsub_isHomogeneous hd i hD⟩
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Pp.exists_mk p
    show Pp.mk (rhoLift_ne_zero (k := k) hd ha) ∈
      Pp.zeroLocus (ι := Dmon n d) (⋃ i, Hsub (k := k) hd i '' T)
    rw [Pp.mem_zeroLocus_iff (ι := Dmon n d) hS (rhoLift_ne_zero (k := k) hd ha)]
    intro f hf
    obtain ⟨i, h, hhT, rfl⟩ := Set.mem_iUnion.1 hf
    obtain ⟨D, hD⟩ := hT h hhT
    rw [eval_Hsub_rhoLift hd i a hD,
      Pp.mem_zeroLocus_iff (ι := Fin (n + 1)) hT ha |>.1 hp h hhT, mul_zero]
  · intro hq
    obtain ⟨v, hv, hvq⟩ := Pp.exists_mk (q : Pp k (Dmon n d))
    have hvanish : ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d),
        MvPolynomial.eval v f = 0 :=
      (mem_Zver_iff (fun f hf e => veroneseIdeal_homogeneousComponent_mem hd hf e) hv).1
        (hvq ▸ q.2)
    have hqS : ∀ f ∈ (⋃ i : Fin (n + 1), Hsub (k := k) hd i '' T),
        MvPolynomial.eval v f = 0 := by
      have hq' : Pp.mk hv ∈ Pp.zeroLocus (ι := Dmon n d)
          (⋃ i, Hsub (k := k) hd i '' T) := by
        rw [hvq]; exact hq
      exact (Pp.mem_zeroLocus_iff (ι := Dmon n d) hS hv).1 hq'
    obtain ⟨i, hi⟩ := exists_pure_ne_zero hd hv hvanish
    refine ⟨Pp.mk (chartVec_ne_zero hd v hi), ?_, ?_⟩
    · rw [Pp.mem_zeroLocus_iff (ι := Fin (n + 1)) hT (chartVec_ne_zero hd v hi)]
      intro h hhT
      obtain ⟨D, hD⟩ := hT h hhT
      have h1 : MvPolynomial.eval v (Hsub (k := k) hd i h) = 0 :=
        hqS _ (Set.mem_iUnion.2 ⟨i, Set.mem_image_of_mem _ hhT⟩)
      rw [eval_Hsub_chartVec hd v hi hD] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero D hi)
    · refine Subtype.ext ?_
      show rho (k := k) (n := n) (d := d) hd (Pp.mk (chartVec_ne_zero hd v hi)) = (q : Pp k (Dmon n d))
      rw [rho_chartVec hd hv hvanish hi, hvq]

/-- The image of a closed set under `ρ_d` is closed in `Z(𝔞)`. -/
theorem rhoSet_isClosedMap (hd : 0 < d) :
    IsClosedMap (rhoSet (k := k) (n := n) (d := d) hd) := by
  intro F hF
  obtain ⟨T, hT, rfl⟩ := Pp.isClosed_iff_exists_zeroLocus.1 hF
  have hS : IsClosed (Pp.zeroLocus (ι := Dmon n d) (⋃ i : Fin (n + 1),
      Hsub (k := k) hd i '' T)) := by
    refine Pp.isClosed_zeroLocus ?_
    intro f hf
    obtain ⟨i, h, hhT, rfl⟩ := Set.mem_iUnion.1 hf
    obtain ⟨D, hD⟩ := hT h hhT
    exact ⟨D, Hsub_isHomogeneous hd i hD⟩
  rw [rhoSet_image_zeroLocus hd hT]
  exact hS.preimage continuous_subtype_val

/-- The image of an open set under `ρ_d` is open in `Z(𝔞)`. -/
theorem rhoSet_isOpenMap (hd : 0 < d) :
    IsOpenMap (rhoSet (k := k) (n := n) (d := d) hd) := by
  intro U hU
  have himg : rhoSet (k := k) (n := n) (d := d) hd '' U
      = (rhoSet (k := k) (n := n) (d := d) hd '' Uᶜ)ᶜ := by
    ext q
    constructor
    · intro hq hqc
      obtain ⟨u, hu, rfl⟩ := hq
      obtain ⟨u', hu', huu'⟩ := hqc
      have huu : u' = u := rhoSet_injective hd huu'
      rw [huu] at hu'
      exact hu' hu
    · intro hq
      by_contra hqc
      have hmem : rhoSet (k := k) (n := n) (d := d) hd
          (Function.invFun (rhoSet (k := k) (n := n) (d := d) hd) q) = q :=
        Function.rightInverse_invFun (rhoSet_surjective hd) q
      have hinvU : Function.invFun (rhoSet (k := k) (n := n) (d := d) hd) q ∉ U :=
        fun hU => hqc ⟨_, hU, hmem⟩
      exact hq ⟨_, hinvU, hmem⟩
  rw [himg]
  exact (rhoSet_isClosedMap hd _ hU.isClosed_compl).isOpen_compl

theorem continuous_invFun_rhoSet (hd : 0 < d) :
    Continuous (Function.invFun (rhoSet (k := k) (n := n) (d := d) hd)) := by
  rw [continuous_def]
  intro U hU
  have hpre : (Function.invFun (rhoSet (k := k) (n := n) (d := d) hd)) ⁻¹' U
      = rhoSet (k := k) (n := n) (d := d) hd '' U := by
    ext q
    constructor
    · intro hq
      exact ⟨Function.invFun (rhoSet (k := k) (n := n) (d := d) hd) q, hq,
        Function.rightInverse_invFun (rhoSet_surjective hd) q⟩
    · rintro ⟨u, hu, rfl⟩
      show Function.invFun (rhoSet (k := k) (n := n) (d := d) hd)
        (rhoSet (k := k) (n := n) (d := d) hd u) ∈ U
      rw [Function.leftInverse_invFun (rhoSet_injective hd)]
      exact hu
  rw [hpre]
  exact rhoSet_isOpenMap hd U hU

/-- **Exercise I.2.12 (c)**: `ρ_d` is a homeomorphism of `ℙⁿ` onto the projective variety
`Z(𝔞)`. -/
def part_c (hd : 0 < d) :
    Pp k (Fin (n + 1)) ≃ₜ Zver (k := k) (n := n) (d := d) where
  toFun := rhoSet (k := k) (n := n) (d := d) hd
  invFun := Function.invFun (rhoSet (k := k) (n := n) (d := d) hd)
  left_inv := Function.leftInverse_invFun (rhoSet_injective hd)
  right_inv := Function.rightInverse_invFun (rhoSet_surjective hd)
  continuous_toFun := rhoSet_continuous hd
  continuous_invFun := continuous_invFun_rhoSet hd

/-! ## 9. Part (d): the twisted cubic is the 3-uple embedding of `ℙ¹` in `ℙ³` -/

/-- The four monomials `x_0^3, x_0^2x_1, x_0x_1^2, x_1^3` of degree `3` in two variables. -/
def tc0 : Dmon 1 3 := Dmon.pure (n := 1) (d := 3) 0
def tc1 : Dmon 1 3 := Dmon.mix (n := 1) (d := 3) (by norm_num) 0 1
def tc2 : Dmon 1 3 := Dmon.mix (n := 1) (d := 3) (by norm_num) 1 0
def tc3 : Dmon 1 3 := Dmon.pure (n := 1) (d := 3) 1

/-- Every degree-`3` monomial in `x_0, x_1` is one of `x_0^3, x_0^2x_1, x_0x_1^2, x_1^3`. -/
theorem Dmon_one_three_cases (α : Dmon 1 3) :
    α = tc0 ∨ α = tc1 ∨ α = tc2 ∨ α = tc3 := by
  have hsum : α.1 0 + α.1 1 = 3 := by
    have h := α.sum_eq
    rwa [Fin.sum_univ_two] at h
  have hexp : α.1 = Finsupp.single 0 (α.1 0) + Finsupp.single 1 (α.1 1) := by
    ext j
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    fin_cases j <;> simp
  have h3 : ∀ (a b : ℕ), a + b = 3 → a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
    intro a b hab
    have ha : a ≤ 3 := by omega
    interval_cases a <;> omega
  rcases h3 (α.1 0) (α.1 1) hsum with h | h | h | h
  · have hb : α.1 1 = 3 := by omega
    have hα : α.1 = Finsupp.single 1 3 := by
      rw [hexp, h, hb]
      ext j; fin_cases j <;> simp
    right; right; right
    exact Subtype.ext (hα.trans rfl)
  · have hb : α.1 1 = 2 := by omega
    have hα : α.1 = Finsupp.single 1 2 + Finsupp.single 0 1 := by
      rw [hexp, h, hb]
      ext j; fin_cases j <;> simp
    right; right; left
    exact Subtype.ext (hα.trans rfl)
  · have hb : α.1 1 = 1 := by omega
    have hα : α.1 = Finsupp.single 0 2 + Finsupp.single 1 1 := by
      rw [hexp, h, hb]
    right; left
    exact Subtype.ext (hα.trans rfl)
  · have hb : α.1 1 = 0 := by omega
    have hα : α.1 = Finsupp.single 0 3 := by
      rw [hexp, h, hb]
      ext j; fin_cases j <;> simp
    left
    exact Subtype.ext (hα.trans rfl)

/-- Splitting a monomial. -/
theorem monomial_add_one {σ : Type*} (s t : σ →₀ ℕ) :
    MvPolynomial.monomial (s + t) (1 : k)
      = MvPolynomial.monomial s 1 * MvPolynomial.monomial t 1 := by
  rw [MvPolynomial.monomial_mul, mul_one]

theorem monomial_add_one' {σ : Type*} (s t : σ →₀ ℕ) :
    MvPolynomial.monomial (t + s) (1 : k)
      = MvPolynomial.monomial s 1 * MvPolynomial.monomial t 1 := by
  rw [add_comm t s, monomial_add_one]

/-- The monomials `x_0^3, x_0^2x_1, x_0x_1^2, x_1^3` as polynomials. -/
theorem mon_tc0 : mon (k := k) tc0 = MvPolynomial.X (0 : Fin 2) ^ 3 := by
  rw [mon, tc0, Dmon.pure_val, MvPolynomial.X_pow_eq_monomial]

theorem mon_tc3 : mon (k := k) tc3 = MvPolynomial.X (1 : Fin 2) ^ 3 := by
  rw [mon, tc3, Dmon.pure_val, MvPolynomial.X_pow_eq_monomial]

theorem mon_tc1 : mon (k := k) tc1
    = MvPolynomial.X (0 : Fin 2) ^ 2 * MvPolynomial.X (1 : Fin 2) := by
  have hX1 : MvPolynomial.X (1 : Fin 2) = MvPolynomial.monomial (Finsupp.single 1 1) (1 : k) := by
    rw [← MvPolynomial.X_pow_eq_monomial]; simp
  have hX0 : MvPolynomial.X (0 : Fin 2) ^ 2 = MvPolynomial.monomial (Finsupp.single 0 2) (1 : k) :=
    MvPolynomial.X_pow_eq_monomial
  rw [hX0, hX1, mon, tc1, Dmon.mix_val, show (3 : ℕ) - 1 = 2 from rfl]
  rw [monomial_add_one (s := Finsupp.single 0 2) (t := Finsupp.single 1 1)]

theorem mon_tc2 : mon (k := k) tc2
    = MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ^ 2 := by
  have hX0 : MvPolynomial.X (0 : Fin 2) = MvPolynomial.monomial (Finsupp.single 0 1) (1 : k) := by
    rw [← MvPolynomial.X_pow_eq_monomial]; simp
  have hX1 : MvPolynomial.X (1 : Fin 2) ^ 2 = MvPolynomial.monomial (Finsupp.single 1 2) (1 : k) :=
    MvPolynomial.X_pow_eq_monomial
  rw [hX0, hX1, mon, tc2, Dmon.mix_val, show (3 : ℕ) - 1 = 2 from rfl]
  rw [monomial_add_one' (s := Finsupp.single 0 1) (t := Finsupp.single 1 2)]

/-- The coordinates of `ρ_3` are the monomials. -/
theorem rhoLift_tc0 (a : Fin 2 → k) :
    rhoLift (k := k) (n := 1) (d := 3) a tc0 = a 0 ^ 3 := by
  rw [rhoLift, mon_tc0]; simp

theorem rhoLift_tc1 (a : Fin 2 → k) :
    rhoLift (k := k) (n := 1) (d := 3) a tc1 = a 0 ^ 2 * a 1 := by
  rw [rhoLift, mon_tc1]; simp

theorem rhoLift_tc2 (a : Fin 2 → k) :
    rhoLift (k := k) (n := 1) (d := 3) a tc2 = a 0 * a 1 ^ 2 := by
  rw [rhoLift, mon_tc2]; simp

theorem rhoLift_tc3 (a : Fin 2 → k) :
    rhoLift (k := k) (n := 1) (d := 3) a tc3 = a 1 ^ 3 := by
  rw [rhoLift, mon_tc3]; simp

/-- The three `2 × 2` minors `x_0x_2 - x_1^2`, `x_0x_3 - x_1x_2`, `x_1x_3 - x_2^2` of the
twisted cubic, as polynomials in the coordinates `y_{tc0}, …, y_{tc3}` of `ℙ³`. -/
def tcM1 : MvPolynomial (Dmon 1 3) k :=
  MvPolynomial.X tc0 * MvPolynomial.X tc2 - MvPolynomial.X tc1 ^ 2
def tcM2 : MvPolynomial (Dmon 1 3) k :=
  MvPolynomial.X tc0 * MvPolynomial.X tc3 - MvPolynomial.X tc1 * MvPolynomial.X tc2
def tcM3 : MvPolynomial (Dmon 1 3) k :=
  MvPolynomial.X tc1 * MvPolynomial.X tc3 - MvPolynomial.X tc2 ^ 2

/-- **The twisted cubic curve** of Exercise I.2.9 in `ℙ³ = ℙ^{Dmon 1 3}`. -/
def twistedCubic : Set (Pp k (Dmon 1 3)) :=
  Pp.zeroLocus ({tcM1 (k := k), tcM2 (k := k), tcM3 (k := k)} : Set (MvPolynomial (Dmon 1 3) k))

theorem tcM_mem : ∀ f ∈ ({tcM1 (k := k), tcM2 (k := k), tcM3 (k := k)} :
      Set (MvPolynomial (Dmon 1 3) k)), ∃ D, f.IsHomogeneous D := by
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  have hX : ∀ m : Dmon 1 3, (MvPolynomial.X m : MvPolynomial (Dmon 1 3) k).IsHomogeneous 1 :=
    fun m => MvPolynomial.isHomogeneous_X (σ := Dmon 1 3) (R := k) m
  rcases hf with rfl | rfl | rfl
  · rw [tcM1]
    exact ⟨2, (hX tc0).mul (hX tc2) |>.sub ((hX tc1).pow 2)⟩
  · rw [tcM2]
    exact ⟨2, (hX tc0).mul (hX tc3) |>.sub ((hX tc1).mul (hX tc2))⟩
  · rw [tcM3]
    exact ⟨2, (hX tc1).mul (hX tc3) |>.sub ((hX tc2).pow 2)⟩

/-- The three minors lie in `𝔞 = ker θ`: they vanish on the image of `ρ_3`. -/
theorem tcM_mem_ker : ∀ f ∈ ({tcM1 (k := k), tcM2 (k := k), tcM3 (k := k)} :
      Set (MvPolynomial (Dmon 1 3) k)), f ∈ veroneseIdeal (k := k) (n := 1) (d := 3) := by
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rw [mem_veroneseIdeal_iff]
  rcases hf with rfl | rfl | rfl
  · rw [tcM1]
    simp only [map_sub, map_mul, map_pow, theta_X, mon_tc0, mon_tc1, mon_tc2]
    ring
  · rw [tcM2]
    simp only [map_sub, map_mul, theta_X, mon_tc0, mon_tc1, mon_tc2, mon_tc3]
    ring
  · rw [tcM3]
    simp only [map_sub, map_mul, map_pow, theta_X, mon_tc1, mon_tc2, mon_tc3]
    ring

/-- The ideal `𝔞` of the 3-uple embedding contains the ideal of the twisted cubic. -/
theorem Zver_subset_twistedCubic :
    Zver (k := k) (n := 1) (d := 3) ⊆ twistedCubic (k := k) := by
  intro q hq
  obtain ⟨v, hv, hvq⟩ := Pp.exists_mk q
  have hvanish : ∀ f ∈ veroneseIdeal (k := k) (n := 1) (d := 3),
      MvPolynomial.eval v f = 0 :=
    (mem_Zver_iff (fun f hf e => veroneseIdeal_homogeneousComponent_mem (by norm_num) hf e) hv).1
      (hvq ▸ hq)
  rw [twistedCubic, ← hvq, Pp.mem_zeroLocus_iff tcM_mem hv]
  exact fun f hf => hvanish f (tcM_mem_ker f hf)

/-- **The twisted cubic is the image of the 3-uple embedding of `ℙ¹`**. -/
theorem twistedCubic_subset_Zver :
    twistedCubic (k := k) ⊆ Zver (k := k) (n := 1) (d := 3) := by
  intro q hq
  obtain ⟨v, hv, hvq⟩ := Pp.exists_mk q
  have hvq' : Pp.mk hv ∈ twistedCubic (k := k) := hvq ▸ hq
  have hM : ∀ f ∈ ({tcM1 (k := k), tcM2 (k := k), tcM3 (k := k)} :
      Set (MvPolynomial (Dmon 1 3) k)), MvPolynomial.eval v f = 0 :=
    (Pp.mem_zeroLocus_iff tcM_mem hv).1 hvq'
  have hm1 : v tc0 * v tc2 - v tc1 ^ 2 = 0 := by simpa [tcM1] using hM tcM1 (by simp)
  have hm2 : v tc0 * v tc3 - v tc1 * v tc2 = 0 := by simpa [tcM2] using hM tcM2 (by simp)
  have hm3 : v tc1 * v tc3 - v tc2 ^ 2 = 0 := by simpa [tcM3] using hM tcM3 (by simp)
  have hm1' : v tc0 * v tc2 = v tc1 ^ 2 := sub_eq_zero.1 hm1
  have hm2' : v tc0 * v tc3 = v tc1 * v tc2 := sub_eq_zero.1 hm2
  have hm3' : v tc1 * v tc3 = v tc2 ^ 2 := sub_eq_zero.1 hm3
  rw [← part_b (by norm_num : (0 : ℕ) < 3)]
  rcases eq_or_ne (v tc0) 0 with hzero | hne
  · -- the point `(0 : 1)`
    have hv1 : v tc1 = 0 := by
      have h : v tc1 ^ 2 = 0 := by rw [← hm1', hzero, zero_mul]
      exact (pow_eq_zero_iff (by norm_num)).1 h
    have hv2 : v tc2 = 0 := by
      have h : v tc2 ^ 2 = 0 := by rw [← hm3', hv1, zero_mul]
      exact (pow_eq_zero_iff (by norm_num)).1 h
    have hv3 : v tc3 ≠ 0 := by
      intro h3
      apply hv
      funext α
      rcases Dmon_one_three_cases α with rfl | rfl | rfl | rfl
      exacts [hzero, hv1, hv2, h3]
    set b : Fin 2 → k := fun j => if j = 0 then 0 else 1 with hbdef
    have hb0 : b 0 = 0 := by simp [hbdef]
    have hb1 : b 1 = 1 := by simp [hbdef]
    have hbne : b ≠ 0 := by
      intro h
      rw [h] at hb1
      exact zero_ne_one hb1
    refine ⟨Pp.mk hbne, ?_⟩
    rw [rho_mk, ← hvq, Pp.mk_eq_mk_iff']
    refine ⟨v tc3, hv3, ?_⟩
    funext α
    rcases Dmon_one_three_cases α with rfl | rfl | rfl | rfl
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc0, hb0]
      simp [hzero]
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc1, hb0, hb1]
      simp [hv1]
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc2, hb0, hb1]
      simp [hv2]
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc3, hb1]
      simp
  · -- the chart `y_{x_0^3} ≠ 0`: the point `(1 : b_1/b_0)`
    have hv1sq : v tc2 = v tc1 ^ 2 / v tc0 := by
      field_simp
      simpa [mul_comm] using hm1'
    have hv3eq : v tc3 = v tc1 ^ 3 / v tc0 ^ 2 := by
      have h2 : v tc0 ^ 2 * v tc3 = v tc1 ^ 3 := by
        calc v tc0 ^ 2 * v tc3 = v tc0 * (v tc0 * v tc3) := by ring
          _ = v tc0 * (v tc1 * v tc2) := by rw [hm2']
          _ = v tc1 * (v tc0 * v tc2) := by ring
          _ = v tc1 * v tc1 ^ 2 := by rw [hm1']
          _ = v tc1 ^ 3 := by ring
      field_simp
      simpa [mul_comm] using h2
    set b : Fin 2 → k := fun j => if j = 0 then 1 else v tc1 / v tc0 with hbdef
    have hb0 : b 0 = 1 := by simp [hbdef]
    have hb1 : b 1 = v tc1 / v tc0 := by simp [hbdef]
    have hbne : b ≠ 0 := by
      intro h
      rw [h] at hb0
      exact zero_ne_one hb0
    refine ⟨Pp.mk hbne, ?_⟩
    rw [rho_mk, ← hvq, Pp.mk_eq_mk_iff']
    refine ⟨v tc0, hne, ?_⟩
    funext α
    rcases Dmon_one_three_cases α with rfl | rfl | rfl | rfl
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc0, hb0]
      ring
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc1, hb0, hb1]
      field_simp
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc2, hb0, hb1]
      have hR : v tc0 * (1 * (v tc1 / v tc0) ^ 2) = v tc1 ^ 2 / v tc0 := by
        field_simp
      rw [hR, ← hv1sq]
    · rw [Pi.smul_apply, smul_eq_mul, rhoLift_tc3, hb1]
      have hR : v tc0 * (v tc1 / v tc0) ^ 3 = v tc1 ^ 3 / v tc0 ^ 2 := by
        field_simp
      rw [hR, ← hv3eq]

/-- **Exercise I.2.12 (d)**: the twisted cubic curve in `ℙ³` is the 3-uple embedding of `ℙ¹`
in `ℙ³`, for the standard choice of coordinates
`(u : x : y : z) = (x_0^3 : x_0^2x_1 : x_0x_1^2 : x_1^3)`. -/
theorem part_d :
    Set.range (rho (k := k) (n := 1) (d := 3) (by norm_num)) = twistedCubic (k := k) := by
  rw [part_b (by norm_num : (0 : ℕ) < 3)]
  exact Set.Subset.antisymm Zver_subset_twistedCubic twistedCubic_subset_Zver

/-! ## 10. Assembly of the exercise -/

/-- **Hartshorne I.2.12, parts (a)–(c)** for arbitrary `n` and `d > 0`:
`𝔞 = ker θ` is a homogeneous prime ideal, the image of `ρ_d` is `Z(𝔞)`, and `ρ_d` is a
homeomorphism of `ℙⁿ` onto `Z(𝔞)`. -/
theorem hartshorne_I_2_12 (hd : 0 < d) :
    ((veroneseIdeal (k := k) (n := n) (d := d)).IsPrime ∧
      ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), ∀ e,
        MvPolynomial.homogeneousComponent e f ∈ veroneseIdeal (k := k) (n := n) (d := d)) ∧
    Set.range (rho (k := k) (n := n) (d := d) hd) = Zver (k := k) (n := n) (d := d) ∧
    Nonempty (Pp k (Fin (n + 1)) ≃ₜ Zver (k := k) (n := n) (d := d)) :=
  ⟨part_a hd, part_b hd, ⟨part_c hd⟩⟩

/-- **Hartshorne I.2.12 (d)**: the twisted cubic curve of `ℙ³` is the 3-uple embedding of `ℙ¹`
for the standard choice of coordinates. -/
theorem hartshorne_I_2_12_d :
    Set.range (rho (k := k) (n := 1) (d := 3) (by norm_num)) = twistedCubic (k := k) :=
  part_d

/-! ## 11. `Z(𝔞)` is a projective variety: closed, irreducible and nonempty

Hartshorne's "`Z(𝔞)` is a projective variety in `ℙ^N`" means: `Z(𝔞)` is a *closed irreducible*
subset of `ℙ^N`.  Over an algebraically closed (indeed any infinite) field, `ℙ^N` is irreducible
because a nonzero homogeneous polynomial cannot vanish at every projective point; transport along
the surjective continuous map `ρ_d` of part (b) then gives irreducibility of `Z(𝔞)`.  (Over a
finite field `ℙ^N` is a finite discrete space and this fails, so Hartshorne's standing hypothesis
that `k` is algebraically closed is essential for this clause.) -/

/-- The set of homogeneous elements of `𝔞`. -/
def veroneseIdealHom : Set (MvPolynomial (Dmon n d) k) :=
  {f | f ∈ veroneseIdeal (k := k) (n := n) (d := d) ∧ ∃ e, f.IsHomogeneous e}

theorem veroneseIdealHom_isHomogeneous :
    ∀ f ∈ veroneseIdealHom (k := k) (n := n) (d := d), ∃ e, f.IsHomogeneous e :=
  fun _ hf => hf.2

/-- `Z(𝔞)` is the zero locus of the homogeneous elements of `𝔞`, hence is closed. -/
theorem Zver_eq_zeroLocus_homogeneous (hd : 0 < d) :
    Zver (k := k) (n := n) (d := d) = Pp.zeroLocus (veroneseIdealHom (k := k) (n := n) (d := d)) := by
  ext q
  constructor
  · rintro hq f ⟨hf, -⟩
    exact hq f hf
  · intro hq
    obtain ⟨v, hv, rfl⟩ := Pp.exists_mk q
    rw [mem_Zver_iff (fun f hf e => veroneseIdeal_homogeneousComponent_mem hd hf e) hv]
    intro f hf
    have hsum := MvPolynomial.sum_homogeneousComponent f
    calc MvPolynomial.eval v f
        = MvPolynomial.eval v (∑ e ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.homogeneousComponent e f) := by rw [hsum]
      _ = ∑ e ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.eval v (MvPolynomial.homogeneousComponent e f) :=
          map_sum (MvPolynomial.eval v) _ _
      _ = 0 := by
          refine Finset.sum_eq_zero (fun e _ => ?_)
          have hmem : MvPolynomial.homogeneousComponent e f
              ∈ veroneseIdealHom (k := k) (n := n) (d := d) :=
            ⟨veroneseIdeal_homogeneousComponent_mem hd hf e,
              ⟨e, MvPolynomial.homogeneousComponent_isHomogeneous (n := e) (φ := f)⟩⟩
          exact (Pp.mem_zeroLocus_iff (T := veroneseIdealHom (k := k) (n := n) (d := d))
            veroneseIdealHom_isHomogeneous hv).1 hq (MvPolynomial.homogeneousComponent e f) hmem

theorem Zver_isClosed (hd : 0 < d) : IsClosed (Zver (k := k) (n := n) (d := d)) := by
  rw [Zver_eq_zeroLocus_homogeneous hd]
  exact Pp.isClosed_zeroLocus veroneseIdealHom_isHomogeneous

theorem Zver_nonempty (hd : 0 < d) : (Zver (k := k) (n := n) (d := d)).Nonempty := by
  rw [← part_b hd]
  exact Set.range_nonempty _

section Infinite

variable [Infinite k]

/-- A nonzero homogeneous polynomial has a nonzero value at a nonzero vector. -/
theorem exists_eval_ne_zero {υ : Type*} [Nonempty υ] {f : MvPolynomial υ k} {e : ℕ}
    (hf : f.IsHomogeneous e) (hne : f ≠ 0) :
    ∃ v : υ → k, v ≠ 0 ∧ MvPolynomial.eval v f ≠ 0 := by
  by_cases he : e = 0
  · have hcomp : MvPolynomial.homogeneousComponent 0 f = f :=
      MvPolynomial.homogeneousComponent_eq_self (he ▸ hf)
    have hfC : f = MvPolynomial.C (MvPolynomial.coeff 0 f) := by
      nth_rewrite 1 [← hcomp]
      rw [MvPolynomial.homogeneousComponent_zero]
    have hc : MvPolynomial.coeff 0 f ≠ 0 := by
      rintro h0
      exact hne (by rw [hfC, h0, MvPolynomial.C_0])
    obtain ⟨i⟩ := ‹Nonempty υ›
    refine ⟨fun _ => (1 : k), ?_, ?_⟩
    · intro h
      have h1 := congrFun h i
      simp at h1
    · rw [hfC, MvPolynomial.eval_C]
      exact hc
  · obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v f ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hne (hf.eq_zero_of_forall_eval_eq_zero h')
    have hz : MvPolynomial.eval (0 : υ → k) f = 0 := by
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
      exact hf.coeff_eq_zero (by rw [map_zero]; exact fun h0 => he h0.symm)
    exact ⟨v, fun h0 => hv (h0 ▸ hz), hv⟩

/-- A nonzero homogeneous polynomial does not vanish at every projective point. -/
theorem exists_not_formVanishesAt {υ : Type*} [Nonempty υ] {f : MvPolynomial υ k} {e : ℕ}
    (hf : f.IsHomogeneous e) (hne : f ≠ 0) :
    ∃ p : Pp k υ, ¬ Pp.FormVanishesAt f p := by
  obtain ⟨v, hv0, hv⟩ := exists_eval_ne_zero hf hne
  exact ⟨Pp.mk hv0, fun h => hv (Pp.formVanishesAt_mk hv0 h)⟩

/-- A nonzero homogeneous polynomial does not vanish at every point of `ℙ^υ`. -/
theorem zeroLocus_singleton_ne_univ {υ : Type*} [Nonempty υ] {f : MvPolynomial υ k} {e : ℕ}
    (hf : f.IsHomogeneous e) (hne : f ≠ 0) :
    Pp.zeroLocus ({f} : Set (MvPolynomial υ k)) ≠ Set.univ := by
  intro h
  obtain ⟨p, hp⟩ := exists_not_formVanishesAt hf hne
  refine hp ?_
  have hmem : p ∈ Pp.zeroLocus ({f} : Set (MvPolynomial υ k)) := by
    rw [h]; exact Set.mem_univ p
  exact hmem f (Set.mem_singleton f)

/-- **`ℙ^υ` is irreducible** over an infinite field. -/
theorem isPreirreducible_univ {υ : Type*} [Nonempty υ] :
    IsPreirreducible (Set.univ : Set (Pp k υ)) := by
  intro u v hu hv hu' hv'
  obtain ⟨Tu, hTu, rfl⟩ := hu
  obtain ⟨Tv, hTv, rfl⟩ := hv
  have hex : ∀ (T : Set (MvPolynomial υ k)), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) →
      (Set.univ ∩ (Pp.zeroLocus T)ᶜ).Nonempty → ∃ f ∈ T, f ≠ 0 := by
    intro T hT hne
    by_contra h'
    push Not at h'
    obtain ⟨p, hp⟩ := hne
    exact hp.2 (fun f hf => by rw [h' f hf]; exact fun w _ _ => by simp)
  obtain ⟨f, hfT, hf0⟩ := hex Tu hTu hu'
  obtain ⟨g, hgT, hg0⟩ := hex Tv hTv hv'
  obtain ⟨df, hdf⟩ := hTu f hfT
  obtain ⟨dg, hdg⟩ := hTv g hgT
  have hfg : f * g ≠ 0 := mul_ne_zero hf0 hg0
  have hhom : (f * g).IsHomogeneous (df + dg) := hdf.mul hdg
  obtain ⟨q, hq⟩ := Set.nonempty_compl.2 (zeroLocus_singleton_ne_univ hhom hfg)
  have hsplit : ({f * g} : Set (MvPolynomial υ k)) = Set.image2 (· * ·) {f} {g} := by
    ext h
    simp
  have hVf : ({f} : Set (MvPolynomial υ k)) ⊆ Tu := by
    intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact hfT
  have hVg : ({g} : Set (MvPolynomial υ k)) ⊆ Tv := by
    intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact hgT
  have hfg_mem : ∀ p, p ∈ Pp.zeroLocus ({f} : Set _) ∪ Pp.zeroLocus ({g} : Set _) →
      p ∈ Pp.zeroLocus ({f * g} : Set _) := by
    intro p hp
    rw [hsplit,
      Pp.zeroLocus_image2_mul_union (fun h hh => hTu h (hVf hh)) (fun h hh => hTv h (hVg hh))]
    exact hp
  refine ⟨q, Set.mem_univ q, ?_, ?_⟩
  · intro hZ
    refine hq (hfg_mem q (Set.mem_union_left _ ?_))
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hZ f hfT
  · intro hZ
    refine hq (hfg_mem q (Set.mem_union_right _ ?_))
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hZ g hgT

/-- **`ℙ^N` is irreducible** over an infinite field. -/
theorem irreducibleSpace_projective (n : ℕ) : IrreducibleSpace (Pp k (Fin (n + 1))) := by
  rw [irreducibleSpace_def]
  exact ⟨Set.univ_nonempty, isPreirreducible_univ⟩

/-- **`Z(𝔞)` is irreducible**: it is the continuous image of the irreducible `ℙⁿ`. -/
theorem Zver_isIrreducible (hd : 0 < d) : IsIrreducible (Zver (k := k) (n := n) (d := d)) := by
  have h : IrreducibleSpace (Pp k (Fin (n + 1))) := irreducibleSpace_projective n
  have h2 : IsIrreducible (Set.univ : Set (Pp k (Fin (n + 1)))) := by
    simpa using (irreducibleSpace_def _).1 h
  rw [← part_b hd]
  have himg := h2.image (rho (k := k) (n := n) (d := d) hd) (rho_continuous hd).continuousOn
  rwa [Set.image_univ] at himg

/-- **Hartshorne I.2.12 (a), the variety clause**, over an infinite field: `Z(𝔞)` is a nonempty
closed irreducible subset of `ℙ^N`, i.e. a projective variety. -/
theorem part_a_variety (hd : 0 < d) :
    IsClosed (Zver (k := k) (n := n) (d := d)) ∧
      IsIrreducible (Zver (k := k) (n := n) (d := d)) ∧
      (Zver (k := k) (n := n) (d := d)).Nonempty :=
  ⟨Zver_isClosed hd, Zver_isIrreducible hd, Zver_nonempty hd⟩

end Infinite

/-- **Hartshorne I.2.12 (a), the variety clause**, over an algebraically closed field
(Hartshorne's standing hypothesis): `Z(𝔞)` is a nonempty closed irreducible subset of `ℙ^N`,
i.e. a projective variety. -/
theorem part_a_variety_algClosed [IsAlgClosed k] (hd : 0 < d) :
    IsClosed (Zver (k := k) (n := n) (d := d)) ∧
      IsIrreducible (Zver (k := k) (n := n) (d := d)) ∧
      (Zver (k := k) (n := n) (d := d)).Nonempty :=
  part_a_variety hd

/-- **Hartshorne I.2.12, full bundle over an algebraically closed field**: `𝔞 = ker θ` is a
homogeneous prime ideal with `Z(𝔞)` a nonempty closed irreducible subset of `ℙ^N` (a projective
variety), the image of `ρ_d` is exactly `Z(𝔞)`, and `ρ_d` is a homeomorphism of `ℙⁿ` onto it. -/
theorem hartshorne_I_2_12_algClosed [IsAlgClosed k] (hd : 0 < d) :
    ((veroneseIdeal (k := k) (n := n) (d := d)).IsPrime ∧
      ∀ f ∈ veroneseIdeal (k := k) (n := n) (d := d), ∀ e,
        MvPolynomial.homogeneousComponent e f ∈ veroneseIdeal (k := k) (n := n) (d := d)) ∧
    IsClosed (Zver (k := k) (n := n) (d := d)) ∧
    IsIrreducible (Zver (k := k) (n := n) (d := d)) ∧
    (Zver (k := k) (n := n) (d := d)).Nonempty ∧
    Set.range (rho (k := k) (n := n) (d := d) hd) = Zver (k := k) (n := n) (d := d) ∧
    Nonempty (Pp k (Fin (n + 1)) ≃ₜ Zver (k := k) (n := n) (d := d)) :=
  ⟨part_a hd, Zver_isClosed hd, Zver_isIrreducible hd, Zver_nonempty hd, part_b hd, ⟨part_c hd⟩⟩

/-! ## 12. Sharpness of the hypothesis `d > 0`

For `d = 0` the ideal `𝔞 = ker θ` is not homogeneous: `θ(y_0) = 1 = θ(1)`, so `y_0 - 1 ∈ 𝔞`,
but the homogeneous component `y_0` of `y_0 - 1` is not in `𝔞` because `θ(y_0) = 1 ≠ 0`.  Hence
the hypothesis `d > 0` in the printed exercise cannot be dropped (clause (a) fails without it). -/

theorem not_homogeneous_of_d_eq_zero :
    ∃ f ∈ veroneseIdeal (k := k) (n := n) (d := 0), ∃ e,
      MvPolynomial.homogeneousComponent e f ∉ veroneseIdeal (k := k) (n := n) (d := 0) := by
  refine ⟨MvPolynomial.X (Dmon.pure (n := n) (d := 0) 0) - 1, ?_, 1, ?_⟩
  · rw [mem_veroneseIdeal_iff, map_sub, theta_X, map_one, mon, Dmon.pure_val]
    simp
  · have hX : (MvPolynomial.X (Dmon.pure (n := n) (d := 0) 0) :
        MvPolynomial (Dmon n 0) k).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X (σ := Dmon n 0) (R := k) _
    have h1 : (1 : MvPolynomial (Dmon n 0) k).IsHomogeneous 0 :=
      MvPolynomial.isHomogeneous_one (σ := Dmon n 0) (R := k)
    have hcomp : MvPolynomial.homogeneousComponent 1
        (MvPolynomial.X (Dmon.pure (n := n) (d := 0) 0)
          - (1 : MvPolynomial (Dmon n 0) k))
        = MvPolynomial.X (Dmon.pure (n := n) (d := 0) 0) := by
      rw [map_sub,
        MvPolynomial.homogeneousComponent_of_mem (p := MvPolynomial.X
          (Dmon.pure (n := n) (d := 0) 0)) hX,
        MvPolynomial.homogeneousComponent_of_mem (p := (1 : MvPolynomial (Dmon n 0) k)) h1]
      simp
    rw [hcomp, mem_veroneseIdeal_iff, theta_X, mon, Dmon.pure_val]
    simp

/-! ## 13. Axiom audit

Every main export and the decisive helpers, checked to use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms hartshorne_I_2_12
#print axioms hartshorne_I_2_12_d
#print axioms part_a
#print axioms part_b
#print axioms part_c
#print axioms part_d
#print axioms veroneseIdeal_isPrime
#print axioms veroneseIdeal_homogeneousComponent_mem
#print axioms eq_zero_of_sum_homogeneous
#print axioms rel1_mem
#print axioms rel2_mem
#print axioms range_rho_subset_Zver
#print axioms Zver_subset_range
#print axioms eval_rhoLift
#print axioms eval_aeval'
#print axioms rho_continuous
#print axioms rho_injective
#print axioms rhoSet_isClosedMap
#print axioms rhoSet_isOpenMap
#print axioms continuous_invFun_rhoSet
#print axioms eval_Hsub_rhoLift
#print axioms eval_Hsub_chartVec
#print axioms rho_chartVec
#print axioms coord_eq_chartVec
#print axioms exists_pure_ne_zero
#print axioms tcM_mem_ker
#print axioms Zver_subset_twistedCubic
#print axioms twistedCubic_subset_Zver
#print axioms Dmon_one_three_cases
#print axioms not_homogeneous_of_d_eq_zero
#print axioms hartshorne_I_2_12_algClosed
#print axioms part_a_variety
#print axioms Zver_isClosed
#print axioms Zver_isIrreducible
#print axioms Zver_nonempty
#print axioms irreducibleSpace_projective
#print axioms isPreirreducible_univ
#print axioms zeroLocus_singleton_ne_univ
#print axioms exists_eval_ne_zero
#print axioms exists_not_formVanishesAt
#print axioms part_a_variety_algClosed
#print axioms Zver_eq_zeroLocus_homogeneous
#print axioms veroneseIdealHom_isHomogeneous
