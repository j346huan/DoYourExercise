import Mathlib

/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §3, Exercise 3.4

SOURCE STATEMENT (verbatim): "3.4. Show that the d-uple embedding of `P^n` (Ex. 2.12) is an
isomorphism onto its image."

Cross-checks: local OCR `.scratch/reference/hartshorne-1977.txt` (Section I.3 exercise list),
R.~E.~Borcherds' solutions (`math.berkeley.edu/~reb/courses/256A/1.3.pdf`, "It is enough to
show that φ⁻¹ is regular near φ(1:x₁:…:xₙ)"), and D.~Z.~Garza's Hartshorne collection.
The public `hartshorne-ag-solutions.wikidot.com/chapter-1-section-3` page does not exist
(the site only has Sections 1 and 2 of Chapter 1), so the statement is corroborated from
the book text and two independent solution transcripts.  Exercise I.2.12 (`d > 0`, the
`M₀,…,M_N` are *all* degrees `d` monomials, `N = C(n+d,d) - 1`) is recalled in the statement
of `rho` below; `d ≥ 1` is its own hypothesis, not an extra assumption.

## What is formalized

The classical point-set development of Hartshorne Chapter I is built from scratch:

* `Proj k ι`: projective space as lines through `0` in `k^ι` (classes of nonzero vectors),
  `zeroLocus`, the Zariski topology (`zariskiTopology`) and the theorem that the closed sets
  are exactly the zero loci of sets of homogeneous forms.
* the standard affine charts `U_i = {x_i ≠ 0}`, dehomogenization `chartCoord`,
  homogenization `chartVec`, and the bijection `chartEquiv` (`U_i ≃ k^{ι∖{i}}`).
* degree-`d` monomials `Monom σ d = {m : σ →₀ ℕ // m.degree = d}`, their evaluation
  `monoEval`, and **the `d`-uple embedding** `rho d : P^σ → P^{Monom σ d}`,
  `P ↦ (m(P))_m` (Hartshorne's `ρ_d`).
* `rho` is injective (`rho_injective`), continuous (`rho_continuous`, via
  `ρ_d⁻¹ V(T) = V(subst T)`), and on the chart `U_i` it is the monomial map
  `w_m = ∏_j z_j^{m_j}` (`chartCoord_rho`).
* Regular functions and morphisms of quasi-projective varieties in Hartshorne's sense
  (`IsRegularAt`, `IsRegular`, `IsMorphism`: continuous plus pullback of regular
  functions), and `rho_isMorphism`.
* The inverse `psi` of `rho` on its image: `psi_rho`, `rho_psi` (so `rho` is a bijection
  onto its image), and the chart formula `psiCoord` (`x_j/x_i = y_{x_i^{d-1}x_j}/y_{x_i^d}`).
  `psi_eval_ratio` proves the inverse is given by the *linear* substitution
  `x_j ↦ x_i^{d-1}x_j`, `x_i ↦ x_i^d` on each chart, hence regular; `psi_zero_iff`,
  `psi_continuous` and `psi_isMorphism` give that the inverse is a morphism of varieties.
* `hartshorne_I_3_4` assembles the result: `rho` is injective, is a morphism, its inverse on
  the image is a morphism, and the two composites are the identities.

Everything is stated for an arbitrary field `k` (Hartshorne assumes `k` algebraically
closed; no algebraic closedness is used, so this is a generalization, not a weakening) and
an arbitrary finite index type `σ` (Hartshorne's `n+1` coordinates); `Monom σ d` plays the
role of `Fin (N+1)` with `N+1 = #(degree-d monomials)`.
-/

namespace Hartshorne77.Ex_I_3_4

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {k : Type*} [Field k]
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

abbrev Vec (k : Type*) (ι : Type*) : Type _ := ι → k

section Proj

variable {ι : Type*}

def projRel (v w : {v : Vec k ι // v ≠ 0}) : Prop := ∃ c : k, c ≠ 0 ∧ v.1 = c • w.1

theorem projRel_equivalence : Equivalence (projRel (k := k) (ι := ι)) where
  refl v := ⟨1, one_ne_zero, by simp⟩
  symm := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  trans := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨c, hc, h₁⟩ ⟨d, hd, h₂⟩
    exact ⟨c * d, mul_ne_zero hc hd, by rw [h₁, h₂, smul_smul]⟩

def projSetoid (k : Type*) [Field k] (ι : Type*) : Setoid {v : Vec k ι // v ≠ 0} :=
  ⟨projRel, projRel_equivalence⟩

/-- Classical projective space: `Proj k ι` is the set of lines through `0` in `k^ι`. -/
def Proj (k : Type*) [Field k] (ι : Type*) : Type _ := Quotient (projSetoid k ι)

namespace Proj

def mk {v : Vec k ι} (hv : v ≠ 0) : Proj k ι := Quotient.mk _ ⟨v, hv⟩

theorem mk_eq_mk_iff {v w : Vec k ι} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (ι := ι) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w :=
  Quotient.eq

theorem mk_eq_mk_iff' {v w : Vec k ι} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (ι := ι) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ c • v = w := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem mk_smul {c : k} (hc : c ≠ 0) {v : Vec k ι} (hv : v ≠ 0) :
    mk (k := k) (ι := ι) (show c • v ≠ 0 from smul_ne_zero hc hv) = mk hv := by
  rw [mk_eq_mk_iff]
  exact ⟨c, hc, rfl⟩

theorem exists_mk (p : Proj k ι) : ∃ (v : Vec k ι) (hv : v ≠ 0), mk hv = p := by
  induction p using Quotient.inductionOn with
  | h x => exact ⟨x.1, x.2, rfl⟩

/-- A chosen representative vector of a projective point. -/
def rep (p : Proj k ι) : Vec k ι := (exists_mk p).choose

theorem rep_ne_zero (p : Proj k ι) : rep p ≠ 0 := (exists_mk p).choose_spec.1

theorem mk_rep (p : Proj k ι) : mk (rep_ne_zero p) = p := (exists_mk p).choose_spec.2

end Proj

end Proj

open MvPolynomial

section Forms

variable {ι : Type*}

abbrev Poly (k : Type*) [CommSemiring k] (ι : Type*) : Type _ := MvPolynomial ι k

variable {f : Poly k ι} {d : ℕ}

/-- Homogeneity of evaluation: `f(c·v) = c^d f(v)` for homogeneous `f` of degree `d`. -/
theorem eval_smul_of_isHomogeneous (hf : f.IsHomogeneous d) (c : k) (v : Vec k ι) :
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

namespace Proj

/-- `f` vanishes at the projective point `p`. -/
def FormVanishesAt (f : Poly k ι) (p : Proj k ι) : Prop :=
  ∀ (v : Vec k ι) (hv : v ≠ 0), mk hv = p → MvPolynomial.eval v f = 0

theorem formVanishesAt_mk {v : Vec k ι} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) → MvPolynomial.eval v f = 0 :=
  fun h => h v hv rfl

theorem formVanishesAt_mk_iff (hf : f.IsHomogeneous d) {v : Vec k ι} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) ↔ MvPolynomial.eval v f = 0 := by
  refine ⟨formVanishesAt_mk hv, ?_⟩
  intro h w hw hwp
  obtain ⟨c, hc, hwv⟩ := (mk_eq_mk_iff hw hv).1 hwp
  rw [hwv, eval_smul_of_isHomogeneous hf, h, mul_zero]

/-- The projective zero locus of a set of forms. -/
def zeroLocus (T : Set (Poly k ι)) : Set (Proj k ι) :=
  {p | ∀ f ∈ T, FormVanishesAt f p}

@[simp]
theorem mem_zeroLocus_iff {T : Set (Poly k ι)} (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d)
    {v : Vec k ι} (hv : v ≠ 0) :
    mk hv ∈ zeroLocus T ↔ ∀ f ∈ T, MvPolynomial.eval v f = 0 := by
  constructor
  · intro h f hf
    exact formVanishesAt_mk hv (h f hf)
  · intro h f hf
    obtain ⟨d, hd⟩ := hT f hf
    rw [formVanishesAt_mk_iff hd hv]
    exact h f hf

theorem zeroLocus_empty : zeroLocus (∅ : Set (Poly k ι)) = Set.univ := by
  ext p; simp [zeroLocus]

theorem zeroLocus_mono {T T' : Set (Poly k ι)} (h : T ⊆ T') :
    zeroLocus T' ⊆ zeroLocus T :=
  fun _ hp f hf => hp f (h hf)

theorem zeroLocus_iUnion {τ : Type*} (T : τ → Set (Poly k ι)) :
    zeroLocus (⋃ i, T i) = ⋂ i, zeroLocus (T i) := by
  ext p
  simp only [zeroLocus, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_union (T T' : Set (Poly k ι)) :
    zeroLocus (T ∪ T') = zeroLocus T ∩ zeroLocus T' := by
  ext p
  simp only [zeroLocus, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

theorem zeroLocus_one_eq_empty :
    zeroLocus ({(1 : Poly k ι)} : Set (Poly k ι)) = ∅ := by
  have h1 : ∀ f ∈ ({(1 : Poly k ι)} : Set (Poly k ι)), ∃ d, f.IsHomogeneous d := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, MvPolynomial.isHomogeneous_one (σ := ι) (R := k)⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff h1 hv]
  simp

theorem zeroLocus_image2_mul_union {T T' : Set (Poly k ι)}
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

set_option warn.classDefReducibility false in
/-- **The Zariski topology on `P^ι`**: a set is open iff it is the complement of the zero
locus `V(T)` of a set `T` of homogeneous polynomials (Hartshorne I.2, p. 10). -/
def zariskiTopology : TopologicalSpace (Proj k ι) where
  IsOpen U := ∃ T : Set (Poly k ι), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ U = (zeroLocus T)ᶜ
  isOpen_univ := by
    have h1 : ∀ f ∈ ({(1 : Poly k ι)} : Set (Poly k ι)), ∃ d, f.IsHomogeneous d := by
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
    have hA' : ∀ a : A, ∃ T : Set (Poly k ι), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
        (a : Set (Proj k ι)) = (zeroLocus T)ᶜ := fun a => hA a a.2
    choose T hT hTA using hA'
    refine ⟨⋃ a : A, T a, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, hfa⟩ := Set.mem_iUnion.1 hf
      exact hT a f hfa
    · rw [zeroLocus_iUnion, Set.sUnion_eq_iUnion, Set.compl_iInter]
      exact Set.iUnion_congr fun a => hTA a

instance : TopologicalSpace (Proj k ι) := zariskiTopology (k := k) (ι := ι)

/-- The closed sets of `P^ι` are exactly the zero loci of sets of homogeneous
polynomials. -/
theorem isClosed_iff_exists_zeroLocus {Z : Set (Proj k ι)} :
    IsClosed Z ↔ ∃ T : Set (Poly k ι), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ Z = zeroLocus T := by
  constructor
  · intro h
    obtain ⟨T, hT, hU⟩ := h.isOpen_compl
    exact ⟨T, hT, by rw [← compl_compl Z, hU, compl_compl]⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩

theorem isClosed_zeroLocus {T : Set (Poly k ι)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) : IsClosed (zeroLocus T) :=
  isClosed_iff_exists_zeroLocus.2 ⟨T, hT, rfl⟩

end Proj

end Forms

/-! ## 2. Standard affine charts `U_i = {x_i ≠ 0}` of `P^ι`. -/

section Charts

variable {ι : Type*}

namespace Proj

/-- The standard chart `U_i = {x_i ≠ 0}` of `P^ι`. -/
def InChart (i : ι) (p : Proj k ι) : Prop :=
  ∀ (v : Vec k ι) (hv : v ≠ 0), mk hv = p → v i ≠ 0

theorem inChart_mk {i : ι} {v : Vec k ι} (hv : v ≠ 0) :
    InChart i (mk hv) ↔ v i ≠ 0 := by
  constructor
  · intro h
    exact h v hv rfl
  · intro h w hw hwp
    obtain ⟨c, hc, hwv⟩ := (mk_eq_mk_iff hw hv).1 hwp
    rw [hwv, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc h

/-- The charts cover `P^ι`. -/
theorem exists_mem_chart (p : Proj k ι) : ∃ i : ι, InChart i p := by
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact ⟨i, (inChart_mk hv).2 hi⟩

/-- The chosen representative of a point of the chart `U_i`. -/
def chartRep (i : ι) (p : {p : Proj k ι // InChart i p}) : Vec k ι :=
  (exists_mk (p : Proj k ι)).choose

theorem chartRep_eq_rep (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartRep i p = rep (p : Proj k ι) := rfl

theorem chartRep_ne_zero (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartRep i p ≠ 0 :=
  (exists_mk (p : Proj k ι)).choose_spec.1

theorem mk_chartRep (i : ι) (p : {p : Proj k ι // InChart i p}) :
    mk (chartRep_ne_zero i p) = (p : Proj k ι) :=
  (exists_mk (p : Proj k ι)).choose_spec.2

theorem chartRep_coord_ne_zero (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartRep i p i ≠ 0 :=
  p.2 (chartRep i p) (chartRep_ne_zero i p) (mk_chartRep i p)

/-- **Dehomogenization**: the affine coordinates `x_j/x_i` of a point of the chart `U_i`. -/
def chartCoord (i : ι) (p : {p : Proj k ι // InChart i p}) : {j : ι // j ≠ i} → k :=
  fun j => chartRep i p j.1 / chartRep i p i

end Proj

section ChartVec

variable [DecidableEq ι]

namespace Proj

/-- **Homogenization**: the vector with `i`-th coordinate `1` and other coordinates `y`. -/
def chartVec (i : ι) (y : {j : ι // j ≠ i} → k) : Vec k ι :=
  fun j => if h : j = i then 1 else y ⟨j, h⟩

theorem chartVec_apply_same (i : ι) (y : {j : ι // j ≠ i} → k) : chartVec i y i = 1 := by
  simp [chartVec]

theorem chartVec_apply_ne (i : ι) (y : {j : ι // j ≠ i} → k) {j : ι} (hj : j ≠ i) :
    chartVec i y j = y ⟨j, hj⟩ := by
  simp [chartVec, hj]

theorem chartVec_ne_zero (i : ι) (y : {j : ι // j ≠ i} → k) : chartVec i y ≠ 0 := by
  intro h
  have h1 : chartVec i y i = 0 := by rw [h]; rfl
  rw [chartVec_apply_same] at h1
  exact one_ne_zero h1

theorem inChart_chartVec (i : ι) (y : {j : ι // j ≠ i} → k) :
    InChart i (mk (chartVec_ne_zero i y)) := by
  rw [inChart_mk, chartVec_apply_same]
  exact one_ne_zero

/-- The inverse of dehomogenization: a point of affine space regarded as a point of `U_i`. -/
def chartInv (i : ι) (y : {j : ι // j ≠ i} → k) : {p : Proj k ι // InChart i p} :=
  ⟨mk (chartVec_ne_zero i y), inChart_chartVec i y⟩

theorem mk_chartVec_chartCoord (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartVec i (chartCoord i p) = (chartRep i p i)⁻¹ • chartRep i p := by
  funext j
  by_cases hj : j = i
  · simp only [chartVec, hj, dif_pos, Pi.smul_apply, smul_eq_mul,
      inv_mul_cancel₀ (chartRep_coord_ne_zero i p)]
  · simp only [chartVec, hj, dif_neg, not_false_iff, chartCoord, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]

/-- The chosen representative is a nonzero multiple of the normalized (homogenized) one. -/
theorem chartRep_eq_smul_chartVec (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartRep i p = chartRep i p i • chartVec i (chartCoord i p) := by
  conv_lhs => rw [← smul_inv_smul₀ (chartRep_coord_ne_zero i p) (chartRep i p)]
  rw [mk_chartVec_chartCoord]

theorem chartInv_chartCoord (i : ι) (p : {p : Proj k ι // InChart i p}) :
    chartInv i (chartCoord i p) = p := by
  apply Subtype.ext
  show mk (chartVec_ne_zero i (chartCoord i p)) = (p : Proj k ι)
  have hmk : mk (chartVec_ne_zero i (chartCoord i p)) = mk (chartRep_ne_zero i p) := by
    rw [mk_eq_mk_iff']
    refine ⟨chartRep i p i, chartRep_coord_ne_zero i p, ?_⟩
    rw [mk_chartVec_chartCoord, smul_smul,
      mul_inv_cancel₀ (chartRep_coord_ne_zero i p), one_smul]
  rw [hmk, mk_chartRep]

theorem chartCoord_chartInv (i : ι) (y : {j : ι // j ≠ i} → k) :
    chartCoord i (chartInv i y) = y := by
  funext j
  have hrep := mk_chartRep i (chartInv i y)
  obtain ⟨c, hc, hcw⟩ := (mk_eq_mk_iff (chartRep_ne_zero i (chartInv i y))
    (chartVec_ne_zero i y)).1 hrep
  have hc0 : c ≠ 0 := hc
  show chartRep i (chartInv i y) j.1 / chartRep i (chartInv i y) i = y j
  rw [hcw]
  simp only [Pi.smul_apply, smul_eq_mul, chartVec_apply_ne i y j.2, chartVec_apply_same, mul_one]
  field_simp

/-- **The affine chart `U_i ≃ k^{ι∖{i}}`**: dehomogenization at `x_i` is a bijection. -/
def chartEquiv (i : ι) : {p : Proj k ι // InChart i p} ≃ ({j : ι // j ≠ i} → k) where
  toFun := chartCoord i
  invFun := chartInv i
  left_inv := chartInv_chartCoord i
  right_inv := chartCoord_chartInv i

theorem chartVec_injective (i : ι) : Function.Injective (chartVec (k := k) i) := by
  intro y z h
  funext j
  have h1 := congrFun h j.1
  rw [chartVec_apply_ne i y j.2, chartVec_apply_ne i z j.2] at h1
  exact h1

theorem chartCoord_congr {i : ι} {p q : Proj k ι} (hp : InChart i p)
    (hq : InChart i q) (h : p = q) (m : {j : ι // j ≠ i}) :
    chartCoord i ⟨p, hp⟩ m = chartCoord i ⟨q, hq⟩ m := by
  cases h
  rfl


/-- Each standard chart is Zariski open: it is the complement of the zero locus of `X i`. -/
theorem isOpen_chart (i : ι) : IsOpen {p : Proj k ι | InChart i p} := by
  have hT : ∀ f ∈ ({MvPolynomial.X i} : Set (Poly k ι)), ∃ d, f.IsHomogeneous d := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨1, MvPolynomial.isHomogeneous_X (σ := ι) (R := k) i⟩
  refine ⟨{MvPolynomial.X i}, hT, ?_⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [Set.mem_compl_iff, mem_zeroLocus_iff hT hv, Set.mem_ofPred_eq, inChart_mk hv]
  simp

/-- The standard charts cover `P^ι`. -/
theorem iUnion_chart : (⋃ i : ι, {p : Proj k ι | InChart i p}) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact exists_mem_chart p

end Proj

end ChartVec

end Charts

/-! ## 3. Degree-`d` monomials and the `d`-uple embedding `ρ_d : P^σ → P^{Monom(σ,d)}`. -/

section Monom

namespace Proj

variable {σ : Type*} [DecidableEq σ]

/-- The index type of degree-`d` monomials in the variables indexed by `σ` (Hartshorne
Ex. I.2.12: `M_0,…,M_N` are *all* the monomials of degree `d`). -/
def Monom (σ : Type*) (d : ℕ) : Type _ := {m : σ →₀ ℕ // m.degree = d}

instance (σ) [DecidableEq σ] (d : ℕ) : DecidableEq (Monom σ d) := by
  unfold Monom; infer_instance

/-- Evaluation of the monomial with exponent vector `m` at the vector `v`. -/
def monoEval (v : Vec k σ) (m : σ →₀ ℕ) : k := ∏ i ∈ m.support, v i ^ m i

theorem monoEval_eq_eval_monomial (v : Vec k σ) (m : σ →₀ ℕ) :
    monoEval v m = MvPolynomial.eval v (MvPolynomial.monomial m (1 : k)) := by
  simp [monoEval, MvPolynomial.eval_monomial, Finsupp.prod]

theorem monoEval_one (v : Vec k σ) : monoEval v 0 = 1 := by
  simp [monoEval]

theorem monoEval_add (v : Vec k σ) (m₁ m₂ : σ →₀ ℕ) :
    monoEval v (m₁ + m₂) = monoEval v m₁ * monoEval v m₂ := by
  simp only [monoEval]
  exact Finsupp.prod_add_index (fun a _ => by simp) (fun a _ b₁ b₂ => by simp [pow_add])

theorem monoEval_single (v : Vec k σ) (i : σ) (k : ℕ) :
    monoEval v (Finsupp.single i k) = v i ^ k := by
  simp only [monoEval]
  exact Finsupp.prod_single_index (by simp)

theorem monoEval_smul {v : Vec k σ} {c : k} (m : σ →₀ ℕ) :
    monoEval (c • v) m = c ^ m.degree * monoEval v m := by
  have h : (MvPolynomial.monomial m (1 : k)).IsHomogeneous m.degree := by
    apply MvPolynomial.isHomogeneous_monomial
    rfl
  rw [monoEval_eq_eval_monomial, monoEval_eq_eval_monomial,
    eval_smul_of_isHomogeneous h]

/-- The `d`-uple embedding on vectors: `v ↦ (M_0(v), …, M_N(v))`. -/
def rhoVec (d : ℕ) (v : Vec k σ) : Vec k (Monom σ d) := fun m => monoEval v m.1

theorem rhoVec_smul (d : ℕ) (c : k) (v : Vec k σ) :
    rhoVec d (c • v) = c ^ d • rhoVec d v := by
  funext m
  simp only [rhoVec, Pi.smul_apply, smul_eq_mul]
  rw [monoEval_smul, m.2]

theorem exists_coord_ne_zero {v : Vec k σ} (hv : v ≠ 0) : ∃ i, v i ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext h)

theorem rhoVec_ne_zero {d : ℕ} (hd : 1 ≤ d) {v : Vec k σ} (hv : v ≠ 0) :
    rhoVec d v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hv
  intro h
  have h2 : rhoVec d v ⟨Finsupp.single i d, by simp⟩ = 0 := congrFun h _
  simp only [rhoVec, monoEval_single] at h2
  rcases eq_or_ne (v i) 0 with h0 | h0
  · exact hi h0
  · exact absurd h2 (pow_ne_zero d h0)

/-- **The `d`-uple embedding** `ρ_d : P^σ → P^{Monom(σ,d)}` of Hartshorne Ex. I.2.12
(for `d ≥ 1`). -/
def rho (d : ℕ) (hd : 1 ≤ d) : Proj k σ → Proj k (Monom σ d) :=
  Quot.lift (fun v : {v : Vec k σ // v ≠ 0} => mk (rhoVec_ne_zero hd v.2)) (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, hvw⟩
    have hvw' : v = c • w := hvw
    refine (mk_eq_mk_iff (rhoVec_ne_zero hd hv) (rhoVec_ne_zero hd hw)).2
      ⟨c ^ d, pow_ne_zero d hc, ?_⟩
    rw [hvw']
    exact rhoVec_smul d c w)

theorem rho_mk (d : ℕ) (hd : 1 ≤ d) {v : Vec k σ} (hv : v ≠ 0) :
    rho (k := k) d hd (mk hv) = mk (rhoVec_ne_zero hd hv) := rfl

/-- The monomial `x_i^d`, as an index. -/
def monoPow (i : σ) (d : ℕ) : Monom σ d :=
  ⟨Finsupp.single i d, by simp⟩

/-- The monomial `x_i^{d-1} x_j` (`j ≠ i`), as an index. -/
def monoShift (i : σ) (j : σ) (d : ℕ) (hd : 1 ≤ d) : Monom σ d :=
  ⟨Finsupp.single i (d - 1) + Finsupp.single j 1, by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega⟩

theorem monoEval_monoPow (v : Vec k σ) (i : σ) (d : ℕ) :
    monoEval v (monoPow i d).1 = v i ^ d := by
  show monoEval v (Finsupp.single i d) = v i ^ d
  exact monoEval_single v i d

theorem monoEval_monoShift (v : Vec k σ) (i : σ) (j : σ) (d : ℕ) (hd : 1 ≤ d) :
    monoEval v (monoShift i j d hd).1 = v i ^ (d - 1) * v j := by
  have hval : (monoShift i j d hd).1 = Finsupp.single i (d - 1) + Finsupp.single j 1 := rfl
  rw [hval, monoEval_add, monoEval_single, monoEval_single, pow_one]

theorem monoShift_ne_monoPow (i : σ) {j : σ} (hj : j ≠ i) (d : ℕ) (hd : 1 ≤ d) :
    monoShift i j d hd ≠ monoPow i d := by
  intro h
  have h1 : (monoShift i j d hd).1 j = (monoPow i d).1 j := by rw [h]
  have h2 : (monoShift i j d hd).1 j = 1 := by
    have hval : (monoShift i j d hd).1 = Finsupp.single i (d - 1) + Finsupp.single j 1 := rfl
    rw [hval]
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hj]
  have h3 : (monoPow i d).1 j = 0 := by
    show Finsupp.single i d j = 0
    rw [Finsupp.single_eq_of_ne hj]
  rw [h2, h3] at h1
  exact one_ne_zero h1

/-- `ρ_d` maps the chart `U_i` into the chart `V_{x_i^d}`. -/
theorem inChart_rho_iff (d : ℕ) (hd : 1 ≤ d) (i : σ) (p : Proj k σ) :
    InChart (monoPow i d) (rho (k := k) d hd p) ↔ InChart i p := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := exists_mk p
    rw [inChart_mk hv]
    have h2 : InChart (monoPow i d) (rho d hd (mk hv)) := h
    rw [rho_mk, inChart_mk (rhoVec_ne_zero hd hv)] at h2
    have h3 : rhoVec d v (monoPow i d) ≠ 0 := h2
    rw [rhoVec, monoEval_monoPow] at h3
    intro hv0
    exact h3 (by rw [hv0, zero_pow (by omega)])
  · intro h
    obtain ⟨v, hv, rfl⟩ := exists_mk p
    rw [inChart_mk hv] at h
    rw [rho_mk, inChart_mk (rhoVec_ne_zero hd hv), rhoVec, monoEval_monoPow]
    exact pow_ne_zero d h

/-- The coordinate formula for the `d`-uple embedding on the chart `U_i`: in the affine
coordinates `z_j = x_j/x_i` of the source and `w_m = y_m/y_{x_i^d}` of the target,
`ρ_d` is the monomial map `w_m = ∏_j z_j^{m_j}`. -/
theorem chartCoord_rho (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (p : {p : Proj k σ // InChart i p}) (m : Monom σ d) (hm : m ≠ monoPow i d) :
    chartCoord (monoPow i d) ⟨rho (k := k) d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩
        ⟨m, hm⟩ =
      monoEval (chartVec i (chartCoord i p)) m.1 := by
  set q : {q : Proj k (Monom σ d) // InChart (monoPow i d) q} :=
    ⟨rho d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩ with hq
  have hmk : mk (chartRep_ne_zero (monoPow i d) q) = (q : Proj k (Monom σ d)) :=
    mk_chartRep _ q
  have hmk2 : mk (chartVec_ne_zero i (chartCoord i p)) = (p : Proj k σ) :=
    congrArg Subtype.val (chartInv_chartCoord i p)
  have hrho : (q : Proj k (Monom σ d)) =
      mk (rhoVec_ne_zero hd (chartVec_ne_zero i (chartCoord i p))) := by
    rw [hq]
    show rho d hd (p : Proj k σ) = mk (rhoVec_ne_zero hd (chartVec_ne_zero i (chartCoord i p)))
    rw [← hmk2]
    exact rho_mk d hd _
  obtain ⟨c, hc, hcw⟩ := (mk_eq_mk_iff (chartRep_ne_zero (monoPow i d) q)
    (rhoVec_ne_zero hd (chartVec_ne_zero i (chartCoord i p)))).1 (by rw [hmk]; exact hrho)
  have hc0 : c ≠ 0 := hc
  show chartRep (monoPow i d) q m / chartRep (monoPow i d) q (monoPow i d) =
      monoEval (chartVec i (chartCoord i p)) m.1
  rw [hcw]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hden : rhoVec d (chartVec i (chartCoord i p)) (monoPow i d) = 1 := by
    rw [rhoVec, monoEval_monoPow, chartVec_apply_same]
    exact one_pow d
  rw [hden, mul_one]
  field_simp
  rfl


/-- **Injectivity of the `d`-uple embedding** (`d ≥ 1`). -/
theorem rho_injective (d : ℕ) (hd : 1 ≤ d) : Function.Injective (rho (k := k) (σ := σ) d hd) := by
  intro p q hpq
  obtain ⟨u, hu, rfl⟩ := exists_mk p
  obtain ⟨v, hv, hvq⟩ := exists_mk q
  subst hvq
  rw [rho_mk, rho_mk] at hpq
  obtain ⟨c, hc, hcu⟩ :=
    (mk_eq_mk_iff (rhoVec_ne_zero hd hu) (rhoVec_ne_zero hd hv)).1 hpq
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hu
  have h1 : u i ^ d = c * v i ^ d := by
    have h := congrFun hcu (monoPow i d)
    simpa only [rhoVec, Pi.smul_apply, smul_eq_mul, monoEval_monoPow] using h
  have hvi : v i ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), mul_zero] at h1
    rcases eq_or_ne (u i) 0 with h | h
    · exact hi h
    · exact absurd h1 (pow_ne_zero d h)
  refine (mk_eq_mk_iff hu hv).2 ⟨u i / v i, div_ne_zero hi hvi, ?_⟩
  funext j
  have h2 : u i ^ (d - 1) * u j = c * (v i ^ (d - 1) * v j) := by
    have h := congrFun hcu (monoShift i j d hd)
    simpa only [rhoVec, Pi.smul_apply, smul_eq_mul, monoEval_monoShift] using h
  have key : u j / u i = v j / v i := by
    have hpd : ∀ x : k, x ^ (d - 1) * x = x ^ d := by
      intro x
      have hd1 : d - 1 + 1 = d := by omega
      calc x ^ (d - 1) * x = x ^ (d - 1 + 1) := (pow_succ x (d - 1)).symm
        _ = x ^ d := by rw [hd1]
    have step : u i ^ (d - 1) * (u j * v i) = u i ^ (d - 1) * (u i * v j) := by
      have e1 : c * (v i ^ (d - 1) * v j) * v i = u i ^ d * v j := by
        rw [h1]
        calc c * (v i ^ (d - 1) * v j) * v i = c * (v i ^ (d - 1) * v i) * v j := by ring
          _ = c * v i ^ d * v j := by rw [hpd]
      calc u i ^ (d - 1) * (u j * v i) = (u i ^ (d - 1) * u j) * v i := by ring
        _ = (c * (v i ^ (d - 1) * v j)) * v i := by rw [h2]
        _ = u i ^ d * v j := e1
        _ = (u i ^ (d - 1) * u i) * v j := by rw [hpd]
        _ = u i ^ (d - 1) * (u i * v j) := by ring
    have := mul_left_cancel₀ (pow_ne_zero (d - 1) hi) step
    exact div_eq_div_iff hi hvi |>.2 (by linear_combination this)
  show u j = (u i / v i) * v j
  have hkey : u j / u i = v j / v i := key
  simp only [div_eq_mul_inv] at hkey ⊢
  calc u j = (u j * (u i)⁻¹) * u i := by field_simp
    _ = (v j * (v i)⁻¹) * u i := by rw [hkey]
    _ = u i * (v i)⁻¹ * v j := by ring

/-! ## 5. Continuity of `ρ_d`: pullback of forms and of projective zero loci. -/

section Continuity

variable {σ : Type*} [DecidableEq σ]

/-- The pullback of a polynomial on the target `P^{Monom(σ,d)}` along `ρ_d`: replace the
coordinate `y_m` by the monomial `m`.  (On the level of forms this is the ring map
`y_m ↦ M_m` of Hartshorne Ex. I.2.12(a).) -/
def subst (d : ℕ) : MvPolynomial (Monom σ d) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun m : Monom σ d => MvPolynomial.monomial m.1 (1 : k))

/-- Evaluation of a pulled-back form at `v` is evaluation of the form at `ρ_d(v)`. -/
theorem eval_subst (d : ℕ) (f : MvPolynomial (Monom σ d) k) (v : Vec k σ) :
    MvPolynomial.eval v (subst (k := k) d f) = MvPolynomial.eval (rhoVec d v) f := by
  have h : (MvPolynomial.eval v).comp (subst (k := k) (σ := σ) d).toRingHom =
      MvPolynomial.eval (rhoVec d v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [subst]
    · intro m
      have hX : subst (k := k) (σ := σ) d (MvPolynomial.X m) =
          MvPolynomial.monomial m.1 (1 : k) := by
        simp [subst]
      show MvPolynomial.eval v (subst (k := k) (σ := σ) d (MvPolynomial.X m)) =
        MvPolynomial.eval (rhoVec d v) (MvPolynomial.X m)
      rw [hX, MvPolynomial.eval_X, ← monoEval_eq_eval_monomial]
      rfl
  exact DFunLike.congr_fun h f

/-- The pullback of a homogeneous form of degree `e` is homogeneous of degree `d * e`. -/
theorem subst_isHomogeneous (d : ℕ) {f : MvPolynomial (Monom σ d) k} {e : ℕ}
    (hf : f.IsHomogeneous e) : (subst (k := k) d f).IsHomogeneous (d * e) :=
  hf.aeval (fun m : Monom σ d => MvPolynomial.monomial m.1 (1 : k)) (fun m => by
    have h := MvPolynomial.isHomogeneous_monomial (R := k) (σ := σ) (d := m.1) (r := (1 : k)) m.2
    simpa using h)

theorem subst_image_homogeneous {T : Set (MvPolynomial (Monom σ d) k)}
    (hT : ∀ f ∈ T, ∃ e, f.IsHomogeneous e) :
    ∀ f ∈ subst (k := k) d '' T, ∃ e, f.IsHomogeneous e := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨e, he⟩ := hT f hf
  exact ⟨_, subst_isHomogeneous d he⟩

/-- **The preimage of a projective zero locus under `ρ_d`** is the zero locus of the
pulled-back forms. -/
theorem preimage_zeroLocus (d : ℕ) (hd : 1 ≤ d) {T : Set (MvPolynomial (Monom σ d) k)}
    (hT : ∀ f ∈ T, ∃ e, f.IsHomogeneous e) :
    rho (k := k) d hd ⁻¹' zeroLocus T = zeroLocus (subst (k := k) d '' T) := by
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [Set.mem_preimage, rho_mk, mem_zeroLocus_iff hT (rhoVec_ne_zero hd hv),
    mem_zeroLocus_iff (subst_image_homogeneous hT) hv]
  constructor
  · rintro h _ ⟨f, hf, rfl⟩
    rw [eval_subst]
    exact h f hf
  · intro h f hf
    rw [← eval_subst]
    exact h _ ⟨f, hf, rfl⟩

/-- **`ρ_d` is continuous.** -/
theorem rho_continuous (d : ℕ) (hd : 1 ≤ d) : Continuous (rho (k := k) (σ := σ) d hd) := by
  rw [continuous_def]
  intro U hU
  obtain ⟨T, hT, rfl⟩ := hU
  rw [Set.preimage_compl, preimage_zeroLocus d hd hT]
  exact (isClosed_zeroLocus (subst_image_homogeneous hT)).isOpen_compl

end Continuity

/-! ## 6. Regular functions, morphisms, and `ρ_d` is a morphism. -/

section Regular

variable {ι : Type*}

/-- Evaluation of a form at a projective point through the chosen representative. -/
def evalRep (f : MvPolynomial ι k) (p : Proj k ι) : k := MvPolynomial.eval (rep p) f

/-- Changing the representative multiplies the value by `c^e` (for homogeneous `f` of
degree `e`): this is what makes quotients of forms of the same degree well defined. -/
theorem evalRep_eq_smul {p : Proj k ι} {v : Vec k ι} (hv : v ≠ 0) (hp : mk hv = p)
    {f : MvPolynomial ι k} {e : ℕ} (hf : f.IsHomogeneous e) :
    ∃ c : k, c ≠ 0 ∧ evalRep f p = c ^ e * MvPolynomial.eval v f := by
  obtain ⟨c, hc, hrep⟩ := (mk_eq_mk_iff (rep_ne_zero p) hv).1 (by rw [mk_rep]; exact hp.symm)
  exact ⟨c, hc, by rw [evalRep, hrep, eval_smul_of_isHomogeneous hf]⟩

theorem evalRep_ne_zero_iff {f : MvPolynomial ι k} {e : ℕ} (hf : f.IsHomogeneous e)
    (p : Proj k ι) : evalRep f p ≠ 0 ↔ ¬ FormVanishesAt f p := by
  have h : FormVanishesAt f p ↔ evalRep f p = 0 := by
    have h2 := formVanishesAt_mk_iff hf (rep_ne_zero p)
    rw [mk_rep p] at h2
    simpa [evalRep] using h2
  rw [h]

/-- The set where a homogeneous form does not vanish is Zariski open. -/
theorem isOpen_evalRep_ne_zero {f : MvPolynomial ι k} {e : ℕ} (hf : f.IsHomogeneous e) :
    IsOpen {p : Proj k ι | evalRep f p ≠ 0} := by
  have hset : {p : Proj k ι | evalRep f p ≠ 0} = (zeroLocus {f})ᶜ := by
    ext p
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, evalRep_ne_zero_iff hf, zeroLocus]
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
  exact ⟨{f}, by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨e, hf⟩, hset⟩

/-- **Regular function at a point** (Hartshorne I.3, p. 15, quasi-projective case): locally
a quotient of two homogeneous forms of the same degree with nowhere-vanishing denominator. -/
def IsRegularAt (Y : Set (Proj k ι)) (f : Y → k) (y : Y) : Prop :=
  ∃ U : Set (Proj k ι), IsOpen U ∧ y.1 ∈ U ∧
    ∃ (g h : MvPolynomial ι k) (e : ℕ), g.IsHomogeneous e ∧ h.IsHomogeneous e ∧
      (∀ z : Y, z.1 ∈ U → evalRep h z.1 ≠ 0) ∧
      (∀ z : Y, z.1 ∈ U → f z = evalRep g z.1 / evalRep h z.1)

/-- A regular function on a quasi-projective set. -/
def IsRegular (Y : Set (Proj k ι)) (f : Y → k) : Prop := ∀ y, IsRegularAt Y f y

end Regular

section Morphism

variable {ι : Type*} {ι' : Type*}

/-- **Morphism of varieties** (Hartshorne I.3, p. 15): a continuous map which pulls regular
functions back to regular functions.  Since every regular function is locally a quotient
`g/h` of homogeneous forms of the same degree, it suffices (and is equivalent) to require
this for all such quotients, which is the condition used below. -/
def IsMorphism (Y : Set (Proj k ι)) (Z : Set (Proj k ι')) (φ : Y → Z) : Prop :=
  Continuous φ ∧
    ∀ (g h : MvPolynomial ι' k) (e : ℕ), g.IsHomogeneous e → h.IsHomogeneous e →
      ∀ y : Y, evalRep h (φ y).1 ≠ 0 →
        IsRegularAt Y (fun z : Y => evalRep g (φ z).1 / evalRep h (φ z).1) y

end Morphism

section RhoMorphism

variable {σ : Type*} [DecidableEq σ]

/-- The proportionality constant between a representative of `ρ_d(p)` and `ρ_d` of a
representative of `p`; it is the same for all forms, which is what makes quotients pull back. -/
theorem exists_smul_rep_rho (d : ℕ) (hd : 1 ≤ d) (p : Proj k σ) :
    ∃ c : k, c ≠ 0 ∧ ∀ (e : ℕ) (f : MvPolynomial (Monom σ d) k), f.IsHomogeneous e →
      evalRep f (rho (k := k) d hd p) = c ^ e * evalRep (subst (k := k) d f) p := by
  classical
  have hp : mk (rep_ne_zero p) = p := mk_rep p
  have h1 : rho (k := k) d hd p = mk (rhoVec_ne_zero hd (rep_ne_zero p)) := by
    conv_lhs => rw [← hp]
    exact rho_mk (k := k) (σ := σ) d hd (rep_ne_zero p)
  have hrepr : mk (rep_ne_zero (rho d hd p)) =
      mk (rhoVec_ne_zero hd (rep_ne_zero p)) := by
    rw [mk_rep]
    exact h1
  obtain ⟨μ, hμ, hμeq⟩ := (mk_eq_mk_iff (rep_ne_zero (rho d hd p))
    (rhoVec_ne_zero hd (rep_ne_zero p))).1 hrepr
  refine ⟨μ, hμ, ?_⟩
  intro e f hf
  simp only [evalRep]
  rw [hμeq, eval_smul_of_isHomogeneous hf, eval_subst]

/-- **`ρ_d` is a morphism of varieties** (into its image). -/
theorem rho_isMorphism (d : ℕ) (hd : 1 ≤ d) :
    IsMorphism (Set.univ : Set (Proj k σ)) (Set.range (rho (k := k) d hd))
      (fun p => (⟨rho d hd p.1, Set.mem_range_self p.1⟩ : Set.range (rho d hd))) := by
  constructor
  · exact Continuous.subtype_mk ((rho_continuous d hd).comp continuous_subtype_val) _
  · intro g h e hg hh y hy
    obtain ⟨c, hc0, hcl⟩ := exists_smul_rep_rho (k := k) (σ := σ) d hd y.1
    have hce : c ^ e ≠ 0 := pow_ne_zero e hc0
    have hy' : evalRep (subst (k := k) d h) y.1 ≠ 0 := by
      intro h0
      apply hy
      rw [hcl e h hh, h0, mul_zero]
    refine ⟨{z : Proj k σ | evalRep (subst (k := k) d h) z ≠ 0},
      isOpen_evalRep_ne_zero (subst_isHomogeneous d hh), hy',
      subst (k := k) d g, subst (k := k) d h, d * e,
      subst_isHomogeneous d hg, subst_isHomogeneous d hh, ?_, ?_⟩
    · intro z hz
      exact hz
    · intro z hz
      obtain ⟨c', hc'0, hcl'⟩ := exists_smul_rep_rho (k := k) (σ := σ) d hd (z : Proj k σ)
      show evalRep g (rho (k := k) d hd (z : Proj k σ)) /
          evalRep h (rho (k := k) d hd (z : Proj k σ)) =
        evalRep (subst (k := k) d g) (z : Proj k σ) /
          evalRep (subst (k := k) d h) (z : Proj k σ)
      rw [hcl' e g hg, hcl' e h hh]
      field_simp

end RhoMorphism

/-! ## 7. The inverse of `ρ_d` on its image, and its chart formula. -/

section Psi

variable {σ : Type*} [DecidableEq σ]

/-- The source coordinates recovered from the target chart `V_{x_i^d}`:
`x_j/x_i = y_{x_i^{d-1}x_j}/y_{x_i^d}`. -/
def psiCoord (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : {q : Proj k (Monom σ d) // InChart (monoPow i d) q}) : {j : σ // j ≠ i} → k :=
  fun j => chartCoord (monoPow i d) q ⟨monoShift i j.1 d hd, monoShift_ne_monoPow i j.2 d hd⟩

/-- The inverse of `ρ_d`, computed in the chart `V_{x_i^d}`. -/
def psiChart (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : {q : Proj k (Monom σ d) // InChart (monoPow i d) q}) : {p : Proj k σ // InChart i p} :=
  chartInv i (psiCoord d hd i q)

theorem psiCoord_rho (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (p : {p : Proj k σ // InChart i p}) :
    psiCoord d hd i ⟨rho (k := k) (σ := σ) d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩ =
      chartCoord i p := by
  funext j
  show chartCoord (monoPow i d) ⟨rho (k := k) (σ := σ) d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩
      ⟨monoShift i j.1 d hd, monoShift_ne_monoPow i j.2 d hd⟩ = chartCoord i p j
  rw [chartCoord_rho, monoEval_monoShift, chartVec_apply_same, one_pow, one_mul]
  exact chartVec_apply_ne i (chartCoord i p) j.2

theorem psiChart_rho (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (p : {p : Proj k σ // InChart i p}) :
    psiChart d hd i ⟨rho (k := k) (σ := σ) d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩ = p := by
  show chartInv i (psiCoord d hd i ⟨rho (k := k) (σ := σ) d hd p.1, (inChart_rho_iff d hd i p.1).2 p.2⟩) = p
  rw [psiCoord_rho]
  exact chartInv_chartCoord i p

/-- Every point of the image of `ρ_d` lies in one of the charts `V_{x_i^d}`. -/
theorem exists_inChart_monoPow (d : ℕ) (hd : 1 ≤ d) {q : Proj k (Monom σ d)}
    (hq : q ∈ Set.range (rho (k := k) (σ := σ) d hd)) : ∃ i : σ, InChart (monoPow i d) q := by
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨i, hi⟩ := exists_mem_chart p
  exact ⟨i, (inChart_rho_iff d hd i p).2 hi⟩

/-- **The inverse of the `d`-uple embedding** on its image. -/
def psi (d : ℕ) (hd : 1 ≤ d) (q : Set.range (rho (k := k) (σ := σ) d hd)) : Proj k σ :=
  (psiChart d hd (exists_inChart_monoPow d hd q.2).choose
    ⟨q.1, (exists_inChart_monoPow d hd q.2).choose_spec⟩).1

theorem psi_rho (d : ℕ) (hd : 1 ≤ d) (p : Proj k σ) :
    psi d hd ⟨rho (k := k) d hd p, Set.mem_range_self p⟩ = p := by
  have h := (exists_inChart_monoPow d hd (Set.mem_range_self p :
    rho (k := k) (σ := σ) d hd p ∈ Set.range (rho (k := k) (σ := σ) d hd))).choose_spec
  have hp : InChart (exists_inChart_monoPow d hd (Set.mem_range_self p :
      rho (k := k) (σ := σ) d hd p ∈ Set.range (rho (k := k) (σ := σ) d hd))).choose p :=
    (inChart_rho_iff d hd _ p).1 h
  show (psiChart d hd _ ⟨rho (k := k) (σ := σ) d hd p, h⟩).1 = p
  exact congrArg Subtype.val (psiChart_rho d hd _ ⟨p, hp⟩)

theorem rho_psi (d : ℕ) (hd : 1 ≤ d) (q : Set.range (rho (k := k) (σ := σ) d hd)) :
    rho (k := k) (σ := σ) d hd (psi d hd q) = q.1 := by
  obtain ⟨p, hp⟩ := q.2
  have hq : q = ⟨rho (k := k) (σ := σ) d hd p, Set.mem_range_self p⟩ := by
    apply Subtype.ext
    exact hp.symm
  rw [hq, psi_rho d hd p]

/-- On any chart containing the point, `psi` is given by the chart formula `psiChart`. -/
theorem psi_eq_psiChart (d : ℕ) (hd : 1 ≤ d) (q : Set.range (rho (k := k) (σ := σ) d hd)) (i : σ)
    (hq : InChart (monoPow i d) q.1) :
    psi d hd q = (psiChart d hd i ⟨q.1, hq⟩).1 := by
  obtain ⟨p, hp⟩ := q.2
  have hq' : q = ⟨rho (k := k) (σ := σ) d hd p, Set.mem_range_self p⟩ := by
    apply Subtype.ext
    exact hp.symm
  cases hq'
  have hp' : InChart i p := (inChart_rho_iff d hd i p).1 hq
  rw [psi_rho d hd p]
  exact (congrArg Subtype.val (psiChart_rho d hd i ⟨p, hp'⟩)).symm

/-- The map `j ↦ x_i^{d-1}x_j` is injective. -/
theorem monoShift_self (i : σ) (d : ℕ) (hd : 1 ≤ d) : monoShift i i d hd = monoPow i d := by
  apply Subtype.ext
  show Finsupp.single i (d - 1) + Finsupp.single i 1 = Finsupp.single i d
  rw [← Finsupp.single_add, show d - 1 + 1 = d by omega]

theorem monoShift_injective (i : σ) (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (fun j : σ => monoShift i j d hd) := by
  intro j j' h
  have h1 : (monoShift i j d hd).1 = (monoShift i j' d hd).1 := congrArg Subtype.val h
  have h2 : (monoShift i j d hd).1 = Finsupp.single i (d - 1) + Finsupp.single j 1 := rfl
  have h3 : (monoShift i j' d hd).1 = Finsupp.single i (d - 1) + Finsupp.single j' 1 := rfl
  rw [h2, h3] at h1
  exact Finsupp.single_left_injective one_ne_zero (add_left_cancel h1)

/-- `psiCoord` is the dehomogenization of the vector `(y_{x_i^{d-1}x_j})_j`. -/
theorem psiCoord_eq (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : {q : Proj k (Monom σ d) // InChart (monoPow i d) q}) :
    psiCoord d hd i q = fun j =>
      chartVec (monoPow i d) (chartCoord (monoPow i d) q) (monoShift i j.1 d hd) := by
  funext j
  rw [psiCoord, chartVec_apply_ne (monoPow i d) _ (monoShift_ne_monoPow i j.2 d hd)]

/-- **The inverse is given by regular (indeed linear) functions of the chart coordinates**:
on the chart `V_{x_i^d}`, pulling a form back along `psi` is the same as applying the
monomial substitution `x_j ↦ x_i^{d-1}x_j`, `x_i ↦ x_i^d`. -/
theorem eval_psi_chart (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : {q : Proj k (Monom σ d) // InChart (monoPow i d) q})
    (g : MvPolynomial σ k) :
    MvPolynomial.eval (chartVec i (psiCoord d hd i q)) g =
      MvPolynomial.eval (chartVec (monoPow i d) (chartCoord (monoPow i d) q))
        (MvPolynomial.rename (fun j => monoShift i j d hd) g) := by
  rw [MvPolynomial.eval_rename]
  have hv : chartVec i (psiCoord d hd i q) =
      chartVec (monoPow i d) (chartCoord (monoPow i d) q) ∘ fun j => monoShift i j d hd := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.comp_apply, chartVec_apply_same, monoShift_self]
    · simp only [Function.comp_apply, chartVec_apply_ne i _ hj, psiCoord_eq,
        chartVec_apply_ne (monoPow i d) _ (monoShift_ne_monoPow i hj d hd)]
  rw [hv]

end Psi

/-! ## 8. `psi` is a morphism; `ρ_d` is an isomorphism onto its image. -/

section PsiMorphism

variable {σ : Type*} [DecidableEq σ]

/-- Evaluation at a point of a chart through its normalized representative. -/
theorem evalRep_eq_chartVec {ι : Type*} [DecidableEq ι] (i : ι)
    (q : {q : Proj k ι // InChart i q}) {f : MvPolynomial ι k} {e : ℕ}
    (hf : f.IsHomogeneous e) :
    evalRep f q.1 = (chartRep i q i) ^ e * MvPolynomial.eval (chartVec i (chartCoord i q)) f := by
  have hsm : MvPolynomial.eval (chartRep i q i • chartVec i (chartCoord i q)) f
      = (chartRep i q i) ^ e * MvPolynomial.eval (chartVec i (chartCoord i q)) f :=
    eval_smul_of_isHomogeneous hf _ _
  rw [evalRep]
  conv_lhs => rw [← chartRep_eq_rep i q, chartRep_eq_smul_chartVec i q]
  exact hsm

/-- The (nonzero) scaling constant comparing the normalized representative of `q` with that
of `psi q` on the chart `V_{x_i^d}`. -/
def psiScale (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : Set.range (rho (k := k) (σ := σ) d hd)) (hq : InChart (monoPow i d) q.1) : k :=
  chartRep i (chartInv i (psiCoord d hd i ⟨q.1, hq⟩)) i /
    chartRep (monoPow i d) ⟨q.1, hq⟩ (monoPow i d)

theorem psiScale_ne_zero (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : Set.range (rho (k := k) (σ := σ) d hd)) (hq : InChart (monoPow i d) q.1) :
    psiScale d hd i q hq ≠ 0 :=
  div_ne_zero (chartRep_coord_ne_zero i _) (chartRep_coord_ne_zero (monoPow i d) _)

/-- **The inverse is given by regular functions of the chart coordinates.**  On the chart
`V_{x_i^d}`, pulling a form back along `psi` is, up to the nonzero constant `psiScale`, the
linear substitution `x_j ↦ x_i^{d-1}x_j`, `x_i ↦ x_i^d`. -/
theorem psi_eval_ratio (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : Set.range (rho (k := k) (σ := σ) d hd)) (hq : InChart (monoPow i d) q.1)
    {f : MvPolynomial σ k} {e : ℕ} (hf : f.IsHomogeneous e) :
    evalRep f (psi d hd q) = psiScale d hd i q hq ^ e *
      evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) f) q.1 := by
  set qc : {q : Proj k (Monom σ d) // InChart (monoPow i d) q} := ⟨q.1, hq⟩ with hqc
  have hpsi : psi d hd q = (chartInv i (psiCoord d hd i qc)).1 := by
    rw [psi_eq_psiChart d hd q i hq]
    rfl
  have h1 : evalRep f (psi d hd q) =
      (chartRep i (chartInv i (psiCoord d hd i qc)) i) ^ e *
        MvPolynomial.eval (chartVec i (psiCoord d hd i qc)) f := by
    rw [hpsi]
    have h := evalRep_eq_chartVec (k := k) i (chartInv i (psiCoord d hd i qc)) hf
    rwa [chartCoord_chartInv] at h
  have h2 : MvPolynomial.eval (chartVec i (psiCoord d hd i qc)) f =
      MvPolynomial.eval (chartVec (monoPow i d) (chartCoord (monoPow i d) qc))
        (MvPolynomial.rename (fun j => monoShift i j d hd) f) := eval_psi_chart d hd i qc f
  have hren : (MvPolynomial.rename (fun j => monoShift i j d hd) f).IsHomogeneous e :=
    (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff
      (monoShift_injective i d hd)).2 hf
  have h3 : evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) f) q.1 =
      (chartRep (monoPow i d) qc (monoPow i d)) ^ e *
        MvPolynomial.eval (chartVec (monoPow i d) (chartCoord (monoPow i d) qc))
          (MvPolynomial.rename (fun j => monoShift i j d hd) f) :=
    evalRep_eq_chartVec (k := k) (monoPow i d) qc hren
  have ha : chartRep i (chartInv i (psiCoord d hd i qc)) i ≠ 0 := chartRep_coord_ne_zero i _
  have hb : chartRep (monoPow i d) qc (monoPow i d) ≠ 0 := chartRep_coord_ne_zero _ qc
  show evalRep f (psi d hd q) = (chartRep i (chartInv i (psiCoord d hd i qc)) i /
      chartRep (monoPow i d) qc (monoPow i d)) ^ e *
    evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) f) q.1
  rw [h1, h2, h3, div_pow]
  field_simp

/-- Vanishing of a form at `psi q` is detected by the renamed form at `q`. -/
theorem psi_zero_iff (d : ℕ) (hd : 1 ≤ d) (i : σ)
    (q : Set.range (rho (k := k) (σ := σ) d hd)) (hq : InChart (monoPow i d) q.1)
    {f : MvPolynomial σ k} {e : ℕ} (hf : f.IsHomogeneous e) :
    evalRep f (psi d hd q) = 0 ↔
      evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) f) q.1 = 0 := by
  have hce : psiScale d hd i q hq ^ e ≠ 0 :=
    pow_ne_zero e (psiScale_ne_zero d hd i q hq)
  rw [psi_eval_ratio d hd i q hq hf]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hce
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **The inverse map is continuous**: its preimages of closed sets are closed, because on each
chart `V_{x_i^d}` it is given by the renamed forms. -/
theorem psi_continuous (d : ℕ) (hd : 1 ≤ d) :
    Continuous (psi (k := k) (σ := σ) d hd) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  rw [Set.mem_compl_iff, Set.mem_preimage, zeroLocus, Set.mem_ofPred_eq] at hq
  push Not at hq
  obtain ⟨f, hfT, hfv⟩ := hq
  obtain ⟨e, he⟩ := hT f hfT
  obtain ⟨i, hi⟩ := exists_inChart_monoPow d hd q.2
  have hren : (MvPolynomial.rename (fun j => monoShift i j d hd) f).IsHomogeneous e :=
    (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff (monoShift_injective i d hd)).2 he
  refine ⟨{q' : Set.range (rho (k := k) (σ := σ) d hd) |
      InChart (monoPow i d) q'.1 ∧
        evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) f) q'.1 ≠ 0},
    ?_, (isOpen_chart (monoPow i d)).inter (isOpen_evalRep_ne_zero hren) |>.preimage
      continuous_subtype_val, ⟨hi, ?_⟩⟩
  · rintro q' ⟨hq'i, hq'v⟩ hq'z
    refine hq'v ?_
    have h0 : evalRep f (psi d hd q') = 0 :=
      hq'z f hfT (rep (psi d hd q')) (rep_ne_zero _) (mk_rep _)
    rw [psi_zero_iff d hd i q' hq'i he] at h0
    exact h0
  · intro h0
    apply hfv
    have h0' : MvPolynomial.eval (rep (psi d hd q)) f = 0 := (psi_zero_iff d hd i q hi he).2 h0
    have h1 : FormVanishesAt f (mk (rep_ne_zero (psi d hd q))) :=
      (formVanishesAt_mk_iff he (rep_ne_zero (psi d hd q))).2 h0'
    rwa [mk_rep] at h1

/-- **`psi` is a morphism of varieties.** -/
theorem psi_isMorphism (d : ℕ) (hd : 1 ≤ d) :
    IsMorphism (Set.range (rho (k := k) (σ := σ) d hd)) Set.univ
      (fun q => (⟨psi d hd q, Set.mem_univ _⟩ : Set.univ)) := by
  refine ⟨?_, ?_⟩
  · exact Continuous.subtype_mk (psi_continuous d hd) _
  · intro g h e hg hh q hqne
    obtain ⟨i, hi⟩ : ∃ i, InChart i (psi d hd q) := exists_mem_chart (psi d hd q)
    have hqi : InChart (monoPow i d) q.1 := by
      rw [← rho_psi d hd q]
      exact (inChart_rho_iff d hd i (psi d hd q)).2 hi
    have hreng : (MvPolynomial.rename (fun j => monoShift i j d hd) g).IsHomogeneous e :=
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff (monoShift_injective i d hd)).2 hg
    have hrenh : (MvPolynomial.rename (fun j => monoShift i j d hd) h).IsHomogeneous e :=
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff (monoShift_injective i d hd)).2 hh
    have hqne' : evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) h) q.1 ≠ 0 := by
      intro h0
      exact hqne ((psi_zero_iff d hd i q hqi hh).2 h0)
    refine ⟨{p : Proj k (Monom σ d) | InChart (monoPow i d) p ∧
        evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) h) p ≠ 0},
      (isOpen_chart (monoPow i d)).inter (isOpen_evalRep_ne_zero hrenh), ⟨hqi, hqne'⟩,
      MvPolynomial.rename (fun j => monoShift i j d hd) g,
      MvPolynomial.rename (fun j => monoShift i j d hd) h, e, hreng, hrenh, ?_, ?_⟩
    · intro z hz
      exact hz.2
    · intro z hz
      show evalRep g (psi d hd z) / evalRep h (psi d hd z) =
        evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) g) z.1 /
          evalRep (MvPolynomial.rename (fun j => monoShift i j d hd) h) z.1
      have hce : psiScale d hd i z hz.1 ^ e ≠ 0 :=
        pow_ne_zero e (psiScale_ne_zero d hd i z hz.1)
      rw [psi_eval_ratio d hd i z hz.1 hg, psi_eval_ratio d hd i z hz.1 hh]
      rw [mul_div_mul_left _ _ hce]

end PsiMorphism

section Main

variable {σ : Type*} [DecidableEq σ]

/-- **Hartshorne (1977), Algebraic Geometry, Chapter I, Exercise 3.4.**  The `d`-uple
embedding `ρ_d : P^σ → P^{Monom(σ,d)}` (Ex. I.2.12, `d ≥ 1`) is an isomorphism of `P^σ`
onto its image: it is injective, it is a morphism of varieties, and the inverse map on the
image is also a morphism of varieties. -/
theorem hartshorne_I_3_4 (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (rho (k := k) (σ := σ) d hd) ∧
    IsMorphism (Set.univ : Set (Proj k σ)) (Set.range (rho (k := k) (σ := σ) d hd))
      (fun p => (⟨rho d hd p.1, Set.mem_range_self p.1⟩ : Set.range (rho d hd))) ∧
    IsMorphism (Set.range (rho (k := k) (σ := σ) d hd)) Set.univ
      (fun q => (⟨psi d hd q, Set.mem_univ _⟩ : Set.univ)) ∧
    (∀ p, psi d hd ⟨rho (k := k) (σ := σ) d hd p, Set.mem_range_self p⟩ = p) ∧
    (∀ q, rho (k := k) (σ := σ) d hd (psi d hd q) = q.1) :=
  ⟨rho_injective d hd, rho_isMorphism d hd, psi_isMorphism d hd,
    psi_rho d hd, rho_psi d hd⟩

end Main


/-! ## Axiom audit -/

#print axioms hartshorne_I_3_4
#print axioms rho_isMorphism
#print axioms psi_isMorphism
#print axioms rho_injective
#print axioms psi_rho
#print axioms rho_psi
#print axioms rho_continuous
#print axioms chartCoord_rho
#print axioms psi_eval_ratio

end Proj

end Monom

end

end Hartshorne77.Ex_I_3_4
