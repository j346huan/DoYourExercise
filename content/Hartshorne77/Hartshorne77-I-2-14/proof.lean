/-
Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise 2.14: **the Segre embedding**.

SOURCE STATEMENT (verbatim, reconstructed from the book's own text as reproduced in
`.scratch/reference/hartshorne-1977.txt` and `.scratch/reference/hartshorne-1977.html`, and
independently confirmed against two further public renderings of Hartshorne's book — the
djvu.online scan and the dokumen.pub copy of the Springer edition; see NOTES.md for the exact
quotations).  The local natural proof is
`.scratch/DoYourExercise/content/Hartshorne77/Hartshorne77-I-2-14/proof.tex`, catalogue entry
<https://j346huan.github.io/DoYourExercise/#/problem/Hartshorne77-I-2-14>.

  "2.14. The Segre Embedding.  Let ψ : P^r × P^s → P^N be the map defined by sending the
   ordered pair (a_0, …, a_r) × (b_0, …, b_s) to (…, a_i b_j, …) in lexicographic order,
   where N = rs + r + s.  Note that ψ is well-defined and injective.  It is called the
   Segre embedding.  Show that the image of ψ is a subvariety of P^N.
   [Hint: Let the homogeneous coordinates of P^N be {z_ij | i = 0, …, r, j = 0, …, s}, and
   let a be the kernel of the homomorphism k[{z_ij}] → k[x_0,…,x_r, y_0,…,y_s] which sends
   z_ij to x_i y_j.  Then show that Im ψ = Z(a).]"

Standing hypotheses of Chapter I (pp. 1, 3, 10, 22): `k` is an algebraically closed field;
`P^n` is the classical projective space of lines through the origin in `k^{n+1}`; an algebraic
set is a common zero locus `Z(T)` of homogeneous polynomials; a *projective variety* is an
irreducible algebraic set in some `P^n`, and a *subvariety* of `P^N` is a subset which is
itself a variety with the induced topology, i.e. (in `P^N`) a closed and irreducible subset.
Accordingly everything below is proved over an arbitrary *infinite* field and the
algebraically closed case is recorded separately (`hartshorne_I_2_14_algClosed`); the
infinite-field hypothesis is used exactly where the natural proof invokes it ("a polynomial
vanishing on all products x_i y_j becomes the zero polynomial over the infinite field k").
No exercise part is omitted, no point-set object is replaced by `Proj` of a graded ring, and
`Z`, `I`, `VanishOnLine` are the intrinsic zero locus / homogeneous vanishing ideal /
vanishing-on-the-line definitions.

CLAUSE-BY-CLAUSE COVERAGE MAP (source clause → Lean name):

1. `ψ : P^r × P^s → P^N` with `N = rs + r + s`            → `segre : Proj k r × Proj k s →
                                                              Proj k (r*s + r + s)`
2. coordinates `{z_ij}` of `P^N` in lexicographic order     → `zIdx`, `zIdx_apply`
   (`zIdx (i,j) = i(s+1) + j`), `zvar`
3. `(a_0,…,a_r) × (b_0,…,b_s) ↦ (…, a_i b_j, …)`           → `segreVec`, `segre_mk`,
                                                              `segreVec_zIdx`
4. "ψ is well-defined"                                      → `segre_welldef`
5. "ψ is injective"                                         → `segre_injective`
                                                              (`segreVec_injective`)
6. "the image of ψ is a subvariety of `P^N`"                → closed: `range_segre_isClosed`;
                                                              irreducible: `range_segre_isIrreducible`
7. hint: `{z_ij}` coordinates, `a = ker(k[{z_ij}] → k[x,y])`,
   `z_ij ↦ x_i y_j`                                        → `segreRingHom`, `kerSegre`,
                                                              `segreRingHom_X`
8. hint: "show that `Im ψ = Z(a)`"                          → `range_segre_eq_Z_ker`
9. natural proof: "the image is the closed set defined by
   the 2×2 minors"                                          → `minor`, `minorsSet`,
                                                              `range_segre_eq_Z_minors`
10. natural proof: "its homogeneous ideal is the kernel"     → `I_range_eq_kerSegre`
11. natural proof: "this kernel is prime, so the image is a
   projective variety"                                      → `kerSegre_isPrime`,
                                                              `range_segre_isIrreducible`
12. natural proof: "a polynomial vanishing on all products
   becomes the zero polynomial over the infinite field"      → `I_range_le_kerSegre`

The bundled statement is `hartshorne_I_2_14` (`SegreConclusion k r s`, all clauses), spelled
out without the abbreviation in `hartshorne_I_2_14_statement`, with
`hartshorne_I_2_14_algClosed` for Hartshorne's standing hypothesis.  No edge-case error was
found in the printed source statement: for `r = s = 0` one gets `P^0 × P^0 → P^0`, both sides
singletons, and the minors set is empty, which the formalization covers.

The file is standalone (`import Mathlib` only, Lean 4.33.1).  Sections 1 and the lemmas
`irreducible_closed_union`, `closed_union_of_isPrime`, `I_union`, `Z_I_eq`, `I_mono`,
`mem_I_of`, `isHomog_I`, `eval_smul_of_isHomogeneous`, `vanishOnLine_mul`, the Zariski topology
instance and `isClosed_Z` are the projective-space infrastructure of the accepted checkpoint
proof of Exercise I.2.4 (same point-set model of `P^n`, same definitions of `Z`, `I` and of
the Zariski topology), copied here because answers are not imported across files.  Everything
else is specific to Exercise I.2.14.
-/
import Mathlib

set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_2_14

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. Projective space, zero loci, vanishing ideals (adapted from Ex. I.2.4) -/

abbrev Coord (n : ℕ) : Type := Fin (n + 1)

abbrev Poly (k : Type*) [CommSemiring k] (n : ℕ) := MvPolynomial (Coord n) k

abbrev Proj (k : Type*) [Field k] (n : ℕ) := Projectivization k (Coord n → k)

variable {k : Type*} [Field k] {n : ℕ}

/-! ### The irrelevant ideal `S₊ = (x₀, …, xₙ)` -/

/-- `S₊`, the ideal of `S` generated by the variables. -/
def SPlus (k : Type*) [CommSemiring k] (n : ℕ) : Ideal (Poly k n) :=
  Ideal.span (Set.range (MvPolynomial.X : Coord n → Poly k n))

/-! ### Vanishing on a projective point and zero loci -/

/-- A polynomial vanishes on the *line* (the affine cone) over the projective point `p`. -/
def VanishOnLine (p : Proj k n) (f : Poly k n) : Prop :=
  ∀ v ∈ p.submodule, MvPolynomial.eval v f = 0

/-- The ideal of polynomials vanishing on the line over `p`. -/
def vanishAt (p : Proj k n) : Ideal (Poly k n) where
  carrier := {f | VanishOnLine p f}
  zero_mem' := by
    intro v _; simp
  add_mem' := by
    intro f g hf hg v hv
    simp only [MvPolynomial.eval_add, hf v hv, hg v hv, add_zero]
  smul_mem' := by
    intro c f hf v hv
    simp only [smul_eq_mul, MvPolynomial.eval_mul, hf v hv, mul_zero]

/-- The zero locus of a set of polynomials: Hartshorne's `Z(T)`. -/
def Z (T : Set (Poly k n)) : Set (Proj k n) :=
  {p | ∀ f ∈ T, VanishOnLine p f}

/-- The ideal generated by the homogeneous polynomials vanishing on `Y`:
Hartshorne's `I(Y)`. -/
def I (Y : Set (Proj k n)) : Ideal (Poly k n) :=
  Ideal.span {f | (∃ d, f.IsHomogeneous d) ∧ ∀ p ∈ Y, VanishOnLine p f}

/-- A polynomial is homogeneous (of some degree). -/
def IsHomogPoly (f : Poly k n) : Prop := ∃ d, f.IsHomogeneous d

/-- A set of polynomials consists of homogeneous polynomials. -/
def IsHomogSet (T : Set (Poly k n)) : Prop := ∀ f ∈ T, IsHomogPoly f

lemma isHomogPoly_zero : IsHomogPoly (0 : Poly k n) :=
  ⟨0, isHomogeneous_zero (σ := Coord n) (R := k) 0⟩

lemma isHomogPoly_one : IsHomogPoly (1 : Poly k n) :=
  ⟨0, isHomogeneous_one (σ := Coord n) (R := k)⟩

lemma isHomogPoly_mul {f g : Poly k n} (hf : IsHomogPoly f) (hg : IsHomogPoly g) :
    IsHomogPoly (f * g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, ha.mul hb⟩

/-! ### Scaling: homogeneous polynomials are homogeneous functions on `k^{n+1}` -/

lemma finsupp_prod_pow_const (m : Coord n →₀ ℕ) (c : k) :
    (m.prod fun _ e => c ^ e) = c ^ m.degree := by
  rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]

lemma eval_smul_monomial (m : Coord n →₀ ℕ) (a c : k) (x : Coord n → k) :
    MvPolynomial.eval (fun i => c * x i) (MvPolynomial.monomial m a)
      = c ^ m.degree * MvPolynomial.eval x (MvPolynomial.monomial m a) := by
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  have h1 : (m.prod fun i e => (c * x i) ^ e)
      = (m.prod fun _ e => c ^ e) * (m.prod fun i e => x i ^ e) := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [h1, finsupp_prod_pow_const]
  ring

/-- The fundamental scaling rule: a homogeneous polynomial of degree `d` is
homogeneous of degree `d` as a function on `k^{n+1}`. -/
theorem eval_smul_of_isHomogeneous {f : Poly k n} {d : ℕ} (hf : f.IsHomogeneous d) (c : k)
    (x : Coord n → k) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ d * MvPolynomial.eval x f := by
  rw [MvPolynomial.as_sum f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval_smul_monomial]
  have hd : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.mp hm)
  rw [hd]

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem eval_zero_of_isHomogeneous {f : Poly k n} {d : ℕ} (hf : f.IsHomogeneous d) (hd : 0 < d) :
    MvPolynomial.eval (0 : Coord n → k) f = 0 := by
  have h := eval_smul_of_isHomogeneous hf (0 : k) (0 : Coord n → k)
  simp only [Pi.zero_apply, mul_zero, zero_pow hd.ne', zero_mul] at h
  exact h

/-! ### Vanishing on a line, via a representative -/

lemma vanishOnLine_iff_eval_rep {f : Poly k n} {d : ℕ} (hf : f.IsHomogeneous d) (p : Proj k n) :
    VanishOnLine p f ↔ MvPolynomial.eval p.rep f = 0 := by
  constructor
  · intro h
    exact h p.rep (by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self p.rep)
  · intro h v hv
    rw [Projectivization.submodule_eq, Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    have hc : (c • p.rep : Coord n → k) = fun i => c * p.rep i := rfl
    rw [hc, eval_smul_of_isHomogeneous hf c p.rep, h, mul_zero]

/-- Vanishing on a line is a property of a homogeneous polynomial that is decided
by the zero set of that polynomial. -/
theorem vanishOnLine_mul {f g : Poly k n} (hf : IsHomogPoly f) (hg : IsHomogPoly g)
    (p : Proj k n) :
    VanishOnLine p (f * g) ↔ VanishOnLine p f ∨ VanishOnLine p g := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  rw [vanishOnLine_iff_eval_rep (ha.mul hb), vanishOnLine_iff_eval_rep ha,
    vanishOnLine_iff_eval_rep hb, MvPolynomial.eval_mul, mul_eq_zero]

lemma vanishOnLine_one (p : Proj k n) : ¬ VanishOnLine p (1 : Poly k n) := by
  intro h
  have := h p.rep (by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self p.rep)
  exact one_ne_zero (by simpa only [map_one] using this)

lemma vanishOnLine_of_mul_left {f g : Poly k n} {p : Proj k n} (h : VanishOnLine p f) :
    VanishOnLine p (f * g) := by
  intro v hv
  rw [MvPolynomial.eval_mul, h v hv, zero_mul]

/-! ### Basic properties of `Z` and `I` -/

theorem mem_Z_iff (T : Set (Poly k n)) (p : Proj k n) : p ∈ Z T ↔ T ⊆ (vanishAt p : Set (Poly k n)) :=
  Iff.rfl

theorem z_empty : Z (∅ : Set (Poly k n)) = Set.univ := by
  ext p
  exact ⟨fun _ => Set.mem_univ p, fun _ f hf => absurd hf (Set.notMem_empty f)⟩

theorem z_one : Z ({1} : Set (Poly k n)) = ∅ := by
  ext p
  simp only [Z, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact vanishOnLine_one p (h 1 rfl)

theorem z_union {T₁ T₂ : Set (Poly k n)} (h₁ : IsHomogSet T₁) (h₂ : IsHomogSet T₂) :
    Z T₁ ∪ Z T₂ = Z {f | ∃ a ∈ T₁, ∃ b ∈ T₂, f = a * b} := by
  ext p
  simp only [Z, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h) f ⟨a, ha, b, hb, rfl⟩
    · exact vanishOnLine_of_mul_left (h a ha)
    · rw [mul_comm]; exact vanishOnLine_of_mul_left (h b hb)
  · intro h
    by_cases hp : T₁ ⊆ (vanishAt p : Set (Poly k n))
    · exact Or.inl hp
    · refine Or.inr fun g hg => ?_
      obtain ⟨f, hfT, hfp⟩ := Set.not_subset.mp hp
      have hfg : VanishOnLine p (f * g) := h (f * g) ⟨f, hfT, g, hg, rfl⟩
      rw [vanishOnLine_mul (h₁ f hfT) (h₂ g hg)] at hfg
      exact hfg.resolve_left hfp

theorem z_ideal_sUnion {ι : Type*} (T : ι → Set (Poly k n)) :
    (⋂ i, Z (T i)) = Z {f | ∃ i, f ∈ T i} := by
  ext p
  simp only [Z, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h f ⟨i, hf⟩; exact h i f hf
  · intro h i f hf; exact h f ⟨i, hf⟩

/-- The Zariski topology on `ℙⁿ`: closed sets are the `Z(T)` for sets `T` of
homogeneous polynomials. -/
instance : TopologicalSpace (Proj k n) where
  IsOpen s := ∃ T : Set (Poly k n), IsHomogSet T ∧ s = (Z T)ᶜ
  isOpen_univ := ⟨{1}, fun f hf => hf ▸ isHomogPoly_one, by rw [z_one]; simp⟩
  isOpen_inter := by
    rintro s t ⟨T₁, h₁, rfl⟩ ⟨T₂, h₂, rfl⟩
    refine ⟨_, fun f hf => ?_, by rw [← Set.compl_union, z_union h₁ h₂]⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    exact isHomogPoly_mul (h₁ a ha) (h₂ b hb)
  isOpen_sUnion := by
    classical
    intro S hS
    refine ⟨{f | ∃ T : Set (Poly k n), IsHomogSet T ∧ (Z T)ᶜ ∈ S ∧ f ∈ T}, ?_, ?_⟩
    · rintro f ⟨T, hT, -, hfT⟩
      exact hT f hfT
    · ext p
      constructor
      · intro hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_sUnion.mp hp
        obtain ⟨T, hT, rfl⟩ := hS t ht
        have hpT : p ∉ Z T := hpt
        rw [Z] at hpT
        simp only [Set.mem_ofPred_eq, not_forall] at hpT
        obtain ⟨f, hfT, hfp⟩ := hpT
        simp only [Set.mem_compl_iff, Z, Set.mem_ofPred_eq, not_forall]
        exact ⟨f, ⟨T, hT, ht, hfT⟩, hfp⟩
      · intro hp
        simp only [Set.mem_compl_iff, Z, Set.mem_ofPred_eq, not_forall] at hp
        obtain ⟨f, ⟨T, hT, hTc, hfT⟩, hfp⟩ := hp
        exact Set.mem_sUnion.mpr ⟨(Z T)ᶜ, hTc, by
          simp only [Set.mem_compl_iff, Z, Set.mem_ofPred_eq, not_forall]
          exact ⟨f, hfT, hfp⟩⟩

theorem isClosed_iff (Y : Set (Proj k n)) :
    IsClosed Y ↔ ∃ T : Set (Poly k n), IsHomogSet T ∧ Y = Z T := by
  constructor
  · intro h
    obtain ⟨T, hT, hTeq⟩ := isOpen_compl_iff.mpr h
    exact ⟨T, hT, by rw [← compl_compl Y, hTeq, compl_compl]⟩
  · rintro ⟨T, hT, hY⟩
    exact isOpen_compl_iff.mp ⟨T, hT, by rw [hY]⟩

/-- Zero loci of homogeneous sets are Zariski closed. -/
theorem isClosed_Z {T : Set (Poly k n)} (hT : IsHomogSet T) : IsClosed (Z T) :=
  (isClosed_iff _).mpr ⟨T, hT, rfl⟩

/-- Every `Z(T)` is the zero locus of the ideal generated by `T`. -/
theorem z_span (S : Set (Poly k n)) : Z (Ideal.span S : Set (Poly k n)) = Z S := by
  ext p
  simp only [Z, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro h f hf; exact h f (Ideal.subset_span hf)
  · intro h f hf
    have hle : Ideal.span S ≤ vanishAt p := Ideal.span_le.mpr (fun s hs => h s hs)
    exact hle hf

/-- A homogeneous ideal is generated by its homogeneous elements. -/
theorem homogIdeal_eq_span (J : Ideal (Poly k n))
    (hJ : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Coord n) k) J) :
    J = Ideal.span {f | f ∈ J ∧ IsHomogPoly f} := by
  apply le_antisymm
  · intro f hf
    have hsum : f = ∑ d ∈ Finset.range (f.totalDegree + 1),
        MvPolynomial.homogeneousComponent d f :=
      (MvPolynomial.sum_homogeneousComponent (φ := f)).symm
    rw [hsum]
    refine Ideal.sum_mem _ fun d _ => Ideal.subset_span ?_
    exact ⟨MvPolynomial.homogeneousComponent_mem_of_mem hJ hf d, d,
      MvPolynomial.homogeneousComponent_isHomogeneous d f⟩
  · rw [Ideal.span_le]
    rintro f ⟨hfJ, -⟩
    exact hfJ

theorem isClosed_Z_ideal (J : Ideal (Poly k n))
    (hJ : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Coord n) k) J) :
    IsClosed (Z (J : Set (Poly k n))) := by
  rw [show (J : Set (Poly k n)) = (Ideal.span {f | f ∈ J ∧ IsHomogPoly f} : Set (Poly k n)) from by
    rw [← homogIdeal_eq_span J hJ]]
  rw [z_span]
  exact isClosed_Z fun f hf => hf.2

/-! ### The irrelevant ideal `S₊` -/

lemma X_mem_SPlus (i : Coord n) : (MvPolynomial.X i : Poly k n) ∈ SPlus k n :=
  Ideal.subset_span (Set.mem_range_self i)

lemma self_sub_C_constantCoeff_mem_SPlus (f : Poly k n) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ SPlus k n := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have h : MvPolynomial.constantCoeff (p + q) =
          MvPolynomial.constantCoeff p + MvPolynomial.constantCoeff q := map_add _ _ _
      rw [h, map_add]
      have heq : p + q - (MvPolynomial.C (MvPolynomial.constantCoeff p) +
            MvPolynomial.C (MvPolynomial.constantCoeff q)) =
          (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
            (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by ring
      rw [heq]
      exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
      have h : MvPolynomial.constantCoeff (p * MvPolynomial.X i) = 0 := by
        rw [map_mul, MvPolynomial.constantCoeff_X, mul_zero]
      rw [h, map_zero, sub_zero]
      have hsplit : p * MvPolynomial.X i =
          (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) * MvPolynomial.X i +
            MvPolynomial.C (MvPolynomial.constantCoeff p) * MvPolynomial.X i := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mul_mem_right (MvPolynomial.X i) (SPlus k n) hp)
        (Ideal.mul_mem_left (SPlus k n) (MvPolynomial.C (MvPolynomial.constantCoeff p)) (X_mem_SPlus i))

lemma isMaximal_SPlus : (SPlus k n).IsMaximal := by
  have hker : SPlus k n = RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Coord n => (0 : k))) := by
    apply le_antisymm
    · rw [SPlus, Ideal.span_le]
      rintro f ⟨i, rfl⟩
      simp
    · intro f hf
      rw [RingHom.mem_ker] at hf
      have hcc : MvPolynomial.constantCoeff f = 0 := by simpa using hf
      have h := self_sub_C_constantCoeff_mem_SPlus (k := k) (n := n) f
      rwa [hcc, map_zero, sub_zero] at h
  rw [hker]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩

/-- The only homogeneous radical ideal strictly containing `S₊` is `S` itself. -/
theorem eq_top_of_SPlus_lt {J : Ideal (Poly k n)} (h : SPlus k n ≤ J) (hne : J ≠ SPlus k n) :
    J = ⊤ := by
  by_contra hJ
  exact hne ((isMaximal_SPlus (k := k) (n := n)).eq_of_le hJ h).symm

/-! ### `I(Y)` is a homogeneous ideal, generated by homogeneous vanishing polynomials -/

theorem I_le_vanishAt {Y : Set (Proj k n)} {p : Proj k n} (hp : p ∈ Y) :
    I Y ≤ vanishAt p := by
  rw [I, Ideal.span_le]
  rintro f ⟨-, hf⟩
  exact hf p hp

theorem mem_I_of {Y : Set (Proj k n)} {f : Poly k n} (hf : IsHomogPoly f)
    (h : ∀ p ∈ Y, VanishOnLine p f) : f ∈ I Y :=
  Ideal.subset_span ⟨hf, h⟩

theorem isHomog_I (Y : Set (Proj k n)) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Coord n) k) (I Y) := by
  rw [I]
  apply Ideal.homogeneous_span
  rintro f ⟨⟨d, hd⟩, -⟩
  exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule d f).mpr hd⟩

theorem I_mono {Y₁ Y₂ : Set (Proj k n)} (h : Y₁ ⊆ Y₂) : I Y₂ ≤ I Y₁ := by
  rw [I, I, Ideal.span_le]
  rintro f ⟨hf, hvan⟩
  exact Ideal.subset_span ⟨hf, fun p hp => hvan p (h hp)⟩

/-! ### Part (a): the inclusion-reversing 1-1 correspondence -/

/-- `Z(I(Y)) = Y` for a closed set `Y`. -/
theorem Z_I_eq {Y : Set (Proj k n)} (hY : IsClosed Y) : Z (I Y : Set (Poly k n)) = Y := by
  obtain ⟨T, hT, rfl⟩ := (isClosed_iff Y).mp hY
  apply le_antisymm
  · intro p hp
    exact fun f hf => hp f (mem_I_of (hT f hf) fun q hq => hq f hf)
  · intro p hp
    exact I_le_vanishAt hp

/-- For a closed set, irreducibility is the closed-union condition. -/
theorem irreducible_closed_union {Y Z₁ Z₂ : Set (Proj k n)} (hY : IsIrreducible Y)
    (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂) (hsub : Y ⊆ Z₁ ∪ Z₂) : Y ⊆ Z₁ ∨ Y ⊆ Z₂ := by
  obtain ⟨T₁, hT₁, rfl⟩ := (isClosed_iff Z₁).mp h₁
  obtain ⟨T₂, hT₂, rfl⟩ := (isClosed_iff Z₂).mp h₂
  by_contra h
  rw [not_or] at h
  obtain ⟨y₁, hy₁Y, hy₁Z⟩ := Set.not_subset.mp h.1
  obtain ⟨y₂, hy₂Y, hy₂Z⟩ := Set.not_subset.mp h.2
  obtain ⟨y, hyY, hy1, hy2⟩ := hY.isPreirreducible (Z T₁)ᶜ (Z T₂)ᶜ
    ⟨T₁, hT₁, rfl⟩ ⟨T₂, hT₂, rfl⟩ ⟨y₁, hy₁Y, hy₁Z⟩ ⟨y₂, hy₂Y, hy₂Z⟩
  rcases hsub hyY with h' | h'
  · exact hy1 h'
  · exact hy2 h'

/-! ### Part (b): irreducible algebraic sets and prime ideals -/

theorem I_union (Y₁ Y₂ : Set (Proj k n)) : I (Y₁ ∪ Y₂) = I Y₁ ⊓ I Y₂ := by
  apply le_antisymm
  · exact le_inf (I_mono Set.subset_union_left) (I_mono Set.subset_union_right)
  · intro f hf
    obtain ⟨hf₁, hf₂⟩ := hf
    have hsum : f = ∑ d ∈ Finset.range (f.totalDegree + 1),
        MvPolynomial.homogeneousComponent d f :=
      (MvPolynomial.sum_homogeneousComponent (φ := f)).symm
    rw [hsum]
    refine Ideal.sum_mem _ fun d _ => mem_I_of ⟨d,
      MvPolynomial.homogeneousComponent_isHomogeneous d f⟩ fun p hp => ?_
    rcases hp with hp | hp
    · exact I_le_vanishAt hp ((MvPolynomial.mem_iff_homogeneousComponent_mem (isHomog_I Y₁) f).mp hf₁ d)
    · exact I_le_vanishAt hp ((MvPolynomial.mem_iff_homogeneousComponent_mem (isHomog_I Y₂) f).mp hf₂ d)

/-- A polynomial vanishing on a closed set but not at a point outside it. -/
theorem exists_mem_I_of_not_mem {W : Set (Proj k n)} (hW : IsClosed W) {p : Proj k n}
    (hpW : p ∉ W) : ∃ f : Poly k n, f ∈ I W ∧ ¬ VanishOnLine p f := by
  have hpW' : p ∉ Z (I W : Set (Poly k n)) := by rwa [Z_I_eq hW]
  simp only [Z, Set.mem_ofPred_eq, not_forall] at hpW'
  obtain ⟨f, hf, hfp⟩ := hpW'
  exact ⟨f, hf, hfp⟩

/-- Primality of `I Y` gives the closed-union criterion. -/
theorem closed_union_of_isPrime {Y Z₁ Z₂ : Set (Proj k n)} (_hY : IsClosed Y)
    (hprime : (I Y).IsPrime) (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂) (hsub : Y ⊆ Z₁ ∪ Z₂) :
    Y ⊆ Z₁ ∨ Y ⊆ Z₂ := by
  obtain ⟨T₁, hT₁, rfl⟩ := (isClosed_iff Z₁).mp h₁
  obtain ⟨T₂, hT₂, rfl⟩ := (isClosed_iff Z₂).mp h₂
  by_contra h
  rw [not_or] at h
  obtain ⟨p₁, hp₁Y, hp₁Z⟩ := Set.not_subset.mp h.1
  obtain ⟨p₂, hp₂Y, hp₂Z⟩ := Set.not_subset.mp h.2
  obtain ⟨f, hfW, hfp⟩ := exists_mem_I_of_not_mem (W := Z T₁) (isClosed_Z hT₁) hp₁Z
  obtain ⟨g, hgW, hgp⟩ := exists_mem_I_of_not_mem (W := Z T₂) (isClosed_Z hT₂) hp₂Z
  have hfY : f ∉ I Y := fun hmem => hfp (I_le_vanishAt hp₁Y hmem)
  have hgY : g ∉ I Y := fun hmem => hgp (I_le_vanishAt hp₂Y hmem)
  have hfg₁ : f * g ∈ I (Z T₁ ∪ Z T₂) := by
    rw [I_union]
    exact ⟨Ideal.mul_mem_right g (I (Z T₁)) hfW, Ideal.mul_mem_left (I (Z T₂)) f hgW⟩
  exact (hprime.mem_or_mem (I_mono hsub hfg₁)).elim hfY hgY

/-- (I.2.4 b) An algebraic set `Y ⊆ ℙⁿ` is irreducible if and only if `I(Y)` is prime. -/
theorem part_b {Y : Set (Proj k n)} (hY : IsClosed Y) :
    IsIrreducible Y ↔ (I Y).IsPrime := by
  constructor
  · intro hirr
    rw [(isHomog_I Y).isPrime_iff]
    refine ⟨?_, ?_⟩
    · intro htop
      obtain ⟨p, hp⟩ := hirr.nonempty
      have h1 : (1 : Poly k n) ∈ I Y := htop ▸ Submodule.mem_top
      exact vanishOnLine_one p (I_le_vanishAt hp h1)
    · rintro f g ⟨df, hdf⟩ ⟨dg, hdg⟩ hfg
      have hsub : Y ⊆ Z ({f} : Set (Poly k n)) ∪ Z ({g} : Set (Poly k n)) := by
        intro p hp
        have h1 : VanishOnLine p (f * g) := I_le_vanishAt hp hfg
        rcases (vanishOnLine_mul ⟨df, hdf⟩ ⟨dg, hdg⟩ p).mp h1 with h | h
        · exact Or.inl fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ h
        · exact Or.inr fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ h
      rcases irreducible_closed_union hirr (isClosed_Z (T := {f}) fun q hq => by
          rw [Set.mem_singleton_iff] at hq; exact hq ▸ ⟨df, hdf⟩)
        (isClosed_Z (T := {g}) fun q hq => by
          rw [Set.mem_singleton_iff] at hq; exact hq ▸ ⟨dg, hdg⟩) hsub with h | h
      · exact Or.inl (mem_I_of ⟨df, hdf⟩ fun p hp => h hp f rfl)
      · exact Or.inr (mem_I_of ⟨dg, hdg⟩ fun p hp => h hp g rfl)
  · intro hprime
    have hYne : Y.Nonempty := by
      rcases Set.eq_empty_or_nonempty Y with hempty | h
      · exfalso
        have h1 : (1 : Poly k n) ∈ I Y := by
          rw [hempty]
          exact mem_I_of isHomogPoly_one fun p hp => absurd hp (Set.notMem_empty p)
        exact hprime.ne_top ((Ideal.eq_top_iff_one (I := I Y)).mpr h1)
      · exact h
    refine ⟨hYne, ?_⟩
    intro u v hu hv hune hvne
    obtain ⟨T₁, hT₁, rfl⟩ := hu
    obtain ⟨T₂, hT₂, rfl⟩ := hv
    by_contra hemp
    have hsub : Y ⊆ Z T₁ ∪ Z T₂ := by
      intro p hp
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      exact hemp ⟨p, hp, hcon.1, hcon.2⟩
    rcases closed_union_of_isPrime hY hprime (isClosed_Z hT₁) (isClosed_Z hT₂) hsub with h | h
    · obtain ⟨p, hp⟩ := hune
      exact hp.2 (h hp.1)
    · obtain ⟨p, hp⟩ := hvne
      exact hp.2 (h hp.1)
/-! ## 2. Homogeneous coordinates `z_ij` on `P^N`, `N = rs + r + s` -/

/-- The lexicographic identification `(i, j) ↦ i(s+1) + j` of the pairs of indices with the
coordinates of `P^N`, where `N = rs + r + s` (Hartshorne's coordinates `{z_ij}`). -/
def zIdx (r s : ℕ) : Coord r × Coord s ≃ Coord (r * s + r + s) :=
  (finProdFinEquiv (m := r + 1) (n := s + 1)).trans (finCongr (by ring))

theorem zIdx_apply (r s : ℕ) (i : Coord r) (j : Coord s) :
    ((zIdx r s (i, j) : Coord (r * s + r + s)) : ℕ) = i * (s + 1) + j := by
  show (↑(finCongr (by ring) (finProdFinEquiv (m := r + 1) (n := s + 1) (i, j))) : ℕ) = _
  rw [finCongr_apply_coe]
  rw [show ((finProdFinEquiv (m := r + 1) (n := s + 1) (i, j)) : ℕ) = j + (s + 1) * i from rfl]
  ring

section Segre

variable {k : Type*} [Field k] {r s : ℕ}

/-- The homogeneous coordinate `z_ij` of `P^N`. -/
def zvar (i : Coord r) (j : Coord s) : Poly k (r * s + r + s) :=
  MvPolynomial.X (zIdx r s (i, j))

/-- The `2 × 2` minor `z_ij z_kl - z_il z_kj` of the matrix of coordinates of `P^N`. -/
def minor (i₁ i₂ : Coord r) (j₁ j₂ : Coord s) : Poly k (r * s + r + s) :=
  zvar i₁ j₁ * zvar i₂ j₂ - zvar i₁ j₂ * zvar i₂ j₁

/-- The set of all `2 × 2` minors of the matrix `(z_ij)`. -/
def minorsSet (k : Type*) [Field k] (r s : ℕ) : Set (Poly k (r * s + r + s)) :=
  Set.range fun p : (Coord r × Coord s) × (Coord r × Coord s) =>
    minor (k := k) p.1.1 p.2.1 p.1.2 p.2.2

theorem minor_isHomogeneous (i₁ i₂ : Coord r) (j₁ j₂ : Coord s) :
    (minor (k := k) i₁ i₂ j₁ j₂).IsHomogeneous 2 := by
  have h₁ : ((zvar (k := k) i₁ j₁) * (zvar i₂ j₂)).IsHomogeneous (1 + 1) :=
    (isHomogeneous_X k (zIdx r s (i₁, j₁))).mul (isHomogeneous_X k (zIdx r s (i₂, j₂)))
  have h₂ : ((zvar (k := k) i₁ j₂) * (zvar i₂ j₁)).IsHomogeneous (1 + 1) :=
    (isHomogeneous_X k (zIdx r s (i₁, j₂))).mul (isHomogeneous_X k (zIdx r s (i₂, j₁)))
  exact h₁.sub h₂

theorem minorsSet_isHomogSet : IsHomogSet (minorsSet k r s) := by
  rintro f ⟨p, rfl⟩
  obtain ⟨⟨i₁, j₁⟩, ⟨i₂, j₂⟩⟩ := p
  exact ⟨2, minor_isHomogeneous i₁ i₂ j₁ j₂⟩

/-! ## 3. The substitution `z_ij ↦ x_i y_j` and Hartshorne's ideal `a` -/

/-- The image of the variables under `z_ij ↦ x_i y_j`. -/
def segreGen (k : Type*) [Field k] (r s : ℕ) :
    Coord (r * s + r + s) → MvPolynomial (Coord r ⊕ Coord s) k :=
  fun t => MvPolynomial.X (Sum.inl ((zIdx r s).symm t).1) *
    MvPolynomial.X (Sum.inr ((zIdx r s).symm t).2)

/-- The homomorphism `k[{z_ij}] → k[x_0,…,x_r,y_0,…,y_s]` sending `z_ij` to `x_i y_j`. -/
def segreRingHom (k : Type*) [Field k] (r s : ℕ) :
    Poly k (r * s + r + s) →+* MvPolynomial (Coord r ⊕ Coord s) k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (segreGen k r s)

/-- Hartshorne's ideal `a`: the kernel of `z_ij ↦ x_i y_j`. -/
def kerSegre (k : Type*) [Field k] (r s : ℕ) : Ideal (Poly k (r * s + r + s)) :=
  RingHom.ker (segreRingHom k r s)

theorem segreRingHom_X (t : Coord (r * s + r + s)) :
    segreRingHom k r s (MvPolynomial.X t) = segreGen k r s t :=
  MvPolynomial.eval₂Hom_X' _ _ t

/-- The Segre vector `(…, a_i b_j, …)`. -/
def segreVec (k : Type*) [Field k] (r s : ℕ) (a : Coord r → k) (b : Coord s → k) :
    Coord (r * s + r + s) → k :=
  fun t => a ((zIdx r s).symm t).1 * b ((zIdx r s).symm t).2

theorem segreVec_zIdx (a : Coord r → k) (b : Coord s → k) (i : Coord r) (j : Coord s) :
    segreVec k r s a b (zIdx r s (i, j)) = a i * b j := by
  simp [segreVec]

/-- The fundamental compatibility: evaluating `f` at the Segre point of `(a, b)` is evaluating
`z_ij ↦ x_i y_j` and then substituting `x_i = a_i`, `y_j = b_j`. -/
theorem eval_segreRingHom (f : Poly k (r * s + r + s)) (a : Coord r → k)
    (b : Coord s → k) :
    MvPolynomial.eval (segreVec k r s a b) f
      = MvPolynomial.eval (Sum.elim a b) (segreRingHom k r s f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [segreRingHom]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f t hf =>
      have hx : MvPolynomial.eval (segreVec k r s a b) (MvPolynomial.X t)
          = MvPolynomial.eval (Sum.elim a b) (segreRingHom k r s (MvPolynomial.X t)) := by
        simp only [segreRingHom_X, segreGen, segreVec, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
      simp only [map_mul, hf, hx]

theorem kerSegre_mem_iff {f : Poly k (r * s + r + s)} :
    f ∈ kerSegre k r s ↔ segreRingHom k r s f = 0 :=
  RingHom.mem_ker

theorem minor_mem_kerSegre (i₁ i₂ : Coord r) (j₁ j₂ : Coord s) :
    minor (k := k) i₁ i₂ j₁ j₂ ∈ kerSegre k r s := by
  rw [kerSegre_mem_iff]
  simp only [minor, map_sub, map_mul, segreRingHom_X, zvar, segreGen]
  simp
  ring

theorem minorsSet_subset_kerSegre : minorsSet k r s ⊆ (kerSegre k r s : Set _) := by
  rintro f ⟨p, rfl⟩
  obtain ⟨⟨i₁, j₁⟩, ⟨i₂, j₂⟩⟩ := p
  exact minor_mem_kerSegre i₁ i₂ j₁ j₂

end Segre

/-! ## 4. The Segre map `ψ : P^r × P^s → P^N` and its injectivity -/

section SegreMap

variable {k : Type*} [Field k] {r s : ℕ}

theorem segreVec_smul (c : k) (a : Coord r → k) (b : Coord s → k) :
    segreVec k r s (c • a) b = c • segreVec k r s a b := by
  funext t
  simp only [segreVec, Pi.smul_apply, smul_eq_mul]
  ring

theorem segreVec_ne_zero {a : Coord r → k} {b : Coord s → k} (ha : a ≠ 0) (hb : b ≠ 0) :
    segreVec k r s a b ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha (funext h)
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hb (funext h)
  intro h
  have h2 : a i * b j = 0 := by
    have := congrFun h (zIdx r s (i, j))
    simpa [segreVec] using this
  exact mul_ne_zero hi hj h2

/-- **The Segre map** `ψ : P^r × P^s → P^N`, `(a_0 : … : a_r) × (b_0 : … : b_s) ↦
(… : a_i b_j : …)`. -/
def segre (k : Type*) [Field k] (r s : ℕ) :
    Proj k r × Proj k s → Proj k (r * s + r + s) :=
  fun q => Projectivization.mk k (segreVec k r s q.1.rep q.2.rep)
    (segreVec_ne_zero (Projectivization.rep_nonzero q.1) (Projectivization.rep_nonzero q.2))

/-- The coordinate formula for `ψ` on representatives. -/
theorem segre_mk {a : Coord r → k} {b : Coord s → k} (ha : a ≠ 0) (hb : b ≠ 0) :
    segre k r s (Projectivization.mk k a ha, Projectivization.mk k b hb)
      = Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb) := by
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff' k a _ ha
    (Projectivization.rep_nonzero (Projectivization.mk k a ha))).1
    (Projectivization.mk_rep (Projectivization.mk k a ha)).symm
  obtain ⟨v, hv⟩ := (Projectivization.mk_eq_mk_iff' k b _ hb
    (Projectivization.rep_nonzero (Projectivization.mk k b hb))).1
    (Projectivization.mk_rep (Projectivization.mk k b hb)).symm
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hu
    exact ha hu.symm
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hv
    exact hb hv.symm
  have hvec : (u * v) • segreVec k r s (Projectivization.mk k a ha).rep
        (Projectivization.mk k b hb).rep = segreVec k r s a b := by
    funext t
    have h1 : a ((zIdx r s).symm t).1 =
        u * (Projectivization.mk k a ha).rep ((zIdx r s).symm t).1 := by
      rw [← congrFun hu ((zIdx r s).symm t).1, Pi.smul_apply, smul_eq_mul]
    have h2 : b ((zIdx r s).symm t).2 =
        v * (Projectivization.mk k b hb).rep ((zIdx r s).symm t).2 := by
      rw [← congrFun hv ((zIdx r s).symm t).2, Pi.smul_apply, smul_eq_mul]
    simp only [segreVec, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2]
    ring
  exact (Projectivization.mk_eq_mk_iff' k _ _ _ _).2 ⟨(u * v)⁻¹, by
    rw [← hvec, smul_smul, inv_mul_cancel₀ (mul_ne_zero hu0 hv0), one_smul]⟩

/-- **Well-definedness of `ψ`**: the coordinate formula does not depend on the chosen
representatives of the two projective points. -/
theorem segre_welldef {a a' : Coord r → k} {b b' : Coord s → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h1 : Projectivization.mk k a ha = Projectivization.mk k a' ha')
    (h2 : Projectivization.mk k b hb = Projectivization.mk k b' hb') :
    Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)
      = Projectivization.mk k (segreVec k r s a' b') (segreVec_ne_zero ha' hb') := by
  rw [← segre_mk ha hb, ← segre_mk ha' hb', h1, h2]

/-- The vector-level injectivity behind the injectivity of `ψ`. -/
theorem segreVec_injective {a a' : Coord r → k} {b b' : Coord s → k}
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h : Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)
      = Projectivization.mk k (segreVec k r s a' b') (segreVec_ne_zero ha' hb')) :
    (Projectivization.mk k a ha, Projectivization.mk k b hb)
      = (Projectivization.mk k a' ha', Projectivization.mk k b' hb') := by
  obtain ⟨c, hcv⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).1 h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcv
    exact segreVec_ne_zero ha hb hcv.symm
  have key : ∀ (i : Coord r) (j : Coord s), c * (a' i * b' j) = a i * b j := by
    intro i j
    have h1 := congrFun hcv (zIdx r s (i, j))
    rw [Pi.smul_apply, smul_eq_mul] at h1
    rwa [segreVec_zIdx, segreVec_zIdx] at h1
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hh
    simp only [not_exists, not_not] at hh
    exact ha (funext hh)
  obtain ⟨j₀, hj₀⟩ : ∃ j, b' j ≠ 0 := by
    by_contra hh
    simp only [not_exists, not_not] at hh
    exact hb' (funext hh)
  have hbj₀ : b j₀ ≠ 0 := by
    intro h0
    have hzero : ∀ i, a' i = 0 := by
      intro i
      have h1 : c * (a' i * b' j₀) = 0 := by rw [key i j₀, h0, mul_zero]
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hc
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact h3
        · exact absurd h3 hj₀
    exact ha' (funext hzero)
  have hsmul_a : (b j₀ / (c * b' j₀)) • a = a' := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : c * (a' i * b' j₀) = a i * b j₀ := key i j₀
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hc hj₀)]
    have h2 : a' i * (c * b' j₀) = a i * b j₀ := by rw [← h1]; ring
    rw [h2]; ring
  have hlamne : b j₀ / (c * b' j₀) ≠ 0 :=
    div_ne_zero hbj₀ (mul_ne_zero hc hj₀)
  have hai₀ : a' i₀ ≠ 0 := by
    have h1 : a' i₀ = (b j₀ / (c * b' j₀)) * a i₀ := by
      rw [← hsmul_a]
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]
    exact mul_ne_zero hlamne hi₀
  have hsmul_b : (a i₀ / (c * a' i₀)) • b = b' := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : c * (a' i₀ * b' j) = a i₀ * b j := key i₀ j
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hc hai₀)]
    have h2 : b' j * (c * a' i₀) = a i₀ * b j := by rw [← h1]; ring
    rw [h2]
  have hmunne : a i₀ / (c * a' i₀) ≠ 0 :=
    div_ne_zero hi₀ (mul_ne_zero hc hai₀)
  refine Prod.ext ?_ ?_
  · refine (Projectivization.mk_eq_mk_iff' k a a' ha ha').2
      ⟨(b j₀ / (c * b' j₀))⁻¹, ?_⟩
    rw [← hsmul_a, smul_smul, inv_mul_cancel₀ hlamne, one_smul]
  · refine (Projectivization.mk_eq_mk_iff' k b b' hb hb').2
      ⟨(a i₀ / (c * a' i₀))⁻¹, ?_⟩
    rw [← hsmul_b, smul_smul, inv_mul_cancel₀ hmunne, one_smul]

/-- **Injectivity of the Segre map** (as stated in the exercise). -/
theorem segre_injective : Function.Injective (segre k r s) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
  have h1 : Projectivization.mk k p.rep p.rep_nonzero = p := Projectivization.mk_rep p
  have h2 : Projectivization.mk k q.rep q.rep_nonzero = q := Projectivization.mk_rep q
  have h3 : Projectivization.mk k p'.rep p'.rep_nonzero = p' := Projectivization.mk_rep p'
  have h4 : Projectivization.mk k q'.rep q'.rep_nonzero = q' := Projectivization.mk_rep q'
  rw [← h1, ← h2, ← h3, ← h4] at hpq ⊢
  simp only [segre_mk] at hpq
  exact segreVec_injective (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q)
    (Projectivization.rep_nonzero p') (Projectivization.rep_nonzero q') hpq

end SegreMap

/-! ## 5. `a = ker(z_ij ↦ x_i y_j)` is a homogeneous ideal -/

section Homog

variable {k : Type*} [Field k] [Infinite k] {r s : ℕ}

/-- Evaluation at `t • v` is the univariate polynomial in `t` whose `d`-th coefficient is the
evaluation at `v` of the `d`-th homogeneous component. -/
theorem eval_smul_eq_sum (f : Poly k (r * s + r + s)) (t : k)
    (v : Coord (r * s + r + s) → k) :
    MvPolynomial.eval (t • v) f =
      ∑ d ∈ Finset.range (f.totalDegree + 1),
        t ^ d * MvPolynomial.eval v (MvPolynomial.homogeneousComponent d f) := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := f)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (t • v : Coord (r * s + r + s) → k) = fun i => t * v i from rfl,
    eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous d f)]

/-- If a degree-`≤ D` polynomial function vanishes identically on the field, all its
coefficients vanish. -/
theorem coeff_eq_zero_of_forall_eval_sum_pow_eq_zero {D : ℕ} {c : ℕ → k}
    (h : ∀ t : k, ∑ d ∈ Finset.range (D + 1), c d * t ^ d = 0) :
    ∀ d, d ≤ D → c d = 0 := by
  intro d hd
  set P : Polynomial k := ∑ i ∈ Finset.range (D + 1), Polynomial.C (c i) * Polynomial.X ^ i
    with hPdef
  have hroot : ∀ t : k, P.eval t = 0 := by
    intro t
    have h1 : P.eval t = ∑ i ∈ Finset.range (D + 1), c i * t ^ i := by
      rw [hPdef]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
    rw [h1]
    exact h t
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P (Set.infinite_univ.mono ?_)
    intro t _
    exact hroot t
  have hcoeff := congrArg (fun q : Polynomial k => q.coeff d) hP0
  simp only [Polynomial.coeff_zero] at hcoeff
  rw [hPdef] at hcoeff
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
  rw [Finset.sum_eq_single d] at hcoeff
  · simpa using hcoeff
  · intro i _ hne
    simp [Ne.symm hne]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd)) hmem

/-- **The kernel of `z_ij ↦ x_i y_j` is a homogeneous ideal**: every homogeneous component of
an element of `a` again lies in `a`. -/
theorem homogeneousComponent_mem_ker {f : Poly k (r * s + r + s)}
    (hf : f ∈ kerSegre k r s) (d : ℕ) :
    MvPolynomial.homogeneousComponent d f ∈ kerSegre k r s := by
  rw [kerSegre_mem_iff] at hf ⊢
  by_cases hd : d ≤ f.totalDegree
  · apply MvPolynomial.funext
    intro x
    set a : Coord r → k := fun i => x (Sum.inl i) with hadef
    set b : Coord s → k := fun j => x (Sum.inr j) with hbdef
    have hx : x = Sum.elim a b := by
      funext z
      cases z <;> rfl
    rw [hx, ← eval_segreRingHom]
    have hkey : ∀ t : k,
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (MvPolynomial.eval (segreVec k r s a b)
            (MvPolynomial.homogeneousComponent i f)) * t ^ i = 0 := by
      intro t
      have h1 : ∑ i ∈ Finset.range (f.totalDegree + 1),
          (MvPolynomial.eval (segreVec k r s a b)
            (MvPolynomial.homogeneousComponent i f)) * t ^ i
          = MvPolynomial.eval (t • segreVec k r s a b) f := by
        rw [eval_smul_eq_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h1, ← segreVec_smul, eval_segreRingHom, hf, map_zero]
    exact coeff_eq_zero_of_forall_eval_sum_pow_eq_zero hkey d hd
  · have hzero : MvPolynomial.homogeneousComponent d f = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero d f (Nat.lt_of_not_le hd)
    rw [hzero, map_zero]

/-- Elements of `a` vanish at every point of the image of the Segre map. -/
theorem vanishOnLine_segre_of_mem_ker {f : Poly k (r * s + r + s)}
    (hf : f ∈ kerSegre k r s) {a : Coord r → k} {b : Coord s → k} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    VanishOnLine (Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)) f := by
  intro z hz
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hz
  obtain ⟨c, rfl⟩ := hz
  rw [eval_smul_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_segreRingHom, kerSegre_mem_iff.mp (homogeneousComponent_mem_ker hf i), map_zero,
    mul_zero]

end Homog

/-! ## 6. Vanishing of a homogeneous polynomial at a projective point -/

section Infra

variable {k : Type*} [Field k] {n : ℕ}

/-- For a homogeneous polynomial, vanishing on the projective point is the same as vanishing at
any chosen nonzero representative. -/
theorem vanishOnLine_mk_iff {f : Poly k n} {d : ℕ} (hf : f.IsHomogeneous d)
    {v : Coord n → k} (hv : v ≠ 0) :
    VanishOnLine (Projectivization.mk k v hv) f ↔ MvPolynomial.eval v f = 0 := by
  constructor
  · intro h
    exact h v (by rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self v)
  · intro h z hz
    rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [show (c • v : Coord n → k) = fun i => c * v i from rfl, eval_smul_of_isHomogeneous hf, h,
      mul_zero]

end Infra

/-! ## 7. The image of the Segre map is the zero locus of the 2×2 minors -/

section Image

variable {k : Type*} [Field k] [Infinite k] {r s : ℕ}

/-- The `P^r`-coordinate of the pair recovered from a rank-one matrix. -/
def recoverA (v : Coord (r * s + r + s) → k) (j₀ : Coord s) : Coord r → k :=
  fun i => v (zIdx r s (i, j₀))

/-- The `P^s`-coordinate of the pair recovered from a rank-one matrix. -/
def recoverB (v : Coord (r * s + r + s) → k) (i₀ : Coord r) (j₀ : Coord s) : Coord s → k :=
  fun j => v (zIdx r s (i₀, j)) / v (zIdx r s (i₀, j₀))

theorem range_segre_subset_Z_ker :
    Set.range (segre k r s) ⊆ Z (kerSegre k r s : Set (Poly k (r * s + r + s))) := by
  rintro _ ⟨⟨p, q⟩, rfl⟩
  exact fun f hf => vanishOnLine_segre_of_mem_ker hf (Projectivization.rep_nonzero p)
    (Projectivization.rep_nonzero q)

theorem Z_kerSegre_subset_Z_minors :
    Z (kerSegre k r s : Set (Poly k (r * s + r + s))) ⊆ Z (minorsSet k r s) :=
  fun _ hp _ hf => hp _ (minorsSet_subset_kerSegre hf)

/-- **The converse direction of the hint**: a point at which all `2 × 2` minors vanish is the
Segre image of the pair recovered from any nonzero entry of a representative matrix. -/
theorem Z_minors_subset_range :
    Z (minorsSet k r s) ⊆ Set.range (segre k r s) := by
  intro p hp
  induction p using Projectivization.ind with
  | h v hv =>
    obtain ⟨t₀, ht₀⟩ : ∃ t : Coord (r * s + r + s), v t ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hv (funext h)
    obtain ⟨⟨i₀, j₀⟩, hpair⟩ : ∃ q : Coord r × Coord s, zIdx r s q = t₀ :=
      ⟨(zIdx r s).symm t₀, Equiv.apply_symm_apply _ _⟩
    rw [← hpair] at ht₀
    have ha : recoverA v j₀ ≠ 0 := by
      intro h
      exact ht₀ (congrFun h i₀)
    have hb : recoverB v i₀ j₀ ≠ 0 := by
      intro h
      have h1 : recoverB v i₀ j₀ j₀ = 0 := by rw [h]; rfl
      simp only [recoverB, div_self ht₀] at h1
      exact one_ne_zero h1
    have hvec : segreVec k r s (recoverA v j₀) (recoverB v i₀ j₀) = v := by
      funext t
      obtain ⟨⟨i, j⟩, rfl⟩ : ∃ q : Coord r × Coord s, zIdx r s q = t :=
        ⟨(zIdx r s).symm t, Equiv.apply_symm_apply _ _⟩
      have hmin : v (zIdx r s (i, j)) * v (zIdx r s (i₀, j₀))
          = v (zIdx r s (i, j₀)) * v (zIdx r s (i₀, j)) := by
        have h0 : MvPolynomial.eval v (minor (k := k) i i₀ j j₀) = 0 := by
          have hmem : minor (k := k) i i₀ j j₀ ∈ minorsSet k r s :=
            ⟨((i, j), (i₀, j₀)), rfl⟩
          rw [← vanishOnLine_mk_iff (minor_isHomogeneous i i₀ j j₀) hv]
          exact hp _ hmem
        simp only [minor, zvar, map_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X] at h0
        exact sub_eq_zero.1 h0
      rw [segreVec_zIdx]
      simp only [recoverA, recoverB]
      rw [← mul_div_assoc, div_eq_iff ht₀]
      exact hmin.symm
    refine ⟨(Projectivization.mk k (recoverA v j₀) ha,
      Projectivization.mk k (recoverB v i₀ j₀) hb), ?_⟩
    rw [segre_mk]
    refine (Projectivization.mk_eq_mk_iff' k _ _ _ _).2 ⟨1, ?_⟩
    rw [one_smul]
    exact hvec.symm

theorem range_segre_eq_Z_minors : Set.range (segre k r s) = Z (minorsSet k r s) :=
  le_antisymm (Set.Subset.trans range_segre_subset_Z_ker Z_kerSegre_subset_Z_minors)
    Z_minors_subset_range

/-- **Hartshorne's hint**: the image of the Segre map is the zero locus of the kernel `a` of
`z_ij ↦ x_i y_j`. -/
theorem range_segre_eq_Z_ker :
    Set.range (segre k r s) = Z (kerSegre k r s : Set (Poly k (r * s + r + s))) := by
  refine le_antisymm range_segre_subset_Z_ker fun p hp => ?_
  exact Z_minors_subset_range (Z_kerSegre_subset_Z_minors hp)

/-- The image of the Segre map is Zariski closed. -/
theorem range_segre_isClosed : IsClosed (Set.range (segre k r s)) := by
  rw [range_segre_eq_Z_minors]
  exact isClosed_Z minorsSet_isHomogSet

end Image

/-! ## 8. Irreducibility from a prime vanishing ideal (direction of Ex. I.2.4 (b)) -/

section Irred

variable {k : Type*} [Field k] {n : ℕ}

/-- A closed set whose vanishing ideal is prime is irreducible.  This is the direction of
Exercise I.2.4 (b) used here. -/
theorem isIrreducible_of_isPrime_I {Y : Set (Proj k n)} (hY : IsClosed Y)
    (hprime : (I Y).IsPrime) : IsIrreducible Y := by
  have hYne : Y.Nonempty := by
    rcases Set.eq_empty_or_nonempty Y with hempty | h
    · exfalso
      have h1 : (1 : Poly k n) ∈ I Y := by
        rw [hempty]
        exact mem_I_of isHomogPoly_one fun p hp => absurd hp (Set.notMem_empty p)
      exact hprime.ne_top ((Ideal.eq_top_iff_one (I := I Y)).mpr h1)
    · exact h
  refine ⟨hYne, ?_⟩
  intro u v hu hv hune hvne
  obtain ⟨T₁, hT₁, rfl⟩ := hu
  obtain ⟨T₂, hT₂, rfl⟩ := hv
  by_contra hemp
  have hsub : Y ⊆ Z T₁ ∪ Z T₂ := by
    intro p hp
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    exact hemp ⟨p, hp, hcon.1, hcon.2⟩
  rcases closed_union_of_isPrime hY hprime (isClosed_Z hT₁) (isClosed_Z hT₂) hsub with h | h
  · obtain ⟨p, hp⟩ := hune
    exact hp.2 (h hp.1)
  · obtain ⟨p, hp⟩ := hvne
    exact hp.2 (h hp.1)

end Irred

/-! ## 9. The homogeneous prime ideal `a` of the image, and the main theorem -/

section Main

variable {k : Type*} [Field k] [Infinite k] {r s : ℕ}

theorem kerSegre_le_I_range : (kerSegre k r s) ≤ I (Set.range (segre k r s)) := by
  intro f hf
  have hsum : f = ∑ d ∈ Finset.range (f.totalDegree + 1),
      MvPolynomial.homogeneousComponent d f :=
    (MvPolynomial.sum_homogeneousComponent (φ := f)).symm
  rw [hsum]
  refine Ideal.sum_mem _ fun d _ =>
    mem_I_of ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d f⟩ ?_
  rintro _ ⟨⟨p, q⟩, rfl⟩ z hz
  exact vanishOnLine_segre_of_mem_ker (homogeneousComponent_mem_ker hf d)
    (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q) z hz

theorem I_range_le_kerSegre : I (Set.range (segre k r s)) ≤ kerSegre k r s := by
  rw [I, Ideal.span_le]
  rintro f ⟨⟨d, hd⟩, hvan⟩
  change f ∈ kerSegre k r s
  rw [kerSegre_mem_iff]
  refine MvPolynomial.funext_set (s := fun _ : Coord r ⊕ Coord s => {x : k | x ≠ 0}) ?_ ?_
  · intro _
    exact (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono (fun _ hx => hx.2)
  · intro x hx
    simp only [map_zero]
    have hxnz : ∀ i, x i ≠ 0 := fun i => hx i (Set.mem_univ i)
    set a : Coord r → k := fun i => x (Sum.inl i) with hadef
    set b : Coord s → k := fun j => x (Sum.inr j) with hbdef
    have ha : a ≠ 0 := by
      intro h
      have h1 : x (Sum.inl (0 : Coord r)) = 0 := by
        have := congrFun h 0
        simpa only [hadef, Pi.zero_apply] using this
      exact hxnz _ h1
    have hb : b ≠ 0 := by
      intro h
      have h1 : x (Sum.inr (0 : Coord s)) = 0 := by
        have := congrFun h 0
        simpa only [hbdef, Pi.zero_apply] using this
      exact hxnz _ h1
    have hx' : x = Sum.elim a b := by
      funext z
      cases z <;> rfl
    rw [hx', ← eval_segreRingHom]
    exact hvan _ ⟨(Projectivization.mk k a ha, Projectivization.mk k b hb), segre_mk ha hb⟩ _
      (by rw [Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self _)

/-- **The homogeneous ideal of the image is Hartshorne's `a`** (as asserted in the natural
proof: "Its homogeneous ideal is the kernel of `k[z_ij] → k[x_i,y_j]`"). -/
theorem I_range_eq_kerSegre :
    I (Set.range (segre k r s)) = kerSegre k r s :=
  le_antisymm I_range_le_kerSegre kerSegre_le_I_range

/-- `a` is a prime ideal. -/
theorem kerSegre_isPrime : (kerSegre k r s).IsPrime :=
  RingHom.ker_isPrime (segreRingHom k r s)

/-- **The image of the Segre map is a projective variety** (closed and irreducible). -/
theorem range_segre_isIrreducible : IsIrreducible (Set.range (segre k r s)) :=
  isIrreducible_of_isPrime_I range_segre_isClosed (by
    rw [I_range_eq_kerSegre]
    exact kerSegre_isPrime)

end Main

/-! ## 10. The statement of Exercise I.2.14, bundled -/

section Statement

variable {k : Type*} [Field k] {r s : ℕ}

/-- The conclusion of Hartshorne I.2.14, as a single proposition:

* `ψ` is given in coordinates by `z_ij = a_i b_j` (lexicographic order, `N = rs + r + s`);
* `ψ` is well defined and injective;
* `Im ψ = Z(a)`, where `a` is the kernel of `z_ij ↦ x_i y_j`;
* `Im ψ = Z(minors)`, the zero locus of the `2 × 2` minors of `(z_ij)`;
* the image is closed and irreducible, i.e. a subvariety of `P^N`;
* `a` is exactly the homogeneous ideal `I(Im ψ)`, and it is prime. -/
def SegreConclusion (k : Type*) [Field k] (r s : ℕ) : Prop :=
  (∀ (a : Coord r → k) (b : Coord s → k) (i : Coord r) (j : Coord s),
      segreVec k r s a b (zIdx r s (i, j)) = a i * b j) ∧
    (∀ (a : Coord r → k) (ha : a ≠ 0) (b : Coord s → k) (hb : b ≠ 0),
      segre k r s (Projectivization.mk k a ha, Projectivization.mk k b hb)
        = Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)) ∧
    (∀ (a a' : Coord r → k) (b b' : Coord s → k) (ha : a ≠ 0) (hb : b ≠ 0)
      (ha' : a' ≠ 0) (hb' : b' ≠ 0),
      Projectivization.mk k a ha = Projectivization.mk k a' ha' →
      Projectivization.mk k b hb = Projectivization.mk k b' hb' →
      Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)
        = Projectivization.mk k (segreVec k r s a' b') (segreVec_ne_zero ha' hb')) ∧
    Function.Injective (segre k r s) ∧
    Set.range (segre k r s) = Z (kerSegre k r s : Set (Poly k (r * s + r + s))) ∧
    Set.range (segre k r s) = Z (minorsSet k r s) ∧
    IsClosed (Set.range (segre k r s)) ∧
    IsIrreducible (Set.range (segre k r s)) ∧
    I (Set.range (segre k r s)) = kerSegre k r s ∧
    (kerSegre k r s).IsPrime

end Statement

section Final

variable {k : Type*} [Field k] [Infinite k] {r s : ℕ}

/-- **Hartshorne (1977), Algebraic Geometry, Chapter I, Exercise 2.14 (the Segre embedding).**

The map `ψ : P^r × P^s → P^N`, `N = rs + r + s`, sending the ordered pair
`(a_0 : … : a_r) × (b_0 : … : b_s)` to `(… : a_i b_j : …)` in lexicographic order is well
defined and injective, its image is the subvariety `Z(a)` of `P^N` cut out by the kernel `a` of
`k[{z_ij}] → k[x_0,…,x_r,y_0,…,y_s]`, `z_ij ↦ x_i y_j` (equivalently by the `2 × 2` minors of
`(z_ij)`), and `a` is the homogeneous prime ideal of that image. -/
theorem hartshorne_I_2_14 (k : Type*) [Field k] [Infinite k] (r s : ℕ) :
    SegreConclusion k r s := by
  refine ⟨?_, ?_, ?_, segre_injective, range_segre_eq_Z_ker, range_segre_eq_Z_minors,
    range_segre_isClosed, range_segre_isIrreducible, I_range_eq_kerSegre, kerSegre_isPrime⟩
  · exact fun a b i j => segreVec_zIdx a b i j
  · exact fun a ha b hb => segre_mk ha hb
  · exact fun a a' b b' ha hb ha' hb' h1 h2 => segre_welldef ha hb ha' hb' h1 h2

/-- The statement of Exercise I.2.14 written out in full, without the `SegreConclusion`
abbreviation (definitionally the same proposition as `hartshorne_I_2_14`). -/
theorem hartshorne_I_2_14_statement (k : Type*) [Field k] [Infinite k] (r s : ℕ) :
    (∀ (a : Coord r → k) (b : Coord s → k) (i : Coord r) (j : Coord s),
        segreVec k r s a b (zIdx r s (i, j)) = a i * b j) ∧
      (∀ (a : Coord r → k) (ha : a ≠ 0) (b : Coord s → k) (hb : b ≠ 0),
        segre k r s (Projectivization.mk k a ha, Projectivization.mk k b hb)
          = Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)) ∧
      (∀ (a a' : Coord r → k) (b b' : Coord s → k) (ha : a ≠ 0) (hb : b ≠ 0)
        (ha' : a' ≠ 0) (hb' : b' ≠ 0),
        Projectivization.mk k a ha = Projectivization.mk k a' ha' →
        Projectivization.mk k b hb = Projectivization.mk k b' hb' →
        Projectivization.mk k (segreVec k r s a b) (segreVec_ne_zero ha hb)
          = Projectivization.mk k (segreVec k r s a' b') (segreVec_ne_zero ha' hb')) ∧
      Function.Injective (segre k r s) ∧
      Set.range (segre k r s) = Z (kerSegre k r s : Set (Poly k (r * s + r + s))) ∧
      Set.range (segre k r s) = Z (minorsSet k r s) ∧
      IsClosed (Set.range (segre k r s)) ∧
      IsIrreducible (Set.range (segre k r s)) ∧
      I (Set.range (segre k r s)) = kerSegre k r s ∧
      (kerSegre k r s).IsPrime :=
  hartshorne_I_2_14 k r s

/-- Exercise I.2.14 over the standing hypothesis of Chapter I: `k` algebraically closed. -/
theorem hartshorne_I_2_14_algClosed (k : Type*) [Field k] [IsAlgClosed k] (r s : ℕ) :
    SegreConclusion k r s :=
  hartshorne_I_2_14 k r s

end Final

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_2_14.zIdx_apply
#print axioms Hartshorne77.Ex_I_2_14.minor_isHomogeneous
#print axioms Hartshorne77.Ex_I_2_14.eval_segreRingHom
#print axioms Hartshorne77.Ex_I_2_14.minorsSet_subset_kerSegre
#print axioms Hartshorne77.Ex_I_2_14.segreVec_ne_zero
#print axioms Hartshorne77.Ex_I_2_14.segre_mk
#print axioms Hartshorne77.Ex_I_2_14.segre_welldef
#print axioms Hartshorne77.Ex_I_2_14.segre_injective
#print axioms Hartshorne77.Ex_I_2_14.coeff_eq_zero_of_forall_eval_sum_pow_eq_zero
#print axioms Hartshorne77.Ex_I_2_14.homogeneousComponent_mem_ker
#print axioms Hartshorne77.Ex_I_2_14.vanishOnLine_segre_of_mem_ker
#print axioms Hartshorne77.Ex_I_2_14.Z_minors_subset_range
#print axioms Hartshorne77.Ex_I_2_14.range_segre_eq_Z_ker
#print axioms Hartshorne77.Ex_I_2_14.range_segre_eq_Z_minors
#print axioms Hartshorne77.Ex_I_2_14.range_segre_isClosed
#print axioms Hartshorne77.Ex_I_2_14.isIrreducible_of_isPrime_I
#print axioms Hartshorne77.Ex_I_2_14.kerSegre_le_I_range
#print axioms Hartshorne77.Ex_I_2_14.I_range_le_kerSegre
#print axioms Hartshorne77.Ex_I_2_14.I_range_eq_kerSegre
#print axioms Hartshorne77.Ex_I_2_14.kerSegre_isPrime
#print axioms Hartshorne77.Ex_I_2_14.range_segre_isIrreducible
#print axioms Hartshorne77.Ex_I_2_14.hartshorne_I_2_14
#print axioms Hartshorne77.Ex_I_2_14.hartshorne_I_2_14_statement
#print axioms Hartshorne77.Ex_I_2_14.hartshorne_I_2_14_algClosed

end Hartshorne77.Ex_I_2_14
