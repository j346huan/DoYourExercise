/-
Hartshorne, *Algebraic Geometry* (1977), Chapter I, Section 3, Exercise I.3.8.

Statement (book; cross-checked against the OCR of the 1977 text and public renderings):
  Let `H_i` and `H_j` be the hyperplanes in `P^n` defined by `X_i = 0` and `X_j = 0`, with
  `i ≠ j`. Show that any regular function on `P^n - (H_i ∩ H_j)` is constant.
  (The book adds: this gives an alternative proof of (3.4a) in the case `Y = P^n`.)

Main result: `hartshorne_I_3_8`, at the end of this file.

Formalization (classical point-set, `import Mathlib` only, no scheme theory):
* `Proj k n` is the set of lines in `k^{n+1}` (`Projectivization`), with `Proj.vanish` and
  `Proj.ratio` for homogeneous forms.
* Zariski topology: opens are unions of basic opens `D_+(A) = {P | A(P) ≠ 0}`
  (`Proj.IsProjOpen`, `Proj.instTopologicalSpace`).
* Regular functions: `IsRegularAt` / `IsRegularOn` — locally `A / B` with `A`, `B` homogeneous of
  the same degree and `B` nowhere zero on an open neighbourhood (Hartshorne, I.3).
* `twoHypCompl i j = P^n - (H_i ∩ H_j)`: `coordHyp i` is `H_i`; `twoHypCompl_eq` identifies the
  set with `Set.univ \ (coordHyp i ∩ coordHyp j)` and `isOpen_twoHypCompl` shows it is open.

Proof route:
* `exists_poly_of_locally_ratio`: a function on `k^m` that is locally a ratio of polynomials with
  non-vanishing denominator is a polynomial function (quasi-compactness of `k^m` + weak
  Nullstellensatz).
* `exists_poly_on_chart`: a function regular on the chart `U_i = D_+(X_i)` is a polynomial in the
  affine chart coordinates (dehomogenisation).
* `chart_poly_const`: if a polynomial `p` in the `i`-th chart coordinates agrees, on the overlap
  `y_kk ≠ 0` (`i.succAbove kk = j`), with a polynomial `q` in the `j`-th chart coordinates, then
  `p` is constant.  Proof: restrict to the line `v ↦ a · v` (`lineSubst`), along which the
  transition to the `j`-th chart has the single pole `(v · a_kk)⁻¹` in the slot `m₀` determined by
  `j.succAbove m₀ = i` and is constant elsewhere; clearing denominators (`clearDenom`,
  `clearDenom_eval`) yields `C (a_kk^d) * X^d * (p ∘ a) = clearDenom q c m₀ a_kk`, whose right
  side has degree `≤ d = totalDegree q` while the left side has degree `d + natDegree (p ∘ a)`;
  hence `p ∘ a` is constant for every direction `a` with `a_kk ≠ 0`, so `p` is constant.
* Assembly: `U_i ∪ U_j = P^n - (H_i ∩ H_j)`, so a regular function `f` on that set is a
  polynomial on each of the two charts; both polynomials are constant, and the two constants
  agree at a point of the overlap `U_i ∩ U_j`.
* `isRegular_const`: constant functions are regular, so on `P^n - (H_i ∩ H_j)` the regular
  functions are exactly the constants.
* `regular_proj_const`: the book's parenthetical remark — `(3.4a)` for `Y = P^n` — that regular
  functions on all of `P^n` are constant, deduced from `hartshorne_I_3_8` by covering `P^n` with
  the open sets `P^n - (H_i ∩ H_j)`.
-/
import Mathlib

noncomputable section

namespace Hartshorne77.Ex_I_3_8

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-! ## Homogeneity: scalars and monomials -/

/-- In a homogeneous polynomial of degree `d` every monomial that occurs has total degree `d`. -/
theorem degree_of_mem_support {m : ℕ} {A : MvPolynomial (Fin m) k} {d : ℕ}
    (hA : A.IsHomogeneous d) {e : Fin m →₀ ℕ} (he : e ∈ A.support) :
    Finsupp.degree e = d := by
  have h1 : A ∈ MvPolynomial.homogeneousSubmodule (Fin m) k d := hA
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at h1
  rw [AddMonoidAlgebra.mem_supported] at h1
  exact h1 (Finset.mem_coe.mpr he)

/-- Evaluating a homogeneous polynomial of degree `d` at a scalar multiple of a point. -/
theorem eval_smul_of_isHomogeneous {m : ℕ} {A : MvPolynomial (Fin m) k} {d : ℕ}
    (hA : A.IsHomogeneous d) (c : k) (v : Fin m → k) :
    A.eval (c • v) = c ^ d * A.eval v := by
  conv_lhs => rw [MvPolynomial.eval_eq']
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : Finsupp.degree e = d := degree_of_mem_support hA he
  have h1 : (∏ i, (c • v) i ^ e i) = c ^ d * ∏ i, v i ^ e i := by
    have h2 : ∀ i, (c • v) i ^ e i = c ^ e i * v i ^ e i := by
      intro i; rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    have hsum : (∑ i, e i) = d := by rw [← Finsupp.degree_eq_sum]; exact hdeg
    rw [Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hsum]
  rw [h1]; ring

/-! ## Projective space -/

/-- Projective `n`-space over `k`: the set of lines in `k^{n+1}`. -/
abbrev Proj (k : Type*) [Field k] (n : ℕ) := Projectivization k (Fin (n + 1) → k)

namespace Proj

/-- `vanish A P` says that the homogeneous polynomial `A` vanishes at the point `P`;
`H_i = {P | vanish (X i) P}` is the `i`-th coordinate hyperplane. -/
def vanish (A : MvPolynomial (Fin (n + 1)) k) (P : Proj k n) : Prop := A.eval P.rep = 0

theorem vanish_mk {A : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    vanish A (Projectivization.mk k v hv) ↔ A.eval v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  have ha' : (a : k) • v = (Projectivization.mk k v hv).rep := by
    rw [← ha]; rfl
  have hmain : A.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * A.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hA]
  simp only [vanish, hmain]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero d hane)
  · intro h; rw [h, mul_zero]

/-- The value at `P` of a ratio `A / B` of homogeneous polynomials of the same degree. -/
def ratio (A B : MvPolynomial (Fin (n + 1)) k) (P : Proj k n) : k :=
  A.eval P.rep / B.eval P.rep

theorem ratio_mk {A B : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (hB : B.IsHomogeneous d) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ratio A B (Projectivization.mk k v hv) = A.eval v / B.eval v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  have ha' : (a : k) • v = (Projectivization.mk k v hv).rep := by
    rw [← ha]; rfl
  have h1 : A.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * A.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hA]
  have h2 : B.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * B.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hB]
  simp only [ratio, h1, h2, mul_div_mul_left _ _ (pow_ne_zero d hane)]

/-- The Zariski topology on `P^n`: open sets are unions of basic open sets
`D_+(A) = {P | A(P) ≠ 0}` for homogeneous forms `A`. -/
def IsProjOpen (V : Set (Proj k n)) : Prop :=
  ∀ P ∈ V, ∃ (A : MvPolynomial (Fin (n + 1)) k) (d : ℕ),
    A.IsHomogeneous d ∧ A.eval P.rep ≠ 0 ∧ {Q | A.eval Q.rep ≠ 0} ⊆ V

theorem isProjOpen_univ : IsProjOpen (Set.univ : Set (Proj k n)) := by
  intro P _
  exact ⟨1, 0, isHomogeneous_one _ _, by simp, Set.subset_univ _⟩

theorem isProjOpen_inter {V W : Set (Proj k n)} (hV : IsProjOpen V) (hW : IsProjOpen W) :
    IsProjOpen (V ∩ W) := by
  intro P hP
  obtain ⟨A, d, hA, hAP, hAV⟩ := hV P hP.1
  obtain ⟨B, e, hB, hBP, hBW⟩ := hW P hP.2
  refine ⟨A * B, d + e, hA.mul hB, ?_, ?_⟩
  · simp only [eval_mul]; exact mul_ne_zero hAP hBP
  · intro Q hQ
    simp only [eval_mul] at hQ
    exact ⟨hAV (fun h => hQ (by rw [h, zero_mul])),
      hBW (fun h => hQ (by rw [h, mul_zero]))⟩

theorem isProjOpen_sUnion (S : Set (Set (Proj k n))) (hS : ∀ s ∈ S, IsProjOpen s) :
    IsProjOpen (⋃₀ S) := by
  intro P hP
  obtain ⟨s, hsS, hPs⟩ := Set.mem_sUnion.mp hP
  obtain ⟨A, d, hA, hAP, hAs⟩ := hS s hsS P hPs
  exact ⟨A, d, hA, hAP, fun Q hQ => Set.mem_sUnion.mpr ⟨s, hsS, hAs hQ⟩⟩

set_option warn.classDefReducibility false in
/-- The Zariski topology on `P^n`. -/
instance instTopologicalSpace : TopologicalSpace (Proj k n) where
  IsOpen := IsProjOpen
  isOpen_univ := isProjOpen_univ
  isOpen_inter := fun _ _ => isProjOpen_inter
  isOpen_sUnion := fun S hS => isProjOpen_sUnion S hS

end Proj

/-! ## Affine space -/

section Affine

/-- Zariski open subsets of affine `m`-space: unions of basic open sets
`D(g) = {y | g(y) ≠ 0}`. -/
def IsAffOpen (W : Set (Fin m → k)) : Prop :=
  ∀ y ∈ W, ∃ g : MvPolynomial (Fin m) k, g.eval y ≠ 0 ∧ {z | g.eval z ≠ 0} ⊆ W

theorem isAffOpen_univ : IsAffOpen (Set.univ : Set (Fin m → k)) := fun y _ =>
  ⟨1, by simp, Set.subset_univ _⟩

theorem isAffOpen_inter {V W : Set (Fin m → k)} (hV : IsAffOpen V) (hW : IsAffOpen W) :
    IsAffOpen (V ∩ W) := by
  intro y hy
  obtain ⟨g, hgy, hgV⟩ := hV y hy.1
  obtain ⟨h, hhy, hhW⟩ := hW y hy.2
  refine ⟨g * h, ?_, ?_⟩
  · simp only [eval_mul]; exact mul_ne_zero hgy hhy
  · intro z hz
    simp only [eval_mul] at hz
    exact ⟨hgV (fun h0 => hz (by rw [h0, zero_mul])),
      hhW (fun h0 => hz (by rw [h0, mul_zero]))⟩

theorem isAffOpen_sUnion (S : Set (Set (Fin m → k))) (hS : ∀ s ∈ S, IsAffOpen s) :
    IsAffOpen (⋃₀ S) := by
  intro y hy
  obtain ⟨s, hsS, hys⟩ := Set.mem_sUnion.mp hy
  obtain ⟨g, hgy, hgs⟩ := hS s hsS y hys
  exact ⟨g, hgy, fun z hz => Set.mem_sUnion.mpr ⟨s, hsS, hgs hz⟩⟩

set_option warn.classDefReducibility false in
/-- The Zariski topology on affine `m`-space. -/
instance instAffTopologicalSpace : TopologicalSpace (Fin m → k) where
  IsOpen := IsAffOpen
  isOpen_univ := isAffOpen_univ
  isOpen_inter := fun _ _ => isAffOpen_inter
  isOpen_sUnion := fun S hS => isAffOpen_sUnion S hS

section AlgClosed
variable [IsAlgClosed k]

/-- **A polynomial function vanishing on a non-empty basic open set is zero.** -/
theorem eq_zero_of_forall_eval_eq_zero_on_basic {g h : MvPolynomial (Fin m) k} {y : Fin m → k}
    (hy : h.eval y ≠ 0) (H : ∀ z, h.eval z ≠ 0 → g.eval z = 0) : g = 0 := by
  have hne : h ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  have hgh : g * h = 0 := by
    refine MvPolynomial.funext fun z => ?_
    rw [MvPolynomial.eval_mul, map_zero]
    by_cases hz : h.eval z = 0
    · rw [hz, mul_zero]
    · rw [H z hz, zero_mul]
  exact (mul_eq_zero.mp hgh).resolve_right hne

/-- **Weak Nullstellensatz**, in the form needed: an ideal of `k[x_1,…,x_m]` all of whose
elements vanish at no common point is the unit ideal. -/
theorem ideal_eq_top_of_no_common_zero (I : Ideal (MvPolynomial (Fin m) k))
    (h : ∀ y : Fin m → k, ∃ p ∈ I, p.eval y ≠ 0) : I = ⊤ := by
  by_contra hI
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := k) hM
  obtain ⟨p, hpI, hpx⟩ := h x
  have hp : p ∈ MvPolynomial.vanishingIdeal k ({x} : Set (Fin m → k)) := by
    rw [← hx]; exact hle hpI
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_def] at hp
  simp only [Algebra.algebraMap_self, MvPolynomial.eval₂_id] at hp
  exact hpx hp

/-- **Regular functions on affine space are polynomial.** A function on `k^m` which is
locally a ratio `a / b` of polynomials, with `b` non-vanishing, is a polynomial function. -/
theorem exists_poly_of_locally_ratio {g : (Fin m → k) → k}
    (h : ∀ y, ∃ (a b : MvPolynomial (Fin m) k), b.eval y ≠ 0 ∧
      ∀ z, b.eval z ≠ 0 → b.eval z * g z = a.eval z) :
    ∃ p : MvPolynomial (Fin m) k, ∀ y, g y = p.eval y := by
  classical
  -- the set of "denominators"
  set S : Set (MvPolynomial (Fin m) k) :=
    {b | ∃ a : MvPolynomial (Fin m) k, ∀ z, b.eval z ≠ 0 → b.eval z * g z = a.eval z}
    with hSdef
  have hS : ∀ y, ∃ b ∈ S, b.eval y ≠ 0 := by
    intro y
    obtain ⟨a, b, hb, hab⟩ := h y
    exact ⟨b, ⟨a, hab⟩, hb⟩
  -- the square of a denominator multiplies `g` to a polynomial function
  have hsq : ∀ b ∈ S, ∃ q : MvPolynomial (Fin m) k, ∀ z, b.eval z ^ 2 * g z = q.eval z := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    refine ⟨a * b, fun z => ?_⟩
    rw [MvPolynomial.eval_mul]
    by_cases hz : b.eval z = 0
    · rw [hz]; ring
    · have h1 : b.eval z * g z = a.eval z := ha z hz
      calc b.eval z ^ 2 * g z = b.eval z * (b.eval z * g z) := by ring
        _ = b.eval z * a.eval z := by rw [h1]
        _ = a.eval z * b.eval z := by ring
  -- the ideal generated by the squares of denominators is the unit ideal
  set T : Set (MvPolynomial (Fin m) k) := {q | ∃ b ∈ S, b ^ 2 = q} with hTdef
  have htop : Ideal.span T = ⊤ := by
    refine ideal_eq_top_of_no_common_zero _ fun y => ?_
    obtain ⟨b, hbS, hby⟩ := hS y
    exact ⟨b ^ 2, Ideal.subset_span ⟨b, hbS, rfl⟩, by simpa using pow_ne_zero 2 hby⟩
  have hone : (1 : MvPolynomial (Fin m) k) ∈ Ideal.span T := htop ▸ Submodule.mem_top
  obtain ⟨c, hc_supp, hc_sum⟩ := Submodule.mem_span_set.mp hone
  have hsq4 : ∀ q : MvPolynomial (Fin m) k, ∃ r : MvPolynomial (Fin m) k,
      (∃ b ∈ S, b ^ 2 = q) → ∀ z, q.eval z * g z = r.eval z := by
    intro q
    by_cases hq : ∃ b ∈ S, b ^ 2 = q
    · obtain ⟨b, hbS, rfl⟩ := hq
      obtain ⟨r, hr⟩ := hsq b hbS
      exact ⟨r, fun _ z => by rw [MvPolynomial.eval_pow]; exact hr z⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose rep hrep using hsq4
  -- convert the `Finsupp.sum` Bezout identity into a `Finset.sum` identity
  have hconv1 : c.sum (fun i x => x • i) = ∑ q ∈ c.support, c q * q := by
    rw [Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (s := c.support)
      (g := fun i x => x • i) (fun i _ => by simp)]
    simp [smul_eq_mul]
  have hconv2 : c.sum (fun q a => a * rep q) = ∑ q ∈ c.support, c q * rep q :=
    Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (s := c.support)
      (g := fun q a => a * rep q) (fun i _ => by simp)
  have hpoly1 : (∑ q ∈ c.support, c q * q) = 1 := by
    rw [← hconv1]; exact hc_sum
  refine ⟨∑ q ∈ c.support, c q * rep q, fun y => ?_⟩
  have hvalq : (∑ q ∈ c.support, c q * q).eval y = 1 := by rw [hpoly1, map_one]
  have hvalrep : (∑ q ∈ c.support, c q * rep q).eval y
      = ∑ q ∈ c.support, (c q).eval y * (rep q).eval y := by
    rw [MvPolynomial.eval_sum]
    exact Finset.sum_congr rfl fun q _ => MvPolynomial.eval_mul ..
  rw [hvalrep]
  calc g y = 1 * g y := (one_mul _).symm
    _ = (∑ q ∈ c.support, c q * q).eval y * g y := by rw [hvalq]
    _ = ∑ q ∈ c.support, (c q).eval y * (q.eval y * g y) := by
          rw [MvPolynomial.eval_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by
            rw [MvPolynomial.eval_mul]; ring
    _ = ∑ q ∈ c.support, (c q).eval y * (rep q).eval y := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have hqT : ∃ b ∈ S, b ^ 2 = q := hc_supp hq
          rw [hrep q hqT y]

end AlgClosed

end Affine

/-! ## The standard affine charts of `P^n` -/

section Charts

variable [IsAlgClosed k]

/-- The homogeneous coordinate vector `(…, 1, …)` with `1` in slot `i` and the entries of `y`
in the remaining slots, i.e. the point of `U_i` with affine coordinates `y`. -/
def chartVec (i : Fin (n + 1)) (y : Fin n → k) : Fin (n + 1) → k := Fin.insertNth i 1 y

omit [IsAlgClosed k] in
theorem chartVec_ne_zero (i : Fin (n + 1)) (y : Fin n → k) : chartVec i y ≠ 0 := by
  intro h
  have h1 := congrFun h i
  simp [chartVec] at h1

omit [IsAlgClosed k] in
theorem chartVec_apply_same (i : Fin (n + 1)) (y : Fin n → k) : chartVec i y i = 1 := by
  simp [chartVec]

omit [IsAlgClosed k] in
theorem chartVec_apply_succAbove (i : Fin (n + 1)) (y : Fin n → k) (m : Fin n) :
    chartVec i y (i.succAbove m) = y m := by simp [chartVec]

/-- The chart `U_i = D_+(X_i) ≅ k^n`, mapping `y` to the point with homogeneous coordinates
`(…, 1, …)` and the entries of `y` elsewhere. -/
def chart (i : Fin (n + 1)) (y : Fin n → k) : Proj k n :=
  Projectivization.mk k (chartVec i y) (chartVec_ne_zero i y)

/-- The affine coordinates `X_m / X_i` of a point of the chart `U_i`. -/
def chartInv (i : Fin (n + 1)) (P : Proj k n) : Fin n → k :=
  fun m => P.rep (i.succAbove m) / P.rep i

/-- The equivalence `Fin n ≃ {ℓ // ℓ ≠ i}` given by `Fin.succAbove`. -/
noncomputable def chartEquiv (i : Fin (n + 1)) : Fin n ≃ {ℓ : Fin (n + 1) // ℓ ≠ i} :=
  Equiv.ofBijective (fun m => (⟨i.succAbove m, i.succAbove_ne m⟩ : {ℓ : Fin (n + 1) // ℓ ≠ i}))
    ⟨fun a b hab => Fin.succAbove_right_injective (congrArg Subtype.val hab),
      fun ⟨ℓ, hℓ⟩ => by
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (x := ℓ) (y := i) hℓ
        exact ⟨z, Subtype.ext hz⟩⟩

@[simp]
theorem chartEquiv_apply (i : Fin (n + 1)) (m : Fin n) :
    ((chartEquiv i) m : Fin (n + 1)) = i.succAbove m := rfl

theorem succAbove_chartEquiv_symm (i : Fin (n + 1)) (ℓ : Fin (n + 1)) (hℓ : ℓ ≠ i) :
    i.succAbove ((chartEquiv i).symm ⟨ℓ, hℓ⟩) = ℓ :=
  congrArg Subtype.val (Equiv.apply_symm_apply (chartEquiv i) ⟨ℓ, hℓ⟩)

/-- Dehomogenisation at the chart `i`: the substitution `X_i ↦ 1`, `X_{succAbove i m} ↦ Y_m`. -/
noncomputable def dehom (i : Fin (n + 1)) (A : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Fin n) k :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun ℓ : Fin (n + 1) => if h : ℓ = i then 1 else MvPolynomial.X ((chartEquiv i).symm ⟨ℓ, h⟩)) A

omit [IsAlgClosed k] in
/-- Dehomogenisation computes the value of `A` on the chart. -/
theorem dehom_eval (i : Fin (n + 1)) (A : MvPolynomial (Fin (n + 1)) k) (y : Fin n → k) :
    (dehom i A).eval y = A.eval (chartVec i y) := by
  rw [dehom, ← MvPolynomial.eval_assoc]
  have hfun : (⇑(MvPolynomial.eval y) ∘ (fun ℓ : Fin (n + 1) =>
        if h : ℓ = i then (1 : MvPolynomial (Fin n) k)
        else MvPolynomial.X ((chartEquiv i).symm ⟨ℓ, h⟩))) = chartVec i y := by
    funext ℓ
    simp only [Function.comp_apply]
    by_cases h : ℓ = i
    · subst h
      simp [chartVec]
    · have key : chartVec i y ℓ = y ((chartEquiv i).symm ⟨ℓ, h⟩) := by
        conv_lhs => rw [← succAbove_chartEquiv_symm i ℓ h]
        exact chartVec_apply_succAbove i y _
      rw [key]
      simp only [dif_neg h, MvPolynomial.eval_X]
  rw [hfun]

omit [IsAlgClosed k] in
/-- Dehomogenisation sends `X_i` to `1`. -/
theorem dehom_X (i : Fin (n + 1)) : dehom (k := k) i (MvPolynomial.X i) = 1 := by
  simp [dehom]

omit [IsAlgClosed k] in
theorem chartInjectivity (i : Fin (n + 1)) : Function.Injective (chart (k := k) i) := by
  intro y y' h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k (chartVec i y) (chartVec i y') _ _).mp h
  have h1 : a = 1 := by
    have h2 := congrFun ha i
    rw [Pi.smul_apply, chartVec_apply_same, chartVec_apply_same, smul_eq_mul, mul_one] at h2
    exact h2
  funext m
  have h2 := congrFun ha (i.succAbove m)
  rw [Pi.smul_apply, chartVec_apply_succAbove, chartVec_apply_succAbove, h1, one_smul] at h2
  exact h2.symm

omit [IsAlgClosed k] in
theorem chartInv_chart (i : Fin (n + 1)) (y : Fin n → k) :
    chartInv i (chart i y) = y := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (chartVec i y) (chartVec_ne_zero i y)
  have hrep : (chart i y).rep = (a : k) • chartVec i y := ha.symm
  have ha' : ∀ m : Fin n, ((a : k) • chartVec i y) (i.succAbove m) = (a : k) * y m := by
    intro m
    rw [Pi.smul_apply, chartVec_apply_succAbove, smul_eq_mul]
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  funext m
  show ((chart i y).rep) (i.succAbove m) / ((chart i y).rep) i = y m
  rw [hrep, ha' m, Pi.smul_apply, chartVec_apply_same, smul_eq_mul, mul_one,
    mul_comm (a : k) (y m), mul_div_cancel_right₀ _ hane]

omit [IsAlgClosed k] in
theorem chart_chartInv {i : Fin (n + 1)} {P : Proj k n} (hP : ¬ Proj.vanish (MvPolynomial.X i) P) :
    chart i (chartInv i P) = P := by
  have hi : P.rep i ≠ 0 := by simpa [Proj.vanish, MvPolynomial.eval_X] using hP
  have hvec : chartVec i (chartInv i P) = fun ℓ => (P.rep i)⁻¹ * P.rep ℓ := by
    rw [chartVec, Fin.insertNth_eq_iff]
    refine ⟨?_, ?_⟩
    · show (1 : k) = (P.rep i)⁻¹ * P.rep i
      rw [inv_mul_cancel₀ hi]
    · funext m
      show P.rep (i.succAbove m) / P.rep i = (P.rep i)⁻¹ * P.rep (i.succAbove m)
      rw [div_eq_inv_mul]
  have h1 : chart i (chartInv i P) = Projectivization.mk k P.rep (Projectivization.rep_nonzero P) := by
    show Projectivization.mk k (chartVec i (chartInv i P)) (chartVec_ne_zero i (chartInv i P)) = _
    rw [Projectivization.mk_eq_mk_iff' k]
    refine ⟨(P.rep i)⁻¹, ?_⟩
    funext ℓ
    rw [Pi.smul_apply, hvec, smul_eq_mul]
  rwa [Projectivization.mk_rep] at h1

end Charts

/-! ## Regular functions on `P^n` -/

/-- Hartshorne's notion: `f` is regular at `P` (relative to the ambient open set `U`). -/
def IsRegularAt (f : Proj k n → k) (U : Set (Proj k n)) (P : U) : Prop :=
  ∃ (d : ℕ) (A B : MvPolynomial (Fin (n + 1)) k), A.IsHomogeneous d ∧ B.IsHomogeneous d ∧
    B.eval P.1.rep ≠ 0 ∧ ∃ V : Set (Proj k n), IsOpen V ∧ P.1 ∈ V ∧ V ⊆ U ∧
      ∀ Q ∈ V, B.eval Q.rep ≠ 0 ∧ f Q = A.eval Q.rep / B.eval Q.rep

/-- `f` is regular on the open set `U`. -/
def IsRegularOn (f : Proj k n → k) (U : Set (Proj k n)) : Prop := ∀ P : U, IsRegularAt f U P

/-- The `i`-th coordinate hyperplane `H_i : X_i = 0`. -/
def coordHyp (i : Fin (n + 1)) : Set (Proj k n) := {P | Proj.vanish (MvPolynomial.X i) P}

section Charts2

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem Proj.isOpen_iff {V : Set (Proj k n)} : IsOpen V ↔ Proj.IsProjOpen V :=
  ⟨fun h => h, fun h => h⟩

omit [IsAlgClosed k] in
theorem chart_eval_eq_zero_iff {A : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (i : Fin (n + 1)) (y : Fin n → k) :
    A.eval (chartVec i y) = 0 ↔ Proj.vanish A (chart i y) :=
  (Proj.vanish_mk hA (chartVec i y) (chartVec_ne_zero i y)).symm

omit [IsAlgClosed k] in
theorem chart_ratio {A B : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (hB : B.IsHomogeneous d) (i : Fin (n + 1)) (y : Fin n → k) :
    Proj.ratio A B (chart i y) = A.eval (chartVec i y) / B.eval (chartVec i y) :=
  Proj.ratio_mk hA hB (chartVec i y) (chartVec_ne_zero i y)

omit [IsAlgClosed k] in
theorem chart_rep_eq_smul (i : Fin (n + 1)) (y : Fin n → k) :
    ∃ a : k, a ≠ 0 ∧ (chart i y).rep = a • chartVec i y := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (chartVec i y) (chartVec_ne_zero i y)
  exact ⟨a, Units.ne_zero a, ha.symm⟩

omit [IsAlgClosed k] in
theorem chartVec_eval_ne {A : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (i : Fin (n + 1)) (y : Fin n → k) :
    A.eval (chartVec i y) ≠ 0 ↔ A.eval (chart i y).rep ≠ 0 := by
  obtain ⟨a, ha, hrep⟩ := chart_rep_eq_smul i y
  rw [hrep, eval_smul_of_isHomogeneous hA]
  constructor
  · rintro h h0
    exact h ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero d ha))
  · rintro h h0
    exact h (by rw [h0, mul_zero])

omit [IsAlgClosed k] in
theorem chart_mem_chart (i : Fin (n + 1)) (y : Fin n → k) :
    ¬ Proj.vanish (MvPolynomial.X i) (chart i y) := by
  intro h
  have h2 : (MvPolynomial.X i).eval (chartVec i y) = 0 :=
    (chart_eval_eq_zero_iff (MvPolynomial.isHomogeneous_X k i) i y).mpr h
  simp [chartVec] at h2

/-- **Step 1**: a function regular on the chart `U_i` is a polynomial in the affine coordinates. -/
theorem exists_poly_on_chart (f : Proj k n → k) (i : Fin (n + 1)) {U : Set (Proj k n)}
    (hU : ∀ P, ¬ Proj.vanish (MvPolynomial.X i) P → P ∈ U) (hf : IsRegularOn f U) :
    ∃ p : MvPolynomial (Fin n) k, ∀ y : Fin n → k, f (chart i y) = p.eval y := by
  classical
  refine exists_poly_of_locally_ratio (m := n) (g := fun y => f (chart i y)) (fun y => ?_)
  obtain ⟨d, A, B, hA, hB, -, V, hVopen, hPV, hVU, hVB⟩ :=
    hf ⟨chart i y, hU _ (chart_mem_chart i y)⟩
  obtain ⟨C, e, hC, hCP, hCV⟩ := Proj.isOpen_iff.mp hVopen (chart i y) hPV
  refine ⟨dehom i A * dehom i C, dehom i B * dehom i C, ?_, ?_⟩
  · rw [MvPolynomial.eval_mul, dehom_eval, dehom_eval]
    exact mul_ne_zero ((chartVec_eval_ne hB i y).mpr (hVB _ hPV).1)
      ((chartVec_eval_ne hC i y).mpr hCP)
  · intro z hz
    have hz' : B.eval (chartVec i z) * C.eval (chartVec i z) ≠ 0 := by
      rw [MvPolynomial.eval_mul, dehom_eval, dehom_eval] at hz
      exact hz
    have hBz : B.eval (chartVec i z) ≠ 0 := (mul_ne_zero_iff.mp hz').1
    have hCz : C.eval (chartVec i z) ≠ 0 := (mul_ne_zero_iff.mp hz').2
    have hmemV : chart i z ∈ V := hCV ((chartVec_eval_ne hC i z).mp hCz)
    obtain ⟨-, hfz⟩ := hVB _ hmemV
    have hratio : f (chart i z) = A.eval (chartVec i z) / B.eval (chartVec i z) := by
      rw [hfz]; exact chart_ratio hA hB i z
    show (MvPolynomial.eval z) (dehom i B * dehom i C) * f (chart i z)
      = (MvPolynomial.eval z) (dehom i A * dehom i C)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul]
    simp only [dehom_eval]
    rw [hratio]
    field_simp

end Charts2

/-! ## Constancy along the two charts -/

section Compare

variable [IsAlgClosed k] {i j : Fin (n + 1)}

omit [IsAlgClosed k] in
/-- The `j`-coordinates of a point of the `i`-th chart, in terms of `chartVec`. -/
theorem chartInv_chart_coord (i j : Fin (n + 1)) (y : Fin n → k) (m : Fin n) :
    chartInv j (chart i y) m = chartVec i y (j.succAbove m) / chartVec i y j := by
  obtain ⟨a, ha, hrep⟩ := chart_rep_eq_smul i y
  show ((chart i y).rep (j.succAbove m)) / ((chart i y).rep j) = _
  rw [hrep]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ ha]

omit [IsAlgClosed k] in
/-- Scaling of the chart coordinates. -/
theorem chartVec_mul (i : Fin (n + 1)) (a : Fin n → k) (u : k) (ℓ : Fin (n + 1)) :
    chartVec i (fun m => a m * u) ℓ = if ℓ = i then 1 else u * chartVec i a ℓ := by
  by_cases hℓ : ℓ = i
  · subst hℓ
    simp [chartVec]
  · have h1 : chartVec i (fun m => a m * u) ℓ = a ((chartEquiv i).symm ⟨ℓ, hℓ⟩) * u := by
      conv_lhs => rw [← succAbove_chartEquiv_symm i ℓ hℓ]
      rw [chartVec_apply_succAbove]
    have h2 : chartVec i a ℓ = a ((chartEquiv i).symm ⟨ℓ, hℓ⟩) := by
      conv_lhs => rw [← succAbove_chartEquiv_symm i ℓ hℓ]
      rw [chartVec_apply_succAbove]
    rw [h1, h2, if_neg hℓ, mul_comm]


end Compare

noncomputable section


open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-! ## Restriction to a line -/

section Line

/-- Substitution `Y_m ↦ a_m · T` into the one variable polynomial ring. -/
noncomputable def lineSubst (a : Fin n → k) (p : MvPolynomial (Fin n) k) : Polynomial k :=
  MvPolynomial.eval₂ Polynomial.C (fun m => Polynomial.C (a m) * Polynomial.X) p

theorem lineSubst_eval (a : Fin n → k) (p : MvPolynomial (Fin n) k) (t : k) :
    (lineSubst a p).eval t = p.eval (fun m => a m * t) := by
  show (Polynomial.evalRingHom t) (lineSubst a p) = p.eval (fun m => a m * t)
  rw [lineSubst, MvPolynomial.hom_eval₂]
  have hcomp : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id k := by
    ext c
    simp
  have hval : (fun m => (Polynomial.evalRingHom t) (Polynomial.C (a m) * Polynomial.X))
      = (fun m => a m * t) := by
    funext m
    simp
  rw [hcomp, hval, MvPolynomial.eval₂_id]

theorem lineSubst_eval_zero (a : Fin n → k) (p : MvPolynomial (Fin n) k) :
    (lineSubst a p).eval 0 = p.eval 0 := by
  rw [lineSubst_eval]
  simp

/-- The polynomial that clears the denominator of `q` after the substitution
`Y_{m₀} ↦ (u · ak)⁻¹`, `Y_m ↦ c m` (`m ≠ m₀`): its value at `u` is
`(u · ak)^d · q(…, (u · ak)⁻¹, …)`, where `d = totalDegree q`. -/
noncomputable def clearDenom (q : MvPolynomial (Fin n) k) (c : Fin n → k) (m₀ : Fin n) (ak : k) :
    Polynomial k :=
  ∑ e ∈ q.support, Polynomial.monomial (q.totalDegree - e m₀)
    (q.coeff e * ak ^ (q.totalDegree - e m₀) * ∏ m, (if m = m₀ then 1 else c m) ^ e m)

theorem prod_split (c : Fin n → k) (m₀ : Fin n) (w : k) (e : Fin n →₀ ℕ) :
    (∏ m, (if m = m₀ then w else c m) ^ e m)
      = w ^ (e m₀) * ∏ m, (if m = m₀ then 1 else c m) ^ e m := by
  have h1 : ∀ m : Fin n, (if m = m₀ then w else c m) ^ e m
      = (if m = m₀ then w else 1) ^ e m * (if m = m₀ then 1 else c m) ^ e m := by
    intro m
    by_cases hm : m = m₀ <;> simp [hm]
  rw [Finset.prod_congr rfl fun m _ => h1 m, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single m₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ m₀) h

theorem clearDenom_eval_sum (q : MvPolynomial (Fin n) k) (c : Fin n → k) (m₀ : Fin n) (ak u : k) :
    (clearDenom q c m₀ ak).eval u
      = ∑ e ∈ q.support, q.coeff e * ak ^ (q.totalDegree - e m₀)
          * (∏ m, (if m = m₀ then 1 else c m) ^ e m) * u ^ (q.totalDegree - e m₀) := by
  rw [clearDenom]
  have h := map_sum (Polynomial.evalRingHom u)
    (fun e => Polynomial.monomial (q.totalDegree - e m₀)
      (q.coeff e * ak ^ (q.totalDegree - e m₀) * ∏ m, (if m = m₀ then 1 else c m) ^ e m))
    q.support
  simp only [Polynomial.coe_evalRingHom] at h
  rw [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.eval_monomial]

theorem clearDenom_eval (q : MvPolynomial (Fin n) k) (c : Fin n → k) (m₀ : Fin n)
    (ak u : k) (hak : ak ≠ 0) (hu : u ≠ 0) :
    (clearDenom q c m₀ ak).eval u
      = (u * ak) ^ q.totalDegree
        * q.eval (fun m => if m = m₀ then (u * ak)⁻¹ else c m) := by
  rw [clearDenom_eval_sum]
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  have huak : u * ak ≠ 0 := mul_ne_zero hu hak
  refine Finset.sum_congr rfl fun e he => ?_
  rw [prod_split c m₀ ((u * ak)⁻¹) e, inv_pow]
  obtain ⟨W, hW⟩ : ∃ W : k, ((u * ak) ^ e m₀)⁻¹ = W := ⟨_, rfl⟩
  rw [hW]
  have he0 : e m₀ ≤ q.totalDegree := by
    refine (Finset.single_le_sum (f := fun m => e m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ m₀)).trans ?_
    rw [← Finsupp.degree_eq_sum]
    exact MvPolynomial.le_totalDegree he
  have hkey : (u * ak) ^ q.totalDegree * W = (u * ak) ^ (q.totalDegree - e m₀) := by
    rw [← hW, ← pow_sub₀ (u * ak) huak he0]
  calc q.coeff e * ak ^ (q.totalDegree - e m₀)
        * (∏ m, (if m = m₀ then 1 else c m) ^ e m) * u ^ (q.totalDegree - e m₀)
      = q.coeff e * (∏ m, (if m = m₀ then 1 else c m) ^ e m)
        * (u * ak) ^ (q.totalDegree - e m₀) := by
        rw [mul_pow]; ring
    _ = q.coeff e * (∏ m, (if m = m₀ then 1 else c m) ^ e m)
        * ((u * ak) ^ q.totalDegree * W) := by rw [hkey]
    _ = (u * ak) ^ q.totalDegree
        * (q.coeff e * (W * ∏ m, (if m = m₀ then 1 else c m) ^ e m)) := by ring

/-- The clearing polynomial has no terms of degree above `totalDegree q`. -/
theorem clearDenom_coeff_eq_zero (q : MvPolynomial (Fin n) k) (c : Fin n → k) (m₀ : Fin n)
    (ak : k) {N : ℕ} (hN : 0 < N) :
    (clearDenom q c m₀ ak).coeff (q.totalDegree + N) = 0 := by
  rw [clearDenom]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [Polynomial.coeff_monomial]
  have hlt : q.totalDegree - e m₀ < q.totalDegree + N := by omega
  simp [ne_of_lt hlt]

end Line

/-! ## Chart transition: a polynomial agreeing with another chart's polynomial is constant -/

/-- The `kk`-th coordinate of the point of the `i`-th chart is nonzero at
`chartInv i (chart j z)`, provided the `m₀`-th coordinate of `z` is nonzero. -/
theorem chartInv_chart_chart_coord_ne_zero {i j : Fin (n + 1)} {kk m₀ : Fin n}
    (hkk : i.succAbove kk = j) (hm₀ : j.succAbove m₀ = i) {z : Fin n → k} (hz : z m₀ ≠ 0) :
    (chartInv i (chart j z)) kk ≠ 0 := by
  obtain ⟨a, ha, hrep⟩ := chart_rep_eq_smul (k := k) j z
  have h1 : (chartInv i (chart j z)) kk = (chart j z).rep j / (chart j z).rep i := by
    simp only [chartInv, hkk]
  rw [h1, hrep]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show chartVec j z j = 1 from chartVec_apply_same j z,
    show chartVec j z i = z m₀ from by rw [← hm₀, chartVec_apply_succAbove], mul_one]
  exact div_ne_zero ha (mul_ne_zero ha hz)

/-- **The comparison of the two chart expressions.** If a polynomial `p` in the `i`-th chart
coordinates agrees with a polynomial `q` in the `j`-th chart coordinates on the overlap
(`y kk ≠ 0`, where `i.succAbove kk = j`), then `p` is a constant. -/
theorem chart_poly_const [IsAlgClosed k] {i j : Fin (n + 1)} (hij : i ≠ j)
    {p q : MvPolynomial (Fin n) k} {kk : Fin n} (hk : i.succAbove kk = j)
    (h : ∀ y : Fin n → k, y kk ≠ 0 →
      p.eval y = q.eval (fun m => chartVec i y (j.succAbove m) / chartVec i y j)) :
    ∃ c : k, p = MvPolynomial.C c := by
  classical
  have hji : j ≠ i := fun h' => hij h'.symm
  -- the `j`-chart coordinate that blows up at the boundary of the two charts
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Fin n, j.succAbove m₀ = i :=
    Fin.exists_succAbove_eq (x := i) (y := j) hij
  -- every line through a point of the `kk`-axis
  have key : ∀ a : Fin n → k, a kk ≠ 0 → ∀ u : k,
      p.eval (fun m => a m * u) = p.eval 0 := by
    intro a ha u
    set Φ : Polynomial k := lineSubst a p with hΦdef
    set c : Fin n → k := fun m => chartVec i a (j.succAbove m) / a kk with hcdef
    -- the `j`-chart coordinates along the rescaled line
    have hcoord : ∀ v : k, v ≠ 0 →
        (fun m => chartVec i (fun m => a m * v) (j.succAbove m)
            / chartVec i (fun m => a m * v) j)
          = (fun m => if m = m₀ then (v * a kk)⁻¹ else c m) := by
      intro v hv
      have hvj : chartVec i (fun m => a m * v) j = v * a kk := by
        rw [chartVec_mul, if_neg hji, ← hk, chartVec_apply_succAbove]
      funext m
      by_cases hm : m = m₀
      · subst hm
        rw [hm₀, if_pos rfl, hvj,
          show chartVec i (fun m => a m * v) i = 1 from by rw [chartVec_mul]; simp]
        exact one_div _
      · have hne : j.succAbove m ≠ i := by
          intro hc
          exact hm (Fin.succAbove_right_injective (hc.trans hm₀.symm))
        rw [hvj, chartVec_mul, if_neg hne, if_neg hm, hcdef]
        exact mul_div_mul_left _ _ hv
    -- the pointwise identity on the overlap
    have hpoint : ∀ v : k, v ≠ 0 → p.eval (fun m => a m * v)
        = q.eval (fun m => if m = m₀ then (v * a kk)⁻¹ else c m) := by
      intro v hv
      rw [h (fun m => a m * v) (mul_ne_zero ha hv), hcoord v hv]
    -- clearing denominators gives a polynomial identity
    have hpoly : Polynomial.C (a kk ^ q.totalDegree) * Polynomial.X ^ q.totalDegree * Φ
        = clearDenom q c m₀ (a kk) := by
      have hX : Polynomial.X * (Polynomial.C (a kk ^ q.totalDegree)
          * Polynomial.X ^ q.totalDegree * Φ - clearDenom q c m₀ (a kk)) = 0 := by
        refine Polynomial.funext fun v => ?_
        by_cases hv : v = 0
        · rw [hv, Polynomial.eval_mul, Polynomial.eval_X, zero_mul]
          simp
        · have h1 : Φ.eval v = p.eval (fun m => a m * v) := by
            rw [hΦdef]
            exact lineSubst_eval a p v
          have h2 : (clearDenom q c m₀ (a kk)).eval v
              = (v * a kk) ^ q.totalDegree
                * q.eval (fun m => if m = m₀ then (v * a kk)⁻¹ else c m) :=
            clearDenom_eval q c m₀ (a kk) v ha hv
          simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
            Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, h1, h2, hpoint v hv,
            mul_pow]
          ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hX).resolve_left Polynomial.X_ne_zero)
    -- hence the restriction to the line has degree zero
    have hΦeval : ∀ w : k, Φ.eval w = Φ.eval 0 := by
      intro w
      by_cases h0 : Φ = 0
      · rw [h0]
        simp
      · have hconst : Φ = Polynomial.C (Φ.coeff 0) := by
          by_contra hcon
          have hpos' : 0 < Φ.natDegree := by
            rcases Nat.eq_zero_or_pos Φ.natDegree with hh | hh
            · exact absurd (Polynomial.eq_C_of_natDegree_eq_zero hh) hcon
            · exact hh
          have hL : (Polynomial.C (a kk ^ q.totalDegree) * Polynomial.X ^ q.totalDegree
              * Φ).coeff (q.totalDegree + Φ.natDegree) ≠ 0 := by
            rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
            rw [if_pos (by omega : q.totalDegree ≤ q.totalDegree + Φ.natDegree),
              show q.totalDegree + Φ.natDegree - q.totalDegree = Φ.natDegree from by omega]
            exact mul_ne_zero (pow_ne_zero _ ha) (Polynomial.leadingCoeff_ne_zero.mpr h0)
          have hR : (clearDenom q c m₀ (a kk)).coeff (q.totalDegree + Φ.natDegree) = 0 :=
            clearDenom_coeff_eq_zero q c m₀ (a kk) hpos'
          rw [hpoly] at hL
          exact hL hR
        rw [hconst]
        simp
    calc p.eval (fun m => a m * u) = Φ.eval u := (lineSubst_eval a p u).symm
      _ = Φ.eval 0 := hΦeval u
      _ = p.eval 0 := lineSubst_eval_zero a p
  -- so `p` agrees with a constant on the nonempty basic open set `y kk ≠ 0`
  have hvan : ∀ y : Fin n → k, (MvPolynomial.X kk).eval y ≠ 0 →
      (p - MvPolynomial.C (p.eval 0)).eval y = 0 := by
    intro y hy
    have h1 : p.eval y = p.eval 0 := by
      have h2 := key y (by simpa using hy) 1
      simpa using h2
    simp [h1]
  have hzero : p - MvPolynomial.C (p.eval 0) = 0 :=
    eq_zero_of_forall_eval_eq_zero_on_basic (m := n) (g := p - MvPolynomial.C (p.eval 0))
      (h := MvPolynomial.X kk) (y := fun _ => 1) (by simp) hvan
  exact ⟨p.eval 0, sub_eq_zero.mp hzero⟩

/-! ## The exercise -/

/-- The quasi-projective set `P^n - (H_i ∩ H_j)`, where `H_i` is the hyperplane `X_i = 0`. -/
def twoHypCompl (i j : Fin (n + 1)) : Set (Proj k n) :=
  {P | ¬ (Proj.vanish (MvPolynomial.X i) P ∧ Proj.vanish (MvPolynomial.X j) P)}

theorem twoHypCompl_eq (i j : Fin (n + 1)) :
    twoHypCompl (k := k) i j
      = Set.univ \ (coordHyp (k := k) i ∩ coordHyp (k := k) j) := by
  ext P
  simp [twoHypCompl, coordHyp]

theorem isOpen_twoHypCompl (i j : Fin (n + 1)) : IsOpen (twoHypCompl (k := k) i j) := by
  rw [Proj.isOpen_iff]
  intro P hP
  by_cases hPi : Proj.vanish (MvPolynomial.X i) P
  · have hPj : ¬ Proj.vanish (MvPolynomial.X j) P := fun h => hP ⟨hPi, h⟩
    exact ⟨MvPolynomial.X j, 1, MvPolynomial.isHomogeneous_X k j, hPj,
      fun Q hQ hcon => hQ hcon.2⟩
  · exact ⟨MvPolynomial.X i, 1, MvPolynomial.isHomogeneous_X k i, hPi,
      fun Q hQ hcon => hQ hcon.1⟩

/-- **Hartshorne I.3.8.** Let `H_i`, `H_j` be the hyperplanes `X_i = 0`, `X_j = 0` in `P^n`,
with `i ≠ j`. Then every regular function on `P^n - (H_i ∩ H_j)` is constant. -/
theorem hartshorne_I_3_8 [IsAlgClosed k] {i j : Fin (n + 1)} (hij : i ≠ j)
    (f : Proj k n → k) (hf : IsRegularOn f (twoHypCompl (k := k) i j)) :
    ∃ c : k, ∀ P : Proj k n, P ∈ twoHypCompl (k := k) i j → f P = c := by
  classical
  obtain ⟨kk, hkk⟩ : ∃ kk : Fin n, i.succAbove kk = j :=
    Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  -- the regular function is a polynomial on each of the two charts
  obtain ⟨p, hp⟩ := exists_poly_on_chart (k := k) f i (U := twoHypCompl (k := k) i j)
    (fun P hP hcon => hP hcon.1) hf
  obtain ⟨q, hq⟩ := exists_poly_on_chart (k := k) f j (U := twoHypCompl (k := k) i j)
    (fun P hP hcon => hP hcon.2) hf
  -- the two polynomials agree on the overlap of the charts
  have hoverlap : ∀ y : Fin n → k, y kk ≠ 0 →
      p.eval y = q.eval (fun m => chartVec i y (j.succAbove m) / chartVec i y j) := by
    intro y hy
    have hvj : chartVec i y j = y kk := by rw [← hkk, chartVec_apply_succAbove]
    have hPj : ¬ Proj.vanish (MvPolynomial.X j) (chart i y) := by
      intro hcon
      have h0 : (MvPolynomial.X j).eval (chartVec i y) = 0 :=
        (chart_eval_eq_zero_iff (MvPolynomial.isHomogeneous_X k j) i y).mpr hcon
      rw [show (MvPolynomial.X j).eval (chartVec i y) = chartVec i y j from by simp, hvj] at h0
      exact hy h0
    calc p.eval y = f (chart i y) := (hp y).symm
      _ = q.eval (chartInv j (chart i y)) := by
          rw [← hq (chartInv j (chart i y)), chart_chartInv hPj]
      _ = q.eval (fun m => chartVec i y (j.succAbove m) / chartVec i y j) := by
          rw [show chartInv j (chart i y)
            = (fun m => chartVec i y (j.succAbove m) / chartVec i y j) from
            funext fun m => chartInv_chart_coord i j y m]
  obtain ⟨c, hc⟩ := chart_poly_const (k := k) hij hkk hoverlap
  -- and the same for the other chart, with the roles exchanged
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Fin n, j.succAbove m₀ = i :=
    Fin.exists_succAbove_eq (x := i) (y := j) hij
  have hoverlap' : ∀ y' : Fin n → k, y' m₀ ≠ 0 →
      q.eval y' = p.eval (fun m => chartVec j y' (i.succAbove m) / chartVec j y' i) := by
    intro y' hy'
    have hPi : ¬ Proj.vanish (MvPolynomial.X i) (chart j y') := by
      intro hcon
      have h0 : (MvPolynomial.X i).eval (chartVec j y') = 0 :=
        (chart_eval_eq_zero_iff (MvPolynomial.isHomogeneous_X k i) j y').mpr hcon
      rw [show (MvPolynomial.X i).eval (chartVec j y') = chartVec j y' i from by simp,
        show chartVec j y' i = y' m₀ from by rw [← hm₀, chartVec_apply_succAbove]] at h0
      exact hy' h0
    set y : Fin n → k := chartInv i (chart j y') with hydef
    have hchart : chart i y = chart j y' := by
      rw [hydef]
      exact chart_chartInv hPi
    have hykk : y kk ≠ 0 := chartInv_chart_chart_coord_ne_zero hkk hm₀ hy'
    have hσ : (fun m => chartVec i y (j.succAbove m) / chartVec i y j) = y' := by
      funext m
      have h3 := chartInv_chart_coord i j y m
      rw [hchart, hydef, chartInv_chart] at h3
      exact h3.symm
    have h2 : p.eval y = q.eval y' := by
      rw [hoverlap y hykk, hσ]
    rw [← h2, hydef]
    exact congrArg (fun w => p.eval w) (funext fun m => chartInv_chart_coord j i y' m)
  obtain ⟨c', hc'⟩ := chart_poly_const (k := k) (i := j) (j := i) hij.symm hm₀ hoverlap'
  -- the two constants agree at a point of the overlap
  have hcc : c = c' := by
    have h1 := hoverlap (fun _ => 1) (by simp)
    rw [hc, hc'] at h1
    simpa using h1
  refine ⟨c, fun P hP => ?_⟩
  by_cases hPi : Proj.vanish (MvPolynomial.X i) P
  · have hPj : ¬ Proj.vanish (MvPolynomial.X j) P := fun h => hP ⟨hPi, h⟩
    calc f P = f (chart j (chartInv j P)) := by rw [chart_chartInv hPj]
      _ = q.eval (chartInv j P) := hq (chartInv j P)
      _ = c := by
          rw [hc']
          simpa using hcc.symm
  · calc f P = f (chart i (chartInv i P)) := by rw [chart_chartInv hPi]
      _ = p.eval (chartInv i P) := hp (chartInv i P)
      _ = c := by
          rw [hc]
          simp

/-! ## The book's parenthetical remark: (3.4a) for `Y = P^n` -/

section ProjConst

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Restricting a regular function to a smaller open set. -/
theorem IsRegularOn.mono {f : Proj k n → k} {U U' : Set (Proj k n)} (hU' : IsOpen U')
    (hsub : U' ⊆ U) (hf : IsRegularOn f U) : IsRegularOn f U' := by
  intro P
  obtain ⟨d, A, B, hA, hB, hBP, V, hVopen, hPV, hVU, hVB⟩ := hf ⟨P.1, hsub P.2⟩
  exact ⟨d, A, B, hA, hB, hBP, V ∩ U', hVopen.inter hU', ⟨hPV, P.2⟩,
    fun Q hQ => hQ.2, fun Q hQ => hVB Q hQ.1⟩

/-- The point of `P^n` all of whose homogeneous coordinates are `1`. -/
def allOnes (n : ℕ) : Proj k n :=
  Projectivization.mk k (fun _ => 1) (by
    intro h
    have := congrFun h 0
    simp at this)

omit [IsAlgClosed k] in
theorem chartVec_one (i : Fin (n + 1)) : chartVec i (fun _ => (1 : k)) = fun _ => 1 := by
  funext ℓ
  by_cases hℓ : ℓ = i
  · rw [hℓ]
    exact chartVec_apply_same i _
  · conv_lhs => rw [← succAbove_chartEquiv_symm i ℓ hℓ]
    rw [chartVec_apply_succAbove]

omit [IsAlgClosed k] in
theorem chart_one_eq_allOnes (i : Fin (n + 1)) : chart i (fun _ => (1 : k)) = allOnes (k := k) n := by
  show Projectivization.mk k (chartVec i (fun _ => 1)) _ = Projectivization.mk k (fun _ => 1) _
  rw [Projectivization.mk_eq_mk_iff' k]
  refine ⟨1, ?_⟩
  rw [chartVec_one]
  simp

omit [IsAlgClosed k] in
theorem not_vanish_allOnes (i : Fin (n + 1)) : ¬ Proj.vanish (MvPolynomial.X i) (allOnes (k := k) n) := by
  rw [← chart_one_eq_allOnes i]
  exact chart_mem_chart i (fun _ => 1)

omit [IsAlgClosed k] in
theorem mem_twoHypCompl_allOnes (i j : Fin (n + 1)) :
    allOnes (k := k) n ∈ twoHypCompl (k := k) i j :=
  fun h => not_vanish_allOnes i h.1

/-- **Regular functions on `P^{m+1}` are constant**: the book's remark that I.3.8 gives an
alternative proof of (3.4a) in the case `Y = P^n`. -/
theorem regular_proj_const {m : ℕ} (f : Proj k (m + 1) → k)
    (hf : IsRegularOn f (Set.univ : Set (Proj k (m + 1)))) :
    ∃ c : k, ∀ P : Proj k (m + 1), f P = c := by
  classical
  have hconst : ∀ (i j : Fin (m + 2)), i ≠ j → ∀ P : Proj k (m + 1),
      P ∈ twoHypCompl (k := k) i j → f P = f (allOnes (k := k) (m + 1)) := by
    intro i j hij P hP
    obtain ⟨c, hc⟩ := hartshorne_I_3_8 (k := k) hij f
      (IsRegularOn.mono (isOpen_twoHypCompl i j) (Set.subset_univ _) hf)
    rw [hc P hP, hc _ (mem_twoHypCompl_allOnes i j)]
  refine ⟨f (allOnes (k := k) (m + 1)), fun P => ?_⟩
  have hne01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  by_cases hP : P ∈ twoHypCompl (k := k) (0 : Fin (m + 2)) 1
  · exact hconst 0 1 hne01 P hP
  · have h01 : Proj.vanish (MvPolynomial.X (0 : Fin (m + 2))) P ∧
        Proj.vanish (MvPolynomial.X (1 : Fin (m + 2))) P := by
      by_contra hcon
      exact hP hcon
    obtain ⟨r, hr⟩ : ∃ r : Fin (m + 2), ¬ Proj.vanish (MvPolynomial.X r) P := by
      by_contra hcon
      push Not at hcon
      apply Projectivization.rep_nonzero P
      funext ℓ
      simpa [Proj.vanish] using hcon ℓ
    have hr0 : r ≠ 0 := by
      intro h
      exact hr (h ▸ h01.1)
    exact hconst r 0 hr0 P (fun hcon => hr hcon.1)

end ProjConst

/-! ## Sharpness: the regular functions on `P^n - (H_i ∩ H_j)` are exactly the constants -/

theorem isRegular_const (c : k) : IsRegularOn (fun _ => c) (Set.univ : Set (Proj k n)) := by
  intro P
  refine ⟨0, MvPolynomial.C c, 1,
    MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) (R := k) c,
    isHomogeneous_one (σ := Fin (n + 1)) (R := k),
    by simp, Set.univ, isOpen_univ, trivial, Set.subset_univ _, ?_⟩
  intro Q _
  exact ⟨by simp, by simp⟩

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_3_8.lineSubst_eval
#print axioms Hartshorne77.Ex_I_3_8.prod_split
#print axioms Hartshorne77.Ex_I_3_8.clearDenom_eval
#print axioms Hartshorne77.Ex_I_3_8.clearDenom_coeff_eq_zero
#print axioms Hartshorne77.Ex_I_3_8.eq_zero_of_forall_eval_eq_zero_on_basic
#print axioms Hartshorne77.Ex_I_3_8.ideal_eq_top_of_no_common_zero
#print axioms Hartshorne77.Ex_I_3_8.exists_poly_of_locally_ratio
#print axioms Hartshorne77.Ex_I_3_8.exists_poly_on_chart
#print axioms Hartshorne77.Ex_I_3_8.chartInv_chart_chart_coord_ne_zero
#print axioms Hartshorne77.Ex_I_3_8.chart_poly_const
#print axioms Hartshorne77.Ex_I_3_8.isOpen_twoHypCompl
#print axioms Hartshorne77.Ex_I_3_8.isRegular_const
#print axioms Hartshorne77.Ex_I_3_8.IsRegularOn.mono
#print axioms Hartshorne77.Ex_I_3_8.hartshorne_I_3_8
#print axioms Hartshorne77.Ex_I_3_8.regular_proj_const
