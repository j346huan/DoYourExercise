import Mathlib

/-!
# Hartshorne (1977), *Algebraic Geometry*, Exercise I.3.6

Source statement (Hartshorne 1977, Chapter I, §3, Exercise 3.6, verbatim):

> "There are quasi-affine varieties which are not affine. For example, show that
> `X = A² - {(0,0)}` is not affine. [Hint: Show that `O(X) ≅ k[x,y]` and use (3.5).]"

Throughout, `k` is an algebraically closed field (Hartshorne's standing hypothesis for
varieties over `k` in Chapter I). We write `X = punctured = {(x₀,x₁) : k² | (x₀,x₁) ≠ 0}`
for `𝔸² \ {(0,0)}`, the quasi-affine variety of the exercise, and use the classical
point-set definitions of Chapter I:

* affine `n`-space `Aff n k` is `Fin n → k`; its Zariski topology is defined by taking the
  closed sets to be the zero loci `V(I)` of ideals `I` of `MvPolynomial (Fin n) k`
  (`Aff.IsZarClosed`, `Aff.instTopologicalSpace`); the basic open sets are
  `D(f) = {x | f(x) ≠ 0}` (`Aff.basicOpen`), and they form a basis
  (`Aff.isOpen_iff_eq_iUnion_basicOpen`).
* a function `f : X → k` on `X ⊆ 𝔸ⁿ` is regular at `x ∈ X` when there are an open
  neighbourhood `V ∋ x` and polynomials `g, h` with `h ≠ 0` on `V ∩ X` and `f = g/h` on
  `V ∩ X` (`Aff.IsLocQuotAt`); `f` is regular on `X` if it is regular at every point
  (`Aff.IsRegularOn`). Regular functions form a ring `Aff.regularSubring X`
  (`Γ(X, O_X)`).
* a morphism of quasi-affine varieties is a map all of whose coordinates are regular
  functions (`Aff.IsMorphismTo`), and an isomorphism is a pair of mutually inverse
  morphisms (`Aff.VarietyIso`); an affine variety is a nonempty closed irreducible subset
  of some `𝔸^m` (the hypotheses `IsClosed`, `Nonempty`, `PairwiseMeetOpens`).

## Clause-by-clause coverage

**(a) `O(X) ≅ k[x,y]`** (the hint).  Formalised as the ring isomorphism
`Aff.gammaPuncturedEquiv : MvPolynomial (Fin 2) k ≃+* regularSubring punctured`:
* polynomial functions are regular: `Aff.polyToRegular`;
* *every* regular function on `X` is a polynomial:
  `Aff.exists_poly_of_isRegularOn_punctured` (hence `polyToRegular` is onto, and it is
  injective because a polynomial vanishing on the nonempty open set `X` is zero).

The proof of `Aff.exists_poly_of_isRegularOn_punctured` is self-contained:
1. `Aff.exists_poly_mul_eq` (patching): on an open set whose nonempty pieces meet pairwise,
   a regular function satisfies `f · H = G` with `H ≠ 0`, obtained from a finite cover by
   basic opens (Noetherianity of `k[x,y]`) by multiplying local denominators
   (`H = ∏ h_i`, `G = g_i ∏_{j≠i} h_j`), the `G_i` being equal because they agree on the
   nonempty intersections.
2. `J = {c | H ∣ c·G}` is an ideal containing the local denominators, so `V(J) ∩ X = ∅`;
   hence `V(J) ⊆ {0}` and, by the Nullstellensatz
   (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), `X₀ ∈ √J`, i.e. `X₀^m ∈ J`, so
   `f·X₀^m = Q` for a polynomial `Q`.
3. `Aff.exists_poly_of_mul_pow_X` removes the power of `X₀` inductively: at every nonzero
   point with `X₀ = 0` the relation forces `Q` to vanish, so `X₀ ∣ Q`
   (`Aff.coordX_dvd_of_forall_eval_zero`, proved via `finSuccEquiv`), and on `D(X₀)` the
   power drops by one; locality (`Aff.IsRegularOn.eq_of_eqOn_isOpen`) spreads the identity.
4. The key lemma used throughout, `Aff.exists_C_of_forall_ne_zero_aeval_ne_zero`: a
   polynomial in two variables over an algebraically closed field with no zero off the
   origin is constant. (If `p` has no nonzero zero, then for every `a ≠ 0` the one-variable
   polynomial `t ↦ p(t,a)` has no root, hence is constant; the substitution argument then
   gives `p = p(0,X₁)`, and the one-variable polynomial `p(0,X₁)` has no root except
   possibly `0`, so `p` is constant.)

**(b) `X` is not affine.**  Formalised as
`Aff.punctured_not_affine : ¬ ∃ (m) (Y ⊆ 𝔸^m), IsClosed Y ∧ Y.Nonempty ∧
PairwiseMeetOpens Y ∧ Nonempty (VarietyIso punctured Y)`.
The proof is exactly the book's argument ("if `X` were affine, the inclusion `X → 𝔸²`, whose
pullback is this isomorphism, would be an isomorphism"):
* regular functions on an affine variety are polynomial functions,
  `Aff.exists_poly_of_isRegularOn_affine` (same patching as in (a), but the denominator
  ideal is taken modulo `I(Y)`, and the Nullstellensatz gives `j ∈ J` with `j = 1` on `Y`);
* hence the coordinates of a morphism `X → Y` and of a morphism `Y → X` are given by
  polynomials `Q : Fin m → k[x₀,x₁]` and `P : Fin 2 → k[y₁..y_m]`, and the identity
  `invFun ∘ toFun = id` forces the substitution `y_i ↦ Q_i` to invert `P`
  (`σ (P j) = x_j`, `hkey` in `Aff.punctured_not_affine`);
* if `P 0` and `P 1` had no common zero on `Y`, then `I(Y) + (P 0, P 1) = ⊤`
  (Nullstellensatz); substituting `y_i ↦ Q_i` would give `1 ∈ (x₀, x₁)`, impossible; so
  there is `y ∈ Y` with `P 0(y) = P 1(y) = 0`, i.e. `invFun y = (0,0) ∉ X`, contradiction.

Only `Mathlib` is imported; no later Hartshorne exercise (in particular not I.3.5) is used.
-/

namespace Hartshorne77.Ex_I_3_6

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open MvPolynomial

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Affine `n`-space over `k`: the set of `k`-points `k^n`. -/
abbrev Aff (n : ℕ) (k : Type*) : Type _ := Fin n → k

namespace Aff

section Topology

variable {n : ℕ}

/-- Zero locus of a set of polynomials. -/
def zeroLocusSet (S : Set (MvPolynomial (Fin n) k)) : Set (Aff n k) :=
  {x | ∀ p ∈ S, aeval x p = 0}

theorem zeroLocusSet_eq_zeroLocus (S : Set (MvPolynomial (Fin n) k)) :
    zeroLocusSet (k := k) S = MvPolynomial.zeroLocus k (Ideal.span S) := by
  rw [MvPolynomial.zeroLocus_span]
  rfl

/-- A subset of `k^n` is Zariski closed when it is the zero locus of an ideal. -/
def IsZarClosed (Z : Set (Aff n k)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) k), Z = MvPolynomial.zeroLocus k I

theorem isZarClosed_empty : IsZarClosed (k := k) (∅ : Set (Aff n k)) :=
  ⟨⊤, MvPolynomial.zeroLocus_top.symm⟩

theorem isZarClosed_univ : IsZarClosed (k := k) (Set.univ : Set (Aff n k)) :=
  ⟨⊥, MvPolynomial.zeroLocus_bot.symm⟩

theorem isZarClosed_sInter {S : Set (Set (Aff n k))}
    (hS : ∀ Z ∈ S, IsZarClosed (k := k) Z) : IsZarClosed (k := k) (⋂₀ S) := by
  choose I hI using hS
  refine ⟨Ideal.span (⋃ Z : S, (I Z.1 Z.2 : Set (MvPolynomial (Fin n) k))), ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext x
  rw [Set.mem_sInter]
  constructor
  · intro h p hp
    obtain ⟨Z, hpZ⟩ := Set.mem_iUnion.mp hp
    have hx : x ∈ Z.1 := h Z.1 Z.2
    rw [hI Z.1 Z.2] at hx
    exact hx p hpZ
  · intro h Z hZ
    rw [hI Z hZ]
    intro p hp
    exact h p (Set.mem_iUnion.mpr ⟨⟨Z, hZ⟩, hp⟩)

theorem isZarClosed_union {Z W : Set (Aff n k)} (hZ : IsZarClosed (k := k) Z)
    (hW : IsZarClosed (k := k) W) : IsZarClosed (k := k) (Z ∪ W) := by
  obtain ⟨I, rfl⟩ := hZ
  obtain ⟨J, rfl⟩ := hW
  refine ⟨I * J, ?_⟩
  ext x
  constructor
  · rintro (h | h) p hp
    · exact h p (Ideal.mul_le_left hp)
    · exact h p (Ideal.mul_le_right hp)
  · intro h
    by_contra hx
    rw [Set.mem_union, not_or] at hx
    obtain ⟨hxI, hxJ⟩ := hx
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at hxI hxJ
    obtain ⟨p, hpI, hpx⟩ := hxI
    obtain ⟨q, hqJ, hqx⟩ := hxJ
    have hne : aeval x (p * q) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hpx hqx
    exact hne (h (p * q) (Ideal.mul_mem_mul hpI hqJ))

instance : TopologicalSpace (Aff n k) :=
  TopologicalSpace.ofClosed {Z : Set (Aff n k) | IsZarClosed (k := k) Z}
    isZarClosed_empty (fun S hS => isZarClosed_sInter hS)
    (fun _ hZ _ hW => isZarClosed_union hZ hW)

theorem isOpen_iff_compl_isZarClosed (U : Set (Aff n k)) :
    IsOpen U ↔ IsZarClosed (k := k) Uᶜ := Iff.rfl

theorem isClosed_iff_isZarClosed (Z : Set (Aff n k)) : IsClosed Z ↔ IsZarClosed (k := k) Z := by
  rw [← isOpen_compl_iff, isOpen_iff_compl_isZarClosed, compl_compl]

/-- The basic (distinguished) open set `D(f) = {x | f x ≠ 0}`. -/
def basicOpen (f : MvPolynomial (Fin n) k) : Set (Aff n k) := {x | aeval x f ≠ 0}

theorem basicOpen_isOpen (f : MvPolynomial (Fin n) k) : IsOpen (basicOpen (k := k) f) := by
  rw [isOpen_iff_compl_isZarClosed]
  refine ⟨Ideal.span {f}, ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp [basicOpen, eq_comm]

theorem exists_basicOpen_subset_of_isOpen {U : Set (Aff n k)} (hU : IsOpen U) {x : Aff n k}
    (hx : x ∈ U) : ∃ f : MvPolynomial (Fin n) k, aeval x f ≠ 0 ∧ basicOpen (k := k) f ⊆ U := by
  rw [isOpen_iff_compl_isZarClosed] at hU
  obtain ⟨I, hI⟩ := hU
  have hx' : x ∉ MvPolynomial.zeroLocus k I := by
    rw [← hI]
    simpa using hx
  simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at hx'
  obtain ⟨f, hfI, hfx⟩ := hx'
  refine ⟨f, hfx, ?_⟩
  intro y hy
  have hy' : y ∉ Uᶜ := by
    rw [hI]
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall]
    exact ⟨f, hfI, hy⟩
  simpa using hy'

/-- Every open subset of `k^n` is a union of basic open sets. -/
theorem isOpen_iff_eq_iUnion_basicOpen (U : Set (Aff n k)) :
    IsOpen U ↔ ∃ S : Set (MvPolynomial (Fin n) k), U = ⋃ f ∈ S, basicOpen (k := k) f := by
  constructor
  · intro hU
    rw [isOpen_iff_compl_isZarClosed] at hU
    obtain ⟨I, hI⟩ := hU
    refine ⟨I, ?_⟩
    ext x
    have hx : x ∈ U ↔ x ∉ MvPolynomial.zeroLocus k I := by
      rw [show x ∉ MvPolynomial.zeroLocus k I ↔ x ∈ U from by rw [← hI, Set.notMem_compl_iff]]
    rw [hx]
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall, Set.mem_iUnion, exists_prop, basicOpen]
    exact ⟨fun ⟨f, hfI, hfx⟩ => ⟨f, hfI, hfx⟩, fun ⟨f, hfI, hfx⟩ => ⟨f, hfI, hfx⟩⟩
  · rintro ⟨S, rfl⟩
    exact isOpen_iUnion fun f => isOpen_iUnion fun _ => basicOpen_isOpen f

/-! ## Polynomials versus functions -/

theorem eq_zero_of_forall_eval_eq_zero {p : MvPolynomial (Fin n) k}
    (h : ∀ x : Aff n k, MvPolynomial.eval x p = 0) : p = 0 := by
  refine MvPolynomial.funext (q := 0) (fun x => ?_)
  rw [h x, map_zero]

theorem eq_zero_of_forall_aeval_eq_zero {p : MvPolynomial (Fin n) k}
    (h : ∀ x : Aff n k, aeval x p = 0) : p = 0 := by
  apply eq_zero_of_forall_eval_eq_zero
  intro x
  rw [← MvPolynomial.aeval_eq_eval]
  exact h x

theorem exists_aeval_ne_zero {p : MvPolynomial (Fin n) k} (hp : p ≠ 0) :
    ∃ x : Aff n k, aeval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (eq_zero_of_forall_aeval_eq_zero h)

theorem exists_aeval_ne_zero_and {f g : MvPolynomial (Fin n) k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ x : Aff n k, aeval x f ≠ 0 ∧ aeval x g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_aeval_ne_zero (mul_ne_zero hf hg)
  rw [map_mul] at hx
  exact ⟨x, fun h => hx (by rw [h, zero_mul]), fun h => hx (by rw [h, mul_zero])⟩

/-- A polynomial vanishing on a nonempty open subset of `k^n` is zero. -/
theorem eq_zero_of_eq_zero_on_isOpen {q : MvPolynomial (Fin n) k} {W : Set (Aff n k)}
    (hW : IsOpen W) (hne : W.Nonempty) (h : ∀ x ∈ W, aeval x q = 0) : q = 0 := by
  by_contra hq
  obtain ⟨x, hxW⟩ := hne
  obtain ⟨f, hfx, hfW⟩ := exists_basicOpen_subset_of_isOpen hW hxW
  have hf0 : f ≠ 0 := fun h0 => hfx (by rw [h0]; simp)
  obtain ⟨y, hyf, hyq⟩ := exists_aeval_ne_zero_and hf0 hq
  exact hyq (h y (hfW hyf))

/-- Two polynomials with the same values on a nonempty open set are equal. -/
theorem eq_of_eq_on_isOpen {q p : MvPolynomial (Fin n) k} {W : Set (Aff n k)}
    (hW : IsOpen W) (hne : W.Nonempty) (h : ∀ x ∈ W, aeval x q = aeval x p) : q = p := by
  by_contra hne'
  have h0 : q - p = 0 := by
    refine eq_zero_of_eq_zero_on_isOpen hW hne ?_
    intro x hx
    rw [map_sub, h x hx, sub_self]
  exact hne' (sub_eq_zero.mp h0)

end Topology

/-! ## Irreducibility -/

section Irred

variable {n : ℕ}

/-- Any two nonempty relatively open subsets of `X` meet. -/
def PairwiseMeetOpens (X : Set (Aff n k)) : Prop :=
  ∀ V W : Set (Aff n k), IsOpen V → IsOpen W → (V ∩ X).Nonempty → (W ∩ X).Nonempty →
    (V ∩ W ∩ X).Nonempty

theorem pairwiseMeetOpens_of_basic {X : Set (Aff n k)}
    (h : ∀ f g : MvPolynomial (Fin n) k, (basicOpen (k := k) f ∩ X).Nonempty →
      (basicOpen g ∩ X).Nonempty → (basicOpen f ∩ basicOpen g ∩ X).Nonempty) :
    PairwiseMeetOpens X := by
  intro V W hV hW hVX hWX
  obtain ⟨x, hx⟩ := hVX
  obtain ⟨f, hfx, hfV⟩ := exists_basicOpen_subset_of_isOpen hV hx.1
  obtain ⟨y, hy⟩ := hWX
  obtain ⟨g, hgy, hgW⟩ := exists_basicOpen_subset_of_isOpen hW hy.1
  obtain ⟨z, ⟨⟨hzf, hzg⟩, hzX⟩⟩ := h f g ⟨x, hfx, hx.2⟩ ⟨y, hgy, hy.2⟩
  exact ⟨z, ⟨⟨hfV hzf, hgW hzg⟩, hzX⟩⟩

/-- In a space where nonempty relatively open pieces pairwise meet, a finite product of
polynomials each nonzero somewhere on `X` is nonzero somewhere on `X`. -/
theorem exists_aeval_ne_zero_prod {X : Set (Aff n k)} (hmeet : PairwiseMeetOpens X)
    (hXne : X.Nonempty) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → MvPolynomial (Fin n) k)
    (h : ∀ i ∈ s, ∃ x : X, aeval x.1 (F i) ≠ 0) :
    ∃ x : X, aeval x.1 (∏ i ∈ s, F i) ≠ 0 := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx⟩ := hXne
    exact ⟨⟨x, hx⟩, by simp⟩
  | insert a s ha ih =>
    obtain ⟨x₁, hx₁⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨x₂, hx₂⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := hmeet _ _
      (basicOpen_isOpen (F a)) (basicOpen_isOpen (∏ i ∈ s, F i))
      ⟨x₂.1, hx₂, x₂.2⟩ ⟨x₁.1, hx₁, x₁.2⟩
    refine ⟨⟨z, hz3⟩, ?_⟩
    rw [Finset.prod_insert ha, map_mul]
    exact mul_ne_zero hz1 hz2

end Irred

end Aff

/-! ## Substitution and evaluation lemmas -/

noncomputable section

section Compat

variable {n : ℕ}

/-- Evaluating a polynomial with polynomial coefficients at a point. -/
theorem eval_aeval (t : k) (g : Fin n → Polynomial k) (p : MvPolynomial (Fin n) k) :
    (aeval g p).eval t = aeval (fun i => (g i).eval t) p := by
  have key := MvPolynomial.hom_eq_hom
    ((Polynomial.evalRingHom t).comp (MvPolynomial.aeval g).toRingHom)
    (MvPolynomial.aeval (fun i => (g i).eval t)).toRingHom
    (by ext a; simp) (by intro i; simp) p
  simpa using key

/-- Substitution of polynomials into polynomials. -/
theorem aeval_aeval {σ τ : Type*} (x : τ → k) (g : σ → MvPolynomial τ k)
    (p : MvPolynomial σ k) :
    aeval x (aeval g p) = aeval (fun i => aeval x (g i)) p := by
  have key := MvPolynomial.hom_eq_hom
    ((MvPolynomial.aeval x).toRingHom.comp (MvPolynomial.aeval g).toRingHom)
    (MvPolynomial.aeval (fun i => aeval x (g i))).toRingHom
    (by ext a; simp) (by intro i; simp) p
  simpa using key

end Compat

/-- A polynomial in one variable over an algebraically closed field with no roots is
a constant. -/
theorem Polynomial.eq_C_of_forall_not_isRoot {P : Polynomial k} (h : ∀ t, ¬ P.IsRoot t) :
    P = Polynomial.C (P.coeff 0) := by
  rw [← Polynomial.degree_le_zero_iff]
  by_contra hdeg
  simp only [not_le] at hdeg
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root P (ne_of_gt hdeg)
  exact h s hs

namespace Aff

/-! ## Polynomials in two variables with no zeros off the origin -/

/-- A point of `k²` is determined by its two coordinates. -/
theorem aff2_eq_cons (x : Aff 2 k) : x = ![x 0, x 1] := by
  funext i
  fin_cases i <;> rfl

theorem cons₂_ne_zero_of_second {a b : k} (hb : b ≠ 0) : (![a, b] : Aff 2 k) ≠ 0 := by
  intro h
  exact hb (by have := congrFun h 1; simpa using this)

theorem cons₂_ne_zero_of_first {a b : k} (ha : a ≠ 0) : (![a, b] : Aff 2 k) ≠ 0 := by
  intro h
  exact ha (by have := congrFun h 0; simpa using this)

/-- The tuple `(X, C a)` of one-variable polynomials. -/
def tupleX (a : k) : Fin 2 → Polynomial k := ![Polynomial.X, Polynomial.C a]

/-- The tuple `(C 0, X)`: the substitution `X₀ ↦ 0`, `X₁ ↦ X` into one variable. -/
def tuple0X : Fin 2 → Polynomial k := ![Polynomial.C 0, Polynomial.X]

/-- The substitution `X₀ ↦ 0`, `X₁ ↦ X₁` of two-variable polynomials. -/
def subst0 : Fin 2 → MvPolynomial (Fin 2) k := ![MvPolynomial.C 0, MvPolynomial.X 1]

@[simp] theorem tupleX_zero (a : k) : tupleX a 0 = Polynomial.X := rfl
@[simp] theorem tupleX_one (a : k) : tupleX a 1 = Polynomial.C a := rfl
@[simp] theorem tuple0X_zero : tuple0X (k := k) 0 = Polynomial.C 0 := rfl
@[simp] theorem tuple0X_one : tuple0X (k := k) 1 = Polynomial.X := rfl
@[simp] theorem subst0_zero : subst0 (k := k) 0 = MvPolynomial.C 0 := rfl
@[simp] theorem subst0_one : subst0 (k := k) 1 = MvPolynomial.X 1 := rfl

/-- **Key lemma.** A polynomial in two variables over an algebraically closed field that
vanishes at no point other than the origin is a constant. -/
theorem exists_C_of_forall_ne_zero_aeval_ne_zero {p : MvPolynomial (Fin 2) k}
    (h : ∀ x : Aff 2 k, x ≠ 0 → aeval x p ≠ 0) : ∃ c : k, p = MvPolynomial.C c := by
  -- Step 1: on every horizontal line `Y = a` with `a ≠ 0` the function `t ↦ p (t,a)` is constant.
  have hconst : ∀ a : k, a ≠ 0 → ∀ t : k, aeval ![t, a] p = aeval ![0, a] p := by
    intro a ha t
    set P : Polynomial k := aeval (tupleX a) p with hP
    have htuple : ∀ s : k, (fun i : Fin 2 => (tupleX a i).eval s) = ![s, a] := by
      intro s
      funext i
      fin_cases i <;> simp
    have hev : ∀ s : k, P.eval s = aeval ![s, a] p := by
      intro s
      rw [hP, eval_aeval, htuple s]
    have hno : ∀ s : k, ¬ P.IsRoot s := by
      intro s hs
      rw [Polynomial.IsRoot, hev s] at hs
      exact h ![s, a] (cons₂_ne_zero_of_second ha) hs
    have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_forall_not_isRoot hno
    rw [← hev t, ← hev 0, hPC]
    simp
  -- Step 2: `p` does not involve the first variable: `p = p(0, X₁)`.
  have hp_eq : p = aeval (subst0 (k := k)) p := by
    have hsub : p - aeval (subst0 (k := k)) p = 0 := by
      refine eq_zero_of_eq_zero_on_isOpen (W := basicOpen (MvPolynomial.X (1 : Fin 2)))
        (basicOpen_isOpen _) ⟨(![0, 1] : Aff 2 k), by simp [basicOpen]⟩ ?_
      intro x hx
      have ha : x 1 ≠ 0 := by simpa [basicOpen] using hx
      have htuple : (fun i : Fin 2 => aeval x (subst0 (k := k) i)) = ![0, x 1] := by
        funext i
        fin_cases i <;> simp
      rw [map_sub, aeval_aeval, htuple, sub_eq_zero, aff2_eq_cons x]
      exact hconst (x 1) ha (x 0)
    exact sub_eq_zero.mp hsub
  -- Step 3: reduce to a polynomial in one variable and conclude.
  set q : Polynomial k := aeval (tuple0X (k := k)) p with hq
  have hevq : ∀ b : k, q.eval b = aeval ![0, b] p := by
    intro b
    have htuple : (fun i : Fin 2 => (tuple0X (k := k) i).eval b) = ![0, b] := by
      funext i
      fin_cases i <;> simp
    rw [hq, eval_aeval, htuple]
  have hqconst : q = Polynomial.C (q.coeff 0) := by
    rw [← Polynomial.degree_le_zero_iff]
    by_contra hdeg
    simp only [not_le] at hdeg
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_root q (ne_of_gt hdeg)
    have hb0 : aeval ![0, b] p = 0 := by rw [← hevq b]; exact hb
    have hb_eq : b = 0 := by
      by_contra hbne
      exact h ![0, b] (cons₂_ne_zero_of_second hbne) hb0
    subst hb_eq
    -- now `q 0 = 0`, i.e. `p` vanishes at `(0,0)`, hence at `(1,0)`
    have h10 : aeval (![1, 0] : Aff 2 k) p = 0 := by
      have hσ : aeval (![1, 0] : Aff 2 k) (aeval (subst0 (k := k)) p)
          = aeval (![0, 0] : Aff 2 k) p := by
        have htuple : (fun i : Fin 2 => aeval (![1, 0] : Aff 2 k) (subst0 (k := k) i))
            = (![0, 0] : Aff 2 k) := by
          funext i
          fin_cases i <;> simp
        rw [aeval_aeval, htuple]
      rw [hp_eq, hσ]
      exact hb0
    exact h (![1, 0] : Aff 2 k) (cons₂_ne_zero_of_first one_ne_zero) h10
  refine ⟨q.coeff 0, ?_⟩
  refine MvPolynomial.funext (q := MvPolynomial.C (q.coeff 0)) (fun x => ?_)
  have hpv : aeval ![x 0, x 1] p = q.eval (x 1) := by
    have hσ : aeval ![x 0, x 1] (aeval (subst0 (k := k)) p) = aeval ![0, x 1] p := by
      have htuple : (fun i : Fin 2 => aeval ![x 0, x 1] (subst0 (k := k) i)) = ![0, x 1] := by
        funext i
        fin_cases i <;> simp
      rw [aeval_aeval, htuple]
    rw [hp_eq, hσ, hevq]
  have hxv : MvPolynomial.eval x p = aeval ![x 0, x 1] p := by
    rw [MvPolynomial.aeval_eq_eval]
    exact congrArg (fun y => MvPolynomial.eval y p) (aff2_eq_cons x)
  have hqev : q.eval (x 1) = q.coeff 0 := by
    nth_rewrite 1 [hqconst]
    rw [Polynomial.eval_C]
  rw [hxv, hpv, hqev, MvPolynomial.eval_C]

end Aff

/-! ## Regular functions on a subset of `k^n` -/

namespace Aff

variable {n : ℕ}

/-- `f` is, near `x`, a quotient of two polynomials with nonvanishing denominator on a
neighbourhood of `x` inside `X`: Hartshorne's notion of a function regular at `x`. -/
def IsLocQuotAt (X : Set (Aff n k)) (f : X → k) (x : X) : Prop :=
  ∃ (V : Set (Aff n k)) (g h : MvPolynomial (Fin n) k),
    IsOpen V ∧ x.1 ∈ V ∧ (∀ (y : Aff n k), y ∈ V → y ∈ X → aeval y h ≠ 0) ∧
      (∀ (y : Aff n k), y ∈ V → (hyX : y ∈ X) → f ⟨y, hyX⟩ = aeval y g / aeval y h)

/-- A function is regular on `X` if it is regular at every point of `X`. -/
def IsRegularOn (X : Set (Aff n k)) (f : X → k) : Prop := ∀ x : X, IsLocQuotAt X f x

theorem mem_inter₁ {α : Type*} {s t : Set α} {x : α} (h : x ∈ s ∩ t) : x ∈ s :=
  (Set.mem_inter_iff x s t).mp h |>.1

theorem mem_inter₂ {α : Type*} {s t : Set α} {x : α} (h : x ∈ s ∩ t) : x ∈ t :=
  (Set.mem_inter_iff x s t).mp h |>.2

theorem isLocQuotAt_add {X : Set (Aff n k)} {f g : X → k} {x : X}
    (hf : IsLocQuotAt X f x) (hg : IsLocQuotAt X g x) : IsLocQuotAt X (f + g) x := by
  obtain ⟨V₁, a₁, b₁, hV₁, hx₁, hb₁, he₁⟩ := hf
  obtain ⟨V₂, a₂, b₂, hV₂, hx₂, hb₂, he₂⟩ := hg
  refine ⟨V₁ ∩ V₂, a₁ * b₂ + a₂ * b₁, b₁ * b₂, hV₁.inter hV₂, ⟨hx₁, hx₂⟩, ?_, ?_⟩
  · intro y hy hyX
    have hy₁ := mem_inter₁ hy
    have hy₂ := mem_inter₂ hy
    simp only [map_mul]
    exact mul_ne_zero (hb₁ y hy₁ hyX) (hb₂ y hy₂ hyX)
  · intro y hy hyX
    have hy₁ := mem_inter₁ hy
    have hy₂ := mem_inter₂ hy
    have h1 := he₁ y hy₁ hyX
    have h2 := he₂ y hy₂ hyX
    have hb1 : aeval y b₁ ≠ 0 := hb₁ y hy₁ hyX
    have hb2 : aeval y b₂ ≠ 0 := hb₂ y hy₂ hyX
    simp only [Pi.add_apply, h1, h2, map_mul, map_add]
    field_simp

theorem isLocQuotAt_mul {X : Set (Aff n k)} {f g : X → k} {x : X}
    (hf : IsLocQuotAt X f x) (hg : IsLocQuotAt X g x) : IsLocQuotAt X (f * g) x := by
  obtain ⟨V₁, a₁, b₁, hV₁, hx₁, hb₁, he₁⟩ := hf
  obtain ⟨V₂, a₂, b₂, hV₂, hx₂, hb₂, he₂⟩ := hg
  refine ⟨V₁ ∩ V₂, a₁ * a₂, b₁ * b₂, hV₁.inter hV₂, ⟨hx₁, hx₂⟩, ?_, ?_⟩
  · intro y hy hyX
    have hy₁ := mem_inter₁ hy
    have hy₂ := mem_inter₂ hy
    simp only [map_mul]
    exact mul_ne_zero (hb₁ y hy₁ hyX) (hb₂ y hy₂ hyX)
  · intro y hy hyX
    have hy₁ := mem_inter₁ hy
    have hy₂ := mem_inter₂ hy
    have h1 := he₁ y hy₁ hyX
    have h2 := he₂ y hy₂ hyX
    simp only [Pi.mul_apply, h1, h2, map_mul]
    rw [div_mul_div_comm]

theorem isLocQuotAt_neg {X : Set (Aff n k)} {f : X → k} {x : X}
    (hf : IsLocQuotAt X f x) : IsLocQuotAt X (-f) x := by
  obtain ⟨V, a, b, hV, hx, hb, he⟩ := hf
  refine ⟨V, -a, b, hV, hx, hb, ?_⟩
  intro y hyV hyX
  have h1 := he y hyV hyX
  simp only [Pi.neg_apply, h1, map_neg, neg_div]

theorem isLocQuotAt_zero (X : Set (Aff n k)) (x : X) : IsLocQuotAt X 0 x := by
  refine ⟨Set.univ, 0, 1, isOpen_univ, trivial, ?_, ?_⟩
  · intro y _ _
    simp
  · intro y _ hyX
    simp

theorem isLocQuotAt_one (X : Set (Aff n k)) (x : X) : IsLocQuotAt X 1 x := by
  refine ⟨Set.univ, 1, 1, isOpen_univ, trivial, ?_, ?_⟩
  · intro y _ _
    simp
  · intro y _ hyX
    simp

/-- Regular functions on `X` form a subring of all functions `X → k`. -/
def regularSubring (X : Set (Aff n k)) : Subring (X → k) where
  carrier := {f | IsRegularOn X f}
  add_mem' hf hg := fun x => isLocQuotAt_add (hf x) (hg x)
  mul_mem' hf hg := fun x => isLocQuotAt_mul (hf x) (hg x)
  neg_mem' hf := fun x => isLocQuotAt_neg (hf x)
  zero_mem' := fun x => isLocQuotAt_zero X x
  one_mem' := fun x => isLocQuotAt_one X x

/-- Polynomial functions are regular. -/
theorem isRegularOn_poly (X : Set (Aff n k)) (p : MvPolynomial (Fin n) k) :
    IsRegularOn X (fun x => aeval x.1 p) := by
  intro x
  refine ⟨Set.univ, p, 1, isOpen_univ, trivial, ?_, ?_⟩
  · intro y _ _
    simp
  · intro y _ hyX
    simp

theorem IsRegularOn.congr {X : Set (Aff n k)} {f g : X → k} (h : ∀ x, f x = g x)
    (hf : IsRegularOn X f) : IsRegularOn X g := by
  intro x
  obtain ⟨V, a, b, hV, hx, hb, he⟩ := hf x
  exact ⟨V, a, b, hV, hx, hb, fun y hyV hyX => by rw [← h, he y hyV hyX]⟩

/-- Regularity is a local property. -/
theorem isRegularOn_of_locally {X : Set (Aff n k)} {f : X → k}
    (h : ∀ x : X, ∃ V : Set (Aff n k), IsOpen V ∧ x.1 ∈ V ∧
      IsRegularOn (V ∩ X) (fun y : ↥(V ∩ X) => f ⟨y.1, mem_inter₂ y.2⟩)) : IsRegularOn X f := by
  intro x
  obtain ⟨V, hV, hxV, hreg⟩ := h x
  have hxVX : x.1 ∈ V ∩ X := ⟨hxV, x.2⟩
  obtain ⟨W, a, b, hW, hxW, hb, he⟩ := hreg ⟨x.1, hxVX⟩
  refine ⟨W ∩ V, a, b, hW.inter hV, ⟨hxW, hxV⟩, ?_, ?_⟩
  · intro y hyV hyX
    exact hb y (mem_inter₁ hyV) ⟨mem_inter₂ hyV, hyX⟩
  · intro y hyV hyX
    exact he y (mem_inter₁ hyV) ⟨mem_inter₂ hyV, hyX⟩

end Aff

/-! ## A single polynomial relation for a regular function -/

namespace Aff

variable {n : ℕ}

/-- **Key patching lemma.** On an open set whose nonempty relatively open pieces pairwise meet,
a regular function satisfies a polynomial relation `f · H = G` with `H ≠ 0`. -/
theorem exists_poly_mul_eq {X : Set (Aff n k)} (hXne : X.Nonempty)
    (hmeet : PairwiseMeetOpens X)
    (hvanish : ∀ (q : MvPolynomial (Fin n) k) (W : Set (Aff n k)), IsOpen W →
      (W ∩ X).Nonempty → (∀ x ∈ W ∩ X, aeval x q = 0) → ∀ x ∈ X, aeval x q = 0)
    {f : X → k} (hf : IsRegularOn X f) :
    ∃ G H : MvPolynomial (Fin n) k, H ≠ 0 ∧ (∃ x : X, aeval x.1 H ≠ 0) ∧
      ∀ x : X, f x * aeval x.1 H = aeval x.1 G := by
  classical
  -- Step 1: each point has a basic open neighbourhood on which `f` is a quotient
  have hex : ∀ x : X, ∃ w g h : MvPolynomial (Fin n) k, aeval x.1 w ≠ 0 ∧
      (∀ (y : Aff n k), y ∈ basicOpen (k := k) w → y ∈ X → aeval y h ≠ 0) ∧
      (∀ (y : Aff n k), y ∈ basicOpen (k := k) w → (hyX : y ∈ X) →
        f ⟨y, hyX⟩ = aeval y g / aeval y h) := by
    intro x
    obtain ⟨V, g, h, hV, hxV, hh, he⟩ := hf x
    obtain ⟨w, hwx, hwV⟩ := exists_basicOpen_subset_of_isOpen hV hxV
    exact ⟨w, g, h, hwx, fun y hy hyX => hh y (hwV hy) hyX,
      fun y hy hyX => he y (hwV hy) hyX⟩
  choose w g h hw hh he using hex
  -- Step 2: finitely many denominators already cover `X`
  have : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  obtain ⟨t, ht_sub, ht_span⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range w)).mp
      (Ideal.fg_of_isNoetherianRing (I := Ideal.span (Set.range w)))
  have ht_mem : ∀ q : MvPolynomial (Fin n) k, q ∈ t → ∃ x : X, w x = q := by
    intro q hq
    exact ht_sub (by simpa using hq)
  let Xq : MvPolynomial (Fin n) k → X := fun q =>
    if h : q ∈ t then Classical.choose (ht_mem q h)
    else ⟨Classical.choose hXne, Classical.choose_spec hXne⟩
  have hXq : ∀ q : MvPolynomial (Fin n) k, q ∈ t → w (Xq q) = q := by
    intro q hq
    simp only [Xq, dif_pos hq]
    exact Classical.choose_spec (ht_mem q hq)
  have htne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hXne
      have hspan : Submodule.span (MvPolynomial (Fin n) k)
          (↑t : Set (MvPolynomial (Fin n) k)) = ⊥ := by simp [h]
      have hmem : w ⟨x, hx⟩ ∈ Submodule.span (MvPolynomial (Fin n) k)
          (↑t : Set (MvPolynomial (Fin n) k)) := by
        rw [← ht_span]
        exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
      rw [hspan] at hmem
      simp only [Submodule.mem_bot] at hmem
      exact hw ⟨x, hx⟩ (by rw [hmem]; simp)
    · exact h
  -- Step 3: the pieces `basicOpen q`, `q ∈ t`, cover `X`
  have hcover : X ⊆ ⋃ q ∈ t, basicOpen (k := k) q := by
    intro y hy
    by_contra hcon
    have hz : ∀ q ∈ t, aeval y q = 0 := by
      intro q hq
      by_contra hqy
      exact hcon (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hqy⟩⟩)
    have hle : Submodule.span (MvPolynomial (Fin n) k)
        (↑t : Set (MvPolynomial (Fin n) k)) ≤
        RingHom.ker (MvPolynomial.aeval y).toRingHom := by
      rw [Submodule.span_le]
      exact hz
    have hmem : w ⟨y, hy⟩ ∈ Submodule.span (MvPolynomial (Fin n) k)
        (↑t : Set (MvPolynomial (Fin n) k)) := by
      rw [← ht_span]
      exact Ideal.subset_span ⟨⟨y, hy⟩, rfl⟩
    exact hw ⟨y, hy⟩ (by simpa using hle hmem)
  -- Step 4: the candidate global denominator and numerators
  set H : MvPolynomial (Fin n) k := ∏ q ∈ t, h (Xq q) with hH
  set Gq : MvPolynomial (Fin n) k → MvPolynomial (Fin n) k :=
    fun q => g (Xq q) * ∏ q' ∈ t.erase q, h (Xq q') with hGq
  have hpiece : ∀ q ∈ t, (basicOpen (k := k) q ∩ X).Nonempty := by
    intro q hq
    refine ⟨(Xq q).1, ?_, (Xq q).2⟩
    have := hw (Xq q)
    rwa [hXq q hq] at this
  -- the relation holds on each piece
  have hkey : ∀ q ∈ t, ∀ (y : Aff n k), y ∈ basicOpen (k := k) q → ∀ hyX : y ∈ X,
      f ⟨y, hyX⟩ * aeval y H = aeval y (Gq q) := by
    intro q hq y hy hyX
    have hwq : w (Xq q) = q := hXq q hq
    have hq' : y ∈ basicOpen (k := k) (w (Xq q)) := by rw [hwq]; exact hy
    have h1 : f ⟨y, hyX⟩ = aeval y (g (Xq q)) / aeval y (h (Xq q)) := he (Xq q) y hq' hyX
    have h2 : aeval y (h (Xq q)) ≠ 0 := hh (Xq q) y hq' hyX
    have hsplit : H = h (Xq q) * ∏ q' ∈ t.erase q, h (Xq q') := by
      rw [hH]
      exact (Finset.mul_prod_erase t (fun q => h (Xq q)) hq).symm
    rw [hsplit, map_mul, h1, hGq]
    simp only [map_mul]
    field_simp
  -- the numerators all agree
  have hGeq : ∀ q ∈ t, ∀ q' ∈ t, ∀ y : X, aeval y.1 (Gq q) = aeval y.1 (Gq q') := by
    intro q hq q' hq' y
    have hneop : (basicOpen (k := k) q ∩ basicOpen (k := k) q' ∩ X).Nonempty :=
      hmeet _ _ (basicOpen_isOpen q) (basicOpen_isOpen q') (hpiece q hq) (hpiece q' hq')
    have hzero : ∀ z ∈ (basicOpen (k := k) q ∩ basicOpen (k := k) q') ∩ X,
        aeval z (Gq q - Gq q') = 0 := by
      rintro z ⟨⟨hz1, hz2⟩, hzX⟩
      have e1 := hkey q hq z hz1 hzX
      have e2 := hkey q' hq' z hz2 hzX
      rw [map_sub, ← e1, ← e2, sub_self]
    have hall := hvanish (Gq q - Gq q') _ ((basicOpen_isOpen q).inter (basicOpen_isOpen q'))
      hneop hzero y.1 y.2
    rw [map_sub, sub_eq_zero] at hall
    exact hall
  obtain ⟨q₀, hq₀⟩ := htne
  have hHne_on : ∃ x : X, aeval x.1 H ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_aeval_ne_zero_prod (k := k) hmeet hXne t
      (fun q => h (Xq q)) (fun q hq => ⟨Xq q, hh (Xq q) (Xq q).1 (hw (Xq q)) (Xq q).2⟩)
    refine ⟨x, ?_⟩
    rwa [hH]
  refine ⟨Gq q₀, H, ?_, hHne_on, ?_⟩
  · rw [hH]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro q hq hzero
    have hval : aeval (Xq q).1 (h (Xq q)) ≠ 0 := hh (Xq q) (Xq q).1 (hw (Xq q)) (Xq q).2
    exact hval (by rw [hzero]; simp)
  · intro x
    have hx : x.1 ∈ ⋃ q ∈ t, basicOpen (k := k) q := hcover x.2
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hqt, hqx⟩ := Set.mem_iUnion.mp hq
    have e1 : f x * aeval x.1 H = aeval x.1 (Gq q) := hkey q hqt x.1 hqx x.2
    have e2 : aeval x.1 (Gq q) = aeval x.1 (Gq q₀) := hGeq q hqt q₀ hq₀ x
    rw [e1, e2]

end Aff

/-! ## The punctured plane -/

namespace Aff

/-- The punctured plane `𝔸² \ {(0,0)}`. -/
def punctured : Set (Aff 2 k) := {x | x ≠ 0}

theorem zeroLocus_X_pair :
    MvPolynomial.zeroLocus k
      (Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k))) = {(0 : Aff 2 k)} := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · rintro hx
    funext i
    fin_cases i
    · have := hx (MvPolynomial.X 0) (by simp)
      simpa using this
    · have := hx (MvPolynomial.X 1) (by simp)
      simpa using this
  · rintro rfl p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp

theorem isOpen_punctured : IsOpen (punctured (k := k)) := by
  rw [isOpen_iff_compl_isZarClosed]
  refine ⟨Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)}, ?_⟩
  rw [zeroLocus_X_pair]
  ext x
  simp [punctured]

/-- A nonzero polynomial has a nonzero value at a point other than the origin. -/
theorem exists_ne_zero_aeval_ne_zero {n : ℕ} {q : MvPolynomial (Fin n) k} (hq : q ≠ 0)
    (hn : 0 < n) : ∃ x : Aff n k, x ≠ 0 ∧ aeval x q ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_and] at h
  have hq0 : q = 0 := by
    refine eq_zero_of_eq_zero_on_isOpen (W := basicOpen (k := k) (MvPolynomial.X ⟨0, hn⟩))
      (basicOpen_isOpen _) ⟨fun i => if i = ⟨0, hn⟩ then 1 else 0, by simp [basicOpen]⟩ ?_
    intro x hx
    have hne : x ≠ 0 := by
      intro hx0
      exact hx (by rw [hx0]; simp)
    exact not_not.mp (h x hne)
  exact hq hq0

theorem pairwiseMeetOpens_punctured : PairwiseMeetOpens (punctured (k := k)) := by
  refine pairwiseMeetOpens_of_basic ?_
  intro f g hf hg
  have hf0 : f ≠ 0 := by
    obtain ⟨x, hx⟩ := hf
    exact fun h => hx.1 (by rw [h]; simp)
  have hg0 : g ≠ 0 := by
    obtain ⟨x, hx⟩ := hg
    exact fun h => hx.1 (by rw [h]; simp)
  obtain ⟨z, hz0, hz⟩ := exists_ne_zero_aeval_ne_zero (mul_ne_zero hf0 hg0) (by norm_num : 0 < 2)
  rw [map_mul] at hz
  exact ⟨z, ⟨fun h => hz (by rw [h, zero_mul]), fun h => hz (by rw [h, mul_zero])⟩, hz0⟩

/-- Two regular functions that agree on a nonempty relatively open subset of `X` agree
everywhere, provided `X` is "irreducible" and polynomials vanishing on a nonempty relatively
open piece of `X` vanish on all of `X`. -/
theorem IsRegularOn.eq_of_eqOn_isOpen {X : Set (Aff n k)}
    (hmeet : PairwiseMeetOpens X)
    (hvanish : ∀ (q : MvPolynomial (Fin n) k) (W : Set (Aff n k)), IsOpen W →
      (W ∩ X).Nonempty → (∀ x ∈ W ∩ X, aeval x q = 0) → ∀ x ∈ X, aeval x q = 0)
    {f g : X → k} (hf : IsRegularOn X f) (hg : IsRegularOn X g)
    {W : Set (Aff n k)} (hW : IsOpen W) (hWne : (W ∩ X).Nonempty)
    (hWeq : ∀ (x : Aff n k) (_ : x ∈ W) (hxX : x ∈ X), f ⟨x, hxX⟩ = g ⟨x, hxX⟩) :
    ∀ x, f x = g x := by
  classical
  have hsub : IsRegularOn X (f - g) := (regularSubring X).sub_mem hf hg
  have hzero : ∀ x, (f - g) x = 0 := by
    intro x
    obtain ⟨V, a, b, hV, hxV, hb, he⟩ := hsub x
    have hne : ((W ∩ V) ∩ X).Nonempty := hmeet W V hW hV hWne ⟨x.1, hxV, x.2⟩
    have hvan : ∀ z ∈ X, aeval z a = 0 := by
      refine hvanish a (W ∩ V) (hW.inter hV) hne ?_
      rintro y ⟨⟨hyW, hyV⟩, hyX⟩
      have h1 := he y hyV hyX
      have h2 : (f - g) ⟨y, hyX⟩ = 0 := by
        have : f ⟨y, hyX⟩ = g ⟨y, hyX⟩ := hWeq y hyW hyX
        simp only [Pi.sub_apply, this, sub_self]
      have hb' : aeval y b ≠ 0 := hb y hyV hyX
      rw [h1] at h2
      rcases div_eq_zero_iff.mp h2 with h | h
      · exact h
      · exact absurd h hb'
    have h1 := he x.1 hxV x.2
    have h2 : aeval x.1 a = 0 := hvan x.1 x.2
    rw [h1, h2]
    simp
  intro x
  exact sub_eq_zero.mp (hzero x)

end Aff

/-! ## Regular functions on the punctured plane are polynomial -/

namespace Aff

/-- The first coordinate function on the plane. -/
def coordX : MvPolynomial (Fin 2) k := MvPolynomial.X 0

@[simp] theorem aeval_coordX (p : Aff 2 k) : aeval p (coordX (k := k)) = p 0 := by
  simp [coordX]

/-- If a polynomial in two variables vanishes on the punctured `Y`-axis, then `X` divides it. -/
theorem coordX_dvd_of_forall_eval_zero {Q : MvPolynomial (Fin 2) k}
    (h : ∀ b : k, b ≠ 0 → aeval (![0, b] : Aff 2 k) Q = 0) : coordX (k := k) ∣ Q := by
  classical
  set P : MvPolynomial (Fin 1) k :=
    Polynomial.eval (0 : MvPolynomial (Fin 1) k) (MvPolynomial.finSuccEquiv k 1 Q) with hP
  have hP0 : P = 0 := by
    by_contra hPne
    obtain ⟨y, hy0, hy⟩ := exists_ne_zero_aeval_ne_zero hPne (n := 1) (by norm_num)
    apply hy
    rw [hP, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_polynomial_eval_finSuccEquiv]
    have hpt : (Fin.cases (MvPolynomial.eval y (0 : MvPolynomial (Fin 1) k)) y)
        = (![0, y 0] : Aff 2 k) := by
      funext i
      fin_cases i
      · rfl
      · rfl
    rw [hpt]
    apply h
    intro h0
    exact hy0 (by funext i; fin_cases i <;> simpa using h0)
  have hcoeff : (MvPolynomial.finSuccEquiv k 1 Q).coeff 0 = 0 := by
    have h1 : (MvPolynomial.finSuccEquiv k 1 Q).coeff 0 = P := by
      rw [hP, Polynomial.coeff_zero_eq_eval_zero]
    rw [h1, hP0]
  obtain ⟨S, hS⟩ := Polynomial.X_dvd_iff.mpr hcoeff
  refine ⟨(MvPolynomial.finSuccEquiv k 1).symm S, ?_⟩
  have hX : (MvPolynomial.finSuccEquiv k 1).symm Polynomial.X = coordX (k := k) := by
    rw [show Polynomial.X = MvPolynomial.finSuccEquiv k 1 (coordX (k := k)) from
      (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 1)).symm, AlgEquiv.symm_apply_apply]
  calc Q = (MvPolynomial.finSuccEquiv k 1).symm (MvPolynomial.finSuccEquiv k 1 Q) :=
        (AlgEquiv.symm_apply_apply _ _).symm
    _ = (MvPolynomial.finSuccEquiv k 1).symm (Polynomial.X * S) := by rw [hS]
    _ = (MvPolynomial.finSuccEquiv k 1).symm Polynomial.X *
          (MvPolynomial.finSuccEquiv k 1).symm S := by rw [map_mul]
    _ = coordX (k := k) * (MvPolynomial.finSuccEquiv k 1).symm S := by rw [hX]

/-- Removing a power of `X` from the denominator. -/
theorem exists_poly_of_mul_pow_X {f : ↥(punctured (k := k)) → k}
    (hf : IsRegularOn (punctured (k := k)) f) (m : ℕ) (Q : MvPolynomial (Fin 2) k)
    (hQ : ∀ x : ↥(punctured (k := k)), f x * aeval x.1 (coordX (k := k)) ^ m = aeval x.1 Q) :
    ∃ p : MvPolynomial (Fin 2) k, ∀ x, f x = aeval x.1 p := by
  classical
  induction m generalizing Q with
  | zero =>
    refine ⟨Q, fun x => ?_⟩
    simpa using hQ x
  | succ m ih =>
    have hQ' : ∀ x : ↥(punctured (k := k)),
        f x * aeval x.1 ((coordX (k := k)) ^ (m + 1)) = aeval x.1 Q := by
      intro x
      rw [map_pow]
      exact hQ x
    have hdvd : coordX (k := k) ∣ Q := by
      refine coordX_dvd_of_forall_eval_zero ?_
      intro b hb
      have hP : (![0, b] : Aff 2 k) ≠ 0 := cons₂_ne_zero_of_second hb
      have h1 := hQ' ⟨(![0, b] : Aff 2 k), hP⟩
      have h2 : aeval (![0, b] : Aff 2 k) ((coordX (k := k)) ^ (m + 1)) = 0 := by
        rw [map_pow]
        simp
      rw [h2] at h1
      simpa using h1.symm
    obtain ⟨Q₁, rfl⟩ := hdvd
    refine ih Q₁ ?_
    have hreg1 : IsRegularOn (punctured (k := k))
        (fun x : ↥(punctured (k := k)) => f x * aeval x.1 ((coordX (k := k)) ^ m)) :=
      (regularSubring _).mul_mem hf (isRegularOn_poly _ _)
    have hreg2 : IsRegularOn (punctured (k := k))
        (fun x : ↥(punctured (k := k)) => aeval x.1 Q₁) := isRegularOn_poly _ _
    have hWeq : ∀ (y : Aff 2 k) (_ : y ∈ basicOpen (k := k) (coordX (k := k)))
        (hyX : y ∈ punctured (k := k)),
        (fun x : ↥(punctured (k := k)) => f x * aeval x.1 ((coordX (k := k)) ^ m)) ⟨y, hyX⟩
          = (fun x : ↥(punctured (k := k)) => aeval x.1 Q₁) ⟨y, hyX⟩ := by
      intro y hyW hyX
      have hx0 : aeval y (coordX (k := k)) ≠ 0 := hyW
      have h1 := hQ' ⟨y, hyX⟩
      rw [map_pow, map_mul] at h1
      have h3 : aeval y (coordX (k := k)) ^ (m + 1)
          = aeval y (coordX (k := k)) ^ m * aeval y (coordX (k := k)) :=
        pow_succ (aeval y (coordX (k := k))) m
      rw [h3] at h1
      refine mul_right_cancel₀ hx0 ?_
      simp only [map_pow]
      calc f ⟨y, hyX⟩ * aeval y (coordX (k := k)) ^ m * aeval y (coordX (k := k))
          = f ⟨y, hyX⟩ * (aeval y (coordX (k := k)) ^ m *
              aeval y (coordX (k := k))) := by ring
        _ = aeval y (coordX (k := k)) * aeval y Q₁ := h1
        _ = aeval y Q₁ * aeval y (coordX (k := k)) := by ring
    intro x
    have heq := hreg1.eq_of_eqOn_isOpen pairwiseMeetOpens_punctured
      (fun q W hW hWne h => by
        have hq0 : q = 0 := eq_zero_of_eq_zero_on_isOpen (hW.inter isOpen_punctured) hWne h
        intro x _; rw [hq0]; simp)
      hreg2
      (basicOpen_isOpen (coordX (k := k)))
      ⟨![1, 0], by simp [basicOpen], cons₂_ne_zero_of_first one_ne_zero⟩ hWeq
    rw [← map_pow]
    exact heq x

/-- **Hartshorne I.3.6 (a).** Every regular function on the punctured plane is a polynomial. -/
theorem exists_poly_of_isRegularOn_punctured {f : ↥(punctured (k := k)) → k}
    (hf : IsRegularOn (punctured (k := k)) f) :
    ∃ p : MvPolynomial (Fin 2) k, ∀ x, f x = aeval x.1 p := by
  classical
  obtain ⟨G, H, hH, -, hGH⟩ :=
    exists_poly_mul_eq ⟨![1, 0], cons₂_ne_zero_of_first one_ne_zero⟩
      pairwiseMeetOpens_punctured
      (fun q W hW hWne h => by
        have hq0 : q = 0 := eq_zero_of_eq_zero_on_isOpen (hW.inter isOpen_punctured) hWne h
        intro x _; rw [hq0]; simp)
      hf
  set J : Ideal (MvPolynomial (Fin 2) k) :=
    { carrier := {c : MvPolynomial (Fin 2) k | H ∣ c * G}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change H ∣ (a + b) * G
        rw [add_mul]
        exact dvd_add ha hb
      smul_mem' := by
        intro c a ha
        change H ∣ (c • a) * G
        rw [smul_eq_mul, mul_assoc]
        exact dvd_mul_of_dvd_right ha c } with hJ
  -- every point of the punctured plane has a nonvanishing denominator
  have hden : ∀ x : ↥(punctured (k := k)), ∃ c ∈ J, aeval x.1 c ≠ 0 := by
    intro x
    obtain ⟨V, g, h, hV, hxV, hb, he⟩ := hf x
    have hid : g * H = h * G := by
      have hz : g * H - h * G = 0 := by
        refine eq_zero_of_eq_zero_on_isOpen (hV.inter isOpen_punctured) ⟨x.1, hxV, x.2⟩ ?_
        rintro y ⟨hyV, hyX⟩
        have h1 := he y hyV hyX
        have h2 : f ⟨y, hyX⟩ * aeval y H = aeval y G := hGH ⟨y, hyX⟩
        have h4 : aeval y g = f ⟨y, hyX⟩ * aeval y h := by
          have hh : aeval y h ≠ 0 := hb y hyV hyX
          rw [h1]; field_simp
        rw [map_sub, map_mul, map_mul, h4]
        calc f ⟨y, hyX⟩ * aeval y h * aeval y H - aeval y h * aeval y G
            = (f ⟨y, hyX⟩ * aeval y H) * aeval y h - aeval y G * aeval y h := by ring
          _ = 0 := by rw [h2, sub_self]
      exact sub_eq_zero.mp hz
    refine ⟨h, ?_, hb x.1 hxV x.2⟩
    refine ⟨g, ?_⟩
    calc h * G = g * H := hid.symm
      _ = H * g := mul_comm _ _
  -- hence the common zero locus of `J` is contained in the origin
  have hVJ : MvPolynomial.zeroLocus k J ⊆ {(0 : Aff 2 k)} := by
    intro x hx
    by_contra hx0
    obtain ⟨c, hcJ, hcx⟩ := hden ⟨x, hx0⟩
    exact hcx (hx c hcJ)
  -- hence `X` lies in the radical of `J`
  have hXrad : coordX (k := k) ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hx0 : x = 0 := by
      by_contra h
      obtain ⟨c, hcJ, hcx⟩ := hden ⟨x, h⟩
      exact hcx (hx c hcJ)
    subst hx0
    simpa using aeval_coordX (k := k) (0 : Aff 2 k)
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hXrad
  have hm' : coordX (k := k) ^ (m + 1) ∈ J := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨Q, hQ⟩ : ∃ Q, coordX (k := k) ^ (m + 1) * G = H * Q := hm'
  have hfQ : ∀ x : ↥(punctured (k := k)),
      f x * aeval x.1 ((coordX (k := k)) ^ (m + 1)) = aeval x.1 Q := by
    have hreg1 : IsRegularOn (punctured (k := k))
        (fun x : ↥(punctured (k := k)) => f x * aeval x.1 ((coordX (k := k)) ^ (m + 1))) :=
      (regularSubring _).mul_mem hf (isRegularOn_poly _ _)
    have hreg2 : IsRegularOn (punctured (k := k))
        (fun x : ↥(punctured (k := k)) => aeval x.1 Q) := isRegularOn_poly _ _
    obtain ⟨x₁, hx₁0, hx₁⟩ := exists_ne_zero_aeval_ne_zero hH (n := 2) (by norm_num)
    have hWeq : ∀ (y : Aff 2 k) (_ : y ∈ basicOpen (k := k) H) (hyX : y ∈ punctured (k := k)),
        (fun x : ↥(punctured (k := k)) => f x * aeval x.1 ((coordX (k := k)) ^ (m + 1))) ⟨y, hyX⟩
          = (fun x : ↥(punctured (k := k)) => aeval x.1 Q) ⟨y, hyX⟩ := by
      intro y hyW hyX
      have hHne : aeval y H ≠ 0 := hyW
      have h1 : f ⟨y, hyX⟩ * aeval y H = aeval y G := hGH ⟨y, hyX⟩
      have h2 : aeval y (coordX (k := k) ^ (m + 1) * G) = aeval y (H * Q) := by rw [hQ]
      simp only [map_mul, map_pow] at h2
      refine mul_left_cancel₀ hHne ?_
      simp only [map_pow]
      calc aeval y H * (f ⟨y, hyX⟩ * aeval y (coordX (k := k)) ^ (m + 1))
          = (f ⟨y, hyX⟩ * aeval y H) * aeval y (coordX (k := k)) ^ (m + 1) := by ring
        _ = aeval y G * aeval y (coordX (k := k)) ^ (m + 1) := by rw [h1]
        _ = aeval y H * aeval y Q := by rw [mul_comm (aeval y G), h2]
    exact hreg1.eq_of_eqOn_isOpen pairwiseMeetOpens_punctured
      (fun q W hW hWne h => by
        have hq0 : q = 0 := eq_zero_of_eq_zero_on_isOpen (hW.inter isOpen_punctured) hWne h
        intro x _; rw [hq0]; simp)
      hreg2 (basicOpen_isOpen _) ⟨x₁, hx₁, hx₁0⟩ hWeq
  exact exists_poly_of_mul_pow_X hf (m + 1) Q (fun x => by rw [← map_pow]; exact hfQ x)

end Aff

/-! ## `Γ(𝔸² \ 0) ≅ k[x,y]` -/

namespace Aff

/-- Polynomial functions as regular functions. -/
def polyToRegular (X : Set (Aff n k)) : MvPolynomial (Fin n) k →+* regularSubring X where
  toFun p := ⟨fun x => aeval x.1 p, isRegularOn_poly X p⟩
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp
  map_zero' := by ext x; simp
  map_add' p q := by ext x; simp

theorem polyToRegular_injective_punctured :
    Function.Injective (polyToRegular (punctured (k := k))) := by
  intro p q h
  have h' : ∀ x : ↥(punctured (k := k)), aeval x.1 p = aeval x.1 q := by
    intro x
    have hx := congrArg (fun f : regularSubring (punctured (k := k)) =>
      (f : ↥(punctured (k := k)) → k) x) h
    simpa [polyToRegular] using hx
  have h0 : p - q = 0 := by
    refine eq_zero_of_eq_zero_on_isOpen isOpen_punctured
      ⟨(![1, 0] : Aff 2 k), cons₂_ne_zero_of_first one_ne_zero⟩ ?_
    intro x hx
    rw [map_sub, h' ⟨x, hx⟩, sub_self]
  exact sub_eq_zero.mp h0

theorem polyToRegular_surjective_punctured :
    Function.Surjective (polyToRegular (punctured (k := k))) := by
  intro f
  refine ⟨Classical.choose (exists_poly_of_isRegularOn_punctured f.2), ?_⟩
  ext x
  have hspec := Classical.choose_spec (exists_poly_of_isRegularOn_punctured f.2) x
  simpa [polyToRegular] using hspec.symm

/-- **Hartshorne I.3.6 (a)**, ring form: the ring of regular functions on `𝔸² \ {(0,0)}` is
`k[x,y]`. -/
def gammaPuncturedEquiv :
    MvPolynomial (Fin 2) k ≃+* regularSubring (punctured (k := k)) :=
  RingEquiv.ofBijective _ ⟨polyToRegular_injective_punctured, polyToRegular_surjective_punctured⟩

end Aff

/-! ## The punctured plane is not an affine variety -/

namespace Aff

section Morphisms

/-- A polynomial that vanishes on a nonempty relatively open piece of an irreducible set
vanishes on all of it. -/
theorem vanish_of_vanish_on_isOpen {n : ℕ} {Y : Set (Aff n k)} (hmeet : PairwiseMeetOpens Y)
    {W : Set (Aff n k)} (hW : IsOpen W) (hWne : (W ∩ Y).Nonempty) {q : MvPolynomial (Fin n) k}
    (hq : ∀ x ∈ W ∩ Y, aeval x q = 0) : ∀ x ∈ Y, aeval x q = 0 := by
  intro y hy
  by_contra hqy
  obtain ⟨x, hxW, hxY⟩ := hWne
  obtain ⟨w, hwx, hwW⟩ := exists_basicOpen_subset_of_isOpen hW hxW
  obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := hmeet _ _ (basicOpen_isOpen (k := k) w)
    (basicOpen_isOpen (k := k) q) ⟨x, hwx, hxY⟩ ⟨y, hqy, hy⟩
  exact hz2 (hq z ⟨hwW hz1, hz3⟩)

/-- A morphism of quasi-affine varieties: all coordinates are regular functions. -/
def IsMorphismTo {n m : ℕ} (X : Set (Aff n k)) (Y : Set (Aff m k)) (f : X → Y) : Prop :=
  ∀ i : Fin m, IsRegularOn X (fun x => (f x).1 i)

/-- Pullback of a polynomial function along a morphism is regular. -/
theorem isRegularOn_comp_poly {n m : ℕ} {X : Set (Aff n k)} {Y : Set (Aff m k)} {f : X → Y}
    (hf : IsMorphismTo X Y f) (P : MvPolynomial (Fin m) k) :
    IsRegularOn X (fun x => aeval (f x).1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hconst : (fun x : X => aeval (f x).1 (MvPolynomial.C a)) = fun _ => a := by
        funext x; simp
      rw [hconst]
      simpa using isRegularOn_poly X (MvPolynomial.C a)
  | add p q hp hq =>
      have hsum : (fun x : X => aeval (f x).1 (p + q))
          = (fun x : X => aeval (f x).1 p) + (fun x : X => aeval (f x).1 q) := by
        funext x; simp
      rw [hsum]
      exact (regularSubring X).add_mem hp hq
  | mul_X p i hp =>
      have hmul : (fun x : X => aeval (f x).1 (p * MvPolynomial.X i))
          = (fun x : X => aeval (f x).1 p) * (fun x : X => (f x).1 i) := by
        funext x; simp
      rw [hmul]
      exact (regularSubring X).mul_mem hp (hf i)

/-- An isomorphism of quasi-affine varieties: mutually inverse morphisms. -/
structure VarietyIso {n m : ℕ} (X : Set (Aff n k)) (Y : Set (Aff m k)) where
  toFun : X → Y
  invFun : Y → X
  isMorphism_toFun : IsMorphismTo X Y toFun
  isMorphism_invFun : IsMorphismTo Y X invFun
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

end Morphisms

/-- **Regular functions on an affine variety are polynomial functions.** -/
theorem exists_poly_of_isRegularOn_affine {m : ℕ} {Y : Set (Aff m k)} (hYc : IsClosed Y)
    (hYne : Y.Nonempty) (hmeet : PairwiseMeetOpens Y) {f : Y → k} (hf : IsRegularOn Y f) :
    ∃ p : MvPolynomial (Fin m) k, ∀ y, f y = aeval y.1 p := by
  classical
  obtain ⟨G, H, hH, ⟨y₀, hy₀⟩, hGH⟩ :=
    exists_poly_mul_eq hYne hmeet
      (fun q W hW hWne h => vanish_of_vanish_on_isOpen hmeet hW hWne h) hf
  -- the vanishing ideal of a closed set has the expected zero locus
  have hVIY : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Y) = Y := by
    obtain ⟨I₀, hI₀⟩ := hYc
    have hYeq : Y = MvPolynomial.zeroLocus k I₀ := by
      rw [← hI₀]; simp
    rw [hYeq, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    apply le_antisymm
    · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
    · intro x hx p hp
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
      match n with
      | 0 =>
          have h1 : aeval x (1 : MvPolynomial (Fin m) k) = 0 := hx 1 (by simpa using hn)
          rw [map_one] at h1
          exact absurd h1 one_ne_zero
      | (k + 1) =>
          have h2 : aeval x (p ^ (k + 1)) = 0 := hx _ hn
          rw [map_pow] at h2
          exact (pow_eq_zero_iff (Nat.succ_ne_zero k)).mp h2
  -- denominators of `f`, modulo the vanishing ideal of `Y`
  set J : Ideal (MvPolynomial (Fin m) k) :=
    { carrier := {c : MvPolynomial (Fin m) k |
        c * G ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change (a + b) * G ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y
        rw [add_mul]
        exact Ideal.add_mem _ ha hb
      smul_mem' := by
        intro c a ha
        change (c • a) * G ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y
        rw [smul_eq_mul, mul_assoc]
        exact Ideal.mul_mem_left _ _ ha } with hJ
  have hden : ∀ y : Y, ∃ c ∈ J, aeval y.1 c ≠ 0 := by
    intro y
    obtain ⟨V, g, h, hV, hxV, hb, he⟩ := hf y
    -- `g * H - h * G` vanishes on `Y`
    have hvanish : ∀ x ∈ Y, aeval x (g * H - h * G) = 0 := by
      refine vanish_of_vanish_on_isOpen hmeet hV ⟨y.1, hxV, y.2⟩ ?_
      rintro x ⟨hxV, hxY⟩
      have h1 := he x hxV hxY
      have h2 : f ⟨x, hxY⟩ * aeval x H = aeval x G := hGH ⟨x, hxY⟩
      have h4 : aeval x g = f ⟨x, hxY⟩ * aeval x h := by
        have hh : aeval x h ≠ 0 := hb x hxV hxY
        rw [h1]; field_simp
      rw [map_sub, map_mul, map_mul, h4]
      calc f ⟨x, hxY⟩ * aeval x h * aeval x H - aeval x h * aeval x G
          = (f ⟨x, hxY⟩ * aeval x H) * aeval x h - aeval x G * aeval x h := by ring
        _ = 0 := by rw [h2, sub_self]
    refine ⟨h, ?_, hb y.1 hxV y.2⟩
    have hmemI : g * H - h * G ∈ MvPolynomial.vanishingIdeal k Y :=
      MvPolynomial.mem_vanishingIdeal_iff.mpr hvanish
    have hsplit : h * G = g * H - (g * H - h * G) := by ring
    have h1 : g * H ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y :=
      Ideal.mem_sup_left
        (Ideal.mul_mem_left _ g (Ideal.subset_span (by simp : H ∈ ({H} : Set (MvPolynomial (Fin m) k)))))
    have h2 : g * H - h * G ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y :=
      Ideal.mem_sup_right hmemI
    show h * G ∈ Ideal.span {H} ⊔ MvPolynomial.vanishingIdeal k Y
    rw [hsplit]
    exact Ideal.sub_mem _ h1 h2
  -- `J + I(Y) = ⊤`
  have htop : J ⊔ MvPolynomial.vanishingIdeal k Y = ⊤ := by
    have hzero : MvPolynomial.zeroLocus k (J ⊔ MvPolynomial.vanishingIdeal k Y) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxY : x ∈ Y := by
        rw [← hVIY]
        exact fun c hc => hx c (Ideal.mem_sup_right hc)
      obtain ⟨c, hcJ, hcx⟩ := hden ⟨x, hxY⟩
      exact hcx (hx c (Ideal.mem_sup_left hcJ))
    have h1 : (1 : MvPolynomial (Fin m) k) ∈
        (J ⊔ MvPolynomial.vanishingIdeal k Y).radical := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k), hzero,
        MvPolynomial.vanishingIdeal_empty]
      trivial
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
    exact (Ideal.eq_top_iff_one _).mpr (by simpa using hn)
  obtain ⟨j, hjJ, i, hiI, hji⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  have hjon : ∀ y : Y, aeval y.1 j = 1 := by
    intro y
    have h1 : aeval y.1 j + aeval y.1 i = 1 := by
      rw [← map_add, hji]; simp
    have h2 : aeval y.1 i = 0 := (MvPolynomial.mem_vanishingIdeal_iff.mp hiI) y.1 y.2
    rw [h2, add_zero] at h1
    exact h1
  -- write `j * G = H * Q` modulo `I(Y)`
  obtain ⟨s, hs, a, haI, hsa⟩ := Submodule.mem_sup.mp hjJ
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hs
  have hfr : ∀ y : Y, f y = aeval y.1 Q := by
    have heq : ∀ (y : Aff m k) (_ : y ∈ basicOpen (k := k) H) (hy : y ∈ Y),
        f ⟨y, hy⟩ = aeval y Q := by
      intro y hyW hy
      have hHne : aeval y H ≠ 0 := hyW
      have h1 : f ⟨y, hy⟩ * aeval y H = aeval y G := hGH ⟨y, hy⟩
      have h2 : aeval y (j * G) = aeval y (H * Q + a) := by rw [← hsa, hQ]
      simp only [map_mul, map_add] at h2
      have h3 : aeval y j = 1 := hjon ⟨y, hy⟩
      have h4 : aeval y a = 0 := (MvPolynomial.mem_vanishingIdeal_iff.mp haI) y hy
      rw [h4, add_zero] at h2
      refine mul_left_cancel₀ hHne ?_
      calc aeval y H * f ⟨y, hy⟩ = f ⟨y, hy⟩ * aeval y H := by ring
        _ = aeval y G := h1
        _ = aeval y j * aeval y G := by rw [h3, one_mul]
        _ = aeval y H * aeval y Q := h2
    intro y
    exact hf.eq_of_eqOn_isOpen hmeet
      (fun q W hW hWne h => vanish_of_vanish_on_isOpen hmeet hW hWne h)
      (isRegularOn_poly Y Q) (basicOpen_isOpen (k := k) H) ⟨y₀.1, hy₀, y₀.2⟩ heq y
  exact ⟨Q, hfr⟩

/-- **Hartshorne I.3.6 (b).** The punctured plane `𝔸² \ {(0,0)}` is not isomorphic to an
affine variety. -/
theorem punctured_not_affine :
    ¬ ∃ (m : ℕ) (Y : Set (Aff m k)), IsClosed Y ∧ Y.Nonempty ∧ PairwiseMeetOpens Y ∧
      Nonempty (VarietyIso (punctured (k := k)) Y) := by
  rintro ⟨m, Y, hYc, hYne, hmeet, ⟨iso⟩⟩
  classical
  -- coordinates of the morphism `𝔸² \ 0 → Y` are polynomials `Q`
  have hQexists : ∀ i : Fin m, ∃ Q : MvPolynomial (Fin 2) k,
      ∀ x : ↥(punctured (k := k)), (iso.toFun x).1 i = aeval x.1 Q :=
    fun i => exists_poly_of_isRegularOn_punctured (iso.isMorphism_toFun i)
  choose Q hQ using hQexists
  -- coordinates of the morphism `Y → 𝔸² \ 0` are polynomials `P`
  have hPexists : ∀ j : Fin 2, ∃ P : MvPolynomial (Fin m) k,
      ∀ y : Y, (iso.invFun y).1 j = aeval y.1 P :=
    fun j => exists_poly_of_isRegularOn_affine hYc hYne hmeet (iso.isMorphism_invFun j)
  choose P hP using hPexists
  -- substitution of the coordinates of `Q`
  set σ : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin 2) k := MvPolynomial.aeval Q with hσ
  -- the substitution inverts `P`
  have hkey : ∀ j : Fin 2, σ (P j) = MvPolynomial.X j := by
    intro j
    refine eq_of_eq_on_isOpen isOpen_punctured
      ⟨(![1, 0] : Aff 2 k), cons₂_ne_zero_of_first one_ne_zero⟩ ?_
    intro x hx
    have h1 : aeval x (σ (P j)) = aeval (iso.toFun ⟨x, hx⟩).1 (P j) := by
      rw [hσ, aeval_aeval]
      rw [show (fun i => aeval x (Q i)) = (iso.toFun ⟨x, hx⟩).1 from by
        funext i
        exact (hQ i ⟨x, hx⟩).symm]
    have h2 : (iso.invFun (iso.toFun ⟨x, hx⟩)).1 j = x j := by
      rw [iso.left_inv]
    have h3 := hP j (iso.toFun ⟨x, hx⟩)
    calc aeval x (σ (P j)) = aeval (iso.toFun ⟨x, hx⟩).1 (P j) := h1
      _ = (iso.invFun (iso.toFun ⟨x, hx⟩)).1 j := h3.symm
      _ = x j := h2
      _ = aeval x (MvPolynomial.X j : MvPolynomial (Fin 2) k) := by simp
  -- the vanishing ideal of a closed set
  have hVIY : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Y) = Y := by
    obtain ⟨I₀, hI₀⟩ := hYc
    have hYeq : Y = MvPolynomial.zeroLocus k I₀ := by
      rw [← hI₀]; simp
    rw [hYeq, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    apply le_antisymm
    · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
    · intro x hx p hp
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
      match n with
      | 0 =>
          have h1 : aeval x (1 : MvPolynomial (Fin m) k) = 0 := hx 1 (by simpa using hn)
          rw [map_one] at h1
          exact absurd h1 one_ne_zero
      | (k + 1) =>
          have h2 : aeval x (p ^ (k + 1)) = 0 := hx _ hn
          rw [map_pow] at h2
          exact (pow_eq_zero_iff (Nat.succ_ne_zero k)).mp h2
  -- `P 0` and `P 1` have a common zero on `Y`
  have hcommon : ∃ y : Y, aeval y.1 (P 0) = 0 ∧ aeval y.1 (P 1) = 0 := by
    by_contra hcon
    have hV : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Y ⊔
        Ideal.span ({P 0, P 1} : Set (MvPolynomial (Fin m) k))) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxY : x ∈ Y := by
        rw [← hVIY]
        exact fun c hc => hx c (Ideal.mem_sup_left hc)
      have hx0 : aeval x (P 0) = 0 :=
        hx _ (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
      have hx1 : aeval x (P 1) = 0 :=
        hx _ (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
      exact hcon ⟨⟨x, hxY⟩, hx0, hx1⟩
    have htop : MvPolynomial.vanishingIdeal k Y ⊔
        Ideal.span ({P 0, P 1} : Set (MvPolynomial (Fin m) k)) = ⊤ := by
      have h1 : (1 : MvPolynomial (Fin m) k) ∈
          (MvPolynomial.vanishingIdeal k Y ⊔
            Ideal.span ({P 0, P 1} : Set (MvPolynomial (Fin m) k))).radical := by
        rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k), hV,
          MvPolynomial.vanishingIdeal_empty]
        trivial
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
      exact (Ideal.eq_top_iff_one _).mpr (by simpa using hn)
    obtain ⟨i, hiI, s, hsS, hsa⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
    -- `σ` kills `I(Y)` and sends `P j` to `x j`
    have hσi : σ i = 0 := by
      by_contra hne
      have hvan : ∀ x : ↥(punctured (k := k)), aeval x.1 (σ i) = 0 := by
        intro x
        have h1 : aeval x.1 (σ i) = aeval (iso.toFun x).1 i := by
          rw [hσ, aeval_aeval]
          rw [show (fun t => aeval x.1 (Q t)) = (iso.toFun x).1 from by
            funext t
            exact (hQ t x).symm]
        rw [h1]
        exact (MvPolynomial.mem_vanishingIdeal_iff.mp hiI) _ (iso.toFun x).2
      obtain ⟨x, hxne, hxval⟩ := exists_ne_zero_aeval_ne_zero hne (n := 2) (by norm_num)
      exact hxval (hvan ⟨x, hxne⟩)
    have hσs : σ s ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k)) := by
      have h1 : σ s ∈ (Ideal.span ({P 0, P 1} : Set (MvPolynomial (Fin m) k))).map σ.toRingHom :=
        Ideal.mem_map_of_mem _ hsS
      rw [Ideal.map_span] at h1
      have h2 : σ.toRingHom '' ({P 0, P 1} : Set (MvPolynomial (Fin m) k)) =
          ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
            Set (MvPolynomial (Fin 2) k)) := by
        rw [Set.image_pair, show σ.toRingHom (P 0) = MvPolynomial.X (0 : Fin 2) from hkey 0,
          show σ.toRingHom (P 1) = MvPolynomial.X (1 : Fin 2) from hkey 1]
      rwa [h2] at h1
    -- hence `1` lies in the maximal ideal of the origin
    have hone : (1 : MvPolynomial (Fin 2) k) ∈
        Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
          Set (MvPolynomial (Fin 2) k)) := by
      have h1 : σ (i + s) = σ (1 : MvPolynomial (Fin m) k) := by rw [hsa]
      rw [map_add, hσi, zero_add, map_one] at h1
      rw [← h1]
      exact hσs
    -- every element of that ideal vanishes at the origin
    have hzero : ∀ p ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k)), aeval (0 : Aff 2 k) p = 0 := by
      intro p hp
      have hle : Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
          Set (MvPolynomial (Fin 2) k)) ≤
          RingHom.ker (MvPolynomial.aeval (0 : Aff 2 k)).toRingHom := by
        rw [Ideal.span_le]
        intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl <;> simp
      simpa using hle hp
    have h1 : (1 : k) = 0 := by simpa using hzero 1 hone
    exact one_ne_zero h1
  -- but then the inverse image of that point would be the origin
  obtain ⟨y, hy0, hy1⟩ := hcommon
  have hcontr : (iso.invFun y).1 = 0 := by
    funext j
    rw [hP j y]
    fin_cases j
    · exact hy0
    · exact hy1
  exact (iso.invFun y).2 hcontr

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_3_6.Aff.gammaPuncturedEquiv
#print axioms Hartshorne77.Ex_I_3_6.Aff.exists_poly_of_isRegularOn_punctured
#print axioms Hartshorne77.Ex_I_3_6.Aff.exists_poly_of_isRegularOn_affine
#print axioms Hartshorne77.Ex_I_3_6.Aff.punctured_not_affine
