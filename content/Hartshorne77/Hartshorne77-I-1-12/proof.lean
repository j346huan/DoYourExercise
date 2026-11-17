/-
Copyright (c) 2026 Hartshorne formalization campaign. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: m4
-/
import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Exercise I.1.12

## The statement in the source

Chapter I, §1, Exercise 1.12 (verbatim, from the book scan):

> 1.12. Give an example of an irreducible polynomial `f ∈ R[x,y]`, whose zero set `V(f)`
> in `A²_R` is not irreducible (cf. 1.4.2).

The exercise has no sub-parts and no further hypotheses: it asks for a *single* example over
the field `R` of real numbers, together with the verification of the two assertions
(irreducibility of `f`, non-irreducibility of `V(f)`).

The cross-reference "cf. 1.4.2" points at the book's Example 1.4.2, which reads (verbatim):

> Example 1.4.2. Let `f` be an irreducible polynomial in `A = k[x,y]`. Then `f` generates a
> prime ideal in `A`, since `A` is a unique factorization domain, so the zero set `Y = Z(f)`
> is irreducible. We call it the affine curve defined by the equation `f(x,y) = 0`. If `f`
> has degree `d` we say that `Y` is a curve of degree `d`.

and at Example 1.4.5 (verbatim):

> Example 1.4.5. If `k` is not algebraically closed, these results do not hold. For example,
> if `k = R`, the curve `x² + y² + 1 = 0` in `A²_R` has no points. So `A.2d)` is false.
> See also (Ex. 1.12).

So the content of the exercise is: the implication "`f` irreducible ⇒ `Z(f)` irreducible"
proved in Example 1.4.2 under the standing hypothesis that `k` is algebraically closed *fails*
over `R`, and the failure is genuinely topological (the point set `Z(f)` with its Zariski
topology is reducible), not merely a breakdown of the ideal/variety dictionary. The final
section of this file records the positive result over an algebraically closed field, which
shows that the hypothesis in Example 1.4.2 is essential.

Hartshorne's definition of irreducibility (Chapter I, §1, verbatim):

> Definition. A nonempty subset `Y` of a topological space `X` is irreducible if it cannot be
> expressed as the union `Y = Y₁ ∪ Y₂` of two proper subsets, each one of which is closed in
> `Y`. The empty set is not considered to be irreducible.

## The example formalised here

We use
`f = (x² - 1)² + y² = y² + (x² - 1)²`,
whose complex factorisation is `(y + i(x²-1)) (y - i(x²-1))`: the two factors are conjugate
and not associates, so no nonconstant factor is real, and `f` is irreducible in `ℝ[x,y]`.
Its real zero set is `{(1,0), (-1,0)}`: a nonempty two-point set. It is reducible because each
of the two points is closed in `𝔸²_R` and each is a proper subset of the zero set.

This is the example used by the natural-proof source
(`Hartshorne77-I-1-12/proof.tex`); the cheap solution `f = x² + y² + 1` with `V(f) = ∅`
(whence not irreducible, by the book's explicit convention) is also legitimate and is
recorded in §6 below, but the two-point example is stronger: it works even for the convention
in which only nonempty sets can be reducible.

## Formalisation choices

* **Ambient space.** `AffineSpace k n` is the abbreviation `Fin n → k`. Hartshorne's `𝔸ⁿ_k`
  is a point set, not a scheme, so the carrier is the honest one: `n`-tuples of elements of
  `k`. The Zariski topology is installed as the `TopologicalSpace` instance of this type; as
  the abbreviation is transparent, this instance shadows Mathlib's product topology on
  `Fin n → k` for the duration of this file. Nothing here uses the product topology, and every
  `IsOpen`/`IsClosed`/`IsIrreducible` statement below is about the Zariski topology (the
  instance is `Hartshorne77.Ex_I_1_12.instTopologicalSpace`).
* **Zariski topology.** The closed sets are declared to be the zero loci
  `Z(I) = {x | ∀ f ∈ I, f(x) = 0}` of ideals `I ⊆ k[x₁,…,xₙ]`, and the topology axioms are
  proved from `Z(I ⊓ J) = Z(I) ∪ Z(J)` and `Z(⨆ Iᵢ) = ⋂ Z(Iᵢ)` (closed sets are closed
  under finite unions and arbitrary intersections, as in Hartshorne §1). This uses Mathlib's
  `MvPolynomial.zeroLocus`/`vanishingIdeal` pair and its Galois connection, but *not* the
  `PrimeSpectrum`/`Proj` machinery: the points are classical points.
* **Irreducibility.** Mathlib's `IsIrreducible s` is `s.Nonempty ∧ IsPreirreducible s`, i.e.
  nonempty and not the union of two proper relatively closed subsets — precisely Hartshorne's
  notion, including his convention that `∅` is not irreducible.
* **Irreducibility of `f`.** `ℝ[x,y]` is a unique factorization domain; concretely we view
  `f` as a monic quadratic `y² + c` in `y` over the integral domain `ℝ[x]`, where
  `c = (x²-1)²`. A monic quadratic of degree two over a domain is irreducible as soon as `c`
  is not a negative square (`¬ ∃ a, c = -a²`), and `c = -a²` is impossible because evaluating
  at `x = 0` gives `1 = -a(0)²`. This is the algebraic content of "the two conjugate factors
  are not associates"; it avoids any appeal to `ℂ[x,y]`.

Everything is proved from the Mathlib axioms; see the `#print axioms` section at the end.
-/

namespace Hartshorne77.Ex_I_1_12

universe u

noncomputable section

open MvPolynomial Polynomial

/-! ## 1. Affine space and its Zariski topology -/

/-- Affine `n`-space over `k` as a point set: the type of `n`-tuples of elements of `k`. -/
abbrev AffineSpace (k : Type u) (n : ℕ) : Type u := Fin n → k

namespace AffineSpace

variable {k : Type u} [Field k] {n : ℕ}

/-- The zero locus of an ideal of polynomials, as a subset of affine space. -/
def zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) : Set (AffineSpace k n) :=
  MvPolynomial.zeroLocus k I

@[simp]
theorem mem_zeroLocus {I : Ideal (MvPolynomial (Fin n) k)} {x : AffineSpace k n} :
    x ∈ zeroLocus I ↔ ∀ p ∈ I, MvPolynomial.aeval x p = 0 :=
  Iff.rfl

/-- The zero set `V(S)` of a set of polynomials (Hartshorne's `Z(S)`). -/
def V (S : Set (MvPolynomial (Fin n) k)) : Set (AffineSpace k n) :=
  zeroLocus (Ideal.span S)

/-- Membership in the zero set of a set of polynomials. -/
theorem mem_V {S : Set (MvPolynomial (Fin n) k)} {x : AffineSpace k n} :
    x ∈ V S ↔ ∀ p ∈ S, MvPolynomial.aeval x p = 0 := by
  unfold V zeroLocus
  rw [MvPolynomial.zeroLocus_span]
  exact Iff.rfl

/-- Membership in the zero set of a single polynomial. -/
theorem mem_zeroLocus_span_singleton (p : MvPolynomial (Fin n) k) {x : AffineSpace k n} :
    x ∈ zeroLocus (Ideal.span {p}) ↔ MvPolynomial.aeval x p = 0 := by
  unfold zeroLocus
  rw [MvPolynomial.zeroLocus_span]
  exact ⟨fun h => h p rfl, fun h q hq => by
    rw [Set.mem_singleton_iff] at hq
    rw [hq]
    exact h⟩

/-- `Z(⨆ᵢ Iᵢ) = ⋂ᵢ Z(Iᵢ)`: an arbitrary intersection of zero loci is a zero locus. -/
theorem zeroLocus_iSup {ι : Type u} (I : ι → Ideal (MvPolynomial (Fin n) k)) :
    zeroLocus (⨆ i, I i) = ⋂ i, zeroLocus (I i) := by
  ext x
  rw [mem_zeroLocus, Set.mem_iInter]
  constructor
  · intro hx i
    exact fun p hp => hx p (le_iSup (fun i => I i) i hp)
  · intro hx p hp
    have hle : (⨆ i, I i) ≤
        MvPolynomial.vanishingIdeal k ({(x : Fin n → k)} : Set (Fin n → k)) := by
      refine iSup_le fun i => ?_
      intro q hq
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mem_zeroLocus.mp (hx i) q hq
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp (hle hp)) (x : Fin n → k) rfl

/-- `Z(I ⊓ J) = Z(I) ∪ Z(J)`: a finite union of zero loci is a zero locus. -/
theorem zeroLocus_inf (I J : Ideal (MvPolynomial (Fin n) k)) :
    zeroLocus (I ⊓ J) = zeroLocus I ∪ zeroLocus J := by
  ext x
  rw [mem_zeroLocus, Set.mem_union, mem_zeroLocus, mem_zeroLocus]
  constructor
  · intro hx
    by_contra hcon
    rw [not_or] at hcon
    have h1 : ∃ a ∈ I, MvPolynomial.aeval x a ≠ 0 := by
      by_contra h
      exact hcon.1 fun p hp => by
        by_contra hne
        exact h ⟨p, hp, hne⟩
    have h2 : ∃ b ∈ J, MvPolynomial.aeval x b ≠ 0 := by
      by_contra h
      exact hcon.2 fun p hp => by
        by_contra hne
        exact h ⟨p, hp, hne⟩
    obtain ⟨a, ha, hax⟩ := h1
    obtain ⟨b, hb, hbx⟩ := h2
    have hmem : a * b ∈ I ⊓ J := ⟨I.mul_mem_right b ha, J.mul_mem_left a hb⟩
    have h0 := hx (a * b) hmem
    rw [map_mul] at h0
    exact mul_ne_zero hax hbx h0
  · rintro (hx | hx) p hp
    · exact hx p hp.1
    · exact hx p hp.2

/-- The family of Zariski closed subsets of affine `n`-space over `k`. -/
def closedSets (k : Type u) [Field k] (n : ℕ) : Set (Set (AffineSpace k n)) :=
  Set.range (zeroLocus (k := k) (n := n))

theorem empty_mem_closedSets (k : Type u) [Field k] (n : ℕ) :
    (⊥ : Set (AffineSpace k n)) ∈ closedSets k n :=
  ⟨⊤, by
    show zeroLocus (⊤ : Ideal (MvPolynomial (Fin n) k)) = ⊥
    unfold zeroLocus
    exact MvPolynomial.zeroLocus_top⟩

theorem sInter_mem_closedSets {A : Set (Set (AffineSpace k n))} (hA : A ⊆ closedSets k n) :
    ⋂₀ A ∈ closedSets k n := by
  classical
  have hex : ∀ V : A, ∃ I : Ideal (MvPolynomial (Fin n) k), zeroLocus I = V.1 := by
    intro V
    obtain ⟨I, hI⟩ := hA V.2
    exact ⟨I, hI⟩
  choose I hI using hex
  refine ⟨⨆ V : A, I V, ?_⟩
  have h1 : ⋂₀ A = ⋂ V : A, zeroLocus (I V) := by
    ext x
    simp only [Set.mem_sInter, Set.mem_iInter]
    constructor
    · intro hx V
      rw [hI V]
      exact hx V.1 V.2
    · intro hx V hV
      have hmem : x ∈ zeroLocus (I ⟨V, hV⟩) := hx ⟨V, hV⟩
      rw [hI ⟨V, hV⟩] at hmem
      simpa using hmem
  rw [h1]
  exact zeroLocus_iSup (fun V : A => I V)

theorem union_mem_closedSets {A B : Set (AffineSpace k n)}
    (hA : A ∈ closedSets k n) (hB : B ∈ closedSets k n) : A ∪ B ∈ closedSets k n := by
  obtain ⟨I, rfl⟩ := hA
  obtain ⟨J, rfl⟩ := hB
  exact ⟨I ⊓ J, zeroLocus_inf I J⟩

end AffineSpace

/-- **The Zariski topology** on affine `n`-space over `k`: the topology whose closed sets are
the zero loci of ideals of polynomials. -/
instance instTopologicalSpace (k : Type u) [Field k] (n : ℕ) : TopologicalSpace (AffineSpace k n) where
  IsOpen s := sᶜ ∈ AffineSpace.closedSets k n
  isOpen_univ := by
    have h : (Set.univ : Set (AffineSpace k n))ᶜ = ⊥ := by simp
    rw [h]
    exact AffineSpace.empty_mem_closedSets k n
  isOpen_inter s t hs ht := by
    show (s ∩ t)ᶜ ∈ AffineSpace.closedSets k n
    rw [Set.compl_inter]
    exact AffineSpace.union_mem_closedSets hs ht
  isOpen_sUnion S hS := by
    show (⋃₀ S)ᶜ ∈ AffineSpace.closedSets k n
    rw [Set.compl_sUnion]
    refine AffineSpace.sInter_mem_closedSets ?_
    rintro V ⟨s, hs, rfl⟩
    exact hS s hs

namespace AffineSpace

variable {k : Type u} [Field k] {n : ℕ}

theorem isOpen_iff (s : Set (AffineSpace k n)) : IsOpen s ↔ sᶜ ∈ closedSets k n :=
  Iff.rfl

theorem isClosed_iff_mem_closedSets {V : Set (AffineSpace k n)} :
    IsClosed V ↔ V ∈ closedSets k n := by
  rw [show IsClosed V ↔ IsOpen Vᶜ from ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩]
  show Vᶜᶜ ∈ closedSets k n ↔ V ∈ closedSets k n
  rw [compl_compl]

theorem isClosed_iff_exists_zeroLocus {V : Set (AffineSpace k n)} :
    IsClosed V ↔ ∃ I : Ideal (MvPolynomial (Fin n) k), V = zeroLocus I := by
  rw [isClosed_iff_mem_closedSets]
  exact ⟨fun ⟨I, hI⟩ => ⟨I, hI.symm⟩, fun ⟨I, hI⟩ => ⟨I, hI.symm⟩⟩

theorem isClosed_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) : IsClosed (zeroLocus I) :=
  isClosed_iff_exists_zeroLocus.mpr ⟨I, rfl⟩

theorem isClosed_V (S : Set (MvPolynomial (Fin n) k)) : IsClosed (V S) :=
  isClosed_zeroLocus (Ideal.span S)

/-- Hartshorne defines the Zariski closed subsets of `𝔸ⁿ_k` as the zero sets `Z(S)` of an
arbitrary set `S` of polynomials; they are exactly the zero loci of ideals, because
`Z(S) = Z(⟨S⟩)`. -/
theorem isClosed_iff_exists_V {Z : Set (AffineSpace k n)} :
    IsClosed Z ↔ ∃ S : Set (MvPolynomial (Fin n) k), Z = V S := by
  rw [isClosed_iff_exists_zeroLocus]
  constructor
  · rintro ⟨I, rfl⟩
    exact ⟨I, by
      show zeroLocus I = zeroLocus (Ideal.span (I : Set (MvPolynomial (Fin n) k)))
      rw [Ideal.span_eq]⟩
  · rintro ⟨S, rfl⟩
    exact ⟨Ideal.span S, rfl⟩

/-- The coordinate hyperplane `{x | x i = a}` is Zariski closed. -/
theorem isClosed_setOf_coord_eq (i : Fin n) (a : k) :
    IsClosed {x : AffineSpace k n | x i = a} := by
  refine isClosed_iff_exists_zeroLocus.mpr
    ⟨Ideal.span {(MvPolynomial.X i - MvPolynomial.C a : MvPolynomial (Fin n) k)}, ?_⟩
  ext x
  rw [mem_zeroLocus_span_singleton]
  have hx : (MvPolynomial.aeval (x : Fin n → k))
      (MvPolynomial.X i - MvPolynomial.C a : MvPolynomial (Fin n) k) = x i - a := by simp
  rw [hx, sub_eq_zero]
  exact Iff.rfl

/-- Points are closed in the Zariski topology: affine space is `T₁`. -/
theorem isClosed_singleton (x : AffineSpace k n) : IsClosed ({x} : Set (AffineSpace k n)) := by
  have h : ({x} : Set (AffineSpace k n)) = ⋂ i : Fin n, {y : AffineSpace k n | y i = x i} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h i => by rw [h], fun h => funext h⟩
  rw [h]
  exact isClosed_iInter fun i => isClosed_setOf_coord_eq i (x i)

/-! ## 2. Irreducibility of a two-point set -/

/-- In a `T₁` space, a two-point set is not irreducible: the two singletons are closed subsets
which cover it, and neither contains the other point. (This is why the zero set `{(1,0),(-1,0)}`
below is reducible.) -/
theorem not_isIrreducible_pair (p q : AffineSpace k n) (hpq : p ≠ q) :
    ¬ IsIrreducible ({p, q} : Set (AffineSpace k n)) := by
  rintro ⟨-, hpre⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  have hcov : ({p, q} : Set (AffineSpace k n)) ⊆ {p} ∪ {q} := by
    intro x hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hpre _ _ (isClosed_singleton p) (isClosed_singleton q) hcov with h | h
  · have hq' : q = p := h (by simp)
    exact hpq hq'.symm
  · have hp' : p = q := h (by simp)
    exact hpq hp'

end AffineSpace

/-! ## 3. Irreducibility of `(x² - 1)² + y²`

The coordinates are `x = X 1` and `y = X 0`; the polynomial of the example is
`f = (x² - 1)² + y² = (X 1² - 1)² + X 0²`, which is `y² + (x² - 1)²` by commutativity. This
writing puts the quadratic variable in the position (`X 0`) that `finSuccEquiv` uses. -/

/-- A monic quadratic `y² + c` of degree two over an integral domain is irreducible when `c` is
not a negative square. -/
theorem irreducible_X_sq_add_C {R : Type*} [CommRing R] [IsDomain R] {c : R}
    (hc : ∀ a : R, c ≠ -(a ^ 2)) : Irreducible (Polynomial.X ^ 2 + Polynomial.C c) := by
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C c).Monic :=
    Polynomial.monic_X_pow_add_C c (by norm_num : (2 : ℕ) ≠ 0)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C c).natDegree = 2 :=
    Polynomial.natDegree_X_pow_add_C
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg])
    (by rw [hdeg]; norm_num)]
  apply Multiset.eq_zero_of_forall_notMem
  intro a ha
  rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot.def] at ha
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ha
  exact hc a (by linear_combination ha)

/-- `(x² - 1)²` is not a negative square in `ℝ[x]`: evaluating at `x = 0` would give
`1 = -a(0)²`. -/
theorem sq_sub_one_sq_not_neg_sq (a : MvPolynomial (Fin 1) ℝ) :
    ((MvPolynomial.X 0 ^ 2 - MvPolynomial.C 1) ^ 2 : MvPolynomial (Fin 1) ℝ) ≠ -(a ^ 2) := by
  intro h
  have h' := congrArg (MvPolynomial.eval (0 : Fin 1 → ℝ)) h
  simp only [map_pow, map_sub, map_neg, map_one, MvPolynomial.eval_X, Pi.zero_apply] at h'
  norm_num at h'
  nlinarith [sq_nonneg (MvPolynomial.eval (0 : Fin 1 → ℝ) a)]

/-- The polynomial of the example, `f = (x² - 1)² + y² = y² + (x² - 1)²`, in the coordinates
`x = X 1`, `y = X 0`. -/
def f : MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.X 1 ^ 2 - MvPolynomial.C 1) ^ 2 + MvPolynomial.X 0 ^ 2

@[simp]
theorem finSuccEquiv_X_zero' :
    MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.X (0 : Fin 2)) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

theorem finSuccEquiv_X_one :
    MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
  have h : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
  rw [h]
  exact MvPolynomial.finSuccEquiv_X_succ

/-- Under `finSuccEquiv`, `f` is the monic quadratic `y² + (x²-1)²` in `y`. -/
theorem finSuccEquiv_f :
    MvPolynomial.finSuccEquiv ℝ 1 f =
      Polynomial.X ^ 2 + Polynomial.C (((MvPolynomial.X 0 ^ 2 - MvPolynomial.C 1) ^ 2 :
        MvPolynomial (Fin 1) ℝ)) := by
  simp [f, finSuccEquiv_X_one, add_comm]

/-- **`f = (x² - 1)² + y²` is irreducible in `ℝ[x,y]`.** -/
theorem irreducible_f : Irreducible f := by
  have hsymm : (MvPolynomial.finSuccEquiv ℝ 1).symm
      (Polynomial.X ^ 2 + Polynomial.C (((MvPolynomial.X 0 ^ 2 - MvPolynomial.C 1) ^ 2 :
        MvPolynomial (Fin 1) ℝ))) = f := by
    rw [← finSuccEquiv_f, AlgEquiv.symm_apply_apply]
  rw [← hsymm]
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℝ 1).symm).mpr
    (irreducible_X_sq_add_C sq_sub_one_sq_not_neg_sq)

/-! ## 4. The real zero set of `f` -/

/-- **The real zero set of `f`**: `V(f) = {(0,1), (0,-1)}`, i.e. `x = 0` and `y = ±1`. -/
theorem V_f :
    AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ)) =
      {x : AffineSpace ℝ 2 | (x 1 = 1 ∨ x 1 = -1) ∧ x 0 = 0} := by
  ext x
  rw [AffineSpace.mem_V]
  simp only [Set.mem_singleton_iff, forall_eq, Set.mem_ofPred_eq]
  have hval : MvPolynomial.aeval (x : Fin 2 → ℝ) f = ((x 1) ^ 2 - 1) ^ 2 + (x 0) ^ 2 := by
    simp [f]
  rw [hval]
  constructor
  · intro h
    have h1 : ((x 1) ^ 2 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((x 1) ^ 2 - 1), sq_nonneg (x 0)]
    have h2 : (x 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((x 1) ^ 2 - 1), sq_nonneg (x 0)]
    refine ⟨?_, ?_⟩
    · have h3 : (x 1) ^ 2 = 1 := by
        have h4 : (x 1) ^ 2 - 1 = 0 :=
          (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
        linarith
      exact sq_eq_one_iff.mp h3
    · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  · rintro ⟨h1' | h1', h0⟩ <;> rw [h1', h0] <;> norm_num

/-- The real zero set of `f` is nonempty. -/
theorem V_f_nonempty : (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))).Nonempty :=
  ⟨fun i => if i = 1 then 1 else 0, by rw [V_f]; simp⟩

/-- **`V(f)` is not irreducible.** It is contained in the union of the two closed sets
`{x | x 1 = 1}` and `{x | x 1 = -1}`, and neither of them contains it. -/
theorem V_f_not_irreducible :
    ¬ IsIrreducible (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))) := by
  rw [V_f]
  rintro ⟨-, hpre⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  have h1 : IsClosed {x : AffineSpace ℝ 2 | x 1 = 1} :=
    AffineSpace.isClosed_setOf_coord_eq 1 1
  have h2 : IsClosed {x : AffineSpace ℝ 2 | x 1 = -1} :=
    AffineSpace.isClosed_setOf_coord_eq 1 (-1)
  have hcov : {x : AffineSpace ℝ 2 | (x 1 = 1 ∨ x 1 = -1) ∧ x 0 = 0} ⊆
      {x : AffineSpace ℝ 2 | x 1 = 1} ∪ {x : AffineSpace ℝ 2 | x 1 = -1} := by
    rintro x ⟨hx | hx, -⟩ <;> simp [hx]
  rcases hpre _ _ h1 h2 hcov with h | h
  · have hmem : (fun i : Fin 2 => if i = 1 then (-1 : ℝ) else 0) ∈
        {x : AffineSpace ℝ 2 | (x 1 = 1 ∨ x 1 = -1) ∧ x 0 = 0} := by simp
    have hcon := h hmem
    norm_num at hcon
  · have hmem : (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∈
        {x : AffineSpace ℝ 2 | (x 1 = 1 ∨ x 1 = -1) ∧ x 0 = 0} := by simp
    have hcon := h hmem
    norm_num at hcon

/-! ## 5. The exercise -/

/-- **Hartshorne I.1.12.** There is an irreducible polynomial `f ∈ ℝ[x,y]` whose zero set
`V(f) ⊆ 𝔸²_ℝ` is nonempty and not irreducible. -/
theorem hartshorne_ex_1_12 :
    ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible f ∧
      (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))).Nonempty ∧
      ¬ IsIrreducible (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))) :=
  ⟨f, irreducible_f, V_f_nonempty, V_f_not_irreducible⟩

/-- The example, stated with the polynomial displayed: `(x² - 1)² + y²` is irreducible but
its real zero set is not irreducible. In the coordinates `x = X 1`, `y = X 0` the zero set is
`{(0,1), (0,-1)}`, i.e. `{(1,0), (-1,0)}` in the coordinates `(x,y)`. -/
theorem hartshorne_ex_1_12_explicit :
    Irreducible f ∧ ¬ IsIrreducible (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))) :=
  ⟨irreducible_f, V_f_not_irreducible⟩

/-! ## 6. The cheap example with empty zero set

Hartshorne's convention is that `∅` is not irreducible, so `f = x² + y² + 1`, whose real zero
set is empty (this is exactly the polynomial displayed in Example 1.4.5), is also an answer to
the exercise. We record it for completeness. -/

/-- `x² + y² + 1` is irreducible in `ℝ[x,y]`. -/
theorem irreducible_x_sq_add_y_sq_add_one :
    Irreducible ((MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.C 1 :
      MvPolynomial (Fin 2) ℝ)) := by
  have hmap : MvPolynomial.finSuccEquiv ℝ 1
      ((MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.C 1 :
        MvPolynomial (Fin 2) ℝ)) =
      Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 ^ 2 + MvPolynomial.C 1 :
        MvPolynomial (Fin 1) ℝ)) := by
    simp [finSuccEquiv_X_one, add_comm, add_left_comm, add_assoc]
  have hsymm : (MvPolynomial.finSuccEquiv ℝ 1).symm
      (Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 ^ 2 + MvPolynomial.C 1 :
        MvPolynomial (Fin 1) ℝ))) =
      ((MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.C 1 :
        MvPolynomial (Fin 2) ℝ)) := by
    rw [← hmap, AlgEquiv.symm_apply_apply]
  rw [← hsymm]
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℝ 1).symm).mpr
    (irreducible_X_sq_add_C ?_)
  intro a h
  have h' := congrArg (MvPolynomial.eval (0 : Fin 1 → ℝ)) h
  simp only [map_add, map_pow, map_one, MvPolynomial.eval_X, Pi.zero_apply] at h'
  norm_num at h'
  nlinarith [sq_nonneg (MvPolynomial.eval (0 : Fin 1 → ℝ) a)]

/-- The real zero set of `x² + y² + 1` is empty. -/
theorem V_x_sq_add_y_sq_add_one :
    AffineSpace.V ({(MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.C 1 :
      MvPolynomial (Fin 2) ℝ)} : Set (MvPolynomial (Fin 2) ℝ)) = ∅ := by
  ext x
  rw [AffineSpace.mem_V]
  simp only [Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false, iff_false]
  have hval : MvPolynomial.aeval x
      ((MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.C 1 :
        MvPolynomial (Fin 2) ℝ)) = (x 0) ^ 2 + (x 1) ^ 2 + 1 := by
    simp
  rw [hval]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- The cheap answer to the exercise: an irreducible polynomial whose zero set is empty, hence
not irreducible by Hartshorne's convention. -/
theorem hartshorne_ex_1_12_empty :
    ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible f ∧
      ¬ IsIrreducible (AffineSpace.V ({f} : Set (MvPolynomial (Fin 2) ℝ))) :=
  ⟨_, irreducible_x_sq_add_y_sq_add_one, by
    rw [V_x_sq_add_y_sq_add_one]
    exact fun h => h.1.ne_empty rfl⟩

/-! ## 7. Why the hypothesis "`k` algebraically closed" in Example 1.4.2 is essential

Over an algebraically closed field the implication of Example 1.4.2 does hold, so the example
above is exactly the failure of the hypothesis. This is not part of the exercise, but it
documents that the exercise is a counterexample to a statement with an essential hypothesis,
rather than to a statement that is simply wrong. -/

/-- **Example 1.4.2 over an algebraically closed field.** If `k` is algebraically closed and
`f ∈ k[x,y]` is irreducible, then `V(f)` is irreducible. -/
theorem isIrreducible_V_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (p : MvPolynomial (Fin 2) k) (hp : Irreducible p) :
    IsIrreducible (AffineSpace.V ({p} : Set (MvPolynomial (Fin 2) k))) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hprime : (Ideal.span {p} : Ideal (MvPolynomial (Fin 2) k)).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)
  have hvan : MvPolynomial.vanishingIdeal k
      (AffineSpace.V ({p} : Set (MvPolynomial (Fin 2) k))) = Ideal.span {p} := by
    rw [AffineSpace.V]
    unfold AffineSpace.zeroLocus
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hprime.radical]
  constructor
  · -- nonemptiness: a proper prime ideal has a common zero
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have htop : (Ideal.span {p} : Ideal (MvPolynomial (Fin 2) k)) = (⊤ : Ideal _) := by
      have h := hvan
      rw [hne, MvPolynomial.vanishingIdeal_empty] at h
      exact h.symm
    have hunit : IsUnit p := (Ideal.span_singleton_eq_top).mp htop
    exact hp.not_isUnit hunit
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hcov
    obtain ⟨I, rfl⟩ := AffineSpace.isClosed_iff_exists_zeroLocus.mp hz₁
    obtain ⟨J, rfl⟩ := AffineSpace.isClosed_iff_exists_zeroLocus.mp hz₂
    rw [← AffineSpace.zeroLocus_inf] at hcov
    have hle : I ⊓ J ≤ Ideal.span {p} := by
      have h := (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp hcov
      rwa [hvan] at h
    rcases (Ideal.IsPrime.mul_le (I := I) (J := J) hprime).mp
      (le_trans Ideal.mul_le_inf hle) with h | h
    · exact Or.inl fun q hq q' hq' => hq q' (h hq')
    · exact Or.inr fun q hq q' hq' => hq q' (h hq')

/-! ## 8. Axiom check -/

#print axioms irreducible_X_sq_add_C
#print axioms sq_sub_one_sq_not_neg_sq
#print axioms irreducible_f
#print axioms AffineSpace.zeroLocus_iSup
#print axioms AffineSpace.zeroLocus_inf
#print axioms AffineSpace.sInter_mem_closedSets
#print axioms AffineSpace.isClosed_iff_exists_zeroLocus
#print axioms AffineSpace.isClosed_iff_exists_V
#print axioms AffineSpace.isClosed_singleton
#print axioms AffineSpace.not_isIrreducible_pair
#print axioms V_f
#print axioms V_f_nonempty
#print axioms V_f_not_irreducible
#print axioms hartshorne_ex_1_12
#print axioms hartshorne_ex_1_12_explicit
#print axioms irreducible_x_sq_add_y_sq_add_one
#print axioms V_x_sq_add_y_sq_add_one
#print axioms hartshorne_ex_1_12_empty
#print axioms isIrreducible_V_of_isAlgClosed

end

end Hartshorne77.Ex_I_1_12
