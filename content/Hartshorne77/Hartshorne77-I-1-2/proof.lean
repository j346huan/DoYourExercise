/-
Copyright (c) 2026 ...
Released under Apache 2.0 license as described in the file LICENSE.

# Hartshorne, Algebraic Geometry, Exercise I.1.2: the twisted cubic curve

Statement (Hartshorne 1977, *Algebraic Geometry*, Chapter I, §1, Exercise 1.2):

> *The Twisted Cubic Curve.* Let `Y ⊆ A³` be the set `Y = {(t, t², t³) | t ∈ k}`.
> Show that `Y` is an affine variety of dimension 1. Find generators for the ideal
> `I(Y)`. Show that `A(Y)` is isomorphic to a polynomial ring in one variable over `k`.

Throughout, `k` is an algebraically closed field (Hartshorne fixes such a `k` in Chapter I).
We work with the classical point-set objects: `A^n = k^n` with the Zariski topology, the
vanishing ideal `I(Y) ⊆ k[x₁,…,xₙ]`, and the affine coordinate ring `A(Y) = k[x₁,…,xₙ]/I(Y)`.

Main results (all in `namespace Hartshorne77.Ex_I_1_2`):

* `twistedCubic_eq_range` : the literal source definition, `Y = {(t, t², t³) | t ∈ k}`.
* `twistedCubic_eq_zeroLocus` : `Y = V(y - x², z - x³)`, i.e. `Y` is Zariski closed.
* `vanishingIdeal_twistedCubic` : `I(Y) = (y - x², z - x³)`.
* `twistedCubicIdeal_isPrime` : the ideal `(y - x², z - x³)` is prime.
* `coordinateRingEquiv` : `A(Y) ≃ₖ k[t]`.
* `twistedCubic_irreducible` : `Y` is irreducible, hence an affine variety.
* `topologicalKrullDim_twistedCubic` : `dim Y = 1`
  (topological Krull dimension = sup of lengths of chains of irreducible closed subsets,
  which is Hartshorne's definition of `dim`).
* `ringKrullDim_coordinateRing` : `dim A(Y) = 1` as well.
* `hartshorne_I_1_2` : all assertions of the exercise bundled together.

## Source fidelity

The local transcription `.scratch/reference/hartshorne-1977.txt` (and its HTML source) has
dropped the exercise list of Chapter I, §1 (the OCR jumps from Corollary 1.4 straight into the
§2 exercises), so the statement of I.1.2 was cross-checked against two independent public
sources quoting the book:

* the solutions wiki `hartshorne-ag-solutions.wikidot.com/chapter-1-section-1`, which quotes
  "1.2. *The Twisted Cubic Curve.* Let `Y ⊆ A³` be the set `Y = {(t,t²,t³) | t ∈ k}`. Show that
  `Y` is an affine variety of dimension 1. Find generators for the ideal `I(Y)`. Show that
  `A(Y)` is isomorphic to a polynomial ring in one variable over `k`.";
* the solutions blog `hartshornesolutions.blogspot.com/2015/06/chapter-1-exercise-12-twisted-cubic.html`,
  which states the same problem.

All statements above are stated for an algebraically closed field `k`, as fixed in Chapter I;
the ideal computation, the coordinate-ring computation and the dimension count in fact only need
`k` infinite (and `Field k` for the topology), which is the form in which they are proved here.
-/

import Mathlib

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_1_2

/-! ## Affine space and the Zariski topology -/

variable (k : Type*) [Field k]

/-- Affine `n`-space over `k`, as a set of points: `A^n = k^n`. -/
abbrev AffineSpace (n : ℕ) : Type _ := Fin n → k

variable {k}

/-- A subset of `A^n` is Zariski closed if it is the zero locus of an ideal of polynomials. -/
def IsZariskiClosed (n : ℕ) (S : Set (AffineSpace k n)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) k), S = MvPolynomial.zeroLocus k I

theorem isZariskiClosed_empty (n : ℕ) : IsZariskiClosed (k := k) n ∅ :=
  ⟨⊤, by simp⟩

theorem isZariskiClosed_univ (n : ℕ) : IsZariskiClosed (k := k) n Set.univ :=
  ⟨⊥, by simp⟩

/-- Arbitrary intersections of zero loci are zero loci. -/
theorem zeroLocus_iInter {n : ℕ} {ι : Type*} (I : ι → Ideal (MvPolynomial (Fin n) k)) :
    (⋂ i, MvPolynomial.zeroLocus k (I i)) = MvPolynomial.zeroLocus k (⨆ i, I i) := by
  ext x
  simp only [Set.mem_iInter, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have hle : (⨆ i, I i) ≤ RingHom.ker (MvPolynomial.aeval (R := k) x) := by
      refine iSup_le fun i => ?_
      intro q hq
      exact h i q hq
    have := hle hp
    simpa using this
  · intro h i p hp
    exact h p (le_iSup I i hp)

/-- The union of two zero loci is the zero locus of the intersection of the ideals. -/
theorem zeroLocus_union {n : ℕ} (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J =
      MvPolynomial.zeroLocus k (I ⊓ J) := by
  refine le_antisymm ?_ ?_
  · rintro x (hx | hx) p hp
    · exact hx p hp.1
    · exact hx p hp.2
  · intro x hx
    by_contra h
    simp only [Set.mem_union, not_or, MvPolynomial.mem_zeroLocus_iff, not_forall] at h
    obtain ⟨⟨p, hpI, hp0⟩, ⟨q, hqJ, hq0⟩⟩ := h
    have hmem : p * q ∈ I ⊓ J := ⟨I.mul_mem_right q hpI, J.mul_mem_left p hqJ⟩
    have hzero := hx (p * q) hmem
    rw [map_mul] at hzero
    exact mul_ne_zero hp0 hq0 hzero

/-- Arbitrary intersections of Zariski closed sets are Zariski closed. -/
theorem isZariskiClosed_sInter {n : ℕ} {S : Set (Set (AffineSpace k n))}
    (hS : ∀ s ∈ S, IsZariskiClosed n s) : IsZariskiClosed (k := k) n (⋂₀ S) := by
  classical
  let J : S → Ideal (MvPolynomial (Fin n) k) := fun s => Classical.choose (hS s.1 s.2)
  have hJ : ∀ s : S, (s : Set (AffineSpace k n)) = MvPolynomial.zeroLocus k (J s) :=
    fun s => Classical.choose_spec (hS s.1 s.2)
  refine ⟨⨆ s : S, J s, ?_⟩
  rw [← zeroLocus_iInter (fun s : S => J s)]
  ext x
  simp only [Set.mem_sInter, Set.mem_iInter]
  constructor
  · intro h s
    rw [← hJ s]
    exact h s.1 s.2
  · intro h s hs
    have h' := h ⟨s, hs⟩
    rw [← hJ ⟨s, hs⟩] at h'
    exact h'

theorem isZariskiClosed_union {n : ℕ} {S T : Set (AffineSpace k n)}
    (hS : IsZariskiClosed n S) (hT : IsZariskiClosed n T) : IsZariskiClosed n (S ∪ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  exact ⟨I ⊓ J, zeroLocus_union I J⟩

/-- The Zariski topology on `A^n = k^n`: a set is open iff its complement is a zero locus. -/
@[instance_reducible]
def zariskiTopology (n : ℕ) : TopologicalSpace (AffineSpace k n) where
  IsOpen S := IsZariskiClosed (k := k) n Sᶜ
  isOpen_univ := by simpa using isZariskiClosed_empty (k := k) n
  isOpen_inter S T hS hT := by
    rw [Set.compl_inter]
    exact isZariskiClosed_union hS hT
  isOpen_sUnion S hS := by
    rw [Set.compl_sUnion]
    refine isZariskiClosed_sInter ?_
    rintro t ⟨s, hs, rfl⟩
    exact hS s hs

attribute [instance 100] zariskiTopology

variable {n : ℕ}

theorem isOpen_iff {S : Set (AffineSpace k n)} : IsOpen S ↔ IsZariskiClosed (k := k) n Sᶜ :=
  Iff.rfl

theorem isClosed_iff {S : Set (AffineSpace k n)} : IsClosed S ↔ IsZariskiClosed (k := k) n S := by
  constructor
  · intro h
    have h' := h.isOpen_compl
    rwa [isOpen_iff, compl_compl] at h'
  · intro h
    exact ⟨by rw [isOpen_iff, compl_compl]; exact h⟩

theorem isClosed_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    IsClosed (MvPolynomial.zeroLocus k I) :=
  isClosed_iff.2 ⟨I, rfl⟩
section TwistedCubic

variable (k : Type*) [Field k]

/-! ## The twisted cubic curve -/

/-- The twisted cubic curve `Y = {(t, t², t³) | t ∈ k} ⊆ A³`. -/
def twistedCubic : Set (AffineSpace k 3) :=
  {P | P 1 = (P 0) ^ 2 ∧ P 2 = (P 0) ^ 3}

/-- The point `(t, t², t³)` of the twisted cubic. -/
def cubicPoint (t : k) : AffineSpace k 3 := ![t, t ^ 2, t ^ 3]

/-- The ideal `(y - x², z - x³) ⊆ k[x,y,z]`. -/
def twistedCubicIdeal : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span
    ({MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2, MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3} :
      Set (MvPolynomial (Fin 3) k))

theorem cubicPoint_mem (t : k) : cubicPoint k t ∈ twistedCubic k := by
  simp [cubicPoint, twistedCubic]

theorem eq_cubicPoint_of_mem {P : AffineSpace k 3} (hP : P ∈ twistedCubic k) :
    P = cubicPoint k (P 0) := by
  funext j
  fin_cases j <;> simp [cubicPoint, twistedCubic] at hP ⊢
  · exact hP.1
  · exact hP.2

theorem twistedCubic_eq_zeroLocus :
    twistedCubic k = MvPolynomial.zeroLocus k (twistedCubicIdeal k) := by
  rw [twistedCubicIdeal, MvPolynomial.zeroLocus_span]
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩ p (rfl | rfl)
    · simp [h1]
    · simp [h2]
  · intro h
    constructor
    · have := h (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2) (Or.inl rfl)
      simpa only [map_sub, map_pow, MvPolynomial.aeval_X, sub_eq_zero] using this
    · have := h (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3) (Or.inr rfl)
      simpa only [map_sub, map_pow, MvPolynomial.aeval_X, sub_eq_zero] using this

theorem isClosed_twistedCubic : IsClosed (twistedCubic k) := by
  rw [isClosed_iff]
  exact ⟨_, twistedCubic_eq_zeroLocus k⟩

/-! ### The substitution `x ↦ t`, `y ↦ t²`, `z ↦ t³` -/

/-- The `k`-algebra homomorphism `k[x,y,z] → k[t]` given by `x ↦ t`, `y ↦ t²`, `z ↦ t³`. -/
def subst : MvPolynomial (Fin 3) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (![Polynomial.X, Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 3 → Polynomial k)

/-- The `k`-algebra homomorphism `k[t] → k[x,y,z]` given by `t ↦ x`. -/
def embed : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k :=
  Polynomial.aeval (MvPolynomial.X 0)

@[simp]
theorem subst_X_zero : subst k (MvPolynomial.X 0) = Polynomial.X := by
  simp [subst]

@[simp]
theorem subst_X_one : subst k (MvPolynomial.X 1) = Polynomial.X ^ 2 := by
  simp [subst]

@[simp]
theorem subst_X_two : subst k (MvPolynomial.X 2) = Polynomial.X ^ 3 := by
  simp [subst]

@[simp]
theorem embed_X : embed k Polynomial.X = MvPolynomial.X 0 := by
  simp [embed]

/-- Every polynomial is congruent to a polynomial in `x` modulo `(y - x², z - x³)`. -/
theorem sub_embed_subst_mem (f : MvPolynomial (Fin 3) k) :
    f - embed k (subst k f) ∈ twistedCubicIdeal k := by
  let S : Subalgebra k (MvPolynomial (Fin 3) k) :=
    { carrier := {f | f - embed k (subst k f) ∈ twistedCubicIdeal k}
      zero_mem' := by
        simp
      add_mem' := by
        intro f g hf hg
        change f + g - embed k (subst k (f + g)) ∈ twistedCubicIdeal k
        have hf' : f - embed k (subst k f) ∈ twistedCubicIdeal k := hf
        have hg' : g - embed k (subst k g) ∈ twistedCubicIdeal k := hg
        have key : f + g - embed k (subst k (f + g)) =
            (f - embed k (subst k f)) + (g - embed k (subst k g)) := by
          rw [map_add, map_add]
          ring
        rw [key]
        exact add_mem hf' hg'
      mul_mem' := by
        intro f g hf hg
        change f * g - embed k (subst k (f * g)) ∈ twistedCubicIdeal k
        have hf' : f - embed k (subst k f) ∈ twistedCubicIdeal k := hf
        have hg' : g - embed k (subst k g) ∈ twistedCubicIdeal k := hg
        have key : f * g - embed k (subst k (f * g)) =
            (f - embed k (subst k f)) * g + embed k (subst k f) * (g - embed k (subst k g)) := by
          rw [map_mul, map_mul]
          ring
        rw [key]
        exact add_mem (Ideal.mul_mem_right g (twistedCubicIdeal k) hf')
          (Ideal.mul_mem_left (twistedCubicIdeal k) (embed k (subst k f)) hg')
      algebraMap_mem' := by
        intro r
        change algebraMap k (MvPolynomial (Fin 3) k) r - embed k (subst k (algebraMap k (MvPolynomial (Fin 3) k) r)) ∈ twistedCubicIdeal k
        have h1 : subst k (algebraMap k (MvPolynomial (Fin 3) k) r) = algebraMap k (Polynomial k) r :=
          (subst k).commutes r
        have h2 : embed k (algebraMap k (Polynomial k) r) = algebraMap k (MvPolynomial (Fin 3) k) r :=
          (embed k).commutes r
        rw [h1, h2, sub_self]
        exact Submodule.zero_mem _ }
  have htop : (⊤ : Subalgebra k (MvPolynomial (Fin 3) k)) ≤ S := by
    rw [← MvPolynomial.adjoin_range_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change MvPolynomial.X 0 - embed k (subst k (MvPolynomial.X 0)) ∈ twistedCubicIdeal k
      simp [subst, embed]
    · change MvPolynomial.X 1 - embed k (subst k (MvPolynomial.X 1)) ∈ twistedCubicIdeal k
      have hsub : embed k (subst k (MvPolynomial.X 1)) = MvPolynomial.X 0 ^ 2 := by simp [subst, embed]
      rw [hsub]
      exact Ideal.subset_span (by simp)
    · change MvPolynomial.X 2 - embed k (subst k (MvPolynomial.X 2)) ∈ twistedCubicIdeal k
      have hsub : embed k (subst k (MvPolynomial.X 2)) = MvPolynomial.X 0 ^ 3 := by simp [subst, embed]
      rw [hsub]
      exact Ideal.subset_span (by simp)
  exact htop (by simp)

/-- `subst f = 0` iff `f` lies in `(y - x², z - x³)`. -/
theorem subst_eq_zero_iff (f : MvPolynomial (Fin 3) k) :
    subst k f = 0 ↔ f ∈ twistedCubicIdeal k := by
  constructor
  · intro h
    have h' := sub_embed_subst_mem k f
    rwa [h, map_zero, sub_zero] at h'
  · intro h
    have hgen : ({MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2, MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3} :
        Set (MvPolynomial (Fin 3) k)) ⊆
        RingHom.ker (subst k : MvPolynomial (Fin 3) k →+* Polynomial k) := by
      rintro q (rfl | rfl)
      · simp
      · simp
    have hle : twistedCubicIdeal k ≤ RingHom.ker (subst k : MvPolynomial (Fin 3) k →+* Polynomial k) :=
      Ideal.span_le.2 hgen
    have := hle h
    simpa using this

/-- The kernel of `subst` is `(y - x², z - x³)`. -/
theorem ker_subst :
    RingHom.ker (subst k : MvPolynomial (Fin 3) k →+* Polynomial k) = twistedCubicIdeal k := by
  ext f
  rw [RingHom.mem_ker]
  exact subst_eq_zero_iff k f

/-- The ideal `(y - x², z - x³)` is prime. -/
theorem twistedCubicIdeal_isPrime : (twistedCubicIdeal k).IsPrime := by
  rw [← ker_subst (k := k)]
  exact RingHom.ker_isPrime _

/-- Evaluating `subst f` at `t` is evaluating `f` at the point `(t, t², t³)`. -/
theorem aeval_cubicPoint (t : k) (f : MvPolynomial (Fin 3) k) :
    MvPolynomial.aeval (R := k) (cubicPoint k t) f = (subst k f).eval t := by
  have h : (MvPolynomial.aeval (R := k) (cubicPoint k t)) = (Polynomial.aeval t).comp (subst k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cubicPoint, subst]
  rw [h]
  rfl

/-- The vanishing ideal of the twisted cubic is `(y - x², z - x³)`. -/
theorem vanishingIdeal_twistedCubic [IsAlgClosed k] :
    MvPolynomial.vanishingIdeal k (twistedCubic k) = twistedCubicIdeal k := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf
    rw [← subst_eq_zero_iff]
    refine Polynomial.funext fun t => ?_
    have h1 := aeval_cubicPoint k t f
    rw [hf (cubicPoint k t) (cubicPoint_mem k t)] at h1
    simpa using h1.symm
  · intro f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro P hP
    have hsub : subst k f = 0 := (subst_eq_zero_iff k f).2 hf
    rw [eq_cubicPoint_of_mem (k := k) hP, aeval_cubicPoint, hsub]
    simp

/-- The affine coordinate ring of a subset `Y ⊆ A^n`. -/
abbrev CoordinateRing (n : ℕ) (Y : Set (AffineSpace k n)) : Type _ :=
  MvPolynomial (Fin n) k ⧸ MvPolynomial.vanishingIdeal k Y

/-- `A(Y) ≅ k[t]` for the twisted cubic `Y`. -/
def coordinateRingEquiv [IsAlgClosed k] :
    CoordinateRing (k := k) 3 (twistedCubic k) ≃ₐ[k] Polynomial k := by
  have hsurj : Function.Surjective (subst k) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, rfl⟩ := hp
      obtain ⟨b, rfl⟩ := hq
      exact ⟨a + b, by simp⟩
    | monomial n a =>
      refine ⟨MvPolynomial.C a * MvPolynomial.X 0 ^ n, ?_⟩
      simp [subst, Polynomial.C_mul_X_pow_eq_monomial]
  have hEq : MvPolynomial.vanishingIdeal k (twistedCubic k) =
      RingHom.ker (subst k : MvPolynomial (Fin 3) k →+* Polynomial k) := by
    rw [vanishingIdeal_twistedCubic, ker_subst]
  exact (Ideal.quotientEquivAlgOfEq k hEq).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)

/-- The coordinate ring of the twisted cubic has Krull dimension one. -/
theorem ringKrullDim_coordinateRing [IsAlgClosed k] :
    ringKrullDim (CoordinateRing (k := k) 3 (twistedCubic k)) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv (coordinateRingEquiv k).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
/-! ### The affine line `A¹` -/

/-- The `k`-algebra homomorphism `k[x] → k[t]`, `x ↦ t`. -/
def substOne : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun _ => Polynomial.X)

/-- The `k`-algebra homomorphism `k[t] → k[x]`, `t ↦ x`. -/
def embedOne : Polynomial k →ₐ[k] MvPolynomial (Fin 1) k :=
  Polynomial.aeval (MvPolynomial.X 0)

theorem substOne_embedOne : (substOne k).comp (embedOne k) = AlgHom.id k (Polynomial k) := by
  apply Polynomial.algHom_ext
  simp [substOne, embedOne]

theorem embedOne_substOne : (embedOne k).comp (substOne k) = AlgHom.id k (MvPolynomial (Fin 1) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  simp [substOne, embedOne]

/-- `k[x] ≅ k[t]`. -/
def polyEquiv : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofAlgHom (substOne k) (embedOne k) (substOne_embedOne k) (embedOne_substOne k)

theorem embedOne_apply_substOne (f : MvPolynomial (Fin 1) k) :
    embedOne k (substOne k f) = f :=
  AlgHom.congr_fun (embedOne_substOne k) f

/-- Evaluating `k[t]` at `x 0`. -/
theorem aeval_embedOne (x : AffineSpace k 1) (p : Polynomial k) :
    MvPolynomial.aeval (R := k) x (embedOne k p) = p.eval (x 0) := by
  have h : (MvPolynomial.aeval (R := k) x).comp (embedOne k) = Polynomial.aeval (x 0) := by
    apply Polynomial.algHom_ext
    simp [embedOne]
  rw [← AlgHom.comp_apply, h]
  rfl

theorem aeval_polyEquiv (x : AffineSpace k 1) (f : MvPolynomial (Fin 1) k) :
    MvPolynomial.aeval (R := k) x f = (polyEquiv k f).eval (x 0) := by
  conv_lhs => rw [← embedOne_apply_substOne (k := k) f]
  rw [aeval_embedOne]
  rfl

/-- On the affine line, Zariski closed sets are exactly the finite sets and the whole line. -/
theorem isClosed_iff_finite_or_univ {S : Set (AffineSpace k 1)} :
    IsClosed S ↔ S = Set.univ ∨ S.Finite := by
  constructor
  · intro hS
    obtain ⟨I, rfl⟩ := isClosed_iff.1 hS
    by_cases hI : I = ⊥
    · left
      rw [hI]
      simp
    · right
      have hex : ∃ f ∈ I, f ≠ 0 := by
        by_contra h
        simp only [not_exists, not_and, not_not] at h
        refine hI ?_
        ext f
        exact ⟨fun hf => by simpa using h f hf,
          fun hf => by rw [show f = 0 from by simpa using hf]; exact I.zero_mem⟩
      obtain ⟨f, hfI, hf0⟩ := hex
      have hp0 : polyEquiv k f ≠ 0 := by
        intro h
        exact hf0 ((polyEquiv k).injective (by rw [h, map_zero]))
      have hfin : {x : AffineSpace k 1 | (polyEquiv k f).eval (x 0) = 0}.Finite := by
        have himg : {x : AffineSpace k 1 | (polyEquiv k f).eval (x 0) = 0} =
            (fun a : k => (fun _ : Fin 1 => a)) '' {a : k | (polyEquiv k f).IsRoot a} := by
          ext x
          constructor
          · intro hx
            exact ⟨x 0, by simpa [Polynomial.IsRoot] using hx, by funext i; fin_cases i; rfl⟩
          · rintro ⟨a, ha, rfl⟩
            simpa [Polynomial.IsRoot] using ha
        rw [himg]
        exact (Polynomial.finite_setOfPred_isRoot hp0).image _
      refine Set.Finite.subset hfin ?_
      intro x hx
      rw [MvPolynomial.mem_zeroLocus_iff] at hx
      have hx' := hx f hfI
      rw [aeval_polyEquiv] at hx'
      simpa using hx'
  · rintro (rfl | hfin)
    · exact isClosed_univ
    · have hT1 : T1Space (AffineSpace k 1) := ⟨fun x => by
        rw [isClosed_iff]
        refine ⟨Ideal.span {MvPolynomial.X 0 - MvPolynomial.C (x 0)}, ?_⟩
        rw [MvPolynomial.zeroLocus_span]
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro rfl
          intro p hp
          rw [hp]
          simp
        · intro h
          have hy : y 0 - x 0 = 0 := by
            have h' := h (MvPolynomial.X 0 - MvPolynomial.C (x 0)) rfl
            simpa using h'
          funext i
          fin_cases i
          exact sub_eq_zero.mp hy⟩
      exact @Set.Finite.isClosed (AffineSpace k 1) _ hT1 S hfin

/-- The affine line over an infinite field is infinite. -/
instance infiniteAffineLine [Infinite k] : Infinite (AffineSpace k 1) :=
  Infinite.of_injective (fun a : k => (fun _ : Fin 1 => a)) (fun a b h => by simpa using congrFun h 0)

/-- The affine line over an infinite field is irreducible. -/
theorem irreducibleSpace_affineLine [Infinite k] : IrreducibleSpace (AffineSpace k 1) := by
  refine { isPreirreducible_univ := ?_, toNonempty := ?_ }
  · intro u v hu hv hu' hv'
    simp only [Set.univ_inter] at hu' hv' ⊢
    have huc : (uᶜ : Set (AffineSpace k 1)).Finite := by
      rcases (isClosed_iff_finite_or_univ (k := k)).1 hu.isClosed_compl with h | h
      · have hu_empty : u = ∅ := by rw [← compl_compl u, h, Set.compl_univ]
        exact absurd hu' (by rw [hu_empty]; simp)
      · exact h
    have hvc : (vᶜ : Set (AffineSpace k 1)).Finite := by
      rcases (isClosed_iff_finite_or_univ (k := k)).1 hv.isClosed_compl with h | h
      · have hv_empty : v = ∅ := by rw [← compl_compl v, h, Set.compl_univ]
        exact absurd hv' (by rw [hv_empty]; simp)
      · exact h
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have huniv : (Set.univ : Set (AffineSpace k 1)) = uᶜ ∪ vᶜ := by
      rw [← Set.compl_inter, h, Set.compl_empty]
    have hfin : (Set.univ : Set (AffineSpace k 1)).Finite := by
      rw [huniv]
      exact huc.union hvc
    exact Infinite.not_finite (Set.finite_univ_iff.1 hfin)
  · exact Nonempty.intro (fun _ : Fin 1 => 0)
/-- A space whose closed sets are the finite sets and the whole space is irreducible
(provided it is infinite). -/
theorem irreducibleSpace_of_isClosed_iff {X : Type*} [TopologicalSpace X] [Infinite X]
    (h : ∀ S : Set X, IsClosed S ↔ S = Set.univ ∨ S.Finite) : IrreducibleSpace X := by
  refine { isPreirreducible_univ := ?_, toNonempty := inferInstance }
  intro u v hu hv hu' hv'
  simp only [Set.univ_inter] at hu' hv' ⊢
  have huc : (uᶜ : Set X).Finite := by
    rcases (h uᶜ).1 hu.isClosed_compl with h' | h'
    · have hu_empty : u = ∅ := by rw [← compl_compl u, h', Set.compl_univ]
      exact absurd hu' (by rw [hu_empty]; simp)
    · exact h'
  have hvc : (vᶜ : Set X).Finite := by
    rcases (h vᶜ).1 hv.isClosed_compl with h' | h'
    · have hv_empty : v = ∅ := by rw [← compl_compl v, h', Set.compl_univ]
      exact absurd hv' (by rw [hv_empty]; simp)
    · exact h'
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have huniv : (Set.univ : Set X) = uᶜ ∪ vᶜ := by
    rw [← Set.compl_inter, hne, Set.compl_empty]
  have hfin : (Set.univ : Set X).Finite := huniv ▸ huc.union hvc
  exact Infinite.not_finite (Set.finite_univ_iff.1 hfin)

theorem irreducibleSpace_affineLine' [Infinite k] : IrreducibleSpace (AffineSpace k 1) :=
  irreducibleSpace_of_isClosed_iff fun _ => isClosed_iff_finite_or_univ (k := k)

/-- A space with at least two points whose closed sets are the finite sets and the whole space
has topological Krull dimension one (Hartshorne's `dim`). -/
theorem topologicalKrullDim_eq_one_of_isClosed_iff {X : Type*} [TopologicalSpace X] [Infinite X]
    (h : ∀ S : Set X, IsClosed S ↔ S = Set.univ ∨ S.Finite) :
    topologicalKrullDim X = 1 := by
  have hIS : IrreducibleSpace X := irreducibleSpace_of_isClosed_iff h
  have huniv : IsIrreducible (Set.univ : Set X) := @IrreducibleSpace.isIrreducible_univ X _ hIS
  have hIrred : ∀ Z : TopologicalSpace.IrreducibleCloseds X, Z.1 = Set.univ ∨ ∃ x, Z.1 = {x} := by
    intro Z
    rcases (h Z.1).1 Z.isClosed' with hZ | hZ
    · exact Or.inl hZ
    · refine Or.inr ?_
      have hsub : Z.1.Subsingleton := by
        intro x hx y hy
        by_contra hne
        have hxc : IsClosed ({x} : Set X) := (h {x}).2 (Or.inr (Set.finite_singleton x))
        have hdc : IsClosed (Z.1 \ {x}) := (h _).2 (Or.inr (hZ.subset Set.sdiff_subset))
        have hpre := Z.isIrreducible'.2 {x}ᶜ (Z.1 \ {x})ᶜ hxc.isOpen_compl hdc.isOpen_compl
          ⟨y, hy, by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact fun h => hne h.symm⟩ ⟨x, hx, by simp⟩
        obtain ⟨z, hz1, hz2, hz3⟩ := hpre
        exact hz3 ⟨hz1, hz2⟩
      obtain ⟨x, hx⟩ := Z.isIrreducible'.1
      exact ⟨x, hsub.eq_singleton_of_mem hx⟩
  have hle : topologicalKrullDim X ≤ 1 := by
    rw [topologicalKrullDim, Order.krullDim_le_one_iff]
    intro Z
    rcases hIrred Z with hZ | ⟨x, hZ⟩
    · right
      intro W _
      change (W.1 : Set X) ⊆ Z.1
      rw [hZ]
      exact Set.subset_univ _
    · left
      intro W hW
      change (Z.1 : Set X) ⊆ W.1
      rw [hZ]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨w, hw⟩ := W.isIrreducible'.1
      have hwZ : w ∈ Z.1 := hW hw
      rw [hZ, Set.mem_singleton_iff] at hwZ
      rwa [hwZ] at hw
  have hge : 1 ≤ topologicalKrullDim X := by
    rw [topologicalKrullDim, Order.one_le_krullDim_iff]
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨y, hyx⟩ : ∃ y : X, y ≠ x := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hfin : (Set.univ : Set X).Finite :=
        Set.Finite.subset (Set.finite_singleton x) (by intro z _; exact hcon z)
      exact Infinite.not_finite (Set.finite_univ_iff.1 hfin)
    refine ⟨⟨{x}, isIrreducible_singleton, (h {x}).2 (Or.inr (Set.finite_singleton x))⟩,
      ⟨Set.univ, huniv, isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne ?_ ?_
    · change ({x} : Set X) ⊆ Set.univ
      exact Set.subset_univ _
    · intro heq
      have hset : ({x} : Set X) = Set.univ := congrArg (fun Z : TopologicalSpace.IrreducibleCloseds X => Z.1) heq
      have : y ∈ ({x} : Set X) := by rw [hset]; trivial
      exact hyx (Set.mem_singleton_iff.1 this)
  exact le_antisymm hle hge

/-- The affine line `A¹` over an infinite field has dimension one. -/
theorem topologicalKrullDim_affineLine [Infinite k] :
    topologicalKrullDim (AffineSpace k 1) = 1 :=
  topologicalKrullDim_eq_one_of_isClosed_iff fun _ => isClosed_iff_finite_or_univ (k := k)
/-! ### Polynomial maps and the homeomorphism `Y ≅ A¹` -/

/-- The map on points induced by a `k`-algebra homomorphism of polynomial rings. -/
def pointMap {n m : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k) :
    AffineSpace k m → AffineSpace k n :=
  fun x j => MvPolynomial.aeval (R := k) x (g (MvPolynomial.X j))

theorem aeval_pointMap {n m : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k)
    (x : AffineSpace k m) (p : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval (R := k) (pointMap k g x) p = MvPolynomial.aeval (R := k) x (g p) := by
  have h : (MvPolynomial.aeval (R := k) (pointMap k g x)) =
      (MvPolynomial.aeval (R := k) x).comp g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [pointMap]
  rw [h]
  rfl

/-- Polynomial maps are continuous for the Zariski topology. -/
theorem continuous_pointMap {n m : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k) :
    Continuous (pointMap k g) := by
  rw [continuous_iff_isClosed]
  intro S hS
  rw [isClosed_iff] at hS ⊢
  obtain ⟨I, rfl⟩ := hS
  refine ⟨Ideal.map (g : MvPolynomial (Fin n) k →+* MvPolynomial (Fin m) k) I, ?_⟩
  ext x
  rw [Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have hker : Ideal.map (g : MvPolynomial (Fin n) k →+* MvPolynomial (Fin m) k) I ≤
        RingHom.ker (MvPolynomial.aeval (R := k) x : MvPolynomial (Fin m) k →+* k) := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      have hq' := h q hq
      rwa [aeval_pointMap] at hq'
    have := hker hp
    simpa using this
  · intro h p hp
    rw [aeval_pointMap]
    exact h (g p) (Ideal.mem_map_of_mem (g : MvPolynomial (Fin n) k →+* MvPolynomial (Fin m) k) hp)

/-- The parametrization `A¹ → A³`, `t ↦ (t, t², t³)`, as a polynomial map. -/
def paramHom : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 1) k :=
  MvPolynomial.aeval
    (![MvPolynomial.X 0, MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 ^ 3] : Fin 3 → MvPolynomial (Fin 1) k)

/-- The projection `A³ → A¹`, `(x, y, z) ↦ x`, as a polynomial map. -/
def projHom : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X 0)

theorem pointMap_paramHom (x : AffineSpace k 1) :
    pointMap k (paramHom k) x = cubicPoint k (x 0) := by
  funext j
  fin_cases j <;> simp [pointMap, paramHom, cubicPoint]

theorem pointMap_projHom (P : AffineSpace k 3) :
    pointMap k (projHom k) P = fun _ => P 0 := by
  funext j
  fin_cases j
  simp [pointMap, projHom]

/-- The tautological bijection `Y ≅ A¹` given by `(t, t², t³) ↦ t` and `t ↦ (t, t², t³)`. -/
def twistedCubicEquiv : ↥(twistedCubic k) ≃ AffineSpace k 1 where
  toFun P := fun _ => P.1 0
  invFun x := ⟨cubicPoint k (x 0), cubicPoint_mem k (x 0)⟩
  left_inv P := by
    apply Subtype.ext
    rw [eq_cubicPoint_of_mem (k := k) P.2]
  right_inv x := by
    funext j
    fin_cases j
    rfl

/-- The twisted cubic is homeomorphic to the affine line. -/
def twistedCubicHomeomorph : ↥(twistedCubic k) ≃ₜ AffineSpace k 1 where
  toEquiv := twistedCubicEquiv k
  continuous_toFun := by
    have h : Continuous (fun P : ↥(twistedCubic k) => pointMap k (projHom k) P.1) :=
      (continuous_pointMap (k := k) (projHom k)).comp continuous_subtype_val
    exact h.congr fun P => pointMap_projHom k P.1
  continuous_invFun := by
    have h : Continuous (fun x : AffineSpace k 1 =>
        (⟨pointMap k (paramHom k) x, by
          rw [pointMap_paramHom]
          exact cubicPoint_mem k (x 0)⟩ : ↥(twistedCubic k))) :=
      Continuous.subtype_mk (continuous_pointMap (k := k) (paramHom k)) _
    exact h.congr fun x => by
      apply Subtype.ext
      exact pointMap_paramHom k x

/-! ### The twisted cubic is an affine variety of dimension one -/

theorem twistedCubic_irreducible [IsAlgClosed k] : IsIrreducible (twistedCubic k) := by
  rw [isIrreducible_iff_irreducibleSpace]
  exact (twistedCubicHomeomorph k).irreducibleSpace_iff.mpr (irreducibleSpace_affineLine' (k := k))

theorem topologicalKrullDim_twistedCubic [IsAlgClosed k] :
    topologicalKrullDim ↥(twistedCubic k) = 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq (twistedCubicHomeomorph k)
    (twistedCubicHomeomorph k).isHomeomorph]
  exact topologicalKrullDim_affineLine (k := k)

/-- **Hartshorne I.1.2, first assertion**: the twisted cubic is an affine variety of
dimension one, i.e. an irreducible Zariski closed subset of `A³` of dimension `1`. -/
theorem twistedCubic_isAffineVariety [IsAlgClosed k] :
    IsClosed (twistedCubic k) ∧ IsIrreducible (twistedCubic k) ∧
      topologicalKrullDim ↥(twistedCubic k) = 1 :=
  ⟨isClosed_twistedCubic k, twistedCubic_irreducible k, topologicalKrullDim_twistedCubic k⟩

end TwistedCubic

end Hartshorne77.Ex_I_1_2

namespace Hartshorne77.Ex_I_1_2

variable (k : Type*) [Field k]

/-- Literal form of the source statement: `Y` is the image of `t ↦ (t, t², t³)`. -/
theorem twistedCubic_eq_range : twistedCubic k = Set.range (cubicPoint k) := by
  ext P
  constructor
  · intro hP
    exact ⟨P 0, (eq_cubicPoint_of_mem (k := k) hP).symm⟩
  · rintro ⟨t, rfl⟩
    exact cubicPoint_mem k t

/-- **Hartshorne, Algebraic Geometry, Exercise I.1.2**, bundled form (with `k` algebraically
closed, as fixed in Chapter I).

The twisted cubic `Y = {(t, t², t³) | t ∈ k} ⊆ A³` is Zariski closed and irreducible (an affine
variety) of dimension `1`; its vanishing ideal is generated by `y - x²` and `z - x³` and is prime;
and the affine coordinate ring `A(Y) = k[x,y,z]/I(Y)` is isomorphic to the polynomial ring `k[t]`
in one variable. -/
theorem hartshorne_I_1_2 [IsAlgClosed k] :
    twistedCubic k = Set.range (cubicPoint k) ∧
      IsClosed (twistedCubic k) ∧
      IsIrreducible (twistedCubic k) ∧
      topologicalKrullDim ↥(twistedCubic k) = 1 ∧
      MvPolynomial.vanishingIdeal k (twistedCubic k) = twistedCubicIdeal k ∧
      (twistedCubicIdeal k).IsPrime ∧
      Nonempty (CoordinateRing (k := k) 3 (twistedCubic k) ≃ₐ[k] Polynomial k) :=
  ⟨twistedCubic_eq_range k, isClosed_twistedCubic k, twistedCubic_irreducible k,
    topologicalKrullDim_twistedCubic k, vanishingIdeal_twistedCubic k,
    twistedCubicIdeal_isPrime k, ⟨coordinateRingEquiv k⟩⟩

end Hartshorne77.Ex_I_1_2

/-! ### Axiom audit -/

namespace Hartshorne77.Ex_I_1_2

#print axioms twistedCubic_eq_range
#print axioms vanishingIdeal_twistedCubic
#print axioms twistedCubicIdeal_isPrime
#print axioms coordinateRingEquiv
#print axioms ringKrullDim_coordinateRing
#print axioms twistedCubic_irreducible
#print axioms topologicalKrullDim_twistedCubic
#print axioms twistedCubic_isAffineVariety
#print axioms hartshorne_I_1_2

end Hartshorne77.Ex_I_1_2
