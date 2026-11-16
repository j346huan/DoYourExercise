import Mathlib

/- Natural-language solution: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-27 -/


/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 1.27

Let `k` be an algebraically closed field and `X` an affine variety in `kⁿ` (that is, the
common zero locus of a family of polynomials in `k[t₁,…,tₙ]`), with vanishing ideal
`I(X) = {f | f = 0 on X}` and coordinate ring `P(X) = k[t₁,…,tₙ]/I(X)`.

The exercise asks for a natural bijection between the points of `X` and the maximal ideals
of `P(X)`.  The map sends `x ∈ X` to the kernel `𝔪ₓ` of the evaluation homomorphism
`ev_x : P(X) → k`, `f ↦ f(x)`.

Proof (as in the book):
* `ev_x` is well defined because every element of `I(X)` vanishes at `x ∈ X`;
* it is surjective because constants map to themselves, so `𝔪ₓ = ker ev_x` is maximal;
* if `𝔪ₓ = 𝔪_y` then the coordinate function `tᵢ - xᵢ` lies in `𝔪ₓ`, hence in `𝔪_y`, so
  `yᵢ = xᵢ`: the map is injective;
* for surjectivity, a maximal ideal `𝔪 ⊆ P(X)` pulls back to a maximal ideal `𝔫` of
  `k[t₁,…,tₙ]` containing `I(X)`; by the weak Nullstellensatz (Exercise 5.17, which is
  Mathlib's `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`)
  `𝔫 = (t₁-a₁,…,tₙ-aₙ) = I({a})` for some `a ∈ kⁿ`, and `I(X) ⊆ 𝔫` forces `a ∈ X`, so
  `𝔪 = 𝔪_a`.
-/

open MvPolynomial

namespace AtiyahMcdonald69.Ex_1_27

variable {k : Type*} [Field k] {n : ℕ}

/-- Affine `n`-space `kⁿ` over `k`. -/
abbrev Point (n : ℕ) (k : Type*) : Type _ := Fin n → k

/-- The ideal of all polynomials in `k[t₁,…,tₙ]` vanishing on a set `X ⊆ kⁿ`. -/
abbrev vanishingIdeal (X : Set (Point n k)) : Ideal (MvPolynomial (Fin n) k) :=
  MvPolynomial.vanishingIdeal k X

/-- The coordinate ring `P(X) = k[t₁,…,tₙ]/I(X)`. -/
abbrev CoordinateRing (X : Set (Point n k)) : Type _ :=
  MvPolynomial (Fin n) k ⧸ vanishingIdeal X

/-- `X ⊆ kⁿ` is an affine variety when it is the common zero locus of a family of
polynomials, i.e. `X = V(S)` for some `S ⊆ k[t₁,…,tₙ]`. -/
def IsAffineVariety (X : Set (Point n k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), X = MvPolynomial.zeroLocus k (Ideal.span S)

/-- An affine variety is the zero locus of its vanishing ideal: `V(I(X)) = X`. -/
theorem IsAffineVariety.zeroLocus_vanishingIdeal {X : Set (Point n k)}
    (hX : IsAffineVariety X) : MvPolynomial.zeroLocus k (vanishingIdeal X) = X := by
  obtain ⟨S, rfl⟩ := hX
  refine le_antisymm ?_ (MvPolynomial.zeroLocus_vanishingIdeal_le _)
  intro x hx
  rw [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
  exact fun p hp => hx p (MvPolynomial.le_vanishingIdeal_zeroLocus (Ideal.span S) hp)

/-- The two standard readings of "affine variety" agree: `X` is the common zero locus of a
family of polynomials iff `X = V(I(X))`. -/
theorem isAffineVariety_iff {X : Set (Point n k)} :
    IsAffineVariety X ↔ MvPolynomial.zeroLocus k (vanishingIdeal X) = X := by
  refine ⟨IsAffineVariety.zeroLocus_vanishingIdeal, fun h => ⟨vanishingIdeal X, ?_⟩⟩
  rw [Ideal.span_eq]
  exact h.symm

/-- Evaluation at a point `x ∈ X`, as a ring homomorphism `P(X) →+* k`. -/
noncomputable def evaluation (X : Set (Point n k)) {x : Point n k} (hx : x ∈ X) :
    CoordinateRing X →+* k :=
  Ideal.Quotient.lift (vanishingIdeal X) (MvPolynomial.aeval x).toRingHom fun _ hp =>
    MvPolynomial.mem_vanishingIdeal_iff.1 hp x hx

/-- The value of the evaluation map at the class of a polynomial `p` is `p(x)`. -/
@[simp]
theorem evaluation_mk (X : Set (Point n k)) {x : Point n k} (hx : x ∈ X)
    (p : MvPolynomial (Fin n) k) :
    evaluation X hx (Ideal.Quotient.mk (vanishingIdeal X) p) = MvPolynomial.aeval x p :=
  Ideal.Quotient.lift_mk _ _ _

/-- The evaluation map `P(X) →+* k` is surjective (constants map to themselves). -/
theorem evaluation_surjective (X : Set (Point n k)) {x : Point n k} (hx : x ∈ X) :
    Function.Surjective (evaluation X hx) := by
  intro c
  exact ⟨Ideal.Quotient.mk (vanishingIdeal X) (MvPolynomial.C c), by simp⟩

/-- The maximal ideal `𝔪ₓ = ker (ev_x)` of the coordinate ring `P(X)` attached to a point
`x ∈ X`. -/
noncomputable def pointToMaximalSpectrum (X : Set (Point n k)) (x : X) :
    MaximalSpectrum (CoordinateRing X) :=
  ⟨RingHom.ker (evaluation X x.2),
    RingHom.ker_isMaximal_of_surjective (evaluation X x.2) (evaluation_surjective X x.2)⟩

/-- The maximal ideal `𝔪ₓ` is the kernel of evaluation at `x`. -/
@[simp]
theorem mem_pointToMaximalSpectrum_iff (X : Set (Point n k)) (x : X)
    (q : CoordinateRing X) :
    q ∈ (pointToMaximalSpectrum X x : Ideal (CoordinateRing X)) ↔
      evaluation X x.2 q = 0 :=
  Iff.rfl

/-- The map `x ↦ 𝔪ₓ` is injective: the coordinate functions `tᵢ - xᵢ` separate points. -/
public theorem pointToMaximalSpectrum_injective (X : Set (Point n k)) :
    Function.Injective (pointToMaximalSpectrum X) := by
  intro x y hxy
  have hker : RingHom.ker (evaluation X x.2) = RingHom.ker (evaluation X y.2) := by
    simpa [pointToMaximalSpectrum] using congrArg MaximalSpectrum.asIdeal hxy
  apply Subtype.ext
  funext i
  have hmem : Ideal.Quotient.mk (vanishingIdeal X)
      (MvPolynomial.X i - MvPolynomial.C (x.1 i)) ∈ RingHom.ker (evaluation X x.2) := by
    rw [RingHom.mem_ker, evaluation_mk]
    simp
  rw [hker, RingHom.mem_ker, evaluation_mk] at hmem
  simp at hmem
  exact (sub_eq_zero.1 hmem).symm

variable [IsAlgClosed k]

/-- The weak Nullstellensatz in the form needed here (Exercise 5.17): over an algebraically
closed field, every maximal ideal of `k[t₁,…,tₙ]` is the vanishing ideal of a point. -/
public theorem weak_nullstellensatz (I : Ideal (MvPolynomial (Fin n) k)) (hI : I.IsMaximal) :
    ∃ a : Point n k, I = MvPolynomial.vanishingIdeal k {a} :=
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hI

/-- The map `x ↦ 𝔪ₓ` is surjective onto the maximal ideals of the coordinate ring. -/
public theorem pointToMaximalSpectrum_surjective (X : Set (Point n k)) (hX : IsAffineVariety X) :
    Function.Surjective (pointToMaximalSpectrum X) := by
  rintro ⟨m, hm⟩
  have hcomap : (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal X)) m).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (f := Ideal.Quotient.mk (vanishingIdeal X))
      Ideal.Quotient.mk_surjective (K := m) (H := hm)
  obtain ⟨a, ha⟩ := weak_nullstellensatz (k := k) (n := n) _ hcomap
  have hI_le : vanishingIdeal X ≤ Ideal.comap (Ideal.Quotient.mk (vanishingIdeal X)) m := by
    intro p hp
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hp]
    exact m.zero_mem
  have hmemX : a ∈ X := by
    rw [← IsAffineVariety.zeroLocus_vanishingIdeal (k := k) hX, MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff a p).1 (ha ▸ hI_le hp)
  refine ⟨⟨a, hmemX⟩, ?_⟩
  refine MaximalSpectrum.ext ?_
  change RingHom.ker (evaluation X hmemX) = m
  have hkereq : RingHom.ker (MvPolynomial.aeval a).toRingHom =
      MvPolynomial.vanishingIdeal k {a} := by
    ext p
    simp
  have hcomp : Ideal.comap (Ideal.Quotient.mk (vanishingIdeal X))
      (RingHom.ker (evaluation X hmemX)) = RingHom.ker (MvPolynomial.aeval a).toRingHom := by
    rw [RingHom.comap_ker]
    rfl
  rw [← Ideal.map_comap_of_surjective (f := Ideal.Quotient.mk (vanishingIdeal X))
      Ideal.Quotient.mk_surjective m, ha, ← hkereq, ← hcomp,
    Ideal.map_comap_of_surjective (f := Ideal.Quotient.mk (vanishingIdeal X))
      Ideal.Quotient.mk_surjective]

/-- Atiyah–Macdonald, Chapter 1, Exercise 1.27: for an affine variety `X ⊆ kⁿ` over an
algebraically closed field `k`, evaluation at points gives a natural bijection between the
elements of `X` and the maximal ideals of the coordinate ring `P(X) = k[t₁,…,tₙ]/I(X)`. -/
public theorem solution (X : Set (Point n k)) (hX : IsAffineVariety X) :
    Function.Bijective (pointToMaximalSpectrum X) :=
  ⟨pointToMaximalSpectrum_injective X, pointToMaximalSpectrum_surjective X hX⟩

/-- Exercise 1.27, packaged as an equivalence `X ≃ MaxSpec P(X)`. -/
noncomputable def solutionEquiv (X : Set (Point n k)) (hX : IsAffineVariety X) :
    X ≃ MaximalSpectrum (CoordinateRing X) :=
  Equiv.ofBijective (pointToMaximalSpectrum X) (solution X hX)

/-- Exercise 1.27 with the equivalent hypothesis `X = V(I(X))` (see
`isAffineVariety_iff`) in place of "`X` is an affine variety". -/
public theorem solution_of_zeroLocus (X : Set (Point n k))
    (hX : MvPolynomial.zeroLocus k (vanishingIdeal X) = X) :
    Function.Bijective (pointToMaximalSpectrum X) :=
  solution X (isAffineVariety_iff.2 hX)

/-- Every maximal ideal of `P(X)` is the ideal `𝔪ₓ` of functions vanishing at a unique
point `x ∈ X`. -/
public theorem existsUnique_pointToMaximalSpectrum (X : Set (Point n k)) (hX : IsAffineVariety X)
    (m : MaximalSpectrum (CoordinateRing X)) :
    ∃! x : X, pointToMaximalSpectrum X x = m :=
  (solution X hX).existsUnique m

end AtiyahMcdonald69.Ex_1_27

#print axioms AtiyahMcdonald69.Ex_1_27.solution
