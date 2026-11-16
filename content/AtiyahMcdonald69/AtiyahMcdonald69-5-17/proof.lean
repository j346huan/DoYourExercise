/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 5, Exercise 17.

Original statement (Chapter 5, page 69, exercise 17):

  "Let X be an affine algebraic variety in kⁿ, where k is an algebraically closed
   field, and let I(X) be the ideal of X in the polynomial ring k[t₁, ..., tₙ]
   (Chapter 1, Exercise 27). If I(X) ≠ (1) then X is not empty.
   Deduce that every maximal ideal in the ring k[t₁, ..., tₙ] is of the form
   (t₁ - a₁, ..., tₙ - aₙ) where aᵢ ∈ k."

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-17

Omitted data, recovered from the source
---------------------------------------
Chapter 1, Exercise 27 defines: an *affine algebraic variety* in kⁿ (k algebraically
closed) is the set of common zeros of a set of polynomial equations, i.e. X = {x ∈ kⁿ |
∀ p ∈ S, p(x) = 0} for some set S ⊆ k[t₁, ..., tₙ] (this is the predicate
`IsAffineAlgebraicVariety` below), and I(X) is the ideal of all polynomials vanishing
on X (`MvPolynomial.vanishingIdeal k X`).  In particular X is Zariski closed.  Note
that for an *arbitrary* subset X ⊆ kⁿ the displayed implication would be vacuous
(I(∅) = (1) by definition); its mathematical content is the weak Nullstellensatz, and
X being an algebraic variety is exactly the hypothesis that makes it non-vacuous.

What is proved below
--------------------
* `exists_aeval_eq_zero_of_ne_top` — weak Nullstellensatz in the form the natural
  proof establishes: every proper ideal of k[t₁, ..., tₙ] (k algebraically closed)
  has a common zero in kⁿ.
* `exists_algHom_quotient_of_ne_top` — the same statement for the coordinate ring:
  a proper ideal has a nonzero quotient, and that quotient admits a k-algebra
  homomorphism to k ("evaluation at y₁ = ⋯ = y_r = 0 extends to a homomorphism
  A → k" in the natural proof).
* `affineAlgebraicVariety_nonempty` — the first sentence of the exercise.
* `vanishingIdeal_singleton_eq_span` — the ideal of the single point a ∈ kⁿ is
  (t₁ - a₁, ..., tₙ - aₙ); `pointIdeal a` is that ideal, `pointIdeal_injective` says
  that it determines a, and `quotient_pointIdeal_algEquiv` shows that its quotient
  is k (the natural proof's "each such ideal has quotient k").
* `isMaximal_iff_exists_pointIdeal` — the "Deduce that ..." sentence: the maximal
  ideals of k[t₁, ..., tₙ] are exactly the ideals (t₁ - a₁, ..., tₙ - aₙ).
* `solution` — the two assertions of the exercise bundled together.

Proof route
-----------
This follows the natural proof.  If I(X) ≠ (1) then the coordinate ring
k[t₁, ..., tₙ]/I(X) is nontrivial; a proper ideal I is contained in a maximal ideal m,
and the residue field k[t₁, ..., tₙ]/m is a finitely generated k-algebra, hence
algebraic over k (Noether normalisation / Zariski's lemma; in Mathlib this is
`MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing`, integrality of the
residue field of a maximal ideal, which is where the natural proof's use of Exercise
5.16 enters), so that — k being algebraically closed — there is a k-algebra map
k[t₁, ..., tₙ]/m → k (`IsAlgClosed.lift`, the natural proof's Exercise 5.2).
Evaluating the variables there gives a common zero a of m, hence of I, hence a point
of X.  For the deduction, a maximal ideal m has a common zero a, so m ⊆ I({a}); the
latter is a maximal ideal, hence m = I({a}) = (t₁ - a₁, ..., tₙ - aₙ), and conversely
that ideal has residue field k.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_17

open MvPolynomial

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

/-! ### The ideal (t₁ - a₁, ..., tₙ - aₙ) -/

omit [IsAlgClosed k] in
/-- The ideal `(t₁ - a₁, ..., tₙ - aₙ)` of the polynomial ring `k[t₁, ..., tₙ]`. -/
noncomputable def pointIdeal (a : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range fun i => X i - C (a i))

omit [IsAlgClosed k] in
/-- For any point `x` of `k^σ`, a polynomial `p` differs from the constant
polynomial `p(x)` by an element of the ideal `(tᵢ - xᵢ)`. -/
theorem sub_C_aeval_mem_span {σ : Type*} (x : σ → k) (p : MvPolynomial σ k) :
    p - C (aeval x p) ∈ Ideal.span (Set.range fun i => X i - C (x i)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have h : p + q - C (aeval x (p + q)) = (p - C (aeval x p)) + (q - C (aeval x q)) := by
        simp only [map_add]
        ring
      rw [h]
      exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
      have hgen : X i - C (x i) ∈ Ideal.span (Set.range fun i => X i - C (x i)) :=
        Ideal.subset_span ⟨i, rfl⟩
      have h1 : p * (X i - C (x i)) ∈ Ideal.span (Set.range fun i => X i - C (x i)) :=
        Ideal.mul_mem_left _ p hgen
      have h2 : (p - C (aeval x p)) * C (x i) ∈
          Ideal.span (Set.range fun i => X i - C (x i)) :=
        Ideal.mul_mem_right _ _ hp
      have h : p * X i - C (aeval x (p * X i)) =
          p * (X i - C (x i)) + (p - C (aeval x p)) * C (x i) := by
        simp only [map_mul, aeval_X]
        ring
      rw [h]
      exact Ideal.add_mem _ h1 h2

omit [IsAlgClosed k] in
/-- The ideal of polynomials vanishing at a single point `x` is generated by the
polynomials `tᵢ - xᵢ`. -/
theorem vanishingIdeal_singleton_eq_span {σ : Type*} (x : σ → k) :
    vanishingIdeal k {x} = Ideal.span (Set.range fun i => X i - C (x i)) := by
  refine le_antisymm ?_ ?_
  · intro p hp
    have h := sub_C_aeval_mem_span x p
    rwa [(mem_vanishingIdeal_singleton_iff x p).mp hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_vanishingIdeal_singleton_iff x (X i - C (x i))).mpr (by simp)

omit [IsAlgClosed k] in
/-- The ideal `(t₁ - a₁, ..., tₙ - aₙ)` is the ideal of polynomials vanishing at `a`. -/
theorem pointIdeal_eq_vanishingIdeal (a : Fin n → k) :
    pointIdeal a = vanishingIdeal k {a} :=
  (vanishingIdeal_singleton_eq_span a).symm

omit [IsAlgClosed k] in
/-- The point `a` is determined by the ideal `(t₁ - a₁, ..., tₙ - aₙ)`. -/
theorem pointIdeal_injective : Function.Injective (pointIdeal (k := k) (n := n)) := by
  intro a b hab
  funext i
  have hmem : X i - C (a i) ∈ vanishingIdeal k {b} := by
    rw [← pointIdeal_eq_vanishingIdeal b, ← hab]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h := (mem_vanishingIdeal_singleton_iff b (X i - C (a i))).mp hmem
  simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h
  exact h.symm

/-- The residue field of `(t₁ - a₁, ..., tₙ - aₙ)` is `k` (the natural proof's
"each such ideal has quotient k"). -/
noncomputable def quotient_pointIdeal_algEquiv (a : Fin n → k) :
    (MvPolynomial (Fin n) k ⧸ pointIdeal a) ≃ₐ[k] k := by
  have hker : ∀ p ∈ pointIdeal a, aeval a p = 0 := by
    intro p hp
    rw [pointIdeal_eq_vanishingIdeal a] at hp
    exact (mem_vanishingIdeal_singleton_iff a p).mp hp
  let f : (MvPolynomial (Fin n) k ⧸ pointIdeal a) →ₐ[k] k :=
    Ideal.Quotient.liftₐ (pointIdeal a) (aeval a) hker
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨(Ideal.Quotient.mkₐ k (pointIdeal a)) (C z), ?_⟩
    simp [f]
  have hinj : Function.Injective f := by
    have hzero : ∀ x, f x = 0 → x = 0 := by
      intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hp0 : aeval a p = 0 := by simpa [f] using hx
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      rw [pointIdeal_eq_vanishingIdeal a]
      exact (mem_vanishingIdeal_singleton_iff a p).mpr hp0
    intro x y hxy
    have h0 : x - y = 0 := hzero (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h0
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

/-! ### Weak Nullstellensatz: every proper ideal has a common zero -/

set_option linter.style.haveILetI false in
/-- **Weak Nullstellensatz.** Every proper ideal of `k[t₁, ..., tₙ]`, with `k`
algebraically closed, has a common zero in `kⁿ`. -/
theorem exists_aeval_eq_zero_of_ne_top (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ a : Fin n → k, ∀ p ∈ I, aeval a p = 0 := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  haveI : m.IsMaximal := hm
  -- the residue field of a maximal ideal is algebraic over `k`
  have halg : Algebra.IsAlgebraic k (MvPolynomial (Fin n) k ⧸ m) := by
    rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
    exact MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing m
  -- a `k`-algebra map of the residue field into the algebraically closed field `k`
  let φ : (MvPolynomial (Fin n) k ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨fun i => φ (Ideal.Quotient.mk m (X i)), ?_⟩
  intro p hp
  have hzero : Ideal.Quotient.mk m p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIm hp)
  have hcomp : aeval (fun i => φ (Ideal.Quotient.mk m (X i))) = φ.comp (Ideal.Quotient.mkₐ k m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Ideal.Quotient.mkₐ_eq_mk]
  rw [hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hzero, map_zero]

/-- The coordinate ring of a proper ideal has a `k`-point: the map
"evaluate at y₁ = ⋯ = y_r = 0" of the natural proof. -/
theorem exists_algHom_quotient_of_ne_top (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    Nonempty ((MvPolynomial (Fin n) k ⧸ I) →ₐ[k] k) := by
  obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_ne_top I hI
  exact ⟨Ideal.Quotient.liftₐ I (aeval a) ha⟩

/-- Restatement of the weak Nullstellensatz in the language of zero loci: a
proper ideal of `k[t₁, ..., tₙ]` has a nonempty zero locus. -/
theorem zeroLocus_nonempty_of_ne_top (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    (zeroLocus k I).Nonempty := by
  obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_ne_top I hI
  exact ⟨a, mem_zeroLocus_iff.mpr ha⟩

/-- Every maximal ideal of `k[t₁, ..., tₙ]` is `(t₁ - a₁, ..., tₙ - aₙ)` for some
point `a ∈ kⁿ`; conversely each such ideal is maximal. -/
theorem isMaximal_iff_exists_pointIdeal (m : Ideal (MvPolynomial (Fin n) k)) :
    m.IsMaximal ↔ ∃ a : Fin n → k, m = pointIdeal a := by
  constructor
  · intro hm
    obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_ne_top m hm.ne_top
    have hle : m ≤ vanishingIdeal k {a} := fun p hp =>
      (mem_vanishingIdeal_singleton_iff a p).mpr (ha p hp)
    have hmax : (vanishingIdeal k {a} : Ideal (MvPolynomial (Fin n) k)).IsMaximal :=
      inferInstance
    exact ⟨a, (hm.eq_of_le hmax.ne_top hle).trans (pointIdeal_eq_vanishingIdeal a).symm⟩
  · rintro ⟨a, rfl⟩
    rw [pointIdeal_eq_vanishingIdeal a]
    infer_instance

/-! ### The first sentence of the exercise: an affine algebraic variety -/

omit [IsAlgClosed k] in
/-- An affine algebraic variety in `kⁿ`: the set of common zeros of a set of
polynomial equations (Chapter 1, Exercise 27). -/
def IsAffineAlgebraicVariety (X : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), X = {x : Fin n → k | ∀ p ∈ S, aeval x p = 0}

/-- If the ideal of an affine algebraic variety `X ⊆ kⁿ` is not the unit ideal,
then `X` is not empty. -/
theorem affineAlgebraicVariety_nonempty (X : Set (Fin n → k))
    (hX : IsAffineAlgebraicVariety X) (h : vanishingIdeal k X ≠ ⊤) : X.Nonempty := by
  obtain ⟨S, rfl⟩ := hX
  -- the ideal generated by the equations is contained in the ideal of the variety
  have hS : Ideal.span S ≤
      vanishingIdeal k {x : Fin n → k | ∀ p ∈ S, aeval x p = 0} :=
    Ideal.span_le.mpr fun p hp x hx => hx p hp
  have hne : Ideal.span S ≠ ⊤ := fun htop => h (top_le_iff.mp (htop ▸ hS))
  obtain ⟨a, ha⟩ := exists_aeval_eq_zero_of_ne_top (Ideal.span S) hne
  exact ⟨a, fun p hp => ha p (Ideal.subset_span hp)⟩

omit [IsAlgClosed k] in
/-- For an affine algebraic variety `X ⊆ kⁿ`, the ideal `I(X)` is the unit ideal
exactly when `X` is empty; contrapositively, `I(X) ≠ (1)` is equivalent to
`X ≠ ∅`. -/theorem vanishingIdeal_eq_top_iff (X : Set (Fin n → k))
    (hX : IsAffineAlgebraicVariety X) : vanishingIdeal k X = ⊤ ↔ X = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ vanishingIdeal k X := h ▸ Submodule.mem_top
    have := (mem_vanishingIdeal_iff.mp h1) x hx
    simp at this
  · rintro rfl
    exact vanishingIdeal_empty

/-- The complete form of the first sentence of the exercise: for an affine
algebraic variety `X ⊆ kⁿ`, `X` is nonempty if and only if its ideal is not the
unit ideal. -/
theorem nonempty_iff_vanishingIdeal_ne_top (X : Set (Fin n → k))
    (hX : IsAffineAlgebraicVariety X) : X.Nonempty ↔ vanishingIdeal k X ≠ ⊤ := by
  refine ⟨fun ⟨x, hx⟩ h => ?_, fun h => affineAlgebraicVariety_nonempty X hX h⟩
  have h1 : (1 : MvPolynomial (Fin n) k) ∈ vanishingIdeal k X := h ▸ Submodule.mem_top
  have h0 : aeval x (1 : MvPolynomial (Fin n) k) = 0 := (mem_vanishingIdeal_iff.mp h1) x hx
  simp at h0

/-! ### The exercise -/

/-- **Atiyah–Macdonald, Exercise 5.17.** For an algebraically closed field `k`,
(1) an affine algebraic variety `X ⊆ kⁿ` whose ideal is not the unit ideal is
nonempty, and (2) every maximal ideal of `k[t₁, ..., tₙ]` is
`(t₁ - a₁, ..., tₙ - aₙ)` for some `a ∈ kⁿ`. -/
theorem solution :
    (∀ X : Set (Fin n → k), IsAffineAlgebraicVariety X →
        vanishingIdeal k X ≠ ⊤ → X.Nonempty) ∧
      (∀ m : Ideal (MvPolynomial (Fin n) k), m.IsMaximal ↔ ∃ a : Fin n → k, m = pointIdeal a) :=
  ⟨fun _ hX h => affineAlgebraicVariety_nonempty _ hX h, isMaximal_iff_exists_pointIdeal⟩

end AtiyahMcdonald69.Ex_5_17

#print axioms AtiyahMcdonald69.Ex_5_17.sub_C_aeval_mem_span
#print axioms AtiyahMcdonald69.Ex_5_17.vanishingIdeal_singleton_eq_span
#print axioms AtiyahMcdonald69.Ex_5_17.pointIdeal_injective
#print axioms AtiyahMcdonald69.Ex_5_17.exists_aeval_eq_zero_of_ne_top
#print axioms AtiyahMcdonald69.Ex_5_17.exists_algHom_quotient_of_ne_top
#print axioms AtiyahMcdonald69.Ex_5_17.zeroLocus_nonempty_of_ne_top
#print axioms AtiyahMcdonald69.Ex_5_17.vanishingIdeal_eq_top_iff
#print axioms AtiyahMcdonald69.Ex_5_17.isMaximal_iff_exists_pointIdeal
#print axioms AtiyahMcdonald69.Ex_5_17.affineAlgebraicVariety_nonempty
#print axioms AtiyahMcdonald69.Ex_5_17.quotient_pointIdeal_algEquiv
#print axioms AtiyahMcdonald69.Ex_5_17.nonempty_iff_vanishingIdeal_ne_top
#print axioms AtiyahMcdonald69.Ex_5_17.solution
