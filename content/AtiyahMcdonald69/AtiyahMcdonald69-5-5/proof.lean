/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 5, Exercise 5.5.

**Statement** (Chapter 5, Exercise 5). Let `A ⊆ B` be rings such that `B` is integral over `A`.
  (i) If `x ∈ A` is a unit in `B`, then it is a unit in `A`.
  (ii) The Jacobson radical of `A` is the contraction of the Jacobson radical of `B`,
       i.e. `J(A) = J(B) ∩ A`.

**Formalization choices.** "`A ⊆ B`" is rendered as an `A`-algebra structure on `B` whose
structure map is injective, `FaithfulSMul A B` (Mathlib's standard way of speaking about a
subring), and "`B` is integral over `A`" as `Algebra.IsIntegral A B`.  The two parts are proved
as `isUnit_of_isUnit_algebraMap` and `jacobson_eq_comap` and packaged as `solution`; the
equivalent form for an injective integral ring homomorphism `f : A →+* B` is
`solution_of_ringHom`, the book's literal subring form is `solution_subring`, and the
set-theoretic form `J(A) = A ∩ J(B)` is `jacobson_eq_inter`.
The injectivity built into `A ⊆ B` is substantive: it cannot be dropped, see
`injectivity_is_needed` at the end of the file, an explicit counterexample with `A = ℚ × ℚ`,
`B = ℚ` and the first projection.

**Proofs.** Part (i) is the book's argument ("multiply an integrality relation for `x⁻¹` by
`x^{n-1}`") in ideal-theoretic form: a unit of `B` generates the unit ideal of `B`, and an
integral extension reflects the unit ideal (`Ideal.map_eq_top_iff`, whose proof is Mathlib's
going-up argument; the direct polynomial argument is `RingHom.IsIntegral.isLocalHom`).
Part (ii) is the book's argument: a maximal ideal of `B` contracts to a maximal ideal of `A`
(Corollary 5.8) and every maximal ideal of `A` is the contraction of a maximal ideal of `B`
(lying over).  Both going-up inputs are Mathlib theorems, so no theory is re-derived here.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_5

/-! ### The Jacobson radical as an intersection of maximal ideals -/

/-- The Jacobson radical of a commutative ring is the intersection of its maximal ideals. -/
theorem mem_jacobson_iff {R : Type*} [CommRing R] {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ I : Ideal R, I.IsMaximal → x ∈ I := by
  rw [Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
  exact ⟨fun h I hI => h hI, fun h I hI => h I hI⟩

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-! ### Exercise 5.5 (i) -/

/-- **Atiyah–Macdonald, Exercise 5.5 (i).** If `x ∈ A` becomes a unit in the integral extension
`B`, then `x` is already a unit in `A`. -/
theorem isUnit_of_isUnit_algebraMap [Algebra.IsIntegral A B] [FaithfulSMul A B] {x : A}
    (hx : IsUnit (algebraMap A B x)) : IsUnit x := by
  -- `x` generates the unit ideal of `B`.
  have hmap : Ideal.map (algebraMap A B) (Ideal.span {x}) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    exact hx
  -- Integral extensions reflect the unit ideal (book: `x⁻¹ ∈ B` satisfies a monic equation).
  have htop : Ideal.span {x} = ⊤ :=
    (Ideal.map_eq_top_iff (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)
      (algebraMap_isIntegral_iff.mpr inferInstance)).mp hmap
  exact Ideal.span_singleton_eq_top.mp htop

/-! ### Exercise 5.5 (ii) -/

/-- **Atiyah–Macdonald, Exercise 5.5 (ii).** The Jacobson radical of `A` is the contraction of
the Jacobson radical of the integral extension `B`: `J(A) = J(B) ∩ A`. -/
theorem jacobson_eq_comap [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Ring.jacobson A = (Ring.jacobson B).comap (algebraMap A B) := by
  ext x
  rw [mem_jacobson_iff, Ideal.mem_comap, mem_jacobson_iff]
  constructor
  · -- a maximal ideal of `B` contracts to a maximal ideal of `A` (Corollary 5.8)
    intro hx J hJ
    exact (Ideal.mem_comap (f := algebraMap A B)).mp
      (hx _ (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J))
  · -- every maximal ideal of `A` is the contraction of a maximal ideal of `B` (lying over)
    intro hx I hI
    obtain ⟨J, hJmax, hJ⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := A) (S := B) I
    have hJI : I = J.comap (algebraMap A B) := by
      rw [← Ideal.under_def]; exact (Ideal.liesOver_iff J I).mp hJ
    rw [hJI]
    exact (Ideal.mem_comap (f := algebraMap A B)).mpr (hx J hJmax)

/-- Exercise 5.5 (ii) phrased with `Ideal.jacobson ⊥`, the intersection of all maximal ideals
of a ring as an ideal. -/
theorem jacobson_bot_eq_comap [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Ideal.jacobson (⊥ : Ideal A) = (Ideal.jacobson (⊥ : Ideal B)).comap (algebraMap A B) := by
  rw [Ideal.jacobson_bot, Ideal.jacobson_bot, jacobson_eq_comap (A := A) (B := B)]

/-- Exercise 5.5 (ii) in the book's set-theoretic form: `J(A) = A ∩ J(B)`. -/
theorem jacobson_eq_inter [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    ((Ring.jacobson A : Ideal A) : Set A) =
      algebraMap A B ⁻¹' ((Ring.jacobson B : Ideal B) : Set B) := by
  rw [jacobson_eq_comap (A := A) (B := B), Ideal.coe_comap]

/-- **Atiyah–Macdonald, Exercise 5.5**, both parts at once. -/
theorem solution [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    (∀ x : A, IsUnit (algebraMap A B x) → IsUnit x) ∧
      Ring.jacobson A = (Ring.jacobson B).comap (algebraMap A B) :=
  ⟨fun _ hx => isUnit_of_isUnit_algebraMap hx, jacobson_eq_comap⟩

/-- Exercise 5.5 in the form of an injective integral ring homomorphism `f : A →+* B`
(the literal "`A ⊆ B`" of the book, with the inclusion named `f`). -/
theorem solution_of_ringHom {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hinj : Function.Injective f) (hint : f.IsIntegral) :
    (∀ x : A, IsUnit (f x) → IsUnit x) ∧ Ring.jacobson A = (Ring.jacobson B).comap f := by
  let : Algebra A B := f.toAlgebra
  have hfaith : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hInt : Algebra.IsIntegral A B := ⟨fun x => hint x⟩
  exact solution

/-- Exercise 5.5 in the book's literal form: `A` is a subring of `B` and `B` is integral over
`A`.  Here `algebraMap A B` is the inclusion `A ⊆ B`. -/
theorem solution_subring {B : Type*} [CommRing B] (A : Subring B) [Algebra.IsIntegral A B] :
    (∀ x : A, IsUnit (algebraMap A B x) → IsUnit x) ∧
      Ring.jacobson A = (Ring.jacobson B).comap (algebraMap A B) :=
  solution

/-! ### Injectivity of `A → B` is a genuine hypothesis

The book assumes `A ⊆ B`.  If the structure map is not injective both statements fail, as the
first projection `ℚ × ℚ → ℚ` (an integral, even surjective, ring map) shows. -/

section Counterexample

/-- The first projection `ℚ × ℚ → ℚ`, viewed as an algebra structure. -/
local instance : Algebra (ℚ × ℚ) ℚ := (RingHom.fst ℚ ℚ).toAlgebra

/-- `ℚ` is integral over `ℚ × ℚ` (the map is even surjective). -/
theorem counterexample_isIntegral : Algebra.IsIntegral (ℚ × ℚ) ℚ :=
  Algebra.isIntegral_of_surjective (fun x => ⟨(x, 0), rfl⟩)

/-- Exercise 5.5 (i) fails without injectivity: `(1, 0)` becomes `1` in `ℚ`. -/
theorem counterexample_part_i_fails :
    ∃ x : ℚ × ℚ, IsUnit (algebraMap (ℚ × ℚ) ℚ x) ∧ ¬ IsUnit x := by
  refine ⟨(1, 0), ?_, ?_⟩
  · change IsUnit (1 : ℚ)
    exact isUnit_one
  · -- the second projection would send a unit of `ℚ × ℚ` to the unit `0` of `ℚ`
    intro h
    have h' : IsUnit ((0 : ℚ)) := by simpa using h.map (RingHom.snd ℚ ℚ)
    simp at h'

/-- Exercise 5.5 (ii) fails without injectivity: `J(ℚ × ℚ) = 0`, but its contraction to `ℚ`
along the first projection is `J(ℚ) = 0`, whose preimage is the kernel of the projection. -/
theorem counterexample_part_ii_fails :
    Ring.jacobson (ℚ × ℚ) ≠ (Ring.jacobson ℚ).comap (algebraMap (ℚ × ℚ) ℚ) := by
  intro h
  -- `(0, 1)` lies in the right-hand side: it maps to `0 ∈ J(ℚ)`.
  have h1 : (0, 1) ∈ (Ring.jacobson ℚ).comap (algebraMap (ℚ × ℚ) ℚ) := by
    rw [Ideal.mem_comap]
    change (RingHom.fst ℚ ℚ) (0, 1) ∈ Ring.jacobson ℚ
    simp
  rw [← h, mem_jacobson_iff] at h1
  -- hence it would lie in every maximal ideal of `ℚ × ℚ`, e.g. in `ker (snd : ℚ × ℚ → ℚ)`.
  have h2 : (0, 1) ∈ RingHom.ker (RingHom.snd ℚ ℚ) :=
    h1 _ (RingHom.ker_isMaximal_of_surjective (RingHom.snd ℚ ℚ) fun x => ⟨(0, x), rfl⟩)
  simp at h2

/-- The structure map `ℚ × ℚ → ℚ` (first projection) is not injective. -/
theorem counterexample_not_injective : ¬ FaithfulSMul (ℚ × ℚ) ℚ := by
  intro h
  have hinj : Function.Injective (algebraMap (ℚ × ℚ) ℚ) :=
    (faithfulSMul_iff_algebraMap_injective (ℚ × ℚ) ℚ).mp h
  have h01 : (algebraMap (ℚ × ℚ) ℚ) (0, 1) = (algebraMap (ℚ × ℚ) ℚ) (0, 0) := by
    change (RingHom.fst ℚ ℚ) (0, 1) = (RingHom.fst ℚ ℚ) (0, 0)
    rfl
  have := hinj h01
  simp at this

/-- Both hypotheses of Exercise 5.5 together with the failures when injectivity is dropped. -/
theorem injectivity_is_needed :
    Algebra.IsIntegral (ℚ × ℚ) ℚ ∧ ¬ FaithfulSMul (ℚ × ℚ) ℚ ∧
      (∃ x : ℚ × ℚ, IsUnit (algebraMap (ℚ × ℚ) ℚ x) ∧ ¬ IsUnit x) ∧
      Ring.jacobson (ℚ × ℚ) ≠ (Ring.jacobson ℚ).comap (algebraMap (ℚ × ℚ) ℚ) :=
  ⟨counterexample_isIntegral, counterexample_not_injective,
    counterexample_part_i_fails, counterexample_part_ii_fails⟩

end Counterexample

end AtiyahMcdonald69.Ex_5_5

#print axioms AtiyahMcdonald69.Ex_5_5.isUnit_of_isUnit_algebraMap
#print axioms AtiyahMcdonald69.Ex_5_5.jacobson_eq_comap
#print axioms AtiyahMcdonald69.Ex_5_5.jacobson_bot_eq_comap
#print axioms AtiyahMcdonald69.Ex_5_5.solution
#print axioms AtiyahMcdonald69.Ex_5_5.injectivity_is_needed
#print axioms AtiyahMcdonald69.Ex_5_5.solution_of_ringHom
#print axioms AtiyahMcdonald69.Ex_5_5.solution_subring
#print axioms AtiyahMcdonald69.Ex_5_5.jacobson_eq_inter
