/-
# Hartshorne, *Algebraic Geometry* (1977), Chapter I, §3, Exercise I.3.2

## The statement of the book

> A morphism whose underlying map on the topological spaces is a homeomorphism need not be an
> isomorphism.
>
> (a) For example, let `φ : A¹ → A²` be defined by `t ↦ (t², t³)`. Show that `φ` defines a
> bijective bicontinuous morphism of `A¹` onto the curve `y² = x³`, but that `φ` is not an
> isomorphism.
>
> (b) For another example, let the characteristic of the base field `k` be `p > 0`, and define a
> map `φ : A¹ → A¹` by `t ↦ t^p`. Show that `φ` is bijective and bicontinuous but not an
> isomorphism. This is called the Frobenius morphism.

## Source traceability

* `.scratch/DoYourExercise/content/Hartshorne77/Hartshorne77-I-3-2/proof.tex` (terse guidance):
  both examples, with the inverse `y/x` away from the origin and the failure of the pullbacks
  `k[t²,t³] ↪ k[t]` and `k[t] → k[t]`, `t ↦ t^p` to be surjective.  This is guidance, not a
  definition of the statement.
* `.scratch/reference/hartshorne-1977.txt` is defective in the I.3 exercise list (exercise 3.2
  is cut down to "... Show that φ is bijective and bicontinuous but not an isomorphism. This is
  called the Frobenius morphism."), so the statement was cross-checked independently against
  * the book rendering `https://djvu.online/file/n2NhnYTcAGqAM`; the page itself is behind a
    bot check, so its OCR text was read from the web-search index of that page, whose Chapter I
    §3 exercise list reads exactly as quoted above: "(a) ... let
    φ: A¹ → A² be defined by t ↦ (t², t³). Show that φ defines a bijective bicontinuous morphism
    of A¹ onto the curve y² = x³, but that φ is not an isomorphism. (b) For another example, let
    the characteristic of the base field k be p > 0, and define a map φ: A¹ → A¹ by t ↦ t^p.
    Show that φ is bijective and bicontinuous but not an isomorphism. This is called the
    Frobenius morphism.");
  * `https://www.dzackgarza.com/rawnotes/orals/HartshorneMegadoc.tex`, §I.3.2, which gives the
    same statement together with the section's lead-in "A morphism whose underlying map on the
    topological spaces is a homeomorphism need not be an isomorphism";
  * `https://math.stackexchange.com/questions/4497531`, which quotes exercise I.3.2 verbatim.
  The page `https://hartshorne-ag-solutions.wikidot.com/chapter-1-section-3` returns HTTP 404
  (only the §1 solutions of that wiki are typed); the same site's Chapter 1 page confirms that
  §3 is not among the typed sections.

No later exercise and no unproved auxiliary result is used as a hypothesis: every ingredient
below is proved in this file.  The two negative statements are proved directly from the
definition of a morphism of varieties (via the local behaviour of the inverse at the origin);
the general theorem identifying global regular functions on an affine variety with its
coordinate ring is neither needed nor assumed.  In particular, the classical facts used about the affine line
(Zariski closed sets are finite or the whole line), about polynomial maps (continuity), and about
points being closed are proved from scratch starting from the definition of the Zariski topology
as zero loci of polynomial ideals.

## Formal setting (Hartshorne Chapter I, classical point-set varieties)

`A^n` is `Fin n → k` (points only, no scheme structure).  Zariski closed subsets are the zero
loci `MvPolynomial.zeroLocus k I` of ideals of polynomials, and the topology is the one whose
closed sets are exactly these (`IsZariskiClosed`, `zariskiTopology`).

For a subset `X ⊆ A^n` with the induced topology:

* `IsRegularAt X f x` (for `f : U → k` on an open `U ⊆ X`): there is an open neighbourhood
  `W ⊆ U` of `x` in `X` and polynomials `p q ∈ k[x₁,…,xₙ]` with `q` nowhere zero on `W` and
  `f = p/q` on `W`.  `IsRegular X U f` means regular at every point of `U`.  This is
  Hartshorne's definition of a regular function (local quotient of polynomials with nonvanishing
  denominator).
* `IsMorphism X Y φ`: `φ : X → Y` is continuous and for every open `U ⊆ Y` and every regular
  `f : U → k`, the pullback `f ∘ φ` is regular on `φ⁻¹(U)` (Hartshorne's definition of a
  morphism of varieties).
* `IsIso X Y φ`: there is a morphism `ψ : Y → X` with `ψ ∘ φ = id` and `φ ∘ ψ = id`.

## What is proved, clause by clause

Part (a) (`Y = cusp k = V(y² - x³) ⊂ A²`, `φ = cuspPhi k`, `t ↦ (t²,t³)`):

| book clause | Lean declaration |
|---|---|
| `Y = V(y²-x³)` | `cusp`, `isClosed_cusp`, `mem_cusp` |
| `φ` is a morphism of varieties | `isMorphism_cuspPhi` (continuity `continuous_cuspPhi` plus pullback of regular functions) |
| `φ` is bijective onto `Y` | `cuspPhi_bijective` (`cuspPhi_injective`, `cuspPhi_surjective`) |
| `φ` is bicontinuous (homeomorphism) | `cuspPhi_bicontinuous` (inverse `cuspInv`, laws `cuspInv_left`, `cuspInv_right`, continuity `continuous_cuspInv`) |
| `φ` is not an isomorphism | `cuspPhi_not_isIso`; explicitly the inverse is not a morphism, `cuspInv_not_isMorphism` |
| (the failure is at the origin) | `isRegular_cuspInv_away`: on `Y ∩ {x ≠ 0}` the inverse is the regular function `y/x` |

Part (b) (`φ = frobPhi k p`, `t ↦ t^p`, `char k = p > 0`):

| book clause | Lean declaration |
|---|---|
| `φ` is a morphism of varieties | `isMorphism_frobPhi` (continuity `continuous_frobPhi` plus pullback of regular functions) |
| `φ` is bijective | `frobPhi_bijective` (`frobPhi_injective` uses `(a-b)^p = a^p - b^p` in char `p`; `frobPhi_surjective` uses that `k` is algebraically closed, i.e. perfect) |
| `φ` is bicontinuous | `frobPhi_bicontinuous` (every bijection of `A¹` is a homeomorphism, since closed sets are finite or the whole line) |
| `φ` is not an isomorphism | `frobPhi_not_isIso` |
| `φ` is the Frobenius morphism | `frobPhi` is literally `t ↦ t^p` |

## Proof mechanism for the two negative statements

Both use the same "order at the origin" argument, with all denominators checked:

Part (a).  Suppose `ψ` were an inverse morphism.  The coordinate function `t` on `A¹` pulled
back along `ψ` is regular on `Y`; at the origin `O = (0,0)` it is locally `p/q` with
`q(O) ≠ 0`.  On the open set where this representation holds, `ψ(γ(t)) = γ(t)` for
`γ(t) = (t²,t³)`, so

  `p(t²,t³) = t · q(t²,t³)`      for all `t` in an infinite set.

Hence `cuspSubstPoly p = X · cuspSubstPoly q` in `k[t]`.  Every monomial of `cuspSubstPoly p`
has degree `2i + 3j ∉ {1}`, so the coefficient of `t` on the left is `0`
(`coeff_one_cuspSubstPoly`, proved by exhibiting `p(t²,t³)` inside the subalgebra of polynomials
with vanishing `X`-coefficient).  On the right the coefficient of `t` is `q(0,0) ≠ 0`;
contradiction.

Part (b).  Same with `p(t^p) = t · q(t^p)`; monomials of `p(t^p)` have degrees divisible by
`p > 1` (`coeff_one_frobSubstPoly`), while `t · q(t^p)` has `t`-coefficient `q(0) ≠ 0`.

## Note on the "not an isomorphism" mechanism

For (a) the inverse map is `y/x` away from the origin: it is a regular function there
(`isRegular_cuspInv_away`), and only fails at the singular point.  For (b) the failure is
everywhere: the inverse of Frobenius is not a rational function at all, so the Frobenius is not
even a local isomorphism at any point, while it is a homeomorphism.
-/

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_3_2

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

/-! ## The affine line `A¹` -/

variable (k : Type*) [Field k]

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


/-! ## Points and finite sets are Zariski closed -/

section Points

variable {k : Type*} [Field k]

theorem isZariskiClosed_singleton {n : ℕ} (x : AffineSpace k n) :
    IsZariskiClosed (k := k) n ({x} : Set (AffineSpace k n)) := by
  refine ⟨Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X i - MvPolynomial.C (x i))), ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro rfl p ⟨i, rfl⟩
    simp
  · intro h
    funext i
    have h' := h (MvPolynomial.X i - MvPolynomial.C (x i)) ⟨i, rfl⟩
    exact sub_eq_zero.mp (by simpa using h')

theorem isClosed_singleton {n : ℕ} (x : AffineSpace k n) :
    IsClosed ({x} : Set (AffineSpace k n)) :=
  isClosed_iff.2 (isZariskiClosed_singleton x)

instance t1Space_affineSpace (n : ℕ) : T1Space (AffineSpace k n) where
  t1 x := isClosed_singleton x

theorem isClosed_finite {n : ℕ} {S : Set (AffineSpace k n)} (hS : S.Finite) : IsClosed S :=
  hS.isClosed

/-- Closed subsets of the affine line, transported to the subtype `↥univ`. -/
theorem isClosed_subtype_univ_iff {α : Type*} [TopologicalSpace α]
    {S : Set ↥(Set.univ : Set α)} :
    IsClosed S ↔ IsClosed (Subtype.val '' S) := by
  have h := Homeomorph.isClosed_image (Homeomorph.Set.univ α) (s := S)
  simpa using h.symm

/-- On `A¹` viewed as the subtype `↥univ`, closed sets are exactly finite sets and the whole
line (the classical statement that the Zariski topology on the affine line is the cofinite
topology). -/
theorem isClosed_univ_line_iff_finite_or_univ
    {S : Set ↥(Set.univ : Set (AffineSpace k 1))} :
    IsClosed S ↔ S.Finite ∨ S = Set.univ := by
  have himg : (Subtype.val '' S : Set (AffineSpace k 1)) = Set.univ ↔ S = Set.univ := by
    constructor
    · intro h
      ext x
      constructor
      · intro _; exact Set.mem_univ _
      · intro _
        have hx : (x : AffineSpace k 1) ∈ Subtype.val '' S := by rw [h]; exact Set.mem_univ _
        obtain ⟨y, hy, hyx⟩ := hx
        have hyx' : y = x := Subtype.ext hyx
        rwa [hyx'] at hy
    · intro h; rw [h]; simp
  have hfin : (Subtype.val '' S : Set (AffineSpace k 1)).Finite ↔ S.Finite :=
    ⟨fun h => h.of_finite_image Subtype.val_injective.injOn, fun h => h.image _⟩
  rw [isClosed_subtype_univ_iff, isClosed_iff_finite_or_univ, himg, hfin]
  tauto

end Points

/-! ## Regular functions and morphisms of affine varieties -/

section RegularFunctions

variable {k : Type*} [Field k]

/-- A function `f` on an open subset `U` of a locally closed set `X ⊆ A^n` is regular at a
point `x ∈ U` if on some open neighbourhood `W ⊆ U` of `x` in `X` it agrees with a quotient
`p/q` of polynomial functions, the denominator `q` being nowhere zero on `W`. -/
def IsRegularAt {n : ℕ} (X : Set (AffineSpace k n)) {U : Set ↥X} (f : ↥U → k)
    (x : ↥U) : Prop :=
  ∃ W : Set ↥X, IsOpen W ∧ x.1 ∈ W ∧
    ∃ hWU : W ⊆ U, ∃ p q : MvPolynomial (Fin n) k, ∀ (y : ↥X) (hy : y ∈ W),
      q.eval y.1 ≠ 0 ∧ f ⟨y, hWU hy⟩ = p.eval y.1 / q.eval y.1

/-- A regular function on an open subset `U` of `X`: regular at every point of `U`. -/
def IsRegular {n : ℕ} (X : Set (AffineSpace k n)) (U : Set ↥X) (f : ↥U → k) : Prop :=
  ∀ x : ↥U, IsRegularAt X f x

/-- A morphism of affine varieties: a continuous map whose pullback sends every regular
function on an open subset of the target to a regular function on the inverse image. -/
def IsMorphism {n m : ℕ} (X : Set (AffineSpace k n)) (Y : Set (AffineSpace k m))
    (φ : ↥X → ↥Y) : Prop :=
  Continuous φ ∧ ∀ (U : Set ↥Y), IsOpen U → ∀ f : ↥U → k, IsRegular Y U f →
    IsRegular X (φ ⁻¹' U) (fun x => f ⟨φ x.1, x.2⟩)

/-- An isomorphism of affine varieties is a morphism admitting a two-sided inverse morphism. -/
def IsIso {n m : ℕ} (X : Set (AffineSpace k n)) (Y : Set (AffineSpace k m))
    (φ : ↥X → ↥Y) : Prop :=
  ∃ ψ : ↥Y → ↥X, IsMorphism X Y φ ∧ IsMorphism Y X ψ ∧
    (∀ x, ψ (φ x) = x) ∧ ∀ y, φ (ψ y) = y

/-- The `i`-th coordinate function on affine `n`-space is regular. -/
theorem isRegular_coord (n : ℕ) (i : Fin n) :
    IsRegular (Set.univ : Set (AffineSpace k n)) Set.univ
      (fun u : ↥(Set.univ : Set ↥(Set.univ : Set (AffineSpace k n))) => u.1.1 i) := by
  intro u
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_, MvPolynomial.X i, 1, ?_⟩
  · intro y hy; exact Set.mem_univ y
  · intro y hy
    exact ⟨by simp, by simp⟩

end RegularFunctions

/-! ## Part (a): the cuspidal cubic `y² = x³` -/

section Cusp

variable (k : Type*) [Field k]

/-- The cuspidal cubic `Y = V(y² - x³) ⊆ A²`. -/
def cusp : Set (AffineSpace k 2) :=
  MvPolynomial.zeroLocus k
    (Ideal.span ({MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ 3} :
      Set (MvPolynomial (Fin 2) k)))

theorem isClosed_cusp : IsClosed (cusp k) :=
  isClosed_zeroLocus _

theorem mem_cusp {P : AffineSpace k 2} : P ∈ cusp k ↔ P 1 ^ 2 = P 0 ^ 3 := by
  rw [cusp, MvPolynomial.zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' := h (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) rfl
    simp only [map_sub, map_pow, MvPolynomial.aeval_X] at h'
    exact sub_eq_zero.mp h'
  · intro h p hp
    rw [hp]
    simp only [map_sub, map_pow, MvPolynomial.aeval_X]
    exact sub_eq_zero.mpr h

/-- The parametrization `t ↦ (t², t³)` of the cusp. -/
def cuspParam (t : k) : AffineSpace k 2 := ![t ^ 2, t ^ 3]

theorem cuspParam_zero (t : k) : cuspParam k t 0 = t ^ 2 := rfl

theorem cuspParam_one (t : k) : cuspParam k t 1 = t ^ 3 := rfl

theorem cuspParam_mem (t : k) : cuspParam k t ∈ cusp k := by
  rw [mem_cusp, cuspParam_one, cuspParam_zero]; ring

theorem cuspParam_injective : Function.Injective (cuspParam k) := by
  intro t s h
  have h1 : t ^ 2 = s ^ 2 := congrFun h 0
  have h2 : t ^ 3 = s ^ 3 := congrFun h 1
  by_cases ht : t = 0
  · subst ht
    have hs : s ^ 3 = 0 := by simpa using h2.symm
    have : s = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hs
    exact this.symm
  · have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hs2 : s ^ 2 ≠ 0 := by rw [← h1]; exact ht2
    have key : t = t ^ 3 / t ^ 2 := by field_simp
    have key2 : s = s ^ 3 / s ^ 2 := by field_simp
    rw [key, key2, h1, h2]

theorem cuspParam_surjective :
    Function.Surjective (fun t => (⟨cuspParam k t, cuspParam_mem k t⟩ : ↥(cusp k))) := by
  intro y
  have hy : y.1 1 ^ 2 = y.1 0 ^ 3 := (mem_cusp (k := k)).1 y.2
  by_cases h0 : y.1 0 = 0
  · have h1 : y.1 1 = 0 := by
      have : y.1 1 ^ 2 = 0 := by rw [hy, h0]; simp
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp this
    refine ⟨0, ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    · change cuspParam k 0 0 = y.1 0
      rw [cuspParam_zero]; simp [h0]
    · change cuspParam k 0 1 = y.1 1
      rw [cuspParam_one]; simp [h1]
  · refine ⟨y.1 1 / y.1 0, ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    · change cuspParam k (y.1 1 / y.1 0) 0 = y.1 0
      rw [cuspParam_zero, div_pow, div_eq_iff (pow_ne_zero 2 h0)]
      rw [hy]; ring
    · change cuspParam k (y.1 1 / y.1 0) 1 = y.1 1
      rw [cuspParam_one, div_pow, div_eq_iff (pow_ne_zero 3 h0)]
      rw [← hy]; ring

/-- The morphism `φ : A¹ → Y`, `t ↦ (t², t³)`. -/
def cuspPhi : ↥(Set.univ : Set (AffineSpace k 1)) → ↥(cusp k) :=
  fun x => ⟨cuspParam k (x.1 0), cuspParam_mem k (x.1 0)⟩

theorem cuspPhi_injective : Function.Injective (cuspPhi k) := by
  intro x y h
  have h' : cuspParam k (x.1 0) = cuspParam k (y.1 0) := congrArg Subtype.val h
  have h0 : x.1 0 = y.1 0 := cuspParam_injective k h'
  apply Subtype.ext
  funext i
  fin_cases i
  exact h0

theorem cuspPhi_surjective : Function.Surjective (cuspPhi k) := by
  intro y
  obtain ⟨t, ht⟩ := cuspParam_surjective k y
  exact ⟨⟨fun _ => t, Set.mem_univ _⟩, ht⟩

theorem cuspPhi_bijective : Function.Bijective (cuspPhi k) :=
  ⟨cuspPhi_injective k, cuspPhi_surjective k⟩

/-- The substitution `k[x,y] → k[x]`, `x ↦ x²`, `y ↦ x³`. -/
def cuspSubst : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 1) k :=
  MvPolynomial.aeval
    (![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 ^ 3] : Fin 2 → MvPolynomial (Fin 1) k)

@[simp] theorem cuspSubst_X0 : cuspSubst k (MvPolynomial.X 0) = MvPolynomial.X 0 ^ 2 := by
  simp [cuspSubst]

@[simp] theorem cuspSubst_X1 : cuspSubst k (MvPolynomial.X 1) = MvPolynomial.X 0 ^ 3 := by
  simp [cuspSubst]

/-- The substitution `k[x,y] → k[t]`, `x ↦ t²`, `y ↦ t³`. -/
def cuspSubstPoly : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval
    (![Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 2 → Polynomial k)

@[simp] theorem polyEquiv_X0 : polyEquiv k (MvPolynomial.X 0) = Polynomial.X := by
  simp [polyEquiv, substOne]

theorem cuspSubstPoly_eq (p : MvPolynomial (Fin 2) k) :
    cuspSubstPoly k p = polyEquiv k (cuspSubst k p) := by
  have h : cuspSubstPoly k = (polyEquiv k).toAlgHom.comp (cuspSubst k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cuspSubstPoly, cuspSubst]
  rw [h]
  rfl

/-- Evaluating the substitution `cuspSubstPoly p` at `t` is evaluating `p` at `(t², t³)`. -/
theorem aeval_cuspParam (t : k) (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.aeval (R := k) (cuspParam k t) p = (cuspSubstPoly k p).eval t := by
  have h : (MvPolynomial.aeval (R := k) (cuspParam k t)) =
      (Polynomial.aeval t).comp (cuspSubstPoly k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cuspParam, cuspSubstPoly]
  rw [h]
  rfl

/-- Pointwise form of `aeval_cuspParam`. -/
theorem eval_cuspSubstPoly (t : k) (p : MvPolynomial (Fin 2) k) :
    p.eval (cuspParam k t) = (cuspSubstPoly k p).eval t := by
  have h := aeval_cuspParam k t p
  rwa [MvPolynomial.aeval_eq_eval] at h

/-- Evaluating `cuspSubst p` at a point `x` of `A¹` is evaluating `p` at `(x₀², x₀³)`. -/
theorem eval_cuspSubst (x : AffineSpace k 1) (p : MvPolynomial (Fin 2) k) :
    (cuspSubst k p).eval x = p.eval (cuspParam k (x 0)) := by
  have h1 : (cuspSubst k p).eval x = (polyEquiv k (cuspSubst k p)).eval (x 0) :=
    aeval_polyEquiv k x (cuspSubst k p)
  rw [h1, ← cuspSubstPoly_eq, ← aeval_cuspParam]
  rfl

/-- The parametrization `A¹ → A²`, `t ↦ (t², t³)`, as a polynomial map. -/
def cuspParamMap : AffineSpace k 1 → AffineSpace k 2 := fun x => cuspParam k (x 0)

theorem cuspParamMap_eq_pointMap : cuspParamMap k = pointMap k (cuspSubst k) := by
  funext x j
  fin_cases j <;> simp [cuspParamMap, cuspParam, pointMap, cuspSubst]

theorem continuous_cuspParamMap : Continuous (cuspParamMap k) := by
  rw [cuspParamMap_eq_pointMap]
  exact continuous_pointMap k (cuspSubst k)

/-- The parametrization as a map into the cusp. -/
def cuspParamToCusp : AffineSpace k 1 → ↥(cusp k) :=
  fun x => ⟨cuspParamMap k x, by rw [cuspParamMap]; exact cuspParam_mem k (x 0)⟩

theorem continuous_cuspParamToCusp : Continuous (cuspParamToCusp k) :=
  Continuous.subtype_mk (continuous_cuspParamMap k) _

theorem continuous_cuspPhi : Continuous (cuspPhi k) :=
  (continuous_cuspParamToCusp k).comp continuous_subtype_val

/-- `φ : A¹ → Y` is a morphism of varieties. -/
theorem isMorphism_cuspPhi :
    IsMorphism (Set.univ : Set (AffineSpace k 1)) (cusp k) (cuspPhi k) := by
  refine ⟨continuous_cuspPhi k, ?_⟩
  intro U hU f hf x
  obtain ⟨W, hW, hxW, hWU, p, q, hpq⟩ := hf ⟨cuspPhi k x.1, x.2⟩
  refine ⟨cuspPhi k ⁻¹' W, hW.preimage (continuous_cuspPhi k), hxW, ?_,
    cuspSubst k p, cuspSubst k q, ?_⟩
  · intro y hy
    exact hWU hy
  · intro y hy
    obtain ⟨hq, hval⟩ := hpq (cuspPhi k y) hy
    constructor
    · rw [eval_cuspSubst]; exact hq
    · rw [eval_cuspSubst, eval_cuspSubst]
      exact hval

end Cusp

section CuspNotIso

variable (k : Type*) [Field k]

/-- Every monomial `t^{2i+3j}` has degree different from `1`, so the coefficient of `X` in
`p(t², t³)` vanishes. -/
theorem coeff_one_cuspSubstPoly (p : MvPolynomial (Fin 2) k) :
    (cuspSubstPoly k p).coeff 1 = 0 := by
  let S : Subalgebra k (Polynomial k) :=
    { carrier := {f | f.coeff 1 = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        show (a + b).coeff 1 = 0
        rw [Polynomial.coeff_add, show a.coeff 1 = 0 from ha, show b.coeff 1 = 0 from hb,
          add_zero]
      mul_mem' := by
        intro a b ha hb
        show (a * b).coeff 1 = 0
        rw [Polynomial.mul_coeff_one, show a.coeff 1 = 0 from ha, show b.coeff 1 = 0 from hb]
        ring
      algebraMap_mem' := by
        intro r
        show (algebraMap k (Polynomial k) r).coeff 1 = 0
        simp }
  have hrange : (Set.range (![Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 2 → Polynomial k)) =
      ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hf
      rcases hf with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hmem : cuspSubstPoly k p ∈
      Algebra.adjoin k ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k)) := by
    have h1 : cuspSubstPoly k p ∈
        (MvPolynomial.aeval (R := k)
          (![Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 2 → Polynomial k)).range :=
      ⟨p, rfl⟩
    have h2 : Algebra.adjoin k
          (Set.range (![Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 2 → Polynomial k)) =
        (MvPolynomial.aeval (R := k)
          (![Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 2 → Polynomial k)).range :=
      Algebra.adjoin_range_eq_range_aeval ..
    rw [← h2, hrange] at h1
    exact h1
  have hle : Algebra.adjoin k ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k)) ≤ S := by
    refine Algebra.adjoin_le_iff.2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show (Polynomial.X ^ 2).coeff 1 = 0; simp
    · show (Polynomial.X ^ 3).coeff 1 = 0; simp
  exact hle hmem

end CuspNotIso

section CuspNotIsoProof

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- `φ : A¹ → Y`, `t ↦ (t², t³)`, is not an isomorphism of varieties. -/
theorem cuspPhi_not_isIso :
    ¬ IsIso (Set.univ : Set (AffineSpace k 1)) (cusp k) (cuspPhi k) := by
  rintro ⟨ψ, _hφm, hψm, hleft, _hright⟩
  have hreg : IsRegular (cusp k) Set.univ
      (fun y : ↥(Set.univ : Set ↥(cusp k)) => (ψ y.1).1 0) := by
    have h := hψm.2 Set.univ isOpen_univ
      (fun u : ↥(Set.univ : Set ↥(Set.univ : Set (AffineSpace k 1))) => u.1.1 0)
      (isRegular_coord (k := k) 1 0)
    simpa using h
  let O : ↥(cusp k) := ⟨cuspParam k 0, cuspParam_mem k 0⟩
  obtain ⟨W, hW, hOW, hWU, p, q, hpq⟩ := hreg ⟨O, Set.mem_univ _⟩
  let γ : AffineSpace k 1 → ↥(cusp k) := fun x => ⟨cuspParam k (x 0), cuspParam_mem k (x 0)⟩
  have hγ : Continuous γ := continuous_cuspParamToCusp k
  let T : Set (AffineSpace k 1) := γ ⁻¹' W
  have hTopen : IsOpen T := hW.preimage hγ
  have hT0 : (0 : AffineSpace k 1) ∈ T := by
    show γ 0 ∈ W
    have hγ0 : γ 0 = O := rfl
    rw [hγ0]; exact hOW
  have hTcofinite : Tᶜ.Finite := by
    have hclosed : IsClosed Tᶜ := hTopen.isClosed_compl
    rcases (isClosed_iff_finite_or_univ (k := k)).1 hclosed with h | h
    · exfalso
      have hmem : (0 : AffineSpace k 1) ∈ Tᶜ := by rw [h]; exact Set.mem_univ _
      exact hmem hT0
    · exact h
  have hTinf : T.Infinite := by simpa using hTcofinite.infinite_compl
  have hident : ∀ x ∈ T, p.eval (cuspParam k (x 0)) = x 0 * q.eval (cuspParam k (x 0)) := by
    intro x hx
    have hxW : γ x ∈ W := hx
    obtain ⟨hq, hval⟩ := hpq (γ x) hxW
    have hleftx := hleft ⟨fun _ => x 0, Set.mem_univ _⟩
    have h1 : (ψ (γ x)).1 0 = x 0 := by
      have := congrArg (fun u : ↥(Set.univ : Set (AffineSpace k 1)) => u.1 0) hleftx
      simpa [γ, cuspPhi] using this
    have h2 : (ψ (γ x)).1 0 = p.eval (cuspParam k (x 0)) / q.eval (cuspParam k (x 0)) := by
      simpa [γ] using hval
    have h3 : x 0 = p.eval (cuspParam k (x 0)) / q.eval (cuspParam k (x 0)) := h1.symm.trans h2
    rw [eq_div_iff hq] at h3
    exact h3.symm
  have hpoly : cuspSubstPoly k p - Polynomial.X * cuspSubstPoly k q = 0 := by
    by_contra hne
    have hfin : {t : k | (cuspSubstPoly k p - Polynomial.X * cuspSubstPoly k q).IsRoot t}.Finite :=
      Polynomial.finite_setOfPred_isRoot hne
    have hinj : Set.InjOn (fun x : AffineSpace k 1 => x 0) T := by
      intro x _ y _ hxy
      funext i
      fin_cases i
      exact hxy
    have hmaps : Set.MapsTo (fun x : AffineSpace k 1 => x 0) T
        {t : k | (cuspSubstPoly k p - Polynomial.X * cuspSubstPoly k q).IsRoot t} := by
      intro x hx
      have hx' := hident x hx
      show (cuspSubstPoly k p - Polynomial.X * cuspSubstPoly k q).eval (x 0) = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        ← eval_cuspSubstPoly, ← eval_cuspSubstPoly, hx']
      ring
    exact (Set.infinite_of_injOn_mapsTo hinj hmaps hTinf).not_finite hfin
  have h1 : (cuspSubstPoly k p).coeff 1 = 0 := coeff_one_cuspSubstPoly k p
  have h2 : (Polynomial.X * cuspSubstPoly k q).coeff 1 = (cuspSubstPoly k q).coeff 0 := by
    simpa using Polynomial.coeff_X_mul (cuspSubstPoly k q) 0
  have h3 : (cuspSubstPoly k q).coeff 0 = q.eval (0 : Fin 2 → k) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← eval_cuspSubstPoly]
    have h0 : cuspParam k 0 = (0 : Fin 2 → k) := by
      funext i; fin_cases i <;> simp [cuspParam]
    rw [h0]
  have hq0 : q.eval (0 : Fin 2 → k) = 0 := by
    have hc := congrArg (fun r : Polynomial k => r.coeff 1) hpoly
    simp only [Polynomial.coeff_sub, Polynomial.coeff_zero] at hc
    rw [h1, h2, h3] at hc
    simpa using hc
  have hqO : q.eval (0 : Fin 2 → k) ≠ 0 := by
    have h := (hpq O hOW).1
    have hO : O.1 = (0 : Fin 2 → k) := by
      funext i
      fin_cases i <;> simp [O, cuspParam]
    rwa [hO] at h
  exact hqO hq0

end CuspNotIsoProof

section CuspBicont

variable (k : Type*) [Field k]

/-- The set-theoretic inverse of `φ : A¹ → Y`: it sends `(x,y) ≠ (0,0)` to `y/x` and the
origin to `0`. -/
def cuspInv : ↥(cusp k) → ↥(Set.univ : Set (AffineSpace k 1)) := by
  classical
  exact fun y => ⟨fun _ => if y.1 0 = 0 then 0 else y.1 1 / y.1 0, Set.mem_univ _⟩

theorem cuspInv_apply (y : ↥(cusp k)) :
    (cuspInv k y).1 0 = if y.1 0 = 0 then 0 else y.1 1 / y.1 0 := rfl

theorem cuspInv_cuspPhi_val (x : ↥(Set.univ : Set (AffineSpace k 1))) :
    (cuspInv k (cuspPhi k x)).1 0 = if x.1 0 = 0 then 0 else x.1 0 := by
  classical
  classical
  rw [cuspInv_apply]
  have h0 : (cuspPhi k x).1 0 = (x.1 0) ^ 2 := rfl
  have h1 : (cuspPhi k x).1 1 = (x.1 0) ^ 3 := rfl
  rw [h0, h1]
  by_cases h : x.1 0 = 0
  · simp [h]
  · rw [if_neg (pow_ne_zero 2 h), if_neg h, div_eq_iff (pow_ne_zero 2 h)]
    ring

theorem cuspInv_left : Function.LeftInverse (cuspInv k) (cuspPhi k) := by
  classical
  intro x
  apply Subtype.ext
  funext i
  fin_cases i
  change (cuspInv k (cuspPhi k x)).1 0 = x.1 0
  rw [cuspInv_cuspPhi_val]
  by_cases h : x.1 0 = 0 <;> simp [h]

theorem cuspPhi_cuspInv_val0 (y : ↥(cusp k)) :
    (cuspPhi k (cuspInv k y)).1 0 = y.1 0 := by
  classical
  have hy : y.1 1 ^ 2 = y.1 0 ^ 3 := (mem_cusp (k := k)).1 y.2
  show (cuspInv k y).1 0 ^ 2 = y.1 0
  rw [cuspInv_apply]
  by_cases h0 : y.1 0 = 0
  · simp [h0]
  · rw [if_neg h0, div_pow, div_eq_iff (pow_ne_zero 2 h0)]
    rw [hy]; ring

theorem cuspPhi_cuspInv_val1 (y : ↥(cusp k)) :
    (cuspPhi k (cuspInv k y)).1 1 = y.1 1 := by
  classical
  have hy : y.1 1 ^ 2 = y.1 0 ^ 3 := (mem_cusp (k := k)).1 y.2
  show (cuspInv k y).1 0 ^ 3 = y.1 1
  rw [cuspInv_apply]
  by_cases h0 : y.1 0 = 0
  · have h1 : y.1 1 = 0 := by
      have h2 : y.1 1 ^ 2 = 0 := by rw [hy, h0]; simp
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    rw [if_pos h0]
    simp [h1]
  · rw [if_neg h0, div_pow, div_eq_iff (pow_ne_zero 3 h0)]
    rw [← hy]; ring

theorem cuspInv_right : Function.RightInverse (cuspInv k) (cuspPhi k) := by
  classical
  intro y
  apply Subtype.ext
  funext i
  fin_cases i
  · change (cuspPhi k (cuspInv k y)).1 0 = y.1 0
    rw [cuspPhi_cuspInv_val0]
  · change (cuspPhi k (cuspInv k y)).1 1 = y.1 1
    rw [cuspPhi_cuspInv_val1]

theorem cuspInv_injective : Function.Injective (cuspInv k) :=
  Function.RightInverse.injective (cuspInv_right k)

/-- The inverse map `Y → A¹` is continuous for the Zariski topology. -/
theorem continuous_cuspInv : Continuous (cuspInv k) := by
  rw [continuous_iff_isClosed]
  intro S hS
  rcases (isClosed_univ_line_iff_finite_or_univ (k := k)).1 hS with hfin | huniv
  · have hsub : cuspInv k ⁻¹' S ⊆ cuspPhi k '' S := by
      intro y hy
      exact ⟨cuspInv k y, hy, cuspInv_right k y⟩
    exact (hfin.image (cuspPhi k)).subset hsub |>.isClosed
  · rw [huniv]
    simp

/-- `φ : A¹ → Y` is bijective and bicontinuous (a homeomorphism). -/
theorem cuspPhi_bicontinuous :
    ∃ ψ : ↥(cusp k) → ↥(Set.univ : Set (AffineSpace k 1)),
      (∀ x, ψ (cuspPhi k x) = x) ∧ (∀ y, cuspPhi k (ψ y) = y) ∧ Continuous ψ :=
  ⟨cuspInv k, cuspInv_left k, cuspInv_right k, continuous_cuspInv k⟩


/-- The two halves of the source statement "not an isomorphism": the set-theoretic inverse
of `φ` is not a morphism. -/
theorem cuspInv_not_isMorphism [IsAlgClosed k] :
    ¬ IsMorphism (cusp k) (Set.univ : Set (AffineSpace k 1)) (cuspInv k) := by
  intro h
  exact cuspPhi_not_isIso k
    ⟨cuspInv k, isMorphism_cuspPhi k, h, cuspInv_left k, cuspInv_right k⟩

/-- The open subset `{x ≠ 0} ⊆ Y`. -/
theorem isOpen_cusp_ne_zero : IsOpen {y : ↥(cusp k) | y.1 0 ≠ 0} := by
  have h : IsOpen {P : AffineSpace k 2 | P 0 ≠ 0} := by
    rw [isOpen_iff]
    refine ⟨Ideal.span ({MvPolynomial.X (0 : Fin 2)} : Set (MvPolynomial (Fin 2) k)), ?_⟩
    rw [MvPolynomial.zeroLocus_span]
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_compl_iff, not_not]
    constructor
    · intro h; simpa using h
    · intro h; simpa using h
  exact h.preimage continuous_subtype_val

/-- Away from the origin, `φ` has a regular inverse: on `Y ∩ {x ≠ 0}` the inverse is the
rational function `y/x`.  (At the origin it is not regular, as `cuspPhi_not_isIso` shows.) -/
theorem isRegular_cuspInv_away :
    IsRegular (cusp k) {y : ↥(cusp k) | y.1 0 ≠ 0} (fun y => (cuspInv k y).1 0) := by
  intro y
  refine ⟨{y' : ↥(cusp k) | y'.1 0 ≠ 0}, isOpen_cusp_ne_zero k, y.2, ?_,
    MvPolynomial.X 1, MvPolynomial.X 0, ?_⟩
  · intro y' hy'; exact hy'
  · intro y' hy'
    constructor
    · simpa using hy'
    · change (cuspInv k y').1 0 =
        (MvPolynomial.eval y'.1) (MvPolynomial.X 1) / (MvPolynomial.eval y'.1) (MvPolynomial.X 0)
      rw [cuspInv_apply, if_neg hy']
      simp

end CuspBicont

/-! ## Part (b): the Frobenius morphism `t ↦ t^p` -/

section Frobenius

variable (k : Type*) [Field k]

/-- The substitution `k[x] → k[x]`, `x ↦ x^p`. -/
def frobSubst (p : ℕ) : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 1) k :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X 0 ^ p)

@[simp] theorem frobSubst_X (p : ℕ) :
    frobSubst k p (MvPolynomial.X 0) = MvPolynomial.X 0 ^ p := by
  simp [frobSubst]

/-- The substitution `k[x] → k[t]`, `x ↦ t^p`. -/
def frobSubstPoly (p : ℕ) : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun _ => Polynomial.X ^ p)

theorem frobSubstPoly_eq (p : ℕ) (r : MvPolynomial (Fin 1) k) :
    frobSubstPoly k p r = polyEquiv k (frobSubst k p r) := by
  have h : frobSubstPoly k p = (polyEquiv k).toAlgHom.comp (frobSubst k p) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp [frobSubstPoly, frobSubst]
  rw [h]
  rfl

/-- Evaluating `frobSubstPoly p r` at `t` gives `r` evaluated at `t^p`. -/
theorem eval_frobSubstPoly (p : ℕ) (t : k) (r : MvPolynomial (Fin 1) k) :
    (frobSubstPoly k p r).eval t = r.eval (fun _ => t ^ p) := by
  have h : (Polynomial.aeval t).comp (frobSubstPoly k p) =
      MvPolynomial.aeval (R := k) (fun _ : Fin 1 => t ^ p) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp [frobSubstPoly]
  exact AlgHom.congr_fun h r

/-- Evaluating `frobSubst p r` at a point `x` of `A¹` gives `r` evaluated at `x₀^p`. -/
theorem eval_frobSubst (p : ℕ) (x : AffineSpace k 1) (r : MvPolynomial (Fin 1) k) :
    (frobSubst k p r).eval x = r.eval (fun _ => (x 0) ^ p) := by
  have h : (MvPolynomial.aeval (R := k) x).comp (frobSubst k p) =
      MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (x 0) ^ p) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp [frobSubst]
  exact AlgHom.congr_fun h r

/-- Every monomial `t^{pi}` has degree `≠ 1` when `p ≠ 1`, so the coefficient of `X` in
`r(t^p)` vanishes. -/
theorem coeff_one_frobSubstPoly (p : ℕ) (hp : p ≠ 1) (r : MvPolynomial (Fin 1) k) :
    (frobSubstPoly k p r).coeff 1 = 0 := by
  let S : Subalgebra k (Polynomial k) :=
    { carrier := {f | f.coeff 1 = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        show (a + b).coeff 1 = 0
        rw [Polynomial.coeff_add, show a.coeff 1 = 0 from ha, show b.coeff 1 = 0 from hb,
          add_zero]
      mul_mem' := by
        intro a b ha hb
        show (a * b).coeff 1 = 0
        rw [Polynomial.mul_coeff_one, show a.coeff 1 = 0 from ha, show b.coeff 1 = 0 from hb]
        ring
      algebraMap_mem' := by
        intro c
        show (algebraMap k (Polynomial k) c).coeff 1 = 0
        simp }
  have hmem : frobSubstPoly k p r ∈
      Algebra.adjoin k ({Polynomial.X ^ p} : Set (Polynomial k)) := by
    have htop : Algebra.adjoin k
        (Set.range (MvPolynomial.X : Fin 1 → MvPolynomial (Fin 1) k)) = ⊤ :=
      MvPolynomial.adjoin_range_X
    have hle : (⊤ : Subalgebra k (MvPolynomial (Fin 1) k)) ≤
        (Algebra.adjoin k ({Polynomial.X ^ p} : Set (Polynomial k))).comap
          (frobSubstPoly k p) := by
      rw [← htop]
      refine Algebra.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      show frobSubstPoly k p (MvPolynomial.X 0) ∈
        Algebra.adjoin k ({Polynomial.X ^ p} : Set (Polynomial k))
      simp [frobSubstPoly]
    have hmem' : r ∈ (Algebra.adjoin k ({Polynomial.X ^ p} : Set (Polynomial k))).comap (frobSubstPoly k p) := hle (by simp)
    exact hmem'
  have hle : Algebra.adjoin k ({Polynomial.X ^ p} : Set (Polynomial k)) ≤ S := by
    refine Algebra.adjoin_le_iff.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show (Polynomial.X ^ p).coeff 1 = 0
    rw [Polynomial.coeff_X_pow]
    simp [show (1 : ℕ) ≠ p by omega]
  exact hle hmem

/-- The Frobenius map `t ↦ t^p` on the affine line. -/
def frobPhi (p : ℕ) :
    ↥(Set.univ : Set (AffineSpace k 1)) → ↥(Set.univ : Set (AffineSpace k 1)) :=
  fun x => ⟨fun _ => (x.1 0) ^ p, Set.mem_univ _⟩

end Frobenius

section FrobeniusPhi

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem frobPhi_injective : Function.Injective (frobPhi k p) := by
  intro x y h
  have h' : (x.1 0) ^ p = (y.1 0) ^ p := congrFun (congrArg Subtype.val h) 0
  have hp0 : p ≠ 0 := by have h := (Fact.out : p.Prime).pos; omega
  have hsub : (x.1 0 - y.1 0) ^ p = 0 := by
    rw [sub_pow_char, h', sub_self]
  have hzero : x.1 0 - y.1 0 = 0 := (pow_eq_zero_iff hp0).mp hsub
  have hxy : x.1 0 = y.1 0 := sub_eq_zero.mp hzero
  apply Subtype.ext
  funext i
  fin_cases i
  exact hxy

theorem frobPhi_surjective [IsAlgClosed k] : Function.Surjective (frobPhi k p) := by
  intro y
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) (y.1 0) (Nat.Prime.pos (Fact.out : p.Prime))
  refine ⟨⟨fun _ => t, Set.mem_univ _⟩, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  exact ht

theorem frobPhi_bijective [IsAlgClosed k] : Function.Bijective (frobPhi k p) :=
  ⟨frobPhi_injective k p, frobPhi_surjective k p⟩

theorem continuous_frobPhi : Continuous (frobPhi k p) := by
  have h : frobPhi k p = fun x : ↥(Set.univ : Set (AffineSpace k 1)) =>
      (⟨pointMap k (frobSubst k p) x.1, Set.mem_univ _⟩ :
        ↥(Set.univ : Set (AffineSpace k 1))) := by
    funext x
    apply Subtype.ext
    funext i
    fin_cases i
    simp [frobPhi, pointMap, frobSubst]
  rw [h]
  exact Continuous.subtype_mk
    ((continuous_pointMap k (frobSubst k p)).comp continuous_subtype_val) _

theorem isMorphism_frobPhi :
    IsMorphism (Set.univ : Set (AffineSpace k 1)) (Set.univ : Set (AffineSpace k 1))
      (frobPhi k p) := by
  refine ⟨continuous_frobPhi k p, ?_⟩
  intro U hU f hf x
  obtain ⟨W, hW, hxW, hWU, r, s, hrs⟩ := hf ⟨frobPhi k p x.1, x.2⟩
  refine ⟨frobPhi k p ⁻¹' W, hW.preimage (continuous_frobPhi k p), hxW, ?_,
    frobSubst k p r, frobSubst k p s, ?_⟩
  · intro y hy
    exact hWU hy
  · intro y hy
    obtain ⟨hq, hval⟩ := hrs (frobPhi k p y) hy
    constructor
    · rw [eval_frobSubst]; exact hq
    · rw [eval_frobSubst, eval_frobSubst]
      exact hval

theorem frobPhi_not_isIso [IsAlgClosed k] :
    ¬ IsIso (Set.univ : Set (AffineSpace k 1)) (Set.univ : Set (AffineSpace k 1))
      (frobPhi k p) := by
  rintro ⟨ψ, _hφm, hψm, hleft, _hright⟩
  have hreg : IsRegular (Set.univ : Set (AffineSpace k 1)) Set.univ
      (fun y : ↥(Set.univ : Set ↥(Set.univ : Set (AffineSpace k 1))) => (ψ y.1).1 0) := by
    have h := hψm.2 Set.univ isOpen_univ
      (fun u : ↥(Set.univ : Set ↥(Set.univ : Set (AffineSpace k 1))) => u.1.1 0)
      (isRegular_coord (k := k) 1 0)
    simpa using h
  let O : ↥(Set.univ : Set (AffineSpace k 1)) := ⟨0, Set.mem_univ _⟩
  obtain ⟨W, hW, hOW, hWU, r, s, hrs⟩ := hreg ⟨O, Set.mem_univ _⟩
  have hp0 : p ≠ 0 := by have h := (Fact.out : p.Prime).pos; omega
  let γ : AffineSpace k 1 → ↥(Set.univ : Set (AffineSpace k 1)) :=
    fun x => ⟨x, Set.mem_univ _⟩
  have hγ : Continuous γ := Continuous.subtype_mk continuous_id _
  let T : Set (AffineSpace k 1) := (fun x => frobPhi k p (γ x)) ⁻¹' W
  have hTopen : IsOpen T := hW.preimage ((continuous_frobPhi k p).comp hγ)
  have hT0 : (0 : AffineSpace k 1) ∈ T := by
    show frobPhi k p (γ 0) ∈ W
    have h0 : frobPhi k p (γ 0) = O := by
      apply Subtype.ext
      funext i
      fin_cases i
      simp [frobPhi, γ, O, hp0]
    rw [h0]; exact hOW
  have hTcofinite : Tᶜ.Finite := by
    have hclosed : IsClosed Tᶜ := hTopen.isClosed_compl
    rcases (isClosed_iff_finite_or_univ (k := k)).1 hclosed with h | h
    · exfalso
      have hmem : (0 : AffineSpace k 1) ∈ Tᶜ := by rw [h]; exact Set.mem_univ _
      exact hmem hT0
    · exact h
  have hTinf : T.Infinite := by simpa using hTcofinite.infinite_compl
  have hident : ∀ x ∈ T, r.eval (fun _ => (x 0) ^ p) = x 0 * s.eval (fun _ => (x 0) ^ p) := by
    intro x hx
    obtain ⟨hq, hval⟩ := hrs (frobPhi k p (γ x)) hx
    have hleftx := hleft (γ x)
    have h1 : (ψ (frobPhi k p (γ x))).1 0 = x 0 := by
      have := congrArg (fun u : ↥(Set.univ : Set (AffineSpace k 1)) => u.1 0) hleftx
      simpa [γ] using this
    have h2 : (ψ (frobPhi k p (γ x))).1 0 =
        r.eval (fun _ => (x 0) ^ p) / s.eval (fun _ => (x 0) ^ p) := by
      simpa [γ, frobPhi] using hval
    have hq' : s.eval (fun _ => (x 0) ^ p) ≠ 0 := by
      simpa [γ, frobPhi] using hq
    have h3 : x 0 = r.eval (fun _ => (x 0) ^ p) / s.eval (fun _ => (x 0) ^ p) :=
      h1.symm.trans h2
    rw [eq_div_iff hq'] at h3
    exact h3.symm
  have hpoly : frobSubstPoly k p r - Polynomial.X * frobSubstPoly k p s = 0 := by
    by_contra hne
    have hfin : {t : k | (frobSubstPoly k p r - Polynomial.X * frobSubstPoly k p s).IsRoot t}.Finite :=
      Polynomial.finite_setOfPred_isRoot hne
    have hinj : Set.InjOn (fun x : AffineSpace k 1 => x 0) T := by
      intro x _ y _ hxy
      funext i
      fin_cases i
      exact hxy
    have hmaps : Set.MapsTo (fun x : AffineSpace k 1 => x 0) T
        {t : k | (frobSubstPoly k p r - Polynomial.X * frobSubstPoly k p s).IsRoot t} := by
      intro x hx
      have hx' := hident x hx
      show (frobSubstPoly k p r - Polynomial.X * frobSubstPoly k p s).eval (x 0) = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        eval_frobSubstPoly, eval_frobSubstPoly, hx']
      ring
    exact (Set.infinite_of_injOn_mapsTo hinj hmaps hTinf).not_finite hfin
  have hp1 : p ≠ 1 := by have h := (Fact.out : p.Prime).one_lt; omega
  have h1 : (frobSubstPoly k p r).coeff 1 = 0 := coeff_one_frobSubstPoly k p hp1 r
  have h2 : (Polynomial.X * frobSubstPoly k p s).coeff 1 = (frobSubstPoly k p s).coeff 0 := by
    simpa using Polynomial.coeff_X_mul (frobSubstPoly k p s) 0
  have h3 : (frobSubstPoly k p s).coeff 0 = s.eval (0 : Fin 1 → k) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_frobSubstPoly]
    have hfun : (fun _ : Fin 1 => (0 : k) ^ p) = (0 : Fin 1 → k) := by
      funext i; fin_cases i; simp [hp0]
    rw [hfun]
  have hs0 : s.eval (0 : Fin 1 → k) = 0 := by
    have hc := congrArg (fun q : Polynomial k => q.coeff 1) hpoly
    simp only [Polynomial.coeff_sub, Polynomial.coeff_zero] at hc
    rw [h1, h2, h3] at hc
    simpa using hc
  have hsO : s.eval (0 : Fin 1 → k) ≠ 0 := by
    have h := (hrs O hOW).1
    have hO : O.1 = (0 : Fin 1 → k) := by
      funext i; fin_cases i; simp [O]
    rwa [hO] at h
  exact hsO hs0

/-- Every bijection `A¹ → A¹` is a homeomorphism for the Zariski topology. -/
theorem frobPhi_bicontinuous [IsAlgClosed k] :
    ∃ ψ : ↥(Set.univ : Set (AffineSpace k 1)) → ↥(Set.univ : Set (AffineSpace k 1)),
      (∀ x, ψ (frobPhi k p x) = x) ∧ (∀ y, frobPhi k p (ψ y) = y) ∧ Continuous ψ := by
  choose ψ hψ using frobPhi_surjective (k := k) p
  have hleft : ∀ x, ψ (frobPhi k p x) = x := by
    intro x
    apply frobPhi_injective k p
    rw [hψ (frobPhi k p x)]
  refine ⟨ψ, hleft, hψ, ?_⟩
  rw [continuous_iff_isClosed]
  intro S hS
  rcases (isClosed_univ_line_iff_finite_or_univ (k := k)).1 hS with hfin | huniv
  · have hsub : ψ ⁻¹' S ⊆ frobPhi k p '' S := by
      intro y hy
      exact ⟨ψ y, hy, hψ y⟩
    exact (hfin.image (frobPhi k p)).subset hsub |>.isClosed
  · rw [huniv]
    simp

end FrobeniusPhi

/-! ## The two parts of Hartshorne I.3.2, bundled -/

section Bundled

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **(a)** The parametrization `φ : A¹ → Y`, `t ↦ (t², t³)`, of the cuspidal cubic
`Y = V(y² - x³)` is a bijective, bicontinuous morphism of varieties, but not an isomorphism. -/
theorem hartshorne_I_3_2_a :
    Function.Bijective (cuspPhi k) ∧
    IsMorphism (Set.univ : Set (AffineSpace k 1)) (cusp k) (cuspPhi k) ∧
    (∃ ψ : ↥(cusp k) → ↥(Set.univ : Set (AffineSpace k 1)),
      (∀ x, ψ (cuspPhi k x) = x) ∧ (∀ y, cuspPhi k (ψ y) = y) ∧ Continuous ψ) ∧
    ¬ IsIso (Set.univ : Set (AffineSpace k 1)) (cusp k) (cuspPhi k) :=
  ⟨cuspPhi_bijective k, isMorphism_cuspPhi k, cuspPhi_bicontinuous k, cuspPhi_not_isIso k⟩

/-- **(b)** The Frobenius map `φ : A¹ → A¹`, `t ↦ t^p`, is a bijective, bicontinuous morphism
of varieties, but not an isomorphism. -/
theorem hartshorne_I_3_2_b (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Bijective (frobPhi k p) ∧
    IsMorphism (Set.univ : Set (AffineSpace k 1)) (Set.univ : Set (AffineSpace k 1))
      (frobPhi k p) ∧
    (∃ ψ : ↥(Set.univ : Set (AffineSpace k 1)) → ↥(Set.univ : Set (AffineSpace k 1)),
      (∀ x, ψ (frobPhi k p x) = x) ∧ (∀ y, frobPhi k p (ψ y) = y) ∧ Continuous ψ) ∧
    ¬ IsIso (Set.univ : Set (AffineSpace k 1)) (Set.univ : Set (AffineSpace k 1))
      (frobPhi k p) :=
  ⟨frobPhi_bijective k p, isMorphism_frobPhi k p, frobPhi_bicontinuous k p,
    frobPhi_not_isIso k p⟩

end Bundled

#print axioms Hartshorne77.Ex_I_3_2.hartshorne_I_3_2_a
#print axioms Hartshorne77.Ex_I_3_2.hartshorne_I_3_2_b
#print axioms Hartshorne77.Ex_I_3_2.cuspPhi_not_isIso
#print axioms Hartshorne77.Ex_I_3_2.frobPhi_not_isIso
#print axioms Hartshorne77.Ex_I_3_2.cuspPhi_bicontinuous
#print axioms Hartshorne77.Ex_I_3_2.frobPhi_bicontinuous
#print axioms Hartshorne77.Ex_I_3_2.isMorphism_cuspPhi
#print axioms Hartshorne77.Ex_I_3_2.isMorphism_frobPhi
#print axioms Hartshorne77.Ex_I_3_2.coeff_one_cuspSubstPoly
#print axioms Hartshorne77.Ex_I_3_2.coeff_one_frobSubstPoly
#print axioms Hartshorne77.Ex_I_3_2.cuspInv_not_isMorphism
#print axioms Hartshorne77.Ex_I_3_2.isRegular_cuspInv_away
#print axioms Hartshorne77.Ex_I_3_2.cuspPhi_bijective
#print axioms Hartshorne77.Ex_I_3_2.frobPhi_bijective
#print axioms Hartshorne77.Ex_I_3_2.continuous_cuspPhi
#print axioms Hartshorne77.Ex_I_3_2.continuous_frobPhi
#print axioms Hartshorne77.Ex_I_3_2.continuous_cuspInv
#print axioms Hartshorne77.Ex_I_3_2.cuspInv_left
#print axioms Hartshorne77.Ex_I_3_2.cuspInv_right
#print axioms Hartshorne77.Ex_I_3_2.eval_cuspSubst
#print axioms Hartshorne77.Ex_I_3_2.eval_frobSubst
#print axioms Hartshorne77.Ex_I_3_2.isRegular_coord
