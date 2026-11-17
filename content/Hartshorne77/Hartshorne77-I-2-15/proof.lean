import Mathlib

/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise I.2.15 — complete

**The quadric surface in P³.**  Namespace `Hartshorne77.Ex_I_2_15`, single `import Mathlib`,
Lean 4.33.1, no `sorry`/`admit`/custom axioms.

## Source statement

> 2.15. The Quadric Surface in P³ (Fig. 2). Consider the surface Q (a surface is a variety of
> dimension 2) in P³ defined by the equation xy − zw = 0.
> (a) Show that Q is equal to the Segre embedding of P¹ × P¹ in P³, for suitable choice of
> coordinates.
> (b) Show that Q contains two families of lines {L_t}, {M_t}, each parametrized by t ∈ P¹, with
> the properties that if L_t ≠ L_s then L_t ∩ L_s = ∅; if M_t ≠ M_s, M_t ∩ M_s = ∅, and for all
> t,u, L_t ∩ M_u = one point.
> (c) Show that Q contains other curves besides these lines, and deduce that the Zariski topology
> on Q is not homeomorphic via ψ to the product topology on P¹ × P¹.

## What this file proves

Main statement: `P.hartshorne_I_2_15_complete` — every clause (a), (b), (c) together with the
parenthetical definition of the word *surface*: `Q` is closed, irreducible, and of Hartshorne
chain dimension two (`IsClosed quadric ∧ IsIrreducible quadric ∧ DimEq quadric 2`).

| Clause | Declarations |
|---|---|
| `P^n` as the classical point set (lines through `0` in `k^{n+1}`), Zariski topology, vanishing of homogeneous forms, closed = zero locus | `P`, `P.mk`, `P.zeroLocus`, `P.zariskiTopology`, `P.isClosed_iff_exists_zeroLocus` (copied from the accepted I.2.5 development) |
| (a) `Q = ψ(P¹×P¹)`, `ψ(a₀:a₁;b₀:b₁) = (a₀b₀:a₀b₁:a₁b₀:a₁b₁)` | `P.segre`, `P.segre_mk`, `P.segre_inj`, `P.range_segre`, `P.quadric_exists_segre` |
| (a) "for suitable choice of coordinates" (the book's `xy − zw`) | `P.permMap`, `P.permMap_image_zeroLocus`, `P.coordsPerm`, `P.rename_coordsPerm`, `P.exists_coordinates_quadric` |
| (b) rulings `L_t = ψ(P¹×{t})`, `M_t = ψ({t}×P¹)`; lines of dimension one; disjointness; `L_t ∩ M_u` a point | `P.L`, `P.M`, `P.L_isProjectiveLine`, `P.M_isProjectiveLine`, `P.L_eq_iff`, `P.M_eq_iff`, `P.L_disjoint`, `P.M_disjoint`, `P.L_inter_M` |
| (c) a curve on `Q` that is not a line | `P.conic`, `P.isClosed_conic`, `P.irreducible_conic`, `P.dim_conic`, `P.conic_ne_L`, `P.conic_ne_M` |
| (c) Zariski topology on `Q` ≠ product topology under `ψ` | `P.diag`, `P.diag_not_closed`, `P.not_homeomorph_product` |
| *surface*: `Q` closed, irreducible, `dim = 2` (**previously missing**) | `P.isClosed_quadric`, `P.isIrreducible_quadric`, `P.dimEq_quadric`, `P.quadric_isVarietyOfDimTwo` |

## The two previously missing clauses and how they are proved

1. **The gate** `(Ideal.span {X₀X₃ − X₁X₂}).IsPrime` (`P.isPrime_span_quadForm`).  The equation
   is irreducible (`P.irreducible_quadForm`): it is linear in `X₃` with leading coefficient `X₀`,
   and `X₀`, `X₁X₂` have no common divisor (`P.isUnit_of_dvd_X_of_dvd_X_mul_X`, the coprimality
   technique of the accepted I.2.16 proof), so Mathlib's `MvPolynomial.irreducible_mul_X_add`
   applies.  Over a field, `MvPolynomial` is a unique factorization monoid, so irreducible
   elements are prime (`P.prime_quadForm`), and `Ideal.span_singleton_prime` yields the gate.
   No change of coordinates, no elimination, no quotient-into-a-domain map.

2. **Dimension and irreducibility**, transferred from the accepted I.2.8 hypersurface theorem
   rather than reproved.  Section `Copy8` below is the accepted I.2.8 development
   (`content/Hartshorne77/Hartshorne77-I-2-8/proof.lean`) copied inline, namespace renamed, as
   the campaign rules permit; it defines the classical model `Copy8.Proj k n =
   Projectivization k (Fin (n+1) → k)` with Hartshorne's chain dimension
   `projDim = irrChainDim` and contains `Proj.projDim_zeroSet : projDim (zeroSet f) + 1 = n` for
   irreducible homogeneous `f` of positive degree.
   The bridge `P k n ≃ Copy8.Proj k n` (`P.projEquiv`) is **built and proved**, not aliased:
   * `P.toProj`, `P.ofProj`, `P.projEquiv` — the identity of the two sets of lines through `0`;
   * `P.isZeroAt_toProj`, `P.image_zeroLocus`, `P.preimage_zeroLocus` — vanishing of a
     homogeneous form agrees, so images and preimages of zero loci are zero loci;
   * `P.isClosed_image_toProj_iff` — **the two models have exactly the same closed sets**;
   * `P.isPreirreducible_image_toProj_iff`, `P.isIrreducible_image_toProj_iff` — irreducibility
     transfers;
   * `P.hasChainIn_le_irrChainDim` — a chain of length `m` in `S` becomes an `LTSeries` of length
     `m` in the image, so `m ≤ irrChainDim (image S)`.
   Then `P.isIrreducible_quadric` is obtained from `Copy8.zeroLocus_irreducible` (the affine cone
   over `Q` is the zero locus of the prime ideal `(X₀X₃ − X₁X₂)`, `Copy8.Proj.cone_zeroSet`)
   together with `Copy8.Proj.isIrreducible_cone_iff`; and `P.dimEq_quadric` from
   `Copy8.Proj.projDim_zeroSet` at `n = 3`, `f = X₀X₃ − X₁X₂`, `d = 2`:
   `projDim Q + 1 = 3`, i.e. `dim Q = 2`; the case `m ≥ 3` is excluded through
   `P.hasChainIn_le_irrChainDim`.  The lower bound `DimEq Q 2` is the explicit chain
   *point ⊂ conic ⊂ Q* (`P.hasChainIn_quadric_two`, using `P.dim_conic` and
   `P.conic_ne_quadric`).

## Edge conditions and hypothesis use

* `k` algebraically closed is the standing hypothesis of Chapter I and is genuinely used:
  `Copy8`'s Nullstellensatz dictionary (`zeroLocus_irreducible`, `varietyDim_zeroLocus`), and
  `Infinite k` (an instance of `IsAlgClosed`) in `Copy8.Proj.isIrreducible_cone_iff` and in this
  file's `P1_open_inter_nonempty`.  `IsIrreducible quadric` is **false over a finite field** (then
  `Q` is a finite set with more than one closed point, hence reducible); the file therefore states
  these two clauses under `[IsAlgClosed k]` only, and nothing weaker is claimed.
* `projDim_zeroSet` requires `0 < d` (`d = 2`) and `Irreducible f` (the gate) and `Q ≠ ∅`
  (`P.zeroSet_quadForm_nonempty`, the point `(1:0:0:0)`): all three supplied.
* `DimEq` is Hartshorne's chain dimension, not ring Krull dimension and not a scheme dimension.

## Axiom audit

The `#print axioms` reports at the end of the file cover the main theorem, the two new clauses,
the gate, the bridge lemmas and the inherited main results; every one is exactly
`[propext, Classical.choice, Quot.sound]`.
-/


/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise 2.8

## The book statement

Exercise I.2.8 of Hartshorne's *Algebraic Geometry* (Chapter I, §2, "Projective Varieties"):

> "A projective variety `Y ⊆ P^n` has dimension `n - 1` if and only if it is the zero set of a
> single irreducible homogeneous polynomial `f` of positive degree.  `Y` is called a hypersurface
> in `P^n`."

Every clause and standing hypothesis of the book is used:

* `k` is an algebraically closed field (Chapter I, §1 standing hypothesis). It enters through the
  Nullstellensatz dictionary (affine and projective) and is needed for it.
* `P^n` is the classical projective space of lines through the origin in `k^{n+1}`
  (`Projectivization k (Fin (n+1) → k)`), with the Zariski topology whose closed sets are the
  zero loci of homogeneous polynomials.
* "projective variety" = irreducible closed subset of `P^n` (Hartshorne I.1). In Mathlib this is
  `IsClosed Y`, `IsIrreducible Y` (which already includes `Y.Nonempty`).
* `dim` is Hartshorne's intrinsic topological dimension: the supremum of the lengths of chains of
  nonempty irreducible closed subsets (Hartshorne I.1, Prop. 1.10). Here this is `projDim`, defined
  by `irrChainDim` as the supremum of lengths of `LTSeries` of irreducible closed subsets; no
  transcendence degree or other substitute invariant is used.
* "zero set of a single irreducible homogeneous polynomial of positive degree" is
  `Proj.zeroSet f` for `f` irreducible, `f.IsHomogeneous d` with `0 < d`.

The formulation `projDim Y + 1 = (n : ℕ∞)` is used for `dim Y = n - 1`; both are equivalent for
`n ≥ 1`, and the addition form is the correct transcription also for `n = 0`
(`hartshorne_exercise_I_2_8_sub` records the literal `n - 1` form under `1 ≤ n`).  When `n = 0`,
`P^0` is a single point, `dim P^0 = 0 ≠ -1`, and no projective zero set of a positive-degree
homogeneous polynomial is nonempty (a positive-degree form in `k[x₀]` vanishes only at the origin
of `k¹`), so both sides of the equivalence are false and it holds.

## Provenance of the statement

The statement above is a reconstruction of the book's exercise, cross-checked against three
independent renderings:

* the bundled natural proof `Hartshorne77-I-2-8/proof.tex`, whose argument is exactly the standard
  one for this statement (`dim Y = n - 1` ⟺ `ht I(Y) = 1` ⟺, `k[x₀,…,xₙ]` being a UFD,
  `I(Y) = (f)` for an irreducible homogeneous `f` of positive degree);
* the public solution rendering <https://hartshornesolutions.blogspot.com/2015/06/chapter-1-exercise-28-hypersurfaces-and.html>,
  which quotes the boxed exercise text: "A projective variety `Y ⊆ P^n` has dimension `n-1` if and
  only if it is the zero set of a single irreducible homogeneous polynomial `f` of positive degree.
  `Y` is called a hypersurface in `P^n`.";
* numbering cross-check: the neighbouring exercises I.2.6, I.2.7, I.2.9, I.2.10 in the same
  sources are `dim S(Y) = dim Y + 1`, `dim P^n = n` / `dim Y = dim Ȳ`, projective closure, and the
  cone over a projective variety, matching the local OCR files of `Hartshorne77-I-2-6/7/9/10`.

The exercise has no lettered parts; the closing sentence "`Y` is called a hypersurface in `P^n`" is a
definition, formalised as `IsHypersurface`.

## Content and provenance

* Sections up to (and including) the affine/projective infrastructure block are the accepted
  Hartshorne I.2.10 formalisation (cone of a projective algebraic set, `dim C(Y) = dim Y + 1`,
  chain dimension, and the affine hypersurface theorem of I.1.8 with its ring-theoretic dimension
  lemmas), copied verbatim; only the namespace differs.
* Everything from `I.2.8 proper` onward is new for this exercise.

## Coverage map (clause by clause)

| book clause | formal counterpart |
|---|---|
| `Y ⊆ P^n` is a projective variety | hypotheses `IsClosed Y`, `IsIrreducible Y` (hence `Y.Nonempty`) |
| `dim` is topological dimension | `projDim Y = irrChainDim Y`, `irrChainDim = ⨆ l : LTSeries {Z // Z ⊆ Y, IsIrreducible Z, IsClosed Z}, l.length` |
| `f` homogeneous of degree `d > 0` | `f.IsHomogeneous d`, `0 < d` |
| `f` irreducible | `Irreducible f` |
| `Y = Z(f)` | `Y = Proj.zeroSet f` |
| `dim Y = n - 1` | `projDim Y + 1 = (n : ℕ∞)` (`= (n-1 : ℕ)` for `1 ≤ n`) |
| `⇒` (dimension forces a hypersurface) | `exists_irreducible_homogeneous_of_projDim` |
| `⇐` (a hypersurface has dimension `n - 1`) | `Proj.projDim_zeroSet` |

## Proof outline

`⇐`: `C(Z(f)) = V(f) ⊆ A^{n+1}` (`Proj.cone_zeroSet`); `V(f)` is an affine hypersurface whose
coordinate ring `k[x₀,…,xₙ]/(f)` has dimension `n` (`Proj.irrChainDim_cone_zeroSet`, from
`ringKrullDim_quotient_span_singleton`), so `dim Z(f) = dim C(Z(f)) - 1 = n - 1`
(`coneDim_eq_projDim_add_one`).

`⇒`: `C(Y) = V(I(Y))` is irreducible of dimension `n = (n+1) - 1`, so `I(Y)` is a prime ideal with
`dim k[x]/(I(Y)) = n`.  Pick `0 ≠ t ∈ I(Y)` and a prime `q ⊆ I(Y)` minimal over `(t)`: the
principal ideal theorem gives `ht q = 1` and the dimension formula gives `dim k[x]/q = n`.
Since `V(I(Y)) ⊆ V(q)` are irreducible closed of the same chain dimension, `V(q) = V(I(Y))`, so
`q = I(Y)` and `ht I(Y) = 1`.  Over the UFD `k[x₀,…,xₙ]` height-one primes are principal
(`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`): `I(Y) = (h)`.  As `I(Y)` is homogeneous,
every homogeneous component of `h` lies in `(h)`, and the top component `h_d = a·h` has the same
total degree as `h`; the top component of a product is the product of top components, so `a` is a
constant and `h` is homogeneous (`homogeneousComponent_mul_totalDegree`).  Its degree is positive
(otherwise `h` would be a unit) and `h` is prime, hence irreducible.  Finally `Y = Z(h)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MvPolynomial

namespace Copy8
universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ## Homogeneous polynomials and scaling -/

/-- A homogeneous polynomial of degree `d` scales by `c ^ d` when the coordinates are scaled
by `c`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : k) (a : σ → k) :
    MvPolynomial.eval (fun i => c * a i) f = c ^ d * MvPolynomial.eval a f := by
  conv_lhs => rw [as_sum f]
  conv_rhs => rw [as_sum f]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := (hf.degree_eq_sum_deg_support hm).symm
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum m.support (fun i => m i) c, hdeg]
  ring

/-! ## The classical projective space -/

/-- The classical projective space `P^n` over `k`: the set of lines through the origin in
`k^{n+1}`, i.e. of nonzero vectors modulo multiplication by a nonzero scalar. -/
abbrev Proj (k : Type u) [Field k] (n : ℕ) : Type u := Projectivization k (Fin (n + 1) → k)

namespace Proj

/-- The point of `P^n` represented by a nonzero vector. -/
abbrev mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : Proj k n := Projectivization.mk k v hv

/-- A homogeneous polynomial vanishes at a projective point. -/
def IsZeroAt (f : MvPolynomial (Fin (n + 1)) k) (x : Proj k n) : Prop :=
  MvPolynomial.eval x.rep f = 0

/-- Vanishing of a homogeneous polynomial does not depend on the chosen representative of the
projective point. -/
theorem isZeroAt_mk_iff {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hf : f.IsHomogeneous d)
    {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    IsZeroAt f (mk v hv) ↔ MvPolynomial.eval v f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) v hv
  have hrep : (mk v hv).rep = fun i => (a : k) * v i := by
    rw [← ha]; rfl
  rw [IsZeroAt, hrep, eval_smul_of_isHomogeneous hf (a : k)]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero d (Units.ne_zero a))
  · intro h
    rw [h, mul_zero]

/-- The set of homogeneous polynomials (each with a chosen degree). -/
abbrev HomogPoly (k : Type u) [Field k] (n : ℕ) : Type u :=
  {f : MvPolynomial (Fin (n + 1)) k // ∃ d, f.IsHomogeneous d}

/-- The projective zero locus of a set of homogeneous polynomials. -/
def zeroLocus (S : Set (HomogPoly k n)) : Set (Proj k n) :=
  {x | ∀ f ∈ S, IsZeroAt f.1 x}

theorem mem_zeroLocus_iff {S : Set (HomogPoly k n)} {x : Proj k n} :
    x ∈ zeroLocus S ↔ ∀ f ∈ S, IsZeroAt f.1 x := Iff.rfl

theorem zeroLocus_anti_mono {S T : Set (HomogPoly k n)} (h : S ⊆ T) :
    zeroLocus T ⊆ zeroLocus S :=
  fun _ hx f hf => hx f (h hf)

theorem zeroLocus_empty : zeroLocus (∅ : Set (HomogPoly k n)) = Set.univ := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_empty_iff_false, IsEmpty.forall_iff,
    Set.mem_univ]
  simp

theorem zeroLocus_union (S T : Set (HomogPoly k n)) :
    zeroLocus (S ∪ T) = zeroLocus S ∩ zeroLocus T := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

theorem zeroLocus_iUnion {ι : Type*} (S : ι → Set (HomogPoly k n)) :
    zeroLocus (⋃ i, S i) = ⋂ i, zeroLocus (S i) := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_sUnion (A : Set (Set (HomogPoly k n))) :
    zeroLocus (⋃₀ A) = ⋂₀ (zeroLocus '' A) := by
  ext x
  simp only [zeroLocus, Set.mem_ofPred_eq, Set.mem_sUnion, Set.mem_sInter, Set.mem_image]
  constructor
  · rintro h Z ⟨S, hS, rfl⟩ f hf
    exact h f ⟨S, hS, hf⟩
  · rintro h f ⟨S, hS, hf⟩
    exact h (zeroLocus S) ⟨S, hS, rfl⟩ f hf

theorem zeroLocus_univ : zeroLocus (Set.univ : Set (HomogPoly k n)) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  refine hj ?_
  have h := hx ⟨MvPolynomial.X j, 1, MvPolynomial.isHomogeneous_X (R := k) j⟩ (Set.mem_univ _)
  simpa [IsZeroAt] using h

/-- The set of products of one member of `S` with one member of `T`. -/
def mulSet (S T : Set (HomogPoly k n)) : Set (HomogPoly k n) :=
  {h | ∃ f ∈ S, ∃ g ∈ T, h.1 = f.1 * g.1}

theorem zeroLocus_mulSet (S T : Set (HomogPoly k n)) :
    zeroLocus (mulSet S T) = zeroLocus S ∪ zeroLocus T := by
  ext x
  rw [Set.mem_union, mem_zeroLocus_iff]
  constructor
  · intro hx
    by_cases h : ∀ f ∈ S, IsZeroAt f.1 x
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨f, hf, hfx⟩ := h
      intro g hg
      obtain ⟨df, hdf⟩ := f.2
      obtain ⟨dg, hdg⟩ := g.2
      have h2 : IsZeroAt (f.1 * g.1) x :=
        hx ⟨f.1 * g.1, df + dg, hdf.mul hdg⟩ ⟨f, hf, g, hg, rfl⟩
      rw [IsZeroAt, map_mul] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hfx
      · exact h3
  · rintro (h | h)
    · intro h' hf'
      obtain ⟨f', hf', g', hg', heq⟩ := hf'
      rw [IsZeroAt, heq, map_mul, h f' hf', zero_mul]
    · intro h' hf'
      obtain ⟨f', hf', g', hg', heq⟩ := hf'
      rw [IsZeroAt, heq, map_mul, h g' hg', mul_zero]

/-- The Zariski topology on `P^n`: closed sets are zero loci of sets of homogeneous
polynomials. -/
noncomputable abbrev zariskiTopology : TopologicalSpace (Proj k n) :=
  TopologicalSpace.ofClosed (Set.range (zeroLocus (k := k) (n := n)))
    ⟨Set.univ, zeroLocus_univ⟩
    (by
      intro A hA
      refine ⟨⋃₀ {S : Set (HomogPoly k n) | zeroLocus S ∈ A}, ?_⟩
      rw [zeroLocus_sUnion]
      congr 1
      ext Z
      constructor
      · rintro ⟨S, hS, rfl⟩
        exact hS
      · intro hZ
        obtain ⟨S, rfl⟩ := hA hZ
        exact ⟨S, hZ, rfl⟩)
    (by
      rintro A ⟨S, rfl⟩ B ⟨T, rfl⟩
      exact ⟨mulSet S T, zeroLocus_mulSet S T⟩)

/-- A set of projective points is closed for the Zariski topology iff it is the zero locus of a
set of homogeneous polynomials. -/
def IsProjClosed (Z : Set (Proj k n)) : Prop := ∃ S : Set (HomogPoly k n), zeroLocus S = Z

end Proj

/-- The projective Zariski topology. -/
noncomputable abbrev projTopologicalSpace (k : Type u) [Field k] (n : ℕ) : TopologicalSpace (Proj k n) :=
  Proj.zariskiTopology

attribute [instance] projTopologicalSpace

namespace Proj

theorem isOpen_iff (U : Set (Proj k n)) :
    IsOpen U ↔ Uᶜ ∈ Set.range (zeroLocus (k := k) (n := n)) := Iff.rfl

theorem isClosed_iff (Z : Set (Proj k n)) :
    IsClosed Z ↔ Z ∈ Set.range (zeroLocus (k := k) (n := n)) := by
  constructor
  · intro h
    have h1 : (Zᶜ)ᶜ ∈ Set.range (zeroLocus (k := k) (n := n)) := (isOpen_iff Zᶜ).1 h.isOpen_compl
    rwa [compl_compl] at h1
  · intro h
    exact ⟨(isOpen_iff Zᶜ).2 (by rwa [compl_compl])⟩

theorem isClosed_of_isProjClosed {Z : Set (Proj k n)} (hZ : IsProjClosed Z) : IsClosed Z :=
  (isClosed_iff Z).2 hZ

theorem isProjClosed_zeroLocus (S : Set (HomogPoly k n)) : IsProjClosed (zeroLocus S) :=
  ⟨S, rfl⟩

theorem isProjClosed_iff_isClosed (Z : Set (Proj k n)) : IsProjClosed Z ↔ IsClosed Z :=
  (isClosed_iff Z).symm

end Proj

end Copy8

/-! ## The affine cone and the vanishing ideal -/

namespace Copy8
universe u
variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

/-- The affine cone over a set of projective points: the union of the lines through the origin
lying over `Y`, together with the origin. -/
def cone (Y : Set (Proj k n)) : Set (Fin (n + 1) → k) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, mk v hv ∈ Y}

/-- `I(Y)`: the homogeneous ideal of `Y`, i.e. the ideal generated by all homogeneous polynomials
vanishing on `Y`. -/
noncomputable def vanishingIdeal (Y : Set (Proj k n)) : Ideal (MvPolynomial (Fin (n + 1)) k) :=
  Ideal.span {f | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x}

theorem subset_vanishingIdeal {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (h : ∀ x ∈ Y, IsZeroAt f x) : f ∈ vanishingIdeal Y :=
  Ideal.subset_span ⟨d, hf, h⟩

theorem vanishingIdeal_mem_iff {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} :
    f ∈ vanishingIdeal Y ↔
      f ∈ Ideal.span {g | ∃ d, g.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt g x} :=
  Iff.rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem vanishingIdeal_isHomogeneous (Y : Set (Proj k n)) :
    (vanishingIdeal Y).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := by
  have h := Ideal.homogeneous_span (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
    {f : MvPolynomial (Fin (n + 1)) k | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x}
    (fun f hf => by
      obtain ⟨d, hd, -⟩ := hf
      exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule d f).2 hd⟩)
  exact h

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem eval_zero_of_isHomogeneous_pos {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) :
    MvPolynomial.eval (0 : Fin (n + 1) → k) f = 0 := by
  have h := eval_smul_of_isHomogeneous hf (0 : k) (fun _ : Fin (n + 1) => (1 : k))
  simpa [zero_pow hd.ne'] using h

/-- If `f` is homogeneous of degree `0` and vanishes at some projective point then `f = 0`. -/
theorem eq_zero_of_isHomogeneous_zero {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous 0)
    {x : Proj k n} (hx : IsZeroAt f x) : f = 0 := by
  have hC : f = MvPolynomial.C (f.coeff 0) := by
    have h := hf.totalDegree_le
    rw [Nat.le_zero] at h
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
  rw [hC] at hx ⊢
  simpa [IsZeroAt] using hx

/-- A homogeneous polynomial vanishing on `Y` vanishes at the origin of the cone. -/
theorem eval_zero_of_mem_gens {Y : Set (Proj k n)} (hY : Y.Nonempty)
    {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ x ∈ Y, IsZeroAt f x) : MvPolynomial.eval (0 : Fin (n + 1) → k) f = 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    obtain ⟨x, hx⟩ := hY
    rw [eq_zero_of_isHomogeneous_zero hf (h x hx)]
    simp
  · exact eval_zero_of_isHomogeneous_pos hd hf

/-- The cone over `Y` is contained in the affine zero locus of `I(Y)`. -/
theorem cone_subset_zeroLocus {Y : Set (Proj k n)} (hY : Y.Nonempty) :
    cone Y ⊆ MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) := by
  intro v hv
  rw [MvPolynomial.mem_zeroLocus_iff]
  have hgen : ∀ f ∈ {f : MvPolynomial (Fin (n + 1)) k | ∃ d, f.IsHomogeneous d ∧ ∀ x ∈ Y, IsZeroAt f x},
      MvPolynomial.eval v f = 0 := by
    rintro f ⟨d, hd, hf⟩
    rcases hv with rfl | ⟨hvne, hvY⟩
    · exact eval_zero_of_mem_gens hY hd hf
    · exact (isZeroAt_mk_iff hd hvne).1 (hf _ hvY)
  have hle : vanishingIdeal Y ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [vanishingIdeal, Ideal.span_le]
    intro f hf
    simpa using hgen f hf
  intro f hf
  simpa using hle hf

/-- Conversely, the affine zero locus of `I(Y)` is contained in the cone over `Y`. -/
theorem zeroLocus_subset_cone {Y : Set (Proj k n)} (hY : IsProjClosed Y) :
    MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) ⊆ cone Y := by
  obtain ⟨S, rfl⟩ := hY
  intro v hv
  rcases eq_or_ne v 0 with rfl | hvne
  · exact Or.inl rfl
  · refine Or.inr ⟨hvne, ?_⟩
    have hv' : ∀ p ∈ vanishingIdeal (zeroLocus S), MvPolynomial.eval v p = 0 := by
      intro p hp
      simp only [MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval] at hv
      exact hv p hp
    intro g hg
    have hgen : g.1 ∈ vanishingIdeal (zeroLocus S) := by
      obtain ⟨d, hd⟩ := g.2
      refine subset_vanishingIdeal hd fun x hx => by simpa [IsZeroAt] using hx g hg
    obtain ⟨d, hd⟩ := g.2
    exact (isZeroAt_mk_iff hd hvne).2 (hv' g.1 hgen)

/-- **(a)** The cone over a closed set is the affine algebraic set defined by the ideal `I(Y)`. -/
theorem cone_eq_zeroLocus {Y : Set (Proj k n)} (hY : IsProjClosed Y) (hne : Y.Nonempty) :
    cone Y = MvPolynomial.zeroLocus (K := k) (vanishingIdeal Y) :=
  Set.Subset.antisymm (cone_subset_zeroLocus hne) (zeroLocus_subset_cone hY)

end Proj

end Copy8

/-! ## Affine dimension theory (accepted Hartshorne I.1.8 infrastructure) -/

namespace Copy8
section Krull

variable {A : Type*} [CommRing A]

/-- In a Noetherian domain, a prime minimal over a nonzero principal ideal has height one. -/
theorem Ideal.height_eq_one_of_mem_minimalPrimes [IsNoetherianRing A] [IsDomain A]
    {t : A} (ht : t ≠ 0) {p : Ideal A} (hp : p ∈ (Ideal.span {t}).minimalPrimes) :
    p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
  have h1 : (1 : ℕ∞) ≤ (Ideal.span {t}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  refine le_trans h1 ?_
  rw [Ideal.height_eq_inf_minimalPrimes]
  exact iInf₂_le p hp

/-- The image of a prime minimal over `I` in `A ⧸ I` has height zero. -/
theorem Ideal.height_map_quotient_eq_zero [IsNoetherianRing A] {I P : Ideal A}
    (h : P ∈ I.minimalPrimes) : (P.map (Ideal.Quotient.mk I)).height = 0 := by
  have hP : P.IsPrime := h.isPrime
  have : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime h.le
  have key : P.map (Ideal.Quotient.mk I) ∈ minimalPrimes (A ⧸ I) := by
    rw [Ideal.minimalPrimes_eq_comap] at h
    obtain ⟨Q, hQ, hQP⟩ := h
    rw [← hQP]
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
    exact hQ
  rw [Ideal.height_eq_zero_iff]
  exact key

/-- Height and dimension are preserved by integral injective extensions of domains. -/
theorem Ideal.height_eq_height_under_of_isIntegral {B S : Type*} [CommRing B] [CommRing S]
    [IsDomain B] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S] [FaithfulSMul B S]
    [IsNoetherianRing B] [IsNoetherianRing S] [Algebra.HasGoingDown B S] {P : Ideal S} [P.IsPrime] :
    P.height = (P.under B).height := by
  have : P.LiesOver (P.under B) := ⟨rfl⟩
  have h2 : (P.map (Ideal.Quotient.mk ((P.under B).map (algebraMap B S)))).height = 0 :=
    Ideal.height_map_quotient_eq_zero (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := B) P)
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under B) P, h2, add_zero]

end Krull

section IntegralDim

variable {B S : Type*} [CommRing B] [CommRing S] [IsDomain B] [IsDomain S] [Algebra B S]
  [Algebra.IsIntegral B S] [FaithfulSMul B S] [IsNoetherianRing B] [IsNoetherianRing S]
  [Algebra.HasGoingDown B S]

/-- Integral injective extensions of Noetherian domains have the same Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective : ringKrullDim S = ringKrullDim B := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := P)
    rw [h]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro q hq
    obtain ⟨Q, -, hQprime, hQeq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := S) q (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B S)]; exact bot_le)
    haveI := hQprime
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := Q)
    show q.height ≤ ringKrullDim S
    rw [← hQeq, ← h]
    exact Ideal.height_le_ringKrullDim_of_isPrime

end IntegralDim

section Concat

variable {A : Type*} [CommRing A]

/-- Concatenation of chains: if `p` is a prime of height one in a domain, then passing to
`A ⧸ p` lowers heights by at most one. -/
theorem Ideal.height_map_quotient_add_one_le [IsNoetherianRing A] [IsDomain A] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1) :
    (q.map (Ideal.Quotient.mk p)).height + 1 ≤ q.height := by
  have hp0 : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hp
    exact zero_ne_one hp
  haveI : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨lq, hlq, hlenq⟩ := Ideal.exists_ltSeries_length_eq_height (q.map (Ideal.Quotient.mk p))
  set F : LTSeries (PrimeSpectrum A) :=
    lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk p))
      (RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective) with hF
  have hbot : (⊥ : PrimeSpectrum A) < F.head := by
    have hple : p ≤ F.head.asIdeal := by
      rw [hF]
      show p ≤ Ideal.comap (Ideal.Quotient.mk p) _
      rw [← Ideal.map_le_iff_le_comap]
      simp
    exact (bot_lt_iff_ne_bot.mpr hp0).trans_le hple
  let G : LTSeries (PrimeSpectrum A) := F.cons ⊥ hbot
  have hFlast : F.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    rw [hF]
    change PrimeSpectrum.comap (Ideal.Quotient.mk p) (RelSeries.last lq) = _
    rw [hlq]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hcomap : Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (A ⧸ p)) = p := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, sup_of_le_left hpq]
  have hlenF : F.length = lq.length := by simp [F]
  have hlenG : G.length = F.length + 1 := by simp [G]
  have hGlast : G.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    change (F.cons ⊥ hbot).last = _
    rw [RelSeries.last_cons, hFlast]
  have hlen : G.length = (q.map (Ideal.Quotient.mk p)).height + 1 := by
    rw [hlenG, hlenF, ← hlenq]
    push_cast
    ring
  rw [← hlen]
  have h := Order.length_le_height (p := G) (x := (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A))
    (le_of_eq hGlast)
  rwa [← PrimeSpectrum.height_eq_orderHeight] at h

end Concat
section PointHeight

variable (k : Type*) [Field k]

/-- Substitution sending `X i` to the constant `a i` for `i < j`, and fixing the other variables. -/
noncomputable def substBelow {s : ℕ} (j : ℕ) (a : Fin s → k) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  MvPolynomial.aeval fun i => if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k)
    else MvPolynomial.X i

lemma substBelow_X {s : ℕ} (j : ℕ) (a : Fin s → k) (i : Fin s) :
    substBelow k j a (MvPolynomial.X i) =
      if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i := by
  simp [substBelow]

lemma substBelow_zero {s : ℕ} (a : Fin s → k) : substBelow k 0 a = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substBelow_X]

lemma substBelow_succ {s : ℕ} (j : ℕ) (a : Fin s → k) :
    substBelow k (j + 1) a = (MvPolynomial.aeval fun (i : Fin s) =>
      if (i : ℕ) = j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i).comp
      (substBelow k j a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, substBelow_X, substBelow_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega), MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  · rw [if_neg h]
    by_cases h2 : (i : ℕ) = j
    · rw [MvPolynomial.aeval_X, if_pos h2, if_pos (by omega)]
    · rw [MvPolynomial.aeval_X, if_neg h2, if_neg (by omega)]

lemma ker_substBelow_antitone {s : ℕ} (j : ℕ) (a : Fin s → k) :
    RingHom.ker (substBelow k j a) ≤ RingHom.ker (substBelow k (j + 1) a) := by
  intro f hf
  simp only [RingHom.mem_ker] at hf ⊢
  rw [substBelow_succ, AlgHom.comp_apply, hf, map_zero]

lemma X_sub_C_mem_ker_substBelow_succ {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∈
      RingHom.ker (substBelow k (j + 1) a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_pos (show ((⟨j, hj⟩ : Fin s) : ℕ) < j + 1 from by simp)]
  simp

lemma X_sub_C_notMem_ker_substBelow {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∉
      RingHom.ker (substBelow k j a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_neg (show ¬ ((⟨j, hj⟩ : Fin s) : ℕ) < j from by simp)]
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => a ⟨j, hj⟩ + 1)) h
  simp at h2

end PointHeight

section Height

variable (k : Type*) [Field k]

/-- The ideal of polynomials vanishing at a point of affine `s`-space has height `s`. -/
theorem vanishingIdeal_singleton_height (s : ℕ) (a : Fin s → k) :
    (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height = ↑s := by
  have hker : RingHom.ker (substBelow k s a) = MvPolynomial.vanishingIdeal k {a} := by
    have heq : substBelow k s a =
        (Algebra.ofId k (MvPolynomial (Fin s) k)).comp (MvPolynomial.aeval a) := by
      rw [MvPolynomial.comp_aeval]
      apply MvPolynomial.algHom_ext
      intro i
      rw [substBelow_X, if_pos i.isLt, MvPolynomial.aeval_X, Algebra.ofId_apply,
        MvPolynomial.algebraMap_eq]
    have hinj : Function.Injective (algebraMap k (MvPolynomial (Fin s) k)) :=
      FaithfulSMul.algebraMap_injective k _
    rw [heq]
    ext p
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Algebra.ofId_apply,
      MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : (MvPolynomial.aeval a) p = 0 := hinj (by simpa using h)
      intro x hx
      rw [hx]
      exact h0
    · intro h
      rw [h a rfl, map_zero]
  have hlower : (↑s : ℕ∞) ≤ (MvPolynomial.vanishingIdeal k {a} :
      Ideal (MvPolynomial (Fin s) k)).height := by
    rw [← hker]
    have key : ∀ j ≤ s, (↑j : ℕ∞) ≤ (RingHom.ker (substBelow k j a)).height := by
      intro j
      induction j with
      | zero => intro _; exact bot_le
      | succ m ih =>
        intro hm
        have hms : m < s := by omega
        have h1 : (RingHom.ker (substBelow k m a)).IsPrime := RingHom.ker_isPrime _
        have h2 : (RingHom.ker (substBelow k (m + 1) a)).IsPrime := RingHom.ker_isPrime _
        have hlt : RingHom.ker (substBelow k m a) < RingHom.ker (substBelow k (m + 1) a) :=
          lt_of_le_of_ne (ker_substBelow_antitone k m a)
            (fun heq => X_sub_C_notMem_ker_substBelow k m hms a (heq ▸
              X_sub_C_mem_ker_substBelow_succ k m hms a))
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have him := ih (by omega : m ≤ s)
        calc (↑(m + 1) : ℕ∞) = (↑m : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (substBelow k m a)).height + 1 := by gcongr
          _ ≤ (RingHom.ker (substBelow k (m + 1) a)).height := hstep
    exact key s le_rfl
  have hupper : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height ≤ ↑s := by
    haveI : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).IsMaximal :=
      inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := MvPolynomial.vanishingIdeal k {a})
      (Ideal.IsMaximal.ne_top ‹(MvPolynomial.vanishingIdeal k {a} :
        Ideal (MvPolynomial (Fin s) k)).IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  exact le_antisymm hupper hlower

end Height

section DimensionDrop

variable {A : Type*} [CommRing A]

/-- Quotient by a prime of height one decreases the Krull dimension by at most one. -/
theorem ringKrullDim_quotient_add_one_le_of_height_eq_one [IsNoetherianRing A] [IsDomain A]
    {p : Ideal A} [hp : p.IsPrime] (h1 : p.height = 1) [FiniteRingKrullDim (A ⧸ p)] :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by
  have key : ∀ (M : Ideal (A ⧸ p)), M.IsMaximal → (↑(M.height + 1) : WithBot ℕ∞) ≤ ringKrullDim A := by
    intro M hM
    haveI := hM
    have hcomap : (Ideal.comap (Ideal.Quotient.mk p) M).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hpcomap : p ≤ Ideal.comap (Ideal.Quotient.mk p) M := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
      exact bot_le
    have hmap : (Ideal.comap (Ideal.Quotient.mk p) M).map (Ideal.Quotient.mk p) = M :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
    have h := Ideal.height_map_quotient_add_one_le (p := p)
      (q := Ideal.comap (Ideal.Quotient.mk p) M) hpcomap h1
    rw [hmap] at h
    have h' : (↑(M.height + 1) : WithBot ℕ∞) ≤ ↑((Ideal.comap (Ideal.Quotient.mk p) M).height) := by
      rw [WithBot.coe_le_coe]
      exact h
    exact h'.trans (Ideal.height_le_ringKrullDim_of_ne_top hcomap.ne_top)
  obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := A ⧸ p)
  calc ringKrullDim (A ⧸ p) + 1 = (↑M.height : WithBot ℕ∞) + 1 := by rw [← hMh]
    _ = ↑(M.height + 1) := by rw [WithBot.coe_add]; norm_cast
    _ ≤ ringKrullDim A := key M hMmax

end DimensionDrop

section Hypersurface

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A hypersurface in affine `s`-space has dimension one less than `s`. -/
theorem MvPolynomial.ringKrullDim_quotient_span_singleton {s : ℕ}
    {g : MvPolynomial (Fin s) k} (hg : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime] :
    ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1
      = ringKrullDim (MvPolynomial (Fin s) k) := by
  haveI hBnoeth : IsNoetherianRing (MvPolynomial (Fin s) k) := inferInstance
  have hgu : ¬ IsUnit g := fun h => hgp.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have htop : Ideal.span {g} ≠ ⊤ := hgp.ne_top
  haveI hquo : Nontrivial (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr htop
  have hh : (Ideal.span {g}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg) hgu
  have hmaxB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  haveI hfin : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top
        (by rw [hmaxB]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le (Ideal.span {g}))
  refine le_antisymm (ringKrullDim_quotient_add_one_le_of_height_eq_one hh) ?_
  obtain ⟨m, hmmax, hgm⟩ := Ideal.exists_le_maximal (Ideal.span {g}) htop
  haveI := hmmax
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hmmax
  have hms : m.height = ↑s := by
    rw [ha]
    exact vanishingIdeal_singleton_height k s a
  have hkey : (↑m.height : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by
    haveI : (Ideal.map (Ideal.Quotient.mk (Ideal.span {g})) m).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hgm
    have h1 : m.height ≤ (m.map (Ideal.Quotient.mk (Ideal.span {g}))).height +
        (Ideal.span {g}).spanFinrank :=
      Ideal.height_le_height_add_spanFinrank_of_le hgm
    have h2 : (Ideal.span {g}).spanFinrank ≤ 1 := by
      simpa using Submodule.spanFinrank_span_le_encard ({g} : Set (MvPolynomial (Fin s) k))
    have h4 : (↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
      Ideal.height_le_ringKrullDim_of_isPrime
    have h1' : (↑m.height : WithBot ℕ∞) ≤
        ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := by
      exact_mod_cast h1
    calc (↑m.height : WithBot ℕ∞)
        ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := h1'
      _ ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + 1 := by
          gcongr
          exact_mod_cast h2
      _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by gcongr
  calc ringKrullDim (MvPolynomial (Fin s) k) = (↑s : WithBot ℕ∞) := hmaxB
    _ = (↑m.height : WithBot ℕ∞) := by rw [hms]; norm_num
    _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := hkey

end Hypersurface

section MainAlgebra

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **Hartshorne I.1.8, algebraic form.**  Let `S` be a finitely generated domain over an
algebraically closed field `k`, let `t ∈ S` be nonzero and not a unit, and let `p` be a prime
minimal over `(t)`.  Then `dim S/p = dim S - 1`, i.e. `dim S/p + 1 = dim S`. -/
theorem ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes
    {S : Type*} [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    {t : S} (ht : t ≠ 0) (htu : ¬ IsUnit t) {p : Ideal S} [hp : p.IsPrime]
    (hpm : p ∈ (Ideal.span {t}).minimalPrimes) :
    ringKrullDim (S ⧸ p) + 1 = ringKrullDim S := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have h1 : p.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes ht hpm
  -- Noether normalization
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k S
  let : Algebra (MvPolynomial (Fin s) k) S := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) S = g.toRingHom := RingHom.algebraMap_toAlgebra _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) S := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hginj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) S := by
    have : Module.Finite (MvPolynomial (Fin s) k) S := hgfin
    infer_instance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) k) S := inferInstance
  have hB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hS : ringKrullDim S = ↑s := by
    rw [ringKrullDim_eq_of_integral_injective (B := MvPolynomial (Fin s) k), hB]
  -- upper bound
  haveI : FiniteRingKrullDim (S ⧸ p) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top (by rw [hS]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le p)
  have hupper : ringKrullDim (S ⧸ p) + 1 ≤ ringKrullDim S :=
    ringKrullDim_quotient_add_one_le_of_height_eq_one h1
  -- the contraction `q` of `p` to the polynomial ring
  set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq
  haveI hqprime : q.IsPrime := Ideal.IsPrime.under _ p
  have hq1 : q.height = 1 := by
    rw [hq, ← Ideal.height_eq_height_under_of_isIntegral (B := MvPolynomial (Fin s) k) (P := p), h1]
  -- `q` is principal
  have hqne : q ≠ ⊥ := fun h => by
    rw [h] at hq1
    exact absurd hq1 (by simp)
  obtain ⟨h, hh⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq1
  have hqspan : q = Ideal.span {h} := hh
  have hhne : h ≠ 0 := by
    rintro rfl
    exact hqne (by rw [hqspan, Ideal.span_singleton_eq_bot])
  haveI hqspanprime : (Ideal.span {h}).IsPrime := hqspan ▸ hqprime
  have hgen : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = ringKrullDim (MvPolynomial (Fin s) k) := by
    rw [hqspan]
    exact MvPolynomial.ringKrullDim_quotient_span_singleton k hhne
  -- lower bound via chain lifting
  haveI : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ q) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · have h2 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = (↑s : WithBot ℕ∞) := by
        rw [hgen, hB]
      intro htop'
      rw [htop'] at h2
      exact absurd h2.symm (by
        intro h; exact ENat.natCast_ne_top s (WithBot.coe_injective h))
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · exfalso
      rw [hs0] at hS
      have hp0 : (↑p.height : WithBot ℕ∞) ≤ (↑(0 : ℕ) : WithBot ℕ∞) := by
        rw [← hS]
        exact Ideal.height_le_ringKrullDim_of_isPrime
      have hp0' : p.height ≤ (0 : ℕ∞) := by simpa using hp0
      rw [h1] at hp0'
      simp at hp0'
    · exact hs
  have hs1 : (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := by
    have h3 : s = (s - 1) + 1 := (Nat.sub_add_cancel hspos).symm
    rw [h3]
    push_cast
    ring
  have hsm1 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) = (↑(s - 1) : WithBot ℕ∞) := by
    have h2 := hgen
    rw [hB] at h2
    rw [hs1] at h2
    exact ENat.WithBot.add_one_cancel.mp h2
  have hlow : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) ≤ ringKrullDim (S ⧸ p) := by
    rw [hsm1]
    haveI hLO : p.LiesOver q := ⟨hq⟩
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : FaithfulSMul (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : Algebra.HasGoingUp (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin s) k ⧸ q)
    haveI := hMmax
    obtain ⟨l, hl, hlen⟩ := Ideal.exists_ltSeries_length_eq_height M
    have hMheight : M.height = (↑(s - 1) : ℕ∞) := by
      have h : (↑M.height : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by
        rw [hMh, hsm1]
      exact WithBot.coe_injective h
    have hlen' : l.length = s - 1 := by
      have h : (↑l.length : ℕ∞) = ↑(s - 1) := by rw [hlen, hMheight]
      exact Nat.cast_injective h
    have hhead : (RelSeries.head l).asIdeal.IsPrime := (RelSeries.head l).isPrime
    obtain ⟨Q, -, hQprime, hQover⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := MvPolynomial (Fin s) k ⧸ q)
        (S := S ⧸ p) ((RelSeries.head l).asIdeal) (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
    haveI := hQprime
    haveI hQlo : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQover.symm⟩
    obtain ⟨L, hLlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    have hL : L.length = s - 1 := by rw [hLlen, hlen']
    have hL' : (↑L.length : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by rw [hL]
    calc (↑(s - 1) : WithBot ℕ∞) = (↑L.length : WithBot ℕ∞) := hL'.symm
      _ ≤ ↑(⨆ p : LTSeries (PrimeSpectrum (S ⧸ p)), (↑p.length : ℕ∞)) := by
          exact WithBot.coe_le_coe.mpr
            (le_iSup (fun p : LTSeries (PrimeSpectrum (S ⧸ p)) => (↑p.length : ℕ∞)) L)
      _ = ringKrullDim (S ⧸ p) := by
          rw [← Order.krullDim_eq_iSup_length]
          rfl
  refine le_antisymm hupper ?_
  rw [hS]
  calc (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := hs1
    _ ≤ ringKrullDim (S ⧸ p) + 1 := by
        have h2 := hlow
        rw [hsm1] at h2
        exact add_le_add h2 (le_refl (1 : WithBot ℕ∞))

end MainAlgebra

section Zariski

variable (k : Type*) [Field k] (n : ℕ)

/-- The zero loci of the ideals of `k[X_1,…,X_n]`, i.e. the closed sets of the Zariski topology
on affine `n`-space `k^n`. -/
def zarClosed : Set (Set (Fin n → k)) :=
  {s | ∃ I : Ideal (MvPolynomial (Fin n) k), s = MvPolynomial.zeroLocus k I}

lemma zarClosed_empty : (∅ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊤, by simp⟩

lemma zarClosed_univ : (Set.univ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊥, by rw [MvPolynomial.zeroLocus_bot]; exact rfl⟩

lemma zeroLocus_mul (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k (I * J) =
      MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra h
    simp only [Set.mem_union, not_or] at h
    obtain ⟨h1, h2⟩ := h
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at h1 h2
    obtain ⟨p, hp, hp0⟩ := h1
    obtain ⟨q, hq, hq0⟩ := h2
    have hpq : (MvPolynomial.aeval x) (p * q) = 0 := hx (p * q) (Ideal.mul_mem_mul hp hq)
    rw [map_mul] at hpq
    rcases mul_eq_zero.mp hpq with h | h
    · exact hp0 h
    · exact hq0 h
  · intro x hx
    rcases hx with h | h
    · exact fun p hp => h p (Ideal.mul_le_left hp)
    · exact fun p hp => h p (Ideal.mul_le_right hp)

lemma zarClosed_sInter {A : Set (Set (Fin n → k))} (hA : A ⊆ zarClosed k n) :
    ⋂₀ A ∈ zarClosed k n := by
  refine ⟨MvPolynomial.vanishingIdeal k (⋂₀ A),
    le_antisymm (MvPolynomial.zeroLocus_vanishingIdeal_le _) ?_⟩
  intro x hx s hs
  obtain ⟨I, hI⟩ := hA hs
  rw [hI]
  intro p hp
  exact hx p fun y hy => by
    have hy' : y ∈ MvPolynomial.zeroLocus k I := hI ▸ (hy s hs)
    exact hy' p hp

lemma zarClosed_union {s t : Set (Fin n → k)} (hs : s ∈ zarClosed k n)
    (ht : t ∈ zarClosed k n) : s ∪ t ∈ zarClosed k n := by
  obtain ⟨I, rfl⟩ := hs
  obtain ⟨J, rfl⟩ := ht
  exact ⟨I * J, (zeroLocus_mul k n I J).symm⟩

/-- The Zariski topology on affine `n`-space over `k`. -/
noncomputable instance : TopologicalSpace (Fin n → k) :=
  TopologicalSpace.ofClosed (zarClosed k n) (zarClosed_empty k n)
    (fun A hA => zarClosed_sInter k n hA) (fun a ha b hb => zarClosed_union k n ha hb)

lemma isOpen_iff_zarClosed {s : Set (Fin n → k)} : IsOpen s ↔ sᶜ ∈ zarClosed k n :=
  Iff.rfl

lemma isClosed_iff_zarClosed {s : Set (Fin n → k)} : IsClosed s ↔ s ∈ zarClosed k n := by
  rw [← isOpen_compl_iff, isOpen_iff_zarClosed, compl_compl]

lemma isClosed_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    IsClosed (MvPolynomial.zeroLocus k I) := by
  rw [isClosed_iff_zarClosed]
  exact ⟨I, rfl⟩

end Zariski

section Dictionary

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

lemma vanishingIdeal_singleton_mem_zeroLocus_iff (x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    p ∈ MvPolynomial.vanishingIdeal k {x} ↔ (MvPolynomial.aeval x) p = 0 :=
  MvPolynomial.mem_vanishingIdeal_singleton_iff x p

/-- The zero locus of a prime ideal is an irreducible closed set. -/
lemma zeroLocus_irreducible {P : Ideal (MvPolynomial (Fin n) k)} (hP : P.IsPrime) :
    IsIrreducible (MvPolynomial.zeroLocus k P) := by
  haveI := hP
  have hIV : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) = P :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
  constructor
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) P
    rw [hempty, MvPolynomial.vanishingIdeal_empty] at h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ P := by
      rw [← hP.radical, ← h]
      exact Submodule.mem_top
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z1 z2 hz1 hz2 hsub
    rw [isClosed_iff_zarClosed] at hz1 hz2
    obtain ⟨I, hI⟩ := hz1
    obtain ⟨J, hJ⟩ := hz2
    have hIJ : I * J ≤ P := by
      rw [← hIV, ← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, zeroLocus_mul]
      rw [hI, hJ] at hsub
      exact hsub
    rcases (Ideal.IsPrime.mul_le hP).mp hIJ with h | h
    · left
      rw [hI]
      exact MvPolynomial.zeroLocus_anti_mono h
    · right
      rw [hJ]
      exact MvPolynomial.zeroLocus_anti_mono h

/-- The vanishing ideal of an irreducible closed set is prime. -/
lemma vanishingIdeal_isPrime {Z : Set (Fin n → k)} (hZc : IsClosed Z) (hZi : IsIrreducible Z) :
    (MvPolynomial.vanishingIdeal k Z).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ MvPolynomial.vanishingIdeal k Z := h ▸ Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have hz1 : ((1 : MvPolynomial (Fin n) k) : MvPolynomial (Fin n) k) ∈
          MvPolynomial.vanishingIdeal k Z := h1
      have := (MvPolynomial.mem_vanishingIdeal_iff).mp hz1 z hz
      simp at this
    rw [hempty] at hZi
    exact hZi.1.ne_empty rfl
  · intro x y hxy
    by_contra h
    simp only [not_or] at h
    obtain ⟨hx, hy⟩ := h
    have hcover : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {x}) ∪
        MvPolynomial.zeroLocus k (Ideal.span {y}) := by
      intro z hz
      have hxyz : (MvPolynomial.aeval z) (x * y) = 0 := hxy z hz
      rw [map_mul] at hxyz
      rcases mul_eq_zero.mp hxyz with h' | h'
      · left
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
      · right
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hZi.2) _ _
      (isClosed_zeroLocus k n (Ideal.span {x})) (isClosed_zeroLocus k n (Ideal.span {y})) hcover
      with h' | h'
    · exact hx fun z hz => h' hz x (Ideal.mem_span_singleton_self x)
    · exact hy fun z hz => h' hz y (Ideal.mem_span_singleton_self y)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_radical (I : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
  refine le_antisymm (MvPolynomial.zeroLocus_anti_mono Ideal.le_radical) ?_
  calc MvPolynomial.zeroLocus k I ⊆
        MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) :=
        MvPolynomial.zeroLocus_vanishingIdeal_le _
    _ ⊆ MvPolynomial.zeroLocus k I.radical :=
        MvPolynomial.zeroLocus_anti_mono (MvPolynomial.radical_le_vanishingIdeal_zeroLocus I)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_vanishingIdeal_of_isClosed {Z : Set (Fin n → k)} (hZ : IsClosed Z) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z) = Z := by
  rw [isClosed_iff_zarClosed] at hZ
  obtain ⟨I, rfl⟩ := hZ
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, zeroLocus_radical]

end Dictionary

section Dimension

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- The dimension of an affine algebraic set, as the supremum of the lengths of chains of
irreducible closed subsets (Hartshorne I.1). -/
noncomputable def varietyDim (Y : Set (Fin n → k)) : WithBot ℕ∞ :=
  Order.krullDim {Z : Set (Fin n → k) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z}

/-- The dimension of the affine algebraic set defined by an ideal equals the Krull dimension of the
coordinate ring. -/
theorem varietyDim_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    varietyDim k n (MvPolynomial.zeroLocus k I) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
  have key : ∀ (Z : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z}), I ≤ MvPolynomial.vanishingIdeal k Z.1 := by
    rintro ⟨Z, hZ, -, -⟩
    rw [← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
    exact hZ
  set F : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧
      IsClosed Z} → (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    fun Z => OrderDual.toDual
      ⟨⟨MvPolynomial.vanishingIdeal k Z.1, vanishingIdeal_isPrime k n Z.2.2.2 Z.2.2.1⟩, key Z⟩ with hF
  set G : (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ →
      {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧ IsClosed Z} :=
    fun p => ⟨MvPolynomial.zeroLocus k (OrderDual.ofDual p).1.asIdeal,
      ⟨fun x hx => by
        rw [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
        exact fun q hq => hx q ((OrderDual.ofDual p).2 hq),
       zeroLocus_irreducible k n (OrderDual.ofDual p).1.isPrime,
       isClosed_zeroLocus k n _⟩⟩ with hG
  have hFinj : Function.Injective F := by
    intro Z1 Z2 heq
    have h1 : MvPolynomial.vanishingIdeal k Z1.1 = MvPolynomial.vanishingIdeal k Z2.1 := by
      have := congrArg (fun x => (OrderDual.ofDual x : ↥(PrimeSpectrum.zeroLocus
        (I : Set (MvPolynomial (Fin n) k)))).1.asIdeal) heq
      simpa [hF] using this
    have hZ1 := zeroLocus_vanishingIdeal_of_isClosed k n Z1.2.2.2
    have hZ2 := zeroLocus_vanishingIdeal_of_isClosed k n Z2.2.2.2
    exact Subtype.ext (by rw [← hZ1, ← hZ2, h1])
  have hFmono : Monotone F := by
    intro Z1 Z2 hle
    simp only [hF, OrderDual.toDual_le_toDual]
    exact Subtype.mk_le_mk.mpr
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (MvPolynomial.vanishingIdeal_anti_mono hle))
  have hGinj : Function.Injective G := by
    intro p1 p2 heq
    have h1 : MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal =
        MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal := by
      have := congrArg Subtype.val heq
      simpa [hG] using this
    have h2 : (OrderDual.ofDual p1).1.asIdeal = (OrderDual.ofDual p2).1.asIdeal := by
      have e1 : (OrderDual.ofDual p1).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      have e2 : (OrderDual.ofDual p2).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      rw [e1, e2, h1]
    have : (OrderDual.ofDual p1).1 = (OrderDual.ofDual p2).1 := PrimeSpectrum.ext h2
    have : OrderDual.ofDual p1 = OrderDual.ofDual p2 := Subtype.ext this
    exact OrderDual.ofDual.injective this
  have hGmono : Monotone G := by
    intro p1 p2 hle
    have hlt : OrderDual.ofDual p2 ≤ OrderDual.ofDual p1 := hle
    have h2 : (OrderDual.ofDual p2).1.asIdeal ≤ (OrderDual.ofDual p1).1.asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt
    exact MvPolynomial.zeroLocus_anti_mono h2
  have hmain : Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} ≤
      Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    Order.krullDim_le_of_strictMono F (hFmono.strictMono_of_injective hFinj)
  have hmain2 : Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ ≤
      Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
        IsIrreducible Z ∧ IsClosed Z} :=
    Order.krullDim_le_of_strictMono G (hGmono.strictMono_of_injective hGinj)
  have hiso : Order.krullDim ↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  show Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} = ringKrullDim (MvPolynomial (Fin n) k ⧸ I)
  rw [le_antisymm hmain hmain2, Order.krullDim_orderDual]
  exact hiso

end Dimension

section Main

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- **Hartshorne, Algebraic Geometry, Exercise I.1.8.**  Let `Y` be an irreducible affine variety
of dimension `r` in `A^n` and let `H = V(f)` be a hypersurface, with `Y ⊄ H`.  Then every
irreducible component `Z` of `Y ∩ H` has dimension `r - 1`; equivalently `dim Z + 1 = dim Y`. -/
theorem hartshorne_exercise_I_1_8
    (Y : Set (Fin n → k)) (f : MvPolynomial (Fin n) k)
    (hYc : IsClosed Y) (hYi : IsIrreducible Y) (hf : f ≠ 0)
    (hne : ∃ y ∈ Y, (MvPolynomial.aeval y) f ≠ 0)
    (Z : Set (Fin n → k)) (hZY : Z ⊆ Y)
    (hZf : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}))
    (hZi : IsIrreducible Z) (hZc : IsClosed Z)
    (hZmax : ∀ W : Set (Fin n → k), W ⊆ Y → W ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) →
      IsIrreducible W → IsClosed W → Z ⊆ W → W ⊆ Z) :
    varietyDim k n Z + 1 = varietyDim k n Y := by
  set IY := MvPolynomial.vanishingIdeal k Y with hIY
  set q := MvPolynomial.vanishingIdeal k Z with hq
  haveI hYprime : IY.IsPrime := vanishingIdeal_isPrime k n hYc hYi
  haveI hqprime : q.IsPrime := vanishingIdeal_isPrime k n hZc hZi
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ IY) := Ideal.Quotient.isDomain _
  have hIYq : IY ≤ q := MvPolynomial.vanishingIdeal_anti_mono hZY
  have hfq : f ∈ q := fun z hz => hZf hz f (Ideal.mem_span_singleton_self f)
  have hYeq : MvPolynomial.zeroLocus k IY = Y := zeroLocus_vanishingIdeal_of_isClosed k n hYc
  -- ## `q` is minimal over `IY ⊔ (f)`
  have hmin : q ∈ (IY ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqprime, sup_le hIYq ((Ideal.span_singleton_le_iff_mem _).mpr hfq)⟩, ?_⟩
    rintro q' ⟨hq'prime, hq'le⟩ hq'q
    haveI := hq'prime
    have h1 : IY ≤ q' := le_trans le_sup_left hq'le
    have hspanle : (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)) ≤ IY ⊔ Ideal.span {f} :=
      le_sup_of_le_right (le_refl (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)))
    have hWY : MvPolynomial.zeroLocus k q' ⊆ Y := by
      rw [← hYeq]
      exact MvPolynomial.zeroLocus_anti_mono h1
    have hWf : MvPolynomial.zeroLocus k q' ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) :=
      MvPolynomial.zeroLocus_anti_mono (le_trans hspanle hq'le)
    have hWirr : IsIrreducible (MvPolynomial.zeroLocus k q') := zeroLocus_irreducible k n hq'prime
    have hWc : IsClosed (MvPolynomial.zeroLocus k q') := isClosed_zeroLocus k n _
    have hZW : Z ⊆ MvPolynomial.zeroLocus k q' := by
      rw [← zeroLocus_vanishingIdeal_of_isClosed k n hZc]
      exact MvPolynomial.zeroLocus_anti_mono hq'q
    have hWZ : MvPolynomial.zeroLocus k q' ⊆ Z := hZmax _ hWY hWf hWirr hWc hZW
    have h4 : q ≤ q' := by
      have h5 : MvPolynomial.vanishingIdeal k Z ≤ MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k q') :=
        MvPolynomial.vanishingIdeal_anti_mono (k := k) (K := k) hWZ
      have h6 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k q') = q' :=
        MvPolynomial.IsPrime.vanishingIdeal_zeroLocus q'
      rw [h6, ← hq] at h5
      exact h5
    exact h4
  -- ## pass to the coordinate ring of `Y`
  set t : MvPolynomial (Fin n) k ⧸ IY := Ideal.Quotient.mk IY f with ht
  set P : Ideal (MvPolynomial (Fin n) k ⧸ IY) := q.map (Ideal.Quotient.mk IY) with hP
  haveI hPprime : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIYq
  have hcomap : Ideal.comap (Ideal.Quotient.mk IY) P = q := by
    rw [hP, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hb : Ideal.comap (Ideal.Quotient.mk IY) (⊥ : Ideal (MvPolynomial (Fin n) k ⧸ IY)) = IY := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hb, sup_of_le_left hIYq]
  have ht0 : t ≠ 0 := by
    intro h0
    have hmem : f ∈ IY := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← ht]
      exact h0
    obtain ⟨y, hy, hfy⟩ := hne
    exact hfy (mem_vanishingIdeal_iff.mp hmem y hy)
  have htP : t ∈ P := by
    rw [ht, hP]
    exact Ideal.mem_map_of_mem _ hfq
  have htunit : ¬ IsUnit t := by
    intro hunit
    have hspan : Ideal.span {t} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr htP
    have hPtop : P = ⊤ := top_le_iff.mp (hspan ▸ hle)
    have hqtop : q = ⊤ := by
      have h1 : Ideal.comap (Ideal.Quotient.mk IY) P = ⊤ := by rw [hPtop]; simp
      rw [hcomap] at h1
      exact h1
    have h1q : (1 : MvPolynomial (Fin n) k) ∈ q := by rw [hqtop]; exact Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have h2 := (MvPolynomial.mem_vanishingIdeal_iff.mp h1q) z hz
      simp at h2
    exact hZi.1.ne_empty hempty
  have hPmin : P ∈ (Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨hPprime, (Ideal.span_singleton_le_iff_mem _).mpr htP⟩, ?_⟩
    rintro P' ⟨hP'prime, hP'le⟩ hP'P
    haveI := hP'prime
    have hq'le : (IY ⊔ Ideal.span {f}) ≤ Ideal.comap (Ideal.Quotient.mk IY) P' := by
      refine sup_le ?_ ?_
      · exact Ideal.le_comap_of_map_le (by
          rw [Ideal.map_quotient_self]
          exact bot_le)
      · refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
        have h8 : t ∈ P' := hP'le (Ideal.mem_span_singleton_self t)
        rwa [ht] at h8
    have hq'q : Ideal.comap (Ideal.Quotient.mk IY) P' ≤ q := by
      rw [← hcomap]
      exact Ideal.comap_mono hP'P
    have hqle : q ≤ Ideal.comap (Ideal.Quotient.mk IY) P' :=
      hmin.2 ⟨Ideal.IsPrime.comap (Ideal.Quotient.mk IY), hq'le⟩ hq'q
    have hfin : P ≤ P' := by
      have h7 : P ≤ (Ideal.comap (Ideal.Quotient.mk IY) P').map (Ideal.Quotient.mk IY) := by
        rw [hP]
        exact Ideal.map_mono hqle
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h7
    exact hfin
  -- ## the algebraic input
  have hmain := ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes k ht0 htunit hPmin
  -- ## the two dimensions
  have hZq : MvPolynomial.zeroLocus k q = Z := zeroLocus_vanishingIdeal_of_isClosed k n hZc
  have h1 : varietyDim k n Z = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) := by
    rw [← hZq]
    exact varietyDim_zeroLocus k n q
  have h2 : varietyDim k n Y = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := by
    rw [← hYeq]
    exact varietyDim_zeroLocus k n IY
  have hiso : ringKrullDim (MvPolynomial (Fin n) k ⧸ q) =
      ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) := by
    have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) = q := by
      ext x
      show (Ideal.Quotient.mk P) ((Ideal.Quotient.mk IY) x) = 0 ↔ x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hcomap, Ideal.mem_comap]
    have hiso' : (MvPolynomial (Fin n) k ⧸ q) ≃+* ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
    exact ringKrullDim_eq_of_ringEquiv hiso'
  calc varietyDim k n Z + 1 = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) + 1 := by rw [h1]
    _ = ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) + 1 := by rw [hiso]
    _ = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := hmain
    _ = varietyDim k n Y := h2.symm

end Main

/-! ## Part 2: homogeneous components and the strong vanishing ideal -/

section HomogScaling

variable {σ : Type*} {k : Type*} [Field k]

/-- Evaluating a polynomial at the point `c • a` obtained by scaling `a`. -/
theorem eval_smul_eq_sum_homogeneousComponent (f : MvPolynomial σ k) (c : k) (a : σ → k) :
    MvPolynomial.eval (fun i => c * a i) f =
      ∑ d ∈ Finset.range (f.totalDegree + 1),
        c ^ d * MvPolynomial.eval a (MvPolynomial.homogeneousComponent d f) := by
  have hL : MvPolynomial.eval (fun i => c * a i) f =
      ∑ m ∈ f.support, c ^ m.degree * (MvPolynomial.coeff m f * m.prod fun i e => a i ^ e) := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    ring
  rw [hL, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (f.totalDegree + 1))
    (g := fun m : σ →₀ ℕ => m.degree)
    (f := fun m => c ^ m.degree * (MvPolynomial.coeff m f * m.prod fun i e => a i ^ e))
    (fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (MvPolynomial.le_totalDegree hm)))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [MvPolynomial.eval_monomial, hm.2]

/-- If a polynomial vanishes at every nonzero scalar multiple of a vector `a`, then each of its
homogeneous components vanishes at `a`. -/
theorem homogeneousComponent_eval_eq_zero [Infinite k] {f : MvPolynomial σ k} {a : σ → k}
    (h : ∀ c : k, c ≠ 0 → MvPolynomial.eval (fun i => c * a i) f = 0) (d : ℕ) :
    MvPolynomial.eval a (MvPolynomial.homogeneousComponent d f) = 0 := by
  classical
  have hcoeff : ∀ (s : Finset ℕ) (y : ℕ → k) (d : ℕ),
      Polynomial.coeff (∑ e ∈ s, Polynomial.C (y e) * Polynomial.X ^ e) d =
        if d ∈ s then y d else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro y d
        simp
    | insert a s ha ih =>
        intro y d
        rw [Finset.sum_insert ha, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul_X_pow]
        by_cases hda : d = a
        · subst hda
          simp [ha]
        · simp [hda, Finset.mem_insert]
  have hzero : ∀ c : k, c ≠ 0 →
      Polynomial.eval c (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = 0 := by
    intro c hc
    rw [Polynomial.eval_finsetSum]
    have hterm : ∀ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.eval c (Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) =
          c ^ e * MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f) := by
      intro e _
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_comm _ _
    rw [Finset.sum_congr rfl hterm, ← eval_smul_eq_sum_homogeneousComponent f c a]
    exact h c hc
  have hinf : ({x : k | Polynomial.eval x (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = Polynomial.eval x (0 : Polynomial k)}).Infinite := by
    refine Set.Infinite.mono ?_ (Set.Finite.infinite_compl (Set.finite_singleton (0 : k)))
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    simpa using hzero c hc
  have hP0 : (∑ e ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) *
          Polynomial.X ^ e) = 0 :=
    Polynomial.eq_of_infinite_eval_eq _ 0 hinf
  have hd := hcoeff (Finset.range (f.totalDegree + 1))
    (fun e => MvPolynomial.eval a (MvPolynomial.homogeneousComponent e f)) d
  rw [hP0, Polynomial.coeff_zero] at hd
  by_cases hle : d ≤ f.totalDegree
  · rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))] at hd
    exact hd.symm
  · push Not at hle
    rw [if_neg (by rw [Finset.mem_range]; omega)] at hd
    have hzero' : MvPolynomial.homogeneousComponent d f = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero (φ := f) (n := d) (by omega)
    simp [hzero']

end HomogScaling

/-! ### The strong vanishing ideal of a projective set -/

section VanishOn

variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

/-- The ideal of polynomials vanishing at every nonzero vector whose line lies in `Y`. -/
noncomputable def vanishOnIdeal (Y : Set (Proj k n)) : Ideal (MvPolynomial (Fin (n + 1)) k) where
  carrier := {f | ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk v hv ∈ Y → MvPolynomial.eval v f = 0}
  add_mem' := by
    intro a b ha hb v hv hmem
    simp only [map_add, ha v hv hmem, hb v hv hmem, add_zero]
  zero_mem' := by
    intro v hv hmem
    simp
  smul_mem' := by
    intro c a ha v hv hmem
    simp only [smul_eq_mul, MvPolynomial.eval_mul, ha v hv hmem, mul_zero]

theorem mem_vanishOnIdeal_iff {Y : Set (Proj k n)} {f : MvPolynomial (Fin (n + 1)) k} :
    f ∈ (vanishOnIdeal Y : Set (MvPolynomial (Fin (n + 1)) k)) ↔
      ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk v hv ∈ Y → MvPolynomial.eval v f = 0 :=
  Iff.rfl

/-- `mk` is invariant under nonzero scaling. -/
theorem mk_smul {c : k} (hc : c ≠ 0) {v : Fin (n + 1) → k} (hv : v ≠ 0) (hcv : c • v ≠ 0) :
    mk (c • v) hcv = mk v hv := by
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc, rfl⟩

/-- The generators of the vanishing ideal belong to the strong vanishing ideal. -/
theorem vanishingIdeal_le_vanishOnIdeal (Y : Set (Proj k n)) :
    vanishingIdeal Y ≤ vanishOnIdeal Y := by
  rw [vanishingIdeal, Ideal.span_le]
  rintro f ⟨d, hf, hvan⟩
  rw [mem_vanishOnIdeal_iff]
  intro v hv hmem
  exact (isZeroAt_mk_iff hf hv).1 (hvan _ hmem)

/-- Homogeneous components of a polynomial vanishing on `Y` vanish on `Y`. -/
theorem homogeneousComponent_mem_vanishOnIdeal [Infinite k] {Y : Set (Proj k n)}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f ∈ vanishOnIdeal Y) (d : ℕ) :
    MvPolynomial.homogeneousComponent d f ∈ vanishOnIdeal Y := by
  refine mem_vanishOnIdeal_iff.mpr ?_
  intro v hv hmem
  refine homogeneousComponent_eval_eq_zero (fun c hc => ?_) d
  have hscale : (fun i => c * v i) = c • v := rfl
  rw [hscale]
  have hmem' : mk (c • v) (smul_ne_zero hc hv) ∈ Y := by
    rw [mk_smul hc hv]
    exact hmem
  exact (mem_vanishOnIdeal_iff.mp hf) _ (smul_ne_zero hc hv) hmem'

/-- The strong vanishing ideal is generated by homogeneous polynomials. -/
theorem vanishOnIdeal_le_vanishingIdeal [Infinite k] (Y : Set (Proj k n)) :
    vanishOnIdeal Y ≤ vanishingIdeal Y := by
  intro f hf
  have hgen : ∀ e : ℕ, MvPolynomial.homogeneousComponent e f ∈ vanishingIdeal Y := by
    intro e
    have hh : (MvPolynomial.homogeneousComponent e f).IsHomogeneous e :=
      MvPolynomial.homogeneousComponent_isHomogeneous e f
    have hv : ∀ x ∈ Y, IsZeroAt (MvPolynomial.homogeneousComponent e f) x := by
      intro x hx
      rw [IsZeroAt]
      exact homogeneousComponent_mem_vanishOnIdeal hf e _ x.rep_nonzero (by simpa using hx)
    exact subset_vanishingIdeal (d := e) hh hv
  have hsum : (∑ e ∈ Finset.range (f.totalDegree + 1),
      MvPolynomial.homogeneousComponent e f) = f := MvPolynomial.sum_homogeneousComponent f
  rw [← hsum]
  exact Ideal.sum_mem _ fun e _ => hgen e

theorem vanishOnIdeal_eq_vanishingIdeal [Infinite k] (Y : Set (Proj k n)) :
    vanishOnIdeal Y = vanishingIdeal Y :=
  le_antisymm (vanishOnIdeal_le_vanishingIdeal Y) (vanishingIdeal_le_vanishOnIdeal Y)

end Proj

end VanishOn

/-! ### Primeness of the vanishing ideal of an irreducible closed set -/

section ConeDictionary

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

namespace Proj

theorem vanishOnIdeal_ne_top [Infinite k] {Y : Set (Proj k n)} (hY : Y.Nonempty) :
    vanishOnIdeal Y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hY
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  intro htop
  have hmem : MvPolynomial.X j ∈ vanishOnIdeal Y := by rw [htop]; exact Submodule.mem_top
  have := (mem_vanishOnIdeal_iff.mp hmem) x.rep x.rep_nonzero (by simpa using hx)
  rw [MvPolynomial.eval_X] at this
  exact hj this

/-- The vanishing ideal of an irreducible closed set is prime. -/
theorem vanishOnIdeal_isPrime [Infinite k] {Y : Set (Proj k n)} (hYi : IsIrreducible Y) :
    (vanishOnIdeal Y).IsPrime := by
  have hhom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (vanishOnIdeal Y) := by
    rw [vanishOnIdeal_eq_vanishingIdeal Y]
    exact vanishingIdeal_isHomogeneous Y
  rw [Ideal.IsHomogeneous.isPrime_iff hhom]
  refine ⟨vanishOnIdeal_ne_top hYi.1, ?_⟩
  intro f g hf hg hfg
  obtain ⟨df, hdf⟩ := hf
  obtain ⟨dg, hdg⟩ := hg
  have hclosed_f : IsClosed {x : Proj k n | IsZeroAt f x} := by
    rw [isClosed_iff]
    exact ⟨{⟨f, df, hdf⟩}, by
      ext x
      exact ⟨fun h => h _ rfl, fun h y hy => by rw [Set.mem_singleton_iff.mp hy]; exact h⟩⟩
  have hclosed_g : IsClosed {x : Proj k n | IsZeroAt g x} := by
    rw [isClosed_iff]
    exact ⟨{⟨g, dg, hdg⟩}, by
      ext x
      exact ⟨fun h => h _ rfl, fun h y hy => by rw [Set.mem_singleton_iff.mp hy]; exact h⟩⟩
  have hcover : Y ⊆ {x : Proj k n | IsZeroAt f x} ∪ {x : Proj k n | IsZeroAt g x} := by
    intro x hx
    have h0 : MvPolynomial.eval x.rep (f * g) = 0 :=
      mem_vanishOnIdeal_iff.mp hfg _ x.rep_nonzero (by simpa using hx)
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp hYi.2)
    _ _ hclosed_f hclosed_g hcover
  rcases hsplit with hYf | hYg
  · refine Or.inl (mem_vanishOnIdeal_iff.mpr ?_)
    intro v hv hmem
    exact (isZeroAt_mk_iff hdf hv).1 (hYf hmem)
  · refine Or.inr (mem_vanishOnIdeal_iff.mpr ?_)
    intro v hv hmem
    exact (isZeroAt_mk_iff hdg hv).1 (hYg hmem)

/-- The vanishing ideal of an irreducible closed set is prime. -/
theorem vanishingIdeal_isPrime_of_isIrreducible [Infinite k] {Y : Set (Proj k n)}
    (hYi : IsIrreducible Y) : (vanishingIdeal Y).IsPrime := by
  rw [← vanishOnIdeal_eq_vanishingIdeal Y]
  exact vanishOnIdeal_isPrime hYi

end Proj

end ConeDictionary

/-! ### Basic geometry of the cone -/

section ConeGeom

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem cone_empty : cone (∅ : Set (Proj k n)) = {0} := by
  ext v
  simp [cone]

theorem cone_union (A B : Set (Proj k n)) : cone (A ∪ B) = cone A ∪ cone B := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem | hmem⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨hv, hmem⟩)
    · exact Or.inr (Or.inr ⟨hv, hmem⟩)
  · rintro (h | h)
    · rcases h with rfl | ⟨hv, hm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hv, Or.inl hm⟩
    · rcases h with rfl | ⟨hv, hm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hv, Or.inr hm⟩

theorem cone_mono {A B : Set (Proj k n)} (h : A ⊆ B) : cone A ⊆ cone B := by
  rintro v (rfl | ⟨hv, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨hv, h hm⟩

theorem cone_univ : cone (Set.univ : Set (Proj k n)) = Set.univ := by
  ext v
  simp only [cone, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  by_cases hv : v = 0
  · exact Or.inl hv
  · exact Or.inr ⟨hv, trivial⟩

/-- The cone over a closed set is closed. -/
theorem isClosed_cone [Infinite k] {A : Set (Proj k n)} (hA : IsClosed A) :
    IsClosed (cone A) := by
  rcases Set.eq_empty_or_nonempty A with rfl | hne
  · rw [cone_empty]
    have hz : ({0} : Set (Fin (n + 1) → k)) =
        MvPolynomial.zeroLocus k (Ideal.span (Set.range (fun i : Fin (n + 1) =>
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)))) := by
      ext v
      rw [Set.mem_singleton_iff, MvPolynomial.mem_zeroLocus_iff]
      constructor
      · rintro rfl
        have hle : Ideal.span (Set.range (fun i : Fin (n + 1) =>
            (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)))
            ≤ RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          rintro q ⟨i, rfl⟩
          simp
        intro p hp
        exact hle hp
      · intro h
        funext i
        have hx := h (MvPolynomial.X i) (Ideal.subset_span ⟨i, rfl⟩)
        rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X] at hx
        exact hx
    rw [hz]
    exact isClosed_zeroLocus k (n + 1) _
  · rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed A).mpr hA) hne]
    exact isClosed_zeroLocus k (n + 1) (vanishingIdeal A)

/-- Cone over an irreducible nonempty closed set is irreducible. -/
theorem isIrreducible_cone [Infinite k] {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) : IsIrreducible (cone Y) := by
  have hp : (vanishingIdeal Y).IsPrime := vanishingIdeal_isPrime_of_isIrreducible hYi
  rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed Y).mpr hYc) hYi.1]
  exact zeroLocus_irreducible k (n + 1) hp

/-- The cone is irreducible iff the projective set is irreducible (for nonempty closed sets). -/
theorem isIrreducible_cone_iff [Infinite k] {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hne : Y.Nonempty) : IsIrreducible (cone Y) ↔ IsIrreducible Y := by
  refine ⟨?_, isIrreducible_cone hYc⟩
  intro hcone
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have hcover : cone Y ⊆ cone A ∪ cone B := by
    rw [← cone_union]
    exact cone_mono hsub
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp hcone.2)
    (cone A) (cone B) (isClosed_cone hA) (isClosed_cone hB) hcover
  rcases hsplit with h | h
  · refine Or.inl ?_
    intro x hx
    have hx' : x.rep ∈ cone A := h (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm
  · refine Or.inr ?_
    intro x hx
    have hx' : x.rep ∈ cone B := h (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm

end Proj

end ConeGeom

/-! ## Part 3: finite irreducible decompositions in noetherian topological spaces
(from the accepted Hartshorne I.2.5 infrastructure, model independent) -/

/-! ## 5. Finite irreducible decompositions in noetherian topological spaces

Hartshorne proves (I.1, Prop. 1.5; Ex. I.2.5(b)) that in a noetherian topological space every
closed subset is a finite union of irreducible closed subsets, no one containing another, and
that this decomposition is unique.  We prove this in an arbitrary topological space satisfying
the descending chain condition for closed subsets, then apply it to `P^n`. -/

section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- **Irreducible closed subset**, in Hartshorne's sense: nonempty and not the union of two
proper closed subsets. -/
def IsIrredClosed (Z : Set X) : Prop :=
  Z.Nonempty ∧ IsClosed Z ∧
    ∀ A B : Set X, IsClosed A → IsClosed B → Z ⊆ A ∪ B → Z ⊆ A ∨ Z ⊆ B

/-- Hartshorne's definition ("cannot be written as the union of two proper closed subsets")
rephrased: `Z` is irreducible iff there are no two closed subsets, neither containing `Z`,
whose union contains `Z`. -/
theorem isIrredClosed_iff_not_union {Z : Set X} :
    IsIrredClosed Z ↔ Z.Nonempty ∧ IsClosed Z ∧
      ¬ ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Z ⊆ A ∪ B ∧ ¬ Z ⊆ A ∧ ¬ Z ⊆ B := by
  constructor
  · rintro ⟨hne, hc, hirr⟩
    refine ⟨hne, hc, ?_⟩
    rintro ⟨A, B, hA, hB, hcov, hAn, hBn⟩
    rcases hirr A B hA hB hcov with h | h
    · exact hAn h
    · exact hBn h
  · rintro ⟨hne, hc, hno⟩
    refine ⟨hne, hc, ?_⟩
    intro A B hA hB hcov
    by_contra hc'
    push Not at hc'
    exact hno ⟨A, B, hA, hB, hcov, hc'.1, hc'.2⟩

/-- The descending chain condition for closed subsets: Hartshorne's definition of a noetherian
topological space. -/
def HasDCCClosed (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ F : ℕ → Set X, (∀ i, IsClosed (F i)) → (∀ i, F (i + 1) ⊆ F i) → ∃ N, ∀ i, N ≤ i → F i = F N

/-- In a space with the descending chain condition, every nonempty family of closed subsets has
a minimal element. -/
theorem exists_minimal_closed (dcc : HasDCCClosed X) {F : Set (Set X)} (hne : F.Nonempty)
    (hF : ∀ Z ∈ F, IsClosed Z) :
    ∃ Z ∈ F, ∀ W ∈ F, W ⊆ Z → Z ⊆ W := by
  classical
  by_contra h
  push Not at h
  have hstep : ∀ x : {Z // Z ∈ F}, ∃ y : {Z // Z ∈ F}, y.1 ⊆ x.1 ∧ ¬ x.1 ⊆ y.1 := by
    rintro ⟨Z, hZ⟩
    obtain ⟨W, hW, hWZ, hZW⟩ := h Z hZ
    exact ⟨⟨W, hW⟩, hWZ, hZW⟩
  let nxt : {Z // Z ∈ F} → {Z // Z ∈ F} := fun x => (hstep x).choose
  have nxt_sub : ∀ x, (nxt x).1 ⊆ x.1 := fun x => (hstep x).choose_spec.1
  have nxt_not_sub : ∀ x, ¬ x.1 ⊆ (nxt x).1 := fun x => (hstep x).choose_spec.2
  obtain ⟨x₀, hx₀⟩ := hne
  let seq : ℕ → {Z // Z ∈ F} := fun i => Nat.rec ⟨x₀, hx₀⟩ (fun _ x => nxt x) i
  have hseq_succ : ∀ i, seq (i + 1) = nxt (seq i) := fun i => rfl
  have hanti : ∀ i, (seq (i + 1)).1 ⊆ (seq i).1 := fun i => by
    rw [hseq_succ]
    exact nxt_sub (seq i)
  have hclosed : ∀ i, IsClosed (seq i).1 := fun i => hF _ (seq i).2
  obtain ⟨N, hN⟩ := dcc (fun i => (seq i).1) hclosed hanti
  have h1 : (seq (N + 1)).1 = (seq N).1 := hN (N + 1) (Nat.le_succ N)
  refine nxt_not_sub (seq N) ?_
  rw [← hseq_succ, h1]

omit [TopologicalSpace X] in
/-- Every finite nonempty family of sets has a member which is maximal for inclusion. -/
theorem exists_maximal_subset_of_finite {E : Set (Set X)} (hE : E.Finite) (hne : E.Nonempty) :
    ∃ W ∈ E, ∀ W' ∈ E, W ⊆ W' → W' ⊆ W := by
  classical
  revert hne
  refine Set.Finite.induction_on
    (motive := fun s _ => s.Nonempty → ∃ W ∈ s, ∀ W' ∈ s, W ⊆ W' → W' ⊆ W) E hE ?_ ?_
  · intro hne
    exact absurd hne (by simp)
  · intro a s ha hs ih hne
    by_cases hsne : s.Nonempty
    · obtain ⟨W, hWs, hmax⟩ := ih hsne
      by_cases hWa : W ⊆ a
      · refine ⟨a, Set.mem_insert a s, ?_⟩
        intro W' hW' haW'
        rcases hW' with rfl | hW's
        · exact subset_rfl
        · have hWW' : W ⊆ W' := hWa.trans haW'
          have hW'W : W' ⊆ W := hmax W' hW's hWW'
          exact hW'W.trans hWa
      · refine ⟨W, Set.mem_insert_of_mem _ hWs, ?_⟩
        intro W' hW' hWW'
        rcases hW' with rfl | hW's
        · exact absurd hWW' hWa
        · exact hmax W' hW's hWW'
    · refine ⟨a, Set.mem_insert a s, ?_⟩
      intro W' hW' haW'
      rw [Set.mem_insert_iff] at hW'
      rcases hW' with rfl | hWs
      · exact subset_rfl
      · exact absurd ⟨W', hWs⟩ hsne

end NoetherianTop


section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- **Existence of a finite irreducible decomposition**: in a space with the descending chain
condition, every closed subset is a finite union of irreducible closed subsets.  The proof is
the minimal-counterexample argument: if some closed set had no such decomposition, a minimal
one would be reducible, `Z = (Z ∩ A) ∪ (Z ∩ B)` with both parts proper closed subsets, and the
decompositions of the two proper parts would combine to one of `Z`. -/
theorem exists_finite_irred_cover (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D := by
  classical
  by_contra hcon
  -- the family of closed sets without a finite irreducible decomposition
  set F : Set (Set X) :=
    {Y | IsClosed Y ∧ ¬ ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Y = ⋃₀ D}
    with hFdef
  have hFne : F.Nonempty := ⟨Z, hZ, hcon⟩
  have hFclosed : ∀ W ∈ F, IsClosed W := fun W hW => hW.1
  obtain ⟨Z₀, hZ₀F, hmin⟩ := exists_minimal_closed dcc hFne hFclosed
  obtain ⟨hZ₀c, hZ₀bad⟩ := hZ₀F
  have hZ₀ne : Z₀.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hZ₀bad ⟨∅, Set.finite_empty, by simp, by rw [Set.sUnion_empty]; exact h⟩
  -- `Z₀` is not irreducible, so it is the union of two proper closed pieces
  have hred : ¬ ∀ A B : Set X, IsClosed A → IsClosed B → Z₀ ⊆ A ∪ B → Z₀ ⊆ A ∨ Z₀ ⊆ B := by
    intro hAB
    exact hZ₀bad ⟨{Z₀}, Set.finite_singleton Z₀, by
      rintro W hW
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hZ₀ne, hZ₀c, hAB⟩, by simp⟩
  push Not at hred
  obtain ⟨A, B, hA, hB, hcov, hAn, hBn⟩ := hred
  have hZ₁c : IsClosed (Z₀ ∩ A) := IsClosed.inter hZ₀c hA
  have hZ₂c : IsClosed (Z₀ ∩ B) := IsClosed.inter hZ₀c hB
  have hZ₁proper : Z₀ ∩ A ⊆ Z₀ ∧ ¬ Z₀ ⊆ Z₀ ∩ A := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hsub
    exact hAn (fun x hx => (hsub hx).2)
  have hZ₂proper : Z₀ ∩ B ⊆ Z₀ ∧ ¬ Z₀ ⊆ Z₀ ∩ B := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hsub
    exact hBn (fun x hx => (hsub hx).2)
  have hdec : ∀ W : Set X, W ∈ F → W ⊆ Z₀ → W ≠ Z₀ → False := by
    intro W hW hsub hne
    exact hne (le_antisymm hsub (hmin W hW hsub))
  have hdec₁ : ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z₀ ∩ A = ⋃₀ D := by
    by_contra h
    exact hdec _ ⟨hZ₁c, h⟩ Set.inter_subset_left (fun heq => hZ₁proper.2 (heq.symm ▸ subset_rfl))
  have hdec₂ : ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z₀ ∩ B = ⋃₀ D := by
    by_contra h
    exact hdec _ ⟨hZ₂c, h⟩ Set.inter_subset_left (fun heq => hZ₂proper.2 (heq.symm ▸ subset_rfl))
  obtain ⟨D₁, hD₁fin, hD₁irr, hD₁cov⟩ := hdec₁
  obtain ⟨D₂, hD₂fin, hD₂irr, hD₂cov⟩ := hdec₂
  have hZ₀eq : Z₀ = (Z₀ ∩ A) ∪ (Z₀ ∩ B) := by
    refine le_antisymm ?_ (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  refine hZ₀bad ⟨D₁ ∪ D₂, hD₁fin.union hD₂fin, ?_, ?_⟩
  · intro W hW
    rcases hW with hW | hW
    · exact hD₁irr W hW
    · exact hD₂irr W hW
  · rw [hZ₀eq, Set.sUnion_union, hD₁cov, hD₂cov]

/-- **A canonical (antichain) finite irreducible decomposition**: keeping only the maximal
members of a finite irreducible cover gives a decomposition no member of which contains
another. -/
theorem exists_antichain_irred_cover (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D : Set (Set X), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D ∧
      (∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' → W = W') := by
  classical
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := exists_finite_irred_cover dcc hZ
  set D' : Set (Set X) := {W ∈ D | ∀ W' ∈ D, W ⊆ W' → W = W'} with hD'def
  have hD'sub : D' ⊆ D := fun W hW => hW.1
  refine ⟨D', hDfin.subset hD'sub, fun W hW => hDirr W hW.1, ?_, ?_⟩
  · refine le_antisymm ?_ (Set.sUnion_subset fun W hW => hDcov ▸ Set.subset_sUnion_of_mem hW.1)
    intro x hx
    have hxD : x ∈ ⋃₀ D := hDcov ▸ hx
    obtain ⟨W, hWD, hxW⟩ := Set.mem_sUnion.1 hxD
    have hEfin : ({V ∈ D | x ∈ V}).Finite := hDfin.subset (fun V hV => hV.1)
    have hEne : ({V ∈ D | x ∈ V}).Nonempty := ⟨W, hWD, hxW⟩
    obtain ⟨W', ⟨hW'D, hxW'⟩, hmax⟩ := exists_maximal_subset_of_finite hEfin hEne
    refine Set.mem_sUnion.2 ⟨W', ⟨hW'D, ?_⟩, hxW'⟩
    intro V hVD hWV
    exact le_antisymm hWV (hmax V ⟨hVD, hWV hxW'⟩ hWV)
  · intro W hW W' hW' hsub
    exact hW.2 W' hW'.1 hsub

/-- A finite irreducible decomposition of `Z`: a finite union `Z = ⋃₀ D` of irreducible closed
subsets, no one containing another. -/
def IsIrredDecomposition (D : Set (Set X)) (Z : Set X) : Prop :=
  D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D ∧
    (∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' → W = W')

/-- **Existence part of Hartshorne Ex. I.2.5(b)**. -/
theorem exists_irredDecomposition (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D, IsIrredDecomposition D Z :=
  exists_antichain_irred_cover dcc hZ

/-- An irreducible closed set contained in a finite union of closed sets is contained in one of
them. -/
theorem IsIrredClosed.exists_subset_of_finite_sUnion {W : Set X} (hW : IsIrredClosed W)
    {E : Set (Set X)} (hEfin : E.Finite) (hEclosed : ∀ V ∈ E, IsClosed V)
    (hsub : W ⊆ ⋃₀ E) : ∃ V ∈ E, W ⊆ V := by
  classical
  revert hsub hEclosed
  refine Set.Finite.induction_on (motive := fun s _ =>
    (∀ V ∈ s, IsClosed V) → W ⊆ ⋃₀ s → ∃ V ∈ s, W ⊆ V) E hEfin ?_ ?_
  · intro _ hsub
    obtain ⟨x, hx⟩ := hW.1
    exact absurd (hsub hx) (by simp)
  · intro a s ha hs ih hEcl hsub
    rw [Set.sUnion_insert] at hsub
    have hscl : IsClosed (⋃₀ s) := by
      rw [Set.sUnion_eq_biUnion]
      exact hs.isClosed_biUnion fun V hV => hEcl V (Set.mem_insert_of_mem a hV)
    rcases hW.2.2 a (⋃₀ s) (hEcl a (Set.mem_insert a s)) hscl hsub with hWa | hWs
    · exact ⟨a, Set.mem_insert a s, hWa⟩
    · obtain ⟨V, hV, hWV⟩ := ih (fun V hV => hEcl V (Set.mem_insert_of_mem a hV)) hWs
      exact ⟨V, Set.mem_insert_of_mem a hV, hWV⟩

/-- **Uniqueness part of Hartshorne Ex. I.2.5(b)**: two finite unions of irreducible closed
subsets, no one containing another, with the same union, coincide. -/
theorem irredDecomposition_unique {D D' : Set (Set X)} {Z : Set X}
    (hD : IsIrredDecomposition D Z) (hD' : IsIrredDecomposition D' Z) : D = D' := by
  classical
  obtain ⟨hDfin, hDirr, hDcov, hDanti⟩ := hD
  obtain ⟨hD'fin, hD'irr, hD'cov, hD'anti⟩ := hD'
  -- key: a member of one decomposition is contained in a member of the other
  have key : ∀ W : Set X, W ∈ D → ∃ W' ∈ D', W ⊆ W' := by
    intro W hW
    have hWZ : W ⊆ Z := by rw [hDcov]; exact Set.subset_sUnion_of_mem hW
    have hWZ' : W ⊆ ⋃₀ D' := by rw [← hD'cov]; exact hWZ
    exact (hDirr W hW).exists_subset_of_finite_sUnion hD'fin (fun V hV => (hD'irr V hV).2.1) hWZ'
  have key' : ∀ W : Set X, W ∈ D' → ∃ W' ∈ D, W ⊆ W' := by
    intro W hW
    have hWZ : W ⊆ Z := by rw [hD'cov]; exact Set.subset_sUnion_of_mem hW
    have hWZ' : W ⊆ ⋃₀ D := by rw [← hDcov]; exact hWZ
    exact (hD'irr W hW).exists_subset_of_finite_sUnion hDfin (fun V hV => (hDirr V hV).2.1) hWZ'
  refine Set.Subset.antisymm ?_ ?_
  · intro W hW
    obtain ⟨W', hW'D', hWW'⟩ := key W hW
    obtain ⟨W'', hW''D, hW'W''⟩ := key' W' hW'D'
    have hWW'' : W ⊆ W'' := hWW'.trans hW'W''
    have hEq : W = W'' := hDanti W hW W'' hW''D hWW''
    have hW'W : W' ⊆ W := hEq.symm ▸ hW'W''
    have hW'W_eq : W' = W := le_antisymm hW'W hWW'
    rw [← hW'W_eq]
    exact hW'D'
  · intro W hW
    obtain ⟨W', hW'D, hWW'⟩ := key' W hW
    obtain ⟨W'', hW''D', hW'W''⟩ := key W' hW'D
    have hWW'' : W ⊆ W'' := hWW'.trans hW'W''
    have hEq : W = W'' := hD'anti W hW W'' hW''D' hWW''
    have hW'W : W' ⊆ W := hEq.symm ▸ hW'W''
    have hW'W_eq : W' = W := le_antisymm hW'W hWW'
    rw [← hW'W_eq]
    exact hW'D

/-- **Hartshorne Ex. I.2.5(b)**, existence and uniqueness together. -/
theorem existsUnique_irredDecomposition (dcc : HasDCCClosed X) {Z : Set X} (hZ : IsClosed Z) :
    ∃ D, IsIrredDecomposition D Z ∧ ∀ D', IsIrredDecomposition D' Z → D' = D := by
  obtain ⟨D, hD⟩ := exists_irredDecomposition dcc hZ
  exact ⟨D, hD, fun D' hD' => irredDecomposition_unique hD' hD⟩

end NoetherianTop


section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- Our notion of irreducible closed subset agrees with Mathlib's `IsIrreducible` (and hence
with Hartshorne's "not the union of two proper closed subsets"). -/
theorem isIrredClosed_iff_isIrreducible {Z : Set X} :
    IsIrredClosed Z ↔ IsClosed Z ∧ IsIrreducible Z := by
  refine ⟨fun h => ⟨h.2.1, h.1, ?_⟩, fun h => ⟨h.2.1, h.1, ?_⟩⟩
  · exact isPreirreducible_iff_isClosed_union_isClosed.2 h.2.2
  · exact isPreirreducible_iff_isClosed_union_isClosed.1 h.2.2

end NoetherianTop

/-! ## Part 4: chain dimension as a supremum of chain lengths -/

section IrrChainDim

variable {X : Type*} [TopologicalSpace X]

/-- The chain dimension of a set `Z` in a topological space: the supremum of the lengths of chains
of irreducible closed subsets of `Z`, as an element of `ℕ∞`. -/
noncomputable def irrChainDim (Z : Set X) : ℕ∞ :=
  ⨆ (l : LTSeries {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W}), (l.length : ℕ∞)

theorem irrChainDim_mono {Z Z' : Set X} (h : Z ⊆ Z') : irrChainDim Z ≤ irrChainDim Z' := by
  refine iSup_le fun l => ?_
  let hmap : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W} :=
    l.map (fun W => ⟨W.1, W.2.1.trans h, W.2.2.1, W.2.2.2⟩) (fun a b hab => hab)
  calc (l.length : ℕ∞) = (hmap.length : ℕ∞) := rfl
    _ ≤ ⨆ (l' : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W}), (l'.length : ℕ∞) :=
        le_iSup (fun l' : LTSeries {W : Set X // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W} =>
          (l'.length : ℕ∞)) hmap

theorem irrChainDim_le_iff {Z : Set X} {c : ℕ∞} :
    irrChainDim Z ≤ c ↔ ∀ l : LTSeries {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W},
      (l.length : ℕ∞) ≤ c :=
  iSup_le_iff

/-- **A finite closed cover computes the dimension.** -/
theorem irrChainDim_iUnion {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : ∀ i, IsClosed (A i)) :
    irrChainDim (⋃ i, A i) = ⨆ i, irrChainDim (A i) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [irrChainDim_le_iff]
    intro l
    -- the last element of the chain lies in one member of the cover
    have hlastirr : IsIrreducible (l (Fin.last l.length)).1 := (l (Fin.last l.length)).2.2.1
    have hlastsub : (l (Fin.last l.length)).1 ⊆ ⋃₀ (Set.range A) := by
      rw [Set.sUnion_range]
      exact (l (Fin.last l.length)).2.1
    obtain ⟨W, ⟨i0, rfl⟩, hWi⟩ := IsIrredClosed.exists_subset_of_finite_sUnion
      ((isIrredClosed_iff_isIrreducible).mpr ⟨(l (Fin.last l.length)).2.2.2, hlastirr⟩)
      (Set.finite_range A) (fun W hW => by obtain ⟨i, rfl⟩ := hW; exact hA i) hlastsub
    -- every element of the chain is contained in that member
    have hall : ∀ j : Fin (l.length + 1), (l j).1 ⊆ A i0 := by
      intro j
      have hle : (l j).1 ⊆ (l (Fin.last l.length)).1 := by
        rcases RelSeries.rel_or_eq_of_le l (Fin.le_last j) with h' | h'
        · exact le_of_lt h'
        · rw [h']
      exact hle.trans hWi
    -- restrict the chain to that member
    let l' : LTSeries {W : Set X // W ⊆ A i0 ∧ IsIrreducible W ∧ IsClosed W} :=
      { length := l.length
        toFun := fun j => ⟨(l j).1, hall j, (l j).2.2.1, (l j).2.2.2⟩
        step := fun j => l.step j }
    have hlen : (l.length : ℕ∞) = (l'.length : ℕ∞) := rfl
    rw [hlen]
    exact le_iSup_of_le i0 (le_iSup (fun l : LTSeries {W : Set X // W ⊆ A i0 ∧ IsIrreducible W ∧ IsClosed W} => (l.length : ℕ∞)) l')
  · refine iSup_le fun i => irrChainDim_mono (Set.subset_iUnion A i)

end IrrChainDim

/-! ## Part 5: dimensions of projective algebraic sets and of their cones -/

section Dims

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- The dimension of a projective algebraic set: the supremum of the lengths of chains of
irreducible closed subsets. -/
noncomputable def projDim (Y : Set (Proj k n)) : ℕ∞ := irrChainDim Y

/-- The dimension of the affine cone over a projective set. -/
noncomputable def coneDim (Y : Set (Proj k n)) : ℕ∞ := irrChainDim (Proj.cone Y)

theorem projDim_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) : projDim Y ≤ projDim Z :=
  irrChainDim_mono h

theorem coneDim_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) : coneDim Y ≤ coneDim Z :=
  irrChainDim_mono (Proj.cone_mono h)

/-- Singletons are closed in the affine Zariski topology. -/
theorem isClosed_singleton_affine {m : ℕ} (z : Fin m → k) :
    IsClosed ({z} : Set (Fin m → k)) := by
  rw [isClosed_iff_zarClosed k m]
  refine ⟨Ideal.span (Set.range (fun i : Fin m => MvPolynomial.X i - MvPolynomial.C (z i))), ?_⟩
  ext v
  rw [Set.mem_singleton_iff, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hzv
    rw [hzv]
    have hle : Ideal.span (Set.range (fun i : Fin m =>
        MvPolynomial.X i - MvPolynomial.C (z i))) ≤ RingHom.ker (MvPolynomial.aeval z) := by
      refine Ideal.span_le.mpr ?_
      rintro q ⟨i, rfl⟩
      simp
    intro p hp
    exact hle hp
  · intro h
    funext i
    have hv := h _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [MvPolynomial.aeval_eq_eval, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hv
    exact sub_eq_zero.mp hv

/-- The vertex of the cone is closed. -/
theorem isClosed_singleton_zero : IsClosed ({0} : Set (Fin (n + 1) → k)) :=
  isClosed_singleton_affine 0

theorem isIrreducible_singleton_affine {m : ℕ} (z : Fin m → k) :
    IsIrreducible ({z} : Set (Fin m → k)) :=
  ⟨⟨z, rfl⟩, isPreirreducible_singleton⟩

/-- Turning an `ℕ∞`-valued dimension into the `WithBot ℕ∞` dimension of I.1.8. -/
theorem varietyDim_eq_coe_irrChainDim {m : ℕ} {Z : Set (Fin m → k)} (hZ : Z.Nonempty) :
    varietyDim k m Z = (irrChainDim Z : WithBot ℕ∞) := by
  obtain ⟨z, hz⟩ := hZ
  haveI : Nonempty {W : Set (Fin m → k) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨{z}, Set.singleton_subset_iff.mpr hz, isIrreducible_singleton_affine z,
      isClosed_singleton_affine z⟩⟩
  rw [varietyDim, Order.krullDim_eq_iSup_length, irrChainDim,
    WithBot.coe_iSup (OrderTop.bddAbove _)]

/-- An affine space has dimension `m`. -/
theorem varietyDim_univ {m : ℕ} :
    varietyDim k m (Set.univ : Set (Fin m → k)) = (m : WithBot ℕ∞) := by
  have h := varietyDim_zeroLocus k m (⊥ : Ideal (MvPolynomial (Fin m) k))
  rw [MvPolynomial.zeroLocus_bot, Set.top_eq_univ] at h
  rw [h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial (Fin m) k)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- The full projective space has cone the whole affine space. -/
theorem coneDim_univ : coneDim (Set.univ : Set (Proj k n)) = (n + 1 : ℕ∞) := by
  have h1 : varietyDim k (n + 1) (Set.univ : Set (Fin (n + 1) → k)) =
      ((coneDim (Set.univ : Set (Proj k n))) : WithBot ℕ∞) := by
    rw [coneDim, ← Proj.cone_univ]
    exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
  rw [varietyDim_univ] at h1
  exact WithBot.coe_injective h1.symm

/-- The dimension of the cone over the empty set (a single point) is zero. -/
theorem coneDim_empty : coneDim (∅ : Set (Proj k n)) = 0 := by
  have h1 : varietyDim k (n + 1) ({0} : Set (Fin (n + 1) → k)) =
      ((coneDim (∅ : Set (Proj k n))) : WithBot ℕ∞) := by
    rw [coneDim, Proj.cone_empty]
    exact varietyDim_eq_coe_irrChainDim ⟨0, rfl⟩
  have h2 : varietyDim k (n + 1) ({0} : Set (Fin (n + 1) → k)) = 0 := by
    haveI : Subsingleton {W : Set (Fin (n + 1) → k) //
        W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W} := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have key : ∀ c : {W : Set (Fin (n + 1) → k) //
          W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W}, c.1 = {0} := by
        intro c
        obtain ⟨v, hv⟩ := c.2.2.1.1
        have hv0 : v = 0 := by simpa using c.2.1 hv
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨hv0 ▸ hv, fun w hw => ?_⟩
        simpa using c.2.1 hw
      rw [key a, key b]
    haveI : Nonempty {W : Set (Fin (n + 1) → k) //
        W ⊆ ({0} : Set (Fin (n + 1) → k)) ∧ IsIrreducible W ∧ IsClosed W} :=
      ⟨⟨{0}, subset_refl _, isIrreducible_singleton_affine 0, isClosed_singleton_zero⟩⟩
    rw [varietyDim]
    exact Order.krullDim_eq_zero
  rw [h2] at h1
  exact WithBot.coe_injective (by simpa using h1.symm)

end Dims

/-! ### Extending chains -/

section ChainExtend

variable {X : Type*} [TopologicalSpace X]

/-- Appending a strictly larger irreducible closed set lengthens a chain by one. -/
theorem irrChainDim_add_one_le {Z Y : Set X} (hZY : Z ⊆ Y) (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hne : Z ≠ Y) :
    irrChainDim Z + 1 ≤ irrChainDim Y := by
  haveI hQ : Nonempty {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨Z, subset_refl Z, hZi, hZc⟩⟩
  rw [irrChainDim, irrChainDim, ENat.iSup_add]
  refine iSup_le fun l => ?_
  let phi : {W : Set X // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} →
      {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    fun W => ⟨W.1, W.2.1.trans hZY, W.2.2.1, W.2.2.2⟩
  have hphi : StrictMono phi := fun a b hab => hab
  let Yq : {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨Y, fun x hx => hx, hYi, hYc⟩
  have hrel : (l.map phi hphi).last < Yq := by
    have hlast : (l.map phi hphi).last = phi (l (Fin.last l.length)) := rfl
    rw [hlast]
    refine ⟨(l (Fin.last l.length)).2.1.trans hZY, ?_⟩
    intro hEq
    exact hne (le_antisymm hZY (hEq.trans (l (Fin.last l.length)).2.1))
  let p : LTSeries {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} :=
    (l.map phi hphi).snoc Yq hrel
  have hlen : (p.length : ℕ∞) = (l.length : ℕ∞) + 1 := by simp [p]
  rw [← hlen]
  exact le_iSup (fun p : LTSeries {W : Set X // W ⊆ Y ∧ IsIrreducible W ∧ IsClosed W} =>
    (p.length : ℕ∞)) p

end ChainExtend

/-! ## Part 6: `P^n` and affine space are noetherian -/

section AffineDCC

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Affine space with the Zariski topology satisfies the descending chain condition. -/
theorem affine_dcc (m : ℕ) : HasDCCClosed (Fin m → k) := by
  intro F hF hanti
  have hmono : Monotone fun i => MvPolynomial.vanishingIdeal k (F i) :=
    monotone_nat_of_le_succ fun i => MvPolynomial.vanishingIdeal_anti_mono (hanti i)
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun i => MvPolynomial.vanishingIdeal k (F i), hmono⟩ : ℕ →o Ideal (MvPolynomial (Fin m) k))
  refine ⟨N, fun i hi => ?_⟩
  have hI : MvPolynomial.vanishingIdeal k (F i) = MvPolynomial.vanishingIdeal k (F N) :=
    (hN i hi).symm
  rw [← zeroLocus_vanishingIdeal_of_isClosed k m (hF i),
    ← zeroLocus_vanishingIdeal_of_isClosed k m (hF N), hI]

end AffineDCC

section ProjForms

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem vanishingIdeal_mono {Y Z : Set (Proj k n)} (h : Y ⊆ Z) :
    vanishingIdeal Z ≤ vanishingIdeal Y := by
  rw [vanishingIdeal, vanishingIdeal, Ideal.span_le]
  rintro f ⟨d, hd, hvan⟩
  exact subset_vanishingIdeal hd fun x hx => hvan x (h hx)

/-- The homogeneous members of the vanishing ideal. -/
noncomputable def vanishingForms (Z : Set (Proj k n)) : Set (HomogPoly k n) :=
  {f | f.1 ∈ vanishingIdeal Z}

theorem mem_zeroLocus_vanishingForms_iff {Z : Set (Proj k n)} {x : Proj k n} :
    x ∈ zeroLocus (vanishingForms Z) ↔
      ∀ f : MvPolynomial (Fin (n + 1)) k, (∃ d, f.IsHomogeneous d) → f ∈ vanishingIdeal Z →
        MvPolynomial.eval x.rep f = 0 := by
  constructor
  · rintro h f ⟨d, hd⟩ hf
    exact h ⟨f, d, hd⟩ hf
  · rintro h f hf
    exact h f.1 f.2 hf

theorem vanishingIdeal_eq_top_of_empty : vanishingIdeal (∅ : Set (Proj k n)) = ⊤ := by
  refine Ideal.eq_top_iff_one _ |>.mpr ?_
  exact subset_vanishingIdeal (MvPolynomial.isHomogeneous_one ..)
    (fun x hx => by simp at hx)

/-- `V(I(Z)) = Z` for closed `Z`. -/
theorem zeroLocus_vanishingForms_eq (Z : Set (Proj k n)) (hZ : IsClosed Z) :
    zeroLocus (vanishingForms Z) = Z := by
  have key : ∀ f : MvPolynomial (Fin (n + 1)) k, f ∈ vanishingIdeal Z → ∀ v hv,
      mk v hv ∈ Z → MvPolynomial.eval v f = 0 := by
    intro f hf v hv hmem
    have hf' : f ∈ vanishOnIdeal Z := by
      rw [vanishOnIdeal_eq_vanishingIdeal Z]; exact hf
    exact mem_vanishOnIdeal_iff.mp hf' v hv hmem
  refine le_antisymm ?_ ?_
  · rintro x hx
    rw [mem_zeroLocus_vanishingForms_iff] at hx
    rcases Set.eq_empty_or_nonempty Z with rfl | hZne
    · -- `1 ∈ I(∅)`, contradiction
      have hI : vanishingIdeal (∅ : Set (Proj k n)) = ⊤ := vanishingIdeal_eq_top_of_empty
      have hone : MvPolynomial.eval x.rep (1 : MvPolynomial (Fin (n + 1)) k) = 0 :=
        hx 1 ⟨0, MvPolynomial.isHomogeneous_one ..⟩ (by rw [hI]; exact Submodule.mem_top)
      simp at hone
    · have hcone : x.rep ∈ MvPolynomial.zeroLocus k (vanishingIdeal Z) := by
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [MvPolynomial.aeval_eq_eval, ← MvPolynomial.sum_homogeneousComponent p, map_sum]
        refine Finset.sum_eq_zero fun e _ => ?_
        have hmem : MvPolynomial.homogeneousComponent e p ∈ vanishingIdeal Z := by
          rw [← vanishOnIdeal_eq_vanishingIdeal Z]
          exact homogeneousComponent_mem_vanishOnIdeal (by rwa [vanishOnIdeal_eq_vanishingIdeal Z]) e
        exact hx _ ⟨e, MvPolynomial.homogeneousComponent_isHomogeneous e p⟩ hmem
      rw [← cone_eq_zeroLocus ((isProjClosed_iff_isClosed Z).mpr hZ) hZne] at hcone
      rcases hcone with h0 | ⟨_, hmem⟩
      · exact absurd h0 x.rep_nonzero
      · simpa using hmem
  · intro x hx f hf
    exact key f.1 hf x.rep x.rep_nonzero (by simpa using hx)

end Proj

end ProjForms

/-! ## Part 7: the projective space is noetherian, hyperplane sections of cones -/

section ProjNoetherian

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

/-- `P^n` satisfies the descending chain condition for closed subsets. -/
theorem dcc_closed (F : ℕ → Set (Proj k n)) (hF : ∀ i, IsClosed (F i))
    (hanti : ∀ i, F (i + 1) ⊆ F i) : ∃ N, ∀ i, N ≤ i → F i = F N := by
  have hmono : Monotone fun i => vanishingIdeal (F i) :=
    monotone_nat_of_le_succ fun i => vanishingIdeal_mono (hanti i)
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun i => vanishingIdeal (F i), hmono⟩ : ℕ →o Ideal (MvPolynomial (Fin (n + 1)) k))
  refine ⟨N, fun i hi => ?_⟩
  have hI : vanishingForms (F i) = vanishingForms (F N) := by
    have h2 : vanishingIdeal (F N) = vanishingIdeal (F i) := hN i hi
    simp only [vanishingForms, h2]
  rw [← zeroLocus_vanishingForms_eq (F i) (hF i), ← zeroLocus_vanishingForms_eq (F N) (hF N)]
  rw [hI]

/-- `P^n` is a noetherian topological space in Hartshorne's sense. -/
theorem hasDCCClosed : HasDCCClosed (Proj k n) := dcc_closed

/-- Finite irreducible decomposition of a closed subset of `P^n`. -/
theorem exists_finite_irred_cover_closed {Z : Set (Proj k n)} (hZ : IsClosed Z) :
    ∃ D : Set (Set (Proj k n)), D.Finite ∧ (∀ W ∈ D, IsIrredClosed W) ∧ Z = ⋃₀ D :=
  exists_finite_irred_cover hasDCCClosed hZ

/-- The coordinate function `x_i`. -/
noncomputable def coord (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k := MvPolynomial.X i

theorem coord_isHomogeneous (i : Fin (n + 1)) : (coord (k := k) i).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X (R := k) i

/-- The coordinate form as a homogeneous polynomial. -/
noncomputable def coordForm (i : Fin (n + 1)) : HomogPoly k n :=
  ⟨coord (k := k) i, 1, coord_isHomogeneous i⟩

theorem eval_coord (v : Fin (n + 1) → k) (i : Fin (n + 1)) :
    MvPolynomial.eval v (coord (k := k) i) = v i := by
  simp [coord]

/-- The defining form of the coordinate hyperplane. -/
noncomputable def hyperplaneForms (i : Fin (n + 1)) : Set (HomogPoly k n) :=
  {coordForm (k := k) i}

/-- The coordinate hyperplane `x_i = 0`. -/
noncomputable def hyperplane (i : Fin (n + 1)) : Set (Proj k n) :=
  zeroLocus (hyperplaneForms (k := k) i)

theorem mem_hyperplaneForms {i : Fin (n + 1)} {f : HomogPoly k n} :
    f ∈ hyperplaneForms (k := k) i ↔ f = coordForm (k := k) i :=
  Iff.rfl

theorem hyperplane_eq_compreh (i : Fin (n + 1)) :
    hyperplane i = {x | IsZeroAt (coord (k := k) i) x} := by
  ext x
  show (∀ f ∈ hyperplaneForms (k := k) i, IsZeroAt f.1 x) ↔ IsZeroAt (coord (k := k) i) x
  constructor
  · intro hx
    exact hx _ (mem_hyperplaneForms.mpr rfl)
  · intro hx f hf
    rw [mem_hyperplaneForms] at hf
    rw [hf]
    exact hx

theorem isClosed_hyperplane (i : Fin (n + 1)) : IsClosed (hyperplane (k := k) (n := n) i) :=
  (isClosed_iff (k := k) (n := n) (hyperplane (k := k) (n := n) i)).mpr
    ⟨hyperplaneForms (k := k) i, rfl⟩

theorem mem_hyperplane_mk_iff {i : Fin (n + 1)} {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    mk v hv ∈ hyperplane i ↔ v i = 0 := by
  rw [hyperplane_eq_compreh]
  exact isZeroAt_mk_iff (coord_isHomogeneous i) hv |>.trans (by simp [eval_coord])

/-- The cone over a hyperplane section of `Y` is the hyperplane section of the cone. -/
theorem cone_inter_hyperplane (Y : Set (Proj k n)) (i : Fin (n + 1)) :
    cone (Y ∩ hyperplane i) =
      cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {coord (k := k) i}) := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem⟩)
    · refine ⟨Or.inl rfl, ?_⟩
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro p hp
      have hle : Ideal.span {coord (k := k) i} ≤
          RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
        refine Ideal.span_le.mpr ?_
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        show MvPolynomial.aeval (0 : Fin (n + 1) → k) (coord (k := k) i) = 0
        rw [MvPolynomial.aeval_eq_eval, eval_coord]
        simp
      rw [MvPolynomial.aeval_eq_eval]
      exact hle hp
    · refine ⟨Or.inr ⟨hv, hmem.1⟩, ?_⟩
      rw [MvPolynomial.mem_zeroLocus_iff]
      intro p hp
      rw [MvPolynomial.aeval_eq_eval]
      have hle : Ideal.span {coord (k := k) i} ≤ RingHom.ker (MvPolynomial.aeval v) := by
        refine Ideal.span_le.mpr ?_
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        show MvPolynomial.aeval v (coord (k := k) i) = 0
        rw [MvPolynomial.aeval_eq_eval, eval_coord]
        exact (mem_hyperplane_mk_iff hv).mp hmem.2
      exact hle hp
  · rintro ⟨hv1, hv2⟩
    rcases hv1 with h0 | ⟨hv, hmem⟩
    · exact Or.inl h0
    · refine Or.inr ⟨hv, hmem, ?_⟩
      refine (mem_hyperplane_mk_iff hv).mpr ?_
      have h := (MvPolynomial.mem_zeroLocus_iff.mp hv2) (coord (k := k) i)
        (Ideal.mem_span_singleton_self _)
      rwa [MvPolynomial.aeval_eq_eval, eval_coord] at h

/-- Cones are strictly monotone on projective sets. -/
theorem cone_ssubset {Y Z : Set (Proj k n)} (h : Y ⊆ Z) (hne : Y ≠ Z) : cone Y ⊂ cone Z := by
  refine ⟨cone_mono h, fun hsub => ?_⟩
  have hZY : Z ⊆ Y := by
    intro x hx
    have hx' : x.rep ∈ cone Z := Or.inr ⟨x.rep_nonzero, by simpa using hx⟩
    rcases hsub hx' with h0 | ⟨_, hm⟩
    · exact absurd h0 x.rep_nonzero
    · simpa using hm
  exact hne (Set.Subset.antisymm h hZY)

/-- Some coordinate function does not vanish on a nonempty projective set. -/
theorem exists_coord_notMem_vanishingIdeal {Y : Set (Proj k n)} (hne : Y.Nonempty) :
    ∃ i : Fin (n + 1), coord (k := k) i ∉ vanishingIdeal Y := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x.rep j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact x.rep_nonzero (funext h')
  have hv : MvPolynomial.eval x.rep (coord (k := k) j) = 0 := by
    refine (mem_vanishOnIdeal_iff.mp ?_) x.rep x.rep_nonzero (by simpa using hx)
    rw [vanishOnIdeal_eq_vanishingIdeal Y]
    exact h j
  exact hj (by simpa [eval_coord] using hv)

end Proj

end ProjNoetherian

/-! ### The cone over a union, and dimensions of finite decompositions -/

section Decomposition

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem cone_iUnion {ι : Type*} [Nonempty ι] (A : ι → Set (Proj k n)) :
    cone (⋃ i, A i) = ⋃ i, cone (A i) := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hmem⟩)
    · exact Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, Or.inl rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact Set.mem_iUnion.mpr ⟨i, Or.inr ⟨hv, hi⟩⟩
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact cone_mono (Set.subset_iUnion A i) hi

end Proj

/-- The cone dimension is computed by any finite closed cover. -/
theorem coneDim_eq_iSup_decomposition {Y : Set (Proj k n)} {D : Set (Set (Proj k n))}
    (hDfin : D.Finite) (hDne : D.Nonempty) (hDirr : ∀ W ∈ D, IsIrredClosed W)
    (hDcov : Y = ⋃₀ D) :
    coneDim Y = ⨆ W : D, coneDim (W : Set (Proj k n)) := by
  haveI : Fintype D := hDfin.fintype
  haveI : Nonempty D := hDne.to_subtype
  have hcl : ∀ W : D, IsClosed (W : Set (Proj k n)) := fun W => (hDirr W.1 W.2).2.1
  rw [coneDim, hDcov, Set.sUnion_eq_iUnion, Proj.cone_iUnion,
    irrChainDim_iUnion (fun W : D => Proj.cone (W : Set (Proj k n)))
      (fun W => Proj.isClosed_cone (hcl W))]
  rfl

/-- The projective dimension is computed by any finite closed cover. -/
theorem projDim_eq_iSup_decomposition {Y : Set (Proj k n)} {D : Set (Set (Proj k n))}
    (hDfin : D.Finite) (hDirr : ∀ W ∈ D, IsIrredClosed W) (hDcov : Y = ⋃₀ D) :
    projDim Y = ⨆ W : D, projDim (W : Set (Proj k n)) := by
  haveI : Fintype D := hDfin.fintype
  have hcl : ∀ W : D, IsClosed (W : Set (Proj k n)) := fun W => (hDirr W.1 W.2).2.1
  rw [projDim, hDcov, Set.sUnion_eq_iUnion,
    irrChainDim_iUnion (fun W : D => (W : Set (Proj k n))) hcl]
  rfl

end Decomposition

/-! ## Part 8: comparison of the dimensions -/

section Comparison

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- Monotonicity of the `WithBot`-valued dimension. -/
theorem varietyDim_mono {m : ℕ} {Z Z' : Set (Fin m → k)} (h : Z ⊆ Z') :
    varietyDim k m Z ≤ varietyDim k m Z' := by
  rw [varietyDim, varietyDim]
  refine Order.krullDim_le_of_strictMono
    (fun W : {W : Set (Fin m → k) // W ⊆ Z ∧ IsIrreducible W ∧ IsClosed W} =>
      (⟨W.1, W.2.1.trans h, W.2.2⟩ :
        {W : Set (Fin m → k) // W ⊆ Z' ∧ IsIrreducible W ∧ IsClosed W}))
    (fun a b hab => hab)

/-- **The lower bound**: the cone over a nonempty closed set has dimension at least one more
than the set itself. -/
theorem projDim_add_one_le_coneDim {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    projDim Y + 1 ≤ coneDim Y := by
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := Proj.exists_finite_irred_cover_closed (k := k) (n := n) hYc
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with rfl | h
    · exfalso
      rw [hDcov] at hne
      simp at hne
    · exact h
  obtain ⟨W, hWD⟩ := hDne
  have hWirr : IsIrreducible W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).2
  have hWcl : IsClosed W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).1
  haveI hQ : Nonempty {Z : Set (Proj k n) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z} :=
    ⟨⟨W, by rw [hDcov]; exact Set.subset_sUnion_of_mem hWD, hWirr, hWcl⟩⟩
  rw [projDim, coneDim, irrChainDim, irrChainDim, ENat.iSup_add]
  refine iSup_le fun l => ?_
  let phi : {Z : Set (Proj k n) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z} →
      {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    fun Z => ⟨Proj.cone Z.1, Proj.cone_mono Z.2.1,
      Proj.isIrreducible_cone Z.2.2.2 Z.2.2.1, Proj.isClosed_cone Z.2.2.2⟩
  have hphi : StrictMono phi := fun a b hab => Proj.cone_ssubset (le_of_lt hab) (ne_of_lt hab)
  let lc := l.map phi hphi
  have hhead : lc.head = phi (l 0) := rfl
  let V0 : {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    ⟨{0}, fun v hv => by rw [Set.mem_singleton_iff] at hv; subst hv; exact Or.inl rfl,
      isIrreducible_singleton_affine 0, isClosed_singleton_zero⟩
  have hrel : V0 < lc.head := by
    rw [hhead]
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Or.inl rfl
    · intro hsub
      obtain ⟨x, hx⟩ := (l 0).2.2.1.1
      have hmem : x.rep ∈ Proj.cone (l 0).1 :=
        Or.inr ⟨x.rep_nonzero, by simpa using hx⟩
      have h0 : x.rep = 0 := by
        have := hsub hmem
        rwa [Set.mem_singleton_iff] at this
      exact x.rep_nonzero h0
  let p : LTSeries {V : Set (Fin (n + 1) → k) // V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} :=
    lc.cons V0 hrel
  have hlen : (p.length : ℕ∞) = (l.length : ℕ∞) + 1 := by
    have h1 : lc.length = l.length := by simp [lc]
    have h2 : p.length = lc.length + 1 := by simp [p]
    rw [h2, h1]
    push_cast
    ring
  rw [← hlen]
  exact le_iSup (fun p : LTSeries {V : Set (Fin (n + 1) → k) //
    V ⊆ Proj.cone Y ∧ IsIrreducible V ∧ IsClosed V} => (p.length : ℕ∞)) p

end Comparison

/-! ## Part 9: the upper bound -/

section UpperBound

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

theorem coord_ne_zero (i : Fin (n + 1)) : Proj.coord (k := k) i ≠ 0 := by
  intro h
  have := Proj.eval_coord (fun j => if j = i then (1 : k) else 0) i
  rw [h] at this
  simpa using this

/-- The affine space over a single point has dimension zero. -/
theorem varietyDim_singleton_zero {m : ℕ} :
    varietyDim k m ({0} : Set (Fin m → k)) = 0 := by
  haveI : Subsingleton {W : Set (Fin m → k) //
      W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W} := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have key : ∀ c : {W : Set (Fin m → k) //
        W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W}, c.1 = {0} := by
      intro c
      obtain ⟨v, hv⟩ := c.2.2.1.1
      have hv0 : v = 0 := by simpa using c.2.1 hv
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hv0 ▸ hv, fun w hw => ?_⟩
      simpa using c.2.1 hw
    rw [key a, key b]
  haveI : Nonempty {W : Set (Fin m → k) //
      W ⊆ ({0} : Set (Fin m → k)) ∧ IsIrreducible W ∧ IsClosed W} :=
    ⟨⟨{0}, subset_refl _, isIrreducible_singleton_affine 0, isClosed_singleton_affine 0⟩⟩
  rw [varietyDim]
  exact Order.krullDim_eq_zero

/-- The cone dimension is bounded by the number of variables. -/
theorem coneDim_le_succ {Y : Set (Proj k n)} (hYc : IsClosed Y) :
    coneDim Y ≤ (n + 1 : ℕ∞) := by
  rcases Set.eq_empty_or_nonempty Y with rfl | hne
  · rw [coneDim_empty]; simp
  · have h1 : varietyDim k (n + 1) (Proj.cone Y) = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
      rw [coneDim]
      exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
    have h2 : Proj.cone Y = MvPolynomial.zeroLocus k (Proj.vanishingIdeal Y) :=
      Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne
    have h3 : varietyDim k (n + 1) (Proj.cone Y) =
        ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) := by
      rw [h2, varietyDim_zeroLocus]
    have h4 : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Proj.vanishingIdeal Y) ≤
        ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
      refine (ringKrullDim_quotient_le (Proj.vanishingIdeal Y)).trans_eq ?_
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    have h5 : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← h1, h3]
      exact h4
    exact WithBot.coe_le_coe.mp h5

/-- **The upper bound**, by strong induction on a bound for `projDim Y`. -/
theorem coneDim_le_projDim_add_one_of_le : ∀ (N : ℕ) (Y : Set (Proj k n)), IsClosed Y →
    IsIrreducible Y → Y.Nonempty → projDim Y ≤ (N : ℕ∞) → coneDim Y ≤ projDim Y + 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro Y hYc hYi hne hbound
    obtain ⟨i, hi⟩ := Proj.exists_coord_notMem_vanishingIdeal (k := k) (n := n) hne
    have hHcl : IsClosed (Proj.hyperplane (k := k) (n := n) i) := Proj.isClosed_hyperplane i
    have hY'cl : IsClosed (Y ∩ Proj.hyperplane (k := k) (n := n) i) := hYc.inter hHcl
    have hYnotH : ¬ (Y ⊆ Proj.hyperplane (k := k) (n := n) i) := by
      intro hsub
      have hmem : Proj.coord (k := k) i ∈ Proj.vanishOnIdeal Y := by
        refine Proj.mem_vanishOnIdeal_iff.mpr ?_
        intro v hv hmem
        have hv0 := (Proj.mem_hyperplane_mk_iff hv).mp (hsub hmem)
        simpa [Proj.eval_coord] using hv0
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal Y] at hmem
      exact hi hmem
    have hYnsub : ∃ y ∈ Proj.cone Y, (MvPolynomial.aeval y) (Proj.coord (k := k) i) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hmem : Proj.coord (k := k) i ∈ Proj.vanishOnIdeal Y := by
        refine Proj.mem_vanishOnIdeal_iff.mpr ?_
        intro v hv hmem
        have hv' : (MvPolynomial.aeval v) (Proj.coord (k := k) i) = 0 := hcon v (Or.inr ⟨hv, hmem⟩)
        rwa [MvPolynomial.aeval_eq_eval] at hv'
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal Y] at hmem
      exact hi hmem
    have hconeYirr : IsIrreducible (Proj.cone Y) := Proj.isIrreducible_cone hYc hYi
    have hconeYcl : IsClosed (Proj.cone Y) := Proj.isClosed_cone hYc
    have hbridge : varietyDim k (n + 1) (Proj.cone Y) = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
      rw [coneDim]
      exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
    by_cases hY'ne : (Y ∩ Proj.hyperplane (k := k) (n := n) i).Nonempty
    · -- ## the hyperplane section is nonempty
      have hAffCl : IsClosed (Proj.cone Y ∩
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i})) := by
        rw [← Proj.cone_inter_hyperplane Y i]
        exact Proj.isClosed_cone hY'cl
      obtain ⟨D, hDfin, hDirr, hDcov, hDanti⟩ :=
        exists_irredDecomposition (affine_dcc (n + 1)) hAffCl
      have h0mem : (0 : Fin (n + 1) → k) ∈ Proj.cone Y ∩
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := by
        refine ⟨Or.inl rfl, ?_⟩
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        have hle : Ideal.span {Proj.coord (k := k) i} ≤
            RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          intro q hq
          rw [Set.mem_singleton_iff] at hq
          subst hq
          show MvPolynomial.aeval (0 : Fin (n + 1) → k) (Proj.coord (k := k) i) = 0
          rw [MvPolynomial.aeval_eq_eval, Proj.eval_coord]
          rfl
        rw [MvPolynomial.aeval_eq_eval]
        exact hle hp
      have hDne : D.Nonempty := by
        rcases Set.eq_empty_or_nonempty D with rfl | h
        · exfalso; rw [hDcov] at h0mem; simp at h0mem
        · exact h
      obtain ⟨W, hWD⟩ := hDne
      have hWirr : IsIrreducible W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).2
      have hWcl : IsClosed W := (isIrredClosed_iff_isIrreducible.mp (hDirr W hWD)).1
      have hWsub : W ⊆ Proj.cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := by
        rw [hDcov]; exact Set.subset_sUnion_of_mem hWD
      have hZmax : ∀ W' : Set (Fin (n + 1) → k),
          W' ⊆ Proj.cone Y → W' ⊆ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) →
          IsIrreducible W' → IsClosed W' → W ⊆ W' → W' ⊆ W := by
        intro W' h1 h2 h3 h4 h5
        have hW'sub : W' ⊆ ⋃₀ D := by rw [← hDcov]; exact fun x hx => ⟨h1 hx, h2 hx⟩
        obtain ⟨W'', hW''D, hW'W''⟩ := IsIrredClosed.exists_subset_of_finite_sUnion
          (isIrredClosed_iff_isIrreducible.mpr ⟨h4, h3⟩) hDfin
          (fun V hV => (isIrredClosed_iff_isIrreducible.mp (hDirr V hV)).1) hW'sub
        rw [hDanti W hWD W'' hW''D (h5.trans hW'W'')]
        exact hW'W''
      have hI18 := hartshorne_exercise_I_1_8 k (n + 1) (Proj.cone Y) (Proj.coord (k := k) i)
        hconeYcl hconeYirr (coord_ne_zero i) hYnsub W (fun x hx => (hWsub hx).1)
        (fun x hx => (hWsub hx).2) hWirr hWcl hZmax
      have hbridge' : varietyDim k (n + 1) (Proj.cone (Y ∩ Proj.hyperplane (k := k) (n := n) i)) =
          ((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) : ℕ∞) : WithBot ℕ∞) := by
        rw [coneDim]
        exact varietyDim_eq_coe_irrChainDim ⟨0, Or.inl rfl⟩
      have hstep1 : coneDim Y ≤ coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 := by
        have hmono : varietyDim k (n + 1) W ≤
            varietyDim k (n + 1) (Proj.cone (Y ∩ Proj.hyperplane (k := k) (n := n) i)) := by
          refine varietyDim_mono ?_
          rw [Proj.cone_inter_hyperplane Y i]
          exact hWsub
        rw [hbridge'] at hmono
        have hI18' : varietyDim k (n + 1) W + 1 = ((coneDim Y : ℕ∞) : WithBot ℕ∞) := by
          rw [hI18, hbridge]
        have hgoal : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤
            ((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) : ℕ∞) : WithBot ℕ∞) + 1 := by
          rw [← hI18']
          exact add_le_add hmono le_rfl
        have hgoal' : ((coneDim Y : ℕ∞) : WithBot ℕ∞) ≤
            (((coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 : ℕ∞)) : WithBot ℕ∞) := by
          simpa using hgoal
        exact WithBot.coe_le_coe.mp hgoal'
      -- ## the projective decomposition of `Y ∩ H`
      obtain ⟨D', hD'fin, hD'irr, hD'cov⟩ :=
        Proj.exists_finite_irred_cover_closed (k := k) (n := n) hY'cl
      have hD'ne : D'.Nonempty := by
        rcases Set.eq_empty_or_nonempty D' with rfl | h
        · exfalso; rw [hD'cov] at hY'ne; simp at hY'ne
        · exact h
      haveI : Nonempty D' := hD'ne.to_subtype
      have hproj' : projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) =
          ⨆ Z : D', projDim (Z : Set (Proj k n)) :=
        projDim_eq_iSup_decomposition hD'fin hD'irr hD'cov
      have hcone' : coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) =
          ⨆ Z : D', coneDim (Z : Set (Proj k n)) :=
        coneDim_eq_iSup_decomposition hD'fin hD'ne hD'irr hD'cov
      have hsmaller : ∀ Z ∈ D', projDim Z + 1 ≤ projDim Y := by
        intro Z hZ
        have hZirr : IsIrreducible Z := (isIrredClosed_iff_isIrreducible.mp (hD'irr Z hZ)).2
        have hZcl : IsClosed Z := (isIrredClosed_iff_isIrreducible.mp (hD'irr Z hZ)).1
        have hZY' : Z ⊆ Y := by
          refine (Set.subset_sUnion_of_mem hZ).trans ?_
          rw [← hD'cov]
          exact Set.inter_subset_left
        have hZne : Z ≠ Y := by
          intro heq
          refine hYnotH ?_
          rw [← heq]
          refine (Set.subset_sUnion_of_mem hZ).trans ?_
          rw [← hD'cov]
          exact Set.inter_subset_right
        exact irrChainDim_add_one_le hZY' hYc hYi hZcl hZirr hZne
      have hIH : ∀ Z : D', coneDim (Z : Set (Proj k n)) ≤ projDim (Z : Set (Proj k n)) + 1 := by
        intro Z
        have hsmall : projDim (Z : Set (Proj k n)) + 1 ≤ projDim Y := hsmaller Z.1 Z.2
        have hZirr : IsIrreducible (Z : Set (Proj k n)) :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).2
        have hZcl : IsClosed (Z : Set (Proj k n)) :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).1
        have hZne : (Z : Set (Proj k n)).Nonempty :=
          (isIrredClosed_iff_isIrreducible.mp (hD'irr Z.1 Z.2)).2.1
        have hNZ' : projDim (Z : Set (Proj k n)) + 1 ≤ ((N : ℕ∞)) := hsmall.trans hbound
        have hNpos : 0 < N := by
          rcases Nat.eq_zero_or_pos N with h0 | h
          · exfalso
            rw [h0] at hNZ'
            simp at hNZ'
          · exact h
        have hNZ : projDim (Z : Set (Proj k n)) ≤ ((N - 1 : ℕ) : ℕ∞) := by
          have h2 : ((N : ℕ∞)) = ((N - 1 : ℕ) : ℕ∞) + 1 := by
            have h3 : N = (N - 1) + 1 := (Nat.sub_add_cancel hNpos).symm
            rw [h3]
            push_cast
            ring
          rw [h2] at hNZ'
          exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hNZ'
        exact IH (N - 1) (Nat.sub_lt hNpos Nat.one_pos) Z.1 hZcl hZirr hZne hNZ
      have hfin : coneDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 ≤ projDim Y + 1 := by
        have h1 : (⨆ Z : D', coneDim (Z : Set (Proj k n))) ≤
            ⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1) :=
          iSup_le fun Z => (hIH Z).trans
            (le_iSup (fun Z : D' => projDim (Z : Set (Proj k n)) + 1) Z)
        have h2 : (⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1)) =
            projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 := by
          rw [← ENat.iSup_add, hproj']
        have h3 : projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1 ≤ projDim Y := by
          rw [hproj', ENat.iSup_add]
          exact iSup_le fun Z => hsmaller Z.1 Z.2
        rw [hcone']
        calc (⨆ Z : D', coneDim (Z : Set (Proj k n))) + 1
            ≤ (⨆ Z : D', (projDim (Z : Set (Proj k n)) + 1)) + 1 := add_le_add h1 le_rfl
          _ = (projDim (Y ∩ Proj.hyperplane (k := k) (n := n) i) + 1) + 1 := by rw [h2]
          _ ≤ projDim Y + 1 := add_le_add h3 le_rfl
      exact hstep1.trans hfin
    · -- ## the hyperplane section is empty
      have hY'empty : Y ∩ Proj.hyperplane (k := k) (n := n) i = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hY'ne
      have hcone0 : Proj.cone Y ∩ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) =
          {0} := by
        rw [← Proj.cone_inter_hyperplane Y i, hY'empty, Proj.cone_empty]
      have hZmax : ∀ W' : Set (Fin (n + 1) → k),
          W' ⊆ Proj.cone Y → W' ⊆ MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) →
          IsIrreducible W' → IsClosed W' → ({0} : Set (Fin (n + 1) → k)) ⊆ W' → W' ⊆ {0} := by
        intro W' h1 h2 h3 h4 h5
        rw [← hcone0]
        exact fun x hx => ⟨h1 hx, h2 hx⟩
      have hsub0 : ({0} : Set (Fin (n + 1) → k)) ⊆ Proj.cone Y := fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl rfl
      have hsub0' : ({0} : Set (Fin (n + 1) → k)) ⊆
          MvPolynomial.zeroLocus k (Ideal.span {Proj.coord (k := k) i}) := fun x hx => by
        rw [Set.mem_singleton_iff] at hx; subst hx
        have hle : Ideal.span {Proj.coord (k := k) i} ≤
            RingHom.ker (MvPolynomial.aeval (0 : Fin (n + 1) → k)) := by
          refine Ideal.span_le.mpr ?_
          intro q hq
          rw [Set.mem_singleton_iff] at hq
          subst hq
          show MvPolynomial.aeval (0 : Fin (n + 1) → k) (Proj.coord (k := k) i) = 0
          rw [MvPolynomial.aeval_eq_eval, Proj.eval_coord]
          rfl
        rw [MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_eq_eval]
        exact hle
      have hI18 := hartshorne_exercise_I_1_8 k (n + 1) (Proj.cone Y) (Proj.coord (k := k) i)
        hconeYcl hconeYirr (coord_ne_zero i) hYnsub ({0} : Set (Fin (n + 1) → k)) hsub0 hsub0'
        (isIrreducible_singleton_affine 0) (isClosed_singleton_affine (0 : Fin (n + 1) → k)) hZmax
      rw [varietyDim_singleton_zero] at hI18
      rw [hbridge] at hI18
      have hone : (coneDim Y : ℕ∞) = 1 := by
        have : ((coneDim Y : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
          rw [← hI18]; norm_num
        exact WithBot.coe_injective this
      rw [hone]
      simp

/-- The irreducible case of the cone dimension formula. -/
theorem coneDim_eq_projDim_add_one_of_irreducible {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) : coneDim Y = projDim Y + 1 := by
  refine le_antisymm ?_ (projDim_add_one_le_coneDim hYc hne)
  refine coneDim_le_projDim_add_one_of_le (n + 1) Y hYc hYi hne ?_
  have h := (projDim_add_one_le_coneDim hYc hne).trans (coneDim_le_succ hYc)
  have h2 : ((n + 1 : ℕ∞)) = ((n : ℕ∞)) + 1 := by simp
  rw [h2] at h
  have hle : projDim Y ≤ ((n : ℕ∞)) :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp h
  refine hle.trans ?_
  exact Nat.cast_le.mpr (Nat.le_succ n)

end UpperBound

/-! ## Part 10: part (b) and the full exercise -/

section Final

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

namespace Proj

theorem isIrreducible_of_isIrreducible_cone {Y : Set (Proj k n)}
    (hne : Y.Nonempty) (h : IsIrreducible (cone Y)) : IsIrreducible Y := by
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have hcover : cone Y ⊆ cone A ∪ cone B := by
    rw [← cone_union]
    exact cone_mono hsub
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp h.2)
    (cone A) (cone B) (isClosed_cone hA) (isClosed_cone hB) hcover
  rcases hsplit with h' | h'
  · refine Or.inl ?_
    intro x hx
    have hx' : x.rep ∈ cone A := h' (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm
  · refine Or.inr ?_
    intro x hx
    have hx' : x.rep ∈ cone B := h' (Or.inr ⟨x.rep_nonzero, by simpa using hx⟩)
    rcases hx' with hzero | ⟨_, hm⟩
    · exact absurd hzero x.rep_nonzero
    · simpa using hm

/-- **(b)**, algebraic form: the cone is irreducible iff `I(Y)` is prime. -/
theorem isIrreducible_cone_iff_isPrime {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hne : Y.Nonempty) :
    IsIrreducible (cone Y) ↔ (vanishingIdeal Y).IsPrime := by
  constructor
  · intro hirr
    have memcone : ∀ f : MvPolynomial (Fin (n + 1)) k,
        f ∈ (MvPolynomial.vanishingIdeal k (cone Y) : Set (MvPolynomial (Fin (n + 1)) k)) ↔
          ∀ v ∈ cone Y, MvPolynomial.aeval v f = 0 :=
      fun f => MvPolynomial.mem_vanishingIdeal_iff
    have h1 : vanishingIdeal Y = MvPolynomial.vanishingIdeal k (cone Y) := by
      refine le_antisymm ?_ ?_
      · rw [vanishingIdeal, Ideal.span_le]
        rintro f ⟨d, hd, hvan⟩
        rw [memcone]
        intro v hv
        rw [MvPolynomial.aeval_eq_eval]
        rcases hv with h0 | ⟨hvne, hmem⟩
        · subst h0
          rcases Nat.eq_zero_or_pos d with hd0 | hdpos
          · subst hd0
            obtain ⟨x, hx⟩ := hne
            rw [eq_zero_of_isHomogeneous_zero hd (hvan x hx)]
            simp
          · exact eval_zero_of_isHomogeneous_pos hdpos hd
        · exact (isZeroAt_mk_iff hd hvne).1 (hvan _ hmem)
      · intro f hf
        have hmem : f ∈ (vanishOnIdeal Y : Set (MvPolynomial (Fin (n + 1)) k)) :=
          (mem_vanishOnIdeal_iff (k := k) (Y := Y) (f := f)).mpr (fun v hv hmem => by
            rw [← MvPolynomial.aeval_eq_eval]
            exact (memcone f).mp hf v (Or.inr ⟨hv, hmem⟩))
        rw [vanishOnIdeal_eq_vanishingIdeal Y] at hmem
        exact hmem
    rw [h1]
    exact vanishingIdeal_isPrime (k := k) (n := n + 1) (isClosed_cone hYc) hirr
  · intro hp
    rw [cone_eq_zeroLocus ((isProjClosed_iff_isClosed Y).mpr hYc) hne]
    exact zeroLocus_irreducible k (n + 1) hp

/-- **(b)**: the cone over `Y` is irreducible iff `Y` is. -/
theorem isIrreducible_cone_iff' {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    IsIrreducible (cone Y) ↔ IsIrreducible Y :=
  ⟨isIrreducible_of_isIrreducible_cone hne, isIrreducible_cone hYc⟩

/-- `I(Y)` is prime iff `Y` is irreducible (for nonempty closed `Y`). -/
theorem vanishingIdeal_isPrime_iff {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    (vanishingIdeal Y).IsPrime ↔ IsIrreducible Y := by
  rw [← isIrreducible_cone_iff_isPrime hYc hne]
  exact isIrreducible_cone_iff' hYc hne

end Proj

/-- **(c)** for an irreducible projective variety. -/
theorem coneDim_eq_projDim_add_one_irreducible {Y : Set (Proj k n)} (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) : coneDim Y = projDim Y + 1 :=
  coneDim_eq_projDim_add_one_of_irreducible hYc hYi hne

/-- **(c)** for an arbitrary projective algebraic set, via its irreducible components. -/
theorem coneDim_eq_projDim_add_one {Y : Set (Proj k n)} (hYc : IsClosed Y) (hne : Y.Nonempty) :
    coneDim Y = projDim Y + 1 := by
  obtain ⟨D, hDfin, hDirr, hDcov⟩ := Proj.exists_finite_irred_cover_closed (k := k) (n := n) hYc
  have hDne : D.Nonempty := by
    rcases Set.eq_empty_or_nonempty D with rfl | h
    · exfalso; rw [hDcov] at hne; simp at hne
    · exact h
  haveI : Nonempty D := hDne.to_subtype
  have hcone : coneDim Y = ⨆ W : D, coneDim (W : Set (Proj k n)) :=
    coneDim_eq_iSup_decomposition hDfin hDne hDirr hDcov
  have hproj : projDim Y = ⨆ W : D, projDim (W : Set (Proj k n)) :=
    projDim_eq_iSup_decomposition hDfin hDirr hDcov
  rw [hcone, hproj, ENat.iSup_add]
  refine iSup_congr fun W => ?_
  exact coneDim_eq_projDim_add_one_irreducible
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).1
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).2
    (isIrredClosed_iff_isIrreducible.mp (hDirr W.1 W.2)).2.1

end Final


end Copy8

namespace Copy8

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-! ### I.2.8 proper: the projective zero locus of a single homogeneous polynomial -/

namespace Proj

/-- The projective zero set of a single polynomial: the set of projective points at which it
vanishes.  For homogeneous `f` this is the zero set of the book. -/
def zeroSet (f : MvPolynomial (Fin (n + 1)) k) : Set (Proj k n) :=
  {x | IsZeroAt f x}

theorem mem_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {x : Proj k n} :
    x ∈ zeroSet f ↔ IsZeroAt f x := Iff.rfl

theorem zeroSet_eq_zeroLocus {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : zeroSet f = zeroLocus ({⟨f, d, hf⟩} : Set (HomogPoly k n)) := by
  ext x
  rw [mem_zeroSet, mem_zeroLocus_iff]
  exact ⟨fun hx => by rintro g rfl; exact hx, fun hx => hx ⟨f, d, hf⟩ rfl⟩

theorem isProjClosed_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : IsProjClosed (zeroSet f) := by
  rw [zeroSet_eq_zeroLocus hf]
  exact isProjClosed_zeroLocus _

theorem isClosed_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) : IsClosed (zeroSet f) :=
  (isProjClosed_iff_isClosed _).mp (isProjClosed_zeroSet hf)

/-- The affine cone over the projective hypersurface `Z(f)` is the affine hypersurface `V(f)`.
This is where the classical point model of `P^n` (lines through the origin) is used. -/
theorem cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) :
    cone (zeroSet f) = MvPolynomial.zeroLocus k (Ideal.span {f}) := by
  ext v
  rw [MvPolynomial.mem_zeroLocus_iff]
  simp only [MvPolynomial.aeval_eq_eval]
  constructor
  · rintro (rfl | ⟨hvne, hvt⟩) g hg
    · rw [Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [map_mul, Proj.eval_zero_of_isHomogeneous_pos hd hf, zero_mul]
    · rw [Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [map_mul, (isZeroAt_mk_iff hf hvne).mp hvt, zero_mul]
  · intro hv
    have hfv : (eval v) f = 0 := hv f (Ideal.mem_span_singleton_self f)
    rcases eq_or_ne v 0 with rfl | hvne
    · exact Or.inl rfl
    · exact Or.inr ⟨hvne, (isZeroAt_mk_iff hf hvne).mpr hfv⟩

/-- The affine hypersurface `V(f) ⊆ A^{n+1}` has dimension `n`. -/
theorem varietyDim_cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) :
    varietyDim k (n + 1) (cone (zeroSet f)) =
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) := by
  rw [cone_zeroSet hd hf, varietyDim_zeroLocus]

/-- `ringKrullDim k[x₀,…,xₙ] = n + 1`. -/
theorem ringKrullDim_mvPolynomial (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = (s : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- For irreducible homogeneous `f` of positive degree, the cone over `Z(f)` has chain
dimension `n`: it is the affine hypersurface `V(f)`, whose coordinate ring
`k[x₀,…,xₙ]/(f)` has dimension `n`. -/
theorem irrChainDim_cone_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    irrChainDim (cone (zeroSet f)) = (n : ℕ∞) := by
  have hfne : f ≠ 0 := hirr.ne_zero
  haveI hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hfne).mpr (irreducible_iff_prime.mp hirr)
  have hne : (cone (zeroSet f)).Nonempty := ⟨0, Or.inl rfl⟩
  have hcoe : varietyDim k (n + 1) (cone (zeroSet f)) =
      ((irrChainDim (cone (zeroSet f)) : ℕ∞) : WithBot ℕ∞) :=
    varietyDim_eq_coe_irrChainDim hne
  have hring : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) + 1 =
      (n : WithBot ℕ∞) + 1 := by
    rw [MvPolynomial.ringKrullDim_quotient_span_singleton k hfne, ringKrullDim_mvPolynomial]
    push_cast
    ring
  have h1 : ((irrChainDim (cone (zeroSet f)) : ℕ∞) : WithBot ℕ∞) + 1 =
      ((n : ℕ∞) : WithBot ℕ∞) + 1 := by
    rw [← hcoe, varietyDim_cone_zeroSet hd hf, hring]
    norm_num
  exact WithBot.coe_injective (ENat.WithBot.add_one_cancel.mp h1)

/-- **I.2.8, `⇐` direction.**  The zero set of an irreducible homogeneous polynomial of positive
degree has dimension `n - 1` (stated as `dim + 1 = n`). -/
theorem projDim_zeroSet {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hd : 0 < d)
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) (hne : (zeroSet f).Nonempty) :
    projDim (zeroSet f) + 1 = (n : ℕ∞) := by
  have hcd := coneDim_eq_projDim_add_one (isClosed_zeroSet hf) hne
  rw [coneDim] at hcd
  rw [← hcd]
  exact irrChainDim_cone_zeroSet hd hf hirr

end Proj


/-! ### The `⇒` direction: a variety of dimension `n-1` is a hypersurface -/

/-- The top homogeneous component of a product is the product of the top homogeneous
components.  (Pure coefficient bookkeeping in a commutative semiring.) -/
theorem homogeneousComponent_mul_totalDegree {R : Type*} [CommSemiring R]
    (a b : MvPolynomial (Fin (n + 1)) R) :
    homogeneousComponent (a.totalDegree + b.totalDegree) (a * b) =
      homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b := by
  ext u
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hu : Finsupp.degree u = a.totalDegree + b.totalDegree
  · rw [if_pos hu]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases hv : x.1 ∈ a.support
    · by_cases hw : x.2 ∈ b.support
      · have hv' : Finsupp.degree x.1 ≤ a.totalDegree := MvPolynomial.le_totalDegree hv
        have hw' : Finsupp.degree x.2 ≤ b.totalDegree := MvPolynomial.le_totalDegree hw
        have hadd : Finsupp.degree x.1 + Finsupp.degree x.2 =
            a.totalDegree + b.totalDegree := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hx, hu]
        rw [if_pos (by omega), if_pos (by omega)]
      · have h0 : MvPolynomial.coeff x.2 b = 0 := Finsupp.notMem_support_iff.mp hw
        simp [h0, MvPolynomial.coeff_homogeneousComponent]
    · have h0 : MvPolynomial.coeff x.1 a = 0 := Finsupp.notMem_support_iff.mp hv
      simp [h0, MvPolynomial.coeff_homogeneousComponent]
  · rw [if_neg hu]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hv : MvPolynomial.coeff x.1 (homogeneousComponent a.totalDegree a) = 0
    · simp [hv]
    · by_cases hw : MvPolynomial.coeff x.2 (homogeneousComponent b.totalDegree b) = 0
      · simp [hw]
      · exfalso
        apply hu
        have h1 : Finsupp.degree x.1 = a.totalDegree := by
          by_contra h
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h] at hv
          exact hv rfl
        have h2 : Finsupp.degree x.2 = b.totalDegree := by
          by_contra h
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h] at hw
          exact hw rfl
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx, map_add, h1, h2]

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {R : Type*} [CommSemiring R]
    {h : MvPolynomial (Fin (n + 1)) R} (hh : h ≠ 0) :
    homogeneousComponent h.totalDegree h ≠ 0 := by
  intro hzero
  have hne : h.support.Nonempty := MvPolynomial.support_nonempty.mpr hh
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup h.support hne (fun s => Finsupp.degree s)
  have hdeg : Finsupp.degree d = h.totalDegree := by
    rw [← hsup]
    rfl
  have hcoeff : MvPolynomial.coeff d h ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h0 : MvPolynomial.coeff d (homogeneousComponent h.totalDegree h) = 0 := by simp [hzero]
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg] at h0
  exact hcoeff h0

/-! ### The `⇒` direction: a projective variety of dimension `n-1` is a hypersurface -/

section Hypersurface

variable (Y : Set (Proj k n))

/-- **I.2.8, `⇒` direction.**  Let `Y ⊆ P^n` be a projective variety (nonempty, irreducible,
closed) with `dim Y + 1 = n`.  Then `Y = Z(f)` for a single irreducible homogeneous polynomial
`f` of positive degree.

Route: the affine cone `C(Y) = V(I(Y)) ⊆ A^{n+1}` is irreducible of dimension `n = m - 1`; the
ideal `I(Y)` is prime.  Choosing `0 ≠ t ∈ I(Y)` and a prime `q ⊆ I(Y)` minimal over `(t)`, the
principal ideal theorem and the dimension formula for cones give `dim A^{n+1}/q = dim A^{n+1}/I(Y)`,
so `V(I(Y)) ⊆ V(q)` are irreducible closed of equal chain dimension, forcing `V(q) = V(I(Y))` and
hence `q = I(Y)`: thus `ht I(Y) = 1`.  Over the UFD `k[x₀,…,xₙ]` a height-one prime is principal,
`I(Y) = (h)`, and since `I(Y)` is homogeneous, `h` may be taken homogeneous of positive degree. -/
theorem exists_irreducible_homogeneous_of_projDim
    (hYc : IsClosed Y) (hYi : IsIrreducible Y) (hne : Y.Nonempty)
    (hdim : projDim Y + 1 = (n : ℕ∞)) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
      0 < d ∧ f.IsHomogeneous d ∧ Irreducible f ∧ Y = Proj.zeroSet f := by
  classical
  set p : Ideal (MvPolynomial (Fin (n + 1)) k) := Proj.vanishingIdeal Y with hpdef
  haveI hp : p.IsPrime := Proj.vanishingIdeal_isPrime_of_isIrreducible hYi
  have hcone : Proj.cone Y = MvPolynomial.zeroLocus k p :=
    Proj.cone_eq_zeroLocus ((Proj.isProjClosed_iff_isClosed Y).mpr hYc) hne
  have hcone_ne : (Proj.cone Y).Nonempty := ⟨0, Or.inl rfl⟩
  have hconeDim : irrChainDim (Proj.cone Y) = (n : ℕ∞) :=
    (coneDim_eq_projDim_add_one hYc hne).trans hdim
  have hvd : varietyDim k (n + 1) (Proj.cone Y) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [varietyDim_eq_coe_irrChainDim hcone_ne, hconeDim]
  have hring : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ p) = (n : WithBot ℕ∞) := by
    rw [← varietyDim_zeroLocus k (n + 1) p, ← hcone]
    exact hvd
  -- `I(Y) ≠ 0`, since otherwise the cone would be all of `A^{n+1}`
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h1 : varietyDim k (n + 1) (Proj.cone Y) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hcone, hbot, MvPolynomial.zeroLocus_bot, Set.top_eq_univ, varietyDim_univ]
    rw [hvd] at h1
    have h2 : (n : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
    have h3 : n = n + 1 := ENat.natCast_inj.mp h2
    omega
  obtain ⟨t, htp, ht0⟩ : ∃ t, t ∈ p ∧ t ≠ 0 := by
    have hlt : (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) < p :=
      lt_of_le_of_ne bot_le (Ne.symm hpne)
    obtain ⟨t, htp, htbot⟩ := SetLike.exists_of_lt hlt
    exact ⟨t, htp, by simpa using htbot⟩
  -- a prime `q ⊆ I(Y)` minimal over `(t)`, of height one
  obtain ⟨q, hqmin, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := Ideal.span {t}) (J := p)
      ((Ideal.span_singleton_le_iff_mem p).mpr htp)
  haveI hqprime : q.IsPrime := hqmin.isPrime
  have hqht : q.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes ht0 hqmin
  have htu : ¬ IsUnit t := fun hu => hp.ne_top (Ideal.eq_top_of_isUnit_mem p htp hu)
  have hqdim : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) + 1 =
      ringKrullDim (MvPolynomial (Fin (n + 1)) k) :=
    ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes k ht0 htu hqmin
  have hqdim' : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) = (n : WithBot ℕ∞) := by
    rw [Proj.ringKrullDim_mvPolynomial] at hqdim
    have h' : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) + 1 =
        (n : WithBot ℕ∞) + 1 := by
      rw [hqdim]
      push_cast
      ring
    exact ENat.WithBot.add_one_cancel.mp h'
  -- the affine varieties `V(I(Y)) ⊆ V(q)` are irreducible closed of equal chain dimension `n`
  have hZirr : IsIrreducible (MvPolynomial.zeroLocus k p) :=
    zeroLocus_irreducible k (n + 1) hp
  have hZcl : IsClosed (MvPolynomial.zeroLocus k p) := isClosed_zeroLocus k (n + 1) p
  have hWirr : IsIrreducible (MvPolynomial.zeroLocus k q) :=
    zeroLocus_irreducible k (n + 1) hqprime
  have hWcl : IsClosed (MvPolynomial.zeroLocus k q) := isClosed_zeroLocus k (n + 1) q
  have hZW : MvPolynomial.zeroLocus k p ⊆ MvPolynomial.zeroLocus k q :=
    MvPolynomial.zeroLocus_anti_mono hqle
  have hZne : (MvPolynomial.zeroLocus k p).Nonempty := by
    rw [← hcone]; exact hcone_ne
  have hWne : (MvPolynomial.zeroLocus k q).Nonempty := hZne.mono hZW
  have hdimZ : irrChainDim (MvPolynomial.zeroLocus k p) = (n : ℕ∞) := by
    have h1 : varietyDim k (n + 1) (MvPolynomial.zeroLocus k p) = ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [varietyDim_zeroLocus]; exact hring
    have h2 := varietyDim_eq_coe_irrChainDim hZne
    rw [h1] at h2
    exact WithBot.coe_injective h2.symm
  have hdimW : irrChainDim (MvPolynomial.zeroLocus k q) = (n : ℕ∞) := by
    have h1 : varietyDim k (n + 1) (MvPolynomial.zeroLocus k q) = ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [varietyDim_zeroLocus]; exact hqdim'
    have h2 := varietyDim_eq_coe_irrChainDim hWne
    rw [h1] at h2
    exact WithBot.coe_injective h2.symm
  have hp1 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k p) = p := by
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hp.radical]
  have hq1 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k q) = q := by
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hqprime.radical]
  -- a strictly larger irreducible closed set has strictly larger chain dimension
  have hqp : q = p := by
    by_contra hne'
    have hZneW : MvPolynomial.zeroLocus k p ≠ MvPolynomial.zeroLocus k q := by
      intro heq
      apply hne'
      rw [← hp1, ← hq1, heq]
    have hstep := irrChainDim_add_one_le hZW hWcl hWirr hZcl hZirr hZneW
    rw [hdimZ, hdimW] at hstep
    exact absurd ((ENat.add_one_le_iff (by simp)).mp hstep) (lt_irrefl _)
  have hpht : p.height = 1 := by rw [← hqp]; exact hqht
  -- over a UFD a height-one prime is principal
  obtain ⟨h, hh⟩ :=
    (Submodule.isPrincipal_iff p).mp (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hpht)
  have hhne : h ≠ 0 := by
    intro h0
    apply hpne
    rw [hh, h0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hhmem : h ∈ p := by
    rw [hh]
    exact Submodule.mem_span_singleton_self h
  -- each homogeneous component of `h` lies in `p = (h)`
  have hcomp : ∀ i, homogeneousComponent i h ∈ p := fun i =>
    (MvPolynomial.mem_iff_homogeneousComponent_mem (I := p)
      (Proj.vanishingIdeal_isHomogeneous Y) h).mp hhmem i
  obtain ⟨a, ha⟩ : ∃ a, homogeneousComponent h.totalDegree h = a * h := by
    have h1 := hcomp h.totalDegree
    rw [hh] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    exact ⟨c, by rw [← hc, smul_eq_mul]⟩
  have hDne : homogeneousComponent h.totalDegree h ≠ 0 :=
    homogeneousComponent_totalDegree_ne_zero hhne
  have ha0 : a ≠ 0 := by
    intro h0
    exact hDne (by rw [ha, h0, zero_mul])
  -- the top component of `a * h` is `a * h_D`; for `h_D` to be homogeneous `a` must be constant
  have ha_const : a.totalDegree = 0 := by
    by_contra hk
    have hkey := homogeneousComponent_mul_totalDegree a h
    rw [← ha] at hkey
    have hzero : homogeneousComponent (a.totalDegree + h.totalDegree)
        (homogeneousComponent h.totalDegree h) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem
        (homogeneousComponent_isHomogeneous h.totalDegree h), if_neg (by omega)]
    rw [hzero] at hkey
    exact mul_ne_zero (homogeneousComponent_totalDegree_ne_zero ha0)
      (homogeneousComponent_totalDegree_ne_zero hhne) hkey.symm
  obtain ⟨c, hc⟩ : ∃ c : k, a = MvPolynomial.C c := by
    obtain h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ha_const
    exact ⟨_, h⟩
  have hcne : c ≠ 0 := by
    intro h0
    exact ha0 (by rw [hc, h0, MvPolynomial.C_0])
  have hhhom : h.IsHomogeneous h.totalDegree := by
    have h1 : MvPolynomial.C c⁻¹ * homogeneousComponent h.totalDegree h = h := by
      rw [ha, hc, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hcne, MvPolynomial.C_1,
        one_mul]
    have h2 : (MvPolynomial.C c⁻¹ * homogeneousComponent h.totalDegree h).IsHomogeneous
        h.totalDegree := by
      simpa using (MvPolynomial.isHomogeneous_C _ c⁻¹).mul
        (homogeneousComponent_isHomogeneous h.totalDegree h)
    rwa [h1] at h2
  have hDpos : 0 < h.totalDegree := by
    rcases Nat.eq_zero_or_pos h.totalDegree with h0 | hpos
    · exfalso
      have hconst : h = MvPolynomial.C (MvPolynomial.coeff 0 h) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
      have hcoeff_ne : MvPolynomial.coeff 0 h ≠ 0 := by
        intro hc0
        exact hhne (by rw [hconst, hc0, MvPolynomial.C_0])
      have hunit : IsUnit h := by
        rw [hconst]
        exact IsUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k)
          (isUnit_iff_ne_zero.mpr hcoeff_ne)
      apply hp.ne_top
      rw [hh]
      exact Ideal.span_singleton_eq_top.mpr hunit
    · exact hpos
  have hprime : Prime h := by
    refine ⟨hhne, ?_, ?_⟩
    · intro hu
      exact hp.ne_top (by rw [hh]; exact Ideal.span_singleton_eq_top.mpr hu)
    · intro a b hab
      have h1 : a * b ∈ p := by
        rw [hh]
        exact Ideal.mem_span_singleton.mpr hab
      rcases hp.mem_or_mem h1 with h2 | h2
      · exact Or.inl (by rw [hh] at h2; exact Ideal.mem_span_singleton.mp h2)
      · exact Or.inr (by rw [hh] at h2; exact Ideal.mem_span_singleton.mp h2)
  refine ⟨h.totalDegree, h, hDpos, hhhom, hprime.irreducible, ?_⟩
  -- `Y = Z(h)`
  ext x
  constructor
  · intro hx
    have hmem : h ∈ Proj.vanishOnIdeal Y := by
      rw [Proj.vanishOnIdeal_eq_vanishingIdeal]; exact hhmem
    have hx' : Proj.mk x.rep x.rep_nonzero = x := Projectivization.mk_rep x
    exact Proj.mem_vanishOnIdeal_iff.mp hmem x.rep x.rep_nonzero (by rwa [← hx'] at hx)
  · intro hx
    have hx' : x ∈ Proj.zeroLocus (Proj.vanishingForms Y) := by
      rw [Proj.mem_zeroLocus_iff]
      rintro ⟨g, dg, hg⟩ hgmem
      have hgmem' : g ∈ p := hgmem
      rw [hh] at hgmem'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgmem'
      show MvPolynomial.eval x.rep g = 0
      rw [← hc, smul_eq_mul, map_mul,
        show MvPolynomial.eval x.rep h = 0 from hx, mul_zero]
    rwa [Proj.zeroLocus_vanishingForms_eq Y hYc] at hx'

/-- Hartshorne's terminology in I.2.8: `Y` is a *hypersurface* in `P^n` when it is the zero set of a
single irreducible homogeneous polynomial of positive degree. -/
def IsHypersurface (Y : Set (Proj k n)) : Prop :=
  ∃ (d : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
    0 < d ∧ f.IsHomogeneous d ∧ Irreducible f ∧ Y = Proj.zeroSet f

/-- **Hartshorne (1977), *Algebraic Geometry*, Exercise I.2.8.**

A projective variety `Y ⊆ P^n` has dimension `n - 1` if and only if it is the zero set of a single
irreducible homogeneous polynomial `f` of positive degree.

Here `dim Y = n - 1` is rendered as `projDim Y + 1 = n` in `ℕ∞`; the two are equivalent for
`n ≥ 1`, and the chosen form is the correct one also for `n = 0`, where `P^0` is a point, no
projective zero set of a positive-degree homogeneous polynomial is nonempty, and neither side
holds. -/
theorem hartshorne_exercise_I_2_8 (Y : Set (Proj k n)) (hYc : IsClosed Y) (hYi : IsIrreducible Y)
    (hne : Y.Nonempty) :
    (projDim Y + 1 = (n : ℕ∞)) ↔ IsHypersurface Y := by
  constructor
  · intro hdim
    exact exists_irreducible_homogeneous_of_projDim Y hYc hYi hne hdim
  · rintro ⟨d, f, hd, hf, hirr, rfl⟩
    exact Proj.projDim_zeroSet hd hf hirr hne

/-- `(n - 1 : ℕ)` cast to `ℕ∞`, plus one, is `n` (for `n ≥ 1`). -/
theorem natCast_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) := by
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← h]
  push_cast
  ring

/-- **I.2.8** in the literal book wording `dim Y = n - 1` (for `n ≥ 1`). -/
theorem hartshorne_exercise_I_2_8_sub (hn : 1 ≤ n) (Y : Set (Proj k n)) (hYc : IsClosed Y)
    (hYi : IsIrreducible Y) (hne : Y.Nonempty) :
    (projDim Y = ((n - 1 : ℕ) : ℕ∞)) ↔ IsHypersurface Y := by
  rw [← hartshorne_exercise_I_2_8 Y hYc hYi hne]
  constructor
  · intro h
    rw [h]
    exact natCast_sub_one_add_one hn
  · intro h
    rw [← natCast_sub_one_add_one hn] at h
    exact WithTop.add_right_cancel (by simp : (1 : ℕ∞) ≠ ⊤) h

end Hypersurface
/-! ### Axiom audit -/


end Copy8


set_option linter.unusedSectionVars false

/-
Hartshorne (1977), *Algebraic Geometry*, Chapter I, §2, Exercise I.2.15.

SOURCE STATEMENT (verbatim, cross-checked against the local OCR of the book
`.scratch/reference/hartshorne-1977.txt` and the public rendering
<https://hartshorne-ag-solutions.wikidot.com/chapter-1-section-2>):

  2.15. The Quadric Surface in P³ (Fig. 2).  Consider the surface Q (a surface is a variety of
  dimension 2) in P³ defined by the equation xy - zw = 0.
  (a) Show that Q is equal to the Segre embedding of P¹ × P¹ in P³, for suitable choice of
      coordinates.
  (b) Show that Q contains two families of lines (a line is a linear variety of dimension 1)
      {L_t}, {M_t}, each parametrized by t ∈ P¹, with the properties that if L_t ≠ L_s then
      L_t ∩ L_s = ∅; if M_t ≠ M_s, M_t ∩ M_s = ∅, and for all t,u, L_t ∩ M_u = one point.
  (c) Show that Q contains other curves besides these lines, and deduce that the Zariski
      topology on Q is not homeomorphic via ψ to the product topology on P¹ × P¹ (where each
      P¹ has its Zariski topology).

Standing hypotheses of Chapter I: `k` is an algebraically closed field; `P^n` is the classical
projective space of lines through the origin in `k^{n+1}` (p. 10); a variety is an irreducible
algebraic set; a curve is a variety of dimension 1; dimension is Hartshorne's chain dimension
(I.1, p. 6).  The Segre embedding is `ψ(a₀:a₁; b₀:b₁) = (a₀b₀ : a₀b₁ : a₁b₀ : a₁b₁)`
(Ex. I.2.14, lexicographic order of the `z_{ij}`).

WHAT IS FORMALIZED (`P k n` below is the genuine classical point set, not `Proj` of a graded
ring; all of `P^n`, its Zariski topology, vanishing of homogeneous forms, closed sets =
zero loci and the vanishing-ideal dictionary are copied from the accepted I.2.5 development):

* `segre : P¹ → P¹ → P³`, well defined on projective classes (`segre_mk`), injective
  (`segre_inj`); **part (a)** `range_segre : range ψ = Q`, where
  `quadric = zeroLocus {X₀X₃ - X₁X₂}` (`quadric_exists_segre` is the surjectivity onto `Q`).
  `exists_coordinates_quadric` upgrades this to the book's literal equation `xy - zw = 0`:
  the projectivity of `P³` induced by the coordinate permutation `(x:y:z:w) = (z₀₀:z₁₁:z₀₁:z₁₀)`
  (`permMap`, `permMap_image_zeroLocus`) carries the Segre image onto
  `zeroLocus {X₀X₁ - X₂X₃}`.
* **Part (b)** `L t = ψ(P¹ × {t})`, `M t = ψ({t} × P¹)`; `L_subset_quadric`, `M_subset_quadric`;
  `IsProjectiveLine (L t)`, `IsProjectiveLine (M t)` — each family member is the set of points
  of a linear subspace of dimension two of `k⁴`, i.e. a linear variety of dimension `2 - 1 = 1`
  (`L_isProjectiveLine`, `M_isProjectiveLine`, with `finrank_span_vecL`, `finrank_span_vecM`);
  `L_eq_iff : L t = L s ↔ t = s`; `L_disjoint : t ≠ s → Disjoint (L t) (L s)`;
  `M_disjoint`; `L_inter_M : L t ∩ M u = {ψ(u,t)}` — exactly one point.
* **Part (c)** `conic = ψ(Δ)` where `Δ` is the diagonal of `P¹ × P¹`; `isClosed_conic`
  (indeed `conic = quadric ∩ {x₁ = x₂}`, `conic_eq_quadric_inter_hyperplane`);
  `irreducible_conic`; `dim_conic : DimEq conic 1` — `conic` is a variety of dimension one, a
  curve; `conic_ne_L`, `conic_ne_M` — it is none of the lines.  Finally
  `diag_not_closed : ¬ IsClosed Δ` for the *product* topology on `P¹ × P¹` (because any two
  nonempty Zariski-open subsets of `P¹` meet, `P1_open_inter_nonempty`), while its image `conic`
  is closed in the Zariski topology of `Q`; hence
  `not_homeomorph_product : ¬ ∀ S, IsClosed S ↔ IsClosed (ψ '' S)`: the Zariski topology on `Q`
  is not homeomorphic via `ψ` to the product topology on `P¹ × P¹`.
  `hartshorne_I_2_15` collects every clause in one statement.

Axiom audit at the end of the file: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Hartshorne77.Ex_I_2_15

noncomputable section

abbrev Vec (k : Type*) (n : ℕ) : Type _ := Fin (n + 1) → k

variable {k : Type*} [Field k] {n : ℕ}

def projRel (v w : {v : Vec k n // v ≠ 0}) : Prop := ∃ c : k, c ≠ 0 ∧ v.1 = c • w.1

theorem projRel_equivalence : Equivalence (projRel (k := k) (n := n)) where
  refl v := ⟨1, one_ne_zero, by simp⟩
  symm := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  trans := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨c, hc, h₁⟩ ⟨d, hd, h₂⟩
    exact ⟨c * d, mul_ne_zero hc hd, by rw [h₁, h₂, smul_smul]⟩

def projSetoid (k : Type*) [Field k] (n : ℕ) : Setoid {v : Vec k n // v ≠ 0} :=
  ⟨projRel, projRel_equivalence⟩

def P (k : Type*) [Field k] (n : ℕ) : Type _ := Quotient (projSetoid k n)

namespace P

def mk {v : Vec k n} (hv : v ≠ 0) : P k n := Quotient.mk _ ⟨v, hv⟩

theorem mk_eq_mk_iff {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (n := n) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w :=
  Quotient.eq

theorem mk_eq_mk_iff' {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (n := n) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ c • v = w := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem mk_smul {c : k} (hc : c ≠ 0) {v : Vec k n} (hv : v ≠ 0) :
    mk (k := k) (n := n) (show c • v ≠ 0 from smul_ne_zero hc hv) = mk hv := by
  rw [mk_eq_mk_iff]
  exact ⟨c, hc, rfl⟩

theorem mk_smul' {c : k} (hc : c ≠ 0) {v : Vec k n} (hv : v ≠ 0) (hcv : c • v ≠ 0) :
    mk (k := k) (n := n) hcv = mk hv :=
  mk_smul hc hv

theorem exists_mk (p : P k n) : ∃ (v : Vec k n) (hv : v ≠ 0), mk hv = p := by
  induction p using Quotient.inductionOn with
  | h x => exact ⟨x.1, x.2, rfl⟩

def Line (k : Type*) [Field k] (n : ℕ) : Type _ :=
  {L : Submodule k (Vec k n) // Module.finrank k L = 1}

namespace Line

def ofVec (v : Vec k n) (hv : v ≠ 0) : Line k n :=
  ⟨Submodule.span k {v}, finrank_span_singleton hv⟩

theorem exists_ne_zero (L : Line k n) : ∃ v : Vec k n, v ∈ L.1 ∧ v ≠ 0 := by
  have hne : L.1 ≠ ⊥ := by
    intro h
    have h0 : Module.finrank k L.1 = 0 := by rw [h]; simp
    have h2 := L.2
    rw [h0] at h2
    exact zero_ne_one h2
  exact L.1.exists_mem_ne_zero_of_ne_bot hne

theorem span_eq_of_mem (L : Line k n) {v : Vec k n} (hv : v ∈ L.1) (hv0 : v ≠ 0) :
    Submodule.span k {v} = L.1 := by
  have hle : Submodule.span k {v} ≤ L.1 := Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)
  have h1 : Module.finrank k (Submodule.span k {v}) = 1 := finrank_span_singleton hv0
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, L.2])

theorem ofVec_eq_iff {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    ofVec v hv = ofVec w hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro h
    have hspan : Submodule.span k {v} = Submodule.span k ({w} : Set (Vec k n)) :=
      congrArg Subtype.val h
    have hwmem : v ∈ Submodule.span k ({w} : Set (Vec k n)) := by
      rw [← hspan]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).1 hwmem
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    rw [zero_smul] at hc
    exact hv hc.symm
  · rintro ⟨c, hc, h⟩
    apply Subtype.ext
    have hv' : v ∈ Submodule.span k ({w} : Set (Vec k n)) := by
      rw [h]
      exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    have hw' : w ∈ Submodule.span k ({v} : Set (Vec k n)) := by
      have hwv : w = c⁻¹ • v := by
        rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hwv]
      exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (by simp))
    exact le_antisymm (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv'))
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hw'))

end Line

/-- The chosen nonzero point of a line, as a vector. -/
def LineRep (L : Line k n) : Vec k n := (Line.exists_ne_zero L).choose

theorem LineRep_mem (L : Line k n) : LineRep L ∈ L.1 := ((Line.exists_ne_zero L).choose_spec).1

theorem LineRep_ne_zero (L : Line k n) : LineRep L ≠ 0 := ((Line.exists_ne_zero L).choose_spec).2

def ofLine (L : Line k n) : P k n := mk (LineRep_ne_zero L)

theorem ofLine_eq_mk (L : Line k n) {v : Vec k n} (hv : v ∈ L.1) (hv0 : v ≠ 0) :
    ofLine L = mk hv0 := by
  have h1 : ofLine L = mk (LineRep_ne_zero L) := rfl
  rw [h1, mk_eq_mk_iff]
  have hspan : Submodule.span k {LineRep L} = Submodule.span k ({v} : Set (Vec k n)) := by
    rw [Line.span_eq_of_mem L (LineRep_mem L) (LineRep_ne_zero L),
      Line.span_eq_of_mem L hv hv0]
  have hmem : LineRep L ∈ Submodule.span k ({v} : Set (Vec k n)) := by
    rw [← hspan]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).1 hmem
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  exact LineRep_ne_zero L hc.symm

def toLine : P k n → Line k n :=
  Quotient.lift (fun x : {v : Vec k n // v ≠ 0} => Line.ofVec x.1 x.2) (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    exact (Line.ofVec_eq_iff hv hw).2 ⟨c, hc, h⟩)

theorem toLine_mk {v : Vec k n} (hv : v ≠ 0) :
    toLine (mk hv) = Line.ofVec v hv :=
  rfl

theorem toLine_mk_span {v : Vec k n} (hv : v ≠ 0) :
    (toLine (mk hv)).1 = Submodule.span k {v} := rfl

def equivLine : P k n ≃ Line k n where
  toFun := toLine
  invFun := ofLine
  left_inv := by
    intro p
    obtain ⟨v, hv, rfl⟩ := exists_mk p
    rw [toLine_mk]
    exact ofLine_eq_mk (Line.ofVec v hv) (Submodule.subset_span (by simp)) hv
  right_inv := by
    intro L
    have h1 : toLine (ofLine L) = Line.ofVec (LineRep L) (LineRep_ne_zero L) := by
      rw [ofLine, toLine_mk]
    rw [h1]
    exact Subtype.ext (Line.span_eq_of_mem L (LineRep_mem L) (LineRep_ne_zero L))

end P


/-! ## 2. Vanishing of homogeneous polynomials at projective points -/

/-- The polynomial ring `S = k[x_0,…,x_n]`. -/
abbrev Poly (k : Type*) [CommSemiring k] (n : ℕ) : Type _ := MvPolynomial (Fin (n + 1)) k

namespace P

variable {f g : Poly k n} {d : ℕ}

/-- **Homogeneity of evaluation**: for a homogeneous polynomial `f` of degree `d` and any
scalar `c`, `f(c·v) = c^d f(v)`.  This is what makes "`f` vanishes at the projective point"
independent of the chosen representative of the point. -/
theorem eval_smul_of_isHomogeneous (hf : f.IsHomogeneous d) (c : k) (v : Vec k n) :
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

/-- `f` vanishes at the projective point `p` if it vanishes at every representative of `p`.
(For homogeneous `f` this is independent of the representative, see
`formVanishesAt_mk_iff`.) -/
def FormVanishesAt (f : Poly k n) (p : P k n) : Prop :=
  ∀ (v : Vec k n) (hv : v ≠ 0), mk hv = p → MvPolynomial.eval v f = 0

theorem formVanishesAt_mk {v : Vec k n} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) → MvPolynomial.eval v f = 0 :=
  fun h => h v hv rfl

/-- Vanishing of a homogeneous polynomial at a projective point is well defined: it does not
depend on the representative. -/
theorem formVanishesAt_mk_iff (hf : f.IsHomogeneous d) {v : Vec k n} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) ↔ MvPolynomial.eval v f = 0 := by
  refine ⟨formVanishesAt_mk hv, ?_⟩
  intro h w hw hwp
  obtain ⟨c, hc, hwv⟩ := (mk_eq_mk_iff hw hv).1 hwp
  rw [hwv, eval_smul_of_isHomogeneous hf, h, mul_zero]

/-- The projective zero locus (Hartshorne's `V(T)`) of a set `T` of polynomials: the set of
points at which every polynomial of `T` vanishes.  For sets of *homogeneous* polynomials this
is Hartshorne's `V(T) ⊆ P^n`. -/
def zeroLocus (T : Set (Poly k n)) : Set (P k n) :=
  {p | ∀ f ∈ T, FormVanishesAt f p}

@[simp]
theorem mem_zeroLocus_iff {T : Set (Poly k n)} (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d)
    {v : Vec k n} (hv : v ≠ 0) :
    mk hv ∈ zeroLocus T ↔ ∀ f ∈ T, MvPolynomial.eval v f = 0 := by
  constructor
  · intro h f hf
    exact formVanishesAt_mk hv (h f hf)
  · intro h f hf
    obtain ⟨d, hd⟩ := hT f hf
    rw [formVanishesAt_mk_iff hd hv]
    exact h f hf

theorem zeroLocus_empty : zeroLocus (∅ : Set (Poly k n)) = Set.univ := by
  ext p
  simp [zeroLocus]

theorem zeroLocus_mono {T T' : Set (Poly k n)} (h : T ⊆ T') :
    zeroLocus T' ⊆ zeroLocus T :=
  fun _ hp f hf => hp f (h hf)

theorem zeroLocus_iUnion {ι : Type*} (T : ι → Set (Poly k n)) :
    zeroLocus (⋃ i, T i) = ⋂ i, zeroLocus (T i) := by
  ext p
  simp only [zeroLocus, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_union (T T' : Set (Poly k n)) :
    zeroLocus (T ∪ T') = zeroLocus T ∩ zeroLocus T' := by
  ext p
  simp only [zeroLocus, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

end P


namespace P

/-- The zero locus of the constant polynomial `1` is empty. -/
theorem zeroLocus_one_eq_empty :
    zeroLocus ({(1 : Poly k n)} : Set (Poly k n)) = ∅ := by
  have h1 : ∀ f ∈ ({(1 : Poly k n)} : Set (Poly k n)), ∃ d, f.IsHomogeneous d := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, MvPolynomial.isHomogeneous_one (σ := Fin (n + 1)) (R := k)⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff h1 hv]
  simp

/-- A union of projective zero loci is the zero locus of the products: over a field a product
vanishes iff one of the factors does.  This is Hartshorne's computation
`V(T_1) ∪ V(T_2) = V({fg : f ∈ T_1, g ∈ T_2})`, which makes the zero loci the closed sets of
a topology. -/
theorem zeroLocus_image2_mul_union {T T' : Set (Poly k n)}
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

/-! ## 3. The Zariski topology on `P^n` -/

set_option warn.classDefReducibility false in
/-- **The Zariski topology on `P^n`**: a set is open iff it is the complement of the zero
locus `V(T)` of a set `T` of homogeneous polynomials (Hartshorne I.2, p. 10). -/
def zariskiTopology : TopologicalSpace (P k n) where
  IsOpen U := ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ U = (zeroLocus T)ᶜ
  isOpen_univ := by
    have h1 : ∀ f ∈ ({(1 : Poly k n)} : Set (Poly k n)), ∃ d, f.IsHomogeneous d := by
      intro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨0, MvPolynomial.isHomogeneous_one (σ := Fin (n + 1)) (R := k)⟩
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
    have hA' : ∀ a : A, ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
        (a : Set (P k n)) = (zeroLocus T)ᶜ := fun a => hA a a.2
    choose T hT hTA using hA'
    refine ⟨⋃ a : A, T a, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, hfa⟩ := Set.mem_iUnion.1 hf
      exact hT a f hfa
    · rw [zeroLocus_iUnion, Set.sUnion_eq_iUnion, Set.compl_iInter]
      exact Set.iUnion_congr fun a => hTA a

instance : TopologicalSpace (P k n) := zariskiTopology (k := k) (n := n)

/-- The closed sets of `P^n` are exactly the zero loci of sets of homogeneous
polynomials. -/
theorem isClosed_iff_exists_zeroLocus {Z : Set (P k n)} :
    IsClosed Z ↔ ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ Z = zeroLocus T := by
  constructor
  · intro h
    obtain ⟨T, hT, hU⟩ := h.isOpen_compl
    exact ⟨T, hT, by rw [← compl_compl Z, hU, compl_compl]⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩

theorem isClosed_zeroLocus {T : Set (Poly k n)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) : IsClosed (zeroLocus T) :=
  isClosed_iff_exists_zeroLocus.2 ⟨T, hT, rfl⟩

end P


namespace P

/-! ### Vanishing ideals -/

/-- The set of all polynomials vanishing at every representative of every point of `Y`. -/
def VanishOn (Y : Set (P k n)) : Set (Poly k n) :=
  fun f => ∀ p ∈ Y, FormVanishesAt f p

theorem mem_vanishOn_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ VanishOn Y ↔ ∀ p ∈ Y, FormVanishesAt f p := Iff.rfl

/-- `VanishOn Y` is an ideal of `S = k[x_0,…,x_n]`. -/
def vanishOnIdeal (Y : Set (P k n)) : Ideal (Poly k n) where
  carrier := VanishOn Y
  zero_mem' := by
    intro p hp v hv _
    simp
  add_mem' := by
    intro f g hf hg p hp v hv hvp
    rw [map_add, hf p hp v hv hvp, hg p hp v hv hvp, add_zero]
  smul_mem' := by
    intro c f hf p hp v hv hvp
    rw [smul_eq_mul, map_mul, hf p hp v hv hvp, mul_zero]

theorem mem_vanishOnIdeal_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ vanishOnIdeal Y ↔ ∀ p ∈ Y, FormVanishesAt f p := Iff.rfl

/-- The homogeneous polynomials vanishing on `Y ⊆ P^n`. -/
def vanishingForms (Y : Set (P k n)) : Set (Poly k n) :=
  fun f => ∃ d, f.IsHomogeneous d ∧ ∀ p ∈ Y, FormVanishesAt f p

theorem mem_vanishingForms_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ vanishingForms Y ↔ ∃ d, f.IsHomogeneous d ∧ ∀ p ∈ Y, FormVanishesAt f p :=
  Iff.rfl

theorem vanishingForms_subset_vanishOn (Y : Set (P k n)) :
    vanishingForms Y ⊆ vanishOnIdeal Y := by
  intro f h
  obtain ⟨d, hd, hf⟩ := mem_vanishingForms_iff.1 h
  exact mem_vanishOnIdeal_iff.2 hf

/-- **Hartshorne's `I(Y)`**: the ideal generated by the homogeneous polynomials vanishing on
`Y ⊆ P^n`. -/
def vanishingIdeal (Y : Set (P k n)) : Ideal (Poly k n) :=
  Ideal.span (vanishingForms Y)

theorem vanishingForms_mono {Y Y' : Set (P k n)} (h : Y ⊆ Y') :
    vanishingForms Y' ⊆ vanishingForms Y := by
  intro f hf
  obtain ⟨d, hd, hf'⟩ := mem_vanishingForms_iff.1 hf
  exact mem_vanishingForms_iff.2 ⟨d, hd, fun p hp => hf' p (h hp)⟩

theorem vanishingIdeal_le_vanishOn (Y : Set (P k n)) : vanishingIdeal Y ≤ vanishOnIdeal Y :=
  Ideal.span_le.2 (vanishingForms_subset_vanishOn Y)

/-- The vanishing ideal is monotone: a smaller set has a larger vanishing ideal. -/
theorem vanishingIdeal_mono {Y Y' : Set (P k n)} (h : Y ⊆ Y') :
    vanishingIdeal Y' ≤ vanishingIdeal Y :=
  Ideal.span_mono (vanishingForms_mono h)

theorem vanishingForms_homogeneous (Y : Set (P k n)) :
    ∀ f ∈ vanishingForms Y, ∃ d, f.IsHomogeneous d := by
  intro f h
  obtain ⟨d, hd, -⟩ := mem_vanishingForms_iff.1 h
  exact ⟨d, hd⟩

/-- Any ideal generated by polynomials vanishing on `Z` vanishes on `Z`. -/
theorem span_le_vanishOn {S : Set (Poly k n)} {Z : Set (P k n)}
    (h : S ⊆ vanishOnIdeal Z) : Ideal.span S ≤ vanishOnIdeal Z :=
  Ideal.span_le.2 h

/-- The zero locus of `I(Y)` is the zero locus of the homogeneous polynomials vanishing on
`Y`: only homogeneous generators are needed to test vanishing at a point. -/
theorem vanishingForms_le_vanishOn_zeroLocus (Y : Set (P k n)) :
    vanishingForms Y ⊆ vanishOnIdeal (zeroLocus (vanishingForms Y)) := by
  intro g hg p hp
  exact hp g hg

theorem zeroLocus_vanishingIdeal_eq_zeroLocus_forms (Y : Set (P k n)) :
    zeroLocus (vanishingIdeal Y : Set (Poly k n)) = zeroLocus (vanishingForms Y) := by
  refine le_antisymm (zeroLocus_mono (Ideal.subset_span (s := vanishingForms Y))) ?_
  intro p hp f hf
  exact mem_vanishOnIdeal_iff.1
    (span_le_vanishOn (vanishingForms_le_vanishOn_zeroLocus Y) hf) p hp

/-- `V(I(Y))` is closed. -/
theorem isClosed_zeroLocus_vanishingIdeal (Y : Set (P k n)) :
    IsClosed (zeroLocus (vanishingIdeal Y : Set (Poly k n))) := by
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms]
  exact isClosed_zeroLocus (vanishingForms_homogeneous Y)

/-- `Y` is contained in `V(I(Y))`. -/
theorem subset_zeroLocus_vanishingIdeal (Y : Set (P k n)) :
    Y ⊆ zeroLocus (vanishingIdeal Y : Set (Poly k n)) := by
  intro p hp f hf
  exact mem_vanishOnIdeal_iff.1 (vanishingIdeal_le_vanishOn Y hf) p hp

/-- **`V(I(Z)) = Z` for closed `Z ⊆ P^n`** (the closed case of Hartshorne Ex. I.2.3(e)). -/
theorem zeroLocus_vanishingIdeal_eq {Z : Set (P k n)} (hZ : IsClosed Z) :
    zeroLocus (vanishingIdeal Z : Set (Poly k n)) = Z := by
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  refine le_antisymm ?_ (subset_zeroLocus_vanishingIdeal (zeroLocus T))
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms]
  refine zeroLocus_mono ?_
  intro f hf
  obtain ⟨d, hd⟩ := hT f hf
  exact mem_vanishingForms_iff.2 ⟨d, hd, fun p hp => hp f hf⟩

/-- The closure of a set is the intersection of the closed sets containing it. -/
theorem closure_eq_sInter (Y : Set (P k n)) :
    closure Y = ⋂₀ {F : Set (P k n) | IsClosed F ∧ Y ⊆ F} := by
  refine le_antisymm ?_ ?_
  · refine Set.subset_sInter ?_
    rintro F ⟨hFc, hYF⟩
    exact closure_minimal hYF hFc
  · exact Set.sInter_subset_of_mem ⟨isClosed_closure, subset_closure⟩

/-- **`V(I(Y)) = closure Y`** for an arbitrary `Y ⊆ P^n` (Hartshorne Ex. I.2.3(e)). -/
theorem zeroLocus_vanishingIdeal_eq_closure (Y : Set (P k n)) :
    zeroLocus (vanishingIdeal Y : Set (Poly k n)) = closure Y := by
  refine le_antisymm ?_ (closure_minimal (subset_zeroLocus_vanishingIdeal Y)
    (isClosed_zeroLocus_vanishingIdeal Y))
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms, closure_eq_sInter]
  intro p hp
  rw [Set.mem_sInter]
  intro F hF
  obtain ⟨hFc, hYF⟩ := hF
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hFc
  intro f hf
  obtain ⟨d, hd⟩ := hT f hf
  exact hp f (mem_vanishingForms_iff.2 ⟨d, hd, fun q hq => hYF hq f hf⟩)

end P

section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- **Irreducible closed subset**, in Hartshorne's sense: nonempty and not the union of two
proper closed subsets. -/
def IsIrredClosed (Z : Set X) : Prop :=
  Z.Nonempty ∧ IsClosed Z ∧
    ∀ A B : Set X, IsClosed A → IsClosed B → Z ⊆ A ∪ B → Z ⊆ A ∨ Z ⊆ B

/-- Hartshorne's definition ("cannot be written as the union of two proper closed subsets")
rephrased: `Z` is irreducible iff there are no two closed subsets, neither containing `Z`,
whose union contains `Z`. -/
theorem isIrredClosed_iff_not_union {Z : Set X} :
    IsIrredClosed Z ↔ Z.Nonempty ∧ IsClosed Z ∧
      ¬ ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Z ⊆ A ∪ B ∧ ¬ Z ⊆ A ∧ ¬ Z ⊆ B := by
  constructor
  · rintro ⟨hne, hc, hirr⟩
    refine ⟨hne, hc, ?_⟩
    rintro ⟨A, B, hA, hB, hcov, hAn, hBn⟩
    rcases hirr A B hA hB hcov with h | h
    · exact hAn h
    · exact hBn h
  · rintro ⟨hne, hc, hno⟩
    refine ⟨hne, hc, ?_⟩
    intro A B hA hB hcov
    by_contra hc'
    push Not at hc'
    exact hno ⟨A, B, hA, hB, hcov, hc'.1, hc'.2⟩

/-- The descending chain condition for closed subsets: Hartshorne's definition of a noetherian
topological space. -/
def HasDCCClosed (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ F : ℕ → Set X, (∀ i, IsClosed (F i)) → (∀ i, F (i + 1) ⊆ F i) → ∃ N, ∀ i, N ≤ i → F i = F N

/-- In a space with the descending chain condition, every nonempty family of closed subsets has
a minimal element. -/
theorem exists_minimal_closed (dcc : HasDCCClosed X) {F : Set (Set X)} (hne : F.Nonempty)
    (hF : ∀ Z ∈ F, IsClosed Z) :
    ∃ Z ∈ F, ∀ W ∈ F, W ⊆ Z → Z ⊆ W := by
  classical
  by_contra h
  push Not at h
  have hstep : ∀ x : {Z // Z ∈ F}, ∃ y : {Z // Z ∈ F}, y.1 ⊆ x.1 ∧ ¬ x.1 ⊆ y.1 := by
    rintro ⟨Z, hZ⟩
    obtain ⟨W, hW, hWZ, hZW⟩ := h Z hZ
    exact ⟨⟨W, hW⟩, hWZ, hZW⟩
  let nxt : {Z // Z ∈ F} → {Z // Z ∈ F} := fun x => (hstep x).choose
  have nxt_sub : ∀ x, (nxt x).1 ⊆ x.1 := fun x => (hstep x).choose_spec.1
  have nxt_not_sub : ∀ x, ¬ x.1 ⊆ (nxt x).1 := fun x => (hstep x).choose_spec.2
  obtain ⟨x₀, hx₀⟩ := hne
  let seq : ℕ → {Z // Z ∈ F} := fun i => Nat.rec ⟨x₀, hx₀⟩ (fun _ x => nxt x) i
  have hseq_succ : ∀ i, seq (i + 1) = nxt (seq i) := fun i => rfl
  have hanti : ∀ i, (seq (i + 1)).1 ⊆ (seq i).1 := fun i => by
    rw [hseq_succ]
    exact nxt_sub (seq i)
  have hclosed : ∀ i, IsClosed (seq i).1 := fun i => hF _ (seq i).2
  obtain ⟨N, hN⟩ := dcc (fun i => (seq i).1) hclosed hanti
  have h1 : (seq (N + 1)).1 = (seq N).1 := hN (N + 1) (Nat.le_succ N)
  refine nxt_not_sub (seq N) ?_
  rw [← hseq_succ, h1]

omit [TopologicalSpace X] in
/-- Every finite nonempty family of sets has a member which is maximal for inclusion. -/
theorem exists_maximal_subset_of_finite {E : Set (Set X)} (hE : E.Finite) (hne : E.Nonempty) :
    ∃ W ∈ E, ∀ W' ∈ E, W ⊆ W' → W' ⊆ W := by
  classical
  revert hne
  refine Set.Finite.induction_on
    (motive := fun s _ => s.Nonempty → ∃ W ∈ s, ∀ W' ∈ s, W ⊆ W' → W' ⊆ W) E hE ?_ ?_
  · intro hne
    exact absurd hne (by simp)
  · intro a s ha hs ih hne
    by_cases hsne : s.Nonempty
    · obtain ⟨W, hWs, hmax⟩ := ih hsne
      by_cases hWa : W ⊆ a
      · refine ⟨a, Set.mem_insert a s, ?_⟩
        intro W' hW' haW'
        rcases hW' with rfl | hW's
        · exact subset_rfl
        · have hWW' : W ⊆ W' := hWa.trans haW'
          have hW'W : W' ⊆ W := hmax W' hW's hWW'
          exact hW'W.trans hWa
      · refine ⟨W, Set.mem_insert_of_mem _ hWs, ?_⟩
        intro W' hW' hWW'
        rcases hW' with rfl | hW's
        · exact absurd hWW' hWa
        · exact hmax W' hW's hWW'
    · refine ⟨a, Set.mem_insert a s, ?_⟩
      intro W' hW' haW'
      rw [Set.mem_insert_iff] at hW'
      rcases hW' with rfl | hWs
      · exact subset_rfl
      · exact absurd ⟨W', hWs⟩ hsne

end NoetherianTop



section NoetherianTop

variable {X : Type*} [TopologicalSpace X]

/-- Our notion of irreducible closed subset agrees with Mathlib's `IsIrreducible` (and hence
with Hartshorne's "not the union of two proper closed subsets"). -/
theorem isIrredClosed_iff_isIrreducible {Z : Set X} :
    IsIrredClosed Z ↔ IsClosed Z ∧ IsIrreducible Z := by
  refine ⟨fun h => ⟨h.2.1, h.1, ?_⟩, fun h => ⟨h.2.1, h.1, ?_⟩⟩
  · exact isPreirreducible_iff_isClosed_union_isClosed.2 h.2.2
  · exact isPreirreducible_iff_isClosed_union_isClosed.1 h.2.2

end NoetherianTop


/-! # Hartshorne, Exercise I.2.15: the quadric surface in `P^3` -/

namespace P

variable {k : Type*} [Field k]

/-! ## 1. The Segre map `P¹ × P¹ → P³` -/

/-- On representatives: `(a₀,a₁) × (b₀,b₁) ↦ (a₀b₀, a₀b₁, a₁b₀, a₁b₁)`, in Hartshorne's
lexicographic order of the coordinates `z_{ij}`. -/
def segreVec (v w : Vec k 1) : Vec k 3 :=
  ![v 0 * w 0, v 0 * w 1, v 1 * w 0, v 1 * w 1]

theorem segreVec_apply_zero (v w : Vec k 1) : segreVec v w 0 = v 0 * w 0 := by
  simp [segreVec]

theorem segreVec_apply_one (v w : Vec k 1) : segreVec v w 1 = v 0 * w 1 := by
  simp [segreVec]

theorem segreVec_apply_two (v w : Vec k 1) : segreVec v w 2 = v 1 * w 0 := by
  simp [segreVec]

theorem segreVec_apply_three (v w : Vec k 1) : segreVec v w 3 = v 1 * w 1 := by
  simp [segreVec]

theorem segreVec_eq_zero_iff {v w : Vec k 1} : segreVec v w = 0 ↔ v = 0 ∨ w = 0 := by
  constructor
  · intro h
    by_cases hv : v = 0
    · exact Or.inl hv
    refine Or.inr ?_
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv
    have h0 : w 0 = 0 := by
      fin_cases i
      · have hz := congrFun h (0 : Fin 4)
        rw [segreVec_apply_zero] at hz
        rcases mul_eq_zero.1 hz with h' | h'
        · exact absurd h' hi
        · exact h'
      · have hz := congrFun h (2 : Fin 4)
        rw [segreVec_apply_two] at hz
        rcases mul_eq_zero.1 hz with h' | h'
        · exact absurd h' hi
        · exact h'
    have h1 : w 1 = 0 := by
      fin_cases i
      · have hz := congrFun h (1 : Fin 4)
        rw [segreVec_apply_one] at hz
        rcases mul_eq_zero.1 hz with h' | h'
        · exact absurd h' hi
        · exact h'
      · have hz := congrFun h (3 : Fin 4)
        rw [segreVec_apply_three] at hz
        rcases mul_eq_zero.1 hz with h' | h'
        · exact absurd h' hi
        · exact h'
    funext j
    fin_cases j
    · simpa using h0
    · simpa using h1
  · rintro (rfl | rfl) <;> funext i <;> fin_cases i <;> simp [segreVec]

theorem segreVec_ne_zero {v w : Vec k 1} (hv : v ≠ 0) (hw : w ≠ 0) : segreVec v w ≠ 0 := by
  intro h
  rcases segreVec_eq_zero_iff.1 h with h' | h'
  exacts [hv h', hw h']

theorem segreVec_smul (c d : k) (v w : Vec k 1) :
    segreVec (c • v) (d • w) = (c * d) • segreVec v w := by
  funext i
  fin_cases i <;> simp [segreVec, mul_assoc, mul_left_comm, mul_comm]

/-! ## 2. The quadratic form `xy - zw` and the quadric `Q` -/

/-- Hartshorne's quadric `xy - zw = 0` in `P³`, written in the lexicographic coordinate order
`(x : y : z : w) = (z₀₀ : z₁₁ : z₀₁ : z₁₀)` of the Segre map: `X₀X₃ - X₁X₂`. -/
def quadForm : Poly k 3 := MvPolynomial.X (0 : Fin 4) * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2

theorem isHomogeneous_X4 (i : Fin 4) : (MvPolynomial.X i : Poly k 3).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X _ _

theorem quadForm_isHomogeneous : (quadForm (k := k)).IsHomogeneous 2 := by
  unfold quadForm
  have := (isHomogeneous_X4 (k := k) 0).mul (isHomogeneous_X4 (k := k) 3)
  have h2 := (isHomogeneous_X4 (k := k) 1).mul (isHomogeneous_X4 (k := k) 2)
  convert this.sub h2 using 1

/-- The quadric surface `Q ⊆ P³`: the zero locus of `xy - zw`. -/
def quadric : Set (P k 3) := zeroLocus {quadForm (k := k)}

theorem mem_quadric_iff {v : Vec k 3} (hv : v ≠ 0) :
    mk hv ∈ quadric (k := k) ↔
      MvPolynomial.eval v (quadForm (k := k)) = 0 := by
  unfold quadric
  rw [mem_zeroLocus_iff]
  · simp
  · intro f hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨2, hf ▸ quadForm_isHomogeneous⟩

theorem eval_quadForm (x : Vec k 3) :
    MvPolynomial.eval x (quadForm (k := k)) = x 0 * x 3 - x 1 * x 2 := by
  simp [quadForm]

/-! ## 3. Part (a): `Q` is the image of the Segre embedding -/

theorem segreVec_component (v w : Vec k 1) (i j : Fin 2) :
    segreVec v w (finProdFinEquiv (i, j)) = v i * w j := by
  fin_cases i <;> fin_cases j <;> simp [segreVec, finProdFinEquiv]

/-- **The Segre embedding** `ψ : P¹ × P¹ → P³`,
`(a₀:a₁; b₀:b₁) ↦ (a₀b₀ : a₀b₁ : a₁b₀ : a₁b₁)` (Hartshorne Ex. I.2.14). -/
def segre (p q : P k 1) : P k 3 :=
  Quotient.lift₂ (fun v w => mk (segreVec_ne_zero v.2 w.2)) (by
    intro v w v' w' hv hw
    obtain ⟨c, hc, hcv⟩ := hv
    obtain ⟨d, hd, hdw⟩ := hw
    refine (mk_eq_mk_iff (segreVec_ne_zero v.2 w.2) (segreVec_ne_zero v'.2 w'.2)).2
      ⟨c * d, mul_ne_zero hc hd, ?_⟩
    show segreVec (v : Vec k 1) (w : Vec k 1) = (c * d) • segreVec (v' : Vec k 1) (w' : Vec k 1)
    rw [hcv, hdw, segreVec_smul]) p q

theorem segre_mk {v w : Vec k 1} (hv : v ≠ 0) (hw : w ≠ 0) :
    segre (k := k) (mk hv) (mk hw) = mk (segreVec_ne_zero hv hw) := rfl

/-- Parallelism of the two factors, read off from proportionality of the Segre products. -/
theorem segreVec_parallel {v w v' w' : Vec k 1} (h : segreVec v w = segreVec v' w')
    (hv : v ≠ 0) (hw : w ≠ 0) (_hv' : v' ≠ 0) (_hw' : w' ≠ 0) :
    (∃ e : k, e ≠ 0 ∧ v = e • v') ∧ ∃ f : k, f ≠ 0 ∧ w = f • w' := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.1 hw
  have hc := congrFun h (finProdFinEquiv (i₀, j₀))
  rw [segreVec_component, segreVec_component] at hc
  have hne : v' i₀ * w' j₀ ≠ 0 := by
    rw [← hc]
    exact mul_ne_zero hi₀ hj₀
  have hvi : v' i₀ ≠ 0 := left_ne_zero_of_mul hne
  have hwj : w' j₀ ≠ 0 := right_ne_zero_of_mul hne
  constructor
  · refine ⟨w' j₀ / w j₀, div_ne_zero hwj hj₀, ?_⟩
    funext i
    have hci := congrFun h (finProdFinEquiv (i, j₀))
    rw [segreVec_component, segreVec_component] at hci
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hj₀, hci, mul_comm]
  · refine ⟨v' i₀ / v i₀, div_ne_zero hvi hi₀, ?_⟩
    funext j
    have hcj := congrFun h (finProdFinEquiv (i₀, j))
    rw [segreVec_component, segreVec_component] at hcj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi₀]
    rw [mul_comm, ← hcj, mul_comm]

/-- The Segre map is injective. -/
theorem segre_inj : Function.Injective (fun p : P k 1 × P k 1 => segre p.1 p.2) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  obtain ⟨w, hw, rfl⟩ := exists_mk q
  obtain ⟨v', hv', rfl⟩ := exists_mk p'
  obtain ⟨w', hw', rfl⟩ := exists_mk q'
  have hpq' : segre (mk hv) (mk hw) = segre (mk hv') (mk hw') := hpq
  rw [segre_mk, segre_mk] at hpq'
  obtain ⟨c, hc, hcs⟩ := (mk_eq_mk_iff (segreVec_ne_zero hv hw) (segreVec_ne_zero hv' hw')).1 hpq'
  have hc' : segreVec (c • v') w' = c • segreVec v' w' := by
    simpa using segreVec_smul (c := c) (d := 1) v' w'
  have hcs' : segreVec v w = segreVec (c • v') w' := by rw [hc']; exact hcs
  have hpar := segreVec_parallel (v := v) (w := w) (v' := c • v') (w' := w') hcs'
    hv hw (smul_ne_zero hc hv') hw'
  obtain ⟨⟨e, he, hev⟩, f, hf, hfw⟩ := hpar
  have hev' : v = (e * c) • v' := by rw [← smul_smul]; exact hev
  have hp : mk hv = mk hv' := (mk_eq_mk_iff hv hv').2 ⟨e * c, mul_ne_zero he hc, hev'⟩
  have hq : mk hw = mk hw' := (mk_eq_mk_iff hw hw').2 ⟨f, hf, hfw⟩
  exact Prod.ext hp hq

/-- The image of the Segre map lies in the quadric. -/
theorem segre_mem_quadric (p q : P k 1) : segre p q ∈ quadric (k := k) := by
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  obtain ⟨w, hw, rfl⟩ := exists_mk q
  rw [segre_mk, mem_quadric_iff (segreVec_ne_zero hv hw), eval_quadForm]
  simp [segreVec]
  ring

theorem isHomogeneous_quadForm_mem : ∀ f ∈ ({quadForm (k := k)} : Set (Poly k 3)),
    ∃ d, f.IsHomogeneous d := by
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  exact ⟨2, hf ▸ quadForm_isHomogeneous⟩

theorem vec2_ne_zero_left {a b : k} (ha : a ≠ 0) : (![a, b] : Vec k 1) ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 2)
  simp at this
  exact ha this

theorem vec2_ne_zero_right {a b : k} (hb : b ≠ 0) : (![a, b] : Vec k 1) ≠ 0 := by
  intro h
  have := congrFun h (1 : Fin 2)
  simp at this
  exact hb this

/-- Every point of the quadric is a Segre product. -/
theorem quadric_exists_segre (x : Vec k 3) (hx : x ≠ 0) (h : x 0 * x 3 = x 1 * x 2) :
    ∃ (v w : Vec k 1), v ≠ 0 ∧ w ≠ 0 ∧ segreVec v w = x := by
  by_cases h0 : x 0 = 0
  · by_cases h1 : x 1 = 0
    · -- `x 0 = x 1 = 0`, so `(x 2, x 3) ≠ 0`
      have hw : (![x 2, x 3] : Vec k 1) ≠ 0 := by
        intro hc
        apply hx
        funext i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · have := congrFun hc (0 : Fin 2); simpa using this
        · have := congrFun hc (1 : Fin 2); simpa using this
      refine ⟨![0, 1], ![x 2, x 3], vec2_ne_zero_right one_ne_zero, hw, ?_⟩
      funext i
      fin_cases i <;> simp [segreVec, h0, h1]
    · -- `x 0 = 0`, `x 1 ≠ 0`, hence `x 2 = 0`
      have h2 : x 2 = 0 := by
        rcases mul_eq_zero.1 (by rw [← h, h0, zero_mul] : x 1 * x 2 = 0) with h' | h'
        exact absurd h' h1
        exact h'
      refine ⟨![x 1, x 3], ![0, 1], vec2_ne_zero_left h1, vec2_ne_zero_right one_ne_zero, ?_⟩
      funext i
      fin_cases i <;> simp [segreVec, h0, h2]
  · -- `x 0 ≠ 0`: `(1, x2/x0) × (x0, x1)`
    have hw : (![x 0, x 1] : Vec k 1) ≠ 0 := vec2_ne_zero_left h0
    refine ⟨![1, x 2 / x 0], ![x 0, x 1], vec2_ne_zero_left one_ne_zero, hw, ?_⟩
    have h3 : x 2 / x 0 * x 1 = x 3 := by
      rw [div_mul_eq_mul_div, div_eq_iff h0, mul_comm (x 3) (x 0), h, mul_comm]
    funext i
    fin_cases i
    · simp [segreVec]
    · simp [segreVec]
    · simp [segreVec, div_mul_cancel₀ _ h0]
    · simpa [segreVec] using h3

/-- **Part (a)**: the quadric `Q : xy - zw = 0` is the image of the Segre embedding. -/
theorem range_segre : Set.range (fun p : P k 1 × P k 1 => segre p.1 p.2) = quadric (k := k) := by
  ext p
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact segre_mem_quadric u v
  · intro hp
    obtain ⟨x, hx, rfl⟩ := exists_mk p
    rw [mem_quadric_iff hx, eval_quadForm] at hp
    obtain ⟨v, w, hv, hw, hvx⟩ := quadric_exists_segre x hx (sub_eq_zero.1 hp)
    subst hvx
    refine ⟨(mk hv, mk hw), ?_⟩
    show segre (mk hv) (mk hw) = mk hx
    rw [segre_mk]

/-! ## 4. Part (b): the two families of lines on `Q` -/

/-- The Segre embedding as a map on the product. -/
def segrePair (p : P k 1 × P k 1) : P k 3 := segre p.1 p.2

theorem segrePair_inj : Function.Injective (segrePair (k := k)) := segre_inj

/-- First family of lines: `L_t = ψ(P¹ × {t})`. -/
def L (t : P k 1) : Set (P k 3) := segrePair '' (Set.univ ×ˢ {t})

/-- Second family of lines: `M_t = ψ({t} × P¹)`. -/
def M (t : P k 1) : Set (P k 3) := segrePair '' ({t} ×ˢ Set.univ)

theorem mem_L {t : P k 1} {p : P k 3} : p ∈ L t ↔ ∃ u : P k 1, segre u t = p := by
  simp [L, segrePair, eq_comm]

theorem mem_M {t : P k 1} {p : P k 3} : p ∈ M t ↔ ∃ u : P k 1, segre t u = p := by
  simp [M, segrePair, eq_comm]

theorem segre_mem_L (u t : P k 1) : segre u t ∈ L t := by
  rw [mem_L]; exact ⟨u, rfl⟩

theorem segre_mem_M (u t : P k 1) : segre u t ∈ M u := by
  rw [mem_M]; exact ⟨t, rfl⟩

theorem L_subset_quadric (t : P k 1) : L t ⊆ quadric (k := k) := by
  rintro p ⟨⟨u, v⟩, hv, rfl⟩
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff] at hv
  obtain ⟨-, rfl⟩ := hv
  exact segre_mem_quadric u v

theorem M_subset_quadric (t : P k 1) : M t ⊆ quadric (k := k) := by
  rintro p ⟨⟨u, v⟩, hv, rfl⟩
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff] at hv
  obtain ⟨rfl, -⟩ := hv
  exact segre_mem_quadric u v

theorem L_injective {t s : P k 1} (h : L t = L s) : t = s := by
  have h1 : segre t t ∈ L s := by
    rw [← h]; exact segre_mem_L t t
  rw [mem_L] at h1
  obtain ⟨u, hu⟩ := h1
  have h2 : segrePair (u, s) = segrePair (t, t) := hu
  exact (Prod.ext_iff.1 (segrePair_inj h2)).2.symm

theorem M_injective {t s : P k 1} (h : M t = M s) : t = s := by
  have h1 : segre t t ∈ M s := by
    rw [← h]; exact segre_mem_M t t
  rw [mem_M] at h1
  obtain ⟨u, hu⟩ := h1
  have h2 : segrePair (s, u) = segrePair (t, t) := hu
  exact (Prod.ext_iff.1 (segrePair_inj h2)).1.symm

theorem L_disjoint {t s : P k 1} (h : t ≠ s) : Disjoint (L t) (L s) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [mem_L] at hp hq
  obtain ⟨u, hu⟩ := hp
  obtain ⟨u', hu'⟩ := hq
  have h2 : segrePair (u, t) = segrePair (u', s) := by
    simp only [segrePair]
    rw [hu, hu']
  have := (Prod.ext_iff.1 (segrePair_inj h2)).2
  exact h this

theorem M_disjoint {t s : P k 1} (h : t ≠ s) : Disjoint (M t) (M s) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [mem_M] at hp hq
  obtain ⟨u, hu⟩ := hp
  obtain ⟨u', hu'⟩ := hq
  have h2 : segrePair (t, u) = segrePair (s, u') := by
    simp only [segrePair]
    rw [hu, hu']
  have := (Prod.ext_iff.1 (segrePair_inj h2)).1
  exact h this

theorem L_inter_M (t u : P k 1) : L t ∩ M u = {segre u t} := by
  ext p
  constructor
  · rintro ⟨hp, hq⟩
    rw [mem_L] at hp
    rw [mem_M] at hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    have h2 : segrePair (a, t) = segrePair (u, b) := by
      simp only [segrePair]
      rw [ha, hb]
    obtain ⟨h1, h2'⟩ := Prod.ext_iff.1 (segrePair_inj h2)
    have h1' : a = u := h1
    rw [Set.mem_singleton_iff]
    rw [← ha, h1']
  · rintro rfl
    exact ⟨segre_mem_L u t, segre_mem_M u t⟩

theorem L_inter_M_ncard (t u : P k 1) : (L t ∩ M u).ncard = 1 := by
  rw [L_inter_M]
  simp

/-! ## 5. The lines are linear varieties of dimension one -/

/-- A **projective line** of `P³` in Hartshorne's sense: the set of points of a linear subspace
of dimension two of `k⁴` (a linear variety of dimension `2 - 1 = 1`). -/
def IsProjectiveLine (S : Set (P k 3)) : Prop :=
  ∃ W : Submodule k (Vec k 3), Module.finrank k W = 2 ∧
    S = {p | ∃ (v : Vec k 3) (hv : v ≠ 0), v ∈ W ∧ mk hv = p}

theorem vec2_eq_zero_iff {a b : k} : (![a, b] : Vec k 1) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨by have := congrFun h (0 : Fin 2); simpa using this,
      by have := congrFun h (1 : Fin 2); simpa using this⟩
  · rintro ⟨rfl, rfl⟩
    funext i; fin_cases i <;> simp

theorem vec2_eta (t : Vec k 1) : (![t 0, t 1] : Vec k 1) = t := by
  funext i; fin_cases i <;> simp

theorem vec2_ne_zero_iff {a b : k} : (![a, b] : Vec k 1) ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h (vec2_eq_zero_iff.2 ⟨hc.1, hc.2⟩)
  · rintro (h | h) h'
    · exact h (vec2_eq_zero_iff.1 h').1
    · exact h (vec2_eq_zero_iff.1 h').2

theorem vec1_ne_zero_iff {t : Vec k 1} : t ≠ 0 ↔ t 0 ≠ 0 ∨ t 1 ≠ 0 := by
  rw [← vec2_eta t, vec2_ne_zero_iff]
  simp

/-- The two spanning vectors of the line `L_t = ψ(P¹ × {t})`. -/
def vecL1 (t : Vec k 1) : Vec k 3 := ![t 0, t 1, 0, 0]
/-- The two spanning vectors of the line `L_t = ψ(P¹ × {t})`. -/
def vecL2 (t : Vec k 1) : Vec k 3 := ![0, 0, t 0, t 1]
/-- The two spanning vectors of the line `M_t = ψ({t} × P¹)`. -/
def vecM1 (t : Vec k 1) : Vec k 3 := ![t 0, 0, t 1, 0]
/-- The two spanning vectors of the line `M_t = ψ({t} × P¹)`. -/
def vecM2 (t : Vec k 1) : Vec k 3 := ![0, t 0, 0, t 1]

theorem segreVec_eq_vecL (v t : Vec k 1) :
    segreVec v t = v 0 • vecL1 t + v 1 • vecL2 t := by
  funext i; fin_cases i <;> simp [segreVec, vecL1, vecL2]

theorem segreVec_eq_vecM (t v : Vec k 1) :
    segreVec t v = v 0 • vecM1 t + v 1 • vecM2 t := by
  funext i; fin_cases i <;> simp [segreVec, vecM1, vecM2, mul_comm]

theorem segreVec_pairL (a b : k) (t : Vec k 1) :
    segreVec (![a, b] : Vec k 1) t = a • vecL1 t + b • vecL2 t := by
  rw [segreVec_eq_vecL]
  simp

theorem segreVec_pairM (a b : k) (t : Vec k 1) :
    segreVec t (![a, b] : Vec k 1) = a • vecM1 t + b • vecM2 t := by
  rw [segreVec_eq_vecM]
  simp

theorem vecL_linearIndependent {t : Vec k 1} (ht : t ≠ 0) :
    LinearIndependent k (![vecL1 t, vecL2 t] : Fin 2 → Vec k 3) := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have h0 : a * t 0 = 0 := by have := congrFun h 0; simpa [vecL1, vecL2] using this
  have h1 : a * t 1 = 0 := by have := congrFun h 1; simpa [vecL1, vecL2] using this
  have h2 : b * t 0 = 0 := by have := congrFun h 2; simpa [vecL1, vecL2] using this
  have h3 : b * t 1 = 0 := by have := congrFun h 3; simpa [vecL1, vecL2] using this
  constructor
  · rcases (vec1_ne_zero_iff.1 ht) with h' | h'
    · rcases mul_eq_zero.1 h0 with h'' | h''
      exacts [h'', absurd h'' h']
    · rcases mul_eq_zero.1 h1 with h'' | h''
      exacts [h'', absurd h'' h']
  · rcases (vec1_ne_zero_iff.1 ht) with h' | h'
    · rcases mul_eq_zero.1 h2 with h'' | h''
      exacts [h'', absurd h'' h']
    · rcases mul_eq_zero.1 h3 with h'' | h''
      exacts [h'', absurd h'' h']

theorem vecM_linearIndependent {t : Vec k 1} (ht : t ≠ 0) :
    LinearIndependent k (![vecM1 t, vecM2 t] : Fin 2 → Vec k 3) := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have h0 : a * t 0 = 0 := by have := congrFun h 0; simpa [vecM1, vecM2] using this
  have h1 : b * t 0 = 0 := by have := congrFun h 1; simpa [vecM1, vecM2] using this
  have h2 : a * t 1 = 0 := by have := congrFun h 2; simpa [vecM1, vecM2] using this
  have h3 : b * t 1 = 0 := by have := congrFun h 3; simpa [vecM1, vecM2] using this
  constructor
  · rcases (vec1_ne_zero_iff.1 ht) with h' | h'
    · rcases mul_eq_zero.1 h0 with h'' | h''
      exacts [h'', absurd h'' h']
    · rcases mul_eq_zero.1 h2 with h'' | h''
      exacts [h'', absurd h'' h']
  · rcases (vec1_ne_zero_iff.1 ht) with h' | h'
    · rcases mul_eq_zero.1 h1 with h'' | h''
      exacts [h'', absurd h'' h']
    · rcases mul_eq_zero.1 h3 with h'' | h''
      exacts [h'', absurd h'' h']

theorem range_pair_vec (a b : Vec k 3) : Set.range (![a, b] : Fin 2 → Vec k 3) = {a, b} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem finrank_span_vecL {t : Vec k 1} (ht : t ≠ 0) :
    Module.finrank k (Submodule.span k {vecL1 t, vecL2 t}) = 2 := by
  have h := finrank_span_eq_card (vecL_linearIndependent (k := k) ht)
  rw [range_pair_vec] at h
  simpa using h

theorem finrank_span_vecM {t : Vec k 1} (ht : t ≠ 0) :
    Module.finrank k (Submodule.span k {vecM1 t, vecM2 t}) = 2 := by
  have h := finrank_span_eq_card (vecM_linearIndependent (k := k) ht)
  rw [range_pair_vec] at h
  simpa using h

theorem L_isProjectiveLine (t : P k 1) : IsProjectiveLine (L t) := by
  obtain ⟨t', ht', rfl⟩ := exists_mk t
  refine ⟨Submodule.span k {vecL1 t', vecL2 t'}, finrank_span_vecL ht', ?_⟩
  ext p
  constructor
  · rintro ⟨⟨u, v⟩, hv, hp⟩
    simp only [segrePair, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff] at hv hp
    obtain ⟨-, rfl⟩ := hv
    subst hp
    obtain ⟨u', hu', rfl⟩ := exists_mk u
    refine ⟨segreVec u' t', segreVec_ne_zero hu' ht', ?_, ?_⟩
    · rw [segreVec_eq_vecL]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [segre_mk]
  · rintro ⟨v, hv0, hvW, hmk⟩
    rw [Submodule.mem_span_pair] at hvW
    obtain ⟨a, b, hab⟩ := hvW
    have hu : (![a, b] : Vec k 1) ≠ 0 := by
      intro hc
      obtain ⟨ha, hb⟩ := vec2_eq_zero_iff.1 hc
      apply hv0
      rw [← hab, ha, hb]
      simp
    rw [mem_L]
    refine ⟨mk hu, ?_⟩
    rw [← hmk, segre_mk]
    congr 1
    rw [segreVec_pairL, hab]

theorem M_isProjectiveLine (t : P k 1) : IsProjectiveLine (M t) := by
  obtain ⟨t', ht', rfl⟩ := exists_mk t
  refine ⟨Submodule.span k {vecM1 t', vecM2 t'}, finrank_span_vecM ht', ?_⟩
  ext p
  constructor
  · rintro ⟨⟨u, v⟩, hv, hp⟩
    simp only [segrePair, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff] at hv hp
    obtain ⟨rfl, -⟩ := hv
    subst hp
    obtain ⟨u', hu', rfl⟩ := exists_mk v
    refine ⟨segreVec t' u', segreVec_ne_zero ht' hu', ?_, ?_⟩
    · rw [segreVec_eq_vecM]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [segre_mk]
  · rintro ⟨v, hv0, hvW, hmk⟩
    rw [Submodule.mem_span_pair] at hvW
    obtain ⟨a, b, hab⟩ := hvW
    have hu : (![a, b] : Vec k 1) ≠ 0 := by
      intro hc
      obtain ⟨ha, hb⟩ := vec2_eq_zero_iff.1 hc
      apply hv0
      rw [← hab, ha, hb]
      simp
    rw [mem_M]
    refine ⟨mk hu, ?_⟩
    rw [← hmk, segre_mk]
    congr 1
    rw [segreVec_pairM, hab]

/-! ## 6. Forms in two variables have finite zero loci in `P¹` -/

section Infinite

variable [Infinite k]

/-- Substitution of one-variable polynomials for the two variables of `k[x₀,x₁]`. -/
noncomputable def substP (g : Fin 2 → Polynomial k) (f : Poly k 1) : Polynomial k :=
  MvPolynomial.eval₂ Polynomial.C g f

theorem eval_substP (g : Fin 2 → Polynomial k) (t : k) (f : Poly k 1) :
    (substP g f).eval t = MvPolynomial.eval (fun i => Polynomial.eval t (g i)) f := by
  have hcomp : (Polynomial.evalRingHom t).comp (Polynomial.C (R := k)) = RingHom.id k := by
    ext a; simp
  have h := RingHom.congr_fun
    (MvPolynomial.comp_eval₂Hom (Polynomial.C (R := k)) g (Polynomial.evalRingHom t)) f
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom] at h
  rw [substP, show MvPolynomial.eval₂ (Polynomial.C (R := k)) g f
    = MvPolynomial.eval₂Hom (Polynomial.C (R := k)) g f from rfl, h, hcomp]
  rfl

/-- Dehomogenisation `f(x₀,x₁) ↦ f(1,x₁)`: setting the first coordinate to `1`. -/
noncomputable def dehom (f : Poly k 1) : Polynomial k :=
  substP (fun i : Fin 2 => if (i : ℕ) = 0 then 1 else Polynomial.X) f

theorem eval_dehom (t : k) (f : Poly k 1) :
    (dehom f).eval t = MvPolynomial.eval (![1, t] : Vec k 1) f := by
  rw [dehom, eval_substP]
  have hg : (fun i : Fin 2 => Polynomial.eval t (if (i : ℕ) = 0 then (1 : Polynomial k) else Polynomial.X))
      = (![1, t] : Vec k 1) := by
    funext i
    fin_cases i <;> simp
  rw [hg]

/-- Setting the second coordinate to a constant. -/
noncomputable def fixSnd (v : k) (f : Poly k 1) : Polynomial k :=
  substP (fun i : Fin 2 => if (i : ℕ) = 0 then Polynomial.X else Polynomial.C v) f

theorem eval_fixSnd (v s : k) (f : Poly k 1) :
    (fixSnd v f).eval s = MvPolynomial.eval (![s, v] : Vec k 1) f := by
  rw [fixSnd, eval_substP]
  have hg : (fun i : Fin 2 => Polynomial.eval s
      (if (i : ℕ) = 0 then Polynomial.X else Polynomial.C v)) = (![s, v] : Vec k 1) := by
    funext i
    fin_cases i <;> simp
  rw [hg]

theorem vec2_smul (s : k) (v : k) (hs : s ≠ 0) :
    (s • (![1, v / s] : Vec k 1)) = ![s, v] := by
  funext i
  fin_cases i
  · simp
  · show s * (v / s) = v
    exact mul_div_cancel₀ v hs

theorem dehom_ne_zero {f : Poly k 1} {d : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    dehom f ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ : ∃ x : Vec k 1, MvPolynomial.eval x f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (MvPolynomial.funext (fun y => by rw [h y]; simp))
  by_cases hx0 : x 0 = 0
  · -- `f(S,x₁)` is nonzero (value at `0`) but vanishes at every `s ≠ 0`
    have hxeq : x = ![0, x 1] := by
      funext i; fin_cases i <;> simp [hx0]
    have hR0 : (fixSnd (x 1) f).eval 0 ≠ 0 := by
      rw [eval_fixSnd, ← hxeq]; exact hx
    have hinf : {s : k | (fixSnd (x 1) f).IsRoot s}.Infinite := by
      refine (Set.Finite.infinite_compl (Set.finite_singleton (0 : k))).mono ?_
      intro s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
      rw [eval_fixSnd, ← vec2_smul s (x 1) hs, eval_smul_of_isHomogeneous hf,
        ← eval_dehom, hzero]
      simp
    rw [Polynomial.eq_zero_of_infinite_isRoot _ hinf] at hR0
    simp at hR0
  · -- `x₀ ≠ 0`: evaluate the dehomogenisation at `x₁/x₀`
    have hxeq : x = x 0 • (![1, x 1 / x 0] : Vec k 1) := by
      funext i
      fin_cases i
      · simp
      · show x 1 = x 0 * (x 1 / x 0)
        exact (mul_div_cancel₀ (x 1) hx0).symm
    have hne : (dehom f).eval (x 1 / x 0) ≠ 0 := by
      rw [eval_dehom]
      intro hc
      apply hx
      rw [hxeq, eval_smul_of_isHomogeneous hf, hc, mul_zero]
    rw [hzero] at hne
    simp at hne

theorem mem_zeroLocus_singleton_iff {f : Poly k 1} {d : ℕ} (hf : f.IsHomogeneous d)
    {v : Vec k 1} (hv : v ≠ 0) :
    mk hv ∈ zeroLocus ({f} : Set (Poly k 1)) ↔ MvPolynomial.eval v f = 0 := by
  rw [mem_zeroLocus_iff]
  · simp
  · intro g hg
    rw [Set.mem_singleton_iff] at hg
    exact ⟨d, hg ▸ hf⟩

/-- The point `(0 : 1)` of `P¹`. -/
def pt01 : P k 1 := mk (vec2_ne_zero_right (a := (0 : k)) (b := (1 : k)) one_ne_zero)

/-- The point `(1 : t)` of `P¹`. -/
def pt1 (t : k) : P k 1 := mk (vec2_ne_zero_left (a := (1 : k)) (b := t) one_ne_zero)

theorem pt1_injective : Function.Injective (pt1 (k := k)) := by
  intro t s h
  obtain ⟨c, hc, hcs⟩ :=
    (mk_eq_mk_iff (vec2_ne_zero_left (a := (1 : k)) (b := t) one_ne_zero)
      (vec2_ne_zero_left (a := (1 : k)) (b := s) one_ne_zero)).1 h
  have h0 := congrFun hcs (0 : Fin 2)
  have h1 := congrFun hcs (1 : Fin 2)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one] at h0 h1
  calc t = c * s := h1
    _ = s := by rw [← h0, one_mul]

/-- **The zero locus of a nonzero form of degree `d` in two variables is finite.** -/
theorem finite_zeroLocus_singleton {f : Poly k 1} (hf0 : f ≠ 0) {d : ℕ}
    (hf : f.IsHomogeneous d) : (zeroLocus ({f} : Set (Poly k 1))).Finite := by
  have hdehom : dehom f ≠ 0 := dehom_ne_zero hf hf0
  have hfin : {t : k | (dehom f).IsRoot t}.Finite := Polynomial.finite_setOfPred_isRoot hdehom
  have himg : (pt1 (k := k) '' {t : k | (dehom f).IsRoot t}).Finite := hfin.image _
  have hins : (insert (pt01 (k := k)) (pt1 (k := k) '' {t : k | (dehom f).IsRoot t})).Finite :=
    Set.Finite.insert _ himg
  refine hins.subset ?_
  intro p hp
  obtain ⟨x, hx, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_singleton_iff hf hx] at hp
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro h
      apply hx
      funext i; fin_cases i <;> simp [hx0, h]
    have hxeq : x = x 1 • (![0, 1] : Vec k 1) := by
      funext i; fin_cases i <;> simp [hx0]
    refine Set.mem_insert_iff.2 (Or.inl ?_)
    rw [show (mk hx : P k 1) = pt01 (k := k) from
      (mk_eq_mk_iff hx _).2 ⟨x 1, hx1, hxeq⟩]
  · have hxeq : x = x 0 • (![1, x 1 / x 0] : Vec k 1) := by
      funext i
      fin_cases i
      · simp
      · show x 1 = x 0 * (x 1 / x 0)
        exact (mul_div_cancel₀ (x 1) hx0).symm
    refine Set.mem_insert_iff.2 (Or.inr ?_)
    have hmk : (mk hx : P k 1) = pt1 (x 1 / x 0) :=
      (mk_eq_mk_iff hx _).2 ⟨x 0, hx0, hxeq⟩
    rw [hmk]
    refine Set.mem_image_of_mem _ ?_
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
    rw [eval_dehom]
    rw [hxeq, eval_smul_of_isHomogeneous hf] at hp
    rcases mul_eq_zero.1 hp with h' | h'
    · exact absurd h' (pow_ne_zero d hx0)
    · exact h'

theorem pt01_ne_pt1_zero : pt01 (k := k) ≠ pt1 (k := k) 0 := by
  intro h
  obtain ⟨c, hc, hcs⟩ :=
    (mk_eq_mk_iff (vec2_ne_zero_right (a := (0 : k)) (b := (1 : k)) one_ne_zero)
      (vec2_ne_zero_left (a := (1 : k)) (b := (0 : k)) one_ne_zero)).1 h
  have h0 := congrFun hcs (0 : Fin 2)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    mul_one] at h0
  exact hc h0.symm

theorem infinite_P1 : Infinite (P k 1) :=
  Infinite.of_injective (pt1 (k := k)) pt1_injective

/-- **`P¹` is not the union of two proper closed subsets**: two nonempty Zariski-open sets meet.
This is the irreducibility of the projective line, proved from the finiteness of the zero locus
of a nonzero form in two variables. -/
theorem zeroLocus_singleton_eq_univ_imp_eq_zero {h : Poly k 1} {e : ℕ} (hh : h.IsHomogeneous e)
    (huniv : zeroLocus ({h} : Set (Poly k 1)) = Set.univ) : h = 0 := by
  have hmem : ∀ v : Vec k 1, v ≠ 0 → MvPolynomial.eval v h = 0 := by
    intro v hv
    have h1 : mk hv ∈ zeroLocus ({h} : Set (Poly k 1)) := by
      rw [huniv]; exact Set.mem_univ _
    rwa [mem_zeroLocus_singleton_iff hh hv] at h1
  have hpt : MvPolynomial.eval (![1, 0] : Vec k 1) h = 0 :=
    hmem _ (vec2_ne_zero_left (a := (1 : k)) (b := (0 : k)) one_ne_zero)
  have h0 : MvPolynomial.eval (0 : Vec k 1) h = 0 := by
    have hsm := eval_smul_of_isHomogeneous hh (0 : k) (![1, 0] : Vec k 1)
    rw [zero_smul, hpt, mul_zero] at hsm
    exact hsm
  refine MvPolynomial.funext (fun x => ?_)
  rw [map_zero]
  by_cases hx : x = 0
  · rw [hx]; exact h0
  · exact hmem x hx

theorem mem_zeroLocus_singleton_iff' {h : Poly k 1} {p : P k 1} :
    p ∈ zeroLocus ({h} : Set (Poly k 1)) ↔ FormVanishesAt h p := by
  simp [zeroLocus]

theorem mem_zeroLocus_singleton_iff_gen {n : ℕ} {h : Poly k n} {p : P k n} :
    p ∈ zeroLocus ({h} : Set (Poly k n)) ↔ FormVanishesAt h p := by
  simp [zeroLocus]

theorem proportional_of_forall_minor {n : ℕ} {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ i j : Fin (n + 1), v i * w j = v j * w i) : ∃ c : k, c ≠ 0 ∧ w = c • v := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv
  refine ⟨w i₀ / v i₀, div_ne_zero ?_ hi₀, ?_⟩
  · intro h0
    apply hw
    funext j
    have := h i₀ j
    rw [h0, mul_zero] at this
    simp only [Pi.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left hi₀
  · funext j
    have := h i₀ j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi₀]
    rw [mul_comm (w j) (v i₀), this, mul_comm]

theorem formVanishesAt_mul_iff {f g : Poly k 1} {df dg : ℕ} (hf : f.IsHomogeneous df)
    (hg : g.IsHomogeneous dg) {p : P k 1} :
    FormVanishesAt (f * g) p ↔ FormVanishesAt f p ∨ FormVanishesAt g p := by
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [formVanishesAt_mk_iff (hf.mul hg) hv, formVanishesAt_mk_iff hf hv,
    formVanishesAt_mk_iff hg hv, map_mul, mul_eq_zero]

/-- **`P¹` is not the union of two proper closed subsets**: two nonempty Zariski-open sets meet.
This is the irreducibility of the projective line, proved from the finiteness of the zero locus
of a nonzero form in two variables. -/
theorem P1_open_inter_nonempty {U V : Set (P k 1)} (hU : IsOpen U) (hV : IsOpen V)
    (hUne : U.Nonempty) (hVne : V.Nonempty) : (U ∩ V).Nonempty := by
  by_contra hdis
  have hinter : U ∩ V = ∅ := Set.not_nonempty_iff_eq_empty.1 hdis
  obtain ⟨T, hT, hTU⟩ := (isClosed_iff_exists_zeroLocus (n := 1)).1 hU.isClosed_compl
  obtain ⟨T', hT', hTV⟩ := (isClosed_iff_exists_zeroLocus (n := 1)).1 hV.isClosed_compl
  -- every point lies in `V(T)` or in `V(T')`
  have hcov : (zeroLocus T) ∪ (zeroLocus T') = Set.univ := by
    rw [← hTU, ← hTV, ← Set.compl_inter, hinter, Set.compl_empty]
  -- nonzero forms witnessing nonemptiness of the two open sets
  have hex : ∃ f ∈ T, f ≠ 0 := by
    obtain ⟨p, hp⟩ := hUne
    have hp' : p ∉ zeroLocus T := by
      rw [← hTU]; exact fun hc => hc hp
    simp only [zeroLocus, Set.mem_ofPred_eq] at hp'
    push Not at hp'
    obtain ⟨f, hfT, hfp⟩ := hp'
    refine ⟨f, hfT, ?_⟩
    rintro rfl
    exact hfp (fun v _ _ => by simp)
  have hex' : ∃ g ∈ T', g ≠ 0 := by
    obtain ⟨p, hp⟩ := hVne
    have hp' : p ∉ zeroLocus T' := by
      rw [← hTV]; exact fun hc => hc hp
    simp only [zeroLocus, Set.mem_ofPred_eq] at hp'
    push Not at hp'
    obtain ⟨g, hgT, hgp⟩ := hp'
    refine ⟨g, hgT, ?_⟩
    rintro rfl
    exact hgp (fun v _ _ => by simp)
  obtain ⟨f, hfT, hf0⟩ := hex
  obtain ⟨g, hgT, hg0⟩ := hex'
  obtain ⟨df, hdf⟩ := hT f hfT
  obtain ⟨dg, hdg⟩ := hT' g hgT
  -- `f * g` vanishes everywhere, so it is zero, contradicting `f, g ≠ 0`
  have huniv : zeroLocus ({f * g} : Set (Poly k 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun r => ?_
    have hr : r ∈ zeroLocus T ∪ zeroLocus T' := by rw [hcov]; exact Set.mem_univ r
    rw [mem_zeroLocus_singleton_iff', formVanishesAt_mul_iff hdf hdg]
    rcases hr with hr | hr
    · exact Or.inl (hr f hfT)
    · exact Or.inr (hr g hgT)
  exact mul_ne_zero hf0 hg0 (zeroLocus_singleton_eq_univ_imp_eq_zero (hdf.mul hdg) huniv)

/-! ## 7. Part (c): the diagonal conic and the non-homeomorphism -/

/-- The hyperplane `x₁ = x₂` of `P³`. -/
def hyperplane : Set (P k 3) := zeroLocus ({MvPolynomial.X (1 : Fin 4) - MvPolynomial.X 2} :
  Set (Poly k 3))

theorem isHomogeneous_hyperplane_mem : ∀ f ∈ ({MvPolynomial.X (1 : Fin 4) - MvPolynomial.X 2} :
    Set (Poly k 3)), ∃ d, f.IsHomogeneous d := by
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  refine ⟨1, hf ▸ ?_⟩
  exact (isHomogeneous_X4 (k := k) 1).sub (isHomogeneous_X4 (k := k) 2)

theorem isClosed_hyperplane : IsClosed (hyperplane (k := k)) :=
  isClosed_zeroLocus isHomogeneous_hyperplane_mem

theorem mk_congr {v w : Vec k 3} (hv : v ≠ 0) (hw : w ≠ 0) (h : v = w) : mk hv = mk hw := by
  subst h
  rfl

/-- The diagonal `Δ ⊆ P¹ × P¹`. -/
def diag : Set (P k 1 × P k 1) := {p | p.1 = p.2}

/-- The image of the diagonal: the conic `{(s² : st : st : t²)} ⊆ Q`. -/
def conic : Set (P k 3) := segrePair '' diag

theorem conic_subset_quadric : conic (k := k) ⊆ quadric := by
  rintro p ⟨⟨t, u⟩, h, rfl⟩
  simp only [diag, Set.mem_ofPred_eq] at h
  subst h
  exact segre_mem_quadric t t

theorem conic_subset_hyperplane : conic (k := k) ⊆ hyperplane := by
  rintro p ⟨⟨t, u⟩, h, rfl⟩
  simp only [diag, Set.mem_ofPred_eq] at h
  subst h
  obtain ⟨v, hv, rfl⟩ := exists_mk t
  rw [hyperplane]
  refine (mem_zeroLocus_iff isHomogeneous_hyperplane_mem
    (segreVec_ne_zero hv hv)).2 ?_
  simp [segreVec]
  ring

/-- Two vectors of `k²` are proportional when the corresponding `2 × 2` matrix is symmetric. -/
theorem proportional_of_mul_comm {a b : Vec k 1} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a 0 * b 1 = a 1 * b 0) : ∃ c : k, c ≠ 0 ∧ b = c • a := by
  by_cases ha0 : a 0 = 0
  · have ha1 : a 1 ≠ 0 := by
      rcases vec1_ne_zero_iff.1 ha with h' | h'
      · exact absurd ha0 h'
      · exact h'
    have hb0 : b 0 = 0 := by
      have h' : a 1 * b 0 = 0 := by rw [← h, ha0, zero_mul]
      exact (mul_eq_zero.1 h').resolve_left ha1
    have hb1 : b 1 ≠ 0 := by
      rcases vec1_ne_zero_iff.1 hb with h' | h'
      · exact absurd hb0 h'
      · exact h'
    refine ⟨b 1 / a 1, div_ne_zero hb1 ha1, ?_⟩
    funext i
    fin_cases i
    · simp [hb0, ha0]
    · show b 1 = b 1 / a 1 * a 1
      rw [div_mul_cancel₀ _ ha1]
  · have hb0 : b 0 ≠ 0 := by
      intro h'
      have h2 : a 0 * b 1 = 0 := by rw [h, h', mul_zero]
      exact hb (by funext i; fin_cases i <;> simp [h', (mul_eq_zero.1 h2).resolve_left ha0])
    refine ⟨b 0 / a 0, div_ne_zero hb0 ha0, ?_⟩
    funext i
    fin_cases i
    · show b 0 = b 0 / a 0 * a 0
      rw [div_mul_cancel₀ _ ha0]
    · show b 1 = b 0 / a 0 * a 1
      rw [div_mul_eq_mul_div, eq_div_iff ha0, mul_comm (b 1) (a 0), h, mul_comm]


theorem quadric_inter_hyperplane_subset_conic : quadric ∩ hyperplane ⊆ conic (k := k) := by
  rintro p ⟨hpq, hph⟩
  obtain ⟨x, hx, rfl⟩ := exists_mk p
  obtain ⟨v, w, hv, hw, hvw⟩ := quadric_exists_segre x hx (by
    rw [mem_quadric_iff hx, eval_quadForm] at hpq
    exact sub_eq_zero.1 hpq)
  have h12 : x 1 = x 2 := by
    rw [hyperplane, mem_zeroLocus_iff isHomogeneous_hyperplane_mem hx] at hph
    have hph' : MvPolynomial.eval x (MvPolynomial.X (1 : Fin 4) - MvPolynomial.X 2) = 0 :=
      hph _ (Set.mem_singleton_iff.2 rfl)
    have hph'' : x 1 - x 2 = 0 := by simpa using hph'
    exact sub_eq_zero.1 hph''
  have hsym : v 0 * w 1 = v 1 * w 0 := by
    have h1 : segreVec v w 1 = segreVec v w 2 := by rw [hvw]; exact h12
    simpa [segreVec] using h1
  obtain ⟨c, hc, hcw⟩ := proportional_of_mul_comm hv hw hsym
  have hsw : segreVec v w = c • segreVec v v := by
    rw [hcw]
    funext i
    fin_cases i <;> simp [segreVec, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨(mk hv, mk hv), ?_, ?_⟩
  · simp [diag]
  · have hmk : mk hx = mk (segreVec_ne_zero hv hv) :=
      (mk_eq_mk_iff hx (segreVec_ne_zero hv hv)).2 ⟨c, hc, by rw [← hvw, hsw]⟩
    show segre (mk hv) (mk hv) = mk hx
    rw [segre_mk, hmk]

theorem isClosed_quadric : IsClosed (quadric (k := k)) :=
  isClosed_zeroLocus isHomogeneous_quadForm_mem

theorem conic_eq_quadric_inter_hyperplane : conic (k := k) = quadric ∩ hyperplane := by
  refine Set.Subset.antisymm ?_ quadric_inter_hyperplane_subset_conic
  intro p hp
  exact ⟨conic_subset_quadric hp, conic_subset_hyperplane hp⟩

theorem isClosed_conic : IsClosed (conic (k := k)) := by
  rw [conic_eq_quadric_inter_hyperplane]
  exact isClosed_quadric.inter isClosed_hyperplane

/-- **The diagonal is not closed in the product topology** on `P¹ × P¹`. -/
theorem diag_not_closed : ¬ IsClosed (diag (k := k)) := by
  intro hc
  have hopen : IsOpen ((diag (k := k))ᶜ) := hc.isOpen_compl
  have hmem : ((pt01 (k := k), pt1 (k := k) 0) : P k 1 × P k 1) ∈ (diag (k := k))ᶜ := by
    simp only [Set.mem_compl_iff, diag, Set.mem_ofPred_eq]
    exact pt01_ne_pt1_zero
  obtain ⟨U, V, hU, hV, h1, h2, hUV⟩ := isOpen_prod_iff.1 hopen _ _ hmem
  obtain ⟨w, hwU, hwV⟩ := P1_open_inter_nonempty hU hV ⟨_, h1⟩ ⟨_, h2⟩
  have h3 : (w, w) ∈ U ×ˢ V := ⟨hwU, hwV⟩
  have h4 := hUV h3
  simp only [Set.mem_compl_iff, diag, Set.mem_ofPred_eq] at h4
  exact absurd trivial h4

/-! ## 8. The affine chart of the conic and its Zariski topology -/

theorem poly_eq_zero_of_forall_eval_eq_zero {q : Polynomial k}
    (h : ∀ u : k, q.eval u = 0) : q = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot (p := q) ?_
  refine Set.Infinite.mono ?_ (Set.infinite_univ (α := k))
  intro u _
  show q.IsRoot u
  rw [Polynomial.IsRoot.def]
  exact h u

/-- Substitution of one-variable polynomials for the four coordinates, evaluated at a scalar. -/
theorem eval_substPoly4 (g : Fin 4 → Polynomial k) (t : k) (F : Poly k 3) :
    (MvPolynomial.eval₂ Polynomial.C g F).eval t
      = MvPolynomial.eval (fun i => Polynomial.eval t (g i)) F := by
  have hcomp : (Polynomial.evalRingHom t).comp (Polynomial.C (R := k)) = RingHom.id k := by
    ext a; simp
  have h := RingHom.congr_fun
    (MvPolynomial.comp_eval₂Hom (Polynomial.C (R := k)) g (Polynomial.evalRingHom t)) F
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom] at h
  rw [show MvPolynomial.eval₂ (Polynomial.C (R := k)) g F
    = MvPolynomial.eval₂Hom (Polynomial.C (R := k)) g F from rfl, h, hcomp]
  rfl

/-- The substitution `F ↦ F(1, U, U, U²)` defining the affine chart of the conic. -/
noncomputable def chartSubst (F : Poly k 3) : Polynomial k :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => (![1, Polynomial.X, Polynomial.X, Polynomial.X * Polynomial.X] :
      Fin 4 → Polynomial k) i) F

theorem eval_chartSubst (u : k) (F : Poly k 3) :
    (chartSubst F).eval u = MvPolynomial.eval (![1, u, u, u * u] : Vec k 3) F := by
  rw [chartSubst, eval_substPoly4]
  have hg : (fun i : Fin 4 => Polynomial.eval u
      ((![1, Polynomial.X, Polynomial.X, Polynomial.X * Polynomial.X] : Fin 4 → Polynomial k) i))
      = (![1, u, u, u * u] : Vec k 3) := by
    funext i
    fin_cases i <;> simp
  rw [hg]

/-- The substitution `F ↦ F(U², U, U, 1)`, used to pass to the point at infinity. -/
noncomputable def infSubst (F : Poly k 3) : Polynomial k :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => (![Polynomial.X * Polynomial.X, Polynomial.X, Polynomial.X, 1] :
      Fin 4 → Polynomial k) i) F

theorem eval_infSubst (u : k) (F : Poly k 3) :
    (infSubst F).eval u = MvPolynomial.eval (![u * u, u, u, 1] : Vec k 3) F := by
  rw [infSubst, eval_substPoly4]
  have hg : (fun i : Fin 4 => Polynomial.eval u
      ((![Polynomial.X * Polynomial.X, Polynomial.X, Polynomial.X, 1] : Fin 4 → Polynomial k) i))
      = (![u * u, u, u, 1] : Vec k 3) := by
    funext i
    fin_cases i <;> simp
  rw [hg]

theorem vec4_ne_zero_left {a b c d : k} (ha : a ≠ 0) : (![a, b, c, d] : Vec k 3) ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 4)
  simp at this
  exact ha this

theorem vec4_ne_zero_last {a b c d : k} (hd : d ≠ 0) : (![a, b, c, d] : Vec k 3) ≠ 0 := by
  intro h
  have := congrFun h (3 : Fin 4)
  simp at this
  exact hd this

/-- The affine chart point `(1 : u : u : u²)` of the conic. -/
def chartPt (u : k) : P k 3 :=
  mk (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u) (d := u * u) one_ne_zero)

/-- The point `(0 : 0 : 0 : 1)` of the conic, "at infinity" for the chart. -/
def pInf : P k 3 := mk (vec4_ne_zero_last (a := (0 : k)) (b := (0 : k)) (c := (0 : k)) (d := (1 : k))
  one_ne_zero)

theorem chartPt_injective : Function.Injective (chartPt (k := k)) := by
  intro u v h
  obtain ⟨c, hc, hcs⟩ :=
    (mk_eq_mk_iff (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u) (d := u * u) one_ne_zero)
      (vec4_ne_zero_left (a := (1 : k)) (b := v) (c := v) (d := v * v) one_ne_zero)).1 h
  have h0 := congrFun hcs (0 : Fin 4)
  have h1 := congrFun hcs (1 : Fin 4)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one] at h0 h1
  calc u = c * v := h1
    _ = v := by rw [← h0, one_mul]

theorem P1_eq_pt1_or_pt01 (t : P k 1) : t = pt01 (k := k) ∨ ∃ u : k, t = pt1 (k := k) u := by
  obtain ⟨v, hv, rfl⟩ := exists_mk t
  by_cases hv0 : v 0 = 0
  · left
    have hv1 : v 1 ≠ 0 := by
      rcases vec1_ne_zero_iff.1 hv with h' | h'
      · exact absurd hv0 h'
      · exact h'
    refine (mk_eq_mk_iff hv _).2 ⟨v 1, hv1, ?_⟩
    funext i
    fin_cases i <;> simp [hv0]
  · right
    refine ⟨v 1 / v 0, (mk_eq_mk_iff hv _).2 ⟨v 0, hv0, ?_⟩⟩
    funext i
    fin_cases i
    · simp
    · show v 1 = v 0 * (v 1 / v 0)
      exact (mul_div_cancel₀ (v 1) hv0).symm

theorem segre_pt01_self : segre (pt01 (k := k)) (pt01 (k := k)) = pInf (k := k) := by
  have h := segre_mk (v := (![0, 1] : Vec k 1)) (w := (![0, 1] : Vec k 1))
    (vec2_ne_zero_right (a := (0 : k)) (b := (1 : k)) one_ne_zero)
    (vec2_ne_zero_right (a := (0 : k)) (b := (1 : k)) one_ne_zero)
  rw [show (mk (vec2_ne_zero_right (a := (0 : k)) (b := (1 : k)) one_ne_zero) : P k 1)
    = pt01 from rfl] at h
  rw [h]
  refine mk_congr _ _ ?_
  funext i
  fin_cases i <;> simp [segreVec]

theorem segre_pt1_self (u : k) : segre (pt1 (k := k) u) (pt1 (k := k) u) = chartPt (k := k) u := by
  have h := segre_mk (v := (![1, u] : Vec k 1)) (w := (![1, u] : Vec k 1))
    (vec2_ne_zero_left (a := (1 : k)) (b := u) one_ne_zero)
    (vec2_ne_zero_left (a := (1 : k)) (b := u) one_ne_zero)
  rw [show (mk (vec2_ne_zero_left (a := (1 : k)) (b := u) one_ne_zero) : P k 1)
    = pt1 u from rfl] at h
  rw [h]
  refine mk_congr _ _ ?_
  funext i
  fin_cases i <;> simp [segreVec]

theorem chartPt_mem_conic (u : k) : chartPt (k := k) u ∈ conic (k := k) :=
  ⟨(pt1 (k := k) u, pt1 (k := k) u), by simp [diag], segre_pt1_self u⟩

theorem pInf_mem_conic : pInf (k := k) ∈ conic (k := k) :=
  ⟨(pt01 (k := k), pt01 (k := k)), by simp [diag], segre_pt01_self⟩

theorem conic_subset_chart_union :
    conic (k := k) ⊆ Set.range (chartPt (k := k)) ∪ {pInf (k := k)} := by
  rintro p ⟨⟨t, u⟩, hdiag, rfl⟩
  simp only [diag, Set.mem_ofPred_eq] at hdiag
  subst hdiag
  rcases P1_eq_pt1_or_pt01 t with rfl | ⟨s, rfl⟩
  · refine Set.mem_union_right _ ?_
    rw [show segrePair (pt01 (k := k), pt01 (k := k)) = pInf (k := k) from segre_pt01_self]
    simp
  · exact Set.mem_union_left _ ⟨s, (segre_pt1_self s).symm⟩

/-- A homogeneous form that vanishes on the affine chart of the conic also vanishes at the
point at infinity `(0:0:0:1)`. -/
theorem eval_pInf_of_vanishes_chart {F : Poly k 3} {d : ℕ} (hF : F.IsHomogeneous d)
    (h : ∀ u : k, MvPolynomial.eval (![1, u, u, u * u] : Vec k 3) F = 0) :
    MvPolynomial.eval (![0, 0, 0, 1] : Vec k 3) F = 0 := by
  have hq : chartSubst F = 0 := by
    refine poly_eq_zero_of_forall_eval_eq_zero (q := chartSubst F) (fun u => ?_)
    rw [eval_chartSubst]
    exact h u
  have hr : infSubst F = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot (p := infSubst F) ?_
    refine Set.Infinite.mono ?_ (Set.Finite.infinite_compl (Set.finite_singleton (0 : k)))
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    show (infSubst F).IsRoot s
    rw [Polynomial.IsRoot.def, eval_infSubst]
    have hscale : (![s * s, s, s, 1] : Vec k 3)
        = (s * s) • (![1, 1 / s, 1 / s, 1 / (s * s)] : Vec k 3) := by
      funext i
      fin_cases i
      · simp
      · show s = s * s * (1 / s)
        field_simp
      · show s = s * s * (1 / s)
        field_simp
      · show (1 : k) = s * s * (1 / (s * s))
        field_simp
    rw [hscale, eval_smul_of_isHomogeneous hF]
    have hzero : MvPolynomial.eval (![1, (1 / s), (1 / s), (1 / s) * (1 / s)] : Vec k 3) F = 0 :=
      h (1 / s)
    have hvec : (![1, 1 / s, 1 / s, 1 / (s * s)] : Vec k 3)
        = (![1, (1 / s), (1 / s), (1 / s) * (1 / s)] : Vec k 3) := by
      funext i
      fin_cases i <;> simp
    rw [hvec, hzero, mul_zero]
  have h0 : (infSubst F).eval 0 = 0 := by rw [hr]; simp
  rw [eval_infSubst] at h0
  simpa using h0

/-! ## 9. Separation of points, and closed points in `P³` -/

/-- Linear forms separate distinct points of `P³`. -/
theorem exists_linear_separating {p q : P k 3} (h : p ≠ q) :
    ∃ f : Poly k 3, f.IsHomogeneous 1 ∧
      FormVanishesAt f p ∧ ¬ FormVanishesAt f q := by
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  obtain ⟨w, hw, rfl⟩ := exists_mk q
  have hnp : ¬ ∃ c : k, c ≠ 0 ∧ w = c • v := by
    intro hc
    obtain ⟨c, hc0, hcw⟩ := hc
    refine h ((mk_eq_mk_iff hv hw).2 ⟨c⁻¹, inv_ne_zero hc0, ?_⟩)
    rw [hcw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hall : ¬ ∀ i j : Fin 4, v i * w j = v j * w i := by
    intro hm
    exact hnp (proportional_of_forall_minor (k := k) hv hw hm)
  push Not at hall
  obtain ⟨i₀, j₀, hij⟩ := hall
  set f : Poly k 3 := MvPolynomial.C (v i₀) * MvPolynomial.X j₀
    - MvPolynomial.C (v j₀) * MvPolynomial.X i₀ with hfdef
  have hf : f.IsHomogeneous 1 := by
    rw [hfdef]
    have h1 : (MvPolynomial.C (v i₀) * MvPolynomial.X j₀ : Poly k 3).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 4) (R := k) (v i₀)).mul
        (isHomogeneous_X4 (k := k) j₀)
    have h2 : (MvPolynomial.C (v j₀) * MvPolynomial.X i₀ : Poly k 3).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 4) (R := k) (v j₀)).mul
        (isHomogeneous_X4 (k := k) i₀)
    exact h1.sub h2
  refine ⟨f, hf, ?_, ?_⟩
  · rw [formVanishesAt_mk_iff hf hv]
    rw [hfdef]
    simp
    ring
  · intro hcon
    have hw0 : MvPolynomial.eval w f = 0 := (formVanishesAt_mk_iff hf hw).1 hcon
    rw [hfdef] at hw0
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at hw0
    exact hij (sub_eq_zero.1 hw0)

theorem closure_singleton_subset (p : P k 3) : closure ({p} : Set (P k 3)) ⊆ {p} := by
  intro q hq
  by_contra hne
  have hpq : p ≠ q := fun h => hne h.symm
  obtain ⟨f, hf, hfp, hfq⟩ := exists_linear_separating hpq
  have hsub : ({p} : Set (P k 3)) ⊆ zeroLocus ({f} : Set (Poly k 3)) := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact (mem_zeroLocus_singleton_iff_gen (h := f)).2 hfp
  have hcl : q ∉ closure ({p} : Set (P k 3)) := by
    intro hqc
    have h1 : q ∈ zeroLocus ({f} : Set (Poly k 3)) :=
      closure_minimal hsub (isClosed_zeroLocus (by
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        exact ⟨1, hg ▸ hf⟩)) hqc
    exact hfq ((mem_zeroLocus_singleton_iff_gen (h := f)).1 h1)
  exact hcl hq

theorem isClosed_singleton (p : P k 3) : IsClosed ({p} : Set (P k 3)) :=
  closure_subset_iff_isClosed.1 (closure_singleton_subset p)

instance : T1Space (P k 3) := ⟨isClosed_singleton⟩

theorem isClosed_finite {S : Set (P k 3)} (h : S.Finite) : IsClosed S :=
  h.isClosed

/-- A finite irreducible closed subset of `P³` is a single point. -/
theorem subsingleton_of_isIrreducible_finite {S : Set (P k 3)} (hS : IsIrreducible S)
    (hfin : S.Finite) : S.Subsingleton := by
  rw [Set.Subsingleton]
  intro p hp q hq
  by_contra hne
  have hsub : S ⊆ ({p} : Set (P k 3)) ∪ (S \ {p}) := by
    intro r hr
    by_cases hrp : r = p
    · exact Or.inl hrp
    · exact Or.inr ⟨hr, hrp⟩
  have h1 : IsClosed ({p} : Set (P k 3)) := isClosed_singleton p
  have h2 : IsClosed (S \ {p}) := isClosed_finite (hfin.subset Set.sdiff_subset)
  have hlt : S \ {p} ≠ S := by
    intro hEq
    have hmem : p ∈ S \ {p} := by rw [hEq]; exact hp
    exact hmem.2 rfl
  have hpre : ∀ z₁ z₂ : Set (P k 3), IsClosed z₁ → IsClosed z₂ → S ⊆ z₁ ∪ z₂ →
      S ⊆ z₁ ∨ S ⊆ z₂ := isPreirreducible_iff_isClosed_union_isClosed.1 hS.2
  rcases hpre {p} (S \ {p}) h1 h2 hsub with h' | h'
  · exact hne (Set.subset_singleton_iff.1 h' q hq).symm
  · exact hlt (Set.Subset.antisymm Set.sdiff_subset h')

/-! ## 10. The conic is a curve: irreducibility, dimension one, and it is not a line -/

/-- The chart points of a closed set in `P³` are the zero set of a set of one-variable
polynomials. -/
theorem chart_mem_closed {Z : Set (P k 3)} (hZ : IsClosed Z) :
    ∃ S : Set (Polynomial k), ∀ u : k, chartPt u ∈ Z ↔ ∀ q ∈ S, q.eval u = 0 := by
  obtain ⟨T, hT, hZT⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  refine ⟨chartSubst '' T, fun u => ?_⟩
  rw [hZT]
  show (mk (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u) (d := u * u) one_ne_zero) : P k 3)
    ∈ zeroLocus T ↔ ∀ q ∈ chartSubst '' T, q.eval u = 0
  rw [mem_zeroLocus_iff hT
    (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u) (d := u * u) one_ne_zero)]
  constructor
  · intro h q hq
    obtain ⟨F, hF, rfl⟩ := hq
    rw [eval_chartSubst]
    exact h F hF
  · intro h F hF
    rw [← eval_chartSubst]
    exact h _ (Set.mem_image_of_mem chartSubst hF)

/-- A closed set containing the affine chart of the conic contains the whole conic. -/
theorem conic_subset_of_chart_subset {Z : Set (P k 3)} (hZ : IsClosed Z)
    (h : ∀ u : k, chartPt u ∈ Z) : conic (k := k) ⊆ Z := by
  obtain ⟨T, hT, hZT⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  have hP : pInf (k := k) ∈ Z := by
    rw [hZT]
    show (mk (vec4_ne_zero_last (a := (0 : k)) (b := (0 : k)) (c := (0 : k)) (d := (1 : k))
      one_ne_zero) : P k 3) ∈ zeroLocus T
    rw [mem_zeroLocus_iff hT (vec4_ne_zero_last (a := (0 : k)) (b := (0 : k)) (c := (0 : k))
      (d := (1 : k)) one_ne_zero)]
    intro F hF
    obtain ⟨d, hd⟩ := hT F hF
    refine eval_pInf_of_vanishes_chart hd (fun u => ?_)
    have hu := h u
    rw [hZT] at hu
    exact (mem_zeroLocus_iff hT (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u)
      (d := u * u) one_ne_zero)).1 hu F hF
  intro p hp
  rcases conic_subset_chart_union hp with ⟨u, rfl⟩ | hp'
  · exact h u
  · rw [Set.mem_singleton_iff] at hp'
    rw [hp']
    exact hP

theorem pInf_ne_chartPt (u : k) : pInf (k := k) ≠ chartPt (k := k) u := by
  intro h
  obtain ⟨c, hc, hcs⟩ := (mk_eq_mk_iff (vec4_ne_zero_last (a := (0 : k)) (b := (0 : k))
    (c := (0 : k)) (d := (1 : k)) one_ne_zero)
    (vec4_ne_zero_left (a := (1 : k)) (b := u) (c := u) (d := u * u) one_ne_zero)).1 h
  have h0 := congrFun hcs (0 : Fin 4)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    mul_one] at h0
  exact hc h0.symm

/-- **The conic is irreducible.** -/
theorem irreducible_conic : IsIrreducible (conic (k := k)) := by
  refine ⟨⟨chartPt 0, chartPt_mem_conic 0⟩, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro Z₁ Z₂ hZ₁ hZ₂ hcov
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨S₁, hS₁⟩ := chart_mem_closed hZ₁
  obtain ⟨S₂, hS₂⟩ := chart_mem_closed hZ₂
  have hproper1 : ∃ q ∈ S₁, q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h1 (conic_subset_of_chart_subset hZ₁
      (fun u => (hS₁ u).2 (fun q hq => by rw [hc q hq]; simp)))
  have hproper2 : ∃ q ∈ S₂, q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h2 (conic_subset_of_chart_subset hZ₂
      (fun u => (hS₂ u).2 (fun q hq => by rw [hc q hq]; simp)))
  obtain ⟨q₁, hq₁, hq₁0⟩ := hproper1
  obtain ⟨q₂, hq₂, hq₂0⟩ := hproper2
  have hfin1 : {u : k | ∀ q ∈ S₁, q.eval u = 0}.Finite := by
    refine Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hq₁0) ?_
    intro u hu
    show q₁.IsRoot u
    rw [Polynomial.IsRoot.def]
    exact hu q₁ hq₁
  have hfin2 : {u : k | ∀ q ∈ S₂, q.eval u = 0}.Finite := by
    refine Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hq₂0) ?_
    intro u hu
    show q₂.IsRoot u
    rw [Polynomial.IsRoot.def]
    exact hu q₂ hq₂
  have hcover : ∀ u : k, (∀ q ∈ S₁, q.eval u = 0) ∨ (∀ q ∈ S₂, q.eval u = 0) := by
    intro u
    rcases hcov (chartPt_mem_conic u) with h' | h'
    · exact Or.inl ((hS₁ u).1 h')
    · exact Or.inr ((hS₂ u).1 h')
  have huniv : (Set.univ : Set k).Finite :=
    Set.Finite.subset (hfin1.union hfin2) (fun u _ => hcover u)
  exact Set.infinite_univ huniv

/-- Every proper closed subset of the conic is finite. -/
theorem finite_of_isClosed_subset_conic {Z : Set (P k 3)} (hZ : IsClosed Z)
    (hsub : Z ⊆ conic (k := k)) (hne : Z ≠ conic (k := k)) : Z.Finite := by
  obtain ⟨S, hS⟩ := chart_mem_closed hZ
  have hproper : ∃ q ∈ S, q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Set.Subset.antisymm hsub (conic_subset_of_chart_subset hZ
      (fun u => (hS u).2 (fun q hq => by rw [hc q hq]; simp))))
  obtain ⟨q, hq, hq0⟩ := hproper
  have hfin : {u : k | ∀ p ∈ S, p.eval u = 0}.Finite := by
    refine Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hq0) ?_
    intro u hu
    show q.IsRoot u
    rw [Polynomial.IsRoot.def]
    exact hu q hq
  refine (hfin.image chartPt |>.union (Set.finite_singleton pInf)).subset ?_
  intro p hp
  have hpc : p ∈ conic := hsub hp
  rcases conic_subset_chart_union hpc with ⟨u, rfl⟩ | hp'
  · exact Set.mem_union_left _ (Set.mem_image_of_mem chartPt ((hS u).1 hp))
  · rw [Set.mem_singleton_iff] at hp'
    rw [hp']
    exact Set.mem_union_right _ (Set.mem_singleton _)

/-- Hartshorne's chain condition (I.1): `S` contains a chain of `n + 1` nonempty irreducible
closed subsets of `P³`. -/
def HasChainIn (S : Set (P k 3)) (n : ℕ) : Prop :=
  ∃ Z : Fin (n + 1) → Set (P k 3),
    (∀ i, Z i ⊆ S ∧ (Z i).Nonempty ∧ IsClosed (Z i) ∧ IsIrreducible (Z i)) ∧ StrictMono Z

/-- `S` has dimension `n` in Hartshorne's sense: chains of length `n` exist, and no chain is
longer. -/
def DimEq (S : Set (P k 3)) (n : ℕ) : Prop :=
  HasChainIn S n ∧ ∀ m, HasChainIn S m → m ≤ n

theorem dim_conic : DimEq (conic (k := k)) 1 := by
  have hchain : HasChainIn (conic (k := k)) 1 := by
    refine ⟨fun i : Fin 2 => if (i : ℕ) = 0 then {chartPt 0} else conic, ?_, ?_⟩
    · intro i
      by_cases hi : (i : ℕ) = 0
      · simp only [if_pos hi]
        refine ⟨?_, ⟨chartPt 0, rfl⟩, isClosed_singleton _, isIrreducible_singleton⟩
        intro p hp
        have hp' : p = chartPt 0 := by simpa using hp
        rw [hp']
        exact chartPt_mem_conic 0
      · simp only [if_neg hi]
        exact ⟨Set.Subset.refl _, ⟨chartPt 0, chartPt_mem_conic 0⟩, isClosed_conic,
          irreducible_conic⟩
    · intro i j hij
      have hi : (i : ℕ) = 0 := by
        have h2 := hij
        simp only [Fin.lt_def] at h2
        omega
      have hj : (j : ℕ) = 1 := by
        have h2 := hij
        simp only [Fin.lt_def] at h2
        omega
      simp only [if_pos hi, if_neg (by omega : ¬(j : ℕ) = 0)]
      refine ⟨?_, ?_⟩
      · intro p hp
        have hp' : p = chartPt 0 := by simpa using hp
        rw [hp']
        exact chartPt_mem_conic 0
      · intro hc
        have hmem : pInf (k := k) ∈ conic (k := k) := pInf_mem_conic
        have h2 : pInf (k := k) = chartPt 0 := by simpa using hc hmem
        exact pInf_ne_chartPt 0 h2
  refine ⟨hchain, ?_⟩
  intro m hm
  obtain ⟨Z, hZ, hmono⟩ := hm
  by_contra hlt
  have hm2 : 2 ≤ m := by omega
  have h01 : (⟨0, by omega⟩ : Fin (m + 1)) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have h12 : (⟨1, by omega⟩ : Fin (m + 1)) < ⟨2, by omega⟩ := by simp [Fin.lt_def]
  have hne1 : Z ⟨1, by omega⟩ ≠ conic (k := k) := by
    intro hEq
    have hlt12 : Z ⟨1, by omega⟩ < Z ⟨2, by omega⟩ := hmono h12
    have h2sub : Z ⟨2, by omega⟩ ⊆ conic := (hZ _).1
    have hEq2 : Z ⟨2, by omega⟩ = Z ⟨1, by omega⟩ := by
      rw [hEq]
      exact Set.Subset.antisymm h2sub (by rw [← hEq]; exact hlt12.1)
    exact hlt12.2 (by rw [hEq2])
  have hfin1 : (Z ⟨1, by omega⟩).Finite :=
    finite_of_isClosed_subset_conic (hZ _).2.2.1 (hZ _).1 hne1
  have hsings : (Z ⟨1, by omega⟩).Subsingleton :=
    subsingleton_of_isIrreducible_finite (hZ _).2.2.2 hfin1
  have hlt01 : Z ⟨0, by omega⟩ < Z ⟨1, by omega⟩ := hmono h01
  obtain ⟨p, hp⟩ := (hZ ⟨0, by omega⟩).2.1
  have hZ0 : Z ⟨0, by omega⟩ = {p} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro q hq
      exact Set.mem_singleton_iff.2 (hsings (hlt01.1 hq) (hlt01.1 hp))
    · rintro q rfl
      exact hp
  have hZ1 : Z ⟨1, by omega⟩ = {p} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro q hq
      exact Set.mem_singleton_iff.2 (hsings hq (hlt01.1 hp))
    · rintro q rfl
      exact hlt01.1 hp
  exact hlt01.2 (by rw [hZ0, hZ1])

theorem conic_ne_L (t : P k 1) : conic (k := k) ≠ L t := by
  intro h
  have h1 : chartPt (k := k) 0 ∈ L t := h ▸ chartPt_mem_conic 0
  have h2 : chartPt (k := k) 1 ∈ L t := h ▸ chartPt_mem_conic 1
  rw [mem_L] at h1 h2
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have e1 : segrePair (a, t) = segrePair (pt1 (k := k) 0, pt1 (k := k) 0) := by
    simp only [segrePair]
    rw [ha, segre_pt1_self]
  have e2 : segrePair (b, t) = segrePair (pt1 (k := k) 1, pt1 (k := k) 1) := by
    simp only [segrePair]
    rw [hb, segre_pt1_self]
  have ht1 : t = pt1 (k := k) 0 := (Prod.ext_iff.1 (segrePair_inj e1)).2
  have ht2 : t = pt1 (k := k) 1 := (Prod.ext_iff.1 (segrePair_inj e2)).2
  have h01 : (0 : k) = 1 := pt1_injective (by rw [← ht1, ht2])
  exact zero_ne_one h01

theorem conic_ne_M (t : P k 1) : conic (k := k) ≠ M t := by
  intro h
  have h1 : chartPt (k := k) 0 ∈ M t := h ▸ chartPt_mem_conic 0
  have h2 : chartPt (k := k) 1 ∈ M t := h ▸ chartPt_mem_conic 1
  rw [mem_M] at h1 h2
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have e1 : segrePair (t, a) = segrePair (pt1 (k := k) 0, pt1 (k := k) 0) := by
    simp only [segrePair]
    rw [ha, segre_pt1_self]
  have e2 : segrePair (t, b) = segrePair (pt1 (k := k) 1, pt1 (k := k) 1) := by
    simp only [segrePair]
    rw [hb, segre_pt1_self]
  have ht1 : t = pt1 (k := k) 0 := (Prod.ext_iff.1 (segrePair_inj e1)).1
  have ht2 : t = pt1 (k := k) 1 := (Prod.ext_iff.1 (segrePair_inj e2)).1
  have h01 : (0 : k) = 1 := pt1_injective (by rw [← ht1, ht2])
  exact zero_ne_one h01

/-! ## 12. The projective coordinate change ("for suitable choice of coordinates") -/

section Coords

/-- The linear map of `k⁴` induced by a permutation of the coordinates. -/
def permVec (e : Equiv.Perm (Fin 4)) (v : Vec k 3) : Vec k 3 := fun i => v (e i)

theorem permVec_ne_zero (e : Equiv.Perm (Fin 4)) {v : Vec k 3} (hv : v ≠ 0) :
    permVec e v ≠ 0 := by
  intro h
  apply hv
  funext i
  have h1 : permVec e v (e.symm i) = 0 := by rw [h]; simp
  have h2 : permVec e v (e.symm i) = v i := by
    simp [permVec, Equiv.apply_symm_apply]
  rw [h2] at h1
  exact h1

/-- The projectivity of `P³` induced by a permutation of the coordinates. -/
def permMap (e : Equiv.Perm (Fin 4)) : P k 3 → P k 3 :=
  fun p => Quotient.liftOn p (fun v => mk (permVec_ne_zero e v.2)) (by
    intro v w hvw
    obtain ⟨c, hc, hcv⟩ := hvw
    refine (mk_eq_mk_iff (permVec_ne_zero e v.2) (permVec_ne_zero e w.2)).2 ⟨c, hc, ?_⟩
    funext i
    simp only [permVec, hcv, Pi.smul_apply, smul_eq_mul])

theorem permMap_mk (e : Equiv.Perm (Fin 4)) {v : Vec k 3} (hv : v ≠ 0) :
    permMap e (mk hv) = mk (permVec_ne_zero e hv) := rfl

theorem permMap_invol (e : Equiv.Perm (Fin 4)) (p : P k 3) : permMap e.symm (permMap e p) = p := by
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [permMap_mk, permMap_mk]
  refine mk_congr _ _ ?_
  funext i
  simp [permVec]

theorem permMap_injective (e : Equiv.Perm (Fin 4)) : Function.Injective (permMap (k := k) e) := by
  intro p q h
  have h2 := congrArg (permMap (k := k) e.symm) h
  rwa [permMap_invol, permMap_invol] at h2

/-- **"For suitable choice of coordinates"**: the projectivity of `P³` induced by the permutation
`e` of the coordinates carries the zero locus of `f` to the zero locus of the renamed form
`f(x_{e(0)}, x_{e(1)}, x_{e(2)}, x_{e(3)})`. -/
theorem permMap_image_zeroLocus (e : Equiv.Perm (Fin 4)) {f : Poly k 3} {df : ℕ}
    (hf : f.IsHomogeneous df) :
    permMap e '' zeroLocus ({f} : Set (Poly k 3))
      = zeroLocus ({MvPolynomial.rename e.symm f} : Set (Poly k 3)) := by
  ext p
  obtain ⟨u, hu, rfl⟩ := exists_mk p
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨v, hv, rfl⟩ := exists_mk q
    have h1 : mk (permVec_ne_zero e hv) = mk hu := hpq
    obtain ⟨c, hc, hcv⟩ := (mk_eq_mk_iff' (permVec_ne_zero e hv) hu).1 h1
    have hq' : MvPolynomial.eval v f = 0 :=
      (formVanishesAt_mk_iff hf hv).1 (mem_zeroLocus_singleton_iff_gen.1 hq)
    rw [mem_zeroLocus_singleton_iff_gen, formVanishesAt_mk_iff hf.rename_isHomogeneous hu,
      MvPolynomial.eval_rename]
    have : (u ∘ e.symm) = c • v := by
      funext i
      have h2 := congrFun hcv (e.symm i)
      simp only [permVec, Pi.smul_apply, smul_eq_mul, Equiv.apply_symm_apply] at h2
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      exact h2.symm
    rw [this, eval_smul_of_isHomogeneous hf, hq', mul_zero]
  · intro hp
    have hp' : MvPolynomial.eval (u ∘ e.symm) f = 0 := by
      have h2 := (mem_zeroLocus_singleton_iff_gen.1 hp)
      rwa [formVanishesAt_mk_iff hf.rename_isHomogeneous hu, MvPolynomial.eval_rename] at h2
    have hne : (u ∘ e.symm) ≠ 0 := by
      intro h
      apply hu
      funext i
      have h2 := congrFun h (e i)
      simpa [Function.comp_apply] using h2
    refine ⟨mk hne, ?_, ?_⟩
    · exact mem_zeroLocus_singleton_iff_gen.2 ((formVanishesAt_mk_iff hf hne).2 hp')
    · rw [permMap_mk]
      refine mk_congr _ _ ?_
      funext i
      simp [permVec, Function.comp_apply]

end Coords

end Infinite

/-! ## 11. Hartshorne Exercise I.2.15, assembled -/

theorem conic_eq_image_diag : conic (k := k) = segrePair (k := k) '' diag (k := k) := rfl

theorem L_eq_iff (t s : P k 1) : L t = L s ↔ t = s :=
  ⟨L_injective, fun h => by rw [h]⟩

theorem M_eq_iff (t s : P k 1) : M t = M s ↔ t = s :=
  ⟨M_injective, fun h => by rw [h]⟩


section AlgClosed

variable [IsAlgClosed k]

/-- **The Segre parametrisation is not a homeomorphism for the product topology.**  The image of
the diagonal is a closed subset of `Q`, but the diagonal itself is not closed in the product
topology on `P¹ × P¹`. -/
theorem not_homeomorph_product :
    ¬ ∀ S : Set (P k 1 × P k 1), IsClosed S ↔ IsClosed (segrePair (k := k) '' S) := by
  intro h
  refine diag_not_closed (k := k) ((h (diag (k := k))).2 ?_)
  rw [← conic_eq_image_diag]
  exact isClosed_conic

/-- **Hartshorne, Algebraic Geometry (1977), Exercise I.2.15** (the quadric surface in `P³`),
all three parts, over an algebraically closed field `k`.

(a) The quadric `Q : xy - zw = 0` in `P³` is the image of the Segre embedding
`ψ : P¹ × P¹ → P³`, `ψ(a₀:a₁;b₀:b₁) = (a₀b₀ : a₀b₁ : a₁b₀ : a₁b₁)` (in the coordinates
`(x:y:z:w) = (z₀₀ : z₁₁ : z₀₁ : z₁₀)`).
(b) `Q` contains the two families of lines `L_t = ψ(P¹ × {t})` and `M_t = ψ({t} × P¹)`,
parametrised by `t ∈ P¹`; each is a linear variety of dimension one; distinct members of one
family are disjoint, and `L_t ∩ M_u` is exactly one point, for all `t, u`.
(c) `Q` contains the curve `C = ψ(Δ)` (the image of the diagonal, a conic), which is not one of
the lines; and consequently the Zariski topology on `Q` is not homeomorphic via `ψ` to the
product topology on `P¹ × P¹`. -/
theorem hartshorne_I_2_15 (k : Type*) [Field k] [IsAlgClosed k] :
    (Set.range (fun p : P k 1 × P k 1 => segre p.1 p.2) = quadric (k := k)) ∧
    (∀ t : P k 1, L t ⊆ quadric (k := k) ∧ IsProjectiveLine (L t)) ∧
    (∀ t : P k 1, M t ⊆ quadric (k := k) ∧ IsProjectiveLine (M t)) ∧
    (∀ t s : P k 1, L t = L s ↔ t = s) ∧
    (∀ t s : P k 1, M t = M s ↔ t = s) ∧
    (∀ t s : P k 1, t ≠ s → Disjoint (L t) (L s)) ∧
    (∀ t s : P k 1, t ≠ s → Disjoint (M t) (M s)) ∧
    (∀ t u : P k 1, L t ∩ M u = {segre u t}) ∧
    (IsClosed (conic (k := k)) ∧ IsIrreducible (conic (k := k)) ∧ DimEq (conic (k := k)) 1) ∧
    (∀ t : P k 1, conic (k := k) ≠ L t ∧ conic (k := k) ≠ M t) ∧
    (¬ IsClosed (diag (k := k))) ∧
    (¬ ∀ S : Set (P k 1 × P k 1), IsClosed S ↔ IsClosed (segrePair (k := k) '' S)) :=
  ⟨range_segre, fun t => ⟨L_subset_quadric t, L_isProjectiveLine t⟩,
    fun t => ⟨M_subset_quadric t, M_isProjectiveLine t⟩,
    fun t s => L_eq_iff t s, fun t s => M_eq_iff t s,
    fun _ _ => L_disjoint, fun _ _ => M_disjoint, fun t u => L_inter_M t u,
    ⟨isClosed_conic, irreducible_conic, dim_conic⟩,
    fun t => ⟨conic_ne_L t, conic_ne_M t⟩,
    diag_not_closed, not_homeomorph_product⟩


/-- The coordinate permutation `(x, y, z, w) = (z₀₀, z₁₁, z₀₁, z₁₀)` of Hartshorne's statement:
`σ` sends the Segre coordinate `X₀, X₁, X₂, X₃` to `x, z, w, y`. -/
def coordsPerm : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem rename_coordsPerm :
    MvPolynomial.rename coordsPerm (quadForm (k := k)) =
      MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3 := by
  simp [quadForm, coordsPerm]

/-- **Part (a) in Hartshorne's own coordinates.**  The projective coordinate change
`(x : y : z : w) = (z₀₀ : z₁₁ : z₀₁ : z₁₀)` carries the Segre image onto the quadric
`xy - zw = 0`, exactly as the book states ("Q is equal to the Segre embedding of `P¹ × P¹` in
`P³`, for suitable choice of coordinates"). -/
theorem exists_coordinates_quadric :
    ∃ e : Equiv.Perm (Fin 4), permMap e '' quadric (k := k)
      = zeroLocus ({MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3} :
          Set (Poly k 3)) := by
  refine ⟨coordsPerm.symm, ?_⟩
  rw [quadric, permMap_image_zeroLocus coordsPerm.symm (quadForm_isHomogeneous (k := k)),
    Equiv.symm_symm, rename_coordsPerm]

end AlgClosed

/-! ## Axiom audit -/


end P

end

end Hartshorne77.Ex_I_2_15

/-! # New material: the primality gate, the bridge to the accepted I.2.8 model, and the two
missing geometric clauses `IsIrreducible quadric`, `DimEq quadric 2`.

The gate `(Ideal.span {X₀X₃ - X₁X₂}).IsPrime` is obtained from `Irreducible (X₀X₃ - X₁X₂)`,
proved by the linear-in-one-variable criterion `MvPolynomial.irreducible_mul_X_add` (the
technique of the installed I.2.16 proof), with no change of coordinates.

The dimension is transferred from the accepted I.2.8 hypersurface theorem
`Copy8.Proj.projDim_zeroSet` through an explicit homeomorphism `P k n ≃ Copy8.Proj k n`
(both models are the set of lines through the origin of `k^{n+1}`); its closed-set
correspondence and the chain transfer are proved below, not assumed. -/

namespace Hartshorne77.Ex_I_2_15
namespace P

section Gate
variable {k : Type*} [Field k]

/-- A common divisor of a variable and of a product of two further variables is a unit.
(This is the coprimality lemma of the accepted I.2.16 proof, copied.) -/
lemma isUnit_of_dvd_X_of_dvd_X_mul_X {σ : Type*} [DecidableEq σ] {i j l : σ} (hji : j ≠ i)
    (hli : l ≠ i) {r : MvPolynomial σ k} (h0 : r ∣ MvPolynomial.X i)
    (h1 : r ∣ MvPolynomial.X j * MvPolynomial.X l) : IsUnit r := by
  rcases (MvPolynomial.X_prime (i := i) (R := k)).irreducible.dvd_iff.mp h0 with hu | hass
  · exact hu
  · exfalso
    have h : (MvPolynomial.X i : MvPolynomial σ k) ∣ r := hass.dvd
    have h2 : (MvPolynomial.X i : MvPolynomial σ k) ∣ MvPolynomial.X j * MvPolynomial.X l :=
      h.trans h1
    rcases (MvPolynomial.X_prime (i := i) (R := k)).dvd_or_dvd h2 with h' | h'
    · rcases h' with ⟨v, hv⟩
      have hc := congrArg (MvPolynomial.eval (Pi.single j (1 : k))) hv
      simp [Pi.single_eq_of_ne (M := fun _ => k) (Ne.symm hji)] at hc
    · rcases h' with ⟨v, hv⟩
      have hc := congrArg (MvPolynomial.eval (Pi.single l (1 : k))) hv
      simp [Pi.single_eq_of_ne (M := fun _ => k) (Ne.symm hli)] at hc

/-- The two coefficients `X₀` and `X₁X₂` of the quadric equation in the variable `X₃` are
relatively prime. -/
lemma isRelPrime_quadForm_coeff :
    IsRelPrime (MvPolynomial.X (0 : Fin 4) : Poly k 3)
      (-(MvPolynomial.X 1 * MvPolynomial.X 2)) :=
  fun d h0 h1 => isUnit_of_dvd_X_of_dvd_X_mul_X (i := (0 : Fin 4)) (j := (1 : Fin 4))
    (l := (2 : Fin 4)) (by decide) (by decide) h0 (dvd_neg.mp h1)

/-- **The quadric equation is irreducible**: `X₀X₃ - X₁X₂` is linear in `X₃` with leading
coefficient `X₀`, and `X₀`, `X₁X₂` have no common divisor. -/
theorem irreducible_quadForm : Irreducible (quadForm (k := k)) := by
  have hfg : (MvPolynomial.X (0 : Fin 4) : Poly k 3) * MvPolynomial.X 3 +
      -(MvPolynomial.X 1 * MvPolynomial.X 2) = quadForm (k := k) := by
    simp only [quadForm]
    ring
  rw [← hfg]
  refine MvPolynomial.irreducible_mul_X_add _ _ (3 : Fin 4) (MvPolynomial.X_ne_zero 0) ?_ ?_
    isRelPrime_quadForm_coeff
  · rw [MvPolynomial.vars_X]
    simp
  · intro hmem
    have h1 : (-(MvPolynomial.X (1 : Fin 4) * MvPolynomial.X 2) : Poly k 3).vars ⊆
        ({1} : Finset (Fin 4)) ∪ {2} := by
      rw [MvPolynomial.vars_neg]
      intro x hx
      have h2 := MvPolynomial.vars_mul (MvPolynomial.X (1 : Fin 4)) (MvPolynomial.X 2) hx
      rwa [MvPolynomial.vars_X, MvPolynomial.vars_X] at h2
    have h3 := h1 hmem
    simp at h3

/-- **The gate**: `X₀X₃ - X₁X₂` is a prime element of `k[X₀,…,X₃]`. -/
theorem prime_quadForm : Prime (quadForm (k := k)) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_quadForm

/-- **The gate in ideal form**: the ideal generated by the quadric equation is prime. -/
theorem isPrime_span_quadForm : (Ideal.span {quadForm (k := k)}).IsPrime :=
  (Ideal.span_singleton_prime prime_quadForm.ne_zero).mpr prime_quadForm

end Gate

/-! ## The bridge `P k n ≃ Copy8.Proj k n` -/

section Bridge
variable {k : Type*} [Field k] {n : ℕ}

/-- The map to the accepted model of `P^n` (`Projectivization`). -/
def toProj (p : P k n) : Copy8.Proj k n :=
  Quotient.lift (fun v : {v : Vec k n // v ≠ 0} => Copy8.Proj.mk v.1 v.2) (by
    intro a b hab
    obtain ⟨c, hc, hcs⟩ := hab
    exact (Projectivization.mk_eq_mk_iff k a.1 b.1 a.2 b.2).2
      ⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0, hcs]⟩) p

theorem toProj_mk {v : Vec k n} (hv : v ≠ 0) : toProj (mk hv) = Copy8.Proj.mk v hv := rfl

/-- The inverse map, from the accepted model to `P k n`. -/
def ofProj (p : Copy8.Proj k n) : P k n :=
  Projectivization.lift (fun v : {v : Vec k n // v ≠ 0} => mk v.2) (by
    intro a b t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using ht)
    exact (mk_eq_mk_iff a.2 b.2).2 ⟨t, ht0, ht⟩) p

theorem ofProj_mk {v : Vec k n} (hv : v ≠ 0) : ofProj (Copy8.Proj.mk v hv) = mk hv := rfl

/-- **The two models of `P^n` are the same set of points.** -/
def projEquiv : P k n ≃ Copy8.Proj k n where
  toFun := toProj
  invFun := ofProj
  left_inv := by
    intro p
    induction p using Quotient.inductionOn with
    | h x => rfl
  right_inv := by
    intro p
    induction p using Projectivization.ind with
    | h v hv => rfl

theorem projEquiv_apply (p : P k n) : projEquiv p = toProj p := rfl

theorem projEquiv_symm_apply (p : Copy8.Proj k n) : projEquiv.symm p = ofProj p := rfl

theorem toProj_ofProj (p : Copy8.Proj k n) : toProj (ofProj p) = p := by
  induction p using Projectivization.ind with
  | h v hv => rfl

/-- Vanishing of a homogeneous form agrees under the identification of the two models. -/
theorem isZeroAt_toProj {f : Poly k n} {d : ℕ} (hf : f.IsHomogeneous d) (p : P k n) :
    Copy8.Proj.IsZeroAt f (toProj p) ↔ FormVanishesAt f p := by
  induction p using Quotient.inductionOn with
  | h v =>
    show Copy8.Proj.IsZeroAt f (Copy8.Proj.mk v.1 v.2) ↔ FormVanishesAt f (mk v.2)
    rw [Copy8.Proj.isZeroAt_mk_iff hf v.2, formVanishesAt_mk_iff hf v.2]

/-- The image of a projective zero locus is the zero locus of the same homogeneous forms in the
accepted model. -/
theorem image_zeroLocus (T : Set (Poly k n)) (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) :
    toProj '' zeroLocus T
      = Copy8.Proj.zeroLocus {g : Copy8.Proj.HomogPoly k n | g.1 ∈ T} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩ g hg
    obtain ⟨d, hd⟩ := hT g.1 hg
    exact (isZeroAt_toProj hd p).2 (hp g.1 hg)
  · intro hx
    exact ⟨ofProj x, by
      intro f hf
      obtain ⟨d, hd⟩ := hT f hf
      refine (isZeroAt_toProj hd (ofProj x)).1 ?_
      rw [toProj_ofProj]
      exact hx ⟨f, d, hd⟩ hf, toProj_ofProj x⟩

theorem preimage_zeroLocus (S : Set (Copy8.Proj.HomogPoly k n)) :
    toProj ⁻¹' Copy8.Proj.zeroLocus S
      = zeroLocus {f : Poly k n | ∃ D : Copy8.Proj.HomogPoly k n, D ∈ S ∧ D.1 = f} := by
  ext p
  constructor
  · intro hp f hf
    obtain ⟨D, hD, rfl⟩ := hf
    obtain ⟨dd, hdd⟩ := D.2
    exact (isZeroAt_toProj hdd p).1 (hp D hD)
  · intro hp g hg
    obtain ⟨dd, hdd⟩ := g.2
    exact (isZeroAt_toProj hdd p).2 (hp g.1 ⟨g, hg, rfl⟩)

/-- Preimages of closed sets are closed. -/
theorem isClosed_preimage_toProj {W : Set (Copy8.Proj k n)} (hW : IsClosed W) :
    IsClosed (toProj ⁻¹' W) := by
  obtain ⟨S, hS⟩ := (Copy8.Proj.isClosed_iff W).1 hW
  rw [← hS, preimage_zeroLocus]
  refine isClosed_zeroLocus (T := {f : Poly k n | ∃ D : Copy8.Proj.HomogPoly k n,
    D ∈ S ∧ D.1 = f}) ?_
  rintro f ⟨D, -, hDf⟩
  rw [← hDf]
  exact D.2

/-- Images of closed sets are closed. -/
theorem isClosed_image_toProj {Z : Set (P k n)} (hZ : IsClosed Z) :
    IsClosed (toProj '' Z) := by
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  rw [image_zeroLocus T hT]
  exact Copy8.Proj.isClosed_of_isProjClosed (Copy8.Proj.isProjClosed_zeroLocus _)

/-- **The two models have the same closed sets.** -/
theorem isClosed_image_toProj_iff (Z : Set (P k n)) :
    IsClosed (toProj '' Z) ↔ IsClosed Z := by
  refine ⟨?_, isClosed_image_toProj⟩
  intro h
  have hpre : toProj ⁻¹' (toProj '' Z) = Z := by
    ext p
    constructor
    · rintro ⟨q, hq, hqp⟩
      rw [← (projEquiv.injective hqp)]
      exact hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [← hpre]
  exact isClosed_preimage_toProj h

/-- Irreducibility is preserved and reflected. -/
theorem isPreirreducible_image_toProj_iff (Z : Set (P k n)) :
    IsPreirreducible (toProj '' Z) ↔ IsPreirreducible Z := by
  constructor
  · intro h
    rw [isPreirreducible_iff_isClosed_union_isClosed] at h ⊢
    intro z1 z2 h1 h2 hsub
    have himg : toProj '' Z ⊆ toProj '' z1 ∪ toProj '' z2 := by
      rintro x ⟨p, hp, rfl⟩
      rcases hsub hp with hp1 | hp2
      · exact Or.inl ⟨p, hp1, rfl⟩
      · exact Or.inr ⟨p, hp2, rfl⟩
    rcases h (toProj '' z1) (toProj '' z2) (isClosed_image_toProj h1)
      (isClosed_image_toProj h2) himg with h' | h'
    · refine Or.inl fun p hp => ?_
      obtain ⟨q, hq, hqp⟩ := h' ⟨p, hp, rfl⟩
      exact projEquiv.injective hqp ▸ hq
    · refine Or.inr fun p hp => ?_
      obtain ⟨q, hq, hqp⟩ := h' ⟨p, hp, rfl⟩
      exact projEquiv.injective hqp ▸ hq
  · intro h
    rw [isPreirreducible_iff_isClosed_union_isClosed] at h ⊢
    intro v1 v2 hv1 hv2 hsub
    have hpre : Z ⊆ toProj ⁻¹' v1 ∪ toProj ⁻¹' v2 := by
      intro p hp
      rcases hsub ⟨p, hp, rfl⟩ with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    rcases h _ _ (isClosed_preimage_toProj hv1) (isClosed_preimage_toProj hv2) hpre with h' | h'
    · refine Or.inl ?_
      rintro x ⟨p, hp, rfl⟩
      exact h' hp
    · refine Or.inr ?_
      rintro x ⟨p, hp, rfl⟩
      exact h' hp

/-- **Irreducibility transfers across the identification.** -/
theorem isIrreducible_image_toProj_iff (Z : Set (P k n)) :
    IsIrreducible (toProj '' Z) ↔ IsIrreducible Z := by
  have hne : (toProj '' Z).Nonempty ↔ Z.Nonempty := by
    constructor
    · rintro ⟨x, p, hp, rfl⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨toProj p, p, hp, rfl⟩
  constructor
  · intro h
    exact ⟨hne.1 h.1, (isPreirreducible_image_toProj_iff Z).1 h.2⟩
  · intro h
    exact ⟨hne.2 h.1, (isPreirreducible_image_toProj_iff Z).2 h.2⟩

end Bridge

/-! ## Chain transfer (in `P³`, where the chain dimension of this file lives) -/

section Chain
variable {k : Type*} [Field k]

/-- A chain in `S` gives a chain of the same length in the image of `S`, hence bounds `m` by the
chain dimension of the image. -/
theorem hasChainIn_le_irrChainDim {S : Set (P k 3)} {m : ℕ} (h : HasChainIn S m) :
    (m : ℕ∞) ≤ Copy8.irrChainDim (toProj '' S) := by
  obtain ⟨Z, hZ, hmono⟩ := h
  have hstep : ∀ i : Fin m, toProj '' Z i.castSucc ⊂ toProj '' Z i.succ := by
    intro i
    have hlt : Z i.castSucc < Z i.succ := hmono (by simp)
    refine ⟨Set.image_mono hlt.1, ?_⟩
    intro heq
    refine hlt.2 fun p hp => ?_
    obtain ⟨q, hq, hqp⟩ := heq ⟨p, hp, rfl⟩
    exact projEquiv.injective hqp ▸ hq
  let l : LTSeries {W : Set (Copy8.Proj k 3) // W ⊆ toProj '' S ∧ IsIrreducible W ∧ IsClosed W} :=
    RelSeries.mk m (fun i => ⟨toProj '' Z i,
      Set.image_mono (hZ i).1,
      (isIrreducible_image_toProj_iff (Z i)).2 (hZ i).2.2.2,
      isClosed_image_toProj (hZ i).2.2.1⟩) (fun i => hstep i)
  have hle := le_iSup (fun l : LTSeries {W : Set (Copy8.Proj k 3) //
      W ⊆ toProj '' S ∧ IsIrreducible W ∧ IsClosed W} => (l.length : ℕ∞)) l
  simpa [Copy8.irrChainDim] using hle


end Chain

end P
end Hartshorne77.Ex_I_2_15


/-! ## The two missing geometric clauses: `IsIrreducible quadric` and `DimEq quadric 2` -/

namespace Hartshorne77.Ex_I_2_15
namespace P

section Main
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The point `(1:0:0:0)` lies on the quadric. -/
theorem zeroSet_quadForm_nonempty :
    (Copy8.Proj.zeroSet (quadForm (k := k))).Nonempty := by
  refine ⟨Copy8.Proj.mk (![1, 0, 0, 0] : Vec k 3)
    (vec4_ne_zero_left (a := (1 : k)) (b := (0 : k)) (c := (0 : k)) (d := (0 : k))
      one_ne_zero), ?_⟩
  refine Copy8.Proj.mem_zeroSet.2 ?_
  rw [Copy8.Proj.isZeroAt_mk_iff (quadForm_isHomogeneous (k := k))]
  simp [quadForm]

/-- The image of the quadric in the accepted model is the zero set of the quadric equation. -/
theorem image_quadric :
    toProj '' quadric (k := k) = Copy8.Proj.zeroSet (quadForm (k := k)) := by
  rw [quadric, image_zeroLocus _ (by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨2, hf ▸ quadForm_isHomogeneous (k := k)⟩)]
  ext x
  constructor
  · intro hx
    exact hx ⟨quadForm (k := k), ⟨2, quadForm_isHomogeneous (k := k)⟩⟩ rfl
  · intro hx g hg
    rw [show (g : MvPolynomial (Fin 4) k) = quadForm (k := k) from hg]
    exact hx

/-- **The quadric is irreducible.**  Via the accepted I.2.8 model: the affine cone over the
quadric is the zero locus of the prime ideal `(X₀X₃ - X₁X₂)`. -/
theorem isIrreducible_quadric : IsIrreducible (quadric (k := k)) := by
  have hcl : IsClosed (Copy8.Proj.zeroSet (quadForm (k := k))) :=
    Copy8.Proj.isClosed_zeroSet (quadForm_isHomogeneous (k := k))
  have hcone : IsIrreducible (Copy8.Proj.cone (Copy8.Proj.zeroSet (quadForm (k := k)))) := by
    rw [Copy8.Proj.cone_zeroSet (by norm_num : 0 < 2) (quadForm_isHomogeneous (k := k))]
    exact Copy8.zeroLocus_irreducible k 4 isPrime_span_quadForm
  have hz : IsIrreducible (Copy8.Proj.zeroSet (quadForm (k := k))) :=
    (Copy8.Proj.isIrreducible_cone_iff hcl zeroSet_quadForm_nonempty).1 hcone
  have hz' : IsIrreducible (toProj '' quadric (k := k)) := by
    rwa [image_quadric]
  exact (isIrreducible_image_toProj_iff (quadric (k := k))).1 hz'

/-- The conic is not the whole quadric (it lies in the hyperplane `x₁ = x₂`). -/
theorem conic_ne_quadric : conic (k := k) ≠ quadric (k := k) := by
  intro h
  have hmem : mk (vec4_ne_zero_left (a := (1 : k)) (b := (0 : k)) (c := (1 : k)) (d := (0 : k))
      one_ne_zero) ∈ quadric (k := k) := by
    rw [mem_quadric_iff, eval_quadForm]
    simp
  have hnotconic : mk (vec4_ne_zero_left (a := (1 : k)) (b := (0 : k)) (c := (1 : k))
      (d := (0 : k)) one_ne_zero) ∉ conic (k := k) := by
    intro hc
    have hh := conic_subset_hyperplane hc
    rw [hyperplane] at hh
    rw [mem_zeroLocus_iff isHomogeneous_hyperplane_mem] at hh
    have h0 := hh (MvPolynomial.X (1 : Fin 4) - MvPolynomial.X 2) rfl
    simp at h0
  exact hnotconic (h ▸ hmem)

/-- The conic sits strictly inside the quadric. -/
theorem conic_ssubset_quadric : conic (k := k) ⊂ quadric (k := k) :=
  ⟨conic_subset_quadric, fun h => conic_ne_quadric (Set.Subset.antisymm conic_subset_quadric h)⟩

/-- A chain of length two inside the quadric: a point, the conic, the quadric. -/
theorem hasChainIn_quadric_two : HasChainIn (quadric (k := k)) 2 := by
  obtain ⟨Z, hZ, hmono⟩ := (dim_conic (k := k)).1
  have hZi : ∀ i : Fin 2, Z i ⊂ quadric (k := k) := by
    intro i
    refine ⟨Set.Subset.trans (hZ i).1 conic_subset_quadric, ?_⟩
    intro hsub
    exact conic_ne_quadric (Set.Subset.antisymm conic_subset_quadric
      (Set.Subset.trans hsub (hZ i).1))
  refine ⟨fun i : Fin 3 => if (i : ℕ) = 0 then Z 0 else if (i : ℕ) = 1 then Z 1
    else quadric (k := k), ?_, ?_⟩
  · intro i
    by_cases h0 : (i : ℕ) = 0
    · simp only [if_pos h0]
      exact ⟨(hZi 0).1, (hZ 0).2.1, (hZ 0).2.2.1, (hZ 0).2.2.2⟩
    · by_cases h1 : (i : ℕ) = 1
      · simp only [if_neg h0, if_pos h1]
        exact ⟨(hZi 1).1, (hZ 1).2.1, (hZ 1).2.2.1, (hZ 1).2.2.2⟩
      · simp only [if_neg h0, if_neg h1]
        exact ⟨Set.Subset.refl _, ⟨chartPt 0, conic_subset_quadric (chartPt_mem_conic 0)⟩,
          isClosed_quadric, isIrreducible_quadric⟩
  · intro i j hij
    have hi : (i : ℕ) < 3 := i.isLt
    have hj : (j : ℕ) < 3 := j.isLt
    have hlt : (i : ℕ) < (j : ℕ) := hij
    obtain ⟨hi0, hj1⟩ | ⟨hi0, hj2⟩ | ⟨hi1, hj2⟩ : ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨
        ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 2) := by omega
    · simp only [if_pos hi0, if_neg (by omega : ¬ (j : ℕ) = 0), if_pos hj1]
      exact hmono (by simp)
    · simp only [if_pos hi0, if_neg (by omega : ¬ (j : ℕ) = 0), if_neg (by omega : ¬ (j : ℕ) = 1)]
      exact hZi 0
    · simp only [if_neg (by omega : ¬ (i : ℕ) = 0), if_pos hi1,
        if_neg (by omega : ¬ (j : ℕ) = 0), if_neg (by omega : ¬ (j : ℕ) = 1)]
      exact hZi 1

/-- From `x + 1 = 3` in `ℕ∞` conclude `x ≤ 2`. -/
lemma enat_le_two_of_add_one_eq_three {x : ℕ∞} (h : x + 1 = 3) : x ≤ 2 := by
  have hx : x ≠ ⊤ := by
    intro hx
    rw [hx] at h
    simp at h
  have h1 : x.toNat + 1 = 3 := by
    have h' := congrArg ENat.toNat h
    rw [ENat.toNat_add hx (by simp : (1 : ℕ∞) ≠ ⊤)] at h'
    simpa using h'
  have h2 : x.toNat ≤ 2 := by omega
  calc x = ((x.toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hx).symm
    _ ≤ ((2 : ℕ) : ℕ∞) := by exact_mod_cast h2

/-- **The quadric has dimension two** (Hartshorne's chain dimension), transferred from the
accepted I.2.8 hypersurface theorem through the homeomorphism of models. -/
theorem dimEq_quadric : DimEq (quadric (k := k)) 2 := by
  refine ⟨hasChainIn_quadric_two, ?_⟩
  intro m hm
  have h1 : (m : ℕ∞) ≤ Copy8.irrChainDim (toProj '' quadric (k := k)) :=
    hasChainIn_le_irrChainDim hm
  have h3 : Copy8.irrChainDim (toProj '' quadric (k := k)) ≤ 2 := by
    rw [image_quadric]
    have hpd := Copy8.Proj.projDim_zeroSet (by norm_num : 0 < 2)
      (quadForm_isHomogeneous (k := k)) irreducible_quadForm zeroSet_quadForm_nonempty
    exact enat_le_two_of_add_one_eq_three (by simpa [Copy8.projDim] using hpd)
  have := le_trans h1 h3
  exact_mod_cast this

end Main

end P
end Hartshorne77.Ex_I_2_15


/-! ## The complete statement of Exercise I.2.15, with the dimension and irreducibility clauses -/

namespace Hartshorne77.Ex_I_2_15
namespace P

section Complete
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The quadric is a projective variety: closed, irreducible, of dimension two. -/
theorem quadric_isVarietyOfDimTwo :
    IsClosed (quadric (k := k)) ∧ IsIrreducible (quadric (k := k)) ∧
      DimEq (quadric (k := k)) 2 :=
  ⟨isClosed_quadric, isIrreducible_quadric, dimEq_quadric⟩

/-- **Hartshorne, Algebraic Geometry (1977), Exercise I.2.15, complete.**

(a) `Q : x₀x₃ - x₁x₂ = 0` is the image of the Segre embedding `ψ : P¹ × P¹ → P³`, and in the
book's own coordinates `xy - zw = 0`.
(b) The two rulings `L_t`, `M_t`, each a linear variety of dimension one, distinct members of a
family disjoint, `L_t ∩ M_u` a single point.
(c) The conic `ψ(Δ)` is a curve on `Q` different from every line, and the Zariski topology on `Q`
is not the product topology under `ψ`.
(d) The parenthetical definition of *surface*: `Q` is a closed irreducible subset of `P³` of
chain dimension two. -/
theorem hartshorne_I_2_15_complete (k : Type*) [Field k] [IsAlgClosed k] :
    (Set.range (fun p : P k 1 × P k 1 => segre p.1 p.2) = quadric (k := k)) ∧
    (∀ t : P k 1, L t ⊆ quadric (k := k) ∧ IsProjectiveLine (L t)) ∧
    (∀ t : P k 1, M t ⊆ quadric (k := k) ∧ IsProjectiveLine (M t)) ∧
    (∀ t s : P k 1, L t = L s ↔ t = s) ∧
    (∀ t s : P k 1, M t = M s ↔ t = s) ∧
    (∀ t s : P k 1, t ≠ s → Disjoint (L t) (L s)) ∧
    (∀ t s : P k 1, t ≠ s → Disjoint (M t) (M s)) ∧
    (∀ t u : P k 1, L t ∩ M u = {segre u t}) ∧
    (IsClosed (conic (k := k)) ∧ IsIrreducible (conic (k := k)) ∧ DimEq (conic (k := k)) 1) ∧
    (∀ t : P k 1, conic (k := k) ≠ L t ∧ conic (k := k) ≠ M t) ∧
    (¬ IsClosed (diag (k := k))) ∧
    (¬ ∀ S : Set (P k 1 × P k 1), IsClosed S ↔ IsClosed (segrePair (k := k) '' S)) ∧
    (IsClosed (quadric (k := k)) ∧ IsIrreducible (quadric (k := k)) ∧
      DimEq (quadric (k := k)) 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hartshorne_I_2_15 (k := k)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, quadric_isVarietyOfDimTwo⟩

end Complete

end P
end Hartshorne77.Ex_I_2_15

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_2_15.P.hartshorne_I_2_15_complete
#print axioms Hartshorne77.Ex_I_2_15.P.hartshorne_I_2_15
#print axioms Hartshorne77.Ex_I_2_15.P.quadric_isVarietyOfDimTwo
#print axioms Hartshorne77.Ex_I_2_15.P.isIrreducible_quadric
#print axioms Hartshorne77.Ex_I_2_15.P.dimEq_quadric
#print axioms Hartshorne77.Ex_I_2_15.P.hasChainIn_quadric_two
#print axioms Hartshorne77.Ex_I_2_15.P.conic_ne_quadric
#print axioms Hartshorne77.Ex_I_2_15.P.image_quadric
#print axioms Hartshorne77.Ex_I_2_15.P.isPrime_span_quadForm
#print axioms Hartshorne77.Ex_I_2_15.P.prime_quadForm
#print axioms Hartshorne77.Ex_I_2_15.P.irreducible_quadForm
#print axioms Hartshorne77.Ex_I_2_15.P.isClosed_image_toProj_iff
#print axioms Hartshorne77.Ex_I_2_15.P.isIrreducible_image_toProj_iff
#print axioms Hartshorne77.Ex_I_2_15.P.hasChainIn_le_irrChainDim
#print axioms Hartshorne77.Ex_I_2_15.P.range_segre
#print axioms Hartshorne77.Ex_I_2_15.P.dim_conic
#print axioms Hartshorne77.Ex_I_2_15.P.not_homeomorph_product
