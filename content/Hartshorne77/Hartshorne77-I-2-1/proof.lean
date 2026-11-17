import Mathlib

/-!
Hartshorne, *Algebraic Geometry* (1977), Chapter I, §2, Exercise 2.1.

## The statement in the source

The exercise asks to prove the **homogeneous Nullstellensatz**:

> if `𝔞 ⊆ S = k[x₀,…,xₙ]` is a homogeneous ideal, and if `f ∈ S` is a homogeneous
> polynomial with `deg f > 0`, such that `f(P) = 0` for all `P ∈ Z(𝔞)` in `Pⁿ`, then
> `f^q ∈ 𝔞` for some `q > 0`.

over an algebraically closed field `k`, where `Pⁿ` is projective `n`-space (nonzero
`(n+1)`-tuples modulo nonzero scalars) and `Z(𝔞)` is the projective zero locus of `𝔞`,
i.e. the book's `Z(𝔞) = Z(T)` for `T` the set of *homogeneous* elements of `𝔞` (we
denote that set by `V 𝔞`).  The book's hint is to interpret the problem in the affine
`(n+1)`-space with affine coordinate ring `S` and to use the usual Nullstellensatz
(1.3A); that is how the proof below proceeds.

Formalisation used here:

* `Pⁿ` is Mathlib's `Projectivization k (Fin (n+1) → k)`, which is literally
  `(k^{n+1} \ {0}) / k^×` (Mathlib's `projectivizationSetoid` is the orbit relation of
  `kˣ` on nonzero vectors, restricted along `Subtype.val`).  This is a faithful
  point-set model of classical projective space; `Proj` is used, not `ProjSpec`/`Proj`.
* `VanishesAt f d hf P` is the statement `f(P) = 0` for a homogeneous `f` of degree `d`.
  Its well-definedness is *proved* (`eval_smul_of_isHomogeneous`), not assumed.
* `V 𝔞` is the source's zero locus: all points at which every homogeneous element of
  `𝔞` vanishes.  For a homogeneous ideal `𝔞` this is the same as the set of projective
  points at which *every* element of `𝔞` vanishes, see `mem_V_iff_forall_eval_rep`.

Contents:
1. point-set projective space;
2. `f(c • a) = c^d f(a)` for homogeneous `f` of degree `d`;
3. `f(P) = 0` for a projective point `P` (well defined) and `V(𝔞)`;
4. `V(𝔞)` is the cone over the affine zero locus `Z(𝔞) ⊆ A^{n+1}` minus its vertex;
5. the closed-set axioms, giving the Zariski topology on `Pⁿ` whose closed sets are the
   `V(𝔞)` (`zariskiTopology`, `isClosed_V`): `V(𝔞 + 𝔟) = V(𝔞) ∩ V(𝔟)` and
   `V(𝔞𝔟) = V(𝔞) ∪ V(𝔟)`;
6. the homogeneous Nullstellensatz (`homogeneous_nullstellensatz`), proved by reducing
   to Hilbert's Nullstellensatz for the affine cone;
7. sanity checks (the definitions compute, the theorem has non-vacuous instances) and
   the sharpness of the hypothesis `deg f > 0`.

Source of the statement: Hartshorne, *Algebraic Geometry* (1977), Chapter I, §2,
Exercise 2.1; wording checked against
https://hartshorne-ag-solutions.wikidot.com/chapter-1-section-2 (the local OCR
`.scratch/reference/hartshorne-1977.txt` omits exercises I.2.1-I.2.11).
-/

noncomputable section

open MvPolynomial

open scoped Topology

-- The standard grading of the polynomial ring by total degree, as a local instance.
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Hartshorne77.Ex_I_2_1

variable {k : Type*} [Field k]

/-! ## 1. Point-set projective space -/

/-- Projective `n`-space over `k`: nonzero `(n+1)`-tuples modulo multiplication by a
nonzero scalar, `Pⁿ = (A^{n+1} \ {0}) / k^×` (Hartshorne, Chapter I §2).  This is
Mathlib's `Projectivization k (Fin (n+1) → k)`, whose defining setoid is precisely the
orbit relation of `k^×` on nonzero vectors. -/
abbrev Proj (k : Type*) [Field k] (n : ℕ) : Type _ := Projectivization k (Fin (n + 1) → k)

/-! ## 2. Homogeneous polynomials are homogeneous functions -/

section HomogeneousEval

variable {σ : Type*}

theorem sum_support_eq_degree (m : σ →₀ ℕ) : ∑ i ∈ m.support, m i = m.degree := by
  rw [Finsupp.degree_eq_weight_one]
  simp [Finsupp.weight_apply, Finsupp.sum]

/-- A homogeneous polynomial of degree `d` scales by `c^d`: this is exactly the fact
that makes the vanishing of `f` at a projective point well defined. -/
theorem eval_smul_of_isHomogeneous {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : k) (a : σ → k) : eval (c • a) f = c ^ d * eval a f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmdeg : m.degree = d := by
    by_contra h
    exact Finsupp.mem_support_iff.1 hm (hf.coeff_eq_zero h)
  rw [eval_monomial, eval_monomial]
  have hkey : m.prod (fun i e => (c • a) i ^ e) = c ^ d * m.prod (fun i e => a i ^ e) := by
    rw [Finsupp.prod, Finsupp.prod]
    have h1 : ∀ i ∈ m.support, (c • a) i ^ m i = c ^ m i * a i ^ m i := by
      intro i _
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      sum_support_eq_degree, hmdeg]
  rw [hkey]
  ring

/-- A homogeneous polynomial of positive degree vanishes at the origin of the affine
cone (this is the only place where the hypothesis `deg f > 0` enters). -/
theorem eval_zero_of_isHomogeneous {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d) : eval (0 : σ → k) f = 0 := by
  have h := eval_smul_of_isHomogeneous (k := k) hf (0 : k) (0 : σ → k)
  rw [zero_smul, zero_pow hd.ne'] at h
  simpa using h

end HomogeneousEval

/-! ## 3. Vanishing of a homogeneous polynomial at a projective point -/

/-- `f` vanishes at the projective point `P`, for `f` homogeneous of degree `d`.
Well defined because `f(c • a) = c^d f(a)` for `c ≠ 0` (`eval_smul_of_isHomogeneous`). -/
def VanishesAt (k : Type*) [Field k] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ)
    (hf : f.IsHomogeneous d) (P : Proj k n) : Prop :=
  Projectivization.lift (K := k) (V := Fin (n + 1) → k)
    (fun v : {v : Fin (n + 1) → k // v ≠ 0} => eval (v : Fin (n + 1) → k) f = 0) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      have ht : t ≠ 0 := by
        rintro rfl
        exact ha (by simpa using hab)
      apply propext
      rw [hab, eval_smul_of_isHomogeneous hf t b]
      exact ⟨fun h => (mul_eq_zero.mp h).resolve_left (pow_ne_zero d ht), fun h => by
        rw [h, mul_zero]⟩) P

@[simp]
theorem vanishesAt_mk {n : ℕ} {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    VanishesAt k n f d hf (Projectivization.mk k v hv) ↔ eval v f = 0 := by
  simp [VanishesAt, Projectivization.lift_mk]

/-- `f` vanishes at `P` iff it vanishes at the chosen representative `P.rep`. -/
theorem vanishesAt_rep {n : ℕ} {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (P : Proj k n) :
    VanishesAt k n f d hf P ↔ eval P.rep f = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep P]
  rw [vanishesAt_mk]

/-- The product of two homogeneous polynomials vanishes where a factor vanishes. -/
theorem VanishesAt.mul {n : ℕ} {f g : MvPolynomial (Fin (n + 1)) k} {d e : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) {P : Proj k n}
    (hfm : VanishesAt k n f d hf P) (hgm : VanishesAt k n g e hg P) :
    VanishesAt k n (f * g) (d + e) (hf.mul hg) P := by
  induction P using Projectivization.ind with
  | h v hv =>
    rw [vanishesAt_mk] at hfm hgm ⊢
    rw [map_mul, hfm, hgm, mul_zero]

/-! ## 4. The projective zero locus of a homogeneous ideal -/

/-- `V(𝔞)` (written `Z(𝔞)` in the exercise): the projective zero locus of an ideal
`𝔞 ⊆ k[x₀,…,xₙ]`, namely the set of projective points at which every *homogeneous*
element of `𝔞` vanishes -- this is Hartshorne's `Z(𝔞) = Z(T)`, `T` the set of homogeneous
elements of `𝔞`.  For a homogeneous ideal this is also `{P ∈ Pⁿ | f(P) = 0 for all
f ∈ 𝔞}`, see `mem_V_iff_forall_eval_rep`. -/
def V (k : Type*) [Field k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    Set (Proj k n) :=
  {P | ∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d),
    f ∈ 𝔞 → VanishesAt k n f d hf P}

theorem mem_V {n : ℕ} {𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)} {P : Proj k n} :
    P ∈ V k n 𝔞 ↔
      ∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d),
        f ∈ 𝔞 → VanishesAt k n f d hf P :=
  Iff.rfl

theorem V_anti_mono {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)} (h : 𝔞 ≤ 𝔟) :
    V k n 𝔟 ⊆ V k n 𝔞 :=
  fun _ hP f d hf hf𝔞 => hP f d hf (h hf𝔞)

@[simp]
theorem V_bot (n : ℕ) : V k n (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) = Set.univ := by
  refine Set.eq_univ_of_forall fun P => ?_
  intro f d hf hf𝔞
  rw [Ideal.mem_bot] at hf𝔞
  subst hf𝔞
  rw [← Projectivization.mk_rep P]
  exact (vanishesAt_mk (isHomogeneous_zero (σ := Fin (n + 1)) (R := k) d) P.rep
    P.rep_nonzero).2 (map_zero (eval P.rep))

@[simp]
theorem V_top (n : ℕ) : V k n (⊤ : Ideal (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun P hP => ?_
  have h1 : VanishesAt k n (1 : MvPolynomial (Fin (n + 1)) k) 0
      (isHomogeneous_one (σ := Fin (n + 1)) (R := k)) P :=
    hP 1 0 _ Submodule.mem_top
  rw [vanishesAt_rep, map_one] at h1
  exact one_ne_zero h1

/-! ## 5. Projective zero loci are the cones over affine zero loci -/

section Cone

/-- For a homogeneous ideal, membership in `V(𝔞)` may be tested on *all* elements of `𝔞`,
not only the homogeneous ones: this is Hartshorne's literal definition of `V(𝔞)`. -/
theorem mem_V_iff_forall_eval_rep {n : ℕ} {𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (P : Proj k n) : P ∈ V k n 𝔞 ↔ ∀ f ∈ 𝔞, eval P.rep f = 0 := by
  constructor
  · intro hP f hf
    rw [← MvPolynomial.sum_homogeneousComponent (φ := f), map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hmem : homogeneousComponent i f ∈ 𝔞 :=
      MvPolynomial.homogeneousComponent_mem_of_mem h𝔞 hf i
    have hv := hP (homogeneousComponent i f) i (homogeneousComponent_isHomogeneous i f) hmem
    rwa [vanishesAt_rep] at hv
  · intro hP f d hf hf𝔞
    rw [vanishesAt_rep]
    exact hP f hf𝔞

/-- A homogeneous ideal in the sense of the source -- an ideal generated by homogeneous
elements -- is the same thing as an ideal closed under taking homogeneous components
(Mathlib's `Ideal.IsHomogeneous`). -/
theorem isHomogeneous_iff_exists_generators {n : ℕ}
    (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ↔
      ∃ S : Set (SetLike.homogeneousSubmonoid (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)),
        𝔞 = Ideal.span (Subtype.val '' S) :=
  Ideal.IsHomogeneous.iff_exists (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) 𝔞

/-- The projective zero locus of a homogeneous ideal is exactly the set of projective
points whose affine representative lies in the affine zero locus: `V(𝔞) ⊆ Pⁿ` is the
image of the cone `Z(𝔞) ⊆ A^{n+1}` minus its vertex. -/
theorem mem_V_iff_exists_cone {n : ℕ} {𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (P : Proj k n) :
    P ∈ V k n 𝔞 ↔
      ∃ (v : Fin (n + 1) → k) (hv : v ≠ 0),
        v ∈ MvPolynomial.zeroLocus k 𝔞 ∧ P = Projectivization.mk k v hv := by
  constructor
  · intro hP
    refine ⟨P.rep, P.rep_nonzero, ?_, (Projectivization.mk_rep P).symm⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    simpa [MvPolynomial.aeval_eq_eval] using (mem_V_iff_forall_eval_rep h𝔞 P).1 hP p hp
  · rintro ⟨v, hv, hz, rfl⟩ f d hf hf𝔞
    rw [vanishesAt_mk]
    have h := hz f hf𝔞
    simpa [MvPolynomial.aeval_eq_eval] using h

end Cone

/-! ## 6. The kernel form, and the closed-set axioms for the projective Zariski topology -/

section KernelForm

/-- `𝔞` vanishes at `P` if every element of `𝔞` (homogeneous or not) vanishes at the
representative `P.rep`.  For a homogeneous ideal this is Hartshorne's condition
`f(P) = 0` for all `f ∈ 𝔞` (`mem_V_iff_idealVanishes`). -/
def IdealVanishes (k : Type*) [Field k] (n : ℕ)
    (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)) (P : Proj k n) : Prop :=
  ∀ f ∈ 𝔞, eval P.rep f = 0

theorem mem_V_iff_idealVanishes {n : ℕ} {𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (P : Proj k n) : P ∈ V k n 𝔞 ↔ IdealVanishes k n 𝔞 P :=
  mem_V_iff_forall_eval_rep h𝔞 P

theorem idealVanishes_iff_le_ker {n : ℕ} {𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    {P : Proj k n} : IdealVanishes k n 𝔞 P ↔ 𝔞 ≤ RingHom.ker (eval P.rep) := by
  simp [IdealVanishes, SetLike.le_def, RingHom.mem_ker]

theorem idealVanishes_sup {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    {P : Proj k n} :
    IdealVanishes k n (𝔞 ⊔ 𝔟) P ↔ IdealVanishes k n 𝔞 P ∧ IdealVanishes k n 𝔟 P := by
  rw [idealVanishes_iff_le_ker, sup_le_iff, ← idealVanishes_iff_le_ker,
    ← idealVanishes_iff_le_ker]

theorem idealVanishes_iSup {n : ℕ} {ι : Sort*} (F : ι → Ideal (MvPolynomial (Fin (n + 1)) k))
    {P : Proj k n} :
    IdealVanishes k n (⨆ i, F i) P ↔ ∀ i, IdealVanishes k n (F i) P := by
  rw [idealVanishes_iff_le_ker, iSup_le_iff]
  exact forall_congr' fun i => (idealVanishes_iff_le_ker).symm

theorem idealVanishes_mul {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    {P : Proj k n} :
    IdealVanishes k n (𝔞 * 𝔟) P ↔ IdealVanishes k n 𝔞 P ∨ IdealVanishes k n 𝔟 P := by
  constructor
  · intro h
    by_cases h𝔞 : IdealVanishes k n 𝔞 P
    · exact Or.inl h𝔞
    · refine Or.inr fun f hf => ?_
      by_contra hfne
      have ha : ∃ a ∈ 𝔞, eval P.rep a ≠ 0 := by
        by_contra h'
        exact h𝔞 fun g hg => by
          by_contra hg'
          exact h' ⟨g, hg, hg'⟩
      obtain ⟨a, ha, hane⟩ := ha
      have hmem : a * f ∈ 𝔞 * 𝔟 := Ideal.mul_mem_mul ha hf
      have h0 : eval P.rep (a * f) = 0 := h _ hmem
      rw [map_mul] at h0
      exact mul_ne_zero hane hfne h0
  · rintro (h | h) f hf
    · exact h f (Ideal.mul_le_left hf)
    · exact h f (Ideal.mul_le_right hf)

/-- A product of homogeneous ideals is homogeneous. -/
theorem isHomogeneous_mul {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (h𝔟 : 𝔟.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    (𝔞 * 𝔟).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := by
  obtain ⟨S, rfl⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) _).1 h𝔞
  obtain ⟨T, rfl⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) _).1 h𝔟
  rw [Ideal.span_mul_span]
  refine Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) _
    fun x hx => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := hx
  obtain ⟨s', -, rfl⟩ := hs
  obtain ⟨t', -, rfl⟩ := ht
  exact SetLike.IsHomogeneousElem.mul s'.2 t'.2

/-- `V` turns sums of homogeneous ideals into intersections. -/
theorem V_sup {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (h𝔟 : 𝔟.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    V k n (𝔞 ⊔ 𝔟) = V k n 𝔞 ∩ V k n 𝔟 := by
  ext P
  rw [Set.mem_inter_iff, mem_V_iff_idealVanishes (h𝔞.sup h𝔟), mem_V_iff_idealVanishes h𝔞,
    mem_V_iff_idealVanishes h𝔟, idealVanishes_sup]

/-- `V` turns products of homogeneous ideals into unions (the projective analogue of
`V(𝔞𝔟) = V(𝔞) ∪ V(𝔟)`). -/
theorem V_mul {n : ℕ} {𝔞 𝔟 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (h𝔟 : 𝔟.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    V k n (𝔞 * 𝔟) = V k n 𝔞 ∪ V k n 𝔟 := by
  ext P
  rw [Set.mem_union, mem_V_iff_idealVanishes (isHomogeneous_mul h𝔞 h𝔟),
    mem_V_iff_idealVanishes h𝔞, mem_V_iff_idealVanishes h𝔟, idealVanishes_mul]

theorem V_iSup {n : ℕ} {ι : Sort*} (F : ι → Ideal (MvPolynomial (Fin (n + 1)) k))
    (hF : ∀ i, (F i).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    V k n (⨆ i, F i) = ⋂ i, V k n (F i) := by
  ext P
  rw [Set.mem_iInter, mem_V_iff_idealVanishes (Ideal.IsHomogeneous.iSup hF), idealVanishes_iSup]
  exact forall_congr' fun i => (mem_V_iff_idealVanishes (hF i) P).symm

/-- The closed sets of the Zariski topology on `Pⁿ`: the projective zero loci of
homogeneous ideals of `k[x₀,…,xₙ]` (Hartshorne, Chapter I §2). -/
def closedSets (k : Type*) [Field k] (n : ℕ) : Set (Set (Proj k n)) :=
  {S | ∃ (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k))
    (_ : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)), S = V k n 𝔞}

theorem empty_mem_closedSets (n : ℕ) : ∅ ∈ closedSets k n :=
  ⟨⊤, Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k),
    (V_top n).symm⟩

theorem univ_mem_closedSets (n : ℕ) : Set.univ ∈ closedSets k n :=
  ⟨⊥, Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k),
    (V_bot n).symm⟩

theorem sInter_mem_closedSets (n : ℕ) {A : Set (Set (Proj k n))} (hA : A ⊆ closedSets k n) :
    ⋂₀ A ∈ closedSets k n := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sInter_empty]
    exact univ_mem_closedSets n
  · have hA' : ∀ a : A, ∃ (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k))
        (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)),
        (a : Set (Proj k n)) = V k n 𝔞 := fun a => hA a.2
    choose f hf hfeq using hA'
    refine ⟨⨆ a : A, f a, Ideal.IsHomogeneous.iSup hf, ?_⟩
    ext P
    rw [Set.mem_sInter, mem_V_iff_idealVanishes (Ideal.IsHomogeneous.iSup hf), idealVanishes_iSup]
    constructor
    · intro h a
      rw [← mem_V_iff_idealVanishes (hf a) P, ← hfeq a]
      exact h a a.2
    · intro h t ht
      have h' : P ∈ V k n (f ⟨t, ht⟩) := by
        rw [mem_V_iff_idealVanishes (hf ⟨t, ht⟩) P]
        exact h ⟨t, ht⟩
      rwa [← hfeq ⟨t, ht⟩] at h'

theorem union_mem_closedSets (n : ℕ) {A B : Set (Proj k n)}
    (hA : A ∈ closedSets k n) (hB : B ∈ closedSets k n) : A ∪ B ∈ closedSets k n := by
  obtain ⟨𝔞, h𝔞, rfl⟩ := hA
  obtain ⟨𝔟, h𝔟, rfl⟩ := hB
  exact ⟨𝔞 * 𝔟, isHomogeneous_mul h𝔞 h𝔟, (V_mul h𝔞 h𝔟).symm⟩

/-- **The Zariski topology on projective space `Pⁿ`**, whose closed sets are exactly the
projective zero loci `V(𝔞)` of homogeneous ideals (Hartshorne, Chapter I §2). -/
@[instance_reducible]
def zariskiTopology (k : Type*) [Field k] (n : ℕ) : TopologicalSpace (Proj k n) :=
  TopologicalSpace.ofClosed (closedSets k n) (empty_mem_closedSets n)
    (fun _ hA => sInter_mem_closedSets n hA) (fun _ hA _ hB => union_mem_closedSets n hA hB)

/-- Each projective zero locus is closed in the Zariski topology. -/
theorem isClosed_V {n : ℕ} (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k))
    (h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    IsClosed[zariskiTopology k n] (V k n 𝔞) := by
  let t := zariskiTopology k n
  rw [← isOpen_compl_iff]
  show ((V k n 𝔞)ᶜ)ᶜ ∈ closedSets k n
  rw [compl_compl]
  exact ⟨𝔞, h𝔞, rfl⟩

end KernelForm

/-! ## 7. The homogeneous Nullstellensatz -/

section Nullstellensatz

variable [IsAlgClosed k]

/-- Auxiliary (slightly stronger) form of the homogeneous Nullstellensatz: the argument
does not need `𝔞` to be homogeneous, since `V` only tests homogeneous elements of `𝔞`.
Applied to a homogeneous ideal it gives Hartshorne I.2.1 verbatim below. -/
theorem homogeneous_nullstellensatz_aux (n : ℕ)
    (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k))
    (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hvan : ∀ P, P ∈ V k n 𝔞 → VanishesAt k n f d hf P) :
    ∃ q, 0 < q ∧ f ^ q ∈ 𝔞 := by
  -- `f` vanishes on the whole affine zero locus `Z(𝔞)` of `𝔞` in `A^{n+1}`.
  have hmem : f ∈ vanishingIdeal k (zeroLocus k 𝔞) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have hx' : ∀ p ∈ 𝔞, eval x p = 0 := by
      simpa [MvPolynomial.aeval_eq_eval] using hx
    have hfx : eval x f = 0 := by
      by_cases hx0 : x = 0
      · subst hx0
        exact eval_zero_of_isHomogeneous hf hd
      · have hP : Projectivization.mk k x hx0 ∈ V k n 𝔞 := by
          intro g e hg hg𝔞
          rw [vanishesAt_mk]
          exact hx' g hg𝔞
        exact (vanishesAt_mk hf x hx0).1 (hvan _ hP)
    simpa [MvPolynomial.aeval_eq_eval] using hfx
  -- Hilbert's Nullstellensatz in the affine cone.
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  rw [Ideal.mem_radical_iff] at hmem
  obtain ⟨q, hq⟩ := hmem
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    rw [pow_zero] at hq
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one, (Ideal.eq_top_iff_one 𝔞).mpr hq]
    exact Submodule.mem_top
  · exact ⟨q, hq0, hq⟩

/-- **Hartshorne I.2.1 (the homogeneous Nullstellensatz).**  Let `k` be an algebraically
closed field, let `𝔞 ⊆ k[x₀,…,xₙ]` be a homogeneous ideal, and let `f` be a homogeneous
polynomial of positive degree which vanishes at every point of `V(𝔞) ⊆ Pⁿ`.  Then
`f^q ∈ 𝔞` for some `q > 0`. -/
theorem homogeneous_nullstellensatz (n : ℕ)
    (𝔞 : Ideal (MvPolynomial (Fin (n + 1)) k))
    (_h𝔞 : 𝔞.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hvan : ∀ P, P ∈ V k n 𝔞 → VanishesAt k n f d hf P) :
    ∃ q, 0 < q ∧ f ^ q ∈ 𝔞 :=
  homogeneous_nullstellensatz_aux n 𝔞 f d hf hd hvan

end Nullstellensatz

/-! ## 8. Sanity checks: the definitions compute, and the theorem is not vacuous -/

section Examples

variable [IsAlgClosed k]

/-- On the projective line `P¹`, the linear form `x₀` vanishes at the point `(0 : 1)`. -/
example : VanishesAt k 1 (X 0) 1 (isHomogeneous_X (R := k) 0)
    (Projectivization.mk k ![0, 1] (by simp)) := by
  rw [vanishesAt_mk]
  simp

/-- The same linear form does not vanish at `(1 : 0)`. -/
example : ¬ VanishesAt k 1 (X 0) 1 (isHomogeneous_X (R := k) 0)
    (Projectivization.mk k ![1, 0] (by simp)) := by
  rw [vanishesAt_mk]
  simp

/-- A concrete instance of the homogeneous Nullstellensatz: in `k[x₀,x₁]`, the linear
form `x₀` vanishes on `V(x₀²) ⊆ P¹`, so some positive power of `x₀` lies in `(x₀²)`
(namely `x₀²` itself, so that `q = 2` is needed here). -/
example : ∃ q, 0 < q ∧ (X 0 : MvPolynomial (Fin 2) k) ^ q ∈ Ideal.span {(X 0) ^ 2} := by
  have hhom : (Ideal.span {(X 0 : MvPolynomial (Fin 2) k) ^ 2}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
    Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Fin 2) k) _
      fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨2, by simpa using (isHomogeneous_X (R := k) 0).pow 2⟩
  refine homogeneous_nullstellensatz 1 _ hhom (X 0) 1 (isHomogeneous_X (R := k) 0) one_pos ?_
  intro P hP
  have h2 : VanishesAt k 1 ((X 0 : MvPolynomial (Fin 2) k) ^ 2) (1 * 2)
      ((isHomogeneous_X (R := k) 0).pow 2) P :=
    hP _ _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [vanishesAt_rep] at h2 ⊢
  rw [map_pow] at h2
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 (by simpa using h2)

end Examples

/-! ## 9. The hypothesis `deg f > 0` is essential -/

section Sharpness

/-- The irrelevant ideal `S_+ = (x₀,…,xₙ)` has empty projective zero locus. -/
theorem V_span_X (n : ℕ) :
    V k n (Ideal.span (Set.range fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) k)))
      = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun P hP => ?_
  obtain ⟨i, hi⟩ : ∃ i, P.rep i ≠ 0 := Function.ne_iff.mp P.rep_nonzero
  have hmem : (X i : MvPolynomial (Fin (n + 1)) k)
      ∈ Ideal.span (Set.range fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) k)) :=
    Ideal.subset_span ⟨i, rfl⟩
  have hv : VanishesAt k n (X i) 1 (isHomogeneous_X (R := k) i) P := hP _ 1 _ hmem
  rw [vanishesAt_rep] at hv
  exact hi (by simpa using hv)

/-- The hypothesis `deg f > 0` in the homogeneous Nullstellensatz cannot be dropped:
`f = 1` is homogeneous of degree `0` and vanishes on `V(S_+) = ∅` vacuously, but no
positive power of `1` lies in `S_+`. -/
theorem deg_pos_needed (n : ℕ) :
    ¬ ∃ q, 0 < q ∧ (1 : MvPolynomial (Fin (n + 1)) k) ^ q
      ∈ Ideal.span (Set.range fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) k)) := by
  rintro ⟨q, -, hq⟩
  have hker : Ideal.span (Set.range fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) k))
      ≤ RingHom.ker (eval (0 : Fin (n + 1) → k)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  have h1 : (1 : k) = 0 := by
    have hmem : (1 : MvPolynomial (Fin (n + 1)) k)
        ∈ Ideal.span (Set.range fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) k)) := by
      simpa using hq
    simpa [RingHom.mem_ker] using hker hmem
  exact one_ne_zero h1

end Sharpness

end Hartshorne77.Ex_I_2_1

end

#print axioms Hartshorne77.Ex_I_2_1.homogeneous_nullstellensatz
#print axioms Hartshorne77.Ex_I_2_1.homogeneous_nullstellensatz_aux
#print axioms Hartshorne77.Ex_I_2_1.eval_smul_of_isHomogeneous
#print axioms Hartshorne77.Ex_I_2_1.mem_V_iff_exists_cone
#print axioms Hartshorne77.Ex_I_2_1.V_mul
#print axioms Hartshorne77.Ex_I_2_1.isClosed_V
#print axioms Hartshorne77.Ex_I_2_1.deg_pos_needed
