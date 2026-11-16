import Mathlib

set_option autoImplicit false

/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 1.28

*Regular maps versus coordinate-ring homomorphisms.*

The exercise (A&M, §1, p. 16–17) reads: let `k` be a field, `X ⊆ k^n` and `Y ⊆ k^m` affine
algebraic varieties; a mapping `φ : X → Y` is **regular** if it is the restriction to `X` of a
polynomial mapping `k^n → k^m`.  If `ψ` is a polynomial function on `Y` then `ψ ∘ φ` is a
polynomial function on `X`, so `φ` induces a `k`-algebra homomorphism
`P(Y) → P(X)`, `ψ ↦ ψ ∘ φ`.  Show that this gives a one-to-one correspondence between the
regular mappings `X → Y` and the `k`-algebra homomorphisms `P(Y) → P(X)`.

## Formalisation

* The ambient spaces are `Fin n → k` and `Fin m → k`.
* `I(X)` is A&M's ideal of polynomials vanishing on `X` (`vanishingIdeal`), and
  `coordRing X = k[t₁,…,tₙ]/I(X)` is A&M's `P(X)`, "the ring of polynomial functions on `X`".
  A&M's remark that `g` and `h` define the same polynomial function on `X` iff `g - h ∈ I(X)`
  is `mk_eq_mk_iff_aeval_eq`.
* `IsAffineAlgebraic X` says that `X` is the common zero set of a set of polynomial equations
  (A&M's definition, which does *not* require irreducibility).
* `RegMap X Y` is the type of regular maps `X → Y`: functions `X → Y` that coincide with the
  polynomial map given by some tuple `F : Fin m → k[t₁,…,tₙ]`.  Equality of regular maps is
  equality of the underlying functions, so the type does not remember the tuple.
* `RegMap.toAlgHom : RegMap X Y → (P(Y) →ₐ[k] P(X))` is `ψ ↦ ψ ∘ f`, built by
  `Ideal.Quotient.liftₐ`: the kernel condition is `aeval F q ∈ I(X)` for `q ∈ I(Y)`, which
  holds because `F` maps `X` into `Y`.
* `RegMap.ofAlgHom` is the source's converse construction
  `f(x) = (φ(t̄₁)(x), …, φ(t̄_m)(x))`: lift the images `φ(t̄ᵢ) ∈ P(X)` to polynomials
  `Gᵢ` (using surjectivity of `k[t] → P(X)`) and evaluate.  The reconstructed map lands in
  `Y` because, for `q ∈ I(Y)`, the class of `q(G)` is `φ(q(t̄)) = 0` in `P(X)`, so `q(G)`
  vanishes on `X`; this is the only place where algebraicity of `Y` is used.
* `regMapEquivAlgHom` is the resulting `Equiv`, `bijective_toAlgHom` the same statement as a
  bijection, and `RegMap.toAlgHom_id`, `RegMap.toAlgHom_comp` show the correspondence is
  compatible with identities and composition (contravariantly); `RegMap.comp_assoc` and
  friends record that regular maps form a category.
* `RegMap.evalAt_toAlgHom` is literally `(f̃ ψ)(x) = ψ(f(x))`, and `RegMap.ofAlgHom_apply_eq`
  is the source's formula `f(x) = (φ(t̄₁)(x), …, φ(t̄_m)(x))`.

The argument uses no Nullstellensatz and no algebraic closedness: everything is the
elementary algebra of `k[t₁,…,tₙ]` and its quotients, valid over any field.  Note also that
`X` need not be algebraic for the construction: `regMapEquivAlgHom` only assumes `Y`
algebraic.
-/

namespace AtiyahMcdonald69.Ex_1_28

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]
variable {n m l : ℕ}

/-! ## 1. The vanishing ideal `I(X)` and the coordinate ring `P(X)` -/

/-- `I(X)`: the ideal of polynomials vanishing at every point of `X ⊆ k^n` (A&M, §1). -/
def idealOf (X : Set (Fin n → k)) : Ideal (MvPolynomial (Fin n) k) := vanishingIdeal k X

@[simp]
theorem mem_idealOf {X : Set (Fin n → k)} {p : MvPolynomial (Fin n) k} :
    p ∈ idealOf X ↔ ∀ x ∈ X, aeval x p = 0 := Iff.rfl

/-- `P(X) = k[t₁,…,tₙ]/I(X)`: A&M's coordinate ring of `X`. -/
abbrev coordRing (X : Set (Fin n → k)) : Type _ := MvPolynomial (Fin n) k ⧸ idealOf X

/-- On elements, the `k`-algebra quotient map is the ring quotient map. -/
theorem mkₐ_apply_eq_mk (X : Set (Fin n → k)) (p : MvPolynomial (Fin n) k) :
    Ideal.Quotient.mkₐ k (idealOf X) p = Ideal.Quotient.mk (idealOf X) p :=
  rfl

/-- A&M (p. 16): `g` and `h` define the same polynomial function on `X` iff `g - h ∈ I(X)`. -/
theorem mk_eq_mk_iff_aeval_eq {X : Set (Fin n → k)} {p q : MvPolynomial (Fin n) k} :
    Ideal.Quotient.mk (idealOf X) p = Ideal.Quotient.mk (idealOf X) q ↔
      ∀ x ∈ X, aeval x p = aeval x q := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_idealOf]
  constructor
  · intro hp x hx
    have h := hp x hx
    rwa [map_sub, sub_eq_zero] at h
  · intro h x hx
    rw [map_sub, h x hx, sub_self]

/-- The `i`-th coordinate function `t̄ᵢ ∈ P(X)`. -/
def coordFn (X : Set (Fin n → k)) (i : Fin n) : coordRing X :=
  Ideal.Quotient.mk (idealOf X) (MvPolynomial.X i)

/-- Evaluation of a polynomial function at a point of `X`. -/
def evalAt (X : Set (Fin n → k)) (x : X) : coordRing X →ₐ[k] k :=
  Ideal.Quotient.liftₐ (idealOf X) (MvPolynomial.aeval (x : Fin n → k))
    fun p hp => by simpa using (mem_idealOf.1 hp) x.1 x.2

theorem evalAt_mk (X : Set (Fin n → k)) (x : X) (p : MvPolynomial (Fin n) k) :
    evalAt X x (Ideal.Quotient.mk (idealOf X) p) = MvPolynomial.aeval (x : Fin n → k) p :=
  rfl

theorem evalAt_coordFn (X : Set (Fin n → k)) (x : X) (i : Fin n) :
    evalAt X x (coordFn X i) = (x : Fin n → k) i := by
  rw [coordFn, evalAt_mk, MvPolynomial.aeval_X]

/-- `P(X)` is the ring of polynomial functions on `X`: its elements are separated by
evaluation at the points of `X` (this is A&M's identification of `k[t]/I(X)` with the ring of
polynomial functions). -/
theorem evalAt_eq_iff {X : Set (Fin n → k)} {ψ₁ ψ₂ : coordRing X} :
    (∀ x : X, evalAt X x ψ₁ = evalAt X x ψ₂) ↔ ψ₁ = ψ₂ := by
  refine ⟨fun h => ?_, fun h x => by rw [h]⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective ψ₁
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective ψ₂
  rw [mk_eq_mk_iff_aeval_eq]
  intro x hx
  have hx' := h ⟨x, hx⟩
  rwa [evalAt_mk, evalAt_mk] at hx'

/-- `P(X)` is generated by the coordinate functions: a `k`-algebra homomorphism out of
`P(X)` is determined by its values on `t̄₁, …, t̄ₙ`. -/
theorem algHom_ext_coordFn {A : Type _} [Semiring A] [Algebra k A] {X : Set (Fin n → k)}
    {φ ψ : coordRing X →ₐ[k] A} (h : ∀ i, φ (coordFn X i) = ψ (coordFn X i)) : φ = ψ := by
  have hcomp : φ.comp (Ideal.Quotient.mkₐ k (idealOf X)) =
      ψ.comp (Ideal.Quotient.mkₐ k (idealOf X)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, mkₐ_apply_eq_mk]
    exact h i
  refine AlgHom.ext fun y => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have := congrArg (fun g : MvPolynomial (Fin n) k →ₐ[k] A => g p) hcomp
  simpa only [AlgHom.comp_apply, mkₐ_apply_eq_mk] using this

/-! ## 2. Affine algebraic varieties -/

/-- A&M, §1: the set of common zeros of a set of polynomial equations in `n` variables. -/
def IsAffineAlgebraic (X : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), X = zeroLocus k (Ideal.span S)

theorem isAffineAlgebraic_iff_exists (X : Set (Fin n → k)) :
    IsAffineAlgebraic X ↔
      ∃ S : Set (MvPolynomial (Fin n) k), ∀ x, x ∈ X ↔ ∀ p ∈ S, aeval x p = 0 := by
  unfold IsAffineAlgebraic
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨S, fun x => by simp only [zeroLocus_span, Set.mem_ofPred_eq]⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, by ext x; rw [zeroLocus_span]; exact hS x⟩

theorem isAffineAlgebraic_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    IsAffineAlgebraic (zeroLocus k I) :=
  ⟨I, by rw [Ideal.span_eq]⟩

theorem isAffineAlgebraic_univ : IsAffineAlgebraic (Set.univ : Set (Fin n → k)) :=
  ⟨⊥, by simp⟩

/-- Vanishing on all of `I(Y)` detects the points of an algebraic set `Y`. -/
theorem mem_of_forall_aeval_eq_zero {Y : Set (Fin m → k)} (hY : IsAffineAlgebraic Y)
    {y : Fin m → k} (h : ∀ q ∈ idealOf Y, aeval y q = 0) : y ∈ Y := by
  obtain ⟨S, rfl⟩ := hY
  rw [zeroLocus_span]
  intro p hp
  exact h p (le_vanishingIdeal_zeroLocus (Ideal.span S) (Ideal.subset_span hp))

/-- For an algebraic set, `Y` is exactly the zero locus of its vanishing ideal. -/
theorem zeroLocus_idealOf {Y : Set (Fin m → k)} (hY : IsAffineAlgebraic Y) :
    zeroLocus k (idealOf Y) = Y := by
  refine le_antisymm (fun y hy => mem_of_forall_aeval_eq_zero hY hy) ?_
  intro y hy q hq
  exact (mem_idealOf.1 hq) y hy

/-! ## 3. Regular maps -/

/-- A&M, Ex. 1.28: `f : X → Y` is regular if it is the restriction to `X` of a polynomial
mapping `k^n → k^m`. -/
def IsRegularMap (X : Set (Fin n → k)) (Y : Set (Fin m → k)) (f : X → Y) : Prop :=
  ∃ F : Fin m → MvPolynomial (Fin n) k,
    ∀ (x : X) (i : Fin m), (f x).1 i = MvPolynomial.aeval (x : Fin n → k) (F i)

/-- The type of regular maps `X → Y`; equality is equality of the underlying mappings. -/
def RegMap (X : Set (Fin n → k)) (Y : Set (Fin m → k)) := {f : X → Y // IsRegularMap X Y f}

namespace RegMap

variable {X : Set (Fin n → k)} {Y : Set (Fin m → k)} {Z : Set (Fin l → k)}
variable {p : ℕ} {W : Set (Fin p → k)}

/-- A polynomial description of a regular map. -/
def poly (f : RegMap X Y) : Fin m → MvPolynomial (Fin n) k := f.2.choose

theorem poly_spec (f : RegMap X Y) (x : X) (i : Fin m) :
    (f.1 x).1 i = MvPolynomial.aeval (x : Fin n → k) (poly f i) := f.2.choose_spec x i

theorem ext {f g : RegMap X Y} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (funext h)

/-- Two polynomial tuples that agree as functions on `X` define the same elements of `P(X)`. -/
theorem mk_eq_of_aeval_eq {F G : Fin m → MvPolynomial (Fin n) k}
    (h : ∀ (x : X) (i : Fin m), aeval (x : Fin n → k) (F i) = aeval (x : Fin n → k) (G i))
    (i : Fin m) : Ideal.Quotient.mk (idealOf X) (F i) = Ideal.Quotient.mk (idealOf X) (G i) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_idealOf]
  intro x hx
  rw [map_sub, h ⟨x, hx⟩ i, sub_self]

/-- A polynomial tuple agreeing with `f` on `X` represents `poly f` in `P(X)`. -/
theorem mk_poly_eq {f : RegMap X Y} {G : Fin m → MvPolynomial (Fin n) k}
    (h : ∀ (x : X) (i : Fin m), (f.1 x).1 i = MvPolynomial.aeval (x : Fin n → k) (G i))
    (i : Fin m) : Ideal.Quotient.mk (idealOf X) (poly f i) = Ideal.Quotient.mk (idealOf X) (G i) :=
  mk_eq_of_aeval_eq (fun x i => (poly_spec f x i).symm.trans (h x i)) i

/-- Polynomials with equal images in `P(X)` take equal values on `X`. -/
theorem aeval_eq_of_mk_eq {p q : MvPolynomial (Fin n) k}
    (h : Ideal.Quotient.mk (idealOf X) p = Ideal.Quotient.mk (idealOf X) q) {x : Fin n → k}
    (hx : x ∈ X) : aeval x p = aeval x q := by
  have h' : p - q ∈ idealOf X :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := idealOf X) p q).1 h
  have h'' : aeval x (p - q) = 0 := (mem_idealOf.1 h') x hx
  rwa [map_sub, sub_eq_zero] at h''

/-- Iterated substitution. -/
theorem aeval_aeval {σ : Type*} {A : Type*} [CommSemiring A] [Algebra k A] (x : σ → A)
    (F : Fin m → MvPolynomial σ k) (q : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval x (MvPolynomial.aeval F q) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (F i)) q :=
  congrArg (fun g : MvPolynomial (Fin m) k →ₐ[k] A => g q)
    (MvPolynomial.comp_aeval F (MvPolynomial.aeval x))

/-! ## 4. The algebra homomorphism induced by a regular map -/

/-- `aeval F q` vanishes on `X` when `q` vanishes on `Y` and `F` describes a map `X → Y`. -/
theorem aeval_mem_idealOf (f : RegMap X Y) {q : MvPolynomial (Fin m) k} (hq : q ∈ idealOf Y) :
    MvPolynomial.aeval (poly f) q ∈ idealOf X := by
  rw [mem_idealOf]
  intro x hx
  rw [aeval_aeval]
  rw [show (fun i => MvPolynomial.aeval (x : Fin n → k) (poly f i)) = (f.1 ⟨x, hx⟩).1 from
    funext fun i => (poly_spec f ⟨x, hx⟩ i).symm]
  exact (mem_idealOf.1 hq) (f.1 ⟨x, hx⟩).1 (f.1 ⟨x, hx⟩).2

theorem toAlgHom_ker (f : RegMap X Y) :
    ∀ q : MvPolynomial (Fin m) k, q ∈ idealOf Y →
      ((Ideal.Quotient.mkₐ k (idealOf X)).comp (MvPolynomial.aeval (poly f))) q = 0 := by
  intro q hq
  rw [AlgHom.comp_apply, mkₐ_apply_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact aeval_mem_idealOf f hq

/-- A&M, Ex. 1.28: a regular map `f : X → Y` induces `f̃ : P(Y) → P(X)`, `ψ ↦ ψ ∘ f`. -/
def toAlgHom (f : RegMap X Y) : coordRing Y →ₐ[k] coordRing X :=
  Ideal.Quotient.liftₐ (idealOf Y)
    ((Ideal.Quotient.mkₐ k (idealOf X)).comp (MvPolynomial.aeval (poly f))) (toAlgHom_ker f)

/-- The induced homomorphism is substitution followed by reduction. -/
theorem toAlgHom_mk (f : RegMap X Y) (q : MvPolynomial (Fin m) k) :
    toAlgHom f (Ideal.Quotient.mk (idealOf Y) q) =
      Ideal.Quotient.mk (idealOf X) (MvPolynomial.aeval (poly f) q) := by
  rfl

/-- On the coordinate function `t̄ᵢ ∈ P(Y)`, `f̃` is the class of the `i`-th coordinate
polynomial of `f`. -/
theorem toAlgHom_coordFn (f : RegMap X Y) (i : Fin m) :
    toAlgHom f (coordFn Y i) = Ideal.Quotient.mk (idealOf X) (poly f i) := by
  rw [coordFn, toAlgHom_mk, MvPolynomial.aeval_X]

/-- `f̃ψ` is `ψ ∘ f`: the induced homomorphism computes pointwise as precomposition. -/
theorem evalAt_toAlgHom (f : RegMap X Y) (ψ : coordRing Y) (x : X) :
    evalAt X x (toAlgHom f ψ) = evalAt Y (f.1 x) ψ := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective ψ
  rw [toAlgHom_mk, evalAt_mk, evalAt_mk, aeval_aeval,
    show (fun i => MvPolynomial.aeval (x : Fin n → k) (poly f i)) = (f.1 x).1 from
      funext fun i => (poly_spec f x i).symm]

/-! ## 5. The regular map induced by an algebra homomorphism -/

/-- A polynomial lift of the images of the coordinate functions of `P(Y)` under `φ`. -/
def liftPoly (φ : coordRing Y →ₐ[k] coordRing X) : Fin m → MvPolynomial (Fin n) k :=
  fun i => (Ideal.Quotient.mk_surjective (φ (coordFn Y i))).choose

theorem mk_liftPoly (φ : coordRing Y →ₐ[k] coordRing X) (i : Fin m) :
    Ideal.Quotient.mk (idealOf X) (liftPoly φ i) = φ (coordFn Y i) :=
  (Ideal.Quotient.mk_surjective (φ (coordFn Y i))).choose_spec

/-- `φ` applied to the class of `q` is the class of `q` evaluated at the lifted tuple. -/
theorem φ_mk (φ : coordRing Y →ₐ[k] coordRing X) (q : MvPolynomial (Fin m) k) :
    φ (Ideal.Quotient.mk (idealOf Y) q) =
      Ideal.Quotient.mk (idealOf X) (MvPolynomial.aeval (liftPoly φ) q) := by
  have h : φ.comp (Ideal.Quotient.mkₐ k (idealOf Y)) =
      (Ideal.Quotient.mkₐ k (idealOf X)).comp (MvPolynomial.aeval (liftPoly φ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, mkₐ_apply_eq_mk,
      mkₐ_apply_eq_mk]
    exact (mk_liftPoly φ i).symm
  calc φ (Ideal.Quotient.mk (idealOf Y) q)
      = (φ.comp (Ideal.Quotient.mkₐ k (idealOf Y))) q := rfl
    _ = ((Ideal.Quotient.mkₐ k (idealOf X)).comp (MvPolynomial.aeval (liftPoly φ))) q := by
          rw [h]
    _ = Ideal.Quotient.mk (idealOf X) (MvPolynomial.aeval (liftPoly φ) q) := rfl

variable (hY : IsAffineAlgebraic Y)

/-- A&M, Ex. 1.28 (converse): a `k`-algebra homomorphism `φ : P(Y) → P(X)` is induced by
the regular map `x ↦ (φ(t̄₁)(x), …, φ(t̄_m)(x))`. -/
def ofAlgHom (φ : coordRing Y →ₐ[k] coordRing X) : RegMap X Y :=
  ⟨fun x =>
      ⟨fun i => MvPolynomial.aeval (x : Fin n → k) (liftPoly φ i),
        mem_of_forall_aeval_eq_zero hY fun q hq => by
          rw [← aeval_aeval (x := (x : Fin n → k)) (F := liftPoly φ) (q := q)]
          have hmem : MvPolynomial.aeval (liftPoly φ) q ∈ idealOf X := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, ← φ_mk φ q,
              Ideal.Quotient.eq_zero_iff_mem.2 hq, map_zero]
          exact (mem_idealOf.1 hmem) x.1 x.2⟩,
    ⟨liftPoly φ, fun x i => rfl⟩⟩

variable {hY}

theorem ofAlgHom_apply (φ : coordRing Y →ₐ[k] coordRing X) (x : X) (i : Fin m) :
    ((ofAlgHom hY φ).1 x).1 i = MvPolynomial.aeval (x : Fin n → k) (liftPoly φ i) := rfl

/-- The source's formula `f(x) = (φ(t̄₁)(x), …, φ(t̄_m)(x))`. -/
theorem ofAlgHom_apply_eq (φ : coordRing Y →ₐ[k] coordRing X) (x : X) (i : Fin m) :
    ((ofAlgHom hY φ).1 x).1 i = evalAt X x (φ (coordFn Y i)) :=
  (ofAlgHom_apply (hY := hY) φ x i).trans (by rw [← mk_liftPoly φ i, evalAt_mk])

/-- `f̃` of the reconstructed map is `φ` again: the coordinate functions generate `P(Y)`. -/
theorem toAlgHom_ofAlgHom (φ : coordRing Y →ₐ[k] coordRing X) :
    toAlgHom (ofAlgHom hY φ) = φ := by
  refine algHom_ext_coordFn fun i => ?_
  rw [toAlgHom_coordFn, ← mk_liftPoly φ i]
  exact mk_poly_eq (f := ofAlgHom hY φ) (G := liftPoly φ)
    (fun x j => ofAlgHom_apply (hY := hY) φ x j) i

/-- Reconstructing from `f̃` gives back `f`. -/
theorem ofAlgHom_toAlgHom (f : RegMap X Y) : ofAlgHom hY (toAlgHom f) = f := by
  refine ext fun x => Subtype.ext (funext fun i => ?_)
  exact (ofAlgHom_apply (hY := hY) (toAlgHom f) x i).trans
    ((aeval_eq_of_mk_eq ((mk_liftPoly (toAlgHom f) i).trans (toAlgHom_coordFn f i)) x.2).trans
      (poly_spec f x i).symm)

/-! ## 6. Identity and composition -/

theorem id_spec (X : Set (Fin n → k)) (x : X) (i : Fin n) :
    (x : Fin n → k) i =
      MvPolynomial.aeval (x : Fin n → k) (MvPolynomial.X i : MvPolynomial (Fin n) k) :=
  (MvPolynomial.aeval_X (x : Fin n → k) i).symm

/-- The identity regular map. -/
def id (X : Set (Fin n → k)) : RegMap X X :=
  ⟨fun x => x, fun i => MvPolynomial.X i, fun x i => id_spec X x i⟩

theorem comp_poly_spec (g : RegMap Y Z) (f : RegMap X Y) (x : X) (j : Fin l) :
    (g.1 (f.1 x)).1 j =
      MvPolynomial.aeval (x : Fin n → k) (MvPolynomial.aeval (poly f) (poly g j)) := by
  rw [aeval_aeval,
    show (fun i => MvPolynomial.aeval (x : Fin n → k) (poly f i)) = (f.1 x).1 from
      funext fun i => (poly_spec f x i).symm]
  exact poly_spec g (f.1 x) j

/-- Composition of regular maps. -/
def comp (g : RegMap Y Z) (f : RegMap X Y) : RegMap X Z :=
  ⟨fun x => g.1 (f.1 x), fun j => MvPolynomial.aeval (poly f) (poly g j), comp_poly_spec g f⟩

theorem comp_id (f : RegMap X Y) : comp (id Y) f = f := by
  refine ext fun x => Subtype.ext (funext fun i => ?_)
  rfl

theorem id_comp (f : RegMap X Y) : comp f (id X) = f := by
  refine ext fun x => Subtype.ext (funext fun i => ?_)
  rfl

theorem comp_assoc (h : RegMap Z W) (g : RegMap Y Z) (f : RegMap X Y) :
    comp (comp h g) f = comp h (comp g f) := by
  refine ext fun x => Subtype.ext (funext fun i => ?_)
  rfl

theorem toAlgHom_id : toAlgHom (id X) = AlgHom.id k (coordRing X) := by
  refine algHom_ext_coordFn fun i => ?_
  rw [toAlgHom_coordFn]
  refine (mk_poly_eq (f := id X) (G := fun i => MvPolynomial.X i)
    (fun x j => id_spec X x j) i).trans ?_
  rfl

theorem toAlgHom_comp (g : RegMap Y Z) (f : RegMap X Y) :
    toAlgHom (comp g f) = (toAlgHom f).comp (toAlgHom g) := by
  refine algHom_ext_coordFn fun j => ?_
  rw [AlgHom.comp_apply, toAlgHom_coordFn g j, toAlgHom_mk f (poly g j),
    toAlgHom_coordFn (comp g f) j]
  exact mk_poly_eq (f := comp g f) (G := fun j => MvPolynomial.aeval (poly f) (poly g j))
    (fun x j => comp_poly_spec g f x j) j

end RegMap

/-! ## 7. The bijection -/

variable {X : Set (Fin n → k)} {Y : Set (Fin m → k)}

/-- **Atiyah–Macdonald, Exercise 1.28.**  For `Y` an affine algebraic variety, regular maps
`X → Y` correspond bijectively to `k`-algebra homomorphisms `P(Y) → P(X)`. -/
def regMapEquivAlgHom (hY : IsAffineAlgebraic Y) :
    RegMap X Y ≃ (coordRing Y →ₐ[k] coordRing X) where
  toFun := RegMap.toAlgHom
  invFun := RegMap.ofAlgHom hY
  left_inv := RegMap.ofAlgHom_toAlgHom (hY := hY)
  right_inv := RegMap.toAlgHom_ofAlgHom (hY := hY)

theorem bijective_toAlgHom (hY : IsAffineAlgebraic Y) :
    Function.Bijective (RegMap.toAlgHom : RegMap X Y → coordRing Y →ₐ[k] coordRing X) :=
  ⟨fun f g h => (RegMap.ofAlgHom_toAlgHom (hY := hY) f).symm.trans
      ((congrArg (RegMap.ofAlgHom hY) h).trans (RegMap.ofAlgHom_toAlgHom (hY := hY) g)),
    fun φ => ⟨RegMap.ofAlgHom hY φ, RegMap.toAlgHom_ofAlgHom (hY := hY) φ⟩⟩

/-- **Atiyah–Macdonald, Exercise 1.28**, verbatim form: for affine algebraic varieties
`X ⊆ k^n` and `Y ⊆ k^m`, the regular maps `X → Y` are in bijection with the `k`-algebra
homomorphisms `P(Y) → P(X)`. -/
def exercise_1_28 (hX : IsAffineAlgebraic X) (hY : IsAffineAlgebraic Y) :
    RegMap X Y ≃ (coordRing Y →ₐ[k] coordRing X) :=
  have _ := hX
  regMapEquivAlgHom hY

/-- The two inverse constructions of Exercise 1.28, as a pair of round-trip identities. -/
theorem exercise_1_28_inverses (hX : IsAffineAlgebraic X) (hY : IsAffineAlgebraic Y) :
    (∀ f : RegMap X Y, RegMap.ofAlgHom hY (RegMap.toAlgHom f) = f) ∧
      (∀ φ : coordRing Y →ₐ[k] coordRing X, RegMap.toAlgHom (RegMap.ofAlgHom hY φ) = φ) :=
  have _ := hX
  ⟨RegMap.ofAlgHom_toAlgHom (hY := hY), RegMap.toAlgHom_ofAlgHom (hY := hY)⟩

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_1_28.exercise_1_28
#print axioms AtiyahMcdonald69.Ex_1_28.bijective_toAlgHom
#print axioms AtiyahMcdonald69.Ex_1_28.exercise_1_28_inverses
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.toAlgHom
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.ofAlgHom
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.evalAt_toAlgHom
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.ofAlgHom_apply_eq
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.toAlgHom_id
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.toAlgHom_comp
#print axioms AtiyahMcdonald69.Ex_1_28.mk_eq_mk_iff_aeval_eq
#print axioms AtiyahMcdonald69.Ex_1_28.evalAt_eq_iff
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.comp_poly_spec
#print axioms AtiyahMcdonald69.Ex_1_28.RegMap.comp_assoc

end

end AtiyahMcdonald69.Ex_1_28
