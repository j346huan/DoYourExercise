import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Chapter I, Exercise 1.1

Throughout, `k` is an algebraically closed field and `k[x,y]` is the polynomial ring in two
variables.  For an algebraic set `S ⊆ 𝔸²` (a point set with the Zariski topology) we write
`A(S) = k[x,y]/I(S)` for its affine coordinate ring, where `I(S)` is the ideal of polynomials
vanishing on `S`: the point-set, "classical" convention of Chapter I.

The exercise (Hartshorne, *Algebraic Geometry*, GTM 52, Exercise I.1.1) reads:

(a) Let `Y` be the plane curve `y = x²` (i.e. `Y` is the zero set of the polynomial
    `f = y - x²`).  Show that `A(Y)` is isomorphic to a polynomial ring in one variable
    over `k`.
(b) Let `Z` be the plane curve `xy = 1`.  Show that `A(Z)` is *not* isomorphic to a
    polynomial ring in one variable over `k`.
(c) Let `f` be any irreducible quadratic polynomial in `k[x,y]`, and let `W` be the conic
    defined by `f`.  Show that `A(W)` is isomorphic to `A(Y)` or to `A(Z)`.  Which one is
    it when?

The answer to the last question: it is `A(Z)` (two distinct points at infinity) when the
degree two homogeneous part of `f` is a product of two *distinct* linear forms, and `A(Y)`
(one point at infinity, a tangency) when it is the square of a linear form.
-/

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_1_1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The polynomial ring `k[x,y]` in two variables. -/
abbrev R (k : Type*) [CommSemiring k] : Type _ := MvPolynomial (Fin 2) k

/-- The affine plane over `k`, as a point set. -/
abbrev Plane (k : Type*) : Type _ := Fin 2 → k

/-- The first coordinate function, in `k[x,y]`. -/
abbrev Xx (k : Type*) [CommSemiring k] : R k := MvPolynomial.X 0

/-- The second coordinate function, in `k[x,y]`. -/
abbrev Yy (k : Type*) [CommSemiring k] : R k := MvPolynomial.X 1

/-! ## The coordinate ring of a point set -/

/-- `Z(S)`: the algebraic set defined by a set `S` of polynomials. -/
def alset (S : Set (R k)) : Set (Plane k) := MvPolynomial.zeroLocus k (Ideal.span S)

/-- `I(S)`: the vanishing ideal of a set of points. -/
def van (S : Set (Plane k)) : Ideal (R k) := MvPolynomial.vanishingIdeal k S

/-- `A(S) = k[x,y]/I(S)`: the affine coordinate ring of a point set `S ⊆ 𝔸²`. -/
abbrev A (S : Set (Plane k)) : Type _ := R k ⧸ van S

/-- Evaluation at a point of the plane, as a `k`-algebra homomorphism. -/
abbrev ev (z : Plane k) : R k →ₐ[k] k := MvPolynomial.aeval z

@[simp]
theorem mem_alset_singleton {f : R k} {z : Plane k} : z ∈ alset {f} ↔ ev z f = 0 := by
  simp [alset, ev, MvPolynomial.zeroLocus_span]

/-- Substitution of a pair commutes with evaluation at a point. -/
theorem ev_aeval_gen (w : Fin 2 → R k) (z : Plane k) (p : R k) :
    ev z (MvPolynomial.aeval w p) = ev (fun i => ev z (w i)) p := by
  rw [ev, MvPolynomial.comp_aeval_apply]

/-- Substitution of a pair commutes with the one-variable substitution `t ↦ a`. -/
theorem polynomial_aeval_aeval_gen (w : Fin 2 → Polynomial k) (a : k) (p : R k) :
    Polynomial.aeval a (MvPolynomial.aeval w p) =
      MvPolynomial.aeval (fun i => Polynomial.aeval a (w i)) p := by
  rw [MvPolynomial.comp_aeval_apply]

/-- Evaluation at a point `z` of `S` gives a `k`-algebra homomorphism `A(S) → k`. -/
def evQuot {S : Set (Plane k)} (z : Plane k) (hz : z ∈ S) : A S →ₐ[k] k :=
  Ideal.Quotient.liftₐ (van S) (ev z) (fun a ha => by
    rw [van, MvPolynomial.mem_vanishingIdeal_iff] at ha
    simpa using ha z hz)

@[simp]
theorem evQuot_mk {S : Set (Plane k)} (z : Plane k) (hz : z ∈ S) (p : R k) :
    evQuot z hz (Ideal.Quotient.mk (van S) p) = ev z p := by
  simp [evQuot]

/-! ## Transporting coordinate rings along affine substitutions

If an affine substitution of `k[x,y]`, with inverse substitution, carries the defining equation
`f` of `Z(f)` to a constant multiple of the defining equation `g` of `Z(g)`, then it induces an
isomorphism `A(Z(f)) ≃ A(Z(g))` of coordinate rings.  This is the working tool for all the
explicit computations below. -/

/-- A substitution which maps the defining equation of `Z(f)` to a multiple of the defining
equation of `Z(g)` maps `I(Z(f))` into `I(Z(g))`. -/
theorem aeval_mem_van_alset {f g : R k} {w : Fin 2 → R k} {c : k}
    (hfg : MvPolynomial.aeval w f = MvPolynomial.C c * g) :
    ∀ q ∈ van (alset {f}), MvPolynomial.aeval w q ∈ van (alset {g}) := by
  intro q hq
  rw [van, MvPolynomial.mem_vanishingIdeal_iff] at hq ⊢
  intro z hz
  rw [show (MvPolynomial.aeval z) (MvPolynomial.aeval w q) = ev (fun i => ev z (w i)) q from
    ev_aeval_gen w z q]
  have hz' : ev (fun i => ev z (w i)) f = 0 := by
    have h : ev z (MvPolynomial.aeval w f) = 0 := by
      rw [hfg, map_mul, mem_alset_singleton.mp hz, mul_zero]
    rwa [show ev z (MvPolynomial.aeval w f) = ev (fun i => ev z (w i)) f from
      ev_aeval_gen w z f] at h
  have hmem : ((fun i => ev z (w i)) : Plane k) ∈ alset {f} := by
    rw [mem_alset_singleton]; exact hz'
  exact hq _ hmem

/-- The same statement for an algebra equivalence of `k[x,y]`. -/
theorem algEquiv_mem_van_alset {f g : R k} (e : R k ≃ₐ[k] R k) {c : k}
    (hfg : e f = MvPolynomial.C c * g) :
    ∀ q ∈ van (alset {f}), (e : R k →ₐ[k] R k) q ∈ van (alset {g}) := by
  have he : (e : R k →ₐ[k] R k) = MvPolynomial.aeval ((e : R k →ₐ[k] R k) ∘ MvPolynomial.X) :=
    MvPolynomial.aeval_unique (e : R k →ₐ[k] R k)
  have hfg' : MvPolynomial.aeval ((e : R k →ₐ[k] R k) ∘ MvPolynomial.X) f =
      MvPolynomial.C c * g := by
    rw [← he]; exact hfg
  intro q hq
  rw [he]
  exact aeval_mem_van_alset hfg' q hq

/-- An algebra equivalence of `k[x,y]` carrying `Z(f)` to `Z(g)` induces an isomorphism of
coordinate rings. -/
def quotEquivOfAlgEquiv {f g : R k} (e : R k ≃ₐ[k] R k) {c c' : k}
    (hfg : e f = MvPolynomial.C c * g) (hgf : e.symm g = MvPolynomial.C c' * f) :
    A (alset {f}) ≃ₐ[k] A (alset {g}) := by
  have h1 := algEquiv_mem_van_alset e hfg
  have h2 := algEquiv_mem_van_alset e.symm hgf
  have hmap : (van (alset {f})).map (e : R k →+* R k) ≤ van (alset {g}) := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    simpa using h1 q hq
  have hmap' : van (alset {g}) ≤ (van (alset {f})).map (e : R k →+* R k) := by
    intro q hq
    have hq' : e.symm q ∈ van (alset {f}) := h2 q hq
    have hmem : (e : R k →+* R k) (e.symm q) ∈ (van (alset {f})).map (e : R k →+* R k) :=
      Ideal.mem_map_of_mem _ hq'
    have hcoe : (e : R k →+* R k) (e.symm q) = q := by
      simpa using AlgEquiv.apply_symm_apply e q
    rwa [hcoe] at hmem
  exact Ideal.quotientEquivAlg (van (alset {f})) (van (alset {g})) e (le_antisymm hmap' hmap)

/-- The substitution `(u,v)` as an algebra equivalence of `k[x,y]`. -/
def substEquiv (u v u' v' : R k)
    (hcomp : (MvPolynomial.aeval ![u, v]).comp (MvPolynomial.aeval ![u', v'])
      = AlgHom.id k (R k))
    (hcomp' : (MvPolynomial.aeval ![u', v']).comp (MvPolynomial.aeval ![u, v])
      = AlgHom.id k (R k)) :
    R k ≃ₐ[k] R k where
  toFun := MvPolynomial.aeval ![u, v]
  invFun := MvPolynomial.aeval ![u', v']
  left_inv q := by simpa using AlgHom.congr_fun hcomp' q
  right_inv q := by simpa using AlgHom.congr_fun hcomp q
  map_mul' q r := map_mul _ q r
  map_add' q r := map_add _ q r
  commutes' r := by simp

/-- An affine coordinate change `(u,v)` carrying `Z(f)` to `Z(g)`, with inverse `(u',v')`,
induces an isomorphism `A(Z(f)) ≃ₐ[k] A(Z(g))` of coordinate rings. -/
def quotEquivOfSubst {f g : R k} {u v u' v' : R k} {c c' : k}
    (hcomp : (MvPolynomial.aeval ![u, v]).comp (MvPolynomial.aeval ![u', v'])
      = AlgHom.id k (R k))
    (hcomp' : (MvPolynomial.aeval ![u', v']).comp (MvPolynomial.aeval ![u, v])
      = AlgHom.id k (R k))
    (hfg : MvPolynomial.aeval ![u, v] f = MvPolynomial.C c * g)
    (hgf : MvPolynomial.aeval ![u', v'] g = MvPolynomial.C c' * f) :
    A (alset {f}) ≃ₐ[k] A (alset {g}) :=
  quotEquivOfAlgEquiv (substEquiv u v u' v' hcomp hcomp') hfg hgf

/-! ## Part (a): the parabola `Y : y = x²` -/

/-- The parabola `Y = Z(y - x²)`. -/
def Yset (k : Type*) [Field k] : Set (Plane k) :=
  alset {Yy k - Xx k ^ 2}

/-- The defining polynomial `y - x²` of the parabola. -/
def parabola (k : Type*) [Field k] : R k := Yy k - Xx k ^ 2

/-- The substitution `x ↦ t`, `y ↦ t²`. -/
def parSub : R k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval ![(Polynomial.X : Polynomial k), Polynomial.X ^ 2]

/-- The one-variable substitution `t ↦ x`, a one-sided inverse to `parSub`. -/
def parSect : Polynomial k →ₐ[k] R k := Polynomial.aeval (Xx k)

theorem parSub_parSect : parSub.comp parSect = AlgHom.id k (Polynomial k) := by
  apply Polynomial.algHom_ext
  simp [parSub, parSect]

theorem parSub_surjective : Function.Surjective (parSub (k := k)) := fun (p : Polynomial k) =>
  ⟨parSect p, AlgHom.congr_fun parSub_parSect p⟩

theorem parSub_parabola : parSub (parabola k) = 0 := by
  simp [parSub, parabola]

theorem parSub_eq_zero_of_mem_van {q : R k} (hq : q ∈ van (Yset k)) : parSub q = 0 := by
  apply Polynomial.funext
  intro a
  have h1 : Polynomial.eval a (parSub q) = MvPolynomial.aeval ![a, a ^ 2] q := by
    show Polynomial.aeval a (MvPolynomial.aeval
      ![(Polynomial.X : Polynomial k), Polynomial.X ^ 2] q) = _
    rw [polynomial_aeval_aeval_gen]
    have h : (fun i : Fin 2 =>
        Polynomial.aeval a (![(Polynomial.X : Polynomial k), Polynomial.X ^ 2] i)) = ![a, a ^ 2] := by
      funext i
      fin_cases i <;> simp
    rw [h]
  rw [h1, Polynomial.eval_zero]
  have h2 : (![a, a ^ 2] : Plane k) ∈ Yset k := by
    rw [Yset, mem_alset_singleton]
    simp [parabola]
  exact (MvPolynomial.mem_vanishingIdeal_iff.mp hq) _ h2

theorem parabola_mem_van_Y : parabola k ∈ van (Yset k) :=
  MvPolynomial.le_vanishingIdeal_zeroLocus (Ideal.span {parabola k}) (Ideal.subset_span rfl)

/-- The substitution `x ↦ t`, `y ↦ t²`, as a ring homomorphism. -/
def parSubR (k : Type*) [Field k] : R k →+* Polynomial k := parSub (k := k)

/-- The ideal of the parabola is the kernel of `x ↦ t`, `y ↦ t²`. -/
theorem van_Yset_eq : van (Yset k) = RingHom.ker (parSubR k) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    simpa [parSubR] using parSub_eq_zero_of_mem_van hq
  · intro q hq
    rw [van, MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    have hpar : parSub q = 0 := by simpa [parSubR, RingHom.mem_ker] using hq
    have hz' : z 1 = z 0 ^ 2 := by
      have h := mem_alset_singleton.mp hz
      simp only [parabola, Yy, Xx, map_sub, map_pow, MvPolynomial.aeval_X] at h
      linear_combination h
    have hz'' : z = ![z 0, z 0 ^ 2] := by
      funext i
      fin_cases i <;> simp [hz']
    rw [hz'']
    have hpair := polynomial_aeval_aeval_gen
      (fun i : Fin 2 => (![(Polynomial.X : Polynomial k), Polynomial.X ^ 2] : Fin 2 → Polynomial k) i)
      (z 0) q
    have hfun : (fun i : Fin 2 =>
        Polynomial.aeval (z 0) (![(Polynomial.X : Polynomial k), Polynomial.X ^ 2] i)) =
        ![z 0, z 0 ^ 2] := by
      funext i
      fin_cases i <;> simp
    rw [← hfun, ← hpair]
    simp only [parSub] at hpar
    rw [hpar]
    simp

/-- **Part (a)**: the coordinate ring of the parabola is a polynomial ring in one variable. -/
theorem part_a : Nonempty (A (Yset k) ≃ₐ[k] Polynomial k) :=
  ⟨(Ideal.quotientEquivAlgOfEq k (van_Yset_eq)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := parSub) parSub_surjective)⟩

/-! ## Part (b): the hyperbola `Z : xy = 1` -/

/-- The hyperbola `Z = Z(xy - 1)`. -/
def Zset (k : Type*) [Field k] : Set (Plane k) :=
  alset {Xx k * Yy k - 1}

/-- The defining polynomial `xy - 1` of the hyperbola. -/
def hyperbola (k : Type*) [Field k] : R k := Xx k * Yy k - 1

theorem hyperbola_mem_van_Z : hyperbola k ∈ van (Zset k) :=
  MvPolynomial.le_vanishingIdeal_zeroLocus (Ideal.span {hyperbola k}) (Ideal.subset_span rfl)

/-- The class of `x` in `A(Z)` is a unit (with inverse the class of `y`). -/
theorem isUnit_mk_x_Z :
    IsUnit (Ideal.Quotient.mk (van (Zset k)) (Xx k) : A (Zset k)) := by
  have h0 : (Ideal.Quotient.mk (van (Zset k)) (hyperbola k) : A (Zset k)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hyperbola_mem_van_Z
  simp only [hyperbola, map_sub, map_mul, map_one] at h0
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (van (Zset k)) (Yy k)) ?_
  linear_combination h0

/-- For every `c : k` there is a nonzero `a` with `a ≠ c`. -/
theorem exists_ne_zero_ne (c : k) : ∃ a : k, a ≠ 0 ∧ a ≠ c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨1, one_ne_zero, one_ne_zero⟩
  · have hfin : ({0, c} : Set k).Finite := Set.toFinite _
    obtain ⟨a, ha⟩ := hfin.exists_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
    exact ⟨a, ha.1, ha.2⟩

/-- The class of `x` in `A(Z)` is not a constant. -/
theorem mk_x_Z_ne_algebraMap (c : k) :
    (Ideal.Quotient.mk (van (Zset k)) (Xx k) : A (Zset k)) ≠
      algebraMap k (A (Zset k)) c := by
  obtain ⟨a, ha0, hac⟩ := exists_ne_zero_ne c
  intro h
  have hz : (![a, a⁻¹] : Plane k) ∈ Zset k := by
    rw [Zset, mem_alset_singleton]
    simp only [hyperbola, map_sub, map_mul, map_one]
    simp [ha0]
  have h1 : evQuot (![a, a⁻¹]) hz (Ideal.Quotient.mk (van (Zset k)) (Xx k)) = a := by
    simp
  have h2 : evQuot (![a, a⁻¹]) hz (algebraMap k (A (Zset k)) c) = c := by
    simp
  rw [h] at h1
  exact hac (h1.symm.trans h2)

/-- **Part (b)**: `A(Z)` is not a polynomial ring in one variable over `k`.  The reason is
that `x` is a nonconstant unit of `A(Z)`, whereas the units of `k[t]` are the constants. -/
theorem part_b : ¬ Nonempty (A (Zset k) ≃ₐ[k] Polynomial k) := by
  rintro ⟨e⟩
  have hunit : IsUnit (e (Ideal.Quotient.mk (van (Zset k)) (Xx k))) :=
    isUnit_mk_x_Z.map (e : A (Zset k) →+* Polynomial k)
  obtain ⟨s, -, hsC⟩ := Polynomial.isUnit_iff.mp hunit
  have hconst : (Ideal.Quotient.mk (van (Zset k)) (Xx k) : A (Zset k)) =
      algebraMap k (A (Zset k)) s := by
    rw [← AlgEquiv.symm_apply_apply e (Ideal.Quotient.mk (van (Zset k)) (Xx k)), ← hsC]
    exact AlgEquiv.commutes e.symm s
  exact mk_x_Z_ne_algebraMap s hconst


/-! ## Part (c): an arbitrary irreducible conic

Let `f` be an irreducible quadratic polynomial and `W = Z(f)`.  Its degree two homogeneous
part factors as a product of two linear forms over `k`.  If the two factors are distinct, an
affine change of coordinates puts `f` in the form `U * V + ε` with `ε ≠ 0` (irreducibility),
and `(x,y) ↦ (U, -V/ε)` is an isomorphism of `W` with the hyperbola `xy = 1`.  If the two
factors coincide, `f` has the form `α * U ^ 2 + L + c` with `L` a linear form not proportional
to `U`, and an affine change of coordinates puts `f` in the form `α * U ^ 2 - V`, which is the
parabola `V = α * U ^ 2`; a further scaling of the coordinates identifies it with `y = x²`.
-/

/-- The linear form `p * x + r * y`. -/
def lin (p r : k) : R k := MvPolynomial.C p * Xx k + MvPolynomial.C r * Yy k

theorem aeval_lin (A B : R k) (p r : k) :
    MvPolynomial.aeval ![A, B] (lin p r) = MvPolynomial.C p * A + MvPolynomial.C r * B := by
  simp [lin]

theorem ev_lin (z : Plane k) (p r : k) : ev z (lin p r) = p * z 0 + r * z 1 := by
  simp [lin]

theorem ev_lin_add (z : Plane k) (p r β : k) :
    ev z (lin p r + MvPolynomial.C β) = p * z 0 + r * z 1 + β := by
  simp [lin]

theorem lin_ne_zero {p r : k} (h : p ≠ 0 ∨ r ≠ 0) : lin p r ≠ 0 := by
  intro hzero
  rcases h with hp | hr
  · apply hp
    have h1 := ev_lin (![1, 0] : Plane k) p r
    rw [hzero, map_zero] at h1
    simpa using h1.symm
  · apply hr
    have h1 := ev_lin (![0, 1] : Plane k) p r
    rw [hzero, map_zero] at h1
    simpa using h1.symm

/-- A nonzero linear form takes the value zero somewhere. -/
theorem exists_ev_lin_add (p r β : k) (h : p ≠ 0 ∨ r ≠ 0) :
    ∃ z : Plane k, ev z (lin p r + MvPolynomial.C β) = 0 := by
  rcases h with hp | hr
  · refine ⟨![-(β / p), 0], ?_⟩
    have h2 : ev (![-(β / p), 0] : Plane k) (lin p r + MvPolynomial.C β) =
        p * (-(β / p)) + r * 0 + β := by
      rw [ev_lin_add]
      simp
    rw [h2]
    field_simp
    ring
  · refine ⟨![0, -(β / r)], ?_⟩
    have h2 : ev (![0, -(β / r)] : Plane k) (lin p r + MvPolynomial.C β) =
        p * 0 + r * (-(β / r)) + β := by
      rw [ev_lin_add]
      simp
    rw [h2]
    field_simp
    ring

/-! ### The normal forms -/

/-- The substitution `x ↦ U`, `y ↦ -V/ε` for `f = U * V + ε`. -/
def σA (p r s t β α ε : k) : Fin 2 → R k :=
  ![lin p r + MvPolynomial.C β, MvPolynomial.C (-(1 / ε)) * (lin s t + MvPolynomial.C α)]

/-- Its inverse. -/
def τA (p r s t β α ε : k) : Fin 2 → R k :=
  ![MvPolynomial.C (1 / (p * t - r * s)) *
      (MvPolynomial.C t * Xx k + MvPolynomial.C (r * ε) * Yy k + MvPolynomial.C (r * α - t * β)),
    MvPolynomial.C (1 / (p * t - r * s)) *
      (-(MvPolynomial.C s) * Xx k - MvPolynomial.C (p * ε) * Yy k +
        MvPolynomial.C (s * β - p * α))]

/-- The various normal forms of a nonzero determinant. -/
theorem det_forms {p r s t : k} (h : p * t - r * s ≠ 0) :
    (t * p - r * s ≠ 0) ∧ (-(s * r) + p * t ≠ 0) ∧ (-(s * r) + t * p ≠ 0) ∧
    (t * p + -(s * r) ≠ 0) ∧ (p * t + -(r * s) ≠ 0) ∧ (p * t - s * r ≠ 0) ∧
    (t * p - s * r ≠ 0) ∧ (p * t - r * s ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h⟩ <;>
    · intro hh
      apply h
      linear_combination hh

theorem σA_τA_zero (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (_hε : ε ≠ 0) :
    MvPolynomial.aeval (σA p r s t β α ε) (τA p r s t β α ε 0) = Xx k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ := det_forms hδ
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σA p r s t β α ε) (τA p r s t β α ε 0))
      = ev (fun i => ev z (σA p r s t β α ε i)) (τA p r s t β α ε 0) from ev_aeval_gen _ z _]
  simp only [τA, σA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem σA_τA_one (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0) :
    MvPolynomial.aeval (σA p r s t β α ε) (τA p r s t β α ε 1) = Yy k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ := det_forms hδ
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σA p r s t β α ε) (τA p r s t β α ε 1))
      = ev (fun i => ev z (σA p r s t β α ε i)) (τA p r s t β α ε 1) from ev_aeval_gen _ z _]
  simp only [τA, σA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem τA_σA_zero (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0) :
    MvPolynomial.aeval (τA p r s t β α ε) (σA p r s t β α ε 0) = Xx k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ := det_forms hδ
  have hε0 : ε ≠ 0 := hε
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τA p r s t β α ε) (σA p r s t β α ε 0))
      = ev (fun i => ev z (τA p r s t β α ε i)) (σA p r s t β α ε 0) from ev_aeval_gen _ z _]
  simp only [τA, σA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem τA_σA_one (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0) :
    MvPolynomial.aeval (τA p r s t β α ε) (σA p r s t β α ε 1) = Yy k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ := det_forms hδ
  have hε0 : ε ≠ 0 := hε
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τA p r s t β α ε) (σA p r s t β α ε 1))
      = ev (fun i => ev z (τA p r s t β α ε i)) (σA p r s t β α ε 1) from ev_aeval_gen _ z _]
  simp only [τA, σA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem σA_comp_τA (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0) :
    (MvPolynomial.aeval (σA p r s t β α ε)).comp (MvPolynomial.aeval (τA p r s t β α ε)) =
      AlgHom.id k (R k) := by
  have h0 := σA_τA_zero p r s t β α ε hδ hε
  have h1 := σA_τA_one p r s t β α ε hδ hε
  have h : (fun i => MvPolynomial.aeval (σA p r s t β α ε) (τA p r s t β α ε i)) =
      fun i => MvPolynomial.X i := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [MvPolynomial.comp_aeval, h]
  exact MvPolynomial.aeval_X_left

theorem τA_comp_σA (p r s t β α ε : k) (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0) :
    (MvPolynomial.aeval (τA p r s t β α ε)).comp (MvPolynomial.aeval (σA p r s t β α ε)) =
      AlgHom.id k (R k) := by
  have h0 := τA_σA_zero p r s t β α ε hδ hε
  have h1 := τA_σA_one p r s t β α ε hδ hε
  have h : (fun i => MvPolynomial.aeval (τA p r s t β α ε) (σA p r s t β α ε i)) =
      fun i => MvPolynomial.X i := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [MvPolynomial.comp_aeval, h]
  exact MvPolynomial.aeval_X_left

/-- The substitution `σA` carries the hyperbola to a multiple of `f = U * V + ε`. -/
theorem σA_hyperbola {f : R k} {p r s t β α ε : k} (hε : ε ≠ 0)
    (hf : f = (lin p r + MvPolynomial.C β) * (lin s t + MvPolynomial.C α) +
      MvPolynomial.C ε) :
    MvPolynomial.aeval (σA p r s t β α ε) (hyperbola k) =
      MvPolynomial.C (-(1 / ε)) * f := by
  have hε0 : ε ≠ 0 := hε
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σA p r s t β α ε) (hyperbola k))
      = ev (fun i => ev z (σA p r s t β α ε i)) (hyperbola k) from ev_aeval_gen _ z _,
    hf]
  simp only [hyperbola, σA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

/-- The substitution `τA` carries `f = U * V + ε` to a multiple of the hyperbola. -/
theorem τA_f {f : R k} {p r s t β α ε : k} (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0)
    (hf : f = (lin p r + MvPolynomial.C β) * (lin s t + MvPolynomial.C α) +
      MvPolynomial.C ε) :
    MvPolynomial.aeval (τA p r s t β α ε) f = MvPolynomial.C (-ε) * hyperbola k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ := det_forms hδ
  have hε0 : ε ≠ 0 := hε
  have hεi : ε⁻¹ ≠ 0 := inv_ne_zero hε
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τA p r s t β α ε) f)
      = ev (fun i => ev z (τA p r s t β α ε i)) f from ev_aeval_gen _ z _, hf]
  simp only [hyperbola, τA, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **Normal form A**: if `f = U * V + ε` with `(U,V)` an invertible pair of affine linear
forms and `ε ≠ 0`, the conic `Z(f)` has the coordinate ring of the hyperbola. -/
def quotEquiv_normalA {f : R k} {p r s t β α ε : k}
    (hδ : p * t - r * s ≠ 0) (hε : ε ≠ 0)
    (hf : f = (lin p r + MvPolynomial.C β) * (lin s t + MvPolynomial.C α) +
      MvPolynomial.C ε) :
    A (alset {f}) ≃ₐ[k] A (Zset k) :=
  (quotEquivOfSubst (f := hyperbola k) (g := f)
    (u := σA p r s t β α ε 0) (v := σA p r s t β α ε 1)
    (u' := τA p r s t β α ε 0) (v' := τA p r s t β α ε 1)
    (c := -(1 / ε)) (c' := -ε)
    (σA_comp_τA p r s t β α ε hδ hε) (τA_comp_σA p r s t β α ε hδ hε)
    (σA_hyperbola hε hf) (τA_f hδ hε hf)).symm


/-! ### The second normal form: a repeated linear factor -/

/-- The substitution `x ↦ U`, `y ↦ W/α` for `f = α * U ^ 2 - W`. -/
def σB (p r d e g₀ α : k) : Fin 2 → R k :=
  ![lin p r,
    MvPolynomial.C (-(1 / α)) *
      (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k + MvPolynomial.C g₀)]

/-- Its inverse. -/
def τB (p r d e g₀ α : k) : Fin 2 → R k :=
  ![MvPolynomial.C (1 / (p * e - r * d)) *
      (MvPolynomial.C e * Xx k + MvPolynomial.C (r * α) * Yy k + MvPolynomial.C (r * g₀)),
    MvPolynomial.C (1 / (p * e - r * d)) *
      (-(MvPolynomial.C d) * Xx k - MvPolynomial.C (p * α) * Yy k -
        MvPolynomial.C (p * g₀))]

theorem σB_τB_zero (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    MvPolynomial.aeval (σB p r d e g₀ α) (τB p r d e g₀ α 0) = Xx k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ :=
    det_forms (p := p) (r := r) (s := d) (t := e) hΔ
  have hα0 : α ≠ 0 := hα
  have hαi : α⁻¹ ≠ 0 := inv_ne_zero hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σB p r d e g₀ α) (τB p r d e g₀ α 0))
      = ev (fun i => ev z (σB p r d e g₀ α i)) (τB p r d e g₀ α 0) from ev_aeval_gen _ z _]
  simp only [τB, σB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem σB_τB_one (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    MvPolynomial.aeval (σB p r d e g₀ α) (τB p r d e g₀ α 1) = Yy k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ :=
    det_forms (p := p) (r := r) (s := d) (t := e) hΔ
  have hα0 : α ≠ 0 := hα
  have hαi : α⁻¹ ≠ 0 := inv_ne_zero hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σB p r d e g₀ α) (τB p r d e g₀ α 1))
      = ev (fun i => ev z (σB p r d e g₀ α i)) (τB p r d e g₀ α 1) from ev_aeval_gen _ z _]
  simp only [τB, σB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem τB_σB_zero (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    MvPolynomial.aeval (τB p r d e g₀ α) (σB p r d e g₀ α 0) = Xx k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ :=
    det_forms (p := p) (r := r) (s := d) (t := e) hΔ
  have hα0 : α ≠ 0 := hα
  have hαi : α⁻¹ ≠ 0 := inv_ne_zero hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τB p r d e g₀ α) (σB p r d e g₀ α 0))
      = ev (fun i => ev z (τB p r d e g₀ α i)) (σB p r d e g₀ α 0) from ev_aeval_gen _ z _]
  simp only [τB, σB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem τB_σB_one (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    MvPolynomial.aeval (τB p r d e g₀ α) (σB p r d e g₀ α 1) = Yy k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ :=
    det_forms (p := p) (r := r) (s := d) (t := e) hΔ
  have hα0 : α ≠ 0 := hα
  have hαi : α⁻¹ ≠ 0 := inv_ne_zero hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τB p r d e g₀ α) (σB p r d e g₀ α 1))
      = ev (fun i => ev z (τB p r d e g₀ α i)) (σB p r d e g₀ α 1) from ev_aeval_gen _ z _]
  simp only [τB, σB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

theorem σB_comp_τB (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    (MvPolynomial.aeval (σB p r d e g₀ α)).comp (MvPolynomial.aeval (τB p r d e g₀ α)) =
      AlgHom.id k (R k) := by
  have h0 := σB_τB_zero p r d e g₀ α hΔ hα
  have h1 := σB_τB_one p r d e g₀ α hΔ hα
  have h : (fun i => MvPolynomial.aeval (σB p r d e g₀ α) (τB p r d e g₀ α i)) =
      fun i => MvPolynomial.X i := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [MvPolynomial.comp_aeval, h]
  exact MvPolynomial.aeval_X_left

theorem τB_comp_σB (p r d e g₀ α : k) (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0) :
    (MvPolynomial.aeval (τB p r d e g₀ α)).comp (MvPolynomial.aeval (σB p r d e g₀ α)) =
      AlgHom.id k (R k) := by
  have h0 := τB_σB_zero p r d e g₀ α hΔ hα
  have h1 := τB_σB_one p r d e g₀ α hΔ hα
  have h : (fun i => MvPolynomial.aeval (τB p r d e g₀ α) (σB p r d e g₀ α i)) =
      fun i => MvPolynomial.X i := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [MvPolynomial.comp_aeval, h]
  exact MvPolynomial.aeval_X_left

/-- The substitution `σB` carries the parabola to a multiple of `f = α * U ^ 2 - W`. -/
theorem σB_parabola {f : R k} {p r d e g₀ α : k} (hα : α ≠ 0)
    (hf : f = MvPolynomial.C α * (lin p r) ^ 2 +
      (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) + MvPolynomial.C g₀) :
    MvPolynomial.aeval (σB p r d e g₀ α) (parabola k) = MvPolynomial.C (-(1 / α)) * f := by
  have hα0 : α ≠ 0 := hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (σB p r d e g₀ α) (parabola k))
      = ev (fun i => ev z (σB p r d e g₀ α i)) (parabola k) from ev_aeval_gen _ z _, hf]
  simp only [parabola, Yy, Xx, σB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

/-- The substitution `τB` carries `f = α * U ^ 2 - W` to a multiple of the parabola. -/
theorem τB_f {f : R k} {p r d e g₀ α : k} (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0)
    (hf : f = MvPolynomial.C α * (lin p r) ^ 2 +
      (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) + MvPolynomial.C g₀) :
    MvPolynomial.aeval (τB p r d e g₀ α) f = MvPolynomial.C (-α) * parabola k := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h1⟩ :=
    det_forms (p := p) (r := r) (s := d) (t := e) hΔ
  have hα0 : α ≠ 0 := hα
  have hαi : α⁻¹ ≠ 0 := inv_ne_zero hα
  apply MvPolynomial.funext
  intro z
  rw [show MvPolynomial.eval z (MvPolynomial.aeval (τB p r d e g₀ α) f)
      = ev (fun i => ev z (τB p r d e g₀ α i)) f from ev_aeval_gen _ z _, hf]
  simp only [parabola, Yy, Xx, τB, Matrix.cons_val_zero, Matrix.cons_val_one, ev_lin_add, lin]
  simp
  field_simp
  ring

/-- **Normal form B**: if `f = α * U ^ 2 + L + c` with `α ≠ 0` and `L` a linear form not
proportional to `U`, the conic `Z(f)` has the coordinate ring of the parabola. -/
def quotEquiv_normalB {f : R k} {p r d e g₀ α : k} (hΔ : p * e - r * d ≠ 0) (hα : α ≠ 0)
    (hf : f = MvPolynomial.C α * (lin p r) ^ 2 +
      (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) + MvPolynomial.C g₀) :
    A (alset {f}) ≃ₐ[k] A (Yset k) :=
  (quotEquivOfSubst (f := parabola k) (g := f)
    (u := σB p r d e g₀ α 0) (v := σB p r d e g₀ α 1)
    (u' := τB p r d e g₀ α 0) (v' := τB p r d e g₀ α 1)
    (c := -(1 / α)) (c' := -α)
    (σB_comp_τB p r d e g₀ α hΔ hα) (τB_comp_σB p r d e g₀ α hΔ hα)
    (σB_parabola hα hf) (τB_f hΔ hα hf)).symm


/-! ### Factoring the quadratic part -/

/-- A polynomial vanishing at a point of the plane is not a unit. -/
theorem not_isUnit_of_ev_eq_zero {g : R k} {z : Plane k} (h : ev z g = 0) : ¬ IsUnit g := by
  intro hu
  have h2 : IsUnit (ev z g) := hu.map (ev z : R k →+* k)
  rw [h] at h2
  exact not_isUnit_zero h2

/-- A nonzero binary quadratic form over an algebraically closed field is either a product of
two linearly independent linear forms, or a nonzero multiple of the square of a linear form. -/
theorem quad_factor (a b c : k) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (∃ p r s t : k, p * t - r * s ≠ 0 ∧
      MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
        MvPolynomial.C c * Yy k ^ 2 = lin p r * lin s t) ∨
    (∃ (α p r : k), α ≠ 0 ∧ (p ≠ 0 ∨ r ≠ 0) ∧
      MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
        MvPolynomial.C c * Yy k ^ 2 = MvPolynomial.C α * (lin p r) ^ 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · rcases eq_or_ne b 0 with hb | hb
    · have ha : a ≠ 0 := by
        rcases h with h' | h' | h'
        · exact h'
        · exact absurd hb h'
        · exact absurd hc h'
      refine Or.inr ⟨a, 1, 0, ha, Or.inl one_ne_zero, ?_⟩
      rw [hb, hc]
      simp only [lin, map_one, map_zero, mul_zero, add_zero]
      ring
    · refine Or.inl ⟨1, 0, a, b, ?_, ?_⟩
      · simpa using hb
      · rw [hc]
        simp only [lin, map_one, map_zero, mul_zero, add_zero]
        ring
  · -- `c ≠ 0`: work with the monic quadratic `T ^ 2 + β T + α`, `α = a/c`, `β = b/c`
    obtain ⟨α, rfl⟩ : ∃ α, a = c * α := ⟨a / c, by field_simp⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = c * β := ⟨b / c, by field_simp⟩
    obtain ⟨ρ, hρroot⟩ := IsAlgClosed.exists_root
      (Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C α) (by
        rw [show (Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X +
          Polynomial.C α : Polynomial k).degree = 2 from by compute_degree!]
        norm_num)
    have hρ : ρ ^ 2 + β * ρ + α = 0 := by
      have h1 := hρroot
      rw [Polynomial.IsRoot.def] at h1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at h1
      linear_combination h1
    by_cases hrep : ρ = -β - ρ
    · have hβ2 : β = -(ρ + ρ) := by linear_combination hrep
      have hα2 : α = ρ * ρ := by
        rw [hβ2] at hρ
        linear_combination hρ
      refine Or.inr ⟨c, -ρ, 1, hc, Or.inr one_ne_zero, ?_⟩
      rw [hα2, hβ2, pow_two, show lin (-ρ) 1 = MvPolynomial.C (-ρ) * Xx k + MvPolynomial.C 1 * Yy k
        from rfl]
      simp only [map_one, map_mul, map_neg, map_ofNat, map_add, map_pow]
      ring
    · refine Or.inl ⟨-(c * ρ), c, -(-β - ρ), 1, ?_, ?_⟩
      · intro hzero
        apply hrep
        have h2 : c * (β + ρ + ρ) = 0 := by linear_combination (-1 : k) * hzero
        have h3 : β + ρ + ρ = 0 := mul_left_cancel₀ hc (by rw [h2, mul_zero])
        linear_combination h3
      · have hβ2 : β = -(ρ + (-β - ρ)) := by ring
        have hα2 : α = ρ * (-β - ρ) := by
          rw [hβ2] at hρ
          linear_combination hρ
        rw [hα2, hβ2]
        simp only [lin, map_one, one_mul, map_mul, map_neg, map_ofNat, map_add, map_pow, map_sub]
        ring


/-! ### Part (c) -/

/-- **Part (c), two-distinct-points-at-infinity case**: if the degree two part of `f` factors as
a product `U * V` of two *linearly independent* linear forms, then `A(W) ≃ A(Z)`.

This is the first half of the case analysis of part (c); the input is exactly the first
alternative produced by `quad_factor`. -/
theorem part_c_of_distinct (f : R k) (hirr : Irreducible f) (a b c d e g₀ : k) {p r s t : k}
    (hf : f = MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
      MvPolynomial.C c * Yy k ^ 2 + (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) +
      MvPolynomial.C g₀)
    (hdet : p * t - r * s ≠ 0)
    (hfac : MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
      MvPolynomial.C c * Yy k ^ 2 = lin p r * lin s t) :
    Nonempty (A (alset {f}) ≃ₐ[k] A (Zset k)) := by
  have hf' : f = lin p r * lin s t + (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) +
      MvPolynomial.C g₀ := by rw [hf, hfac]
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    rcases eq_or_ne p 0 with hp | hp
    · right; intro hr; exact hdet (by rw [hp, hr]; ring)
    · exact Or.inl hp
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    rcases eq_or_ne t 0 with ht | ht
    · left; intro hs; exact hdet (by rw [ht, hs]; ring)
    · exact Or.inr ht
  have hsplit : f = (lin p r + MvPolynomial.C ((p * e - r * d) / (p * t - r * s))) *
      (lin s t + MvPolynomial.C ((d * t - e * s) / (p * t - r * s))) +
      MvPolynomial.C (g₀ - ((d * t - e * s) / (p * t - r * s)) *
        ((p * e - r * d) / (p * t - r * s))) := by
    apply MvPolynomial.funext
    intro z
    rw [hf']
    simp only [lin]
    simp
    field_simp
    ring
  have hε : g₀ - ((d * t - e * s) / (p * t - r * s)) *
      ((p * e - r * d) / (p * t - r * s)) ≠ 0 := by
    intro hzero
    have hfac' : f = (lin p r + MvPolynomial.C ((p * e - r * d) / (p * t - r * s))) *
        (lin s t + MvPolynomial.C ((d * t - e * s) / (p * t - r * s))) := by
      rw [hsplit, hzero, map_zero, add_zero]
    rcases hirr.isUnit_or_isUnit hfac' with hu | hu
    · obtain ⟨z, hz⟩ := exists_ev_lin_add p r ((p * e - r * d) / (p * t - r * s)) hpr
      exact not_isUnit_of_ev_eq_zero hz hu
    · obtain ⟨z, hz⟩ := exists_ev_lin_add s t ((d * t - e * s) / (p * t - r * s)) hst
      exact not_isUnit_of_ev_eq_zero hz hu
  exact ⟨quotEquiv_normalA hdet hε hsplit⟩


/-! ### The repeated-factor case of part (c)

If the linear part of `f` is proportional to the linear form `U` of the square, then `f` is a
quadratic polynomial in `U` alone, hence reducible over an algebraically closed field. -/

/-- A linear form whose determinant with `(p,r)` vanishes is proportional to `(p,r)`. -/
theorem linear_part_proportional {p r d e : k} (hpr : p ≠ 0 ∨ r ≠ 0)
    (hΔ : p * e - r * d = 0) : ∃ lam : k, d = lam * p ∧ e = lam * r := by
  rcases eq_or_ne p 0 with hp | hp
  · have hr : r ≠ 0 := by rcases hpr with h | h; exact absurd hp h; exact h
    have hd0 : d = 0 := by
      have h : r * d = 0 := by linear_combination (-1 : k) * hΔ + e * hp
      exact (mul_eq_zero.mp h).resolve_left hr
    exact ⟨e / r, by rw [hd0, hp]; ring, by field_simp⟩
  · refine ⟨d / p, by field_simp, ?_⟩
    field_simp
    linear_combination hΔ

/-- `α * U ^ 2 + λ * U + c` is reducible over an algebraically closed field when `α ≠ 0` and
`U` is a nonzero linear form. -/
theorem reducible_of_proportional {f : R k} {α p r lam g₀ : k} (hα : α ≠ 0)
    (hpr : p ≠ 0 ∨ r ≠ 0)
    (hf : f = MvPolynomial.C α * (lin p r) ^ 2 + MvPolynomial.C lam * lin p r +
      MvPolynomial.C g₀) :
    ¬ Irreducible f := by
  obtain ⟨lam', rfl⟩ : ∃ lam', lam = α * lam' := ⟨lam / α, by field_simp⟩
  obtain ⟨g', rfl⟩ : ∃ g', g₀ = α * g' := ⟨g₀ / α, by field_simp⟩
  obtain ⟨ρ, hρroot⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 + Polynomial.C lam' * Polynomial.X + Polynomial.C g') (by
      rw [show (Polynomial.X ^ 2 + Polynomial.C lam' * Polynomial.X +
        Polynomial.C g' : Polynomial k).degree = 2 from by compute_degree!]
      norm_num)
  have hρ : ρ ^ 2 + lam' * ρ + g' = 0 := by
    have h1 := hρroot
    rw [Polynomial.IsRoot.def] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h1
    linear_combination h1
  have hαp : α * (ρ + (-lam' - ρ)) = -(α * lam') := by ring
  have hαq : α * (ρ * (-lam' - ρ)) = α * g' := by
    have h := hρ
    linear_combination (-α) * h
  have hfac : f = MvPolynomial.C α * (lin p r - MvPolynomial.C ρ) *
      (lin p r - MvPolynomial.C (-lam' - ρ)) := by
    have e1 : α * lam' = -(α * (ρ + (-lam' - ρ))) := by rw [hαp]; ring
    have e2 : α * g' = α * (ρ * (-lam' - ρ)) := hαq.symm
    apply MvPolynomial.funext
    intro z
    rw [hf]
    simp only [lin]
    simp
    rw [e1, e2]
    ring
  intro hirr
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · -- cancel the unit `C α`
    have hu1 : IsUnit ((MvPolynomial.C α : R k) * (lin p r - MvPolynomial.C ρ)) := hu
    have hu' : IsUnit (lin p r - MvPolynomial.C ρ) := by
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu1
      exact isUnit_iff_exists_inv.mpr ⟨MvPolynomial.C α * v, by rw [← hv]; ring⟩
    have h1 : lin p r - MvPolynomial.C ρ = lin p r + MvPolynomial.C (-ρ) := by
      rw [map_neg]; ring
    rw [h1] at hu'
    obtain ⟨z, hz⟩ := exists_ev_lin_add p r (-ρ) hpr
    exact not_isUnit_of_ev_eq_zero hz hu'
  · have h1 : lin p r - MvPolynomial.C (-lam' - ρ) =
        lin p r + MvPolynomial.C (-(-lam' - ρ)) := by rw [map_neg]; ring
    rw [h1] at hu
    obtain ⟨z, hz⟩ := exists_ev_lin_add p r (-(-lam' - ρ)) hpr
    exact not_isUnit_of_ev_eq_zero hz hu

/-- **Part (c), one-point-at-infinity case**: if the degree two part of `f` is a nonzero
multiple of the square of a linear form, then `A(W) ≃ A(Y)`. -/
theorem part_c_of_repeated (f : R k) (hirr : Irreducible f) (a b c d e g₀ : k) {α p r : k}
    (hf : f = MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
      MvPolynomial.C c * Yy k ^ 2 + (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) +
      MvPolynomial.C g₀)
    (hα : α ≠ 0) (hpr : p ≠ 0 ∨ r ≠ 0)
    (hfac : MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
      MvPolynomial.C c * Yy k ^ 2 = MvPolynomial.C α * (lin p r) ^ 2) :
    Nonempty (A (alset {f}) ≃ₐ[k] A (Yset k)) := by
  have hf' : f = MvPolynomial.C α * (lin p r) ^ 2 +
      (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) + MvPolynomial.C g₀ := by
    rw [hf, hfac]
  have hΔ : p * e - r * d ≠ 0 := by
    intro hΔ
    obtain ⟨lam, hd, he⟩ := linear_part_proportional hpr hΔ
    have hred : f = MvPolynomial.C α * (lin p r) ^ 2 + MvPolynomial.C lam * lin p r +
        MvPolynomial.C g₀ := by
      rw [hf', hd, he]
      simp only [lin]
      simp
      ring
    exact reducible_of_proportional hα hpr hred hirr
  exact ⟨quotEquiv_normalB hΔ hα hf'⟩

/-- **Part (c)** (Hartshorne I.1.1 (c)): the coordinate ring of a conic defined by an
irreducible quadratic polynomial is isomorphic to that of the parabola `y = x²` or to that of
the hyperbola `xy = 1`.  Which one it is is determined by the degree two part: two distinct
linear factors give `A(Z)`, a repeated factor gives `A(Y)`. -/
theorem part_c (f : R k) (hirr : Irreducible f) (a b c d e g₀ : k)
    (hf : f = MvPolynomial.C a * Xx k ^ 2 + MvPolynomial.C b * Xx k * Yy k +
      MvPolynomial.C c * Yy k ^ 2 + (MvPolynomial.C d * Xx k + MvPolynomial.C e * Yy k) +
      MvPolynomial.C g₀)
    (hq : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    Nonempty (A (alset {f}) ≃ₐ[k] A (Yset k)) ∨ Nonempty (A (alset {f}) ≃ₐ[k] A (Zset k)) := by
  rcases quad_factor a b c hq with ⟨p, r, s, t, hdet, hfac⟩ | ⟨α, p, r, hα, hpr, hfac⟩
  · exact Or.inr (part_c_of_distinct f hirr a b c d e g₀ hf hdet hfac)
  · exact Or.inl (part_c_of_repeated f hirr a b c d e g₀ hf hα hpr hfac)

end Hartshorne77.Ex_I_1_1

#print axioms Hartshorne77.Ex_I_1_1.part_a
#print axioms Hartshorne77.Ex_I_1_1.part_b
#print axioms Hartshorne77.Ex_I_1_1.quad_factor
#print axioms Hartshorne77.Ex_I_1_1.quotEquiv_normalA
#print axioms Hartshorne77.Ex_I_1_1.quotEquiv_normalB
#print axioms Hartshorne77.Ex_I_1_1.part_c_of_distinct
#print axioms Hartshorne77.Ex_I_1_1.part_c_of_repeated
#print axioms Hartshorne77.Ex_I_1_1.part_c
