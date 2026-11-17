import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Exercise I.3.3

Book statement (Chapter I, §3, p. 22):

* (a) Let `φ : X → Y` be a morphism. Then for each `P ∈ X`, `φ` induces a homomorphism
  of local rings `φ*_P : O_{φ(P),Y} → O_{P,X}`.
* (b) `φ` is an isomorphism if and only if `φ` is a homeomorphism and the induced map
  `φ*_P` on local rings is an isomorphism, for all `P ∈ X`.
* (c) If `φ(X)` is dense in `Y`, then `φ*_P` is injective for all `P ∈ X`.

This file formalizes all three parts over a field `k` (in particular over an
algebraically closed field, as in the book), in the classical language of Hartshorne
Chapter I: varieties are topological spaces equipped with a sheaf of `k`-valued regular
functions, morphisms are continuous maps pulling regular functions back to regular
functions, and the local ring `O_P` is the ring of germs of regular functions at `P`.
The framework is not vacuous: affine algebraic sets `Z ⊆ A^n` with their sheaf of regular
functions are proved to be varieties (`affineVariety`), and their regular functions are
proved continuous into `A^1` (`affReg_fibre_isClosed`).
-/

set_option linter.unusedSectionVars false

namespace Hartshorne77.Ex_I_3_3

open Set Function Filter
open scoped Topology

variable {k : Type*} [Field k]

/-- A *variety over `k`*, in the classical sense of Hartshorne Chapter I: a topological
space `X` together with the sheaf of `k`-valued regular functions on it, encoded by the
local regularity predicate `reg U f` ("`f` is regular on the open set `U`").

The fields are the standard facts about varieties used in I.3:

* `reg_const`, `reg_add`, `reg_mul`, `reg_inv` say that `O_X(U)` is a `k`-subalgebra of
  the ring of all functions `U → k` closed under inversion of nowhere-vanishing functions;
* `reg_mono`, `reg_congr`, `reg_glue` say that regularity is a local condition defining
  a subsheaf of the sheaf of all functions (Hartshorne I.3, definition of `O_X`);
* `reg_ne_zero` says the zero set of a regular function is closed (a regular function
  which is nonzero at a point is nonzero on a neighbourhood of it);
* `irreducible` records that varieties are irreducible (Hartshorne I.3, definition).

All of these are *proved* below for affine algebraic sets with their sheaf of regular
functions (see `AffineVariety`), so the theory is not vacuous. -/
class Variety (k : Type*) [Field k] (X : Type*) [TopologicalSpace X] where
  /-- `reg U f`: the total function `f : X → k` is regular on the set `U`. -/
  reg : Set X → (X → k) → Prop
  reg_const : ∀ {U : Set X}, IsOpen U → ∀ c : k, reg U (fun _ => c)
  reg_add : ∀ {U : Set X} {f g : X → k}, reg U f → reg U g → reg U (f + g)
  reg_mul : ∀ {U : Set X} {f g : X → k}, reg U f → reg U g → reg U (f * g)
  reg_inv : ∀ {U : Set X} {f : X → k}, reg U f → (∀ x ∈ U, f x ≠ 0) → reg U f⁻¹
  reg_mono : ∀ {U V : Set X} {f : X → k}, IsOpen V → V ⊆ U → reg U f → reg V f
  reg_congr : ∀ {U : Set X} {f g : X → k}, reg U f → (∀ x ∈ U, f x = g x) → reg U g
  reg_glue : ∀ {U : Set X} {f : X → k},
    (∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ reg V f) → reg U f
  reg_ne_zero : ∀ {U : Set X} {f : X → k}, reg U f → ∀ x ∈ U, f x ≠ 0 →
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, f y ≠ 0
  irreducible : IrreducibleSpace X

attribute [instance 100] Variety.irreducible

namespace Variety

variable {X : Type*} [TopologicalSpace X] [Variety k X]

theorem reg_zero {U : Set X} (hU : IsOpen U) : Variety.reg (k := k) U (0 : X → k) :=
  Variety.reg_const hU 0

theorem reg_one {U : Set X} (hU : IsOpen U) : Variety.reg (k := k) U (1 : X → k) :=
  Variety.reg_const hU 1

theorem reg_neg {U : Set X} {f : X → k} (hU : IsOpen U) (hf : Variety.reg U f) :
    Variety.reg U (-f) := by
  have h : Variety.reg U ((-1 : X → k) * f) :=
    Variety.reg_mul (Variety.reg_const hU (-1)) hf
  refine Variety.reg_congr h (fun x _ => ?_)
  simp

theorem reg_sub {U : Set X} {f g : X → k} (hU : IsOpen U) (hf : Variety.reg U f)
    (hg : Variety.reg U g) : Variety.reg U (f - g) := by
  simpa [sub_eq_add_neg] using Variety.reg_add hf (Variety.reg_neg hU hg)

/-- `f` is regular near `P`. -/
def RegAt (P : X) (f : X → k) : Prop := ∃ U : Set X, IsOpen U ∧ P ∈ U ∧ Variety.reg U f

theorem RegAt.congr {P : X} {f g : X → k} (hf : RegAt P f) (h : f = g) : RegAt P g :=
  h ▸ hf

theorem regAt_congr_near {P : X} {f g : X → k} (hf : RegAt P f)
    (h : ∀ᶠ x in 𝓝 P, f x = g x) : RegAt P g := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  obtain ⟨W, hWU, hWo, hPW⟩ := mem_nhds_iff.1 h
  exact ⟨U ∩ W, hUo.inter hWo, ⟨hPU, hPW⟩,
    Variety.reg_congr (Variety.reg_mono (hUo.inter hWo) inter_subset_left hU)
      (fun x hx => hWU hx.2)⟩

theorem regAt_add {P : X} {f g : X → k} (hf : RegAt P f) (hg : RegAt P g) :
    RegAt P (f + g) := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  obtain ⟨V, hVo, hPV, hV⟩ := hg
  exact ⟨U ∩ V, hUo.inter hVo, ⟨hPU, hPV⟩,
    Variety.reg_add (Variety.reg_mono (hUo.inter hVo) inter_subset_left hU)
      (Variety.reg_mono (hUo.inter hVo) inter_subset_right hV)⟩

theorem regAt_mul {P : X} {f g : X → k} (hf : RegAt P f) (hg : RegAt P g) :
    RegAt P (f * g) := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  obtain ⟨V, hVo, hPV, hV⟩ := hg
  exact ⟨U ∩ V, hUo.inter hVo, ⟨hPU, hPV⟩,
    Variety.reg_mul (Variety.reg_mono (hUo.inter hVo) inter_subset_left hU)
      (Variety.reg_mono (hUo.inter hVo) inter_subset_right hV)⟩

theorem regAt_zero (P : X) : RegAt (k := k) P 0 :=
  ⟨univ, isOpen_univ, mem_univ P, Variety.reg_zero isOpen_univ⟩

theorem regAt_one (P : X) : RegAt (k := k) P 1 :=
  ⟨univ, isOpen_univ, mem_univ P, Variety.reg_one isOpen_univ⟩

/-- A regular function that is nonzero at a point of its domain is nonzero on a
neighbourhood of that point: zero sets of regular functions are closed. -/
theorem eventually_ne_zero {U : Set X} {f : X → k} (hf : Variety.reg U f)
    {P : X} (hPU : P ∈ U) (hP : f P ≠ 0) : ∀ᶠ x in 𝓝 P, f x ≠ 0 := by
  obtain ⟨V, hVo, hPV, -, hV⟩ := Variety.reg_ne_zero hf P hPU hP
  exact mem_of_superset (hVo.mem_nhds hPV) hV

/-- A nowhere vanishing regular function has a regular reciprocal. -/
theorem reg_inv' {U : Set X} {f : X → k} (hf : Variety.reg U f) (h : ∀ x ∈ U, f x ≠ 0) :
    Variety.reg U (fun x => (f x)⁻¹) := by
  have := Variety.reg_inv hf h
  exact this

end Variety






/-! ## The affine model: Zariski topology and regular functions on `A^σ`

We construct the standard examples for the framework above: a subset `Z ⊆ A^σ = (σ → k)`
whose subspace Zariski topology is irreducible carries the sheaf of regular functions
"locally a quotient of polynomials with nowhere vanishing denominator" (Hartshorne I.3),
and we verify every axiom of `Variety` for it. -/

section Affine

variable {σ : Type*}

/-- The zero locus of a set of polynomials. -/
def zar (S : Set (MvPolynomial σ k)) : Set (σ → k) :=
  {x | ∀ p ∈ S, MvPolynomial.eval x p = 0}

/-- The Zariski topology on `A^σ = (σ → k)`: a set is open when it is a union of basic
open sets `D(p) = {x | p(x) ≠ 0}`, i.e. of the form `{x | ∃ p ∈ S, p(x) ≠ 0}`. -/
@[instance_reducible]
def zarTopology : TopologicalSpace (σ → k) where
  IsOpen U := ∃ S : Set (MvPolynomial σ k), U = {x | ∃ p ∈ S, MvPolynomial.eval x p ≠ 0}
  isOpen_univ := ⟨({1} : Set (MvPolynomial σ k)), by
    ext x
    exact ⟨fun _ => ⟨1, rfl, by simp⟩, fun _ => trivial⟩⟩
  isOpen_inter := by
    rintro U V ⟨S, rfl⟩ ⟨T, rfl⟩
    refine ⟨Set.image2 (· * ·) S T, ?_⟩
    ext x
    constructor
    · rintro ⟨⟨p, hp, hp0⟩, q, hq, hq0⟩
      exact ⟨p * q, ⟨p, hp, q, hq, rfl⟩, by rw [map_mul]; exact mul_ne_zero hp0 hq0⟩
    · rintro ⟨r, ⟨p, hp, q, hq, rfl⟩, hr⟩
      rw [map_mul] at hr
      exact ⟨⟨p, hp, (mul_ne_zero_iff.1 hr).1⟩, q, hq, (mul_ne_zero_iff.1 hr).2⟩
  isOpen_sUnion := by
    intro s hs
    classical
    let S : s → Set (MvPolynomial σ k) :=
      fun u => Classical.choose (hs (u : Set (σ → k)) u.2)
    have hS : ∀ u : s, (u : Set (σ → k)) = {x | ∃ p ∈ S u, MvPolynomial.eval x p ≠ 0} :=
      fun u => Classical.choose_spec (hs (u : Set (σ → k)) u.2)
    refine ⟨⋃ u : s, S u, ?_⟩
    rw [Set.sUnion_eq_iUnion]
    ext x
    constructor
    · intro hx
      simp only [mem_iUnion] at hx
      obtain ⟨u, hu⟩ := hx
      rw [hS u] at hu
      obtain ⟨p, hp, hpx⟩ := hu
      exact ⟨p, mem_iUnion.2 ⟨u, hp⟩, hpx⟩
    · rintro ⟨p, hp, hpx⟩
      simp only [mem_iUnion] at hp
      obtain ⟨u, hpu⟩ := hp
      exact mem_iUnion.2 ⟨u, by rw [hS u]; exact ⟨p, hpu, hpx⟩⟩

instance affineTop : TopologicalSpace (σ → k) := zarTopology (k := k) (σ := σ)

lemma isOpen_iff_zar {U : Set (σ → k)} :
    IsOpen U ↔ ∃ S : Set (MvPolynomial σ k), U = {x | ∃ p ∈ S, MvPolynomial.eval x p ≠ 0} :=
  Iff.rfl

lemma isOpen_eval_ne_zero (p : MvPolynomial σ k) :
    IsOpen {x : σ → k | MvPolynomial.eval x p ≠ 0} := by
  refine isOpen_iff_zar.2 ⟨{p}, ?_⟩
  ext x
  simp

lemma compl_setOf_exists (S : Set (MvPolynomial σ k)) :
    {x : σ → k | ∃ p ∈ S, MvPolynomial.eval x p ≠ 0}ᶜ = zar S := by
  ext x
  simp only [mem_compl_iff, zar]
  constructor
  · intro h p hp
    by_contra hne
    exact h ⟨p, hp, hne⟩
  · rintro h ⟨p, hp, hne⟩
    exact hne (h p hp)

lemma isClosed_iff_zar {s : Set (σ → k)} :
    IsClosed s ↔ ∃ S : Set (MvPolynomial σ k), zar S = s := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := isOpen_iff_zar.1 h.isOpen_compl
    refine ⟨S, ?_⟩
    have : s = zar S := by rw [← compl_compl s, hS, compl_setOf_exists]
    exact this.symm
  · rintro ⟨S, rfl⟩
    refine ⟨?isOpen_compl⟩
    rw [← compl_setOf_exists, compl_compl]
    exact isOpen_iff_zar.2 ⟨S, rfl⟩

lemma isClosed_zar (S : Set (MvPolynomial σ k)) : IsClosed (zar S) :=
  isClosed_iff_zar.2 ⟨S, rfl⟩

lemma exists_eval_ne_zero_of_ne_zero [Infinite k] {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  exact hp (MvPolynomial.funext (fun x => by simpa using h x))

lemma exists_open_subset {U : Set (σ → k)} (hU : IsOpen U) (x : σ → k) (hx : x ∈ U) :
    ∃ p : MvPolynomial σ k, MvPolynomial.eval x p ≠ 0 ∧
      {y : σ → k | MvPolynomial.eval y p ≠ 0} ⊆ U := by
  obtain ⟨S, rfl⟩ := isOpen_iff_zar.1 hU
  obtain ⟨p, hpS, hpx⟩ := hx
  exact ⟨p, hpx, fun _ hy => ⟨p, hpS, hy⟩⟩

instance preirreducible [Infinite k] : PreirreducibleSpace (σ → k) :=
  PreirreducibleSpace.of_forall_nonempty_inter (fun U V hU hV hUne hVne => by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy⟩ := hVne
    obtain ⟨p, hpx, hpU⟩ := exists_open_subset hU x hx
    obtain ⟨q, hqy, hqV⟩ := exists_open_subset hV y hy
    have hp0 : p ≠ 0 := fun h => hpx (by rw [h, map_zero])
    have hq0 : q ≠ 0 := fun h => hqy (by rw [h, map_zero])
    obtain ⟨z, hz⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero hp0 hq0)
    rw [map_mul] at hz
    refine ⟨z, hpU ?_, hqV ?_⟩
    · intro h
      exact hz (by rw [h, zero_mul])
    · intro h
      exact hz (by rw [h, mul_zero]))

instance irreducible [Infinite k] : IrreducibleSpace (σ → k) where
  toNonempty := ⟨fun _ => 0⟩

end Affine


/-! ## Regular functions on an affine algebraic set

For a subset `Z ⊆ A^σ`, a function `f : Z → k` is *regular* on `U ⊆ Z` when every point of
`U` has a neighbourhood inside `U` on which `f` is a quotient `p/q` of polynomials with `q`
nowhere vanishing (Hartshorne I.3).  We prove that this makes an irreducible `Z` a variety
in the sense of the class `Variety` above. -/

section Model

variable {σ : Type*}

/-- Regularity of `f` on `U ⊆ Z`, in the sense of Hartshorne I.3: locally a quotient of
polynomial functions with nowhere vanishing denominator. -/
def AffReg (Z : Set (σ → k)) (U : Set ↥Z) (f : ↥Z → k) : Prop :=
  ∀ x ∈ U, ∃ V : Set ↥Z, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ p q : MvPolynomial σ k,
    (∀ y ∈ V, MvPolynomial.eval (y : σ → k) q ≠ 0) ∧
      ∀ y ∈ V, f y * MvPolynomial.eval (y : σ → k) q = MvPolynomial.eval (y : σ → k) p

lemma affReg_mono {Z : Set (σ → k)} {U V : Set ↥Z} (hV : IsOpen V) (hVU : V ⊆ U)
    {f : ↥Z → k} (hf : AffReg Z U f) : AffReg Z V f := by
  intro x hx
  obtain ⟨W, hWo, hxW, hWU, p, q, hq, hfg⟩ := hf x (hVU hx)
  exact ⟨W ∩ V, hWo.inter hV, ⟨hxW, hx⟩, inter_subset_right, p, q,
    fun y hy => hq y hy.1, fun y hy => hfg y hy.1⟩

lemma affReg_congr {Z : Set (σ → k)} {U : Set ↥Z} {f g : ↥Z → k} (hf : AffReg Z U f)
    (h : ∀ x ∈ U, f x = g x) : AffReg Z U g := by
  intro x hx
  obtain ⟨V, hVo, hxV, hVU, p, q, hq, hfg⟩ := hf x hx
  exact ⟨V, hVo, hxV, hVU, p, q, hq, fun y hy => by rw [← h y (hVU hy), hfg y hy]⟩

/-- A regular function on `U` that is nonzero at `x ∈ U` is nonzero on a neighbourhood:
this is the closedness of zero sets, in the form used by the framework. -/
lemma affReg_ne_zero {Z : Set (σ → k)} {U : Set ↥Z} {f : ↥Z → k} (hf : AffReg Z U f)
    {x : ↥Z} (hxU : x ∈ U) (hfx : f x ≠ 0) :
    ∃ V : Set ↥Z, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, f y ≠ 0 := by
  obtain ⟨V, hVo, hxV, hVU, p, q, hq, hfg⟩ := hf x hxU
  have hopen : IsOpen {y : ↥Z | MvPolynomial.eval (y : σ → k) p ≠ 0} :=
    (isOpen_eval_ne_zero (k := k) p).preimage continuous_subtype_val
  have hxp : MvPolynomial.eval (x : σ → k) p ≠ 0 := by
    rw [← hfg x hxV]
    exact mul_ne_zero hfx (hq x hxV)
  refine ⟨V ∩ {y | MvPolynomial.eval (y : σ → k) p ≠ 0}, hVo.inter hopen,
    ⟨hxV, hxp⟩, fun y hy => hVU hy.1, ?_⟩
  rintro y ⟨hyV, hyp⟩ hzero
  exact hyp (by rw [← hfg y hyV, hzero, zero_mul])

/-- Subtracting a constant from a regular function keeps it regular. -/
lemma affReg_sub_const {Z : Set (σ → k)} {U : Set ↥Z} {f : ↥Z → k}
    (hf : AffReg Z U f) (c : k) : AffReg Z U (fun y => f y - c) := by
  intro x hxU
  obtain ⟨V, hVo, hxV, hVU, p, q, hq, hfg⟩ := hf x hxU
  refine ⟨V, hVo, hxV, hVU, p - MvPolynomial.C c * q, q, hq, ?_⟩
  intro y hy
  have h1 := hfg y hy
  rw [map_sub, map_mul, MvPolynomial.eval_C, ← h1]
  ring

/-- The variety structure on an irreducible subset `Z ⊆ A^σ` given by the sheaf of regular
functions. -/
@[instance_reducible]
def affineVariety (Z : Set (σ → k)) [IrreducibleSpace ↥Z] : Variety k ↥Z where
  reg := AffReg Z
  reg_const := by
    intro U hU c x hx
    exact ⟨U, hU, hx, subset_rfl, MvPolynomial.C c, 1,
      fun y _ => by simp, fun y _ => by simp⟩
  reg_add := by
    intro U f g hf hg x hx
    obtain ⟨V₁, hV₁o, hx₁, hV₁U, p₁, q₁, hq₁, hfg₁⟩ := hf x hx
    obtain ⟨V₂, hV₂o, hx₂, hV₂U, p₂, q₂, hq₂, hfg₂⟩ := hg x hx
    refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hx₁, hx₂⟩, fun y hy => hV₁U hy.1,
      p₁ * q₂ + p₂ * q₁, q₁ * q₂, ?_, ?_⟩
    · intro y hy
      rw [map_mul]
      exact mul_ne_zero (hq₁ y hy.1) (hq₂ y hy.2)
    · intro y hy
      have h1 := hfg₁ y hy.1
      have h2 := hfg₂ y hy.2
      simp only [Pi.add_apply, map_add, map_mul]
      rw [← h1, ← h2]
      ring
  reg_mul := by
    intro U f g hf hg x hx
    obtain ⟨V₁, hV₁o, hx₁, hV₁U, p₁, q₁, hq₁, hfg₁⟩ := hf x hx
    obtain ⟨V₂, hV₂o, hx₂, hV₂U, p₂, q₂, hq₂, hfg₂⟩ := hg x hx
    refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hx₁, hx₂⟩, fun y hy => hV₁U hy.1,
      p₁ * p₂, q₁ * q₂, ?_, ?_⟩
    · intro y hy
      rw [map_mul]
      exact mul_ne_zero (hq₁ y hy.1) (hq₂ y hy.2)
    · intro y hy
      have h1 := hfg₁ y hy.1
      have h2 := hfg₂ y hy.2
      simp only [Pi.mul_apply, map_mul]
      rw [← h1, ← h2]
      ring
  reg_inv := by
    intro U f hf hne x hx
    obtain ⟨V, hVo, hxV, hVU, p, q, hq, hfg⟩ := hf x hx
    have hp : ∀ y ∈ V, MvPolynomial.eval (y : σ → k) p ≠ 0 := by
      intro y hy
      rw [← hfg y hy]
      exact mul_ne_zero (hne y (hVU hy)) (hq y hy)
    refine ⟨V, hVo, hxV, hVU, q, p, hp, ?_⟩
    intro y hy
    have h1 := hfg y hy
    simp only [Pi.inv_apply]
    rw [← h1]
    exact inv_mul_cancel_left₀ (hne y (hVU hy)) _
  reg_mono := fun {_ _ _} hV hVU hf => affReg_mono hV hVU hf
  reg_congr := fun {_ _ _} hf h => affReg_congr hf h
  reg_glue := by
    intro U f H x hx
    obtain ⟨V, hVo, hxV, hVU, hV⟩ := H x hx
    obtain ⟨W, hWo, hxW, hWV, p, q, hq, hfg⟩ := hV x hxV
    exact ⟨W, hWo, hxW, fun y hy => hVU (hWV hy), p, q, hq, hfg⟩
  reg_ne_zero := fun hf _ hxU hfx => affReg_ne_zero hf hxU hfx
  irreducible := ‹IrreducibleSpace ↥Z›

end Model


/-! ## The local ring `O_P` of germs of regular functions

Following Hartshorne I.3, `O_P` is the ring of germs of regular functions defined near `P`,
with maximal ideal `m_P` the germs of functions vanishing at `P`.  We realize germs as
elements of `Filter.Germ (𝓝 P) k` and `O_P` as the subring of germs having a regular
representative.  -/

section Stalks

open Variety

variable {X : Type*} [TopologicalSpace X] [Variety k X]

namespace Variety

lemma RegAt.neg {P : X} {f : X → k} (hf : RegAt P f) : RegAt P (-f) := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  exact ⟨U, hUo, hPU, Variety.reg_neg hUo hU⟩

lemma RegAt.inv {P : X} {f : X → k} (hf : RegAt P f) (h : f P ≠ 0) : RegAt P f⁻¹ := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  obtain ⟨V, hVo, hPV, hVU, hV⟩ := Variety.reg_ne_zero hU P hPU h
  exact ⟨V, hVo, hPV, Variety.reg_inv (Variety.reg_mono hVo hVU hU) hV⟩

end Variety

/-- The set of germs at `P` of functions that are regular near `P`. -/
def germSet (P : X) : Set (Filter.Germ (𝓝 P) k) :=
  {g | ∃ f : X → k, RegAt P f ∧ (f : Filter.Germ (𝓝 P) k) = g}

theorem germSet_zero (P : X) : (0 : Filter.Germ (𝓝 P) k) ∈ germSet (k := k) P :=
  ⟨0, regAt_zero P, by simp⟩

theorem germSet_one (P : X) : (1 : Filter.Germ (𝓝 P) k) ∈ germSet (k := k) P :=
  ⟨1, regAt_one P, by simp⟩

theorem germSet_add {P : X} {g h : Filter.Germ (𝓝 P) k}
    (hg : g ∈ germSet (k := k) P) (hh : h ∈ germSet P) : g + h ∈ germSet P := by
  obtain ⟨f, hf, rfl⟩ := hg
  obtain ⟨f', hf', rfl⟩ := hh
  exact ⟨f + f', regAt_add hf hf', by rw [Filter.Germ.coe_add]⟩

theorem germSet_mul {P : X} {g h : Filter.Germ (𝓝 P) k}
    (hg : g ∈ germSet (k := k) P) (hh : h ∈ germSet P) : g * h ∈ germSet P := by
  obtain ⟨f, hf, rfl⟩ := hg
  obtain ⟨f', hf', rfl⟩ := hh
  exact ⟨f * f', regAt_mul hf hf', by rw [Filter.Germ.coe_mul]⟩

theorem germSet_neg {P : X} {g : Filter.Germ (𝓝 P) k} (hg : g ∈ germSet (k := k) P) :
    -g ∈ germSet P := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨-f, hf.neg, by rw [Filter.Germ.coe_neg]⟩

/-- `O_P`: the ring of germs of regular functions at `P` (Hartshorne I.3). -/
noncomputable def stalk (P : X) : Subring (Filter.Germ (𝓝 P) k) where
  carrier := germSet (k := k) P
  zero_mem' := germSet_zero P
  one_mem' := germSet_one P
  add_mem' := fun hg hh => germSet_add hg hh
  neg_mem' := fun hg => germSet_neg hg
  mul_mem' := fun hg hh => germSet_mul hg hh

/-- Evaluation of a germ of a regular function at `P`. -/
noncomputable def evalGerm (P : X) : stalk (k := k) P →+* k :=
  (Filter.Germ.valueRingHom (x := P)).comp (stalk (k := k) P).subtype

lemma evalGerm_apply (P : X) (g : stalk (k := k) P) :
    evalGerm P g = Filter.Germ.value (g : Filter.Germ (𝓝 P) k) := rfl

theorem evalGerm_surjective (P : X) : Function.Surjective (evalGerm (k := k) P) := by
  intro c
  refine ⟨⟨((fun _ : X => c) : Filter.Germ (𝓝 P) k), ?_⟩, ?_⟩
  · exact ⟨fun _ => c, ⟨univ, isOpen_univ, mem_univ P, Variety.reg_const isOpen_univ c⟩, rfl⟩
  · show Filter.Germ.value (↑(fun _ : X => c) : Filter.Germ (𝓝 P) k) = c
    rw [Filter.Germ.value_ofFun]

/-- `m_P`: the maximal ideal of `O_P`, consisting of the germs of regular functions
vanishing at `P`. -/
noncomputable def maxIdeal (P : X) : Ideal (stalk (k := k) P) :=
  RingHom.ker (evalGerm (k := k) P)

theorem maxIdeal_isMaximal (P : X) : (maxIdeal (k := k) P).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evalGerm_surjective P)

lemma mem_maxIdeal_iff {P : X} {g : stalk (k := k) P} :
    g ∈ maxIdeal P ↔
      ∃ f : X → k, RegAt P f ∧ f P = 0 ∧ (f : Filter.Germ (𝓝 P) k) = (g : Filter.Germ (𝓝 P) k) := by
  constructor
  · intro hg
    obtain ⟨germ, hgerm⟩ := g
    obtain ⟨f, hf, rfl⟩ := hgerm
    refine ⟨f, hf, ?_, rfl⟩
    have h : evalGerm P ⟨↑f, ⟨f, hf, rfl⟩⟩ = 0 := hg
    rw [evalGerm_apply] at h
    simpa using h
  · rintro ⟨f, hf, hf0, hfg⟩
    show evalGerm P g = 0
    rw [evalGerm_apply, ← hfg, Filter.Germ.value_ofFun, hf0]

/-- An element of `O_P` that does not vanish at `P` is a unit. -/
theorem isUnit_of_notMem_maxIdeal {P : X} {g : stalk (k := k) P}
    (hg : g ∉ maxIdeal P) : IsUnit g := by
  obtain ⟨germ, hgerm⟩ := g
  obtain ⟨f, hf, rfl⟩ := hgerm
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  have hval : f P ≠ 0 := by
    intro h0
    refine hg ?_
    rw [maxIdeal, RingHom.mem_ker, evalGerm_apply]
    show Filter.Germ.value (↑f : Filter.Germ (𝓝 P) k) = 0
    rw [Filter.Germ.value_ofFun, h0]
  refine IsUnit.of_mul_eq_one ⟨((f⁻¹ : X → k) : Filter.Germ (𝓝 P) k),
    ⟨f⁻¹, Variety.RegAt.inv ⟨U, hUo, hPU, hU⟩ hval, rfl⟩⟩ ?_
  apply Subtype.ext
  change (f : Filter.Germ (𝓝 P) k) * ((f⁻¹ : X → k) : Filter.Germ (𝓝 P) k) = 1
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [Variety.eventually_ne_zero hU hPU hval] with x hx
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
  exact mul_inv_cancel₀ hx

/-- `O_P` is a local ring with maximal ideal `m_P`: the maximal ideals of `O_P` are
unique, and `m_P` is one of them. -/
theorem eq_maxIdeal_of_isMaximal {P : X} {I : Ideal (stalk (k := k) P)} (hI : I.IsMaximal) :
    I = maxIdeal P := by
  refine Ideal.IsMaximal.eq_of_le hI (maxIdeal_isMaximal P).ne_top ?_
  intro x hx
  by_contra hx'
  exact hI.ne_top (I.eq_top_of_isUnit_mem hx (isUnit_of_notMem_maxIdeal hx'))

theorem existsUnique_isMaximal (P : X) :
    ∃! I : Ideal (stalk (k := k) P), I.IsMaximal :=
  ⟨maxIdeal P, maxIdeal_isMaximal P, fun _ hI => eq_maxIdeal_of_isMaximal hI⟩

instance stalk_isLocalRing (P : X) : IsLocalRing (stalk (k := k) P) :=
  IsLocalRing.of_unique_max_ideal (existsUnique_isMaximal P)

/-- The maximal ideal of the local ring `O_P` is `m_P`. -/
theorem maximalIdeal_eq (P : X) :
    IsLocalRing.maximalIdeal (stalk (k := k) P) = maxIdeal P :=
  (IsLocalRing.eq_maximalIdeal (maxIdeal_isMaximal P)).symm

end Stalks



/-! ## Morphisms and the induced maps on local rings (Hartshorne I.3.3 (a)) -/

section Morphisms

open Variety

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The pullback of a germ along a continuous map. -/
noncomputable def germPullback (φ : X → Y) (hφ : Continuous φ) (P : X) :
    Filter.Germ (𝓝 (φ P)) k → Filter.Germ (𝓝 P) k :=
  fun g => g.compTendsto φ hφ.continuousAt

lemma germPullback_coe (φ : X → Y) (hφ : Continuous φ) (P : X) (g : Y → k) :
    germPullback φ hφ P ((g : Y → k) : Filter.Germ (𝓝 (φ P)) k) =
      ((g ∘ φ : X → k) : Filter.Germ (𝓝 P) k) :=
  Filter.Germ.coe_compTendsto g hφ.continuousAt

lemma germPullback_add (φ : X → Y) (hφ : Continuous φ) (P : X)
    (g h : Filter.Germ (𝓝 (φ P)) k) :
    germPullback φ hφ P (g + h) = germPullback φ hφ P g + germPullback φ hφ P h := by
  have key : ∀ f f' : Y → k,
      germPullback φ hφ P (((f + f' : Y → k)) : Filter.Germ (𝓝 (φ P)) k) =
        germPullback φ hφ P ((f : Y → k) : Filter.Germ (𝓝 (φ P)) k) +
          germPullback φ hφ P ((f' : Y → k) : Filter.Germ (𝓝 (φ P)) k) := by
    intro f f'
    rw [germPullback_coe φ hφ P, germPullback_coe φ hφ P, germPullback_coe φ hφ P,
      ← Filter.Germ.coe_add]
    apply Filter.Germ.coe_eq.2
    filter_upwards with x
    rfl
  refine Filter.Germ.inductionOn g (fun f => ?_)
  refine Filter.Germ.inductionOn h (fun f' => ?_)
  rw [← Filter.Germ.coe_add]
  exact key f f'

lemma germPullback_mul (φ : X → Y) (hφ : Continuous φ) (P : X)
    (g h : Filter.Germ (𝓝 (φ P)) k) :
    germPullback φ hφ P (g * h) = germPullback φ hφ P g * germPullback φ hφ P h := by
  have key : ∀ f f' : Y → k,
      germPullback φ hφ P (((f * f' : Y → k)) : Filter.Germ (𝓝 (φ P)) k) =
        germPullback φ hφ P ((f : Y → k) : Filter.Germ (𝓝 (φ P)) k) *
          germPullback φ hφ P ((f' : Y → k) : Filter.Germ (𝓝 (φ P)) k) := by
    intro f f'
    rw [germPullback_coe φ hφ P, germPullback_coe φ hφ P, germPullback_coe φ hφ P,
      ← Filter.Germ.coe_mul]
    apply Filter.Germ.coe_eq.2
    filter_upwards with x
    rfl
  refine Filter.Germ.inductionOn g (fun f => ?_)
  refine Filter.Germ.inductionOn h (fun f' => ?_)
  rw [← Filter.Germ.coe_mul]
  exact key f f'

lemma germPullback_one (φ : X → Y) (hφ : Continuous φ) (P : X) :
    germPullback φ hφ P (1 : Filter.Germ (𝓝 (φ P)) k) = 1 := by
  have h1 : (1 : Filter.Germ (𝓝 (φ P)) k) = ((fun _ : Y => (1 : k)) : Filter.Germ (𝓝 (φ P)) k) :=
    Filter.Germ.coe_one.symm
  rw [h1, germPullback_coe]
  exact Filter.Germ.coe_one

lemma germPullback_zero (φ : X → Y) (hφ : Continuous φ) (P : X) :
    germPullback φ hφ P (0 : Filter.Germ (𝓝 (φ P)) k) = 0 := by
  have h0 : (0 : Filter.Germ (𝓝 (φ P)) k) = ((fun _ : Y => (0 : k)) : Filter.Germ (𝓝 (φ P)) k) :=
    Filter.Germ.coe_zero.symm
  rw [h0, germPullback_coe]
  exact Filter.Germ.coe_zero

end Morphisms

section MorphismsVariety

open Variety

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Variety k X] [Variety k Y]

/-- A morphism of varieties (Hartshorne I.3): a continuous map `φ : X → Y` such that for
every open `U ⊆ Y` and every regular function `f` on `U`, the composite `f ∘ φ` is regular
on `φ⁻¹(U)`. -/
def IsMorphism (φ : X → Y) : Prop :=
  Continuous φ ∧ ∀ (U : Set Y), IsOpen U → ∀ f : Y → k,
    Variety.reg U f → Variety.reg (φ ⁻¹' U) (f ∘ φ)

/-- Composition of germs with a morphism, as a ring homomorphism. -/
noncomputable def germMap (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) :
    Filter.Germ (𝓝 (φ P)) k →+* Filter.Germ (𝓝 P) k where
  toFun := germPullback φ hφ.1 P
  map_one' := germPullback_one φ hφ.1 P
  map_mul' := fun g h => germPullback_mul φ hφ.1 P g h
  map_zero' := germPullback_zero φ hφ.1 P
  map_add' := fun g h => germPullback_add φ hφ.1 P g h

lemma germMap_coe (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) (g : Y → k) :
    germMap φ hφ P ((g : Y → k) : Filter.Germ (𝓝 (φ P)) k) =
      ((g ∘ φ : X → k) : Filter.Germ (𝓝 P) k) :=
  germPullback_coe φ hφ.1 P g

lemma germMap_mem (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) {g : Filter.Germ (𝓝 (φ P)) k}
    (hg : g ∈ germSet (k := k) (φ P)) : germMap φ hφ P g ∈ germSet (k := k) P := by
  obtain ⟨f, hf, rfl⟩ := hg
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  refine ⟨f ∘ φ, ⟨φ ⁻¹' U, hUo.preimage hφ.1, hPU, hφ.2 U hUo f hU⟩, ?_⟩
  show ((f ∘ φ : X → k) : Filter.Germ (𝓝 P) k) = germMap φ hφ P ↑f
  exact (germMap_coe φ hφ P f).symm

/-- `φ*_P : O_{φ(P)} → O_P`, the homomorphism of local rings induced by a morphism `φ`
(Hartshorne I.3.3 (a)). -/
noncomputable def stalkMap (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) :
    stalk (k := k) (φ P) →+* stalk (k := k) P where
  toFun g := ⟨germMap φ hφ P (g : Filter.Germ (𝓝 (φ P)) k), germMap_mem φ hφ P g.2⟩
  map_one' := Subtype.ext (by
    change germMap φ hφ P (1 : Filter.Germ (𝓝 (φ P)) k) = 1
    exact map_one (germMap φ hφ P))
  map_mul' := fun g h => Subtype.ext (by
    change germMap φ hφ P ((g : Filter.Germ (𝓝 (φ P)) k) * (h : Filter.Germ (𝓝 (φ P)) k)) =
      germMap φ hφ P g * germMap φ hφ P h
    exact map_mul (germMap φ hφ P) _ _)
  map_zero' := Subtype.ext (by
    change germMap φ hφ P (0 : Filter.Germ (𝓝 (φ P)) k) = 0
    exact map_zero (germMap φ hφ P))
  map_add' := fun g h => Subtype.ext (by
    change germMap φ hφ P ((g : Filter.Germ (𝓝 (φ P)) k) + (h : Filter.Germ (𝓝 (φ P)) k)) =
      germMap φ hφ P g + germMap φ hφ P h
    exact map_add (germMap φ hφ P) _ _)

lemma stalkMap_coe (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) (g : stalk (k := k) (φ P)) :
    ((stalkMap φ hφ P g : stalk (k := k) P) : Filter.Germ (𝓝 P) k) =
      germMap φ hφ P (g : Filter.Germ (𝓝 (φ P)) k) := rfl

/-- The constant function `c` as an element of `O_P`. -/
noncomputable def constStalk (P : X) (c : k) : stalk (k := k) P :=
  ⟨((fun _ : X => c) : Filter.Germ (𝓝 P) k), fun _ => c,
    ⟨univ, isOpen_univ, mem_univ P, Variety.reg_const isOpen_univ c⟩, rfl⟩

lemma stalkMap_const (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) (c : k) :
    stalkMap φ hφ P (constStalk (k := k) (φ P) c) = constStalk (k := k) P c := by
  apply Subtype.ext
  show germMap φ hφ P ((fun _ : Y => c) : Filter.Germ (𝓝 (φ P)) k) =
    ((fun _ : X => c) : Filter.Germ (𝓝 P) k)
  rw [germMap_coe]
  rfl

/-- Part (a) of Hartshorne I.3.3: `φ*_P` is a local homomorphism, i.e. it carries the
maximal ideal `m_{φ(P)}` of `O_{φ(P)}` into the maximal ideal `m_P` of `O_P`. -/
theorem stalkMap_mem_maxIdeal (φ : X → Y) (hφ : IsMorphism (k := k) φ) (P : X) :
    ∀ g ∈ maxIdeal (k := k) (φ P), stalkMap φ hφ P g ∈ maxIdeal (k := k) P := by
  intro g hg
  obtain ⟨f, hf, hf0, hfg⟩ := mem_maxIdeal_iff.1 hg
  rw [mem_maxIdeal_iff]
  refine ⟨f ∘ φ, ?_, hf0, ?_⟩
  · obtain ⟨U, hUo, hPU, hU⟩ := hf
    exact ⟨φ ⁻¹' U, hUo.preimage hφ.1, hPU, hφ.2 U hUo f hU⟩
  · show ((f ∘ φ : X → k) : Filter.Germ (𝓝 P) k) =
      ((stalkMap φ hφ P g : stalk (k := k) P) : Filter.Germ (𝓝 P) k)
    rw [stalkMap_coe, ← hfg, germMap_coe]

end MorphismsVariety


/-! ## Isolation of the pullback on germs, and Hartshorne I.3.3 (b) and (c) -/

section MainTheorems

open Variety

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Variety k X] [Variety k Y]

lemma IsMorphism.regAt {φ : X → Y} (hφ : IsMorphism (k := k) φ) {P : X} {f : Y → k}
    (hf : RegAt (k := k) (φ P) f) : RegAt (k := k) P (f ∘ φ) := by
  obtain ⟨U, hUo, hPU, hU⟩ := hf
  exact ⟨φ ⁻¹' U, hUo.preimage hφ.1, hPU, hφ.2 U hUo f hU⟩

/-- The germ at `P` of a function regular near `P`, as an element of `O_P`. -/
noncomputable def germAt (P : X) (f : X → k) (hf : RegAt (k := k) P f) :
    stalk (k := k) P :=
  ⟨((f : X → k) : Filter.Germ (𝓝 P) k), f, hf, rfl⟩

lemma germAt_coe (P : X) (f : X → k) (hf : RegAt (k := k) P f) :
    ((germAt P f hf : stalk (k := k) P) : Filter.Germ (𝓝 P) k) =
      ((f : X → k) : Filter.Germ (𝓝 P) k) := rfl

lemma stalkMap_germAt {φ : X → Y} (hφ : IsMorphism (k := k) φ) (P : X) {f : Y → k}
    (hf : RegAt (k := k) (φ P) f) :
    stalkMap φ hφ P (germAt (k := k) (φ P) f hf) =
      germAt (k := k) P (f ∘ φ) (hφ.regAt hf) := by
  apply Subtype.ext
  show germMap φ hφ P ((f : Y → k) : Filter.Germ (𝓝 (φ P)) k) =
    ((f ∘ φ : X → k) : Filter.Germ (𝓝 P) k)
  rw [germMap_coe]

/-- Part (b), `⇒`: an isomorphism of varieties is a homeomorphism. -/
theorem homeomorph_of_isIso {φ : X → Y} (hφ : IsMorphism (k := k) φ)
    (h : ∃ ψ : Y → X, IsMorphism (k := k) ψ ∧ (∀ y, φ (ψ y) = y) ∧ (∀ x, ψ (φ x) = x)) :
    ∃ e : X ≃ₜ Y, ⇑e = φ := by
  obtain ⟨ψ, hψ, hright, hleft⟩ := h
  let e₀ : X ≃ Y := { toFun := φ, invFun := ψ, left_inv := hleft, right_inv := hright }
  exact ⟨{ toEquiv := e₀, continuous_toFun := hφ.1, continuous_invFun := hψ.1 }, rfl⟩

/-- Part (b), `⇒`: the induced map on local rings is injective (its inverse is `ψ*`). -/
theorem stalkMap_injective_of_isIso {φ : X → Y} (hφ : IsMorphism (k := k) φ)
    {ψ : Y → X} (hψ : IsMorphism (k := k) ψ) (hleft : ∀ x, ψ (φ x) = x)
    (hright : ∀ y, φ (ψ y) = y) (P : X) :
    Function.Injective (stalkMap φ hφ P) := by
  intro g h hgh
  obtain ⟨germ₁, hgerm₁⟩ := g
  obtain ⟨germ₂, hgerm₂⟩ := h
  obtain ⟨f, hf, rfl⟩ := hgerm₁
  obtain ⟨f', hf', rfl⟩ := hgerm₂
  have key : ((f ∘ φ : X → k) : Filter.Germ (𝓝 P) k) =
      ((f' ∘ φ : X → k) : Filter.Germ (𝓝 P) k) := by
    have h2 := congrArg (fun x : stalk (k := k) P => (x : Filter.Germ (𝓝 P) k)) hgh
    rw [stalkMap_coe, germMap_coe, stalkMap_coe, germMap_coe] at h2
    exact h2
  obtain ⟨W, hWsub, hWo, hPW⟩ := mem_nhds_iff.1 (Filter.Germ.coe_eq.1 key)
  apply Subtype.ext
  show ((f : Y → k) : Filter.Germ (𝓝 (φ P)) k) = ((f' : Y → k) : Filter.Germ (𝓝 (φ P)) k)
  apply Filter.Germ.coe_eq.2
  refine mem_of_superset ((hWo.preimage hψ.1).mem_nhds ?_) ?_
  · simpa [hleft P] using hPW
  · intro y hy
    have h1 : f (φ (ψ y)) = f' (φ (ψ y)) := hWsub hy
    rwa [hright y] at h1

/-- Part (b), `⇒`: the induced map on local rings is surjective. -/
theorem stalkMap_surjective_of_isIso {φ : X → Y} (hφ : IsMorphism (k := k) φ)
    {ψ : Y → X} (hψ : IsMorphism (k := k) ψ) (hleft : ∀ x, ψ (φ x) = x) (P : X) :
    Function.Surjective (stalkMap φ hφ P) := by
  intro h
  obtain ⟨germ, hgerm⟩ := h
  obtain ⟨f, hf, rfl⟩ := hgerm
  refine ⟨germAt (k := k) (φ P) (f ∘ ψ) (hψ.regAt ?_), ?_⟩
  · simpa [hleft P] using hf
  · rw [stalkMap_germAt]
    apply Subtype.ext
    show ((f ∘ ψ ∘ φ : X → k) : Filter.Germ (𝓝 P) k) = ((f : X → k) : Filter.Germ (𝓝 P) k)
    rw [Filter.Germ.coe_eq]
    filter_upwards with x
    simp only [Function.comp_apply, hleft x]

/-- Part (b), `⇐`: if `φ` is a homeomorphism whose induced maps on local rings are
surjective, then `φ⁻¹` is again a morphism, so `φ` is an isomorphism of varieties. -/
theorem isMorphism_symm (φ : X → Y) (hφ : IsMorphism (k := k) φ) (e : X ≃ₜ Y)
    (he : ⇑e = φ) (hsurj : ∀ P : X, Function.Surjective (stalkMap φ hφ P)) :
    IsMorphism (k := k) e.symm := by
  subst he
  constructor
  · exact e.continuous_invFun
  · intro U hUo f hUf
    refine Variety.reg_glue (fun y hy => ?_)
    obtain ⟨g, hg⟩ := hsurj (e.symm y) (germAt (k := k) (e.symm y) f ⟨U, hUo, hy, hUf⟩)
    obtain ⟨germ, hgerm⟩ := g
    obtain ⟨g₀, hg₀, rfl⟩ := hgerm
    have hgg : ((g₀ ∘ ⇑e : X → k) : Filter.Germ (𝓝 (e.symm y)) k) =
        ((f : X → k) : Filter.Germ (𝓝 (e.symm y)) k) := by
      have h2 := congrArg
        (fun x : stalk (k := k) (e.symm y) => (x : Filter.Germ (𝓝 (e.symm y)) k)) hg
      rw [stalkMap_coe, germMap_coe] at h2
      exact h2
    obtain ⟨W, hWsub, hWo, hPW⟩ := mem_nhds_iff.1 (Filter.Germ.coe_eq.1 hgg)
    have hgy : RegAt (k := k) y g₀ := by simpa using hg₀
    obtain ⟨W', hW'o, hyW', hW'⟩ := hgy
    have hpre : e.symm ⁻¹' (W ∩ U) ∈ 𝓝 y :=
      (hWo.inter hUo).preimage e.continuous_invFun |>.mem_nhds ⟨hPW, hy⟩
    obtain ⟨O, hOsub, hOo, hyO⟩ := mem_nhds_iff.1 hpre
    refine ⟨W' ∩ O, hW'o.inter hOo, ⟨hyW', hyO⟩, ?_, ?_⟩
    · intro z hz
      exact (hOsub hz.2).2
    · refine Variety.reg_congr (Variety.reg_mono (hW'o.inter hOo) inter_subset_left hW') ?_
      intro z hz
      have h1 : g₀ (⇑e (e.symm z)) = f (e.symm z) := hWsub (hOsub hz.2).1
      rwa [e.apply_symm_apply] at h1

/-- **Hartshorne I.3.3 (b)**: a morphism of varieties is an isomorphism if and only if it
is a homeomorphism and the induced maps `φ*_P` on local rings are isomorphisms for all
`P ∈ X`. -/
theorem isIso_iff_homeomorph_and_stalkMap_bijective (φ : X → Y) (hφ : IsMorphism (k := k) φ) :
    (∃ ψ : Y → X, IsMorphism (k := k) ψ ∧ (∀ y, φ (ψ y) = y) ∧ (∀ x, ψ (φ x) = x)) ↔
      (∃ e : X ≃ₜ Y, ⇑e = φ) ∧ ∀ P : X, Function.Bijective (stalkMap φ hφ P) := by
  constructor
  · rintro ⟨ψ, hψ, hright, hleft⟩
    exact ⟨homeomorph_of_isIso hφ ⟨ψ, hψ, hright, hleft⟩,
      fun P => ⟨stalkMap_injective_of_isIso hφ hψ hleft hright P,
        stalkMap_surjective_of_isIso hφ hψ hleft P⟩⟩
  · rintro ⟨⟨e, rfl⟩, hbij⟩
    refine ⟨e.symm, isMorphism_symm _ hφ e rfl (fun P => (hbij P).2),
      fun y => e.apply_symm_apply y, fun x => e.symm_apply_apply x⟩

/-- The kernel of `φ*_P` is trivial when `φ(X)` is dense in `Y`: a regular function on a
neighbourhood of `φ(P)` whose pullback vanishes near `P` vanishes on its whole domain. -/
theorem stalkMap_eq_zero_of_denseRange {φ : X → Y} (hφ : IsMorphism (k := k) φ)
    (hd : DenseRange φ) {P : X} {g : stalk (k := k) (φ P)}
    (hg : stalkMap φ hφ P g = 0) : g = 0 := by
  obtain ⟨germ, hgerm⟩ := g
  obtain ⟨f, hf, rfl⟩ := hgerm
  have hzero : ((f ∘ φ : X → k) : Filter.Germ (𝓝 P) k) = ((0 : X → k) : Filter.Germ (𝓝 P) k) := by
    have h2 := congrArg (fun x : stalk (k := k) P => (x : Filter.Germ (𝓝 P) k)) hg
    rw [stalkMap_coe, germMap_coe] at h2
    simpa using h2
  obtain ⟨U, hUsub, hUo, hPU⟩ := mem_nhds_iff.1 (Filter.Germ.coe_eq.1 hzero)
  have hzeroU : ∀ x ∈ U, f (φ x) = 0 := by
    intro x hx
    simpa using hUsub hx
  obtain ⟨W, hWo, hWP, hW⟩ := hf
  have hdense : Dense (φ '' U) := by
    rw [dense_iff_closure_eq]
    have hsub : range φ ⊆ closure (φ '' U) := by
      have himg : φ '' closure U ⊆ closure (φ '' U) := image_closure_subset_closure_image hφ.1
      rw [(hUo.dense ⟨P, hPU⟩).closure_eq, image_univ] at himg
      exact himg
    have h1 : closure (range φ) ⊆ closure (φ '' U) := closure_minimal hsub isClosed_closure
    rw [hd.closure_eq] at h1
    exact eq_top_iff.2 h1
  have hzeroW : ∀ y ∈ W, f y = 0 := by
    intro y hyW
    by_contra hfy
    obtain ⟨V, hVo, hyV, hVW, hVne⟩ := Variety.reg_ne_zero hW y hyW hfy
    have hy : y ∈ closure (φ '' U) := by rw [hdense.closure_eq]; trivial
    rw [mem_closure_iff] at hy
    obtain ⟨z, hzV, hzφU⟩ := hy V hVo hyV
    obtain ⟨x, hxU, rfl⟩ := hzφU
    exact hVne (φ x) hzV (hzeroU x hxU)
  apply Subtype.ext
  show ((f : Y → k) : Filter.Germ (𝓝 (φ P)) k) = (0 : Filter.Germ (𝓝 (φ P)) k)
  rw [← Filter.Germ.coe_zero]
  apply Filter.Germ.coe_eq.2
  exact mem_of_superset (hWo.mem_nhds hWP) hzeroW

/-- **Hartshorne I.3.3 (c)**: if `φ(X)` is dense in `Y`, then `φ*_P` is injective for every
`P ∈ X`. -/
theorem stalkMap_injective_of_denseRange (φ : X → Y) (hφ : IsMorphism (k := k) φ)
    (hd : DenseRange φ) (P : X) : Function.Injective (stalkMap φ hφ P) := by
  intro g h hgh
  have hsub : stalkMap φ hφ P (g - h) = 0 := by
    rw [map_sub, hgh, sub_self]
  have hzero : g - h = 0 := stalkMap_eq_zero_of_denseRange hφ hd hsub
  exact sub_eq_zero.1 hzero

end MainTheorems


/-! ## Regular functions on an affine algebraic set are continuous

Every fibre of a regular function is closed, i.e. a regular function is continuous as a map
into `A^1 = k` (whose closed subsets are the finite sets). This is the classical
"zero sets of regular functions are closed" property, and is the property isolated as
`Variety.reg_ne_zero` in the framework above. -/

section Continuity

open Variety

variable {σ : Type*} {Z : Set (σ → k)}

theorem affReg_fibre_isClosed [IrreducibleSpace ↥Z] {U : Set ↥Z}
    {f : ↥Z → k} (hf : AffReg Z U f) (c : k) :
    IsClosed {x : ↥U | f (x : ↥Z) = c} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨x, hxU⟩ hx
  have hxc : f x ≠ c := by simpa using hx
  obtain ⟨W, hWo, hxW, hWU, hWne⟩ :=
    affReg_ne_zero (affReg_sub_const hf c) hxU (by simpa [sub_eq_zero] using hxc)
  refine ⟨{y : ↥U | (y : ↥Z) ∈ W}, ?_, hWo.preimage continuous_subtype_val, hxW⟩
  intro y hy
  have hy' : f (y : ↥Z) - c ≠ 0 := hWne (y : ↥Z) hy
  simpa [sub_eq_zero] using hy'

end Continuity

/-! ## The standard example: affine space is a variety, and morphisms between affine spaces

This shows that the framework above is non-vacuous: `A^σ = (σ → k)` with its sheaf of
regular functions is a variety in the sense of `Variety`, so the theorems (a), (b), (c)
apply to it. -/

section Examples

open Variety

variable {σ : Type*} [Infinite k]

instance : IrreducibleSpace ↥(univ : Set (σ → k)) :=
  isIrreducible_iff_irreducibleSpace.mp (IrreducibleSpace.isIrreducible_univ (σ → k))

/-- Affine space `A^σ` is a variety over `k`. -/
instance : Variety k ↥(univ : Set (σ → k)) := affineVariety univ

/-- The identity map of `A^σ` is a morphism of varieties. -/
theorem isMorphism_id :
    IsMorphism (k := k) (id : ↥(univ : Set (σ → k)) → ↥(univ : Set (σ → k))) :=
  ⟨continuous_id, fun U _ _ hf => by simpa using hf⟩

/-- The identity map of `A^σ` is an isomorphism of varieties. -/
theorem isIso_id :
    ∃ ψ : ↥(univ : Set (σ → k)) → ↥(univ : Set (σ → k)),
      IsMorphism (k := k) ψ ∧ (∀ y : ↥(univ : Set (σ → k)), id (ψ y) = y) ∧
        (∀ x : ↥(univ : Set (σ → k)), ψ (id x) = x) :=
  ⟨id, isMorphism_id, fun _ => rfl, fun _ => rfl⟩

/-- Part (b) applied to the identity: its induced maps on local rings are bijective. -/
example (P : ↥(univ : Set (σ → k))) :
    Function.Bijective (stalkMap (k := k) id isMorphism_id P) :=
  ((isIso_iff_homeomorph_and_stalkMap_bijective id isMorphism_id).1 isIso_id).2 P

/-- Part (c) applied to the identity: it has dense image, so its induced maps on local
rings are injective. -/
example (P : ↥(univ : Set (σ → k))) :
    Function.Injective (stalkMap (k := k) id isMorphism_id P) :=
  stalkMap_injective_of_denseRange id isMorphism_id
    (by simp [DenseRange]) P

/-- A constant map of affine spaces is a morphism of varieties. -/
theorem isMorphism_const (a : ↥(univ : Set (σ → k))) :
    IsMorphism (k := k) (fun _ : ↥(univ : Set (σ → k)) => a) := by
  constructor
  · exact continuous_const
  · intro U _ f _
    have hpre : IsOpen ((fun _ : ↥(univ : Set (σ → k)) => a) ⁻¹' U) := by
      by_cases h : a ∈ U
      · have h1 : (fun _ : ↥(univ : Set (σ → k)) => a) ⁻¹' U = univ := by
          ext x
          simp [h]
        rw [h1]
        exact isOpen_univ
      · have h1 : (fun _ : ↥(univ : Set (σ → k)) => a) ⁻¹' U = ∅ := by
          ext x
          simp [h]
        rw [h1]
        exact isOpen_empty
    exact Variety.reg_const hpre (f a)

instance pointIrreducible (a : σ → k) : IrreducibleSpace ↥({a} : Set (σ → k)) :=
  isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton

/-- A point of affine space, with the subspace topology, is a variety over `k`. -/
instance pointVariety (a : σ → k) : Variety k ↥({a} : Set (σ → k)) :=
  affineVariety {a}

/-- A point of affine space is irreducible, so it is a variety. -/
example (a : σ → k) : IsIrreducible ({a} : Set (σ → k)) := isIrreducible_singleton

end Examples

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_3_3.stalkMap_mem_maxIdeal
#print axioms Hartshorne77.Ex_I_3_3.existsUnique_isMaximal
#print axioms Hartshorne77.Ex_I_3_3.maximalIdeal_eq
#print axioms Hartshorne77.Ex_I_3_3.isIso_iff_homeomorph_and_stalkMap_bijective
#print axioms Hartshorne77.Ex_I_3_3.stalkMap_injective_of_denseRange
#print axioms Hartshorne77.Ex_I_3_3.isMorphism_const
#print axioms Hartshorne77.Ex_I_3_3.stalkMap_surjective_of_isIso
#print axioms Hartshorne77.Ex_I_3_3.isMorphism_symm
#print axioms Hartshorne77.Ex_I_3_3.affineVariety
#print axioms Hartshorne77.Ex_I_3_3.affReg_fibre_isClosed

end Hartshorne77.Ex_I_3_3
