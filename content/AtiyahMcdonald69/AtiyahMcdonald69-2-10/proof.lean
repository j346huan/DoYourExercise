/-
Atiyah & Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 2, Exercise 10.

Statement (verbatim from the text, p. 32):

  "Let A be a ring, 𝔞 an ideal contained in the Jacobson radical of A; let M be an
   A-module and N a finitely generated A-module, and let u : M → N be a
   homomorphism. If the induced homomorphism M/𝔞M → N/𝔞N is surjective, then u
   is surjective."

The proof given in the standard solution follows the hint structure: put
C = N/u(M), which is finitely generated; tensoring M → N → C → 0 with A/𝔞 and
using Exercise 2.2 gives an exact sequence
M/𝔞M → N/𝔞N → C/𝔞C → 0, so C = 𝔞C, and Nakayama's lemma gives C = 0.

We formalize:
* `map_smul_top_le`      : u(𝔞M) ⊆ 𝔞N,
* `inducedMap`           : the genuine induced linear map M/𝔞M → N/𝔞N,
* `inducedMap_surjective_iff` : its surjectivity, elementwise,
* `inducedMap_surjective_iff_comp_mkQ_surjective` : agreement with the phrasing
  "M → N → N/𝔞N is surjective",
* `range_sup_smul_top_eq_top` : the hypothesis as `N = u(M) + 𝔞N`,
* `exercise_2_10`        : the exercise, proved via C = N/u(M) and Nakayama,
* `smul_top_cokernel_eq_top` : the step `C = 𝔞C` of the text's proof,
* `exercise_2_10_direct` : the same, directly from Nakayama's lemma (2.5),
* `quotEquivTensor`, `tensorMap_surjective_iff_inducedMap_surjective`,
  `exercise_2_10_tensor` : Exercise 2.2 and the tensor form `u ⊗ 1`,
* `counterexample_jacobson` : the hypothesis 𝔞 ⊆ Jac(A) cannot be dropped,
* `counterexample_finite_generation` : the hypothesis "N finitely generated"
  cannot be dropped.
-/
import Mathlib

set_option autoImplicit false

open scoped TensorProduct

namespace AtiyahMcdonald69.Ex_2_10

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {N : Type*} [AddCommGroup N] [Module A N]

/-- The image of `𝔞M` under an `A`-linear map lies in `𝔞N`. -/
theorem map_smul_top_le (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    (𝔞 • ⊤ : Submodule A M).map u ≤ (𝔞 • ⊤ : Submodule A N) := by
  rw [Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_mono le_rfl le_top

/-- For an ideal `𝔞` and a linear map `u : M →ₗ[A] N`, the homomorphism
`M ⧸ 𝔞M → N ⧸ 𝔞N` induced by `u` (well defined because `u(𝔞M) ⊆ 𝔞N`). -/
noncomputable def inducedMap (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    (M ⧸ (𝔞 • ⊤ : Submodule A M)) →ₗ[A] (N ⧸ (𝔞 • ⊤ : Submodule A N)) :=
  Submodule.mapQ (p := (𝔞 • ⊤ : Submodule A M)) (q := (𝔞 • ⊤ : Submodule A N)) u
    (Submodule.map_le_iff_le_comap.mp (map_smul_top_le 𝔞 u))

@[simp]
theorem inducedMap_mk (𝔞 : Ideal A) (u : M →ₗ[A] N) (m : M) :
    inducedMap 𝔞 u (Submodule.Quotient.mk m) = Submodule.Quotient.mk (u m) := rfl

/-- Surjectivity of `M/𝔞M → N/𝔞N`, spelled out elementwise: every element of `N`
is congruent to some `u m` modulo `𝔞N`. -/
theorem inducedMap_surjective_iff (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    Function.Surjective (inducedMap 𝔞 u) ↔ ∀ n : N, ∃ m : M, n - u m ∈ (𝔞 • ⊤ : Submodule A N) := by
  constructor
  · intro hu n
    obtain ⟨x, hx⟩ := hu (Submodule.Quotient.mk (p := 𝔞 • ⊤) n)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (p := (𝔞 • ⊤ : Submodule A M)) x
    rw [inducedMap_mk, Submodule.Quotient.eq] at hx
    exact ⟨m, by simpa using Submodule.neg_mem _ hx⟩
  · rintro h y
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (p := (𝔞 • ⊤ : Submodule A N)) y
    obtain ⟨m, hm⟩ := h n
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    rw [inducedMap_mk, Submodule.Quotient.eq]
    simpa using Submodule.neg_mem _ hm

/-- The induced map `M/𝔞M → N/𝔞N` is surjective iff the composite `M → N → N/𝔞N`
is surjective; both say that every element of `N` is congruent to some `u m`
modulo `𝔞N`. -/
theorem inducedMap_surjective_iff_comp_mkQ_surjective (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    Function.Surjective (inducedMap 𝔞 u) ↔
      Function.Surjective ((𝔞 • ⊤ : Submodule A N).mkQ ∘ₗ u) := by
  constructor
  · intro hu y
    obtain ⟨x, hx⟩ := hu y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (p := (𝔞 • ⊤ : Submodule A M)) x
    exact ⟨m, by simpa using hx⟩
  · intro hu y
    obtain ⟨m, hm⟩ := hu y
    exact ⟨Submodule.Quotient.mk m, by simpa using hm⟩

/-- The hypothesis of the exercise, as an inclusion of submodules: every element
of `N` lies in `u(M) + 𝔞N`. -/
theorem range_sup_smul_top_eq_top (𝔞 : Ideal A) (u : M →ₗ[A] N)
    (hu : Function.Surjective (inducedMap 𝔞 u)) :
    (⊤ : Submodule A N) ≤ LinearMap.range u ⊔ (𝔞 • ⊤ : Submodule A N) := by
  intro n _
  obtain ⟨m, hm⟩ := (inducedMap_surjective_iff 𝔞 u).mp hu n
  have h : n = u m + (n - u m) := by abel
  rw [h]
  exact Submodule.add_mem_sup ⟨m, rfl⟩ hm

/-- **Atiyah–Macdonald, Exercise 2.10.**  Let `A` be a commutative ring, `𝔞` an
ideal contained in the Jacobson radical of `A`, `M` an arbitrary `A`-module, `N`
a finitely generated `A`-module and `u : M →ₗ[A] N`.  If the induced map
`M/𝔞M → N/𝔞N` is surjective, then `u` is surjective.

The proof is the one of the text: `C := N ⧸ u(M)` is finitely generated and the
induced map being onto forces `C = 𝔞C`; Nakayama's lemma then gives `C = 0`. -/
theorem exercise_2_10 (𝔞 : Ideal A) (h𝔞 : 𝔞 ≤ Ideal.jacobson (⊥ : Ideal A))
    (hN : Module.Finite A N) (u : M →ₗ[A] N)
    (hu : Function.Surjective (inducedMap 𝔞 u)) : Function.Surjective u := by
  classical
  -- every element of `N` lies in `u(M) + 𝔞N`
  have htop := range_sup_smul_top_eq_top 𝔞 u hu
  -- the cokernel `C = N ⧸ u(M)`, which is finitely generated
  set C := N ⧸ LinearMap.range u with hC
  have hCfin : Module.Finite A C :=
    Module.Finite.of_surjective (hM := hN) (Submodule.mkQ (LinearMap.range u))
      (Submodule.mkQ_surjective _)
  -- passing to the cokernel, `C = 𝔞C`
  have hCsmul : (⊤ : Submodule A C) ≤ (𝔞 • ⊤ : Submodule A C) := by
    have h := Submodule.map_mono (f := Submodule.mkQ (LinearMap.range u)) htop
    rw [Submodule.map_top, Submodule.range_mkQ, Submodule.map_sup, Submodule.map_smul'',
      Submodule.map_top, Submodule.mkQ_map_self] at h
    simpa using h
  -- Nakayama's lemma
  have hCbot : (⊤ : Submodule A C) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 ⊤ hCfin.fg_top hCsmul h𝔞
  have hzero : ∀ x : C, x = 0 := fun x => (Submodule.eq_bot_iff (⊤ : Submodule A C)).mp hCbot x trivial
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  intro n
  exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range u)).mp (hzero _)

/-- **Atiyah–Macdonald, Exercise 2.10**, direct form: the hypothesis is exactly
`⊤ ≤ u(M) + 𝔞N`, and Nakayama's lemma (statement (4), i.e. (2.5)) in the form
`Submodule.le_of_le_smul_of_le_jacobson_bot` finishes at once. -/
theorem exercise_2_10_direct (𝔞 : Ideal A) (h𝔞 : 𝔞 ≤ Ideal.jacobson (⊥ : Ideal A))
    (hN : Module.Finite A N) (u : M →ₗ[A] N)
    (hu : Function.Surjective (inducedMap 𝔞 u)) : Function.Surjective u := by
  rw [← LinearMap.range_eq_top]
  exact top_le_iff.mp
    (Submodule.le_of_le_smul_of_le_jacobson_bot hN.fg_top h𝔞
      (range_sup_smul_top_eq_top 𝔞 u hu))

/-! ### The cokernel form of the argument, and the tensor-product form of the hypothesis

The text's proof passes to `C = N/u(M)`, shows `C = 𝔞C` (using that tensoring with
`A/𝔞` is right exact, i.e. Exercise 2.2), and applies Nakayama.  Below we isolate the
step `C = 𝔞C`, and record the tensor-product description `M/𝔞M ≃ M ⊗[A] A/𝔞`
(Exercise 2.2) together with the fact that the induced map is `u ⊗ 1`. -/

/-- **The cokernel of `u` is `𝔞`-divisible** when `u` induces a surjection
`M/𝔞M → N/𝔞N`: this is the statement `C = 𝔞C` for `C = N ⧸ u(M)`. -/
theorem smul_top_cokernel_eq_top (𝔞 : Ideal A) (u : M →ₗ[A] N)
    (hu : Function.Surjective (inducedMap 𝔞 u)) :
    (𝔞 • ⊤ : Submodule A (N ⧸ LinearMap.range u)) = ⊤ := by
  refine le_antisymm le_top ?_
  have h := Submodule.map_mono (f := Submodule.mkQ (LinearMap.range u))
    (range_sup_smul_top_eq_top 𝔞 u hu)
  rw [Submodule.map_top, Submodule.range_mkQ, Submodule.map_sup, Submodule.map_smul'',
    Submodule.map_top, Submodule.mkQ_map_self] at h
  simpa using h

/-- **Chapter 2, Exercise 2** (used in the proof of Exercise 10): for any ideal `𝔞`
and any `A`-module `M`, `M/𝔞M ≃ M ⊗[A] (A/𝔞)`. -/
noncomputable def quotEquivTensor (𝔞 : Ideal A) :
    (M ⧸ (𝔞 • ⊤ : Submodule A M)) ≃ₗ[A] (M ⊗[A] (A ⧸ 𝔞)) :=
  (TensorProduct.tensorQuotEquivQuotSMul M 𝔞).symm

@[simp]
theorem quotEquivTensor_mk (𝔞 : Ideal A) (m : M) :
    quotEquivTensor (M := M) 𝔞 (Submodule.Quotient.mk m) = m ⊗ₜ[A] (1 : A ⧸ 𝔞) :=
  rfl

/-- Naturality of Exercise 2.2: under `M/𝔞M ≃ M ⊗ A/𝔞`, the map induced by `u`
corresponds to `u ⊗ id`. -/
theorem tensorQuotEquivQuotSMul_natural (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    ((TensorProduct.tensorQuotEquivQuotSMul N 𝔞 : _ →ₗ[A] _)).comp
        (TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞))) =
      (inducedMap 𝔞 u).comp (TensorProduct.tensorQuotEquivQuotSMul M 𝔞 : _ →ₗ[A] _) := by
  refine TensorProduct.ext' fun m x => ?_
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (p := (𝔞 : Submodule A A)) x
  simp [TensorProduct.map_tmul]

/-- The hypothesis of Exercise 10, in tensor-product form: the induced map
`M/𝔞M → N/𝔞N` is surjective iff `u ⊗ id : M ⊗ A/𝔞 → N ⊗ A/𝔞` is surjective
(right exactness of `- ⊗ A/𝔞`). -/
theorem tensorMap_surjective_iff_inducedMap_surjective (𝔞 : Ideal A) (u : M →ₗ[A] N) :
    Function.Surjective (TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞))) ↔
      Function.Surjective (inducedMap 𝔞 u) := by
  have h := tensorQuotEquivQuotSMul_natural (M := M) (N := N) 𝔞 u
  have hfun :
      (⇑(TensorProduct.tensorQuotEquivQuotSMul N 𝔞 : (N ⊗[A] (A ⧸ 𝔞)) →ₗ[A] (N ⧸ (𝔞 • ⊤)))) ∘
          (⇑(TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞)))) =
        (⇑(inducedMap 𝔞 u)) ∘
          (⇑(TensorProduct.tensorQuotEquivQuotSMul M 𝔞 :
            (M ⊗[A] (A ⧸ 𝔞)) →ₗ[A] (M ⧸ (𝔞 • ⊤)))) := by
    rw [← LinearMap.coe_comp, ← LinearMap.coe_comp, h]
  constructor
  · intro hu
    have hcomp :
        Function.Surjective
          ((⇑(TensorProduct.tensorQuotEquivQuotSMul N 𝔞)) ∘
            (⇑(TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞))))) := by
      intro y
      obtain ⟨x, hx⟩ := hu ((TensorProduct.tensorQuotEquivQuotSMul N 𝔞).symm y)
      exact ⟨x, by simp [hx]⟩
    have hcomp' :
        Function.Surjective
          ((⇑(inducedMap 𝔞 u)) ∘
            (⇑(TensorProduct.tensorQuotEquivQuotSMul M 𝔞))) := hfun ▸ hcomp
    exact Function.Surjective.of_comp hcomp'
  · intro hu
    have hcomp :
        Function.Surjective
          ((⇑(inducedMap 𝔞 u)) ∘
            (⇑(TensorProduct.tensorQuotEquivQuotSMul M 𝔞))) := by
      intro z
      obtain ⟨x, hx⟩ := hu z
      obtain ⟨w, rfl⟩ := (TensorProduct.tensorQuotEquivQuotSMul M 𝔞).surjective x
      exact ⟨w, hx⟩
    have hcomp' :
        Function.Surjective
          ((⇑(TensorProduct.tensorQuotEquivQuotSMul N 𝔞)) ∘
            (⇑(TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞))))) := hfun ▸ hcomp
    intro y
    obtain ⟨x, hx⟩ := hcomp' (TensorProduct.tensorQuotEquivQuotSMul N 𝔞 y)
    exact ⟨x, (TensorProduct.tensorQuotEquivQuotSMul N 𝔞).injective hx⟩

/-- **Atiyah–Macdonald, Exercise 2.10**, tensor-product form of the hypothesis:
if `u ⊗ id : M ⊗ A/𝔞 → N ⊗ A/𝔞` is surjective, then `u` is surjective. -/
theorem exercise_2_10_tensor (𝔞 : Ideal A) (h𝔞 : 𝔞 ≤ Ideal.jacobson (⊥ : Ideal A))
    (hN : Module.Finite A N) (u : M →ₗ[A] N)
    (hu : Function.Surjective (TensorProduct.map u (LinearMap.id : (A ⧸ 𝔞) →ₗ[A] (A ⧸ 𝔞)))) :
    Function.Surjective u :=
  exercise_2_10 𝔞 h𝔞 hN u ((tensorMap_surjective_iff_inducedMap_surjective 𝔞 u).mp hu)

/-! ### The hypothesis `𝔞 ⊆ Jac(A)` is essential -/

/-- Multiplication by `2` on `ℚ` exhibits `2 • ⊤ = ⊤`: `ℚ` is divisible. -/
theorem span_two_smul_top_rational :
    (Ideal.span {(2 : ℤ)} • ⊤ : Submodule ℤ ℚ) = ⊤ := by
  refine top_unique fun x _ => ?_
  have hx : x = (2 : ℤ) • ((2 : ℚ)⁻¹ * x) := by
    push_cast [zsmul_eq_mul]
    field_simp
  rw [hx]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 2) trivial

/-- The ideal `(2) ⊆ ℤ` is not contained in the Jacobson radical of `ℤ`
(which is `0`). -/
theorem span_two_not_le_jacobson : ¬ (Ideal.span {(2 : ℤ)} ≤ Ideal.jacobson (⊥ : Ideal ℤ)) := by
  intro h
  have h2 : (2 : ℤ) ∈ Ideal.jacobson (⊥ : Ideal ℤ) :=
    h (Ideal.mem_span_singleton_self 2)
  rw [Ideal.mem_jacobson_bot] at h2
  have hunit : IsUnit (3 : ℤ) := by simpa using h2 1
  have h31 : (3 : ℤ) ∣ 1 := hunit.dvd
  omega

/-- **The hypothesis `𝔞 ≤ Jac(A)` cannot be dropped.**  Take `A = ℤ`, `𝔞 = (2)`
(not contained in the Jacobson radical `Jac ℤ = 0`), `M = N = ℚ` and `u = 0`.
Since `ℚ` is `2`-divisible, `𝔞N = N`, so `N/𝔞N = 0` and — because also
`M/𝔞M = 0` — the induced map is surjective; but `u = 0` is not surjective. -/
theorem counterexample_jacobson :
    ¬ (Ideal.span {(2 : ℤ)} ≤ Ideal.jacobson (⊥ : Ideal ℤ)) ∧
      ∃ u : ℚ →ₗ[ℤ] ℚ,
        Function.Surjective
            (inducedMap (A := ℤ) (M := ℚ) (N := ℚ) (Ideal.span {(2 : ℤ)}) u) ∧
          ¬ Function.Surjective u := by
  refine ⟨span_two_not_le_jacobson, 0, ?_, ?_⟩
  · intro y
    have hsub : Subsingleton (ℚ ⧸ (Ideal.span {(2 : ℤ)} • ⊤ : Submodule ℤ ℚ)) := by
      rw [span_two_smul_top_rational]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨0, hsub.elim _ _⟩
  · intro h
    obtain ⟨x, hx⟩ := h 1
    simp at hx

/-! ### The hypothesis "finitely generated" is essential

Over the local ring `A = ℤ_[p]`, whose Jacobson radical is the maximal ideal `(p)`,
the `A`-module `N = ℚ_[p]` is `p`-divisible, because `p` is a unit of the fraction
field.  With `M = N` and `u = 0` the induced map `M/pM → N/pN` is a map of zero
modules, hence surjective, but `u` is not surjective.  (`N` is necessarily not
finitely generated: were it finitely generated, Nakayama's lemma — Exercise 10
itself — would force `N = 0`.) -/

section PadicCounterexample

variable {p : ℕ} [hp : Fact p.Prime]

/-- The maximal ideal `(p)` of `ℤ_[p]` is contained in its Jacobson radical. -/
theorem span_p_le_jacobson :
    (Ideal.span {(p : PadicInt p)} : Ideal (PadicInt p)) ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (PadicInt p)) bot_ne_top,
    PadicInt.maximalIdeal_eq_span_p]

/-- `ℚ_[p]` is `p`-divisible as a `ℤ_[p]`-module. -/
theorem span_p_smul_top_padic :
    (Ideal.span {(p : PadicInt p)} • ⊤ : Submodule (PadicInt p) (Padic p)) = ⊤ := by
  have hp0 : (p : Padic p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine top_unique fun x _ => ?_
  have hx : (p : PadicInt p) • ((p : Padic p)⁻¹ * x) = x := by
    rw [Algebra.smul_def, map_natCast, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  rw [← hx]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

/-- **Finite generation cannot be dropped from Exercise 2.10.**  Take the local ring
`A = ℤ_[p]`, whose Jacobson radical is the maximal ideal `(p)`, and `M = N = ℚ_[p]`
with `u = 0`.  Since `p` is a unit of the field `ℚ_[p]`, we have `𝔞N = N`, so
`N/𝔞N = 0 = M/𝔞M` and the induced map is surjective, while `u = 0` is not.  Note
that `N = ℚ_[p]` is necessarily not finitely generated: were it finitely
generated, Nakayama's lemma — Exercise 10 itself — would force `N = 0`. -/
theorem counterexample_finite_generation :
    (Ideal.span {(p : PadicInt p)} ≤ Ideal.jacobson (⊥ : Ideal (PadicInt p))) ∧
      ∃ u : Padic p →ₗ[PadicInt p] Padic p,
        Function.Surjective (inducedMap (A := PadicInt p) (M := Padic p) (N := Padic p)
          (Ideal.span {(p : PadicInt p)}) u) ∧ ¬ Function.Surjective u := by
  refine ⟨span_p_le_jacobson, 0, ?_, ?_⟩
  · intro y
    have hsub : Subsingleton (Padic p ⧸
        (Ideal.span {(p : PadicInt p)} • ⊤ : Submodule (PadicInt p) (Padic p))) := by
      rw [span_p_smul_top_padic]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨0, hsub.elim _ _⟩
  · intro h
    obtain ⟨x, hx⟩ := h 1
    simp at hx

end PadicCounterexample

end AtiyahMcdonald69.Ex_2_10

/-! ### Axiom audit

The formalization uses only Lean's / Mathlib's standard axioms. -/

#print axioms AtiyahMcdonald69.Ex_2_10.map_smul_top_le
#print axioms AtiyahMcdonald69.Ex_2_10.inducedMap_surjective_iff
#print axioms AtiyahMcdonald69.Ex_2_10.inducedMap_surjective_iff_comp_mkQ_surjective
#print axioms AtiyahMcdonald69.Ex_2_10.range_sup_smul_top_eq_top
#print axioms AtiyahMcdonald69.Ex_2_10.exercise_2_10
#print axioms AtiyahMcdonald69.Ex_2_10.exercise_2_10_direct
#print axioms AtiyahMcdonald69.Ex_2_10.smul_top_cokernel_eq_top
#print axioms AtiyahMcdonald69.Ex_2_10.quotEquivTensor
#print axioms AtiyahMcdonald69.Ex_2_10.quotEquivTensor_mk
#print axioms AtiyahMcdonald69.Ex_2_10.tensorQuotEquivQuotSMul_natural
#print axioms AtiyahMcdonald69.Ex_2_10.tensorMap_surjective_iff_inducedMap_surjective
#print axioms AtiyahMcdonald69.Ex_2_10.exercise_2_10_tensor
#print axioms AtiyahMcdonald69.Ex_2_10.counterexample_jacobson
#print axioms AtiyahMcdonald69.Ex_2_10.span_p_le_jacobson
#print axioms AtiyahMcdonald69.Ex_2_10.span_p_smul_top_padic
#print axioms AtiyahMcdonald69.Ex_2_10.counterexample_finite_generation
