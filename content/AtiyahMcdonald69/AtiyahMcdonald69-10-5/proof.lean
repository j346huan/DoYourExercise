import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Filtration

/-!
# Atiyah–Macdonald (1969), Exercise 10.5 — full formalization

**Original exercise** (Chapter 10, *Completions*, p. 114). "Let `A` be a Noetherian ring and let
`a`, `b` be ideals in `A`. If `M` is any `A`-module, let `M^a`, `M^b` denote its `a`-adic and
`b`-adic completions respectively. If `M` is finitely generated, prove that
`(M^a)^b ≅ M^(a+b)`."

**Formal statement proved here** (Mathlib's `AdicCompletion I M = lim_n M ⧸ I^n • ⊤`, and
`I ⊔ J` is the ideal sum `a + b`): for `R` Noetherian, `I J : Ideal R` and `M` a finite
`R`-module, there is a linear equivalence of `R`-modules

`AtiyahMcdonald69.Ex_10_5.solution :
  AdicCompletion J (AdicCompletion I M) ≃ₗ[R] AdicCompletion (I ⊔ J) M`.

Both maps are given explicitly on the components `m : ℕ` (for the `J`-adic direction) and
`n : ℕ` (for the `I`-adic one); the content of the exercise is the comparison of the two limits,
whose index categories are `ℕ` and `ℕ × ℕ`.

## Structure of the proof

1. **A–M Proposition 10.13 in sharp form** (`quotientAdicEquiv`): for every ideal `L`,
   `M^I ⧸ L • ⊤ ≃ₗ AdicCompletion I (M ⧸ L • ⊤)`, i.e. the closure of the image of `L·M` in `M^I`
   is exactly `L • M^I`.  This is obtained by transporting the trivial tensor identity
   `range (A ⊗_R L • ⊤ → A ⊗_R M) = L • ⊤` (for an `R`-algebra `A`, here `A = R^I`) along
   `R^I ⊗_R M ≅ M^I`; this is where Noetherian + finite generation are used.
2. **The double-limit comparison.**  For `m n : ℕ` put
   `compP(m,n) : M^(I+J) → M ⧸ (I^n + J^m)`, `x ↦ x_{m+n}`, and similarly
   `compQ(m,n) : (M^I)^J → M ⧸ (I^n + J^m)`, obtained from step 1 applied to `J^m`, the `n`-th
   component of the inner completion, and the third isomorphism theorem
   `(M ⧸ J^m M) ⧸ I^n(M ⧸ J^m M) ≅ M ⧸ (I^n + J^m) M` (`qq`).  These families are compatible in
   both indices (`compP_compat`, `compQ_compat`), using
   `(I ⊔ J)^{m+n} ⊆ I^m ⊔ J^n ⊆ (I ⊔ J)^{min m n}` (`Ideal.sup_pow_add_le_pow_sup_pow`).
3. **The two maps.**  `Φ : (M^I)^J → M^(I+J)` (`Phi`) has `k`-th component `compQ(k,k)` pushed
   forward along `I^k + J^k ⊆ (I+J)^k`; `Ψ : M^(I+J) → (M^I)^J` (`Psi`) has `m`-th component given
   by the compatible family `n ↦ compP(m,n)` of `lim_n M/(I^n + J^m)`, transported back across
   step 1 (`Lm`, `Lm_nat`).
4. **The round trips** are proved componentwise (`Phi_Psi`, `Psi_Phi`), using the diagonal
   estimates `(I+J)^{k+k} ⊆ I^k + J^k ⊆ (I+J)^k`.

Note that the naive map `M → M^I` is *not* `(I+J)`-adically continuous in general
(`(I+J)^k ⊄ I^k + J^k`: for `R = k[x,y]`, `I = (x)`, `J = (y)` one has `xy ∉ (x², y²)`), which is
why the comparison has to be made through the double limit rather than by an abstract universal
property.

**Adaptation**: `R` and `M` are required to live in the same universe (a limitation of
`AdicCompletion.map_exact` in Mathlib, which puts all three modules in the universe of `R`); the
mathematical statement is universe-free.  `AdicCompletion` is Mathlib's inverse limit
`lim_n M ⧸ I^n • ⊤` and `I ⊔ J` is the ideal sum, matching `a + b`.  The constructions
`quotientAdicEquiv`, `tensor_map_range_subtype_smul` and `range_map_subtype_smul` (A–M 10.13 with
an arbitrary ideal `L`) were developed in a previous partial attempt
(`.ultramath/smwi64e55/m15/answer.lean`); they were re-verified here by compilation, and the
double-limit comparison (steps 2–4) is new.
-/


namespace AtiyahMcdonald69.Ex_10_5

open Submodule TensorProduct

universe u

/-! ### Maps out of an adic completion -/

section LiftOut

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {T : Type u} [AddCommGroup T] [Module R T]

/-- A linear map `g : M →ₗ T` which vanishes on `I ^ n • ⊤` induces a linear map
`AdicCompletion I M →ₗ T`, namely `g` on representatives of the `n`-th approximation. -/
noncomputable def liftOut (n : ℕ) (g : M →ₗ[R] T) (h : I ^ n • ⊤ ≤ LinearMap.ker g) :
    AdicCompletion I M →ₗ[R] T :=
  (Submodule.liftQ (I ^ n • ⊤) g h) ∘ₗ AdicCompletion.eval I M n

@[simp]
theorem liftOut_of (n : ℕ) (g : M →ₗ[R] T) (h : I ^ n • ⊤ ≤ LinearMap.ker g) (x : M) :
    liftOut I n g h (AdicCompletion.of I M x) = g x := by
  simp [liftOut]

/-- The canonical map `M → AdicCompletion I M` carries `I ^ n • ⊤` into `I ^ n • ⊤`. -/
theorem of_mem_pow_smul_top {n : ℕ} {x : M} (hx : x ∈ I ^ n • (⊤ : Submodule R M)) :
    AdicCompletion.of I M x ∈ (I ^ n • (⊤ : Submodule R (AdicCompletion I M))) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Uniqueness of maps out of an adic completion: two maps which both vanish on `I ^ n • ⊤` and
agree on the image of `of` coincide (here `I` is finitely generated). -/
theorem liftOut_ext {n : ℕ} (hI : I.FG) {h₁ h₂ : AdicCompletion I M →ₗ[R] T}
    (k₁ : I ^ n • ⊤ ≤ LinearMap.ker h₁) (k₂ : I ^ n • ⊤ ≤ LinearMap.ker h₂)
    (H : ∀ x, h₁ (AdicCompletion.of I M x) = h₂ (AdicCompletion.of I M x)) : h₁ = h₂ := by
  have hle₁ : LinearMap.ker (AdicCompletion.eval I M n) ≤ LinearMap.ker h₁ := by
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := M) (n := n) hI]
    exact k₁
  have hle₂ : LinearMap.ker (AdicCompletion.eval I M n) ≤ LinearMap.ker h₂ := by
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := M) (n := n) hI]
    exact k₂
  refine LinearMap.ext fun u => ?_
  obtain ⟨y, hy⟩ : ∃ y : M, Submodule.mkQ (I ^ n • ⊤ : Submodule R M) y
      = AdicCompletion.eval I M n u := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R M)
    (AdicCompletion.eval I M n u)
  have key : ∀ {h : AdicCompletion I M →ₗ[R] T}, LinearMap.ker (AdicCompletion.eval I M n) ≤
      LinearMap.ker h → h u = h (AdicCompletion.of I M y) := by
    intro h hh
    have hmem : u - AdicCompletion.of I M y ∈ LinearMap.ker (AdicCompletion.eval I M n) := by
      rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, ← hy, sub_self]
    have hu : u = AdicCompletion.of I M y + (u - AdicCompletion.of I M y) := by abel
    rw [hu, map_add, LinearMap.mem_ker.mp (hh hmem), add_zero]
  rw [key hle₁, key hle₂]
  exact H y

end LiftOut

/-! ### The tensor product description of `L • ⊤` in a completed tensor product -/

section TensorRange

variable {R : Type u} [CommRing R] (L : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {A : Type u} [CommRing A] [Algebra R A]

/-- The image of `A ⊗ ↥(L • ⊤) → A ⊗ M` is `L • ⊤`. -/
theorem tensor_map_range_subtype_smul :
    LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
        (Submodule.subtype (L • (⊤ : Submodule R M)))) =
      L • (⊤ : Submodule R (A ⊗[R] M)) := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply]
        change a ⊗ₜ[R] (y : M) ∈ L • (⊤ : Submodule R (A ⊗[R] M))
        refine Submodule.smul_induction_on y.2 ?_ ?_
        · intro r hr m _
          rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · intro u v hu hv
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hu hv
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr n _
      let g : M →ₗ[R] ↥(L • (⊤ : Submodule R M)) :=
        (LinearMap.lsmul R M r).codRestrict _ (fun m => by
          simpa using Submodule.smul_mem_smul hr
            (Submodule.mem_top : m ∈ (⊤ : Submodule R M)))
      have hcomp : (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
            (Submodule.subtype (L • (⊤ : Submodule R M)))) ∘ₗ
          TensorProduct.map (LinearMap.id : A →ₗ[R] A) g = r • LinearMap.id := by
        refine LinearMap.ext fun n => ?_
        induction n using TensorProduct.induction_on with
        | zero => simp
        | tmul a m =>
            simp [g, TensorProduct.map_tmul, TensorProduct.tmul_smul]
        | add x y hx hy =>
            simp only [map_add, hx, hy]
      refine ⟨TensorProduct.map (LinearMap.id : A →ₗ[R] A) g n, ?_⟩
      have := LinearMap.congr_fun hcomp n
      simpa using this
    · intro u v hu hv
      obtain ⟨u', hu'⟩ := hu
      obtain ⟨v', hv'⟩ := hv
      exact ⟨u' + v', by rw [map_add, hu', hv']⟩

end TensorRange

/-- A submodule of a finite module over a Noetherian ring is finite. -/
theorem moduleFinite_submodule {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (S : Submodule R M) :
    Module.Finite R ↥S := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian S)

/-! ### A–M (10.13): `AdicCompletion I M ⧸ (L • ⊤) ≅ AdicCompletion I (M ⧸ L • ⊤)` -/

/-- The range of the completion of the inclusion `L • ⊤ → M` is `L • ⊤` inside `M^I`. -/
theorem range_map_subtype_smul {R : Type u} [CommRing R] (I L : Ideal R)
    {M : Type u} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    (LinearMap.range (AdicCompletion.map I
        (Submodule.subtype (L • (⊤ : Submodule R M))))).restrictScalars R =
      L • (⊤ : Submodule R (AdicCompletion I M)) := by
  have hN : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  have hfin : Module.Finite R ↥(L • (⊤ : Submodule R M) : Submodule R M) :=
    (Module.Finite.iff_fg (N := (L • (⊤ : Submodule R M) : Submodule R M))).mpr
      (IsNoetherian.noetherian (L • (⊤ : Submodule R M) : Submodule R M))
  have hnat : ∀ z : AdicCompletion I R ⊗[R] ↥(L • (⊤ : Submodule R M) : Submodule R M),
      AdicCompletion.map I (Submodule.subtype (L • (⊤ : Submodule R M)))
          (AdicCompletion.ofTensorProduct I ↥(L • (⊤ : Submodule R M)) z)
        = AdicCompletion.ofTensorProduct I M
            (TensorProduct.map (LinearMap.id : AdicCompletion I R →ₗ[R] AdicCompletion I R)
              (Submodule.subtype (L • (⊤ : Submodule R M))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of,
          AdicCompletion.ofTensorProduct_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsurj : Function.Surjective
      (AdicCompletion.ofTensorProduct I ↥(L • (⊤ : Submodule R M))) :=
    AdicCompletion.ofTensorProduct_surjective_of_finite I _
  have hsurjM : Function.Surjective (AdicCompletion.ofTensorProduct I M) :=
    AdicCompletion.ofTensorProduct_surjective_of_finite I M
  have hT : ∀ t : AdicCompletion I R ⊗[R] ↥(L • (⊤ : Submodule R M) : Submodule R M),
      TensorProduct.map (LinearMap.id : AdicCompletion I R →ₗ[R] AdicCompletion I R)
        (Submodule.subtype (L • (⊤ : Submodule R M))) t
        ∈ L • (⊤ : Submodule R (AdicCompletion I R ⊗[R] M)) := by
    intro t
    rw [← tensor_map_range_subtype_smul (A := AdicCompletion I R) L]
    exact ⟨t, rfl⟩
  have key : (LinearMap.range (AdicCompletion.map I
        (Submodule.subtype (L • (⊤ : Submodule R M))))).restrictScalars R
      = Submodule.map ((AdicCompletion.ofTensorProduct I M).restrictScalars R)
          (L • (⊤ : Submodule R (AdicCompletion I R ⊗[R] M))) := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨u, rfl⟩
      obtain ⟨t, rfl⟩ := hsurj u
      rw [hnat]
      exact Submodule.mem_map_of_mem (hT t)
    · rintro z ⟨y, hy, rfl⟩
      have hyr : y ∈ LinearMap.range (TensorProduct.map
          (LinearMap.id : AdicCompletion I R →ₗ[R] AdicCompletion I R)
          (Submodule.subtype (L • (⊤ : Submodule R M)))) := by
        rwa [tensor_map_range_subtype_smul (A := AdicCompletion I R) L]
      obtain ⟨t, rfl⟩ := hyr
      exact ⟨AdicCompletion.ofTensorProduct I ↥(L • (⊤ : Submodule R M)) t, hnat t⟩
  have hmap : Submodule.map ((AdicCompletion.ofTensorProduct I M).restrictScalars R)
      (L • (⊤ : Submodule R (AdicCompletion I R ⊗[R] M))) =
      L • (⊤ : Submodule R (AdicCompletion I M)) := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr m _
        rw [map_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    · intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr m _
        obtain ⟨t, ht⟩ := hsurjM m
        refine Submodule.mem_map.mpr ⟨r • t, ?_, ?_⟩
        · exact Submodule.smul_mem_smul hr
            (Submodule.mem_top : t ∈ (⊤ : Submodule R (AdicCompletion I R ⊗[R] M)))
        · rw [map_smul]
          congr 1
      · intro x y hx hy
        obtain ⟨x', hx'S, hx'⟩ := Submodule.mem_map.mp hx
        obtain ⟨y', hy'S, hy'⟩ := Submodule.mem_map.mp hy
        exact Submodule.mem_map.mpr ⟨x' + y', Submodule.add_mem _ hx'S hy'S,
          by rw [map_add, hx', hy']⟩
  rw [key, hmap]


/-- **A–M (10.13)**, quotient form: for a Noetherian ring, a finite module `M` and any ideal `L`,
the quotient of the `I`-adic completion of `M` by `L • ⊤` is the `I`-adic completion of
`M ⧸ L • ⊤`. -/
noncomputable def quotientAdicEquiv {R : Type u} [CommRing R] (I L : Ideal R)
    {M : Type u} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    (AdicCompletion I M ⧸ (L • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      AdicCompletion I (M ⧸ (L • (⊤ : Submodule R M))) := by
  have hex : Function.Exact
      ⇑(AdicCompletion.map I (Submodule.subtype (L • (⊤ : Submodule R M))))
      ⇑(AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M)))) :=
    AdicCompletion.map_exact (I := I) (Submodule.subtype_injective _)
      (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  have hA0 : LinearMap.ker (AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M))))
      = LinearMap.range (AdicCompletion.map I
          (Submodule.subtype (L • (⊤ : Submodule R M)))) :=
    LinearMap.exact_iff.mp hex
  have hmem : ∀ y : AdicCompletion I M,
      (y ∈ LinearMap.ker (AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M)))))
        ↔ y ∈ L • (⊤ : Submodule R (AdicCompletion I M)) := by
    intro y
    have h1 : y ∈ LinearMap.range (AdicCompletion.map I
        (Submodule.subtype (L • (⊤ : Submodule R M))))
        ↔ y ∈ (LinearMap.range (AdicCompletion.map I
          (Submodule.subtype (L • (⊤ : Submodule R M))))).restrictScalars R := Iff.rfl
    rw [hA0, h1, range_map_subtype_smul I L]
  have hker : LinearMap.ker
      ((AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M)))).restrictScalars R)
      = L • (⊤ : Submodule R (AdicCompletion I M)) := by
    refine SetLike.ext fun y => ?_
    rw [LinearMap.mem_ker, ← hmem y, LinearMap.mem_ker]
    exact Iff.rfl
  have hsurj : Function.Surjective
      ((AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M)))).restrictScalars R) :=
    AdicCompletion.map_surjective _ (Submodule.mkQ_surjective _)
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)


section Main



set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable (I J : Ideal R)
lemma sup_pow_le_pow_sup (k : ℕ) : I ^ k ⊔ J ^ k ≤ (I ⊔ J) ^ k :=
  sup_le (Ideal.pow_right_mono le_sup_left k) (Ideal.pow_right_mono le_sup_right k)

/-- `(I ⊔ J) ^ (m + n) ≤ I ^ m ⊔ J ^ n`. -/
lemma pow_sup_le (m n : ℕ) : (I ⊔ J) ^ (m + n) ≤ I ^ m ⊔ J ^ n :=
  Ideal.sup_pow_add_le_pow_sup_pow (n := m) (m := n)

/-- The image of `I • ⊤` under a quotient map is `I • ⊤` of the quotient. -/
lemma map_smul_top_mkQ (K : Ideal R) (S : Submodule R M) :
    (K • (⊤ : Submodule R M)).map S.mkQ = (K • (⊤ : Submodule R (M ⧸ S))) := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

/-- `Submodule.factor` only depends on the two submodules, not on the proof of the inclusion. -/
lemma factor_congr {p p' : Submodule R M} (h₁ h₂ : p ≤ p') :
    Submodule.factor h₁ = Submodule.factor h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- The canonical quotient map `M ⧸ K • ⊤ → M ⧸ L • ⊤` for `K ≤ L`. -/
noncomputable def qmap {K L : Ideal R} (h : K ≤ L) :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R] M ⧸ (L • (⊤ : Submodule R M)) :=
  Submodule.factor (Submodule.smul_mono_left h)

lemma qmap_apply {K L : Ideal R} (h : K ≤ L) (x : M) :
    qmap h (Submodule.mkQ (K • (⊤ : Submodule R M)) x) =
      Submodule.mkQ (L • (⊤ : Submodule R M)) x :=
  Submodule.factor_mk (Submodule.smul_mono_left h) x

lemma qmap_apply_mk {K L : Ideal R} (h : K ≤ L) (x : M) :
    qmap (M := M) h (Submodule.Quotient.mk (p := K • (⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := L • (⊤ : Submodule R M)) x :=
  Submodule.factor_mk (Submodule.smul_mono_left h) x

lemma qmap_comp {K L N' : Ideal R} (h₁ : K ≤ L) (h₂ : L ≤ N') :
    qmap (M := M) (le_trans h₁ h₂) = (qmap h₂).comp (qmap h₁) := by
  rw [qmap, qmap, qmap, Submodule.factor_comp]

/-- The canonical comparison map between the `(m,n)`-components. -/
lemma qmap_comp_mkQ {K L : Ideal R} (h : K ≤ L) :
    (qmap (M := M) h).comp (Submodule.mkQ (K • (⊤ : Submodule R M))) =
      Submodule.mkQ (L • (⊤ : Submodule R M)) :=
  Submodule.factor_comp_mk (Submodule.smul_mono_left h)

/-- `quotientAdicEquiv` is natural in the ideal. -/
lemma qmap_qmap {K L N' : Ideal R} (h₁ : K ≤ L) (h₂ : L ≤ N')
    (y : M ⧸ (K • (⊤ : Submodule R M))) :
    qmap (M := M) h₂ (qmap (M := M) h₁ y) = qmap (M := M) (le_trans h₁ h₂) y := by
  rw [← LinearMap.comp_apply, ← qmap_comp (M := M) h₁ h₂]

lemma qmap_congr {K L : Ideal R} (h₁ h₂ : K ≤ L) (y : M ⧸ (K • (⊤ : Submodule R M))) :
    qmap (M := M) h₁ y = qmap (M := M) h₂ y := by
  induction y using Submodule.Quotient.induction_on with
  | H y => simp only [qmap_apply_mk]

lemma qmap_congr_lm {K L : Ideal R} (h₁ h₂ : K ≤ L) :
    qmap (M := M) h₁ = qmap (M := M) h₂ :=
  LinearMap.ext fun y => qmap_congr h₁ h₂ y

noncomputable def tmap {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    M ⧸ ((I ^ n' ⊔ J ^ m') • (⊤ : Submodule R M)) →ₗ[R]
      M ⧸ ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) :=
  qmap (M := M) (sup_le_sup (Ideal.pow_le_pow_right (I := I) hn) (Ideal.pow_le_pow_right (I := J) hm))

lemma tmap_eq {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    tmap (R := R) (M := M) I J hm hn = Submodule.factor (R := R) (M := M)
      (Submodule.smul_mono_left (sup_le_sup (Ideal.pow_le_pow_right (I := I) hn)
        (Ideal.pow_le_pow_right (I := J) hm))) := rfl

lemma tmap_apply_mk {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') (x : M) :
    tmap (R := R) (M := M) I J hm hn
        (Submodule.Quotient.mk (p := ((I ^ n' ⊔ J ^ m') • (⊤ : Submodule R M))) x)
      = Submodule.Quotient.mk (p := ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M))) x :=
  Submodule.factor_mk (Submodule.smul_mono_left
    (sup_le_sup (Ideal.pow_le_pow_right (I := I) hn) (Ideal.pow_le_pow_right (I := J) hm))) x

lemma tmap_comp {m₀ m₁ m₂ n₀ n₁ n₂ : ℕ} (h₁ : m₀ ≤ m₁) (h₁' : n₀ ≤ n₁)
    (h₂ : m₁ ≤ m₂) (h₂' : n₁ ≤ n₂) :
    tmap (R := R) (M := M) I J (le_trans h₁ h₂) (le_trans h₁' h₂') =
      (tmap (R := R) (M := M) I J h₁ h₁').comp (tmap (R := R) (M := M) I J h₂ h₂') := by
  refine LinearMap.ext fun y => ?_
  induction y using Submodule.Quotient.induction_on with
  | H y => simp only [LinearMap.comp_apply, tmap_apply_mk]

/-- The defining property of `quotientAdicEquiv` on classes. -/
lemma transitionMap_apply_mk {K : Ideal R} {k k' : ℕ} (h : k ≤ k') (N : Type u)
    [AddCommGroup N] [Module R N] (y : N) :
    AdicCompletion.transitionMap K N h
        (Submodule.Quotient.mk (p := K ^ k' • (⊤ : Submodule R N)) y) =
      Submodule.Quotient.mk (p := K ^ k • (⊤ : Submodule R N)) y :=
  Submodule.factor_mk _ y

/-! ### Naturality of `qq` -/

/-- Naturality of `qq` in the second variable. -/
lemma transitionMap_eq_qmap (K : Ideal R) {k k' : ℕ} (h : k ≤ k') :
    AdicCompletion.transitionMap K M h =
      qmap (M := M) (Ideal.pow_le_pow_right (I := K) h) := rfl

lemma eval_eq_transitionMap {K : Ideal R} {k k' : ℕ} (h : k ≤ k') (x : AdicCompletion K M) :
    AdicCompletion.eval K M k x = AdicCompletion.transitionMap K M h (AdicCompletion.eval K M k' x) := by
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply,
    AdicCompletion.transitionMap_comp_eval_apply (I := K) (M := M) h x]

noncomputable def qq (m n : ℕ) :
    ((M ⧸ (J ^ m • (⊤ : Submodule R M))) ⧸
        (I ^ n • (⊤ : Submodule R (M ⧸ (J ^ m • (⊤ : Submodule R M)))))) ≃ₗ[R]
      M ⧸ ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq
      (I ^ n • (⊤ : Submodule R (M ⧸ (J ^ m • (⊤ : Submodule R M)))))
      ((I ^ n • (⊤ : Submodule R M)).map (Submodule.mkQ (J ^ m • (⊤ : Submodule R M))))
      (map_smul_top_mkQ (I ^ n) (J ^ m • (⊤ : Submodule R M))).symm).trans <|
    (Submodule.quotientQuotientEquivQuotientSup
      (J ^ m • (⊤ : Submodule R M)) (I ^ n • (⊤ : Submodule R M))).trans <|
      Submodule.quotEquivOfEq
        ((J ^ m • (⊤ : Submodule R M)) ⊔ (I ^ n • (⊤ : Submodule R M)))
        ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M))
        (by rw [sup_comm, ← Submodule.sup_smul])

lemma qq_apply_mkQ (m n : ℕ) (x : M) :
    qq (R := R) (M := M) I J m n
        (Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R (M ⧸ (J ^ m • (⊤ : Submodule R M)))))
          (Submodule.Quotient.mk (p := J ^ m • (⊤ : Submodule R M)) x)) =
      Submodule.Quotient.mk (p := (I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) x := by
  simp only [qq, LinearEquiv.trans_apply]
  rfl

lemma qq_symm_apply_mkQ (m n : ℕ) (x : M) :
    (qq (R := R) (M := M) I J m n).symm
        (Submodule.Quotient.mk (p := (I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R (M ⧸ (J ^ m • (⊤ : Submodule R M)))))
        (Submodule.Quotient.mk (p := J ^ m • (⊤ : Submodule R M)) x) := by
  rw [LinearEquiv.symm_apply_eq, qq_apply_mkQ]

lemma qq_nat_n {m n n' : ℕ} (hn : n ≤ n')
    (u : (M ⧸ (J ^ m • (⊤ : Submodule R M))) ⧸
      (I ^ n' • (⊤ : Submodule R (M ⧸ (J ^ m • (⊤ : Submodule R M)))))) :
    tmap (R := R) (M := M) I J (le_refl m) hn (qq (R := R) (M := M) I J m n' u) =
      qq (R := R) (M := M) I J m n
        (AdicCompletion.transitionMap I (M ⧸ (J ^ m • (⊤ : Submodule R M))) hn u) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction u using Submodule.Quotient.induction_on with
    | H x =>
      rw [qq_apply_mkQ, tmap_apply_mk, transitionMap_apply_mk, qq_apply_mkQ]

/-- Naturality of `qq` in the first variable. -/
lemma qq_nat_m {m m' n : ℕ} (hm : m ≤ m')
    (u : (M ⧸ (J ^ m' • (⊤ : Submodule R M))) ⧸
      (I ^ n • (⊤ : Submodule R (M ⧸ (J ^ m' • (⊤ : Submodule R M)))))) :
    tmap (R := R) (M := M) I J hm (le_refl n) (qq (R := R) (M := M) I J m' n u) =
      qq (R := R) (M := M) I J m n
        ((qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm)).reduceModIdeal (I ^ n) u) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction u using Submodule.Quotient.induction_on with
    | H x =>
      rw [qq_apply_mkQ, tmap_apply_mk, LinearMap.reduceModIdeal_apply, qmap_apply_mk,
        qq_apply_mkQ]

/-! ### The component maps -/

/-- The `(m,n)`-th component of an element of `M^(I+J)`, in `M ⧸ (I^n + J^m)`. -/
noncomputable def compP (m n : ℕ) :
    AdicCompletion (I ⊔ J) M →ₗ[R] M ⧸ ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) :=
  qmap (M := M) (by rw [Nat.add_comm]; exact pow_sup_le I J n m) ∘ₗ
    AdicCompletion.eval (I ⊔ J) M (m + n)

/-- The `(m,n)`-th component of an element of `(M^I)^J`, in `M ⧸ (I^n + J^m)`. -/
lemma compP_compat {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    (tmap (R := R) (M := M) I J hm hn).comp (compP (R := R) (M := M) I J m' n') =
      compP (R := R) (M := M) I J m n := by
  have hle : m + n ≤ m' + n' := by lia
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, compP, tmap]
  rw [eval_eq_transitionMap hle x, transitionMap_eq_qmap]
  rw [qmap_qmap, qmap_qmap]


/-! ### Naturality of `quotientAdicEquiv` in the ideal -/

noncomputable def Lm (m : ℕ) :
    AdicCompletion (I ⊔ J) M →ₗ[R] AdicCompletion I (M ⧸ (J ^ m • (⊤ : Submodule R M))) :=
  AdicCompletion.lift I
    (fun n => (qq (R := R) (M := M) I J m n).symm.toLinearMap ∘ₗ
      compP (R := R) (M := M) I J m n) (by
    intro n n' hnn'
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    refine (LinearEquiv.eq_symm_apply (e := qq (R := R) (M := M) I J m n)).mpr ?_
    rw [← qq_nat_n (I := I) (J := J) hnn' _]
    erw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (compP_compat (I := I) (J := J) (le_refl m) hnn') x)

lemma eval_Lm (m n : ℕ) (x : AdicCompletion (I ⊔ J) M) :
    AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n (Lm I J m x) =
      (qq (R := R) (M := M) I J m n).symm (compP (R := R) (M := M) I J m n x) :=
  rfl

lemma map_eval {K : Ideal R} {N N' : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] {g : N →ₗ[R] N'} (n : ℕ) (z : AdicCompletion K N) :
    AdicCompletion.eval K N' n (AdicCompletion.map K g z) =
      g.reduceModIdeal (K ^ n) (AdicCompletion.eval K N n z) := rfl

/-- The maps `Lm` are compatible in `m`. -/
lemma Lm_nat {m m' : ℕ} (hm : m ≤ m') (x : AdicCompletion (I ⊔ J) M) :
    AdicCompletion.map I (qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm)) (Lm I J m' x) =
      Lm I J m x := by
  refine AdicCompletion.ext fun n => ?_
  show AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
      (AdicCompletion.map I (qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm)) (Lm I J m' x)) =
    AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n (Lm I J m x)
  rw [map_eval, eval_Lm, eval_Lm]
  refine (LinearEquiv.eq_symm_apply (e := qq (R := R) (M := M) I J m n)).mpr ?_
  rw [← qq_nat_m (I := I) (J := J) hm _]
  erw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (compP_compat (I := I) (J := J) hm (le_refl n)) x

/-! ### Compatibility of the `compQ` components -/

end Main

section Main2

set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]
variable (I J : Ideal R)
lemma quotientAdicEquiv_mkQ (L : Ideal R) (y : AdicCompletion I M) :
    quotientAdicEquiv (M := M) I L
        (Submodule.Quotient.mk (p := L • (⊤ : Submodule R (AdicCompletion I M))) y) =
      AdicCompletion.map I (Submodule.mkQ (L • (⊤ : Submodule R M))) y := rfl

/-! ### The double quotient -/

/-- `(M ⧸ J^m M) ⧸ I^n (M ⧸ J^m M) ≃ M ⧸ (I^n + J^m) M`. -/
noncomputable def compQ (m n : ℕ) :
    AdicCompletion J (AdicCompletion I M) →ₗ[R]
      M ⧸ ((I ^ n ⊔ J ^ m) • (⊤ : Submodule R M)) :=
  (qq (R := R) (M := M) I J m n).toLinearMap ∘ₗ
    (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n) ∘ₗ
      (quotientAdicEquiv I (J ^ m)).toLinearMap ∘ₗ
        (AdicCompletion.eval J (AdicCompletion I M) m)

lemma quotientAdicEquiv_nat {m m' : ℕ} (hm : m ≤ m')
    (u : AdicCompletion I M ⧸ (J ^ m' • (⊤ : Submodule R (AdicCompletion I M)))) :
    AdicCompletion.map I (qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm))
        (quotientAdicEquiv (M := M) I (J ^ m') u) =
      quotientAdicEquiv (M := M) I (J ^ m)
        (qmap (M := AdicCompletion I M) (Ideal.pow_le_pow_right (I := J) hm) u) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    rw [qmap_apply_mk, quotientAdicEquiv_mkQ (M := M), AdicCompletion.map_comp_apply,
      qmap_comp_mkQ, quotientAdicEquiv_mkQ (M := M)]

lemma quotientAdicEquiv_nat_symm {m m' : ℕ} (hm : m ≤ m')
    (z : AdicCompletion I (M ⧸ (J ^ m' • (⊤ : Submodule R M)))) :
    qmap (M := AdicCompletion I M) (Ideal.pow_le_pow_right (I := J) hm)
        ((quotientAdicEquiv (M := M) I (J ^ m')).symm z) =
      (quotientAdicEquiv (M := M) I (J ^ m)).symm
        (AdicCompletion.map I (qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm)) z) := by
  refine (LinearEquiv.eq_symm_apply (e := quotientAdicEquiv (M := M) I (J ^ m))).mpr ?_
  rw [← quotientAdicEquiv_nat (I := I) (J := J) hm
      ((quotientAdicEquiv (M := M) I (J ^ m')).symm z),
    LinearEquiv.apply_symm_apply]

/-! ### The map `M^(I+J) → lim_m lim_n M/(I^n + J^m)` -/

/-- Compatibility of the `qq` components in the second index, in the shape of `compQ`. -/
lemma tmap_qq_nat_n {m n n' : ℕ} (hn : n ≤ n') (z : AdicCompletion I (M ⧸ (J ^ m • (⊤ : Submodule R M)))) :
    tmap (R := R) (M := M) I J (le_refl m) hn
        (qq (R := R) (M := M) I J m n'
          (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n' z)) =
      qq (R := R) (M := M) I J m n
        (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n z) := by
  rw [qq_nat_n (I := I) (J := J) hn, eval_eq_transitionMap (K := I) hn]

/-- Compatibility of the `qq` components in the first index, in the shape of `compQ`. -/
lemma tmap_qq_nat_m {m m' n : ℕ} (hm : m ≤ m') (z : AdicCompletion I (M ⧸ (J ^ m' • (⊤ : Submodule R M)))) :
    tmap (R := R) (M := M) I J hm (le_refl n)
        (qq (R := R) (M := M) I J m' n
          (AdicCompletion.eval I (M ⧸ (J ^ m' • (⊤ : Submodule R M))) n z)) =
      qq (R := R) (M := M) I J m n
        (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
          (AdicCompletion.map I (qmap (M := M) (Ideal.pow_le_pow_right (I := J) hm)) z)) := by
  rw [qq_nat_m (I := I) (J := J) hm, map_eval]

lemma compQ_compat {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    (tmap (R := R) (M := M) I J hm hn).comp (compQ (R := R) (M := M) I J m' n') =
      compQ (R := R) (M := M) I J m n := by
  refine LinearMap.ext fun y => ?_
  change tmap (R := R) (M := M) I J hm hn (compQ (R := R) (M := M) I J m' n' y)
      = compQ (R := R) (M := M) I J m n y
  have hstep : tmap (R := R) (M := M) I J hm hn
      = (tmap (R := R) (M := M) I J hm (le_refl n)).comp
        (tmap (R := R) (M := M) I J (le_refl m') hn) :=
    tmap_comp (R := R) (M := M) (I := I) (J := J) (h₁ := hm) (h₁' := le_refl n)
      (h₂ := le_refl m') (h₂' := hn)
  rw [hstep, LinearMap.comp_apply]
  have h2 : compQ (R := R) (M := M) I J m' n' y = qq (R := R) (M := M) I J m' n'
      (AdicCompletion.eval I (M ⧸ (J ^ m' • (⊤ : Submodule R M))) n'
        (quotientAdicEquiv (M := M) I (J ^ m')
          (AdicCompletion.eval J (AdicCompletion I M) m' y))) := rfl
  rw [h2, tmap_qq_nat_n (I := I) (J := J) hn, tmap_qq_nat_m (I := I) (J := J) hm,
    quotientAdicEquiv_nat (I := I) (J := J) hm]
  have h3 : qmap (M := AdicCompletion I M) (Ideal.pow_le_pow_right (I := J) hm)
      (AdicCompletion.eval J (AdicCompletion I M) m' y) = AdicCompletion.eval J (AdicCompletion I M) m y := by
    rw [← transitionMap_eq_qmap (M := AdicCompletion I M) J hm, AdicCompletion.eval_apply,
      AdicCompletion.eval_apply]
    exact AdicCompletion.transitionMap_comp_eval_apply (I := J) (M := AdicCompletion I M) hm y
  rw [h3]
  rfl


/-! ### The two comparison maps `Φ` and `Ψ` -/

/-- `Φ : (M^I)^J → M^(I+J)`, given on the `k`-th component by the `(k,k)`-component. -/
noncomputable def Phi :
    AdicCompletion J (AdicCompletion I M) →ₗ[R] AdicCompletion (I ⊔ J) M where
  toFun y := ⟨fun k => qmap (M := M) (sup_pow_le_pow_sup I J k)
      (compQ (R := R) (M := M) I J k k y), by
    intro k k' hkk'
    show qmap (M := M) (Ideal.pow_le_pow_right (I := I ⊔ J) hkk')
        (qmap (M := M) (sup_pow_le_pow_sup I J k')
          (compQ (R := R) (M := M) I J k' k' y))
      = qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k y)
    have hcq : compQ (R := R) (M := M) I J k k y
        = tmap (R := R) (M := M) I J hkk' hkk'
          (compQ (R := R) (M := M) I J k' k' y) := by
      rw [← LinearMap.comp_apply]
      exact (LinearMap.congr_fun (compQ_compat (I := I) (J := J) hkk' hkk') y).symm
    have htmap : tmap (R := R) (M := M) I J hkk' hkk'
        = qmap (M := M) (sup_le_sup (Ideal.pow_le_pow_right (I := I) hkk')
            (Ideal.pow_le_pow_right (I := J) hkk')) := rfl
    rw [hcq, htmap, qmap_qmap, qmap_qmap]⟩
  map_add' y z := by
    ext k
    show qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k (y + z))
      = qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k y)
        + qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k z)
    rw [map_add, map_add]
  map_smul' r y := by
    ext k
    show qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k (r • y))
      = r • qmap (M := M) (sup_pow_le_pow_sup I J k) (compQ (R := R) (M := M) I J k k y)
    rw [map_smul, map_smul]

/-- `Ψ : M^(I+J) → (M^I)^J`. -/
noncomputable def Psi :
    AdicCompletion (I ⊔ J) M →ₗ[R] AdicCompletion J (AdicCompletion I M) where
  toFun x := ⟨fun m => (quotientAdicEquiv (M := M) I (J ^ m)).symm
      (Lm (R := R) (M := M) I J m x), by
    intro m m' hmm'
    show qmap (M := AdicCompletion I M) (Ideal.pow_le_pow_right (I := J) hmm')
        ((quotientAdicEquiv (M := M) I (J ^ m')).symm (Lm (R := R) (M := M) I J m' x))
      = (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m x)
    rw [quotientAdicEquiv_nat_symm (I := I) (J := J) hmm', Lm_nat (I := I) (J := J) hmm']⟩
  map_add' x y := by
    ext m
    show (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m (x + y))
      = (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m x)
        + (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m y)
    rw [map_add, map_add]
  map_smul' r x := by
    ext m
    show (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m (r • x))
      = r • (quotientAdicEquiv (M := M) I (J ^ m)).symm (Lm (R := R) (M := M) I J m x)
    rw [map_smul, map_smul]

lemma compQ_Psi (m n : ℕ) (x : AdicCompletion (I ⊔ J) M) :
    compQ (R := R) (M := M) I J m n (Psi (R := R) (M := M) I J x) =
      compP (R := R) (M := M) I J m n x := by
  show qq (R := R) (M := M) I J m n
      (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
        (quotientAdicEquiv (M := M) I (J ^ m)
          (AdicCompletion.eval J (AdicCompletion I M) m (Psi (R := R) (M := M) I J x)))) = _
  have h1 : (quotientAdicEquiv (M := M) I (J ^ m))
      (AdicCompletion.eval J (AdicCompletion I M) m (Psi (R := R) (M := M) I J x))
        = Lm (R := R) (M := M) I J m x := LinearEquiv.apply_symm_apply _ _
  rw [h1, eval_Lm]
  exact LinearEquiv.apply_symm_apply _ _

lemma compP_Phi (m n : ℕ) (y : AdicCompletion J (AdicCompletion I M)) :
    compP (R := R) (M := M) I J m n (Phi (R := R) (M := M) I J y) =
      compQ (R := R) (M := M) I J m n y := by
  show qmap (M := M) (by rw [Nat.add_comm]; exact pow_sup_le I J n m)
      (AdicCompletion.eval (I ⊔ J) M (m + n) (Phi (R := R) (M := M) I J y)) = _
  have h1 : AdicCompletion.eval (I ⊔ J) M (m + n) (Phi (R := R) (M := M) I J y)
      = qmap (M := M) (sup_pow_le_pow_sup I J (m + n))
        (compQ (R := R) (M := M) I J (m + n) (m + n) y) := rfl
  rw [h1, qmap_qmap]
  have h2 : compQ (R := R) (M := M) I J m n y
      = qmap (M := M) (sup_le_sup (Ideal.pow_le_pow_right (I := I) (Nat.le_add_left n m))
          (Ideal.pow_le_pow_right (I := J) (Nat.le_add_right m n)))
        (compQ (R := R) (M := M) I J (m + n) (m + n) y) := by
    rw [← LinearMap.comp_apply,
      ← compQ_compat (I := I) (J := J) (Nat.le_add_right m n) (Nat.le_add_left n m)]
    rfl
  rw [h2]

/-- `Φ` is a left inverse of `Ψ`. -/
theorem Phi_Psi (x : AdicCompletion (I ⊔ J) M) :
    Phi (R := R) (M := M) I J (Psi (R := R) (M := M) I J x) = x := by
  refine AdicCompletion.ext fun k => ?_
  show qmap (M := M) (sup_pow_le_pow_sup I J k)
      (compQ (R := R) (M := M) I J k k (Psi (R := R) (M := M) I J x)) = x.val k
  rw [compQ_Psi]
  show qmap (M := M) (sup_pow_le_pow_sup I J k) (compP (R := R) (M := M) I J k k x) = x.val k
  rw [show compP (R := R) (M := M) I J k k x
      = qmap (M := M) (by rw [Nat.add_comm]; exact pow_sup_le I J k k) (x.val (k + k)) from rfl,
    qmap_qmap,
    ← AdicCompletion.transitionMap_comp_eval_apply (I := I ⊔ J) (M := M)
      (m := k) (n := k + k) (by lia) x,
    transitionMap_eq_qmap]

/-- `Ψ` is a left inverse of `Φ`. -/
theorem Psi_Phi (y : AdicCompletion J (AdicCompletion I M)) :
    Psi (R := R) (M := M) I J (Phi (R := R) (M := M) I J y) = y := by
  refine AdicCompletion.ext fun m => ?_
  show (quotientAdicEquiv (M := M) I (J ^ m)).symm
      (Lm (R := R) (M := M) I J m (Phi (R := R) (M := M) I J y)) = y.val m
  refine (LinearEquiv.symm_apply_eq (e := quotientAdicEquiv (M := M) I (J ^ m))).mpr ?_
  show Lm (R := R) (M := M) I J m (Phi (R := R) (M := M) I J y)
      = (quotientAdicEquiv (M := M) I (J ^ m)) (y.val m)
  refine AdicCompletion.ext fun n => ?_
  show AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
      (Lm (R := R) (M := M) I J m (Phi (R := R) (M := M) I J y))
    = AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
      ((quotientAdicEquiv (M := M) I (J ^ m)) (y.val m))
  rw [eval_Lm, compP_Phi]
  have hcomp : compQ (R := R) (M := M) I J m n y
      = qq (R := R) (M := M) I J m n
        (AdicCompletion.eval I (M ⧸ (J ^ m • (⊤ : Submodule R M))) n
          ((quotientAdicEquiv (M := M) I (J ^ m)) (y.val m))) := rfl
  rw [hcomp]
  exact LinearEquiv.symm_apply_apply _ _

/-- **Atiyah–Macdonald (1969), Exercise 10.5**: the `b`-adic completion of the `a`-adic completion
of a finitely generated module over a Noetherian ring is the `(a+b)`-adic completion. -/
noncomputable def solution :
    AdicCompletion J (AdicCompletion I M) ≃ₗ[R] AdicCompletion (I ⊔ J) M where
  toFun := Phi (R := R) (M := M) I J
  invFun := Psi (R := R) (M := M) I J
  left_inv := Psi_Phi (R := R) (M := M) (I := I) (J := J)
  right_inv := Phi_Psi (R := R) (M := M) (I := I) (J := J)
  map_add' := map_add (Phi (R := R) (M := M) I J)
  map_smul' := map_smul (Phi (R := R) (M := M) I J)

end Main2
end AtiyahMcdonald69.Ex_10_5

/-! ### Main exports and axiom check -/

#check @AtiyahMcdonald69.Ex_10_5.solution
#print axioms AtiyahMcdonald69.Ex_10_5.solution
#print axioms AtiyahMcdonald69.Ex_10_5.Phi_Psi
#print axioms AtiyahMcdonald69.Ex_10_5.Psi_Phi
#print axioms AtiyahMcdonald69.Ex_10_5.compQ_compat
#print axioms AtiyahMcdonald69.Ex_10_5.quotientAdicEquiv
