import Mathlib

/-!
# Atiyah–Macdonald, Chapter 2, Exercise 24 — Lean 4 formalisation

Reference: M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*,
Addison–Wesley 1969, Chapter 2 ("Modules"), Exercise 24.  The book introduces the batch of
Exercises 22–26 with the sentence

> "In these Exercises it will be assumed that the reader is familiar with the definition and
> basic properties of the Tor functor."

and Exercise 24 reads verbatim

> 24. If `M` is an `A`-module, the following are equivalent:
>   i) `M` is flat;
>   ii) `Tor_n^A(M, N) = 0` for all `n > 0` and all `A`-modules `N`;
>   iii) `Tor_1^A(M, N) = 0` for all `A`-modules `N`.

(Chapter 2 of the book has no §-numbering for the exercises; exercise 2.24 is the one quoted
above.)

## How `Tor` is represented here

`Tor_n^A(M, N)` is, by definition, the `n`-th homology of the complex `M ⊗_A P_•`, where
`P_• → N → 0` is a projective resolution of `N` (over a commutative ring projective
resolutions may be taken free, and we take them free).  Since `Tor_n` does not depend on the
chosen resolution, the assertion `Tor_n^A(M, N) = 0` is equivalent to the
resolution-independent assertion

  for every free partial resolution `P_•` of `N`, the `n`-th homology of `M ⊗ P_•` vanishes.

This is the assertion `TorVanishes M k N` below, indexed so that `TorVanishes M k N` is the
statement `Tor_{k+1}^A(M, N) = 0`: a partial resolution `P` of `N` provides free modules
`P.X n`, differentials `P.d n : P.X (n+1) ⟶ P.X n`, exactness at the inner levels
`0, 1, …, k`, and an augmentation `P.X 0 ⟶ N` onto `N`; the `(k+1)`-st homology of the
tensored complex is `ker (1 ⊗ P.d k) / im (1 ⊗ P.d (k+1))`.

`TorZero M n N` (for `n ≥ 1`) is by definition `TorVanishes M (n-1) N`, i.e. it is the
statement `Tor_n^A(M,N) = 0` with the same indexing as in the book.  The three statements of
the exercise then read

  i)   `Module.Flat R M`;
  ii)  `∀ n, 0 < n → ∀ N, TorZero M n N`;
  iii) `∀ N, TorZero M 1 N`.

## Main results

* `FreePartialResolution` — the data of a free partial resolution;
* `TorVanishes`, `TorZero` — `Tor_{k+1}^A(M,N) = 0` and `Tor_n^A(M,N) = 0`;
* `flat_imp_torVanishes` — (i) ⇒ (ii);
* `torVanishes_zero_imp_flat` — (iii) ⇒ (i);
* `flat_iff_torOne` — (i) ⇔ (iii);
* `atiyah_macdonald_2_24` — the three-way equivalence of the exercise.

## Proof

* (i) ⇒ (ii): if `M` is flat then `M ⊗ -` is exact, so it carries an exact partial resolution
  of `N` to an exact complex, and all positive homology vanishes.
* (ii) ⇒ (iii) is immediate.
* (iii) ⇒ (i): by the ideal criterion for flatness (`Module.Flat.iff_lTensor_injective'`) it
  suffices to show that `M ⊗ I → M ⊗ R` is injective for every ideal `I` of `R`.  Apply (iii)
  to the free partial resolution `Q_1 → Q_0 → R → R/I` of `R/I`, where `Q_0` is the free
  module on the underlying set of `I` (mapping onto `I`) and `Q_1` is the free module on the
  underlying set of the kernel of `Q_0 → I` (mapping onto that kernel).  Vanishing of
  `Tor_1(M, R/I)` says precisely `ker (1 ⊗ (Q_0 → R)) ⊆ im (1 ⊗ (Q_1 → Q_0))`.  Given
  `x ∈ M ⊗ I` mapping to `0` in `M ⊗ R`, lift `x` to `y ∈ M ⊗ Q_0` (possible since
  `M ⊗ Q_0 → M ⊗ I` is surjective); then `y` dies in `M ⊗ R`, hence `y = (1 ⊗ (Q_1 → Q_0))(z)`,
  and `x` is the image of `z` under `1 ⊗ (Q_1 → Q_0 → I → R)`, which is zero because
  `Q_1 → Q_0 → I` lands in the kernel of `Q_0 → I`.  Hence `x = 0`.
-/

namespace AtiyahMcdonald69.Ex_2_24

open TensorProduct LinearMap

universe u

variable {R : Type u} [CommRing R]

/-- A free partial resolution of the module `N`, exact in degrees `0, …, k`.

It consists of free modules `X 0, X 1, X 2, …`, differentials `d n : X (n+1) ⟶ X n`, an
augmentation `ε : X 0 ⟶ N` onto `N`, and exactness at the levels `0, …, k`
(`ker (d n) = im (d (n+1))` for `n ≤ k`) together with `ker ε = im (d 0)`. -/
structure FreePartialResolution (N : ModuleCat.{u} R) (k : ℕ) where
  /-- the terms of the resolution -/
  X : ℕ → ModuleCat.{u} R
  /-- every term is a free module -/
  free : ∀ n, Module.Free R (X n)
  /-- the differentials `d n : X (n+1) ⟶ X n` -/
  d : ∀ n, X (n + 1) ⟶ X n
  /-- exactness at the inner levels `0, …, k` -/
  exact : ∀ m, m ≤ k → Function.Exact (d (m + 1)).hom (d m).hom
  /-- the augmentation `X 0 ⟶ N` -/
  ε : X 0 ⟶ N
  /-- the augmentation is surjective -/
  ε_surj : Function.Surjective ε.hom
  /-- exactness at the level of `X 0` -/
  exact_aug : Function.Exact (d 0).hom ε.hom

variable (M : ModuleCat.{u} R)

/-- `TorVanishes M k N` is the assertion `Tor_{k+1}^A(M, N) = 0`.

It states that for every free partial resolution `P` of `N` the `(k+1)`-st homology of the
complex `M ⊗ P_•` vanishes, i.e. `ker (1 ⊗ P.d k) ⊆ im (1 ⊗ P.d (k+1))`.  As `Tor_{k+1}`
does not depend on the chosen free resolution, this is the standard meaning of
`Tor_{k+1}^A(M,N) = 0`. -/
def TorVanishes (k : ℕ) (N : ModuleCat.{u} R) : Prop :=
  ∀ P : FreePartialResolution N k,
    LinearMap.ker (lTensor M (P.d k).hom) ≤ LinearMap.range (lTensor M (P.d (k + 1)).hom)

/-- `TorZero M n N` is the assertion `Tor_n^A(M, N) = 0`, with the same indexing as in the
book.  It is used only for `n ≥ 1`; because subtraction on `ℕ` is truncated, `TorZero M 0 N`
coincides definitionally with `TorZero M 1 N`, and the statement of the exercise below
quantifies only over `n` with `0 < n`. -/
def TorZero (n : ℕ) (N : ModuleCat.{u} R) : Prop := TorVanishes M (n - 1) N

/-! ### (i) ⇒ (ii) : flatness implies vanishing of Tor -/

/-- If `M` is flat, then `Tor_{k+1}^A(M,N) = 0` for every `k` and every `N`. -/
theorem flat_imp_torVanishes (hM : Module.Flat R M) :
    ∀ (k : ℕ) (N : ModuleCat.{u} R), TorVanishes M k N := by
  intro k N P
  have hex : Function.Exact (lTensor M (P.d (k + 1)).hom) (lTensor M (P.d k).hom) := by
    have h := P.exact k le_rfl
    have h' := Module.Flat.lTensor_exact (R := R) (M := (M : Type u)) h
    simpa using h'
  rw [LinearMap.exact_iff] at hex
  exact le_of_eq hex

/-! ### The free partial resolution `Q_1 ⟶ Q_0 ⟶ R` of `R ⧸ I` -/

section Construction

variable (I : Ideal R)

/-- The free module on the underlying set of `I`, mapping onto `I`. -/
noncomputable def cover0 : (↥I →₀ R) →ₗ[R] ↥I :=
  Finsupp.linearCombination R (id : ↥I → ↥I)

theorem cover0_surj : Function.Surjective (cover0 I) := by
  intro x
  exact ⟨Finsupp.single x 1, by simp [cover0]⟩

/-- The first syzygy of `cover0`, i.e. the kernel of the free cover of `I`. -/
noncomputable def syz1 : Submodule R (↥I →₀ R) := LinearMap.ker (cover0 I)

/-- The free module on the underlying set of the first syzygy, mapping onto that syzygy. -/
noncomputable def cover1 : (↥(syz1 I) →₀ R) →ₗ[R] ↥(syz1 I) :=
  Finsupp.linearCombination R (id : ↥(syz1 I) → ↥(syz1 I))

theorem cover1_surj : Function.Surjective (cover1 I) := by
  intro x
  exact ⟨Finsupp.single x 1, by simp [cover1]⟩

/-- The map `Q_0 ⟶ R` of the resolution of `R ⧸ I` (the composition `Q_0 ↠ I ↪ R`). -/
noncomputable def resD0 : (↥I →₀ R) →ₗ[R] R := I.subtype ∘ₗ cover0 I

/-- The map `Q_1 ⟶ Q_0` of the resolution of `R ⧸ I` (the composition `Q_1 ↠ K ↪ Q_0`). -/
noncomputable def resD1 : (↥(syz1 I) →₀ R) →ₗ[R] (↥I →₀ R) := (syz1 I).subtype ∘ₗ cover1 I

theorem ker_resD0 : LinearMap.ker (resD0 I) = syz1 I := by
  ext x
  rw [LinearMap.mem_ker, syz1, LinearMap.mem_ker]
  exact Submodule.coe_eq_zero

theorem range_resD1 : LinearMap.range (resD1 I) = syz1 I := by
  have htop : LinearMap.range (cover1 I) = ⊤ := LinearMap.range_eq_top.mpr (cover1_surj I)
  rw [resD1, LinearMap.range_comp, htop, Submodule.map_top, Submodule.range_subtype]

theorem exact_resD1_resD0 : Function.Exact (resD1 I) (resD0 I) := by
  rw [LinearMap.exact_iff, ker_resD0, range_resD1]

theorem range_resD0 : LinearMap.range (resD0 I) = I := by
  have htop : LinearMap.range (cover0 I) = ⊤ := LinearMap.range_eq_top.mpr (cover0_surj I)
  rw [resD0, LinearMap.range_comp, htop, Submodule.map_top, Submodule.range_subtype]

theorem exact_resD0_mkQ : Function.Exact (resD0 I) (Submodule.mkQ I) := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_resD0]

/-- The terms of the free partial resolution of `R ⧸ I`: `R`, `Q_0`, `Q_1`, and `Q_1` again
from degree `2` on (all terms are free, and only degrees `0, 1, 2` carry information). -/
noncomputable def resX : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | 1 => ModuleCat.of R (↥I →₀ R)
  | _ => ModuleCat.of R (↥(syz1 I) →₀ R)

/-- The differentials of the free partial resolution of `R ⧸ I`. -/
noncomputable def resD : ∀ n, resX I (n + 1) ⟶ resX I n
  | 0 => ModuleCat.ofHom (resD0 I)
  | 1 => ModuleCat.ofHom (resD1 I)
  | _ + 2 => 0

theorem resX_free : ∀ n, Module.Free R (resX I n)
  | 0 => show Module.Free R R from inferInstance
  | 1 => show Module.Free R (↥I →₀ R) from inferInstance
  | _ + 2 => show Module.Free R (↥(syz1 I) →₀ R) from inferInstance

theorem resD_exact : ∀ m ≤ 0, Function.Exact (resD I (m + 1)).hom (resD I m).hom
  | 0, _ => exact_resD1_resD0 I

theorem resD_aug : Function.Exact (resD I 0).hom (Submodule.mkQ I) := exact_resD0_mkQ I

/-- The free partial resolution `Q_1 ⟶ Q_0 ⟶ R` of `R ⧸ I`. -/
noncomputable def resQuot : FreePartialResolution (ModuleCat.of R (R ⧸ I)) 0 where
  X := resX I
  free := resX_free I
  d := resD I
  exact := resD_exact I
  ε := ModuleCat.ofHom (Submodule.mkQ I)
  ε_surj := Submodule.mkQ_surjective I
  exact_aug := resD_aug I

theorem cover0_comp_resD1 : cover0 I ∘ₗ resD1 I = 0 := by
  rw [resD1, ← LinearMap.comp_assoc]
  have h : cover0 I ∘ₗ (syz1 I).subtype = 0 := by
    ext x
    have hx : cover0 I (x : ↥I →₀ R) = 0 := x.2
    simpa using hx
  rw [h, LinearMap.zero_comp]

end Construction

/-! ### (iii) ⇒ (i) : vanishing of `Tor_1` implies flatness -/

/-- If `Tor_1^A(M,N) = 0` for every `N`, then `M` is flat. -/
theorem torVanishes_zero_imp_flat (h : ∀ N : ModuleCat.{u} R, TorVanishes M 0 N) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective M (cover0_surj I) x
  have hy0 : (lTensor M (resD0 I)) y = 0 := by
    rw [resD0, LinearMap.lTensor_comp, LinearMap.comp_apply, hy, hx]
  have hhyp := h (ModuleCat.of R (R ⧸ I)) (resQuot I)
  have hmem : y ∈ LinearMap.ker (lTensor M (resD0 I)) := hy0
  have hmem' : y ∈ LinearMap.range (lTensor M (resD1 I)) := hhyp hmem
  obtain ⟨z, hz⟩ := hmem'
  calc x = lTensor M (cover0 I) y := hy.symm
    _ = lTensor M (cover0 I) (lTensor M (resD1 I) z) := by rw [hz]
    _ = lTensor M (cover0 I ∘ₗ resD1 I) z := by
        rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    _ = 0 := by rw [cover0_comp_resD1, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-! ### The exercise -/

/-- `Tor_1^A(M,N) = 0` for all `N` if and only if `M` is flat. -/
theorem flat_iff_torOne :
    Module.Flat R M ↔ ∀ N : ModuleCat.{u} R, TorZero M 1 N :=
  ⟨fun h N => flat_imp_torVanishes M h 0 N, fun h => torVanishes_zero_imp_flat M h⟩

/-- Every free module is flat, so its Tor groups vanish: a concrete consistency check of the
definition of `TorZero`. -/
example (N : ModuleCat.{u} R) : TorZero (ModuleCat.of R R) 1 N :=
  (flat_iff_torOne (ModuleCat.of R R)).mp inferInstance N

/-- **Atiyah–Macdonald, Exercise 2.24.** For an `A`-module `M` the following are equivalent:
(i) `M` is flat; (ii) `Tor_n^A(M,N) = 0` for all `n > 0` and all `A`-modules `N`;
(iii) `Tor_1^A(M,N) = 0` for all `A`-modules `N`. -/
theorem atiyah_macdonald_2_24 :
    List.TFAE [ Module.Flat R M,
      (∀ (n : ℕ), 0 < n → ∀ N : ModuleCat.{u} R, TorZero M n N),
      (∀ N : ModuleCat.{u} R, TorZero M 1 N) ] := by
  tfae_have 1 → 2 := fun h n _hn N => flat_imp_torVanishes M h (n - 1) N
  tfae_have 2 → 3 := fun h N => h 1 one_pos N
  tfae_have 3 → 1 := fun h => torVanishes_zero_imp_flat M h
  tfae_finish

end AtiyahMcdonald69.Ex_2_24

#print axioms AtiyahMcdonald69.Ex_2_24.flat_imp_torVanishes
#print axioms AtiyahMcdonald69.Ex_2_24.torVanishes_zero_imp_flat
#print axioms AtiyahMcdonald69.Ex_2_24.flat_iff_torOne
#print axioms AtiyahMcdonald69.Ex_2_24.atiyah_macdonald_2_24
