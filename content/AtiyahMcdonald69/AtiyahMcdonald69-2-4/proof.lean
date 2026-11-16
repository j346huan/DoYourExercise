/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter II (Modules), Exercise 4.

Statement (verbatim, p. 32 of the 1969 edition):

  "Let M_i (i ∈ I) be any family of A-modules, and let M be their direct sum.
   Prove that M is flat  ⟺  each M_i is flat."

Below this is formalized for an arbitrary (possibly infinite) index type `ι` and an arbitrary
family `M : ι → Type v` of modules over a commutative ring `R`, the module `M` of the statement
being the direct sum `⨁ i, M i`.

The textbook proof rests on three ingredients, and each is proved here rather than quoted:

1. `flat_iff_rTensor_injective` : the tensor-injectivity criterion for flatness, which
   identifies Mathlib's `Module.Flat` with the textbook definition of flatness;
2. `tensorDirectSumRight` : the concrete isomorphism `N ⊗ (⨁ i, M i) ≃ ⨁ i, N ⊗ M i` given by
   the universal property of the tensor product and of the direct sum, together with the
   *naturality square* `tensorDirectSumRight_rTensor_comm`, which is what "tensor products
   commute with direct sums" leaves implicit when one says that `f ⊗ 1` for `⨁ i, M i`
   "identifies with" the family of the `f ⊗ 1` for `M i`;
3. `directSum_lmap_injective_iff` : a map out of a direct sum is injective iff each of its
   components is (this needs both the coprojections `DirectSum.lof` and the projections
   `DirectSum.component`).

The direction `⇐` is the tensor-distribution argument; the direction `⇒` is
`flat_of_directSummand`, which uses that every `M i` is a direct summand of `⨁ i, M i`, hence a
retract of it.  A concrete non-flat module (`ℤ/2` over `ℤ`) and a concrete direct sum that fails
to be flat are given at the end, so that the flatness hypothesis on the members of the family is
not vacuous.

## Audit of the natural (one-paragraph) proof

The natural proof runs: "for any injection `f`, the map `f ⊗ 1` for `⨁ i, M i` identifies with
`⨁ i, (f ⊗ 1_{M i})`, since tensor products commute with direct sums; a direct sum of maps is
injective exactly when each component is; the assertion follows from the injectivity criterion
for flatness."  Each step needs something that the sketch omits, and the omissions are harmless
but real:

* "Identifies with" must be a *naturality square*, not merely an isomorphism: one needs
  `tensorDirectSumRight_rTensor_comm`, which says that transporting `f ⊗ 1_{⨁ i, M i}` along the
  distribution isomorphisms gives exactly the direct sum of the maps `f ⊗ 1_{M i}`;
* the componentwise criterion needs the coprojections into the direct sum (to test a component)
  and the projections out of it (to conclude `x = y`); this is `directSum_lmap_injective_iff`,
  and at the level of `f ⊗ 1` it is `rTensor_directSum_injective_iff`;
* the direction `M` flat `⇒` each `M i` flat is *not* obtained by composing arrows in the wrong
  direction; it uses that `DirectSum.component i ∘ DirectSum.lof i = id`, i.e. that each `M i` is
  a retract of the direct sum (`flat_of_directSummand`);
* the hypothesis that `A` is a commutative *ring* is used twice (in the flatness criterion and in
  the identification of the two orders of the tensor product); the statement is otherwise
  unchanged and in particular no finiteness of the index set `I` is assumed.  The statement is
  about the direct *sum*: the proof uses finite supports, and no claim is made here about direct
  products; for a finite index set the two agree, which is the corollary `flat_pi_iff`.
-/
import Mathlib

universe u v w t

namespace AtiyahMcdonald69.Ex_2_4

open TensorProduct DirectSum

/-! ### 1. The textbook criterion for flatness

Flatness of a module `M` is the requirement that `- ⊗ M` (equivalently `M ⊗ -`) turns injective
linear maps into injective maps.  `Module.Flat` in Mathlib is stated through finitely generated
submodules; over a commutative ring the two formulations agree, which is the content of the next
two theorems. -/

section FlatnessCriterion

variable {R : Type u} [CommRing R]

/-- **The injectivity criterion for flatness.** An `R`-module `M` is flat if and only if
`f ⊗ 1_M : N ⊗ M → N' ⊗ M` is injective for every injective linear map `f : N → N'`. -/
theorem flat_iff_rTensor_injective (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
        (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  Module.Flat.iff_rTensor_preserves_injective_linearMap

/-- The same criterion with `1_M ⊗ f` in place of `f ⊗ 1_M`. -/
theorem flat_iff_lTensor_injective (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
        (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) :=
  Module.Flat.iff_lTensor_preserves_injective_linearMap

end FlatnessCriterion

/-! ### 2. Tensor products commute with direct sums -/

section DirectSumTensor

variable {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **Tensor products commute with direct sums** (right argument):
`N ⊗ (⨁ i, M i) ≃ₗ ⨁ i, N ⊗ M i`.  This is the isomorphism used in the textbook proof; it is
built from the universal property of the tensor product and of the direct sum. -/
noncomputable def tensorDirectSumRight (N : Type t) [AddCommMonoid N] [Module R N] :
    (N ⊗[R] ⨁ i, M i) ≃ₗ[R] (⨁ i, N ⊗[R] M i) := by
  classical
  exact TensorProduct.directSumRight R R N M

/-- **Tensor products commute with direct sums** (left argument):
`(⨁ i, M i) ⊗ N ≃ₗ ⨁ i, M i ⊗ N`. -/
noncomputable def tensorDirectSumLeft (N : Type t) [AddCommMonoid N] [Module R N] :
    ((⨁ i, M i) ⊗[R] N) ≃ₗ[R] (⨁ i, M i ⊗[R] N) := by
  classical
  exact TensorProduct.directSumLeft R R M N

/-- The value of `tensorDirectSumRight` on a pure tensor, componentwise: on `n ⊗ₜ x` the
isomorphism is `n ⊗ₜ x ↦ (fun i => n ⊗ₜ x i)`. -/
theorem tensorDirectSumRight_tmul_apply (N : Type t) [AddCommMonoid N] [Module R N]
    (n : N) (x : ⨁ i, M i) (i : ι) :
    tensorDirectSumRight (M := M) N (n ⊗ₜ[R] x) i = n ⊗ₜ[R] x i := by
  classical
  simp [tensorDirectSumRight]

/-- The value of `tensorDirectSumLeft` on a pure tensor, componentwise:
`x ⊗ₜ n ↦ (fun i => x i ⊗ₜ n)`. -/
theorem tensorDirectSumLeft_tmul_apply (N : Type t) [AddCommMonoid N] [Module R N]
    (x : ⨁ i, M i) (n : N) (i : ι) :
    tensorDirectSumLeft (M := M) N (x ⊗ₜ[R] n) i = x i ⊗ₜ[R] n := by
  classical
  simp [tensorDirectSumLeft]

/-- **Naturality of the tensor/direct-sum isomorphism**: tensoring with the direct sum
corresponds, through `tensorDirectSumRight`, to the direct sum of the maps obtained by tensoring
with the individual summands.  This is the precise sense in which `f ⊗ 1` for `⨁ i, M i`
"identifies with" the family of the `f ⊗ 1_{M i}`. -/
theorem tensorDirectSumRight_rTensor_comm {N N' : Type t} [AddCommMonoid N] [AddCommMonoid N']
    [Module R N] [Module R N'] (f : N →ₗ[R] N') :
    (tensorDirectSumRight (M := M) N').toLinearMap ∘ₗ f.rTensor (⨁ i, M i) =
      DirectSum.lmap (fun i => f.rTensor (M i)) ∘ₗ
        (tensorDirectSumRight (M := M) N).toLinearMap := by
  classical
  refine LinearMap.ext fun x => ?_
  refine DirectSum.ext_component R fun i => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => simp [tensorDirectSumRight, ← DirectSum.apply_eq_component]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Naturality of the tensor/direct-sum isomorphism**, left version. -/
theorem tensorDirectSumLeft_lTensor_comm {N N' : Type t} [AddCommMonoid N] [AddCommMonoid N']
    [Module R N] [Module R N'] (f : N →ₗ[R] N') :
    (tensorDirectSumLeft (M := M) N').toLinearMap ∘ₗ f.lTensor (⨁ i, M i) =
      DirectSum.lmap (fun i => f.lTensor (M i)) ∘ₗ
        (tensorDirectSumLeft (M := M) N).toLinearMap := by
  classical
  refine LinearMap.ext fun x => ?_
  refine DirectSum.ext_component R fun i => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [tensorDirectSumLeft, ← DirectSum.apply_eq_component]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Injectivity of a map out of a direct sum, componentwise.**  A linear map
`⨁ i, M i → ⨁ i, N i` induced by a family of maps `f i : M i → N i` is injective exactly when
every `f i` is injective.  (This uses a *direct sum*: the coprojections `DirectSum.lof i` test the
components, and the projections `DirectSum.component i` reassemble an element from them.) -/
theorem directSum_lmap_injective_iff {M : ι → Type v} {N : ι → Type t}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (f : ∀ i, M i →ₗ[R] N i) :
    Function.Injective (DirectSum.lmap f) ↔ ∀ i, Function.Injective (f i) := by
  classical
  constructor
  · intro h i x y hxy
    have h' : DirectSum.lmap f (DirectSum.lof R ι M i x) =
        DirectSum.lmap f (DirectSum.lof R ι M i y) := by
      rw [DirectSum.lmap_lof, DirectSum.lmap_lof, hxy]
    have h'' := congrArg (DirectSum.component R ι M i) (h h')
    simpa using h''
  · intro h x y hxy
    refine DirectSum.ext_component R fun i => ?_
    have h2 : f i (x i) = f i (y i) := by
      have h'' := congrArg (DirectSum.component R ι N i) hxy
      simpa [DirectSum.lmap_apply, ← DirectSum.apply_eq_component] using h''
    exact h i h2

/-- Naturality of `TensorProduct` with respect to a coprojection into a direct sum: tensoring the
composite `M i → ⨁ i, M i` with a map `g` agrees with applying `g` first. -/
theorem lof_lTensor_rTensor_comm [DecidableEq ι] {N₀ N₁ : Type t} [AddCommMonoid N₀]
    [AddCommMonoid N₁] [Module R N₀] [Module R N₁] (g : N₀ →ₗ[R] N₁) (i : ι)
    (z : N₀ ⊗[R] M i) :
    g.rTensor (⨁ i, M i) ((DirectSum.lof R ι M i).lTensor N₀ z) =
      (DirectSum.lof R ι M i).lTensor N₁ (g.rTensor (M i) z) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- The coprojection into a direct sum followed by the projection onto that summand is the
identity, also after tensoring with an arbitrary module. -/
theorem component_lTensor_lof_lTensor [DecidableEq ι] (N₀ : Type t) [AddCommMonoid N₀]
    [Module R N₀] (i : ι) (z : N₀ ⊗[R] M i) :
    (DirectSum.component R ι M i).lTensor N₀ ((DirectSum.lof R ι M i).lTensor N₀ z) = z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end DirectSumTensor

/-! ### 3. The exercise: `⨁ i, M i` is flat iff every `M i` is flat -/

section Main

variable {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **Every member of the family is a retract of the direct sum.**  The coprojection
`DirectSum.lof i : M i →ₗ ⨁ i, M i` and the projection `DirectSum.component i` compose to the
identity, so flatness of the direct sum descends to each summand. -/
theorem flat_of_directSummand (h : Module.Flat R (⨁ i, M i)) (i : ι) :
    Module.Flat R (M i) := by
  classical
  exact Module.Flat.of_retract (f := h) (DirectSum.lof R ι M i) (DirectSum.component R ι M i)
    (DirectSum.component_comp_lof_same R i)

/-- **A direct sum of flat modules is flat.**  An injective `f` tensored with `⨁ i, M i`
becomes, through the isomorphism `tensorDirectSumRight`, the direct sum of the maps `f ⊗ 1_{M i}`,
which is injective because each of its components is. -/
theorem flat_directSum (h : ∀ i, Module.Flat R (M i)) : Module.Flat R (⨁ i, M i) := by
  classical
  refine Module.Flat.iff_rTensor_injectiveₛ.mpr ?_
  intro P _ _ K
  have hcomp : ∀ i, Function.Injective (K.subtype.rTensor (M i)) := fun i =>
    Module.Flat.rTensor_preserves_injective_linearMap (M := M i) _ K.injective_subtype
  have hlmap : Function.Injective (DirectSum.lmap fun i => K.subtype.rTensor (M i)) :=
    (directSum_lmap_injective_iff (M := fun i => K ⊗[R] M i) (N := fun i => P ⊗[R] M i)
      (f := fun i => K.subtype.rTensor (M i))).mpr hcomp
  intro x y hxy
  have sq := tensorDirectSumRight_rTensor_comm (M := M) (N := K) (N' := P) K.subtype
  have hx : (tensorDirectSumRight (M := M) P) (K.subtype.rTensor (⨁ i, M i) x) =
      (DirectSum.lmap fun i => K.subtype.rTensor (M i))
        (tensorDirectSumRight (M := M) K x) := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun sq x
  have hy : (tensorDirectSumRight (M := M) P) (K.subtype.rTensor (⨁ i, M i) y) =
      (DirectSum.lmap fun i => K.subtype.rTensor (M i))
        (tensorDirectSumRight (M := M) K y) := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun sq y
  have hsquare := congrArg (tensorDirectSumRight (M := M) P) hxy
  rw [hx, hy] at hsquare
  exact (tensorDirectSumRight (M := M) K).injective (hlmap hsquare)

/-- **The componentwise form of the tensor/direct-sum argument.**  For every linear map `f`, the
map `f ⊗ 1` tensored with the direct sum `⨁ i, M i` is injective if and only if every `f ⊗ 1_{M i}`
is injective.  This is the statement the textbook proof establishes before quoting the
injectivity criterion for flatness. -/
theorem rTensor_directSum_injective_iff {N N' : Type t} [AddCommMonoid N] [AddCommMonoid N']
    [Module R N] [Module R N'] (f : N →ₗ[R] N') :
    Function.Injective (f.rTensor (⨁ i, M i)) ↔ ∀ i, Function.Injective (f.rTensor (M i)) := by
  classical
  constructor
  · intro hf i x y hxy
    have hstep : (DirectSum.lof R ι M i).lTensor N' (f.rTensor (M i) x) =
        (DirectSum.lof R ι M i).lTensor N' (f.rTensor (M i) y) := by rw [hxy]
    have hkey : (DirectSum.lof R ι M i).lTensor N x = (DirectSum.lof R ι M i).lTensor N y := by
      apply hf
      rw [lof_lTensor_rTensor_comm (M := M) f i x, lof_lTensor_rTensor_comm (M := M) f i y]
      exact hstep
    have hfin := congrArg (fun z => (DirectSum.component R ι M i).lTensor N z) hkey
    rwa [component_lTensor_lof_lTensor (M := M) N i x,
      component_lTensor_lof_lTensor (M := M) N i y] at hfin
  · intro hf
    have hlmap : Function.Injective (DirectSum.lmap fun i => f.rTensor (M i)) :=
      (directSum_lmap_injective_iff (M := fun i => N ⊗[R] M i) (N := fun i => N' ⊗[R] M i)
        (f := fun i => f.rTensor (M i))).mpr hf
    intro x y hxy
    have sq := tensorDirectSumRight_rTensor_comm (M := M) (N := N) (N' := N') f
    have hx : (tensorDirectSumRight (M := M) N') (f.rTensor (⨁ i, M i) x) =
        (DirectSum.lmap fun i => f.rTensor (M i)) (tensorDirectSumRight (M := M) N x) := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun sq x
    have hy : (tensorDirectSumRight (M := M) N') (f.rTensor (⨁ i, M i) y) =
        (DirectSum.lmap fun i => f.rTensor (M i)) (tensorDirectSumRight (M := M) N y) := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun sq y
    have hsquare := congrArg (tensorDirectSumRight (M := M) N') hxy
    rw [hx, hy] at hsquare
    exact (tensorDirectSumRight (M := M) N).injective (hlmap hsquare)

/-- **Atiyah–Macdonald, Chapter II, Exercise 4.**  Let `M i` (`i ∈ I`) be any family of
`A`-modules and let `M` be their direct sum.  Then `M` is flat if and only if each `M i` is
flat. -/
theorem flat_directSum_iff : Module.Flat R (⨁ i, M i) ↔ ∀ i, Module.Flat R (M i) :=
  ⟨fun h i => flat_of_directSummand h i, flat_directSum⟩

/-- Contrapositive form: a direct sum with a non-flat summand is not flat. -/
theorem not_flat_directSum_of_not_flat (i : ι) (h : ¬ Module.Flat R (M i)) :
    ¬ Module.Flat R (⨁ i, M i) :=
  fun hsum => h (flat_directSum_iff.mp hsum i)

/-- Direct sums of copies of the ring are flat (they are free). -/
theorem flat_directSum_self : Module.Flat R (⨁ _ : ι, R) :=
  flat_directSum fun _ => Module.Flat.self

/-- For a finite index type the direct sum and the direct product agree, so the criterion also
holds for finite direct products. -/
theorem flat_pi_iff [Fintype ι] :
    Module.Flat R (∀ i, M i) ↔ ∀ i, Module.Flat R (M i) := by
  rw [← flat_directSum_iff (M := M)]
  exact (Module.Flat.equiv_iff (DirectSum.linearEquivFunOnFintype R ι M)).symm

end Main

/-! ### 4. A concrete non-flat module and a concrete non-flat direct sum

The flatness hypothesis on the members of the family is not vacuous: over `ℤ` the module `ℤ/2`
fails to be flat, because multiplication by `2` is injective on `ℤ` but not on `ℤ/2`. -/

section Concrete

/-- `ℤ/2` is not a flat `ℤ`-module: a flat module has no `2`-torsion, while `2 • 1 = 0`. -/
theorem zmod_two_not_flat : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  have hreg : IsSMulRegular (ZMod 2) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (x := (2 : ℤ)) (by norm_num))
  have h2 : (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • (0 : ZMod 2) := by
    rw [smul_zero, zsmul_eq_mul, mul_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  exact one_ne_zero (hreg h2)

/-- The direct sum of copies of `ℤ/2` indexed by `Bool` is not flat. -/
theorem zmodTwo_directSum_not_flat : ¬ Module.Flat ℤ (⨁ _ : Bool, ZMod 2) :=
  fun h => zmod_two_not_flat (flat_directSum_iff.mp h false)

/-- The direct sum of copies of `ℤ` indexed by `Bool` is flat. -/
theorem int_directSum_flat : Module.Flat ℤ (⨁ _ : Bool, ℤ) :=
  flat_directSum fun _ => Module.Flat.self

end Concrete

/-! ### 5. Axiom audit -/

#print axioms flat_iff_rTensor_injective
#print axioms tensorDirectSumRight_rTensor_comm
#print axioms directSum_lmap_injective_iff
#print axioms rTensor_directSum_injective_iff
#print axioms flat_directSum
#print axioms flat_of_directSummand
#print axioms flat_directSum_iff
#print axioms flat_pi_iff
#print axioms zmod_two_not_flat
#print axioms zmodTwo_directSum_not_flat

end AtiyahMcdonald69.Ex_2_4
