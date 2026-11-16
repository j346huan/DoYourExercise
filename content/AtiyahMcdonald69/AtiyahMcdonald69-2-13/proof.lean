/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Addison–Wesley 1969.
Chapter 2 (Modules), Exercise 13.
-/
import Mathlib

/-!
# Atiyah–Macdonald, Exercise 2.13

Let `f : A →+* B` be a ring homomorphism, and let `N` be a `B`-module.  Regarding `N` as an
`A`-module by restriction of scalars, form the `B`-module `N_B = B ⊗[A] N`.  Show that the
homomorphism `g : N → N_B` which maps `y` to `1 ⊗ y` is injective and that `g(N)` is a direct
summand of `N_B`.

The book's argument is reproduced here: the balanced map `(b, y) ↦ b • y` induces
`p : N_B → N` with `p (b ⊗ y) = b • y`; then `p ∘ g = id`, which gives both the injectivity of
`g` and the decomposition `N_B = g(N) ⊕ ker p`.

## Formalisation notes

`N` being a `B`-module "regarded as an `A`-module by restriction of scalars" is formalised by an
`A`-module structure together with `IsScalarTower A B N` (compatibility of the two actions) and
`SMulCommClass A B N` (the actions commute); this is exactly what pulling the scalar
multiplication of a `B`-module back along `f : A →+* B` produces.  The version stated directly
for an arbitrary ring homomorphism `f : A →+* B` is `exercise_2_13` at the end of the file.

Note that `g` is only `A`-linear: `g (b • y) = 1 ⊗ (b • y)` and `b • g y = b ⊗ y` differ in
general (they agree when `b` lies in the image of `A`), so `g N` is not a `B`-submodule of `N_B`.
It is `p` which is also `B`-linear — formalised below as `p_smul`, resp. `pB`.  The decomposition
is therefore one of `A`-modules, as in the proof given in the book; it cannot be refined to one of
`B`-modules.

Audit of the natural proof.  The book's proof is complete and its statement is literally true; its
only implicit point is the one above, namely that the two maps whose composite is the identity are
`A`-linear (not `B`-linear), so that the direct sum decomposition lives in `A`-modules.  Concretely,
with `A = ℤ`, `B = ℤ × ℤ`, `N = ℤ` and `(b₁, b₂) • n = b₁ * n`, and with `b = (0,1)`, `y = 1`, one
gets `g (b • y) = 1 ⊗ 0 = 0` while `b • g y = (0,1) ⊗ 1`; the `ℤ`-bilinear form
`(f, g) ↦ f.1 * g.2` separates the two, so `g (b • y) ≠ b • g y` and `g` is not `B`-linear.
(That last, purely illustrative, example is not formalised in this file.)

## Main results

* `AtiyahMcdonald69.Ex_2_13.p_tmul` : `p (b ⊗ y) = b • y`
* `AtiyahMcdonald69.Ex_2_13.p_unique` : `p` is the unique such `A`-linear map
* `AtiyahMcdonald69.Ex_2_13.smul_tmul_B` : `b • (b' ⊗ y) = (b • b') ⊗ y` in `N_B`
* `AtiyahMcdonald69.Ex_2_13.p_g` : `p (g y) = y`
* `AtiyahMcdonald69.Ex_2_13.g_injective` : `g` is injective
* `AtiyahMcdonald69.Ex_2_13.g_smul_g` : `g (b • y) = 1 ⊗ (b • y)` but `b • g y = b ⊗ y`
* `AtiyahMcdonald69.Ex_2_13.z_eq_g_add_ker` : `z = g (p z) + (z - g (p z))` and
  `p (z - g (p z)) = 0`
* `AtiyahMcdonald69.Ex_2_13.isCompl_range_ker` : `N_B = g(N) ⊕ ker p`
* `AtiyahMcdonald69.Ex_2_13.range_directSummand` : `g(N)` is a direct summand of `N_B`
* `AtiyahMcdonald69.Ex_2_13.gProjection` : the idempotent projection onto `g(N)`
* `AtiyahMcdonald69.Ex_2_13.exercise_2_13` : the exercise for an arbitrary `f : A →+* B`
-/

namespace AtiyahMcdonald69.Ex_2_13

open TensorProduct

section General

variable {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module A N] [Module B N]
variable [IsScalarTower A B N] [SMulCommClass A B N]

/-- The `A`-bilinear map `B × N → N`, `(b, y) ↦ b • y`, whose linearisation is the map `p` of
the exercise. -/
def smulBilin : B →ₗ[A] N →ₗ[A] N where
  toFun b :=
    { toFun := fun y => b • y
      map_add' := fun y z => smul_add b y z
      map_smul' := fun a y => (smul_comm a b y).symm }
  map_add' b b' := LinearMap.ext fun y => add_smul b b' y
  map_smul' a b := LinearMap.ext fun y => IsScalarTower.smul_assoc a b y

/-- The map `p : N_B → N` of the exercise, `p (b ⊗ y) = b • y`, obtained from the universal
property of the tensor product. -/
noncomputable def p : B ⊗[A] N →ₗ[A] N :=
  TensorProduct.lift (smulBilin (A := A) (B := B) (N := N))

/-- The map `g : N → N_B` of the exercise, `g y = 1 ⊗ y`. -/
noncomputable def g : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

omit [Module B N] [IsScalarTower A B N] [SMulCommClass A B N] in
theorem g_apply (y : N) : (g : N →ₗ[A] B ⊗[A] N) y = (1 : B) ⊗ₜ[A] y := rfl

theorem p_tmul (b : B) (y : N) : p (b ⊗ₜ[A] y) = b • y := by
  rw [p, TensorProduct.lift.tmul]
  rfl

omit [Module B N] [IsScalarTower A B N] [SMulCommClass A B N] in
/-- The `B`-module structure of `N_B = B ⊗[A] N`: `B` acts on the left tensor factor. -/
theorem smul_tmul_B (b b' : B) (y : N) : b • ((b' : B) ⊗ₜ[A] y) = (b • b') ⊗ₜ[A] y := rfl

/-- `p` is a retraction of `g`, i.e. `p ∘ g = id`. -/
theorem p_g (y : N) : p ((g : N →ₗ[A] B ⊗[A] N) y) = y := by
  rw [g_apply, p_tmul, one_smul]

/-- The composite `p ∘ g` is the identity of `N`. -/
theorem p_comp_g : p.comp (g : N →ₗ[A] B ⊗[A] N) = LinearMap.id := by
  ext y
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  exact p_g y

/-- `p` is the unique `A`-linear map sending `b ⊗ y` to `b • y`: this is the universal property
of the tensor product applied to the balanced map `smulBilin`. -/
theorem p_unique {q : B ⊗[A] N →ₗ[A] N} (hq : ∀ (b : B) (y : N), q (b ⊗ₜ[A] y) = b • y) :
    q = p := by
  apply LinearMap.ext
  intro z
  induction z with
  | zero => rw [map_zero, map_zero]
  | tmul b y => rw [hq b y, p_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsScalarTower A B N] [SMulCommClass A B N] in
/-- The reason why `g` is only `A`-linear: on the one hand `g (b • y) = 1 ⊗ (b • y)`, while on the
other hand `b • g y = b ⊗ y`.  These two tensors differ in general (they agree when `b` is in the
image of `A`), which is why the decomposition below is one of `A`-modules only. -/
theorem g_smul_g (b : B) (y : N) :
    (g : N →ₗ[A] B ⊗[A] N) (b • y) = (1 : B) ⊗ₜ[A] (b • y) ∧
      b • ((g : N →ₗ[A] B ⊗[A] N) y) = b ⊗ₜ[A] y := by
  refine ⟨rfl, ?_⟩
  rw [g_apply, smul_tmul_B, smul_eq_mul, mul_one]

/-- `g` is injective: it is a section of `p`. -/
theorem g_injective : Function.Injective (g : N → B ⊗[A] N) := by
  intro y z h
  have h' : p ((g : N →ₗ[A] B ⊗[A] N) y) = p ((g : N →ₗ[A] B ⊗[A] N) z) := by rw [h]
  rwa [p_g, p_g] at h'

/-- `g` has trivial kernel. -/
theorem ker_g : LinearMap.ker (g : N →ₗ[A] B ⊗[A] N) = ⊥ := by
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hy
    apply g_injective (A := A) (B := B)
    rw [hy, map_zero]
  · intro hy
    rw [hy, map_zero]

/-- The decomposition used in the book: `z = g (p z) + (z - g (p z))`, the second summand
lying in the kernel of `p`. -/
theorem z_eq_g_add_ker (z : B ⊗[A] N) :
    z = (g : N →ₗ[A] B ⊗[A] N) (p z) + (z - (g : N →ₗ[A] B ⊗[A] N) (p z)) ∧
      p (z - (g : N →ₗ[A] B ⊗[A] N) (p z)) = 0 := by
  refine ⟨(add_sub_cancel _ _).symm, ?_⟩
  rw [map_sub, p_g, sub_self]

/-- `N_B = g(N) ⊕ ker p`, as `A`-modules. -/
theorem isCompl_range_ker :
    IsCompl (LinearMap.range (g : N →ₗ[A] B ⊗[A] N)) (LinearMap.ker p) where
  disjoint := by
    rw [disjoint_iff_inf_le]
    intro z hz
    rw [Submodule.mem_inf, LinearMap.mem_range] at hz
    obtain ⟨hzr, hzk⟩ := hz
    obtain ⟨y, hy⟩ := hzr
    rw [← hy, LinearMap.mem_ker, p_g] at hzk
    rw [Submodule.mem_bot, ← hy, hzk, map_zero]
  codisjoint := by
    rw [codisjoint_iff, eq_top_iff]
    intro z _
    have hmem : z - (g : N →ₗ[A] B ⊗[A] N) (p z) ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker]
      exact (z_eq_g_add_ker z).2
    have h := Submodule.add_mem_sup (LinearMap.mem_range_self (g : N →ₗ[A] B ⊗[A] N) (p z)) hmem
    rwa [add_sub_cancel] at h

/-- `g(N)` is a direct summand of `N_B`. -/
theorem range_directSummand :
    ∃ q : Submodule A (B ⊗[A] N), IsCompl (LinearMap.range (g : N →ₗ[A] B ⊗[A] N)) q :=
  ⟨LinearMap.ker p, isCompl_range_ker⟩

/-- The retraction `p` splits the inclusion of the direct summand `g(N)`. -/
theorem exists_retraction :
    ∃ r : B ⊗[A] N →ₗ[A] N, ∀ y : N, r ((g : N →ₗ[A] B ⊗[A] N) y) = y :=
  ⟨p, p_g⟩

/-- The projection of `N_B` onto the direct summand `g(N)`, `z ↦ g (p z)`. -/
noncomputable def gProjection : B ⊗[A] N →ₗ[A] B ⊗[A] N :=
  (g : N →ₗ[A] B ⊗[A] N).comp p

theorem gProjection_apply (z : B ⊗[A] N) :
    gProjection z = (g : N →ₗ[A] B ⊗[A] N) (p z) := rfl

theorem gProjection_eq_self {z : B ⊗[A] N} (hz : z ∈ LinearMap.range (g : N →ₗ[A] B ⊗[A] N)) :
    gProjection z = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [gProjection_apply, p_g]

theorem gProjection_isIdempotent :
    (gProjection : B ⊗[A] N →ₗ[A] B ⊗[A] N).comp gProjection = gProjection := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, gProjection_apply, gProjection_apply, p_g]

theorem gProjection_range :
    LinearMap.range (gProjection : B ⊗[A] N →ₗ[A] B ⊗[A] N) =
      LinearMap.range (g : N →ₗ[A] B ⊗[A] N) := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := hz
    exact ⟨p w, (gProjection_apply w).symm⟩
  · intro hz
    exact ⟨z, gProjection_eq_self hz⟩

theorem gProjection_ker :
    LinearMap.ker (gProjection : B ⊗[A] N →ₗ[A] B ⊗[A] N) = LinearMap.ker p := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hz
    have h : p ((gProjection : B ⊗[A] N →ₗ[A] B ⊗[A] N) z) = p (0 : B ⊗[A] N) := by rw [hz]
    rwa [gProjection_apply, p_g, map_zero] at h
  · intro hz
    rw [gProjection_apply, hz, map_zero]

/-- `p` is `B`-linear, where `B` acts on the left factor of `N_B = B ⊗[A] N`. -/
theorem p_smul (b : B) (z : B ⊗[A] N) : p (b • z) = b • p z := by
  induction z with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b' y => rw [smul_tmul_B, p_tmul, p_tmul, IsScalarTower.smul_assoc b b' y]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `p` as a `B`-linear map. -/
noncomputable def pB : B ⊗[A] N →ₗ[B] N where
  toFun := p
  map_add' := map_add p
  map_smul' := p_smul

theorem pB_apply (z : B ⊗[A] N) : pB z = p z := rfl

end General

section RingHom

variable {A B N : Type*} [CommRing A] [CommRing B]

set_option linter.style.haveILetI false in
/-- **Atiyah–Macdonald, Exercise 2.13.**  Let `f : A →+* B` be a ring homomorphism and let `N` be
a `B`-module, regarded as an `A`-module by restriction of scalars.  Then the homomorphism
`g : N → B ⊗[A] N`, `y ↦ 1 ⊗ y`, is injective and its image is a direct summand of `B ⊗[A] N`. -/
theorem exercise_2_13 (f : A →+* B) (N : Type*) [AddCommGroup N] [Module B N] :
    letI : Algebra A B := f.toAlgebra
    letI : Module A N := Module.compHom N f
    Function.Injective (fun y : N => (1 : B) ⊗ₜ[A] y) ∧
      ∃ q : Submodule A (B ⊗[A] N),
        IsCompl (LinearMap.range (TensorProduct.mk A B N (1 : B))) q := by
  letI : Algebra A B := f.toAlgebra
  letI : Module A N := Module.compHom N f
  haveI hST : IsScalarTower A B N :=
    ⟨fun a b n => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  haveI hSC : SMulCommClass A B N :=
    ⟨fun a b n => by
      show f a • (b • n) = b • (f a • n)
      exact smul_comm (f a) b n⟩
  have hg := g_injective (A := A) (B := B) (N := N)
  refine ⟨?_, ?_⟩
  · intro y z h
    exact hg h
  · exact ⟨LinearMap.ker (p (A := A) (B := B) (N := N)), isCompl_range_ker⟩

end RingHom





/-! ### Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_2_13.exercise_2_13
#print axioms AtiyahMcdonald69.Ex_2_13.g_injective
#print axioms AtiyahMcdonald69.Ex_2_13.isCompl_range_ker
#print axioms AtiyahMcdonald69.Ex_2_13.range_directSummand
#print axioms AtiyahMcdonald69.Ex_2_13.p_smul
#print axioms AtiyahMcdonald69.Ex_2_13.p_tmul
#print axioms AtiyahMcdonald69.Ex_2_13.z_eq_g_add_ker
#print axioms AtiyahMcdonald69.Ex_2_13.exists_retraction
#print axioms AtiyahMcdonald69.Ex_2_13.p_unique
#print axioms AtiyahMcdonald69.Ex_2_13.g_smul_g

end AtiyahMcdonald69.Ex_2_13
