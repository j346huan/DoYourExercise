/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter 6 ("Chain Conditions"), Exercise 10.

Book statement (verbatim):
  "Let M be a Noetherian A-module. Show that Supp(M) is a closed Noetherian subspace of Spec(A)."

Reference site (human-language proof, public source j346huan commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-10

Source audit.  The reference proof is:
  * `Supp(M) = V(Ann(M))` (3.19) — needs `M` finitely generated, which holds because a Noetherian
    module is finitely generated (Mathlib: `Module.support_eq_zeroLocus` under `Module.Finite`);
  * `V(Ann M)` is homeomorphic to `Spec(A ⧸ Ann M)` — in Mathlib the map
    `Spec (A ⧸ Ann M) → Spec A` (`PrimeSpectrum.comap`) is a closed embedding with range `V(Ann M)`
    (root-level lemma `range_comap_of_surjective`);
  * `A ⧸ Ann M` is a Noetherian ring (6.4), so its spectrum is a Noetherian space.

No step needs an unstated hypothesis: in particular `A` itself need *not* be Noetherian, and the
exercise does not assume it.  The only substantive point is the third one: for a Noetherian
`A`-module `M`, the ring `A ⧸ Ann M` is Noetherian.  Because `M` is finitely generated, say by
`m₁, …, mₙ`, the map `A → Mⁿ`, `a ↦ (a m₁, …, a mₙ)` is `A`-linear with kernel `Ann M`; hence
`A ⧸ Ann M` embeds `A`-linearly into the Noetherian `A`-module `Mⁿ`, so it is a Noetherian
`A`-module, hence (its ideals are `A`-submodules) a Noetherian ring.  This is proved below as
`isNoetherianRing_quot_annihilator`; note that it cannot be replaced by "a quotient of a
Noetherian ring is Noetherian" since `A` is not assumed Noetherian.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_6_10

open PrimeSpectrum TopologicalSpace

/-- Exercise 6.4-flavoured ingredient of Exercise 6.10: if `M` is a Noetherian `R`-module then
`R ⧸ Ann(M)` is a Noetherian ring.  (Equivalently: a Noetherian `R`-module is a faithful Noetherian
module over `R ⧸ Ann(M)`.) -/
theorem isNoetherianRing_quot_annihilator (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] [IsNoetherian R M] : IsNoetherianRing (R ⧸ Module.annihilator R M) := by
  classical
  -- Step 1: `R ⧸ Ann M` is a Noetherian `R`-module: it embeds into `M^n` for `n` generators of `M`.
  have hfin : IsNoetherian R (R ⧸ Module.annihilator R M) := by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Finite R M)
    -- evaluation of scalars on a generating family
    let φ : R →ₗ[R] (s → M) :=
      { toFun := fun r i => r • (i : M)
        map_add' := fun a b => by
          funext i
          simp [add_smul]
        map_smul' := fun a b => by
          funext i
          simp [mul_smul] }
    have hφ : ∀ r : R, φ r = 0 ↔ ∀ i : s, r • (i : M) = 0 := by
      intro r
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        funext i
        exact h i
    have hmem : ∀ r : R, r ∈ Module.annihilator R M ↔ ∀ i : s, r • (i : M) = 0 := by
      intro r
      rw [← Submodule.annihilator_top (M := M), ← hs, Submodule.mem_annihilator_span]
      exact Iff.rfl
    have hker : LinearMap.ker φ = Module.annihilator R M := by
      ext r
      rw [LinearMap.mem_ker, hφ r]
      exact (hmem r).symm
    have e : (R ⧸ Module.annihilator R M) ≃ₗ[R] LinearMap.range φ :=
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ LinearMap.quotKerEquivRange φ
    exact isNoetherian_of_linearEquiv e.symm
  -- Step 2: `R ⧸ Ann M` is a Noetherian ring, i.e. Noetherian as a module over itself.
  exact isNoetherian_of_tower R hfin

/-- Atiyah–Macdonald, Exercise 6.10: for a Noetherian `A`-module `M`, the support `Supp(M)` is a
closed Noetherian subspace of `Spec(A)`. -/
theorem solution (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M] :
    IsClosed (Module.support R M) ∧ NoetherianSpace ↥(Module.support R M) := by
  refine ⟨?_, ?_⟩
  · -- closedness: `Supp M = V(Ann M)`
    rw [Module.support_eq_zeroLocus]
    exact PrimeSpectrum.isClosed_zeroLocus _
  · -- `V(Ann M)` is the range of the closed embedding `Spec (R ⧸ Ann M) → Spec R`
    haveI : IsNoetherianRing (R ⧸ Module.annihilator R M) := isNoetherianRing_quot_annihilator R M
    have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Module.annihilator R M)))
        = PrimeSpectrum.zeroLocus (Module.annihilator R M) := by
      rw [range_comap_of_surjective (R ⧸ Module.annihilator R M) (Ideal.Quotient.mk _)
        Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    rw [Module.support_eq_zeroLocus, ← hrange]
    exact NoetherianSpace.range _ (PrimeSpectrum.continuous_comap _)

end AtiyahMcdonald69.Ex_6_10

#print axioms AtiyahMcdonald69.Ex_6_10.solution
#print axioms AtiyahMcdonald69.Ex_6_10.isNoetherianRing_quot_annihilator
