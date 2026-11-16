/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 2 (Modules), Exercise 25 (p. 34 of the book):

  Let `0 → N' → N → N'' → 0` be an exact sequence of `A`-modules, with `N''` flat.
  Then `N'` is flat if and only if `N` is flat.

This file gives a complete, Tor-free formalisation of that statement.

Main results:

* `rTensor_injective_of_flat_coker` — the horseshoe ("3 × 3") step: if
  `0 → M1 → M2 → M → 0` is exact and `M` is flat, then for every module `Q` the map
  `M1 ⊗ Q → M2 ⊗ Q` is injective (i.e. tensoring the sequence with `Q` stays exact on the
  left).
* `flat_of_flat_of_flat_coker`    — `N'` flat and `N''` flat imply `N` flat.
* `flat_of_flat_of_flat_quotient` — `N` flat and `N''` flat imply `N'` flat.
* `flat_iff_flat_of_exact`        — Exercise 2.25.
* `flat_iff_flat_of_submodule_quotient` — the same statement for a submodule `M ≤ N`
  and the quotient `N ⧸ M`.

The only input is the characterisation of flatness as preservation of injectivity under
tensoring (`Module.Flat.rTensor_preserves_injective_linearMap`,
`Module.Flat.lTensor_preserves_injective_linearMap`) together with right exactness of the
tensor product (`lTensor_exact`, `rTensor_exact`).

Note on the "natural" proof by Tor: it is correct but far from self-contained — it needs the
Tor functor, its long exact sequence in both variables, the symmetry `Tor₁(M, N) ≃ Tor₁(N, M)`
and Exercise 2.24, none of which is developed in the book (which does not mention Tor at all
before Exercise 2.24, where it is merely quoted).  In particular the step
`Tor₂(M, N'') = 0 → Tor₁(M, N') ≃ Tor₁(M, N)` is the only place where flatness of `N''` is
used, and the appeal to "symmetry of Tor" hides a nontrivial theorem.  The proof below
replaces all of it by two short element chases plus one horseshoe argument.

Hypothesis audit: flatness of `N''` cannot be dropped from the second direction: for
`A = k[x,y]`, `N = A` (flat), `N' = (x,y)` and `N'' = k` the sequence
`0 → (x,y) → A → k → 0` is exact, `N` is flat, but `N'` is not flat (it is finitely
generated and not projective over the Noetherian ring `k[x,y]`).
-/
import Mathlib.RingTheory.Flat.Basic

universe u

namespace AtiyahMcdonald69.Ex_2_25

open TensorProduct LinearMap

variable {R : Type u} [CommRing R]

/-! ### The horseshoe step -/

/-- Auxiliary lemma (the horseshoe/3 × 3 step, in the general form with a prescribed cover
`F → Q` of the test module): if `0 → M1 → M2 → M → 0` is exact and `M` is flat, then
`M1 ⊗ Q → M2 ⊗ Q` is injective.

Choose `P` with `0 → P → F → Q → 0` exact and `F` free.  Three right exact rows are compared;
the crucial point is that `P ⊗ M → F ⊗ M` is injective (flatness of `M`) and that
`M1 ⊗ F → M2 ⊗ F` is injective (flatness of `F`). -/
theorem rTensor_injective_of_flat_coker_aux
    {M1 M2 M F Q : Type u} [AddCommGroup M1] [Module R M1] [AddCommGroup M2] [Module R M2]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup Q] [Module R Q]
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M) (hf : Function.Injective f)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (π : F →ₗ[R] Q) (hπ : Function.Surjective π) :
    Function.Injective (f.rTensor Q) := by
  let P : Submodule R F := LinearMap.ker π
  have hexP : Function.Exact P.subtype π := by
    intro y
    exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  have hπ0 : π.comp P.subtype = 0 := by
    ext x
    exact x.2
  -- the two ways of forming `f ⊗ π` agree
  have hcomm : (f.rTensor Q).comp (π.lTensor M1) = (π.lTensor M2).comp (f.rTensor F) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hsq : (P.subtype.lTensor M).comp (g.rTensor P) =
      (g.rTensor F).comp (P.subtype.lTensor M2) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hsq2 : (P.subtype.lTensor M2).comp (f.rTensor P) =
      (f.rTensor F).comp (P.subtype.lTensor M1) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hgf : g.comp f = 0 := hex.linearMap_comp_eq_zero
  have hinjF : Function.Injective (f.rTensor F) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hinjM : Function.Injective (P.subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap P.subtype P.subtype_injective
  have key : ∀ x : M1 ⊗[R] Q, (f.rTensor Q) x = 0 → x = 0 := by
    intro x hx
    obtain ⟨xt, rfl⟩ := LinearMap.lTensor_surjective M1 (g := π) hπ x
    -- the image of `xt` in `M2 ⊗ F` lands in the range of `M2 ⊗ P → M2 ⊗ F`
    have h1 : (π.lTensor M2) ((f.rTensor F) xt) = 0 := by
      have hc := congrArg (fun k : M1 ⊗[R] F →ₗ[R] M2 ⊗[R] Q => k xt) hcomm
      simp only [LinearMap.comp_apply] at hc
      rw [← hc]
      exact hx
    obtain ⟨y, hy⟩ :=
      (lTensor_exact M2 (f := P.subtype) (g := π) hexP hπ) ((f.rTensor F) xt) |>.mp h1
    -- applying `g` lands in the range of `M ⊗ P → M ⊗ F`, whence it vanishes
    have h2 : (P.subtype.lTensor M) ((g.rTensor P) y) = 0 := by
      have hc := congrArg (fun k : M2 ⊗[R] P →ₗ[R] M ⊗[R] F => k y) hsq
      simp only [LinearMap.comp_apply] at hc
      rw [hc, hy, ← LinearMap.rTensor_comp_apply, hgf, LinearMap.rTensor_zero]
      rfl
    have h3 : (g.rTensor P) y = 0 := by
      apply hinjM
      exact h2.trans (map_zero _).symm
    obtain ⟨y', hy'⟩ := (rTensor_exact P (f := f) (g := g) hex hg) y |>.mp h3
    -- conclude
    have h4 : (f.rTensor F) ((P.subtype.lTensor M1) y') = (f.rTensor F) xt := by
      have hc := congrArg (fun k : M1 ⊗[R] P →ₗ[R] M2 ⊗[R] F => k y') hsq2
      simp only [LinearMap.comp_apply] at hc
      rw [← hc, hy', hy]
    have h5 : (P.subtype.lTensor M1) y' = xt := hinjF h4
    rw [← h5, ← LinearMap.lTensor_comp_apply, hπ0, LinearMap.lTensor_zero]
    rfl
  intro x y hxy
  have h0 : (f.rTensor Q) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

set_option linter.style.haveILetI false in
/-- If `0 → M1 → M2 → M → 0` is exact and `M` is flat, then for every module `Q` the map
`M1 ⊗ Q → M2 ⊗ Q` is injective. -/
theorem rTensor_injective_of_flat_coker
    {M1 M2 M : Type u} [AddCommGroup M1] [Module R M1] [AddCommGroup M2] [Module R M2]
    [AddCommGroup M] [Module R M]
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M) (hf : Function.Injective f)
    (hex : Function.Exact f g) (hg : Function.Surjective g) (hM : Module.Flat R M)
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective (f.rTensor Q) := by
  haveI := hM
  refine rTensor_injective_of_flat_coker_aux f g hf hex hg
    (Finsupp.linearCombination R (_root_.id : Q → Q)) ?_
  intro q
  exact ⟨Finsupp.single q 1, by simp⟩

/-! ### The two directions of Exercise 2.25 -/

set_option linter.style.haveILetI false in
/-- Flatness is stable under extensions: if `0 → N1 → N2 → N3 → 0` is exact and `N1`, `N3`
are flat, then `N2` is flat. -/
theorem flat_of_flat_of_flat_coker
    {N1 N2 N3 : Type u} [AddCommGroup N1] [Module R N1] [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (f : N1 →ₗ[R] N2) (g : N2 →ₗ[R] N3) (hf : Function.Injective f)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (h1 : Module.Flat R N1) (h3 : Module.Flat R N3) : Module.Flat R N2 := by
  haveI := h1
  haveI := h3
  refine Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr ?_
  intro A B _ _ _ _ u hu
  have hexA : Function.Exact (f.lTensor A) (g.lTensor A) :=
    lTensor_exact A (f := f) (g := g) hex hg
  have hsqA : (u.rTensor N3).comp (g.lTensor A) = (g.lTensor B).comp (u.rTensor N2) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hsqB : (f.lTensor B).comp (u.rTensor N1) = (u.rTensor N2).comp (f.lTensor A) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hinjN3 : Function.Injective (u.rTensor N3) :=
    Module.Flat.rTensor_preserves_injective_linearMap u hu
  have hinjN1 : Function.Injective (u.rTensor N1) :=
    Module.Flat.rTensor_preserves_injective_linearMap u hu
  -- here flatness of the quotient `N3` is used, through the horseshoe lemma
  have hinjfB : Function.Injective (f.lTensor B) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj (f := f) B).2
      (rTensor_injective_of_flat_coker f g hf hex hg h3 B)
  have key : ∀ z : A ⊗[R] N2, (u.rTensor N2) z = 0 → z = 0 := by
    intro z hz
    have h1 : (g.lTensor A) z = 0 := by
      have hc := congrArg (fun k : A ⊗[R] N2 →ₗ[R] B ⊗[R] N3 => k z) hsqA
      simp only [LinearMap.comp_apply] at hc
      have h2 : (u.rTensor N3) ((g.lTensor A) z) = 0 := by rw [hc, hz, map_zero]
      exact hinjN3 (by rw [h2, map_zero])
    obtain ⟨w, hw⟩ := (hexA z).mp h1
    have h3 : (u.rTensor N1) w = 0 := by
      have hc := congrArg (fun k : A ⊗[R] N1 →ₗ[R] B ⊗[R] N2 => k w) hsqB
      simp only [LinearMap.comp_apply] at hc
      have h4 : (f.lTensor B) ((u.rTensor N1) w) = 0 := by rw [hc, hw, hz]
      exact hinjfB (by rw [h4, map_zero])
    have hw0 : w = 0 := hinjN1 (by rw [h3, map_zero])
    rw [← hw, hw0, map_zero]
  intro x y hxy
  have h0 : (u.rTensor N2) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

set_option linter.style.haveILetI false in
/-- If `0 → N1 → N2 → N3 → 0` is exact and `N2`, `N3` are flat, then `N1` is flat. -/
theorem flat_of_flat_of_flat_quotient
    {N1 N2 N3 : Type u} [AddCommGroup N1] [Module R N1] [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (f : N1 →ₗ[R] N2) (g : N2 →ₗ[R] N3) (hf : Function.Injective f)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (h2 : Module.Flat R N2) (h3 : Module.Flat R N3) : Module.Flat R N1 := by
  haveI := h2
  haveI := h3
  refine Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr ?_
  intro A B _ _ _ _ u hu
  have hinjN2 : Function.Injective (u.rTensor N2) :=
    Module.Flat.rTensor_preserves_injective_linearMap u hu
  -- here flatness of the quotient `N3` is used, through the horseshoe lemma
  have hinjfA : Function.Injective (f.lTensor A) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj (f := f) A).2
      (rTensor_injective_of_flat_coker f g hf hex hg h3 A)
  have hsq : (u.rTensor N2).comp (f.lTensor A) = (f.lTensor B).comp (u.rTensor N1) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have key : ∀ z : A ⊗[R] N1, (u.rTensor N1) z = 0 → z = 0 := by
    intro z hz
    have h1 : (f.lTensor A) z = 0 := by
      have hc := congrArg (fun k : A ⊗[R] N1 →ₗ[R] B ⊗[R] N2 => k z) hsq
      simp only [LinearMap.comp_apply] at hc
      have h2 : (u.rTensor N2) ((f.lTensor A) z) = 0 := by rw [hc, hz, map_zero]
      exact hinjN2 (by rw [h2, map_zero])
    exact hinjfA (by rw [h1, map_zero])
  intro x y hxy
  have h0 : (u.rTensor N1) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

/-! ### Exercise 2.25 -/

/-- **Atiyah–Macdonald, Chapter 2, Exercise 25.** Let `0 → N' → N → N'' → 0` be an exact
sequence of `A`-modules with `N''` flat. Then `N'` is flat if and only if `N` is flat. -/
theorem flat_iff_flat_of_exact
    {N' N N'' : Type u} [AddCommGroup N'] [Module R N'] [AddCommGroup N] [Module R N]
    [AddCommGroup N''] [Module R N'']
    (f : N' →ₗ[R] N) (g : N →ₗ[R] N'') (hf : Function.Injective f)
    (hex : Function.Exact f g) (hg : Function.Surjective g) (h : Module.Flat R N'') :
    Module.Flat R N' ↔ Module.Flat R N :=
  ⟨fun h' => flat_of_flat_of_flat_coker f g hf hex hg h' h,
   fun hN => flat_of_flat_of_flat_quotient f g hf hex hg hN h⟩

set_option linter.style.haveILetI false in
/-- Exercise 2.25 in the submodule/quotient form: if `N ⧸ M` is flat, then `M` is flat if
and only if `N` is flat. -/
theorem flat_iff_flat_of_submodule_quotient
    {N : Type u} [AddCommGroup N] [Module R N] (M : Submodule R N)
    [Module.Flat R (N ⧸ M)] :
    Module.Flat R M ↔ Module.Flat R N :=
  flat_iff_flat_of_exact M.subtype M.mkQ M.subtype_injective
    (LinearMap.exact_subtype_mkQ M) (Submodule.mkQ_surjective M) ‹Module.Flat R (N ⧸ M)›

end AtiyahMcdonald69.Ex_2_25

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_2_25.rTensor_injective_of_flat_coker
#print axioms AtiyahMcdonald69.Ex_2_25.flat_of_flat_of_flat_coker
#print axioms AtiyahMcdonald69.Ex_2_25.flat_of_flat_of_flat_quotient
#print axioms AtiyahMcdonald69.Ex_2_25.flat_iff_flat_of_exact
#print axioms AtiyahMcdonald69.Ex_2_25.flat_iff_flat_of_submodule_quotient
