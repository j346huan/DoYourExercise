/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 5.12

*Statement (Chapter 5, Exercise 12).* Let `G` be a finite group of automorphisms of a ring `A`,
and let `A^G` denote the subring of `G`-invariants, i.e. of all `x ∈ A` with `σ x = x` for all
`σ ∈ G`.

1. `A` is integral over `A^G`.
2. Let `S ⊆ A` be a multiplicatively closed subset (a submonoid) with `σ(S) ⊆ S` for all
   `σ ∈ G`, and put `S^G = S ∩ A^G`. Then the action of `G` on `A` extends to an action of `G`
   on `S⁻¹A`, and `(S^G)⁻¹A^G ≃ (S⁻¹A)^G`.

Formalization choices.

* A "group of automorphisms of `A`" is encoded as `[Group G] [MulSemiringAction G A]`: every
  `g : G` acts by a ring automorphism `MulSemiringAction.toRingEquiv G A g` (the action need not
  be faithful; an unfaithful action is an action of a quotient, so nothing is lost).
  Finiteness is `[Fintype G]`; see `isIntegral_invariants_of_finite` for the `Finite` form.
* `A^G` is Mathlib's `FixedPoints.subring A G`; `S^G` is `fixedSubmonoid G S`, the pullback of `S`
  along `A^G ⊆ A` (so `mem_fixedSubmonoid` is the statement `S^G = S ∩ A^G`).
* The action on the localization is `localizationAct`/the instance
  `MulSemiringAction G (Localization S)`; `smul_algebraMap` says it extends the given action, and
  `smul_mk'` records that `g • (a/s) = (g • a)/(g • s)`.
* The isomorphism `(S^G)⁻¹A^G ≃ (S⁻¹A)^G` is `fixedLocalizationEquiv`. It is obtained by proving
  that `(S⁻¹A)^G` *is* the localization of `A^G` at `S^G` (`isLocalization_fixed`), which is the
  invariant content of the statement; `fixedLocalizationEquiv_algebraMap` records that the
  isomorphism is the canonical one.

The proof of part (3) is the textbook one: write `z ∈ S⁻¹A` as `a/s`, multiply numerator and
denominator by the conjugates of `s` to get a `G`-invariant denominator `d = ∏_σ σ(s)`, then
average the multipliers that make the numerator invariant over the group.

All results below are proved unconditionally (no `sorry`, no new axioms); `#print axioms` at the
end of the file confirms that only the standard Lean axioms are used.
-/

open Polynomial

namespace AtiyahMcdonald69.Ex_5_12

section Integral

variable {A : Type*} [CommRing A]
variable {G : Type*} [Group G] [MulSemiringAction G A]

/-- The fixed subring `A^G` of the group of automorphisms `G` of `A`. -/
abbrev invariants : Subring A := FixedPoints.subring A G

theorem mem_invariants (x : A) : x ∈ invariants (A := A) (G := G) ↔ ∀ g : G, g • x = x :=
  Iff.rfl

variable [Fintype G]

/-- **Exercise 5.12 (1)**: every element of `A` is integral over `A^G`. It is a root of the monic
polynomial `∏_{σ ∈ G} (T - σ x)`, whose coefficients are fixed by `G`. -/
theorem isIntegral_invariants (x : A) : IsIntegral ↥(invariants (A := A) (G := G)) x := by
  have hmem : MulSemiringAction.charpoly G x ∈
      Polynomial.lifts (Subring.subtype (invariants (A := A) (G := G))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, MulSemiringAction.smul_coeff_charpoly x n⟩, rfl⟩
  obtain ⟨q, hq, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hmem (MulSemiringAction.monic_charpoly G x)
  refine ⟨q, hqmonic, ?_⟩
  have halg : (algebraMap ↥(invariants (A := A) (G := G)) A) =
      Subring.subtype (invariants (A := A) (G := G)) := rfl
  rw [halg, ← Polynomial.eval_map, hq, MulSemiringAction.eval_charpoly]

/-- **Exercise 5.12 (1)**, as an integral extension. -/
theorem isIntegral_invariants_iff : Algebra.IsIntegral ↥(invariants (A := A) (G := G)) A :=
  ⟨isIntegral_invariants⟩

end Integral

variable {A : Type*} [CommRing A]
variable {G : Type*} [Group G] [MulSemiringAction G A]

section Localization

variable (S : Submonoid A)

/-- A submonoid `S` is stable under the group action if `σ(S) ⊆ S` for all `σ ∈ G`. -/
class Submonoid.GStable : Prop where
  smul_mem : ∀ (g : G) {s : A}, s ∈ S → g • s ∈ S

theorem map_toRingEquiv [Submonoid.GStable (G := G) S] (g : G) :
    S.map (MulSemiringAction.toRingEquiv G A g).toMonoidHom = S := by
  refine le_antisymm ?_ ?_
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hs
    exact Submonoid.GStable.smul_mem g ht
  · intro s hs
    refine Submonoid.mem_map.mpr ⟨(MulSemiringAction.toRingEquiv G A g).symm s, ?_, ?_⟩
    · rw [MulSemiringAction.toRingEquiv_apply_symm_apply]
      exact Submonoid.GStable.smul_mem (G := G) g⁻¹ hs
    · exact RingEquiv.apply_symm_apply _ s

/-- The action of `G` on `A` extends to an action of `G` on the localization `S⁻¹A`. -/
noncomputable def localizationAct [Submonoid.GStable (G := G) S] :
    G →* (Localization S ≃+* Localization S) where
  toFun g := IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
    (MulSemiringAction.toRingEquiv G A g) (map_toRingEquiv S g)
  map_one' := by
    refine RingEquiv.ext fun x => ?_
    have key : ((IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
        (MulSemiringAction.toRingEquiv G A 1) (map_toRingEquiv S 1)) :
          Localization S →+* Localization S) = 1 := by
      refine IsLocalization.ringHom_ext (M := S) ?_
      ext a
      simp
    exact RingHom.congr_fun key x
  map_mul' g h := by
    refine RingEquiv.ext fun x => ?_
    have key : ((IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
        (MulSemiringAction.toRingEquiv G A (g * h)) (map_toRingEquiv S (g * h))) :
          Localization S →+* Localization S) =
        ((IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
          (MulSemiringAction.toRingEquiv G A g) (map_toRingEquiv S g)) :
            Localization S →+* Localization S) *
        ((IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
          (MulSemiringAction.toRingEquiv G A h) (map_toRingEquiv S h)) :
            Localization S →+* Localization S) := by
      refine IsLocalization.ringHom_ext (M := S) ?_
      ext a
      simp [map_mul]
    exact RingHom.congr_fun key x

attribute [instance_reducible] localizationAct

/-- The `MulSemiringAction` of `G` on `S⁻¹A`. -/
noncomputable instance [Submonoid.GStable (G := G) S] :
    MulSemiringAction G (Localization S) :=
  MulSemiringAction.compHom (Localization S) (localizationAct S)

/-- The extended action restricts to the original action on `A`: this is what it means for the
action on the localization to *extend* the action on `A`. -/
theorem smul_algebraMap [Submonoid.GStable (G := G) S] (g : G) (a : A) :
    g • algebraMap A (Localization S) a = algebraMap A (Localization S) (g • a) := by
  have h1 : g • (algebraMap A (Localization S) a) =
      (IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
        (MulSemiringAction.toRingEquiv G A g) (map_toRingEquiv S g))
        (algebraMap A (Localization S) a) := rfl
  rw [h1, IsLocalization.ringEquivOfRingEquiv_eq (j := MulSemiringAction.toRingEquiv G A g)
    (map_toRingEquiv S g) a, MulSemiringAction.toRingEquiv_apply_apply]

/-- The action on the localization sends a fraction `a/s` to `(g • a)/(g • s)`. -/
theorem smul_mk' [Submonoid.GStable (G := G) S] (g : G) (a : A) (s : S) :
    g • IsLocalization.mk' (Localization S) a s =
      IsLocalization.mk' (Localization S) (g • a)
        ⟨g • (s : A), Submonoid.GStable.smul_mem g s.2⟩ := by
  have h1 : g • IsLocalization.mk' (Localization S) a s =
      (IsLocalization.ringEquivOfRingEquiv (Localization S) (Localization S)
        (MulSemiringAction.toRingEquiv G A g) (map_toRingEquiv S g))
        (IsLocalization.mk' (Localization S) a s) := rfl
  rw [h1, IsLocalization.ringEquivOfRingEquiv_mk']
  simp only [MulSemiringAction.toRingEquiv_apply_apply]

end Localization


section FixedLocalization

variable (S : Submonoid A)

/-- `S^G = S ∩ A^G`, viewed as a submonoid of the fixed subring `A^G`. -/
def fixedSubmonoid (G : Type*) [Group G] [MulSemiringAction G A] (S : Submonoid A) :
    Submonoid ↥(FixedPoints.subring A G) :=
  S.comap (Subring.subtype (FixedPoints.subring A G))

@[simp]
theorem mem_fixedSubmonoid {x : ↥(FixedPoints.subring A G)} :
    x ∈ fixedSubmonoid G S ↔ (x : A) ∈ S := Iff.rfl

variable [Submonoid.GStable (G := G) S]

/-- The `A^G`-algebra structure on `(S⁻¹A)^G`, via `x ↦ x/1`. -/
def invariantsToFixed (G : Type*) [Group G] [MulSemiringAction G A]
    (S : Submonoid A) [Submonoid.GStable (G := G) S] :
    ↥(FixedPoints.subring A G) →+* ↥(FixedPoints.subring (Localization S) G) where
  toFun x := ⟨algebraMap A (Localization S) (x : A), by
    intro g
    rw [smul_algebraMap, x.2 g]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- `(S⁻¹A)^G` as an algebra over `A^G`. -/
@[instance_reducible]
noncomputable def fixedAlgebra :
    Algebra ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) :=
  (invariantsToFixed G S).toAlgebra

attribute [local instance] fixedAlgebra

theorem fixed_algebraMap_apply (x : ↥(FixedPoints.subring A G)) :
    algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) x =
      ⟨algebraMap A (Localization S) (x : A), by
        intro g
        rw [smul_algebraMap, x.2 g]⟩ := rfl

include S in
theorem fixed_map_units (y : fixedSubmonoid G S) :
    IsUnit (algebraMap ↥(FixedPoints.subring A G)
      ↥(FixedPoints.subring (Localization S) G) (y : ↥(FixedPoints.subring A G))) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := S) (S := Localization S)
    (y := (⟨((y : ↥(FixedPoints.subring A G)) : A), y.2⟩ : S))
  have hfix : ∀ g : G, g • (u : Localization S) = (u : Localization S) := by
    intro g
    rw [hu, smul_algebraMap, (y : ↥(FixedPoints.subring A G)).2 g]
  -- uniqueness of the right inverse of a unit
  have huniq : ∀ b : Localization S, (u : Localization S) * b = 1 →
      b = ((u⁻¹ : (Localization S)ˣ) : Localization S) := by
    intro b hb
    calc b = b * ((u : Localization S) * ((u⁻¹ : (Localization S)ˣ) : Localization S)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((u : Localization S) * b) * ((u⁻¹ : (Localization S)ˣ) : Localization S) := by ring
      _ = ((u⁻¹ : (Localization S)ˣ) : Localization S) := by rw [hb, one_mul]
  have hfixinv : ∀ g : G, g • ((u⁻¹ : (Localization S)ˣ) : Localization S) =
      ((u⁻¹ : (Localization S)ˣ) : Localization S) := by
    intro g
    refine huniq _ ?_
    rw [← hfix g, ← smul_mul', Units.mul_inv, smul_one]
  refine IsUnit.of_mul_eq_one ⟨((u⁻¹ : (Localization S)ˣ) : Localization S), fun g => by
    rw [hfixinv g]⟩ (Subtype.ext ?_)
  show algebraMap A (Localization S) ((y : ↥(FixedPoints.subring A G)) : A) *
    ((u⁻¹ : (Localization S)ˣ) : Localization S) = 1
  rw [← hu]
  exact Units.mul_inv u

variable [Fintype G]

/-- Every `G`-invariant element of `S⁻¹A` is a fraction with `G`-invariant numerator and
denominator. -/
theorem fixed_surj (z : ↥(FixedPoints.subring (Localization S) G)) :
    ∃ x : ↥(FixedPoints.subring A G) × fixedSubmonoid G S,
      z * algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G)
          (x.2 : ↥(FixedPoints.subring A G)) =
        algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) x.1 := by
  classical
  obtain ⟨a, s, hz⟩ := IsLocalization.exists_mk'_eq (M := S) (S := Localization S) (z : Localization S)
  set P : A := ∏ g : G, g • (s : A) with hP
  have hPmem : P ∈ S := Submonoid.prod_mem S (fun g _ => Submonoid.GStable.smul_mem g s.2)
  have hPfixed : ∀ g : G, g • P = P := fun g => Finset.smul_prod_perm (s : A) g
  set a₁ : A := a * ∏ g ∈ Finset.univ.erase (1 : G), g • (s : A) with ha₁
  have hsplit : P = (s : A) * ∏ g ∈ Finset.univ.erase (1 : G), g • (s : A) := by
    rw [hP, ← Finset.mul_prod_erase (Finset.univ) (fun g : G => g • (s : A)) (Finset.mem_univ 1),
      one_smul]
  have hz₁ : IsLocalization.mk' (Localization S) a₁ ⟨P, hPmem⟩ = z := by
    rw [← hz, IsLocalization.mk'_eq_iff_eq]
    have heq : (s : A) * a₁ = P * a := by
      rw [ha₁, hsplit]; ring
    rw [heq]
  -- For every `g` there is `t ∈ S` annihilating `a₁ - g • a₁`.
  have hkey : ∀ g : G, ∃ t ∈ S, t * (a₁ - g • a₁) = 0 := by
    intro g
    have hgz : IsLocalization.mk' (Localization S) (g • a₁)
        ⟨g • P, Submonoid.GStable.smul_mem g hPmem⟩ =
        IsLocalization.mk' (Localization S) a₁ ⟨P, hPmem⟩ := by
      rw [← smul_mk' (S := S) g a₁ ⟨P, hPmem⟩, hz₁]
      exact z.2 g
    have hPsub : (⟨g • P, Submonoid.GStable.smul_mem g hPmem⟩ : S) = ⟨P, hPmem⟩ :=
      Subtype.ext (hPfixed g)
    rw [hPsub] at hgz
    rw [IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (M := S)] at hgz
    obtain ⟨c, hc⟩ := hgz
    refine ⟨(c : A) * P, S.mul_mem c.2 hPmem, ?_⟩
    have hc' : (c : A) * P * (g • a₁) = (c : A) * P * a₁ := by
      have hc₂ : (c : A) * (P * (g • a₁)) = (c : A) * (P * a₁) := hc
      rw [mul_assoc (c : A) P, mul_assoc (c : A) P]
      exact hc₂
    rw [mul_sub, hc', sub_self]
  choose t htS htann using hkey
  -- Averaging over the group to make the multiplier invariant.
  set T : A := ∏ g : G, t g with hT
  set c : A := ∏ g : G, g • T with hc
  have hTmem : T ∈ S := Submonoid.prod_mem S (fun g _ => htS g)
  have hcmem : c ∈ S := Submonoid.prod_mem S (fun g _ => Submonoid.GStable.smul_mem g hTmem)
  have hcfixed : ∀ g : G, g • c = c := fun g => Finset.smul_prod_perm T g
  have hTann : ∀ g : G, T * (a₁ - g • a₁) = 0 := by
    intro g
    rw [hT, ← Finset.prod_erase_mul (Finset.univ) t (Finset.mem_univ g), mul_assoc, htann g,
      mul_zero]
  have hcann : ∀ g : G, c * (a₁ - g • a₁) = 0 := by
    intro g
    rw [hc, ← Finset.prod_erase_mul (Finset.univ) (fun τ : G => τ • T) (Finset.mem_univ g),
      mul_assoc]
    have h3 : (g • T) * (a₁ - g • a₁) = 0 := by
      have h2 : (g • T) * (g • a₁ - a₁) = 0 := by
        have h := congrArg (fun x : A => g • x) (hTann g⁻¹)
        simpa [smul_sub, inv_smul_smul] using h
      have : a₁ - g • a₁ = -(g • a₁ - a₁) := by ring
      rw [this, mul_neg, h2, neg_zero]
    rw [h3, mul_zero]
  have hnumfixed : c * a₁ ∈ FixedPoints.subring A G := by
    intro g
    show g • (c * a₁) = c * a₁
    rw [smul_mul', hcfixed g]
    have h : c * a₁ = c * (g • a₁) := by
      have := hcann g
      rw [mul_sub, sub_eq_zero] at this
      exact this
    rw [h]
  have hcPfixed : c * P ∈ FixedPoints.subring A G := by
    intro g
    show g • (c * P) = c * P
    rw [smul_mul', hcfixed g, hPfixed g]
  have hcPmem : c * P ∈ S := S.mul_mem hcmem hPmem
  refine ⟨(⟨c * a₁, hnumfixed⟩, ⟨⟨c * P, hcPfixed⟩, hcPmem⟩), ?_⟩
  have hspec : z.1 * algebraMap A (Localization S) P = algebraMap A (Localization S) a₁ := by
    rw [← hz₁]
    exact IsLocalization.mk'_spec (Localization S) a₁ ⟨P, hPmem⟩
  refine Subtype.ext ?_
  show z.1 * algebraMap A (Localization S) (c * P) = algebraMap A (Localization S) (c * a₁)
  calc z.1 * algebraMap A (Localization S) (c * P)
      = z.1 * (algebraMap A (Localization S) c * algebraMap A (Localization S) P) := by
        rw [map_mul]
    _ = z.1 * algebraMap A (Localization S) P * algebraMap A (Localization S) c := by ring
    _ = algebraMap A (Localization S) a₁ * algebraMap A (Localization S) c := by rw [hspec]
    _ = algebraMap A (Localization S) (c * a₁) := by simp only [map_mul]; ring

/-- The map `A^G → (S⁻¹A)^G` is injective modulo `S^G`. -/
theorem fixed_exists_of_eq {x y : ↥(FixedPoints.subring A G)}
    (h : algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) x =
      algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) y) :
    ∃ c : fixedSubmonoid G S,
      ((c : ↥(FixedPoints.subring A G)) * x = (c : ↥(FixedPoints.subring A G)) * y) := by
  classical
  have h' : algebraMap A (Localization S) (x : A) = algebraMap A (Localization S) (y : A) :=
    congrArg Subtype.val h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := S) (S := Localization S)).mp h'
  set C : A := ∏ g : G, g • (c : A) with hC
  have hCmem : C ∈ S := Submonoid.prod_mem S (fun g _ => Submonoid.GStable.smul_mem g c.2)
  have hCfixed : C ∈ FixedPoints.subring A G := fun g => Finset.smul_prod_perm (c : A) g
  have hfac : ∀ g : G, (g • (c : A)) * ((x : A) - (y : A)) = 0 := by
    intro g
    have h := congrArg (fun z : A => g • z) hc
    simp only [smul_mul'] at h
    rw [x.2 g, y.2 g] at h
    rw [mul_sub, h, sub_self]
  have hCann : C * ((x : A) - (y : A)) = 0 := by
    rw [hC, ← Finset.prod_erase_mul (Finset.univ) (fun g : G => g • (c : A)) (Finset.mem_univ 1),
      mul_assoc, hfac 1, mul_zero]
  refine ⟨⟨⟨C, hCfixed⟩, hCmem⟩, Subtype.ext ?_⟩
  show C * (x : A) = C * (y : A)
  rw [← sub_eq_zero, ← mul_sub]
  exact hCann

/-- **Exercise 5.12**: `(S^G)⁻¹A^G ≃ (S⁻¹A)^G`. -/
theorem isLocalization_fixed :
    IsLocalization (M := fixedSubmonoid G S) ↥(FixedPoints.subring (Localization S) G) := by
  rw [isLocalization_iff]
  exact ⟨fixed_map_units S, fixed_surj S, fun {x y} h => fixed_exists_of_eq S h⟩

/-- **Exercise 5.12 (final form)**: the fixed points of the localised action form the localization
of `A^G` at `S^G`. -/
noncomputable def fixedLocalizationEquiv :
    Localization (fixedSubmonoid G S) ≃+* ↥(FixedPoints.subring (Localization S) G) := by
  letI := isLocalization_fixed (G := G) S
  exact (IsLocalization.algEquiv (M := fixedSubmonoid G S) (S := Localization (fixedSubmonoid G S))
    (Q := ↥(FixedPoints.subring (Localization S) G))).toRingEquiv

/-- The isomorphism `(S^G)⁻¹A^G ≃ (S⁻¹A)^G` is the natural one. -/
theorem fixedLocalizationEquiv_algebraMap (x : ↥(FixedPoints.subring A G)) :
    fixedLocalizationEquiv S
        (algebraMap ↥(FixedPoints.subring A G) (Localization (fixedSubmonoid G S)) x) =
      algebraMap ↥(FixedPoints.subring A G) ↥(FixedPoints.subring (Localization S) G) x := by
  simp [fixedLocalizationEquiv]

end FixedLocalization

section FiniteVersion

variable {A : Type*} [CommRing A]

/-- **Exercise 5.12 (1)** with the book's hypothesis that `G` is a finite group (rather than
carrying a `Fintype` instance). -/
theorem isIntegral_invariants_of_finite {G : Type*} [Group G] [MulSemiringAction G A]
    [Finite G] (x : A) : IsIntegral ↥(FixedPoints.subring A G) x := by
  cases nonempty_fintype G
  exact isIntegral_invariants x

variable {G : Type*} [Group G] [MulSemiringAction G A]
variable (S : Submonoid A) [Submonoid.GStable (G := G) S] [Finite G]

/-- **Exercise 5.12 (3)** with the book's hypothesis that `G` is a finite group. -/
theorem exists_fixedLocalizationEquiv_of_finite :
    Nonempty (Localization (fixedSubmonoid G S) ≃+* ↥(FixedPoints.subring (Localization S) G)) := by
  cases nonempty_fintype G
  exact ⟨fixedLocalizationEquiv S⟩

end FiniteVersion

/-! ## Axiom check -/

#print axioms AtiyahMcdonald69.Ex_5_12.isIntegral_invariants
#print axioms AtiyahMcdonald69.Ex_5_12.localizationAct
#print axioms AtiyahMcdonald69.Ex_5_12.smul_algebraMap
#print axioms AtiyahMcdonald69.Ex_5_12.isLocalization_fixed
#print axioms AtiyahMcdonald69.Ex_5_12.fixedLocalizationEquiv
#print axioms AtiyahMcdonald69.Ex_5_12.exists_fixedLocalizationEquiv_of_finite

end AtiyahMcdonald69.Ex_5_12
