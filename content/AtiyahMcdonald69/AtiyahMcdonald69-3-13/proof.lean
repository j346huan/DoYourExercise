import Mathlib

set_option linter.style.haveILetI false

/-!
# Atiyah–Macdonald (1969), Exercise 3.13

The book's statement (Chapter 3, Exercise 13, verbatim from the 1969 text):

> Let `S` be a multiplicatively closed subset of an integral domain `A`. In the notation of
> Exercise 12, show that `T(S⁻¹M) = S⁻¹(T(M))`. Deduce that the following are equivalent:
> i) `M` is torsion-free.
> ii) `M_𝔭` is torsion-free for all prime ideals `𝔭`.
> iii) `M_𝔪` is torsion-free for all maximal ideals `𝔪`.

Exercise 12 introduces the notation used here: for an integral domain `A` and an `A`-module `M`,
an element `x ∈ M` is a *torsion element* if `Ann(x) ≠ 0`, i.e. if `x` is killed by some non-zero
element of `A`; the torsion elements form a submodule `T(M) ≤ M`, and `M` is *torsion-free* if
`T(M) = 0`.

## Formalization

* `T A M` is the torsion submodule (Mathlib's `Submodule.torsion`, i.e. the elements killed by a
  non-zero-divisor; over a domain this is the same as “killed by a non-zero element”, see
  `mem_T_iff`, and `coe_T_eq_annihilator_ne_bot` recovers the book's definition
  `T(M) = {x | Ann(x) ≠ 0}`).
* `torsion_localized` is `T(S⁻¹M) = S⁻¹(T(M))`, stated as an equality of submodules of `S⁻¹M`
  (the right hand side is `Submodule.localized`, the image of the localisation of `T(M)`).
* `mem_torsion_localized_iff` is the elementwise form: `y ∈ T(S⁻¹M)` iff `y = m/s` with
  `m ∈ T(M)`, `s ∈ S`.
* `localized_torsion_equiv` records that `S⁻¹(T(M))` really is the localisation of the `A`-module
  `T(M)`.
* `torsionFree_iff_forall_isTorsionFree_atMaximal` and
  `torsionFree_iff_forall_isTorsionFree_atPrime` are the equivalences (i) ⟺ (iii) and
  (i) ⟺ (ii); `torsionFree_tfae` states all three are equivalent.

## Audit of the hypotheses and of the natural solution

The domain hypothesis is used exactly where the book uses it, and nothing is silently dropped:

* The localisation map `A → S⁻¹A` is injective when `S` consists of non-zero elements, which is what
  lets a non-zero element of `A` be used as a non-zero-divisor of `S⁻¹`A (direction `⊇` of
  `torsion_localized`, via `IsLocalization.to_map_eq_zero_iff`), and lets `S⁻¹A` be a domain
  (`IsLocalization.isDomain_localization`).
* In the direction `⊆` the natural solution says “`(a/s)(m/t) = 0`, so `u a m = 0` for some `u ∈ S`;
  since `ua ≠ 0`, `m ∈ T(M)`”. The `u ∈ S` is essential (it is the relation defining the localised
  module, here `IsLocalizedModule.mk'_eq_zero'`), and `ua ≠ 0` needs `u ≠ 0` (i.e. `0 ∉ S`) together
  with the domain hypothesis (`mul_ne_zero`).
* The natural solution does not discuss the degenerate case `0 ∈ S`. There `S⁻¹A` is the trivial ring
  and `S⁻¹M = 0`, so both sides of `T(S⁻¹M) = S⁻¹(T(M))` are `⊤`; this is handled separately in
  `torsion_localized`.
* The final deduction “the local criterion for a module to vanish gives both equivalences” is the
  step from `T(M) = 0` to the localisations. Here it is proved from the fact that the annihilator of
  a *non-zero* element is a proper ideal (`exists_isMaximal_mk_one_ne_zero`), together with the main
  equality; note that this auxiliary lemma in fact needs no domain hypothesis (it is stated with the
  hypothesis `omit`ted), only `CommRing A`.

The identification of the book's `T(M)` with `Submodule.torsion` uses that in a domain every non-zero
element is a non-zero-divisor (`mem_T_iff`); `coe_T_eq_annihilator_ne_bot` recovers the book's
definition `T(M) = {x | Ann x ≠ 0}` verbatim.
-/

namespace AtiyahMcdonald69.Ex_3_13

open Submodule
open scoped nonZeroDivisors

universe u v w

/-! ## The torsion submodule -/

section Torsion

variable (A : Type u) [CommRing A] [IsDomain A]

/-- `T(M)`: the torsion submodule of an `A`-module `M`, where `A` is an integral domain.
An element is torsion when it is annihilated by some non-zero element of `A`
(equivalently, when its annihilator is non-zero). -/
abbrev T (M : Type v) [AddCommGroup M] [Module A M] : Submodule A M := Submodule.torsion A M

/-- An element `x` of an `A`-module is a torsion element when it is killed by a non-zero
element of `A`, i.e. when `Ann x ≠ 0`. -/
def IsTorsionElement (M : Type v) [AddCommGroup M] [Module A M] (x : M) : Prop :=
  ∃ a : A, a ≠ 0 ∧ a • x = 0

lemma mem_T_iff (M : Type v) [AddCommGroup M] [Module A M] (x : M) :
    x ∈ T A M ↔ IsTorsionElement A M x := by
  rw [show x ∈ T A M ↔ x ∈ Submodule.torsion A M from Iff.rfl, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hx⟩
    exact ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hx⟩

lemma isTorsionElement_iff_mem_T (M : Type v) [AddCommGroup M] [Module A M] (x : M) :
    IsTorsionElement A M x ↔ x ∈ T A M :=
  (mem_T_iff A M x).symm

/-- The torsion submodule consists exactly of the elements with non-zero annihilator, as in the
book's definition of `T(M)`. -/
theorem coe_T_eq_annihilator_ne_bot (M : Type v) [AddCommGroup M] [Module A M] :
    (T A M : Set M) = {x : M | Ideal.torsionOf A M x ≠ ⊥} := by
  ext x
  change x ∈ T A M ↔ _
  rw [mem_T_iff A M x]
  constructor
  · rintro ⟨a, ha, hx⟩ hbot
    have hmem : a ∈ Ideal.torsionOf A M x := (Ideal.mem_torsionOf_iff x a).mpr hx
    rw [hbot] at hmem
    exact ha (by simpa using hmem)
  · intro h
    obtain ⟨a, ha, ha0⟩ := Submodule.ne_bot_iff _ |>.mp h
    exact ⟨a, ha0, (Ideal.mem_torsionOf_iff x a).mp ha⟩

/-- `M` is torsion-free when `T(M) = 0`. -/
def TorsionFree (M : Type v) [AddCommGroup M] [Module A M] : Prop := T A M = ⊥

lemma torsionFree_iff_isTorsionFree (M : Type v) [AddCommGroup M] [Module A M] :
    TorsionFree A M ↔ Module.IsTorsionFree A M :=
  (Submodule.isTorsionFree_iff_torsion_eq_bot).symm

end Torsion

/-! ## The main theorem: `T(S⁻¹M) = S⁻¹(T(M))` -/

section Localization

variable (A : Type u) [CommRing A] [IsDomain A]
variable (S : Submonoid A)
variable (M : Type v) [AddCommGroup M] [Module A M]

/-- Auxiliary form of one inclusion, stated with `Submodule.localized'`. -/
theorem torsion_le_localized' (hS : (0 : A) ∉ S) :
    Submodule.torsion (Localization S) (LocalizedModule S M)
      ≤ (T A M).localized' (Localization S) S (LocalizedModule.mkLinearMap S M) := by
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hS)
  intro y hy
  rw [Submodule.mem_torsion_iff] at hy
  obtain ⟨b, hb⟩ := hy
  obtain ⟨m, t, rfl⟩ : ∃ (m : M) (t : S), y = LocalizedModule.mk m t := by
    induction y using LocalizedModule.induction_on with
    | h m t => exact ⟨m, t, rfl⟩
  obtain ⟨⟨r, s⟩, hrs⟩ :
      ∃ p : A × S, IsLocalization.mk' (Localization S) p.1 p.2 = (b : Localization S) :=
    IsLocalization.mk'_surjective S (b : Localization S)
  have hbne : (b : Localization S) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hrne : r ≠ 0 := by
    rintro rfl
    exact hbne (hrs ▸ IsLocalization.mk'_zero s)
  have hb' : IsLocalization.mk' (Localization S) r s •
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m t = 0 := by
    rw [hrs, ← IsLocalizedModule.mk_eq_mk']
    exact hb
  have hsm : IsLocalization.mk' (Localization S) r s •
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m t =
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (r • m) (s * t) :=
    IsLocalizedModule.mk'_smul_mk' (Localization S) (LocalizedModule.mkLinearMap S M) r m s t
  have key : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (r • m) (s * t) = 0 := by
    rw [← hsm]
    exact hb'
  rw [IsLocalizedModule.mk'_eq_zero'] at key
  obtain ⟨u, hu⟩ := key
  refine (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
    (T A M) _).mpr ⟨m, ?_, t, (IsLocalizedModule.mk_eq_mk' t m).symm⟩
  rw [mem_T_iff]
  refine ⟨(u : A) * r, mul_ne_zero ?_ hrne, ?_⟩
  · rintro h; exact hS (h ▸ u.2)
  · simpa [Submonoid.smul_def, mul_smul] using hu

/-- Auxiliary form of the other inclusion, stated with `Submodule.localized'`. -/
theorem localized'_le_torsion (hS : (0 : A) ∉ S) :
    (T A M).localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
      ≤ Submodule.torsion (Localization S) (LocalizedModule S M) := by
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hS)
  intro y hy
  obtain ⟨m, hm, s, rfl⟩ :=
    (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S M) (T A M) y).mp hy
  rw [mem_T_iff] at hm
  obtain ⟨a, ha, ham⟩ := hm
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨algebraMap A (Localization S) a, ?_⟩, ?_⟩
  · refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, IsLocalization.to_map_eq_zero_iff (Localization S) (M := S)
      (le_nonZeroDivisors_of_noZeroDivisors hS)]
    exact ha
  · have hmain : (algebraMap A (Localization S) a) •
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m s = 0 := by
      rw [IsScalarTower.algebraMap_smul, ← IsLocalizedModule.mk'_smul, ham]
      exact IsLocalizedModule.mk'_zero (LocalizedModule.mkLinearMap S M) s
    simpa [Submonoid.smul_def] using hmain

/-- **Atiyah–Macdonald, Exercise 3.13**: for a multiplicatively closed subset `S` of an integral
domain `A` and an `A`-module `M`, the torsion submodule of the localized module `S⁻¹M` is the
localization `S⁻¹(T(M))` of the torsion submodule `T(M)`. -/
theorem torsion_localized :
    Submodule.torsion (Localization S) (LocalizedModule S M) = (T A M).localized S := by
  by_cases hS : (0 : A) ∈ S
  · haveI : Subsingleton (LocalizedModule S M) :=
      LocalizedModule.subsingleton_iff.mpr fun m => ⟨0, hS, by simp⟩
    refine le_antisymm ?_ ?_
    · intro y _
      refine (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
        (T A M) y).mpr ⟨0, (T A M).zero_mem, 1, ?_⟩
      rw [IsLocalizedModule.mk'_zero (LocalizedModule.mkLinearMap S M)]
      exact Subsingleton.elim (0 : LocalizedModule S M) y
    · intro y _
      rw [Submodule.mem_torsion_iff]
      refine ⟨1, ?_⟩
      rw [Submonoid.smul_def, show y = 0 from Subsingleton.elim y 0, smul_zero]
  · exact le_antisymm (torsion_le_localized' A S M hS) (localized'_le_torsion A S M hS)

/-- **Atiyah–Macdonald, Exercise 3.13**, elementwise form: an element of `S⁻¹M` is a torsion
element iff it is of the form `m/s` with `m ∈ T(M)` and `s ∈ S`. -/
theorem mem_torsion_localized_iff (y : LocalizedModule S M) :
    y ∈ Submodule.torsion (Localization S) (LocalizedModule S M) ↔
      ∃ (m : M) (s : S), m ∈ T A M ∧ LocalizedModule.mk m s = y := by
  rw [torsion_localized A S M, Submodule.localized]
  refine (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S M)
    (T A M) y).trans ?_
  exact ⟨fun ⟨m, hm, s, hs⟩ => ⟨m, s, hm, by rw [IsLocalizedModule.mk_eq_mk', hs]⟩,
    fun ⟨m, s, hm, hs⟩ => ⟨m, hm, s, by rw [← IsLocalizedModule.mk_eq_mk', hs]⟩⟩

/-- `S⁻¹(T(M))` is the localisation of the `A`-module `T(M)`: the submodule `S⁻¹(T(M)) ≤ S⁻¹M` is
linearly isomorphic to `LocalizedModule S (T(M))`. -/
noncomputable def localized_torsion_equiv :
    ↥((T A M).localized S) ≃ₗ[Localization S] LocalizedModule S ↥(T A M) :=
  Submodule.localizedEquiv S (T A M)

/-- `T(A) = 0`: an integral domain is torsion-free as a module over itself. (A sanity check that
the definition of `T` behaves as the book's.) -/
theorem torsion_self_eq_bot : T A A = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_T_iff] at hx
  obtain ⟨a, ha, hax⟩ := hx
  rw [smul_eq_mul] at hax
  exact (mul_eq_zero.mp hax).resolve_left ha

/-- If `M` is torsion-free then so is every localisation `S⁻¹M`. -/
theorem torsionFree_localized (h : TorsionFree A M) :
    Submodule.torsion (Localization S) (LocalizedModule S M) = ⊥ := by
  rw [torsion_localized A S M, show T A M = ⊥ from h]
  simpa only [Submodule.localized] using
    Submodule.localized'_bot (Localization S) S (LocalizedModule.mkLinearMap S M)

end Localization

/-! ## Torsion-freeness is a local condition -/

section LocalCriterion

variable (A : Type u) [CommRing A] [IsDomain A]
variable (M : Type v) [AddCommGroup M] [Module A M]

omit [IsDomain A] in
/-- A non-zero element `x` of a module has non-zero image in the localisation at some maximal
ideal. (This does not need the domain hypothesis: `Ann x ≠ ⊤` because `1 ∉ Ann x`.) -/
theorem exists_isMaximal_mk_one_ne_zero {x : M} (hx : x ≠ 0) :
    ∃ (P : Ideal A) (_ : P.IsMaximal), LocalizedModule.mk x (1 : P.primeCompl) ≠ 0 := by
  have hI : Ideal.torsionOf A M x ≠ ⊤ := fun h =>
    hx ((Ideal.torsionOf_eq_top_iff A x).mp h)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.torsionOf A M x) hI
  refine ⟨P, hP, ?_⟩
  haveI := hP
  intro hzero
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero'] at hzero
  obtain ⟨s, hs⟩ := hzero
  have hmem : (s : A) ∈ Ideal.torsionOf A M x := (Ideal.mem_torsionOf_iff x (s : A)).mpr hs
  exact s.2 (hle hmem)

/-- The "in particular" of the exercise: at a prime ideal `𝔭`, `T(M_𝔭) = T(M)_𝔭`. -/
theorem torsion_atPrime (P : Ideal A) [P.IsPrime] :
    Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      (T A M).localized P.primeCompl :=
  torsion_localized A P.primeCompl M

/-- **A–M Exercise 3.13, (i) ⟺ (iii)**: `M` is torsion-free iff `M_𝔪` is torsion-free for all
maximal ideals `𝔪`. -/
theorem torsionFree_iff_forall_isTorsionFree_atMaximal :
    T A M = ⊥ ↔ ∀ (P : Ideal A) [P.IsMaximal],
      Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥ := by
  constructor
  · intro h P _
    rw [torsion_localized A P.primeCompl M, h]
    simpa only [Submodule.localized] using
      Submodule.localized'_bot (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)
  · intro h
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    obtain ⟨P, hP, hne⟩ := exists_isMaximal_mk_one_ne_zero A M hx0
    haveI := hP
    have hmk : LocalizedModule.mk x (1 : P.primeCompl) ∈
        Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      (mem_torsion_localized_iff A P.primeCompl M _).mpr ⟨x, 1, hx, rfl⟩
    rw [h P] at hmk
    exact hne (by simpa using hmk)

/-- **A–M Exercise 3.13, (i) ⟺ (ii)**: `M` is torsion-free iff `M_𝔭` is torsion-free for all
prime ideals `𝔭`. -/
theorem torsionFree_iff_forall_isTorsionFree_atPrime :
    T A M = ⊥ ↔ ∀ (P : Ideal A) [P.IsPrime],
      Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥ := by
  constructor
  · intro h P _
    rw [torsion_localized A P.primeCompl M, h]
    simpa only [Submodule.localized] using
      Submodule.localized'_bot (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)
  · intro h
    rw [torsionFree_iff_forall_isTorsionFree_atMaximal A M]
    intro P _
    exact h P

/-- **A–M Exercise 3.13**: the conditions (i), (ii) and (iii) are equivalent. -/
theorem torsionFree_tfae :
    [T A M = ⊥,
      (∀ (P : Ideal A) [P.IsPrime],
        Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥),
      (∀ (P : Ideal A) [P.IsMaximal],
        Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥)].TFAE := by
  tfae_have 1 ↔ 2 := torsionFree_iff_forall_isTorsionFree_atPrime A M
  tfae_have 1 ↔ 3 := torsionFree_iff_forall_isTorsionFree_atMaximal A M
  tfae_finish

/-- The torsion submodule of a localisation at a maximal ideal vanishes iff that localisation is
torsion-free in the sense of `Module.IsTorsionFree`. -/
theorem isTorsionFree_localized_iff (P : Ideal A) [P.IsMaximal] :
    Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥ ↔
      Module.IsTorsionFree (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  exact (Submodule.isTorsionFree_iff_torsion_eq_bot).symm

/-- **A–M Exercise 3.13, (i) ⟺ (iii)** in terms of Mathlib's `Module.IsTorsionFree`. -/
theorem isTorsionFree_iff_forall_isTorsionFree_atMaximal :
    Module.IsTorsionFree A M ↔ ∀ (P : Ideal A) [P.IsMaximal],
      Module.IsTorsionFree (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  rw [← torsionFree_iff_isTorsionFree A M]
  change T A M = ⊥ ↔ ∀ (P : Ideal A) [P.IsMaximal],
    Module.IsTorsionFree (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
  rw [torsionFree_iff_forall_isTorsionFree_atMaximal A M]
  exact ⟨fun h P hP => (isTorsionFree_localized_iff A M P).mp (h P),
    fun h P hP => (isTorsionFree_localized_iff A M P).mpr (h P)⟩

end LocalCriterion

/-! ## Bundled statement of the exercise -/

section Solution

variable (A : Type u) [CommRing A] [IsDomain A]
variable (S : Submonoid A)
variable (M : Type v) [AddCommGroup M] [Module A M]

/-- **Atiyah–Macdonald, Exercise 3.13**, bundled: `T(S⁻¹M) = S⁻¹(T(M))` together with the two
equivalences (i) ⟺ (ii) and (i) ⟺ (iii) deduced from it. -/
theorem solution :
    (Submodule.torsion (Localization S) (LocalizedModule S M) = (T A M).localized S) ∧
    (∀ y : LocalizedModule S M,
      y ∈ Submodule.torsion (Localization S) (LocalizedModule S M) ↔
        ∃ (m : M) (s : S), m ∈ T A M ∧ LocalizedModule.mk m s = y) ∧
    (T A M = ⊥ ↔ ∀ (P : Ideal A) [P.IsPrime],
      Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥) ∧
    (T A M = ⊥ ↔ ∀ (P : Ideal A) [P.IsMaximal],
      Submodule.torsion (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = ⊥) :=
  ⟨torsion_localized A S M, mem_torsion_localized_iff A S M,
    torsionFree_iff_forall_isTorsionFree_atPrime A M,
    torsionFree_iff_forall_isTorsionFree_atMaximal A M⟩

end Solution

end AtiyahMcdonald69.Ex_3_13
