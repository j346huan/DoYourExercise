/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Addison–Wesley, 1969.
Chapter 6 (Chain Conditions), Exercise 6.1.

The book's exercise (the local scan of the book is truncated before the
Chapter 6 exercise list, so the text below is the common wording of Macdonald's
own solutions manual, of the natural proof of `AtiyahMcdonald69-6-1` on the
DoYourExercise site, and of two independent course solution sets; all agree)
reads:

  (i)  Let M be a Noetherian A-module and u : M → M a module homomorphism.
       If u is surjective, then u is an isomorphism.
  (ii) If M is Artinian and u is injective, then again u is an isomorphism.

Here `u : M → M` is an `A`-linear endomorphism of `M`, and "`u` is an
isomorphism" means that `u` is bijective, equivalently that it is the
underlying linear map of some `e : M ≃ₗ[A] M`.

The proofs formalised below are the book's own arguments (they are also the
arguments of the natural proof):
  (i)  the ascending chain of submodules `ker u ⊆ ker u² ⊆ ⋯` of the Noetherian
       module `M` is eventually constant;
  (ii) the descending chain of submodules `range u ⊇ range u² ⊇ ⋯` of the
       Artinian module `M` is eventually constant.
The natural proof omits no hypothesis; both parts are stated and proved below
exactly for the objects the book quantifies over.

A final, clearly separated supplement (not asked for by the book) shows that
neither hypothesis can be dropped: on the non-Noetherian `ℚ`-vector space
`ℕ →₀ ℚ` the backward shift is surjective but not injective, and on the
non-Artinian ring `ℤ` multiplication by `2` is injective but not surjective.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_6_1

open Function

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ## Part (i): Noetherian modules -/

/-- Exercise 6.1 (i), injectivity form.

Let `M` be a Noetherian `A`-module and let `u : M → M` be a surjective
`A`-linear map. Then `u` is injective.

Proof: the submodules `ker (u ^ n)` form an increasing chain in the Noetherian
module `M`, so `ker (u ^ n) = ker (u ^ (n + 1))` for some `n`. If `u x = 0`,
surjectivity of `u ^ n` gives `y` with `u ^ n y = x`, and then
`u ^ (n + 1) y = u x = 0`, i.e. `y ∈ ker (u ^ (n + 1)) = ker (u ^ n)`, so
`x = u ^ n y = 0`. -/
theorem noetherian_surjective_injective [IsNoetherian A M] (u : M →ₗ[A] M)
    (hu : Surjective u) : Injective u := by
  -- The increasing chain `ker (u ^ n)` of submodules of `M` is eventually constant.
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian A M› u.iterateKer
  have hstab : LinearMap.ker (u ^ n) = LinearMap.ker (u ^ (n + 1)) :=
    hn (n + 1) (Nat.le_succ n)
  -- It suffices to prove that the kernel of `u` is zero.
  have hzero : ∀ x, u x = 0 → x = 0 := by
    intro x hx
    -- `x = u ^ n y` because `u ^ n` is surjective.
    obtain ⟨y, hy⟩ := Module.End.iterate_surjective hu n x
    -- `u ^ (n + 1) y = u x = 0`, so `y` lies in `ker (u ^ (n + 1)) = ker (u ^ n)`.
    have hmem : (u ^ n) y = 0 := by
      have h1 : y ∈ LinearMap.ker (u ^ (n + 1)) := by
        have huy : (u ^ (n + 1)) y = u x := by
          rw [pow_succ', Module.End.mul_apply, hy]
        rw [LinearMap.mem_ker, huy, hx]
      have h2 : y ∈ LinearMap.ker (u ^ n) := by
        rw [hstab]
        exact h1
      simpa using h2
    rw [← hy]
    exact hmem
  intro a b hab
  have hsub : u (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (hzero (a - b) hsub)

/-- Exercise 6.1 (i), bijectivity form: a surjective endomorphism of a
Noetherian module is bijective. -/
theorem noetherian_surjective_bijective [IsNoetherian A M] (u : M →ₗ[A] M)
    (hu : Surjective u) : Bijective u :=
  ⟨noetherian_surjective_injective u hu, hu⟩

/-- Exercise 6.1 (i), isomorphism form: a surjective endomorphism of a
Noetherian module is (the underlying linear map of) a linear automorphism. -/
theorem noetherian_surjective_linearEquiv [IsNoetherian A M] (u : M →ₗ[A] M)
    (hu : Surjective u) : ∃ e : M ≃ₗ[A] M, (e : M →ₗ[A] M) = u :=
  ⟨LinearEquiv.ofBijective u (noetherian_surjective_bijective u hu), rfl⟩

/-! ## Part (ii): Artinian modules -/

/-- Exercise 6.1 (ii), surjectivity form.

Let `M` be an Artinian `A`-module and let `u : M → M` be an injective
`A`-linear map. Then `u` is surjective.

Proof: the submodules `range (u ^ n)` form a decreasing chain in the Artinian
module `M`, so `range (u ^ n) = range (u ^ (n + 1))` for some `n`. Given `x`,
`u ^ n x = u ^ (n + 1) y` for some `y`; applying the injective map `u ^ n`
gives `x = u y`. -/
theorem artinian_injective_surjective [IsArtinian A M] (u : M →ₗ[A] M)
    (hu : Injective u) : Surjective u := by
  -- The decreasing chain `range (u ^ n)` of submodules of `M` is eventually constant.
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (u ^ n) = LinearMap.range (u ^ m)⟩ :=
    IsArtinian.monotone_stabilizes u.iterateRange
  intro x
  have hx : (u ^ n) x ∈ LinearMap.range (u ^ (n + 1)) := by
    rw [← hn (n + 1) (Nat.le_succ n)]
    exact LinearMap.mem_range_self _ x
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  -- `u ^ n` is injective, and `u ^ n (u y) = u ^ (n + 1) y = u ^ n x`.
  have hux : (u ^ n) (u y) = (u ^ n) x := by
    rw [← hy, pow_succ, Module.End.mul_apply]
  exact Module.End.iterate_injective hu n hux

/-- Exercise 6.1 (ii), bijectivity form: an injective endomorphism of an
Artinian module is bijective. -/
theorem artinian_injective_bijective [IsArtinian A M] (u : M →ₗ[A] M)
    (hu : Injective u) : Bijective u :=
  ⟨hu, artinian_injective_surjective u hu⟩

/-- Exercise 6.1 (ii), isomorphism form: an injective endomorphism of an
Artinian module is (the underlying linear map of) a linear automorphism. -/
theorem artinian_injective_linearEquiv [IsArtinian A M] (u : M →ₗ[A] M)
    (hu : Injective u) : ∃ e : M ≃ₗ[A] M, (e : M →ₗ[A] M) = u :=
  ⟨LinearEquiv.ofBijective u (artinian_injective_bijective u hu), rfl⟩

/-! ## The two parts of the book's exercise, under the book's own labels -/

/-- Exercise 6.1 (i): a surjective endomorphism of a Noetherian module is an
isomorphism. -/
theorem part_i [IsNoetherian A M] (u : M →ₗ[A] M) (hu : Surjective u) :
    ∃ e : M ≃ₗ[A] M, (e : M →ₗ[A] M) = u :=
  noetherian_surjective_linearEquiv u hu

/-- Exercise 6.1 (ii): an injective endomorphism of an Artinian module is an
isomorphism. -/
theorem part_ii [IsArtinian A M] (u : M →ₗ[A] M) (hu : Injective u) :
    ∃ e : M ≃ₗ[A] M, (e : M →ₗ[A] M) = u :=
  artinian_injective_linearEquiv u hu


/-! ## Supplement: neither hypothesis can be dropped

The book does not ask for this, but it shows that the two statements above are
sharp, i.e. that "surjective endomorphism ⇒ injective" is false for modules that
are not Noetherian and "injective endomorphism ⇒ surjective" is false for
modules that are not Artinian. -/

/-! ### The Noetherian hypothesis is not redundant

On the infinite-dimensional `ℚ`-vector space `ℕ →₀ ℚ` the backward shift
`e₀ ↦ 0`, `e_{n+1} ↦ e_n` is surjective but not injective, and this module is
not Noetherian. -/

/-- The `ℚ`-vector space on the basis `ℕ`. -/
abbrev shiftSpace : Type := ℕ →₀ ℚ

lemma rank_shiftSpace : Module.rank ℚ shiftSpace = Cardinal.aleph0 := by
  rw [rank_finsupp_self', Cardinal.mk_nat]

lemma not_isNoetherian_shiftSpace : ¬ IsNoetherian ℚ shiftSpace := by
  rw [IsNoetherian.iff_rank_lt_aleph0, rank_shiftSpace]
  exact lt_irrefl _

/-- The backward shift `e₀ ↦ 0`, `e_{n+1} ↦ e_n` on `ℕ →₀ ℚ`. -/
noncomputable def shiftDown : shiftSpace →ₗ[ℚ] shiftSpace :=
  Finsupp.linearCombination ℚ fun n : ℕ => if n = 0 then 0 else Finsupp.single (n - 1) 1

/-- The forward shift `e_n ↦ e_{n+1}` on `ℕ →₀ ℚ`. -/
noncomputable def shiftUp : shiftSpace →ₗ[ℚ] shiftSpace :=
  Finsupp.linearCombination ℚ fun n : ℕ => Finsupp.single (n + 1) 1

lemma shiftDown_single_zero (c : ℚ) : shiftDown (Finsupp.single 0 c) = 0 := by
  simp [shiftDown]

lemma shiftDown_single_succ (n : ℕ) (c : ℚ) :
    shiftDown (Finsupp.single (n + 1) c) = Finsupp.single n c := by
  simp [shiftDown, Finsupp.smul_single]

lemma shiftUp_single (n : ℕ) (c : ℚ) :
    shiftUp (Finsupp.single n c) = Finsupp.single (n + 1) c := by
  simp [shiftUp, Finsupp.smul_single]

lemma shiftDown_shiftUp (g : shiftSpace) : shiftDown (shiftUp g) = g := by
  induction g using Finsupp.induction with
  | zero => simp
  | single_add a b g _ _ ih =>
      rw [map_add, map_add, ih, shiftUp_single, shiftDown_single_succ]

lemma shiftDown_surjective : Surjective shiftDown :=
  fun x => ⟨shiftUp x, shiftDown_shiftUp x⟩

lemma shiftDown_not_injective : ¬ Injective shiftDown := by
  intro h
  have h0 : shiftDown (Finsupp.single 0 1) = shiftDown 0 := by
    rw [shiftDown_single_zero, map_zero]
  have h1 := h h0
  rw [Finsupp.single_eq_zero] at h1
  exact one_ne_zero h1

/-- The Noetherian hypothesis is needed: `ℕ →₀ ℚ` is not Noetherian over `ℚ`,
and its backward shift is surjective but not injective. -/
theorem noetherian_hypothesis_necessary :
    ¬ IsNoetherian ℚ shiftSpace ∧
      ∃ u : shiftSpace →ₗ[ℚ] shiftSpace, Surjective u ∧ ¬ Injective u :=
  ⟨not_isNoetherian_shiftSpace, shiftDown, shiftDown_surjective, shiftDown_not_injective⟩


/-! ### The Artinian hypothesis is not redundant

On `ℤ` (a Noetherian, non-Artinian ring) multiplication by `2` is an injective
endomorphism of `ℤ` as a `ℤ`-module that is not surjective. -/

section SharpnessArtinian

/-- Multiplication by `2` on `ℤ`. -/
noncomputable def doubleInt : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ 2

lemma doubleInt_injective : Injective doubleInt := by
  intro a b h
  simp only [doubleInt, LinearMap.lsmul_apply, smul_eq_mul] at h
  omega

lemma doubleInt_not_surjective : ¬ Surjective doubleInt := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  simp only [doubleInt, LinearMap.lsmul_apply, smul_eq_mul] at hx
  omega

/-- `ℤ` is not an Artinian ring, though it is Noetherian. -/
lemma not_isArtinianRing_int : ¬ IsArtinianRing ℤ := by
  intro h
  have hf : IsField ℤ := @IsArtinianRing.isField_of_isDomain ℤ _ h _
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (a := 2) (by norm_num)
  omega

/-- The Artinian hypothesis is needed: `ℤ` is not an Artinian ring, and
multiplication by `2` on `ℤ` is injective but not surjective. -/
theorem artinian_hypothesis_necessary :
    ¬ IsArtinianRing ℤ ∧ ∃ u : ℤ →ₗ[ℤ] ℤ, Injective u ∧ ¬ Surjective u :=
  ⟨not_isArtinianRing_int, doubleInt, doubleInt_injective, doubleInt_not_surjective⟩

end SharpnessArtinian


end AtiyahMcdonald69.Ex_6_1
