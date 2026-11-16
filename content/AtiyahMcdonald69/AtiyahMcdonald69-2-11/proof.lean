/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 2 (Modules), Exercise 11.
(Translation of the exercise, pp. 31–32 of the book:)

> **11.** Let `A` be a ring `≠ 0`. Show that `A^m ≅ A^n ⇒ m = n`.
> [Let `𝔪` be a maximal ideal of `A` and let `φ : A^m → A^n` be an isomorphism. Then
> `1 ⊗ φ : (A/𝔪) ⊗_A A^m → (A/𝔪) ⊗_A A^n` is an isomorphism between vector spaces of
> dimensions `m` and `n` over the field `k = A/𝔪`. Hence `m = n`.]
> (Cf. Chapter 3, Exercise 15.) If `φ : A^m → A^n` is surjective, then `m ≥ n`.
> If `φ : A^m → A^n` is injective, is it always the case that `m ≤ n`?

The three claims are formalized below as

* `eq_of_linearEquiv`      : a linear equivalence `A^m ≃ₗ A^n` forces `m = n`;
* `le_of_surjective`       : a surjective linear map `A^m → A^n` forces `n ≤ m`;
* `le_of_injective`        : an injective linear map `A^m → A^n` forces `m ≤ n`.

The first two are proved by the method of the book's hint: pass to a residue field `k = A ⧸ 𝔪`
and compare dimensions of the `k`-vector spaces `k ⊗[A] A^m ≅ k^m`, `k ⊗[A] A^n ≅ k^n`
(`residueTensorEquiv`, `residueTensorCongr`, `residueTensorMap` below are those base-change
constructions).  Tensoring does not help for the third, injective, statement — the answer to
the book's question is nevertheless *yes*; `le_of_injective` is proved by the classical
Cayley–Hamilton argument (the natural solution reproduced in the DoYourExercise notes):
composing with the inclusion `A^n ↪ A^m` on the first `n` coordinates gives an injective
endomorphism `T` of `A^m` whose image lies in a coordinate hyperplane; a monic polynomial of
least degree satisfied by `T` then has zero constant coefficient, hence is divisible by `X`,
and after cancelling the injective factor `T` we obtain a monic polynomial of smaller degree
satisfied by `T` — a contradiction.

Finally `subsingleton_counterexample` shows that the hypothesis `A ≠ 0` (`Nontrivial A`) is
not redundant, and `eq_of_linearEquiv_mathlib` etc. cross-check the three statements against
Mathlib's abstract `InvariantBasisNumber` / `RankCondition` / `StrongRankCondition` results.
-/
import Mathlib



open Polynomial TensorProduct

namespace AtiyahMcdonald69.Ex_2_11

variable {A : Type*} [CommRing A]

/-! ### Base change along `A → A ⧸ I` : the residue-field comparison -/

/-- For a commutative ring `A`, an ideal `I` and `k = A ⧸ I`, the tensor product
`k ⊗[A] A^m` is the `k`-vector space `k^m`; this is the book's
`(A/𝔪) ⊗_A A^m ≅ k^m` for a maximal ideal `𝔪`. -/
noncomputable def residueTensorEquiv (I : Ideal A) (m : ℕ) :
    ((A ⧸ I) ⊗[A] (Fin m → A)) ≃ₗ[A ⧸ I] (Fin m → A ⧸ I) :=
  TensorProduct.piScalarRight A (A ⧸ I) (A ⧸ I) (Fin m)

/-- The value of `residueTensorEquiv` on a pure tensor: `c ⊗ x ↦ (i ↦ x i • c)`. -/
lemma residueTensorEquiv_tmul (I : Ideal A) (m : ℕ) (c : A ⧸ I) (x : Fin m → A) :
    residueTensorEquiv I m (c ⊗ₜ[A] x) = fun i => (x i) • c :=
  rfl

/-- Base change (`- ⊗[A] A ⧸ I`) of an `A`-linear equivalence: this is the
`1 ⊗ φ` of the book's hint, as a `k`-linear equivalence. -/
noncomputable def residueTensorCongr (I : Ideal A) {m n : ℕ}
    (e : (Fin m → A) ≃ₗ[A] (Fin n → A)) :
    ((A ⧸ I) ⊗[A] (Fin m → A)) ≃ₗ[A ⧸ I] ((A ⧸ I) ⊗[A] (Fin n → A)) :=
  AlgebraTensorModule.congr (LinearEquiv.refl (A ⧸ I) (A ⧸ I)) e

/-- The value of `residueTensorCongr` on a pure tensor: it is `1 ⊗ e`. -/
lemma residueTensorCongr_tmul (I : Ideal A) {m n : ℕ}
    (e : (Fin m → A) ≃ₗ[A] (Fin n → A)) (c : A ⧸ I) (x : Fin m → A) :
    residueTensorCongr I e (c ⊗ₜ[A] x) = c ⊗ₜ[A] e x :=
  rfl

/-- Base change (`- ⊗[A] A ⧸ I`) of an `A`-linear map. -/
noncomputable def residueTensorMap (I : Ideal A) {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) :
    ((A ⧸ I) ⊗[A] (Fin m → A)) →ₗ[A ⧸ I] ((A ⧸ I) ⊗[A] (Fin n → A)) :=
  AlgebraTensorModule.map (LinearMap.id : (A ⧸ I) →ₗ[A ⧸ I] (A ⧸ I)) φ

@[simp]
lemma residueTensorMap_tmul (I : Ideal A) {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) (c : A ⧸ I) (x : Fin m → A) :
    residueTensorMap I φ (c ⊗ₜ[A] x) = c ⊗ₜ[A] φ x :=
  rfl

/-- Tensoring a surjective linear map is surjective (right exactness of `- ⊗[A] A ⧸ I`,
in the explicit form needed for the exercise). -/
lemma residueTensorMap_surjective (I : Ideal A) {m n : ℕ}
    {φ : (Fin m → A) →ₗ[A] (Fin n → A)} (h : Function.Surjective φ) :
    Function.Surjective (residueTensorMap I φ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c y =>
      obtain ⟨x, rfl⟩ := h y
      exact ⟨c ⊗ₜ x, rfl⟩
  | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by simp [ha, hb]⟩

/-- The `k`-linear equivalence `k^m ≃ k^n` obtained by tensoring an `A`-linear equivalence
`A^m ≃ A^n` with the residue field `k = A ⧸ I` — the book's `1 ⊗ φ`. -/
noncomputable def residueEquiv (I : Ideal A) {m n : ℕ}
    (e : (Fin m → A) ≃ₗ[A] (Fin n → A)) :
    (Fin m → A ⧸ I) ≃ₗ[A ⧸ I] (Fin n → A ⧸ I) :=
  (residueTensorEquiv I m).symm ≪≫ₗ residueTensorCongr I e ≪≫ₗ residueTensorEquiv I n

/-- The `k`-linear map `k^m → k^n` obtained by tensoring an `A`-linear map with `k = A ⧸ I`. -/
noncomputable def residueMap (I : Ideal A) {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) :
    (Fin m → A ⧸ I) →ₗ[A ⧸ I] (Fin n → A ⧸ I) :=
  (residueTensorEquiv I n).toLinearMap ∘ₗ residueTensorMap I φ ∘ₗ
    (residueTensorEquiv I m).symm.toLinearMap

/-- The `k`-vector space `k ⊗[A] A^m` has dimension `m` (the book's "vector spaces of
dimensions `m` and `n` over the field `k = A/𝔪`"). -/
theorem finrank_residueTensor (I : Ideal A) [I.IsMaximal] (m : ℕ) :
    Module.finrank (A ⧸ I) ((A ⧸ I) ⊗[A] (Fin m → A)) = m := by
  rw [LinearEquiv.finrank_eq (residueTensorEquiv I m), Module.finrank_fin_fun]

/-- `A^m ≅ A^n ⟹ m = n` (`A ≠ 0`): tensor an isomorphism with a residue field, and compare
dimensions of vector spaces.  This is the main assertion of Exercise 2.11. -/
theorem eq_of_linearEquiv [Nontrivial A] {m n : ℕ}
    (e : (Fin m → A) ≃ₗ[A] (Fin n → A)) : m = n := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal A
  have := hI
  have key : Module.finrank (A ⧸ I) (Fin m → A ⧸ I) = Module.finrank (A ⧸ I) (Fin n → A ⧸ I) :=
    (residueEquiv I e).finrank_eq
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at key

/-- If `φ : A^m → A^n` is surjective then `n ≤ m` (`A ≠ 0`): tensoring with a residue field
gives a surjection `k^m → k^n`. -/
theorem le_of_surjective [Nontrivial A] {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) (h : Function.Surjective φ) : n ≤ m := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal A
  have := hI
  have hsurj : Function.Surjective (residueMap I φ) :=
    (residueTensorEquiv I n).surjective.comp
      ((residueTensorMap_surjective I h).comp (residueTensorEquiv I m).symm.surjective)
  have key : Module.finrank (A ⧸ I) (Fin n → A ⧸ I) ≤ Module.finrank (A ⧸ I) (Fin m → A ⧸ I) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at key

/-! ### The injective case : Cayley–Hamilton -/

section CayleyHamilton

variable {m : ℕ}

/-- If `p` is a polynomial annihilating `T`, and `T` maps everything into the `j`-th
coordinate hyperplane, then `p` cannot have a nonzero constant term. -/
theorem coeff_zero_of_aeval_eq_zero (T : (Fin m → A) →ₗ[A] (Fin m → A)) (j : Fin m)
    {p : A[X]} (hp : Polynomial.aeval T p = 0) (hT : ∀ x, T x j = 0) :
    p.coeff 0 = 0 := by
  have hpoly : (Polynomial.aeval T) (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)) = 0 := by
    rw [Polynomial.X_mul_divX_add p]
    exact hp
  have happ : ∀ x : Fin m → A,
      (Polynomial.aeval T) (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)) x =
        T (Polynomial.aeval T p.divX x) + (p.coeff 0) • x := by
    intro x
    rw [map_add, map_mul, Polynomial.aeval_X]
    simp
  have key : ∀ x : Fin m → A, T (Polynomial.aeval T p.divX x) + (p.coeff 0) • x = 0 := by
    intro x
    have h := congrArg (fun f : Module.End A (Fin m → A) => f x) hpoly
    rw [happ x] at h
    exact h
  have h0 := congrArg (fun y : Fin m → A => y j) (key (Pi.single j 1))
  simpa [hT] using h0

/-- The key step of the Cayley–Hamilton argument.  If `T` is an injective endomorphism of
`A^m` whose image is contained in the `j`-th coordinate hyperplane, then we get a
contradiction: a monic polynomial of least degree satisfied by `T` would have to be divisible
by `X`, and cancelling `T` would produce one of smaller degree. -/
theorem false_of_injective_coordinate [Nontrivial A] (T : (Fin m → A) →ₗ[A] (Fin m → A))
    (j : Fin m) (hT : ∀ x, T x j = 0) (hinj : Function.Injective T) : False := by
  classical
  -- the monic polynomial of least degree satisfied by `T`
  set p : A[X] := minpoly A T with hp
  have hp_monic : p.Monic := minpoly.monic (LinearMap.isIntegral T)
  have hp_ne : p ≠ 0 := hp_monic.ne_zero
  have hp_aeval : Polynomial.aeval T p = 0 := minpoly.aeval A T
  -- the constant coefficient of `p` vanishes
  have hcoeff : p.coeff 0 = 0 := coeff_zero_of_aeval_eq_zero T j hp_aeval hT
  -- hence `p = X * q` with `q` monic of smaller degree
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hcoeff
  have hq_monic : q.Monic :=
    Polynomial.Monic.of_mul_monic_left Polynomial.monic_X (hq ▸ hp_monic)
  have hq_ne : q ≠ 0 := hq_monic.ne_zero
  have hq_aeval : Polynomial.aeval T q = 0 := by
    have hmul : T * Polynomial.aeval T q = 0 := by
      have h2 : Polynomial.aeval T (Polynomial.X * q) = T * Polynomial.aeval T q := by
        rw [map_mul, Polynomial.aeval_X]
      rw [← h2, ← hq]
      exact hp_aeval
    refine LinearMap.ext fun x => ?_
    refine hinj ?_
    have hx : T (Polynomial.aeval T q x) = 0 := by
      have h := congrArg (fun f : Module.End A (Fin m → A) => f x) hmul
      simpa using h
    simpa using hx
  -- but `p` was of least degree
  have hdeg : p.natDegree = q.natDegree + 1 := by
    rw [hq, Polynomial.natDegree_X_mul hq_ne]
  have hmin : p.natDegree ≤ q.natDegree := by
    have h := minpoly.min A T hq_monic hq_aeval
    rw [Polynomial.degree_eq_natDegree hp_ne, Polynomial.degree_eq_natDegree hq_ne] at h
    exact_mod_cast h
  omega

end CayleyHamilton

/-- If `φ : A^m → A^n` is injective then `m ≤ n` (`A ≠ 0`).  This answers the question at the
end of Exercise 2.11: yes, injectivity also forces the inequality. -/
theorem le_of_injective [Nontrivial A] {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) (hφ : Function.Injective φ) : m ≤ n := by
  classical
  by_contra hcon
  have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_le hcon)
  have hlt : n < m := Nat.lt_of_not_le hcon
  -- inclusion of `A^n` into the first `n` coordinates of `A^m`
  set i : (Fin n → A) →ₗ[A] (Fin m → A) :=
    LinearMap.pi fun j : Fin m =>
      if hj : (j : ℕ) < n then (LinearMap.proj (R := A) (φ := fun _ : Fin n => A) ⟨j, hj⟩)
      else 0 with hi
  have hi_apply : ∀ (x : Fin n → A) (j : Fin m),
      i x j = if hj : (j : ℕ) < n then x ⟨j, hj⟩ else 0 := by
    intro x j
    simp only [hi, LinearMap.pi_apply]
    by_cases hj : (j : ℕ) < n <;> simp [hj]
  have hi_inj : Function.Injective i := by
    intro x y hxy
    funext j
    have h1 : i x (Fin.castLE hnm j) = i y (Fin.castLE hnm j) := by
      rw [hxy]
    rw [hi_apply, hi_apply] at h1
    simpa [Fin.castLE] using h1
  -- the composite `T = i ∘ φ` is an injective endomorphism of `A^m` killing the `n`-th coordinate
  have hT_inj : Function.Injective (i.comp φ) := hi_inj.comp hφ
  have hT_coord : ∀ x, (i.comp φ) x ⟨n, hlt⟩ = 0 := by
    intro x
    rw [LinearMap.comp_apply, hi_apply]
    simp
  exact false_of_injective_coordinate (i.comp φ) ⟨n, hlt⟩ hT_coord hT_inj

/-! ### The hypothesis `A ≠ 0` is necessary -/

/-- Over the zero ring, `A^m` and `A^n` are both trivial modules, so the zero map
`A^m → A^n` is injective for every `m`, `n`; thus the hypothesis `A ≠ 0` in Exercise 2.11
cannot be dropped from the injective statement. -/
theorem subsingleton_counterexample :
    ∃ (A : Type) (_ : CommRing A) (m n : ℕ) (f : (Fin m → A) →ₗ[A] (Fin n → A)),
      Function.Injective f ∧ ¬ m ≤ n :=
  ⟨ℤ ⧸ (⊤ : Ideal ℤ), inferInstance, 2, 1, 0, fun x y _ => Subsingleton.elim x y, by norm_num⟩

/-! ### Cross-check against Mathlib's abstract rank conditions -/

/-- Mathlib's `InvariantBasisNumber` for nontrivial commutative rings recovers the first part. -/
theorem eq_of_linearEquiv_mathlib [Nontrivial A] {m n : ℕ}
    (e : (Fin m → A) ≃ₗ[A] (Fin n → A)) : m = n :=
  InvariantBasisNumber.eq_of_fin_equiv e

/-- Mathlib's `RankCondition` for nontrivial commutative rings recovers the second part. -/
theorem le_of_surjective_mathlib [Nontrivial A] {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) (h : Function.Surjective φ) : n ≤ m :=
  le_of_fin_surjective A φ h

/-- Mathlib's `StrongRankCondition` for nontrivial commutative rings recovers the third part. -/
theorem le_of_injective_mathlib [Nontrivial A] {m n : ℕ}
    (φ : (Fin m → A) →ₗ[A] (Fin n → A)) (h : Function.Injective φ) : m ≤ n :=
  le_of_fin_injective A φ h

/-- Non-vacuity check: there is no injection `ℤ² →ₗ ℤ`. -/
example : ¬∃ f : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ), Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := le_of_injective f hf
  omega

/-! ### The exercise as a single statement -/

/-- Exercise 2.11 bundled: over a nonzero commutative ring `A`,
`A^m ≅ A^n ⇒ m = n`, a surjection `A^m → A^n` forces `n ≤ m`, and an injection `A^m → A^n`
forces `m ≤ n`. -/
theorem exercise_2_11 [Nontrivial A] :
    (∀ m n : ℕ, ((Fin m → A) ≃ₗ[A] (Fin n → A)) → m = n) ∧
      (∀ (m n : ℕ) (φ : (Fin m → A) →ₗ[A] (Fin n → A)), Function.Surjective φ → n ≤ m) ∧
        ∀ (m n : ℕ) (φ : (Fin m → A) →ₗ[A] (Fin n → A)), Function.Injective φ → m ≤ n :=
  ⟨fun _ _ e => eq_of_linearEquiv e,
   fun _ _ φ h => le_of_surjective φ h,
   fun _ _ φ h => le_of_injective φ h⟩

#print axioms AtiyahMcdonald69.Ex_2_11.exercise_2_11
#print axioms AtiyahMcdonald69.Ex_2_11.eq_of_linearEquiv
#print axioms AtiyahMcdonald69.Ex_2_11.le_of_surjective
#print axioms AtiyahMcdonald69.Ex_2_11.le_of_injective
#print axioms AtiyahMcdonald69.Ex_2_11.residueTensorMap_surjective
#print axioms AtiyahMcdonald69.Ex_2_11.finrank_residueTensor
#print axioms AtiyahMcdonald69.Ex_2_11.coeff_zero_of_aeval_eq_zero
#print axioms AtiyahMcdonald69.Ex_2_11.false_of_injective_coordinate
#print axioms AtiyahMcdonald69.Ex_2_11.subsingleton_counterexample
#print axioms AtiyahMcdonald69.Ex_2_11.eq_of_linearEquiv_mathlib
#print axioms AtiyahMcdonald69.Ex_2_11.le_of_surjective_mathlib
#print axioms AtiyahMcdonald69.Ex_2_11.le_of_injective_mathlib

end AtiyahMcdonald69.Ex_2_11
