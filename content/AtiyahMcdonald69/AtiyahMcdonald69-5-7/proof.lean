/-
Copyright: public domain (formalization of a textbook exercise).

# Atiyah–Macdonald, Exercise 5.7

*Statement* (M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative
Algebra*, Addison–Wesley 1969, Chapter 5, Exercise 7):

> Let `A` be a subring of a ring `B`, such that the set `B - A` is closed under
> multiplication. Show that `A` is integrally closed in `B`.

"Integrally closed in `B`" means: every `x ∈ B` which is integral over `A`
(i.e. a root of a monic polynomial with coefficients in `A`) already lies in `A`.
Formalized below as `IsIntegrallyClosedIn ↥A B`, the Mathlib predicate for "all
integral elements of the ambient ring are already in the subring"
(`AtiyahMcdonald69.Ex_5_7.solution`).

Note that the only hypothesis is `B - A` being multiplicatively closed: no
domain, reducedness, or Noetherian hypothesis is used (compare the book's
standing assumptions in Chapter 5, which are *not* needed here).

## Proof

Let `x ∈ B` be integral over `A` and suppose `x ∉ A`; choose a monic `p ∈ A[X]`
with `p(x) = 0` and let `n = p.natDegree` be minimal among such. Degree `0` is
impossible, since a monic polynomial of degree `0` is `1`, so `p(x) = 0` would
give `1 = 0` in `B` (then `x = 1 ∈ A`). For `n ≥ 1` write

  `p = X * p.divX + C (p.coeff 0)`;

evaluating at `x` gives `x * (p.divX)(x) = -p.coeff 0 ∈ A`. Were `(p.divX)(x)`
outside `A`, then, `x` being outside `A`, multiplicative closure of `B - A`
would put `x * (p.divX)(x) = -p.coeff 0` outside `A`: contradiction. Hence
`(p.divX)(x) ∈ A`, and subtracting this constant from `p.divX` produces a monic
polynomial of smaller degree `n - 1` vanishing at `x`; by strong induction on
the degree, `x ∈ A` after all. (For `n = 1` we get `p.divX = 1` and
`x = -p.coeff 0 ∈ A` directly.)

The final sections record a counterexample showing that the multiplicative closure
hypothesis cannot be dropped (`diag`, `exists_integral_not_mem_of_not_mulClosed`)
and a concrete instance where the hypothesis does hold
(`constants_integrallyClosedIn_polynomial`).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_7

open Polynomial

variable {B : Type*} [CommRing B]

/-- **Exercise 5.7, quantitative form.** Let `A` be a subring of a commutative
ring `B` such that `B \ A` is closed under multiplication. If `x ∈ B` is a root
of a monic polynomial `p` with coefficients in `A` of degree `n`, then `x ∈ A`.
(Strong induction on `n`; the case `n = 0` forces `1 = 0` in `B`.) -/
theorem mem_of_monic_eval₂ (A : Subring B)
    (hA : ∀ x y : B, x ∉ A → y ∉ A → x * y ∉ A) (n : ℕ) :
    ∀ (x : B) (p : Polynomial ↥A), p.Monic → p.natDegree = n →
      p.eval₂ (Subring.subtype A) x = 0 → x ∈ A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x p hp hdeg hev
    by_contra hx
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- Degree `0`: the monic polynomial is `1`, so `1 = 0` in `B`.
      subst hn0
      have hp1 : p.coeff 0 = 1 := by
        rw [← hdeg]
        exact hp.coeff_natDegree
      have hpc : p = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, hp1, Polynomial.C_1]
      have h10 : (1 : B) = 0 := by
        have h1 : p.eval₂ (Subring.subtype A) x = 1 := by
          rw [hpc, Polynomial.eval₂_one]
        rw [h1] at hev
        exact hev
      have hx1 : x = 1 :=
        calc x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [h10]
          _ = 0 := mul_zero x
          _ = 1 := h10.symm
      exact hx (hx1.symm ▸ A.one_mem)
    · -- Degree `n ≥ 1`.
      have hqd : p.divX.natDegree = n - 1 := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]
      have hqmonic : p.divX.Monic := by
        rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hqd, Polynomial.coeff_divX,
          Nat.sub_add_cancel hnpos]
        rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hdeg] at hp
        exact hp
      -- `p = X * p.divX + C (p.coeff 0)`, evaluated at `x`.
      have hsplit : Polynomial.X * p.divX + Polynomial.C (p.coeff 0) = p :=
        Polynomial.X_mul_divX_add p
      have hmul : x * (p.divX).eval₂ (Subring.subtype A) x = -(Subring.subtype A (p.coeff 0)) := by
        have h1 : (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)).eval₂ (Subring.subtype A) x =
            x * (p.divX).eval₂ (Subring.subtype A) x + Subring.subtype A (p.coeff 0) := by
          rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
        have h0 : x * (p.divX).eval₂ (Subring.subtype A) x +
            Subring.subtype A (p.coeff 0) = 0 := by
          rw [← h1, hsplit]
          exact hev
        exact eq_neg_of_add_eq_zero_left h0
      -- The complement of `A` being multiplicatively closed yields `(p.divX)(x) ∈ A`.
      have hmem : (p.divX).eval₂ (Subring.subtype A) x ∈ A := by
        by_contra hc
        have hnot := hA x _ hx hc
        rw [hmul] at hnot
        exact hnot (A.neg_mem (p.coeff 0).2)
      rcases Nat.lt_or_ge 1 n with hn2 | hn1
      · -- Degree `n ≥ 2`: subtract the constant `(p.divX)(x)`.
        let c₀ : ↥A := ⟨(p.divX).eval₂ (Subring.subtype A) x, hmem⟩
        have hc₀ : Subring.subtype A c₀ = (p.divX).eval₂ (Subring.subtype A) x := rfl
        have hnew_monic : (p.divX - Polynomial.C c₀).Monic := by
          have hne : p.divX.natDegree ≠ 0 := by omega
          rw [Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
            Polynomial.coeff_sub, Polynomial.coeff_C, if_neg hne, sub_zero]
          exact hqmonic.coeff_natDegree
        have hnew_deg : (p.divX - Polynomial.C c₀).natDegree < n := by
          rw [Polynomial.natDegree_sub_C, hqd]
          omega
        have hnew_eval : (p.divX - Polynomial.C c₀).eval₂ (Subring.subtype A) x = 0 := by
          rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, hc₀, sub_self]
        exact hx (ih _ hnew_deg x _ hnew_monic rfl hnew_eval)
      · -- Degree `n = 1`: then `p.divX = 1` and `x = -p.coeff 0`.
        have hqd0 : p.divX.natDegree = 0 := by omega
        have hq1 : p.divX = 1 := by
          have hc : p.divX.coeff 0 = 1 := by
            rw [← hqd0]
            exact hqmonic.coeff_natDegree
          rw [Polynomial.eq_C_of_natDegree_eq_zero hqd0, hc, Polynomial.C_1]
        have hxeq : x = -(Subring.subtype A (p.coeff 0)) := by
          rw [← hmul, hq1, Polynomial.eval₂_one, mul_one]
        exact hx (hxeq.symm ▸ A.neg_mem (p.coeff 0).2)

/-- **Exercise 5.7.** Let `A` be a subring of a ring `B` such that `B - A` is
closed under multiplication. Then every element of `B` integral over `A` lies in
`A`, i.e. `A` is integrally closed in `B`. -/
theorem mem_of_isIntegral (A : Subring B)
    (hA : ∀ x y : B, x ∉ A → y ∉ A → x * y ∉ A) {x : B} (hx : IsIntegral ↥A x) :
    x ∈ A := by
  obtain ⟨p, hp, hev⟩ := hx
  exact mem_of_monic_eval₂ A hA p.natDegree x p hp rfl hev

/-- **Atiyah–Macdonald, Exercise 5.7.** If `A` is a subring of a ring `B` whose
complement `B - A` is closed under multiplication, then `A` is integrally closed
in `B`: every element of `B` integral over `A` already lies in `A`. -/
theorem solution (A : Subring B)
    (hA : ∀ x y : B, x ∉ A → y ∉ A → x * y ∉ A) : IsIntegrallyClosedIn ↥A B := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  exact mem_of_isIntegral A hA hx

/-- Exercise 5.7, with the hypothesis literally stated for the set `B \ A`:
the complement of `A` in `B` is closed under multiplication. -/
theorem solution_compl (A : Subring B)
    (hA : ∀ x y : B, x ∈ (A : Set B)ᶜ → y ∈ (A : Set B)ᶜ → x * y ∈ (A : Set B)ᶜ) :
    IsIntegrallyClosedIn ↥A B :=
  solution A fun x y hx hy => by simpa using hA x y (by simpa using hx) (by simpa using hy)

/-- Exercise 5.7 restated in the book's own words: `A` is its own integral
closure in `B`. -/
theorem integralClosure_eq_bot (A : Subring B)
    (hA : ∀ x y : B, x ∉ A → y ∉ A → x * y ∉ A) : integralClosure ↥A B = ⊥ :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff B fun _ _ h => Subtype.ext h).mpr
    (solution A hA)

/-! ### The multiplicative closure hypothesis cannot be dropped

The diagonal subring `A = {(n, n)} ⊆ B = ℤ × ℤ` is *not* integrally closed in
`B`: the idempotent `(1, 0)` is a root of `X² - X`, whose coefficients
`(1, 1)`/`(-1, -1)`/`(0, 0)` lie in `A`, yet `(1, 0) ∉ A`. Consistently, `B - A`
is not closed under multiplication there, since `(1, 0) * (0, 1) = (0, 0) ∈ A`.
This shows that the hypothesis in Exercise 5.7 is essential, i.e. the exercise
is not a restatement of a tautology. -/

/-- The diagonal subring `{(n, n) : n ∈ ℤ}` of `ℤ × ℤ`. -/
def diag : Subring (ℤ × ℤ) where
  carrier := {x | x.1 = x.2}
  mul_mem' := by rintro ⟨a, b⟩ ⟨c, d⟩ (h1 : a = b) (h2 : c = d); simp [h1, h2]
  one_mem' := rfl
  add_mem' := by rintro ⟨a, b⟩ ⟨c, d⟩ (h1 : a = b) (h2 : c = d); simp [h1, h2]
  zero_mem' := rfl
  neg_mem' := by rintro ⟨a, b⟩ (h : a = b); simp [h]

/-- The multiplicative closure hypothesis of Exercise 5.7 is not automatic:
without it, an integral element can lie outside the subring. -/
theorem exists_integral_not_mem_of_not_mulClosed :
    ∃ (A : Subring (ℤ × ℤ)) (x y z : ℤ × ℤ),
      IsIntegral ↥A x ∧ x ∉ A ∧ y ∉ A ∧ z ∉ A ∧ y * z ∈ A := by
  refine ⟨diag, (1, 0), (1, 0), (0, 1), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · have h : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ↥diag) =
          Polynomial.X ^ 2 + (-Polynomial.X) := by ring
      rw [h]
      refine Polynomial.monic_X_pow_add ?_
      rw [Polynomial.degree_neg, Polynomial.degree_X]
      norm_num
    · simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
  · simp [diag]
  · simp [diag]
  · simp [diag]
  · simp [diag]

/-! ### A concrete instance where the hypothesis holds

The constants form a subring of `Polynomial ℚ` whose complement (the non-constant
polynomials) is closed under multiplication, so Exercise 5.7 applies: a polynomial
integral over `ℚ` is constant. -/

/-- The multiplicative closure hypothesis of Exercise 5.7 holds for the constants
inside `Polynomial ℚ`, so the conclusion holds for them as well. -/
theorem constants_integrallyClosedIn_polynomial :
    IsIntegrallyClosedIn ↥((algebraMap ℚ (Polynomial ℚ)).range) (Polynomial ℚ) := by
  refine solution _ ?_
  intro x y hx hy hxy
  have hxn : x.natDegree ≠ 0 := by
    intro h
    exact hx ⟨x.coeff 0, by
      rw [Polynomial.algebraMap_eq]
      exact (Polynomial.eq_C_of_natDegree_eq_zero h).symm⟩
  have hyn : y.natDegree ≠ 0 := by
    intro h
    exact hy ⟨y.coeff 0, by
      rw [Polynomial.algebraMap_eq]
      exact (Polynomial.eq_C_of_natDegree_eq_zero h).symm⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hxn; simp at hxn
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hyn; simp at hyn
  obtain ⟨c, hc⟩ := hxy
  have h0 : (x * y).natDegree = 0 := by
    rw [← hc, Polynomial.algebraMap_eq, Polynomial.natDegree_C]
  rw [Polynomial.natDegree_mul hx0 hy0] at h0
  omega

end AtiyahMcdonald69.Ex_5_7

#print axioms AtiyahMcdonald69.Ex_5_7.mem_of_monic_eval₂
#print axioms AtiyahMcdonald69.Ex_5_7.mem_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_7.solution
#print axioms AtiyahMcdonald69.Ex_5_7.solution_compl
#print axioms AtiyahMcdonald69.Ex_5_7.integralClosure_eq_bot
#print axioms AtiyahMcdonald69.Ex_5_7.exists_integral_not_mem_of_not_mulClosed
#print axioms AtiyahMcdonald69.Ex_5_7.constants_integrallyClosedIn_polynomial
