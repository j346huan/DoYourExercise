/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 10.10 (Chapter 10,
"Completions", p. 115).  Formalisation of the complete statement, all three parts.

## The original exercise

> **10.** i) With the notation of Exercise 9, deduce from Hensel's lemma that if `f̄(x)` has a
> simple root `ā ∈ A/𝔪`, then `f(x)` has a simple root `a ∈ A` such that `a ≡ ā mod 𝔪`.
> ii) Show that `2` is a square in the ring of `7`-adic integers.
> iii) Let `f(x,y) ∈ k[x,y]`, where `k` is a field, and assume that `f(0,y)` has `y = a₀` as a
> simple root. Prove that there exists a formal power series `y(x) = Σ_{n=0}^∞ aₙ xⁿ` such that
> `f(x, y(x)) = 0`.

The notation of Exercise 9 (recovered from the book): `A` is a local ring, `𝔪` its maximal ideal,
`A` is assumed `𝔪`-adically complete, `f(x) ∈ A[x]` is monic of degree `n`, and `f̄ ∈ (A/𝔪)[x]`
denotes the reduction of `f` modulo `𝔪`.  A root `ā` of `f̄` is *simple* when `f̄'(ā) ≠ 0`.

## Coverage

* `part_a` : part (i) in full.  `IsAdicComplete 𝔪 A` is Mathlib's notion of `𝔪`-adic completeness
  (Hausdorff, and every `𝔪`-adic Cauchy sequence has a limit); this is the book's notion of a
  complete topological ring.  Both hypotheses `f̄(ā) = 0` and `f̄'(ā) ≠ 0` are kept, as is the
  monicity of `f`; the conclusion gives a lift `a` of `ā` with `f(a) = 0` **and** `f'(a)` a unit,
  i.e. `a` really is a *simple* root and not merely a root, as in the book.
* `part_b` : part (ii), `∃ x : ℤ_[7], x ^ 2 = 2`, obtained by applying part (i) to `x ^ 2 - 2`
  over `ℤ_[7]` and the simple root `3` mod `7` (`3² - 2 = 7` and `2·3 = 6 ≢ 0 mod 7`), exactly as
  the book asks.  `ℤ_[7]` is Mathlib's `PadicInt 7`, the ring of `7`-adic integers.
* `part_c` : part (iii).  `f ∈ k[x,y]` is represented as an element of `(k[x])[y]`
  (`Polynomial (Polynomial k)`), which is canonically `k[x,y]`; `f(0,y)` is `f.map (evalRingHom 0)`
  and the relevant partial derivative is `f.derivative`.  The conclusion produces `y : k⟦X⟧` with
  constant term `a₀` (the book's `y(x) = Σ aₙ xⁿ` uses `a₀` as its constant term) and
  `f(x, y(x)) = 0`; the value `f(x,y(x))` is `Polynomial.eval₂` of `f` along the inclusion
  `k[x] → k⟦X⟧`, so this is the substitution of the power series `y` into `f`.  Pinning the
  constant term of `y` to `a₀` is the intended reading of the book's notation
  `y(x) = Σ_{n≥0} aₙxⁿ` (the given `a₀` is its constant term), and is a genuine strengthening of
  the bare existential `∃y, f(x,y(x)) = 0`; the Newton iteration produces it.
* `exists_root_of_eval_mem_of_isUnit_derivative` is an auxiliary general form of Hensel's lemma
  (without a monicity assumption) used for part (iii); it is needed because the plane curve
  `f = 0` of part (iii) need not be monic in `y` (e.g. `x·y² + y - 1`).  It is the Newton-iteration
  argument, adapted from Mathlib's proof of `IsAdicComplete.henselianRing`.

## Statement adaptation

None mathematically.  The only representation choices are: (a) the residue ring `A/𝔪` is
Mathlib's `A ⧸ IsLocalRing.maximalIdeal A`; (b) `k[x,y]` is represented as `(k[x])[y]`, i.e.
`Polynomial (Polynomial k)`, via the canonical isomorphism
`k[x,y] ≅ (k[x])[y]`; (c) `k[[x]]` is Mathlib's `PowerSeries k`; (d) `ℤ_7` is `PadicInt 7`
(notation `ℤ_[7]`).  `f(0,y)` and `∂f/∂y` are `f.map (Polynomial.evalRingHom 0)` and
`f.derivative`.

## Source of the natural-language solution

https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-10-10

## Approach

Part (i) invokes Mathlib's Hensel lemma for the maximal ideal of a complete local ring
(`HenselianRing.is_henselian`, obtained from `IsAdicComplete.henselianRing`), then shows that the
resulting root is simple: modulo `𝔪` its derivative is `f̄'(ā) ≠ 0`, so it is not in `𝔪`, hence a
unit.  Part (ii) is part (i) applied to `x ^ 2 - 2` over `ℤ_[7]`, using
`PadicInt.maximalIdeal_eq_span_p` to see that `7` lies in the maximal ideal while `6` does not.
Part (iii) applies the non-monic Hensel lemma over the complete local ring `k⟦X⟧` (Mathlib:
`PowerSeries` is `X`-adically complete) to `f` viewed in `k⟦X⟧[y]`, at the approximate root
`y₀ = a₀`; the hypotheses transfer because `f(0, a₀) = 0` means `f(a₀) ∈ (X)`, while
`(∂f/∂y)(0, a₀) ≠ 0` means that `f'(a₀)` has non-zero constant term, hence is a unit of `k⟦X⟧`.
The root found has the required shape.
-/
import Mathlib

open Polynomial
open scoped PadicInt Ring

namespace AtiyahMcdonald69.Ex_10_10

/-! ## Part (i): Hensel's lemma for a simple root -/

/-- A local ring that is complete for its maximal ideal satisfies Hensel's lemma in the local
form: a monic polynomial with a simple root modulo the maximal ideal has a lift of that root.
This is the local form of `IsAdicComplete.henselianRing`. -/
instance henselianLocalRing_of_isAdicComplete (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : HenselianLocalRing A where
  is_henselian := by
    intro f hf a₀ hmem hunit
    exact HenselianRing.is_henselian f hf a₀ hmem (IsUnit.map (Ideal.Quotient.mk _) hunit)

/-- **Atiyah–Macdonald, Exercise 10.10 (i).**

Let `A` be a local ring, `𝔪` its maximal ideal, `A` assumed `𝔪`-adically complete.  Let
`f ∈ A[x]` be monic and let `ā ∈ A/𝔪` be a simple root of the reduction `f̄` of `f` modulo `𝔪`
(so `f̄(ā) = 0` and `f̄'(ā) ≠ 0`).  Then `f` has a simple root `a ∈ A` with `a ≡ ā (mod 𝔪)`. -/
theorem part_a {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f : Polynomial A) (hf : f.Monic)
    (abar : A ⧸ IsLocalRing.maximalIdeal A)
    (hroot : (f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).eval abar = 0)
    (hsimple : ((f.derivative).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).eval abar ≠
      0) :
    ∃ a : A, Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a = abar ∧ f.IsRoot a ∧
      IsUnit (f.derivative.eval a) := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective abar
  -- `f(a₀)` reduces to `f̄(ā) = 0`, hence lies in the maximal ideal
  have hmemy : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hroot
  -- `f'(a₀)` reduces to `f̄'(ā) ≠ 0`, hence is not in the maximal ideal, hence a unit
  have hsimple' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval a₀) ≠ 0 := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hsimple
  have hunit : IsUnit (f.derivative.eval a₀) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmem => hsimple' ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨a, hroot_a, hmem_a⟩ :=
    HenselianLocalRing.is_henselian (R := A) f hf a₀ hmemy hunit
  -- `a` reduces to `ā`
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a₀ := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem_a
  refine ⟨a, hmk, hroot_a, ?_⟩
  -- `f'(a)` has the same reduction as `f'(a₀) ≠ 0`, hence is a unit too
  have hne : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval a) ≠ 0 := by
    have hcongr : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval a) =
        ((f.derivative).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).eval
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [hcongr, hmk]
    exact hsimple
  exact IsLocalRing.notMem_maximalIdeal.mp fun hmem =>
    hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

/-! ## Part (ii): `2` is a square in the `7`-adic integers -/

instance hp7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- **Atiyah–Macdonald, Exercise 10.10 (ii).**  `2` is a square in `ℤ_[7]`. -/
theorem part_b : ∃ x : ℤ_[7], x ^ 2 = 2 := by
  have h7 : (7 : ℤ_[7]) ∈ IsLocalRing.maximalIdeal ℤ_[7] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have h6 : (6 : ℤ_[7]) ∉ IsLocalRing.maximalIdeal ℤ_[7] := by
    have h6norm : ‖(6 : ℤ_[7])‖ = 1 := by
      rw [show (6 : ℤ_[7]) = ((6 : ℕ) : ℤ_[7]) from rfl, PadicInt.norm_natCast_eq_one_iff]
      norm_num
    intro hmem
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    have hlt : ‖(6 : ℤ_[7])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd (6 : ℤ_[7])).mpr hmem
    rw [h6norm] at hlt
    exact lt_irrefl 1 hlt
  -- `3` is a simple root of `x ^ 2 - 2` modulo `7`, since `3 ^ 2 - 2 = 7` and `2 * 3 = 6`
  have hval : (Polynomial.X ^ 2 - Polynomial.C (2 : ℤ_[7])).eval (3 : ℤ_[7]) = 7 := by
    norm_num
  have hval' : ((Polynomial.X ^ 2 - Polynomial.C (2 : ℤ_[7])).derivative).eval (3 : ℤ_[7]) = 6 := by
    norm_num
  have hroot : ((Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℤ_[7]).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[7]))).eval
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[7]) 3) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h7
  have hsimple : ((Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℤ_[7]).derivative.map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[7]))).eval
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[7]) 3) ≠ 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hval']
    exact fun h0 => h6 (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  obtain ⟨a, -, hroot_a, -⟩ := part_a (f := Polynomial.X ^ 2 - Polynomial.C 2)
    (monic_X_pow_sub_C (2 : ℤ_[7]) (n := 2) (by norm_num)) _ hroot hsimple
  refine ⟨a, ?_⟩
  have h : a ^ 2 - 2 = 0 := by simpa using hroot_a
  exact sub_eq_zero.mp h

/-! ## Auxiliary: Hensel's lemma without a monicity assumption

Part (iii) concerns an arbitrary polynomial `f(x,y)`, which need not be monic in `y`: its leading
coefficient in `y` may vanish at `x = 0` (e.g. `f = x·y² + y - 1`, where `f(0,y) = y - 1` has the
simple root `1`).  The Newton iteration behind Hensel's lemma
does not use monicity at all, so we record the general statement here.  The proof is the Newton
iteration of Mathlib's `IsAdicComplete.henselianRing`, with the monicity assumption removed. -/

/-- **Hensel's lemma for an arbitrary polynomial.**  Let `A` be a commutative ring that is
`I`-adically complete for an ideal `I`, let `f ∈ A[x]` and let `a₀ ∈ A` satisfy `f(a₀) ∈ I` and
`f'(a₀)` a unit modulo `I`.  Then `f` has a root congruent to `a₀` modulo `I`. -/
theorem exists_root_of_eval_mem_of_isUnit_derivative {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] (f : Polynomial A) (a₀ : A) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  -- we define a sequence `c n` by starting at `a₀` and then continually
  -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
  -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
  let c : ℕ → A := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
  -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
  -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  -- we are now in the position to show that `c : ℕ → A` is a Cauchy sequence
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal A)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal A)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-! ## Part (iii): the analytic branch of a plane curve at a smooth point -/

/-- The composition of the inclusion `k[x] → k⟦X⟧` with the constant-term map is evaluation at
`x = 0`. -/
theorem constantCoeff_comp_coeToPowerSeries {k : Type*} [CommRing k] :
    PowerSeries.constantCoeff.comp
        (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k) =
      Polynomial.evalRingHom 0 := by
  refine RingHom.ext fun p => ?_
  simp [Polynomial.coeff_zero_eq_eval_zero]

/-- **Atiyah–Macdonald, Exercise 10.10 (iii).**

Let `k` be a field and `f ∈ k[x,y]` (represented as a polynomial in `y` with coefficients in
`k[x]`).  If `f(0,y)` has `y = a₀` as a simple root, i.e. `f(0,a₀) = 0` and
`(∂f/∂y)(0,a₀) ≠ 0`, then there is a formal power series `y(x) = Σ aₙxⁿ` with constant term
`a₀` such that `f(x, y(x)) = 0` in `k⟦X⟧`. -/
theorem part_c {k : Type*} [Field k] (f : Polynomial (Polynomial k)) (a₀ : k)
    (h_root : (f.map (Polynomial.evalRingHom 0)).eval a₀ = 0)
    (h_simple : (f.derivative.map (Polynomial.evalRingHom 0)).eval a₀ ≠ 0) :
    ∃ y : PowerSeries k, PowerSeries.constantCoeff y = a₀ ∧
      f.eval₂ (Polynomial.coeToPowerSeries.ringHom) y = 0 := by
  have hcomp : PowerSeries.constantCoeff.comp
      (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k) =
      Polynomial.evalRingHom 0 := constantCoeff_comp_coeToPowerSeries
  -- `f` viewed as a polynomial over the complete local ring `k⟦X⟧`
  set F : Polynomial (PowerSeries k) :=
    f.map (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k) with hF
  -- `f(a₀) = 0` means that `F(a₀)` lies in the ideal `(X)`
  have hmem : F.eval (PowerSeries.C a₀) ∈ Ideal.span {PowerSeries.X} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have h1 : F.eval (PowerSeries.C a₀) =
        f.eval₂ (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k)
          (PowerSeries.C a₀) := by
      rw [hF, Polynomial.eval_map]
    rw [h1, Polynomial.hom_eval₂, hcomp, PowerSeries.constantCoeff_C, ← Polynomial.eval_map]
    exact h_root
  -- `(∂f/∂y)(0,a₀) ≠ 0` means that `F'(a₀)` has non-zero constant term, i.e. is a unit
  have hunitA : IsUnit (F.derivative.eval (PowerSeries.C a₀)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    have hcoeff : PowerSeries.constantCoeff (F.derivative.eval (PowerSeries.C a₀)) =
        (f.derivative.map (Polynomial.evalRingHom 0)).eval a₀ := by
      have h1 : F.derivative = f.derivative.map
          (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k) := by
        rw [hF, Polynomial.derivative_map]
      have h2 : F.derivative.eval (PowerSeries.C a₀) =
          (f.derivative).eval₂
            (Polynomial.coeToPowerSeries.ringHom : Polynomial k →+* PowerSeries k)
            (PowerSeries.C a₀) := by
        rw [h1, Polynomial.eval_map]
      rw [h2, Polynomial.hom_eval₂, hcomp, PowerSeries.constantCoeff_C, ← Polynomial.eval_map]
    rw [hcoeff]
    exact h_simple
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {PowerSeries.X})
      (F.derivative.eval (PowerSeries.C a₀))) :=
    IsUnit.map (Ideal.Quotient.mk _) hunitA
  obtain ⟨y, hy_root, hy_mem⟩ :=
    exists_root_of_eval_mem_of_isUnit_derivative (Ideal.span {PowerSeries.X}) F
      (PowerSeries.C a₀) hmem hunit
  refine ⟨y, ?_, ?_⟩
  · have hdvd : PowerSeries.X ∣ y - PowerSeries.C a₀ := Ideal.mem_span_singleton.mp hy_mem
    have h0 : PowerSeries.constantCoeff (y - PowerSeries.C a₀) = 0 :=
      PowerSeries.X_dvd_iff.mp hdvd
    simp only [map_sub, PowerSeries.constantCoeff_C] at h0
    exact sub_eq_zero.mp h0
  · rw [← Polynomial.eval_map, ← hF]
    exact hy_root

/-! ## Sanity tests: the statements are non-vacuous and usable -/

section sanity

variable {k : Type*} [Field k]

-- The hypotheses of part (iii) are satisfiable and the conclusion is usable:
-- for `f = y - x` the solution is `y(x) = x`.
example : ∃ y : PowerSeries k, PowerSeries.constantCoeff y = 0 ∧
    (Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial k)).eval₂
      (Polynomial.coeToPowerSeries.ringHom) y = 0 := by
  apply part_c
  · simp
  · simp

-- The conclusion of part (i) is non-vacuous: over the field `ℚ` (complete for the zero ideal)
-- the monic polynomial `x` has a simple root.
example : ∃ x : ℚ, (Polynomial.X : Polynomial ℚ).IsRoot x ∧
    IsUnit ((Polynomial.X : Polynomial ℚ).derivative.eval x) := by
  obtain ⟨x, -, hx, -⟩ := part_a (A := ℚ) (f := Polynomial.X) monic_X (0 : ℚ) (by simp) (by simp)
  exact ⟨x, hx, by simp⟩

end sanity

end AtiyahMcdonald69.Ex_10_10

#print axioms AtiyahMcdonald69.Ex_10_10.part_a
#print axioms AtiyahMcdonald69.Ex_10_10.part_b
#print axioms AtiyahMcdonald69.Ex_10_10.part_c
