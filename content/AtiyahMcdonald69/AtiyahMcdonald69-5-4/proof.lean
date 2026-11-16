/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 5, Exercise 4.

**Statement (book).** Let `A` be a subring of a ring `B` such that `B` is integral over `A`.
Let `𝔫` be a maximal ideal of `B` and let `𝔪 = 𝔫 ∩ A` be the corresponding maximal ideal
of `A`. Is `B_𝔫` necessarily integral over `A_𝔪`?
[Hint: consider the subring `k[x²-1]` of `k[x]`, where `k` is a field, and let `𝔫 = (x-1)`.
Can the element `1/(x+1)` be integral?]

**Answer: no.**  Below, with `k = ℚ`, `B = ℚ[X]`, `A = ℚ[X²-1] = range(ℚ[T] → ℚ[X], T ↦ X²-1)`,
`𝔫 = (X-1)` and `𝔪 = 𝔫 ∩ A`, we verify all the hypotheses (`B` is integral over `A`, `𝔫` is
maximal, `𝔪` is maximal, `𝔪 = 𝔫 ∩ A`) and then prove that the element
`y = 1/(X+1) ∈ B_𝔫` is *not* integral over `A_𝔪`.  Hence `B_𝔫` is not integral over `A_𝔪`.

The mathematical argument for non-integrality: if `y` satisfied a monic equation
`y^N + a_{N-1}y^{N-1} + ⋯ + a_0 = 0` with `a_i ∈ A_𝔪`, write `a_i = c_i/d_i` with
`d_i ∈ A`, `d_i(-1) ≠ 0`, and multiply by `z^N` where `z = X+1` (a unit of `B_𝔫`) and by the
common denominator `D = ∏ d_i`.  This produces an identity in `B_𝔫` which is the image of the
polynomial `F = ∑_i (c_i ∏_{j≠i} d_j) (X+1)^{N-i} ∈ ℚ[X]`.  Since `B → B_𝔫` is injective (as `B`
is a domain), `F = 0`; evaluating at `X = -1` gives `0 = F(-1) = D(-1) ≠ 0` because every
`d_i(-1) ≠ 0` (an element of `A` vanishing at `-1` would lie in `𝔫 = (X-1)`, as elements of `A`
take the same value at `1` and at `-1`).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_4

open Polynomial

/-! ### The ring extension `A = ℚ[X²-1] ⊆ B = ℚ[X]` -/

/-- The base ring `A = ℚ[X²-1]`, realised as the range of `ℚ[T] →ₐ[ℚ] ℚ[X]`, `T ↦ X²-1`. -/
noncomputable def A : Subalgebra ℚ ℚ[X] := (Polynomial.aeval (X ^ 2 - 1)).range

lemma X_sq_sub_one_mem : (X : ℚ[X]) ^ 2 - 1 ∈ A := ⟨X, by simp⟩

lemma algebraMap_X_sq_sub_one :
    algebraMap ↥A ℚ[X] ⟨(X : ℚ[X]) ^ 2 - 1, X_sq_sub_one_mem⟩ = X ^ 2 - 1 := rfl

lemma isConstant_mem (q : ℚ) : (C q : ℚ[X]) ∈ A := by
  refine ⟨C q, ?_⟩
  simp

/-- `X` is integral over `A`, since `X² = (X²-1) + 1` with `X²-1 ∈ A`. -/
theorem isIntegral_X : IsIntegral ↥A (X : ℚ[X]) := by
  have h2 : IsIntegral ↥A ((X : ℚ[X]) ^ 2) := by
    have h : IsIntegral ↥A
        (algebraMap ↥A ℚ[X] ⟨(X : ℚ[X]) ^ 2 - 1, X_sq_sub_one_mem⟩ + 1) :=
      IsIntegral.add isIntegral_algebraMap isIntegral_one
    rwa [algebraMap_X_sq_sub_one, sub_add_cancel] at h
  exact IsIntegral.of_pow (by norm_num) h2

/-- Every polynomial is integral over `A`. -/
theorem isIntegral_polynomial (f : ℚ[X]) : IsIntegral ↥A f := by
  induction f using Polynomial.induction_on with
  | C a =>
    have h : (C a : ℚ[X]) = algebraMap ↥A ℚ[X] ⟨C a, isConstant_mem a⟩ := rfl
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq => exact hp.add hq
  | monomial n a h =>
    have h1 : (C a * X ^ (n + 1) : ℚ[X]) = C a * X ^ n * X := by ring
    rw [h1]
    exact h.mul isIntegral_X

/-- **Hypothesis of the exercise**: `B = ℚ[X]` is integral over `A = ℚ[X²-1]`. -/
theorem B_integral : Algebra.IsIntegral ↥A ℚ[X] := ⟨isIntegral_polynomial⟩

/-! ### The ideals `𝔫 = (X-1)` and `𝔪 = 𝔫 ∩ A` -/

/-- `𝔫 = (X - 1)`, an ideal of `B = ℚ[X]`. -/
noncomputable def n : Ideal ℚ[X] := Ideal.span {X - 1}

/-- `𝔪 = 𝔫 ∩ A`, the contraction of `𝔫 = (X-1)` to `A = ℚ[X²-1]`. -/
noncomputable def m : Ideal ↥A := n.comap (algebraMap ↥A ℚ[X])

lemma m_def : m = n.comap (algebraMap ↥A ℚ[X]) := rfl

/-- Every element of `A = ℚ[X²-1]` takes the same value at `1` and at `-1`. -/
lemma eval_one_eq_eval_neg_one (d : ↥A) : (d : ℚ[X]).eval 1 = (d : ℚ[X]).eval (-1) := by
  obtain ⟨g, hg⟩ := d.2
  have hcomp : (d : ℚ[X]) = g.comp (X ^ 2 - 1) :=
    hg.symm.trans (Polynomial.comp_eq_aeval).symm
  rw [hcomp, Polynomial.eval_comp]
  norm_num

/-- Membership in `𝔪` is vanishing at `-1`. -/
lemma mem_m_iff (d : ↥A) : d ∈ m ↔ (d : ℚ[X]).eval (-1) = 0 := by
  have key : (algebraMap ↥A ℚ[X]) d = (d : ℚ[X]) := rfl
  rw [m, Ideal.mem_comap, n, Ideal.mem_span_singleton, key,
    show (X - 1 : ℚ[X]) = X - C 1 by norm_num,
    Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, eval_one_eq_eval_neg_one d]

/-- `𝔫 = (X-1)` is a maximal ideal of `B = ℚ[X]`. -/
theorem n_isMaximal : n.IsMaximal := by
  rw [n, show (X - 1 : ℚ[X]) = X - C 1 by norm_num]
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (Polynomial.quotientSpanXSubCAlgEquiv (1 : ℚ)).toMulEquiv.isField (Field.toIsField ℚ)

/-- Evaluation at `-1`, as a ring hom `A → ℚ`. -/
noncomputable def evNeg : ↥A →+* ℚ := (Polynomial.evalRingHom (-1)).comp (algebraMap ↥A ℚ[X])

lemma evNeg_apply (d : ↥A) : evNeg d = (d : ℚ[X]).eval (-1) := rfl

lemma evNeg_surjective : Function.Surjective evNeg := by
  intro q
  exact ⟨⟨C q, isConstant_mem q⟩, by simp [evNeg]⟩

/-- **Hypothesis of the exercise**: `𝔪 = 𝔫 ∩ A` is a maximal ideal of `A`
(its quotient is `A/𝔪 ≅ ℚ`). -/
theorem m_isMaximal : m.IsMaximal := by
  have hker : m = RingHom.ker evNeg := by
    ext d
    rw [RingHom.mem_ker, evNeg_apply, ← mem_m_iff d]
  rw [hker]
  exact RingHom.ker_isMaximal_of_surjective _ evNeg_surjective

instance : n.IsPrime := n_isMaximal.isPrime
instance : m.IsPrime := m_isMaximal.isPrime

/-- `𝔪` contains the element `X² - 1`, so `(X²-1) ⊆ 𝔪`. -/
lemma X_sq_sub_one_mem_m : (⟨(X : ℚ[X]) ^ 2 - 1, X_sq_sub_one_mem⟩ : ↥A) ∈ m := by
  rw [mem_m_iff]
  norm_num

/-- **`𝔪` is the principal ideal `(X²-1)` of `A = ℚ[X²-1]`**, as in the book's hint. -/
theorem m_eq_span : m = Ideal.span {(⟨(X : ℚ[X]) ^ 2 - 1, X_sq_sub_one_mem⟩ : ↥A)} := by
  apply le_antisymm
  · intro d hd
    rw [mem_m_iff] at hd
    obtain ⟨g, hg⟩ := d.2
    have hcomp : (d : ℚ[X]) = g.comp (X ^ 2 - 1) :=
      hg.symm.trans (Polynomial.comp_eq_aeval).symm
    have hg0 : g.eval 0 = 0 := by
      have h1 : (g.comp (X ^ 2 - 1)).eval (-1) = g.eval 0 := by
        rw [Polynomial.eval_comp]
        norm_num
      rw [← h1, ← hcomp, hd]
    have hcoeff : g.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hg0
    obtain ⟨h, hh⟩ := (Polynomial.X_dvd_iff (f := g)).mpr hcoeff
    refine Ideal.mem_span_singleton'.mpr
      ⟨⟨h.comp (X ^ 2 - 1), ⟨h, (Polynomial.comp_eq_aeval).symm⟩⟩, ?_⟩
    apply Subtype.ext
    show (h.comp (X ^ 2 - 1)) * ((X : ℚ[X]) ^ 2 - 1) = (d : ℚ[X])
    rw [hcomp, hh, Polynomial.mul_comp, Polynomial.X_comp]
    ring
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact X_sq_sub_one_mem_m

/-- `X + 1 ∉ 𝔫 = (X-1)`, so `X+1` becomes a unit in `B_𝔫`. -/
lemma X_add_one_notMem_n : (X + 1 : ℚ[X]) ∉ n := by
  rw [n, Ideal.mem_span_singleton, show (X - 1 : ℚ[X]) = X - C 1 by norm_num,
    Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  norm_num

/-! ### The localizations `A_𝔪` and `B_𝔫` -/

/-- `A_𝔪`, the localization of `A` at `𝔪 = 𝔫 ∩ A`. -/
abbrev Am := Localization.AtPrime m

/-- `B_𝔫`, the localization of `B` at `𝔫 = (X-1)`. -/
abbrev Bn := Localization.AtPrime n

lemma primeCompl_le : m.primeCompl ≤ n.primeCompl.comap (algebraMap ↥A ℚ[X]) :=
  fun _ hx => hx

/-- The natural ring map `A_𝔪 → B_𝔫` induced by `A ⊆ B`. -/
noncomputable def φ : Am →+* Bn :=
  IsLocalization.map (Q := Bn) (algebraMap ↥A ℚ[X]) primeCompl_le

noncomputable instance : Algebra Am Bn := φ.toAlgebra

lemma algebraMap_algebraMap_apply (a : ↥A) :
    algebraMap Am Bn (algebraMap ↥A Am a) = algebraMap ↥A Bn a := by
  rw [RingHom.algebraMap_toAlgebra]
  exact (IsLocalization.map_eq (M := m.primeCompl) (T := n.primeCompl)
    (g := algebraMap ↥A ℚ[X]) (hy := primeCompl_le) (Q := Bn) a).trans
    (IsScalarTower.algebraMap_apply ↥A ℚ[X] Bn a).symm

instance : IsScalarTower ↥A Am Bn :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (algebraMap_algebraMap_apply a).symm)

/-- The element `1/(X+1) ∈ B_𝔫`. -/
noncomputable def y : Bn := IsLocalization.mk' Bn 1 (⟨X + 1, X_add_one_notMem_n⟩ : n.primeCompl)

/-- The element `X+1 ∈ B_𝔫`, a unit since `X+1 ∉ 𝔫`. -/
noncomputable def z : Bn := algebraMap ℚ[X] Bn (X + 1)

lemma z_mul_y : z * y = 1 := by
  rw [z, y, mul_comm, IsLocalization.mk'_spec, map_one]

lemma y_mul_z : y * z = 1 := by rw [mul_comm, z_mul_y]

lemma algebraMap_injective : Function.Injective (algebraMap ℚ[X] Bn) :=
  FaithfulSMul.algebraMap_injective ℚ[X] Bn


set_option maxHeartbeats 1000000 in
/-- **Exercise 5.4, the counterexample**: `1/(X+1)` is not integral over `A_𝔪`. -/
theorem not_integral_y : ¬ IsIntegral Am y := by
  rintro ⟨P, hPmonic, hP0⟩
  set N := P.natDegree with hN
  have hPN : P.coeff N = 1 := hPmonic.coeff_natDegree
  -- Step 1: the relation as a finite sum
  have hsum : ∑ i ∈ Finset.range (N + 1), algebraMap Am Bn (P.coeff i) * y ^ i = 0 := by
    rw [← hP0, Polynomial.eval₂_eq_sum_range]
  -- Step 2: multiply by `z^N`
  have hrev : ∑ i ∈ Finset.range (N + 1), algebraMap Am Bn (P.coeff i) * z ^ (N - i) = 0 := by
    have hmul := congr_arg (· * z ^ N) hsum
    rw [Finset.sum_mul, zero_mul] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hzN : z ^ N = z ^ i * z ^ (N - i) := by
      conv_lhs => rw [← Nat.add_sub_of_le hi', pow_add]
    have hterm : y ^ i * z ^ N = z ^ (N - i) := by
      rw [hzN, ← mul_assoc, ← mul_pow, mul_comm y z, z_mul_y, one_pow, one_mul]
    rw [mul_assoc, hterm]
  -- Step 3: choose denominators for the coefficients
  have hsurj : ∀ i, ∃ (c : ↥A) (d : m.primeCompl),
      P.coeff i * algebraMap ↥A Am (d : ↥A) = algebraMap ↥A Am c := by
    intro i
    obtain ⟨⟨c, d⟩, hd⟩ := IsLocalization.surj (M := m.primeCompl) (S := Am) (P.coeff i)
    exact ⟨c, d, hd⟩
  choose c d hcd using hsurj
  set D : ↥A := ∏ i ∈ Finset.range (N + 1), (d i : ↥A) with hD
  have hDmem : D ∈ m.primeCompl := Submonoid.prod_mem _ fun i _ => (d i).2
  set q : ℕ → ↥A := fun i => c i * ∏ j ∈ Finset.range (N + 1) \ {i}, (d j : ↥A) with hq
  have hqD : ∀ i ∈ Finset.range (N + 1),
      P.coeff i * algebraMap ↥A Am D = algebraMap ↥A Am (q i) := by
    intro i hi
    have hsplit : D = (d i : ↥A) * ∏ j ∈ Finset.range (N + 1) \ {i}, (d j : ↥A) := by
      rw [hD, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hi]
    rw [hsplit, hq, map_mul, map_mul, ← hcd i, mul_assoc, ← map_mul]
  -- Step 4: multiply the reversed relation by the common denominator
  have hfin : ∑ i ∈ Finset.range (N + 1), algebraMap ↥A Bn (q i) * z ^ (N - i) = 0 := by
    have hmul := congr_arg (· * algebraMap ↥A Bn D) hrev
    rw [Finset.sum_mul, zero_mul] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hD' : algebraMap ↥A Bn D = algebraMap Am Bn (algebraMap ↥A Am D) :=
      (algebraMap_algebraMap_apply D).symm
    have hq' : algebraMap ↥A Bn (q i) = algebraMap Am Bn (algebraMap ↥A Am (q i)) :=
      (algebraMap_algebraMap_apply (q i)).symm
    have hmain : algebraMap Am Bn (P.coeff i) * z ^ (N - i) * algebraMap ↥A Bn D
        = algebraMap ↥A Bn (q i) * z ^ (N - i) := by
      rw [hD', hq', ← hqD i hi, map_mul]
      ring
    exact hmain.symm
  -- Step 5: recognise the left side as the image of a polynomial `F ∈ ℚ[X]`
  set F : ℚ[X] := ∑ i ∈ Finset.range (N + 1),
    algebraMap ↥A ℚ[X] (q i) * (X + 1) ^ (N - i) with hF
  have hFmap : algebraMap ℚ[X] Bn F = 0 := by
    rw [hF, map_sum, ← hfin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, IsScalarTower.algebraMap_apply ↥A ℚ[X] Bn]
    rfl
  have hFzero : F = 0 := algebraMap_injective (by rw [hFmap, map_zero])
  -- Step 6: evaluate at `-1`
  have hqNne : ((q N : ↥A) : ℚ[X]).eval (-1) ≠ 0 := by
    intro hzero
    have hqm : q N ∈ m := (mem_m_iff (q N)).mpr hzero
    have hNmem : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)
    have hrel : algebraMap ↥A Am D = algebraMap ↥A Am (q N) := by
      rw [← hqD N hNmem, hPN, one_mul]
    obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists m.primeCompl Am).mp hrel
    have hmul : (cc : ↥A) * D ∈ m := by
      rw [hcc]
      exact Ideal.mul_mem_left m (cc : ↥A) hqm
    rcases Ideal.IsPrime.mem_or_mem (I := m) inferInstance hmul with h | h
    · exact cc.2 h
    · exact hDmem h
  have heval : Polynomial.evalRingHom (-1) F = 0 := by rw [hFzero]; simp
  have hone : Polynomial.evalRingHom (-1) F = ((q N : ↥A) : ℚ[X]).eval (-1) := by
    rw [hF, map_sum, Finset.sum_eq_single N]
    · rw [Nat.sub_self, pow_zero, mul_one]
      rfl
    · intro i hi hne
      have hiN : i < N := by
        have := Finset.mem_range.mp hi
        omega
      rw [map_mul, map_pow, show (Polynomial.evalRingHom (-1)) (X + 1 : ℚ[X]) = 0 by simp,
        zero_pow (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)) h
  rw [hone] at heval
  exact hqNne heval

/-- `B_𝔫` is not integral over `A_𝔪` (the literal negation of the question). -/
theorem not_isIntegral_algebra : ¬ Algebra.IsIntegral Am Bn :=
  fun h => not_integral_y (h.isIntegral y)

/-- **Atiyah–Macdonald, Exercise 5.4: the answer is `no`.**

For `A = ℚ[X²-1] ⊆ B = ℚ[X]` (`B` integral over `A`), `𝔫 = (X-1)` maximal in `B` and
`𝔪 = 𝔫 ∩ A` maximal in `A`, the localization `B_𝔫` is not integral over `A_𝔪`: no inverse
of `X+1` in `B_𝔫` is integral over `A_𝔪`.  (The inverse `1/(X+1)` is `y`, and
`y * z = 1` where `z` is the image of `X+1`.) -/
theorem solution :
    Algebra.IsIntegral ↥A ℚ[X] ∧ n.IsMaximal ∧ m.IsMaximal ∧
      ¬ Algebra.IsIntegral Am Bn ∧ (∀ y' : Bn, y' * z = 1 → ¬ IsIntegral Am y') :=
  ⟨B_integral, n_isMaximal, m_isMaximal, not_isIntegral_algebra, fun y' hy' => by
    have hyy : y' = y := by
      rw [← mul_one y', ← z_mul_y, ← mul_assoc, hy', one_mul]
    rw [hyy]
    exact not_integral_y⟩

end AtiyahMcdonald69.Ex_5_4

#print axioms AtiyahMcdonald69.Ex_5_4.solution
#print axioms AtiyahMcdonald69.Ex_5_4.not_integral_y
#print axioms AtiyahMcdonald69.Ex_5_4.not_isIntegral_algebra
#print axioms AtiyahMcdonald69.Ex_5_4.B_integral
#print axioms AtiyahMcdonald69.Ex_5_4.n_isMaximal
#print axioms AtiyahMcdonald69.Ex_5_4.m_isMaximal
#print axioms AtiyahMcdonald69.Ex_5_4.m_eq_span
#print axioms AtiyahMcdonald69.Ex_5_4.isIntegral_X
