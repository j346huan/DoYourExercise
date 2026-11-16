/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 1, Exercise 2.
Complete formalisation of all four parts, for one indeterminate.

The statement, restored from the book text (`.scratch/reference/atiyah-macdonald-original.txt`
and the local transcription `.scratch/dl/amcd.tex`, "Page 11, Exercise 1.2"):

  Let `A` be a ring and let `A[x]` be the ring of polynomials in an indeterminate `x`, with
  coefficients in `A`.  Let `f = a₀ + a₁x + ⋯ + aₙxⁿ ∈ A[x]`.  Prove that

  (i)   `f` is a unit in `A[x]` ⟺ `a₀` is a unit in `A` and `a₁, …, aₙ` are nilpotent;
  (ii)  `f` is nilpotent ⟺ `a₀, a₁, …, aₙ` are nilpotent;
  (iii) `f` is a zero-divisor ⟺ there exists `a ≠ 0` in `A` such that `a f = 0`;
  (iv)  `f` is *primitive* if `(a₀, a₁, …, aₙ) = (1)`.  Prove that if `f, g ∈ A[x]`, then
        `f g` is primitive ⟺ `f` and `g` are primitive.

Everything is stated for an arbitrary commutative ring `A` (the zero ring included), and the
book's `n` is allowed to be any bound on the degree; coefficients of index `> n` are zero and
therefore nilpotent, so the versions below with all coefficients indexed by `ℕ` and the literal
versions with a degree bound `n` are equivalent.

Mathlib lemmas used, after checking their exact statements:
* part (i):  `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`
             (`IsUnit P ↔ IsUnit (P.coeff 0) ∧ ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)`)
             — this is exactly the book's (i), since `0 < i ↔ i ≠ 0` on `ℕ`;
* part (ii): `Polynomial.isNilpotent_iff` (`IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i)`);
* part (iv): `Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top` (Gauss: a product of
             primitive polynomials is primitive) and
             `Polynomial.contentIdeal_eq_top_of_contentIdeal_mul_eq_top` (a factor of a
             primitive polynomial is primitive), both for the content ideal
             `p.contentIdeal = Ideal.span p.coeffs`, which is `Ideal.span (Set.range p.coeff)`.
Part (iii) is proved here from scratch (McCoy's theorem).
-/
import Mathlib

set_option autoImplicit false

namespace AtiyahMcdonald69.Ex_1_2

open Polynomial

variable {R : Type*} [CommRing R]

/-! ### Part (i): units of `A[x]` -/

/-- **Exercise 1.2 (i).**  `f` is a unit of `A[x]` iff its constant coefficient is a unit of `A`
and all its coefficients of positive index are nilpotent. -/
theorem isUnit_iff_coeff_zero_isUnit_coeff_pos_isNilpotent (f : R[X]) :
    IsUnit f ↔ IsUnit (f.coeff 0) ∧ ∀ i : ℕ, 0 < i → IsNilpotent (f.coeff i) := by
  rw [Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [Nat.pos_iff_ne_zero]

/-- **Exercise 1.2 (i)**, in the literal form of the book: if `f = a₀ + a₁x + ⋯ + aₙxⁿ`
(that is, `n ≥ natDegree f`), then `f` is a unit iff `a₀` is a unit and `a₁, …, aₙ` are
nilpotent. -/
theorem isUnit_iff_coeff_zero_isUnit_coeff_pos_isNilpotent_le (f : R[X]) {n : ℕ}
    (hn : f.natDegree ≤ n) :
    IsUnit f ↔ IsUnit (f.coeff 0) ∧ ∀ i : ℕ, 0 < i → i ≤ n → IsNilpotent (f.coeff i) := by
  rw [isUnit_iff_coeff_zero_isUnit_coeff_pos_isNilpotent]
  refine and_congr Iff.rfl ⟨fun h i hi _ => h i hi, fun h i hi => ?_⟩
  by_cases hin : i ≤ n
  · exact h i hi hin
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact IsNilpotent.zero

/-! ### Part (ii): nilpotents of `A[x]` -/

/-- **Exercise 1.2 (ii).**  `f` is nilpotent iff all its coefficients are nilpotent. -/
theorem isNilpotent_iff_forall_coeff_isNilpotent (f : R[X]) :
    IsNilpotent f ↔ ∀ i : ℕ, IsNilpotent (f.coeff i) :=
  Polynomial.isNilpotent_iff

/-- **Exercise 1.2 (ii)**, in the literal form of the book: if `n ≥ natDegree f`, then `f` is
nilpotent iff `a₀, a₁, …, aₙ` are nilpotent. -/
theorem isNilpotent_iff_forall_coeff_isNilpotent_le (f : R[X]) {n : ℕ} (hn : f.natDegree ≤ n) :
    IsNilpotent f ↔ ∀ i : ℕ, i ≤ n → IsNilpotent (f.coeff i) := by
  rw [isNilpotent_iff_forall_coeff_isNilpotent]
  exact ⟨fun h i _ => h i, fun h i => by
    by_cases hin : i ≤ n
    · exact h i hin
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact IsNilpotent.zero⟩

/-! ### Part (iii): zero-divisors of `A[x]` (McCoy's theorem)

The elementary proof of the book: choose a nonzero annihilator `g` of `f` of minimal degree.
Every coefficient `a` of `f` gives an annihilator `a • g` of `f`; if it is nonzero its degree is
smaller than that of `g`, because `a` kills the leading coefficient of `g` (otherwise the leading
coefficient of `f g` would be nonzero).  Hence every coefficient of `f` annihilates `g`, and any
nonzero coefficient of `g` annihilates `f`.

The formal proof below implements the same argument using strong induction on the degree of the
annihilator instead of a minimality assumption. -/

/-- Auxiliary lemma for part (iii): if every coefficient of `f` of index `> i` annihilates `g`,
then the coefficient of `X^(i + natDegree g)` in `f * g` is `f.coeff i * g.coeff (natDegree g)`.
Indeed all terms of the antidiagonal sum of index `< i` vanish because they involve a
coefficient of `g` above its degree, and all terms of index `> i` vanish because the
corresponding coefficient of `f` annihilates `g`. -/
lemma coeff_mul_natDegree_add_of_forall_coeff_mul_eq_zero {f g : R[X]} {i : ℕ}
    (H : ∀ j, i < j → C (f.coeff j) * g = 0) :
    (f * g).coeff (i + g.natDegree) = f.coeff i * g.coeff g.natDegree := by
  rw [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (M := R) (fun a b => f.coeff a * g.coeff b)]
  have hsum := Finset.sum_eq_single (s := Finset.range (i + g.natDegree).succ)
    (f := fun k => f.coeff k * g.coeff (i + g.natDegree - k)) i ?_ ?_
  · rw [hsum, Nat.add_sub_cancel_left]
  · intro j hj hji
    simp only [Finset.mem_range] at hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hk : g.natDegree < i + g.natDegree - j := by
        rw [Nat.lt_sub_iff_add_lt]; omega
      rw [coeff_eq_zero_of_natDegree_lt (p := g) hk, mul_zero]
    · have h1 := congrArg (fun p : R[X] => p.coeff (i + g.natDegree - j)) (H j hgt)
      simpa using h1
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    omega

/-- Auxiliary lemma for part (iii) (McCoy): if a nonzero polynomial `g` annihilates `f`, then
some nonzero *constant* annihilates `f`. -/
lemma exists_ne_zero_C_mul_eq_zero_of_mul_eq_zero {f g : R[X]} (hg : g ≠ 0) (hfg : f * g = 0) :
    ∃ a : R, a ≠ 0 ∧ C a * f = 0 := by
  -- Strong induction on a bound for the degree of the annihilator.
  have key : ∀ M : ℕ, ∀ g : R[X], g.natDegree ≤ M → ∀ f : R[X], f * g = 0 → g ≠ 0 →
      ∃ a : R, a ≠ 0 ∧ C a * f = 0 := by
    intro M
    refine Nat.strong_induction_on M ?_
    intro M ih g hdeg f hfg hg0
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · exact ih g.natDegree hlt g le_rfl f hfg hg0
    -- From now on `g` has degree `M`, so `ih` applies to annihilators of `f` of smaller degree.
    -- If all coefficients of `f` of index `> i` annihilate `g`, then so does `f.coeff i`,
    -- unless we are already done.
    have step : ∀ i : ℕ, (∀ j, i < j → C (f.coeff j) * g = 0) →
        C (f.coeff i) * g = 0 ∨ ∃ a : R, a ≠ 0 ∧ C a * f = 0 := by
      intro i H
      by_cases h0 : C (f.coeff i) * g = 0
      · exact Or.inl h0
      refine Or.inr (ih (C (f.coeff i) * g).natDegree ?_ (C (f.coeff i) * g) le_rfl f ?_ h0)
      · -- the degree drops, because `f.coeff i` kills the leading coefficient of `g`
        have hcoeff : f.coeff i * g.coeff g.natDegree = 0 := by
          have h := coeff_mul_natDegree_add_of_forall_coeff_mul_eq_zero H
          rw [hfg, coeff_zero] at h
          exact h.symm
        have hle := natDegree_C_mul_le (f.coeff i) g
        rcases lt_or_eq_of_le hle with h | h
        · omega
        · exfalso
          have hlead : (C (f.coeff i) * g).coeff (C (f.coeff i) * g).natDegree ≠ 0 :=
            leadingCoeff_ne_zero.mpr h0
          rw [h, coeff_C_mul, hcoeff] at hlead
          exact hlead rfl
      · -- it is again an annihilator of `f`
        rw [← mul_assoc, mul_comm f (C (f.coeff i)), mul_assoc, hfg, mul_zero]
    -- Reverse induction: either we are done, or every coefficient of `f` annihilates `g`.
    have hR : ∀ k : ℕ, ∀ i : ℕ, f.natDegree - i = k → i ≤ f.natDegree →
        ((∀ j, i ≤ j → j ≤ f.natDegree → C (f.coeff j) * g = 0) ∨
          ∃ a : R, a ≠ 0 ∧ C a * f = 0) := by
      intro k
      refine Nat.strong_induction_on k ?_
      intro k ihk i hk hiN
      rcases eq_or_lt_of_le hiN with rfl | hlt
      · -- the top coefficient of `f` annihilates `g`
        rcases step f.natDegree (fun j hj => by
          rw [coeff_eq_zero_of_natDegree_lt hj, C_0, zero_mul]) with h | h
        · exact Or.inl fun j hj hle => by rw [le_antisymm hle hj]; exact h
        · exact Or.inr h
      · rcases ihk (f.natDegree - (i + 1)) (by omega) (i + 1) (by omega) (by omega) with H | H
        · rcases step i (fun j hj => by
            by_cases hjN : j ≤ f.natDegree
            · exact H j (by omega) hjN
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), C_0, zero_mul]) with h | h
          · refine Or.inl fun j hij hjN => ?_
            rcases eq_or_lt_of_le hij with rfl | hlt'
            · exact h
            · exact H j (by omega) hjN
          · exact Or.inr h
        · exact Or.inr H
    rcases hR f.natDegree 0 (by omega) (Nat.zero_le _) with H | H
    · -- every coefficient of `f` annihilates `g`; a nonzero coefficient of `g` annihilates `f`
      obtain ⟨j, hj⟩ : ∃ j : ℕ, g.coeff j ≠ 0 := by
        by_contra hcon
        refine hg0 (Polynomial.ext fun n => ?_)
        rw [coeff_zero]
        by_contra h
        exact hcon ⟨n, h⟩
      refine ⟨g.coeff j, hj, ?_⟩
      ext n
      rw [coeff_C_mul, coeff_zero]
      have hkill : C (f.coeff n) * g = 0 := by
        by_cases hn : n ≤ f.natDegree
        · exact H n (Nat.zero_le n) hn
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), C_0, zero_mul]
      have h2 := congrArg (fun p : R[X] => p.coeff j) hkill
      simp only [coeff_C_mul, coeff_zero] at h2
      rw [mul_comm (g.coeff j) (f.coeff n), h2]
    · exact H
  exact key g.natDegree g le_rfl f hfg hg

/-- **Exercise 1.2 (iii).**  `f` is a zero-divisor of `A[x]` iff some nonzero element of `A`
annihilates it. -/
theorem exists_ne_zero_mul_eq_zero_iff (f : R[X]) :
    (∃ g : R[X], g ≠ 0 ∧ f * g = 0) ↔ ∃ a : R, a ≠ 0 ∧ C a * f = 0 := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    exact exists_ne_zero_C_mul_eq_zero_of_mul_eq_zero hg hfg
  · rintro ⟨a, ha, hfa⟩
    exact ⟨C a, by simpa using ha, by rw [mul_comm]; exact hfa⟩

/-! ### Part (iv): primitive polynomials -/

/-- **Exercise 1.2 (iv)**: `f` is primitive if the ideal of `A` generated by its coefficients
is the unit ideal, `(a₀, a₁, …, aₙ) = (1)`. -/
def Primitive (f : R[X]) : Prop := Ideal.span (Set.range f.coeff) = ⊤

/-- The content ideal of `f` (the ideal generated by its nonzero coefficients) is the ideal
generated by all of its coefficients. -/
lemma contentIdeal_eq_span_range_coeff (f : R[X]) :
    f.contentIdeal = Ideal.span (Set.range f.coeff) := by
  rw [contentIdeal_def]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact Ideal.subset_span ⟨n, rfl⟩
  · rw [Ideal.span_le]
    rintro c ⟨n, rfl⟩
    by_cases h : f.coeff n = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Ideal.subset_span (coeff_mem_coeffs h)

lemma primitive_iff_contentIdeal_eq_top (f : R[X]) : Primitive f ↔ f.contentIdeal = ⊤ := by
  rw [Primitive, contentIdeal_eq_span_range_coeff]

lemma primitive_one : Primitive (1 : R[X]) := by
  rw [Primitive, Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩

/-- **Exercise 1.2 (iv).**  A product is primitive iff both factors are primitive. -/
theorem primitive_mul_iff (f g : R[X]) : Primitive (f * g) ↔ Primitive f ∧ Primitive g := by
  rw [primitive_iff_contentIdeal_eq_top, primitive_iff_contentIdeal_eq_top,
    primitive_iff_contentIdeal_eq_top]
  constructor
  · intro hfg
    exact ⟨contentIdeal_eq_top_of_contentIdeal_mul_eq_top hfg,
      contentIdeal_eq_top_of_contentIdeal_mul_eq_top (p := g) (q := f) (by rwa [mul_comm])⟩
  · rintro ⟨hf, hg⟩
    exact contentIdeal_mul_eq_top_of_contentIdeal_eq_top hf hg

end AtiyahMcdonald69.Ex_1_2

/-! ### Axiom checks for all exports (only `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms AtiyahMcdonald69.Ex_1_2.isUnit_iff_coeff_zero_isUnit_coeff_pos_isNilpotent
#print axioms AtiyahMcdonald69.Ex_1_2.isUnit_iff_coeff_zero_isUnit_coeff_pos_isNilpotent_le
#print axioms AtiyahMcdonald69.Ex_1_2.isNilpotent_iff_forall_coeff_isNilpotent
#print axioms AtiyahMcdonald69.Ex_1_2.isNilpotent_iff_forall_coeff_isNilpotent_le
#print axioms AtiyahMcdonald69.Ex_1_2.coeff_mul_natDegree_add_of_forall_coeff_mul_eq_zero
#print axioms AtiyahMcdonald69.Ex_1_2.exists_ne_zero_C_mul_eq_zero_of_mul_eq_zero
#print axioms AtiyahMcdonald69.Ex_1_2.exists_ne_zero_mul_eq_zero_iff
#print axioms AtiyahMcdonald69.Ex_1_2.contentIdeal_eq_span_range_coeff
#print axioms AtiyahMcdonald69.Ex_1_2.primitive_iff_contentIdeal_eq_top
#print axioms AtiyahMcdonald69.Ex_1_2.primitive_one
#print axioms AtiyahMcdonald69.Ex_1_2.primitive_mul_iff
