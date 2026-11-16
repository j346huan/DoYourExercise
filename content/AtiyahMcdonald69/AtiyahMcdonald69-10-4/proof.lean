/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 10 (Completions), Exercise 4 (book page 114).

**Original statement** (verbatim, from the text of the book):

  "Let `A` be a Noetherian ring, `𝔞` an ideal in `A`, and `Â` the `𝔞`-adic completion.
   For any `x ∈ A`, let `x̂` be the image of `x` in `Â`. Show that

        `x` not a zero-divisor in `A`  ⟹  `x̂` not a zero-divisor in `Â`.

   Does this imply that

        `A` is an integral domain  ⟹  `Â` is an integral domain?

   [Apply the exactness of completion to the sequence `0 → A --x--> A`.]"

**Coverage.** Both parts are formalized, with the book's quantifiers intact.

* `part_a` : for every Noetherian ring `A`, every ideal `I` of `A`, and every `x : A` which
  is not a zero-divisor in `A` (rendered as injectivity of multiplication by `x`, see
  `not_isZeroDivisor_iff`), the image `AdicCompletion.of I A x` in the `I`-adic completion
  is not a zero-divisor in `AdicCompletion I A`.  `part_a_isZeroDivisor` is the same
  statement phrased with the book's own predicate `IsZeroDivisor` ("annihilates a nonzero
  element", AM p. 2).  No properness of `I` is assumed, exactly as in the book; for
  `I = ⊤` the completion is the zero ring and the statement still holds.
* `part_b` : the answer to the book's question is **NO**.  `part_b` is the negation of the
  displayed implication (so it is refuted, not assumed); the counterexample is
  `A = ℤ`, `𝔞 = (6)` (`not_isDomain_adicCompletion_six`), together with
  `exists_zero_divisors`, which exhibits two explicit nonzero elements of
  `AdicCompletion (6) ℤ` with zero product, and `part_b_counterexample`, the existential
  form of the failure.

**Approach.**

* (a) The book's hint is to apply exactness of completion to `0 → A --x--> A`.  The Mathlib
  form of that exactness is `AdicCompletion.map_injective`: completion of an injective map
  of finite modules over a Noetherian ring is injective.  The only work is to identify
  `AdicCompletion.map I (LinearMap.mulLeft A x)` with multiplication by
  `AdicCompletion.of I A x` on the completion (`map_mulLeft`); this uses that
  `AdicCompletion.map I f` is linear over the completion, together with `map_of`,
  `LinearMap.map_smul`, and the fact that `1` in the completion is the image of `1`.
* (b) `ℤ` is a Noetherian domain, but its `(6)`-adic completion is `ℤ_2 × ℤ_3`, which is not
  a domain.  Instead of computing that isomorphism we exhibit the Chinese-remainder
  idempotent `e = lim_n 3^(2^(n-1)) mod 6^n` (congruent to `1` mod `2^n` and to `0` mod
  `3^n`) as a compatible sequence (`seq`, `sModEq_seq`, `eZ`), prove `e * e = e`
  (`eZ_mul_self`), `e ≠ 0` (`eZ_ne_zero`) and `e ≠ 1` (`eZ_ne_one`) by evaluating at the
  levels `n`, resp. `1`, with `AdicCompletion.evalₐ`, and conclude that `e * (1 - e) = 0`
  with both factors nonzero.  The arithmetic input is
  `2^(k+1) ∣ 3^(2^k) - 1` (`two_pow_dvd_three`), which yields
  `6^(k+1) ∣ 3^(2^(k+1)) - 3^(2^k)` (`six_pow_dvd_three`).

**Statement adaptation.** None mathematically.  "`x` is not a zero-divisor in `A`" is
rendered by the classically equivalent form `∀ y, x * y = 0 → y = 0` (equivalence with AM's
definition is proved in `not_isZeroDivisor_iff`), the formulation used by the Mathlib API.

Checked with `lean -DwarningAsError=true`, using the Lean 4.33.1 toolchain that the Mathlib
build in `/opt/mathlib` was compiled with (`/opt/lean/bin/lean`; note that the `lean`
found on `PATH` here is 4.35.0 and cannot read those oleans).

Source proof URL (natural-language solution, covering (a) and the `ℤ`, `(6)` counterexample):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-10-4
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Tactic

namespace AtiyahMcdonald69.Ex_10_4

open AdicCompletion

/-! ## Zero-divisors (AM, p. 2) -/

section ZeroDivisor

variable {A : Type*} [CommRing A]

/-- AM's notion: `x` is a zero-divisor in `A` if it annihilates some nonzero element. -/
def IsZeroDivisor (x : A) : Prop := ∃ y, y ≠ 0 ∧ x * y = 0

/-- Being a zero-divisor is the same as multiplication by `x` failing to be injective. -/
theorem not_isZeroDivisor_iff {x : A} : ¬ IsZeroDivisor x ↔ ∀ y, x * y = 0 → y = 0 := by
  constructor
  · intro h y hy
    by_contra hne
    exact h ⟨y, hne, hy⟩
  · rintro h ⟨y, hyne, hy⟩
    exact hyne (h y hy)

end ZeroDivisor

/-! ## Part (a): nonzero-divisors survive completion -/

section PartA

variable {A : Type*} [CommRing A]

/-- Multiplication by `x` on `A` and multiplication by the image of `x` on the `I`-adic
completion agree under `AdicCompletion.map`. -/
theorem map_mulLeft (I : Ideal A) (x : A) (z : AdicCompletion I A) :
    AdicCompletion.map I (LinearMap.mulLeft A x) z = AdicCompletion.of I A x * z := by
  have h1 : AdicCompletion.map I (LinearMap.mulLeft A x) 1 = AdicCompletion.of I A x := by
    have hone : (1 : AdicCompletion I A) = AdicCompletion.of I A 1 := by
      ext n
      simp
    rw [hone, AdicCompletion.map_of, LinearMap.mulLeft_apply, mul_one]
  calc AdicCompletion.map I (LinearMap.mulLeft A x) z
      = AdicCompletion.map I (LinearMap.mulLeft A x) (z * 1) := by rw [mul_one]
    _ = AdicCompletion.map I (LinearMap.mulLeft A x) (z • (1 : AdicCompletion I A)) := by
          rw [smul_eq_mul, mul_one]
    _ = z • AdicCompletion.map I (LinearMap.mulLeft A x) 1 := LinearMap.map_smul _ z 1
    _ = z • AdicCompletion.of I A x := by rw [h1]
    _ = z * AdicCompletion.of I A x := smul_eq_mul z _
    _ = AdicCompletion.of I A x * z := mul_comm _ _

/-- **Exercise 10.4 (a).**  Let `A` be a Noetherian ring, `𝔞` an ideal of `A` and `x ∈ A`
not a zero-divisor; then the image of `x` in the `𝔞`-adic completion is not a zero-divisor
either. -/
theorem part_a [IsNoetherianRing A] (I : Ideal A) {x : A}
    (hx : ∀ y : A, x * y = 0 → y = 0) :
    ∀ z : AdicCompletion I A, AdicCompletion.of I A x * z = 0 → z = 0 := by
  have hinj : Function.Injective (LinearMap.mulLeft A x) := by
    intro a b hab
    have hab' : x * a = x * b := hab
    have h : x * (a - b) = 0 := by
      rw [mul_sub, hab', sub_self]
    exact sub_eq_zero.mp (hx (a - b) h)
  intro z hz
  have hmap : AdicCompletion.map I (LinearMap.mulLeft A x) z = 0 := by
    rw [map_mulLeft, hz]
  have hinj' := AdicCompletion.map_injective I (M := A) (N := A) hinj
  exact hinj' (by simpa using hmap)

/-- **Exercise 10.4 (a)**, in the book's own words (`x` is not a zero-divisor). -/
theorem part_a_isZeroDivisor [IsNoetherianRing A] (I : Ideal A) {x : A}
    (hx : ¬ IsZeroDivisor x) : ¬ IsZeroDivisor (AdicCompletion.of I A x) := by
  rw [not_isZeroDivisor_iff] at hx ⊢
  exact part_a I hx

end PartA

/-! ## Part (b): the completion of a domain need not be a domain

The counterexample is `A = ℤ` with `𝔞 = (6)`.  The `(6)`-adic completion of `ℤ` is
`ℤ_2 × ℤ_3`; the Chinese-remainder idempotent `(1, 0)` is the compatible family
`3 ^ 2 ^ (n-1) mod 6^n` (which is `1` mod `2^n` and `0` mod `3^n`). -/

/-! ### Integer arithmetic -/

/-- `2 ∣ 3^m + 1` for every `m`. -/
lemma two_dvd_three_pow_add_one (m : ℕ) : (2 : ℤ) ∣ (3 : ℤ) ^ m + 1 := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    have hk : (3 : ℤ) ^ k = 2 * t - 1 := by linarith
    refine ⟨3 * t - 1, ?_⟩
    rw [pow_succ]
    linear_combination 3 * hk

/-- `2^(k+1) ∣ 3^(2^k) - 1`. -/
lemma two_pow_dvd_three (k : ℕ) : (2 : ℤ) ^ (k + 1) ∣ (3 : ℤ) ^ 2 ^ k - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu⟩ := two_dvd_three_pow_add_one (2 ^ k)
    have hsq : (3 : ℤ) ^ 2 ^ (k + 1) = ((3 : ℤ) ^ 2 ^ k) ^ 2 := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]
    have h2k : (2 : ℤ) ^ (k + 2) = 2 ^ (k + 1) * 2 := by
      rw [show k + 2 = k + 1 + 1 from rfl, pow_succ]
    refine ⟨t * u, ?_⟩
    rw [hsq, h2k]
    calc ((3 : ℤ) ^ 2 ^ k) ^ 2 - 1
        = ((3 : ℤ) ^ 2 ^ k - 1) * ((3 : ℤ) ^ 2 ^ k + 1) := by ring
      _ = (2 ^ (k + 1) * t) * (2 * u) := by rw [ht, hu]
      _ = 2 ^ (k + 1) * 2 * (t * u) := by ring

/-- `k + 1 ≤ 2 ^ k`. -/
lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 * (k + 1) ≤ 2 * 2 ^ k := by omega
    rw [pow_succ]
    omega

/-- `6^(k+1) ∣ 3^(2^(k+1)) - 3^(2^k)`. -/
lemma six_pow_dvd_three (k : ℕ) :
    (6 : ℤ) ^ (k + 1) ∣ (3 : ℤ) ^ 2 ^ (k + 1) - (3 : ℤ) ^ 2 ^ k := by
  have h2 : (2 : ℤ) ^ (k + 1) ∣ (3 : ℤ) ^ 2 ^ k - 1 := two_pow_dvd_three k
  have h3 : (3 : ℤ) ^ (k + 1) ∣ (3 : ℤ) ^ 2 ^ k :=
    pow_dvd_pow 3 (succ_le_two_pow k)
  have h6 : (6 : ℤ) ^ (k + 1) = (3 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) := by
    rw [← mul_pow]
    norm_num
  have hprod : (6 : ℤ) ^ (k + 1) ∣ (3 : ℤ) ^ 2 ^ k * ((3 : ℤ) ^ 2 ^ k - 1) := by
    rw [h6]
    exact mul_dvd_mul h3 h2
  have hgoal : (3 : ℤ) ^ 2 ^ (k + 1) - (3 : ℤ) ^ 2 ^ k
      = (3 : ℤ) ^ 2 ^ k * ((3 : ℤ) ^ 2 ^ k - 1) := by
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]
    ring
  rw [hgoal]
  exact hprod

/-! ### The example `A = ℤ`, `𝔞 = (6)` -/

/-- The ideal `(6)` of `ℤ`. -/
def I6 : Ideal ℤ := Ideal.span {(6 : ℤ)}

/-- `3 ^ 2 ^ (n-1)`: the level `n` representative of the CRT idempotent `(1,0)` of
`ℤ/2^n × ℤ/3^n` (it is `1` mod `2^n` and `0` mod `3^n`). -/
def seq (n : ℕ) : ℤ := (3 : ℤ) ^ 2 ^ (n - 1)

lemma seq_succ (n : ℕ) : seq (n + 1) = (3 : ℤ) ^ 2 ^ n := by
  simp [seq]

lemma I6_pow_eq (n : ℕ) : I6 ^ n = Ideal.span {((6 : ℤ) ^ n)} :=
  Ideal.span_singleton_pow 6 n

lemma mem_I6_pow_iff {n : ℕ} {x : ℤ} : x ∈ I6 ^ n ↔ (6 : ℤ) ^ n ∣ x := by
  rw [I6_pow_eq, Ideal.mem_span_singleton]

lemma I6_pow_smul_top (n : ℕ) : (I6 ^ n • (⊤ : Ideal ℤ) : Ideal ℤ) = I6 ^ n := by
  ext x
  simp

lemma six_pow_dvd_seq (n : ℕ) : (6 : ℤ) ^ n ∣ seq n - seq (n + 1) := by
  rcases n with _ | k
  · exact one_dvd _
  · have h := six_pow_dvd_three k
    have hneg : seq (k + 1) - seq (k + 1 + 1)
        = -((3 : ℤ) ^ 2 ^ (k + 1) - (3 : ℤ) ^ 2 ^ k) := by
      simp only [seq_succ]
      ring
    rw [hneg]
    exact dvd_neg.mpr h

lemma six_pow_dvd_seq_sq (n : ℕ) : (6 : ℤ) ^ n ∣ seq n * seq n - seq n := by
  rcases n with _ | k
  · exact one_dvd _
  · have hsq : seq (k + 1) * seq (k + 1) = seq (k + 2) := by
      rw [seq_succ, seq_succ, ← pow_add,
        show 2 ^ k + 2 ^ k = 2 ^ (k + 1) from by rw [pow_succ]; ring]
    rw [hsq]
    simpa only [seq_succ] using six_pow_dvd_three k

lemma sModEq_seq (n : ℕ) : SModEq (I6 ^ n • (⊤ : Ideal ℤ)) (seq n) (seq (n + 1)) := by
  rw [SModEq.def, Submodule.Quotient.eq, I6_pow_smul_top, mem_I6_pow_iff]
  exact six_pow_dvd_seq n

/-- The CRT idempotent `(1, 0)` in the `(6)`-adic completion of `ℤ`. -/
noncomputable def eZ : AdicCompletion I6 ℤ :=
  AdicCompletion.mk I6 ℤ (AdicCauchySequence.mk I6 ℤ seq sModEq_seq)

lemma evalₐ_eZ (n : ℕ) :
    AdicCompletion.evalₐ I6 n eZ = Ideal.Quotient.mk (I6 ^ n) (seq n) := by
  rw [eZ, AdicCompletion.evalₐ_mk]
  rfl

lemma eZ_mul_self : eZ * eZ = eZ := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_mul, evalₐ_eZ]
  have hmem : seq n * seq n - seq n ∈ I6 ^ n := by
    rw [mem_I6_pow_iff]
    exact six_pow_dvd_seq_sq n
  have hq : Ideal.Quotient.mk (I6 ^ n) (seq n * seq n)
      = Ideal.Quotient.mk (I6 ^ n) (seq n) := Ideal.Quotient.eq.mpr hmem
  simpa using hq

lemma eZ_ne_zero : eZ ≠ 0 := by
  intro h
  have h2 : Ideal.Quotient.mk (I6 ^ 1) (seq 1) = 0 := by
    rw [← evalₐ_eZ, h]
    simp
  have hmem : seq 1 ∈ I6 ^ 1 := Ideal.Quotient.eq_zero_iff_mem.mp h2
  rw [show I6 ^ 1 = Ideal.span {(6 : ℤ)} from by rw [pow_one]; rfl,
    Ideal.mem_span_singleton] at hmem
  have h3 : seq 1 = 3 := by norm_num [seq]
  rw [h3] at hmem
  norm_num at hmem

lemma eZ_ne_one : eZ ≠ 1 := by
  intro h
  have h2 : Ideal.Quotient.mk (I6 ^ 1) (seq 1) = Ideal.Quotient.mk (I6 ^ 1) (1 : ℤ) := by
    rw [← evalₐ_eZ, h]
    simp
  rw [Ideal.Quotient.eq] at h2
  rw [show I6 ^ 1 = Ideal.span {(6 : ℤ)} from by rw [pow_one]; rfl,
    Ideal.mem_span_singleton] at h2
  have h3 : seq 1 = 3 := by norm_num [seq]
  rw [h3] at h2
  norm_num at h2

/-- The `(6)`-adic completion of `ℤ` is not an integral domain. -/
theorem not_isDomain_adicCompletion_six : ¬ IsDomain (AdicCompletion I6 ℤ) := by
  intro h
  have h1 : eZ * (1 - eZ) = 0 := by rw [mul_sub, mul_one, eZ_mul_self, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
  · exact eZ_ne_zero h2
  · exact eZ_ne_one (sub_eq_zero.mp h2).symm

/-- Explicit nonzero zero-divisors in `AdicCompletion (6) ℤ`. -/
theorem exists_zero_divisors :
    ∃ x y : AdicCompletion I6 ℤ, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 :=
  ⟨eZ, 1 - eZ, eZ_ne_zero, sub_ne_zero.mpr eZ_ne_one.symm, by
    rw [mul_sub, mul_one, eZ_mul_self, sub_self]⟩

/-- **Exercise 10.4 (b).**  The implication "`A` integral domain ⟹ `Â` integral domain"
is false: `ℤ` is a Noetherian domain but its `(6)`-adic completion is not a domain. -/
theorem part_b :
    ¬ ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A] (I : Ideal A),
        IsDomain (AdicCompletion I A) := by
  intro h
  exact not_isDomain_adicCompletion_six (h ℤ I6)

/-- **Exercise 10.4 (b)**, existential form of the counterexample. -/
theorem part_b_counterexample :
    ∃ (A : Type) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsDomain A) (I : Ideal A),
      ¬ IsDomain (AdicCompletion I A) :=
  ⟨ℤ, inferInstance, inferInstance, inferInstance, I6, not_isDomain_adicCompletion_six⟩

#print axioms AtiyahMcdonald69.Ex_10_4.part_a
#print axioms AtiyahMcdonald69.Ex_10_4.part_a_isZeroDivisor
#print axioms AtiyahMcdonald69.Ex_10_4.part_b
#print axioms AtiyahMcdonald69.Ex_10_4.part_b_counterexample
#print axioms AtiyahMcdonald69.Ex_10_4.not_isDomain_adicCompletion_six
#print axioms AtiyahMcdonald69.Ex_10_4.exists_zero_divisors

end AtiyahMcdonald69.Ex_10_4
