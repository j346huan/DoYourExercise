/-
# Atiyah–Macdonald, Exercise 9.4

## The exercise

M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Addison–Wesley 1969,
Chapter 9 ("Discrete Valuation Rings and Dedekind Domains"), Exercise 4 (p. 99), verbatim:

> Let `A` be a local domain which is not a field and in which the maximal ideal `m` is
> principal and `⋂_{n ⩾ 1} m^n = 0`. Prove that `A` is a discrete valuation ring.

The book's definitions (§9.1, p. 94) are:

* a *discrete valuation* on a field `K` is a mapping `v` of `K* = K - {0}` **onto** `ℤ`
  such that (1) `v (xy) = v x + v y` and (2) `v (x + y) ≥ min (v x) (v y)`
  (with the convention `v 0 = +∞`);
* the *valuation ring* of `v` is `{0} ∪ {x ∈ K* | v x ≥ 0}`;
* an integral domain `A` is a *discrete valuation ring* if there is a discrete valuation
  `v` of the field of fractions `K` of `A` such that `A` is the valuation ring of `v`.

## Formal statement

`AtiyahMcdonald69.Ex_9_4.solution` states, for a commutative ring `A`:

* hypotheses: `[IsDomain A]`, `[IsLocalRing A]` (a local domain), `¬ IsField A`, an element
  `t : A` with `maximalIdeal A = Ideal.span {t}` (the maximal ideal is principal), and
  `⨅ n : ℕ, (maximalIdeal A) ^ (n + 1) = ⊥`, i.e. `⋂_{n ≥ 1} m^n = 0`;
* conclusion: `IsDiscreteValuationRing A` **and** the existence of a `DiscreteValuation`
  `v` of `FractionRing A` — i.e. `v : (FractionRing A)* → ℤ` is onto `ℤ`, multiplicative,
  and satisfies the ultrametric inequality — whose valuation ring is `A`, i.e.
  `0 ≤ v x ↔ x ∈ A` for `x ≠ 0` (`exists_discreteValuation`), and, with `0` included,
  `x ∈ v.valuationSet ↔ ∃ a, algebraMap a = x` (`mem_valuationSet_iff`); moreover
  `m = {a | 0 < v a}` (`maximalIdeal_iff_pos`) and `v t = 1` (`amValuation_generator`),
  matching the book's description of a DVR (p. 94).

## Faithfulness / scope notes

* The field of fractions is realised as the canonical `FractionRing A`, which is the
  fraction field up to a unique `A`-algebra isomorphism; no generality is lost.
* The book's convention `v 0 = +∞` is rendered by the side condition `x + y ≠ 0` in
  `DiscreteValuation.map_add_ge'`; the case `x + y = 0` is exactly what the convention
  covers.
* `⋂_{n ≥ 1} m^n = 0` is formalised with the index shift `n ↦ n + 1`.  This hypothesis is
  essential (it is what replaces Noetherianity, cf. the book's (9.2)): it produces a
  *maximal* exponent with `a ∈ m^n`.
* `¬ IsField A` is the book's "not a field"; for a local ring it is equivalent to
  `m ≠ 0`.  It is needed: a field satisfies `⋂ m^n = 0` but is not a DVR in the book's
  sense (there is no surjection `K* → ℤ` for a field).
* Non-vacuity: `int_at_prime_satisfies` verifies the hypotheses for `ℤ_(p)` (uniformiser
  `p`, `⋂ m^n = 0` from Krull's intersection theorem), and
  `int_at_prime_isDiscreteValuationRing` applies the exercise to it.
* Nothing here relies on Mathlib's Noetherian characterisation
  `IsDiscreteValuationRing.TFAE`; the proof uses only the exercise's own hypotheses, as
  the book intends.

Source of the natural-language proof (j346huan/DoYourExercise, commit 80e1ebe):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-9-4

## Proof outline

The natural proof is followed.  Since `⋂_{n ≥ 1} m^n = 0`, for every `a ≠ 0` there is a
largest `n` with `a ∈ m^n`; writing `m = (t)` gives `a = t^n u` with `u ∉ m`, hence `u` a
unit, and therefore `(a) = m^n` (`exists_span_eq_pow`, `exp`).  The exponent is additive
(`exp_mul`) and satisfies the ultrametric inequality (`exp_add_ge`).  Every nonzero ideal
is then a power of `m` (`ideal_eq_pow_of_ne_bot`), so `A` is a principal ideal ring
(`isPrincipalIdealRing`) and hence `IsDiscreteValuationRing A`
(`isDiscreteValuationRing`).  Finally the exponent is extended to `K*` by
`v (a / b) = exp a - exp b`, which is well defined by multiplicativity
(`val_eq_of_div`), is multiplicative (`val_mul`), satisfies the ultrametric inequality
(`val_add_ge`), is onto `ℤ` (`val_surjective`), and `0 ≤ v x` holds exactly for the
nonzero `x` lying in `A` (`mem_iff_nonneg`).
-/
import Mathlib

open Ideal IsLocalRing

namespace AtiyahMcdonald69.Ex_9_4

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
variable {t : A}

/-! ### The exponent of a nonzero element -/

omit [IsDomain A] in
lemma maximalIdeal_ne_bot (hfield : ¬ IsField A) : maximalIdeal A ≠ ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hfield

omit [IsDomain A] in
lemma generator_mem (hprinc : maximalIdeal A = Ideal.span {t}) : t ∈ maximalIdeal A :=
  hprinc ▸ Submodule.mem_span_singleton_self t

omit [IsDomain A] in
lemma generator_ne_zero (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t}) :
    t ≠ 0 := by
  intro h
  refine maximalIdeal_ne_bot hfield ?_
  rw [hprinc, h, Ideal.span_singleton_eq_bot]

omit [IsDomain A] in
lemma generator_not_unit (hprinc : maximalIdeal A = Ideal.span {t}) : ¬ IsUnit t := fun h =>
  (IsLocalRing.notMem_maximalIdeal.mpr h) (generator_mem hprinc)

omit [IsDomain A] in
lemma maximalIdeal_pow_eq (hprinc : maximalIdeal A = Ideal.span {t}) (n : ℕ) :
    maximalIdeal A ^ n = Ideal.span {t ^ n} := by
  rw [hprinc, Ideal.span_singleton_pow]

/-- The powers of the principal maximal ideal decrease strictly. -/
lemma pow_succ_lt_pow (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (n : ℕ) : maximalIdeal A ^ (n + 1) < maximalIdeal A ^ n := by
  refine lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ n)) ?_
  intro heq
  have hmem : t ^ n ∈ maximalIdeal A ^ (n + 1) := by
    rw [heq, maximalIdeal_pow_eq hprinc]
    exact Submodule.mem_span_singleton_self (t ^ n)
  rw [maximalIdeal_pow_eq hprinc, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have htn : t ^ n ≠ 0 := pow_ne_zero n (generator_ne_zero hfield hprinc)
  have h2 : t ^ n = t ^ n * (t * c) := by
    nth_rewrite 1 [hc]
    rw [pow_succ]
    ring
  have h1 : (1 : A) = t * c := mul_left_cancel₀ htn (by rw [mul_one]; exact h2)
  exact generator_not_unit hprinc (isUnit_of_dvd_one ⟨c, h1⟩)

lemma pow_injective (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t}) :
    Function.Injective fun n : ℕ => maximalIdeal A ^ n := by
  intro i j hij
  change maximalIdeal A ^ i = maximalIdeal A ^ j at hij
  rcases le_total i j with h | h
  · by_contra hne
    have hlt : i < j := lt_of_le_of_ne h hne
    have h1 : maximalIdeal A ^ j ≤ maximalIdeal A ^ (i + 1) :=
      Ideal.pow_le_pow_right (Nat.succ_le_of_lt hlt)
    have h2 : maximalIdeal A ^ (i + 1) < maximalIdeal A ^ i := pow_succ_lt_pow hfield hprinc i
    rw [hij] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  · by_contra hne
    have hlt : j < i := lt_of_le_of_ne h (Ne.symm hne)
    have h1 : maximalIdeal A ^ i ≤ maximalIdeal A ^ (j + 1) :=
      Ideal.pow_le_pow_right (Nat.succ_le_of_lt hlt)
    have h2 : maximalIdeal A ^ (j + 1) < maximalIdeal A ^ j := pow_succ_lt_pow hfield hprinc j
    rw [← hij] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

lemma pow_le_pow_iff (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    {i j : ℕ} : maximalIdeal A ^ i ≤ maximalIdeal A ^ j ↔ j ≤ i := by
  refine ⟨fun hle => ?_, fun h => Ideal.pow_le_pow_right h⟩
  by_contra h'
  have hij : i < j := not_le.mp h'
  have h1 : maximalIdeal A ^ j ≤ maximalIdeal A ^ (i + 1) :=
    Ideal.pow_le_pow_right (Nat.succ_le_of_lt hij)
  have h2 : maximalIdeal A ^ (i + 1) < maximalIdeal A ^ i := pow_succ_lt_pow hfield hprinc i
  exact (not_le_of_gt (lt_of_le_of_lt h1 h2)) hle

omit [IsDomain A] in
/-- Every nonzero element of `A` generates a power of the maximal ideal. -/
theorem exists_span_eq_pow (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, Ideal.span {a} = maximalIdeal A ^ n := by
  classical
  have hnot : a ∉ ⨅ n : ℕ, maximalIdeal A ^ (n + 1) := by
    rw [hbot]; exact ha
  rw [Ideal.mem_iInf] at hnot
  have hex : ∃ n : ℕ, a ∉ maximalIdeal A ^ (n + 1) := by
    by_contra h
    apply hnot
    intro n
    by_contra hn
    exact h ⟨n, hn⟩
  set k := Nat.find hex with hk
  have hspec : a ∉ maximalIdeal A ^ (k + 1) := hk ▸ Nat.find_spec hex
  have hmem : a ∈ maximalIdeal A ^ k := by
    rcases k with _ | j
    · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · exact not_not.mp (Nat.find_min hex (m := j) (by omega))
  rw [maximalIdeal_pow_eq hprinc k] at hmem
  rw [maximalIdeal_pow_eq hprinc (k + 1)] at hspec
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  have hu_notMem : u ∉ maximalIdeal A := by
    intro hu_m
    apply hspec
    rw [Ideal.mem_span_singleton']
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hprinc ▸ hu_m)
    refine ⟨c, ?_⟩
    calc c * t ^ (k + 1) = (c * t) * t ^ k := by rw [pow_succ]; ring
      _ = u * t ^ k := by rw [hc]
      _ = a := hu
  have hu_unit : IsUnit u := IsLocalRing.notMem_maximalIdeal.mp hu_notMem
  refine ⟨k, ?_⟩
  rw [← hu, maximalIdeal_pow_eq hprinc k]
  exact Ideal.span_singleton_mul_left_unit (a := u) hu_unit (t ^ k)

/-- The exponent `n` such that `(a) = m ^ n`, for `a ≠ 0`. -/
noncomputable def exp (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) : ℕ :=
  Classical.choose (exists_span_eq_pow hprinc hbot ha)

omit [IsDomain A] in
lemma span_eq_pow_exp (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) :
    Ideal.span {a} = maximalIdeal A ^ exp hprinc hbot ha :=
  Classical.choose_spec (exists_span_eq_pow hprinc hbot ha)

omit [IsDomain A] in
lemma exp_congr (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a b : A} (hab : a = b) (ha : a ≠ 0)
    (hb : b ≠ 0) : exp hprinc hbot ha = exp hprinc hbot hb := by
  subst hab
  rfl

lemma exp_eq_of_span_eq_pow (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) {n : ℕ}
    (h : Ideal.span {a} = maximalIdeal A ^ n) : exp hprinc hbot ha = n := by
  refine pow_injective hfield hprinc ?_
  change maximalIdeal A ^ exp hprinc hbot ha = maximalIdeal A ^ n
  rw [← span_eq_pow_exp hprinc hbot ha, h]

lemma exp_mul (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    exp hprinc hbot (mul_ne_zero ha hb) = exp hprinc hbot ha + exp hprinc hbot hb := by
  refine exp_eq_of_span_eq_pow hfield hprinc hbot (mul_ne_zero ha hb) ?_
  rw [← Ideal.span_singleton_mul_span_singleton, span_eq_pow_exp hprinc hbot ha,
    span_eq_pow_exp hprinc hbot hb, ← pow_add]

lemma exp_pow (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) (n : ℕ) :
    exp hprinc hbot (pow_ne_zero n (generator_ne_zero hfield hprinc)) = n := by
  refine exp_eq_of_span_eq_pow hfield hprinc hbot _ ?_
  rw [maximalIdeal_pow_eq hprinc]

lemma exp_eq_zero_iff (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) :
    exp hprinc hbot ha = 0 ↔ IsUnit a := by
  constructor
  · intro h
    have htop : Ideal.span {a} = ⊤ := by
      rw [span_eq_pow_exp hprinc hbot ha, h, pow_zero, Ideal.one_eq_top]
    have h1 : (1 : A) ∈ Ideal.span {a} := htop ▸ Submodule.mem_top
    exact isUnit_of_dvd_one (Ideal.mem_span_singleton.mp h1)
  · intro h
    refine exp_eq_of_span_eq_pow hfield hprinc hbot ha ?_
    rw [pow_zero, Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr h

/-- A nonzero element is a unit times `t ^ exp a`. -/
lemma exists_unit_eq_mul_pow (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A} (ha : a ≠ 0) :
    ∃ u : Aˣ, a = (u : A) * t ^ exp hprinc hbot ha := by
  have hmem : a ∈ maximalIdeal A ^ exp hprinc hbot ha := by
    rw [← span_eq_pow_exp hprinc hbot ha]
    exact Submodule.mem_span_singleton_self a
  rw [maximalIdeal_pow_eq hprinc, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  have hu_notMem : u ∉ maximalIdeal A := by
    intro hu_m
    have ha_mem : a ∈ maximalIdeal A ^ (exp hprinc hbot ha + 1) := by
      rw [maximalIdeal_pow_eq hprinc, Ideal.mem_span_singleton']
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hprinc ▸ hu_m)
      refine ⟨c, ?_⟩
      calc c * t ^ (exp hprinc hbot ha + 1) = (c * t) * t ^ exp hprinc hbot ha := by
            rw [pow_succ]; ring
        _ = u * t ^ exp hprinc hbot ha := by rw [hc]
        _ = a := hu
    have hle : maximalIdeal A ^ exp hprinc hbot ha ≤ maximalIdeal A ^ (exp hprinc hbot ha + 1) := by
      rw [← span_eq_pow_exp hprinc hbot ha]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_mem)
    exact (not_le_of_gt (pow_succ_lt_pow hfield hprinc (exp hprinc hbot ha))) hle
  have hu_unit : IsUnit u := IsLocalRing.notMem_maximalIdeal.mp hu_notMem
  exact ⟨hu_unit.unit, by rw [IsUnit.unit_spec]; exact hu.symm⟩

/-- The ultrametric inequality for the exponent. -/
lemma exp_add_ge (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) :
    min (exp hprinc hbot ha) (exp hprinc hbot hb) ≤ exp hprinc hbot hab := by
  set ea := exp hprinc hbot ha with hea
  set eb := exp hprinc hbot hb with heb
  obtain ⟨u, hu⟩ := exists_unit_eq_mul_pow hfield hprinc hbot ha
  obtain ⟨v, hv⟩ := exists_unit_eq_mul_pow hfield hprinc hbot hb
  rw [← hea] at hu
  rw [← heb] at hv
  rcases le_total ea eb with h | h
  · set w : A := (u : A) + t ^ (eb - ea) * (v : A) with hw
    have hfac : a + b = t ^ ea * w := by
      rw [hu, hv, hw]
      have hsplit : t ^ eb = t ^ ea * t ^ (eb - ea) := by
        rw [← pow_add, Nat.add_sub_of_le h]
      rw [hsplit]
      ring
    have hw0 : w ≠ 0 := fun h0 => hab (by rw [hfac, h0, mul_zero])
    have htn : t ^ ea ≠ 0 := pow_ne_zero _ (generator_ne_zero hfield hprinc)
    have hcalc : exp hprinc hbot hab = ea + exp hprinc hbot hw0 := by
      rw [exp_congr hprinc hbot hfac hab (mul_ne_zero htn hw0),
        exp_mul hfield hprinc hbot htn hw0, exp_pow hfield hprinc hbot ea]
    calc min (exp hprinc hbot ha) (exp hprinc hbot hb) = min ea eb := by rw [hea, heb]
      _ = ea := min_eq_left h
      _ ≤ ea + exp hprinc hbot hw0 := Nat.le_add_right _ _
      _ = exp hprinc hbot hab := hcalc.symm
  · set w : A := (v : A) + t ^ (ea - eb) * (u : A) with hw
    have hfac : a + b = t ^ eb * w := by
      rw [hu, hv, hw]
      have hsplit : t ^ ea = t ^ eb * t ^ (ea - eb) := by
        rw [← pow_add, Nat.add_sub_of_le h]
      rw [hsplit]
      ring
    have hw0 : w ≠ 0 := fun h0 => hab (by rw [hfac, h0, mul_zero])
    have htn : t ^ eb ≠ 0 := pow_ne_zero _ (generator_ne_zero hfield hprinc)
    have hcalc : exp hprinc hbot hab = eb + exp hprinc hbot hw0 := by
      rw [exp_congr hprinc hbot hfac hab (mul_ne_zero htn hw0),
        exp_mul hfield hprinc hbot htn hw0, exp_pow hfield hprinc hbot eb]
    calc min (exp hprinc hbot ha) (exp hprinc hbot hb) = min ea eb := by rw [hea, heb]
      _ = eb := min_eq_right h
      _ ≤ eb + exp hprinc hbot hw0 := Nat.le_add_right _ _
      _ = exp hprinc hbot hab := hcalc.symm

/-- Every nonzero ideal of `A` is a power of the maximal ideal. -/
theorem ideal_eq_pow_of_ne_bot (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {I : Ideal A} (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = maximalIdeal A ^ n := by
  classical
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha_not : a ∉ maximalIdeal A ^ (exp hprinc hbot ha0 + 1) := by
    intro hmem
    have hspan : Ideal.span {a} ≤ maximalIdeal A ^ (exp hprinc hbot ha0 + 1) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
    rw [span_eq_pow_exp hprinc hbot ha0] at hspan
    exact (not_le_of_gt (pow_succ_lt_pow hfield hprinc (exp hprinc hbot ha0))) hspan
  have hex : ∃ n : ℕ, ¬ I ≤ maximalIdeal A ^ n :=
    ⟨exp hprinc hbot ha0 + 1, fun hle => ha_not (hle haI)⟩
  set j := Nat.find hex with hj
  have hInot : ¬ I ≤ maximalIdeal A ^ j := hj ▸ Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top] at hInot
    exact hInot le_top
  obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hInot' : ¬ I ≤ maximalIdeal A ^ (k + 1) := hk ▸ hInot
  have hIk : I ≤ maximalIdeal A ^ k := by
    refine not_not.mp (Nat.find_min hex (m := k) ?_)
    omega
  obtain ⟨x, hxI, hxnot⟩ : ∃ x ∈ I, x ∉ maximalIdeal A ^ (k + 1) := by
    by_contra h
    apply hInot'
    intro y hy
    by_contra hy'
    exact h ⟨y, hy, hy'⟩
  have hx0 : x ≠ 0 := fun h0 => hxnot (h0 ▸ zero_mem (maximalIdeal A ^ (k + 1)))
  have hxe : exp hprinc hbot hx0 = k := by
    have hle1 : maximalIdeal A ^ exp hprinc hbot hx0 ≤ maximalIdeal A ^ k := by
      rw [← span_eq_pow_exp hprinc hbot hx0]
      exact le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxI)) hIk
    have hkle : k ≤ exp hprinc hbot hx0 := (pow_le_pow_iff hfield hprinc).mp hle1
    have hle2 : ¬ (k + 1 ≤ exp hprinc hbot hx0) := by
      intro hc
      refine hxnot (Ideal.pow_le_pow_right hc ?_)
      rw [← span_eq_pow_exp hprinc hbot hx0]
      exact Submodule.mem_span_singleton_self x
    exact le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hle2)) hkle
  refine ⟨k, le_antisymm hIk ?_⟩
  rw [← hxe, ← span_eq_pow_exp hprinc hbot hx0]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxI)

theorem isPrincipalIdealRing (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) : IsPrincipalIdealRing A := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · refine Submodule.IsPrincipal.mk ⟨0, ?_⟩
    rw [hI]
    simp
  · obtain ⟨n, hn⟩ := ideal_eq_pow_of_ne_bot hfield hprinc hbot hI
    exact Submodule.IsPrincipal.mk ⟨t ^ n, by rw [hn, maximalIdeal_pow_eq hprinc]⟩

/-- **Atiyah–Macdonald 9.4**, in the form of Mathlib's predicate: `A` is a local PID
which is not a field. -/
theorem isDiscreteValuationRing (hfield : ¬ IsField A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) : IsDiscreteValuationRing A := by
  have := isPrincipalIdealRing hfield hprinc hbot
  exact IsDiscreteValuationRing.mk (maximalIdeal_ne_bot hfield)

/-! ### The discrete valuation on the fraction field

We now extend the exponent to `K = FractionRing A` by `v (a / b) = exp a - exp b`. -/

/-- Atiyah–Macdonald §9.1: a *discrete valuation* on a field `K` is a surjective map
`v : K* → ℤ` such that `v (xy) = v x + v y` and `v (x + y) ≥ min (v x) (v y)`
(the latter for `x + y ≠ 0`; the book's convention `v 0 = +∞` covers `x + y = 0`). -/
structure DiscreteValuation (K : Type*) [Field K] where
  toFun : Kˣ → ℤ
  map_mul' : ∀ x y : Kˣ, toFun (x * y) = toFun x + toFun y
  map_add_ge' : ∀ (x y : Kˣ) (h : (x : K) + (y : K) ≠ 0),
    min (toFun x) (toFun y) ≤ toFun (Units.mk0 ((x : K) + (y : K)) h)
  surjective' : Function.Surjective toFun

namespace DiscreteValuation

variable {K : Type*} [Field K]

instance : CoeFun (DiscreteValuation K) (fun _ => Kˣ → ℤ) := ⟨toFun⟩

/-- The valuation ring of a discrete valuation, as a subset of `K`: `0` together with the
`x ≠ 0` with `0 ≤ v x`.  `A` is the valuation ring of `v` iff `A = valuationSet v`. -/
def valuationSet (v : DiscreteValuation K) : Set K :=
  {x | x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ v (Units.mk0 x h)}

end DiscreteValuation

section FractionField

theorem exists_num_den (x : FractionRing A) :
    ∃ p : A × A, p.2 ∈ nonZeroDivisors A ∧
      algebraMap A (FractionRing A) p.1 / algebraMap A (FractionRing A) p.2 = x := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective A x
  exact ⟨(a, b), hb, h⟩

/-- A chosen numerator/denominator pair for an element of the fraction field. -/
noncomputable def fracPair (x : FractionRing A) : A × A := Classical.choose (exists_num_den x)

lemma fracPair_spec (x : FractionRing A) :
    (fracPair x).2 ∈ nonZeroDivisors A ∧
      algebraMap A (FractionRing A) (fracPair x).1 /
        algebraMap A (FractionRing A) (fracPair x).2 = x :=
  Classical.choose_spec (exists_num_den x)

/-- The numerator of a chosen fractional representation. -/
noncomputable def fracNum (x : FractionRing A) : A := (fracPair x).1

/-- The denominator of a chosen fractional representation. -/
noncomputable def fracDen (x : FractionRing A) : A := (fracPair x).2

lemma fracDen_ne_zero (x : FractionRing A) : fracDen x ≠ 0 :=
  nonZeroDivisors.ne_zero (fracPair_spec x).1

lemma fracNum_div_fracDen (x : FractionRing A) :
    algebraMap A (FractionRing A) (fracNum x) / algebraMap A (FractionRing A) (fracDen x) = x :=
  (fracPair_spec x).2

lemma fracNum_ne_zero {x : FractionRing A} (hx : x ≠ 0) : fracNum x ≠ 0 := by
  intro h
  exact hx (by rw [← fracNum_div_fracDen x, h, map_zero, zero_div])

/-- The exponent `v x` of `x ≠ 0` in the fraction field, from a chosen representation
`x = fracNum x / fracDen x`. -/
noncomputable def valNumDen (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) (x : FractionRing A)
    (hx : x ≠ 0) : ℤ :=
  (exp hprinc hbot (fracNum_ne_zero hx) : ℤ) - (exp hprinc hbot (fracDen_ne_zero x) : ℤ)

/-- Well-definedness: the exponent depends only on `x`, and may be computed from any
representation `x = a / b` with `a b ∈ A` and `b ≠ 0`. -/
lemma val_eq_of_div (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    {x : FractionRing A} (hx : x ≠ 0)
    (h : algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b = x) :
    valNumDen hprinc hbot x hx = (exp hprinc hbot ha : ℤ) - (exp hprinc hbot hb) := by
  have hd0 : fracDen x ≠ 0 := fracDen_ne_zero x
  have hn0 : fracNum x ≠ 0 := fracNum_ne_zero hx
  have hnd : algebraMap A (FractionRing A) (fracNum x) /
      algebraMap A (FractionRing A) (fracDen x) = x := fracNum_div_fracDen x
  have hbK : algebraMap A (FractionRing A) b ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr hb
  have hdK : algebraMap A (FractionRing A) (fracDen x) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr hd0
  have hdiv : algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b
      = algebraMap A (FractionRing A) (fracNum x) / algebraMap A (FractionRing A) (fracDen x) :=
    h.trans hnd.symm
  have key : a * fracDen x = b * fracNum x := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul]
    have h' := (div_eq_div_iff hbK hdK).mp hdiv
    rw [h']; ring
  have e1 := exp_mul hfield hprinc hbot ha hd0
  have e2 := exp_mul hfield hprinc hbot hb hn0
  have e3 : exp hprinc hbot (mul_ne_zero ha hd0) = exp hprinc hbot (mul_ne_zero hb hn0) :=
    exp_congr hprinc hbot key _ _
  have h4 : exp hprinc hbot ha + exp hprinc hbot hd0
      = exp hprinc hbot hb + exp hprinc hbot hn0 := by rw [← e1, ← e2]; exact e3
  have h3 : (exp hprinc hbot ha : ℤ) + (exp hprinc hbot hd0 : ℤ)
      = (exp hprinc hbot hb : ℤ) + (exp hprinc hbot hn0 : ℤ) := by exact_mod_cast h4
  simp only [valNumDen]
  omega

lemma val_mul (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {x y : FractionRing A}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    valNumDen hprinc hbot (x * y) (mul_ne_zero hx hy)
      = valNumDen hprinc hbot x hx + valNumDen hprinc hbot y hy := by
  have hnx : fracNum x ≠ 0 := fracNum_ne_zero hx
  have hny : fracNum y ≠ 0 := fracNum_ne_zero hy
  have hdx : fracDen x ≠ 0 := fracDen_ne_zero x
  have hdy : fracDen y ≠ 0 := fracDen_ne_zero y
  have hdiv : algebraMap A (FractionRing A) (fracNum x * fracNum y) /
      algebraMap A (FractionRing A) (fracDen x * fracDen y) = x * y := by
    rw [map_mul, map_mul, ← div_mul_div_comm, fracNum_div_fracDen x, fracNum_div_fracDen y]
  rw [val_eq_of_div hfield hprinc hbot (mul_ne_zero hnx hny) (mul_ne_zero hdx hdy)
    (mul_ne_zero hx hy) hdiv]
  have e1 : exp hprinc hbot (mul_ne_zero hnx hny) = exp hprinc hbot hnx + exp hprinc hbot hny :=
    exp_mul hfield hprinc hbot hnx hny
  have e2 : exp hprinc hbot (mul_ne_zero hdx hdy) = exp hprinc hbot hdx + exp hprinc hbot hdy :=
    exp_mul hfield hprinc hbot hdx hdy
  rw [e1, e2,
    val_eq_of_div hfield hprinc hbot hnx hdx hx (fracNum_div_fracDen x),
    val_eq_of_div hfield hprinc hbot hny hdy hy (fracNum_div_fracDen y)]
  push_cast
  ring

lemma val_inv (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {x : FractionRing A} (hx : x ≠ 0) :
    valNumDen hprinc hbot x⁻¹ (inv_ne_zero hx) = -valNumDen hprinc hbot x hx := by
  have hdiv : algebraMap A (FractionRing A) (fracDen x) / algebraMap A (FractionRing A) (fracNum x)
      = x⁻¹ := by
    rw [← inv_div, fracNum_div_fracDen x]
  rw [val_eq_of_div hfield hprinc hbot (fracDen_ne_zero x) (fracNum_ne_zero hx)
      (inv_ne_zero hx) hdiv,
    val_eq_of_div hfield hprinc hbot (fracNum_ne_zero hx) (fracDen_ne_zero x) hx
      (fracNum_div_fracDen x)]
  ring

/-- The ultrametric inequality for the exponent on the fraction field. -/
lemma val_add_ge (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {x y : FractionRing A}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (valNumDen hprinc hbot x hx) (valNumDen hprinc hbot y hy)
      ≤ valNumDen hprinc hbot (x + y) hxy := by
  have hnx : fracNum x ≠ 0 := fracNum_ne_zero hx
  have hny : fracNum y ≠ 0 := fracNum_ne_zero hy
  have hdx : fracDen x ≠ 0 := fracDen_ne_zero x
  have hdy : fracDen y ≠ 0 := fracDen_ne_zero y
  have hdxK : algebraMap A (FractionRing A) (fracDen x) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr hdx
  have hdyK : algebraMap A (FractionRing A) (fracDen y) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr hdy
  have hdiv : algebraMap A (FractionRing A)
        (fracNum x * fracDen y + fracDen x * fracNum y) /
        algebraMap A (FractionRing A) (fracDen x * fracDen y) = x + y := by
    rw [map_add, map_mul, map_mul, map_mul,
      ← div_add_div (algebraMap A (FractionRing A) (fracNum x))
        (algebraMap A (FractionRing A) (fracNum y)) hdxK hdyK,
      fracNum_div_fracDen x, fracNum_div_fracDen y]
  have hnum : fracNum x * fracDen y + fracDen x * fracNum y ≠ 0 := by
    intro h
    exact hxy (by rw [← hdiv, h, map_zero, zero_div])
  have hval := val_eq_of_div hfield hprinc hbot hnum (mul_ne_zero hdx hdy) hxy hdiv
  have hadd := exp_add_ge hfield hprinc hbot (mul_ne_zero hnx hdy) (mul_ne_zero hdx hny) hnum
  have e1 := exp_mul hfield hprinc hbot hnx hdy
  have e2 := exp_mul hfield hprinc hbot hdx hny
  have e3 := exp_mul hfield hprinc hbot hdx hdy
  have vx := val_eq_of_div hfield hprinc hbot hnx hdx hx (fracNum_div_fracDen x)
  have vy := val_eq_of_div hfield hprinc hbot hny hdy hy (fracNum_div_fracDen y)
  have cA : ((exp hprinc hbot (mul_ne_zero hnx hdy) : ℕ) : ℤ)
      = (exp hprinc hbot hnx : ℤ) + (exp hprinc hbot hdy : ℤ) := by rw [e1]; push_cast; ring
  have cB : ((exp hprinc hbot (mul_ne_zero hdx hny) : ℕ) : ℤ)
      = (exp hprinc hbot hdx : ℤ) + (exp hprinc hbot hny : ℤ) := by rw [e2]; push_cast; ring
  have cD : ((exp hprinc hbot (mul_ne_zero hdx hdy) : ℕ) : ℤ)
      = (exp hprinc hbot hdx : ℤ) + (exp hprinc hbot hdy : ℤ) := by rw [e3]; push_cast; ring
  rcases le_total (exp hprinc hbot hnx + exp hprinc hbot hdy)
    (exp hprinc hbot hny + exp hprinc hbot hdx) with hAB | hAB
  · have hZ : ((exp hprinc hbot (mul_ne_zero hnx hdy) : ℕ) : ℤ)
        ≤ ((exp hprinc hbot (mul_ne_zero hdx hny) : ℕ) : ℤ) := by
      have h := hAB
      rw [add_comm (exp hprinc hbot hny)] at h
      rw [cA, cB]
      exact_mod_cast h
    have hleNat : exp hprinc hbot (mul_ne_zero hnx hdy) ≤ exp hprinc hbot (mul_ne_zero hdx hny) := by
      exact_mod_cast hZ
    have hminNat : min (exp hprinc hbot (mul_ne_zero hnx hdy))
        (exp hprinc hbot (mul_ne_zero hdx hny)) = exp hprinc hbot (mul_ne_zero hnx hdy) :=
      min_eq_left hleNat
    have hge : exp hprinc hbot (mul_ne_zero hnx hdy) ≤ exp hprinc hbot hnum := hminNat ▸ hadd
    have hgeZ : ((exp hprinc hbot (mul_ne_zero hnx hdy) : ℕ) : ℤ)
        ≤ ((exp hprinc hbot hnum : ℕ) : ℤ) := by exact_mod_cast hge
    have hABZ : (exp hprinc hbot hnx : ℤ) + (exp hprinc hbot hdy : ℤ)
        ≤ (exp hprinc hbot hdx : ℤ) + (exp hprinc hbot hny : ℤ) := by
      have h := hAB
      rw [add_comm (exp hprinc hbot hny)] at h
      exact_mod_cast h
    have hle : valNumDen hprinc hbot x hx ≤ valNumDen hprinc hbot y hy := by
      rw [vx, vy]; linarith
    rw [min_eq_left hle, hval, vx, cD]
    linarith [hgeZ, cA]
  · have hZ : ((exp hprinc hbot (mul_ne_zero hdx hny) : ℕ) : ℤ)
        ≤ ((exp hprinc hbot (mul_ne_zero hnx hdy) : ℕ) : ℤ) := by
      have h := hAB
      rw [add_comm (exp hprinc hbot hny)] at h
      rw [cA, cB]
      exact_mod_cast h
    have hleNat : exp hprinc hbot (mul_ne_zero hdx hny) ≤ exp hprinc hbot (mul_ne_zero hnx hdy) := by
      exact_mod_cast hZ
    have hminNat : min (exp hprinc hbot (mul_ne_zero hnx hdy))
        (exp hprinc hbot (mul_ne_zero hdx hny)) = exp hprinc hbot (mul_ne_zero hdx hny) :=
      min_eq_right hleNat
    have hge : exp hprinc hbot (mul_ne_zero hdx hny) ≤ exp hprinc hbot hnum := hminNat ▸ hadd
    have hgeZ : ((exp hprinc hbot (mul_ne_zero hdx hny) : ℕ) : ℤ)
        ≤ ((exp hprinc hbot hnum : ℕ) : ℤ) := by exact_mod_cast hge
    have hABZ : (exp hprinc hbot hdx : ℤ) + (exp hprinc hbot hny : ℤ)
        ≤ (exp hprinc hbot hnx : ℤ) + (exp hprinc hbot hdy : ℤ) := by
      have h := hAB
      rw [add_comm (exp hprinc hbot hny)] at h
      exact_mod_cast h
    have hle : valNumDen hprinc hbot y hy ≤ valNumDen hprinc hbot x hx := by
      rw [vx, vy]; linarith
    rw [min_eq_right hle, hval, vy, cD]
    linarith [hgeZ, cB]

/-- The exponent on `K*` is surjective onto `ℤ`. -/
lemma val_surjective (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) (m : ℤ) :
    ∃ x : FractionRing A, ∃ hx : x ≠ 0, valNumDen hprinc hbot x hx = m := by
  have ht : t ≠ 0 := generator_ne_zero hfield hprinc
  have h1 : exp hprinc hbot (one_ne_zero : (1 : A) ≠ 0) = 0 :=
    (exp_eq_zero_iff hfield hprinc hbot one_ne_zero).mpr isUnit_one
  rcases le_or_gt 0 m with hm | hm
  · refine ⟨algebraMap A (FractionRing A) (t ^ m.toNat), ?_, ?_⟩
    · intro h
      exact pow_ne_zero _ ht (IsFractionRing.injective A (FractionRing A) (by rw [h, map_zero]))
    · have hdiv : algebraMap A (FractionRing A) (t ^ m.toNat) /
          algebraMap A (FractionRing A) (1 : A) = algebraMap A (FractionRing A) (t ^ m.toNat) := by
        rw [map_one, div_one]
      rw [val_eq_of_div hfield hprinc hbot (pow_ne_zero _ ht) one_ne_zero _ hdiv,
        exp_pow hfield hprinc hbot, h1, Int.toNat_of_nonneg hm]
      ring
  · have hx0 : algebraMap A (FractionRing A) (t ^ (-m).toNat) ≠ 0 := by
      intro h
      exact pow_ne_zero _ ht (IsFractionRing.injective A (FractionRing A) (by rw [h, map_zero]))
    refine ⟨(algebraMap A (FractionRing A) (t ^ (-m).toNat))⁻¹, inv_ne_zero hx0, ?_⟩
    have hdiv : algebraMap A (FractionRing A) (t ^ (-m).toNat) /
        algebraMap A (FractionRing A) (1 : A) = algebraMap A (FractionRing A) (t ^ (-m).toNat) := by
      rw [map_one, div_one]
    rw [val_inv hfield hprinc hbot hx0,
      val_eq_of_div hfield hprinc hbot (pow_ne_zero _ ht) one_ne_zero hx0 hdiv,
      exp_pow hfield hprinc hbot, h1]
    have h2 : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by linarith)
    rw [h2]
    ring

/-- `A` is the valuation ring of `v`: a nonzero element of the fraction field has
non-negative valuation exactly when it lies in `A`. -/
lemma mem_iff_nonneg (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {x : FractionRing A} (hx : x ≠ 0) :
    (∃ a : A, algebraMap A (FractionRing A) a = x) ↔ 0 ≤ valNumDen hprinc hbot x hx := by
  constructor
  · rintro ⟨a, rfl⟩
    have ha : a ≠ 0 := fun h => hx (by rw [h, map_zero])
    have h1 : exp hprinc hbot (one_ne_zero : (1 : A) ≠ 0) = 0 :=
      (exp_eq_zero_iff hfield hprinc hbot one_ne_zero).mpr isUnit_one
    have hdiv : algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) (1 : A)
        = algebraMap A (FractionRing A) a := by rw [map_one, div_one]
    rw [val_eq_of_div hfield hprinc hbot ha one_ne_zero hx hdiv, h1]
    push_cast
    exact Int.natCast_nonneg _
  · intro hv
    have hnx : fracNum x ≠ 0 := fracNum_ne_zero hx
    have hdx : fracDen x ≠ 0 := fracDen_ne_zero x
    obtain ⟨u, hu⟩ := exists_unit_eq_mul_pow hfield hprinc hbot hnx
    obtain ⟨v, hv'⟩ := exists_unit_eq_mul_pow hfield hprinc hbot hdx
    set en := exp hprinc hbot hnx with hen
    set ed := exp hprinc hbot hdx with hed
    have hvZ : 0 ≤ valNumDen hprinc hbot x hx := hv
    rw [val_eq_of_div hfield hprinc hbot hnx hdx hx (fracNum_div_fracDen x)] at hvZ
    rw [← hen, ← hed] at hvZ
    have hed_le : ed ≤ en := by
      have hZ : (ed : ℤ) ≤ (en : ℤ) := by linarith
      exact_mod_cast hZ
    refine ⟨(u : A) * ((↑v⁻¹ : Aˣ) : A) * t ^ (en - ed), ?_⟩
    have hunit : ((↑v⁻¹ : Aˣ) : A) * (v : A) = 1 := by simp
    have hpow : t ^ (en - ed) * t ^ ed = t ^ en := by
      rw [← pow_add, Nat.sub_add_cancel hed_le]
    have key : (u : A) * ((↑v⁻¹ : Aˣ) : A) * t ^ (en - ed) * fracDen x = fracNum x := by
      rw [hu, hv']
      calc (u : A) * ((↑v⁻¹ : Aˣ) : A) * t ^ (en - ed) * ((v : A) * t ^ ed)
          = ((u : A) * ((↑v⁻¹ : Aˣ) : A) * (v : A)) * (t ^ (en - ed) * t ^ ed) := by ring
        _ = (u : A) * 1 * t ^ en := by
              rw [mul_assoc (u : A) ((↑v⁻¹ : Aˣ) : A) (v : A), hunit, mul_one, hpow]
        _ = (u : A) * t ^ en := by ring
    have hdK : algebraMap A (FractionRing A) (fracDen x) ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff).not.mpr hdx
    have hxmul : x * algebraMap A (FractionRing A) (fracDen x)
        = algebraMap A (FractionRing A) (fracNum x) := by
      have h := fracNum_div_fracDen x
      field_simp at h
      rw [mul_comm]
      exact h.symm
    have hamul : algebraMap A (FractionRing A) ((u : A) * ((↑v⁻¹ : Aˣ) : A) * t ^ (en - ed)) *
        algebraMap A (FractionRing A) (fracDen x) = algebraMap A (FractionRing A) (fracNum x) := by
      rw [← map_mul, key]
    exact mul_right_cancel₀ hdK (hamul.trans hxmul.symm)

/-- The discrete valuation of the fraction field of `A` whose valuation ring is `A`. -/
noncomputable def amValuation (hfield : ¬ IsField A) (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) : DiscreteValuation (FractionRing A) where
  toFun u := valNumDen hprinc hbot (u : FractionRing A) (Units.ne_zero u)
  map_mul' x y := by
    simpa using val_mul hfield hprinc hbot (Units.ne_zero x) (Units.ne_zero y)
  map_add_ge' x y h := by
    simpa using val_add_ge hfield hprinc hbot (Units.ne_zero x) (Units.ne_zero y) h
  surjective' m := by
    obtain ⟨x, hx, hv⟩ := val_surjective hfield hprinc hbot m
    exact ⟨Units.mk0 x hx, hv⟩

/-- **Atiyah–Macdonald 9.4**, book-literal form: `A` is the valuation ring of a discrete
valuation of its field of fractions. -/
theorem exists_discreteValuation (hfield : ¬ IsField A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ v : DiscreteValuation (FractionRing A), ∀ (x : FractionRing A) (hx : x ≠ 0),
      ((∃ a : A, algebraMap A (FractionRing A) a = x) ↔ 0 ≤ v (Units.mk0 x hx)) := by
  refine ⟨amValuation hfield hprinc hbot, fun x hx => ?_⟩
  simpa [amValuation] using mem_iff_nonneg hfield hprinc hbot hx

/-- `A` is exactly the valuation ring of `amValuation`: inside the fraction field,
`A` is `{0} ∪ {x ≠ 0 | 0 ≤ v x}`. -/
theorem mem_valuationSet_iff (hfield : ¬ IsField A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) (x : FractionRing A) :
    x ∈ (amValuation hfield hprinc hbot).valuationSet
      ↔ ∃ a : A, algebraMap A (FractionRing A) a = x := by
  constructor
  · rintro (rfl | ⟨hx, hv⟩)
    · exact ⟨0, map_zero _⟩
    · exact (mem_iff_nonneg hfield hprinc hbot hx).mpr (by simpa [amValuation] using hv)
  · rintro ⟨a, rfl⟩
    by_cases h : algebraMap A (FractionRing A) a = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, by
        simpa [amValuation] using (mem_iff_nonneg hfield hprinc hbot h).mp ⟨a, rfl⟩⟩

/-- The valuation is normalised at the uniformiser: `v t = 1`, so `m = (t)` is exactly the
set of elements of positive valuation. -/
theorem amValuation_generator (hfield : ¬ IsField A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥)
    (hx : algebraMap A (FractionRing A) t ≠ 0) :
    amValuation hfield hprinc hbot (Units.mk0 (algebraMap A (FractionRing A) t) hx) = 1 := by
  have ht : t ≠ 0 := generator_ne_zero hfield hprinc
  have h1 : exp hprinc hbot (one_ne_zero : (1 : A) ≠ 0) = 0 :=
    (exp_eq_zero_iff hfield hprinc hbot one_ne_zero).mpr isUnit_one
  have hexp : exp hprinc hbot ht = 1 := by
    refine exp_eq_of_span_eq_pow hfield hprinc hbot ht ?_
    rw [pow_one]
    exact hprinc.symm
  have hdiv : algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) (1 : A)
      = algebraMap A (FractionRing A) t := by rw [map_one, div_one]
  change valNumDen hprinc hbot (algebraMap A (FractionRing A) t) hx = 1
  rw [val_eq_of_div hfield hprinc hbot ht one_ne_zero hx hdiv, hexp, h1]
  ring

/-- The maximal ideal is the set of elements of positive valuation, as in the book's
discussion of discrete valuation rings (p. 94). -/
theorem maximalIdeal_iff_pos (hfield : ¬ IsField A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) {a : A}
    (hx : algebraMap A (FractionRing A) a ≠ 0) :
    a ∈ maximalIdeal A ↔
      0 < amValuation hfield hprinc hbot (Units.mk0 (algebraMap A (FractionRing A) a) hx) := by
  have ha : a ≠ 0 := fun h => hx (by rw [h, map_zero])
  have h1 : exp hprinc hbot (one_ne_zero : (1 : A) ≠ 0) = 0 :=
    (exp_eq_zero_iff hfield hprinc hbot one_ne_zero).mpr isUnit_one
  have hdiv : algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) (1 : A)
      = algebraMap A (FractionRing A) a := by rw [map_one, div_one]
  have hval : amValuation hfield hprinc hbot (Units.mk0 (algebraMap A (FractionRing A) a) hx)
      = (exp hprinc hbot ha : ℤ) := by
    change valNumDen hprinc hbot (algebraMap A (FractionRing A) a) hx = _
    rw [val_eq_of_div hfield hprinc hbot ha one_ne_zero hx hdiv, h1]
    push_cast
    ring
  rw [hval]
  constructor
  · intro hmem
    have hnu : ¬ IsUnit a := fun hu => (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem
    have hne : exp hprinc hbot ha ≠ 0 := fun h0 =>
      hnu ((exp_eq_zero_iff hfield hprinc hbot ha).mp h0)
    omega
  · intro hpos
    by_contra hmem
    have hu : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp hmem
    rw [show exp hprinc hbot ha = 0 from (exp_eq_zero_iff hfield hprinc hbot ha).mpr hu] at hpos
    omega

end FractionField

/-- **Atiyah–Macdonald, Exercise 9.4.**

Let `A` be a local domain which is not a field and in which the maximal ideal `m` is
principal and `⋂_{n ≥ 1} m^n = 0`.  Then `A` is a discrete valuation ring, in both senses:
it satisfies Mathlib's `IsDiscreteValuationRing`, and — literally as in the book — there is
a discrete valuation `v` of the fraction field of `A` (surjective `K* → ℤ`, multiplicative,
satisfying the ultrametric inequality) whose valuation ring is `A`. -/
theorem solution (hfield : ¬ IsField A) (t : A)
    (hprinc : maximalIdeal A = Ideal.span {t})
    (hbot : ⨅ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥) :
    IsDiscreteValuationRing A ∧
      ∃ v : DiscreteValuation (FractionRing A), ∀ (x : FractionRing A) (hx : x ≠ 0),
        ((∃ a : A, algebraMap A (FractionRing A) a = x) ↔ 0 ≤ v (Units.mk0 x hx)) :=
  ⟨isDiscreteValuationRing hfield hprinc hbot,
    exists_discreteValuation hfield hprinc hbot⟩

/-! ### Non-vacuity of the hypotheses

The hypotheses are satisfiable: `ℤ` localised at a prime ideal `(p)` satisfies them with
uniformiser `p`, so the theorem above is not vacuous.  (Here `⋂ m^n = 0` comes from
Krull's intersection theorem for Noetherian local rings.) -/

local notation "ℤ_(" p ")" => Localization.AtPrime (Ideal.span {(p : ℤ)})

/-- The hypotheses of Exercise 9.4 hold for `ℤ_(p)` with uniformiser `p`. -/
theorem int_at_prime_satisfies (p : ℕ) [hp : Fact p.Prime] :
    ∃ t : ℤ_(p), ¬ IsField ℤ_(p) ∧
      IsLocalRing.maximalIdeal ℤ_(p) = Ideal.span {t} ∧
      ⨅ n : ℕ, IsLocalRing.maximalIdeal ℤ_(p) ^ (n + 1) = ⊥ := by
  have hne : algebraMap ℤ ℤ_(p) (p : ℤ) ≠ 0 := by
    intro h
    have h0 : (p : ℤ) = 0 :=
      IsLocalization.injective (M := (Ideal.span {(p : ℤ)}).primeCompl) ℤ_(p)
        (Ideal.primeCompl_le_nonZeroDivisors _) (by rw [h, map_zero])
    exact hp.out.ne_zero (by exact_mod_cast h0)
  have hspan : IsLocalRing.maximalIdeal ℤ_(p) = Ideal.span {algebraMap ℤ ℤ_(p) (p : ℤ)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) ℤ_(p),
      Ideal.map_span, Set.image_singleton]
  refine ⟨algebraMap ℤ ℤ_(p) p, ?_, hspan, ?_⟩
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, hspan]
    intro hbot
    have hmem : algebraMap ℤ ℤ_(p) (p : ℤ) ∈ Ideal.span {algebraMap ℤ ℤ_(p) (p : ℤ)} :=
      Submodule.mem_span_singleton_self _
    rw [hbot] at hmem
    exact hne (by simpa using hmem)
  · have hne_top : IsLocalRing.maximalIdeal ℤ_(p) ≠ ⊤ :=
      Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal ℤ_(p))
    have hkrull :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing (R := ℤ_(p)) (IsLocalRing.maximalIdeal ℤ_(p)) hne_top
    refine le_antisymm ?_ bot_le
    rw [← hkrull]
    refine le_iInf fun n => ?_
    exact le_trans (iInf_le (fun k : ℕ => IsLocalRing.maximalIdeal ℤ_(p) ^ (k + 1)) n)
      (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- `ℤ_(p)` is a discrete valuation ring, by the exercise. -/
theorem int_at_prime_isDiscreteValuationRing (p : ℕ) [hp : Fact p.Prime] :
    IsDiscreteValuationRing ℤ_(p) := by
  obtain ⟨t, hfield, hprinc, hbot⟩ := int_at_prime_satisfies p
  exact isDiscreteValuationRing hfield hprinc hbot

end AtiyahMcdonald69.Ex_9_4
