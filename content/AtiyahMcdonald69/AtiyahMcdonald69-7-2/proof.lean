/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 7 (Noetherian Rings), Exercise 2.

**Exercise statement (Atiyah–Macdonald, Ch. 7, Exercise 2), verbatim form.**
"Suppose `A` is a Noetherian ring and let `f = ∑_{i=0}^∞ a_i x^i` be an element of
`A[[x]]`. Show that `f` is nilpotent if and only if each `a_i` is nilpotent."

**Formal statement.** `solution` below: for every commutative ring `A` with
`[IsNoetherianRing A]` (this is "`A` is Noetherian", i.e. the ascending chain condition on
ideals) and every `f : A⟦X⟧`,
`IsNilpotent f ↔ ∀ n, IsNilpotent (PowerSeries.coeff n f)`,
where `PowerSeries.coeff n f` is the `n`-th coefficient `a_n` of `f`.  This is the whole
exercise: one biconditional, both directions proved, no hypothesis dropped and none added
(`A` may be the zero ring, in which case both sides hold).

**Source of the natural-language proof.**
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-2
(local copy: `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-7-2/proof.tex`,
repository `j346huan/DoYourExercise`, commit `80e1ebef1d7621c66aabb3920d981ffd8995ba91`).
That proof is correct and no hypothesis is missing from the book's formulation; its two
halves are exactly the two halves proved below:
* (⇒) modulo a prime ideal `P`, the image of `f` in `(A ⧸ P)⟦X⟧` is nilpotent and this ring
  is an integral domain, so the image of `f` is `0`; hence every `a_n` lies in every prime
  ideal, i.e. is nilpotent;
* (⇐) if every `a_n` lies in the nilradical `𝔫` of `A`, then `f^k ∈ 𝔫^k⟦X⟧` for every `k`,
  and `𝔫` is nilpotent because `A` is Noetherian (A–M 7.15).

**Audit of the statement.**  The scan `atiyah-macdonald-original.txt` provided in
`.scratch/reference/` breaks off inside Chapter 6 and does not contain the Chapter 7
exercises; the statement above was therefore checked against (i) the site's tag `7.2`,
(ii) Chapter 1, Exercise 5 (ii) of the scan ("If `f` is nilpotent, then `a_n` is nilpotent
for all `n ≥ 0`. Is the converse true? (See Chapter 7, Exercise 2.)"), and (iii) two
independent book transcriptions, `atiyah-solutions.txt` ("7.2. Suppose `A` is a Noetherian
ring ... Show that `f` is nilpotent if and only if each `a_i` is nilpotent") and the LaTeX
translation `.scratch/dl/amcd.tex` (Section `ex7.2`), which agree.

**Scope remarks, with the sharpness of the Noetherian hypothesis formalized.**
* The hypothesis "`A` Noetherian" is used only in the (⇐) direction (via
  `IsNoetherianRing.isNilpotent_nilradical`, A–M 7.15).  The (⇒) direction holds
  in an *arbitrary* commutative ring and is proved below as `isNilpotent_coeff`, i.e. the
  formalization is stronger than the book there, not weaker.
* The Noetherian hypothesis cannot be dropped from (⇐).  Theorems
  `not_isNilpotent_cexSeries` and `cexSeries_coeff_isNilpotent` construct, over the
  (necessarily non-Noetherian) infinite product `CexRing = ∏_n ℤ[X]/(X^{n+1})`, a power
  series all of whose coefficients are nilpotent which is not itself nilpotent, so the
  biconditional with the Noetherian hypothesis deleted is false.  The book's statement is
  therefore correct as it stands and is not modified anywhere in this file.
-/
import Mathlib.RingTheory.PowerSeries.CoeffMulMem
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Polynomial.Basic

open scoped PowerSeries

namespace AtiyahMcdonald69.Ex_7_2

open PowerSeries

variable {A : Type*} [CommRing A]

/-- (⇒) of A–M Ch. 7 Ex. 2, in its natural generality: for an arbitrary commutative ring `A`,
if `f : A⟦X⟧` is nilpotent then every coefficient of `f` is nilpotent.

Reduction to a domain: for a prime ideal `P`, the image of `f` under `A⟦X⟧ → (A ⧸ P)⟦X⟧` is
nilpotent, and `(A ⧸ P)⟦X⟧` has no nonzero nilpotent element, so that image is `0`; thus
`a_n ∈ P` for every prime ideal `P`, i.e. `a_n` is nilpotent. -/
theorem isNilpotent_coeff {f : A⟦X⟧} (hf : IsNilpotent f) (n : ℕ) :
    IsNilpotent (PowerSeries.coeff n f) := by
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have hmap : IsNilpotent (PowerSeries.map (Ideal.Quotient.mk P) f) := hf.map _
  have hzero : PowerSeries.map (Ideal.Quotient.mk P) f = 0 := hmap.eq_zero
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  have hcoeff : PowerSeries.coeff n (PowerSeries.map (Ideal.Quotient.mk P) f) = 0 := by
    rw [hzero, map_zero]
  simpa using hcoeff

/-- (⇐) of A–M Ch. 7 Ex. 2: over a Noetherian ring, a formal power series all of whose
coefficients are nilpotent is nilpotent.

If all coefficients lie in the nilradical `𝔫`, then by induction every coefficient of `f^k`
lies in `𝔫^k` (`PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`).  Since `A`
is Noetherian its nilradical is nilpotent, `𝔫^m = 0` (A–M 7.15), hence
`f^(m+1) = 0`. -/
theorem isNilpotent_of_forall_coeff [IsNoetherianRing A] {f : A⟦X⟧}
    (h : ∀ n, IsNilpotent (PowerSeries.coeff n f)) : IsNilpotent f := by
  have hmem : ∀ n, PowerSeries.coeff n f ∈ nilradical A := fun n =>
    mem_nilradical.mpr (h n)
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical A
  have hpow : ∀ (k j : ℕ), PowerSeries.coeff j (f ^ k) ∈ nilradical A ^ k := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      have key := PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
        (I := nilradical A ^ k) (J := nilradical A) (f := f ^ k) (g := f) ih hmem j
      simpa only [pow_succ] using key
  refine ⟨m + 1, ?_⟩
  ext j
  have hbot : nilradical A ^ (m + 1) = ⊥ := by
    rw [pow_succ, hm]; simp
  have := hpow (m + 1) j
  rw [hbot] at this
  simpa using this

/-- **Atiyah–Macdonald, Chapter 7, Exercise 2.**  For a Noetherian ring `A` and
`f : A⟦X⟧`, the series `f` is nilpotent if and only if each of its coefficients is
nilpotent. -/
theorem solution (A : Type*) [CommRing A] [IsNoetherianRing A] (f : A⟦X⟧) :
    IsNilpotent f ↔ ∀ n, IsNilpotent (PowerSeries.coeff n f) :=
  ⟨fun hf n => isNilpotent_coeff hf n, fun h => isNilpotent_of_forall_coeff h⟩

/-! ### Sharpness of the Noetherian hypothesis

The (⇐) direction of the exercise uses noetherianity through A–M 7.15 (the
nilradical of a Noetherian ring is nilpotent).  The rest of this file formalizes a
counterexample showing that this hypothesis cannot be deleted: the infinite product
`CexRing = ∏_n ℤ[X]/(X^{n+1})` carries a power series whose every coefficient is nilpotent
but which is not nilpotent.  By `solution` above, `CexRing` is necessarily not Noetherian. -/

noncomputable section

/-- The truncated polynomial ring `ℤ[X]/(X^{n+1})`: the ring over which the `n`-th coefficient
of the counterexample lives. -/
abbrev Trunc (n : ℕ) : Type := Polynomial ℤ ⧸ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ (n + 1)}

/-- The class of `X` in `Trunc n`; it is nilpotent of index `n + 1` and no smaller. -/
def t (n : ℕ) : Trunc n := Ideal.Quotient.mk _ Polynomial.X

lemma t_pow_succ (n : ℕ) : t n ^ (n + 1) = 0 := by
  rw [t, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

lemma t_pow_ne_zero {n k : ℕ} (hk : k ≤ n) : t n ^ k ≠ 0 := by
  intro hzero
  rw [t, ← map_pow] at hzero
  have hmem : (Polynomial.X : Polynomial ℤ) ^ k ∈ Ideal.span {Polynomial.X ^ (n + 1)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [Ideal.mem_span_singleton] at hmem
  have hne : (Polynomial.X : Polynomial ℤ) ^ k ≠ 0 := (Polynomial.monic_X_pow k).ne_zero
  have hdeg := Polynomial.natDegree_le_of_dvd hmem hne
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hdeg
  omega

/-- The counterexample ring: the product of the truncated polynomial rings `Trunc n`, in which
the `n`-th factor only knows about the `n`-th coefficient of a power series. -/
abbrev CexRing : Type := (n : ℕ) → Trunc n

/-- The `n`-th coefficient of the counterexample series: the element of the product ring which
is `t n` in the `n`-th factor and `0` in every other factor.  It is nilpotent of index `n+1`
because `(t n)^(n+1) = 0`. -/
def cexCoeff (n : ℕ) : CexRing := Pi.single n (t n)

lemma cexCoeff_pow_succ (n : ℕ) : cexCoeff n ^ (n + 1) = 0 := by
  ext j
  by_cases h : j = n
  · subst h
    simp [cexCoeff, Pi.single_eq_same, t_pow_succ]
  · simp [cexCoeff, h]

/-- The counterexample series `∑_n cexCoeff n · X^n` over the non-Noetherian ring
`CexRing`. -/
def cexSeries : PowerSeries CexRing := PowerSeries.mk cexCoeff

/-- Every coefficient of the counterexample series is nilpotent. -/
theorem cexSeries_coeff_isNilpotent (n : ℕ) :
    IsNilpotent (PowerSeries.coeff n cexSeries) := by
  rw [cexSeries, PowerSeries.coeff_mk]
  exact ⟨n + 1, cexCoeff_pow_succ n⟩

/-- In the `j`-th factor of `CexRing` only the `j`-th coefficient survives, so the image of
`cexSeries` there is the monomial `(t j) · X^j`. -/
lemma map_cexSeries (j : ℕ) :
    PowerSeries.map (Pi.evalRingHom Trunc j) cexSeries = PowerSeries.monomial j (t j) := by
  ext n
  rw [PowerSeries.coeff_map, cexSeries, PowerSeries.coeff_mk, PowerSeries.coeff_monomial,
    cexCoeff]
  by_cases h : n = j
  · subst h
    simp [Pi.single_eq_same]
  · simp [h]

/-- The counterexample series is not nilpotent: in the `(k+1)`-st factor, the coefficient of
`X^((k+1)*(k+1))` in `cexSeries^(k+1)` is `(t (k+1))^(k+1)`, which is nonzero because
`k+1 ≤ k+1`. -/
theorem not_isNilpotent_cexSeries : ¬ IsNilpotent cexSeries := by
  rintro ⟨k, hk⟩
  have hk' : cexSeries ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have h2 : PowerSeries.map (Pi.evalRingHom Trunc (k + 1)) (cexSeries ^ (k + 1)) = 0 := by
    rw [hk', map_zero]
  rw [map_pow, map_cexSeries, PowerSeries.monomial_pow] at h2
  have hcoeff := congrArg (PowerSeries.coeff ((k + 1) * (k + 1))) h2
  rw [PowerSeries.coeff_monomial_same] at hcoeff
  exact t_pow_ne_zero (by omega) hcoeff

/-- **The Noetherian hypothesis of A–M Ch. 7 Ex. 2 is essential**: over the ring `CexRing`
every coefficient of `cexSeries` is nilpotent, yet `cexSeries` itself is not nilpotent, so the
biconditional with the hypothesis "`A` is Noetherian" deleted is false. -/
theorem noetherian_hypothesis_not_redundant :
    (∀ n, IsNilpotent (PowerSeries.coeff n cexSeries)) ∧ ¬ IsNilpotent cexSeries :=
  ⟨cexSeries_coeff_isNilpotent, not_isNilpotent_cexSeries⟩

end

end AtiyahMcdonald69.Ex_7_2
