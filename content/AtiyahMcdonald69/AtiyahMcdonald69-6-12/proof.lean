/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: m11 (swarm smwi7oexz)
-/
import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 6 (Chain Conditions), Exercise 12

Reference: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-12

The exercise reads:

> Let `A` be a ring such that `Spec A` is a Noetherian space. Show that the set of prime ideals
> of `A` satisfies the ascending chain condition. Is the converse true?

Both halves are formalized below.

* `AtiyahMcdonald69.Ex_6_12.part_i`: if `Spec A` is a Noetherian topological space, then every
  ascending chain of prime ideals of `A` is eventually constant.
* `AtiyahMcdonald69.Ex_6_12.Cring`, `...part_ii` and `...converse_false`: the converse fails.
  For the ring `A = ∏_{i ∈ ℕ} ℤ/2ℤ` every prime ideal is maximal, hence the prime ideals satisfy
  the ascending chain condition, while the zero loci of the sets of functions supported in the
  first `n` coordinates form a strictly decreasing sequence of closed subsets of `Spec A`; thus
  `Spec A` is not a Noetherian space.

Source audit.  The statement quoted above is Chapter 6, Exercise 12 of the book, and is exactly the
statement proved in the reference proof for `AtiyahMcdonald69-6-12` (it also agrees with the
standard solution manual).  The public scan `.scratch/reference/atiyah-macdonald-original.txt`
stops in the middle of Chapter 6 and does not reach the Chapter 6 exercise list, so the statement
was cross-checked against the reference proof and the solution manual rather than the scan.  The
counterexample formalized here, the product of countably many copies of `ℤ/2ℤ`, is the one given
in the solution manual; the reference proof uses instead `k[x₁, x₂, …]/(xᵢxⱼ : i ≠ j)`, which is
also a correct counterexample but is not formalized here.
-/

namespace AtiyahMcdonald69.Ex_6_12

open TopologicalSpace

/-! ## Part (i): a Noetherian spectrum forces the ascending chain condition on primes -/

/-- Atiyah–Macdonald define a Noetherian space by the descending chain condition on closed
subsets; Mathlib's `NoetherianSpace` is the ascending chain condition on open subsets, and
`noetherianSpace_TFAE` gives the equivalence (`WellFoundedLT (Closeds X)` is the DCC).  We record
the equivalence to pin down that the hypothesis of the exercise is the one used in `part_i`. -/
theorem noetherianSpace_iff_dcc_closed (X : Type*) [TopologicalSpace X] :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (noetherianSpace_TFAE X).out 0 1

/-- Auxiliary combinatorial fact: in a Noetherian space, an antitone sequence of closed sets is
eventually constant. -/
theorem antitone_closeds_eventually_eq {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (F : ℕ → Closeds X) (hF : ∀ n, F (n + 1) ≤ F n) :
    ∃ N, ∀ n, N ≤ n → F n = F N := by
  have hanti : Antitone F := antitone_nat_of_succ_le hF
  -- a minimal element of the range
  obtain ⟨a, ha, hmin⟩ := wellFounded_lt.has_min (Set.range F) ⟨F 0, Set.mem_range_self 0⟩
  obtain ⟨N, rfl⟩ := ha
  refine ⟨N, fun n hn => le_antisymm (hanti hn) ?_⟩
  by_contra h
  exact hmin (F n) ⟨n, rfl⟩ (lt_of_le_not_ge (hanti hn) h)

/-- **Atiyah–Macdonald, Exercise 6.12, first part.**  If `Spec A` is a Noetherian topological
space, then the set of prime ideals of `A` satisfies the ascending chain condition: every
ascending chain `p 0 ≤ p 1 ≤ ⋯` of prime ideals is eventually constant. -/
theorem part_i (A : Type*) [CommRing A] [NoetherianSpace (PrimeSpectrum A)]
    (p : ℕ → Ideal A) (hp : ∀ n, (p n).IsPrime) (hmono : Monotone p) :
    ∃ N, ∀ n, N ≤ n → p n = p N := by
  -- the associated antitone sequence of closed subsets `V (p n)`
  let F : ℕ → Closeds (PrimeSpectrum A) :=
    fun n => ⟨PrimeSpectrum.zeroLocus (p n : Set A), PrimeSpectrum.isClosed_zeroLocus _⟩
  have hF : ∀ n, F (n + 1) ≤ F n := by
    intro n
    show PrimeSpectrum.zeroLocus (p (n + 1) : Set A) ⊆ PrimeSpectrum.zeroLocus (p n : Set A)
    intro x hx
    exact le_trans (hmono (Nat.le_succ n)) hx
  obtain ⟨N, hN⟩ := antitone_closeds_eventually_eq F hF
  refine ⟨N, fun n hn => le_antisymm ?_ (hmono hn)⟩
  -- `p N` is a point of `V (p N) = V (p n)`, hence `p n ≤ p N`
  have hmem : (⟨p N, hp N⟩ : PrimeSpectrum A) ∈ F N := by
    show (p N : Set A) ⊆ (⟨p N, hp N⟩ : PrimeSpectrum A).asIdeal
    exact fun _ hx => hx
  rw [← hN n hn] at hmem
  exact hmem

/-! ## Part (ii): the converse fails -/

/-- The counterexample ring: the product of countably many copies of `ℤ/2`. -/
abbrev Cring : Type := ℕ → ZMod 2

namespace Cring

/-- Every element of `ℤ/2` is idempotent. -/
theorem zmod_two_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

/-- The counterexample ring is a Boolean ring: every element is idempotent. -/
theorem mul_self (x : Cring) : x * x = x := by
  funext i
  exact zmod_two_mul_self (x i)

/-- In this ring any two comparable prime ideals are equal; in other words every prime ideal is
maximal.  (Comparability is all that is needed for the ascending chain condition.) -/
theorem eq_of_le_of_isPrime {P Q : Ideal Cring} (hP : P.IsPrime) (hQ : Q.IsPrime) (h : P ≤ Q) :
    P = Q := by
  refine le_antisymm h (fun x hx => ?_)
  have hzero : x * (1 - x) ∈ P := by
    rw [mul_sub, mul_one, mul_self, sub_self]
    exact P.zero_mem
  rcases hP.mem_or_mem hzero with hxp | hx'
  · exact hxp
  · exact absurd (by
      have h1 : x + (1 - x) ∈ Q := Q.add_mem hx (h hx')
      rwa [add_sub_cancel] at h1) hQ.one_notMem

/-- Every prime ideal of `∏_{i ∈ ℕ} ℤ/2ℤ` is maximal (it suffices that distinct prime ideals are
incomparable, which follows from idempotence). -/
theorem isMaximal_of_isPrime {P : Ideal Cring} (hP : P.IsPrime) : P.IsMaximal := by
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun J hJ => ?_⟩
  by_contra hJne
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJne
  have hPm : P ≤ m := le_trans hJ.le hJm
  have hPeq : P = m := eq_of_le_of_isPrime hP hm.isPrime hPm
  exact lt_irrefl P (lt_of_lt_of_le hJ (hPeq ▸ hJm))

/-- The prime ideals of `∏_{i ∈ ℕ} ℤ/2ℤ` satisfy the ascending chain condition (in fact every
ascending chain of prime ideals is constant). -/
theorem primes_acc (p : ℕ → Ideal Cring) (hp : ∀ n, (p n).IsPrime) (hmono : Monotone p) :
    ∃ N, ∀ n, N ≤ n → p n = p N :=
  ⟨0, fun n _ => (eq_of_le_of_isPrime (P := p 0) (Q := p n) (hp 0) (hp n)
    (hmono (Nat.zero_le n))).symm⟩

/-- The prime ideal given by the `n`-th coordinate projection. -/
def coordPrime (n : ℕ) : Ideal Cring :=
  RingHom.ker (Pi.evalRingHom (fun _ : ℕ => ZMod 2) n)

theorem coordPrime_isPrime (n : ℕ) : (coordPrime n).IsPrime :=
  RingHom.ker_isPrime _

theorem mem_coordPrime {n : ℕ} {x : Cring} : x ∈ coordPrime n ↔ x n = 0 := by
  simp [coordPrime, RingHom.mem_ker]

/-- The set of elements of `∏_{i ∈ ℕ} ℤ/2ℤ` supported in the first `n` coordinates. -/
def tailVanish (n : ℕ) : Set Cring := {x | ∀ i, n ≤ i → x i = 0}

theorem tailVanish_subset_succ (n : ℕ) : tailVanish n ⊆ tailVanish (n + 1) :=
  fun _x hx i hi => hx i (le_trans (Nat.le_succ n) hi)

theorem coordPrime_mem_zeroLocus (n : ℕ) :
    (⟨coordPrime n, coordPrime_isPrime n⟩ : PrimeSpectrum Cring) ∈
      PrimeSpectrum.zeroLocus (tailVanish n) := by
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  exact mem_coordPrime.mpr (hx n le_rfl)

theorem coordPrime_notMem_zeroLocus (n : ℕ) :
    (⟨coordPrime n, coordPrime_isPrime n⟩ : PrimeSpectrum Cring) ∉
      PrimeSpectrum.zeroLocus (tailVanish (n + 1)) := by
  intro h
  have hmem : Pi.single n (1 : ZMod 2) ∈ tailVanish (n + 1) := by
    intro i hi
    exact Pi.single_eq_of_ne' (by omega) 1
  have h2 : Pi.single n (1 : ZMod 2) ∈ coordPrime n := h hmem
  rw [mem_coordPrime, Pi.single_eq_same] at h2
  exact one_ne_zero h2

/-- The strictly increasing chain of open subsets of `Spec (∏_{i ∈ ℕ} ℤ/2ℤ)` given by the
complements of the zero loci of `tailVanish n`. -/
def U (n : ℕ) : Opens (PrimeSpectrum Cring) :=
  ⟨(PrimeSpectrum.zeroLocus (tailVanish n))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

theorem U_lt_succ (n : ℕ) : U n < U (n + 1) := by
  rw [lt_iff_le_not_ge]
  constructor
  · intro x hx
    exact fun hc => hx (Set.Subset.trans (tailVanish_subset_succ n) hc)
  · intro h
    have hq : (⟨coordPrime n, coordPrime_isPrime n⟩ : PrimeSpectrum Cring) ∈ U (n + 1) :=
      coordPrime_notMem_zeroLocus n
    exact (h hq) (coordPrime_mem_zeroLocus n)

/-- `Spec (∏_{i ∈ ℕ} ℤ/2ℤ)` is not a Noetherian space. -/
theorem not_noetherianSpace : ¬ NoetherianSpace (PrimeSpectrum Cring) := by
  intro h
  exact @not_strictMono_of_wellFoundedGT (Opens (PrimeSpectrum Cring)) _ h U
    (strictMono_nat_of_lt_succ U_lt_succ)

/-- **Atiyah–Macdonald, Exercise 6.12, second part.**  The ring `∏_{i ∈ ℕ} ℤ/2ℤ` has the ascending
chain condition on prime ideals but its spectrum is not a Noetherian space. -/
theorem part_ii :
    (∀ p : ℕ → Ideal Cring, (∀ n, (p n).IsPrime) → Monotone p →
        ∃ N, ∀ n, N ≤ n → p n = p N) ∧ ¬ NoetherianSpace (PrimeSpectrum Cring) :=
  ⟨primes_acc, not_noetherianSpace⟩

end Cring

/-- **Atiyah–Macdonald, Exercise 6.12, answer to "Is the converse true?"**  No: the ascending chain
condition on prime ideals does not force the spectrum to be a Noetherian space. -/
theorem converse_false :
    ¬ (∀ (A : Type) [CommRing A],
        (∀ p : ℕ → Ideal A, (∀ n, (p n).IsPrime) → Monotone p →
          ∃ N, ∀ n, N ≤ n → p n = p N) →
        NoetherianSpace (PrimeSpectrum A)) := by
  intro H
  exact Cring.not_noetherianSpace (H Cring Cring.primes_acc)

/-- **Atiyah–Macdonald, Exercise 6.12**, both halves in one statement: a Noetherian spectrum
forces the ascending chain condition on prime ideals, but not conversely. -/
theorem solution :
    (∀ (A : Type) [CommRing A] [NoetherianSpace (PrimeSpectrum A)]
        (p : ℕ → Ideal A), (∀ n, (p n).IsPrime) → Monotone p → ∃ N, ∀ n, N ≤ n → p n = p N) ∧
      ¬ (∀ (A : Type) [CommRing A],
        (∀ p : ℕ → Ideal A, (∀ n, (p n).IsPrime) → Monotone p →
          ∃ N, ∀ n, N ≤ n → p n = p N) →
        NoetherianSpace (PrimeSpectrum A)) :=
  ⟨fun A _ _ p hp hmono => part_i A p hp hmono, converse_false⟩

end AtiyahMcdonald69.Ex_6_12
