import Mathlib

/- Natural-language solution: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-14 -/


/-!
# Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 1.14

Statement (Chapter 1, Exercise 14). *In a ring `A`, let `Σ` be the set of all ideals in which
every element is a zero-divisor. Show that the set `Σ` has maximal elements and that every
maximal element of `Σ` is a prime ideal. Hence the set of zero-divisors in `A` is a union of
prime ideals.*

Main results (namespace `AtiyahMcdonald69.Ex_1_14`):

* `SigmaSet A` — the set `Σ` of ideals all of whose elements are zero-divisors;
* `exists_maximal_SigmaSet` — `Σ` has maximal elements (part 1);
* `isPrime_of_maximal` — every maximal member of `Σ` is a prime ideal (part 2);
* `zeroDivisorSet_eq_iUnion` — the set `D` of zero-divisors is the union of the maximal
  members of `Σ`, and `exists_prime_union` — hence `D` is a union of prime ideals (part 3);
* `solution` — the three assertions of the exercise, bundled.

The `Nontrivial A` hypothesis is necessary for part 1, as the book also permits the zero ring formally: in the zero ring
`1 = 0` is not a zero-divisor, so the zero ideal (the whole ring) is not in `Σ`, `Σ = ∅` has no
maximal element, and `D = ∅`.  The primality of the maximal members of `Σ` and the description
of `D` as a union of prime ideals need no such hypothesis.
-/

namespace AtiyahMcdonald69.Ex_1_14

variable {A : Type*} [CommRing A]

/-- A zero-divisor, in the sense of Atiyah–Macdonald: an element with a nonzero annihilator. -/
def IsZeroDivisor (a : A) : Prop := ∃ b : A, b ≠ 0 ∧ a * b = 0

/-- The set `D` of zero-divisors of a ring. -/
def zeroDivisorSet (A : Type*) [CommRing A] : Set A := {a | IsZeroDivisor a}

/-- The set `Σ` of the exercise: the ideals in which every element is a zero-divisor. -/
def SigmaSet (A : Type*) [CommRing A] : Set (Ideal A) := {I | ∀ a ∈ I, IsZeroDivisor a}

/-- The maximal members of `Σ` (maximality is with respect to inclusion). -/
def SigmaMaximals (A : Type*) [CommRing A] : Set (Ideal A) :=
  {P | P ∈ SigmaSet A ∧ ∀ Q ∈ SigmaSet A, P ≤ Q → Q = P}

theorem mem_zeroDivisorSet {a : A} : a ∈ zeroDivisorSet A ↔ IsZeroDivisor a := Iff.rfl

theorem mem_SigmaSet {I : Ideal A} : I ∈ SigmaSet A ↔ ∀ a ∈ I, IsZeroDivisor a := Iff.rfl

theorem mem_SigmaMaximals {P : Ideal A} :
    P ∈ SigmaMaximals A ↔ P ∈ SigmaSet A ∧ ∀ Q ∈ SigmaSet A, P ≤ Q → Q = P := Iff.rfl

/-- `0` is a zero-divisor as soon as `1 ≠ 0`. -/
theorem zero_isZeroDivisor [Nontrivial A] : IsZeroDivisor (0 : A) :=
  ⟨1, one_ne_zero, zero_mul 1⟩

/-- A multiple of a zero-divisor is a zero-divisor. -/
theorem IsZeroDivisor.mul_right {a : A} (h : IsZeroDivisor a) (r : A) :
    IsZeroDivisor (a * r) := by
  obtain ⟨b, hb, hab⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [mul_assoc, mul_comm r b, ← mul_assoc, hab, zero_mul]

/-- A product of two elements that are not zero-divisors is not a zero-divisor. -/
theorem not_isZeroDivisor_mul {a b : A} (ha : ¬ IsZeroDivisor a) (hb : ¬ IsZeroDivisor b) :
    ¬ IsZeroDivisor (a * b) := by
  rintro ⟨z, hz, hz0⟩
  rw [mul_assoc] at hz0
  by_cases h : b * z = 0
  · exact hb ⟨z, hz, h⟩
  · exact ha ⟨b * z, h, hz0⟩

/-- The zero ideal lies in `Σ`. -/
theorem bot_mem_SigmaSet [Nontrivial A] : (⊥ : Ideal A) ∈ SigmaSet A := by
  intro a ha
  rw [Ideal.mem_bot] at ha
  subst ha
  exact zero_isZeroDivisor

/-- The supremum (= union) of a nonempty chain of members of `Σ` is a member of `Σ`. -/
theorem sSup_mem_SigmaSet {c : Set (Ideal A)} (hne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    (hc : ∀ I ∈ c, I ∈ SigmaSet A) : sSup c ∈ SigmaSet A := by
  intro a ha
  obtain ⟨I, hI, haI⟩ := (Submodule.mem_sSup_of_directed hne hchain.directedOn).1 ha
  exact hc I hI a haI

/-- **Zorn step.** Every member of `Σ` is contained in a maximal member of `Σ`. -/
theorem exists_maximal_ge {I₀ : Ideal A} (hI₀ : I₀ ∈ SigmaSet A) :
    ∃ P, I₀ ≤ P ∧ Maximal (· ∈ SigmaSet A) P :=
  zorn_le_nonempty₀ (SigmaSet A)
    (fun c hc hchain y hy =>
      ⟨sSup c, sSup_mem_SigmaSet ⟨y, hy⟩ hchain hc, fun _ hz => le_sSup hz⟩)
    I₀ hI₀

/-- In the zero ring every element is `0`, which has no nonzero annihilator, so `Σ` is empty.
The existence assertion therefore needs `Nontrivial A`; it need not hold in the zero ring. -/
theorem SigmaSet_eq_empty_of_subsingleton [Subsingleton A] : SigmaSet A = ∅ := by
  ext I
  constructor
  · intro h
    obtain ⟨b, hb, -⟩ := h 0 I.zero_mem
    exact hb (Subsingleton.elim b 0)
  · intro h
    exact False.elim h

/-- **Part 1 of the exercise.** The set `Σ` has maximal elements. -/
theorem exists_maximal_SigmaSet [Nontrivial A] : ∃ P, Maximal (· ∈ SigmaSet A) P :=
  (exists_maximal_ge (I₀ := ⊥) bot_mem_SigmaSet).imp fun _ h => h.2

/-- **Part 2 of the exercise.** Every maximal member of `Σ` is a prime ideal. -/
theorem isPrime_of_maximal {P : Ideal A} (hP : P ∈ SigmaSet A)
    (hmax : ∀ Q ∈ SigmaSet A, P ≤ Q → Q = P) : P.IsPrime := by
  refine ⟨?_, ?_⟩
  · -- `1` is not a zero-divisor, so `1 ∉ P`
    intro htop
    obtain ⟨b, hb, hb0⟩ := hP 1 (htop.symm ▸ Submodule.mem_top)
    exact hb (by simpa using hb0)
  · intro x y hxy
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hy⟩ := hcon
    -- `P ⊔ (x)` strictly contains `P`, so it is not in `Σ`: it has a non-zero-divisor `c`
    have hex : ∃ c ∈ (P ⊔ Ideal.span {x} : Ideal A), ¬ IsZeroDivisor c := by
      by_contra h
      have hmem : P ⊔ Ideal.span {x} ∈ SigmaSet A := by
        intro a ha
        by_contra hna
        exact h ⟨a, ha, hna⟩
      have heq : P ⊔ Ideal.span {x} = P := hmax _ hmem le_sup_left
      exact hx ((Ideal.span_singleton_le_iff_mem P).mp (heq ▸ le_sup_right))
    -- likewise for `P ⊔ (y)`
    have hey : ∃ d ∈ (P ⊔ Ideal.span {y} : Ideal A), ¬ IsZeroDivisor d := by
      by_contra h
      have hmem : P ⊔ Ideal.span {y} ∈ SigmaSet A := by
        intro a ha
        by_contra hna
        exact h ⟨a, ha, hna⟩
      have heq : P ⊔ Ideal.span {y} = P := hmax _ hmem le_sup_left
      exact hy ((Ideal.span_singleton_le_iff_mem P).mp (heq ▸ le_sup_right))
    obtain ⟨c, hcP, hc⟩ := hex
    obtain ⟨d, hdP, hd⟩ := hey
    -- `(P + (x)) * (P + (y)) ⊆ P + (x * y) = P`
    have hcdP : c * d ∈ P := by
      have hle : (P ⊔ Ideal.span {x}) * (P ⊔ Ideal.span {y}) ≤ P := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup,
          Ideal.span_singleton_mul_span_singleton]
        exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
          (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem P).mpr hxy))
      exact hle (Ideal.mul_mem_mul hcP hdP)
    -- but a product of non-zero-divisors is not a zero-divisor
    exact (not_isZeroDivisor_mul hc hd) (hP (c * d) hcdP)

/-- Multiples of a zero-divisor span a member of `Σ`. -/
theorem span_singleton_mem_SigmaSet {a : A} (ha : IsZeroDivisor a) :
    Ideal.span {a} ∈ SigmaSet A := by
  intro b hb
  obtain ⟨r, rfl⟩ := (Ideal.mem_span_singleton).1 hb
  exact ha.mul_right r

/-- **Part 3 of the exercise.** An element is a zero-divisor iff it lies in some maximal
member of `Σ`. -/
theorem isZeroDivisor_iff_exists_maximal (a : A) :
    a ∈ zeroDivisorSet A ↔ ∃ P ∈ SigmaSet A, (∀ Q ∈ SigmaSet A, P ≤ Q → Q = P) ∧ a ∈ P := by
  constructor
  · intro ha
    obtain ⟨P, hle, hmax⟩ := exists_maximal_ge (span_singleton_mem_SigmaSet ha)
    exact ⟨P, hmax.1, fun Q hQ hPQ => le_antisymm (hmax.2 hQ hPQ) hPQ,
      hle (Ideal.subset_span (by simp))⟩
  · rintro ⟨P, hP, -, haP⟩
    exact hP a haP

/-- The set of zero-divisors is the union of the maximal members of `Σ`. -/
theorem zeroDivisorSet_eq_iUnion :
    zeroDivisorSet A = ⋃ P ∈ SigmaMaximals A, (P : Set A) := by
  ext a
  constructor
  · intro ha
    obtain ⟨P, hP, hmax, haP⟩ := (isZeroDivisor_iff_exists_maximal a).1 ha
    exact Set.mem_iUnion.2 ⟨P, Set.mem_iUnion.2 ⟨⟨hP, hmax⟩, haP⟩⟩
  · intro ha
    obtain ⟨P, hP⟩ := Set.mem_iUnion.1 ha
    obtain ⟨hP', haP⟩ := Set.mem_iUnion.1 hP
    exact (isZeroDivisor_iff_exists_maximal a).2 ⟨P, (mem_SigmaMaximals.1 hP').1,
      (mem_SigmaMaximals.1 hP').2, haP⟩

/-- **Part 3 of the exercise, prime form.** The zero-divisors are a union of prime ideals. -/
theorem exists_prime_union :
    ∃ S : Set (Ideal A), (∀ P ∈ S, P.IsPrime) ∧ zeroDivisorSet A = ⋃ P ∈ S, (P : Set A) :=
  ⟨SigmaMaximals A, fun _ hP => isPrime_of_maximal hP.1 hP.2, zeroDivisorSet_eq_iUnion⟩

/-- **Atiyah–Macdonald, Exercise 1.14.** In a nonzero ring, the set `Σ` of ideals all of whose
elements are zero-divisors has maximal elements, every maximal element of `Σ` is prime, and the
set of zero-divisors is the union of the maximal elements of `Σ`. -/
theorem solution [Nontrivial A] :
    (∃ P ∈ SigmaSet A, ∀ Q ∈ SigmaSet A, P ≤ Q → Q = P) ∧
    (∀ P ∈ SigmaSet A, (∀ Q ∈ SigmaSet A, P ≤ Q → Q = P) → P.IsPrime) ∧
    zeroDivisorSet A = ⋃ P ∈ SigmaMaximals A, (P : Set A) := by
  refine ⟨?_, ?_, zeroDivisorSet_eq_iUnion⟩
  · obtain ⟨P, hmax⟩ := exists_maximal_SigmaSet (A := A)
    exact ⟨P, hmax.1, fun Q hQ hPQ => le_antisymm (hmax.2 hQ hPQ) hPQ⟩
  · intro P hP hmax
    exact isPrime_of_maximal hP hmax

end AtiyahMcdonald69.Ex_1_14
