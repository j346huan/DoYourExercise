import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.Ring
import Mathlib.SetTheory.Cardinal.Finite

/-!
Atiyah–Macdonald (1969), Chapter 1, Exercise 11.

For a commutative ring all of whose elements are idempotent, prove:
(i) `2x = 0`;
(ii) every prime ideal `p` is maximal and its quotient has exactly two elements;
(iii) every finitely generated ideal is principal.
The formal theorem `solution` bundles all three assertions, each with the
exercise's original scope.
Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-11
-/

namespace AtiyahMcdonald69.Ex_1_11

variable {A : Type*} [CommRing A] (h : ∀ x : A, x * x = x)

include h

private lemma add_self_zero (x : A) : x + x = 0 := by
  have hx : (x + x) * (x + x) = (x + x) + (x + x) := by
    simp only [add_mul, mul_add, h x]
  apply add_left_cancel (a := x + x)
  rw [add_zero, ← hx]
  exact h (x + x)

/-- Exercise 1.11(i). -/
theorem part_a (x : A) : 2 * x = 0 := by
  simpa [two_mul] using add_self_zero h x

private lemma mem_or_one_sub_mem (p : Ideal A) (hp : p.IsPrime) (x : A) :
    x ∈ p ∨ 1 - x ∈ p := by
  have hz : x * (1 - x) = 0 := by
    rw [mul_sub, h x, mul_one, sub_self]
  apply hp.mem_or_mem
  rw [hz]
  exact p.zero_mem

private theorem quotient_zero_or_one (p : Ideal A) (hp : p.IsPrime) :
    ∀ x : A ⧸ p, x = 0 ∨ x = 1 := by
  rintro ⟨x⟩
  rcases mem_or_one_sub_mem h p hp x with hx | hx
  · left
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · right
    apply Ideal.Quotient.eq.mpr
    simpa only [neg_sub] using p.neg_mem hx

/-- Exercise 1.11(ii), maximality of a prime ideal. -/
private theorem prime_isMaximal (p : Ideal A) (hp : p.IsPrime) : p.IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨?_, ?_⟩
  · intro h1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)
  · intro J x hpJ hx hxJ
    have hxI : 1 - x ∈ p := (mem_or_one_sub_mem h p hp x).resolve_left hx
    have hsum : x + (1 - x) = 1 := by abel
    rw [← hsum]
    exact J.add_mem hxJ (hpJ hxI)

/-- Exercise 1.11(ii), including the assertion that the quotient has two elements. -/
theorem part_b (p : Ideal A) (hp : p.IsPrime) :
    p.IsMaximal ∧ Nat.card (A ⧸ p) = 2 := by
  refine ⟨prime_isMaximal h p hp, ?_⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨0, 1, ?_, Set.eq_univ_of_forall ?_⟩
  · intro h01
    have hmem : (1 : A) ∈ p := Ideal.Quotient.eq_zero_iff_mem.mp h01.symm
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr hmem)
  · intro x
    rcases quotient_zero_or_one h p hp x with hx | hx <;> simp [hx]

private lemma join_mul_left (a b : A) : a * (a + b + a * b) = a := by
  rw [mul_add, mul_add, h a, ← mul_assoc, h a, add_assoc, add_self_zero h, add_zero]

private lemma join_mul_right (a b : A) : b * (a + b + a * b) = b := by
  calc
    b * (a + b + a * b) = b * (b + a + b * a) := by ring
    _ = b := join_mul_left h b a

omit h in
private lemma join_mem_span (a b : A) : a + b + a * b ∈ Ideal.span {a} ⊔ Ideal.span {b} := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton a))
    · exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton b))
  · apply Ideal.mul_mem_left
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton b))

private lemma span_pair_join (a b : A) :
    Ideal.span {a} ⊔ Ideal.span {b} = Ideal.span {a + b + a * b} := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
      exact Ideal.mem_span_singleton'.mpr ⟨a, join_mul_left h a b⟩
    · refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
      exact Ideal.mem_span_singleton'.mpr ⟨b, join_mul_right h a b⟩
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (join_mem_span a b))

/-- Exercise 1.11(iii): finitely generated ideals are principal. -/
theorem part_c (I : Ideal A) (hI : I.FG) : ∃ a : A, Ideal.span {a} = I := by
  induction I, hI using Submodule.fg_induction with
  | singleton x => exact ⟨x, rfl⟩
  | sup J K hJ hK ihJ ihK =>
    obtain ⟨a, rfl⟩ := ihJ
    obtain ⟨b, rfl⟩ := ihK
    exact ⟨a + b + a * b, (span_pair_join h a b).symm⟩

/-- Complete Exercise 1.11. -/
theorem solution :
    (∀ x : A, 2 * x = 0) ∧
    (∀ p : Ideal A, p.IsPrime → p.IsMaximal ∧ Nat.card (A ⧸ p) = 2) ∧
    (∀ I : Ideal A, I.FG → ∃ a : A, Ideal.span {a} = I) :=
  ⟨part_a h, part_b h, part_c h⟩

end AtiyahMcdonald69.Ex_1_11

#print axioms AtiyahMcdonald69.Ex_1_11.solution
