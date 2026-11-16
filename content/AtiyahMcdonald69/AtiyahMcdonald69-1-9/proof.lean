import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
Atiyah–Macdonald (1969), Chapter 1, Exercise 9.

A proper ideal `a` is radical if and only if it is the intersection of a
collection of prime ideals. The properness assumption is retained, although
the argument also works when the collection is empty, since `sInf ∅ = ⊤`.
Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-9
-/

/-- Exercise 1.9: characterization of a radical ideal by an intersection of prime ideals. -/
theorem AtiyahMcdonald69.Ex_1_9.solution {A : Type*} [CommRing A]
    (a : Ideal A) (ha : a ≠ ⊤) :
    a.radical = a ↔ ∃ s : Set (Ideal A), (∀ p ∈ s, p.IsPrime) ∧ a = sInf s := by
  constructor
  · intro h
    refine ⟨{p : Ideal A | a ≤ p ∧ p.IsPrime}, fun p hp => hp.2, ?_⟩
    rw [← Ideal.radical_eq_sInf, h]
  · rintro ⟨s, hs, rfl⟩
    apply le_antisymm ?_ Ideal.le_radical
    rintro x ⟨n, hn⟩
    rw [Ideal.mem_sInf] at hn ⊢
    exact fun p hp => (hs p hp).mem_of_pow_mem n (hn hp)

#print axioms AtiyahMcdonald69.Ex_1_9.solution
