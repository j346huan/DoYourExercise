import Mathlib.RingTheory.Jacobson.Ideal

theorem AtiyahMcdonald69.Ex_1_6.solution (A : Type*) [CommRing A] (h : ∀ I : Ideal A, ¬ I ≤ (⊥ : Ideal A).radical → ∃ e : A, e ∈ I ∧ e ≠ 0 ∧ e * e = e) :
  (⊥ : Ideal A).jacobson = (⊥ : Ideal A).radical := by
    apply le_antisymm _ Ideal.radical_le_jacobson
    by_contra hn
    obtain ⟨e, he, hne, hee⟩ := h _ hn
    have hu : IsUnit (1 - e) := by
      simpa [sub_eq_add_neg, add_comm] using (Ideal.mem_jacobson_bot.mp he (-1))
    apply hne
    apply hu.mul_left_cancel
    simp [sub_mul, hee]
