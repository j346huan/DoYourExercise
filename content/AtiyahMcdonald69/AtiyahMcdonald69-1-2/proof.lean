import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.RingTheory.Ideal.Span

theorem AtiyahMcdonald69.Ex_1_2.solution {A : Type*} [CommRing A] (f g : Polynomial A) :
  (IsUnit f ↔ IsUnit (f.coeff 0) ∧ ∀ i : ℕ, i ≠ 0 → IsNilpotent (f.coeff i)) ∧
  (IsNilpotent f ↔ ∀ i : ℕ, IsNilpotent (f.coeff i)) ∧
  ((∃ h : Polynomial A, h ≠ 0 ∧ f * h = 0) ↔ ∃ a : A, a ≠ 0 ∧ Polynomial.C a * f = 0) ∧
  (Ideal.span (Set.range (f * g).coeff) = (⊤ : Ideal A) ↔
    Ideal.span (Set.range f.coeff) = (⊤ : Ideal A) ∧
    Ideal.span (Set.range g.coeff) = (⊤ : Ideal A)) := by
  classical
  refine ⟨Polynomial.isUnit_iff_coeff_isUnit_isNilpotent, Polynomial.isNilpotent_iff, ?_, ?_⟩
  · constructor
    · rintro ⟨h, hh, hfh⟩
      by_contra hn
      apply hh
      apply Polynomial.eq_zero_of_mul_eq_zero_of_smul f _ h hfh
      intro a haf
      by_contra ha
      apply hn
      refine ⟨a, ha, ?_⟩
      simpa only [Polynomial.smul_eq_C_mul] using haf
    · rintro ⟨a, ha, haf⟩
      refine ⟨Polynomial.C a, ?_, ?_⟩
      · intro h
        apply ha
        simpa using congrArg (fun p : Polynomial A => p.coeff 0) h
      · simpa [mul_comm] using haf
  · have hmap (p : Polynomial A) (I : Ideal A) :
        p.map (Ideal.Quotient.mk I) = 0 ↔ Ideal.span (Set.range p.coeff) ≤ I := by
      rw [Ideal.span_le]
      constructor
      · intro hp x hx
        obtain ⟨i, rfl⟩ := hx
        have hc := congrArg (fun q : Polynomial (A ⧸ I) => q.coeff i) hp
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
          Ideal.Quotient.eq_zero_iff_mem] using hc
      · intro hp
        ext i
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
          Ideal.Quotient.eq_zero_iff_mem] using hp (Set.mem_range_self i)
    have hle (p q : Polynomial A) :
        Ideal.span (Set.range (p * q).coeff) ≤ Ideal.span (Set.range p.coeff) := by
      apply (hmap (p * q) _).mp
      rw [Polynomial.map_mul, (hmap p _).mpr le_rfl, zero_mul]
    constructor
    · intro hfg
      constructor
      · apply top_unique
        simpa only [hfg] using hle f g
      · apply top_unique
        have hgf : Ideal.span (Set.range (g * f).coeff) = (⊤ : Ideal A) := by
          simpa only [mul_comm] using hfg
        simpa only [hgf] using hle g f
    · rintro ⟨hf, hg⟩
      by_contra hfg
      obtain ⟨M, h₁, h₂⟩ := Ideal.exists_le_maximal
        (Ideal.span (Set.range (f * g).coeff)) hfg
      have hM : M.IsMaximal := by assumption
      have hIM : Ideal.span (Set.range (f * g).coeff) ≤ M := by assumption
      letI : M.IsMaximal := hM
      have hm : f.map (Ideal.Quotient.mk M) * g.map (Ideal.Quotient.mk M) = 0 := by
        rw [← Polynomial.map_mul]
        exact (hmap (f * g) M).mpr hIM
      rcases mul_eq_zero.mp hm with hfm | hgm
      · apply hM.ne_top
        apply top_unique
        simpa only [hf] using (hmap f M).mp hfm
      · apply hM.ne_top
        apply top_unique
        simpa only [hg] using (hmap g M).mp hgm
