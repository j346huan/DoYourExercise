import Mathlib.RingTheory.Ideal.Maximal

theorem AtiyahMcdonald69.Ex_1_7.solution (A : Type*) [CommRing A] (hA : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x) :
  ∀ p : Ideal A, p.IsPrime → p.IsMaximal := by
  intro p hp
  refine Ideal.isMaximal_iff.mpr ⟨?_, ?_⟩
  · simpa only [Ideal.ne_top_iff_one] using hp.ne_top
  · intro J x hpJ hxp hxJ
    obtain ⟨n, hn, hx⟩ := hA x
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ k =>
        have hz : x * (x ^ (k + 1) - 1) = 0 := by
          rw [mul_sub, mul_one, ← pow_succ', hx, sub_self]
        have hs : x ^ (k + 1) - 1 ∈ p := by
          apply (hp.mem_or_mem (show x * (x ^ (k + 1) - 1) ∈ p from hz.symm ▸ p.zero_mem)).resolve_left hxp
        have hpow : x ^ (k + 1) ∈ J := by
          rw [pow_succ]
          exact J.mul_mem_left (x ^ k) hxJ
        simpa using J.sub_mem hpow (hpJ hs)
