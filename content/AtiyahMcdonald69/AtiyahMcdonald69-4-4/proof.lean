/-
# Atiyah–Macdonald, Chapter 4, Exercise 4

The exercise (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 4, Exercise 4)
reads:

> In the polynomial ring `ℤ[t]`, the ideal `𝔪 = (2, t)` is maximal and the ideal
> `𝔮 = (4, t)` is `𝔪`-primary, but is not a power of `𝔪`.

We formalize all three assertions for `R = ℤ[X]`.

The proofs use two evaluation maps:
* `ev₀ : ℤ[X] →+* ℤ`, evaluation at `t = 0` (the constant coefficient). Its kernel
  description gives `(a, t) = ev₀ ⁻¹ (a)` for every `a : ℤ`, so `𝔪 = ev₀ ⁻¹ (2)` is maximal
  (pullback of a maximal ideal along a surjection) and `𝔮 = ev₀ ⁻¹ (4)`.
* `φ : ℤ[X] →+* ZMod 4`, evaluation at `t = 2`. It kills `𝔪² = (4, 2t, t²)` but sends `t`
  to `2 ≠ 0`, which shows `t ∉ 𝔪²` and hence `𝔮 ≠ 𝔪ⁿ` for `n ≥ 2`.
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_4_4

open Polynomial

/-- The ideal `𝔪 = (2, t)` of `ℤ[t]`. -/
noncomputable def m : Ideal ℤ[X] := Ideal.span {(2 : ℤ[X]), X}

/-- The ideal `𝔮 = (4, t)` of `ℤ[t]`. -/
noncomputable def q : Ideal ℤ[X] := Ideal.span {(4 : ℤ[X]), X}

/-! ## The constant coefficient as a ring hom -/

/-- Evaluation at `t = 0`, i.e. the constant coefficient, as a ring hom `ℤ[t] →+* ℤ`. -/
noncomputable def ev₀ : ℤ[X] →+* ℤ := Polynomial.eval₂RingHom (RingHom.id ℤ) 0

@[simp]
lemma ev₀_apply (f : ℤ[X]) : ev₀ f = f.coeff 0 := by
  simp [ev₀, Polynomial.eval₂_at_zero]

lemma ev₀_surjective : Function.Surjective ev₀ := fun n => ⟨C n, by simp⟩

/-- For every `a : ℤ`, the ideal `(a, t)` is the preimage of the ideal `(a)` of `ℤ` under the
constant-coefficient map. -/
lemma span_pair_eq_comap (a : ℤ) :
    Ideal.span {C a, X} = Ideal.comap ev₀ (Ideal.span {a}) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show ev₀ (C a) ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      simp
    · show ev₀ (X : ℤ[X]) ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      simp
  · intro f hf
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hf
    obtain ⟨k, hk⟩ := hf
    have hk' : f.coeff 0 = a * k := by rw [← ev₀_apply]; exact hk
    have hdec : f = X * f.divX + C (f.coeff 0) := (X_mul_divX_add f).symm
    rw [hdec, hk']
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · have h1 : C (a * k) = (C a) * C k := by simp
      rw [h1]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

lemma m_eq_comap : m = Ideal.comap ev₀ (Ideal.span {(2 : ℤ)}) := by
  rw [m]; simpa using span_pair_eq_comap 2

lemma q_eq_comap : q = Ideal.comap ev₀ (Ideal.span {(4 : ℤ)}) := by
  rw [q]; simpa using span_pair_eq_comap 4

/-- Membership in `𝔪 = (2, t)`: the constant coefficient is even. -/
lemma mem_m_iff {f : ℤ[X]} : f ∈ m ↔ (2 : ℤ) ∣ f.coeff 0 := by
  rw [m_eq_comap, Ideal.mem_comap, Ideal.mem_span_singleton, ev₀_apply]

/-- Membership in `𝔮 = (4, t)`: the constant coefficient is divisible by `4`. -/
lemma mem_q_iff {f : ℤ[X]} : f ∈ q ↔ (4 : ℤ) ∣ f.coeff 0 := by
  rw [q_eq_comap, Ideal.mem_comap, Ideal.mem_span_singleton, ev₀_apply]

/-! ## `𝔪` is maximal -/

theorem m_isMaximal : m.IsMaximal := by
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  rw [m_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective ev₀ ev₀_surjective

/-! ## `𝔮` is `𝔪`-primary -/

lemma q_le_m : q ≤ m := by
  intro f hf
  rw [mem_m_iff, mem_q_iff] at *
  exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) hf

/-- The radical of `𝔮 = (4, t)` is `𝔪 = (2, t)`. -/
theorem q_radical : q.radical = m := by
  refine le_antisymm ?_ ?_
  · rw [← m_isMaximal.isPrime.radical]
    exact Ideal.radical_mono q_le_m
  · rw [m, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have h4 : (4 : ℤ[X]) ∈ q := Ideal.subset_span (by simp)
      have h2 : (2 : ℤ[X]) ^ 2 ∈ q := by
        have hsq : (2 : ℤ[X]) ^ 2 = 4 := by norm_num
        rwa [hsq]
      exact Ideal.mem_radical_iff.mpr ⟨2, h2⟩
    · exact Ideal.mem_radical_iff.mpr ⟨1, Ideal.subset_span (by simp)⟩

/-- `𝔮 = (4, t)` is `𝔪`-primary: it is primary with radical `𝔪`. -/
theorem q_isPrimary : q.IsPrimary := by
  refine Ideal.isPrimary_of_isMaximal_radical ?_
  rw [q_radical]
  exact m_isMaximal

/-- The primary condition, unfolded: a product in `𝔮` has a factor in `𝔮` or in `𝔪 = √𝔮`. -/
theorem q_primary_def {x y : ℤ[X]} (h : x * y ∈ q) : x ∈ q ∨ y ∈ m := by
  have h' := (Ideal.isPrimary_iff.mp q_isPrimary).2 h
  rwa [q_radical] at h'

lemma four_mem_q : (4 : ℤ[X]) ∈ q := Ideal.subset_span (by simp)

lemma X_mem_q : (X : ℤ[X]) ∈ q := Ideal.subset_span (by simp)

lemma two_notMem_q : (2 : ℤ[X]) ∉ q := by
  rw [mem_q_iff]; norm_num

lemma two_mem_m : (2 : ℤ[X]) ∈ m := Ideal.subset_span (by simp)

lemma q_ne_top : q ≠ ⊤ := by
  intro h
  have h2 : (2 : ℤ[X]) ∈ q := h ▸ Submodule.mem_top
  exact two_notMem_q h2

/-! ## `t ∉ 𝔪²` -/

/-- Evaluation at `t = 2` in `ℤ/4`. -/
noncomputable def phi : ℤ[X] →+* ZMod 4 := Polynomial.eval₂RingHom (Int.castRingHom (ZMod 4)) 2

lemma phi_two : phi (2 : ℤ[X]) = 2 := by simp [phi]

lemma phi_X : phi (X : ℤ[X]) = 2 := by simp [phi]

/-- `𝔪² = (4, 2t, t²)`. -/
lemma m_sq : m ^ 2 = Ideal.span ({(2 : ℤ[X]) * 2, 2 * X, X * 2, X * X} : Set ℤ[X]) := by
  rw [pow_two, m, Ideal.span_pair_mul_span_pair]

/-- The book's shape of the second power: `𝔪² = (4, 2t, t²)`. -/
lemma m_sq' : m ^ 2 = Ideal.span {(4 : ℤ[X]), 2 * X, X * X} := by
  rw [m_sq]
  congr 1
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl (by rw [mul_comm]))
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- `𝔪² ⊆ 𝔮`. Together with `q_lt_m` (`𝔮 ⊊ 𝔪`) and `X_notMem_m_sq`
(`t ∈ 𝔮 \ 𝔪²`), this is the sandwich `𝔪² ⊆ 𝔮 ⊊ 𝔪`. -/
lemma m_sq_le_q : m ^ 2 ≤ q := by
  rw [m_sq', Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact four_mem_q
  · rw [mul_comm (2 : ℤ[X]) X]
    exact Ideal.mul_mem_right 2 q X_mem_q
  · exact Ideal.mul_mem_right X q X_mem_q

lemma q_lt_m : q < m := by
  refine lt_of_le_of_ne q_le_m ?_
  intro h
  exact two_notMem_q (h ▸ two_mem_m)

theorem X_notMem_m_sq : (X : ℤ[X]) ∉ m ^ 2 := by
  intro h
  have hle : Ideal.span ({(2 : ℤ[X]) * 2, 2 * X, X * 2, X * X} : Set ℤ[X]) ≤
      RingHom.ker phi := by
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact RingHom.mem_ker.mpr (by simp [phi]; decide)
    · exact RingHom.mem_ker.mpr (by simp [phi]; decide)
    · exact RingHom.mem_ker.mpr (by simp [phi]; decide)
    · exact RingHom.mem_ker.mpr (by simp [phi]; decide)
  have hz : phi (X : ℤ[X]) = 0 := hle (m_sq ▸ h)
  rw [phi_X] at hz
  exact absurd hz (by decide)

/-! ## `𝔮` is not a power of `𝔪` -/

theorem q_ne_pow (n : ℕ) : q ≠ m ^ n := by
  rintro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have h1 : (1 : ℤ[X]) ∈ q := by rw [h]; simp
      rw [mem_q_iff] at h1
      norm_num at h1
    · have h2 : (2 : ℤ[X]) ∈ q := by
        rw [h, pow_one, mem_m_iff]
        norm_num
      rw [mem_q_iff] at h2
      norm_num at h2
  · have hXq : (X : ℤ[X]) ∈ q := by rw [mem_q_iff]; norm_num
    have hXm : (X : ℤ[X]) ∈ m ^ n := by rw [← h]; exact hXq
    exact X_notMem_m_sq (Ideal.pow_le_pow_right (I := m) hn hXm)

/-- Atiyah–Macdonald, Chapter 4, Exercise 4: in `ℤ[t]`, the ideal `𝔪 = (2, t)` is maximal,
`𝔮 = (4, t)` is `𝔪`-primary, and `𝔮` is not a power of `𝔪`. -/
theorem solution :
    m.IsMaximal ∧ q.IsPrimary ∧ q.radical = m ∧ (∀ n : ℕ, q ≠ m ^ n) :=
  ⟨m_isMaximal, q_isPrimary, q_radical, q_ne_pow⟩

end AtiyahMcdonald69.Ex_4_4

/-! ## Axiom audit -/

#print axioms AtiyahMcdonald69.Ex_4_4.m_isMaximal
#print axioms AtiyahMcdonald69.Ex_4_4.q_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_4.q_radical
#print axioms AtiyahMcdonald69.Ex_4_4.m_sq'
#print axioms AtiyahMcdonald69.Ex_4_4.m_sq_le_q
#print axioms AtiyahMcdonald69.Ex_4_4.q_lt_m
#print axioms AtiyahMcdonald69.Ex_4_4.X_notMem_m_sq
#print axioms AtiyahMcdonald69.Ex_4_4.q_primary_def
#print axioms AtiyahMcdonald69.Ex_4_4.q_ne_pow
#print axioms AtiyahMcdonald69.Ex_4_4.solution
