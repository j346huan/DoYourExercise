import Mathlib

/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, §3, Exercise 3.9

SOURCE STATEMENT (verbatim, `.scratch/reference/hartshorne-1977.txt`, Section I.3 exercise
list): "3.9. The homogeneous coordinate ring of a projective variety is not invariant under
isomorphism. For example, let `X = P^1`, and let `Y` be the 2-uple embedding of `P^1` in `P^2`.
Then `X ≅ Y` (Ex. 3.4). But show that `S(X) ≢ S(Y)`."

Natural solution (`.scratch/DoYourExercise/content/Hartshorne77/Hartshorne77-I-3-9/proof.tex`):
"By I.3.4, `X ≅ Y`, but `S(X) = k[s,t]` and `S(Y) ≅ k[s²,st,t²]`. The elements `s²,st,t²`
are irreducible in the latter ring: every nonconstant factor has degree at least `2`. They
are pairwise nonassociate, and `s²t² = (st)²` gives two distinct factorizations. Thus `S(Y)`
is not a UFD, whereas `S(X)` is, so the rings are not isomorphic."

## What is formalized here

The clause to be *shown* is `S(X) ≢ S(Y)`: there is no ring isomorphism between the
homogeneous coordinate rings.  We realize

* `S(X)` as `MvPolynomial (Fin 2) k = k[x₀,x₁]` (`SX`), and
* `S(Y)` as the image `k[x₀², x₀x₁, x₁²]` of the 2-uple substitution
  `θ : k[y₀,y₁,y₂] → k[x₀,x₁]`, `y₀ ↦ x₀²`, `y₁ ↦ x₀x₁`, `y₂ ↦ x₁²` (`SY`),
  Hartshorne's `S(Y) = k[s²,st,t²]`;
* `X ≅ Y` itself is Hartshorne Ex. 3.4, quoted by the exercise and formalized separately
  in this checkpoint (`content/Hartshorne77/Hartshorne77-I-3-4/proof.lean`); it is not
  reproved here.

Main results: `irreducible_st`, `not_prime_st`, `not_isUFD_SY`, `no_ringEquiv`.

The field `k` is arbitrary (the argument is characteristic free); the standing hypothesis
"`k` algebraically closed" is not used.
-/

namespace Hartshorne77.Ex_I_3_9

open MvPolynomial

variable (k : Type*) [Field k]

/-- `S(X)`, the homogeneous coordinate ring of `X = P¹`: `k[x₀,x₁]`. -/
abbrev SX : Type _ := MvPolynomial (Fin 2) k

/-- The 2-uple substitution `θ : k[y₀,y₁,y₂] → k[x₀,x₁]`,
`y₀ ↦ x₀²`, `y₁ ↦ x₀x₁`, `y₂ ↦ x₁²`. -/
noncomputable def theta : MvPolynomial (Fin 3) k →ₐ[k] SX k :=
  aeval ![(X 0) ^ 2, X 0 * X 1, (X 1) ^ 2]

@[simp] theorem theta_X_zero : theta k (X 0) = (X 0) ^ 2 := by
  simp [theta]

@[simp] theorem theta_X_one : theta k (X 1) = X 0 * X 1 := by
  simp [theta]

@[simp] theorem theta_X_two : theta k (X 2) = (X 1) ^ 2 := by
  simp [theta]

/-- `S(Y) = k[x₀², x₀x₁, x₁²] ⊆ k[x₀,x₁]`, the homogeneous coordinate ring of the
2-uple image `Y` of `P¹` in `P²` (Hartshorne's `S(Y) = k[s²,st,t²]`). -/
noncomputable def SY : Subring (SX k) := (theta k : MvPolynomial (Fin 3) k →+* SX k).range

/-- `S(Y)` is the quotient of `k[y₀,y₁,y₂]` by the kernel of the 2-uple substitution: the
coordinate ring of the 2-uple image, presented as a quotient (Hartshorne's
`S(Y) = k[y₀,y₁,y₂]/I(Y)`, here with `ker θ` in place of `I(Y)`; that the two agree is the
content of Hartshorne Ex. I.2.12 (b), formalized separately in this checkpoint). -/
noncomputable def SY_quotient_equiv :
    (MvPolynomial (Fin 3) k ⧸ RingHom.ker (theta k : MvPolynomial (Fin 3) k →+* SX k)) ≃+*
      SY k :=
  RingHom.quotientKerEquivRange _

theorem mem_SY_iff {p : SX k} : p ∈ SY k ↔ ∃ q, theta k q = p := Iff.rfl

/-- Every element of `S(Y)` is a sum of monomials of even total degree. -/
def EvenMono (p : SX k) : Prop := ∀ m ∈ p.support, Even (Finsupp.degree m)

theorem evenMono_C (c : k) : EvenMono k (C c : SX k) := by
  classical
  intro m hm
  by_cases hc : c = 0
  · rw [show (C c : SX k) = 0 by simp [hc]] at hm
    simp at hm
  · rw [support_C, if_neg hc, Finset.mem_singleton] at hm
    rw [hm]
    simp

theorem evenMono_add {p q : SX k} (hp : EvenMono k p) (hq : EvenMono k q) :
    EvenMono k (p + q) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hp m h
  · exact hq m h

theorem evenMono_mul {p q : SX k} (hp : EvenMono k p) (hq : EvenMono k q) :
    EvenMono k (p * q) := by
  intro m hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  rw [map_add]
  exact Even.add (hp m₁ hm₁) (hq m₂ hm₂)

theorem evenMono_monomial {d : Fin 2 →₀ ℕ} {c : k} (hd : Even (Finsupp.degree d)) :
    EvenMono k (monomial d c : SX k) := by
  intro m hm
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact hd

theorem evenMono_X_zero_sq : EvenMono k ((X 0) ^ 2 : SX k) := by
  have h : (X 0 : SX k) ^ 2 = monomial (Finsupp.single (0 : Fin 2) 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
  rw [h]
  exact evenMono_monomial k (by simp [Finsupp.degree_single])

theorem evenMono_X_one_sq : EvenMono k ((X 1) ^ 2 : SX k) := by
  have h : (X 1 : SX k) ^ 2 = monomial (Finsupp.single (1 : Fin 2) 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
  rw [h]
  exact evenMono_monomial k (by simp [Finsupp.degree_single])

theorem evenMono_X_zero_mul_X_one : EvenMono k (X 0 * X 1 : SX k) := by
  have h : (X 0 * X 1 : SX k) =
      monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 := by
    simp [MvPolynomial.X, monomial_mul]
  rw [h]
  refine evenMono_monomial k ?_
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
  exact ⟨1, rfl⟩

/-- `θ` lands in the even-degree part: this is the key structural fact about `S(Y)`. -/
theorem evenMono_theta (q : MvPolynomial (Fin 3) k) : EvenMono k (theta k q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simpa using evenMono_C k c
  | add p q hp hq => simpa using evenMono_add k hp hq
  | mul_X p n hp =>
      have h : theta k (p * X n) = theta k p * theta k (X n) := by simp
      rw [h]
      have hn : EvenMono k (theta k (X n)) := by
        fin_cases n
        · simpa using evenMono_X_zero_sq k
        · simpa using evenMono_X_zero_mul_X_one k
        · simpa using evenMono_X_one_sq k
      exact evenMono_mul k hp hn

/-! ### Degree bookkeeping -/

theorem totalDegree_eq_sup (p : SX k) :
    p.totalDegree = p.support.sup (fun m => Finsupp.degree m) := by
  rw [MvPolynomial.totalDegree_eq]
  congr 1
  funext m
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

theorem degree_le_totalDegree {p : SX k} {m : Fin 2 →₀ ℕ}
    (hm : m ∈ p.support) : Finsupp.degree m ≤ p.totalDegree := by
  rw [totalDegree_eq_sup]
  exact Finset.le_sup hm

/-- An element of `k[x₀,x₁]` whose monomials all have even degree and whose total degree is
at most one is a constant. -/
theorem eq_C_of_evenMono_totalDegree_le_one {p : SX k} (hp : EvenMono k p)
    (h : p.totalDegree ≤ 1) : ∃ c : k, p = C c := by
  have hzero : p.totalDegree = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    rw [totalDegree_eq_sup, Finset.sup_le_iff]
    intro m hm
    obtain ⟨j, hj⟩ := hp m hm
    have h1 : Finsupp.degree m ≤ 1 := le_trans (degree_le_totalDegree (k := k) hm) h
    rw [hj] at h1
    have hj0 : j = 0 := by omega
    rw [hj, hj0]
  exact ⟨p.coeff 0, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero⟩

theorem X_ne_zero (i : Fin 2) : (X i : SX k) ≠ 0 := by
  intro h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h
  simp at hc

theorem totalDegree_st : (X 0 * X 1 : SX k).totalDegree = 2 := by
  rw [totalDegree_mul_of_isDomain (X_ne_zero k 0) (X_ne_zero k 1), MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_X]

theorem st_ne_zero : (X 0 * X 1 : SX k) ≠ 0 := by
  intro h
  have h2 := totalDegree_st k
  rw [h, MvPolynomial.totalDegree_zero] at h2
  omega

/-! ### The three degree-two generators of `S(Y)` -/

theorem s2_mem : (X 0) ^ 2 ∈ SY k := (mem_SY_iff k).mpr ⟨X 0, by simp⟩

theorem st_mem : X 0 * X 1 ∈ SY k := (mem_SY_iff k).mpr ⟨X 1, by simp⟩

theorem t2_mem : (X 1) ^ 2 ∈ SY k := (mem_SY_iff k).mpr ⟨X 2, by simp⟩

theorem evenMono_mem {p : SX k} (hp : p ∈ SY k) : EvenMono k p := by
  obtain ⟨q, rfl⟩ := (mem_SY_iff k).mp hp
  exact evenMono_theta k q

theorem constant_mem (c : k) : (C c : SX k) ∈ SY k := (mem_SY_iff k).mpr ⟨C c, by simp⟩

/-- `s²t² = (st)²` in `S(Y)`. -/
theorem s2_mul_t2 : (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) * ⟨(X 1) ^ 2, t2_mem k⟩ =
    ⟨X 0 * X 1, st_mem k⟩ * ⟨X 0 * X 1, st_mem k⟩ := by
  apply Subtype.ext
  show (X 0) ^ 2 * (X 1) ^ 2 = (X 0 * X 1) * (X 0 * X 1)
  ring

theorem not_dvd_s2 : ¬ (⟨X 0 * X 1, st_mem k⟩ : SY k) ∣ ⟨(X 0) ^ 2, s2_mem k⟩ := by
  rintro ⟨b, hb⟩
  have hb' : (X 0) ^ 2 = (X 0 * X 1) * (b : SX k) := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have h := congrArg (MvPolynomial.eval ![(1 : k), (0 : k)]) hb'
  simp at h

theorem not_dvd_t2 : ¬ (⟨X 0 * X 1, st_mem k⟩ : SY k) ∣ ⟨(X 1) ^ 2, t2_mem k⟩ := by
  rintro ⟨b, hb⟩
  have hb' : (X 1) ^ 2 = (X 0 * X 1) * (b : SX k) := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have h := congrArg (MvPolynomial.eval ![(0 : k), (1 : k)]) hb'
  simp at h

theorem totalDegree_eq_zero_of_isUnit {x : SX k} (hx : IsUnit x) : x.totalDegree = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have h2 : ((u : SX k)) * ((u⁻¹ : (SX k)ˣ) : SX k) = 1 := by simp
  have hu0 : ((u : SX k)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hu'0 : ((u⁻¹ : (SX k)ˣ) : SX k) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact zero_ne_one h2
  have h3 : ((u : SX k)) * ((u⁻¹ : (SX k)ˣ) : SX k) = 1 := by simp
  have h4 := totalDegree_mul_of_isDomain hu0 hu'0
  rw [h3, MvPolynomial.totalDegree_one] at h4
  omega

/-- In `S(Y) = k[s²,st,t²]` every element of total degree two is irreducible: its monomials
all have even degree, so any factor of total degree at most one is a constant. -/
theorem irreducible_of_mem_SY_totalDegree_two {x : SX k} (hx : x ∈ SY k)
    (h2 : x.totalDegree = 2) : Irreducible (⟨x, hx⟩ : SY k) := by
  constructor
  · rintro hunit
    have hxunit : IsUnit x := hunit.map (SY k).subtype
    rw [totalDegree_eq_zero_of_isUnit k hxunit] at h2
    omega
  · intro a b hab
    have hab' : x = (a : SX k) * (b : SX k) := by
      have := congrArg (Subtype.val) hab
      simpa using this
    have ha0 : (a : SX k) ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hab'
      rw [hab'] at h2
      exact absurd h2 (by rw [MvPolynomial.totalDegree_zero]; omega)
    have hb0 : (b : SX k) ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hab'
      rw [hab'] at h2
      exact absurd h2 (by rw [MvPolynomial.totalDegree_zero]; omega)
    have hdeg : (a : SX k).totalDegree + (b : SX k).totalDegree = 2 := by
      rw [← totalDegree_mul_of_isDomain ha0 hb0, ← hab', h2]
    have ha_even : EvenMono k (a : SX k) := evenMono_mem k a.2
    have hb_even : EvenMono k (b : SX k) := evenMono_mem k b.2
    have unit_of_le_one : ∀ x : SY k, (x : SX k) ≠ 0 → EvenMono k (x : SX k) →
        (x : SX k).totalDegree ≤ 1 → IsUnit x := by
      intro y hy0 hyev hle
      obtain ⟨c, hc⟩ := eq_C_of_evenMono_totalDegree_le_one k hyev hle
      refine isUnit_iff_exists_inv.mpr ⟨⟨C c⁻¹, constant_mem k c⁻¹⟩, ?_⟩
      apply Subtype.ext
      show (y : SX k) * C c⁻¹ = 1
      rw [hc]
      have hc0 : c ≠ 0 := by
        intro hc0
        rw [hc, hc0, map_zero] at hy0
        exact hy0 rfl
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    by_cases h1 : (a : SX k).totalDegree ≤ 1
    · exact Or.inl (unit_of_le_one a ha0 ha_even h1)
    · exact Or.inr (unit_of_le_one b hb0 hb_even (by omega))

theorem totalDegree_s2 : ((X 0) ^ 2 : SX k).totalDegree = 2 := by
  rw [pow_two, totalDegree_mul_of_isDomain (X_ne_zero k 0) (X_ne_zero k 0),
    MvPolynomial.totalDegree_X]

theorem totalDegree_t2 : ((X 1) ^ 2 : SX k).totalDegree = 2 := by
  rw [pow_two, totalDegree_mul_of_isDomain (X_ne_zero k 1) (X_ne_zero k 1),
    MvPolynomial.totalDegree_X]

/-- `st ∈ S(Y)` is irreducible. -/
theorem irreducible_st : Irreducible (⟨X 0 * X 1, st_mem k⟩ : SY k) :=
  irreducible_of_mem_SY_totalDegree_two k (st_mem k) (totalDegree_st k)

/-- `s² ∈ S(Y)` is irreducible. -/
theorem irreducible_s2 : Irreducible (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) :=
  irreducible_of_mem_SY_totalDegree_two k (s2_mem k) (totalDegree_s2 k)

/-- `t² ∈ S(Y)` is irreducible. -/
theorem irreducible_t2 : Irreducible (⟨(X 1) ^ 2, t2_mem k⟩ : SY k) :=
  irreducible_of_mem_SY_totalDegree_two k (t2_mem k) (totalDegree_t2 k)

theorem not_dvd_s2_st : ¬ (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ∣ ⟨X 0 * X 1, st_mem k⟩ := by
  rintro ⟨b, hb⟩
  have hb' : (X 0 * X 1 : SX k) = (X 0) ^ 2 * (b : SX k) := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have hc : (X 1 : SX k) = X 0 * (b : SX k) := by
    refine mul_left_cancel₀ (X_ne_zero k 0) ?_
    rw [hb']
    ring
  have h := congrArg (MvPolynomial.eval ![(0 : k), (1 : k)]) hc
  simp at h

theorem not_associated_s2_st :
    ¬ Associated (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ⟨X 0 * X 1, st_mem k⟩ := by
  intro h
  exact not_dvd_s2_st k h.dvd

/-- `S(X) = k[x₀,x₁]` is a unique factorization monoid. -/
theorem isUFD_SX : UniqueFactorizationMonoid (SX k) := inferInstance

theorem not_dvd_t2_st : ¬ (⟨(X 1) ^ 2, t2_mem k⟩ : SY k) ∣ ⟨X 0 * X 1, st_mem k⟩ := by
  rintro ⟨b, hb⟩
  have hb' : (X 0 * X 1 : SX k) = (X 1) ^ 2 * (b : SX k) := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have hc : (X 0 : SX k) = X 1 * (b : SX k) := by
    refine mul_left_cancel₀ (X_ne_zero k 1) ?_
    calc (X 1 : SX k) * X 0 = X 0 * X 1 := by ring
      _ = (X 1) ^ 2 * (b : SX k) := hb'
      _ = X 1 * (X 1 * (b : SX k)) := by ring
  have h := congrArg (MvPolynomial.eval ![(1 : k), (0 : k)]) hc
  simp at h

theorem not_dvd_s2_t2 : ¬ (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ∣ ⟨(X 1) ^ 2, t2_mem k⟩ := by
  rintro ⟨b, hb⟩
  have hb' : ((X 1) ^ 2 : SX k) = (X 0) ^ 2 * (b : SX k) := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have h := congrArg (MvPolynomial.eval ![(0 : k), (1 : k)]) hb'
  simp at h

theorem not_associated_t2_st :
    ¬ Associated (⟨(X 1) ^ 2, t2_mem k⟩ : SY k) ⟨X 0 * X 1, st_mem k⟩ := by
  intro h
  exact not_dvd_t2_st k h.dvd

theorem not_associated_s2_t2 :
    ¬ Associated (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ⟨(X 1) ^ 2, t2_mem k⟩ := by
  intro h
  exact not_dvd_s2_t2 k h.dvd

/-- `s²`, `st`, `t²` are pairwise nonassociate in `S(Y)`, as the natural proof states. -/
theorem pairwise_nonassociated :
    (¬ Associated (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ⟨X 0 * X 1, st_mem k⟩) ∧
      (¬ Associated (⟨(X 1) ^ 2, t2_mem k⟩ : SY k) ⟨X 0 * X 1, st_mem k⟩) ∧
      (¬ Associated (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) ⟨(X 1) ^ 2, t2_mem k⟩) :=
  ⟨not_associated_s2_st k, not_associated_t2_st k, not_associated_s2_t2 k⟩

/-- The natural proof's conclusion: `s²·t² = st·st` in `S(Y)` gives two distinct
factorizations of the same element into irreducibles. -/
theorem two_distinct_factorizations :
    ∃ a b c : SY k, Irreducible a ∧ Irreducible b ∧ Irreducible c ∧
      ¬ Associated a c ∧ a * b = c * c :=
  ⟨⟨(X 0) ^ 2, s2_mem k⟩, ⟨(X 1) ^ 2, t2_mem k⟩, ⟨X 0 * X 1, st_mem k⟩,
    irreducible_s2 k, irreducible_t2 k, irreducible_st k, not_associated_s2_st k,
    s2_mul_t2 k⟩

/-- `st` is not prime in `S(Y)`: it divides `s²t² = (st)²` but neither `s²` nor `t²`. -/
theorem not_prime_st : ¬ Prime (⟨X 0 * X 1, st_mem k⟩ : SY k) := by
  rintro ⟨-, -, hdvd⟩
  have hd : (⟨X 0 * X 1, st_mem k⟩ : SY k) ∣
      (⟨(X 0) ^ 2, s2_mem k⟩ : SY k) * ⟨(X 1) ^ 2, t2_mem k⟩ :=
    ⟨⟨X 0 * X 1, st_mem k⟩, by rw [s2_mul_t2]⟩
  rcases hdvd _ _ hd with h | h
  · exact not_dvd_s2 k h
  · exact not_dvd_t2 k h

/-- `S(Y) = k[s²,st,t²]` is not a unique factorization monoid. -/
theorem not_isUFD_SY : ¬ UniqueFactorizationMonoid (SY k) := by
  intro h
  exact not_prime_st k (h.irreducible_iff_prime.mp (irreducible_st k))

/-- **Hartshorne I.3.9**: `S(X) ≢ S(Y)`.  There is no ring isomorphism between
`S(X) = k[x₀,x₁]` and `S(Y) = k[x₀²,x₀x₁,x₁²]`. -/
theorem no_ringEquiv : ¬ Nonempty (SX k ≃+* SY k) := by
  rintro ⟨e⟩
  set p : SX k := e.symm ⟨X 0 * X 1, st_mem k⟩ with hp
  have hp_map : e p = ⟨X 0 * X 1, st_mem k⟩ := by simp [hp]
  have hst_irr : Irreducible (⟨X 0 * X 1, st_mem k⟩ : SY k) := irreducible_st k
  have hp_irr : Irreducible p := by
    have h : Irreducible (e p) := by
      rw [hp_map]
      exact hst_irr
    exact (MulEquiv.irreducible_iff (f := e.toMulEquiv) (x := p)).mp h
  have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
  have hst_prime : Prime (⟨X 0 * X 1, st_mem k⟩ : SY k) := by
    rw [← hp_map]
    exact (MulEquiv.prime_iff (e := (e : SX k ≃+* SY k)) (p := p)).mpr hp_prime
  exact not_prime_st k hst_prime

/-- **Hartshorne I.3.9, bundled.**  `S(X) = k[x₀,x₁]` is a unique factorization monoid,
`S(Y) = k[x₀²,x₀x₁,x₁²]` is not, and consequently there is no ring isomorphism
`S(X) ≃+* S(Y)`: the homogeneous coordinate ring of a projective variety is not an
invariant of the isomorphism class of the variety. -/
theorem hartshorne_I_3_9 :
    UniqueFactorizationMonoid (SX k) ∧ ¬ UniqueFactorizationMonoid (SY k) ∧
      ¬ Nonempty (SX k ≃+* SY k) :=
  ⟨isUFD_SX k, not_isUFD_SY k, no_ringEquiv k⟩

end Hartshorne77.Ex_I_3_9
