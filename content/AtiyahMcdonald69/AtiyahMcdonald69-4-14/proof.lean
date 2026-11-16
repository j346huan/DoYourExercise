/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 4, Exercise 14

Book statement (Atiyah–Macdonald, Ch. 4, Exercise 14):

> Let `a` be a decomposable ideal in a ring `A` and let `p` be a maximal element of the
> set of ideals `(a : x)`, where `x ∈ A` and `x ∉ a`. Show that `p` is a prime ideal
> belonging to `a`.

Formalization plan:

* `colonFamily a` is the family `{(a : x) | x ∉ a}` of the statement.
* `IsMaxColon a p` says that `p` is a maximal element of that family.
* `isPrime_of_isMaxColon` : such a `p` is prime.
* `radical_colon_of_isMaxColon` : such a `p` is the radical of a colon ideal `(a : x)`.
* `mem_associatedPrimes_of_isMaxColon` : such a `p` is an associated prime of `A ⧸ a`,
  expressed Mathlib-style as an associated prime of the submodule `a ≤ A`.
* `solution` : the book statement, with "belonging to `a`" spelled out both as membership
  in the associated primes and as being the radical of a member of a minimal primary
  decomposition (Atiyah–Macdonald, Theorem 4.5 /
  `Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`).

Note on the hypothesis "decomposable": the argument for primality and for the radical
identity proceeds by maximality alone and hence does not use decomposability at all; we
state the general form and then derive the book's statement from it.  Decomposability is
only what makes "belonging to `a`" agree with "occurring as `r(qᵢ)` in a primary
decomposition", which is exactly the content of Theorem 4.5 used at the end.
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_4_14

open Ideal

variable {A : Type*} [CommRing A]

/-- The family of ideals `(a : x)` with `x ∉ a`, among which `p` is maximal in
Atiyah–Macdonald, Chapter 4, Exercise 14. -/
def colonFamily (a : Ideal A) : Set (Ideal A) :=
  {q | ∃ x : A, x ∉ a ∧ q = a.colon {x}}

/-- `p` is a maximal element of the family `{(a : x) | x ∉ a}`. -/
def IsMaxColon (a p : Ideal A) : Prop :=
  p ∈ colonFamily a ∧ ∀ q ∈ colonFamily a, p ≤ q → q = p

variable {a p : Ideal A}

/-- Membership in a colon ideal `(a : x)`, unwound multiplicatively. -/
theorem mem_colon_singleton_mul {b x : A} : b ∈ a.colon {x} ↔ b * x ∈ a := by
  rw [Submodule.mem_colon_singleton, smul_eq_mul]

/-- Key monotonicity: `(a : x) ≤ (a : w * x)`. -/
theorem colon_le_colon_mul_left {x w : A} : a.colon {x} ≤ a.colon {w * x} := by
  intro b hb
  rw [mem_colon_singleton_mul] at hb ⊢
  rw [show b * (w * x) = w * (b * x) by ring]
  exact a.mul_mem_left w hb

/-- Atiyah–Macdonald, Chapter 4, Exercise 14, primality part: a maximal element of the
family `{(a : x) | x ∉ a}` is a prime ideal.  (Decomposability of `a` is not needed.) -/
theorem isPrime_of_isMaxColon (h : IsMaxColon a p) : p.IsPrime := by
  obtain ⟨⟨x, hx, hpx⟩, hmax⟩ := h
  subst hpx
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- `(a : x) ≠ ⊤` because `x ∉ a`
    intro htop
    have h1 : (1 : A) ∈ a.colon {x} := by rw [htop]; exact Submodule.mem_top
    rw [mem_colon_singleton_mul] at h1
    exact hx (by simpa using h1)
  · intro u v huv
    by_cases hv : v ∈ a.colon {x}
    · exact Or.inr hv
    refine Or.inl ?_
    have hvx : v * x ∉ a := by rwa [mem_colon_singleton_mul] at hv
    have hle : a.colon {x} ≤ a.colon {v * x} := colon_le_colon_mul_left
    have heq : a.colon {v * x} = a.colon {x} := hmax _ ⟨v * x, hvx, rfl⟩ hle
    have hux : u ∈ a.colon {v * x} := by
      rw [mem_colon_singleton_mul] at huv ⊢
      rw [show u * (v * x) = (u * v) * x by ring]
      exact huv
    rwa [heq] at hux

/-- A maximal element of the family `{(a : x) | x ∉ a}` contains `a`. -/
theorem le_of_isMaxColon (h : IsMaxColon a p) : a ≤ p := by
  obtain ⟨⟨x, -, hpx⟩, -⟩ := h
  rw [hpx]
  exact Ideal.le_colon

/-- Atiyah–Macdonald, Chapter 4, Exercise 14, radical part: a maximal element `p` of the
family `{(a : x) | x ∉ a}` is the radical of the colon ideal `(a : x)` for any `x` with
`p = (a : x)` and `x ∉ a`.  (Decomposability of `a` is not needed.) -/
theorem radical_colon_of_isMaxColon (h : IsMaxColon a p) {x : A} (hx : x ∉ a)
    (hpx : p = a.colon {x}) : (a.colon {x}).radical = p := by
  have hmax := h.2
  subst hpx
  refine le_antisymm ?_ Ideal.le_radical
  intro w hw
  rw [Ideal.mem_radical_iff] at hw
  obtain ⟨n, hn⟩ := hw
  have hn' : w ^ n * x ∈ a := by rwa [mem_colon_singleton_mul] at hn
  clear hn
  have key : ∀ n : ℕ, w ^ n * x ∈ a → w ∈ a.colon {x} := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      match n, hn with
      | 0, hn => exact absurd (by simpa using hn) hx
      | m + 1, hn =>
        by_cases hm : w ^ m * x ∈ a
        · exact ih m (Nat.lt_succ_self m) hm
        · have hle : a.colon {x} ≤ a.colon {w ^ m * x} := colon_le_colon_mul_left
          have heq : a.colon {w ^ m * x} = a.colon {x} :=
            hmax _ ⟨w ^ m * x, hm, rfl⟩ hle
          have hmem : w ∈ a.colon {w ^ m * x} := by
            rw [mem_colon_singleton_mul]
            rw [show w * (w ^ m * x) = w ^ (m + 1) * x by rw [pow_succ]; ring]
            exact hn
          rwa [heq] at hmem
  exact key n hn'

/-- Atiyah–Macdonald, Chapter 4, Exercise 14: a maximal element of the family
`{(a : x) | x ∉ a}` is an associated prime of `A ⧸ a`, here expressed as an associated
prime of the submodule `a ≤ A` (Mathlib's `Submodule.IsAssociatedPrime`, whose radical
convention is exactly the one matching primary decomposition, see Theorem 4.5). -/
theorem mem_associatedPrimes_of_isMaxColon (h : IsMaxColon a p) :
    p ∈ (a : Submodule A A).associatedPrimes := by
  obtain ⟨⟨x, hx, hpx⟩, hmax⟩ := h
  exact ⟨isPrime_of_isMaxColon ⟨⟨x, hx, hpx⟩, hmax⟩, x,
    (radical_colon_of_isMaxColon ⟨⟨x, hx, hpx⟩, hmax⟩ hx hpx).symm⟩


/-- The Atiyah–Macdonald (4.5) characterization of the primes belonging to `a`: `p` is
prime and `p = r(a : x)` for some `x ∉ a`. -/
theorem isPrime_and_eq_radical_colon_of_isMaxColon (h : IsMaxColon a p) :
    p.IsPrime ∧ ∃ x : A, x ∉ a ∧ p = (a.colon {x}).radical := by
  obtain ⟨⟨x, hx, hpx⟩, hmax⟩ := h
  exact ⟨isPrime_of_isMaxColon ⟨⟨x, hx, hpx⟩, hmax⟩, x, hx,
    (radical_colon_of_isMaxColon ⟨⟨x, hx, hpx⟩, hmax⟩ hx hpx).symm⟩

/-- `a` is *decomposable* in the sense of Atiyah–Macdonald, Chapter 4: `a` is a finite
intersection of primary ideals (not necessarily a minimal decomposition). -/
def IsDecomposable (a : Ideal A) : Prop :=
  ∃ s : Finset (Ideal A), s.inf id = a ∧ ∀ q ∈ s, q.IsPrimary

/-- Any decomposable ideal admits a minimal primary decomposition. -/
theorem exists_isMinimalPrimaryDecomposition_of_isDecomposable {a : Ideal A}
    (h : IsDecomposable a) :
    ∃ t : Finset (Ideal A), Submodule.IsMinimalPrimaryDecomposition (a : Submodule A A) t := by
  obtain ⟨s, hs, hsp⟩ := h
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs hsp
  exact ⟨t, h1, h2, h3, h4⟩

/-- The annihilator of the class of `x` in `A ⧸ a` is the colon ideal `(a : x)`. -/
theorem colon_bot_quotient_mk (x : A) :
    (⊥ : Submodule A (A ⧸ a)).colon {Ideal.Quotient.mk a x} = a.colon {x} := by
  ext y
  rw [Submodule.mem_colon_singleton, mem_colon_singleton_mul]
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Submodule.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem]

/-- "Associated primes of `A ⧸ a`" and "associated primes of the submodule `a ≤ A`"
agree; this is the module-theoretic form of the set of primes belonging to `a`. -/
theorem associatedPrimes_quotient (a : Ideal A) :
    associatedPrimes A (A ⧸ a) = (a : Submodule A A).associatedPrimes := by
  ext p
  constructor
  · rintro ⟨hp, y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨hp, x, by rw [hy, colon_bot_quotient_mk]⟩
  · rintro ⟨hp, x, hx⟩
    exact ⟨hp, Ideal.Quotient.mk a x, by rw [hx, colon_bot_quotient_mk]⟩

/-- Atiyah–Macdonald, Chapter 4, Exercise 14, "belonging" part in the form of a primary
decomposition: if `p` is maximal among the `(a : x)` with `x ∉ a`, then `p` occurs as the
radical of a member of *every* minimal primary decomposition of `a`. -/
theorem exists_mem_image_radical_colon_of_isMaxColon (h : IsMaxColon a p)
    (t : Finset (Ideal A)) (ht : Submodule.IsMinimalPrimaryDecomposition (a : Submodule A A) t) :
    ∃ q ∈ t, p = (q.colon Set.univ).radical := by
  have hmem : p ∈ (a : Submodule A A).associatedPrimes := mem_associatedPrimes_of_isMaxColon h
  rw [← Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes ht] at hmem
  obtain ⟨q, hq, hqp⟩ := hmem
  exact ⟨q, hq, hqp.symm⟩

/-- **Atiyah–Macdonald, Chapter 4, Exercise 14.**  Let `a` be a decomposable ideal in a
ring `A` and let `p` be a maximal element of the set of ideals `(a : x)` with `x ∉ a`.
Then `p` is a prime ideal belonging to `a`.

"Belonging to `a`" is stated in both equivalent forms: `p` is an associated prime of
`A ⧸ a`, and `p` is the radical of a member of some (= every) minimal primary
decomposition of `a` (Atiyah–Macdonald, Theorem 4.5). -/
theorem solution (ha : IsDecomposable a) (h : IsMaxColon a p) :
    p.IsPrime ∧ p ∈ associatedPrimes A (A ⧸ a) ∧
      ∃ t : Finset (Ideal A), Submodule.IsMinimalPrimaryDecomposition (a : Submodule A A) t ∧
        ∃ q ∈ t, p = (q.colon Set.univ).radical := by
  obtain ⟨t, ht⟩ := exists_isMinimalPrimaryDecomposition_of_isDecomposable ha
  exact ⟨isPrime_of_isMaxColon h, by rw [associatedPrimes_quotient]; exact mem_associatedPrimes_of_isMaxColon h,
    t, ht, exists_mem_image_radical_colon_of_isMaxColon h t ht⟩

section SanityCheck

/-- `(p : x) = p` for a prime ideal `p` and `x ∉ p`. -/
theorem colon_singleton_eq_self_of_isPrime (hp : p.IsPrime) {x : A} (hx : x ∉ p) :
    p.colon {x} = p := by
  refine le_antisymm ?_ Ideal.le_colon
  intro b hb
  rw [mem_colon_singleton_mul] at hb
  exact (hp.mem_or_mem hb).resolve_right hx

/-- A prime ideal is a maximal element of its own colon family `{(p : x) | x ∉ p}`.
This shows that the hypotheses of Exercise 14 are satisfiable. -/
theorem isMaxColon_self_of_isPrime (hp : p.IsPrime) : IsMaxColon p p := by
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hp.ne_top)
  refine ⟨⟨x, hx, (colon_singleton_eq_self_of_isPrime hp hx).symm⟩, ?_⟩
  rintro q ⟨y, hy, rfl⟩ -
  exact colon_singleton_eq_self_of_isPrime hp hy

/-- A prime ideal is decomposable (it is primary). -/
theorem isDecomposable_of_isPrime (hp : p.IsPrime) : IsDecomposable p :=
  ⟨{p}, by simp, by simpa using hp.isPrimary⟩

/-- Concrete non-vacuity check for Exercise 14: for a prime ideal `p`, the conclusion of
the exercise holds, i.e. `p ∈ Ass(A ⧸ p)`. -/
theorem mem_associatedPrimes_quotient_self_of_isPrime (hp : p.IsPrime) :
    p ∈ associatedPrimes A (A ⧸ p) :=
  (solution (isDecomposable_of_isPrime hp) (isMaxColon_self_of_isPrime hp)).2.1

end SanityCheck

section Counterexample

/-- The hypothesis `x ∉ a` in Exercise 14 is essential.  If it is dropped, then `x = 0`
is allowed, `(a : 0) = ⊤` is a maximal element of the enlarged family, and `⊤` is not a
prime ideal.  So the statement without the hypothesis is false in every nontrivial ring. -/
theorem top_colon_not_isPrime [Nontrivial A] (a : Ideal A) :
    a.colon {0} = ⊤ ∧ ¬ (a.colon {0}).IsPrime := by
  refine ⟨a.colon_singleton_zero, ?_⟩
  rw [a.colon_singleton_zero]
  exact fun h => h.ne_top rfl

/-- The analogue of Exercise 14 without the hypothesis `x ∉ a` is **false**: in any
nontrivial ring, `⊤ = (a : 0)` is a maximal element of the enlarged family
`{(a : x) | x ∈ A}` but is not a prime ideal.  (E.g. in `ℤ` with `a = (4)`, `((4) : 0) = ⊤`
is the unique maximal element of the enlarged family.) -/
theorem not_forall_isPrime_dropping_hypothesis [Nontrivial A] (a : Ideal A) :
    ¬ ∀ p : Ideal A, (∃ x : A, p = a.colon {x}) →
      (∀ q : Ideal A, (∃ x : A, q = a.colon {x}) → p ≤ q → q = p) → p.IsPrime := by
  intro H
  have hmem : ∃ x : A, (⊤ : Ideal A) = a.colon {x} := ⟨0, (a.colon_singleton_zero).symm⟩
  have hmax : ∀ q : Ideal A, (∃ x : A, q = a.colon {x}) → ⊤ ≤ q → q = ⊤ :=
    fun q _ hq => top_le_iff.mp hq
  exact (H ⊤ hmem hmax).ne_top rfl

end Counterexample

end AtiyahMcdonald69.Ex_4_14

#print axioms AtiyahMcdonald69.Ex_4_14.le_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.isPrime_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.radical_colon_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.mem_associatedPrimes_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.isPrime_and_eq_radical_colon_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.exists_mem_image_radical_colon_of_isMaxColon
#print axioms AtiyahMcdonald69.Ex_4_14.top_colon_not_isPrime
#print axioms AtiyahMcdonald69.Ex_4_14.not_forall_isPrime_dropping_hypothesis
#print axioms AtiyahMcdonald69.Ex_4_14.isMaxColon_self_of_isPrime
#print axioms AtiyahMcdonald69.Ex_4_14.mem_associatedPrimes_quotient_self_of_isPrime
#print axioms AtiyahMcdonald69.Ex_4_14.solution
