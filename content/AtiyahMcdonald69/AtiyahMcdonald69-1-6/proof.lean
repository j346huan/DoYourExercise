/-
Atiyah & Macdonald, *Introduction to Commutative Algebra*, Chapter 1, Exercise 6.

**Statement (book).** A ring `A` is such that every ideal not contained in the nilradical
contains a non-zero idempotent (that is, an element `e` such that `e ^ 2 = e ≠ 0`).
Prove that the nilradical and the Jacobson radical of `A` are equal.

In Mathlib terms, for a commutative ring `A`:
* the nilradical is `nilradical A = (⊥ : Ideal A).radical`, the ideal of nilpotent elements;
* the Jacobson radical is `Ring.jacobson A = (⊥ : Ideal A).jacobson`, the intersection of all
  maximal ideals.

The solution follows the book's hint, a lemma about idempotents: an idempotent which is a unit
is `1`, and an idempotent which lies in the Jacobson radical is `0`.  Since the nilradical is
always contained in the Jacobson radical, it suffices to show that the Jacobson radical is
contained in the nilradical; if not, the hypothesis of the exercise applied to the Jacobson
radical produces a nonzero idempotent `e` inside it, which must be `0`, a contradiction.

We also record the Boolean-ring consequence: in a Boolean ring (`x * x = x` for all `x`) both
the nilradical and the Jacobson radical vanish, so the two radicals are equal with both sides
equal to `(0)`.
-/
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Ring.BooleanRing

set_option autoImplicit false

namespace AtiyahMcdonald69.Ex_1_6

variable {A : Type*} [CommRing A]

/-! ### Idempotents (the hint in the book's solution) -/

/-- An idempotent element of a ring which happens to be a unit must be `1`. -/
theorem eq_one_of_mul_self_eq_self_of_isUnit {e : A} (hee : e * e = e) (hu : IsUnit e) :
    e = 1 :=
  hu.mul_left_cancel (by rw [hee, mul_one])

/-- An idempotent element which lies in the Jacobson radical is zero. -/
theorem eq_zero_of_mul_self_eq_self_of_mem_jacobson {e : A} (hee : e * e = e)
    (he : e ∈ (⊥ : Ideal A).jacobson) : e = 0 := by
  -- `e` in the Jacobson radical implies `1 - e` is a unit (Proposition 1.9 of the book).
  have hu : IsUnit (1 - e) := by
    have h := (Ideal.mem_jacobson_bot (R := A)).1 he (-1)
    have heq : e * -1 + 1 = 1 - e := by ring
    rwa [heq] at h
  -- `1 - e` is again idempotent, so as a unit it must be `1`, whence `e = 0`.
  have hidem : (1 - e) * (1 - e) = 1 - e := by
    have h : (1 - e) * (1 - e) = 1 - e - (e - e * e) := by ring
    rw [h, hee, sub_self, sub_zero]
  have h1 : 1 - e = 1 := eq_one_of_mul_self_eq_self_of_isUnit hidem hu
  have h0 : -e = 0 := by
    have h : 1 - e - 1 = -e := by ring
    rw [← h, h1, sub_self]
  exact neg_eq_zero.1 h0

/-! ### Exercise 1.6 -/

/-- **Exercise 1.6.** If every ideal of `A` which is not contained in the nilradical contains a
nonzero idempotent, then the nilradical and the Jacobson radical of `A` are equal. -/
theorem nilradical_eq_jacobson
    (h : ∀ I : Ideal A, ¬ I ≤ (⊥ : Ideal A).radical → ∃ e : A, e ∈ I ∧ e ≠ 0 ∧ e * e = e) :
    (⊥ : Ideal A).radical = (⊥ : Ideal A).jacobson := by
  -- The nilradical is always contained in the Jacobson radical.
  refine le_antisymm Ideal.radical_le_jacobson ?_
  -- Suppose the Jacobson radical is not contained in the nilradical.
  by_contra hlt
  -- Then, by hypothesis, it contains a nonzero idempotent.
  obtain ⟨e, he, hne, hee⟩ := h _ hlt
  -- But an idempotent in the Jacobson radical vanishes, a contradiction.
  exact hne (eq_zero_of_mul_self_eq_self_of_mem_jacobson hee he)

/-- **Exercise 1.6**, stated with the notations `nilradical` and `Ring.jacobson` for the two
radicals. -/
theorem nilradical_eq_ringJacobson
    (h : ∀ I : Ideal A, ¬ I ≤ nilradical A → ∃ e : A, e ∈ I ∧ e ≠ 0 ∧ e * e = e) :
    nilradical A = Ring.jacobson A := by
  have h' : (⊥ : Ideal A).radical = (⊥ : Ideal A).jacobson := nilradical_eq_jacobson h
  rw [nilradical, ← Ideal.jacobson_bot]
  exact h'

/-! ### Boolean rings: nilradical = Jacobson radical = (0) -/

/-- In a ring in which every element is idempotent, there is no nonzero nilpotent element:
the nilradical vanishes. -/
theorem radical_bot_eq_bot_of_mul_self (h : ∀ x : A, x * x = x) :
    (⊥ : Ideal A).radical = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [Ideal.mem_bot] at hn ⊢
  exact IsIdempotentElem.eq_zero_of_isNilpotent (h x) ⟨n, hn⟩

/-- In a ring in which every element is idempotent, every ideal which is not contained in the
nilradical contains a nonzero idempotent; that is, the hypothesis of Exercise 1.6 holds. -/
theorem exists_idempotent_of_not_le_radical_of_mul_self (h : ∀ x : A, x * x = x)
    (I : Ideal A) (hI : ¬ I ≤ (⊥ : Ideal A).radical) :
    ∃ e : A, e ∈ I ∧ e ≠ 0 ∧ e * e = e := by
  have hnil : (⊥ : Ideal A).radical = ⊥ := radical_bot_eq_bot_of_mul_self h
  have hex : ∃ e ∈ I, e ≠ 0 := by
    by_contra hcon
    apply hI
    rw [hnil]
    intro x hx
    by_contra hx0
    exact hcon ⟨x, hx, hx0⟩
  obtain ⟨e, heI, he0⟩ := hex
  exact ⟨e, heI, he0, h e⟩

/-- In a Boolean ring the nilradical and the Jacobson radical both vanish. -/
theorem nilradical_eq_jacobson_eq_bot_of_mul_self (h : ∀ x : A, x * x = x) :
    (⊥ : Ideal A).radical = ⊥ ∧ (⊥ : Ideal A).jacobson = ⊥ := by
  have hnil : (⊥ : Ideal A).radical = ⊥ := radical_bot_eq_bot_of_mul_self h
  have hmain : (⊥ : Ideal A).radical = (⊥ : Ideal A).jacobson :=
    nilradical_eq_jacobson (exists_idempotent_of_not_le_radical_of_mul_self h)
  exact ⟨hnil, by rw [← hmain, hnil]⟩

/-- Exercise 1.6 for Mathlib's `BooleanRing` class: in a Boolean ring the nilradical and the
Jacobson radical coincide, and both are the zero ideal. -/
theorem nilradical_eq_jacobson_eq_bot_of_booleanRing (A : Type*) [BooleanRing A] :
    (⊥ : Ideal A).radical = ⊥ ∧ (⊥ : Ideal A).jacobson = ⊥ :=
  nilradical_eq_jacobson_eq_bot_of_mul_self (fun x => BooleanRing.mul_self x)

/-- In a Boolean ring, written with the convention `x ^ 2 = x`, both radicals vanish. -/
theorem nilradical_eq_jacobson_eq_bot_of_pow_two (h : ∀ x : A, x ^ 2 = x) :
    (⊥ : Ideal A).radical = ⊥ ∧ (⊥ : Ideal A).jacobson = ⊥ :=
  nilradical_eq_jacobson_eq_bot_of_mul_self (fun x => by simpa [pow_two] using h x)

/-! ### Sanity checks: the degenerate zero ring and a nontrivial Boolean ring -/

/-- The zero ring is Boolean, and both radicals are `(0)` there (this is the degenerate case in
which `(0)` is the whole ring). -/
example (A : Type*) [CommRing A] [Subsingleton A] :
    (⊥ : Ideal A).radical = ⊥ ∧ (⊥ : Ideal A).jacobson = ⊥ :=
  nilradical_eq_jacobson_eq_bot_of_mul_self (fun x => Subsingleton.elim (x * x) x)

/-- The two-element Boolean ring, a nontrivial example. -/
example : (⊥ : Ideal Bool).radical = ⊥ ∧ (⊥ : Ideal Bool).jacobson = ⊥ :=
  nilradical_eq_jacobson_eq_bot_of_booleanRing Bool

end AtiyahMcdonald69.Ex_1_6

#print axioms AtiyahMcdonald69.Ex_1_6.eq_one_of_mul_self_eq_self_of_isUnit
#print axioms AtiyahMcdonald69.Ex_1_6.eq_zero_of_mul_self_eq_self_of_mem_jacobson
#print axioms AtiyahMcdonald69.Ex_1_6.nilradical_eq_jacobson
#print axioms AtiyahMcdonald69.Ex_1_6.nilradical_eq_ringJacobson
#print axioms AtiyahMcdonald69.Ex_1_6.radical_bot_eq_bot_of_mul_self
#print axioms AtiyahMcdonald69.Ex_1_6.exists_idempotent_of_not_le_radical_of_mul_self
#print axioms AtiyahMcdonald69.Ex_1_6.nilradical_eq_jacobson_eq_bot_of_mul_self
#print axioms AtiyahMcdonald69.Ex_1_6.nilradical_eq_jacobson_eq_bot_of_pow_two
#print axioms AtiyahMcdonald69.Ex_1_6.nilradical_eq_jacobson_eq_bot_of_booleanRing
