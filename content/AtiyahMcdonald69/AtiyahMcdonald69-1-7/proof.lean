import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

/-!
# Atiyah–Macdonald (1969), Chapter 1, Exercise 7

**Statement** (A–M, Chapter 1, Exercise 7). Let `A` be a commutative ring in which every
element `x` satisfies `x ^ n = x` for some integer `n > 1` depending on `x`. Then every prime
ideal of `A` is maximal.

**Natural proof.** If `p` is a prime ideal, then `A ⧸ p` is an integral domain satisfying the
same condition: the image of `x` satisfies `y ^ n = y` for the exponent belonging to `x`. For a
nonzero element `y` of that domain, `y * (y ^ (n - 1) - 1) = y ^ n - y = 0`, hence
`y ^ (n - 1) = 1` and `y` is a unit. Thus `A ⧸ p` is a field, and `p` is maximal.

**Forms of the hypothesis.** The book's exponent `n > 1` depends on the element `x`; this is
the statement `solution` below. The stronger *fixed-exponent* hypothesis, where one `n > 1`
works for every element at once, is also recorded (`solution_fixed`); it is an immediate
special case of the book's form. The bound `1 < n` is essential (`exponent_one_not_sufficient`).

**Degenerate zero ring.** A–M require a prime ideal to be proper (`p ≠ (1)`), and Mathlib's
`Ideal.IsPrime` carries the same requirement, so a subsingleton ring has no prime ideals at
all and the conclusion is vacuous there; this is checked in `zero_ring_case`.
-/

namespace AtiyahMcdonald69.Ex_1_7

variable {A : Type*} [CommRing A]

/-- The key step of the natural proof, stated inside `A`: if `p` is prime, `x ∉ p` and
`x ^ n = x` with `n > 1`, then `x ^ (n - 1) - 1 ∈ p`. -/
theorem pow_sub_one_mem_of_isPrime {p : Ideal A} (hp : p.IsPrime) {x : A} {n : ℕ}
    (hn : 1 < n) (hpow : x ^ n = x) (hx : x ∉ p) : x ^ (n - 1) - 1 ∈ p := by
  have hprod : x * (x ^ (n - 1) - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ' x (n - 1), Nat.sub_add_cancel (le_of_lt hn), hpow,
      sub_self]
  rcases hp.mem_or_mem (hprod ▸ p.zero_mem) with h | h
  · exact absurd h hx
  · exact h

/-- In a domain, a nonzero `x` with `x ^ n = x` and `n > 1` is a unit: `x ^ (n - 1) = 1`.
This is the statement that makes the domain `A ⧸ p` a field. -/
theorem isUnit_of_pow_eq_self [IsDomain A] {x : A} {n : ℕ} (hn : 1 < n) (hpow : x ^ n = x)
    (hx : x ≠ 0) : IsUnit x := by
  have hprod : x * (x ^ (n - 1) - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ' x (n - 1), Nat.sub_add_cancel (le_of_lt hn), hpow,
      sub_self]
  have hx1 : x ^ (n - 1) = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hx
    · exact sub_eq_zero.mp h
  refine IsUnit.of_mul_eq_one (x ^ (n - 2)) ?_
  rw [← pow_succ' x (n - 2)]
  have hsub : n - 2 + 1 = n - 1 := by omega
  rw [hsub, hx1]

/-- A domain in which every element satisfies `x ^ n = x` for some `n > 1` (depending on `x`)
is a field. This is the heart of the natural proof, applied to `A ⧸ p`. -/
theorem isField_of_forall_exists_pow_eq_self [IsDomain A]
    (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x) : IsField A where
  exists_pair_ne := exists_pair_ne A
  mul_comm := fun x y => mul_comm x y
  mul_inv_cancel := by
    intro a ha
    obtain ⟨n, hn, hpow⟩ := h a
    obtain ⟨u, hu⟩ := isUnit_of_pow_eq_self hn hpow ha
    exact ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv⟩

/-- The hypothesis of Exercise 1.7 passes to every quotient ring. -/
theorem forall_exists_pow_eq_self_quotient (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x)
    (I : Ideal A) : ∀ y : A ⧸ I, ∃ n : ℕ, 1 < n ∧ y ^ n = y := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, hn, hpow⟩ := h x
  exact ⟨n, hn, by rw [← map_pow, hpow]⟩

/-- The quotient of `A` by a prime ideal is a field, which is the form in which the natural
proof uses the hypothesis. -/
theorem isField_quotient_of_isPrime (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x)
    (p : Ideal A) (hp : p.IsPrime) : IsField (A ⧸ p) :=
  @isField_of_forall_exists_pow_eq_self (A ⧸ p) _ ((Ideal.Quotient.isDomain_iff_prime p).mpr hp)
    (forall_exists_pow_eq_self_quotient h p)

/-- **Exercise 1.7**, book form: the exponent may depend on the element.

If every `x : A` satisfies `x ^ n = x` for some `n > 1` depending on `x`, then every prime
ideal of `A` is maximal. -/
theorem isMaximal_of_isPrime (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x)
    (p : Ideal A) (hp : p.IsPrime) : p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField p (isField_quotient_of_isPrime h p hp)

/-- Direct proof of Exercise 1.7 inside `A`, without passing to the quotient: if `x ∉ p` then
`x ^ (n - 1) - 1 ∈ p` by primality, so any ideal containing `p` and `x` contains
`1 = x ^ (n - 1) - (x ^ (n - 1) - 1)`. -/
theorem isMaximal_of_isPrime_direct (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x)
    (p : Ideal A) (hp : p.IsPrime) : p.IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨hp.one_notMem, ?_⟩
  intro J x hpJ hx hxJ
  obtain ⟨n, hn, hpow⟩ := h x
  have hmem : x ^ (n - 1) - 1 ∈ p := pow_sub_one_mem_of_isPrime hp hn hpow hx
  have hone : (1 : A) = x ^ (n - 1) - (x ^ (n - 1) - 1) := by ring
  rw [hone]
  exact J.sub_mem (J.pow_mem_of_mem hxJ (n - 1) (by omega)) (hpJ hmem)

/-- **Exercise 1.7**, fixed-exponent variant: a stronger hypothesis, in which a single `n > 1`
works for every element, gives the same conclusion. This is a special case of the book form. -/
theorem isMaximal_of_isPrime_of_forall_pow_eq_self (n : ℕ) (hn : 1 < n)
    (h : ∀ x : A, x ^ n = x) (p : Ideal A) (hp : p.IsPrime) : p.IsMaximal :=
  isMaximal_of_isPrime (fun x => ⟨n, hn, h x⟩) p hp

/-- A subsingleton ring has no prime ideals: this is the properness requirement on prime
ideals, common to A–M (`p ≠ (1)`) and to Mathlib's `Ideal.IsPrime`. -/
theorem not_isPrime_of_subsingleton [Subsingleton A] (p : Ideal A) : ¬ p.IsPrime := by
  intro hp
  refine hp.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)
  rw [Subsingleton.elim (1 : A) 0]
  exact p.zero_mem

/-- The zero ring satisfies the hypothesis of Exercise 1.7 with the fixed exponent `2`, and has
no prime ideals, so the conclusion is vacuous there. -/
theorem zero_ring_case :
    (∀ x : ZMod 1, x ^ 2 = x) ∧ ∀ p : Ideal (ZMod 1), ¬ p.IsPrime :=
  ⟨fun _ => Subsingleton.elim _ _, fun p => not_isPrime_of_subsingleton p⟩

/-- **Exercise 1.7**, exactly in the book's form: every element has its own exponent `n > 1`. -/
theorem solution (A : Type*) [CommRing A] (hA : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x) :
    ∀ p : Ideal A, p.IsPrime → p.IsMaximal :=
  fun p hp => isMaximal_of_isPrime hA p hp

/-- **Exercise 1.7**, fixed-exponent form: one exponent `n > 1` for all elements. -/
theorem solution_fixed (A : Type*) [CommRing A] (n : ℕ) (hn : 1 < n)
    (hA : ∀ x : A, x ^ n = x) : ∀ p : Ideal A, p.IsPrime → p.IsMaximal :=
  fun p hp => isMaximal_of_isPrime_of_forall_pow_eq_self n hn hA p hp

/-- **Exercise 1.7**, fixed-exponent form with the exponent existentially quantified. -/
theorem solution_fixed_exists (A : Type*) [CommRing A]
    (hA : ∃ n : ℕ, 1 < n ∧ ∀ x : A, x ^ n = x) :
    ∀ p : Ideal A, p.IsPrime → p.IsMaximal := by
  obtain ⟨n, hn, hf⟩ := hA
  exact solution_fixed A n hn hf

/-- Exercise 1.7 with both forms of the hypothesis displayed together. -/
theorem solution_both (A : Type*) [CommRing A]
    (hA : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x) :
    (∀ p : Ideal A, p.IsPrime → p.IsMaximal) ∧
      ∀ (n : ℕ), 1 < n → (∀ x : A, x ^ n = x) → ∀ p : Ideal A, p.IsPrime → p.IsMaximal :=
  ⟨solution A hA, fun n hn hf p hp => solution_fixed A n hn hf p hp⟩

end AtiyahMcdonald69.Ex_1_7

namespace AtiyahMcdonald69.Ex_1_7

/-- The hypothesis `1 < n` cannot be dropped: every element of `ℤ` satisfies `x ^ 1 = x`, but
the zero ideal of `ℤ` is prime and not maximal. -/
theorem exponent_one_not_sufficient :
    (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal ∧ ∀ x : ℤ, x ^ 1 = x := by
  refine ⟨inferInstance, ?_, fun x => pow_one x⟩
  intro hmax
  have hmem : (1 : ℤ) ∈ Ideal.span ({2} : Set ℤ) :=
    (Ideal.isMaximal_iff.mp hmax).2 (Ideal.span {2}) 2 bot_le (by simp)
      (Ideal.mem_span_singleton_self 2)
  rw [Ideal.mem_span_singleton] at hmem
  omega

/-- A non-Boolean example of the fixed-exponent hypothesis: in `ZMod 6` every element
satisfies `x ^ 3 = x`, so all its prime ideals are maximal by `solution_fixed`. -/
theorem zmod_six_example (p : Ideal (ZMod 6)) (hp : p.IsPrime) : p.IsMaximal :=
  solution_fixed (ZMod 6) 3 (by norm_num) (by decide) p hp

end AtiyahMcdonald69.Ex_1_7

#print axioms AtiyahMcdonald69.Ex_1_7.pow_sub_one_mem_of_isPrime
#print axioms AtiyahMcdonald69.Ex_1_7.isUnit_of_pow_eq_self
#print axioms AtiyahMcdonald69.Ex_1_7.isField_of_forall_exists_pow_eq_self
#print axioms AtiyahMcdonald69.Ex_1_7.forall_exists_pow_eq_self_quotient
#print axioms AtiyahMcdonald69.Ex_1_7.isField_quotient_of_isPrime
#print axioms AtiyahMcdonald69.Ex_1_7.isMaximal_of_isPrime
#print axioms AtiyahMcdonald69.Ex_1_7.isMaximal_of_isPrime_direct
#print axioms AtiyahMcdonald69.Ex_1_7.isMaximal_of_isPrime_of_forall_pow_eq_self
#print axioms AtiyahMcdonald69.Ex_1_7.not_isPrime_of_subsingleton
#print axioms AtiyahMcdonald69.Ex_1_7.zero_ring_case
#print axioms AtiyahMcdonald69.Ex_1_7.solution
#print axioms AtiyahMcdonald69.Ex_1_7.solution_fixed
#print axioms AtiyahMcdonald69.Ex_1_7.solution_fixed_exists
#print axioms AtiyahMcdonald69.Ex_1_7.solution_both
#print axioms AtiyahMcdonald69.Ex_1_7.exponent_one_not_sufficient
#print axioms AtiyahMcdonald69.Ex_1_7.zmod_six_example
