/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 2, Exercise 7.

Statement (verbatim, Chapter 2, Exercise 7): "Let 𝔭 be a prime ideal in A. Show that 𝔭[x] is a
prime ideal in A[x]. If 𝔪 is a maximal ideal in A, is 𝔪[x] a maximal ideal in A[x]?"

Here `A[x]` is the polynomial ring in one indeterminate over the (commutative, unital) ring `A`,
and for an ideal `a` of `A`, `a[x]` denotes the set of all polynomials in `A[x]` all of whose
coefficients lie in `a` (this is the set meant in the book; `polyIdeal_eq_map_C` below shows that
it coincides with the extension of `a` to `A[x]`).

Main results:
* `polyIdeal` : the ideal `a[x]` of polynomials with coefficients in `a`, together with the
  coefficient criterion `mem_polyIdeal_iff`;
* `polyIdeal_eq_map_C` : `a[x]` is the extension of `a` to `A[x]`;
* `quotientEquivQuotientPolyIdeal` : the textbook isomorphism `A[x]/a[x] ≃+* (A/a)[x]`;
* `isPrime_polyIdeal` : if `p` is a prime ideal then `p[x]` is a prime ideal of `A[x]`
  (first part of Exercise 2.7); `isPrime_polyIdeal_iff` gives the converse as well;
* `polyIdeal_lt_sup_X`, `sup_X_ne_top` : `p[x] < (p[x], x) < A[x]` for every proper `p`;
* `not_isMaximal_polyIdeal` : the answer to the second part of Exercise 2.7 is *no*: if `m` is a
  maximal ideal then `m[x]` is not maximal, the witness being the ideal `(m[x], x)`;
* `not_isMaximal_polyIdeal_bot_rat` : the concrete counterexample `A = ℚ`, `m = (0)`.

The proof does not use the pre-packaged Mathlib result `Polynomial.isPrime_map_C_iff_isPrime`
(or the instance `Polynomial.isPrime_map_C_of_isPrime`): `polyIdeal` is defined coefficientwise,
exactly as in the book, and primality is proved through the quotient ring `A[x]/a[x] ≃ (A/a)[x]`
and the elementary computation with the constant coefficient for the second part.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_2_7

open Polynomial

variable {A : Type*} [CommRing A]

/-! ### The ideal `a[x]` of polynomials with coefficients in `a` -/

/-- For an ideal `a` of a ring `A`, the set `a[x]` of all polynomials in `A[x]` all of whose
coefficients lie in `a`.  This is the set used in Atiyah–Macdonald, Exercise 2.7;
`polyIdeal_eq_map_C` below shows that it is the extension of `a` to `A[X]`. -/
def polyIdeal (a : Ideal A) : Ideal A[X] where
  carrier := {f | ∀ n, f.coeff n ∈ a}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro f g hf hg n
    simpa using a.add_mem (hf n) (hg n)
  smul_mem' := by
    intro c f hf n
    rw [smul_eq_mul, Polynomial.coeff_mul]
    exact Submodule.sum_mem _ fun ⟨i, j⟩ _ => a.mul_mem_left (c.coeff i) (hf j)

/-- The defining property of `a[x]`: a polynomial lies in `a[x]` exactly when all of its
coefficients lie in `a`. -/
@[simp]
theorem mem_polyIdeal_iff {a : Ideal A} {f : A[X]} :
    f ∈ polyIdeal a ↔ ∀ n, f.coeff n ∈ a :=
  Iff.rfl

theorem coeff_mem_polyIdeal {a : Ideal A} {f : A[X]} (hf : f ∈ polyIdeal a) (n : ℕ) :
    f.coeff n ∈ a :=
  mem_polyIdeal_iff.1 hf n

theorem polyIdeal_mono {a b : Ideal A} (h : a ≤ b) : polyIdeal a ≤ polyIdeal b :=
  fun _ hf n => h (hf n)

@[simp]
theorem polyIdeal_bot : polyIdeal (⊥ : Ideal A) = ⊥ := by
  ext f
  simp [mem_polyIdeal_iff, Polynomial.ext_iff]

@[simp]
theorem polyIdeal_top : polyIdeal (⊤ : Ideal A) = ⊤ := by
  ext f
  simp [mem_polyIdeal_iff]

/-- `a[x]` is the extension of `a` to `A[x]`: the two possible readings of the notation agree. -/
theorem polyIdeal_eq_map_C (a : Ideal A) :
    polyIdeal a = Ideal.map (C : A →+* A[X]) a := by
  refine le_antisymm ?_ ?_
  · intro f hf
    have h : f = f.sum fun n r => C r * X ^ n := (Polynomial.sum_C_mul_X_pow_eq f).symm
    rw [h]
    refine Submodule.sum_mem _ fun n _ => ?_
    exact Ideal.mul_mem_right (X ^ n) _ (Ideal.mem_map_of_mem (C : A →+* A[X]) (hf n))
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx n
    rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hx
    · exact a.zero_mem

/-! ### `A[x]/a[x] ≃ (A/a)[x]` -/

/-- Coefficientwise reduction modulo `a` kills exactly the polynomials all of whose coefficients
lie in `a`. -/
theorem mapRingHom_quotientMk_eq_zero_iff {a : Ideal A} {f : A[X]} :
    Polynomial.mapRingHom (Ideal.Quotient.mk a) f = 0 ↔ f ∈ polyIdeal a := by
  show Polynomial.map (Ideal.Quotient.mk a) f = 0 ↔ f ∈ polyIdeal a
  constructor
  · intro h n
    have h' := congrArg (fun p : (A ⧸ a)[X] => p.coeff n) h
    rw [Polynomial.coeff_map, Polynomial.coeff_zero] at h'
    exact Ideal.Quotient.eq_zero_iff_mem.mp h'
  · intro hf
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hf n

theorem ker_mapRingHom_quotientMk (a : Ideal A) :
    RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk a)) = polyIdeal a := by
  ext f
  rw [RingHom.mem_ker]
  exact mapRingHom_quotientMk_eq_zero_iff

/-- The isomorphism `A[x]/a[x] ≃+* (A/a)[x]` used in the textbook solution. -/
noncomputable def quotientEquivQuotientPolyIdeal (a : Ideal A) :
    A[X] ⧸ polyIdeal a ≃+* (A ⧸ a)[X] :=
  (Ideal.quotEquivOfEq (ker_mapRingHom_quotientMk a).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := Polynomial.mapRingHom (Ideal.Quotient.mk a))
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective))

/-! ### Part 1: `p[x]` is a prime ideal of `A[x]` -/

/-- **Exercise 2.7, first part.**  If `p` is a prime ideal of `A`, then the ideal `p[x]` of
polynomials with coefficients in `p` is a prime ideal of `A[x]`. -/
theorem isPrime_polyIdeal {p : Ideal A} [hp : p.IsPrime] : (polyIdeal p).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : A[X]) ∈ polyIdeal p := h ▸ Submodule.mem_top
    have : (1 : A) ∈ p := by simpa using coeff_mem_polyIdeal h1 0
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr this)
  · intro f g hfg
    have h0 : Polynomial.mapRingHom (Ideal.Quotient.mk p) (f * g) = 0 :=
      mapRingHom_quotientMk_eq_zero_iff.mpr hfg
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact Or.inl (mapRingHom_quotientMk_eq_zero_iff.mp h')
    · exact Or.inr (mapRingHom_quotientMk_eq_zero_iff.mp h')

/-- The converse of the first part: `p[x]` prime implies `p` prime.  Hence
`p[x]` is prime if and only if `p` is prime. -/
theorem isPrime_polyIdeal_iff {p : Ideal A} : (polyIdeal p).IsPrime ↔ p.IsPrime := by
  refine ⟨?_, fun h => @isPrime_polyIdeal A _ p h⟩
  intro h
  refine ⟨?_, ?_⟩
  · intro hp
    exact h.ne_top (by rw [hp, polyIdeal_top])
  · intro x y hxy
    have hC : (C (x * y) : A[X]) ∈ polyIdeal p := by
      rw [mem_polyIdeal_iff]
      intro n
      rw [Polynomial.coeff_C]
      split_ifs with h0
      · subst h0; simpa using hxy
      · exact p.zero_mem
    have hC' : (C x * C y : A[X]) ∈ polyIdeal p := by
      rw [← map_mul]
      exact hC
    rcases h.mem_or_mem hC' with hx | hy
    · exact Or.inl (by simpa using coeff_mem_polyIdeal hx 0)
    · exact Or.inr (by simpa using coeff_mem_polyIdeal hy 0)

/-! ### Part 2: `m[x]` is not a maximal ideal of `A[x]` -/

/-- The key coefficient computation: a polynomial in the ideal `(a[x], x)` has its constant
coefficient in `a`. -/
theorem coeff_zero_mem_of_mem_sup_X {a : Ideal A} {f : A[X]}
    (hf : f ∈ polyIdeal a ⊔ Ideal.span {X}) : f.coeff 0 ∈ a := by
  rw [Submodule.mem_sup] at hf
  obtain ⟨p, hp, q, hq, rfl⟩ := hf
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
  rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero]
  exact coeff_mem_polyIdeal hp 0

/-- For a proper ideal `a` the ideal `a[x]` is strictly contained in `(a[x], x)`, because `x`
itself is not in `a[x]`. -/
theorem polyIdeal_lt_sup_X {a : Ideal A} (ha : a ≠ ⊤) :
    polyIdeal a < polyIdeal a ⊔ Ideal.span {X} := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro h
  have hX : (X : A[X]) ∈ polyIdeal a :=
    h ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self X)
  have : (1 : A) ∈ a := by simpa using coeff_mem_polyIdeal hX 1
  exact ha ((Ideal.eq_top_iff_one a).mpr this)

/-- For a proper ideal `a` the ideal `(a[x], x)` is proper: every element of it has constant
coefficient in `a`, and `1 ∉ a`. -/
theorem sup_X_ne_top {a : Ideal A} (ha : a ≠ ⊤) :
    polyIdeal a ⊔ Ideal.span {X} ≠ ⊤ := by
  intro h
  have h1 : (1 : A[X]) ∈ polyIdeal a ⊔ Ideal.span {X} := h ▸ Submodule.mem_top
  have : (1 : A) ∈ a := by simpa using coeff_zero_mem_of_mem_sup_X h1
  exact ha ((Ideal.eq_top_iff_one a).mpr this)

/-- **Exercise 2.7, second part: the answer is no.**  If `m` is a maximal ideal of `A`, then
`m[x]` is *not* a maximal ideal of `A[x]`: it is strictly contained in the proper ideal
`(m[x], x)`. -/
theorem not_isMaximal_polyIdeal {m : Ideal A} (hm : m.IsMaximal) :
    ¬ (polyIdeal m).IsMaximal := by
  intro hmax
  have hne : m ≠ ⊤ := hm.ne_top
  have hcoord := Ideal.isMaximal_iff.mp hmax
  have hx : (X : A[X]) ∉ polyIdeal m := by
    intro hX
    exact hne ((Ideal.eq_top_iff_one m).mpr (by simpa using coeff_mem_polyIdeal hX 1))
  have hxmem : (X : A[X]) ∈ polyIdeal m ⊔ Ideal.span {X} :=
    Submodule.mem_sup_right (Ideal.mem_span_singleton_self X)
  have h1 : (1 : A[X]) ∈ polyIdeal m ⊔ Ideal.span {X} := hcoord.2 _ _ le_sup_left hx hxmem
  exact sup_X_ne_top hne ((Ideal.eq_top_iff_one _).mpr h1)

/-- More generally, for any proper ideal `a` of `A`, the ideal `a[x]` is not maximal in `A[x]`. -/
theorem not_isMaximal_polyIdeal_of_ne_top {a : Ideal A} (ha : a ≠ ⊤) :
    ¬ (polyIdeal a).IsMaximal := by
  intro hmax
  have hcoord := Ideal.isMaximal_iff.mp hmax
  have hx : (X : A[X]) ∉ polyIdeal a := by
    intro hX
    exact ha ((Ideal.eq_top_iff_one a).mpr (by simpa using coeff_mem_polyIdeal hX 1))
  have hxmem : (X : A[X]) ∈ polyIdeal a ⊔ Ideal.span {X} :=
    Submodule.mem_sup_right (Ideal.mem_span_singleton_self X)
  have h1 : (1 : A[X]) ∈ polyIdeal a ⊔ Ideal.span {X} := hcoord.2 _ _ le_sup_left hx hxmem
  exact sup_X_ne_top ha ((Ideal.eq_top_iff_one _).mpr h1)

/-- The concrete counterexample asked for by the question, in the simplest case `A = ℚ`,
`m = (0)`: `(0)[x] = (0)` is the zero ideal of `ℚ[x]`, which is prime but not maximal. -/
theorem not_isMaximal_polyIdeal_bot_rat :
    ¬ (polyIdeal (⊥ : Ideal ℚ)).IsMaximal :=
  not_isMaximal_polyIdeal (Ideal.bot_isMaximal (K := ℚ))

/-- **Exercise 2.7 as a single statement.**  For every ring `A`: (i) the coefficient ideal `p[x]`
is a prime ideal of `A[x]` whenever `p` is a prime ideal of `A`; (ii) for every maximal ideal `m`
of `A` the coefficient ideal `m[x]` is *not* a maximal ideal of `A[x]` — the answer to the
question posed in the exercise is no. -/
theorem exercise_2_7 :
    (∀ (p : Ideal A), p.IsPrime → (polyIdeal p).IsPrime) ∧
      (∀ (m : Ideal A), m.IsMaximal → ¬ (polyIdeal m).IsMaximal) :=
  ⟨fun p hp => @isPrime_polyIdeal A _ p hp, fun m hm => not_isMaximal_polyIdeal (m := m) hm⟩

end AtiyahMcdonald69.Ex_2_7
