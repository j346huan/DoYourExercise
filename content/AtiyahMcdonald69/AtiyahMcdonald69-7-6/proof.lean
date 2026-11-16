/-
Copyright: formalization of Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 7, Exercise 6.

Reference statement (public sources), see
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-6 :

  A field `K` which is finitely generated *as a ring* (i.e. as a `ℤ`-algebra) is finite.

In Atiyah–Macdonald's conventions a "finitely generated ring" means a ring which is finitely
generated as a `ℤ`-algebra, which is exactly our hypothesis `Algebra.FiniteType ℤ K` (see the
source audit below).

## Source audit

* The scan supplied in `.scratch/reference/atiyah-macdonald-original.txt` stops inside Chapter 6
  (mid-proof of Corollary 6.11), so it does **not** contain the text of the Chapter 7 exercises.
  The statement was therefore checked against the two available public sources instead, which
  agree on the numbering of the Chapter 7 exercises (verified on Exercises 7.4, 7.5, 7.6, 7.7,
  7.8, where both list the same problem in each slot):
  - the public solutions `.scratch/reference/atiyah-solutions.txt`, line 4019:
    "7.6. Show that a finitely generated field K is finite.", whose proof starts
    "Then K is finitely generated over ℤ by hypothesis";
  - `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-7-6/proof.tex`, whose
    argument starts "Suppose K has characteristic zero. Then ℤ ⊆ ℚ ⊆ K, and K is a finitely
    generated ℚ-algebra", i.e. it also uses finite generation over `ℤ`.
* Reading of the statement.  `K` must be finitely generated *as a ring*; that is the hypothesis
  `Algebra.FiniteType ℤ K` below.  The alternative reading "finitely generated as a field
  extension of the prime field" would make the exercise false: `ℚ(X)` is generated as a field by
  the single element `X`, yet is infinite (this is recorded at the end of the file as
  `ratFunc_adjoin_X` and `ratFunc_not_finite`).  So the ring-theoretic reading is the only sensible
  one, and it is the one used by both sources.
* The site's proof is mathematically correct; the only points it leaves implicit are (i) the
  reading of "finitely generated" above, (ii) injectivity of `ℚ → K` in characteristic `0`, which
  the Artin–Tate lemma (Proposition 7.8) requires for the tower `ℤ ⊆ ℚ ⊆ K`, and (iii) that `ℤ` is
  Noetherian, also needed for (7.8).  All three are supplied in the formalization below.

## Proof

In characteristic `p` Zariski's lemma turns the finitely generated `𝔽_p`-algebra `K` into a finite
dimensional `𝔽_p`-vector space, hence a finite field; in characteristic `0` the same lemma makes
`K` finite (module finite) over `ℚ`, and the Artin–Tate lemma then makes `ℚ` finitely generated
as a `ℤ`-algebra, which is impossible by a denominator argument (every element of a finitely
generated `ℤ`-subalgebra of `ℚ` is `m / N ^ k`, so a prime `p ∤ N` prevents `1 / p` from lying
there).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_7_6

/-- `ℚ` is not a finitely generated `ℤ`-algebra: if `ℚ = ℤ[x₁,…,xₙ]` and `N` is a common
denominator of the `xᵢ`, then every element of `ℤ[x₁,…,xₙ]` is of the shape `m / N ^ k`, so it
cannot be `1 / p` for a prime `p ∤ N`. -/
theorem rat_not_finiteType_int : ¬ Algebra.FiniteType ℤ ℚ := by
  rintro ⟨hFG⟩
  obtain ⟨s, hs⟩ := hFG
  classical
  set N : ℕ := ∏ q ∈ s, q.den with hN
  have hNpos : 0 < N := Finset.prod_pos fun q _ => q.den_pos
  have key : ∀ y ∈ Algebra.adjoin ℤ (s : Set ℚ),
      ∃ k : ℕ, ∃ m : ℤ, (N : ℚ) ^ k * y = (m : ℚ) := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y _ => ∃ k : ℕ, ∃ m : ℤ, (N : ℚ) ^ k * y = (m : ℚ))
      ?_ ?_ ?_ ?_ hy
    · -- a generator: `x = x.num / x.den` with `x.den ∣ N`
      intro x hx
      have hdvd : x.den ∣ N := hN ▸ Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hx
      obtain ⟨c, hc⟩ := hdvd
      have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have hx2 : (x.den : ℚ) * x = (x.num : ℚ) := by
        rw [mul_comm]
        exact ((div_eq_iff hden).mp (Rat.num_div_den x)).symm
      refine ⟨1, (c : ℤ) * x.num, ?_⟩
      have hcast : (N : ℚ) = (x.den : ℚ) * (c : ℚ) := by rw [hc]; push_cast; ring
      calc (N : ℚ) ^ 1 * x = (N : ℚ) * x := by rw [pow_one]
        _ = ((x.den : ℚ) * (c : ℚ)) * x := by rw [hcast]
        _ = (c : ℚ) * ((x.den : ℚ) * x) := by ring
        _ = (c : ℚ) * (x.num : ℚ) := by rw [hx2]
        _ = (((c : ℤ) * x.num : ℤ) : ℚ) := by push_cast; ring
    · -- an integer coefficient
      intro r
      exact ⟨0, r, by simp⟩
    · -- sums
      intro a b _ _ ha hb
      obtain ⟨k₁, m₁, h₁⟩ := ha
      obtain ⟨k₂, m₂, h₂⟩ := hb
      refine ⟨k₁ + k₂, m₁ * (N : ℤ) ^ k₂ + m₂ * (N : ℤ) ^ k₁, ?_⟩
      calc (N : ℚ) ^ (k₁ + k₂) * (a + b)
          = (N : ℚ) ^ k₂ * ((N : ℚ) ^ k₁ * a) + (N : ℚ) ^ k₁ * ((N : ℚ) ^ k₂ * b) := by
            rw [pow_add]; ring
        _ = (N : ℚ) ^ k₂ * (m₁ : ℚ) + (N : ℚ) ^ k₁ * (m₂ : ℚ) := by rw [h₁, h₂]
        _ = ((m₁ * (N : ℤ) ^ k₂ + m₂ * (N : ℤ) ^ k₁ : ℤ) : ℚ) := by push_cast; ring
    · -- products
      intro a b _ _ ha hb
      obtain ⟨k₁, m₁, h₁⟩ := ha
      obtain ⟨k₂, m₂, h₂⟩ := hb
      refine ⟨k₁ + k₂, m₁ * m₂, ?_⟩
      calc (N : ℚ) ^ (k₁ + k₂) * (a * b)
          = ((N : ℚ) ^ k₁ * a) * ((N : ℚ) ^ k₂ * b) := by rw [pow_add]; ring
        _ = (m₁ : ℚ) * (m₂ : ℚ) := by rw [h₁, h₂]
        _ = ((m₁ * m₂ : ℤ) : ℚ) := by push_cast; ring
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 1)
  have hp_not_dvd : ¬ p ∣ N := by
    intro hd
    have := Nat.le_of_dvd hNpos hd
    omega
  have hmem : ((p : ℚ))⁻¹ ∈ Algebra.adjoin ℤ (s : Set ℚ) := by
    rw [hs]; trivial
  obtain ⟨k, m, hm⟩ := key _ hmem
  have hp0 : (p : ℚ) ≠ 0 := by
    have h := hp_prime.ne_zero
    exact_mod_cast h
  -- multiply `N ^ k * p⁻¹ = m` by `p`
  have hm2 : (N : ℚ) ^ k = (m : ℚ) * (p : ℚ) := by
    have h := congrArg (fun t : ℚ => t * (p : ℚ)) hm
    rw [mul_assoc, inv_mul_cancel₀ hp0, mul_one] at h
    exact h
  have hZ : (N : ℤ) ^ k = m * (p : ℤ) := by
    exact_mod_cast hm2
  have hdvdZ : (p : ℤ) ∣ (N : ℤ) ^ k := ⟨m, by rw [hZ, mul_comm]⟩
  have hdvd : p ∣ N ^ k := by
    have h2 : ((p : ℤ) ∣ ((N ^ k : ℕ) : ℤ)) := by
      rwa [Nat.cast_pow]
    exact_mod_cast h2
  exact hp_not_dvd (hp_prime.dvd_of_dvd_pow hdvd)

/-- **Atiyah–Macdonald, Exercise 7.6.**  A finitely generated field is finite: a field which is
finitely generated as a ring (as a `ℤ`-algebra) has finitely many elements. -/
theorem solution (K : Type*) [Field K] (h : Algebra.FiniteType ℤ K) : Finite K := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · -- positive characteristic `p`: Zariski's lemma over `𝔽_p`
    have : Fact (Nat.Prime (ringChar K)) := ⟨hp⟩
    let : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
    have : IsScalarTower ℤ (ZMod (ringChar K)) K :=
      ⟨fun r s a => by
        have h1 : ∀ r : ℤ, algebraMap (ZMod (ringChar K)) K
            (algebraMap ℤ (ZMod (ringChar K)) r) = algebraMap ℤ K r := by
          intro r; simp
        simp only [Algebra.smul_def, map_mul, h1]
        ring⟩
    have : Algebra.FiniteType (ZMod (ringChar K)) K :=
      Algebra.FiniteType.of_restrictScalars_finiteType (R := ℤ) (S := ZMod (ringChar K)) (A := K)
        (hA := h)
    have : Module.Finite (ZMod (ringChar K)) K :=
      finite_of_finite_type_of_isJacobsonRing (ZMod (ringChar K)) K
    exact Module.finite_of_finite (ZMod (ringChar K))
  · -- characteristic `0`: Artin–Tate gives the contradiction `ℤ ⊆ ℚ ⊆ K`
    have : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp h0
    have : Algebra.FiniteType ℚ K :=
      Algebra.FiniteType.of_restrictScalars_finiteType (R := ℤ) (S := ℚ) (A := K) (hA := h)
    have : Module.Finite ℚ K := finite_of_finite_type_of_isJacobsonRing ℚ K
    have hinj : Function.Injective (algebraMap ℚ K) := by
      intro x y hxy
      exact Rat.cast_injective hxy
    have hFT : (⊤ : Subalgebra ℤ ℚ).FG :=
      fg_of_fg_of_fg ℤ ℚ K h.out Module.Finite.fg_top hinj
    exact absurd ⟨hFT⟩ rat_not_finiteType_int

/-- Exercise 7.6 with the finite set of ring generators made explicit: a field generated, as a
ring, by finitely many elements is finite. -/
theorem solution_of_adjoin (K : Type*) [Field K] (s : Finset K)
    (h : Algebra.adjoin ℤ (s : Set K) = ⊤) : Finite K :=
  solution K ⟨s, h⟩

/-- Concretely: every field which is a quotient of a finitely generated polynomial ring over `ℤ`
(in particular every residue field of such a ring) is finite. -/
theorem solution_of_surjective (K : Type*) [Field K] (n : ℕ)
    (f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] K) (hf : Function.Surjective f) : Finite K :=
  solution K (Algebra.FiniteType.of_surjective f hf)

/-! ### Scope remark: the other reading of "finitely generated"

The exercise is about finite generation *as a ring*.  If "finitely generated field" were read as
"finitely generated as a field extension of its prime field", the assertion would be false, as the
following two statements show: `ℚ(X)` is generated as a field over `ℚ` by the single element `X`,
and it is infinite.  These two lemmas are recorded only to document that the ring-theoretic reading
is the only one under which Exercise 7.6 is a true statement; they are not used above. -/

/-- `ℚ(X)` is generated, as a field over `ℚ`, by the single element `X`. -/
theorem ratFunc_adjoin_X :
    letI := RatFunc.instAlgebraOfPolynomial ℚ
    IntermediateField.adjoin ℚ ({RatFunc.X} : Set (RatFunc ℚ)) = ⊤ :=
  RatFunc.adjoin_X

/-- `ℚ(X)` is infinite. -/
theorem ratFunc_not_finite : ¬ Finite (RatFunc ℚ) := by
  intro h
  have : Finite ℚ := Finite.of_injective (algebraMap ℚ (RatFunc ℚ)) Rat.cast_injective
  exact not_finite ℚ

end AtiyahMcdonald69.Ex_7_6
