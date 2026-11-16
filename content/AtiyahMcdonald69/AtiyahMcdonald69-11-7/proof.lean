/-
Copyright: formalization for the Atiyah–Macdonald formalization project.

# Atiyah–Macdonald (1969), Chapter 11, Exercise 11.7

## The exercise (original statement)

Let `A` be a Noetherian ring.  Then

  dim A[x] = 1 + dim A,

and hence, by induction on `n`,

  dim A[x₁, …, xₙ] = n + dim A.

(The exercise is on p. 126 of the book.  The wording above is the one transcribed in
P.-Y. Gaillard, "About Atiyah and MacDonald's Book", §12.2.6.)

The book also gives a hint, consisting of three claims, which we state and prove as well:

1. if `p` is a prime of `A` of height `m`, there are `a₁, …, aₘ ∈ p` such that `p` is a minimal
   prime ideal of `(a₁, …, aₘ)`;
2. then `p[x]` is a minimal prime ideal of `(a₁, …, aₘ)[x]` (Exercise 4.7 of Chapter 4);
3. hence `ht p[x] = ht p`  (using Corollary 11.16, Krull's height theorem, for `≤`, and the
   chain `p₀ ⊂ ⋯ ⊂ pₘ = p` for `≥`).

## Coverage of the original statement

* `part_a` : `dim A[x] = dim A + 1` (the displayed identity (69) of the exercise);
* `part_b` : `dim A[x₁, …, xₙ] = dim A + n` for every `n : ℕ`;
* `solution` : the conjunction of the two, i.e. the full exercise;
* `exists_finset_isMinimalPrime_card_eq_height`, `mem_minimalPrimes_map_C`, `height_map_C_le`,
  `map_C_lt_map_C`, `height_le_height_map_C`, `height_map_C_eq` : the book's hint, claims 1–3;
* `height_le_comap_C_add_one` : the key estimate proved in the solution text,
  `ht q ≤ ht (q ∩ A) + 1` for every prime `q` of `A[x]`;
* `comap_C_map_C`, `height_le_one_of_comap_C_eq_bot`, `eq_of_le_of_isPrime_of_comap_C_eq_bot` :
  the fibre computation over a domain used in `height_le_comap_C_add_one`.

## Source

Natural-language solution (used as guidance, checked line by line against the book's hint):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-11-7
(local copy: `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-11-7/proof.tex`)

## Mathematical approach

Upper bound `dim A[x] ≤ dim A + 1`, following the book: let `q` be a prime of `A[x]` and
`p = q ∩ A`, of height `h`.  Choose `a₁, …, a_h ∈ p` with `p` minimal over `(a₁, …, a_h)`
(this uses that `p.height` is finite in a Noetherian ring).  If `q = p[x]`, then `q` is minimal
over `(a₁, …, a_h)[x]`, so `ht q ≤ h` by Krull's height theorem.  If `q ≠ p[x]` and
`f ∈ q ∖ p[x]`, then `q` is a minimal prime of the ideal `J = (a₁, …, a_h, f)`: any prime
`J ≤ Q ≤ q` contracts to `p`, so after passing to the fibre `(A ⧸ p)[x]` both `Q` and `q` become
nonzero primes of a polynomial ring over a domain contracting to `0`, hence coincide (a prime of
`D[x]` contracting to `0` has height at most one, proved here by localizing at the nonzero
divisors and using that `K[x]` is a PID).  Krull's height theorem then gives `ht q ≤ h + 1`.
Taking suprema yields `dim A[x] ≤ dim A + 1`.

Lower bound `dim A + 1 ≤ dim A[x]`: this is Exercise 11.6 of the book, which the solution text
cites; formally it is Mathlib's `ringKrullDim_succ_le_ringKrullDim_polynomial`.

The `n`-variable statement follows by induction from the one-variable statement, exactly as in
the book, using `A[x₁, …, xₙ₊₁] ≅ A[x₁, …, xₙ][x]` (`MvPolynomial.finSuccEquiv`) and
`A[x₁, …, x₀] ≅ A` (`MvPolynomial.isEmptyAlgEquiv`).

## Statement adaptation (dimension conventions)

`dim` is Mathlib's `ringKrullDim : WithBot ℕ∞`, the order-theoretic Krull dimension of
`PrimeSpectrum A`.  This matches the book's supremum of lengths of chains of prime ideals:
* for a nontrivial ring, `ringKrullDim A = ⊤` exactly when `Spec A` is infinite dimensional, and
  `⊤ + 1 = ⊤`, so the identity is a statement about both finite and infinite dimension (the
  latter can really occur for Noetherian `A`, cf. Exercise 11.4);
* for the zero ring, which Atiyah–Macdonald exclude, `ringKrullDim A = ⊥ = ⊥ + 1`, so the
  identity holds there too; no `Nontrivial` hypothesis is needed.
`A[x₁, …, xₙ]` is `MvPolynomial (Fin n) A`, and heights are `Ideal.height : ℕ∞`.

Notational detail: the `Finset` image of `a₁, …, aₘ` under `a ↦ a` in `A[x]` is written
`s.map Cemb`, where `Cemb : A ↪ A[X]` is the embedding `a ↦ Polynomial.C a` (a bundled form is
needed because `Finset.image` would require `DecidableEq A[X]`); as a set it is exactly
`C '' ↑s`, i.e. the coefficient set of `(a₁, …, aₘ)[x]`.

The hypothesis "`A` Noetherian" is used exactly where the book uses it: `A[x]` is Noetherian, and
every prime of a Noetherian ring has finite height (needed to choose the system of parameters).
No other hypothesis is added.  There are no `sorry`s and no axioms beyond the standard three.
-/

import Mathlib

set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_11_7

open Polynomial

variable {A : Type*} [CommRing A]

/-- The embedding `A → A[X]`, `a ↦ C a`, as a `Finset` embedding (avoids `DecidableEq`). -/
noncomputable def Cemb : A ↪ A[X] := ⟨C, Polynomial.C_injective⟩

@[simp] lemma Cemb_apply (a : A) : Cemb a = C a := rfl

/-- The constants `I[X]` of an ideal `I` contract back to `I`. -/
lemma comap_C_map_C (I : Ideal A) :
    (I.map (C : A →+* A[X])).comap (C : A →+* A[X]) = I := by
  refine le_antisymm ?_ Ideal.le_comap_map
  intro a ha
  have h := (Ideal.mem_map_C_iff.mp (Ideal.mem_comap.mp ha)) 0
  simpa using h

/-- **(Book hint, first assertion).**  If `A` is Noetherian and `p` is a prime of height `m`,
there are `a₁, …, a_m ∈ p` such that `p` is a minimal prime of `(a₁, …, a_m)`. -/
theorem exists_finset_isMinimalPrime_card_eq_height [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    ∃ s : Finset A, p ∈ (Ideal.span (s : Set A)).minimalPrimes ∧ (s.card : ℕ∞) = p.height :=
  Ideal.exists_finset_card_eq_height_of_isNoetherianRing p

/-- **(Book hint, second assertion, Exercise 4.7 of Chapter 4).**  If `p` is a minimal prime
of `(a₁, …, a_m)` then `p[x]` is a minimal prime of `(a₁, …, a_m)[x]`. -/
theorem mem_minimalPrimes_map_C {s : Finset A} {p : Ideal A} [p.IsPrime]
    (hp : p ∈ (Ideal.span (s : Set A)).minimalPrimes) :
    p.map (C : A →+* A[X]) ∈ (Ideal.span ((s.map Cemb) : Set A[X])).minimalPrimes := by
  have hspaneq : Ideal.span ((s.map Cemb) : Set A[X]) =
      Ideal.map (C : A →+* A[X]) (Ideal.span (s : Set A)) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp
  rw [hspaneq]
  refine ⟨⟨Ideal.isPrime_map_C_of_isPrime, ?_⟩, ?_⟩
  · -- `(a₁, …, a_m)[x] ≤ p[x]`
    exact Ideal.map_mono hp.le
  · intro y hy hyq
    haveI : y.IsPrime := hy.1
    have hspan_le : Ideal.span (s : Set A) ≤ y.comap (C : A →+* A[X]) := by
      rw [Ideal.span_le]
      intro a ha
      exact Ideal.mem_comap.mpr (hy.2 (Ideal.mem_map_of_mem C (Ideal.subset_span ha)))
    have hcomap_le : y.comap (C : A →+* A[X]) ≤ p := by
      intro a ha
      have h := (Ideal.mem_map_C_iff.mp (hyq (Ideal.mem_comap.mp ha))) 0
      simpa using h
    exact Ideal.map_le_iff_le_comap.mpr (hp.2 ⟨Ideal.IsPrime.comap C, hspan_le⟩ hcomap_le)

/-- **(Book hint, third assertion, `≤` half).**  Krull's height theorem (Corollary 11.16):
`ht p[x] ≤ ht p`. -/
theorem height_map_C_le [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* A[X])).height ≤ p.height := by
  obtain ⟨s, hs, hcard⟩ := exists_finset_isMinimalPrime_card_eq_height p
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset (mem_minimalPrimes_map_C hs)).trans ?_
  rw [Finset.card_map, hcard]

/-- If `x < y` are primes, then `x[x] < y[x]`. -/
theorem map_C_lt_map_C {x y : Ideal A} [x.IsPrime] [y.IsPrime] (h : x < y) :
    x.map (C : A →+* A[X]) < y.map (C : A →+* A[X]) := by
  have h1 : x.map (C : A →+* A[X]) ≤ y.map (C : A →+* A[X]) := Ideal.map_mono h.le
  refine lt_of_le_of_ne h1 ?_
  intro heq
  apply h.ne
  have h2 : Ideal.comap (C : A →+* A[X]) (Ideal.map (C : A →+* A[X]) x) =
      Ideal.comap (C : A →+* A[X]) (Ideal.map (C : A →+* A[X]) y) := by rw [heq]
  rwa [comap_C_map_C, comap_C_map_C] at h2

/-- **(Book hint, third assertion, `≥` half).**  A chain of primes below `p` maps to a chain of
primes below `p[x]`, so `ht p ≤ ht p[x]`. -/
theorem height_le_height_map_C [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    p.height ≤ (p.map (C : A →+* A[X])).height := by
  have htop : p.height ≠ ⊤ := (Ideal.height_lt_top (I := p) Ideal.IsPrime.ne_top').ne
  have key : ∀ (n : ℕ), ∀ (r : Ideal A), r.IsPrime → (n : ℕ∞) ≤ r.height →
      (n : ℕ∞) ≤ (r.map (C : A →+* A[X])).height := by
    intro n
    induction n with
    | zero => intro r hr h; exact zero_le
    | succ n ih =>
      intro r hr hnr
      haveI : r.IsPrime := hr
      have hlt : ¬ (r.height ≤ (n : ℕ∞)) := by
        intro hle
        have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := le_trans hnr hle
        have h2 : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
        exact absurd h1 (not_le_of_gt h2)
      rw [Ideal.height_le_iff] at hlt
      push Not at hlt
      obtain ⟨q, hq, hqr, hqn⟩ := hlt
      haveI : q.IsPrime := hq
      have h1 : (n : ℕ∞) ≤ (q.map (C : A →+* A[X])).height := ih q hq hqn
      have h2 : (q.map (C : A →+* A[X])).height + 1 ≤ (r.map (C : A →+* A[X])).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime (map_C_lt_map_C hqr)
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
        _ ≤ (q.map (C : A →+* A[X])).height + 1 := by gcongr
        _ ≤ (r.map (C : A →+* A[X])).height := h2
  have hcoe : (((p.height.toNat : ℕ) : ℕ∞)) = p.height := ENat.natCast_toNat htop
  calc p.height = (((p.height.toNat : ℕ) : ℕ∞)) := hcoe.symm
    _ ≤ (p.map (C : A →+* A[X])).height := key p.height.toNat p ‹p.IsPrime› hcoe.le

/-- **(Book hint, third assertion).**  For a prime `p` of a Noetherian ring, `ht p[x] = ht p`. -/
theorem height_map_C_eq [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* A[X])).height = p.height :=
  le_antisymm (height_map_C_le p) (height_le_height_map_C p)

section Fibre

variable {D : Type*} [CommRing D] [IsDomain D]

/-- **Fibre lemma.**  A prime of `D[x]`, `D` a domain, that contracts to `0` has height at most one.

Formal proof: `D[x] → K[x]` (`K` the fraction field of `D`) is a localization at the non-zero
divisors of `D`, so it preserves heights of primes disjoint from that submonoid; the image of `P`
is a prime of the PID `K[x]`, which has dimension one. -/
theorem height_le_one_of_comap_C_eq_bot (P : Ideal D[X]) [P.IsPrime]
    (hP : P.comap (C : D →+* D[X]) = ⊥) : P.height ≤ 1 := by
  letI : Algebra D[X] (Polynomial (FractionRing D)) := Polynomial.algebra D (FractionRing D)
  haveI hisLoc : IsLocalization ((nonZeroDivisors D).map (C : D →+* D[X]))
      (Polynomial (FractionRing D)) :=
    Polynomial.isLocalization (nonZeroDivisors D) (FractionRing D)
  have hdisj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (P : Set D[X]) := by
    rw [Set.disjoint_left]
    rintro x ⟨d, hd, rfl⟩ hxP
    have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
    have hx : d ∈ P.comap (C : D →+* D[X]) := hxP
    rw [hP] at hx
    exact hd0 (by simpa using hx)
  have hprime : (P.map (algebraMap D[X] (Polynomial (FractionRing D)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (M := (nonZeroDivisors D).map (C : D →+* D[X]))
      (S := Polynomial (FractionRing D)) P ‹P.IsPrime› hdisj
  have hcomap : (P.map (algebraMap D[X] (Polynomial (FractionRing D)))).under D[X] = P :=
    IsLocalization.under_map_of_isPrime_disjoint (M := (nonZeroDivisors D).map (C : D →+* D[X]))
      (S := Polynomial (FractionRing D)) ‹P.IsPrime› hdisj
  have hheight : P.height = (P.map (algebraMap D[X] (Polynomial (FractionRing D)))).height := by
    conv_lhs => rw [← hcomap]
    exact IsLocalization.height_under ((nonZeroDivisors D).map (C : D →+* D[X]))
      (A := Polynomial (FractionRing D)) _
  rw [hheight]
  have hK : ringKrullDim (Polynomial (FractionRing D)) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← Ring.krullDimLE_iff]
    exact IsPrincipalIdealRing.krullDimLE_one _
  have h := (ringKrullDim_le_iff_height_le ((1 : ℕ) : WithBot ℕ∞)).mp hK hprime
  exact WithBot.coe_le_coe.mp h

/-- Primes of `D[x]` contracting to `0` and different from `0` are equal to each other. -/
theorem eq_of_le_of_isPrime_of_comap_C_eq_bot {P Q : Ideal D[X]} [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) (hP : P ≠ ⊥) (hQ : Q.comap (C : D →+* D[X]) = ⊥) : P = Q := by
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ hne
  have hQle : Q.height ≤ 1 := height_le_one_of_comap_C_eq_bot Q hQ
  have hPlt : P.height < 1 := by
    have h' := (Ideal.height_le_iff (p := Q) (n := 1)).mp hQle P ‹P.IsPrime› hlt
    simpa using h'
  have hP0 : P.height = 0 := Order.lt_one_iff.mp hPlt
  exact hP ((Ideal.height_eq_zero_iff_eq_bot).mp hP0)

end Fibre

section Main

variable [IsNoetherianRing A]

/-- The heart of the exercise: any prime `q` of `A[x]` has height at most one more than the
height of its contraction `p = q ∩ A`.

This is the book's argument: pick `a₁, …, a_h ∈ p` with `p` minimal over `(a₁, …, a_h)`; if
`q ≠ p[x]` and `f ∈ q ∖ p[x]`, then `q` is a minimal prime of the ideal generated by
`a₁, …, a_h, f`, so Krull's height theorem gives `ht q ≤ h + 1`. -/
theorem height_le_comap_C_add_one (q : Ideal A[X]) [q.IsPrime] :
    q.height ≤ (q.comap (C : A →+* A[X])).height + 1 := by
  classical
  obtain ⟨s, hsmin, hscard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (q.comap (C : A →+* A[X]))
  have hmap_le_q : (q.comap (C : A →+* A[X])).map C ≤ q :=
    Ideal.map_le_iff_le_comap.mpr le_rfl
  rcases eq_or_ne q ((q.comap (C : A →+* A[X])).map C) with hq | hq
  · rw [hq, comap_C_map_C]
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (mem_minimalPrimes_map_C hsmin)).trans ?_
    rw [Finset.card_map, hscard]
    exact le_self_add
  · have hnotle : ¬ q ≤ (q.comap (C : A →+* A[X])).map C := fun h =>
      hq (le_antisymm h hmap_le_q)
    obtain ⟨f, hfq, hfnot⟩ := Set.not_subset.mp hnotle
    -- the ideal `J = (a₁, …, a_h, f)`
    set t : Finset A[X] := insert f (s.map Cemb) with ht
    have hfJ : f ∈ Ideal.span (t : Set A[X]) := by
      refine Ideal.subset_span ?_
      rw [ht]
      exact Finset.mem_coe.mpr (Finset.mem_insert_self f _)
    have hspanC : ∀ a ∈ s, C a ∈ (t : Set A[X]) := by
      intro a ha
      rw [ht]
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
    have hminJ : q ∈ (Ideal.span (t : Set A[X])).minimalPrimes := by
      refine ⟨⟨‹q.IsPrime›, ?_⟩, ?_⟩
      · rw [Ideal.span_le]
        intro x hx
        have hxt : x ∈ t := Finset.mem_coe.mp hx
        rw [ht] at hxt
        rcases Finset.mem_insert.mp hxt with rfl | hx'
        · exact hfq
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx'
          exact hmap_le_q (Ideal.mem_map_of_mem C (hsmin.le (Ideal.subset_span ha)))
      · intro y hy hyq
        haveI : y.IsPrime := hy.1
        have hspan_le : Ideal.span (s : Set A) ≤ y.comap (C : A →+* A[X]) := by
          rw [Ideal.span_le]
          intro a ha
          exact Ideal.mem_comap.mpr (hy.2 (Ideal.subset_span (hspanC a ha)))
        have hcomap_le : y.comap (C : A →+* A[X]) ≤ q.comap (C : A →+* A[X]) :=
          Ideal.comap_mono hyq
        have hcomap_eq : y.comap (C : A →+* A[X]) = q.comap (C : A →+* A[X]) :=
          le_antisymm hcomap_le (hsmin.2 ⟨Ideal.IsPrime.comap C, hspan_le⟩ hcomap_le)
        -- pass to the fibre `(A ⧸ p)[x]`
        let ψ : A[X] →+* (A ⧸ q.comap (C : A →+* A[X]))[X] :=
          Polynomial.mapRingHom (Ideal.Quotient.mk (q.comap (C : A →+* A[X])))
        have hψ : Function.Surjective ψ :=
          Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
        have hker : RingHom.ker ψ = (q.comap (C : A →+* A[X])).map C := by
          rw [show ψ = Polynomial.mapRingHom (Ideal.Quotient.mk (q.comap (C : A →+* A[X]))) from rfl,
            Polynomial.ker_mapRingHom, Ideal.mk_ker]
        have hker_le_y : RingHom.ker ψ ≤ y := by
          rw [hker]
          exact Ideal.map_le_iff_le_comap.mpr hcomap_eq.ge
        have hybar : (y.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψ hker_le_y
        have hqbar : (q.map ψ).IsPrime :=
          Ideal.map_isPrime_of_surjective hψ (hker.trans_le hmap_le_q)
        haveI : (y.map ψ).IsPrime := hybar
        haveI : (q.map ψ).IsPrime := hqbar
        have hf_not_ker : f ∉ RingHom.ker ψ := by
          rw [hker]
          exact hfnot
        have hybar_ne : y.map ψ ≠ ⊥ := by
          intro hbot
          have hmem : ψ f ∈ y.map ψ := Ideal.mem_map_of_mem ψ (hy.2 hfJ)
          rw [hbot] at hmem
          exact hf_not_ker (RingHom.mem_ker.mpr (Ideal.mem_bot.mp hmem))
        have hqbar_bot : (q.map ψ).comap (C : (A ⧸ q.comap (C : A →+* A[X])) →+*
            (A ⧸ q.comap (C : A →+* A[X]))[X]) = ⊥ := by
          rw [eq_bot_iff]
          intro a ha
          rw [Ideal.mem_comap] at ha
          obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
          rw [Ideal.mem_map_iff_of_surjective ψ hψ] at ha
          obtain ⟨x, hxq, hx⟩ := ha
          have hC : ψ (C a') = C (Ideal.Quotient.mk (q.comap (C : A →+* A[X])) a') := by
            simp [ψ]
          have hx0 : ψ (x - C a') = 0 := by rw [map_sub, hx, hC, sub_self]
          have hCa'q : C a' ∈ q := by
            have hsub : x - C a' ∈ (q.comap (C : A →+* A[X])).map C := by
              rw [← hker]
              exact RingHom.mem_ker.mp hx0
            simpa using q.sub_mem hxq (hmap_le_q hsub)
          have hmem_p : a' ∈ q.comap (C : A →+* A[X]) := hCa'q
          exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hmem_p)
        have hEq : y.map ψ = q.map ψ :=
          eq_of_le_of_isPrime_of_comap_C_eq_bot (Ideal.map_mono hyq) hybar_ne hqbar_bot
        have hycomap : Ideal.comap ψ (Ideal.map ψ y) = y := by
          rw [Ideal.comap_map_of_surjective' ψ hψ]
          exact sup_eq_left.mpr hker_le_y
        have hqcomap : Ideal.comap ψ (Ideal.map ψ q) = q := by
          rw [Ideal.comap_map_of_surjective' ψ hψ]
          exact sup_eq_left.mpr (hker.trans_le hmap_le_q)
        have hyq_eq : y = q := by
          calc y = Ideal.comap ψ (Ideal.map ψ y) := hycomap.symm
            _ = Ideal.comap ψ (Ideal.map ψ q) := by rw [hEq]
            _ = q := hqcomap
        rw [hyq_eq]
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hminJ).trans ?_
    calc ((t.card : ℕ) : ℕ∞) ≤ ((s.card + 1 : ℕ) : ℕ∞) := by
          have h1 : t.card ≤ s.card + 1 := by
            rw [ht]
            exact (Finset.card_insert_le f (s.map Cemb)).trans (by rw [Finset.card_map])
          exact_mod_cast h1
      _ = (q.comap (C : A →+* A[X])).height + 1 := by
          push_cast
          rw [hscard]

end Main

section Exercise

variable [IsNoetherianRing A]

/-- **Exercise 11.7, first assertion.**  If `A` is Noetherian, then `dim A[x] = dim A + 1`. -/
theorem part_a : ringKrullDim (Polynomial A) = ringKrullDim A + 1 := by
  refine le_antisymm ?_ ringKrullDim_succ_le_ringKrullDim_polynomial
  rw [ringKrullDim_le_iff_height_le]
  intro p hp
  haveI : p.IsPrime := hp
  calc ((p.height : ℕ∞) : WithBot ℕ∞) ≤ (((p.comap (C : A →+* A[X])).height + 1 : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast height_le_comap_C_add_one p
    _ = ((p.comap (C : A →+* A[X])).height : WithBot ℕ∞) + 1 := by
        rw [WithBot.coe_add, WithBot.coe_one]
    _ ≤ ringKrullDim A + 1 := by
        gcongr
        exact Ideal.height_le_ringKrullDim_of_ne_top (I := p.comap (C : A →+* A[X]))
          (Ideal.IsPrime.ne_top' (I := p.comap (C : A →+* A[X])))

/-- **Exercise 11.7, second assertion.**  If `A` is Noetherian, then
`dim A[x₁, …, xₙ] = dim A + n`. -/
theorem part_b (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) A) = ringKrullDim A + n := by
  induction n with
  | zero =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toRingEquiv]
    simp
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv A n).toRingEquiv]
    rw [part_a, ih]
    push_cast
    ring

/-- **Atiyah–Macdonald, Exercise 11.7.**  Let `A` be a Noetherian ring.  Then
`dim A[x] = 1 + dim A`, and hence, by induction on `n`, `dim A[x₁, …, xₙ] = n + dim A`. -/
theorem solution :
    ringKrullDim (Polynomial A) = ringKrullDim A + 1 ∧
      (∀ n : ℕ, ringKrullDim (MvPolynomial (Fin n) A) = ringKrullDim A + n) :=
  ⟨part_a, part_b⟩

/-- Sanity (non-vacuity) check: over a field `k`, the exercise gives `dim k[x₁, …, xₙ] = n`,
the classical computation of the dimension of affine `n`-space. -/
theorem part_b_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [part_b]
  simp

end Exercise

end AtiyahMcdonald69.Ex_11_7

/-! ## Axiom check for the main declarations -/

#print axioms AtiyahMcdonald69.Ex_11_7.part_a
#print axioms AtiyahMcdonald69.Ex_11_7.part_b
#print axioms AtiyahMcdonald69.Ex_11_7.solution
#print axioms AtiyahMcdonald69.Ex_11_7.height_le_comap_C_add_one
#print axioms AtiyahMcdonald69.Ex_11_7.height_map_C_eq
#print axioms AtiyahMcdonald69.Ex_11_7.mem_minimalPrimes_map_C
