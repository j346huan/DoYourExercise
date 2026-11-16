/-
# Atiyah–Macdonald (1969), Chapter V, Exercise 13

## The book statement

> **Exercise 5.13.** In the situation of Exercise 12, let `𝔭` be a prime ideal of `A^G`, and let
> `P` be the set of prime ideals of `A` whose contraction is `𝔭`. Show that `G` acts transitively
> on `P`. In particular, `P` is finite.

The situation of Exercise 12 is: `G` is a **finite group of automorphisms** of a (commutative)
ring `A`, and `A^G ⊆ A` is the subring of `G`-invariants, i.e. of all `x` with `σ x = x` for all
`σ ∈ G`; Exercise 12 (its first part, which is the only part used here) proves that `A` is
**integral** over `A^G`, hence lying-over holds for the extension `A^G ⊆ A`.

## Formalization

* `A` is a `CommRing`, `G` a `Group` with a `MulSemiringAction G A` (an action by ring
  automorphisms) and `[Finite G]`.
* `A^G` is `FixedPoints.subring A G`.
* For a prime `𝔭 : Ideal (FixedPoints.subring A G)`, the set of primes of `A` contracting to
  `𝔭` is `𝔭.primesOver A` (Mathlib's `Ideal.primesOver`, defined as the set of prime `P` with
  `P.LiesOver 𝔭`, i.e. `𝔭 = P.under (FixedPoints.subring A G) = P.comap (algebraMap _ A)`).
* `g • P` is the conjugate of `P` by `g` (`Ideal.pointwise_smul`, the image of `P` under `g`).

Main declarations:

* `nonempty_primesOver`: lying-over (this is where Exercise 12's integrality enters);
* `smul_mem_primesOver`, `smul_eq_map`: `G` acts on the set of primes over `𝔭`, by images
  `g • P = g(P)`;
* `eq_of_le_of_under_eq`: incomparability in the integral extension `A^G ⊆ A`;
* `exists_smul_eq_of_under_eq_book`: transitivity, by the book's own argument (invariant
  products, finite prime avoidance, incomparability), using Exercise 12 only through
  `isIntegral_invariants`;
* `exists_smul_eq_of_under_eq`, `exists_smul_eq_of_primesOver`, `orbit_eq_primesOver`:
  transitivity through Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`, and the sharper
  statement that the primes over `𝔭` form a single `G`-orbit;
* `finite_primesOver`: the "in particular" clause, and `ncard_primesOver_le`: the explicit bound
  `|P| ≤ |G|` (the book's solution only says "finite");
* `exists_smul_eq_of_primesOver_book`, `finite_primesOver_book`, `solution_book`: the whole
  exercise again, derived only from the book's route above;
* `solution`, `solution'`, `solution_comap`: Exercise 5.13 itself, in three equivalent shapes
  (`primesOver`/`LiesOver`, the bundle "nonempty + stable + one orbit + finite", and the
  contraction form matching the book's wording).

## Audit of the statement and of the natural proof

* The hypothesis that `G` is **finite** is part of the situation of Exercise 12 and is essential:
  it enters through integrality of `A` over `A^G` (Exercise 12). Without it the conclusion fails:
  for `A = k[X]` with `G = k^×` acting by `X ↦ cX` (`k` infinite) one has `A^G = k`, and the
  prime ideals `(0)` and `(X)` of `A` both contract to `(0)`, while `(X)` is fixed by every `c`, so
  the two are not conjugate. (This sharpness example is *not* formalized here; the exercise itself
  only asks the finite case.)
* `P` is nonempty by lying-over, which is why `solution'` records `Nonempty`; transitivity alone
  would be vacuous otherwise, and the natural proof's first line ("Lying-over and 5.12 show that
  this set is nonempty") is exactly `nonempty_primesOver`.
* The natural proof's chain -- invariant product `∏_σ σ x` lies in `A^G` and in `P`, hence in
  `Q`; primality gives `σ x ∈ Q`; finite prime avoidance; incomparability -- is correct as stated
  and is formalized verbatim in `exists_smul_eq_of_under_eq_book`. No hypothesis of the book
  statement needs to be added, removed or weakened.
* Only the first part of Exercise 12 (integrality) is used; the multiplicative-set part of
  Exercise 12 is irrelevant to Exercise 13.
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_5_13

open scoped Pointwise

variable {G A : Type*} [Group G] [CommRing A] [MulSemiringAction G A] [Finite G]

/-! ### The two inputs from Exercise 12 and from lying-over -/

/-- Every element of `A` fixed by all of `G` lies in `A^G`: the extension `A^G ⊆ A` is invariant. -/
instance : Algebra.IsInvariant (FixedPoints.subring A G) A G :=
  ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

/-- Exercise 5.12, first part: a ring is integral over its ring of invariants under a finite group
of automorphisms. (This is the only part of Exercise 12 used in Exercise 13.) -/
instance isIntegral_invariants : Algebra.IsIntegral (FixedPoints.subring A G) A :=
  Algebra.IsInvariant.isIntegral (A := FixedPoints.subring A G) (B := A) (G := G)

/-- Lying-over for `A^G ⊆ A`: the set of primes of `A` contracting to a given prime of `A^G` is
nonempty. -/
theorem nonempty_primesOver (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (p.primesOver A).Nonempty := by
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_primesOver (R := FixedPoints.subring A G) (S := A) (P := p)
  exact ⟨Q, hQ⟩

/-! ### `G` acts on the set of primes over `𝔭` -/

omit [Finite G] in
/-- The conjugate of a prime of `A` over `𝔭` is again a prime over `𝔭`. -/
theorem smul_mem_primesOver {p : Ideal (FixedPoints.subring A G)} [p.IsPrime] {P : Ideal A}
    (hP : P ∈ p.primesOver A) (g : G) : g • P ∈ p.primesOver A :=
  ⟨hP.1.smul g, hP.2.smul g⟩

omit [Finite G] in
/-- The conjugate `g • P` is the image of `P` under the ring automorphism `g`, i.e. the prime
`g(P)` of the book. -/
theorem smul_eq_map (g : G) (P : Ideal A) :
    g • P = P.map (MulSemiringAction.toRingHom G A g) :=
  Ideal.pointwise_smul_def P

/-! ### Incomparability in the integral extension `A^G ⊆ A` -/

/-- Two primes of `A` over the same prime of `A^G`, one containing the other, are equal. -/
theorem eq_of_le_of_under_eq {P Q : Ideal A} [P.IsPrime]
    (hle : P ≤ Q) (h : Q.under (FixedPoints.subring A G) = P.under (FixedPoints.subring A G)) :
    P = Q := by
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hle hne
  have hcontra := Ideal.IsIntegral.comap_lt_comap (R := FixedPoints.subring A G) (A := A) hlt
  rw [Ideal.under_def, Ideal.under_def] at h
  rw [h] at hcontra
  exact absurd hcontra (lt_irrefl _)

/-! ### Transitivity, following the book's proof -/

/-- **Atiyah–Macdonald 5.13, transitivity**, by the book's argument.

Let `P` and `Q` be primes of `A` contracting to the same prime of `A^G`. For `x ∈ P` the
invariant product `y = ∏_{σ ∈ G} σ x` is fixed by `G`, hence lies in `A^G`, and it lies in `P`
(one factor is `1 • x = x`); so `y ∈ P ∩ A^G ⊆ Q`, and primality of `Q` gives `σ x ∈ Q` for some
`σ`, i.e. `x ∈ σ⁻¹ • Q`. Thus `P ⊆ ⋃_{σ ∈ G} σ • Q`, and finite prime avoidance yields
`P ⊆ σ • Q` for a single `σ`. Both sides contract to the same prime of `A^G`, so incomparability
forces `P = σ • Q`. -/
theorem exists_smul_eq_of_under_eq_book {P Q : Ideal A} [hPprime : P.IsPrime]
    [hQprime : Q.IsPrime]
    (h : P.under (FixedPoints.subring A G) = Q.under (FixedPoints.subring A G)) :
    ∃ g : G, Q = g • P := by
  classical
  cases nonempty_fintype G
  have key : ∀ x ∈ P, ∃ g : G, x ∈ g • Q := by
    intro x hx
    have hmem : (∏ g : G, g • x) ∈ FixedPoints.subring A G := by
      intro g
      rw [Finset.smul_prod_perm]
    have hprodP : (∏ g : G, g • x) ∈ P := by
      rw [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ 1) (fun g : G => g • x),
        one_smul]
      exact P.mul_mem_left _ hx
    have hunder : (⟨∏ g : G, g • x, hmem⟩ : FixedPoints.subring A G) ∈
        P.under (FixedPoints.subring A G) :=
      Ideal.mem_comap.mpr hprodP
    have hprodQ : (∏ g : G, g • x) ∈ Q := by
      rw [h] at hunder
      exact Ideal.mem_comap.mp hunder
    obtain ⟨g, -, hg⟩ :=
      (Ideal.IsPrime.prod_mem_iff (p := Q) (s := Finset.univ) (x := fun g : G => g • x)).mp hprodQ
    exact ⟨g⁻¹, (Ideal.mem_inv_pointwise_smul_iff (a := g) (S := Q) (x := x)).mpr hg⟩
  have hsub : (P : Set A) ⊆ ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G),
      ((fun g : G => g • Q) g : Set A) := by
    intro x hx
    obtain ⟨g, hg⟩ := key x hx
    exact Set.mem_biUnion (Finset.mem_univ g) hg
  obtain ⟨g, -, hle⟩ :=
    (Ideal.subset_union_prime (s := Finset.univ) (f := fun g : G => g • Q) (a := 1) (b := 1)
      (I := P) (fun i _ _ _ => Ideal.IsPrime.smul i)).mp hsub
  have hunder' : (g • Q).under (FixedPoints.subring A G) = P.under (FixedPoints.subring A G) := by
    rw [Ideal.under_smul]
    exact h.symm
  have hPeq : P = g • Q := eq_of_le_of_under_eq (G := G) hle hunder'
  exact ⟨g⁻¹, by rw [hPeq, inv_smul_smul]⟩

/-- **Atiyah–Macdonald 5.13, transitivity**, via Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq`. -/
theorem exists_smul_eq_of_under_eq {P Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (h : P.under (FixedPoints.subring A G) = Q.under (FixedPoints.subring A G)) :
    ∃ g : G, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq (A := FixedPoints.subring A G) (B := A) (G := G)
    P Q (hP := hP) (hQ := hQ) h

/-- Two primes of `A` over the same prime of `A^G` are conjugate under `G`. -/
theorem exists_smul_eq_of_primesOver {p : Ideal (FixedPoints.subring A G)} [p.IsPrime]
    {P Q : Ideal A} (hP : P ∈ p.primesOver A) (hQ : Q ∈ p.primesOver A) :
    ∃ g : G, Q = g • P :=
  exists_smul_eq_of_under_eq (G := G) hP.1 hQ.1 (by rw [← hP.2.over, ← hQ.2.over])

/-- Book route, membership form: two primes of `A` over the same prime of `A^G` are conjugate. -/
theorem exists_smul_eq_of_primesOver_book {p : Ideal (FixedPoints.subring A G)} [p.IsPrime]
    {P Q : Ideal A} (hP : P ∈ p.primesOver A) (hQ : Q ∈ p.primesOver A) :
    ∃ g : G, Q = g • P :=
  exists_smul_eq_of_under_eq_book (G := G) (P := P) (Q := Q) (hPprime := hP.1) (hQprime := hQ.1)
    (by rw [← hP.2.over, ← hQ.2.over])

/-- Book route, finiteness: the primes of `A` over `𝔭` are finitely many, because they form one
`G`-orbit and `G` is finite. -/
theorem finite_primesOver_book (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (p.primesOver A).Finite := by
  obtain ⟨P, hP⟩ := nonempty_primesOver (A := A) (G := G) p
  refine Set.Finite.subset (Set.finite_range (fun g : G => g • P)) ?_
  rintro Q hQ
  obtain ⟨g, hg⟩ := exists_smul_eq_of_primesOver_book (G := G) hP hQ
  exact Set.mem_range.mpr ⟨g, hg.symm ▸ rfl⟩

/-- **Exercise 5.13, proved entirely along the book's route** (invariant products, finite prime
avoidance, incomparability). -/
theorem solution_book (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (∀ P ∈ p.primesOver A, ∀ Q ∈ p.primesOver A, ∃ g : G, Q = g • P) ∧
      (p.primesOver A).Finite :=
  ⟨fun _ hP _ hQ => exists_smul_eq_of_primesOver_book (G := G) hP hQ,
    finite_primesOver_book (A := A) (G := G) p⟩

/-- The set of primes of `A` over `𝔭` is exactly the orbit of any one of its elements. -/
theorem orbit_eq_primesOver (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] (P : Ideal A)
    (hP : P ∈ p.primesOver A) : MulAction.orbit G P = p.primesOver A :=
  Algebra.IsInvariant.orbit_eq_primesOver (A := FixedPoints.subring A G) (B := A) (G := G)
    p P (hP := hP.2) (hQ := hP.1)

/-! ### Finiteness -/

/-- **Atiyah–Macdonald 5.13, "in particular `P` is finite"**: there are only finitely many primes
of `A` contracting to a given prime of `A^G` (lying-over + one orbit under the finite group). -/
theorem finite_primesOver (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (p.primesOver A).Finite := by
  obtain ⟨P, hP⟩ := nonempty_primesOver (A := A) (G := G) p
  rw [← orbit_eq_primesOver (G := G) p P hP]
  exact Finite.finite_mulAction_orbit P

/-- The primes over `𝔭` are at most as numerous as the group: `|P| ≤ |G|`. -/
theorem ncard_primesOver_le (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (p.primesOver A).ncard ≤ Nat.card G := by
  obtain ⟨P, hP⟩ := nonempty_primesOver (A := A) (G := G) p
  rw [← orbit_eq_primesOver (G := G) p P hP]
  calc (MulAction.orbit G P).ncard
      = ((fun g : G => g • P) '' (Set.univ : Set G)).ncard := by
        rw [MulAction.orbit, Set.image_univ]
    _ ≤ (Set.univ : Set G).ncard := Set.ncard_image_le
    _ = Nat.card G := Set.ncard_univ G

/-! ### Exercise 5.13 -/

/-- **Atiyah–Macdonald, Exercise 5.13.** In the situation of Exercise 12, for a prime ideal `𝔭` of
the invariant subring `A^G`, the group `G` acts transitively on the set `P` of prime ideals of `A`
whose contraction is `𝔭`; in particular `P` is finite. -/
theorem solution (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (∀ P ∈ p.primesOver A, ∀ Q ∈ p.primesOver A, ∃ g : G, Q = g • P) ∧
      (p.primesOver A).Finite := by
  refine ⟨?_, finite_primesOver (A := A) (G := G) p⟩
  intro P hP Q hQ
  exact exists_smul_eq_of_primesOver (G := G) hP hQ

/-- Exercise 5.13 in the form of the book: the set of primes over `𝔭` is nonempty, is acted on by
`G`, is a single orbit, and is finite. -/
theorem solution' (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (p.primesOver A).Nonempty ∧
      (∀ P ∈ p.primesOver A, ∀ g : G, g • P ∈ p.primesOver A) ∧
      (∀ P ∈ p.primesOver A, MulAction.orbit G P = p.primesOver A) ∧
      (p.primesOver A).Finite :=
  ⟨nonempty_primesOver (A := A) (G := G) p,
    fun _P hP g => smul_mem_primesOver (G := G) hP g,
    fun P hP => orbit_eq_primesOver (G := G) p P hP,
    finite_primesOver (A := A) (G := G) p⟩

/-- Exercise 5.13 with the conclusion spelled out through contractions, as in the book: the set
of prime ideals of `A` whose contraction to `A^G` is `𝔭` is a single `G`-orbit, hence finite. -/
theorem solution_comap (p : Ideal (FixedPoints.subring A G)) [p.IsPrime] :
    (∀ P Q : Ideal A, P.IsPrime → Q.IsPrime →
        P.comap (algebraMap (FixedPoints.subring A G) A) = p →
        Q.comap (algebraMap (FixedPoints.subring A G) A) = p → ∃ g : G, Q = g • P) ∧
      {P : Ideal A | P.IsPrime ∧
        P.comap (algebraMap (FixedPoints.subring A G) A) = p}.Finite := by
  have hLies : ∀ P : Ideal A,
      (P.comap (algebraMap (FixedPoints.subring A G) A) = p ↔ P.LiesOver p) :=
    fun P => ⟨fun h => ⟨h.symm⟩, fun h => h.over.symm⟩
  have hset : {P : Ideal A | P.IsPrime ∧
      P.comap (algebraMap (FixedPoints.subring A G) A) = p} = p.primesOver A := by
    ext P
    simp only [Set.mem_ofPred_eq, Ideal.primesOver, hLies P]
  refine ⟨?_, ?_⟩
  · intro P Q hP hQ hPc hQc
    refine exists_smul_eq_of_under_eq (G := G) hP hQ ?_
    rw [Ideal.under_def, Ideal.under_def, hPc, hQc]
  · rw [hset]
    exact finite_primesOver (A := A) (G := G) p

end AtiyahMcdonald69.Ex_5_13

#print axioms AtiyahMcdonald69.Ex_5_13.solution
#print axioms AtiyahMcdonald69.Ex_5_13.solution'
#print axioms AtiyahMcdonald69.Ex_5_13.exists_smul_eq_of_under_eq_book
#print axioms AtiyahMcdonald69.Ex_5_13.finite_primesOver
#print axioms AtiyahMcdonald69.Ex_5_13.solution_comap
#print axioms AtiyahMcdonald69.Ex_5_13.ncard_primesOver_le
#print axioms AtiyahMcdonald69.Ex_5_13.solution_book
