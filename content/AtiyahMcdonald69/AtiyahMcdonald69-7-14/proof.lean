/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 7, Exercise 14.

**Textbook statement.**  Let `k` be an algebraically closed field and let `𝔞` be an ideal of the
polynomial ring `A = k[t₁,…,tₙ]`.  Then `I(V(𝔞)) = r(𝔞)`, where

* `V(𝔞) = {x ∈ kⁿ | f(x) = 0 for every f ∈ 𝔞}` is the set of common zeros of `𝔞`,
* `I(S) = {f ∈ A | f(x) = 0 for every x ∈ S}` is the ideal of polynomials vanishing on `S`,
* `r(𝔞) = {f ∈ A | fᵐ ∈ 𝔞 for some m}` is the radical of `𝔞`.

Natural-language solution (used as an independent cross-check):
<https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-14>
(source commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91).  It proves the two inclusions
`r(𝔞) ⊆ I(V(𝔞))` and `I(V(𝔞)) ⊆ r(𝔞)`.  For the second one, given `f ∉ r(𝔞)`, it

1. picks a prime `𝔭 ⊇ 𝔞` with `f ∉ 𝔭` (using `r(𝔞) = ⋂ {𝔭 prime | 𝔞 ⊆ 𝔭}`),
2. forms the finitely generated `k`-algebra `C = (A/𝔭)_f`, which is nonzero, and takes a maximal
   ideal `𝔪` of it (equivalently: a maximal ideal of `A/𝔭` not containing the image of `f`,
   which is what the localization buys),
3. uses the weak Nullstellensatz in the form `C/𝔪 ≅ k`: the images of `t₁,…,tₙ` give a point
   `x ∈ kⁿ`, and `x ∈ V(𝔞)` while `f(x) ≠ 0`.

Below, all of this is formalized.  The localization step (2) is realized by its equivalent
Jacobson-ring form "the radical is the intersection of the maximal ideals above it"
(`Ideal.radical_eq_jacobson` plus the instance `IsJacobsonRing (MvPolynomial ι k)`), and step
(3) by `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`.  The constructions `V(𝔞)` and
`I(S)` of the exercise are defined explicitly from the evaluation map; they are also shown to
agree with Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`.

Verification: `/opt/lean/bin/lean -DwarningAsError=true answer.lean`; the `#print axioms`
commands at the end show that no `sorryAx` and no new axiom is used.
-/
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

namespace AtiyahMcdonald69.Ex_7_14

variable {k : Type*} [Field k]
variable {σ : Type*}

/-! ### The two constructions of the exercise: `V(𝔞)` and `I(V)` -/

/-- `V(𝔞) ⊆ k^σ`: the set of points at which every element of the ideal `𝔞` of `k[t₁,…,tₙ]`
vanishes. -/
def zeroSet (𝔞 : Ideal (MvPolynomial σ k)) : Set (σ → k) :=
  {x | ∀ f ∈ 𝔞, MvPolynomial.eval x f = 0}

@[simp]
theorem mem_zeroSet {𝔞 : Ideal (MvPolynomial σ k)} {x : σ → k} :
    x ∈ zeroSet 𝔞 ↔ ∀ f ∈ 𝔞, MvPolynomial.eval x f = 0 := Iff.rfl

/-- `I(S)`: the ideal of all polynomials vanishing at every point of a set `S ⊆ k^σ`. -/
def idealOfSet (S : Set (σ → k)) : Ideal (MvPolynomial σ k) where
  carrier := {f | ∀ x ∈ S, MvPolynomial.eval x f = 0}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

@[simp]
theorem mem_idealOfSet {S : Set (σ → k)} {f : MvPolynomial σ k} :
    f ∈ idealOfSet S ↔ ∀ x ∈ S, MvPolynomial.eval x f = 0 := Iff.rfl

/-! ### `V` and `I` agree with the corresponding constructions of Mathlib -/

theorem zeroSet_eq_zeroLocus (𝔞 : Ideal (MvPolynomial σ k)) :
    zeroSet 𝔞 = MvPolynomial.zeroLocus k 𝔞 := rfl

theorem idealOfSet_eq_vanishingIdeal (S : Set (σ → k)) :
    idealOfSet S = MvPolynomial.vanishingIdeal k S := by
  ext f
  simp [mem_idealOfSet, MvPolynomial.mem_vanishingIdeal_iff]

/-! ### First inclusion of the exercise: `r(𝔞) ⊆ I(V(𝔞))` -/

/-- `I(S)` is a radical ideal: if `f²` vanishes on `S`, then so does `f`. -/
theorem isRadical_idealOfSet (S : Set (σ → k)) : (idealOfSet S).IsRadical := by
  rw [Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)]
  intro f hf x hx
  have h : MvPolynomial.eval x f * MvPolynomial.eval x f = 0 := by
    simpa [pow_two, map_mul] using hf x hx
  exact mul_self_eq_zero.1 h

/-- Every element of `r(𝔞)` vanishes on `V(𝔞)`, i.e. `r(𝔞) ⊆ I(V(𝔞))`. -/
theorem radical_le_idealOfSet_zeroSet (𝔞 : Ideal (MvPolynomial σ k)) :
    𝔞.radical ≤ idealOfSet (zeroSet 𝔞) := by
  refine (isRadical_idealOfSet (zeroSet 𝔞)).radical_le_iff.2 ?_
  intro f hf x hx
  exact hx f hf

/-! ### The weak Nullstellensatz ingredient of the proof (`C/𝔪 ≅ k`) -/

/-- The weak Nullstellensatz: every maximal ideal of `k[t₁,…,tₙ]`, with `k` algebraically
closed, is the ideal of polynomials vanishing at a single point of `kⁿ`.  This is the form in
which the exercise uses that the residue field of a maximal ideal of a finitely generated
`k`-algebra is `k`. -/
theorem exists_maximal_eq_idealOfSet_singleton [IsAlgClosed k] [Finite σ]
    {M : Ideal (MvPolynomial σ k)} (hM : M.IsMaximal) :
    ∃ x : σ → k, M = idealOfSet {x} := by
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hM
  exact ⟨x, hx.trans (idealOfSet_eq_vanishingIdeal {x}).symm⟩

/-- The weak Nullstellensatz: distinct points of `kⁿ` have distinct vanishing ideals. -/
theorem injective_point_vanishingIdeal [IsAlgClosed k] [Finite σ] :
    Function.Injective fun x : σ → k =>
      (MvPolynomial.vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) := by
  intro x y hxy
  funext i
  have h : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      (MvPolynomial.vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hxy' : (MvPolynomial.vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) =
      MvPolynomial.vanishingIdeal k {y} := hxy
  rw [hxy', MvPolynomial.mem_vanishingIdeal_singleton_iff] at h
  exact (sub_eq_zero.1 (by simpa using h)).symm

/-- The weak Nullstellensatz: the maximal ideals of `k[t₁,…,tₙ]` are exactly the vanishing
ideals of points of `kⁿ`. -/
theorem range_point_vanishingIdeal [IsAlgClosed k] [Finite σ] :
    Set.range (fun x : σ → k =>
      (MvPolynomial.vanishingIdeal k {x} : Ideal (MvPolynomial σ k))) = {M | M.IsMaximal} := by
  ext M
  constructor
  · rintro ⟨x, rfl⟩
    exact MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨x, rfl⟩
  · intro hM
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hM
    exact ⟨x, hx.symm⟩

/-- The step `C/𝔪 ≅ k` of the source proof, for a maximal ideal `M` of `k[t₁,…,tₙ]`: the
residue field of `M` is `k`. -/
theorem quotient_maximal_algEquiv [IsAlgClosed k] [Finite σ] (M : Ideal (MvPolynomial σ k))
    (hM : M.IsMaximal) : Nonempty ((MvPolynomial σ k ⧸ M) ≃ₐ[k] k) := by
  obtain ⟨x, hxM⟩ := exists_maximal_eq_idealOfSet_singleton (k := k) hM
  rw [hxM]
  have hker : idealOfSet ({x} : Set (σ → k)) = RingHom.ker (MvPolynomial.aeval x) := by
    ext f
    simp [mem_idealOfSet, RingHom.mem_ker]
  rw [hker]
  refine ⟨Ideal.quotientKerAlgEquivOfSurjective (R₁ := k) (A := MvPolynomial σ k) (B := k)
    (f := MvPolynomial.aeval x) ?_⟩
  intro c
  exact ⟨MvPolynomial.C c, by simp⟩

/-! ### Second inclusion of the exercise: `I(V(𝔞)) ⊆ r(𝔞)` -/

/-- `I(V(𝔞)) ⊆ r(𝔞)`.  As in the proof of the exercise: `r(𝔞)` is the intersection of the
maximal ideals above `𝔞`; each such maximal ideal `J` is `I({x})` for a point `x` by the weak
Nullstellensatz, and that point lies in `V(𝔞)`, so a polynomial vanishing on `V(𝔞)` vanishes at
`x`, i.e. belongs to `J`. -/
theorem idealOfSet_zeroSet_le_radical [IsAlgClosed k] [Finite σ]
    (𝔞 : Ideal (MvPolynomial σ k)) : idealOfSet (zeroSet 𝔞) ≤ 𝔞.radical := by
  rw [Ideal.radical_eq_jacobson]
  refine le_sInf ?_
  rintro J ⟨h𝔞J, hJmax⟩
  obtain ⟨x, hxJ⟩ := exists_maximal_eq_idealOfSet_singleton (k := k) hJmax
  rw [hxJ] at h𝔞J ⊢
  intro f hf
  rw [mem_idealOfSet] at hf ⊢
  have hx : x ∈ zeroSet 𝔞 := fun p hp => (mem_idealOfSet.1 (h𝔞J hp)) x rfl
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hf x hx

/-- **The Nullstellensatz statement of the exercise.**  If `k` is an algebraically closed field
and `𝔞` is an ideal of `k[t₁,…,tₙ]`, then `I(V(𝔞)) = r(𝔞)`. -/
theorem idealOfSet_zeroSet_eq_radical [IsAlgClosed k] [Finite σ]
    (𝔞 : Ideal (MvPolynomial σ k)) : idealOfSet (zeroSet 𝔞) = 𝔞.radical :=
  le_antisymm (idealOfSet_zeroSet_le_radical 𝔞) (radical_le_idealOfSet_zeroSet 𝔞)

/-! ### The exercise -/

/-- **Atiyah–Macdonald, Chapter 7, Exercise 14**, in the shape of the book: `k` algebraically
closed, `n` a natural number, `𝔞` an ideal of `k[t₁,…,tₙ]`; then `I(V(𝔞)) = r(𝔞)`. -/
theorem exercise_7_14 [IsAlgClosed k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin n) k)) :
    idealOfSet (zeroSet 𝔞) = 𝔞.radical :=
  idealOfSet_zeroSet_eq_radical 𝔞

/-- The exercise, as the main deliverable of this file. -/
theorem solution [IsAlgClosed k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin n) k)) :
    idealOfSet (zeroSet 𝔞) = 𝔞.radical :=
  exercise_7_14 n 𝔞

/-- Elementwise form of the exercise: `f` vanishes on `V(𝔞)` if and only if `f ∈ r(𝔞)`. -/
theorem exercise_7_14_iff [IsAlgClosed k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) :
    (∀ x : Fin n → k, x ∈ zeroSet 𝔞 → MvPolynomial.eval x f = 0) ↔ f ∈ 𝔞.radical := by
  rw [← exercise_7_14 n 𝔞, mem_idealOfSet]

/-- Elementwise form with the quantifiers of the textbook: for every polynomial `f` in
`k[t₁,…,tₙ]`, `f` vanishes at every common zero of `𝔞` if and only if some power of `f` lies in
`𝔞`. -/
theorem exercise_7_14_iff' [IsAlgClosed k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) :
    (∀ x : Fin n → k, (∀ g ∈ 𝔞, MvPolynomial.eval x g = 0) → MvPolynomial.eval x f = 0) ↔
      f ∈ 𝔞.radical := by
  rw [← exercise_7_14_iff n 𝔞]
  simp only [mem_zeroSet]

/-- The exercise with both sides written out as sets of polynomials, matching the textbook
statement literally: the set of polynomials vanishing at every common zero of `𝔞` is exactly the
set of `f` with `fᵐ ∈ 𝔞` for some `m`. -/
theorem exercise_7_14_set_eq [IsAlgClosed k] (n : ℕ) (𝔞 : Ideal (MvPolynomial (Fin n) k)) :
    {f : MvPolynomial (Fin n) k |
        ∀ x : Fin n → k, (∀ g ∈ 𝔞, MvPolynomial.eval x g = 0) → MvPolynomial.eval x f = 0} =
      {f : MvPolynomial (Fin n) k | f ∈ 𝔞.radical} := by
  ext f
  exact exercise_7_14_iff' n 𝔞 f

/-- The exercise in the form of Mathlib's own Nullstellensatz constructions. -/
theorem exercise_7_14_vanishingIdeal_zeroLocus [IsAlgClosed k] (n : ℕ)
    (𝔞 : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k 𝔞) = 𝔞.radical := by
  rw [← idealOfSet_eq_vanishingIdeal, ← zeroSet_eq_zeroLocus, exercise_7_14]

/-! ### Two consequences, as an audit of the constructions -/

/-- `V(√𝔞) = V(𝔞)`: passing to the radical does not change the variety.  (This needs no
hypothesis on `k`.) -/
theorem zeroSet_radical (𝔞 : Ideal (MvPolynomial σ k)) :
    zeroSet 𝔞.radical = zeroSet 𝔞 := by
  refine Set.Subset.antisymm (fun x hx f hf => hx f (Ideal.le_radical hf)) ?_
  intro x hx f hf
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hf
  have h : MvPolynomial.eval x f ^ m = 0 := by
    rw [← map_pow]
    exact hx (f ^ m) hm
  exact (pow_eq_zero_iff'.1 h).1

/-- Consequence (the weak Nullstellensatz in the form of A–M Exercise 5.17): over an
algebraically closed field every proper ideal of `k[t₁,…,tₙ]` has a common zero, i.e.
`V(𝔞) = ∅ ↔ 𝔞 = ⊤`. -/
theorem zeroSet_eq_empty_iff [IsAlgClosed k] [Finite σ] (𝔞 : Ideal (MvPolynomial σ k)) :
    zeroSet 𝔞 = ∅ ↔ 𝔞 = ⊤ := by
  constructor
  · intro h
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : MvPolynomial σ k) ∈ idealOfSet (zeroSet 𝔞) := by
      rw [h]
      simp [mem_idealOfSet]
    rw [idealOfSet_zeroSet_eq_radical] at h1
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 h1
    simpa using hm
  · intro h
    rw [h]
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have h1 : MvPolynomial.eval x (1 : MvPolynomial σ k) = 0 := hx 1 (by simp)
    rw [map_one] at h1
    exact one_ne_zero h1

/-! ### The contrapositive step of the proof, following the source

If `f ∉ r(𝔞)`, the source produces a point of `V(𝔞)` at which `f` does not vanish.  The three
lemmas below are the three moves of that argument; the last theorem assembles them. -/

/-- Move 1 of the proof: `r(𝔞)` is the intersection of the primes above `𝔞`, so a polynomial
outside `r(𝔞)` avoids some such prime. -/
theorem exists_prime_of_notMem_radical {𝔞 : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : f ∉ 𝔞.radical) :
    ∃ P : Ideal (MvPolynomial σ k), P.IsPrime ∧ 𝔞 ≤ P ∧ f ∉ P := by
  by_contra h
  apply hf
  rw [Ideal.radical_eq_sInf]
  exact Ideal.mem_sInf.mpr fun P hP => by_contra fun hfP => h ⟨P, hP.2, hP.1, hfP⟩

/-- Move 2 of the proof, in the general form provided by Jacobson rings: the radical is the
intersection of the maximal ideals above the ideal, so a polynomial outside the radical avoids
some maximal ideal above the ideal.  This is what the localization `(A/𝔭)_f` and a maximal
ideal `𝔪` of it produce, since the contraction of `𝔪` is maximal in `A/𝔭`. -/
theorem exists_maximal_of_notMem_radical {R : Type*} [CommRing R] [IsJacobsonRing R]
    {I : Ideal R} {f : R} (hf : f ∉ I.radical) :
    ∃ M : Ideal R, I ≤ M ∧ M.IsMaximal ∧ f ∉ M := by
  by_contra h
  apply hf
  rw [Ideal.radical_eq_jacobson]
  exact Ideal.mem_sInf.mpr fun M hM => by_contra fun hfM => h ⟨M, hM.1, hM.2, hfM⟩

/-- Move 2 of the proof for a domain: a nonzero element of a Jacobson domain avoids some
maximal ideal. -/
theorem exists_maximal_notMem_of_ne_zero {R : Type*} [CommRing R] [IsDomain R] [IsJacobsonRing R]
    {f : R} (hf : f ≠ 0) : ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M := by
  have hbot : (⊥ : Ideal R).radical = ⊥ := le_antisymm Ideal.isRadical_bot bot_le
  have h : f ∉ (⊥ : Ideal R).radical := by
    rw [hbot]
    simpa using hf
  obtain ⟨M, -, hM, hfM⟩ := exists_maximal_of_notMem_radical h
  exact ⟨M, hM, hfM⟩

/-- **The contrapositive of the exercise, along the lines of the source proof.**  If `f ∉ r(𝔞)`,
then `f` fails to vanish at some point of `V(𝔞)`. -/
theorem exists_zeroSet_eval_ne_zero_of_notMem_radical [IsAlgClosed k] [Finite σ]
    {𝔞 : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k} (hf : f ∉ 𝔞.radical) :
    ∃ x : σ → k, x ∈ zeroSet 𝔞 ∧ MvPolynomial.eval x f ≠ 0 := by
  -- move 1: a prime `P ⊇ 𝔞` with `f ∉ P`
  obtain ⟨P, hP, h𝔞P, hfP⟩ := exists_prime_of_notMem_radical hf
  have hPp : P.IsPrime := hP
  -- move 2: a maximal ideal of the domain `A ⧸ P` avoiding the image of `f`
  let q : MvPolynomial σ k →+* (MvPolynomial σ k ⧸ P) := Ideal.Quotient.mk P
  have hq : q f ≠ 0 := fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.1 h)
  obtain ⟨Mbar, hMbar, hfMbar⟩ := exists_maximal_notMem_of_ne_zero hq
  have hMbm : Mbar.IsMaximal := hMbar
  -- contract it to a maximal ideal of `k[t₁,…,tₙ]` containing `P`
  let M : Ideal (MvPolynomial σ k) := Mbar.comap q
  have hMmax : M.IsMaximal := Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  have hfM : f ∉ M := fun h => hfMbar h
  have hPM : P ≤ M := fun p hp =>
    Ideal.mem_comap.2 (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]; exact Mbar.zero_mem)
  -- move 3: realize it as the vanishing ideal of a point
  obtain ⟨x, hxM⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hMmax
  refine ⟨x, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (MvPolynomial.vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) :=
      hxM ▸ hPM (h𝔞P hg)
    simpa using (MvPolynomial.mem_vanishingIdeal_singleton_iff x g).1 hg'
  · intro hfx
    apply hfM
    rw [hxM, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simpa using hfx

/-- The exercise's key step, in the form of an existential avoidance statement: if `f ∈ k[t]`
does not lie in `r(𝔞)`, there is a point of `kⁿ` at which all of `𝔞` vanishes and `f` does not. -/
theorem exists_point_of_notMem_radical [IsAlgClosed k] [Finite σ]
    {𝔞 : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k} (hf : f ∉ 𝔞.radical) :
    ∃ x : σ → k, (∀ g ∈ 𝔞, MvPolynomial.eval x g = 0) ∧ MvPolynomial.eval x f ≠ 0 := by
  obtain ⟨x, hx, hfx⟩ := exists_zeroSet_eval_ne_zero_of_notMem_radical hf
  exact ⟨x, hx, hfx⟩

end AtiyahMcdonald69.Ex_7_14

#print axioms AtiyahMcdonald69.Ex_7_14.solution
#print axioms AtiyahMcdonald69.Ex_7_14.exercise_7_14
#print axioms AtiyahMcdonald69.Ex_7_14.exercise_7_14_iff
#print axioms AtiyahMcdonald69.Ex_7_14.exercise_7_14_iff'
#print axioms AtiyahMcdonald69.Ex_7_14.exercise_7_14_set_eq
#print axioms AtiyahMcdonald69.Ex_7_14.exercise_7_14_vanishingIdeal_zeroLocus
#print axioms AtiyahMcdonald69.Ex_7_14.exists_zeroSet_eval_ne_zero_of_notMem_radical
#print axioms AtiyahMcdonald69.Ex_7_14.exists_point_of_notMem_radical
#print axioms AtiyahMcdonald69.Ex_7_14.range_point_vanishingIdeal
#print axioms AtiyahMcdonald69.Ex_7_14.injective_point_vanishingIdeal
#print axioms AtiyahMcdonald69.Ex_7_14.quotient_maximal_algEquiv
#print axioms AtiyahMcdonald69.Ex_7_14.zeroSet_radical
#print axioms AtiyahMcdonald69.Ex_7_14.zeroSet_eq_empty_iff
