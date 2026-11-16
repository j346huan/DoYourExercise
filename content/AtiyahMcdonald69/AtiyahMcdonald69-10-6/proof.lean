/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter X (Completions), Exercise 6.

**Original statement** (as printed in the text; quoted verbatim in B. Carlson's
`Exercises to Atiyah and Macdonald's Introduction to Commutative Algebra`, Ex. 10.6, which
is the reference used here since the book itself is not available in this VM):

  "Let `A` be a Noetherian ring and `𝔞` an ideal in `A`. Prove that `𝔞` is contained in the
  Jacobson radical of `A` if and only if every maximal ideal of `A` is closed for the
  `𝔞`-topology. (A Noetherian topological ring in which the topology is defined by an
  ideal contained in the Jacobson radical is called a Zariski ring. Examples are local
  rings and (by (10.15)(iv)) `𝔞`-adic completions.)"

The "`𝔞`-topology" of Chapter X is the topology on `A` for which the ideals `𝔞ⁿ` form a
basis of neighbourhoods of `0`; in Mathlib this is `Ideal.adicTopology 𝔞`, and `IsAdic 𝔞`
records that a given topological structure is that topology.

**Coverage.**  `solution` is the exercise's iff with all hypotheses of the book (`A`
Noetherian, `𝔞` an ideal of `A`, "closed" taken in the `𝔞`-adic topology, `J(A)` taken to be
the intersection of all maximal ideals, here `Ideal.jacobson ⊥`, which is `Ring.jacobson A`
by `Ideal.jacobson_bot`).  The parenthetical sentence of the book *defines* Zariski rings
and lists examples.  The definition needs no formalization (Mathlib has no `ZariskiRing`
predicate, and introducing one would add bookkeeping but no mathematics), but its first
example is proved: a local Noetherian ring is a Zariski ring, i.e. its maximal ideal is
closed for the `𝔪`-adic topology (`isClosed_maximalIdeal_adic`, using `𝔪 = J(A)`).  The
remaining example — that `𝔞`-adic completions are Zariski rings, which the book attributes
to (10.15)(iv) — is *not* formalized here: it is a separate result about `AdicCompletion`,
not part of the exercise's assertion.

**Statement adaptations / audit.**
* The book's hypothesis that `A` is Noetherian is retained verbatim in `solution`, although
  the argument does not use it; theorem `general` states the same result for an arbitrary
  commutative ring with an `𝔞`-adic topology.  No hypothesis is dropped or strengthened.
* No dimension, finiteness or non-degeneracy assumption is hidden: the zero ring has no
  maximal ideals, the right-hand side is then vacuous, and the left-hand side holds since
  `⊥ ≤ Ideal.jacobson ⊥`; for `𝔞 = ⊥` the topology is discrete, every set is closed, and
  `⊥` lies below every ideal.  Both cases are covered by the general proof.

**Proof strategy.**  Step 1 (`closure_eq_iInter`) resolves the construction the source
solution leaves implicit: in the `𝔞`-adic topology the closure of an ideal `𝔟` is
`⋂ₙ (𝔟 + 𝔞ⁿ)`.  Step 2: for a maximal ideal `𝔪` one shows `𝔪` closed ↔ `𝔞 ≤ 𝔪`.
  * If `𝔞 ≤ 𝔪`, then `𝔪 + 𝔞ⁿ = 𝔪` for all `n`, so the closure of `𝔪` is `𝔪`.
  * If `𝔞 ≰ 𝔪`, then `𝔪 < 𝔪 + 𝔞`, so `𝔪 + 𝔞 = ⊤` and hence `𝔪 + 𝔞ⁿ = ⊤` for every `n`
    (source solution: "the image of `𝔞` in the field `A/𝔪` is the whole field, and the
    same holds for every power"); thus the closure is all of `A`, and `𝔪 ≠ ⊤` is not
    closed.  This is `closure_eq_univ_of_not_le`.
  * As an independent second route to the failure of closedness, `one_mem_closure_of_not_le`
    exhibits `1` as a limit point of `𝔪` using maximality rather than the closure formula:
    if `1 - y * a ∈ 𝔪` with `a ∈ 𝔞`, then `1 - (y * a)ⁿ ∈ 𝔪` while `(y * a)ⁿ ∈ 𝔞ⁿ`.
Step 3: `𝔞 ≤ J(A) = ⋂ {maximal ideals}` iff `𝔞 ≤ 𝔪` for every maximal ideal `𝔪`
(`le_of_le_jacobson`), which assembles the two directions in `general` and `solution`.

Natural-language source proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-10-6

Lean toolchain: the Mathlib oleans installed in this VM are built against Lean 4.33.1, so
this file is checked with `/opt/lean/bin/lean` (the elan default `lean`, 4.35.0, cannot read
them).  Verified with `lean -DwarningAsError=true`; there is no `sorry`, `admit`, custom
axiom or extra premise anywhere in the file, and
`#print axioms AtiyahMcdonald69.Ex_10_6.solution` reports only
`[propext, Classical.choice, Quot.sound]` (see `check_axioms.lean`).
-/
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.Noetherian.Defs

namespace AtiyahMcdonald69.Ex_10_6

open Set Filter

variable {A : Type*} [CommRing A]

/-! ## The `𝔞`-adic topology -/

/-- If `1 - b ∈ 𝔪` then `1 - b ^ n ∈ 𝔪` for every `n ≥ 1` (geometric telescoping). -/
theorem one_sub_pow_mem {𝔪 : Ideal A} {b : A} (h : 1 - b ∈ 𝔪) (n : ℕ) :
    1 - b ^ (n + 1) ∈ 𝔪 := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
    have hstep : (1 : A) - b ^ (k + 1 + 1) = (1 - b ^ (k + 1)) + b ^ (k + 1) * (1 - b) := by
      rw [pow_succ b (k + 1)]
      ring
    rw [hstep]
    exact 𝔪.add_mem ih (𝔪.mul_mem_left _ h)

/-- In the `𝔞`-adic topology the closure of an ideal `𝔟` is `⋂ₙ (𝔟 + 𝔞ⁿ)`. -/
theorem closure_eq_iInter [TopologicalSpace A] {𝔞 : Ideal A} (h𝔞 : IsAdic 𝔞)
    (𝔟 : Ideal A) :
    closure (𝔟 : Set A) = ⋂ n : ℕ, ((𝔟 + 𝔞 ^ n : Ideal A) : Set A) := by
  ext x
  rw [mem_iInter, mem_closure_iff_nhds_basis (h𝔞.hasBasis_nhds x)]
  constructor
  · rintro h n
    obtain ⟨y, hy, z, hz, hzy⟩ := h n trivial
    have hx : x = y - z := by rw [← hzy]; ring
    rw [hx]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hy) (Ideal.mem_sup_right hz)
  · intro h n _
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp (h n)
    exact ⟨b, hb, -c, neg_mem hc, by rw [← hbc]; ring⟩

/-! ## Two proofs that a maximal ideal not containing `𝔞` is not closed -/

/-- The source solution's argument: if `𝔞 ≰ 𝔪` and `𝔪` is maximal then `𝔪` is dense, since
`𝔪 + 𝔞ⁿ = ⊤` for every `n`. -/
theorem closure_eq_univ_of_not_le [TopologicalSpace A] {𝔞 : Ideal A} (h𝔞 : IsAdic 𝔞)
    {𝔪 : Ideal A} (h𝔪 : 𝔪.IsMaximal) (hle : ¬ 𝔞 ≤ 𝔪) :
    closure (𝔪 : Set A) = univ := by
  have hlt : 𝔪 < 𝔪 ⊔ 𝔞 := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact hle (heq ▸ le_sup_right)
  have hsup : 𝔪 ⊔ 𝔞 = ⊤ := h𝔪.out.2 _ hlt
  have htop : ∀ n : ℕ, 𝔪 ⊔ 𝔞 ^ n = ⊤ := fun n => Ideal.sup_pow_eq_top hsup
  rw [closure_eq_iInter h𝔞, Set.eq_univ_iff_forall]
  intro x
  rw [mem_iInter]
  intro n
  change x ∈ ((𝔪 ⊔ 𝔞 ^ n : Ideal A) : Set A)
  rw [htop n]
  exact Submodule.mem_top

/-- Independent second route to the same conclusion: if `𝔞 ≰ 𝔪` and `𝔪` is maximal, then
`1` is a limit point of `𝔪`, so `𝔪` is not closed. -/
theorem one_mem_closure_of_not_le [TopologicalSpace A] {𝔞 : Ideal A} (h𝔞 : IsAdic 𝔞)
    {𝔪 : Ideal A} (h𝔪 : 𝔪.IsMaximal) (hle : ¬ 𝔞 ≤ 𝔪) :
    (1 : A) ∈ closure (𝔪 : Set A) := by
  obtain ⟨a, ha𝔞, ha𝔪⟩ := Set.not_subset.mp hle
  obtain ⟨y, i, hi𝔪, hyi⟩ := h𝔪.exists_inv ha𝔪
  have hb𝔞 : y * a ∈ 𝔞 := 𝔞.mul_mem_left y ha𝔞
  have h1b : 1 - y * a ∈ 𝔪 := by
    have h : (1 : A) - y * a = i := by rw [← hyi]; ring
    rwa [h]
  rw [mem_closure_iff_nhds_basis (h𝔞.hasBasis_nhds 1)]
  intro n _
  cases n with
  | zero => exact ⟨0, 𝔪.zero_mem, -1, by simp, by ring⟩
  | succ m =>
    exact ⟨1 - (y * a) ^ (m + 1), one_sub_pow_mem h1b m,
      -((y * a) ^ (m + 1)), neg_mem (𝔞.pow_mem_pow hb𝔞 (m + 1)), by ring⟩

/-! ## The exercise -/

/-- In the `𝔞`-adic topology, a maximal ideal `𝔪` is closed if and only if `𝔞 ≤ 𝔪`. -/
theorem isClosed_isMaximal_iff [TopologicalSpace A] {𝔞 : Ideal A} (h𝔞 : IsAdic 𝔞)
    {𝔪 : Ideal A} (h𝔪 : 𝔪.IsMaximal) : IsClosed (𝔪 : Set A) ↔ 𝔞 ≤ 𝔪 := by
  constructor
  · intro hc
    by_contra hle
    have hdense := closure_eq_univ_of_not_le h𝔞 h𝔪 hle
    have h1 : (1 : A) ∈ (𝔪 : Set A) := by
      rw [← hc.closure_eq, hdense]
      exact mem_univ 1
    exact h𝔪.ne_top (Ideal.eq_top_iff_one 𝔪 |>.mpr h1)
  · intro hle
    rw [← closure_subset_iff_isClosed]
    intro x hx
    rw [mem_closure_iff_nhds_basis (h𝔞.hasBasis_nhds x)] at hx
    obtain ⟨y, hy, z, hz, hzy⟩ := hx 1 trivial
    have hz𝔞 : z ∈ 𝔞 := by simpa using hz
    have hx' : x = y - z := by rw [← hzy]; ring
    rw [hx']
    exact Ideal.sub_mem _ hy (hle hz𝔞)

/-- If `𝔞 ≤ J(A)` (the Jacobson radical) then `𝔞` is contained in every maximal ideal. -/
theorem le_of_le_jacobson {𝔞 𝔪 : Ideal A} (h : 𝔞 ≤ Ideal.jacobson (⊥ : Ideal A))
    (h𝔪 : 𝔪.IsMaximal) : 𝔞 ≤ 𝔪 := by
  refine le_trans h ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, h𝔪⟩

/-- Exercise 10.6 in its general form, with no Noetherian hypothesis: for a topology that
is `𝔞`-adic, `𝔞` lies in the Jacobson radical iff every maximal ideal is closed. -/
theorem general [TopologicalSpace A] {𝔞 : Ideal A} (h𝔞 : IsAdic 𝔞) :
    𝔞 ≤ Ideal.jacobson (⊥ : Ideal A) ↔
      ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → IsClosed (𝔪 : Set A) := by
  constructor
  · intro h 𝔪 h𝔪
    exact (isClosed_isMaximal_iff h𝔞 h𝔪).mpr (le_of_le_jacobson h h𝔪)
  · intro h
    rw [Ideal.jacobson]
    refine le_sInf ?_
    rintro 𝔪 ⟨-, h𝔪⟩
    exact (isClosed_isMaximal_iff h𝔞 h𝔪).mp (h 𝔪 h𝔪)

/-- **Atiyah–Macdonald, Chapter X, Exercise 6.**  For a Noetherian ring `A` and an ideal
`𝔞` of `A`, `𝔞` is contained in the Jacobson radical of `A` if and only if every maximal
ideal of `A` is closed for the `𝔞`-adic topology. -/
theorem solution [IsNoetherianRing A] (𝔞 : Ideal A) :
    𝔞 ≤ Ideal.jacobson (⊥ : Ideal A) ↔
      ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → @IsClosed A 𝔞.adicTopology (𝔪 : Set A) :=
  @general A _ 𝔞.adicTopology 𝔞 rfl

/-- The same statement with the Jacobson radical written as `Ring.jacobson A`. -/
theorem solution_ringJacobson [IsNoetherianRing A] (𝔞 : Ideal A) :
    𝔞 ≤ Ring.jacobson A ↔
      ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → @IsClosed A 𝔞.adicTopology (𝔪 : Set A) := by
  rw [← Ideal.jacobson_bot]
  exact solution 𝔞

/-- The book's first example in the parenthetical: a local ring is a Zariski ring, i.e. its
maximal ideal is closed in the `𝔪`-adic topology (because `𝔪 = J(A)`). -/
theorem isClosed_maximalIdeal_adic [IsLocalRing A] [IsNoetherianRing A] :
    @IsClosed A (IsLocalRing.maximalIdeal A).adicTopology
      ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) :=
  (solution (IsLocalRing.maximalIdeal A)).mp (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
    _ (IsLocalRing.maximalIdeal.isMaximal A)

end AtiyahMcdonald69.Ex_10_6
