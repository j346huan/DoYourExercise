import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter VI, Exercise 2

Statement (site tag `6.2`, i.e. Chapter 6, Exercise 2 — the site numbers the book's
exercises, cf. `5.35`, `6.1`, `6.3`, `6.4`):

> Let `M` be an `A`-module. If every non-empty set of finitely generated
> submodules of `M` has a maximal element, then `M` is Noetherian.

Natural-language proof (advisory only):
<https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-6-2>

## Source audit

* The reference text `.scratch/reference/atiyah-macdonald-original.txt` stops
  inside Chapter VI (after Corollary 6.11), so the Chapter VI exercise list is
  not in it. The statement above is the exercise list's wording as reproduced by
  A. Allan, *Solutions to Atiyah–Macdonald* (`.scratch/reference/atiyah-solutions.txt`,
  §6.2); it is the statement that the site's `-6-2/proof.tex` establishes, and the
  two readings agree.
* Tag/statement trap: the book also has a *Proposition* 6.2 ("`M` is a Noetherian
  `A`-module ⇔ every submodule of `M` is finitely generated"). It is a different
  assertion with a similar proof, and it is *not* the tagged item; the tags are
  chapter.exercise numbers. The proposition is used here only as an auxiliary
  (`prop_6_2` below), exactly as the site's final sentence "so `M` is Noetherian"
  uses it.
* The exercise's hypothesis is formally weaker than the book's maximal condition:
  it is imposed only on sets of *finitely generated* submodules.
  `maximalConditionOnFG_of_maximalCondition` records the implication between the
  two hypotheses.
* The site's proof is complete for the exercise, but terse in two places: it reads
  the maximal member off the hypothesis (correct here, since the hypothesis *is*
  the maximal condition restricted to finitely generated submodules), and its last
  sentence "so `M` is Noetherian" is Proposition 6.2, invoked silently. Both
  steps are separated out here (`fg_of_maximalConditionOnFG`, `prop_6_2`).

## Formalisation notes

* The book defines a Noetherian module by the ascending chain condition (a.c.c.)
  on submodules (Chapter VI, p. 74). Mathlib's `IsNoetherian R M` is instead
  *defined* as "every submodule is finitely generated" (`isNoetherian_def`), so
  the a.c.c. is introduced here as `AscendingChainCondition`, the book's
  definition, and shown equivalent to finite generation of all submodules
  (`prop_6_2`). `isNoetherian_iff_acc` records the compatibility with Mathlib's
  class, and `solution_isNoetherian` states the exercise with that class.
* The `MaximalConditionOnFG` is the exercise's hypothesis; `MaximalCondition` is
  the book's maximal condition 6.1 (ii), for comparison.

## Main results

* `solution` — Exercise 6.2, by the book's/site's route: the maximal finitely
  generated submodule of a fixed `N`, adjoining one element, then the
  union-of-a-chain step (`prop_6_2`).
* `solution_contrapositive` — the same statement by an independent route: a
  non-finitely-generated submodule yields a strictly increasing sequence of
  finitely generated submodules, whose range has no maximal member.
* `not_maximalConditionOnFG_of_not_fg` — the contrapositive in explicit form.
* `prop_6_1`, `prop_6_2` — the book's Propositions 6.1 and 6.2, proved from
  scratch as auxiliaries.
* Dual asymmetry: `minimalCondition_fg_finsupp` (over an infinite-dimensional
  space the finitely generated submodules *do* satisfy the minimal condition) and
  `not_isArtinian_finsupp` (the space is not Artinian, the witnesses being
  infinite-dimensional), so the minimal-condition analogue of the exercise is
  false.
-/

namespace AtiyahMcdonald69.Ex_6_2

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-! ### Definitions -/

/-- The ascending chain condition (a.c.c.) on submodules of `M`: every increasing
sequence of submodules of `M` is eventually constant. This is the book's
definition of a Noetherian module (Chapter VI, p. 74); a bundled `ℕ →o` map is
exactly a monotone `ℕ`-indexed sequence of submodules. -/
def AscendingChainCondition : Prop :=
  ∀ N : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → N m = N n

/-- The maximal condition for the poset of submodules of `M` (Atiyah–Macdonald
6.1 (ii)): every nonempty set of submodules has a maximal element. -/
def MaximalCondition : Prop :=
  ∀ s : Set (Submodule R M), s.Nonempty → ∃ N ∈ s, ∀ N' ∈ s, N ≤ N' → N' = N

/-- The hypothesis of Exercise 6.2: every non-empty set of *finitely generated*
submodules of `M` has a maximal element. -/
def MaximalConditionOnFG : Prop :=
  ∀ s : Set (Submodule R M), s.Nonempty → (∀ N ∈ s, N.FG) →
    ∃ N ∈ s, ∀ N' ∈ s, N ≤ N' → N' = N

/-- The full maximal condition implies the hypothesis of Exercise 6.2. -/
theorem maximalConditionOnFG_of_maximalCondition
    (h : MaximalCondition (R := R) (M := M)) : MaximalConditionOnFG (R := R) (M := M) :=
  fun s hs _ => h s hs

/-! ### Proposition 6.1: a.c.c. ⟺ maximal condition (auxiliary) -/

/-- Atiyah–Macdonald, Proposition 6.1, for an arbitrary partially ordered set as
in the book: the ascending chain condition (i) is equivalent to the maximal
condition (ii). -/
theorem prop_6_1 {α : Type*} [PartialOrder α] :
    (∀ f : ℕ →o α, ∃ n, ∀ m, n ≤ m → f m = f n) ↔
      ∀ s : Set α, s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b = a := by
  constructor
  · intro hacc s hs
    by_contra hcon
    -- no maximal element: every member of `s` has a strictly larger one in `s`
    have key : ∀ a ∈ s, ∃ b ∈ s, a < b := by
      intro a ha
      by_contra hno
      simp only [not_exists, not_and] at hno
      refine hcon ⟨a, ha, fun b hb hab => le_antisymm ?_ hab⟩
      by_contra hba
      exact hno b hb (hab.lt_of_not_ge hba)
    obtain ⟨a₀, ha₀⟩ := hs
    let step : {a // a ∈ s} → {a // a ∈ s} := fun a =>
      ⟨(key a.1 a.2).choose, (key a.1 a.2).choose_spec.1⟩
    have hstep : ∀ a : {a // a ∈ s}, a.1 < (step a).1 := fun a =>
      (key a.1 a.2).choose_spec.2
    let g : ℕ → {a // a ∈ s} := fun n => step^[n] ⟨a₀, ha₀⟩
    have hsucc : ∀ n, (g (n + 1)).1 = (step (g n)).1 := by
      intro n
      simp only [g, Function.iterate_succ_apply']
    have hmono : Monotone fun n => (g n).1 :=
      monotone_nat_of_le_succ fun n => by
        rw [hsucc n]
        exact (hstep (g n)).le
    let F : ℕ →o α := ⟨fun n => (g n).1, hmono⟩
    obtain ⟨n, hn⟩ := hacc F
    have hstat : (g (n + 1)).1 = (g n).1 := hn (n + 1) (Nat.le_succ n)
    rw [hsucc n] at hstat
    exact (hstep (g n)).ne hstat.symm
  · intro hmax f
    obtain ⟨a, ha, hmaxa⟩ := hmax (Set.range f) ⟨f 0, Set.mem_range_self 0⟩
    obtain ⟨n, rfl⟩ := ha
    exact ⟨n, fun m hm => hmaxa (f m) (Set.mem_range_self m) (f.monotone hm)⟩

/-- Proposition 6.1 specialised to the poset of submodules of `M`. -/
theorem acc_iff_maximalCondition :
    AscendingChainCondition (R := R) (M := M) ↔ MaximalCondition (R := R) (M := M) :=
  prop_6_1

/-- The chain condition phrased with unbundled monotone sequences, as the book
writes it ("every increasing sequence `x₁ ≤ x₂ ≤ ⋯` is stationary"). -/
theorem acc_iff_monotone :
    AscendingChainCondition (R := R) (M := M) ↔
      ∀ f : ℕ → Submodule R M, Monotone f → ∃ n, ∀ m, n ≤ m → f m = f n := by
  constructor
  · intro h f hf
    exact h ⟨f, hf⟩
  · intro h N
    exact h (⇑N) N.monotone

/-- A Noetherian module satisfies the maximal condition. -/
theorem maximalCondition_of_acc (h : AscendingChainCondition (R := R) (M := M)) :
    MaximalCondition (R := R) (M := M) :=
  acc_iff_maximalCondition.mp h

/-! ### Proposition 6.2: Noetherian ⟺ all submodules finitely generated (auxiliary) -/

/-- Proposition 6.2, direction proved in the book: under the maximal condition,
the finitely generated submodules of a fixed submodule `N` have a maximal member
`K`; if `K ≠ N`, adjoining `x ∈ N ∖ K` produces a larger finitely generated
submodule of `N`, a contradiction. -/
theorem fg_of_maximalCondition (h : MaximalCondition (R := R) (M := M))
    (N : Submodule R M) : N.FG := by
  obtain ⟨K, hK, hmax⟩ :=
    h {K : Submodule R M | K.FG ∧ K ≤ N} ⟨⊥, Submodule.fg_bot, bot_le⟩
  have hK' : K.FG ∧ K ≤ N := hK
  obtain ⟨hKfg, hKN⟩ := hK'
  by_contra hNfg
  have hKNlt : K < N := by
    refine lt_of_le_of_ne hKN ?_
    intro hEq
    exact hNfg (hEq ▸ hKfg)
  obtain ⟨-, x, hxN, hxK⟩ := SetLike.lt_iff_le_and_exists.mp hKNlt
  have hle : K ⊔ R ∙ x ≤ N :=
    sup_le hKN ((Submodule.span_singleton_le_iff_mem x N).mpr hxN)
  have hmem : K ⊔ R ∙ x ∈ {K : Submodule R M | K.FG ∧ K ≤ N} :=
    ⟨hKfg.sup (Submodule.fg_span_singleton x), hle⟩
  have heq : K ⊔ R ∙ x = K := hmax _ hmem le_sup_left
  exact hxK (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))

/-- Proposition 6.2, converse (not written out in the printed proof): the union of
an increasing chain of submodules is a submodule; if it is finitely generated then
the chain is constant beyond the largest index of a generator. -/
theorem acc_of_fg (h : ∀ N : Submodule R M, N.FG) :
    AscendingChainCondition (R := R) (M := M) := by
  intro c
  obtain ⟨S, hS⟩ := h (⨆ n, c n)
  have hgen : ∀ x : S, (x : M) ∈ ⨆ n, c n := by
    intro x
    rw [← hS]
    exact Submodule.subset_span x.2
  have hex : ∀ x : S, ∃ n, (x : M) ∈ c n := fun x =>
    (Submodule.mem_iSup_of_chain c (x : M)).mp (hgen x)
  choose f hf using hex
  refine ⟨S.attach.sup f, fun m hm => le_antisymm ?_ (c.monotone hm)⟩
  calc c m ≤ ⨆ n, c n := le_iSup (fun n => c n) m
    _ = Submodule.span R (S : Set M) := hS.symm
    _ ≤ c (S.attach.sup f) := by
        rw [Submodule.span_le]
        intro x hx
        exact c.monotone (Finset.le_sup (f := f) (Finset.mem_attach S ⟨x, hx⟩)) (hf ⟨x, hx⟩)

/-- Noetherian ⟹ every submodule is finitely generated (Proposition 6.2, forward
direction, via Proposition 6.1). -/
theorem fg_of_acc (h : AscendingChainCondition (R := R) (M := M))
    (N : Submodule R M) : N.FG :=
  fg_of_maximalCondition (maximalCondition_of_acc h) N

/-- Proposition 6.2 with "finitely generated" in terms of `Submodule.FG`. -/
theorem acc_iff_fg_submodules :
    AscendingChainCondition (R := R) (M := M) ↔ ∀ N : Submodule R M, N.FG :=
  ⟨fg_of_acc, acc_of_fg⟩

/-- **Atiyah–Macdonald, Proposition 6.2** (auxiliary): `M` is a Noetherian
`A`-module iff every submodule of `M` is finitely generated. -/
theorem prop_6_2 :
    AscendingChainCondition (R := R) (M := M) ↔
      ∀ N : Submodule R M, Module.Finite R N := by
  rw [acc_iff_fg_submodules]
  exact ⟨fun h N => Module.Finite.of_fg (h N), fun h N => Module.Finite.iff_fg.mp (h N)⟩

/-- The chain condition agrees with Mathlib's `IsNoetherian`, which is defined by
finite generation of all submodules. -/
theorem isNoetherian_iff_acc :
    IsNoetherian R M ↔ AscendingChainCondition (R := R) (M := M) := by
  rw [isNoetherian_def]
  exact (acc_iff_fg_submodules (R := R) (M := M)).symm

/-! ### Exercise 6.2, route of the book and of the site -/

/-- Exercise 6.2, main step: under the hypothesis, every submodule `N` is finitely
generated. Apply the hypothesis to the non-empty set of finitely generated
submodules of `N`; a maximal member `K` must equal `N`, since otherwise
`K ⊔ A·x` for `x ∈ N ∖ K` would be a larger member. -/
theorem fg_of_maximalConditionOnFG (h : MaximalConditionOnFG (R := R) (M := M))
    (N : Submodule R M) : N.FG := by
  obtain ⟨K, hK, hmax⟩ :=
    h {K : Submodule R M | K.FG ∧ K ≤ N} ⟨⊥, Submodule.fg_bot, bot_le⟩
      (by rintro _ ⟨h1, -⟩; exact h1)
  have hK' : K.FG ∧ K ≤ N := hK
  obtain ⟨hKfg, hKN⟩ := hK'
  by_contra hNfg
  have hKNlt : K < N := by
    refine lt_of_le_of_ne hKN ?_
    intro hEq
    exact hNfg (hEq ▸ hKfg)
  obtain ⟨-, x, hxN, hxK⟩ := SetLike.lt_iff_le_and_exists.mp hKNlt
  have hle : K ⊔ R ∙ x ≤ N :=
    sup_le hKN ((Submodule.span_singleton_le_iff_mem x N).mpr hxN)
  have hmem : K ⊔ R ∙ x ∈ {K : Submodule R M | K.FG ∧ K ≤ N} :=
    ⟨hKfg.sup (Submodule.fg_span_singleton x), hle⟩
  have heq : K ⊔ R ∙ x = K := hmax _ hmem le_sup_left
  exact hxK (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))

/-- **Atiyah–Macdonald, Chapter VI, Exercise 2**, by the route of the book and of
the site: every submodule is finitely generated, hence—by Proposition 6.2—`M`
satisfies the ascending chain condition. -/
theorem solution (h : MaximalConditionOnFG (R := R) (M := M)) :
    AscendingChainCondition (R := R) (M := M) :=
  acc_of_fg fun N => fg_of_maximalConditionOnFG h N

/-- Exercise 6.2 with the book's wording "then `M` is Noetherian", using Mathlib's
class `IsNoetherian`. -/
theorem solution_isNoetherian (h : MaximalConditionOnFG (R := R) (M := M)) :
    IsNoetherian R M :=
  isNoetherian_iff_acc.mpr (solution h)

/-- The hypothesis of Exercise 6.2 is not only sufficient but also necessary: it
characterises Noetherian modules (the converse is the maximal condition 6.1 for
submodules of a module all of whose submodules are finitely generated). -/
theorem solution_iff :
    MaximalConditionOnFG (R := R) (M := M) ↔ AscendingChainCondition (R := R) (M := M) :=
  ⟨solution, fun h => maximalConditionOnFG_of_maximalCondition (maximalCondition_of_acc h)⟩

/-! ### Independent route: the contrapositive, with an explicit chain

If `N` is not finitely generated, then inside `N` one can adjoin elements one at
a time and obtain a strictly increasing sequence of finitely generated
submodules; the set of its terms is a set of finitely generated submodules with
no maximal member. -/

/-- Inside a non-finitely-generated submodule, every finitely generated submodule
can be strictly enlarged within it. -/
theorem exists_notMem_of_fg_of_le_of_not_fg {K N : Submodule R M} (hK : K.FG) (hKN : K ≤ N)
    (hN : ¬ N.FG) : ∃ x ∈ N, x ∉ K := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hN (le_antisymm hKN h ▸ hK)

/-- A non-finitely-generated submodule contains a strictly increasing sequence of
finitely generated submodules. -/
theorem exists_strictMono_chain_of_not_fg {N : Submodule R M} (hN : ¬ N.FG) :
    ∃ K : ℕ → Submodule R M, (∀ n, (K n).FG) ∧ (∀ n, K n ≤ N) ∧ ∀ n, K n < K (n + 1) := by
  classical
  -- one step: strictly enlarge a finitely generated submodule of `N` inside `N`
  have step : ∀ K : {K : Submodule R M // K.FG ∧ K ≤ N},
      ∃ K' : {K : Submodule R M // K.FG ∧ K ≤ N}, K.1 < K'.1 := by
    rintro ⟨K, hK, hKN⟩
    obtain ⟨x, hxN, hxK⟩ := exists_notMem_of_fg_of_le_of_not_fg hK hKN hN
    have hlt : K < K ⊔ R ∙ x := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hEq
      exact hxK (hEq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
    exact ⟨⟨K ⊔ R ∙ x, hK.sup (Submodule.fg_span_singleton x),
      sup_le hKN ((Submodule.span_singleton_le_iff_mem x N).mpr hxN)⟩, hlt⟩
  let f : {K : Submodule R M // K.FG ∧ K ≤ N} → {K : Submodule R M // K.FG ∧ K ≤ N} :=
    fun K => (step K).choose
  have hf : ∀ K, K.1 < (f K).1 := fun K => (step K).choose_spec
  let g : ℕ → {K : Submodule R M // K.FG ∧ K ≤ N} := fun n => f^[n] ⟨⊥, Submodule.fg_bot, bot_le⟩
  refine ⟨fun n => (g n).1, fun n => (g n).2.1, fun n => (g n).2.2, fun n => ?_⟩
  have hsucc : (g (n + 1)).1 = (f (g n)).1 := by
    simp only [g, Function.iterate_succ_apply']
  show (g n).1 < (g (n + 1)).1
  rw [hsucc]
  exact hf (g n)

/-- The contrapositive of Exercise 6.2: a module with a non-finitely-generated
submodule violates the exercise's hypothesis. -/
theorem not_maximalConditionOnFG_of_not_fg {N : Submodule R M} (hN : ¬ N.FG) :
    ¬ MaximalConditionOnFG (R := R) (M := M) := by
  intro h
  obtain ⟨K, hKfg, hKN, hKlt⟩ := exists_strictMono_chain_of_not_fg hN
  obtain ⟨L, hLmem, hLmax⟩ :=
    h (Set.range K) ⟨K 0, Set.mem_range_self 0⟩ (by rintro _ ⟨n, rfl⟩; exact hKfg n)
  obtain ⟨m, rfl⟩ := hLmem
  exact (hKlt m).ne' (hLmax (K (m + 1)) (Set.mem_range_self (m + 1)) (hKlt m).le)

/-- **Exercise 6.2 by an independent route**: contraposition. If the chain
condition failed, then some submodule would fail to be finitely generated
(`acc_of_fg`), and that submodule would carry a strictly increasing sequence of
finitely generated submodules, contradicting the hypothesis. -/
theorem solution_contrapositive (h : MaximalConditionOnFG (R := R) (M := M)) :
    AscendingChainCondition (R := R) (M := M) := by
  by_contra hacc
  have hfg : ∃ N : Submodule R M, ¬ N.FG := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hacc (acc_of_fg hcon)
  obtain ⟨N, hN⟩ := hfg
  exact not_maximalConditionOnFG_of_not_fg hN h

/-! ### The dual (minimal-condition) analogue is false

The exercise's statement is one-sided: the maximal condition on finitely generated
submodules forces the a.c.c. Its formal dual — the *minimal* condition on finitely
generated submodules forcing the d.c.c. — is false. Over a field, in `ℕ →₀ k` the
finitely generated submodules are exactly the finite-dimensional subspaces, and
those satisfy the minimal condition because dimension is a natural number; but the
subspaces spanned by the tails `e_n, e_{n+1}, …` form an infinite strictly
decreasing chain, so `ℕ →₀ k` is not Artinian. -/

section Dual

set_option linter.style.haveILetI false

/-- The subspace of `ℕ →₀ k` spanned by the coordinate vectors `e_m` with `m ≥ n`. -/
noncomputable def tailSpan (k : Type*) [Field k] (n : ℕ) : Submodule k (ℕ →₀ k) :=
  Submodule.span k {x : ℕ →₀ k | ∃ m ≥ n, x = Finsupp.single m 1}

/-- The tail subspaces are decreasing. -/
theorem tailSpan_le (k : Type*) [Field k] (n : ℕ) : tailSpan k (n + 1) ≤ tailSpan k n := by
  refine Submodule.span_mono ?_
  rintro x ⟨m, hm, rfl⟩
  exact ⟨m, le_trans (Nat.le_succ n) hm, rfl⟩

/-- `e_n` is not in the tail subspace starting at `n + 1`: the coordinate functional
at `n` vanishes on that tail but not at `e_n`. -/
theorem not_mem_tailSpan_succ (k : Type*) [Field k] (n : ℕ) :
    Finsupp.single n (1 : k) ∉ tailSpan k (n + 1) := by
  intro hmem
  let f : (ℕ →₀ k) →ₗ[k] k := Finsupp.lapply n
  have hle : tailSpan k (n + 1) ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨m, hm, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    show Finsupp.single m (1 : k) n = 0
    rcases lt_or_ge n m with h | h
    · exact Finsupp.single_eq_of_ne (Nat.ne_of_lt h)
    · exact absurd hm (not_le.mpr (Nat.lt_succ_of_le h))
  have h0 : f (Finsupp.single n (1 : k)) = 0 := LinearMap.mem_ker.mp (hle hmem)
  have h1 : f (Finsupp.single n (1 : k)) = 1 := by
    show Finsupp.single n (1 : k) n = 1
    exact Finsupp.single_eq_same
  rw [h1] at h0
  exact one_ne_zero h0

/-- The tail subspaces decrease strictly. -/
theorem tailSpan_strictAnti (k : Type*) [Field k] (n : ℕ) :
    tailSpan k (n + 1) < tailSpan k n := by
  refine lt_of_le_of_ne (tailSpan_le k n) ?_
  intro hEq
  have hmem : Finsupp.single n (1 : k) ∈ tailSpan k n :=
    Submodule.subset_span ⟨n, le_rfl, rfl⟩
  rw [← hEq] at hmem
  exact not_mem_tailSpan_succ k n hmem

/-- Over an infinite-dimensional space the finitely generated submodules satisfy the
minimal condition: they are the finite-dimensional subspaces, and the dimensions of
a nonempty family of them have a least element. -/
theorem minimalCondition_fg_finsupp (k : Type*) [Field k] :
    ∀ s : Set (Submodule k (ℕ →₀ k)), s.Nonempty → (∀ W ∈ s, W.FG) →
      ∃ W ∈ s, ∀ W' ∈ s, W' ≤ W → W' = W := by
  intro s hs hfg
  obtain ⟨W₀, hW₀⟩ := hs
  have hne : {m : ℕ | ∃ W ∈ s, Module.finrank k W = m}.Nonempty := ⟨_, W₀, hW₀, rfl⟩
  obtain ⟨W, hWs, hWm⟩ := Nat.sInf_mem hne
  haveI hWfin : Module.Finite k W := Module.Finite.iff_fg.mpr (hfg W hWs)
  refine ⟨W, hWs, fun W' hW's hW'W => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq hW'W ?_
  exact le_antisymm (Submodule.finrank_mono hW'W) (hWm.trans_le (Nat.sInf_le ⟨W', hW's, rfl⟩))

/-- `ℕ →₀ k` is not Artinian: the tail subspaces descend forever. -/
theorem not_isArtinian_finsupp (k : Type*) [Field k] : ¬ IsArtinian k (ℕ →₀ k) := by
  intro hA
  have hwf : WellFounded ((· < ·) : Submodule k (ℕ →₀ k) → Submodule k (ℕ →₀ k) → Prop) :=
    (isArtinian_iff k (ℕ →₀ k)).mp hA
  exact (RelEmbedding.natGT (tailSpan k) (tailSpan_strictAnti k)).not_wellFounded hwf

/-- **The dual analogue of the exercise fails**: the minimal condition on finitely
generated submodules does not force the descending chain condition. -/
theorem dual_analogue_false (k : Type*) [Field k] :
    (∀ s : Set (Submodule k (ℕ →₀ k)), s.Nonempty → (∀ W ∈ s, W.FG) →
        ∃ W ∈ s, ∀ W' ∈ s, W' ≤ W → W' = W) ∧ ¬ IsArtinian k (ℕ →₀ k) :=
  ⟨minimalCondition_fg_finsupp k, not_isArtinian_finsupp k⟩

end Dual

end AtiyahMcdonald69.Ex_6_2

#print axioms AtiyahMcdonald69.Ex_6_2.solution
#print axioms AtiyahMcdonald69.Ex_6_2.solution_isNoetherian
#print axioms AtiyahMcdonald69.Ex_6_2.solution_iff
#print axioms AtiyahMcdonald69.Ex_6_2.solution_contrapositive
#print axioms AtiyahMcdonald69.Ex_6_2.fg_of_maximalConditionOnFG
#print axioms AtiyahMcdonald69.Ex_6_2.not_maximalConditionOnFG_of_not_fg
#print axioms AtiyahMcdonald69.Ex_6_2.exists_strictMono_chain_of_not_fg
#print axioms AtiyahMcdonald69.Ex_6_2.prop_6_1
#print axioms AtiyahMcdonald69.Ex_6_2.prop_6_2
#print axioms AtiyahMcdonald69.Ex_6_2.acc_of_fg
#print axioms AtiyahMcdonald69.Ex_6_2.isNoetherian_iff_acc
#print axioms AtiyahMcdonald69.Ex_6_2.minimalCondition_fg_finsupp
#print axioms AtiyahMcdonald69.Ex_6_2.not_isArtinian_finsupp
#print axioms AtiyahMcdonald69.Ex_6_2.dual_analogue_false
