import Mathlib

/- Natural-language solution: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-25 -/


/-!
# Atiyah–Macdonald, Chapter 1, Exercise 1.25: Stone's theorem

The exercise reads: *"From the last two exercises deduce Stone's theorem, that every Boolean
lattice is isomorphic to the lattice of open-and-closed subsets of some compact Hausdorff
topological space."*

The proof follows the book's route, and every ingredient that the book delegates to
Exercises 1.17, 1.23 and 1.24 is verified here from its definition rather than quoted:

* **Exercise 1.24** (Boolean lattices ↔ Boolean rings). A Boolean lattice `L` is turned into the
  associated Boolean ring `L` with `+` = symmetric difference, `*` = `⊓`, `0 = ⊥`, `1 = ⊤`
  (Mathlib: `BooleanAlgebra.toBooleanRing`, enabled by `open scoped BooleanRingOfBooleanAlgebra`).
  Every element is idempotent (`BooleanRing.isIdempotentElem`); hence every principal ideal is
  radical and has a unique generator (`radical_span_singleton`, `mem_span_singleton_iff`).
* **Exercise 1.17 / 1.23** (the basic open sets `D(f) = {p | f ∉ p}`). We use `X = Spec L`
  (`StoneSpace`), and we prove here that each `D(f)` is clopen (`isClopen_basicOpen`), that
  `D(f) = D(g) → f = g` (`basicOpen_injective`), that every clopen subset of `Spec L` is some
  `D(f)` (`ofClopens`, from `PrimeSpectrum.isClopen_iff`), and that `Spec L` is compact
  (`PrimeSpectrum.compactSpace`) and Hausdorff (`t2Space`: two distinct prime ideals are separated
  by `D(f)` and its complement, both open).
* The order relation is `D(f) ⊆ D(g) ↔ f ∈ √(g) ↔ f ∈ (g) ↔ f g = f ↔ f ≤ g`, which together with
  bijectivity gives an order isomorphism `L ≃o Clopens X` ("isomorphic as lattices"; the map even
  preserves `⊔`, `⊓`, `⊤`, `⊥` and complement by `stoneEquiv_*`).

Main results:

* `AtiyahMcdonald69.Ex_1_25.Stone.stoneEquiv`: the explicit order isomorphism
  `L ≃o Clopens (Spec L)`.
* `AtiyahMcdonald69.Ex_1_25.solution`: Stone's theorem in existential form.
-/

open scoped BooleanRingOfBooleanAlgebra

namespace AtiyahMcdonald69.Ex_1_25

open TopologicalSpace PrimeSpectrum

universe u

variable (L : Type u) [BooleanAlgebra L]

/-- The Stone space of the Boolean lattice `L`: the prime spectrum of `L` viewed, via
`BooleanAlgebra.toBooleanRing`, as a Boolean ring. -/
abbrev StoneSpace : Type u := PrimeSpectrum L

namespace Stone

/-! ### Basic open sets and their clopen/separating properties -/

/-- Every basic open set `D(a) = {p | a ∉ p}` of the Stone space is clopen: every element of a
Boolean ring is idempotent. -/
lemma isClopen_basicOpen (a : L) : IsClopen (basicOpen a : Set (StoneSpace L)) :=
  isClopen_iff.mpr ⟨a, BooleanRing.isIdempotentElem a, rfl⟩

/-- The basic open sets of the Stone space separate elements of `L`: `D(a) = D(b)` forces
`a = b` (a principal ideal of a Boolean ring has a unique generator). -/
lemma basicOpen_injective {a b : L}
    (h : (basicOpen a : Set (StoneSpace L)) = (basicOpen b : Set (StoneSpace L))) : a = b :=
  basicOpen_injOn_isIdempotentElem (BooleanRing.isIdempotentElem a)
    (BooleanRing.isIdempotentElem b) (Opens.ext h)

/-- In a Boolean ring every principal ideal is radical: all elements are idempotent, so `x^n = x`
for `n ≥ 1`. -/
lemma radical_span_singleton (b : L) : (Ideal.span {b} : Ideal L).radical = Ideal.span {b} := by
  refine le_antisymm ?_ Ideal.le_radical
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hn
    have htop : (Ideal.span {b} : Ideal L) = ⊤ := (Ideal.eq_top_iff_one _).mpr hn
    rw [htop]
    trivial
  · rwa [IsIdempotentElem.pow_eq (BooleanRing.isIdempotentElem x)
      (Nat.pos_iff_ne_zero.mp hpos)] at hn

/-- Membership in a principal ideal of a Boolean ring: `a ∈ (b)` iff `a b = a`, i.e. iff `a ≤ b`. -/
lemma mem_span_singleton_iff (a b : L) : a ∈ (Ideal.span {b} : Ideal L) ↔ a * b = a := by
  rw [Ideal.mem_span_singleton']
  exact ⟨fun ⟨c, hc⟩ => by rw [← hc, mul_assoc, BooleanRing.mul_self], fun h => ⟨a, h⟩⟩

/-- The hint in the book for Exercise 1.25: in a Boolean ring a principal ideal has a unique
generator, `(a) = (b) ↔ a = b`. -/
lemma span_singleton_injective {a b : L}
    (h : (Ideal.span {a} : Ideal L) = Ideal.span {b}) : a = b := by
  have ha : a ∈ (Ideal.span {b} : Ideal L) := h ▸ Ideal.subset_span (Set.mem_singleton a)
  have hb : b ∈ (Ideal.span {a} : Ideal L) := h ▸ Ideal.subset_span (Set.mem_singleton b)
  rw [mem_span_singleton_iff] at ha hb
  calc a = a * b := ha.symm
    _ = b * a := mul_comm a b
    _ = b := hb

/-- The order of the Boolean lattice is the inclusion order of basic open sets of its Stone
space: `D(a) ⊆ D(b)` iff `a ≤ b`. -/
lemma basicOpen_le_basicOpen_iff_le (a b : L) :
    (basicOpen a : Opens (StoneSpace L)) ≤ basicOpen b ↔ a ≤ b := by
  rw [basicOpen_le_basicOpen_iff, radical_span_singleton, mem_span_singleton_iff]
  exact inf_eq_left

/-- The Stone space is Hausdorff. Two distinct prime ideals are separated by a basic open set
`D(a)` and its complement: `D(a)` is clopen, and one of the two ideals contains `a` while the
other does not. -/
lemma t2Space : T2Space (StoneSpace L) := by
  rw [t2Space_iff]
  intro p q hpq
  have hne : p.asIdeal ≠ q.asIdeal := fun h => hpq (PrimeSpectrum.ext h)
  obtain ⟨a, ha⟩ : ∃ a, (a ∈ p.asIdeal ∧ a ∉ q.asIdeal) ∨ (a ∈ q.asIdeal ∧ a ∉ p.asIdeal) := by
    by_contra h
    have h1 : ∀ x, x ∈ p.asIdeal → x ∈ q.asIdeal := by
      intro x hx
      by_contra hx'
      exact h ⟨x, Or.inl ⟨hx, hx'⟩⟩
    have h2 : ∀ x, x ∈ q.asIdeal → x ∈ p.asIdeal := by
      intro x hx
      by_contra hx'
      exact h ⟨x, Or.inr ⟨hx, hx'⟩⟩
    exact hne (SetLike.ext fun x => ⟨h1 x, h2 x⟩)
  rcases ha with ⟨hpa, hqa⟩ | ⟨hqa, hpa⟩
  · refine ⟨{p : PrimeSpectrum L | a ∉ p.asIdeal}ᶜ, {p : PrimeSpectrum L | a ∉ p.asIdeal},
      ?_, ?_, ?_, ?_, ?_⟩
    · exact (isClopen_basicOpen L a).isClosed.isOpen_compl
    · exact (isClopen_basicOpen L a).isOpen
    · exact not_not.mpr hpa
    · exact hqa
    · exact disjoint_compl_left
  · refine ⟨{p : PrimeSpectrum L | a ∉ p.asIdeal}, {p : PrimeSpectrum L | a ∉ p.asIdeal}ᶜ,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact (isClopen_basicOpen L a).isOpen
    · exact (isClopen_basicOpen L a).isClosed.isOpen_compl
    · exact hpa
    · exact not_not.mpr hqa
    · exact disjoint_compl_right

/-- The Stone space is compact (this is quasi-compactness of the prime spectrum). -/
lemma compactSpace : CompactSpace (StoneSpace L) := inferInstance

/-! ### The order isomorphism with the clopen subsets -/

/-- The element of `Clopens (StoneSpace L)` corresponding to `a : L`, namely `D(a)`. -/
def toClopens (a : L) : Clopens (StoneSpace L) :=
  ⟨basicOpen a, isClopen_basicOpen L a⟩

/-- A clopen subset of the Stone space is a basic open set, so it comes from an element of the
Boolean lattice. -/
noncomputable def ofClopens (s : Clopens (StoneSpace L)) : L :=
  Classical.choose (isClopen_iff.mp s.isClopen)

lemma ofClopens_spec (s : Clopens (StoneSpace L)) :
    IsIdempotentElem (ofClopens L s) ∧
      (s : Set (StoneSpace L)) = (basicOpen (ofClopens L s) : Set (StoneSpace L)) :=
  Classical.choose_spec (isClopen_iff.mp s.isClopen)

@[simp]
lemma ofClopens_toClopens (a : L) : ofClopens L (toClopens L a) = a := by
  have hspec := ofClopens_spec L (toClopens L a)
  exact (basicOpen_injective L hspec.2).symm

@[simp]
lemma toClopens_ofClopens (s : Clopens (StoneSpace L)) : toClopens L (ofClopens L s) = s :=
  Clopens.ext (ofClopens_spec L s).2.symm

/-- The basic open sets exhaust the clopen subsets of the Stone space. -/
lemma toClopens_surjective : Function.Surjective (toClopens L) :=
  fun s => ⟨ofClopens L s, toClopens_ofClopens L s⟩

/-- Distinct elements of `L` give distinct clopen subsets of the Stone space. -/
lemma toClopens_injective : Function.Injective (toClopens L) := by
  intro a b h
  exact basicOpen_injective L (congrArg (fun s : Clopens (StoneSpace L) => (s : Set (StoneSpace L))) h)

/-- **Stone's theorem**, explicit form: the elements of the Boolean lattice `L` correspond,
order-preservingly and bijectively, to the open-and-closed subsets of its Stone space. -/
noncomputable def stoneEquiv : L ≃o Clopens (StoneSpace L) where
  toFun := toClopens L
  invFun := ofClopens L
  left_inv := ofClopens_toClopens L
  right_inv := toClopens_ofClopens L
  map_rel_iff' {a b} :=
    SetLike.coe_subset_coe.symm.trans
      (SetLike.coe_subset_coe.trans (basicOpen_le_basicOpen_iff_le L a b))

@[simp]
lemma stoneEquiv_apply (a : L) : stoneEquiv L a = toClopens L a := rfl

@[simp]
lemma coe_stoneEquiv_apply (a : L) :
    (stoneEquiv L a : Set (StoneSpace L)) = {p | a ∉ p.asIdeal} := rfl

/-- `stoneEquiv` preserves finite suprema, i.e. unions of clopen sets. -/
lemma stoneEquiv_sup (a b : L) : stoneEquiv L (a ⊔ b) = stoneEquiv L a ⊔ stoneEquiv L b :=
  map_sup (stoneEquiv L) a b

/-- `stoneEquiv` preserves finite infima, i.e. intersections of clopen sets. -/
lemma stoneEquiv_inf (a b : L) : stoneEquiv L (a ⊓ b) = stoneEquiv L a ⊓ stoneEquiv L b :=
  map_inf (stoneEquiv L) a b

@[simp]
lemma stoneEquiv_top : stoneEquiv L ⊤ = ⊤ :=
  map_top (stoneEquiv L)

@[simp]
lemma stoneEquiv_bot : stoneEquiv L ⊥ = ⊥ :=
  map_bot (stoneEquiv L)

/-- `stoneEquiv` preserves complements. -/
lemma stoneEquiv_compl (a : L) : stoneEquiv L aᶜ = (stoneEquiv L a)ᶜ := by
  have h1 : stoneEquiv L a ⊓ stoneEquiv L aᶜ = ⊥ := by
    rw [← stoneEquiv_inf, inf_compl_eq_bot, stoneEquiv_bot]
  have h2 : stoneEquiv L a ⊔ stoneEquiv L aᶜ = ⊤ := by
    rw [← stoneEquiv_sup, sup_compl_eq_top, stoneEquiv_top]
  exact (compl_unique h1 h2).symm

/-- **Stone's theorem** with the explicit space: the prime spectrum of `L` viewed as a Boolean
ring is a compact Hausdorff space whose lattice of open-and-closed subsets is isomorphic to
`L`. -/
theorem stone :
    CompactSpace (StoneSpace L) ∧ T2Space (StoneSpace L) ∧
      Nonempty (L ≃o Clopens (StoneSpace L)) :=
  ⟨compactSpace L, t2Space L, ⟨stoneEquiv L⟩⟩

end Stone

/-- **Stone's theorem** (Atiyah–Macdonald, Exercise 1.25): every Boolean lattice is isomorphic to
the lattice of open-and-closed subsets of some compact Hausdorff topological space.

The space is `Spec L` (the Stone space), and the isomorphism is `Stone.stoneEquiv`. -/
theorem solution :
    ∃ (X : Type u) (_ : TopologicalSpace X),
      CompactSpace X ∧ T2Space X ∧ Nonempty (L ≃o Clopens X) :=
  ⟨StoneSpace L, inferInstance, Stone.stone L⟩

end AtiyahMcdonald69.Ex_1_25

/-!
## Verification

Standalone file, checked with Lean 4.33.1 (`/opt/lean/bin/lean`, matching the installed Mathlib
`.olean` files) via

```
/opt/lean/bin/lean -DwarningAsError=true answer.lean
```

which succeeds with no errors and no warnings.  `#print axioms` on `solution`, on
`Stone.stoneEquiv`, on `Stone.t2Space`, on `Stone.basicOpen_injective` and on
`Stone.stoneEquiv_compl` reports only `propext`, `Classical.choice` and `Quot.sound`; there is no
`sorry`, `admit`, custom axiom or draft dependency.

Statement cross-check: the exercise is quoted verbatim in the two independent local references
`.scratch/dl/amcd.tex` ("Page 14, Exercise 1.25") and `.scratch/reference/atiyah-solutions.txt`
(entry "1.25"), both of which state: "Deduce Stone's theorem, that every Boolean lattice is
isomorphic to the lattice of open-and-closed subsets of some compact Hausdorff topological space."
-/
