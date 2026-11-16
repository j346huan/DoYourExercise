/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 2 (Modules),
Exercise 2.22.

**Statement of the exercise** (p. 34): Let `(A_i, α_ij)` be a direct system of rings and let
`N_i` be the nilradical of `A_i`. Show that `lim N_i` is the nilradical of `lim A_i`.
If each `A_i` is an integral domain, then so is `lim A_i`.

**What is proved below.**  For a direct system `S` of commutative rings over a directed
preorder `ι` (Exercise 2.14: a family of rings and transition maps `α_ij : A_i ⟶ A_j` for
`i ≤ j` satisfying `α_ii = id` and `α_jk ∘ α_ij = α_ik`) we construct

* the direct limit `S.colim` of the rings (Mathlib's `DirectLimit`, whose underlying set is
  the quotient of `Σ i, A i` by the relation `x ∼ y ↔ ∃ k ≥ i, j, α_ik x = α_jk y`; this is
  the construction of Exercise 2.14, see the note on the empty index set below), with canonical
  maps `S.of i : A i →+* S.colim`;
* the direct system `S.nilSys i = nilradical (A i)` of nilradicals, with the induced maps
  `S.nilMap`, its direct limit `S.nilColim`, and the canonical comparison map
  `S.nilToColim : S.nilColim → S.colim`.

The two assertions of the exercise are then, for nonempty `ι` (see the last item below),

* `S.nilToColim_injective` : `S.nilToColim` is injective, and
  `S.nilToColim_range` : its range is exactly the nilradical of `S.colim`
  (equivalently `S.isNilpotent_iff`: an element of `S.colim` is nilpotent iff it is the image
  of a nilpotent element of some `A i`; this is the precise meaning of
  `lim N_i = N(lim A_i)`), and
* `S.isDomain_colim` : if every `A i` is an integral domain, then so is `S.colim`.

**Hypotheses; audit of the natural proof.**

* *Directedness* (`[IsDirectedOrder ι]`) is the book's own hypothesis.  The natural proof uses
  it twice, both times through Exercise 2.15 (lifting an equality of two elements of the limit
  to a common later stage, and lifting `x^n = 0` to a vanishing power at a later stage).
* `[Nonempty ι]` is an *extra* hypothesis, and it is not hidden: the book's definition of a
  directed set (Exercise 2.14) does not exclude `I = ∅`, and then the second assertion of
  Exercise 2.22 is *false* — the hypothesis is vacuous while the construction of Exercise 2.14
  gives the zero ring, which is not an integral domain.  The section "The empty index set"
  below gives a source-valid reason why the book's intended setup has `I ≠ ∅` (Exercise 2.15
  already fails for `I = ∅`), formalizes the triviality of `⨁_{i∈∅} A_i` and of the resulting
  limit, and proves `emptyIndex_literal_statement_fails`, the counterexample to the
  unconditional literal formulation.  All theorems about `S.colim` therefore carry
  `[Nonempty ι]` explicitly (inspect them with `#check`).
* The second half needs `1 ≠ 0` in every `A i`, i.e. the hypothesis is "integral domain" and
  not merely "no zero divisors": a component may be the zero ring (Exercise 2.21 is exactly the
  statement that `lim A_i = 0` forces some `A_i = 0`; Mathlib's `Nontrivial (DirectLimit ...)`
  instance is that argument).  The section "Sharpness of the hypotheses" makes this concrete
  (`ZMod 1` has no zero divisors but is not a domain), and "A worked example" applies the
  theorem to `ℤ[x_1,…,x_n] ↪ ℤ[x_1,…,x_{n+1}]`.
-/
import Mathlib

open DirectLimit

universe u v

namespace AtiyahMcdonald69.Ex_2_22

/-- A direct system of commutative rings over a preorder `ι`: a family of rings together with
transition maps `α_ij : A_i ⟶ A_j` for `i ≤ j`, subject to the two conditions (1) and (2) of
Atiyah–Macdonald, Chapter 2, Exercise 2.14. -/
structure DirectSystemOfRings (ι : Type u) [Preorder ι] where
  /-- the rings of the direct system -/
  A : ι → Type v
  [ring : ∀ i, CommRing (A i)]
  /-- the transition maps `α_ij : A_i ⟶ A_j` for `i ≤ j` -/
  map : ∀ ⦃i j : ι⦄, i ≤ j → A i →+* A j
  /-- condition (1) of Exercise 2.14: `α_ii` is the identity -/
  map_self : ∀ ⦃i : ι⦄ (x : A i), map (le_refl i) x = x
  /-- condition (2) of Exercise 2.14: `α_ik = α_jk ∘ α_ij` for `i ≤ j ≤ k` -/
  map_map : ∀ ⦃i j k : ι⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    map hjk (map hij x) = map (hij.trans hjk) x

namespace DirectSystemOfRings

variable {ι : Type u} [Preorder ι] (S : DirectSystemOfRings ι)

attribute [instance] DirectSystemOfRings.ring

/-- The transition maps, as plain functions: this is the directed system of types underlying
`S` (Exercise 2.14). -/
instance instDirectedSystem : DirectedSystem S.A (fun _ _ h => ⇑(S.map h)) :=
  ⟨fun _ x => S.map_self x, fun _ _ _ hij hjk x => S.map_map hij hjk x⟩

/-! ## The nilradicals (before the nonemptiness hypothesis is needed) -/

/-- The nilradical `N_i` of `A_i`, regarded as a type (an ideal of `A_i`). -/
abbrev nilSys (i : ι) : Type v := nilradical (S.A i)

/-- The transition map `N_i ⟶ N_j` induced by `α_ij`; a ring homomorphism sends nilpotent
elements to nilpotent elements, so this is well defined. -/
def nilMap (i j : ι) (h : i ≤ j) : S.nilSys i →+ S.nilSys j where
  toFun x := ⟨S.map h x.1, by
    rw [mem_nilradical]
    exact (mem_nilradical.mp x.2).map (S.map h)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

instance instDirectedSystemNil : DirectedSystem S.nilSys (fun _ _ h => ⇑(S.nilMap _ _ h)) :=
  ⟨fun _ x => Subtype.ext (S.map_self x.1),
   fun _ _ _ hij hjk x => Subtype.ext (S.map_map hij hjk x.1)⟩

/-! ## The empty index set

The definition of a directed set in Exercise 2.14 ("for each pair `i`, `j` in `I` there exists
`k ∈ I` with `i ≤ k` and `j ≤ k`") does not exclude `I = ∅`, and `∅` does satisfy it.  So
`[Nonempty ι]`, assumed by all the results below, is a genuine extra hypothesis which has to be
justified.

*Source-valid justification.*  Exercise 2.15, stated for the same data as Exercise 2.14, says
that every element of `lim M_i` is of the form `μ_i(x_i)` with `i ∈ I`.  For `I = ∅` the limit
is `0`, and this fails for its element `0`, because there is no `i ∈ I` at all.  Exercise 2.22
is proved from Exercise 2.15 (the natural proof uses precisely that statement), so the book's
intended setup has `I ≠ ∅`.

*The unconditional literal statement is false.*  In the construction of Exercise 2.14 the limit
is `C / D` with `C = ⨁_{i ∈ I} A_i`; for an empty index `C` is trivial, so the limit is the zero
ring, whose identity is `0`, whereas an integral domain has `1 ≠ 0` (Chapter 1).  The vacuity of
the hypothesis and the triviality of `C` are both recorded formally below. -/

/-- The direct sum `C = ⨁_{i ∈ I} A_i` of the construction of Exercise 2.14 is trivial for an
empty index set; hence the limit `C / D` of the empty system is the zero ring. -/
theorem subsingleton_directSum [IsEmpty ι] : Subsingleton (DirectSum ι (fun i => S.A i)) := by
  refine ⟨fun x y => ?_⟩
  ext i
  exact (isEmptyElim i : False).elim

section EmptyIndex

variable [IsDirectedOrder ι]

/-- For an empty index set the type underlying Mathlib's direct limit is empty.  (Mathlib's
`DirectLimit` is a quotient of `Σ i, A i`, while the construction of Exercise 2.14 quotients
the direct sum `⨁ i, A i`; for nonempty directed index sets the two are canonically
isomorphic.)  In particular no ring
structure is available on it, which is why the theorems below assume `[Nonempty ι]`. -/
theorem isEmpty_colim [IsEmpty ι] : IsEmpty (DirectLimit S.A (fun _ _ h => S.map h)) := by
  refine ⟨fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ y => exact isEmptyElim y.1

/-- Likewise the direct limit of the nilradicals is empty for an empty index set: the first
assertion of Exercise 2.22 is then vacuous, and this is the only sense in which the limiting
case `I = ∅` is unproblematic. -/
theorem isEmpty_nilColim [IsEmpty ι] :
    IsEmpty (DirectLimit S.nilSys (fun i j h => S.nilMap i j h)) := by
  refine ⟨fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ y => exact isEmptyElim y.1

end EmptyIndex

/-- A commutative ring whose additive group is trivial is the zero ring, hence not an integral
domain: this is the ring obtained as the empty direct limit. -/
theorem not_isDomain_of_subsingleton (R : Type*) [CommRing R] [Subsingleton R] : ¬ IsDomain R := by
  intro h
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (Subsingleton.elim x y)

/-- The zero ring, the ring structure inherited by the empty direct limit, is not a domain. -/
example : ¬ IsDomain (ZMod 1) := not_isDomain_of_subsingleton (ZMod 1)

/-- The direct system of rings over the empty index set: all of its data is vacuous. -/
def emptySystem : DirectSystemOfRings PEmpty where
  A := PEmpty.elim
  ring := fun i => i.elim
  map := fun i => i.elim
  map_self := fun i => i.elim
  map_map := fun i => i.elim

/-- **The unconditional literal statement is false for the empty index set.**  The empty set is
directed in the sense of Exercise 2.14 (vacuously), the hypothesis "every `A_i` is an integral
domain" holds vacuously for the empty system, the direct sum `⨁_{i∈∅} A_i` of the construction
of Exercise 2.14 is trivial (so the limit is the zero ring), and no commutative ring with
trivial additive group is an integral domain.  Compare Exercise 2.15, whose first assertion
already fails for `I = ∅`. -/
theorem emptyIndex_literal_statement_fails :
    (∀ i : PEmpty, IsDomain (emptySystem.A i)) ∧
      Subsingleton (DirectSum PEmpty (fun i => emptySystem.A i)) ∧
      (∀ (R : Type) [CommRing R], Subsingleton R → ¬ IsDomain R) :=
  ⟨fun i => i.elim, subsingleton_directSum (S := emptySystem),
    fun _ _ _ => not_isDomain_of_subsingleton _⟩

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The direct limit `lim A_i` of the direct system of rings `S` (Exercise 2.14). -/
abbrev colim : Type (max u v) := DirectLimit S.A (fun _ _ h => S.map h)

/-- The canonical ring homomorphism `A_i ⟶ lim A_i`. -/
noncomputable def of (i : ι) : S.A i →+* S.colim :=
  DirectLimit.Ring.of S.A (fun _ _ h => S.map h) i

@[simp] theorem of_coe (i : ι) (x : S.A i) : S.of i x = ⟦⟨i, x⟩⟧ := rfl

/-- The canonical maps are compatible with the transition maps. -/
@[simp] theorem of_f {i j : ι} (hij : i ≤ j) (x : S.A i) :
    S.of j (S.map hij x) = S.of i x := DirectLimit.Ring.of_f hij x

/-- Exercise 2.15 (second part) for the direct system of rings `S`: an element of a component
maps to zero in the direct limit iff it already maps to zero at some later stage. -/
theorem of_eq_zero_iff {i : ι} (x : S.A i) :
    S.of i x = 0 ↔ ∃ (j : ι) (h : i ≤ j), S.map h x = 0 := by
  rw [S.of_coe i x, show (0 : S.colim) = ⟦⟨i, (0 : S.A i)⟩⟧ from DirectLimit.zero_def i]
  constructor
  · intro hx
    obtain ⟨k, h1, h2, heq⟩ := Quotient.eq.mp hx
    exact ⟨k, h1, by simpa using heq⟩
  · rintro ⟨j, h, hx⟩
    exact Quotient.sound ⟨j, h, h, by simp [hx]⟩

/-- Two elements of components of the direct limit are equal iff they become equal after
mapping to a common later stage (Exercise 2.15, first part, in the form needed below). -/
theorem of_eq_of_iff {i j : ι} (x : S.A i) (y : S.A j) :
    S.of i x = S.of j y ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), S.map hik x = S.map hjk y := by
  rw [S.of_coe i x, S.of_coe j y]
  exact ⟨fun h => Quotient.eq.mp h, fun ⟨k, h1, h2, heq⟩ => Quotient.sound ⟨k, h1, h2, heq⟩⟩

/-- The nilradical of the direct limit is the direct limit of the nilradicals: an element of
`lim A_i` is nilpotent iff it is the image of a nilpotent element of some `A i`. -/
theorem isNilpotent_iff {x : S.colim} :
    IsNilpotent x ↔ ∃ (i : ι) (a : S.A i), IsNilpotent a ∧ x = S.of i a := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk (fun _ _ h => S.map h) x
    have hn' : (⟦⟨i, a ^ n⟩⟧ : S.colim) = 0 := by
      rw [← DirectLimit.npow_def]
      exact hn
    have hn'' : S.of i (a ^ n) = 0 := hn'
    obtain ⟨j, h, hj⟩ := (S.of_eq_zero_iff (a ^ n)).mp hn''
    exact ⟨j, S.map h a, ⟨n, by rw [← map_pow]; exact hj⟩, (S.of_f h a).symm⟩
  · rintro ⟨i, a, ha, rfl⟩
    exact ha.map (S.of i)

/-! ## The direct limit of the nilradicals -/

/-- The direct limit `lim N_i` of the nilradicals. -/
abbrev nilColim : Type (max u v) := DirectLimit S.nilSys (fun i j h => S.nilMap i j h)

omit [Nonempty ι] in
@[simp] theorem nilMk_apply {i j : ι} (h : i ≤ j) (x : S.nilSys i) :
    (⟦⟨j, S.nilMap i j h x⟩⟧ : S.nilColim) = ⟦⟨i, x⟩⟧ :=
  DirectLimit.mk_apply i j x h

/-- The canonical map `lim N_i ⟶ lim A_i` induced by the inclusions `N_i ⊆ A_i`. -/
noncomputable def nilToColim : S.nilColim → S.colim :=
  DirectLimit.lift (fun _i _j h => S.nilMap _i _j h) (fun i x => S.of i x.1)
    (fun _i _j h x => (S.of_f h x.1).symm)

@[simp] theorem nilToColim_coe {i : ι} (x : S.nilSys i) :
    S.nilToColim ⟦⟨i, x⟩⟧ = S.of i x.1 := rfl

/-- `lim N_i ⟶ lim A_i` is injective: a nilpotent element of a component which dies in the
direct limit already dies in `lim N_i`. -/
theorem nilToColim_injective : Function.Injective S.nilToColim := by
  intro z w hzw
  obtain ⟨i, x, y, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (fun _i _j h => S.nilMap _i _j h) z w
  have h : S.of i x.1 = S.of i y.1 := hzw
  obtain ⟨k, h1, h2, heq⟩ := (S.of_eq_of_iff x.1 y.1).mp h
  have hxy : S.nilMap i k h1 x = S.nilMap i k h2 y := Subtype.ext heq
  rw [← S.nilMk_apply h1 x, ← S.nilMk_apply h2 y, hxy]

/-- The range of `lim N_i ⟶ lim A_i` is exactly the nilradical of `lim A_i`: this is the
precise sense in which `lim N_i` *is* the nilradical of `lim A_i`. -/
theorem nilToColim_range :
    Set.range S.nilToColim = (nilradical S.colim : Set S.colim) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, n, rfl⟩ := DirectLimit.exists_eq_mk (fun _i _j h => S.nilMap _i _j h) y
    rw [S.nilToColim_coe (i := i) n]
    exact mem_nilradical.mpr ((mem_nilradical.mp n.2).map (S.of i))
  · intro hz
    have hz' : IsNilpotent z := mem_nilradical.mp hz
    obtain ⟨i, a, ha, rfl⟩ := S.isNilpotent_iff.mp hz'
    exact ⟨(⟦⟨i, ⟨a, mem_nilradical.mpr ha⟩⟩⟧ : S.nilColim), by rw [S.nilToColim_coe (i := i)]⟩

/-- The comparison map `lim N_i ⟶ lim A_i` is additive. -/
theorem nilToColim_add (x y : S.nilColim) :
    S.nilToColim (x + y) = S.nilToColim x + S.nilToColim y :=
  DirectLimit.induction₂ (f := fun i j h => S.nilMap i j h) (fun i a b => by
    simp only [DirectLimit.add_def, S.nilToColim_coe]
    show (S.of i) (↑a + ↑b) = (S.of i) ↑a + (S.of i) ↑b
    exact map_add _ _ _) x y

/-- The comparison map `lim N_i ⟶ lim A_i` preserves zero. -/
theorem nilToColim_zero : S.nilToColim (0 : S.nilColim) = 0 := by
  have h : (0 : S.nilColim) =
      ⟦⟨Classical.arbitrary ι, (0 : S.nilSys (Classical.arbitrary ι))⟩⟧ :=
    DirectLimit.zero_def (Classical.arbitrary ι)
  rw [h, S.nilToColim_coe]
  exact map_zero _

/-- The nilradical of `lim A_i` is the union (supremum of ideals) of the images of the
nilradicals `N_i`, the map `lim N_i ⟶ lim A_i` being injective. -/
theorem nilradical_eq_iSup :
    nilradical S.colim = ⨆ i, Ideal.map (S.of i) (nilradical (S.A i)) := by
  refine le_antisymm ?_ (iSup_le fun i => ?_)
  · intro x hx
    rw [mem_nilradical] at hx
    obtain ⟨i, a, ha, rfl⟩ := S.isNilpotent_iff.mp hx
    exact Ideal.mem_iSup_of_mem i (Ideal.mem_map_of_mem _ (mem_nilradical.mpr ha))
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_nilradical]
    exact (mem_nilradical.mp hx).map (S.of i)

/-! ## The direct limit of integral domains -/

/-- The direct limit of a direct system of integral domains has no zero divisors. -/
instance noZeroDivisors_colim [∀ i, IsDomain (S.A i)] : NoZeroDivisors S.colim where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    obtain ⟨i, x, y, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (fun _ _ h => S.map h) a b
    have h : (⟦⟨i, x * y⟩⟧ : S.colim) = 0 := by
      rw [← DirectLimit.mul_def]
      exact hab
    have h' : S.of i (x * y) = 0 := h
    obtain ⟨j, hj, hzero⟩ := (S.of_eq_zero_iff (x * y)).mp h'
    have hzero' : S.map hj x * S.map hj y = 0 := by
      rw [← map_mul]
      exact hzero
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero' with hx | hy
    · left
      have h0 : (S.of j) (S.map hj x) = 0 := by rw [hx]; exact map_zero _
      exact (S.of_f hj x).symm.trans h0
    · right
      have h0 : (S.of j) (S.map hj y) = 0 := by rw [hy]; exact map_zero _
      exact (S.of_f hj y).symm.trans h0

/-- A commutative ring without zero divisors has cancellative multiplication. -/
instance isCancelMulZero_colim [∀ i, IsDomain (S.A i)] : IsCancelMulZero S.colim :=
  inferInstance

/-- **Atiyah–Macdonald, Chapter 2, Exercise 2.22**, second assertion: the direct limit of a
direct system of integral domains is an integral domain.  (Nontriviality is the content of
Exercise 2.21: `1 = 0` in the limit forces `1 = 0` in some component, which is impossible in a
domain.) -/
theorem isDomain_colim [∀ i, IsDomain (S.A i)] : IsDomain S.colim := IsDomain.mk

/-! ## Exercise 2.22 -/

/-- **Atiyah–Macdonald, Chapter 2, Exercise 2.22**, first assertion: `lim N_i` is the
nilradical of `lim A_i`.  The canonical map from the direct limit of the nilradicals `N_i` to
`lim A_i` is injective with range exactly the nilradical of `lim A_i`. -/
theorem exercise_2_22_nilradical :
    Function.Injective S.nilToColim ∧
      Set.range S.nilToColim = (nilradical S.colim : Set S.colim) ∧
      nilradical S.colim = ⨆ i, Ideal.map (S.of i) (nilradical (S.A i)) :=
  ⟨S.nilToColim_injective, S.nilToColim_range, S.nilradical_eq_iSup⟩

/-- **Atiyah–Macdonald, Chapter 2, Exercise 2.22**, second assertion: the direct limit of a
direct system of integral domains is an integral domain. -/
theorem exercise_2_22_domain [∀ i, IsDomain (S.A i)] : IsDomain S.colim := S.isDomain_colim


/-! ## Sharpness of the hypotheses

The hypothesis "integral domain" in the second half of Exercise 2.22 cannot be weakened to
"no zero divisors": a direct system whose components all have no zero divisors may have a
limit which is the zero ring.  (This is why Exercise 2.21, i.e. `1 ≠ 0` in the components,
is needed; `IsDomain` in Mathlib is exactly "nontrivial + no zero divisors".) -/

/-- The constant direct system over `ℕ` with value the zero ring `ZMod 1`. -/
def zeroRingSystem : DirectSystemOfRings ℕ where
  A _ := ZMod 1
  map _ _ _ := RingHom.id (ZMod 1)
  map_self := by intro i x; rfl
  map_map := by intro i j k hij hjk x; rfl

/-- Every component of `zeroRingSystem` has no zero divisors (vacuously). -/
example (n : ℕ) : NoZeroDivisors (zeroRingSystem.A n) :=
  show NoZeroDivisors (ZMod 1) from inferInstance

/-- But the limit of `zeroRingSystem` is the zero ring, which is not an integral domain. -/
theorem not_isDomain_zeroRingSystem : ¬ IsDomain zeroRingSystem.colim := by
  intro h
  have h1 : (1 : zeroRingSystem.colim) = 0 := by
    rw [show (1 : zeroRingSystem.colim) = ⟦⟨0, (1 : ZMod 1)⟩⟧ from DirectLimit.one_def 0,
      show (0 : zeroRingSystem.colim) = ⟦⟨0, (0 : ZMod 1)⟩⟧ from DirectLimit.zero_def 0]
    exact congrArg (fun x : ZMod 1 => (⟦⟨0, x⟩⟧ : zeroRingSystem.colim))
      (Subsingleton.elim (1 : ZMod 1) 0)
  have hzero : ∀ x : zeroRingSystem.colim, x = 0 := fun x => by
    rw [← mul_one x, h1, mul_zero]
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (by rw [hzero x, hzero y])

/-! ## A worked example

The direct system `ℤ[x_1,…,x_n] ↪ ℤ[x_1,…,x_{n+1}]` of polynomial rings in growing numbers of
variables: every component is an integral domain, hence so is the limit (the nilradical of the
limit is trivial, in accordance with `nilradical_eq_iSup`). -/

/-- The direct system `A_n = ℤ[x_1,…,x_n]` with the inclusions `x_i ↦ x_i`. -/
noncomputable def polySystem : DirectSystemOfRings ℕ where
  A n := MvPolynomial (Fin n) ℤ
  map i j h := (MvPolynomial.rename (Fin.castLE h)).toRingHom
  map_self i x := by
    have h : Fin.castLE (le_refl i) = id := by funext k; exact Fin.ext rfl
    show MvPolynomial.rename (Fin.castLE (le_refl i)) x = x
    rw [h, MvPolynomial.rename_id]
    rfl
  map_map i j k hij hjk x := by
    show MvPolynomial.rename (Fin.castLE hjk) (MvPolynomial.rename (Fin.castLE hij) x) =
      MvPolynomial.rename (Fin.castLE (hij.trans hjk)) x
    rw [MvPolynomial.rename_rename]
    have hc : (Fin.castLE hjk) ∘ (Fin.castLE hij) = Fin.castLE (hij.trans hjk) := by
      funext l
      exact Fin.ext rfl
    rw [hc]

instance polySystem_isDomain (n : ℕ) : IsDomain (polySystem.A n) :=
  show IsDomain (MvPolynomial (Fin n) ℤ) from inferInstance

/-- Every component `ℤ[x_1,…,x_n]` is an integral domain, hence so is the limit. -/
theorem polySystem_isDomain_colim : IsDomain polySystem.colim := polySystem.isDomain_colim

end DirectSystemOfRings

end AtiyahMcdonald69.Ex_2_22

#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.of_eq_zero_iff
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.nilToColim_injective
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.nilToColim_range
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.isDomain_colim
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.nilradical_eq_iSup
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.exercise_2_22_nilradical
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.exercise_2_22_domain
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.nilToColim_add
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.nilToColim_zero
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.noZeroDivisors_colim
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.not_isDomain_zeroRingSystem
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.polySystem_isDomain_colim
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.subsingleton_directSum
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.isEmpty_colim
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.isEmpty_nilColim
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.not_isDomain_of_subsingleton
#print axioms AtiyahMcdonald69.Ex_2_22.DirectSystemOfRings.emptyIndex_literal_statement_fails
