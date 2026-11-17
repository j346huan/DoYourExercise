import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Exercise I.1.10

## The statement in the source

Chapter I, §1, Exercise 1.10 (verbatim):

> (a) If `Y` is any subset of a topological space `X`, then `dim Y ≤ dim X`.
> (b) If `X` is a topological space which is covered by a family of open subsets `{Uᵢ}`,
>     then `dim X = sup dim Uᵢ`.
> (c) Give an example of a topological space `X` and a dense open subset `U` with
>     `dim U < dim X`.
> (d) If `Y` is a closed subset of an irreducible finite-dimensional topological space `X`,
>     and if `dim Y = dim X`, then `Y = X`.
> (e) Give an example of a noetherian topological space of infinite dimension.

The book's definition (I.1, p. 5) is: the dimension of a topological space `X` is the
supremum of the integers `n` such that there is a chain
`Z₀ ⊊ Z₁ ⊊ … ⊊ Zₙ` of distinct irreducible closed subsets of `X`; the dimension of the
empty set is defined to be `-∞`.

## Formalisation notes

* `dim X` is Mathlib's `topologicalKrullDim X : WithBot ℕ∞`, the Krull dimension of the
  poset `IrreducibleCloseds X` of irreducible closed subsets.  `WithBot ℕ∞` contains
  `⊥ = -∞`, matching the book's convention for the empty space, and `⊤ = +∞`.
  `dim_eq_iSup_chain` below shows that this is exactly the book's definition.
* `IsIrreducible` in Mathlib means "nonempty and not a union of two proper closed
  subsets", exactly Hartshorne's notion; `isIrreducible_iff_irreducibleSpace` relates it
  to irreducibility of the subspace, the book's "irreducible in its induced topology".
* Part (a) is stated for an arbitrary subset `Y ⊆ X` with the subspace topology, i.e. as
  `dim ↥Y ≤ dim X`: that is what `dim Y` means for `Y` a subset.
-/

namespace Hartshorne77.Ex_I_1_10

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ## 1. The definition of dimension, in the book's own terms -/

/-- **Hartshorne I.1, p. 5.**  The dimension of a topological space: the supremum of the
integers `n` for which there is a chain of `n + 1` distinct irreducible closed subsets.
Values lie in `WithBot ℕ∞` so that the dimension of the empty space is `⊥ = -∞`. -/
noncomputable def dim (X : Type*) [TopologicalSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

/-- Unfolding `dim`: it is the supremum of the lengths of strictly increasing series of
irreducible closed subsets. -/
theorem dim_def (X : Type*) [TopologicalSpace X] :
    dim X = ⨆ (p : LTSeries (IrreducibleCloseds X)), (p.length : WithBot ℕ∞) := rfl

/-- A chain `Z₀ ⊊ Z₁ ⊊ … ⊊ Zₙ` of distinct irreducible closed subsets of `X`. -/
structure Chain (X : Type*) [TopologicalSpace X] (n : ℕ) where
  /-- the members of the chain -/
  toFun : Fin (n + 1) → Set X
  /-- every member is irreducible -/
  isIrred : ∀ i, IsIrreducible (toFun i)
  /-- every member is closed -/
  isClosed' : ∀ i, IsClosed (toFun i)
  /-- the chain is strictly increasing -/
  strictMono' : StrictMono toFun

namespace Chain

variable {n : ℕ}

instance : CoeFun (Chain X n) (fun _ => Fin (n + 1) → Set X) := ⟨Chain.toFun⟩

/-- A chain of irreducible closed subsets of `X` is exactly a strictly increasing series in
the poset of irreducible closed subsets. -/
def toLTSeries (c : Chain X n) : LTSeries (IrreducibleCloseds X) where
  length := n
  toFun i := ⟨c i, c.isIrred i, c.isClosed' i⟩
  step i := by
    show (⟨c (Fin.castSucc i), c.isIrred _, c.isClosed' _⟩ : IrreducibleCloseds X) <
      ⟨c i.succ, c.isIrred _, c.isClosed' _⟩
    exact c.strictMono' (Fin.castSucc_lt_succ)

@[simp] theorem length_toLTSeries (c : Chain X n) : c.toLTSeries.length = n := rfl

/-- Conversely a strictly increasing series of irreducible closed subsets is a chain. -/
def ofLTSeries (p : LTSeries (IrreducibleCloseds X)) : Chain X p.length where
  toFun i := (p i : Set X)
  isIrred i := (p i).isIrreducible
  isClosed' i := (p i).isClosed
  strictMono' := by
    intro i j hij
    refine lt_of_le_of_ne (p.monotone hij.le) ?_
    intro h
    exact hij.ne (p.strictMono.injective (IrreducibleCloseds.ext h))

end Chain

/-- **The book's definition of dimension.**  `dim X` is the supremum of the lengths `n` of
chains `Z₀ ⊊ ⋯ ⊊ Zₙ` of distinct irreducible closed subsets of `X`. -/
theorem dim_eq_iSup_chain (X : Type*) [TopologicalSpace X] :
    dim X = ⨆ (n : ℕ) (_ : Nonempty (Chain X n)), (n : WithBot ℕ∞) := by
  rw [dim_def]
  refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun n => iSup_le fun hn => ?_)
  · exact le_iSup_of_le p.length (le_iSup_of_le ⟨Chain.ofLTSeries p⟩ le_rfl)
  · obtain ⟨c⟩ := hn
    exact le_iSup_of_le c.toLTSeries (by simp)

/-- A chain of length `n` exists as soon as `n ≤ dim X`. -/
theorem nonempty_chain_iff_le_dim (n : ℕ) :
    Nonempty (Chain X n) ↔ (n : WithBot ℕ∞) ≤ dim X := by
  rw [dim, topologicalKrullDim, Order.le_krullDim_iff]
  exact ⟨fun ⟨c⟩ => ⟨c.toLTSeries, rfl⟩, fun ⟨p, hp⟩ => ⟨hp ▸ Chain.ofLTSeries p⟩⟩

/-- Chains of length `n` give lower bounds for the dimension. -/
theorem le_dim_of_chain {n : ℕ} (c : Chain X n) : (n : WithBot ℕ∞) ≤ dim X :=
  (nonempty_chain_iff_le_dim n).mp ⟨c⟩

/-- **`dim X ≤ n` means there is no chain of length `n + 1`.**  Equivalently: the dimension
is the supremum of the lengths of chains. -/
theorem dim_le_iff_chain {n : ℕ} :
    dim X ≤ (n : WithBot ℕ∞) ↔ ∀ m : ℕ, n < m → ¬ Nonempty (Chain X m) := by
  constructor
  · rintro h m hm ⟨c⟩
    have h1 : (m : WithBot ℕ∞) ≤ dim X := le_dim_of_chain c
    have h2 : (n : WithBot ℕ∞) < (m : WithBot ℕ∞) := by exact_mod_cast hm
    exact absurd h (not_le_of_gt (lt_of_lt_of_le h2 h1))
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ dim X := ENat.WithBot.add_one_le_iff.mpr hlt
    exact h (n + 1) (Nat.lt_succ_self n) ((nonempty_chain_iff_le_dim (n + 1)).mpr h1)


/-! ## 2. Part (a): dimension decreases on subsets -/

/-- **Hartshorne I.1.10 (a).**  If `Y` is any subset of a topological space `X`, then
`dim Y ≤ dim X`.

Hartshorne's proof: taking closures in `X` carries a chain of distinct irreducible closed
subsets of `Y` to a chain of the same length.  In the poset language this is exactly the
statement that `Z ↦ closure (Subtype.val '' Z)` is strictly monotone from the irreducible
closed subsets of `Y` to those of `X` (`IrreducibleCloseds.map_strictMono_of_isInducing`),
which strictly monotone map gives `krullDim_le_of_strictMono`. -/
theorem dim_subtype_le (Y : Set X) : dim ↥Y ≤ dim X :=
  Order.krullDim_le_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal)

/-! ## 3. Part (b): dimension is the supremum over an open cover -/

/-- **Restriction of a chain to a nonempty relatively open piece.**  If `U` is open and meets
the smallest member of a chain of irreducible closed subsets, then intersecting every member
with `U` gives a chain of the *same* length inside the subspace `U`.

This is Hartshorne's step "each `Uᵢ ∩ Z_j` is irreducible and dense in `Z_j`, so the
intersections are distinct". -/
def Chain.restrict {U : Set X} (hU : IsOpen U) (c : Chain X n) (hne : (c 0 ∩ U).Nonempty) :
    Chain ↥U n where
  toFun i := (Subtype.val : ↥U → X) ⁻¹' (c i)
  isIrred i := by
    have h0i : c 0 ⊆ c i := c.strictMono'.monotone (Fin.zero_le i)
    have hnei : (c i ∩ U).Nonempty := hne.mono fun x hx => ⟨h0i hx.1, hx.2⟩
    have hpre : (c i ∩ Set.range (Subtype.val : ↥U → X)).Nonempty := by
      simpa [Subtype.range_val] using hnei
    exact (c.isIrred i).preimage hU.isOpenEmbedding_subtypeVal hpre
  isClosed' i := (c.isClosed' i).preimage continuous_subtype_val
  strictMono' := by
    intro i j hij
    have hlt : c i < c j := c.strictMono' hij
    have h0j : c 0 ⊆ c j := c.strictMono'.monotone (Fin.zero_le j)
    have hneU : (c j ∩ U).Nonempty := hne.mono fun x hx => ⟨h0j hx.1, hx.2⟩
    obtain ⟨x, hxj, hxi⟩ := Set.exists_of_ssubset hlt
    obtain ⟨y, hyj, hyi, hyU⟩ :
        ∃ y, y ∈ c j ∧ y ∉ c i ∧ y ∈ U := by
      obtain ⟨y, hy⟩ := (c.isIrred j).isPreirreducible (c i)ᶜ U
        (c.isClosed' i).isOpen_compl hU ⟨x, hxj, hxi⟩ hneU
      exact ⟨y, hy.1, hy.2.1, hy.2.2⟩
    have hle : (Subtype.val : ↥U → X) ⁻¹' (c i) ⊆ (Subtype.val : ↥U → X) ⁻¹' (c j) :=
      fun z hz => hlt.le hz
    refine lt_of_le_of_ne hle ?_
    intro heq
    have heq' : (Subtype.val : ↥U → X) ⁻¹' (c i) = (Subtype.val : ↥U → X) ⁻¹' (c j) := heq
    have hmem : (⟨y, hyU⟩ : ↥U) ∈ (Subtype.val : ↥U → X) ⁻¹' (c i) := by
      rw [heq']; exact hyj
    exact hyi hmem

/-- **Hartshorne I.1.10 (b).**  If `X` is covered by a family of open subsets `{Uᵢ}`, then
`dim X = sup dim Uᵢ`. -/
theorem dim_eq_iSup_of_isOpen_cover {ι : Type*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    dim X = ⨆ i, dim ↥(U i) := by
  refine le_antisymm ?_ (iSup_le fun i => dim_subtype_le (U i))
  rw [dim_def]
  refine iSup_le fun p => ?_
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.nonempty
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  simp only [Set.mem_iUnion] at hxU
  obtain ⟨i, hi⟩ := hxU
  have hne : (Chain.ofLTSeries p 0 ∩ U i).Nonempty := ⟨x, hx, hi⟩
  have hchain : ((p.length : WithBot ℕ∞)) ≤ dim ↥(U i) :=
    le_dim_of_chain ((Chain.ofLTSeries p).restrict (hU i) hne)
  exact le_trans hchain (le_iSup (fun i => dim ↥(U i)) i)


/-! ## 4. Part (d): a closed subset of full dimension in an irreducible space -/

/-- In an irreducible space the whole space is the largest irreducible closed subset. -/
instance instOrderTopIrreducibleCloseds [IrreducibleSpace X] : OrderTop (IrreducibleCloseds X) where
  top := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  le_top _ := subset_univ _

/-- An irreducible space has nonnegative dimension: only the empty space has dimension
`-∞`. -/
theorem dim_pos [IrreducibleSpace X] : ⊥ < dim X :=
  Order.bot_lt_krullDim

/-- **Hartshorne I.1.10 (d).**  If `Y` is a closed subset of an irreducible
finite-dimensional topological space `X`, and if `dim Y = dim X`, then `Y = X`.

Hartshorne's proof: a chain of length `n = dim Y` in `Y` is a chain of closed irreducible
subsets of `X` ending in `Y`; if `Y ≠ X` one can append `X`, giving a chain of length
`n + 1` in `X`, contradicting `dim X = n`.  Formalised here with heights: the chain of
length `n` ending at `Y` shows `n ≤ height Y`, while `Y < X = ⊤` shows
`height Y + 1 ≤ height ⊤ = dim X = n`. -/
theorem eq_univ_of_isClosed_of_dim_eq [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hfin : dim X ≠ ⊤) (hdim : dim ↥Y = dim X) : Y = univ := by
  classical
  -- `dim X` is a natural number
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ne_of_gt (dim_pos (X := X)))
  have hnetop : m ≠ ⊤ := by rintro rfl; exact hfin hm.symm
  obtain ⟨n, hn'⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hn : dim X = (n : WithBot ℕ∞) := by rw [← hm, ← hn']; simp
  -- a chain of length `n` in `Y`
  have h1 : (n : WithBot ℕ∞) ≤ dim ↥Y := by rw [hdim, hn]
  obtain ⟨c⟩ := (nonempty_chain_iff_le_dim (X := ↥Y) n).mpr h1
  -- push it into `X` by taking closures of the images
  let W : LTSeries (IrreducibleCloseds X) :=
    c.toLTSeries.map (fun Z => IrreducibleCloseds.map (Subtype.val : ↥Y → X) continuous_subtype_val Z)
      (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal)
  have hWlen : W.length = n := by simp [W]
  -- the largest member of the pushed-forward chain lies in `Y`
  have hlast : (↑(W.last) : Set X) ⊆ Y := by
    have h : ((W.last : IrreducibleCloseds X) : Set X) =
        closure (Subtype.val '' (c.toLTSeries.last : Set ↥Y)) := by
      simp [W]
    rw [h, hY.closure_subset_iff]
    rintro z ⟨w, -, rfl⟩
    exact w.2
  by_contra hYne
  have hproper : W.last < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    apply hYne
    refine eq_univ_of_univ_subset ?_
    rw [show (univ : Set X) = (↑(W.last) : Set X) from by rw [h]; rfl]
    exact hlast
  -- `n ≤ height W.last` and `height W.last + 1 ≤ height ⊤ = dim X = n`
  have h2 : (n : WithBot ℕ∞) ≤ ((Order.height W.last : ℕ∞) : WithBot ℕ∞) := by
    have h := Order.length_le_height_last (p := W)
    have h' := WithBot.coe_le_coe.mpr h
    simpa [hWlen] using h'
  have h3 : ((Order.height W.last : ℕ∞) : WithBot ℕ∞) + 1 ≤ (n : WithBot ℕ∞) := by
    have h4 : Order.height W.last + 1 ≤ Order.height (⊤ : IrreducibleCloseds X) :=
      Order.height_add_one_le hproper
    have h5 : ((Order.height W.last : ℕ∞) : WithBot ℕ∞) + 1 ≤
        ((Order.height (⊤ : IrreducibleCloseds X) : ℕ∞) : WithBot ℕ∞) := by
      rw [← WithBot.coe_one, ← WithBot.coe_add]
      exact WithBot.coe_le_coe.mpr h4
    have h6 : ((Order.height (⊤ : IrreducibleCloseds X) : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [Order.height_top_eq_krullDim, ← hn]
      rfl
    rwa [h6] at h5
  have h7 : (n : WithBot ℕ∞) + 1 ≤ (n : WithBot ℕ∞) := le_trans (add_le_add h2 le_rfl) h3
  exact absurd h7 (by rw [ENat.WithBot.add_one_le_iff]; exact lt_irrefl _)


/-! ## 5. Set-theoretic toolkit for the examples

Both examples below have closed sets of the shape "initial segments of a level function,
plus the whole space".  This section supplies the set-theoretic closure properties.
-/

section LevelSets

variable {X : Type*}

/-- The initial segment `{x | level x < n}`. -/
def initSeg (level : X → ℕ) (n : ℕ) : Set X := {x | level x < n}

@[simp] theorem mem_initSeg {level : X → ℕ} {n : ℕ} {x : X} :
    x ∈ initSeg level n ↔ level x < n := Iff.rfl

/-- The closed sets of a level space: every initial segment `{x | level x < n}` and the
whole space. -/
def levelCloseds (level : X → ℕ) : Set (Set X) := Set.range (initSeg level) ∪ {univ}

theorem empty_mem_levelCloseds (level : X → ℕ) : (∅ : Set X) ∈ levelCloseds level :=
  Or.inl ⟨0, by ext x; simp⟩

theorem sInter_mem_levelCloseds (level : X → ℕ) {A : Set (Set X)}
    (hA : A ⊆ levelCloseds level) : ⋂₀ A ∈ levelCloseds level := by
  classical
  by_cases hAe : A = ∅
  · subst hAe; exact Or.inr (by simp)
  · by_cases hB : A \ {univ} = ∅
    · have hall : ∀ s ∈ A, s = univ := by
        intro s hs
        by_contra h
        have hmem : s ∈ A \ {univ} := ⟨hs, by simpa using h⟩
        rw [hB] at hmem
        exact hmem
      have hInter : ⋂₀ A = univ := by
        ext x
        simp only [Set.mem_sInter, Set.mem_univ, iff_true]
        exact fun s hs => by rw [hall s hs]; trivial
      rw [hInter]; exact Or.inr rfl
    · set N : Set ℕ := {n | initSeg level n ∈ A \ {univ}} with hN
      have hNne : N.Nonempty := by
        obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hB
        have hsA : s ∈ A := hs.1
        have hsu : s ≠ univ := by simpa using hs.2
        rcases hA hsA with ⟨n, hn⟩ | huniv
        · exact ⟨n, by simp [hN, hn, hsA, hsu]⟩
        · exact absurd huniv hsu
      have hInter : ⋂₀ A = initSeg level (sInf N) := by
        ext x
        simp only [Set.mem_sInter, mem_initSeg]
        constructor
        · intro hx
          exact hx _ (Nat.sInf_mem hNne).1
        · intro hx s hs
          by_cases hsu : s = univ
          · rw [hsu]; trivial
          · rcases hA hs with ⟨n, hn⟩ | huniv
            · have hnN : n ∈ N := by simp [hN, hn, hs, hsu]
              rw [← hn]
              exact lt_of_lt_of_le hx (Nat.sInf_le hnN)
            · exact absurd huniv hsu
      rw [hInter]; exact Or.inl ⟨_, rfl⟩

theorem union_mem_levelCloseds (level : X → ℕ) {A B : Set X}
    (hA : A ∈ levelCloseds level) (hB : B ∈ levelCloseds level) :
    A ∪ B ∈ levelCloseds level := by
  rcases hA with ⟨m, rfl⟩ | rfl <;> rcases hB with ⟨n, rfl⟩ | rfl
  · refine Or.inl ⟨max m n, ?_⟩
    ext x
    simp only [Set.mem_union, mem_initSeg]
    omega
  · rw [Set.union_univ]; exact Or.inr rfl
  · rw [Set.univ_union]; exact Or.inr rfl
  · rw [Set.union_self]; exact Or.inr rfl

end LevelSets

/-! ## 6. Part (c): a dense open subset of smaller dimension -/

/-- The two-point space of the example in part (c): `p` has level `0`, `q` has level `1`;
the closed sets are `∅`, `{p}` and the whole space. -/
inductive TwoPoint : Type
  | p : TwoPoint
  | q : TwoPoint

namespace TwoPoint

/-- The level of a point. -/
def level : TwoPoint → ℕ
  | p => 0
  | q => 1

instance : TopologicalSpace TwoPoint where
  IsOpen s := sᶜ ∈ levelCloseds level
  isOpen_univ := by simpa using empty_mem_levelCloseds level
  isOpen_inter s t hs ht := by
    simpa only [compl_inter] using union_mem_levelCloseds level hs ht
  isOpen_sUnion S hS := by
    have h : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) := Set.compl_sUnion S
    rw [h]
    exact sInter_mem_levelCloseds level (by rintro _ ⟨s, hs, rfl⟩; exact hS s hs)

theorem isClosed_iff {s : Set TwoPoint} :
    IsClosed s ↔ s = univ ∨ ∃ n, s = initSeg level n := by
  have h1 : IsClosed s ↔ IsOpen sᶜ := ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩
  have h2 : IsOpen sᶜ ↔ sᶜᶜ ∈ levelCloseds level := Iff.rfl
  rw [h1, h2, compl_compl, levelCloseds]
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  tauto

theorem isOpen_iff {s : Set TwoPoint} :
    IsOpen s ↔ s = ∅ ∨ s = univ ∨ ∃ n, s = {x | n ≤ level x} := by
  have hmem : IsOpen s ↔ sᶜ ∈ levelCloseds level := Iff.rfl
  rw [hmem, levelCloseds]
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro (⟨n, hn⟩ | hc)
    · refine Or.inr (Or.inr ⟨n, ?_⟩)
      have hs : s = (initSeg level n)ᶜ := by rw [hn, compl_compl]
      rw [hs]
      ext x
      show ¬ (level x < n) ↔ n ≤ level x
      omega
    · exact Or.inl (by rw [← compl_compl s, hc]; simp)
  · rintro (rfl | rfl | ⟨n, rfl⟩)
    · rw [compl_empty]
      exact Or.inr rfl
    · exact Or.inl ⟨0, by simp [initSeg]⟩
    · refine Or.inl ⟨n, ?_⟩
      ext x
      show level x < n ↔ ¬ (n ≤ level x)
      omega

/-- The closed subsets of the two-point space are `∅`, `{p}` and the whole space. -/
theorem isClosed_cases {s : Set TwoPoint} (hs : IsClosed s) :
    s = ∅ ∨ s = {p} ∨ s = univ := by
  rw [isClosed_iff] at hs
  rcases hs with rfl | ⟨n, rfl⟩
  · exact Or.inr (Or.inr rfl)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (by ext x; simp [initSeg])
    · rcases eq_or_lt_of_le (show 1 ≤ n from hn) with h1 | h2
      · exact Or.inr (Or.inl (by
          rw [← h1]
          ext x
          cases x <;> simp [initSeg, level]))
      · exact Or.inr (Or.inr (by
          ext x
          cases x <;> simp [initSeg, level] <;> omega))

instance : PreirreducibleSpace TwoPoint where
  isPreirreducible_univ := by
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro F G hF hG hcov
    rcases isClosed_cases hF with rfl | rfl | rfl <;>
      rcases isClosed_cases hG with rfl | rfl | rfl
    · exact absurd (hcov (mem_univ p)) (by simp)
    · exact absurd (hcov (mem_univ q)) (by simp)
    · exact Or.inr (subset_univ _)
    · exact absurd (hcov (mem_univ q)) (by simp)
    · exact absurd (hcov (mem_univ q)) (by simp)
    · exact Or.inr (subset_univ _)
    · exact Or.inl (subset_univ _)
    · exact Or.inl (subset_univ _)
    · exact Or.inl (subset_univ _)

instance : IrreducibleSpace TwoPoint := ⟨⟨p⟩⟩

/-- The irreducible closed subsets of the two-point space are `{p}` and the whole space. -/
theorem isIrreducibleCloseds_cases (x : IrreducibleCloseds TwoPoint) :
    (x : Set TwoPoint) = {p} ∨ (x : Set TwoPoint) = univ := by
  rcases isClosed_cases x.isClosed with h | h | h
  · exact absurd h (fun h => by simpa [h] using x.isIrreducible.nonempty)
  · exact Or.inl h
  · exact Or.inr h

/-- A one-point space has dimension at most `0`. -/
theorem dim_singleton_le (x : TwoPoint) : dim ↥({x} : Set TwoPoint) ≤ 0 := by
  have hdim : dim ↥({x} : Set TwoPoint) =
      Order.krullDim (IrreducibleCloseds ↥({x} : Set TwoPoint)) := rfl
  rw [hdim, Order.krullDim_nonpos_iff_forall_isMax]
  intro a b _
  rw [← SetLike.coe_subset_coe]
  intro y _
  obtain ⟨z, hz⟩ := a.isIrreducible.nonempty
  have hyz : y = z := Subsingleton.elim y z
  rw [hyz]; exact hz

theorem isClosed_singleton_p : IsClosed ({p} : Set TwoPoint) := by
  rw [isClosed_iff]; exact Or.inr ⟨1, by ext x; cases x <;> simp [initSeg, level]⟩

theorem isIrreducible_singleton_p : IsIrreducible ({p} : Set TwoPoint) := isIrreducible_singleton

theorem isOpen_singleton_q : IsOpen ({q} : Set TwoPoint) := by
  rw [isOpen_iff]
  refine Or.inr (Or.inr ⟨1, ?_⟩)
  ext x
  cases x <;> simp [level]

/-- The nonempty open subset `{q}` of the two-point space is dense. -/
theorem dense_singleton_q : Dense ({q} : Set TwoPoint) := by
  rw [dense_iff_closure_eq]
  rcases isClosed_cases isClosed_closure with h | h | h
  · exact absurd (subset_closure (mem_singleton q)) (by rw [h]; simp)
  · exact absurd (subset_closure (mem_singleton q)) (by rw [h]; simp)
  · exact h

/-- The two-point space has dimension `1`. -/
theorem dim_eq_one : dim TwoPoint = 1 := by
  have hdim : dim TwoPoint = Order.krullDim (IrreducibleCloseds TwoPoint) := rfl
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_le_one_iff]
    intro z
    have hnot : ¬ ((univ : Set TwoPoint) ⊆ ({p} : Set TwoPoint)) := by
      intro hh
      have hq : q ∈ ({p} : Set TwoPoint) := hh (mem_univ q)
      simp at hq
    rcases isIrreducibleCloseds_cases z with h | h
    · refine Or.inl ?_
      intro w hw
      rcases isIrreducibleCloseds_cases w with h' | h'
      · exact le_of_eq (IrreducibleCloseds.ext (by rw [h, h']))
      · rw [← SetLike.coe_subset_coe] at hw
        rw [h, h'] at hw
        exact absurd hw hnot
    · refine Or.inr ?_
      intro w hw
      rcases isIrreducibleCloseds_cases w with h' | h'
      · rw [← SetLike.coe_subset_coe] at hw
        rw [h, h'] at hw
        exact absurd hw hnot
      · exact le_of_eq (IrreducibleCloseds.ext (by rw [h, h']))
  · rw [Order.one_le_krullDim_iff]
    refine ⟨⟨{p}, isIrreducible_singleton_p, isClosed_singleton_p⟩,
      ⟨univ, IrreducibleSpace.isIrreducible_univ TwoPoint, isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne (subset_univ _) ?_
    intro h
    have h' : ({p} : Set TwoPoint) = univ :=
      congrArg (fun z : IrreducibleCloseds TwoPoint => (z : Set TwoPoint)) h
    have hq : q ∈ ({p} : Set TwoPoint) := by rw [h']; trivial
    simp at hq

/-- **Hartshorne I.1.10 (c).**  The two-point space has a dense open subset `{q}` of
dimension strictly smaller than `dim X = 1`. -/
theorem part_c : ∃ U : Set TwoPoint, IsOpen U ∧ Dense U ∧ dim ↥U < dim TwoPoint :=
  ⟨{q}, isOpen_singleton_q, dense_singleton_q, by
    have h := dim_singleton_le q
    rw [dim_eq_one]
    exact lt_of_le_of_lt h (by decide)⟩

end TwoPoint

/-! ## 7. Part (e): a noetherian space of infinite dimension -/

/-- The underlying set of the example in part (e): one point for each natural number; the
closed sets are the initial segments `{0, …, k-1}` and the whole space. -/
structure NatChain : Type where
  /-- the natural number attached to the point -/
  n : ℕ

namespace NatChain

/-- The level of a point. -/
def level : NatChain → ℕ := NatChain.n

instance : TopologicalSpace NatChain where
  IsOpen s := sᶜ ∈ levelCloseds level
  isOpen_univ := by simpa using empty_mem_levelCloseds level
  isOpen_inter s t hs ht := by
    simpa only [compl_inter] using union_mem_levelCloseds level hs ht
  isOpen_sUnion S hS := by
    have h : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) := Set.compl_sUnion S
    rw [h]
    exact sInter_mem_levelCloseds level (by rintro _ ⟨s, hs, rfl⟩; exact hS s hs)

theorem isClosed_iff {s : Set NatChain} :
    IsClosed s ↔ s = univ ∨ ∃ n, s = {x : NatChain | x.n < n} := by
  have h1 : IsClosed s ↔ IsOpen sᶜ := ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩
  have h2 : IsOpen sᶜ ↔ sᶜᶜ ∈ levelCloseds level := Iff.rfl
  rw [h1, h2, compl_compl, levelCloseds]
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, initSeg, level]
  tauto

theorem isOpen_iff {s : Set NatChain} :
    IsOpen s ↔ s = ∅ ∨ s = univ ∨ ∃ n, s = {x : NatChain | n ≤ x.n} := by
  have hmem : IsOpen s ↔ sᶜ ∈ levelCloseds level := Iff.rfl
  rw [hmem, levelCloseds]
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, initSeg, level]
  constructor
  · rintro (⟨n, hn⟩ | hc)
    · refine Or.inr (Or.inr ⟨n, ?_⟩)
      have hs : s = {x : NatChain | x.n < n}ᶜ := by rw [hn, compl_compl]
      rw [hs]
      ext x
      show ¬ (x.n < n) ↔ n ≤ x.n
      omega
    · exact Or.inl (by rw [← compl_compl s, hc]; simp)
  · rintro (rfl | rfl | ⟨n, rfl⟩)
    · rw [compl_empty]
      exact Or.inr rfl
    · exact Or.inl ⟨0, by ext x; simp⟩
    · refine Or.inl ⟨n, ?_⟩
      ext x
      show x.n < n ↔ ¬ (n ≤ x.n)
      omega

theorem level_zero : ∃ x : NatChain, x.n = 0 := ⟨⟨0⟩, rfl⟩

theorem level_surj : ∀ m, ∃ x : NatChain, x.n = m := fun m => ⟨⟨m⟩, rfl⟩

instance : IrreducibleSpace NatChain where
  toNonempty := ⟨⟨0⟩⟩
  isPreirreducible_univ := by
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro F G hF hG hcov
    rw [isClosed_iff] at hF hG
    rcases hF with rfl | ⟨a, rfl⟩
    · exact Or.inl (subset_univ _)
    rcases hG with rfl | ⟨b, rfl⟩
    · exact Or.inr (subset_univ _)
    obtain ⟨x, hx⟩ := level_surj (max a b)
    have hxm : x ∈ ({x : NatChain | x.n < a} ∪ {x : NatChain | x.n < b}) :=
      hcov (mem_univ x)
    rcases hxm with h | h
    · have h' : x.n < a := h
      omega
    · have h' : x.n < b := h
      omega

/-- **Hartshorne I.1.10 (e).**  The space of natural numbers with closed sets the initial
segments is noetherian and of infinite dimension. -/
theorem noetherian_and_dim_top : NoetherianSpace NatChain ∧ dim NatChain = ⊤ := by
  constructor
  · rw [noetherianSpace_iff_opens]
    intro s
    rw [isCompact_iff_finite_subcover]
    intro ι U hU hcov
    rcases isOpen_iff.mp s.2 with hcase | hcase | ⟨k, hcase⟩
    · have h' : (s : Set NatChain) = ∅ := hcase
      rw [h'] at hcov ⊢
      exact ⟨∅, by simp⟩
    · have h' : (s : Set NatChain) = univ := hcase
      rw [h'] at hcov ⊢
      obtain ⟨i, hi⟩ : ∃ i, (⟨0⟩ : NatChain) ∈ U i := by
        have h : (⟨0⟩ : NatChain) ∈ ⋃ i, U i := hcov (mem_univ _)
        exact Set.mem_iUnion.mp h
      rcases isOpen_iff.mp (hU i) with h | h | ⟨m, hm⟩
      · rw [h] at hi; exact absurd hi (by simp)
      · refine ⟨{i}, ?_⟩
        intro x _
        simp [h]
      · have hm0 : m = 0 := by
          have hle : m ≤ (⟨0⟩ : NatChain).n := by rw [hm] at hi; simpa using hi
          simpa using hle
        refine ⟨{i}, ?_⟩
        intro x _
        exact Set.mem_iUnion.mpr ⟨i, by
          rw [hm]
          simp [hm0]⟩
    · have h' : (s : Set NatChain) = {x : NatChain | k ≤ x.n} := hcase
      rw [h'] at hcov ⊢
      obtain ⟨i, hi⟩ : ∃ i, (⟨k⟩ : NatChain) ∈ U i := by
        have h : (⟨k⟩ : NatChain) ∈ ⋃ i, U i := hcov (by simp)
        exact Set.mem_iUnion.mp h
      rcases isOpen_iff.mp (hU i) with h | h | ⟨m, hm⟩
      · rw [h] at hi; exact absurd hi (by simp)
      · refine ⟨{i}, ?_⟩
        intro x _
        simp [h]
      · have hmk : m ≤ k := by rw [hm] at hi; simpa using hi
        refine ⟨{i}, ?_⟩
        intro x hx
        have hx' : m ≤ x.n := le_trans hmk (by simpa using hx)
        simp only [Set.mem_iUnion, Finset.mem_singleton, exists_prop]
        exact ⟨i, rfl, by rw [hm]; simpa using hx'⟩
  · rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    refine le_dim_of_chain (n := n) ?_
    refine
      { toFun := fun i => {x : NatChain | x.n < (i : ℕ) + 1}
        isIrred := ?_
        isClosed' := ?_
        strictMono' := ?_ }
    · intro i
      refine ⟨⟨⟨0⟩, by simp⟩, ?_⟩
      rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro F G hF hG hcov
      rw [isClosed_iff] at hF hG
      rcases hF with rfl | ⟨a, rfl⟩
      · exact Or.inl (subset_univ _)
      rcases hG with rfl | ⟨b, rfl⟩
      · exact Or.inr (subset_univ _)
      by_cases ha : ((i : ℕ) + 1) ≤ a
      · exact Or.inl fun x hx => by
          have hx' : x.n < (i : ℕ) + 1 := hx
          show x.n < a
          omega
      by_cases hb : ((i : ℕ) + 1) ≤ b
      · exact Or.inr fun x hx => by
          have hx' : x.n < (i : ℕ) + 1 := hx
          show x.n < b
          omega
      push Not at ha hb
      obtain ⟨x, hx⟩ := level_surj (max a b)
      have hxi : x.n < (i : ℕ) + 1 := by omega
      have hxm : x ∈ ({x : NatChain | x.n < a} ∪ {x : NatChain | x.n < b}) :=
        hcov hxi
      rcases hxm with h | h
      · have h' : x.n < a := h
        omega
      · have h' : x.n < b := h
        omega
    · intro i
      rw [isClosed_iff]
      exact Or.inr ⟨(i : ℕ) + 1, rfl⟩
    · intro i j hij
      refine lt_of_le_of_ne (fun x hx => ?_) ?_
      · have hx' : x.n < (i : ℕ) + 1 := hx
        show x.n < (j : ℕ) + 1
        omega
      · intro heq
        obtain ⟨x, hx⟩ := level_surj ((i : ℕ) + 1)
        have hmem : x ∈ ({x : NatChain | x.n < (j : ℕ) + 1}) := by
          show x.n < (j : ℕ) + 1
          omega
        have heq' : ({x : NatChain | x.n < (i : ℕ) + 1} : Set NatChain) =
            {x : NatChain | x.n < (j : ℕ) + 1} := heq
        rw [← heq'] at hmem
        have hmem' : x.n < (i : ℕ) + 1 := hmem
        omega

end NatChain

/-! ## 8. The exercise as a single statement -/

/-- **Hartshorne, *Algebraic Geometry* (1977), Exercise I.1.10**, all five parts.

(a) dimension does not increase on passing to a subset;
(b) dimension is the supremum over any open cover;
(c) an example of a dense open subset of strictly smaller dimension;
(d) a closed subset of full dimension of an irreducible finite-dimensional space is the
    whole space;
(e) an example of a noetherian space of infinite dimension. -/
theorem hartshorne_ex_1_10 :
    (∀ (X : Type) [TopologicalSpace X] (Y : Set X), dim ↥Y ≤ dim X) ∧
    (∀ (X : Type) [TopologicalSpace X] {ι : Type} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → ⋃ i, U i = univ → dim X = ⨆ i, dim ↥(U i)) ∧
    (∃ U : Set TwoPoint, IsOpen U ∧ Dense U ∧ dim ↥U < dim TwoPoint) ∧
    (∀ (X : Type) [TopologicalSpace X] [IrreducibleSpace X] (Y : Set X), IsClosed Y →
      dim X ≠ ⊤ → dim ↥Y = dim X → Y = univ) ∧
    (NoetherianSpace NatChain ∧ dim NatChain = ⊤) :=
  ⟨fun _ _ Y => dim_subtype_le Y,
   fun _ _ _ _U hU hcov => dim_eq_iSup_of_isOpen_cover hU hcov,
   TwoPoint.part_c,
   fun _ _ _ _Y hY hfin hdim => eq_univ_of_isClosed_of_dim_eq hY hfin hdim,
   NatChain.noetherian_and_dim_top⟩

end Hartshorne77.Ex_I_1_10
