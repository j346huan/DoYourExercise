import Mathlib
open MvPolynomial Set Topology

/-!
# Hartshorne (1977), *Algebraic Geometry*, Chapter I, Exercise 2.7

Formalization of

> **Exercise I.2.7.** (a) `dim ℙ^n = n`.
> (b) If `Y ⊆ ℙ^n` is a quasi-projective variety, then `dim Y = dim Ȳ`.

## The model

* `Projectivization k (Fin (n+1) → k)` is the classical projective space `ℙ^n`: the quotient of
  the nonzero vectors of `k^{n+1}` by scaling, i.e. the set of lines through the origin.
* `Vanish f P` says that `f` vanishes on the line `P` (evaluated at the canonical
  representative); for homogeneous `f` this is independent of the representative
  (`vanish_mk`, using the scaling law `eval_smul_of_isHomogeneous`).
* `V S` is the zero locus of a set of polynomials, and the Zariski topology on `ℙ^n` is the
  topology whose closed sets are the zero loci of *homogeneous* polynomials
  (`projClosedFamily`, `projTop`, `isClosed_V`).
* `Aff σ k = σ → k` is affine space with the Zariski topology whose closed sets are the zero
  loci of ideals (`zloc`, `affTop`).
* `chartPoint i : 𝔸^{n} → ℙ^n` is the chart map `y ↦ (y,1)` of the chart `U_i = {x_i ≠ 0}`;
  `chartCoord i` is its inverse on `U_i` (`chartPoint_chartCoord`, `chartCoord_chartPoint`),
  `U i` is open (`isOpen_U`), and `chartPiece i Y` is the affine model of `Y ∩ U_i`.
* `dimTop X` is Hartshorne's dimension of a topological space (Definition I.1.6): the supremum
  of the lengths of chains of distinct irreducible closed subsets, implemented as the Krull
  dimension of the poset of nonempty irreducible closed subsets.
  `dimSet X S` is the same for a subset `S` with the subspace topology; `dimSet_univ` identifies
  the two.
* `dimProj Y = ⨆ i, dimSet (𝔸^{J i}) (closure (chartPiece i Y))` is Hartshorne's dimension of a
  (quasi-)projective variety, computed on the affine charts exactly as in the proof of I.2.7.

## Main results

* `dimTop_aff : dim 𝔸^σ = Nat.card σ` (so `dim 𝔸^n = n`), via the order correspondence between
  nonempty irreducible closed subsets and prime ideals and
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
* `dim_projective_space : dimProj ℙ^n = n` (Exercise I.2.7 (a)).
* `dimProj_closure : dimProj Y = dimProj Ȳ` for every `Y ⊆ ℙ^n`, and its quasi-projective form
  `dim_eq_dim_closure_of_isQuasiProjective` (Exercise I.2.7 (b)).
* `exercise_2_7` bundles (a) and (b).

The key geometric input for (b) is that the chart pieces of `Y` and of `Ȳ` have the same
closure in the affine chart: `chartPiece i Ȳ ⊆ closure (chartPiece i Y)`, proved by
homogenization (`homog`, `eval_homog`) together with the closedness of zero loci of homogeneous
polynomials and the fact that a dense subset meets an open chart densely (`closure_inter_subset`).
-/


namespace Hartshorne77.Ex_I_2_7
set_option linter.unusedSectionVars false
noncomputable section
variable {k : Type*} [Field k] [IsAlgClosed k]

abbrev Aff (σ : Type*) (k : Type*) : Type _ := σ → k

/-- Zero locus of an ideal, as a set of points of `𝔸^σ`. -/
def zloc (σ : Type*) (k : Type*) [Field k] (I : Ideal (MvPolynomial σ k)) : Set (Aff σ k) :=
  MvPolynomial.zeroLocus (K := k) I

lemma zeroLocus_mul (σ : Type*) (I J : Ideal (MvPolynomial σ k)) :
    zloc σ k (I * J) = zloc σ k I ∪ zloc σ k J := by
  ext x
  simp only [zloc, Set.mem_union, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h
    by_cases h1 : ∀ p ∈ I, MvPolynomial.aeval x p = 0
    · exact Or.inl h1
    · right
      push Not at h1
      obtain ⟨p, hp, hp0⟩ := h1
      intro q hq
      have hpq := h (p * q) (Ideal.mul_mem_mul hp hq)
      rw [map_mul] at hpq
      exact (mul_eq_zero.mp hpq).resolve_left hp0
  · rintro (h | h) p hp
    · exact h p (Ideal.mul_le_left hp)
    · exact h p (Ideal.mul_le_right hp)

instance affTop (σ : Type*) : TopologicalSpace (Aff σ k) :=
  TopologicalSpace.ofClosed (Set.range (zloc σ k))
    ⟨⊤, by simp [zloc]⟩
    (fun A hA => by
      refine ⟨MvPolynomial.vanishingIdeal k (⋂₀ A), ?_⟩
      refine subset_antisymm (fun x hx => ?_)
        (MvPolynomial.zeroLocus_vanishingIdeal_le (k := k) (K := k) (⋂₀ A))
      rw [zloc, MvPolynomial.mem_zeroLocus_iff] at hx
      intro t ht
      obtain ⟨I, rfl⟩ := hA ht
      rw [zloc, MvPolynomial.mem_zeroLocus_iff]
      intro p hp
      refine hx p (MvPolynomial.mem_vanishingIdeal_iff.mpr fun z hz => ?_)
      exact MvPolynomial.mem_vanishingIdeal_iff.mp
        (MvPolynomial.vanishingIdeal_anti_mono (sInter_subset_of_mem ht)
          (MvPolynomial.le_vanishingIdeal_zeroLocus I hp)) z hz)
    (fun A hA B hB => by
      obtain ⟨I, rfl⟩ := hA
      obtain ⟨J, rfl⟩ := hB
      exact ⟨I * J, zeroLocus_mul σ I J⟩)

lemma isOpen_aff_iff (σ : Type*) (U : Set (Aff σ k)) :
    IsOpen U ↔ ∃ I : Ideal (MvPolynomial σ k), zloc σ k I = Uᶜ := by
  constructor
  · intro h; exact h
  · rintro ⟨I, hI⟩
    show Uᶜ ∈ Set.range (zloc σ k)
    rw [← hI]
    exact ⟨I, rfl⟩

lemma isClosed_aff_iff (σ : Type*) (S : Set (Aff σ k)) :
    IsClosed S ↔ ∃ I : Ideal (MvPolynomial σ k), zloc σ k I = S := by
  constructor
  · intro hS
    have h : ∃ I, zloc σ k I = (Sᶜ)ᶜ := (isOpen_aff_iff σ Sᶜ).mp hS.isOpen_compl
    rwa [compl_compl] at h
  · rintro ⟨I, rfl⟩
    exact ⟨(isOpen_aff_iff σ (zloc σ k I)ᶜ).mpr ⟨I, by rw [compl_compl]⟩⟩

lemma isClosed_zloc (σ : Type*) (I : Ideal (MvPolynomial σ k)) :
    IsClosed (zloc σ k I) := (isClosed_aff_iff σ _).mpr ⟨I, rfl⟩

/-- The zero locus of an ideal and of its radical agree. -/
lemma zeroLocus_radical (σ : Type*) [Fintype σ] (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus (K := k) I.radical = MvPolynomial.zeroLocus (K := k) I := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I]
  refine le_antisymm (MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_vanishingIdeal_zeroLocus I)) ?_
  intro x hx
  rw [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
  exact fun p hp => hp x hx

/-- For a closed set, the zero locus of its vanishing ideal is itself. -/
lemma zeroLocus_vanishingIdeal_eq {σ : Type*} [Fintype σ] {S : Set (Aff σ k)}
    (hS : IsClosed S) : zloc σ k (MvPolynomial.vanishingIdeal k S) = S := by
  obtain ⟨I, rfl⟩ := (isClosed_aff_iff σ S).mp hS
  simp only [zloc]
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k), zeroLocus_radical]

/-- For any set `S`, the closure of `S` is the zero locus of its vanishing ideal. -/
lemma closure_eq_zloc_vanishingIdeal (σ : Type*) (S : Set (Aff σ k)) :
    closure S = zloc σ k (MvPolynomial.vanishingIdeal k S) := by
  refine subset_antisymm ?_ ?_
  · exact closure_minimal (MvPolynomial.zeroLocus_vanishingIdeal_le (k := k) (K := k) S)
      (isClosed_zloc σ _)
  · obtain ⟨J, hJ⟩ := (isClosed_aff_iff σ (closure S)).mp isClosed_closure
    rw [← hJ]
    refine MvPolynomial.zeroLocus_anti_mono ?_
    intro f hf
    have h1 : f ∈ MvPolynomial.vanishingIdeal k (zloc σ k J) :=
      MvPolynomial.le_vanishingIdeal_zeroLocus J hf
    rw [hJ] at h1
    exact MvPolynomial.vanishingIdeal_anti_mono subset_closure h1

/-- A closed set whose vanishing ideal is prime is irreducible. -/
lemma isIrreducible_of_isPrime {σ : Type*} [Fintype σ] {C : Set (Aff σ k)} (hC : IsClosed C)
    (hP : (MvPolynomial.vanishingIdeal k C).IsPrime) : IsIrreducible C := by
  have hne : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hP.ne_top
    rw [h, MvPolynomial.vanishingIdeal_empty]
  refine ⟨hne, ?_⟩
  intro u v hu hv huC hvC
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : C ⊆ uᶜ ∪ vᶜ := by
    intro z hz
    by_contra hzv
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hzv
    have hz' : z ∈ C ∩ (u ∩ v) := ⟨hz, hzv.1, hzv.2⟩
    rw [h] at hz'
    simp at hz'
  obtain ⟨I, hI⟩ := (isClosed_aff_iff σ uᶜ).mp hu.isClosed_compl
  obtain ⟨J, hJ⟩ := (isClosed_aff_iff σ vᶜ).mp hv.isClosed_compl
  have hmul : I * J ≤ MvPolynomial.vanishingIdeal k C := by
    intro p hp
    refine MvPolynomial.mem_vanishingIdeal_iff.mpr fun z hz => ?_
    rcases hsub hz with h' | h'
    · have hzI : z ∈ zloc σ k I := by rw [hI]; exact h'
      exact (MvPolynomial.mem_zeroLocus_iff.mp hzI) p (Ideal.mul_le_left hp)
    · have hzJ : z ∈ zloc σ k J := by rw [hJ]; exact h'
      exact (MvPolynomial.mem_zeroLocus_iff.mp hzJ) p (Ideal.mul_le_right hp)
  have hsplit : I ≤ MvPolynomial.vanishingIdeal k C ∨ J ≤ MvPolynomial.vanishingIdeal k C := by
    by_contra hh
    push Not at hh
    obtain ⟨f, hfI, hfC⟩ := SetLike.not_le_iff_exists.mp hh.1
    obtain ⟨g, hgJ, hgC⟩ := SetLike.not_le_iff_exists.mp hh.2
    have hmem : f * g ∈ MvPolynomial.vanishingIdeal k C := hmul (Ideal.mul_mem_mul hfI hgJ)
    rcases hP.mem_or_mem hmem with h' | h'
    · exact hfC h'
    · exact hgC h'
  rcases hsplit with h' | h'
  · have hsub' : C ⊆ uᶜ := by
      calc C = zloc σ k (MvPolynomial.vanishingIdeal k C) := (zeroLocus_vanishingIdeal_eq hC).symm
        _ ⊆ zloc σ k I := MvPolynomial.zeroLocus_anti_mono h'
        _ = uᶜ := hI
    apply huC.ne_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzC, hzu⟩
    exact hsub' hzC hzu
  · have hsub' : C ⊆ vᶜ := by
      calc C = zloc σ k (MvPolynomial.vanishingIdeal k C) := (zeroLocus_vanishingIdeal_eq hC).symm
        _ ⊆ zloc σ k J := MvPolynomial.zeroLocus_anti_mono h'
        _ = vᶜ := hJ
    apply hvC.ne_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzC, hzv⟩
    exact hsub' hzC hzv

/-- The vanishing ideal of a nonempty irreducible closed set is prime. -/
lemma isPrime_vanishingIdeal {σ : Type*} {C : Set (Aff σ k)} (_hC : IsClosed C)
    (hI : IsIrreducible C) : (MvPolynomial.vanishingIdeal k C).IsPrime := by
  have htop : MvPolynomial.vanishingIdeal k C ≠ ⊤ := by
    intro h
    have : (1 : MvPolynomial σ k) ∈ MvPolynomial.vanishingIdeal k C := h ▸ Submodule.mem_top
    rw [MvPolynomial.mem_vanishingIdeal_iff] at this
    have := this _ hI.nonempty.choose_spec
    simp at this
  refine ⟨htop, ?_⟩
  intro f g hfg
  by_contra h
  push Not at h
  obtain ⟨hf, hg⟩ := h
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hf hg hfg
  push Not at hf hg
  obtain ⟨x, hxC, hxf⟩ := hf
  obtain ⟨y, hyC, hyg⟩ := hg
  have hU : IsOpen {z : Aff σ k | MvPolynomial.aeval z f ≠ 0} := by
    refine (isOpen_aff_iff σ _).mpr ⟨Ideal.span ({f} : Set (MvPolynomial σ k)), ?_⟩
    rw [zloc, MvPolynomial.zeroLocus_span]
    ext z
    simp
  have hV : IsOpen {z : Aff σ k | MvPolynomial.aeval z g ≠ 0} := by
    refine (isOpen_aff_iff σ _).mpr ⟨Ideal.span ({g} : Set (MvPolynomial σ k)), ?_⟩
    rw [zloc, MvPolynomial.zeroLocus_span]
    ext z
    simp
  obtain ⟨z, hzC, hzf, hzg⟩ := hI.2 _ _ hU hV ⟨x, hxC, hxf⟩ ⟨y, hyC, hyg⟩
  have h0 := hfg z hzC
  rw [map_mul] at h0
  exact mul_ne_zero hzf hzg h0

/-- The zero locus of a prime ideal is irreducible. -/
lemma isIrreducible_zloc_of_isPrime {σ : Type*} [Finite σ] {P : Ideal (MvPolynomial σ k)}
    (hP : P.IsPrime) : IsIrreducible (zloc σ k P) := by
  have : Fintype σ := Fintype.ofFinite σ
  have hne : (zloc σ k P).Nonempty := by
    obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal P hP.ne_top
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := k) hm
    refine ⟨x, ?_⟩
    rw [zloc, MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    rw [hx] at hPm
    exact MvPolynomial.mem_vanishingIdeal_iff.mp (hPm hp) x rfl
  refine isIrreducible_of_isPrime (isClosed_zloc σ P) ?_
  have h' : MvPolynomial.vanishingIdeal k (zloc σ k P) = P :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) P
  rw [h']
  exact hP


/-- The poset of nonempty irreducible closed subsets of a topological space. -/
abbrev IrredClosed (X : Type*) [TopologicalSpace X] := {C : Set X // IsClosed C ∧ IsIrreducible C}

/-- Hartshorne's dimension of a topological space: the supremum of the lengths of chains of
distinct irreducible closed subsets (Definition I.1.6).  For varieties this is Hartshorne's
`dim` (compare Proposition I.1.7, Theorem I.1.8A). -/
def dimTop (X : Type*) [TopologicalSpace X] : WithBot ℕ∞ := Order.krullDim (IrredClosed X)

/-- Hartshorne's dimension of a *subset* `S` of a topological space: the supremum of the
lengths of chains of distinct irreducible closed subsets of the subspace `S`
(Definition I.1.6 applied to the subspace). -/
def dimSet (X : Type*) [TopologicalSpace X] (S : Set X) : WithBot ℕ∞ :=
  Order.krullDim {C : Set X // IsClosed C ∧ IsIrreducible C ∧ C ⊆ S}

lemma dimSet_univ (X : Type*) [TopologicalSpace X] : dimSet X Set.univ = dimTop X := by
  rw [dimSet, dimTop]
  refine Order.krullDim_eq_of_orderIso ?_
  refine
    { toFun := fun C => ⟨C.1, C.2.1, C.2.2.1⟩
      invFun := fun C => ⟨C.1, C.2.1, C.2.2, Set.subset_univ C.1⟩
      left_inv := fun C => rfl
      right_inv := fun C => rfl
      map_rel_iff' := Iff.rfl }

/-- **Dimension of affine space**: `dim 𝔸^σ = #σ`. -/
theorem dimTop_aff (σ : Type*) [Fintype σ] : dimTop (Aff σ k) = (Nat.card σ : WithBot ℕ∞) := by
  have h1 : dimTop (Aff σ k) ≤ ringKrullDim (MvPolynomial σ k) := by
    have hmono := Order.krullDim_le_of_strictMono
      (fun C : IrredClosed (Aff σ k) => OrderDual.toDual
        (⟨MvPolynomial.vanishingIdeal k C.1, isPrime_vanishingIdeal C.2.1 C.2.2⟩ :
          PrimeSpectrum (MvPolynomial σ k)))
      (by
        intro C C' h
        rw [OrderDual.toDual_lt_toDual]
        show MvPolynomial.vanishingIdeal k C'.1 < MvPolynomial.vanishingIdeal k C.1
        refine lt_of_le_of_ne (MvPolynomial.vanishingIdeal_anti_mono h.le) ?_
        intro heq
        refine h.ne (Subtype.ext ?_)
        rw [← zeroLocus_vanishingIdeal_eq C.2.1, ← zeroLocus_vanishingIdeal_eq C'.2.1, heq])
    rw [Order.krullDim_orderDual] at hmono
    exact hmono
  have h2 : ringKrullDim (MvPolynomial σ k) ≤ dimTop (Aff σ k) := by
    have hmono := Order.krullDim_le_of_strictMono
      (fun p : (PrimeSpectrum (MvPolynomial σ k))ᵒᵈ =>
        (⟨zloc σ k (OrderDual.ofDual p).1, isClosed_zloc σ _,
          isIrreducible_zloc_of_isPrime (OrderDual.ofDual p).2⟩ : IrredClosed (Aff σ k)))
      (by
        intro p q h
        have hlt : (OrderDual.ofDual q).1 < (OrderDual.ofDual p).1 := h
        refine ⟨MvPolynomial.zeroLocus_anti_mono hlt.le, ?_⟩
        intro hcon
        have hmono2 : zloc σ k (OrderDual.ofDual p).1 ⊆ zloc σ k (OrderDual.ofDual q).1 :=
          MvPolynomial.zeroLocus_anti_mono hlt.le
        have heqset : zloc σ k (OrderDual.ofDual p).1 = zloc σ k (OrderDual.ofDual q).1 :=
          subset_antisymm hmono2 hcon
        have hp : MvPolynomial.vanishingIdeal k (zloc σ k (OrderDual.ofDual p).1)
            = (OrderDual.ofDual p).1 :=
          MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) _
        have hq : MvPolynomial.vanishingIdeal k (zloc σ k (OrderDual.ofDual q).1)
            = (OrderDual.ofDual q).1 :=
          MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) _
        have heqideals : (OrderDual.ofDual p).1 = (OrderDual.ofDual q).1 := by
          rw [← hp, ← hq, heqset]
        exact hlt.ne heqideals.symm)
    rw [Order.krullDim_orderDual] at hmono
    exact hmono
  have h3 : ringKrullDim (MvPolynomial σ k) = (Nat.card σ : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := σ),
      ringKrullDim_eq_zero_of_field]
    simp
  rw [← h3]
  exact le_antisymm h1 h2


/-! ### Projective space -/

abbrev J (n : ℕ) (i : Fin (n+1)) := {j : Fin (n+1) // j ≠ i}

local notation "ℙ[" n "]" => Projectivization k (Fin (n+1) → k)

lemma card_J (n : ℕ) (i : Fin (n+1)) : Nat.card (J n i) = n := by
  have h := Fintype.card_subtype_compl (fun j : Fin (n+1) => j = i)
  have h1 : Fintype.card {j : Fin (n+1) // j = i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨i, rfl⟩, fun x => Subtype.ext x.2⟩
  rw [Nat.card_eq_fintype_card, h, h1, Fintype.card_fin]
  exact Nat.succ_sub_one n

/-- The vector with coordinate `1` at `i` and coordinates `y` elsewhere. -/
def vec {n : ℕ} (i : Fin (n+1)) (y : J n i → k) : Fin (n+1) → k :=
  fun j => if h : j = i then 1 else y ⟨j, h⟩

lemma vec_self {n : ℕ} (i : Fin (n+1)) (y : J n i → k) : vec i y i = 1 := by
  simp [vec]

lemma vec_of_ne {n : ℕ} (i : Fin (n+1)) (y : J n i → k) {j : Fin (n+1)} (h : j ≠ i) :
    vec i y j = y ⟨j, h⟩ := by
  simp [vec, h]

lemma vec_ne_zero {n : ℕ} (i : Fin (n+1)) (y : J n i → k) : vec i y ≠ 0 := by
  intro h
  have := vec_self i y
  rw [h] at this
  exact zero_ne_one this

/-- The chart map `𝔸^{n} → ℙ^n` of the affine chart `x_i ≠ 0`. -/
def chartPoint {n : ℕ} (i : Fin (n+1)) (y : J n i → k) : ℙ[n] :=
  Projectivization.mk k (vec i y) (vec_ne_zero i y)

/-- Vanishing of a polynomial at a projective point (evaluated at the canonical
representative). -/
def Vanish {n : ℕ} (f : MvPolynomial (Fin (n+1)) k) (P : ℙ[n]) : Prop :=
  MvPolynomial.eval P.rep f = 0

lemma vanish_mul_iff {n : ℕ} (f g : MvPolynomial (Fin (n+1)) k) (P : ℙ[n]) :
    Vanish (f * g) P ↔ Vanish f P ∨ Vanish g P := by
  simp only [Vanish, map_mul, mul_eq_zero]

/-- The zero locus in `ℙ^n` of a set of polynomials. -/
def V {n : ℕ} (S : Set (MvPolynomial (Fin (n+1)) k)) : Set (ℙ[n]) :=
  {P | ∀ f ∈ S, Vanish f P}

/-- Scaling law for a homogeneous polynomial evaluated at a multiple of a vector. -/
lemma eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (a : k) (v : σ → k) :
    MvPolynomial.eval (a • v) f = a ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.sum (fun _ e => e) = d := by
    simpa [Finsupp.weight_apply] using hf (d := m) (MvPolynomial.mem_support_iff.mp hm)
  have hkey : (∏ i ∈ m.support, (a • v) i ^ m i) = a ^ d * ∏ i ∈ m.support, v i ^ m i := by
    rw [← hdeg, Finsupp.sum]
    rw [show (∏ i ∈ m.support, (a • v) i ^ m i)
        = ∏ i ∈ m.support, (a ^ (m i) * v i ^ (m i)) from by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hkey]; ring

/-- For homogeneous `f`, vanishing at a projective point is independent of the
representative of the line. -/
lemma vanish_mk {n : ℕ} {f : MvPolynomial (Fin (n+1)) k} {d : ℕ} (hf : f.IsHomogeneous d)
    (v : Fin (n+1) → k) (hv : v ≠ 0) :
    Vanish f (Projectivization.mk k v hv) ↔ MvPolynomial.eval v f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) v hv
  have ha' : (a : k) ≠ 0 := Units.ne_zero a
  constructor
  · intro h
    rw [Vanish] at h
    rw [← ha] at h
    have h' : MvPolynomial.eval ((a : k) • v) f = 0 := h
    rw [eval_smul_of_isHomogeneous hf] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (pow_ne_zero d ha')
    · exact h''
  · intro h
    rw [Vanish, ← ha]
    have h' : MvPolynomial.eval ((a : k) • v) f = 0 := by
      rw [eval_smul_of_isHomogeneous hf, h, mul_zero]
    exact h'

/-- A set of homogeneous polynomials (of unspecified degrees). -/
def HomogSet {n : ℕ} (S : Set (MvPolynomial (Fin (n+1)) k)) : Prop :=
  ∀ f ∈ S, ∃ d, f.IsHomogeneous d

/-- Pointwise product of two sets of polynomials. -/
def setMul {n : ℕ} (S T : Set (MvPolynomial (Fin (n+1)) k)) :
    Set (MvPolynomial (Fin (n+1)) k) :=
  {f | ∃ a ∈ S, ∃ b ∈ T, a * b = f}

lemma homogSet_setMul {n : ℕ} {S T : Set (MvPolynomial (Fin (n+1)) k)}
    (hS : HomogSet S) (hT : HomogSet T) : HomogSet (setMul S T) := by
  rintro f ⟨a, ha, b, hb, rfl⟩
  obtain ⟨d, hd⟩ := hS a ha
  obtain ⟨e, he⟩ := hT b hb
  exact ⟨d + e, hd.mul he⟩

lemma homogSet_sUnion {n : ℕ} {A : Set (Set (MvPolynomial (Fin (n+1)) k))}
    (hA : ∀ S ∈ A, HomogSet S) : HomogSet (⋃₀ A) := by
  rintro f ⟨S, hS, hf⟩
  exact hA S hS f hf

/-- The family of Zariski closed subsets of `ℙ^n`: zero loci of homogeneous polynomials. -/
def projClosedFamily (n : ℕ) :
    Set (Set (Projectivization k (Fin (n+1) → k))) :=
  Set.range (fun I : {S : Set (MvPolynomial (Fin (n+1)) k) // HomogSet S} =>
    V I.1)

lemma mem_projClosedFamily {n : ℕ} {T : Set (Projectivization k (Fin (n+1) → k))} :
    T ∈ projClosedFamily (k := k) n ↔
      ∃ S : Set (MvPolynomial (Fin (n+1)) k), HomogSet S ∧ V S = T := by
  constructor
  · rintro ⟨⟨S, hS⟩, rfl⟩
    exact ⟨S, hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩

lemma projClosedFamily_empty {n : ℕ} :
    (∅ : Set (Projectivization k (Fin (n+1) → k))) ∈ projClosedFamily (k := k) n := by
  rw [mem_projClosedFamily]
  let S₀ : Set (MvPolynomial (Fin (n+1)) k) := fun f => f = (1 : MvPolynomial (Fin (n+1)) k)
  have hS₀ : HomogSet S₀ := by
    intro f hf
    rw [show f = (1 : MvPolynomial (Fin (n+1)) k) from hf]
    exact ⟨0, by simpa using (isHomogeneous_C (R := k) (σ := Fin (n+1)) (1 : k))⟩
  have hV : V S₀ = (∅ : Set (Projectivization k (Fin (n+1) → k))) := by
    ext P
    constructor
    · intro h
      have h1 : MvPolynomial.eval P.rep (1 : MvPolynomial (Fin (n+1)) k) = 0 :=
        h 1 rfl
      rw [map_one] at h1
      exact one_ne_zero h1
    · intro h
      exact absurd h (Set.notMem_empty P)
  exact ⟨S₀, hS₀, hV⟩

lemma projClosedFamily_sInter {n : ℕ}
    {A : Set (Set (Projectivization k (Fin (n+1) → k)))}
    (hA : A ⊆ projClosedFamily (k := k) n) : ⋂₀ A ∈ projClosedFamily (k := k) n := by
  classical
  have hA' : ∀ T ∈ A, ∃ S : Set (MvPolynomial (Fin (n+1)) k), HomogSet S ∧ V S = T :=
    fun T hT => (mem_projClosedFamily (k := k)).mp (hA hT)
  let S : (T : Set (Projectivization k (Fin (n+1) → k))) → T ∈ A →
      Set (MvPolynomial (Fin (n+1)) k) :=
    fun T hT => Classical.choose (hA' T hT)
  have hS : ∀ (T : Set (Projectivization k (Fin (n+1) → k))) (hT : T ∈ A),
      HomogSet (S T hT) ∧ V (S T hT) = T := fun T hT => Classical.choose_spec (hA' T hT)
  rw [mem_projClosedFamily]
  refine ⟨{f | ∃ T, ∃ hT : T ∈ A, f ∈ S T hT}, ?_, ?_⟩
  · rintro f ⟨T, hT, hf⟩
    exact (hS T hT).1 f hf
  · ext P
    simp only [Set.mem_sInter]
    constructor
    · intro h T hT
      have hVT : P ∈ V (S T hT) := fun f hf => h f ⟨T, hT, hf⟩
      rwa [(hS T hT).2] at hVT
    · intro h f ⟨T, hT, hf⟩
      have hVT : P ∈ V (S T hT) := by
        rw [(hS T hT).2]
        exact h T hT
      exact hVT f hf

lemma projClosedFamily_union {n : ℕ}
    {A B : Set (Projectivization k (Fin (n+1) → k))}
    (hA : A ∈ projClosedFamily (k := k) n) (hB : B ∈ projClosedFamily (k := k) n) :
    A ∪ B ∈ projClosedFamily (k := k) n := by
  rw [mem_projClosedFamily] at hA hB ⊢
  obtain ⟨S, hS, rfl⟩ := hA
  obtain ⟨T, hT, rfl⟩ := hB
  refine ⟨setMul S T, homogSet_setMul hS hT, ?_⟩
  ext P
  constructor
  · intro h
    by_cases h1 : ∀ f ∈ S, Vanish f P
    · exact Or.inl h1
    · right
      push Not at h1
      obtain ⟨f, hfS, hfP⟩ := h1
      intro g hgT
      have hmul : Vanish (f * g) P := h (f * g) ⟨f, hfS, g, hgT, rfl⟩
      rw [vanish_mul_iff] at hmul
      rcases hmul with h' | h'
      · exact absurd h' hfP
      · exact h'
  · rintro (h | h) f ⟨a, ha, b, hb, rfl⟩
    · exact (vanish_mul_iff a b P).mpr (Or.inl (h a ha))
    · exact (vanish_mul_iff a b P).mpr (Or.inr (h b hb))

/-- The Zariski topology on `ℙ^n`. -/
instance projTop (n : ℕ) : TopologicalSpace (Projectivization k (Fin (n+1) → k)) :=
  TopologicalSpace.ofClosed (projClosedFamily (k := k) n)
    (projClosedFamily_empty) (fun _ hA => projClosedFamily_sInter hA)
    (fun _ hA _ hB => projClosedFamily_union hA hB)

lemma isClosed_V {n : ℕ} {S : Set (MvPolynomial (Fin (n+1)) k)} (hS : HomogSet S) :
    IsClosed (V S) := by
  refine ⟨?_⟩
  rw [projTop, isOpen_mk]
  rw [compl_compl, mem_projClosedFamily]
  exact ⟨S, hS, rfl⟩


/-- Coordinates of a point of the chart `x_i ≠ 0`. -/
def chartCoord {n : ℕ} (i : Fin (n+1)) (P : Projectivization k (Fin (n+1) → k)) :
    J n i → k :=
  fun j => P.rep j.val / P.rep i

lemma vec_chartCoord {n : ℕ} (i : Fin (n+1))
    (P : Projectivization k (Fin (n+1) → k)) (hP : P.rep i ≠ 0) :
    vec i (chartCoord i P) = (P.rep i)⁻¹ • P.rep := by
  funext j
  by_cases h : j = i
  · subst h
    rw [vec_self]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hP).symm
  · rw [vec_of_ne i _ h]
    simp [chartCoord, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- The chart maps `𝔸^n → U_i ⊆ ℙ^n` are surjective onto the chart. -/
lemma chartPoint_chartCoord {n : ℕ} (i : Fin (n+1))
    {P : Projectivization k (Fin (n+1) → k)} (hP : P.rep i ≠ 0) :
    chartPoint i (chartCoord i P) = P := by
  have hne : (P.rep i)⁻¹ • P.rep ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨inv_ne_zero hP, P.rep_nonzero⟩
  refine Projectivization.submodule_injective ?_
  show (Projectivization.mk k (vec i (chartCoord i P)) (vec_ne_zero i _)).submodule = P.submodule
  rw [Projectivization.submodule_mk, Projectivization.submodule_eq, vec_chartCoord i P hP,
    Submodule.span_singleton_eq_span_singleton]
  exact ⟨Units.mk0 (P.rep i) hP, by
    show (P.rep i : k) • (P.rep i)⁻¹ • P.rep = P.rep
    rw [smul_smul, mul_inv_cancel₀ hP, one_smul]⟩

lemma chartCoord_chartPoint {n : ℕ} (i : Fin (n+1)) (y : J n i → k) :
    chartCoord i (chartPoint i y) = y := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) (vec i y) (vec_ne_zero i y)
  have hrep : (chartPoint i y).rep = (a : k) • vec i y := ha.symm
  have ha0 : (a : k) ≠ 0 := Units.ne_zero a
  funext j
  simp only [chartCoord, hrep, Pi.smul_apply, smul_eq_mul, vec_self, vec_of_ne i y j.2]
  field_simp

/-- The open affine chart `U_i = {x_i ≠ 0}`. -/
def U {n : ℕ} (i : Fin (n+1)) : Set (Projectivization k (Fin (n+1) → k)) :=
  {P | P.rep i ≠ 0}

lemma isOpen_U {n : ℕ} (i : Fin (n+1)) : IsOpen (U (k := k) i) := by
  have h : U (k := k) i = (V ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n+1)) k)))ᶜ := by
    ext P
    simp only [U, V, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_compl_iff, forall_eq,
      Vanish, MvPolynomial.eval_X]
  rw [h]
  exact (isClosed_V (by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]
    exact ⟨1, isHomogeneous_X (R := k) i⟩)).isOpen_compl

lemma chartPoint_mem_U {n : ℕ} (i : Fin (n+1)) (y : J n i → k) :
    chartPoint i y ∈ U (k := k) i := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) (vec i y) (vec_ne_zero i y)
  have hrep : (chartPoint i y).rep = (a : k) • vec i y := ha.symm
  show (chartPoint i y).rep i ≠ 0
  rw [hrep, Pi.smul_apply, smul_eq_mul, vec_self, mul_one]
  exact Units.ne_zero a

/-- The affine chart piece of a subset of `ℙ^n`. -/
def chartPiece {n : ℕ} (i : Fin (n+1))
    (Y : Set (Projectivization k (Fin (n+1) → k))) : Set (Aff (J n i) k) :=
  {y | chartPoint i y ∈ Y}

/-- Hartshorne's dimension of a subset of `ℙ^n`, computed on the affine charts. -/
def dimProj {n : ℕ} (Y : Set (Projectivization k (Fin (n+1) → k))) : WithBot ℕ∞ :=
  ⨆ i : Fin (n+1), dimSet (Aff (J n i) k) (closure (chartPiece i Y))

/-- **(a)** The dimension of projective space is `n`. -/
theorem dim_projective_space (n : ℕ) :
    dimProj (Set.univ : Set (Projectivization k (Fin (n+1) → k))) = (n : WithBot ℕ∞) := by
  have h : ∀ i : Fin (n+1),
      dimSet (Aff (J n i) k) (closure (chartPiece i (Set.univ : Set _))) = (n : WithBot ℕ∞) := by
    intro i
    have h1 : chartPiece (k := k) i (Set.univ : Set (Projectivization k (Fin (n+1) → k)))
        = Set.univ := by
      ext y
      simp [chartPiece]
    rw [h1, closure_univ, dimSet_univ, dimTop_aff, card_J]
  calc dimProj (Set.univ : Set (Projectivization k (Fin (n+1) → k)))
      = ⨆ i : Fin (n+1), (n : WithBot ℕ∞) := iSup_congr h
    _ = (n : WithBot ℕ∞) := by simp


/-! ### Homogenization and the dimension of the closure -/

lemma isHomogeneous_X_pow {n : ℕ} (i : Fin (n+1)) (m : ℕ) :
    ((MvPolynomial.X i) ^ m : MvPolynomial (Fin (n+1)) k).IsHomogeneous m := by
  induction m with
  | zero => simpa using isHomogeneous_one (σ := Fin (n+1)) (R := k)
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul (isHomogeneous_X (R := k) i)

/-- Homogenization of a polynomial in the chart coordinates with respect to `x_i`. -/
def homog {n : ℕ} (i : Fin (n+1)) (g : MvPolynomial (J n i) k) : MvPolynomial (Fin (n+1)) k :=
  ∑ d ∈ Finset.range (g.totalDegree + 1),
    MvPolynomial.X i ^ (g.totalDegree - d) *
      MvPolynomial.rename (Subtype.val) (MvPolynomial.homogeneousComponent d g)

lemma eval_homog {n : ℕ} (i : Fin (n+1)) (g : MvPolynomial (J n i) k) (y : J n i → k) :
    MvPolynomial.eval (vec i y) (homog i g) = MvPolynomial.eval y g := by
  have hXi : MvPolynomial.eval (vec i y) (MvPolynomial.X i) = 1 := by
    simp [vec_self]
  have hren : ∀ h : MvPolynomial (J n i) k,
      MvPolynomial.eval (vec i y) (MvPolynomial.rename (Subtype.val) h)
        = MvPolynomial.eval y h := by
    intro h
    rw [MvPolynomial.eval_rename]
    have hfun : (vec i y) ∘ (Subtype.val : J n i → Fin (n+1)) = y := by
      funext j
      exact vec_of_ne i y j.2
    rw [hfun]
  rw [homog, map_sum]
  simp only [map_mul, map_pow, hren, hXi, one_pow, one_mul]
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent]

lemma isHomogeneous_homog {n : ℕ} (i : Fin (n+1)) (g : MvPolynomial (J n i) k) :
    (homog i g).IsHomogeneous g.totalDegree := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, homog]
  refine Submodule.sum_mem _ ?_
  intro d hd
  rw [Finset.mem_range] at hd
  have hd' : d ≤ g.totalDegree := Nat.lt_succ_iff.mp hd
  have h1 : (MvPolynomial.X i ^ (g.totalDegree - d) *
      MvPolynomial.rename (Subtype.val) (MvPolynomial.homogeneousComponent d g)).IsHomogeneous
        g.totalDegree := by
    have h2 := (isHomogeneous_X_pow (k := k) i (g.totalDegree - d)).mul
      ((MvPolynomial.homogeneousComponent_isHomogeneous (n := d) (φ := g)).rename_isHomogeneous
        (f := (Subtype.val : J n i → Fin (n+1))))
    rwa [Nat.sub_add_cancel hd'] at h2
  simpa only [MvPolynomial.mem_homogeneousSubmodule] using h1

/-- The charts are open, and a dense subset meets them densely. -/
lemma closure_inter_subset {n : ℕ} {Y : Set (Projectivization k (Fin (n+1) → k))}
    (i : Fin (n+1)) : closure Y ∩ U i ⊆ closure (Y ∩ U i) := by
  intro x ⟨hxY, hxU⟩
  rw [mem_closure_iff] at hxY ⊢
  intro W hW hxW
  have h1 : ((W ∩ U i) ∩ Y).Nonempty := hxY (W ∩ U i) (hW.inter (isOpen_U i)) ⟨hxW, hxU⟩
  obtain ⟨z, hz⟩ := h1
  exact ⟨z, hz.1.1, hz.2, hz.1.2⟩

/-- **(b)** A quasi-projective variety and its closure have the same dimension. -/
theorem dimProj_closure {n : ℕ} (Y : Set (Projectivization k (Fin (n+1) → k))) :
    dimProj Y = dimProj (closure Y) := by
  refine iSup_congr fun i => ?_
  have h : closure (chartPiece (k := k) i Y) = closure (chartPiece (k := k) i (closure Y)) := by
    refine subset_antisymm (closure_mono ?_) ?_
    · intro y hy
      exact subset_closure hy
    · refine closure_minimal ?_ isClosed_closure
      intro y₀ hy₀
      rw [closure_eq_zloc_vanishingIdeal]
      intro g hg
      have hYV : Y ∩ U i ⊆ V ({homog i g} : Set (MvPolynomial (Fin (n+1)) k)) := by
        rintro P ⟨hPY, hPU⟩
        have hP : chartPoint i (chartCoord i P) = P := chartPoint_chartCoord i hPU
        intro f hf
        rw [Set.mem_singleton_iff] at hf
        subst hf
        rw [← hP]
        show Vanish (homog i g)
          (Projectivization.mk k (vec i (chartCoord i P)) (vec_ne_zero i _))
        rw [vanish_mk (isHomogeneous_homog i g) (vec i (chartCoord i P)) (vec_ne_zero i _)]
        rw [eval_homog]
        exact hg _ (by
          show chartPoint i (chartCoord i P) ∈ Y
          rw [hP]; exact hPY)
      have hclosed : IsClosed (V ({homog i g} : Set (MvPolynomial (Fin (n+1)) k))) := by
        refine isClosed_V ?_
        intro f hf
        rw [Set.mem_singleton_iff] at hf
        rw [hf]
        exact ⟨_, isHomogeneous_homog i g⟩
      have hZU : closure Y ∩ U i ⊆ V ({homog i g} : Set (MvPolynomial (Fin (n+1)) k)) :=
        subset_trans (closure_inter_subset i) (closure_minimal hYV hclosed)
      have hy₀' : chartPoint i y₀ ∈ closure Y := hy₀
      have hP₀ : chartPoint i y₀ ∈ closure Y ∩ U i := ⟨hy₀', chartPoint_mem_U i y₀⟩
      have hfin : Vanish (homog i g) (chartPoint i y₀) :=
        hZU hP₀ (homog i g) (Set.mem_singleton _)
      have hfin' : Vanish (homog i g)
          (Projectivization.mk k (vec i y₀) (vec_ne_zero i y₀)) := hfin
      rw [vanish_mk (isHomogeneous_homog i g) (vec i y₀) (vec_ne_zero i _)] at hfin'
      rw [eval_homog] at hfin'
      exact hfin'
  show dimSet (Aff (J n i) k) (closure (chartPiece i Y))
      = dimSet (Aff (J n i) k) (closure (chartPiece i (closure Y)))
  rw [h]


/-- A quasi-projective variety in `ℙ^n`: a nonempty irreducible locally closed subset
(Hartshorne, Chapter I, §2: an open subset of a projective variety). -/
def IsQuasiProjective {n : ℕ} (Y : Set (Projectivization k (Fin (n+1) → k))) : Prop :=
  Y.Nonempty ∧ IsIrreducible Y ∧ ∃ U Z : Set (Projectivization k (Fin (n+1) → k)),
    IsOpen U ∧ IsClosed Z ∧ Y = U ∩ Z

/-- **Exercise I.2.7(b)**, chartwise form: a quasi-projective variety and its closure give the
same value of the chartwise dimension `dimProj`.  This is *not* the intrinsic statement; the
intrinsic form is `topologicalKrullDim_closure_eq_of_isQuasiProjective` below. -/
theorem dimProj_eq_dimProj_closure_of_isQuasiProjective {n : ℕ}
    {Y : Set (Projectivization k (Fin (n+1) → k))} (_hY : IsQuasiProjective Y) :
    dimProj Y = dimProj (closure Y) :=
  dimProj_closure Y


/-! ### Hartshorne I.1.10(b): dimension is the supremum over an open cover
(copied from the verified corpus proof of Exercise I.1.10) -/

namespace CoverDim

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


end CoverDim

/-! ### Intrinsic dimension: the charts are homeomorphic to affine space -/

/-- `dimTop` and Mathlib's `topologicalKrullDim` agree. -/
lemma dimTop_eq_topologicalKrullDim (X : Type*) [TopologicalSpace X] :
    dimTop X = topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [dimTop, topologicalKrullDim]
    refine Order.krullDim_le_of_strictMono
      (fun C : IrredClosed X =>
        (TopologicalSpace.IrreducibleCloseds.mk C.1 C.2.2 C.2.1 :
          TopologicalSpace.IrreducibleCloseds X))
      (fun a b h => h)
  · rw [dimTop, topologicalKrullDim]
    refine Order.krullDim_le_of_strictMono
      (fun C : TopologicalSpace.IrreducibleCloseds X =>
        (⟨C.carrier, C.isClosed', C.isIrreducible'⟩ : IrredClosed X))
      (fun a b h => h)

lemma isClosed_iff_mem_projClosedFamily {n : ℕ} {T : Set (ℙ[n])} :
    IsClosed T ↔ T ∈ projClosedFamily (k := k) n := by
  constructor
  · intro h
    have h' := h.isOpen_compl
    rw [projTop, isOpen_mk, compl_compl] at h'
    exact h'
  · intro h
    refine ⟨?_⟩
    rw [projTop, isOpen_mk, compl_compl]
    exact h

/-- Membership in a zero locus, in terms of evaluation. -/
lemma mem_zloc {σ : Type*} {I : Ideal (MvPolynomial σ k)} {y : Aff σ k} :
    y ∈ zloc σ k I ↔ ∀ p ∈ I, MvPolynomial.eval y p = 0 := by
  rw [zloc, MvPolynomial.mem_zeroLocus_iff]
  exact ⟨fun h p hp => by simpa using h p hp, fun h p hp => by simpa using h p hp⟩

/-- Vanishing of a homogenization at a point of the chart. -/
lemma vanish_homog_chartCoord {n : ℕ} (i : Fin (n+1)) {g : MvPolynomial (J n i) k}
    {P : ℙ[n]} (hP : P ∈ U (k := k) i) :
    Vanish (homog (k := k) i g) P ↔ MvPolynomial.eval (chartCoord (k := k) i P) g = 0 := by
  have h1 : chartPoint (k := k) i (chartCoord (k := k) i P) = P := chartPoint_chartCoord i hP
  conv_lhs => rw [← h1]
  show Vanish (homog (k := k) i g)
      (Projectivization.mk k (vec i (chartCoord (k := k) i P)) (vec_ne_zero i _)) ↔ _
  rw [vanish_mk (k := k) (hf := isHomogeneous_homog i g)
    (vec i (chartCoord (k := k) i P)) (vec_ne_zero i _), eval_homog]

/-- Membership in the zero locus of a principal ideal. -/
lemma mem_zloc_span {σ : Type*} {g : MvPolynomial σ k} {y : Aff σ k} :
    y ∈ zloc σ k (Ideal.span {g}) ↔ MvPolynomial.eval y g = 0 := by
  rw [zloc, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h
    simpa using h g (Ideal.mem_span_singleton_self g)
  · rintro h p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul]
    simp [h]

/-- Substitution `X_i = 1`: dehomogenization with respect to the chart `x_i ≠ 0`. -/
noncomputable def dehom {n : ℕ} (i : Fin (n+1)) (f : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial (J n i) k :=
  MvPolynomial.aeval
    (fun t => if h : t = i then (1 : MvPolynomial (J n i) k) else MvPolynomial.X ⟨t, h⟩) f

lemma eval_dehom {n : ℕ} (i : Fin (n+1)) (f : MvPolynomial (Fin (n+1)) k)
    (y : J n i → k) :
    MvPolynomial.eval y (dehom (k := k) i f) = MvPolynomial.eval (vec i y) f := by
  have key : ∀ p : MvPolynomial (Fin (n+1)) k,
      MvPolynomial.eval y (MvPolynomial.aeval
        (fun t => if h : t = i then (1 : MvPolynomial (J n i) k)
          else MvPolynomial.X ⟨t, h⟩) p) = MvPolynomial.eval (vec i y) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p t hp =>
        rw [map_mul, MvPolynomial.aeval_X, map_mul, hp, map_mul]
        congr 1
        by_cases h : t = i
        · subst h
          simp [vec_self]
        · rw [dif_neg h, MvPolynomial.eval_X, MvPolynomial.eval_X, vec_of_ne i y h]
  exact key f

lemma isClosed_preimage_chartPoint_V {n : ℕ} (i : Fin (n+1))
    {S : Set (MvPolynomial (Fin (n+1)) k)} (hS : HomogSet S) :
    IsClosed ((chartPoint (k := k) i) ⁻¹' V S) := by
  have h : (chartPoint (k := k) i) ⁻¹' V S
      = ⋂ f ∈ S, zloc (J n i) k (Ideal.span {dehom (k := k) i f}) := by
    ext y
    simp only [Set.mem_preimage, V, Set.mem_iInter, Set.mem_ofPred_eq, mem_zloc_span]
    constructor
    · intro h f hf
      obtain ⟨d, hd⟩ := hS f hf
      rw [eval_dehom]
      exact (vanish_mk (k := k) (hf := hd) (vec i y) (vec_ne_zero i y)).mp (h f hf)
    · intro h f hf
      obtain ⟨d, hd⟩ := hS f hf
      have h1 : MvPolynomial.eval (vec i y) f = 0 := by
        rw [← eval_dehom]
        exact h f hf
      rw [Vanish]
      exact (vanish_mk (k := k) (hf := hd) (vec i y) (vec_ne_zero i y)).mpr h1
  rw [h]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_zloc (J n i) (Ideal.span {dehom (k := k) i f})

lemma isClosed_preimage_chartPoint {n : ℕ} (i : Fin (n+1))
    {C : Set (ℙ[n])} (hC : IsClosed C) : IsClosed ((chartPoint (k := k) i) ⁻¹' C) := by
  obtain ⟨S, hS, rfl⟩ := (mem_projClosedFamily (k := k)).mp
    ((isClosed_iff_mem_projClosedFamily (k := k)).mp hC)
  exact isClosed_preimage_chartPoint_V i hS

lemma continuous_chartPoint {n : ℕ} (i : Fin (n+1)) :
    Continuous (chartPoint (k := k) i) :=
  continuous_iff_isClosed.mpr fun _ hC => isClosed_preimage_chartPoint i hC

lemma continuous_chartCoord {n : ℕ} (i : Fin (n+1)) :
    Continuous fun P : (U (k := k) i : Set (ℙ[n])) => chartCoord (k := k) i P.1 := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨I, rfl⟩ := (isClosed_aff_iff (J n i) C).mp hC
  have h : (fun P : (U (k := k) i : Set (ℙ[n])) => chartCoord (k := k) i P.1) ⁻¹'
      zloc (J n i) k I = Subtype.val ⁻¹' V (homog (k := k) i '' I) := by
    ext P
    constructor
    · intro hP
      rw [Set.mem_preimage, V, Set.mem_ofPred_eq]
      rintro _ ⟨x, hx, rfl⟩
      exact (vanish_homog_chartCoord i P.2).mpr ((mem_zloc.mp hP) x hx)
    · intro hP
      rw [Set.mem_preimage, mem_zloc]
      intro x hx
      have h1 : Vanish (homog (k := k) i x) (P : ℙ[n]) := by
        rw [Set.mem_preimage, V, Set.mem_ofPred_eq] at hP
        exact hP _ ⟨x, hx, rfl⟩
      exact (vanish_homog_chartCoord i P.2).mp h1
  rw [h]
  exact (isClosed_V (by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨_, isHomogeneous_homog i g⟩)).preimage continuous_subtype_val

/-- The chart `U_i` is homeomorphic to affine `n`-space. -/
noncomputable def chartHomeomorph {n : ℕ} (i : Fin (n+1)) :
    (J n i → k) ≃ₜ (U (k := k) i : Set (ℙ[n])) where
  toFun y := ⟨chartPoint (k := k) i y, chartPoint_mem_U i y⟩
  invFun P := chartCoord (k := k) i P.1
  left_inv y := chartCoord_chartPoint i y
  right_inv P := Subtype.ext (chartPoint_chartCoord i P.2)
  continuous_toFun := (continuous_chartPoint i).subtype_mk _
  continuous_invFun := continuous_chartCoord i

lemma topologicalKrullDim_U {n : ℕ} (i : Fin (n+1)) :
    topologicalKrullDim (U (k := k) i : Set (ℙ[n])) = (n : WithBot ℕ∞) := by
  rw [← IsHomeomorph.topologicalKrullDim_eq (chartHomeomorph (k := k) i).toFun
    (chartHomeomorph (k := k) i).isHomeomorph]
  rw [← dimTop_eq_topologicalKrullDim, dimTop_aff, card_J]

/-- **(a), intrinsic form**: the topological dimension of `ℙ^n` is `n`. -/
theorem dimTop_projective_space (n : ℕ) :
    dimTop (ℙ[n]) = (n : WithBot ℕ∞) := by
  have hU : ∀ i : Fin (n+1), IsOpen (U (k := k) i) := fun i => isOpen_U i
  have hcov : (⋃ i : Fin (n+1), U (k := k) i) = Set.univ := by
    ext P
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_contra h
    push Not at h
    have h0 : P.rep = 0 := funext fun j => by simpa [U] using h j
    exact P.rep_nonzero h0
  have h := CoverDim.dim_eq_iSup_of_isOpen_cover (X := ℙ[n]) (ι := Fin (n+1)) hU hcov
  rw [dimTop_eq_topologicalKrullDim,
    show topologicalKrullDim (ℙ[n]) = ⨆ i : Fin (n+1),
      topologicalKrullDim (U (k := k) i : Set (ℙ[n])) from h]
  calc ⨆ i : Fin (n+1), topologicalKrullDim (U (k := k) i : Set (ℙ[n]))
      = ⨆ _i : Fin (n+1), (n : WithBot ℕ∞) := iSup_congr fun i => topologicalKrullDim_U i
    _ = (n : WithBot ℕ∞) := by simp
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace AwayDim

variable {A : Type*} [CommRing A]

theorem Ideal.height_eq_one_of_mem_minimalPrimes [IsNoetherianRing A] [IsDomain A]
    {t : A} (ht : t ≠ 0) {p : Ideal A} (hp : p ∈ (Ideal.span {t}).minimalPrimes) :
    p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
  have h1 : (1 : ℕ∞) ≤ (Ideal.span {t}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  refine le_trans h1 ?_
  rw [Ideal.height_eq_inf_minimalPrimes]
  exact iInf₂_le p hp

/-- The image of a prime minimal over `I` in `A ⧸ I` has height zero. -/
theorem Ideal.height_map_quotient_eq_zero [IsNoetherianRing A] {I P : Ideal A}
    (h : P ∈ I.minimalPrimes) : (P.map (Ideal.Quotient.mk I)).height = 0 := by
  have hP : P.IsPrime := h.isPrime
  have : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime h.le
  have key : P.map (Ideal.Quotient.mk I) ∈ minimalPrimes (A ⧸ I) := by
    rw [Ideal.minimalPrimes_eq_comap] at h
    obtain ⟨Q, hQ, hQP⟩ := h
    rw [← hQP]
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
    exact hQ
  rw [Ideal.height_eq_zero_iff]
  exact key

/-- Height and dimension are preserved by integral injective extensions of domains. -/
theorem Ideal.height_eq_height_under_of_isIntegral {B S : Type*} [CommRing B] [CommRing S]
    [IsDomain B] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S] [FaithfulSMul B S]
    [IsNoetherianRing B] [IsNoetherianRing S] [Algebra.HasGoingDown B S] {P : Ideal S} [P.IsPrime] :
    P.height = (P.under B).height := by
  have : P.LiesOver (P.under B) := ⟨rfl⟩
  have h2 : (P.map (Ideal.Quotient.mk ((P.under B).map (algebraMap B S)))).height = 0 :=
    Ideal.height_map_quotient_eq_zero (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := B) P)
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under B) P, h2, add_zero]

variable {B S : Type*} [CommRing B] [CommRing S] [IsDomain B] [IsDomain S] [Algebra B S]
  [Algebra.IsIntegral B S] [FaithfulSMul B S] [IsNoetherianRing B] [IsNoetherianRing S]
  [Algebra.HasGoingDown B S]

/-- Integral injective extensions of Noetherian domains have the same Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective : ringKrullDim S = ringKrullDim B := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := P)
    rw [h]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro q hq
    obtain ⟨Q, -, hQprime, hQeq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := S) q (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B S)]; exact bot_le)
    haveI := hQprime
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := Q)
    show q.height ≤ ringKrullDim S
    rw [← hQeq, ← h]
    exact Ideal.height_le_ringKrullDim_of_isPrime




section PointHeight

variable (k : Type*) [Field k]

/-- Substitution sending `X i` to the constant `a i` for `i < j`, and fixing the other variables. -/
noncomputable def substBelow {s : ℕ} (j : ℕ) (a : Fin s → k) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  MvPolynomial.aeval fun i => if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k)
    else MvPolynomial.X i

lemma substBelow_X {s : ℕ} (j : ℕ) (a : Fin s → k) (i : Fin s) :
    substBelow k j a (MvPolynomial.X i) =
      if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i := by
  simp [substBelow]

lemma substBelow_zero {s : ℕ} (a : Fin s → k) : substBelow k 0 a = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substBelow_X]

lemma substBelow_succ {s : ℕ} (j : ℕ) (a : Fin s → k) :
    substBelow k (j + 1) a = (MvPolynomial.aeval fun (i : Fin s) =>
      if (i : ℕ) = j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i).comp
      (substBelow k j a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, substBelow_X, substBelow_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega), MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  · rw [if_neg h]
    by_cases h2 : (i : ℕ) = j
    · rw [MvPolynomial.aeval_X, if_pos h2, if_pos (by omega)]
    · rw [MvPolynomial.aeval_X, if_neg h2, if_neg (by omega)]

lemma ker_substBelow_antitone {s : ℕ} (j : ℕ) (a : Fin s → k) :
    RingHom.ker (substBelow k j a) ≤ RingHom.ker (substBelow k (j + 1) a) := by
  intro f hf
  simp only [RingHom.mem_ker] at hf ⊢
  rw [substBelow_succ, AlgHom.comp_apply, hf, map_zero]

lemma X_sub_C_mem_ker_substBelow_succ {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∈
      RingHom.ker (substBelow k (j + 1) a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_pos (show ((⟨j, hj⟩ : Fin s) : ℕ) < j + 1 from by simp)]
  simp

lemma X_sub_C_notMem_ker_substBelow {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∉
      RingHom.ker (substBelow k j a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_neg (show ¬ ((⟨j, hj⟩ : Fin s) : ℕ) < j from by simp)]
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => a ⟨j, hj⟩ + 1)) h
  simp at h2



section Height

variable (k : Type*) [Field k]

/-- The ideal of polynomials vanishing at a point of affine `s`-space has height `s`. -/
theorem vanishingIdeal_singleton_height (s : ℕ) (a : Fin s → k) :
    (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height = ↑s := by
  have hker : RingHom.ker (substBelow k s a) = MvPolynomial.vanishingIdeal k {a} := by
    have heq : substBelow k s a =
        (Algebra.ofId k (MvPolynomial (Fin s) k)).comp (MvPolynomial.aeval a) := by
      rw [MvPolynomial.comp_aeval]
      apply MvPolynomial.algHom_ext
      intro i
      rw [substBelow_X, if_pos i.isLt, MvPolynomial.aeval_X, Algebra.ofId_apply,
        MvPolynomial.algebraMap_eq]
    have hinj : Function.Injective (algebraMap k (MvPolynomial (Fin s) k)) :=
      FaithfulSMul.algebraMap_injective k _
    rw [heq]
    ext p
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Algebra.ofId_apply,
      MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : (MvPolynomial.aeval a) p = 0 := hinj (by simpa using h)
      intro x hx
      rw [hx]
      exact h0
    · intro h
      rw [h a rfl, map_zero]
  have hlower : (↑s : ℕ∞) ≤ (MvPolynomial.vanishingIdeal k {a} :
      Ideal (MvPolynomial (Fin s) k)).height := by
    rw [← hker]
    have key : ∀ j ≤ s, (↑j : ℕ∞) ≤ (RingHom.ker (substBelow k j a)).height := by
      intro j
      induction j with
      | zero => intro _; exact bot_le
      | succ m ih =>
        intro hm
        have hms : m < s := by omega
        have h1 : (RingHom.ker (substBelow k m a)).IsPrime := RingHom.ker_isPrime _
        have h2 : (RingHom.ker (substBelow k (m + 1) a)).IsPrime := RingHom.ker_isPrime _
        have hlt : RingHom.ker (substBelow k m a) < RingHom.ker (substBelow k (m + 1) a) :=
          lt_of_le_of_ne (ker_substBelow_antitone k m a)
            (fun heq => X_sub_C_notMem_ker_substBelow k m hms a (heq ▸
              X_sub_C_mem_ker_substBelow_succ k m hms a))
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have him := ih (by omega : m ≤ s)
        calc (↑(m + 1) : ℕ∞) = (↑m : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (substBelow k m a)).height + 1 := by gcongr
          _ ≤ (RingHom.ker (substBelow k (m + 1) a)).height := hstep
    exact key s le_rfl
  have hupper : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height ≤ ↑s := by
    haveI : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).IsMaximal :=
      inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := MvPolynomial.vanishingIdeal k {a})
      (Ideal.IsMaximal.ne_top ‹(MvPolynomial.vanishingIdeal k {a} :
        Ideal (MvPolynomial (Fin s) k)).IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  exact le_antisymm hupper hlower


end Height

end PointHeight

/-! ## Maximal ideals of a polynomial ring and equidimensionality of f.g. domains -/

section MaxHeight

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- Every maximal ideal of `k[X_1,…,X_s]` has height `s`. -/
theorem Ideal.height_eq_of_isMaximal_mvPolynomial {s : ℕ}
    {M : Ideal (MvPolynomial (Fin s) k)} (hM : M.IsMaximal) :
    M.height = (s : ℕ∞) := by
  obtain ⟨a, rfl⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := k) hM
  exact vanishingIdeal_singleton_height k s a

/-- **Equidimensionality of finitely generated domains over an algebraically closed field**:
every maximal ideal has height equal to the Krull dimension. -/
theorem Ideal.height_eq_ringKrullDim_of_isMaximal {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {m : Ideal A} (hm : m.IsMaximal) :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI hmprime : m.IsPrime := hm.isPrime
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) A = g.toRingHom := RingHom.algebraMap_toAlgebra _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hginj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := by
    have : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
    infer_instance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) k) A := inferInstance
  have h1 : m.height = (m.under (MvPolynomial (Fin s) k)).height :=
    Ideal.height_eq_height_under_of_isIntegral (B := MvPolynomial (Fin s) k) (P := m)
  have h2 : (m.under (MvPolynomial (Fin s) k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have h3 : (m.under (MvPolynomial (Fin s) k)).height = (s : ℕ∞) :=
    Ideal.height_eq_of_isMaximal_mvPolynomial k h2
  have h4 : ringKrullDim A = ((s : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_integral_injective (B := MvPolynomial (Fin s) k) (S := A),
      MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := Fin s),
      ringKrullDim_eq_zero_of_field k]
    simp
  rw [h1, h3, ← h4]

/-- Two maximal ideals of a finitely generated domain over an algebraically closed field
have the same height. -/
theorem Ideal.height_eq_height_of_isMaximal {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {m m' : Ideal A} (hm : m.IsMaximal)
    (hm' : m'.IsMaximal) : m.height = m'.height := by
  have h : (m.height : WithBot ℕ∞) = (m'.height : WithBot ℕ∞) := by
    rw [Ideal.height_eq_ringKrullDim_of_isMaximal k hm,
      Ideal.height_eq_ringKrullDim_of_isMaximal k hm']
  exact WithBot.coe_injective h

end MaxHeight



section LocalDim

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A finitely generated domain over an algebraically closed field has a maximal ideal
avoiding any given nonzero element. -/
theorem exists_isMaximal_notMem {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) :
    ∃ m : Ideal A, m.IsMaximal ∧ f ∉ m := by
  obtain ⟨n, φ, hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType k A)
  set I : Ideal (MvPolynomial (Fin n) k) := RingHom.ker φ with hI
  haveI hIprime : I.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨F, rfl⟩ := hφ f
  have hFI : F ∉ I := fun h => hf (by rw [hI, RingHom.mem_ker] at h; exact h)
  -- a point of the zero locus where `F` does not vanish
  have hex : ∃ a : Fin n → k, (∀ p ∈ I, MvPolynomial.aeval a p = 0) ∧
      MvPolynomial.aeval a F ≠ 0 := by
    by_contra h
    push Not at h
    have hmem : F ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus (K := k) I) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro a ha
      exact h a (by rwa [MvPolynomial.mem_zeroLocus_iff] at ha)
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.IsPrime.radical hIprime] at hmem
    exact hFI hmem
  obtain ⟨a, ha, haF⟩ := hex
  have hle : I ≤ MvPolynomial.vanishingIdeal k {a} := by
    rw [← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
    rw [Set.singleton_subset_iff, MvPolynomial.mem_zeroLocus_iff]
    exact ha
  haveI hmax : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin n) k)).IsMaximal :=
    inferInstance
  have haF' : F ∉ MvPolynomial.vanishingIdeal k {a} := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    push Not
    exact ⟨a, rfl, haF⟩
  let φr : MvPolynomial (Fin n) k →+* A := φ
  have hφr : Function.Surjective φr := hφ
  have hmapmax : ((MvPolynomial.vanishingIdeal k {a}).map φr).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hφr hle
  refine ⟨(MvPolynomial.vanishingIdeal k {a}).map φr, hmapmax, ?_⟩
  intro hcon
  have h2 : F ∈ Ideal.comap φr ((MvPolynomial.vanishingIdeal k {a}).map φr) := hcon
  rw [Ideal.comap_map_eq_self_of_isMaximal φr hmapmax.ne_top] at h2
  exact haF' h2

end LocalDim



section LocalDimMain

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **The local dimension lemma.** Inverting a nonzero element of a finitely generated domain
over an algebraically closed field does not change the Krull dimension
(equidimensionality of affine domains). -/
theorem ringKrullDim_away_eq {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim A := by
  haveI hdom : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  haveI hft : Algebra.FiniteType k (Localization.Away f) := inferInstance
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro q hq
    haveI := hq
    rw [← IsLocalization.height_under (Submonoid.powers f) q]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro p hp
    haveI := hp
    obtain ⟨m, hmmax, hfm⟩ := exists_isMaximal_notMem k hf
    haveI := hmmax
    obtain ⟨m', hm'max, hpm'⟩ := Ideal.exists_le_maximal p hp.ne_top
    haveI := hm'max
    have h1 : (↑p.height : WithBot ℕ∞) ≤ (↑m.height : WithBot ℕ∞) := by
      rw [WithBot.coe_le_coe]
      calc p.height ≤ m'.height := Ideal.height_mono hpm'
        _ = m.height := Ideal.height_eq_height_of_isMaximal k hm'max hmmax
    have hdisj : Disjoint (Submonoid.powers f : Set A) (m : Set A) := by
      rw [Set.disjoint_left]
      intro x hx hxm
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x f).mp hx
      rw [← hn] at hxm
      exact hfm (hmmax.isPrime.mem_of_pow_mem n hxm)
    have hpr : (Ideal.map (algebraMap A (Localization.Away f)) m).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
        (Localization.Away f) m hmmax.isPrime hdisj
    have h2 : (↑m.height : WithBot ℕ∞) ≤ ringKrullDim (Localization.Away f) := by
      have hle : (Ideal.map (algebraMap A (Localization.Away f)) m).height
          ≤ ringKrullDim (Localization.Away f) := Ideal.height_le_ringKrullDim_of_isPrime
      rwa [IsLocalization.height_map_of_disjoint (Submonoid.powers f)
        (S := Localization.Away f) m hdisj] at hle
    exact le_trans h1 h2

end LocalDimMain


end AwayDim


/-! ### Intrinsic dimension of affine closed sets -/

lemma image_preimage_val_of_subset {X : Type*} [TopologicalSpace X] {S C : Set X}
    (hC : C ⊆ S) :
    (Subtype.val : ↥S → X) '' (Subtype.val ⁻¹' C) = C := by
  rw [Set.image_preimage_eq_inter_range, Subtype.range_val]
  exact Set.inter_eq_left.mpr hC

lemma isClosed_image_subtype_of_isClosed {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsClosed S) {D : Set ↥S} (hD : IsClosed D) :
    IsClosed ((Subtype.val : ↥S → X) '' D) := by
  obtain ⟨E, hE, rfl⟩ := isClosed_induced_iff.mp hD
  rw [Set.image_preimage_eq_inter_range, Subtype.range_val]
  exact hE.inter hS

lemma isIrreducible_preimage_subtype {X : Type*} [TopologicalSpace X] {S C : Set X}
    (hC : C ⊆ S) :
    IsIrreducible (Subtype.val ⁻¹' C : Set ↥S) ↔ IsIrreducible C := by
  constructor
  · intro h
    rw [← image_preimage_val_of_subset hC]
    exact h.image _ continuous_subtype_val.continuousOn
  · rintro ⟨hne, hpre⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hC hx⟩, hx⟩
    · intro u v hu hv hu' hv'
      obtain ⟨u', hu'open, rfl⟩ := isOpen_induced_iff.mp hu
      obtain ⟨v', hv'open, rfl⟩ := isOpen_induced_iff.mp hv
      obtain ⟨x, hxC, hxu⟩ := hu'
      obtain ⟨y, hyC, hyv⟩ := hv'
      obtain ⟨z, hzC, hzu, hzv⟩ := hpre u' v' hu'open hv'open ⟨x, hxC, hxu⟩ ⟨y, hyC, hyv⟩
      exact ⟨⟨z, hC hzC⟩, hzC, hzu, hzv⟩

/-- **Dimension of a closed affine set** is the Krull dimension of its ring of coordinates. -/
theorem topologicalKrullDim_zloc (σ : Type*) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    [I.IsPrime] :
    topologicalKrullDim ↥(zloc σ k I) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  have hkr : Order.krullDim ↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ k)))
      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
    rw [ringKrullDim]
    exact (Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)).symm
  rw [← hkr]
  set P := ↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ k)))
  have hmem : ∀ D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I),
      I ≤ MvPolynomial.vanishingIdeal k ((Subtype.val : ↥(zloc σ k I) → Aff σ k) '' D.1) := by
    intro D
    rw [← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
    rintro _ ⟨d, hd, rfl⟩
    exact d.2
  have hclosed : ∀ D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I),
      IsClosed ((Subtype.val : ↥(zloc σ k I) → Aff σ k) '' D.1) :=
    fun D => isClosed_image_subtype_of_isClosed (isClosed_zloc σ I) D.isClosed'
  have hprime : ∀ D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I),
      (MvPolynomial.vanishingIdeal k
        ((Subtype.val : ↥(zloc σ k I) → Aff σ k) '' D.1)).IsPrime :=
    fun D => isPrime_vanishingIdeal (hclosed D)
      (IsIrreducible.image D.isIrreducible' _ continuous_subtype_val.continuousOn)
  have hinv : ∀ D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I),
      Subtype.val ⁻¹' (zloc σ k (MvPolynomial.vanishingIdeal k
        ((Subtype.val : ↥(zloc σ k I) → Aff σ k) '' D.1))) = D.1 := by
    intro D
    rw [zeroLocus_vanishingIdeal_eq (hclosed D), Set.preimage_image_eq _ Subtype.val_injective]
  let F : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I) → P := fun D =>
    ⟨⟨MvPolynomial.vanishingIdeal k
      ((Subtype.val : ↥(zloc σ k I) → Aff σ k) '' D.1), hprime D⟩, hmem D⟩
  have hsub : ∀ p : P, zloc σ k p.1.asIdeal ⊆ zloc σ k I :=
    fun p => MvPolynomial.zeroLocus_anti_mono p.2
  let G : P → TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I) := fun p =>
    ⟨Subtype.val ⁻¹' zloc σ k p.1.asIdeal,
      (isIrreducible_preimage_subtype (hsub p)).mpr (isIrreducible_zloc_of_isPrime p.1.isPrime),
      (isClosed_zloc σ _).preimage continuous_subtype_val⟩
  have hGF : ∀ D, G (F D) = D := by
    intro D
    exact TopologicalSpace.IrreducibleCloseds.ext (hinv D)
  have hFG : ∀ p, F (G p) = p := by
    intro p
    refine Subtype.ext (PrimeSpectrum.ext ?_)
    show MvPolynomial.vanishingIdeal k ((Subtype.val : ↥(zloc σ k I) → Aff σ k) ''
      (Subtype.val ⁻¹' zloc σ k p.1.asIdeal)) = p.1.asIdeal
    rw [image_preimage_val_of_subset (hsub p)]
    exact MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) p.1.asIdeal
  have hFanti : ∀ D D' : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I), D ≤ D' → F D' ≤ F D := by
    intro D D' hDD'
    exact MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono hDD')
  have hFstrict : StrictMono (fun D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I) =>
      OrderDual.toDual (F D)) := by
    intro D D' hDD'
    refine OrderDual.toDual_lt_toDual.mpr (lt_of_le_of_ne (hFanti D D' hDD'.le) ?_)
    intro heq
    exact hDD'.ne (by
      have h := congrArg G heq
      rw [hGF, hGF] at h
      exact h.symm)
  have hGanti : ∀ p p' : P, p ≤ p' → G p' ≤ G p := by
    intro p p' hpp'
    show Subtype.val ⁻¹' zloc σ k p'.1.asIdeal ⊆ Subtype.val ⁻¹' zloc σ k p.1.asIdeal
    have hle : p.1.asIdeal ≤ p'.1.asIdeal := (PrimeSpectrum.asIdeal_le_asIdeal p.1 p'.1).mpr hpp'
    exact Set.preimage_mono (show zloc σ k p'.1.asIdeal ⊆ zloc σ k p.1.asIdeal from
      MvPolynomial.zeroLocus_anti_mono hle)
  have hGstrict : StrictMono (fun p : Pᵒᵈ => G (OrderDual.ofDual p)) := by
    intro p p' hpp'
    refine lt_of_le_of_ne (hGanti (OrderDual.ofDual p') (OrderDual.ofDual p) (le_of_lt hpp')) ?_
    intro heq
    have h2 : G (OrderDual.ofDual p') = G (OrderDual.ofDual p) := heq.symm
    have h := congrArg F h2
    rw [hFG, hFG] at h
    exact hpp'.ne (by rw [← OrderDual.toDual_ofDual p, ← OrderDual.toDual_ofDual p', h])
  refine le_antisymm ?_ ?_
  · rw [← Order.krullDim_orderDual (α := P)]
    exact Order.krullDim_le_of_strictMono
      (fun D : TopologicalSpace.IrreducibleCloseds ↥(zloc σ k I) => OrderDual.toDual (F D)) hFstrict
  · rw [← Order.krullDim_orderDual (α := P)]
    exact Order.krullDim_le_of_strictMono (fun p : Pᵒᵈ => G (OrderDual.ofDual p)) hGstrict

end
end Hartshorne77.Ex_I_2_7


/-! ### Intrinsic dimension: basic open pieces of affine algebraic sets -/

namespace Hartshorne77.Ex_I_2_7

namespace IntrinsicOpen

open TopologicalSpace

/-- Dimension is monotone under passing to a subset. -/
theorem topologicalKrullDim_subset_le {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) : topologicalKrullDim ↥A ≤ topologicalKrullDim ↥B := by
  have hind : Topology.IsInducing (fun x : ↥A => (⟨x.1, h x.2⟩ : ↥B)) := by
    rw [← Topology.IsInducing.subtypeVal.of_comp_iff]
    exact Topology.IsInducing.subtypeVal
  exact hind.topologicalKrullDim_le

/-- Membership in the closure of the image of a closed subset of a subspace. -/
theorem mem_closure_image_iff {X : Type*} [TopologicalSpace X] {Y : Set X} {T : Set ↥Y}
    (hT : IsClosed T) {y : X} (hy : y ∈ Y) :
    y ∈ closure ((Subtype.val : ↥Y → X) '' T) ↔ (⟨y, hy⟩ : ↥Y) ∈ T := by
  constructor
  · intro h
    obtain ⟨C, hC, hCT⟩ := isClosed_induced_iff.mp hT
    have himg : (Subtype.val : ↥Y → X) '' T = C ∩ Y := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, w.2⟩
        rw [← hCT] at hw
        exact hw
      · rintro ⟨hzC, hzY⟩
        refine ⟨⟨z, hzY⟩, ?_, rfl⟩
        rw [← hCT]
        exact hzC
    rw [← hCT]
    exact closure_minimal inter_subset_left hC (by rw [← himg]; exact h)
  · intro h
    exact subset_closure ⟨⟨y, hy⟩, h, rfl⟩

/-- Transport of topological Krull dimension along a homeomorphism of ambient spaces. -/
theorem topologicalKrullDim_subtype_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) (S : Set α) (T : Set β)
    (h : ∀ y : α, y ∈ S ↔ e y ∈ T) :
    topologicalKrullDim ↥S = topologicalKrullDim ↥T := by
  let Φ : ↥S → ↥T := fun x => ⟨e x.1, (h x.1).mp x.2⟩
  let Ψ : ↥T → ↥S := fun y => ⟨e.symm y.1, (h (e.symm y.1)).mpr (by simp)⟩
  have hleft : Function.LeftInverse Ψ Φ := fun x => Subtype.ext (by simp [Φ, Ψ])
  have hright : Function.RightInverse Ψ Φ := fun y => Subtype.ext (by simp [Φ, Ψ])
  have hcont : Continuous Φ := (e.continuous.comp continuous_subtype_val).subtype_mk _
  have hcont' : Continuous Ψ := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hh : ↥S ≃ₜ ↥T :=
    { toEquiv := ⟨Φ, Ψ, hleft, hright⟩
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  exact IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph

/-- Identification of a subspace of a subspace with the intersection. -/
theorem topologicalKrullDim_subtype_inter {X : Type*} [TopologicalSpace X] (S T : Set X) :
    topologicalKrullDim ↥(S ∩ T) =
      topologicalKrullDim ↥((Subtype.val : ↥T → X) ⁻¹' S) := by
  let Φ : ↥(S ∩ T) → ↥((Subtype.val : ↥T → X) ⁻¹' S) := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  let Ψ : ↥((Subtype.val : ↥T → X) ⁻¹' S) → ↥(S ∩ T) := fun y => ⟨y.1.1, y.2, y.1.2⟩
  have hleft : Function.LeftInverse Ψ Φ := fun x => Subtype.ext rfl
  have hright : Function.RightInverse Ψ Φ := fun y => Subtype.ext (Subtype.ext rfl)
  have hcont : Continuous Φ := by fun_prop
  have hcont' : Continuous Ψ := by fun_prop
  have hh : ↥(S ∩ T) ≃ₜ ↥((Subtype.val : ↥T → X) ⁻¹' S) :=
    { toEquiv := ⟨Φ, Ψ, hleft, hright⟩
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  exact IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph

/-- Dimension over an open cover, for a subset. -/
theorem topologicalKrullDim_subset_iSup_open {X : Type*} [TopologicalSpace X] {S : Set X}
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    topologicalKrullDim ↥S = ⨆ i, topologicalKrullDim ↥(S ∩ U i) := by
  have hW : ∀ i, IsOpen ((Subtype.val : ↥S → X) ⁻¹' U i) := fun i =>
    (hU i).preimage continuous_subtype_val
  have hcov' : (⋃ i, (Subtype.val : ↥S → X) ⁻¹' U i) = Set.univ := by
    rw [← Set.preimage_iUnion, hcov, Set.preimage_univ]
  have h := CoverDim.dim_eq_iSup_of_isOpen_cover (X := ↥S) hW hcov'
  have h2 : (⨆ i, topologicalKrullDim ↥((Subtype.val : ↥S → X) ⁻¹' U i))
      = ⨆ i, topologicalKrullDim ↥(S ∩ U i) :=
    iSup_congr fun i => by
      rw [← topologicalKrullDim_subtype_inter (U i) S, Set.inter_comm]
  exact h.trans h2


/-- Irreducibility is preserved by a homeomorphism. -/
theorem isIrreducible_iff_preimage_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) {T : Set β} :
    IsIrreducible ((e : α → β) ⁻¹' T) ↔ IsIrreducible T := by
  constructor
  · intro h
    have h2 : (e : α → β) '' ((e : α → β) ⁻¹' T) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨e.symm x, by simpa using hx, by simp⟩
    rw [← h2]
    exact h.image e e.continuous.continuousOn
  · intro h
    have h2 : (e.symm : β → α) '' T = (e : α → β) ⁻¹' T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hx; exact ⟨e x, hx, by simp⟩
    rw [← h2]
    exact h.image e.symm e.symm.continuous.continuousOn

section AffineOpenPort

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Fintype σ]

/-- A nonzero element does not vanish identically on a prime zero locus. -/
theorem exists_mem_zloc_notMem_eval {I : Ideal (MvPolynomial σ k)} [hI : I.IsPrime]
    {f : MvPolynomial σ k} (hf : f ∉ I) :
    ∃ x : Aff σ k, x ∈ zloc σ k I ∧ MvPolynomial.eval x f ≠ 0 := by
  by_contra hall
  push Not at hall
  refine hf ?_
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) I]
  exact MvPolynomial.mem_vanishingIdeal_iff.mpr fun x hx => hall x hx

/-- The nonempty basic open piece of an irreducible zero locus is dense in it. -/
theorem closure_zloc_inter_compl_span {I : Ideal (MvPolynomial σ k)} [hI : I.IsPrime]
    {f : MvPolynomial σ k} (hf : f ∉ I) :
    closure (zloc σ k I ∩ (zloc σ k (Ideal.span {f}))ᶜ) = zloc σ k I := by
  obtain ⟨x, hx1, hx2⟩ := exists_mem_zloc_notMem_eval (k := k) hf
  have hne : (zloc σ k I ∩ (zloc σ k (Ideal.span {f}))ᶜ).Nonempty :=
    ⟨x, hx1, by rw [mem_compl_iff]; intro h; exact hx2 (mem_zloc_span.mp h)⟩
  have hopen : IsOpen (zloc σ k (Ideal.span {f}))ᶜ :=
    (isOpen_aff_iff σ ((zloc σ k (Ideal.span {f}))ᶜ)).mpr ⟨Ideal.span {f}, by rw [compl_compl]⟩
  refine le_antisymm (closure_minimal inter_subset_left (isClosed_zloc σ I)) ?_
  exact subset_closure_inter_of_isPreirreducible_of_isOpen
    (isIrreducible_zloc_of_isPrime (P := I) hI).isPreirreducible hopen hne

/-- The prime of the polynomial ring attached to a prime of the localization `A_f`. -/
noncomputable def qOf (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k)
    (P : PrimeSpectrum (Localization.Away (Ideal.Quotient.mk I f))) : Ideal (MvPolynomial σ k) :=
  Ideal.comap (Ideal.Quotient.mk I) (P.asIdeal.under (MvPolynomial σ k ⧸ I))

/-- **(≥)-direction of the basic open lemma.** -/
theorem dim_open_ge_zloc (I : Ideal (MvPolynomial σ k)) [hI : I.IsPrime]
    {f : MvPolynomial σ k} (hf : f ∉ I) :
    ringKrullDim (MvPolynomial σ k ⧸ I) ≤
      topologicalKrullDim ↥(zloc σ k I ∩ (zloc σ k (Ideal.span {f}))ᶜ) := by
  classical
  set Y : Set (Aff σ k) := zloc σ k I ∩ (zloc σ k (Ideal.span {f}))ᶜ with hYdef
  have hg : Ideal.Quotient.mk I f ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hf
  have hdim : ringKrullDim (Localization.Away (Ideal.Quotient.mk I f)) =
      ringKrullDim (MvPolynomial σ k ⧸ I) := AwayDim.ringKrullDim_away_eq k hg
  rw [← hdim]
  have hqprime : ∀ P, (qOf I f P).IsPrime := fun P =>
    Ideal.comap_isPrime (Ideal.Quotient.mk I) (P.asIdeal.under (MvPolynomial σ k ⧸ I))
  have hpq : ∀ P, I ≤ qOf I f P := fun P => by
    have h : RingHom.ker (Ideal.Quotient.mk I) ≤ qOf I f P := Ideal.ker_le_comap _
    rwa [Ideal.mk_ker] at h
  have hfq : ∀ P, f ∉ qOf I f P := by
    intro P hmem
    have hunit : IsUnit (algebraMap (MvPolynomial σ k ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I f)) (Ideal.Quotient.mk I f)) :=
      IsLocalization.Away.algebraMap_isUnit _
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  have hinj : Function.Injective (qOf (I := I) f) := by
    intro P P' h
    have h1 : P.asIdeal.under (MvPolynomial σ k ⧸ I) = P'.asIdeal.under (MvPolynomial σ k ⧸ I) := by
      have h2 := congrArg (fun J => J.map (Ideal.Quotient.mk I)) h
      simpa [qOf, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using h2
    have h3 : P.asIdeal = P'.asIdeal := by
      have h2 := congrArg (fun J => J.map (algebraMap (MvPolynomial σ k ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I f)))) h1
      rw [IsLocalization.map_under (Submonoid.powers (Ideal.Quotient.mk I f)),
        IsLocalization.map_under (Submonoid.powers (Ideal.Quotient.mk I f))] at h2
      exact h2
    exact PrimeSpectrum.ext h3
  let T : PrimeSpectrum (Localization.Away (Ideal.Quotient.mk I f)) →
      TopologicalSpace.IrreducibleCloseds ↥Y := fun P =>
    ⟨(Subtype.val : ↥Y → Aff σ k) ⁻¹' zloc σ k (qOf I f P), ?_, (isClosed_zloc σ _).preimage continuous_subtype_val⟩
  · have hmono : StrictMono (fun P : PrimeSpectrum (Localization.Away (Ideal.Quotient.mk I f)) =>
        OrderDual.toDual (T P)) := by
      intro P P' hlt
      have hqlt : qOf I f P < qOf I f P' :=
        lt_of_le_of_ne (Ideal.comap_mono (Ideal.comap_mono hlt.le))
          (fun h => ne_of_lt hlt (hinj h))
      have hZle : zloc σ k (qOf I f P') ⊆ zloc σ k (qOf I f P) :=
        MvPolynomial.zeroLocus_anti_mono hqlt.le
      have hZne : zloc σ k (qOf I f P') ≠ zloc σ k (qOf I f P) := by
        intro heq
        apply ne_of_lt hqlt
        have h2 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k (qOf I f P')) =
            MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k (qOf I f P)) := by
          have h3 : MvPolynomial.zeroLocus k (qOf I f P') = MvPolynomial.zeroLocus k (qOf I f P) :=
            heq
          rw [h3]
        rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) (qOf I f P'),
          MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) (qOf I f P)] at h2
        exact h2.symm
      have hmain : T P' < T P := by
        refine lt_of_le_of_ne (fun x hx => hZle hx) ?_
        intro heq
        have hset : ((T P' : TopologicalSpace.IrreducibleCloseds ↥Y) : Set ↥Y) =
            ((T P : TopologicalSpace.IrreducibleCloseds ↥Y) : Set ↥Y) :=
          congrArg (fun x : TopologicalSpace.IrreducibleCloseds ↥Y => (x : Set ↥Y)) heq
        have hkey : zloc σ k (qOf I f P') ∩ (zloc σ k (Ideal.span {f}))ᶜ =
            zloc σ k (qOf I f P) ∩ (zloc σ k (Ideal.span {f}))ᶜ := by
          ext x
          constructor
          · intro hx
            have hxY : x ∈ Y := ⟨MvPolynomial.zeroLocus_anti_mono (hpq P') hx.1, hx.2⟩
            have h1 : (⟨x, hxY⟩ : ↥Y) ∈
                ((T P' : TopologicalSpace.IrreducibleCloseds ↥Y) : Set ↥Y) := hx.1
            rw [hset] at h1
            exact ⟨h1, hx.2⟩
          · intro hx
            have hxY : x ∈ Y := ⟨MvPolynomial.zeroLocus_anti_mono (hpq P) hx.1, hx.2⟩
            have h1 : (⟨x, hxY⟩ : ↥Y) ∈
                ((T P : TopologicalSpace.IrreducibleCloseds ↥Y) : Set ↥Y) := hx.1
            rw [← hset] at h1
            exact ⟨h1, hx.2⟩
        have hkey2 : zloc σ k (qOf I f P') = zloc σ k (qOf I f P) := by
          have h2 := congrArg closure hkey
          rwa [closure_zloc_inter_compl_span (hfq P'), closure_zloc_inter_compl_span (hfq P)] at h2
        exact hZne hkey2
      exact OrderDual.toDual_lt_toDual.mpr hmain
    have hkr := Order.krullDim_le_of_strictMono _ hmono
    rwa [Order.krullDim_orderDual] at hkr
  · refine ⟨?_, ?_⟩
    · obtain ⟨x, hx1, hx2⟩ := exists_mem_zloc_notMem_eval (k := k) (hfq P)
      exact ⟨⟨x, MvPolynomial.zeroLocus_anti_mono (hpq P) hx1,
        by rw [mem_compl_iff]; intro h; exact hx2 (mem_zloc_span.mp h)⟩, hx1⟩
    · rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hc₁ hc₂ hsub
      obtain ⟨F₁, hF₁, hz₁⟩ := isClosed_induced_iff.mp hc₁
      obtain ⟨F₂, hF₂, hz₂⟩ := isClosed_induced_iff.mp hc₂
      have hsub' : zloc σ k (qOf I f P) ∩ (zloc σ k (Ideal.span {f}))ᶜ ⊆ F₁ ∪ F₂ := by
        intro x hx
        have hxY : x ∈ Y := ⟨MvPolynomial.zeroLocus_anti_mono (hpq P) hx.1, hx.2⟩
        have hmem : (⟨x, hxY⟩ : ↥Y) ∈ (Subtype.val : ↥Y → Aff σ k) ⁻¹'
            zloc σ k (qOf I f P) := hx.1
        rcases hsub hmem with h | h
        · rw [← hz₁] at h
          exact Or.inl h
        · rw [← hz₂] at h
          exact Or.inr h
      have hZ : zloc σ k (qOf I f P) ⊆ F₁ ∪ F₂ := by
        rw [← closure_zloc_inter_compl_span (hfq P)]
        exact closure_minimal hsub' (hF₁.union hF₂)
      rcases (isPreirreducible_iff_isClosed_union_isClosed.mp
        (isIrreducible_zloc_of_isPrime (P := qOf I f P) (hqprime P)).isPreirreducible)
        F₁ F₂ hF₁ hF₂ hZ with h | h
      · left
        rw [← hz₁]
        exact fun x hx => h hx
      · right
        rw [← hz₂]
        exact fun x hx => h hx

/-- **A nonempty relatively open piece of an irreducible affine algebraic set has the same
dimension as the whole set.** -/
theorem dim_open_of_open_zloc (I : Ideal (MvPolynomial σ k)) [hI : I.IsPrime]
    {W : Set (Aff σ k)} (hW : IsOpen W) (hne : (zloc σ k I ∩ W).Nonempty) :
    topologicalKrullDim ↥(zloc σ k I ∩ W) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  refine le_antisymm ?_ ?_
  · rw [← topologicalKrullDim_zloc σ I]
    exact topologicalKrullDim_subset_le inter_subset_left
  · obtain ⟨J, hJ⟩ := (isOpen_aff_iff σ W).mp hW
    have hex : ∃ g ∈ J, g ∉ I := by
      by_contra hall
      push Not at hall
      obtain ⟨x, hx⟩ := hne
      have h2 : x ∈ zloc σ k J := MvPolynomial.zeroLocus_anti_mono (fun g hg => hall g hg) hx.1
      rw [hJ] at h2
      exact h2 hx.2
    obtain ⟨g, hgJ, hgI⟩ := hex
    have hspan : Ideal.span {g} ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgJ)
    have hZle : zloc σ k J ⊆ zloc σ k (Ideal.span {g}) := MvPolynomial.zeroLocus_anti_mono hspan
    have hsub : zloc σ k I ∩ (zloc σ k (Ideal.span {g}))ᶜ ⊆ zloc σ k I ∩ W := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hWcc : x ∈ (Wᶜ)ᶜ := by
        rw [← hJ]
        exact fun hxJ => hx.2 (hZle hxJ)
      simpa using hWcc
    have hlow : ringKrullDim (MvPolynomial σ k ⧸ I) ≤
        topologicalKrullDim ↥(zloc σ k I ∩ (zloc σ k (Ideal.span {g}))ᶜ) :=
      dim_open_ge_zloc I hgI
    exact le_trans hlow (topologicalKrullDim_subset_le hsub)

end AffineOpenPort

end IntrinsicOpen


section FinalTheorem

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- **(b), intrinsic form.**  A nonempty quasi-projective variety in `ℙ^n` and its closure have
the same topological dimension. -/
theorem topologicalKrullDim_closure_eq_of_isQuasiProjective {n : ℕ}
    {Y : Set ((Projectivization k (Fin (n+1) → k)))} (hY : IsQuasiProjective Y) :
    topologicalKrullDim ↥(closure Y) = topologicalKrullDim ↥Y := by
  classical
  obtain ⟨hne, hirr, Uo, Z, hUopen, hZclosed, hYZ⟩ := hY
  have hcov : (⋃ i : Fin (n+1), U (k := k) i) = Set.univ := by
    ext P
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_contra h
    push Not at h
    have h0 : P.rep = 0 := funext fun j => by simpa [U] using h j
    exact P.rep_nonzero h0
  have hU : ∀ i : Fin (n+1), IsOpen (U (k := k) i) := fun i => isOpen_U i
  refine le_antisymm ?_ (IntrinsicOpen.topologicalKrullDim_subset_le subset_closure)
  rw [IntrinsicOpen.topologicalKrullDim_subset_iSup_open (S := closure Y) hU hcov,
    IntrinsicOpen.topologicalKrullDim_subset_iSup_open (S := Y) hU hcov]
  refine iSup_le fun i => ?_
  refine le_trans ?_ (le_iSup (fun j => topologicalKrullDim ↥(Y ∩ U (k := k) j)) i)
  by_cases hempty : (Y ∩ U (k := k) i).Nonempty
  · have hempty' : (closure Y ∩ U (k := k) i).Nonempty :=
      hempty.mono fun x hx => ⟨subset_closure hx.1, hx.2⟩
    have h1 : topologicalKrullDim ↥(Y ∩ U (k := k) i) =
        topologicalKrullDim ↥(chartPiece (k := k) i Y) := by
      rw [IntrinsicOpen.topologicalKrullDim_subtype_inter Y (U (k := k) i)]
      exact (IntrinsicOpen.topologicalKrullDim_subtype_homeomorph (chartHomeomorph (k := k) i)
        (chartPiece (k := k) i Y) ((Subtype.val : ↥(U (k := k) i) → _) ⁻¹' Y)
        (fun y => Iff.rfl)).symm
    have h2 : topologicalKrullDim ↥(closure Y ∩ U (k := k) i) =
        topologicalKrullDim ↥(chartPiece (k := k) i (closure Y)) := by
      rw [IntrinsicOpen.topologicalKrullDim_subtype_inter (closure Y) (U (k := k) i)]
      exact (IntrinsicOpen.topologicalKrullDim_subtype_homeomorph (chartHomeomorph (k := k) i)
        (chartPiece (k := k) i (closure Y)) ((Subtype.val : ↥(U (k := k) i) → _) ⁻¹' closure Y)
        (fun y => Iff.rfl)).symm
    rw [h1, h2]
    refine le_of_eq ?_
    have hVcclosed : IsClosed (chartPiece (k := k) i (closure Y)) :=
      isClosed_preimage_chartPoint i isClosed_closure
    have hVcirr : IsIrreducible (chartPiece (k := k) i (closure Y)) := by
      have hpre : IsIrreducible ((Subtype.val : ↥(U (k := k) i) → _) ⁻¹' closure Y) :=
        (IsIrreducible.closure hirr).preimage ((isOpen_U (k := k) i).isOpenEmbedding_subtypeVal)
          ⟨hempty'.choose, hempty'.choose_spec.1,
            ⟨⟨hempty'.choose, hempty'.choose_spec.2⟩, rfl⟩⟩
      have h3 := (IntrinsicOpen.isIrreducible_iff_preimage_homeomorph (chartHomeomorph (k := k) i)
        (T := (Subtype.val : ↥(U (k := k) i) → _) ⁻¹' closure Y)).mpr hpre
      have hEq : ((chartHomeomorph (k := k) i : (J n i → k) → ↥(U (k := k) i)) ⁻¹'
          ((Subtype.val : ↥(U (k := k) i) → _) ⁻¹' closure Y)) =
          chartPiece (k := k) i (closure Y) := rfl
      rwa [hEq] at h3
    set I := MvPolynomial.vanishingIdeal k (chartPiece (k := k) i (closure Y)) with hIdef
    have hIprime : I.IsPrime := isPrime_vanishingIdeal hVcclosed hVcirr
    have hVceq : zloc (J n i) k I = chartPiece (k := k) i (closure Y) :=
      zeroLocus_vanishingIdeal_eq hVcclosed
    have hWopen : IsOpen ((chartPoint (k := k) i) ⁻¹' Uo) :=
      hUopen.preimage (continuous_chartPoint i)
    have hVo : chartPiece (k := k) i Y =
        chartPiece (k := k) i (closure Y) ∩ ((chartPoint (k := k) i) ⁻¹' Uo) := by
      ext y
      change chartPoint (k := k) i y ∈ Y ↔
        chartPoint (k := k) i y ∈ closure Y ∧ chartPoint (k := k) i y ∈ Uo
      constructor
      · intro hy
        exact ⟨subset_closure hy, (hYZ ▸ hy).1⟩
      · rintro ⟨hy1, hy2⟩
        rw [hYZ]
        exact ⟨hy2, hZclosed.closure_subset_iff.mpr (by rw [hYZ]; exact Set.inter_subset_right) hy1⟩
    have hVoNe : (zloc (J n i) k I ∩ ((chartPoint (k := k) i) ⁻¹' Uo)).Nonempty := by
      obtain ⟨P, hP1, hP2⟩ := hempty
      have hmem : chartPoint (k := k) i (chartCoord (k := k) i (⟨P, hP2⟩ : ↥(U (k := k) i))) ∈ closure Y := by
        rw [chartPoint_chartCoord (k := k) i hP2]
        exact subset_closure hP1
      have hmem2 : chartPoint (k := k) i (chartCoord (k := k) i (⟨P, hP2⟩ : ↥(U (k := k) i))) ∈ Uo := by
        rw [chartPoint_chartCoord (k := k) i hP2]
        exact (hYZ ▸ hP1).1
      refine ⟨chartCoord (k := k) i (⟨P, hP2⟩ : ↥(U (k := k) i)), ?_, ?_⟩
      · rw [hVceq]
        exact hmem
      · exact hmem2
    calc topologicalKrullDim ↥(chartPiece (k := k) i (closure Y))
        = ringKrullDim (MvPolynomial (J n i) k ⧸ I) := by
          rw [← hVceq]
          exact topologicalKrullDim_zloc (J n i) I
      _ = topologicalKrullDim ↥(chartPiece (k := k) i Y) := by
          rw [show chartPiece (k := k) i Y =
            zloc (J n i) k I ∩ ((chartPoint (k := k) i) ⁻¹' Uo) from by rw [hVo, ← hVceq]]
          exact (IntrinsicOpen.dim_open_of_open_zloc I hWopen hVoNe).symm
  · have h1 : Y ∩ U (k := k) i = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have h2 : closure Y ∩ U (k := k) i = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hxcl : x ∈ closure (Y ∩ U (k := k) i) := closure_inter_subset i ⟨hx.1, hx.2⟩
      rw [h1, closure_empty] at hxcl
      exact hxcl
    rw [h1, h2]

/-- **Hartshorne, Exercise I.2.7**, both parts, in intrinsic form:
(a) `dim ℙ^n = n`; (b) a nonempty quasi-projective variety `Y ⊆ ℙ^n` has `dim Y = dim Ȳ`,
where `dim` is Hartshorne's intrinsic dimension (supremum of lengths of chains of distinct
irreducible closed subsets). -/
theorem exercise_2_7 (n : ℕ) :
    topologicalKrullDim (Projectivization k (Fin (n+1) → k)) = (n : WithBot ℕ∞) ∧
    (∀ Y : Set (Projectivization k (Fin (n+1) → k)), IsQuasiProjective Y →
      topologicalKrullDim ↥(closure Y) = topologicalKrullDim ↥Y) := by
  constructor
  · rw [← dimTop_eq_topologicalKrullDim]
    exact dimTop_projective_space n
  · intro Y hY
    exact topologicalKrullDim_closure_eq_of_isQuasiProjective hY

end FinalTheorem

end Hartshorne77.Ex_I_2_7

#print axioms Hartshorne77.Ex_I_2_7.exercise_2_7
#print axioms Hartshorne77.Ex_I_2_7.topologicalKrullDim_closure_eq_of_isQuasiProjective
#print axioms Hartshorne77.Ex_I_2_7.dimTop_projective_space
#print axioms Hartshorne77.Ex_I_2_7.IntrinsicOpen.dim_open_of_open_zloc
#print axioms Hartshorne77.Ex_I_2_7.IntrinsicOpen.topologicalKrullDim_subset_iSup_open
#print axioms Hartshorne77.Ex_I_2_7.AwayDim.ringKrullDim_away_eq
#print axioms Hartshorne77.Ex_I_2_7.topologicalKrullDim_zloc
