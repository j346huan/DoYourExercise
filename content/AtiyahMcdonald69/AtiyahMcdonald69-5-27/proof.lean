/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 5, Exercise 27.

Original statement (scan, exercise 27 of Chapter 5):

  "Valuation rings and valuations
   27. Let A, B be two local rings. B is said to dominate A if A is a subring of B and the
   maximal ideal m of A is contained in the maximal ideal n of B (or, equivalently, if
   m = n ∩ A). Let K be a field and let Σ be the set of all local subrings of K. If Σ is ordered
   by the relation of domination, show that Σ has maximal elements and that A ∈ Σ is maximal
   if and only if A is a valuation ring of K. [Use (5.21).]"

Formal content of this file (namespace `AtiyahMcdonald69.Ex_5_27`):

* `Dominates A B` : the book's domination relation for two local subrings of a field `K`, stated
  literally with the two maximal ideals (`m_A ⊆ m_B`).
* `dominates_iff_le`, `dominates_iff_forall`, `dominates_iff_comap` : the book's definition
  read elementwise, and the book's parenthetical that `m_A ⊆ m_B` is equivalent to
  `m_A = m_B ∩ A`.
* `exists_upperBound_of_isChain` : the Zorn step of the book's proof: a chain of local subrings
  of `K` has an upper bound (the union of the chain is again a local subring dominating it).
* `exists_maximal` (PART 1) : `Σ` has maximal elements.
* `exists_maximal_ge` : the refinement used in the proof of (5.22): a maximal element above any
  prescribed local subring.
* `IsValuationRingOf A` : the book's definition (5.18) of "`A` is a valuation ring of `K`":
  for every `x ≠ 0` either `x ∈ A` or `x⁻¹ ∈ A`.
* `isValuationRingOf_iff_exists_valuationSubring` : agreement with Mathlib's `ValuationSubring`.
* `dominates_of_isValuationRingOf` : the book's converse paragraph: a valuation ring cannot be
  strictly dominated.
* `isValuationRingOf_of_isMax` : a maximal element of `Σ` is a valuation ring (the direction that
  in the book uses (5.20) and Theorem (5.21); here it is obtained from `LocalSubring.isMax_iff`,
  which is Mathlib's formalised proof of (the Stacks project form of) Theorem (5.21)).
* `maximal_iff_isValuationRingOf` (PART 2) : `A ∈ Σ` is maximal if and only if `A` is a
  valuation ring of `K`; `maximal_iff_exists_valuationSubring` is the same statement for
  Mathlib's `ValuationSubring`.
* `isLocalRing_of_forall_mem_or_inv_mem` (5.18)(i) and `forall_mem_or_inv_mem_of_le` (5.18)(ii):
  the two facts about valuation rings that the exercise's terminology rests on.

Everything is proved in terms of these statements; no `sorry`, no added axioms.
-/
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Order.Zorn

namespace AtiyahMcdonald69.Ex_5_27

open IsLocalRing

variable {K : Type*} [Field K]

/-! ## The domination relation -/

/-- `B` dominates `A` (Atiyah–Macdonald, Chapter 5, Exercise 27): `A` is a subring of `B` and the
maximal ideal of `A` is contained in the maximal ideal of `B`. -/
def Dominates (A B : LocalSubring K) : Prop :=
  ∃ h : A.toSubring ≤ B.toSubring,
    Ideal.map (Subring.inclusion h) (maximalIdeal A.toSubring) ≤ maximalIdeal B.toSubring

/-- The book's domination relation is Mathlib's partial order on `LocalSubring K`
(which is defined by the equivalent "reflects units" condition). -/
theorem dominates_iff_le {A B : LocalSubring K} : Dominates A B ↔ A ≤ B := by
  rw [LocalSubring.le_def]
  exact exists_congr fun h =>
    ((IsLocalRing.local_hom_TFAE (Subring.inclusion h)).out 0 2).symm

/-- The book's parenthetical: for local subrings `A ⊆ B` of `K`, `m_A ⊆ m_B` if and only if
`m_A = m_B ∩ A`. -/
theorem dominates_iff_comap {A B : LocalSubring K} :
    Dominates A B ↔ ∃ h : A.toSubring ≤ B.toSubring,
      Ideal.comap (Subring.inclusion h) (maximalIdeal B.toSubring) = maximalIdeal A.toSubring := by
  refine exists_congr fun h => ?_
  exact (IsLocalRing.local_hom_TFAE (Subring.inclusion h)).out 2 4

theorem dominates_iff_forall {A B : LocalSubring K} :
    Dominates A B ↔ ∃ h : A.toSubring ≤ B.toSubring,
      ∀ x : A.toSubring,
        x ∈ maximalIdeal A.toSubring → Subring.inclusion h x ∈ maximalIdeal B.toSubring := by
  refine exists_congr fun h => ?_
  rw [Ideal.map_le_iff_le_comap]
  exact ⟨fun h x hx => Ideal.mem_comap.mp (h hx), fun h x hx => Ideal.mem_comap.mpr (h x hx)⟩

theorem dominates_refl (A : LocalSubring K) : Dominates A A :=
  dominates_iff_le.mpr le_rfl

theorem dominates_trans {A B C : LocalSubring K} (hAB : Dominates A B) (hBC : Dominates B C) :
    Dominates A C :=
  dominates_iff_le.mpr ((dominates_iff_le.mp hAB).trans (dominates_iff_le.mp hBC))

/-- Domination is a partial order on the local subrings of `K`, so the phrase "`Σ` ordered by
the relation of domination" is legitimate. -/
theorem dominates_antisymm {A B : LocalSubring K} (hAB : Dominates A B) (hBA : Dominates B A) :
    A = B :=
  le_antisymm (dominates_iff_le.mp hAB) (dominates_iff_le.mp hBA)

/-! ## The Zorn step: a chain of local subrings has an upper bound

This is the argument of the printed solution: for a chain `c` of local subrings of `K` ordered by
domination, the union of the underlying subrings is a subring of `K`; it is local, because an
element of the union which is not a unit is a nonunit at the stage where it occurs, and domination
prevents it from becoming invertible at a later (larger) stage.  The union therefore dominates the
whole chain. -/

theorem exists_upperBound_of_isChain (c : Set (LocalSubring K)) (hc : IsChain (· ≤ ·) c) :
    ∃ ub : LocalSubring K, ∀ A ∈ c, A ≤ ub := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨(⊤ : ValuationSubring K).toLocalSubring, by simp⟩
  obtain ⟨y₀, hy₀⟩ := hne
  have dirOn : ∀ ⦃A⦄, A ∈ c → ∀ ⦃B⦄, B ∈ c → ∃ C ∈ c, A ≤ C ∧ B ≤ C := by
    intro A hA B hB
    rcases eq_or_ne A B with rfl | hne
    · exact ⟨A, hA, le_rfl, le_rfl⟩
    · rcases hc hA hB hne with h | h
      · exact ⟨B, hB, h, le_rfl⟩
      · exact ⟨A, hA, le_rfl, h⟩
  have hdir : Directed (· ≤ ·) fun A : c => (A : LocalSubring K).toSubring :=
    hc.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ A : c, (A : LocalSubring K).toSubring) ⟨?_⟩, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨A, haA⟩ := (Subring.mem_iSup_of_directed (hι := ⟨⟨y₀, hy₀⟩⟩) hdir).mp ha
    obtain ⟨B, hbB⟩ := (Subring.mem_iSup_of_directed (hι := ⟨⟨y₀, hy₀⟩⟩) hdir).mp hb
    obtain ⟨C, hC, hAC, hBC⟩ := dirOn A.2 B.2
    have hab' : a + b = 1 := congrArg Subtype.val hab
    refine (IsLocalRing.isUnit_or_isUnit_of_add_one (R := ↥C.toSubring)
      (a := ⟨a, hAC.1 haA⟩) (b := ⟨b, hBC.1 hbB⟩) (Subtype.ext hab')).imp ?_ ?_
    · exact fun h =>
        h.map (Subring.inclusion (le_iSup (fun A : c => (A : LocalSubring K).toSubring) ⟨C, hC⟩))
    · exact fun h =>
        h.map (Subring.inclusion (le_iSup (fun A : c => (A : LocalSubring K).toSubring) ⟨C, hC⟩))
  · intro A hA
    refine ⟨le_iSup (fun A : c => (A : LocalSubring K).toSubring) ⟨A, hA⟩, ?_⟩
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hyx⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨B, hBy⟩ := (Subring.mem_iSup_of_directed (hι := ⟨⟨y₀, hy₀⟩⟩) hdir).mp y.2
    obtain ⟨C, hC, hAC, hBC⟩ := dirOn hA B.2
    have hxC : IsUnit (Subring.inclusion hAC.1 x) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨y.1, hBC.1 hBy⟩, Subtype.ext ?_⟩
      simpa using congrArg Subtype.val hyx
    exact hAC.2.map_nonunit x hxC

/-! ## Part 1: `Σ` has maximal elements -/

/-- **Exercise 5.27, first assertion.** The set `Σ` of local subrings of `K`, ordered by
domination, has maximal elements. -/
theorem exists_maximal (K : Type*) [Field K] :
    ∃ A : LocalSubring K, ∀ B : LocalSubring K, Dominates A B → Dominates B A := by
  obtain ⟨A, hA⟩ := zorn_le (fun c hc => exists_upperBound_of_isChain (K := K) c hc)
  exact ⟨A, fun B hAB => dominates_iff_le.mpr (hA (dominates_iff_le.mp hAB))⟩

/-- Zorn's lemma also gives a maximal element above any prescribed local subring, a form used in
the proof of Corollary (5.22). -/
theorem exists_maximal_ge (A : LocalSubring K) :
    ∃ B : LocalSubring K, Dominates A B ∧ ∀ C : LocalSubring K, Dominates B C → Dominates C B := by
  obtain ⟨B, hAB, hB⟩ := zorn_le_nonempty_Ici₀ (α := LocalSubring K) A
    (fun c _ hc _ _ => exists_upperBound_of_isChain (K := K) c hc) A le_rfl
  exact ⟨B, dominates_iff_le.mpr hAB,
    fun C hBC => dominates_iff_le.mpr (hB (dominates_iff_le.mp hBC))⟩

/-! ## Part 2: maximal elements are exactly the valuation rings of `K` -/

/-- Atiyah–Macdonald (5.18): `A` is a valuation ring of `K` if for every `x ≠ 0` either `x ∈ A`
or `x⁻¹ ∈ A`. -/
def IsValuationRingOf (A : LocalSubring K) : Prop :=
  ∀ x : K, x ≠ 0 → x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

/-- The book's definition of a valuation ring agrees with Mathlib's `ValuationSubring`
(whose condition also covers `x = 0`, where it is trivially satisfied). -/
theorem isValuationRingOf_iff_exists_valuationSubring (A : LocalSubring K) :
    IsValuationRingOf A ↔ ∃ V : ValuationSubring K, V.toSubring = A.toSubring := by
  constructor
  · intro h
    refine ⟨⟨A.toSubring, fun x => ?_⟩, rfl⟩
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ A.toSubring.zero_mem)
    · exact h x hx
  · rintro ⟨V, hV⟩ x _
    rw [← hV]
    simpa using V.mem_or_inv_mem x

/-- The book's converse paragraph: no local subring strictly dominates a valuation ring. -/
theorem dominates_of_isValuationRingOf {A : LocalSubring K} (hA : IsValuationRingOf A)
    {B : LocalSubring K} (hAB : Dominates A B) : Dominates B A := by
  have hle : A ≤ B := dominates_iff_le.mp hAB
  obtain ⟨h, hmap⟩ := hAB
  have hsub : B.toSubring ≤ A.toSubring := by
    intro x hx
    by_contra hxA
    have hx0 : x ≠ 0 := by rintro rfl; exact hxA A.toSubring.zero_mem
    have hinv : x⁻¹ ∈ A.toSubring := (hA x hx0).resolve_left hxA
    -- `x⁻¹` is a nonunit of `A`
    have hnonunit : (⟨x⁻¹, hinv⟩ : ↥A.toSubring) ∈ maximalIdeal A.toSubring := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : ↥A.toSubring) : K) = x⁻¹ := congrArg Subtype.val hu
      have h3 : x⁻¹ * ((↑u⁻¹ : ↥A.toSubring) : K) = 1 := by
        rw [← h1]
        exact congrArg Subtype.val (u.mul_inv)
      have h4 : ((↑u⁻¹ : ↥A.toSubring) : K) = x := by
        calc ((↑u⁻¹ : ↥A.toSubring) : K)
            = 1 * ((↑u⁻¹ : ↥A.toSubring) : K) := (one_mul _).symm
          _ = (x * x⁻¹) * ((↑u⁻¹ : ↥A.toSubring) : K) := by rw [mul_inv_cancel₀ hx0]
          _ = x * (x⁻¹ * ((↑u⁻¹ : ↥A.toSubring) : K)) := by rw [mul_assoc]
          _ = x * 1 := by rw [h3]
          _ = x := mul_one x
      exact hxA (h4 ▸ (↑u⁻¹ : ↥A.toSubring).2)
    -- but it is a unit of `B`, since `x ∈ B`
    have hmem : (Subring.inclusion h ⟨x⁻¹, hinv⟩ : ↥B.toSubring) ∈ maximalIdeal B.toSubring :=
      hmap (Ideal.mem_map_of_mem (Subring.inclusion h) hnonunit)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    apply hmem
    exact isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  have heq : B = A := LocalSubring.toSubring_injective (le_antisymm hsub hle.1)
  rw [heq]
  exact dominates_refl A

/-- A maximal element of `Σ` is a valuation ring of `K`.

In the book this is where (5.20) and Theorem (5.21) are used.  Here the reduction is
`LocalSubring.isMax_iff`, Mathlib's formalised proof of that theorem (Stacks 00IB): a local
subring which is maximal for domination is a valuation ring.  The rest of this file is
independent of that result. -/
theorem isValuationRingOf_of_isMax {A : LocalSubring K}
    (hA : ∀ B : LocalSubring K, Dominates A B → Dominates B A) : IsValuationRingOf A := by
  have hmax : IsMax A := fun B hAB => dominates_iff_le.mp (hA B (dominates_iff_le.mpr hAB))
  obtain ⟨V, hV⟩ := LocalSubring.isMax_iff.mp hmax
  rw [isValuationRingOf_iff_exists_valuationSubring]
  exact ⟨V, congrArg LocalSubring.toSubring hV⟩

/-- **Exercise 5.27, second assertion.** A local subring of `K` is maximal for domination if and
only if it is a valuation ring of `K`. -/
theorem maximal_iff_isValuationRingOf (A : LocalSubring K) :
    (∀ B : LocalSubring K, Dominates A B → Dominates B A) ↔ IsValuationRingOf A :=
  ⟨isValuationRingOf_of_isMax, fun h _ hAB => dominates_of_isValuationRingOf h hAB⟩

/-! ## The facts about valuation rings on which the exercise's terminology rests -/

/-- (5.18)(i): a subring of `K` satisfying the book's valuation condition is a local ring, so that
it is an element of `Σ`. -/
theorem isLocalRing_of_forall_mem_or_inv_mem {B : Subring K}
    (hB : ∀ x : K, x ≠ 0 → x ∈ B ∨ x⁻¹ ∈ B) : IsLocalRing ↥B := by
  have hV : ∃ V : ValuationSubring K, V.toSubring = B := by
    refine ⟨⟨B, fun x => ?_⟩, rfl⟩
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ B.zero_mem)
    · exact hB x hx
  obtain ⟨V, hV⟩ := hV
  exact hV ▸ V.isLocalRing

/-- (5.18)(ii): every subring of `K` containing a valuation ring of `K` is a valuation ring. -/
theorem forall_mem_or_inv_mem_of_le {B C : Subring K} (hBC : B ≤ C)
    (hB : ∀ x : K, x ≠ 0 → x ∈ B ∨ x⁻¹ ∈ B) :
    ∀ x : K, x ≠ 0 → x ∈ C ∨ x⁻¹ ∈ C := by
  intro x hx
  rcases hB x hx with h | h
  · exact Or.inl (hBC h)
  · exact Or.inr (hBC h)

/-- **Exercise 5.27**, both assertions in one statement. -/
theorem solution :
    (∃ A : LocalSubring K, ∀ B : LocalSubring K, Dominates A B → Dominates B A) ∧
      (∀ A : LocalSubring K,
        (∀ B : LocalSubring K, Dominates A B → Dominates B A) ↔ IsValuationRingOf A) :=
  ⟨exists_maximal K, maximal_iff_isValuationRingOf⟩

/-- The second assertion of the exercise, in the form of Mathlib's `ValuationSubring`. -/
theorem maximal_iff_exists_valuationSubring (A : LocalSubring K) :
    (∀ B : LocalSubring K, Dominates A B → Dominates B A) ↔
      ∃ V : ValuationSubring K, V.toSubring = A.toSubring :=
  (maximal_iff_isValuationRingOf A).trans (isValuationRingOf_iff_exists_valuationSubring A)

end AtiyahMcdonald69.Ex_5_27
