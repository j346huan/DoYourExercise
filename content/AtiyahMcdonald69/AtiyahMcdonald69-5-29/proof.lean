import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic

/-!
# Atiyah–Macdonald (1969), Chapter 5, Exercise 29

Book scan (`.scratch/reference/atiyah-macdonald-original.txt`, p. 72):

> 29. Let A be a valuation ring of a field K. Show that every subring of K which
> contains A is a local ring of A.

Natural-language proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-29

## Source reading

A–M define a valuation ring of a field `K` (5.17) as a subring `A ⊆ K` such that for
every `x ≠ 0` in `K` one has `x ∈ A` or `x⁻¹ ∈ A`; since `0 ∈ A` this is exactly
`∀ x : K, x ∈ A ∨ x⁻¹ ∈ A`, the predicate used below.  The phrase "a local ring of A"
is not terminology the book defines; the content established by the site's natural
proof, and formalised here, is that every subring `B` with `A ≤ B ≤ K` is a local
ring, and more precisely that `B` is the localisation `A_p` of `A` at the prime ideal
`p = m_B ∩ A`.  Both the weak reading (`B` is local) and the strong reading
(`B = A_p`) are proved, so the formalisation is faithful under either reading.

## Main results

* `mem_or_inv_mem_of_le` — `B` is again a valuation ring of `K`.
* `isLocalRing_of_mem_or_inv_mem` — a subring of a field with the valuation property
  is a local ring (A–M 1.18-style criterion).
* `p_isPrime` — `p = m_B ∩ A` is a prime ideal of `A`.
* `mem_of_mem_p_inv`, `exists_fraction` — the two inclusions expressing `B = A_p`.
* `solution` — the bundled statement of the exercise.
-/

namespace AtiyahMcdonald69.Ex_5_29

variable {K : Type*} [Field K]

section SubringLemmas

variable {A B : Subring K}

/-! ### Elementary lemmas on subrings of a field used below -/

/-- An element of `B ⊆ K` whose inverse in `K` lies in `B` is a unit of `B`. -/
theorem isUnit_of_inv_mem {x : ↥B} (hx : (x : K) ≠ 0) (h : (x : K)⁻¹ ∈ B) : IsUnit x := by
  refine IsUnit.of_mul_eq_one (⟨(x : K)⁻¹, h⟩ : ↥B) ?_
  apply Subtype.ext
  simp [mul_inv_cancel₀ hx]

/-- A unit of `B ⊆ K` has its inverse in `B`. -/
theorem inv_mem_of_isUnit {x : ↥B} (hx : IsUnit x) : (x : K)⁻¹ ∈ B := by
  obtain ⟨u, rfl⟩ := hx
  have h : ((↑u : ↥B) : K) * (((u⁻¹ : (↥B)ˣ) : ↥B) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]
    rfl
  rw [inv_eq_of_mul_eq_one_right h]
  exact ((u⁻¹ : (↥B)ˣ) : ↥B).2

/-! ### Part 1: the overring of a valuation ring is a valuation ring -/

/-- A subring of `K` containing a valuation ring `A` of `K` is again a valuation
ring of `K`. -/
theorem mem_or_inv_mem_of_le (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) (hAB : A ≤ B) :
    ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B :=
  fun x => (hA x).imp (fun h => hAB h) (fun h => hAB h)

/-! ### Part 2: such a ring is local -/

/-- Key step: for `a : ↥B` with `B ⊆ K` satisfying the valuation property, either `a`
or `1 - a` is a unit of `B`. -/
theorem isUnit_or_isUnit_one_sub (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (a : ↥B) :
    IsUnit a ∨ IsUnit (1 - a) := by
  by_cases h0 : (a : K) = 0
  · right
    have ha : a = 0 := Subtype.ext (by simpa using h0)
    simp [ha]
  by_cases h1 : (a : K) = 1
  · left
    have ha : a = 1 := Subtype.ext (by simpa using h1)
    simp [ha]
  have hne : (1 : K) - (a : K) ≠ 0 := by
    intro h
    exact h1 (sub_eq_zero.mp h).symm
  rcases hB ((a : K) / (1 - (a : K))) with hc | hc
  · -- `a / (1 - a) ∈ B`: then `1 - a` is a unit
    let c : ↥B := ⟨(a : K) / (1 - (a : K)), hc⟩
    have hca : c * (1 - a) = a := by
      apply Subtype.ext
      show (a : K) / (1 - (a : K)) * (1 - (a : K)) = (a : K)
      exact div_mul_cancel₀ _ hne
    right
    refine IsUnit.of_mul_eq_one_right (c + 1) ?_
    rw [add_mul, one_mul, hca]
    ring
  · -- `(a / (1 - a))⁻¹ = (1 - a) / a ∈ B`: then `a` is a unit
    rw [inv_div] at hc
    let d : ↥B := ⟨(1 - (a : K)) / (a : K), hc⟩
    have hda : d * a = 1 - a := by
      apply Subtype.ext
      show (1 - (a : K)) / (a : K) * (a : K) = 1 - (a : K)
      exact div_mul_cancel₀ _ h0
    left
    refine IsUnit.of_mul_eq_one_right (d + 1) ?_
    rw [add_mul, one_mul, hda]
    ring

/-- A subring of a field satisfying the valuation property is a local ring. -/
theorem isLocalRing_of_mem_or_inv_mem (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) :
    IsLocalRing ↥B :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self (isUnit_or_isUnit_one_sub hB)

/-- Every subring of `K` containing a valuation ring `A` of `K` is a local ring. -/
theorem isLocalRing_of_le (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) (hAB : A ≤ B) :
    IsLocalRing ↥B :=
  isLocalRing_of_mem_or_inv_mem (mem_or_inv_mem_of_le hA hAB)

/-! ### Part 3: the prime ideal `p = m_B ∩ A` -/

/-- The contraction `p = m_B ∩ A` of the maximal ideal of `B` to `A`. -/
def p (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (hAB : A ≤ B) : Ideal ↥A :=
  letI := isLocalRing_of_mem_or_inv_mem hB
  Ideal.comap (Subring.inclusion hAB) (IsLocalRing.maximalIdeal ↥B)

/-- Membership in `p`, in terms of the inclusion `A → B`. -/
theorem mem_p (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (hAB : A ≤ B) (a : ↥A) :
    a ∈ p hB hAB ↔ ¬ IsUnit (Subring.inclusion hAB a) := by
  have _hloc : IsLocalRing ↥B := isLocalRing_of_mem_or_inv_mem hB
  exact Iff.rfl

/-- Membership in `p`, in terms of the ambient field. -/
theorem mem_p_iff (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (hAB : A ≤ B) (a : ↥A) :
    a ∈ p hB hAB ↔ ¬ IsUnit (⟨(a : K), hAB a.2⟩ : ↥B) := by
  rw [mem_p]
  have h : Subring.inclusion hAB a = (⟨(a : K), hAB a.2⟩ : ↥B) := Subtype.ext rfl
  rw [h]

/-- `p` is a prime ideal of `A`. -/
theorem p_isPrime (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (hAB : A ≤ B) :
    (p hB hAB).IsPrime := by
  have _hloc : IsLocalRing ↥B := isLocalRing_of_mem_or_inv_mem hB
  have hp : p hB hAB = Ideal.comap (Subring.inclusion hAB) (IsLocalRing.maximalIdeal ↥B) :=
    rfl
  rw [hp]
  exact Ideal.comap_isPrime _ _

/-! ### Part 4: `B = A_p` -/

/-- The inclusion `A_p ⊆ B`: if `s ∈ A` becomes a unit of `B` (i.e. `s ∉ p`), then
every fraction `a / s` with `a ∈ A` lies in `B`. -/
theorem mem_of_mem_p_inv (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B) (hAB : A ≤ B) {a s : ↥A}
    (hs : s ∉ p hB hAB) : (a : K) * (s : K)⁻¹ ∈ B := by
  have hs' : IsUnit (Subring.inclusion hAB s) := by
    by_contra h
    exact hs ((mem_p hB hAB s).mpr h)
  have hinv : (s : K)⁻¹ ∈ B := by
    have h1 := inv_mem_of_isUnit hs'
    simpa using h1
  exact B.mul_mem (hAB a.2) hinv

/-- The inclusion `B ⊆ A_p`: every element of `B` is a fraction `a / s` with `a ∈ A`
and `s ∈ A \ p`. -/
theorem exists_fraction (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B)
    (hAB : A ≤ B) (b : ↥B) :
    ∃ a s : ↥A, s ∉ p hB hAB ∧ (b : K) = (a : K) * (s : K)⁻¹ := by
  by_cases hb : (b : K) ∈ A
  · refine ⟨⟨(b : K), hb⟩, 1, ?_, ?_⟩
    · rw [mem_p_iff]
      intro h
      exact h isUnit_one
    · simp
  · have hb0 : (b : K) ≠ 0 := fun h => hb (h ▸ A.zero_mem)
    have hinvA : (b : K)⁻¹ ∈ A := (hA ((b : K))).resolve_left hb
    let s : ↥A := ⟨(b : K)⁻¹, hinvA⟩
    have hsv : (s : K) = (b : K)⁻¹ := rfl
    refine ⟨1, s, ?_, ?_⟩
    · rw [mem_p_iff]
      intro h
      have hx0 : (s : K) ≠ 0 := by rw [hsv]; exact inv_ne_zero hb0
      have hinv : (s : K)⁻¹ ∈ B := by rw [hsv, inv_inv]; exact b.2
      exact h (isUnit_of_inv_mem (x := (⟨(s : K), hAB s.2⟩ : ↥B)) hx0 hinv)
    · show (b : K) = ((1 : ↥A) : K) * (s : K)⁻¹
      rw [Subring.coe_one, one_mul, hsv, inv_inv]

/-! ### `B` is the localisation of `A` at `p` -/

/-- **The strong form of the exercise**: `B` is the localisation of `A` at the prime
ideal `p = m_B ∩ A` (i.e. `IsLocalization.AtPrime ↥B p`), with `A`-algebra structure
given by the inclusion `A → B`. -/
theorem isLocalization_p (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) (hB : ∀ x : K, x ∈ B ∨ x⁻¹ ∈ B)
    (hAB : A ≤ B) :
    letI : Algebra ↥A ↥B := (Subring.inclusion hAB).toAlgebra
    haveI : (p hB hAB).IsPrime := p_isPrime hB hAB
    IsLocalization (p hB hAB).primeCompl ↥B := by
  let _alg : Algebra ↥A ↥B := (Subring.inclusion hAB).toAlgebra
  have _pr : (p hB hAB).IsPrime := p_isPrime hB hAB
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- every `s ∉ p` is a unit of `B`
    intro y
    have hy : (y : ↥A) ∉ p hB hAB := y.2
    show IsUnit (Subring.inclusion hAB (y : ↥A))
    exact not_not.mp ((mem_p hB hAB (y : ↥A)).not.mp hy)
  · -- every element of `B` is a fraction `a / s` with `s ∉ p`
    intro z
    obtain ⟨a, s, hs, he⟩ := exists_fraction hA hB hAB z
    refine ⟨(a, ⟨s, hs⟩), ?_⟩
    change z * Subring.inclusion hAB s = Subring.inclusion hAB a
    have hs0 : (s : K) ≠ 0 := by
      intro h
      apply hs
      have hsz : s = 0 := Subtype.ext (by simpa using h)
      rw [hsz]
      exact (p hB hAB).zero_mem
    have hK : (z : K) * (s : K) = (a : K) := by
      rw [he, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    apply Subtype.ext
    simpa only [Subring.coe_mul, Subring.coe_inclusion] using hK
  · -- the inclusion `A → B` is injective
    intro x y hxy
    refine ⟨1, ?_⟩
    have h : Subring.inclusion hAB x = Subring.inclusion hAB y := hxy
    have hxy' : x = y := Subring.inclusion_injective hAB h
    rw [hxy']

/-! ### The maximal ideal of `B` and its contraction -/

/-- The units of `B` are exactly the elements of `B` whose inverse in `K` lies in `B`. -/
theorem isUnit_iff_inv_mem {x : ↥B} (hx : (x : K) ≠ 0) : IsUnit x ↔ (x : K)⁻¹ ∈ B :=
  ⟨inv_mem_of_isUnit, isUnit_of_inv_mem hx⟩

section MaximalIdeal

variable [IsLocalRing ↥B]

/-- The maximal ideal of `B` is the set of nonunits, namely the elements of `B` whose
inverse in `K` is not in `B`, together with `0`. -/
theorem mem_maximalIdeal_iff {x : ↥B} :
    x ∈ IsLocalRing.maximalIdeal ↥B ↔ (x : K) = 0 ∨ (x : K)⁻¹ ∉ B := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    by_cases h0 : (x : K) = 0
    · exact Or.inl h0
    · exact Or.inr fun hinv => hx (isUnit_of_inv_mem h0 hinv)
  · rintro (h0 | hinv)
    · have hx0 : x = 0 := Subtype.ext (by simpa using h0)
      rw [hx0]
      exact not_isUnit_zero
    · intro hx
      exact hinv (inv_mem_of_isUnit hx)

end MaximalIdeal

/-! ### The exercise -/

/-- **Atiyah–Macdonald (1969), Chapter 5, Exercise 29.**  Let `A` be a valuation ring
of a field `K`.  Then every subring `B` of `K` containing `A` is a local ring, and is
in fact the localisation `A_p` of `A` at the prime ideal `p = m_B ∩ A`: the nonunits
of `B` form its maximal ideal, `p` is prime, and an element of `K` lies in `B` exactly
when it is a fraction `a / s` with `a ∈ A` and `s ∈ A` a unit of `B`. -/
theorem solution (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) (hAB : A ≤ B) :
    IsLocalRing ↥B ∧ (p (mem_or_inv_mem_of_le hA hAB) hAB).IsPrime ∧
      ∀ x : K, x ∈ B ↔ ∃ a s : ↥A,
        s ∉ p (mem_or_inv_mem_of_le hA hAB) hAB ∧ x = (a : K) * (s : K)⁻¹ := by
  have hB := mem_or_inv_mem_of_le hA hAB
  refine ⟨isLocalRing_of_mem_or_inv_mem hB, p_isPrime hB hAB, ?_⟩
  intro x
  constructor
  · intro hx
    exact exists_fraction hA hB hAB ⟨x, hx⟩
  · rintro ⟨a, s, hs, rfl⟩
    exact mem_of_mem_p_inv hB hAB hs

end SubringLemmas

end AtiyahMcdonald69.Ex_5_29

#print axioms AtiyahMcdonald69.Ex_5_29.isUnit_of_inv_mem
#print axioms AtiyahMcdonald69.Ex_5_29.inv_mem_of_isUnit
#print axioms AtiyahMcdonald69.Ex_5_29.mem_or_inv_mem_of_le
#print axioms AtiyahMcdonald69.Ex_5_29.isUnit_or_isUnit_one_sub
#print axioms AtiyahMcdonald69.Ex_5_29.isLocalRing_of_mem_or_inv_mem
#print axioms AtiyahMcdonald69.Ex_5_29.isLocalRing_of_le
#print axioms AtiyahMcdonald69.Ex_5_29.mem_p
#print axioms AtiyahMcdonald69.Ex_5_29.mem_p_iff
#print axioms AtiyahMcdonald69.Ex_5_29.p_isPrime
#print axioms AtiyahMcdonald69.Ex_5_29.mem_of_mem_p_inv
#print axioms AtiyahMcdonald69.Ex_5_29.exists_fraction
#print axioms AtiyahMcdonald69.Ex_5_29.isUnit_iff_inv_mem
#print axioms AtiyahMcdonald69.Ex_5_29.mem_maximalIdeal_iff
#print axioms AtiyahMcdonald69.Ex_5_29.isLocalization_p
#print axioms AtiyahMcdonald69.Ex_5_29.solution
