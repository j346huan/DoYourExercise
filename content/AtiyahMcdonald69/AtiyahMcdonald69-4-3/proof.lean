/-
# Atiyah–Macdonald (1969), Exercise 4.3

**Statement** (Chapter 4, page 55; cross-checked against the book text and the
transcription in `.scratch/dl/amcd.tex`, "Page 55, Exercise 4.3"):

> If `A` is absolutely flat, every primary ideal is maximal.

*Absolutely flat* means (Chapter 2, Exercise 27) that every `A`-module is flat.
The natural solution accompanying the exercise routes through Exercise 3.10(ii)
(`A` is absolutely flat iff `A_𝔪` is a field for every maximal ideal `𝔪`) together
with Proposition 4.8, concluding via `𝔮A_𝔪 = 0` and `(𝔪A_𝔪)^c = 𝔪`.  The route
formalized below is shorter and needs neither localization nor Proposition 4.8:
from the flatness of `A ⧸ (a)` and the
equational criterion for flatness we get the "von Neumann regularity" consequence
of absolute flatness,

  `∀ a, ∃ b, a = a ^ 2 * b`   (i.e. every principal ideal is idempotent),

and then the argument is a two-line element chase: for a primary `𝔮 ⊆ 𝔪` with `𝔪`
maximal and `x ∈ 𝔪`, write `x = x ^ 2 * b`; then `x * (1 - x * b) = 0 ∈ 𝔮`, so
`x ∉ 𝔮` would force `(1 - x * b) ^ n ∈ 𝔮 ⊆ 𝔪`, contradicting `1 - x * b ∉ 𝔪`.
Hence `𝔪 ⊆ 𝔮`.  (This is the same idea as the solution in `amcd.tex`, which reduces
to the case `𝔮 = 0` and shows that `A` is then a field.)
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_4_3

universe u

/-- A ring is **absolutely flat** (Atiyah–Macdonald, Chapter 2, Exercise 27) if every
module over it is flat.  As is standard in Mathlib, modules are taken in the same
universe as the ring; this is the only case ever used below (the quotient `A ⧸ (a)`). -/
def AbsolutelyFlat (A : Type u) [CommRing A] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Flat A M

/-- **Absolutely flat rings are von Neumann regular**: every principal ideal is
idempotent, i.e. `a = a ^ 2 * b` for some `b`.  This is the implication (i) ⇒ (ii) of
Atiyah–Macdonald, Chapter 2, Exercise 27.

Proof: `A ⧸ (a)` is flat, so by the equational criterion for flatness the relation
`a * 1 = 0` in `A ⧸ (a)` is trivial.  This gives a finite family `y j ∈ A ⧸ (a)` and
coefficients `c j` with `1 = ∑ j, c j * y j` in `A ⧸ (a)` and `a * c j = 0` in `A`.
Lifting the `y j` to elements `c' j` of `A` gives `1 - ∑ j, c j * c' j = b * a`, whence
`a = a * (∑ j, c j * c' j) + a * (b * a) = 0 + a ^ 2 * b`, as `a * c j = 0`. -/
theorem exists_eq_mul_sq_of_absolutelyFlat {A : Type u} [CommRing A]
    (hA : AbsolutelyFlat A) (a : A) : ∃ b, a = a ^ 2 * b := by
  classical
  let I : Ideal A := Ideal.span {a}
  have hflat : Module.Flat A (A ⧸ I) := hA _
  -- the relation `a • 1 = 0` in `A ⧸ (a)`
  have hrel : ∑ i : Fin 1, (fun _ : Fin 1 => a) i • (fun _ : Fin 1 => (1 : A ⧸ I)) i = 0 := by
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    · intro b _ hb; exact absurd (Fin.eq_zero b) hb
    · intro h; exact absurd (Finset.mem_univ _) h
  -- triviality of the relation, via the equational criterion for flatness
  obtain ⟨k, c, y, hy1, hy2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  -- lift the `y j` to elements of `A`
  choose c' hc' using fun j => Ideal.Quotient.mk_surjective (y j)
  have hsum : (∑ j : Fin k, c 0 j • y j) =
      ∑ j : Fin k, (Ideal.Quotient.mk I) (c 0 j * c' j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul, hc' j]
  -- `1 = ∑ j, c 0 j * c' j` in `A ⧸ (a)`
  have hone : (Ideal.Quotient.mk I) (∑ j : Fin k, c 0 j * c' j) = 1 := by
    rw [map_sum, ← hsum, ← hy1 0]
  have hmem : (1 - ∑ j : Fin k, c 0 j * c' j) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hone]
    simp
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  -- the coefficients `c 0 j` annihilate `a`
  have h1 : ∀ j : Fin k, a * c 0 j = 0 := by
    intro j
    have := hy2 j
    simpa using this
  have hzero : a * (∑ j : Fin k, c 0 j * c' j) = 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_assoc, h1 j, zero_mul]
  refine ⟨b, ?_⟩
  calc a = a * 1 := by ring
    _ = a * ((∑ j : Fin k, c 0 j * c' j) + (1 - ∑ j : Fin k, c 0 j * c' j)) := by ring
    _ = a * (∑ j : Fin k, c 0 j * c' j) + a * (1 - ∑ j : Fin k, c 0 j * c' j) := by ring
    _ = a * (b * a) := by rw [← hb, hzero, zero_add]
    _ = a ^ 2 * b := by ring

/-- **The heart of Exercise 4.3.**  If every element `a` of a ring satisfies
`a = a ^ 2 * b` for some `b` (in particular if the ring is absolutely flat, see
`exists_eq_mul_sq_of_absolutelyFlat`), then every primary ideal is maximal.

Proof: let `𝔮` be primary and `𝔪 ⊇ 𝔮` maximal.  For `x ∈ 𝔪` choose `b` with
`x = x ^ 2 * b`; then `x * (1 - x * b) = 0 ∈ 𝔮`.  If `x ∉ 𝔮`, primarity gives
`(1 - x * b) ^ n ∈ 𝔮 ⊆ 𝔪`, so `1 - x * b ∈ 𝔪` as `𝔪` is prime; but `x * b ∈ 𝔪`,
hence `1 ∈ 𝔪`, contradiction.  Thus `𝔪 ≤ 𝔮`, i.e. `𝔮 = 𝔪` is maximal. -/
theorem isMaximal_of_isPrimary_of_forall_eq_mul_sq {A : Type u} [CommRing A]
    (h : ∀ a : A, ∃ b, a = a ^ 2 * b) (q : Ideal A) (hq : q.IsPrimary) : q.IsMaximal := by
  obtain ⟨hne, hmem⟩ := Ideal.isPrimary_iff.mp hq
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hne
  have hmq : m ≤ q := by
    intro x hx
    obtain ⟨b, hb⟩ := h x
    by_contra hxq
    have hx0 : x * (1 - x * b) = 0 := by
      calc x * (1 - x * b) = x - x ^ 2 * b := by ring
        _ = 0 := by rw [← hb, sub_self]
    have hx0q : x * (1 - x * b) ∈ q := by rw [hx0]; exact q.zero_mem
    have hrad : (1 - x * b) ∈ q.radical := (hmem hx0q).resolve_left hxq
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    have hnotm : (1 - x * b) ∉ m := by
      intro hcon
      have h1 : (1 : A) ∈ m := by
        have := add_mem hcon (m.mul_mem_right b hx)
        simpa using this
      exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h1)
    exact hnotm (hm.isPrime.mem_of_pow_mem n (hqm hn))
  have hqm' : q = m := le_antisymm hqm hmq
  rw [hqm']
  exact hm

/-- **Atiyah–Macdonald, Exercise 4.3.**  If `A` is an absolutely flat ring, every
primary ideal of `A` is maximal. -/
theorem solution {A : Type u} [CommRing A] (hA : AbsolutelyFlat A)
    (q : Ideal A) (hq : q.IsPrimary) : q.IsMaximal :=
  isMaximal_of_isPrimary_of_forall_eq_mul_sq (exists_eq_mul_sq_of_absolutelyFlat hA) q hq

/-- Consequence: in an absolutely flat ring every prime ideal is maximal, since a prime
ideal is primary.  (This is one half of Chapter 3, Exercise 11: a homomorphic image of an
absolutely flat ring is absolutely flat — Chapter 2, Exercise 28 — so `A ⧸ 𝔑` is
absolutely flat, which is equivalent to every prime ideal of `A` being maximal.) -/
theorem isMaximal_of_isPrime_of_absolutelyFlat {A : Type u} [CommRing A]
    (hA : AbsolutelyFlat A) (p : Ideal A) (hp : p.IsPrime) : p.IsMaximal :=
  solution hA p hp.isPrimary

/-- Consequence: if the zero ideal of an absolutely flat ring is primary, then the
ring is a field.  (This is the case treated in the solution given in `amcd.tex`.) -/
theorem isField_of_isPrimary_bot_of_absolutelyFlat {A : Type u} [CommRing A] [Nontrivial A]
    (hA : AbsolutelyFlat A) (h : (⊥ : Ideal A).IsPrimary) : IsField A :=
  (Ring.isField_iff_maximal_bot (R := A)).mpr (solution hA ⊥ h)

/-- Sanity check on the hypothesis: a field is absolutely flat (every module over a field
is free, hence flat), so `solution` is not vacuous. -/
theorem absolutelyFlat_of_field (K : Type u) [Field K] : AbsolutelyFlat K :=
  fun _ _ _ => Module.Flat.of_free

/-- The conclusion of `solution`, instantiated at a field. -/
example (K : Type u) [Field K] (q : Ideal K) (hq : q.IsPrimary) : q.IsMaximal :=
  solution (absolutelyFlat_of_field K) q hq

end AtiyahMcdonald69.Ex_4_3

#print axioms AtiyahMcdonald69.Ex_4_3.exists_eq_mul_sq_of_absolutelyFlat
#print axioms AtiyahMcdonald69.Ex_4_3.isMaximal_of_isPrimary_of_forall_eq_mul_sq
#print axioms AtiyahMcdonald69.Ex_4_3.solution
#print axioms AtiyahMcdonald69.Ex_4_3.isMaximal_of_isPrime_of_absolutelyFlat
#print axioms AtiyahMcdonald69.Ex_4_3.isField_of_isPrimary_bot_of_absolutelyFlat
