/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley 1969.
Chapter 10 (Completions), Exercise 7.  Standalone Lean 4/Mathlib formalisation.

## The exercise (book statement)

Atiyah–Macdonald, Chapter 10 (Completions), Exercise 7, verbatim:

  "Let `A` be a Noetherian ring, `𝔞` an ideal of `A`, and `Â` the `𝔞`-adic completion. Prove that
  `Â` is faithfully flat over `A` (Chapter 3, Exercise 16) if and only if `A` is a Zariski ring
  (for the `𝔞`-topology)."

The notions are the book's own:

* A *Zariski ring* is defined in Exercise 6 of the same chapter: "a Noetherian topological ring
  in which the topology is defined by an ideal contained in the Jacobson radical".  For `A`
  carrying the `𝔞`-adic topology this says that `𝔞` lies in the Jacobson radical (the
  intersection of all maximal ideals): indeed, if some ideal `𝔟` defining the same topology as
  `𝔞` lies in the Jacobson radical `J`, then `𝔞 ⊆ √𝔟 ⊆ J` because `J` is an intersection of
  maximal ideals and hence radical; conversely `𝔟 := 𝔞` works.  So the conclusion below is
  stated as `I ≤ (⊥ : Ideal A).jacobson`.
* Chapter 3, Exercise 16 characterises a faithfully flat `A`-algebra `B` among flat `A`-algebras
  by the equivalent conditions (i) `𝔞^{ec} = 𝔞` for all ideals, (ii) `Spec B → Spec A`
  surjective, (iii) `𝔪^e ≠ (1)` for every maximal ideal `𝔪` of `A`, (iv) `M^e ≠ 0` for every
  nonzero `A`-module `M`, (v) `M → M^e` injective.  Mathlib's `Module.FaithfullyFlat A M` is
  literally flatness together with (iii) (`𝔪 • ⊤ ≠ ⊤` for every maximal ideal `𝔪`), and Mathlib
  proves it equivalent to (iv) and (v) (`Module.FaithfullyFlat.rTensor_reflects_triviality`,
  `...iff_flat_and_lTensor_faithful`).

The exercise is a single equivalence, so the deliverable is the single theorem `solution` below
(no `part_a`/`part_b` split; the two implications are proved inside it).  The source repository
quoted below stores solutions but not statements, so the statement was taken from a public full
text of the 1969 edition; the exercise numbering there is the one the source repository's tags
`10.1 … 10.12` follow (Chapter 10 has 12 exercises).

## Coverage of the original statement

* Quantifiers and hypotheses are preserved: `A` is an arbitrary commutative ring assumed
  `IsNoetherianRing` (Noetherian, as in the book), `I` is an arbitrary ideal, and the
  conclusion is stated for the actual `𝔞`-adic completion `AdicCompletion I A`.
* "Faithfully flat `A`-algebra" is Mathlib's `Module.FaithfullyFlat A (AdicCompletion I A)`,
  i.e. flat together with `𝔪 • ⊤ ≠ ⊤` for every maximal ideal `𝔪` of `A`, which is condition
  (iii) of Chapter 3, Exercise 16 of the book.
* "`𝔞` is contained in the Jacobson radical" is `I ≤ (⊥ : Ideal A).jacobson`, and
  `Ideal.jacobson_bot` identifies `(⊥ : Ideal A).jacobson` with `Ring.jacobson A`.  The lemma
  `le_jacobson_iff_forall_le_maximal` below records that this is literally "`𝔞 ⊆ 𝔪` for every
  maximal ideal `𝔪`", i.e. that `A` is a Zariski ring for the `𝔞`-topology.

Nothing is postulated: there is no `sorry`, no extra axiom, no hypothesis beyond Noetherianness.

## Source proof (guidance, not trusted)

`https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-10-7`
(public repository `j346huan/DoYourExercise`, commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91,
file `content/AtiyahMcdonald69/AtiyahMcdonald69-10-7/proof.tex`).  It argues: `Â` is flat by
Proposition 10.14, faithful flatness amounts to `Â/𝔪Â ≠ 0` for all maximal `𝔪`, and by
Proposition 10.13 `Â/𝔪Â` is the `𝔞`-adic completion of `A/𝔪`, which is `A/𝔪` when `𝔞 ⊆ 𝔪` and
`0` otherwise.  This is essentially the book's hint (flatness of `Â` plus condition (iii) of
Chapter 3, Exercise 16).  Flatness of the completion is available in Mathlib
(`AdicCompletion.flat_of_isNoetherian`, itself proved via exactness of completion on finite
modules over a Noetherian ring, i.e. Artin–Rees).  We do *not* use the 10.13 reduction: both
implications are proved directly from the two facts that the ideal `𝔞Â` lies in the Jacobson
radical of the complete ring `Â` (`IsAdicComplete.le_jacobson_bot`) and that `𝔪Â` is a maximal
ideal of `Â` whenever `𝔪 ⊇ 𝔞` is maximal (`AdicCompletion.isMaximal_map_of_le`).  This is a
genuinely different (and shorter) route than the source proof.

* (⟸) For a maximal `𝔪 ⊇ 𝔞`, `𝔪 ↦ 𝔪Â` is a maximal ideal of `Â`
  (`AdicCompletion.isMaximal_map_of_le`), in particular not the unit ideal.
* (⟹) If `𝔪` is maximal with `𝔞 ⊄ 𝔪` then `𝔞 + 𝔪 = A`; writing `1 = i + j` with `i ∈ 𝔞`,
  `j ∈ 𝔪` and applying `algebraMap A Â`, the element `algebraMap j = 1 - algebraMap i` is a unit
  because `algebraMap i ∈ 𝔞Â ⊆ Jac(Â)` (here completeness of `Â` gives the Jacobson-radical
  statement).  Hence `𝔪Â = Â`, contradicting faithful flatness.

## Statement adaptations

Only notation is adapted: Mathlib's `AdicCompletion I A` (a subring of `∏ n, A ⧸ I^n`) for the
`𝔞`-adic completion, `Module.FaithfullyFlat` for faithful flatness, `Ideal.jacobson ⊥` for the
Jacobson radical.  No hypothesis is weakened and no conclusion is moved into the assumptions.

## Checking

Verified with `lean -DwarningAsError=true answer.lean` against the installed Mathlib
(`/opt/lean/bin/lean`, Lean 4.33.1 — the toolchain matching the prebuilt Mathlib oleans in this
VM; the elan default on `PATH` is 4.35.0 and cannot read those oleans).  `#print axioms` on
every declaration below reports only `propext`, `Classical.choice` and `Quot.sound`.
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

namespace AtiyahMcdonald69.Ex_10_7

open Ideal
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A]

/-- The Jacobson radical `⊥.jacobson` is the intersection of the maximal ideals, so
`I ≤ ⊥.jacobson` is exactly the book's condition "`I` is contained in every maximal ideal". -/
theorem le_jacobson_iff_forall_le_maximal {R : Type*} [CommRing R] (I : Ideal R) :
    I ≤ (⊥ : Ideal R).jacobson ↔ ∀ m : Ideal R, m.IsMaximal → I ≤ m := by
  constructor
  · intro h m hm
    exact h.trans (sInf_le ⟨bot_le, hm⟩)
  · intro h
    exact le_sInf fun J hJ => h J hJ.2

variable [IsNoetherianRing A]

/-- Key lemma for the easy implication: if `𝔪` is a maximal ideal with `𝔞 ⊔ 𝔪 = ⊤`, then `𝔪`
generates the unit ideal in the `𝔞`-adic completion `Â`.  Indeed in `Â` we have
`1 = algebraMap i + algebraMap j` with `i ∈ 𝔞`, `j ∈ 𝔪`, and `algebraMap i` lies in the
Jacobson radical of the complete ring `Â`, so `algebraMap j` is a unit. -/
theorem map_eq_top_of_sup_eq_top (I m : Ideal A) (h : I ⊔ m = ⊤) :
    m.map (algebraMap A (AdicCompletion I A)) = ⊤ := by
  have hcomp : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  obtain ⟨i, hi, j, hj, hij⟩ :
      ∃ i ∈ I, ∃ j ∈ m, i + j = 1 :=
    Submodule.mem_sup.mp (show (1 : A) ∈ I ⊔ m from h ▸ Submodule.mem_top)
  -- `algebraMap i` lies in the Jacobson radical of the complete ring `Â`
  have hmem : algebraMap A (AdicCompletion I A) i ∈ (⊥ : Ideal (AdicCompletion I A)).jacobson :=
    @IsAdicComplete.le_jacobson_bot (AdicCompletion I A) _
      (I.map (algebraMap A (AdicCompletion I A))) hcomp
      (algebraMap A (AdicCompletion I A) i)
      (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) hi)
  have hsum : algebraMap A (AdicCompletion I A) i + algebraMap A (AdicCompletion I A) j = 1 := by
    rw [← map_add, hij, map_one]
  have hunit : IsUnit (algebraMap A (AdicCompletion I A) j) := by
    have h2 : IsUnit (1 - algebraMap A (AdicCompletion I A) i) := by
      have h3 := (Ideal.mem_jacobson_bot.mp hmem) (-1)
      have h4 : algebraMap A (AdicCompletion I A) i * -1 + 1 =
          1 - algebraMap A (AdicCompletion I A) i := by
        ring
      rwa [h4] at h3
    have heq : (1 : AdicCompletion I A) - algebraMap A (AdicCompletion I A) i =
        algebraMap A (AdicCompletion I A) j := by
      rw [sub_eq_iff_eq_add, add_comm, ← hsum]
    rwa [heq] at h2
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) hj) hunit

/-- **Atiyah–Macdonald, Exercise 10.7.**  For a Noetherian ring `A` and an ideal `I`, the
`I`-adic completion `AdicCompletion I A` is faithfully flat over `A` if and only if `A` is a
Zariski ring for the `I`-adic topology, i.e. if and only if `I` is contained in the Jacobson
radical of `A`. -/
theorem solution (I : Ideal A) :
    Module.FaithfullyFlat A (AdicCompletion I A) ↔ I ≤ (⊥ : Ideal A).jacobson := by
  constructor
  · -- (⟹) a maximal ideal not containing `I` becomes the unit ideal after completion
    intro hff
    rw [le_jacobson_iff_forall_le_maximal]
    intro m hm
    by_contra hle
    have hsup : I ⊔ m = ⊤ := by
      by_contra hne
      have heq : m = I ⊔ m := hm.eq_of_le hne le_sup_right
      exact hle (heq.symm ▸ le_sup_left)
    refine hff.submodule_ne_top hm ?_
    rw [Ideal.smul_top_eq_map, map_eq_top_of_sup_eq_top I m hsup]
    simp
  · -- (⟸) flatness, plus `𝔪Â` maximal (hence proper) for every maximal `𝔪 ⊇ I`
    intro hI
    rw [Module.faithfullyFlat_iff]
    refine ⟨AdicCompletion.flat_of_isNoetherian I, ?_⟩
    intro m hm
    have hle : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
    have hmax : (m.map (algebraMap A (AdicCompletion I A))).IsMaximal :=
      AdicCompletion.isMaximal_map_of_le I m hle I.fg_of_isNoetherianRing
    rw [Ideal.smul_top_eq_map]
    intro htop
    refine hmax.ne_top ?_
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : AdicCompletion I A) ∈
        Submodule.restrictScalars A (Ideal.map (algebraMap A (AdicCompletion I A)) m) := by
      rw [htop]
      exact Submodule.mem_top
    simpa using h1

/-- The same statement with the Jacobson radical written as `Ring.jacobson A`, the intersection
of all maximal ideals of `A`. -/
theorem solution_ringJacobson (I : Ideal A) :
    Module.FaithfullyFlat A (AdicCompletion I A) ↔ I ≤ Ring.jacobson A := by
  rw [solution I, Ideal.jacobson_bot]

/-- The same statement in the book's wording: `𝔞` is contained in every maximal ideal of `A`. -/
theorem solution_forall_maximal (I : Ideal A) :
    Module.FaithfullyFlat A (AdicCompletion I A) ↔
      ∀ m : Ideal A, m.IsMaximal → I ≤ m := by
  rw [solution I, le_jacobson_iff_forall_le_maximal I]

/-- Faithful flatness of the completion in the tensor formulation used in the book: `Â` is flat
and tensoring with it reflects triviality of a module (equivalently, it does not kill a nonzero
module). -/
theorem solution_tensor (I : Ideal A) :
    (Module.Flat A (AdicCompletion I A) ∧
      ∀ (N : Type u) [AddCommGroup N] [Module A N],
        Subsingleton (N ⊗[A] AdicCompletion I A) → Subsingleton N) ↔
      I ≤ (⊥ : Ideal A).jacobson := by
  rw [← Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality A (AdicCompletion I A)]
  exact solution I

end AtiyahMcdonald69.Ex_10_7

#print axioms AtiyahMcdonald69.Ex_10_7.map_eq_top_of_sup_eq_top
#print axioms AtiyahMcdonald69.Ex_10_7.solution
#print axioms AtiyahMcdonald69.Ex_10_7.solution_ringJacobson
#print axioms AtiyahMcdonald69.Ex_10_7.solution_forall_maximal
#print axioms AtiyahMcdonald69.Ex_10_7.solution_tensor
