/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 7.12

Statement (Chapter VII, Exercise 12, alongside `AtiyahMcdonald69,3.16`):

> Let `A` be a ring and `B` a faithfully flat `A`-algebra. If `B` is Noetherian, show that `A`
> is Noetherian.

Reference: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-12>

## Proof (the book's argument)

Let `𝔞₁ ⊆ 𝔞₂ ⊆ ⋯` be an ascending chain of ideals of `A`. Extension of ideals is order
preserving, so `𝔞₁B ⊆ 𝔞₂B ⊆ ⋯` is an ascending chain of ideals of `B`. Since `B` is Noetherian
this chain is eventually constant: `𝔞ₙB = 𝔞_NB` for all `n ≥ N`. Faithful flatness of `B` over `A`
gives `𝔞ᵢ = 𝔞ᵢB ∩ A` (Exercise 3.16: contraction of the extension of an ideal is the ideal
itself), hence `𝔞ₙ = (𝔞ₙB) ∩ A = (𝔞_NB) ∩ A = 𝔞_N` for all `n ≥ N`. Thus every ascending chain
of ideals of `A` stabilizes, i.e. `A` is Noetherian.

## Formalization notes

* `Module.FaithfullyFlat A B` is Mathlib's notion of a faithfully flat `A`-algebra `B`
  (flat, and `N ⊗[A] B` is nontrivial for every nontrivial `A`-module `N`), which is the
  hypothesis of the exercise.
* `Ideal.comap_map_eq_self_of_faithfullyFlat` is Exercise 3.16 in the form used by the book;
  `Ideal.map_injective_of_faithfullyFlat` is the resulting injectivity of `𝔞 ↦ 𝔞B`.
* `monotone_stabilizes_iff_noetherian` is the ascending chain condition for `IsNoetherian`.
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Noetherian.Defs

namespace AtiyahMcdonald69.Ex_7_12

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Atiyah–Macdonald, Exercise 3.16, as used in the proof of Exercise 7.12: for a faithfully flat
`A`-algebra `B`, the contraction of the extension `𝔞B` of an ideal `𝔞` of `A` is `𝔞` itself,
i.e. `𝔞B ∩ A = 𝔞`. -/
theorem comap_map_eq_self [Module.FaithfullyFlat A B] (I : Ideal A) :
    Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) I) = I :=
  Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The chain-theoretic core of the exercise: for a faithfully flat `A`-algebra `B`, an ascending
chain of ideals of `A` whose extension to `B` stabilizes is itself stable. (This is the step of
the book's proof that contracts `𝔞ₙB = 𝔞_NB` back along `B ∩ −`.) -/
theorem exists_stable_of_map_stable [Module.FaithfullyFlat A B] (a : ℕ →o Ideal A)
    (h : ∃ N, ∀ n, N ≤ n → Ideal.map (algebraMap A B) (a N) = Ideal.map (algebraMap A B) (a n)) :
    ∃ N, ∀ n, N ≤ n → a N = a n := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn ↦ Ideal.map_injective_of_faithfullyFlat (hN n hn)⟩

/-- **Atiyah–Macdonald, Exercise 7.12.** If `B` is a faithfully flat `A`-algebra and `B` is a
Noetherian ring, then `A` is a Noetherian ring. -/
theorem solution [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  -- It suffices to show that every ascending chain of ideals of `A` stabilizes.
  refine monotone_stabilizes_iff_noetherian.mp fun a ↦ ?_
  -- Extend the chain to `B`, where it stabilizes because `B` is Noetherian.
  have hchain : ∃ N, ∀ n, N ≤ n →
      Ideal.map (algebraMap A B) (a N) = Ideal.map (algebraMap A B) (a n) := by
    let b : ℕ →o Ideal B :=
      ⟨fun k => Ideal.map (algebraMap A B) (a k), fun i j hij => Ideal.map_mono (a.monotone hij)⟩
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian B B) b
    exact ⟨N, fun n hn => hN n hn⟩
  -- Faithful flatness lets the stabilization descend back to `A`.
  exact exists_stable_of_map_stable a hchain

set_option linter.style.haveILetI false in
/-- Variant of Exercise 7.12 phrased for a faithfully flat ring homomorphism `A →+* B` (Mathlib's
`RingHom.FaithfullyFlat` is definitionally faithful flatness of `B` as an `A`-algebra). -/
theorem solution_ringHom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.FaithfullyFlat) [IsNoetherianRing B] : IsNoetherianRing A := by
  letI : Algebra A B := f.toAlgebra
  exact @solution A B _ _ _ hf _

/-- Sanity check that the hypotheses are satisfiable (so the theorem is not vacuous): the
identity algebra is faithfully flat, and every ascending chain in a Noetherian ring stabilizes. -/
example (A : Type u) [CommRing A] [IsNoetherianRing A] : IsNoetherianRing A :=
  solution (A := A) (B := A)

/-- The hypotheses are jointly satisfiable in a non-trivial instance: `k[X]` is a faithfully flat
`k`-algebra for a field `k`, so the theorem derives `IsNoetherianRing k` from
`IsNoetherianRing k[X]`. -/
example (k : Type u) [Field k] : IsNoetherianRing k :=
  solution (A := k) (B := Polynomial k)

end AtiyahMcdonald69.Ex_7_12

#print axioms AtiyahMcdonald69.Ex_7_12.comap_map_eq_self
#print axioms AtiyahMcdonald69.Ex_7_12.exists_stable_of_map_stable
#print axioms AtiyahMcdonald69.Ex_7_12.solution
#print axioms AtiyahMcdonald69.Ex_7_12.solution_ringHom
