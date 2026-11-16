/-
# Atiyah–Macdonald (1969), Exercise 9.9 — the Chinese remainder theorem in a Dedekind domain

## The exercise

*M. F. Atiyah and I. G. Macdonald, Introduction to Commutative Algebra, Addison–Wesley 1969,
Chapter 9 (Discrete Valuation Rings and Dedekind Domains), Exercise 9.9 (Chinese Remainder Theorem):*

> Let `𝔞₁, …, 𝔞ₙ` be ideals and let `x₁, …, xₙ` be elements in a Dedekind domain `A`. Then the system
> of congruences `x ≡ xᵢ mod 𝔞ᵢ` (1 ≤ i ≤ n) has a solution `x ∈ A` if and only if
> `xᵢ ≡ xⱼ mod (𝔞ᵢ + 𝔞ⱼ)` whenever `i ≠ j`.

## Coverage

`solution` is the full statement, both directions, for an arbitrary **finite** index type `ι`
(specialising to `{1, …, n}`; `solution_fin` restates it with the textbook indexing `Fin n`).
The ideals `𝔞ᵢ` are arbitrary ideals of `A` — no properness, nonzeroness or coprimality is assumed —
and `IsDedekindDomain A` is Mathlib's Noetherian integrally closed domain of Krull dimension ≤ 1,
which is exactly Atiyah–Macdonald's notion. No `sorry`, no additional axioms, no extra hypotheses.

## Mathematical approach

The necessity direction is formalised in any commutative ring. For sufficiency we follow the
source proof, which is an induction on the number of congruences and rests on Exercise 9.8:

* `sup_inf_eq` : `𝔞 ⊔ (𝔟 ⊓ 𝔠) = (𝔞 ⊔ 𝔟) ⊓ (𝔞 ⊔ 𝔠)` in a Dedekind domain. This distributivity of
  the ideal lattice is proved by localising at every maximal ideal `𝔪`: `A_𝔪` is a discrete
  valuation ring, so `Ideal (A_𝔪)` is a chain (Mathlib: `ValuationRing` ⟹ `Std.Total` on ideals) and
  distributivity is a case split; `IsLocalization.map_inf`/`Ideal.map_sup` transport the identity,
  and `mem_of_mem_map_maximal` reflects it back to `A` (if `t ∉ I`, the colon ideal `(I : t)` is
  proper, so it lies in a maximal ideal `𝔪`, and `t ∉ I_𝔪`).
* `iInf_sup` : the finitary form `(⨅ i ∈ s, 𝔞ᵢ) ⊔ 𝔟 = ⨅ i ∈ s, (𝔞ᵢ ⊔ 𝔟)`.
* `crt_pair` : the two-ideal case `x₁ - x₂ ∈ 𝔞 + 𝔟 ⟹ ∃ x, x - x₁ ∈ 𝔞 ∧ x - x₂ ∈ 𝔟`, valid in any ring.
* `exists_solution_of_compat` : induction over a finite set of congruences — solve the first `n - 1`,
  use the compatibility hypothesis and `iInf_sup` to see `xₙ - y ∈ (⨅_{i<n} 𝔞ᵢ) + 𝔞ₙ`, then apply the
  two-ideal case to the pair `(⨅_{i<n} 𝔞ᵢ, 𝔞ₙ)`.

## Sources

Natural-language solution (source material for this task):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-9-9
(public `j346huan/DoYourExercise` repository, commit 80e1ebef1d7621c66aabb3920d981ffd8995ba91,
`content/AtiyahMcdonald69/AtiyahMcdonald69-9-9/proof.tex`).
The exercise text above was cross-checked against an independent copy of the book's exercise list
(Y. Yao, MATH 831 Assignment 10, Georgia State University, Exercise 9.9).

## Scope adaptations

None in content. The only generalisation is the indexing: the textbook's finite sequence
`𝔞₁, …, 𝔞ₙ` is replaced by an arbitrary `Fintype ι` (the case `ι = Fin 0`, which is vacuous, is
included); `solution_fin` records the literal `Fin n` version.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_9_9

section AnyRing

variable {A : Type*} [CommRing A]

/-- The two-ideal case of the Chinese remainder theorem, valid in any commutative ring:
if `x₁ - x₂ ∈ 𝔞 + 𝔟`, then `x₁` can be corrected by an element of `𝔞` to land in `x₂ + 𝔟`. -/
theorem crt_pair {a b : Ideal A} {x₁ x₂ : A} (h : x₁ - x₂ ∈ a + b) :
    ∃ y : A, y - x₁ ∈ a ∧ y - x₂ ∈ b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
  refine ⟨x₁ - u, ?_, ?_⟩
  · simpa using a.neg_mem hu
  · have h2 : x₁ - u - x₂ = (x₁ - x₂) - u := by ring
    rw [h2, ← huv, add_sub_cancel_left]
    exact hv

/-- The colon ideal `(I : (t)) = {s | s * t ∈ I}`, the annihilator of `t` in `A ⧸ I`. -/
def colonSpan (I : Ideal A) (t : A) : Ideal A where
  carrier := {s : A | s * t ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) * t ∈ I
    rw [add_mul]
    exact I.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change (c * x) * t ∈ I
    rw [mul_assoc]
    exact I.mul_mem_left c hx

-- `haveI` below is not cosmetic: the maximality of the ideal obtained from
-- `Ideal.exists_le_maximal` has to be registered as a typeclass instance (it is needed for
-- `Localization.AtPrime` and `Ideal.primeCompl`), which `have` cannot do.
set_option linter.style.haveILetI false in
/-- Ideals are local at maximal ideals: if `t` belongs to `I` after localising at every maximal
ideal, then `t ∈ I`. (Standard local–global principle, proved through the colon ideal `(I : t)`.) -/
theorem mem_of_mem_map_maximal {I : Ideal A} {t : A}
    (h : ∀ (m : Ideal A) [m.IsMaximal],
      algebraMap A (Localization.AtPrime m) t ∈
        Ideal.map (algebraMap A (Localization.AtPrime m)) I) :
    t ∈ I := by
  by_contra ht
  have hJ : colonSpan I t ≠ ⊤ := by
    intro htop
    refine ht ?_
    have h1 : (1 : A) ∈ colonSpan I t := by rw [htop]; exact Submodule.mem_top
    simpa [colonSpan] using h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (colonSpan I t) hJ
  haveI := hm
  obtain ⟨s, hs, hst⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff m.primeCompl
      (Localization.AtPrime m) I t).mp (h m)
  exact hs (hle hst)

/-- In a lattice whose order is total, `⊔` distributes over `⊓`. -/
theorem sup_inf_distrib_of_total {α : Type*} [Lattice α] (h : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (a b c : α) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rcases h b c with hbc | hcb
  · have h1 : b ⊓ c = b := inf_eq_left.mpr hbc
    have h2 : a ⊔ b ≤ a ⊔ c := sup_le le_sup_left (le_trans hbc le_sup_right)
    rw [h1, inf_eq_left.mpr h2]
  · have h1 : b ⊓ c = c := inf_eq_right.mpr hcb
    have h2 : a ⊔ c ≤ a ⊔ b := sup_le le_sup_left (le_trans hcb le_sup_right)
    rw [h1, inf_eq_right.mpr h2]

/-- In a field every ideal is `⊥` or `⊤`, so the ideal lattice is a chain and hence distributive. -/
theorem sup_inf_eq_of_isField (hF : IsField A) (a b c : Ideal A) :
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  let : Field A := hF.toField
  have htot : ∀ I J : Ideal A, I ≤ J ∨ J ≤ I := by
    intro I J
    rcases Ideal.eq_bot_or_top I with rfl | rfl
    · exact Or.inl bot_le
    · exact Or.inr le_top
  exact sup_inf_distrib_of_total htot a b c

end AnyRing

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

/-- **Local distributivity.** In the localisation of a Dedekind domain at a maximal ideal (a discrete
valuation ring) the ideal lattice is a chain, hence distributive; localisation of ideals preserves
`⊔` and `⊓`. -/
theorem map_sup_inf (a b c : Ideal A) (m : Ideal A) [m.IsMaximal] :
    Ideal.map (algebraMap A (Localization.AtPrime m)) (a ⊔ (b ⊓ c)) =
      Ideal.map (algebraMap A (Localization.AtPrime m)) ((a ⊔ b) ⊓ (a ⊔ c)) := by
  simp only [Ideal.map_sup, IsLocalization.map_inf m.primeCompl (Localization.AtPrime m)]
  exact sup_inf_distrib_of_total (fun I J => Std.Total.total I J) _ _ _

/-- **Distributivity of the ideal lattice of a Dedekind domain** (Atiyah–Macdonald Exercise 9.8):
the sum of an ideal with an intersection is the intersection of the sums. This is the key
ingredient of the induction in Exercise 9.9. -/
theorem sup_inf_eq (a b c : Ideal A) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  by_cases hF : IsField A
  · exact sup_inf_eq_of_isField hF a b c
  · refine le_antisymm
      (sup_le (le_inf le_sup_left le_sup_left)
        (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right))) ?_
    intro t ht
    refine mem_of_mem_map_maximal (I := a ⊔ (b ⊓ c)) (fun m hm => ?_)
    rw [map_sup_inf (a := a) (b := b) (c := c) m]
    exact Ideal.mem_map_of_mem _ ht

section FinsetForm

variable {ι : Type*}

/-- Finitary form of distributivity: an ideal distributes over a finite intersection. -/
theorem iInf_sup (a : ι → Ideal A) (b : Ideal A) (s : Finset ι) :
    (⨅ i ∈ s, a i) ⊔ b = ⨅ i ∈ s, (a i ⊔ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.iInf_insert, Finset.iInf_insert, ← ih]
    calc (a k ⊓ ⨅ i ∈ s, a i) ⊔ b = b ⊔ (a k ⊓ ⨅ i ∈ s, a i) := sup_comm ..
      _ = (b ⊔ a k) ⊓ (b ⊔ ⨅ i ∈ s, a i) := sup_inf_eq b (a k) _
      _ = (a k ⊔ b) ⊓ ((⨅ i ∈ s, a i) ⊔ b) := by
        rw [sup_comm b (a k), sup_comm b (⨅ i ∈ s, a i)]

/-- **Induction step of Exercise 9.9.** A finite system of congruences in a Dedekind domain that is
compatible on all pairs has a solution. -/
theorem exists_solution_of_compat (a : ι → Ideal A) (x : ι → A) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i - x j ∈ a i + a j) :
    ∃ y : A, ∀ i ∈ s, y - x i ∈ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert k s hk ih =>
    have h' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i - x j ∈ a i + a j :=
      fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    obtain ⟨y, hy⟩ := ih h'
    -- `y` solves the congruences in `s`; correct it by an element of `⨅ i ∈ s, a i` to solve `a k`.
    have hmem : y - x k ∈ (⨅ i ∈ s, a i) ⊔ a k := by
      have hneg : x k - y ∈ (⨅ i ∈ s, a i) ⊔ a k := by
        rw [iInf_sup a (a k) s]
        simp only [Submodule.mem_iInf]
        intro i hi
        have hki : x k - x i ∈ a k + a i :=
          h k (Finset.mem_insert_self k s) i (Finset.mem_insert_of_mem hi)
            (fun hki => hk (hki ▸ hi))
        have hiy : x i - y ∈ a i := by
          simpa using Submodule.neg_mem (a i) (hy i hi)
        have hsum : x k - y = (x k - x i) + (x i - y) := by ring
        rw [hsum]
        have h1 : x k - x i ∈ a i ⊔ a k := by
          rw [← Ideal.add_eq_sup, add_comm]
          exact hki
        exact add_mem h1 (Submodule.mem_sup_left hiy)
      simpa using Submodule.neg_mem _ hneg
    obtain ⟨y', hy', hy'k⟩ := crt_pair hmem
    refine ⟨y', ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hik | hi
    · rw [hik]; exact hy'k
    · have hle : y' - y ∈ a i :=
        (iInf_le (f := fun _ : i ∈ s => a i) hi)
          ((iInf_le (f := fun i => ⨅ (_ : i ∈ s), a i) i) hy')
      have h2 : y' - x i = (y' - y) + (y - x i) := by ring
      rw [h2]
      exact add_mem hle (hy i hi)

end FinsetForm

section Main

variable {ι : Type*}

/-- **Atiyah–Macdonald (1969), Exercise 9.9 — Chinese remainder theorem in a Dedekind domain.**

Let `A` be a Dedekind domain, let `a i` be ideals of `A` indexed by a finite type `ι`, and let
`x i ∈ A`. Then the system of congruences `y ≡ x i mod a i` (`i : ι`) has a solution `y ∈ A` if and
only if `x i ≡ x j mod (a i + a j)` for all `i ≠ j`. -/
theorem solution [Fintype ι] (a : ι → Ideal A) (x : ι → A) :
    (∃ y : A, ∀ i, y - x i ∈ a i) ↔ ∀ i j : ι, i ≠ j → x i - x j ∈ a i + a j := by
  classical
  constructor
  · -- Necessity: `xᵢ - xⱼ = (x - xⱼ) - (x - xᵢ) ∈ 𝔞ᵢ + 𝔞ⱼ`.
    rintro ⟨y, hy⟩ i j _
    have h1 : y - x i ∈ a i ⊔ a j := Submodule.mem_sup_left (hy i)
    have h2 : y - x j ∈ a i ⊔ a j := Submodule.mem_sup_right (hy j)
    have hd : (y - x j) - (y - x i) ∈ a i ⊔ a j := sub_mem h2 h1
    have he : x i - x j = (y - x j) - (y - x i) := by ring
    rw [he, Ideal.add_eq_sup]
    exact hd
  · -- Sufficiency: the induction of `exists_solution_of_compat`.
    intro h
    obtain ⟨y, hy⟩ := exists_solution_of_compat a x Finset.univ (by
      intro i _ j _ hij
      exact h i j hij)
    exact ⟨y, fun i => hy i (Finset.mem_univ i)⟩

/-- Atiyah–Macdonald Exercise 9.9 in the textbook indexing by `Fin n`. -/
theorem solution_fin (n : ℕ) (a : Fin n → Ideal A) (x : Fin n → A) :
    (∃ y : A, ∀ i, y - x i ∈ a i) ↔ ∀ i j : Fin n, i ≠ j → x i - x j ∈ a i + a j :=
  solution a x

end Main

end Dedekind

end AtiyahMcdonald69.Ex_9_9

-- Axiom check (the file is expected to use only standard axioms).
#print axioms AtiyahMcdonald69.Ex_9_9.solution
#print axioms AtiyahMcdonald69.Ex_9_9.solution_fin
