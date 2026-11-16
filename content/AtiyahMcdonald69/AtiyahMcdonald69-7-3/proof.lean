/-
Formalization of Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 7 ("Noetherian Rings"), Exercise 3, p. 84.

Natural-language reference (site source: j346huan/DoYourExercise, commit 80e1ebef):
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-3

Statement of the exercise (as printed, see audit note below):

  Let `a` be an irreducible ideal in a ring `A`. Then the following are equivalent:
  (i)  `a` is primary;
  (ii) for every multiplicatively closed subset `S` of `A` we have `(S⁻¹a)^c = (a : s)`
       for some `s ∈ S`;
  (iii) for every `x ∈ A` the sequence `((a : xⁿ))_{n ≥ 0}` is stationary.

Source audit.
  * The public scan `.scratch/reference/atiyah-macdonald-original.txt` in this workspace is
    truncated in the middle of Chapter 6 (it ends inside the proof of Corollary 6.11), so it
    does not contain Chapter 7.  The statement above was taken from the solution notes
    `.scratch/dl/amcd.tex` ("Page 84, Exercise 7.3"), which quote the book verbatim, and was
    cross-checked against `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-7-3/proof.tex`
    and against Papaioannou's solutions (`.scratch/dl/papa.txt`, "7.3").
  * The site's proof is correct as far as (i) ⇒ (ii) and (ii) ⇒ (iii) go; these two
    implications do not use irreducibility of `a` at all (as the book's hint states), and
    this file proves them without that hypothesis.
    For (iii) ⇒ (i) the site's proof uses irreducibility of `0` in `A/a` ("Irreducibility of
    zero and `(y) ≠ 0` give `(xⁿ) = 0`"); this step is essential and is reproduced below
    (as irreducibility of `a` in `A`).
  * Book ambiguity (properness).  The book's notion of irreducible ideal
    (`a = b ∩ c ⇒ a = b or a = c`) does not exclude `a = ⊤`; the book's own Lemma 7.12 has the
    same slip ("every *proper* irreducible ideal is primary"; cf. amcd.tex, p. 83).  For
    `a = ⊤` conditions (ii) and (iii) hold while (i) fails, so the exercise is literally false
    without a properness assumption.  This file therefore states the intended theorem for
    proper irreducible ideals (Mathlib's `InfIrred a`, which is `a ≠ ⊤` together with
    `a = b ⊓ c → a = b ∨ a = c`; `infIrred_iff_irreducible` below records the translation),
    and separately formalizes the counterexample to the literal reading
    (`literal_statement_false`).
  * The irreducibility hypothesis is not redundant for (iii) ⇒ (i): in `ℤ × ℤ` the zero ideal
    satisfies (iii) but is neither primary nor irreducible
    (`condIII_does_not_imply_primary`).  So the step of the site's proof that uses
    irreducibility is genuinely needed, and the two other implications are the only ones that
    generalize to arbitrary ideals.

Verification: `/opt/lean/bin/lean -DwarningAsError=true answer.lean` (Lean 4.33.1, Mathlib
from `/opt/mathlib`) exits 0; `#print axioms` at the end of the file shows that every principal
result depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Order.Irreducible

open Pointwise

namespace AtiyahMcdonald69.Ex_7_3

variable {A : Type*} [CommRing A]

/-! ### The three conditions of the exercise -/

/-- `(S⁻¹a)^c`: the contraction to `A` of the extension of the ideal `a` to `S⁻¹A`. -/
def saturation (S : Submonoid A) (a : Ideal A) : Ideal A :=
  (a.map (algebraMap A (Localization S))).under A

/-- Explicit description of the saturation: `x` lies in `(S⁻¹a)^c` iff `s x ∈ a` for some `s ∈ S`. -/
theorem mem_saturation_iff {S : Submonoid A} {a : Ideal A} {y : A} :
    y ∈ saturation S a ↔ ∃ s ∈ S, s * y ∈ a := by
  rw [saturation, Ideal.mem_under A,
    IsLocalization.algebraMap_mem_map_algebraMap_iff S (Localization S)]


/-- The saturation for the trivial multiplicatively closed subset `{1}` is the ideal itself. -/
theorem saturation_bot (a : Ideal A) : saturation (⊥ : Submonoid A) a = a := by
  ext y
  rw [mem_saturation_iff]
  constructor
  · rintro ⟨s, hs, hsy⟩
    rw [Submonoid.mem_bot] at hs
    rwa [hs, one_mul] at hsy
  · intro hy
    exact ⟨1, by simp, by rwa [one_mul]⟩

/-- If `S` meets `a`, then `(S⁻¹a)^c` is the whole ring. -/
theorem saturation_eq_top_of_mem {S : Submonoid A} {a : Ideal A} {s : A}
    (hs : s ∈ S) (hsa : s ∈ a) : saturation S a = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_saturation_iff]
  exact ⟨s, hs, by rwa [mul_one]⟩

/-- If `s ∈ a` then `(a : s)` is the whole ring. -/
theorem colon_span_singleton_eq_top_of_mem {a : Ideal A} {s : A} (hsa : s ∈ a) :
    a.colon (Ideal.span {s}) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_colon_span_singleton]
  rwa [one_mul]

/-- Condition (ii) of the exercise: for every multiplicatively closed `S ⊆ A` the contraction
`(S⁻¹a)^c` is `(a : s)` for some `s ∈ S`. -/
def CondII (a : Ideal A) : Prop :=
  ∀ S : Submonoid A, ∃ s ∈ S, saturation S a = a.colon (Ideal.span {s})

/-- Condition (iii) of the exercise: for every `x ∈ A` the sequence `(a : xⁿ)` is stationary. -/
def CondIII (a : Ideal A) : Prop :=
  ∀ x : A, ∃ n : ℕ, ∀ m ≥ n, a.colon (Ideal.span {x ^ m}) = a.colon (Ideal.span {x ^ n})

/-! ### (i) ⇒ (ii)

This needs no irreducibility hypothesis (as noted in the book's hint). -/

theorem primary_implies_condII {a : Ideal A} (ha : a.IsPrimary) : CondII a := by
  intro S
  by_cases h : ∃ s ∈ S, s ∈ a
  · -- `S` meets `a`: both `(S⁻¹a)^c` and `(a : s)` are `⊤`.
    obtain ⟨s, hsS, hsa⟩ := h
    exact ⟨s, hsS, by rw [saturation_eq_top_of_mem hsS hsa, colon_span_singleton_eq_top_of_mem hsa]⟩
  · -- `S` misses `a`, hence misses `r(a)` (as `S` is multiplicatively closed), so by the
    -- contraction theorem for primary ideals (the book's Proposition 4.8) `(S⁻¹a)^c = a`,
    -- and `a = (a : 1)`.
    have hmiss : ∀ s ∈ S, s ∉ a := fun s hsS hsa => h ⟨s, hsS, hsa⟩
    have hdisj : Disjoint (S : Set A) (a : Set A) := Set.disjoint_left.2 hmiss
    have hcontr := IsLocalization.under_map_of_isPrimary_disjoint S (Localization S) ha hdisj
    refine ⟨1, S.one_mem, ?_⟩
    rw [saturation, hcontr, Ideal.span_singleton_one]
    simp

/-! ### (ii) ⇒ (iii)

This needs no irreducibility hypothesis either. -/

theorem condII_implies_condIII {a : Ideal A} (h : CondII a) : CondIII a := by
  intro x
  obtain ⟨s, hsS, hsat⟩ := h (Submonoid.powers x)
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff s x).1 hsS
  refine ⟨n, fun m hm => ?_⟩
  refine le_antisymm ?_ ?_
  · -- `(a : xᵐ) ≤ (S⁻¹a)^c = (a : xⁿ)` for `S = {1, x, x², …}`
    intro y hy
    rw [Ideal.mem_colon_span_singleton] at hy ⊢
    have hmem : y ∈ saturation (Submonoid.powers x) a := by
      rw [mem_saturation_iff]
      exact ⟨x ^ m, (Submonoid.mem_powers_iff (x ^ m) x).2 ⟨m, rfl⟩, by rwa [mul_comm]⟩
    rw [hsat] at hmem
    exact Ideal.mem_colon_span_singleton.1 hmem
  · -- `(a : xⁿ) ≤ (a : xᵐ)` for `m ≥ n`
    intro y hy
    rw [Ideal.mem_colon_span_singleton] at hy ⊢
    obtain ⟨c, hc⟩ := pow_dvd_pow x hm
    rw [hc, ← mul_assoc y (x ^ n) c]
    exact Ideal.mul_mem_right c a hy

/-! ### (iii) ⇒ (i)

Here irreducibility of `a` is essential.  This is the argument of Lemma 7.12 of the book
(and of the site's proof), carried out directly in `A`. -/

theorem condIII_implies_primary {a : Ideal A} (hirr : InfIrred a) (h : CondIII a) :
    a.IsPrimary := by
  refine Ideal.isPrimary_iff.2 ⟨hirr.ne_top, ?_⟩
  intro x y hxy
  by_cases hx : x ∈ a
  · exact Or.inl hx
  right
  obtain ⟨n, hn⟩ := h y
  -- Stationarity of `(a : yᵏ)` at `n` and `n+1`.
  have hstep : a.colon (Ideal.span {y ^ (n + 1)}) = a.colon (Ideal.span {y ^ n}) :=
    hn (n + 1) (Nat.le_succ n)
  -- The key claim: `a = (a + (yⁿ)) ∩ (a + (x))`.
  have hkey : (a ⊔ Ideal.span {y ^ n}) ⊓ (a ⊔ Ideal.span {x}) = a := by
    refine le_antisymm ?_ (le_inf (le_sup_left : a ≤ a ⊔ Ideal.span {y ^ n})
      (le_sup_left : a ≤ a ⊔ Ideal.span {x}))
    intro z hz
    obtain ⟨hz1, hz2⟩ : z ∈ a ⊔ Ideal.span {y ^ n} ∧ z ∈ a ⊔ Ideal.span {x} :=
      Ideal.mem_inf.1 hz
    obtain ⟨p, hp, u, hu, hpu⟩ := Submodule.mem_sup.1 hz1
    obtain ⟨q, hq, v, hv, hqv⟩ := Submodule.mem_sup.1 hz2
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hu
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hv
    -- `y * z ∈ a`, because `z = q + c x` and `x * y ∈ a`
    have hyz : y * z ∈ a := by
      have h1 : y * z = y * q + y * (x * c) := by rw [← hqv, mul_add]
      have h2 : y * (x * c) = x * y * c := by ring
      rw [h1, h2]
      exact Ideal.add_mem a (Ideal.mul_mem_left a y hq) (Ideal.mul_mem_right c a hxy)
    -- hence `b yⁿ⁺¹ = y z - y p ∈ a`
    have hyu : y ^ (n + 1) * b ∈ a := by
      have h2 : y * (y ^ n * b) = y * z - y * p := by
        have h3 : y * z = y * p + y * (y ^ n * b) := by rw [← hpu, mul_add]
        rw [h3]
        ring
      have h3 : y * (y ^ n * b) = y ^ (n + 1) * b := by ring
      rw [h3] at h2
      rw [h2]
      exact Ideal.sub_mem a hyz (Ideal.mul_mem_left a y hp)
    -- so `b ∈ (a : yⁿ⁺¹) = (a : yⁿ)`, i.e. `b yⁿ ∈ a`
    have hb : y ^ n * b ∈ a := by
      have h1 : b ∈ a.colon (Ideal.span {y ^ (n + 1)}) := by
        rw [Ideal.mem_colon_span_singleton]
        simpa [mul_comm] using hyu
      rw [hstep] at h1
      have h2 : b * y ^ n ∈ a := Ideal.mem_colon_span_singleton.1 h1
      simpa [mul_comm] using h2
    rw [← hpu]
    exact Ideal.add_mem a hp hb
  rcases hirr.2 hkey with h1 | h2
  · -- `a = a + (yⁿ)`, so `yⁿ ∈ a`
    have hy : y ^ n ∈ a := by
      have hle : Ideal.span {y ^ n} ≤ a := h1 ▸ le_sup_right
      exact (Ideal.span_singleton_le_iff_mem a).1 hle
    exact Ideal.mem_radical_iff.2 ⟨n, hy⟩
  · -- `a = a + (x)` contradicts `x ∉ a`
    have hle : Ideal.span {x} ≤ a := h2 ▸ le_sup_right
    exact absurd ((Ideal.span_singleton_le_iff_mem a).1 hle) hx

/-! ### The exercise -/

/-- Atiyah–Macdonald, Chapter 7, Exercise 3 (p. 84), for a proper irreducible ideal:
conditions (i) and (ii) are equivalent. -/
theorem primary_iff_condII {a : Ideal A} (ha : InfIrred a) : a.IsPrimary ↔ CondII a :=
  ⟨primary_implies_condII, fun h => condIII_implies_primary ha (condII_implies_condIII h)⟩

/-- Atiyah–Macdonald, Chapter 7, Exercise 3 (p. 84), for a proper irreducible ideal:
conditions (i) and (iii) are equivalent. -/
theorem primary_iff_condIII {a : Ideal A} (ha : InfIrred a) : a.IsPrimary ↔ CondIII a :=
  ⟨fun h => condII_implies_condIII (primary_implies_condII h), fun h => condIII_implies_primary ha h⟩

/-- Atiyah–Macdonald, Chapter 7, Exercise 3 (p. 84): for a proper irreducible ideal the three
conditions are equivalent. -/
theorem exercise_7_3 {a : Ideal A} (ha : InfIrred a) :
    (a.IsPrimary ↔ CondII a) ∧ (a.IsPrimary ↔ CondIII a) :=
  ⟨primary_iff_condII ha, primary_iff_condIII ha⟩

/-! ### Irreducibility in the sense of the book -/

/-- `InfIrred a` is exactly the book's notion of an irreducible ideal: `a` is proper and
`a = b ∩ c` forces `a = b` or `a = c`.  (The properness is the part that the book leaves
implicit; see the counterexample below.) -/
theorem infIrred_iff_irreducible {a : Ideal A} :
    InfIrred a ↔ a ≠ ⊤ ∧ ∀ b c : Ideal A, a = b ⊓ c → a = b ∨ a = c := by
  constructor
  · intro h
    refine ⟨h.ne_top, fun b c hbc => ?_⟩
    rcases h.2 hbc.symm with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rintro ⟨hne, h⟩
    refine ⟨?_, fun b c hbc => ?_⟩
    · rwa [isMax_iff_eq_top]
    · rcases h b c hbc.symm with h' | h'
      · exact Or.inl h'.symm
      · exact Or.inr h'.symm

/-- Atiyah–Macdonald, Chapter 7, Exercise 3 (p. 84), stated in the book's own phrasing:
`a` is a proper irreducible ideal (`a = b ∩ c ⇒ a = b or a = c`) and the three conditions are
equivalent.  This is exactly the intended reading of the printed exercise; the properness is
the only hypothesis made explicit. -/
theorem exercise_7_3_book_phrasing {a : Ideal A}
    (hirr : a ≠ ⊤ ∧ ∀ b c : Ideal A, a = b ⊓ c → a = b ∨ a = c) :
    (a.IsPrimary ↔ CondII a) ∧ (a.IsPrimary ↔ CondIII a) :=
  exercise_7_3 (infIrred_iff_irreducible.2 hirr)

/-! ### The literal reading without properness is false

The book's irreducible ideals are not required to be proper, and conditions (ii) and (iii)
hold for `a = ⊤`, whereas (i) does not.  So the properness built into `InfIrred` above is
not an artefact of the formalization: without it the statement of the exercise is false. -/

section LiteralReading

/-- `⊤` satisfies the book's literal irreducibility condition `a = b ∩ c ⇒ a = b or a = c`. -/
theorem top_literally_irreducible :
    ∀ b c : Ideal A, (⊤ : Ideal A) = b ⊓ c → (⊤ : Ideal A) = b ∨ (⊤ : Ideal A) = c := by
  intro b c hbc
  left
  exact (top_le_iff.1 (hbc ▸ (inf_le_left : b ⊓ c ≤ b))).symm

theorem top_condII : CondII (⊤ : Ideal A) := by
  intro S
  exact ⟨1, S.one_mem, by
    rw [saturation_eq_top_of_mem S.one_mem (by simp : (1 : A) ∈ ⊤), Submodule.top_colon]⟩

theorem top_condIII : CondIII (⊤ : Ideal A) := by
  intro x
  exact ⟨0, fun m _ => by simp⟩

theorem top_not_isPrimary : ¬ (⊤ : Ideal A).IsPrimary := by
  rw [Ideal.isPrimary_iff]
  exact fun h => h.1 rfl

/-- The statement of the exercise without the properness assumption is false. -/
theorem literal_statement_false :
    ∃ a : Ideal A, (∀ b c : Ideal A, a = b ⊓ c → a = b ∨ a = c) ∧
      CondII a ∧ CondIII a ∧ ¬ a.IsPrimary :=
  ⟨⊤, top_literally_irreducible, top_condII, top_condIII, top_not_isPrimary⟩

end LiteralReading

/-! ### The irreducibility hypothesis is needed for (iii) ⇒ (i)

In `A = ℤ × ℤ` the zero ideal satisfies (iii) (its colon ideals `(0 : xⁿ)` do not depend on
`n ≥ 1`) but is neither primary nor irreducible.  So (iii) alone does not imply (i): the
irreducibility hypothesis of the exercise, used in the site's proof in the step
"irreducibility of zero gives `(xⁿ) = 0`", cannot be dropped. -/

section NecessityOfIrreducibility

theorem int_mul_pow_eq_zero_iff {a b : ℤ} {n : ℕ} (hn : 1 ≤ n) :
    b * a ^ n = 0 ↔ b * a = 0 := by
  by_cases ha : a = 0
  · subst ha
    have h0 : (0 : ℤ) ^ n = 0 := zero_pow (by omega)
    rw [h0]
  · constructor
    · intro h
      rcases mul_eq_zero.1 h with h1 | h1
      · rw [h1, zero_mul]
      · exact absurd h1 (pow_ne_zero n ha)
    · intro h
      rcases mul_eq_zero.1 h with h1 | h1
      · rw [h1, zero_mul]
      · exact absurd h1 ha

theorem int_prod_mul_pow_eq_zero_iff (y x : ℤ × ℤ) {n : ℕ} (hn : 1 ≤ n) :
    y * x ^ n = 0 ↔ y * x = 0 := by
  constructor
  · intro h
    have h1 : y.1 * x.1 = 0 := (int_mul_pow_eq_zero_iff hn).1 (by simpa using congrArg Prod.fst h)
    have h2 : y.2 * x.2 = 0 := (int_mul_pow_eq_zero_iff hn).1 (by simpa using congrArg Prod.snd h)
    exact Prod.ext h1 h2
  · intro h
    have h1 : y.1 * x.1 ^ n = 0 :=
      (int_mul_pow_eq_zero_iff hn).2 (by simpa using congrArg Prod.fst h)
    have h2 : y.2 * x.2 ^ n = 0 :=
      (int_mul_pow_eq_zero_iff hn).2 (by simpa using congrArg Prod.snd h)
    exact Prod.ext h1 h2

/-- The zero ideal of `ℤ × ℤ` satisfies condition (iii). -/
theorem prod_bot_condIII : CondIII (⊥ : Ideal (ℤ × ℤ)) := by
  intro x
  refine ⟨1, fun m hm => ?_⟩
  ext y
  rw [Ideal.mem_colon_span_singleton, Ideal.mem_colon_span_singleton, Submodule.mem_bot,
    Submodule.mem_bot, pow_one]
  exact int_prod_mul_pow_eq_zero_iff y x hm

/-- The zero ideal of `ℤ × ℤ` is not primary. -/
theorem prod_bot_not_isPrimary : ¬ (⊥ : Ideal (ℤ × ℤ)).IsPrimary := by
  intro h
  have hmem := (Ideal.isPrimary_iff.1 h).2 (x := (1, 0)) (y := (0, 1)) (by simp)
  rcases hmem with h1 | h1
  · exact absurd ((Submodule.mem_bot (ℤ × ℤ)).1 h1) (by simp)
  · rw [Ideal.mem_radical_iff] at h1
    obtain ⟨k, hk⟩ := h1
    rw [Submodule.mem_bot] at hk
    have hne : ((0, 1) : ℤ × ℤ) ^ k ≠ 0 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp
      · intro hzero
        have h2 : (1 : ℤ) = 0 := by simpa using congrArg Prod.snd hzero
        exact one_ne_zero h2
    exact hne hk

/-- The zero ideal of `ℤ × ℤ` is reducible: it is the intersection of the two coordinate axes. -/
theorem prod_bot_not_infIrred : ¬ InfIrred (⊥ : Ideal (ℤ × ℤ)) := by
  have hbc : Ideal.span {((1, 0) : ℤ × ℤ)} ⊓ Ideal.span {((0, 1) : ℤ × ℤ)} = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨hz1, hz2⟩ := Ideal.mem_inf.1 hz
    rw [Ideal.mem_span_singleton] at hz1 hz2
    obtain ⟨u, hu⟩ := hz1
    obtain ⟨v, hv⟩ := hz2
    rw [Submodule.mem_bot]
    refine Prod.ext ?_ ?_
    · show z.1 = 0
      rw [hv]
      simp
    · show z.2 = 0
      rw [hu]
      simp
  have hb : Ideal.span {((1, 0) : ℤ × ℤ)} ≠ ⊥ := by
    intro h
    have hmem : ((1, 0) : ℤ × ℤ) ∈ (⊥ : Ideal (ℤ × ℤ)) := by
      rw [← h]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact absurd ((Submodule.mem_bot (ℤ × ℤ)).1 hmem) (by simp)
  have hc : Ideal.span {((0, 1) : ℤ × ℤ)} ≠ ⊥ := by
    intro h
    have hmem : ((0, 1) : ℤ × ℤ) ∈ (⊥ : Ideal (ℤ × ℤ)) := by
      rw [← h]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact absurd ((Submodule.mem_bot (ℤ × ℤ)).1 hmem) (by simp)
  intro h
  rcases h.2 hbc with h1 | h1
  · exact hb h1
  · exact hc h1

/-- Condition (iii) does not imply (i) without the irreducibility hypothesis. -/
theorem condIII_does_not_imply_primary :
    ∃ (A : Type) (_ : CommRing A) (a : Ideal A), CondIII a ∧ ¬ a.IsPrimary ∧ ¬ InfIrred a :=
  ⟨ℤ × ℤ, inferInstance, ⊥, prod_bot_condIII, prod_bot_not_isPrimary, prod_bot_not_infIrred⟩

end NecessityOfIrreducibility

end AtiyahMcdonald69.Ex_7_3

#print axioms AtiyahMcdonald69.Ex_7_3.exercise_7_3
#print axioms AtiyahMcdonald69.Ex_7_3.primary_iff_condII
#print axioms AtiyahMcdonald69.Ex_7_3.primary_iff_condIII
#print axioms AtiyahMcdonald69.Ex_7_3.literal_statement_false
#print axioms AtiyahMcdonald69.Ex_7_3.condIII_does_not_imply_primary

#print axioms AtiyahMcdonald69.Ex_7_3.primary_implies_condII
#print axioms AtiyahMcdonald69.Ex_7_3.condII_implies_condIII
#print axioms AtiyahMcdonald69.Ex_7_3.condIII_implies_primary
#print axioms AtiyahMcdonald69.Ex_7_3.infIrred_iff_irreducible
#print axioms AtiyahMcdonald69.Ex_7_3.top_literally_irreducible
#print axioms AtiyahMcdonald69.Ex_7_3.prod_bot_condIII
#print axioms AtiyahMcdonald69.Ex_7_3.prod_bot_not_isPrimary
#print axioms AtiyahMcdonald69.Ex_7_3.prod_bot_not_infIrred
#print axioms AtiyahMcdonald69.Ex_7_3.exercise_7_3_book_phrasing
