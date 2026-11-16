/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter 8 ("Artin Rings"), Exercise 8.6.

## The exercise

Let `A` be a Noetherian ring, `p` a prime ideal of `A` and `q` a `p`-primary ideal.  Consider
chains of primary ideals from `q` to `p`,
  `q = q₀ ⊊ q₁ ⊊ ... ⊊ q_r = p`.
Then every such chain has finite length, the lengths of all such chains are bounded, and all
maximal chains have the same length: if the chain is maximal, then `r + 1 = ℓ(A_p / qA_p)`,
the length of `A_p / q A_p` as an `A_p`-module.  (In particular the common length of a maximal
chain is `ℓ(A_p/qA_p) - 1`.)

## Formal statement of the results below

* `solution` : if `a : Fin (r+1) → Ideal A` is a strictly increasing chain with `a 0 = q`,
  `a (Fin.last r) = p`, all `a i` primary, and no primary ideal can be inserted between two
  consecutive members (`hmax`), then `(r+1 : ℕ∞) = ℓ(A_p / qA_p)`, where the length is
  `Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸ q.map (algebraMap A _))`.
  This is the main assertion of the exercise.
* `chain_length_le` : for *any* such chain (no maximality needed),
  `(r+1 : ℕ∞) ≤ ℓ(A_p / qA_p)`; this is the boundedness/finiteness assertion.
* `maximal_chain_lengths_eq` : any two maximal chains have the same length (the Jordan–Hölder
  conclusion stated without reference to the length).

## Proof outline (following the natural proof)

1. Every ideal `a` with `q ≤ a ≤ p` and `a` primary satisfies `(a A_p) ∩ A = a`
   (`under_map_eq_self`, from `IsLocalization.under_map_of_isPrimary_disjoint`), and every
   ideal `J` of `A_p` with `qA_p ≤ J ≤ pA_p` has `p`-primary contraction
   (`isPrimary_under_of_le`: its radical is `p`, and an element not in `p` becomes a unit in
   `A_p`).  Hence primary ideals between `q` and `p` correspond bijectively, and order
   preservingly, to the ideals of `A_p` between `qA_p` and `pA_p`.
2. Passing to `A_p ⧸ qA_p`, chains from `q` to `p` correspond to chains of submodules from
   `0` to the maximal ideal `pA_p/qA_p`; the maximal chains are exactly the chains of covering
   pairs (`chainImage_covBy`, `chainImage_last_covBy`, using maximality of `pA_p` in `A_p`).
3. Appending `⊤` turns a maximal chain into a composition series of `A_p ⧸ qA_p`
   (`exists_compositionSeries_of_covBy`), so its length is the module length
   (`Module.length_compositionSeries`, i.e. Jordan–Hölder).  For an arbitrary chain the
   appended sequence is a strictly increasing series, whence the bound
   (`length_le_of_strictMono_of_lt_top`).

## Scope and adaptations

* The Noetherian hypothesis of the book is kept, although the chain arguments themselves do
  not use it (the bound is stated with values in `ℕ∞`, so it is meaningful without finiteness).
* `ℓ(A_p/qA_p)` is formalised as the length of `A_p ⧸ qA_p` as a module over `A_p`, which is
  the length of the ring `A_p/qA_p` as a module over itself (same submodule lattice).
* "Maximal chain" is expressed as: no primary ideal lies strictly between two consecutive
  members of the chain (equivalently, the chain cannot be refined).
* We do not reprove the Chapter 8 fact that `ℓ(A_p/qA_p)` is *finite* (that `A_p/qA_p` is
  Artinian); the bound `chain_length_le` is stated with values in `ℕ∞` and is meaningful
  whether or not that length is finite.  Chain lengths are `r + 1` for a family indexed by
  `Fin (r+1)`, so no separate finiteness statement for chains is needed.

Source of the natural-language proof:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8-6
-/

import Mathlib

namespace AtiyahMcdonald69
namespace Ex_8_6

open JordanHolderLattice Ideal

/-! ## Generic length arguments for chains of submodules -/

section ChainLength

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Extend a chain of covering pairs `f 0 ⋖ f 1 ⋖ ... ⋖ f n` by a top element: the result is a
composition series of length `n + 1` with head `f 0` and last `⊤`. -/
lemma exists_compositionSeries_of_covBy {n : ℕ} (f : Fin (n + 1) → Submodule R M)
    (hstep : ∀ i : Fin n, f i.castSucc ⋖ f i.succ)
    (htop : f (Fin.last n) ⋖ ⊤) :
    ∃ s : CompositionSeries (Submodule R M), s.length = n + 1 ∧ s.head = f 0 ∧ s.last = ⊤ := by
  set g : Fin (n + 2) → Submodule R M := Fin.snoc (α := fun _ => Submodule R M) f ⊤ with hg
  have hgc : ∀ i : Fin (n + 1), g i.castSucc = f i := by
    intro i
    rw [hg]
    exact Fin.snoc_castSucc (α := fun _ => Submodule R M) ⊤ f i
  have hgl : g (Fin.last (n + 1)) = ⊤ := by
    rw [hg]
    exact Fin.snoc_last (α := fun _ => Submodule R M) ⊤ f
  have hstepg : ∀ i : Fin (n + 1), g i.castSucc ⋖ g i.succ := by
    intro i
    refine Fin.lastCases (motive := fun i => g i.castSucc ⋖ g i.succ) ?_ (fun j => ?_) i
    · rw [Fin.succ_last, hgl]
      simpa [hgc] using htop
    · have h1 : g (j.castSucc).castSucc = f j.castSucc := hgc j.castSucc
      have h2 : g ((j.castSucc).succ) = f j.succ := by
        rw [Fin.succ_castSucc]
        exact hgc j.succ
      rw [h1, h2]
      exact hstep j
  refine ⟨⟨n + 1, g, hstepg⟩, rfl, ?_, ?_⟩
  · have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    show g 0 = f 0
    rw [h0, hgc 0]
  · show g (Fin.last (n + 1)) = ⊤
    exact hgl

/-- A strictly increasing chain of submodules which can be extended by `⊤` has at most
`n + 1` steps. -/
lemma length_le_of_strictMono_of_lt_top {n : ℕ} {N : Fin (n + 1) → Submodule R M}
    (hN : StrictMono N) (hNtop : N (Fin.last n) < ⊤) :
    (n + 1 : ℕ∞) ≤ Module.length R M := by
  have hstep : ∀ i : Fin n, N i.castSucc < N i.succ := fun i => hN (Fin.castSucc_lt_succ (i := i))
  let p : LTSeries (Submodule R M) := ⟨n, N, hstep⟩
  have hp_last : p.last = N (Fin.last n) := rfl
  have hlt : p.last < ⊤ := by rw [hp_last]; exact hNtop
  let p' : LTSeries (Submodule R M) := p.snoc ⊤ hlt
  have hlen : p'.length = n + 1 := rfl
  have h : (n + 1 : ℕ∞) ≤ Order.height (⊤ : Submodule R M) := by
    have hh := Order.length_le_height (p := p') (x := ⊤) le_top
    simpa [hlen] using hh
  rwa [Module.length_eq_height]

/-- If a chain `N 0 ⋖ N 1 ⋖ ... ⋖ N n ⋖ ⊤` consists of covering pairs, then `n + 1` equals the
length of `M`. -/
lemma length_eq_of_maximal_chain {n : ℕ} {N : Fin (n + 1) → Submodule R M}
    (hN0 : N 0 = ⊥) (hstep : ∀ i : Fin n, N i.castSucc ⋖ N i.succ)
    (htop : N (Fin.last n) ⋖ ⊤) :
    (n + 1 : ℕ∞) = Module.length R M := by
  obtain ⟨s, hlen, hhead, hlast⟩ := exists_compositionSeries_of_covBy N hstep htop
  have h := Module.length_compositionSeries s (hhead.trans hN0) hlast
  rw [hlen] at h
  exact h

end ChainLength

/-! ## Elementary lemma: the radical of an ideal between `q` and `radical q` -/

lemma radical_eq_of_le_of_le_radical {R : Type*} [CommSemiring R] {q a : Ideal R}
    (h1 : q ≤ a) (h2 : a ≤ q.radical) : a.radical = q.radical := by
  refine le_antisymm ?_ (Ideal.radical_mono h1)
  calc a.radical ≤ q.radical.radical := Ideal.radical_mono h2
    _ = q.radical := Ideal.radical_idem q

section Localization

variable {A : Type*} [CommRing A]

lemma isPrimary_under_of_le (p : Ideal A) [hp : p.IsPrime] {q : Ideal A} (_hq : q.IsPrimary)
    (hrad : q.radical = p) (J : Ideal (Localization.AtPrime p))
    (h1 : q ≤ J.under A) (h2 : J ≤ Ideal.map (algebraMap A (Localization.AtPrime p)) p) :
    (J.under A).IsPrimary := by
  have hle_p : J.under A ≤ p := by
    calc J.under A
        ≤ (Ideal.map (algebraMap A (Localization.AtPrime p)) p).under A :=
          (IsLocalization.under_le_under_iff p.primeCompl (Localization.AtPrime p)).mpr h2
      _ = p := by
          rw [IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
          exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p
  have hradJ : (J.under A).radical = p := by
    refine le_antisymm ?_ ?_
    · calc (J.under A).radical ≤ p.radical := Ideal.radical_mono hle_p
        _ = p := hp.radical
    · have h := Ideal.radical_mono h1
      rw [hrad] at h
      exact h
  rw [Ideal.isPrimary_iff, hradJ]
  refine ⟨?_, ?_⟩
  · intro htop
    have : (⊤ : Ideal A).radical = p := by rw [← htop]; exact hradJ
    rw [Ideal.radical_top] at this
    exact hp.ne_top this.symm
  · intro x y hxy
    by_cases hx : x ∈ J.under A
    · exact Or.inl hx
    · refine Or.inr ?_
      by_contra hy
      have hunit : IsUnit (algebraMap A (Localization.AtPrime p) y) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p y).mpr hy
      have hxJ : algebraMap A (Localization.AtPrime p) x ∈ J := by
        obtain ⟨u, hu⟩ := hunit.exists_right_inv
        have hxy' : algebraMap A (Localization.AtPrime p) (x * y) ∈ J := hxy
        have hmem : algebraMap A (Localization.AtPrime p) (x * y) * u ∈ J :=
          Ideal.mul_mem_right u J hxy'
        have heq : algebraMap A (Localization.AtPrime p) x
            = algebraMap A (Localization.AtPrime p) (x * y) * u := by
          rw [map_mul, mul_assoc, hu, mul_one]
        rw [heq]
        exact hmem
      exact hx hxJ

lemma under_map_eq_self (p : Ideal A) [hp : p.IsPrime] {a : Ideal A} (ha : a.IsPrimary)
    (hle : a ≤ p) : (Ideal.map (algebraMap A (Localization.AtPrime p)) a).under A = a :=
  IsLocalization.under_map_of_isPrimary_disjoint p.primeCompl (Localization.AtPrime p) ha
    (Set.disjoint_left.mpr fun _ hx1 hx2 => hx1 (hle hx2))

/-! ## The image of a chain of ideals in `A_p ⧸ qA_p` -/

variable (p : Ideal A) [hp : p.IsPrime]

/-- Image of a chain of ideals of `A` in `A_p ⧸ q A_p`. -/
noncomputable def chainImage (q : Ideal A) {r : ℕ} (a : Fin (r + 1) → Ideal A) :
    Fin (r + 1) → Submodule (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p))) :=
  fun i => Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
    ((a i).map (algebraMap A (Localization.AtPrime p)))

/-- `(q A_p)` is contained in the contraction of what it generates. -/
lemma comap_map_mkQ_apply (q : Ideal A) {b : Ideal (Localization.AtPrime p)}
    (hb : q.map (algebraMap A (Localization.AtPrime p)) ≤ b) :
    Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
      (Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ b) = b := by
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hb]

/-- Every submodule of `A_p ⧸ qA_p` is the image of its contraction. -/
lemma map_comap_mkQ_apply (q : Ideal A) (c : Submodule (Localization.AtPrime p)
    (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p)))) :
    Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
      (Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c) = c :=
  Submodule.map_comap_eq_self (by simp)

/-- The image of `p A_p` in `A_p ⧸ q A_p`. -/
lemma chainImage_last_eq (q : Ideal A) {r : ℕ} {a : Fin (r + 1) → Ideal A}
    (hl : a (Fin.last r) = p) :
    chainImage p q a (Fin.last r)
      = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
          (p.map (algebraMap A (Localization.AtPrime p))) := by
  simp only [chainImage, hl]

lemma chainImage_strictMono (q : Ideal A) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hmono : StrictMono a) (h0 : a 0 = q)
    (hl : a (Fin.last r) = p) (hprim : ∀ i, (a i).IsPrimary) :
    StrictMono (chainImage p q a) := by
  have haP : ∀ k, a k ≤ p := fun k => (hmono.monotone (Fin.le_last k)).trans hl.le
  have hQa : ∀ k, q ≤ a k := fun k => h0 ▸ hmono.monotone (Fin.zero_le k)
  have hunder : ∀ k, ((a k).map (algebraMap A (Localization.AtPrime p))).under A = a k :=
    fun k => under_map_eq_self p (hprim k) (haP k)
  have hQb : ∀ k, q.map (algebraMap A (Localization.AtPrime p))
      ≤ (a k).map (algebraMap A (Localization.AtPrime p)) := fun k => Ideal.map_mono (hQa k)
  intro i j hij
  simp only [chainImage]
  refine lt_of_le_of_ne (Submodule.map_mono (Ideal.map_mono (hmono.monotone hij.le))) ?_
  intro heq
  have h1 : Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
      (Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
        ((a i).map (algebraMap A (Localization.AtPrime p))))
      = Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
        (Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
          ((a j).map (algebraMap A (Localization.AtPrime p)))) := by rw [heq]
  have h2 : q.map (algebraMap A (Localization.AtPrime p)) ⊔
        (a i).map (algebraMap A (Localization.AtPrime p))
      = q.map (algebraMap A (Localization.AtPrime p)) ⊔
        (a j).map (algebraMap A (Localization.AtPrime p)) := by
    simpa only [Submodule.comap_map_mkQ] using h1
  have h3 : (a i).map (algebraMap A (Localization.AtPrime p))
      = (a j).map (algebraMap A (Localization.AtPrime p)) := by
    simpa only [sup_eq_right.mpr (hQb i), sup_eq_right.mpr (hQb j)] using h2
  have h4 : a i = a j := by
    rw [← hunder i, ← hunder j]
    exact congrArg (Ideal.under A) h3
  exact absurd h4 (ne_of_lt (hmono hij))

lemma chainImage_zero (q : Ideal A) {r : ℕ} {a : Fin (r + 1) → Ideal A} (h0 : a 0 = q) :
    chainImage p q a 0 = ⊥ := by
  simp only [chainImage, h0]
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]

lemma chainImage_last_lt_top (q : Ideal A) (hrad : q.radical = p) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hl : a (Fin.last r) = p) :
    chainImage p q a (Fin.last r) < ⊤ := by
  have hP : (p.map (algebraMap A (Localization.AtPrime p))).IsMaximal := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hQP : q.map (algebraMap A (Localization.AtPrime p))
      ≤ p.map (algebraMap A (Localization.AtPrime p)) :=
    Ideal.map_mono (hrad ▸ Ideal.le_radical)
  simp only [chainImage, hl]
  refine lt_top_iff_ne_top.mpr ?_
  intro htop
  rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hQP] at htop
  exact hP.ne_top htop


lemma chainImage_covBy (q : Ideal A) (hq : q.IsPrimary) (hrad : q.radical = p) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hmono : StrictMono a) (h0 : a 0 = q)
    (hl : a (Fin.last r) = p) (hprim : ∀ i, (a i).IsPrimary)
    (hmax : ∀ (i : Fin r) (c : Ideal A), a i.castSucc < c → c < a i.succ → ¬ c.IsPrimary) :
    ∀ i : Fin r, CovBy (chainImage p q a i.castSucc) (chainImage p q a i.succ) := by
  have hstrict := chainImage_strictMono p q hmono h0 hl hprim
  have haP : ∀ k, a k ≤ p := fun k => (hmono.monotone (Fin.le_last k)).trans hl.le
  have hQa : ∀ k, q ≤ a k := fun k => h0 ▸ hmono.monotone (Fin.zero_le k)
  have hunder : ∀ k, ((a k).map (algebraMap A (Localization.AtPrime p))).under A = a k :=
    fun k => under_map_eq_self p (hprim k) (haP k)
  have hQb : ∀ k, q.map (algebraMap A (Localization.AtPrime p))
      ≤ (a k).map (algebraMap A (Localization.AtPrime p)) := fun k => Ideal.map_mono (hQa k)
  have hbP : ∀ k, (a k).map (algebraMap A (Localization.AtPrime p))
      ≤ p.map (algebraMap A (Localization.AtPrime p)) := fun k => Ideal.map_mono (haP k)
  intro i
  refine ⟨hstrict (Fin.castSucc_lt_succ (i := i)), ?_⟩
  intro c h1 h2
  set J : Ideal (Localization.AtPrime p) :=
    Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c with hJ
  have hJQ : q.map (algebraMap A (Localization.AtPrime p)) ≤ J :=
    Submodule.le_comap_mkQ (p := q.map (algebraMap A (Localization.AtPrime p))) c
  have hJle : J ≤ (a i.succ).map (algebraMap A (Localization.AtPrime p)) := by
    calc J = Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c := hJ
      _ ≤ Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (chainImage p q a i.succ) := Submodule.comap_mono (le_of_lt h2)
      _ = (a i.succ).map (algebraMap A (Localization.AtPrime p)) := by
          simp only [chainImage]
          exact comap_map_mkQ_apply p q (hQb i.succ)
  have hJge : (a i.castSucc).map (algebraMap A (Localization.AtPrime p)) ≤ J := by
    calc (a i.castSucc).map (algebraMap A (Localization.AtPrime p))
        = Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (chainImage p q a i.castSucc) := by
            simp only [chainImage]
            exact (comap_map_mkQ_apply p q (hQb i.castSucc)).symm
      _ ≤ Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c :=
            Submodule.comap_mono (le_of_lt h1)
      _ = J := hJ
  have hJgt : (a i.castSucc).map (algebraMap A (Localization.AtPrime p)) < J := by
    refine lt_of_le_of_ne hJge ?_
    intro heq
    have hc : c = chainImage p q a i.castSucc := by
      calc c = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c) :=
            (map_comap_mkQ_apply p q c).symm
        _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ J := by rw [hJ]
        _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
              ((a i.castSucc).map (algebraMap A (Localization.AtPrime p))) := by rw [heq]
        _ = chainImage p q a i.castSucc := rfl
    exact absurd hc (ne_of_gt h1)
  have hJlt : J < (a i.succ).map (algebraMap A (Localization.AtPrime p)) := by
    refine lt_of_le_of_ne hJle ?_
    intro heq
    have hc : c = chainImage p q a i.succ := by
      calc c = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c) :=
            (map_comap_mkQ_apply p q c).symm
        _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ J := by rw [hJ]
        _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
              ((a i.succ).map (algebraMap A (Localization.AtPrime p))) := by rw [heq]
        _ = chainImage p q a i.succ := rfl
    exact absurd hc (ne_of_lt h2)
  have hqJ : q ≤ J.under A := by
    calc q = a 0 := h0.symm
      _ ≤ a i.castSucc := hmono.monotone (Fin.zero_le _)
      _ = ((a i.castSucc).map (algebraMap A (Localization.AtPrime p))).under A :=
            (hunder i.castSucc).symm
      _ ≤ J.under A := Ideal.comap_mono hJge
  have hJP : J ≤ p.map (algebraMap A (Localization.AtPrime p)) := hJle.trans (hbP i.succ)
  have hJprim : (J.under A).IsPrimary := isPrimary_under_of_le p hq hrad J hqJ hJP
  have hlt1 : a i.castSucc < J.under A := by
    refine lt_of_le_of_ne ?_ ?_
    · calc a i.castSucc
          = ((a i.castSucc).map (algebraMap A (Localization.AtPrime p))).under A :=
              (hunder i.castSucc).symm
        _ ≤ J.under A := Ideal.comap_mono hJge
    · intro heq
      have hconj : J = (a i.castSucc).map (algebraMap A (Localization.AtPrime p)) := by
        calc J = (J.under A).map (algebraMap A (Localization.AtPrime p)) :=
              (IsLocalization.map_under p.primeCompl (Localization.AtPrime p) J).symm
          _ = (a i.castSucc).map (algebraMap A (Localization.AtPrime p)) := by rw [← heq]
      exact absurd hconj (ne_of_gt hJgt)
  have hlt2 : J.under A < a i.succ := by
    refine lt_of_le_of_ne ?_ ?_
    · calc J.under A ≤ ((a i.succ).map (algebraMap A (Localization.AtPrime p))).under A :=
              Ideal.comap_mono hJle
        _ = a i.succ := hunder i.succ
    · intro heq
      have hconj : J = (a i.succ).map (algebraMap A (Localization.AtPrime p)) := by
        calc J = (J.under A).map (algebraMap A (Localization.AtPrime p)) :=
              (IsLocalization.map_under p.primeCompl (Localization.AtPrime p) J).symm
          _ = (a i.succ).map (algebraMap A (Localization.AtPrime p)) := by rw [heq]
      exact absurd hconj (ne_of_lt hJlt)
  exact hmax i (J.under A) hlt1 hlt2 hJprim

lemma chainImage_last_covBy (q : Ideal A) (hrad : q.radical = p) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hl : a (Fin.last r) = p) :
    CovBy (chainImage p q a (Fin.last r)) ⊤ := by
  have hP : (p.map (algebraMap A (Localization.AtPrime p))).IsMaximal := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hQP : q.map (algebraMap A (Localization.AtPrime p))
      ≤ p.map (algebraMap A (Localization.AtPrime p)) :=
    Ideal.map_mono (hrad ▸ Ideal.le_radical)
  refine ⟨chainImage_last_lt_top p q hrad hl, ?_⟩
  intro c h1 h2
  set J : Ideal (Localization.AtPrime p) :=
    Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c with hJ
  have hPJ : p.map (algebraMap A (Localization.AtPrime p)) ≤ J := by
    calc p.map (algebraMap A (Localization.AtPrime p))
        = Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
              (p.map (algebraMap A (Localization.AtPrime p)))) :=
            (comap_map_mkQ_apply p q hQP).symm
      _ = Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (chainImage p q a (Fin.last r)) := by rw [chainImage_last_eq p q hl]
      _ ≤ Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c :=
            Submodule.comap_mono (le_of_lt h1)
      _ = J := hJ
  have hJne : J ≠ ⊤ := by
    intro hJtop
    have hc : c = ⊤ := by
      calc c = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c) :=
            (map_comap_mkQ_apply p q c).symm
        _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ J := by rw [hJ]
        _ = ⊤ := by rw [hJtop, Submodule.map_top, Submodule.range_mkQ]
    exact absurd hc (ne_of_lt h2)
  have hJP : J = p.map (algebraMap A (Localization.AtPrime p)) := (hP.eq_of_le hJne hPJ).symm
  have hc : c = chainImage p q a (Fin.last r) := by
    calc c = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
          (Submodule.comap (q.map (algebraMap A (Localization.AtPrime p))).mkQ c) :=
          (map_comap_mkQ_apply p q c).symm
      _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ J := by rw [hJ]
      _ = Submodule.map (q.map (algebraMap A (Localization.AtPrime p))).mkQ
            (p.map (algebraMap A (Localization.AtPrime p))) := by rw [hJP]
      _ = chainImage p q a (Fin.last r) := by rw [chainImage_last_eq p q hl]
  exact absurd hc (ne_of_gt h1)


end Localization

/-! ## The main results -/

section Main

/-- **Atiyah–Macdonald, Exercise 8.6 (boundedness part).**  Every chain of primary ideals from
`q` to `p` has length at most `ℓ(A_p/qA_p)`. -/
theorem chain_length_le {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    {q : Ideal A} (_hq : q.IsPrimary) (hrad : q.radical = p) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hmono : StrictMono a) (h0 : a 0 = q)
    (hl : a (Fin.last r) = p) (hprim : ∀ i, (a i).IsPrimary) :
    (r + 1 : ℕ∞) ≤ Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p))) :=
  length_le_of_strictMono_of_lt_top (chainImage_strictMono p q hmono h0 hl hprim)
    (chainImage_last_lt_top p q hrad hl)

/-- **Atiyah–Macdonald, Exercise 8.6 (main part).**  A maximal chain of primary ideals from `q`
to `p` has length `r` with `r + 1 = ℓ(A_p/qA_p)`. -/
theorem solution {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    {q : Ideal A} (hq : q.IsPrimary) (hrad : q.radical = p) {r : ℕ}
    {a : Fin (r + 1) → Ideal A} (hmono : StrictMono a) (h0 : a 0 = q)
    (hl : a (Fin.last r) = p) (hprim : ∀ i, (a i).IsPrimary)
    (hmax : ∀ (i : Fin r) (c : Ideal A), a i.castSucc < c → c < a i.succ → ¬ c.IsPrimary) :
    (r + 1 : ℕ∞) = Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p))) :=
  length_eq_of_maximal_chain (chainImage_zero p q h0)
    (chainImage_covBy p q hq hrad hmono h0 hl hprim hmax) (chainImage_last_covBy p q hrad hl)

/-- **Atiyah–Macdonald, Exercise 8.6 (Jordan–Hölder conclusion).**  Any two maximal chains of
primary ideals from `q` to `p` have the same length. -/
theorem maximal_chain_lengths_eq {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A)
    [p.IsPrime] {q : Ideal A} (hq : q.IsPrimary) (hrad : q.radical = p) {r r' : ℕ}
    {a : Fin (r + 1) → Ideal A} {a' : Fin (r' + 1) → Ideal A}
    (hmono : StrictMono a) (h0 : a 0 = q) (hl : a (Fin.last r) = p)
    (hprim : ∀ i, (a i).IsPrimary)
    (hmax : ∀ (i : Fin r) (c : Ideal A), a i.castSucc < c → c < a i.succ → ¬ c.IsPrimary)
    (hmono' : StrictMono a') (h0' : a' 0 = q) (hl' : a' (Fin.last r') = p)
    (hprim' : ∀ i, (a' i).IsPrimary)
    (hmax' : ∀ (i : Fin r') (c : Ideal A), a' i.castSucc < c → c < a' i.succ → ¬ c.IsPrimary) :
    r = r' := by
  have h1 := solution p hq hrad hmono h0 hl hprim hmax
  have h2 := solution p hq hrad hmono' h0' hl' hprim' hmax'
  have h3 : (r + 1 : ℕ∞) = (r' + 1 : ℕ∞) := h1.trans h2.symm
  have h4 : r + 1 = r' + 1 := Nat.cast_injective h3
  exact Nat.succ.inj h4

end Main

end Ex_8_6
end AtiyahMcdonald69
