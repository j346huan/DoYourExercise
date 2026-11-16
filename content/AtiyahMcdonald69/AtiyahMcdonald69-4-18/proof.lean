/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 4, Exercise 18.

Statement (book, p. 57):

  "18. Consider the following condition on a ring A:
   (L2) Given an ideal a and a descending chain S₁ ⊇ S₂ ⊇ ⋯ ⊇ Sₙ ⊇ ⋯ of multiplicatively
   closed subsets of A, there exists an integer n such that Sₙ(a) = Sₙ₊₁(a) = ⋯.
   Prove that the following are equivalent:
   i) Every ideal in A has a primary decomposition;
   ii) A satisfies (L1) and (L2)."

Here (L1) is the hypothesis of Exercise 17:

  "(L1) For every ideal a ≠ (1) in A and every prime ideal p, there exists x ∉ p such that
   S_p(a) = (a:x), where S_p = A - p."

and for a multiplicatively closed set S, S(a) is the saturation of a with respect to S, i.e.
the contraction of S⁻¹a in A (Exercise 12); this is `saturation S a` below, with membership
criterion `mem_saturation : x ∈ S(a) ↔ ∃ s ∈ S, s * x ∈ a`.

The statement checked here is the full equivalence
`(HasPrimaryDecompositions A) ↔ (ConditionL1 A ∧ ConditionL2 A)`
(`solution`, and `solution_isLasker` in Mathlib's `IsLasker` terminology).

Formalisation notes:

* A "multiplicatively closed subset" is a `Submonoid A` (it contains `1` and is closed under
  multiplication, exactly as in the book), and "`a` has a primary decomposition" means that `a`
  is a finite intersection of primary ideals, the empty intersection (i.e. `⊤`) being allowed so
  that the unit ideal is covered: `HasPrimaryDecompositions A`.
* `(a : x)` is `a.colon (Ideal.span {x})`; `mem_colon_singleton` records that its elements are
  the `y` with `y * x ∈ a`, and `p.primeCompl` is `A - p`.
* (i) ⇒ (L2) is the observation of the natural proof that each primary component `q` of a
  decomposition saturates to `⊤` or to `q`, and can switch from the former to the latter at most
  once (Exercise 4.12 is used for finite intersections).
* (i) ⇒ (L1) takes `x = ∏_{√q ⊄ p} y_q` with `y_q ∈ √q - p`, a power `x ^ N` of it, and
  computes `S_p(a) = ⋂_{√q ≤ p} q = (a : x ^ N)` with Exercise 4.15.
* (ii) ⇒ (i) is the transfinite construction of Exercise 17, with the maximality device made
  explicit through Zorn's lemma (`maxIdeal`, `stepAux`, `orbit`) and terminated by (L2): the
  multiplicative sets `A - (p₁ ∪ ⋯ ∪ pₙ)` are decreasing, so the running intersections
  `Qₙ = Sₙ(a)` eventually stabilise, and maximality at the stabilising stage forces the process to
  stop.  Prime avoidance (`Ideal.subset_union_prime`) shows `Sₙ` meets `aₙ`, which is what makes
  `Sₙ(a) = Qₙ` provable.
* The hypothesis (L1) alone gives only intersections of *possibly infinitely many* primary
  ideals (Chapter 4, Exercise 17); the finiteness in (i) genuinely uses (L2).  Nothing here is
  weakened silently: `ConditionL1` and `ConditionL2` are literally the ones stated in the book.
* Sanity checks: Noetherian rings, `ℤ` and fields satisfy (L1) and (L2)
  (`conditions_of_isNoetherianRing`), so condition (ii) is satisfiable.
-/
import Mathlib

open scoped Classical Pointwise

set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_4_18

variable {A : Type*} [CommRing A]

/-! ## The saturation `S(a)` of an ideal -/

/-- The **saturation** of an ideal `a` with respect to a multiplicatively closed subset
`S ⊆ A` (Atiyah–Macdonald, Chapter 4, Exercise 12): the contraction in `A` of the extension
`S⁻¹a` of `a` to the ring of fractions `S⁻¹A`. -/
noncomputable def saturation (S : Submonoid A) (a : Ideal A) : Ideal A :=
  (a.map (algebraMap A (Localization S))).under A

/-- Membership criterion for the saturation: `x ∈ S(a)` iff `s * x ∈ a` for some `s ∈ S`. -/
theorem mem_saturation {S : Submonoid A} {a : Ideal A} {x : A} :
    x ∈ saturation S a ↔ ∃ s ∈ S, s * x ∈ a := by
  rw [saturation, Ideal.mem_under]
  exact IsLocalization.algebraMap_mem_map_algebraMap_iff S (Localization S) a x

/-- Every ideal is contained in its saturation. -/
theorem le_saturation (S : Submonoid A) (a : Ideal A) : a ≤ saturation S a := by
  intro x hx
  exact mem_saturation.mpr ⟨1, S.one_mem, by simpa using hx⟩

/-- The saturation of the whole ring is the whole ring. -/
theorem saturation_top (S : Submonoid A) : saturation S (⊤ : Ideal A) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact mem_saturation.mpr ⟨1, S.one_mem, by simp⟩

/-- Exercise 4.12 (i): `S(a) ∩ S(b) = S(a ∩ b)`. -/
theorem saturation_inf (S : Submonoid A) (a b : Ideal A) :
    saturation S a ⊓ saturation S b = saturation S (a ⊓ b) := by
  ext x
  simp only [Ideal.mem_inf, mem_saturation]
  constructor
  · rintro ⟨⟨s, hs, hsa⟩, t, ht, htb⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_, ?_⟩
    · rw [show s * t * x = t * (s * x) by ring]; exact a.mul_mem_left t hsa
    · rw [mul_assoc]; exact b.mul_mem_left s htb
  · rintro ⟨s, hs, hsa, hsb⟩
    exact ⟨⟨s, hs, hsa⟩, s, hs, hsb⟩

/-- The saturation of a finite intersection is the intersection of the saturations. -/
theorem saturation_finsetInf {ι : Type*} (S : Submonoid A) (t : Finset ι)
    (f : ι → Ideal A) :
    saturation S (t.inf f) = t.inf (fun i => saturation S (f i)) := by
  induction t using Finset.induction with
  | empty => rw [Finset.inf_empty, Finset.inf_empty, saturation_top]
  | insert a s _ ih => rw [Finset.inf_insert, Finset.inf_insert, ← saturation_inf, ih]

/-- A finite infimum in which the terms outside a given finite set are `⊤` is the infimum
over that finite set. -/
theorem inf_ite_eq {ι : Type*} (t : Finset ι) (p : ι → Prop) [DecidablePred p]
    (q : ι → Ideal A) : t.inf (fun i => if p i then q i else ⊤) = (t.filter p).inf q := by
  induction t using Finset.induction with
  | empty => rw [Finset.inf_empty, Finset.filter_empty, Finset.inf_empty]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.filter_insert]
    by_cases h : p a
    · rw [if_pos h, if_pos h, Finset.inf_insert, ih]
    · rw [if_neg h, if_neg h, ih, top_inf_eq]

/-- Exercise 4.12 (iii): `S(a) = (1)` iff `a` meets `S`. -/
theorem saturation_eq_top_iff (S : Submonoid A) (a : Ideal A) :
    saturation S a = ⊤ ↔ ∃ s ∈ S, s ∈ a := by
  rw [Ideal.eq_top_iff_one, mem_saturation]
  exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, by simpa using h⟩,
    fun ⟨s, hs, h⟩ => ⟨s, hs, by simpa using h⟩⟩

/-- The saturation is antitone in the multiplicatively closed set. -/
theorem saturation_le_of_le {S T : Submonoid A} (h : S ≤ T) (a : Ideal A) :
    saturation S a ≤ saturation T a := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := mem_saturation.mp hx
  exact mem_saturation.mpr ⟨s, h hs, hsx⟩

/-- The saturation is monotone in the ideal. -/
theorem saturation_mono (S : Submonoid A) {a b : Ideal A} (h : a ≤ b) :
    saturation S a ≤ saturation S b := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := mem_saturation.mp hx
  exact mem_saturation.mpr ⟨s, hs, h hsx⟩

/-- A saturated ideal is stable under division by elements of `S`. -/
theorem saturation_mul_mem {S : Submonoid A} {a : Ideal A} {s y : A} (hs : s ∈ S)
    (h : s * y ∈ saturation S a) : y ∈ saturation S a := by
  obtain ⟨t, ht, hty⟩ := mem_saturation.mp h
  refine mem_saturation.mpr ⟨t * s, S.mul_mem ht hs, ?_⟩
  have h' : t * s * y = t * (s * y) := by ring
  rw [h']
  exact hty

/-- A primary ideal whose radical is disjoint from `S` saturates to itself. -/
theorem saturation_primary_eq_self {q : Ideal A} (hq : q.IsPrimary) {S : Submonoid A}
    (h : Disjoint (S : Set A) (q.radical : Set A)) : saturation S q = q := by
  refine le_antisymm ?_ (le_saturation S q)
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_saturation.mp hx
  rw [mul_comm] at hxs
  rcases (Ideal.isPrimary_iff.mp hq).2 hxs with h1 | h1
  · exact h1
  · exact absurd h1 (Set.disjoint_left.mp h hs)

/-- A primary ideal whose radical meets `S` saturates to the whole ring. -/
theorem saturation_primary_eq_top {q : Ideal A} {S : Submonoid A}
    (h : ¬ Disjoint (S : Set A) (q.radical : Set A)) : saturation S q = ⊤ := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨s, hs, hsr⟩ := h
  have hsr' : s ∈ q.radical := hsr
  rw [Ideal.mem_radical_iff] at hsr'
  obtain ⟨n, hn⟩ := hsr'
  exact saturation_eq_top_iff _ _ |>.mpr ⟨s ^ n, S.pow_mem hs n, hn⟩

/-- For prime `p` and `a ≤ p`, the saturation `S_p(a)` is contained in `p`. -/
theorem saturation_le_of_le_prime {p a : Ideal A} [hp : p.IsPrime] (h : a ≤ p) :
    saturation p.primeCompl a ≤ p := by
  intro y hy
  obtain ⟨s, hs, hsy⟩ := mem_saturation.mp hy
  rcases hp.mem_or_mem (h hsy) with h' | h'
  · exact absurd h' (Ideal.mem_primeCompl_iff.mp hs)
  · exact h'

/-- For a primary ideal `q`, an element `f ∉ √q` is a non-zero-divisor modulo `q`. -/
theorem mem_of_mul_mem_of_notMem_radical {q : Ideal A} (hq : q.IsPrimary) {f x : A}
    (hf : f ∉ q.radical) (h : x * f ∈ q) : x ∈ q := by
  rcases (Ideal.isPrimary_iff.mp hq).2 h with h' | h'
  · exact h'
  · exact absurd h' hf

/-- If `f` is not in a prime ideal `p`, no power of `f` lies in `p`. -/
theorem pow_notMem_of_notMem {p : Ideal A} (hp : p.IsPrime) {f : A} (hf : f ∉ p) (n : ℕ) :
    f ^ n ∉ p :=
  fun h => hf (hp.mem_of_pow_mem n h)

/-! ## The multiplicatively closed set generated by `A - p` and one element -/

/-- The multiplicatively closed set generated by `A - p` and `y`, namely
`{ s * y ^ n | s ∉ p, n : ℕ }`. -/
def primeComplPowers (p : Ideal A) [hp : p.IsPrime] (y : A) : Submonoid A where
  carrier := {z | ∃ s : A, s ∉ p ∧ ∃ n : ℕ, s * y ^ n = z}
  one_mem' := ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨s, hs, m, rfl⟩ ⟨t, ht, n, rfl⟩
    refine ⟨s * t, ?_, m + n, by rw [pow_add]; ring⟩
    intro h
    exact (hp.mem_or_mem h).elim hs ht

theorem mem_primeComplPowers {p : Ideal A} [hp : p.IsPrime] {y z : A} :
    z ∈ primeComplPowers p y ↔ ∃ s : A, s ∉ p ∧ ∃ n : ℕ, s * y ^ n = z := Iff.rfl

/-- If `p` is a minimal prime ideal over `b`, then `p` is the radical of the saturation
`S_p(b)`. -/
theorem radical_saturation_eq_of_isMinimalPrime {b p : Ideal A} [hp : p.IsPrime]
    (h : b.IsMinimalPrime p) : (saturation p.primeCompl b).radical = p := by
  refine le_antisymm (hp.radical_le_iff.mpr (saturation_le_of_le_prime h.le)) ?_
  intro y hy
  rw [Ideal.mem_radical_iff]
  by_contra hcon
  simp only [not_exists] at hcon
  have hdisj : Disjoint (b : Set A) ((primeComplPowers p y : Submonoid A) : Set A) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨s, hs, n, hsz⟩
    rw [← hsz] at hz
    exact hcon n (mem_saturation.mpr ⟨s, Ideal.mem_primeCompl_iff.mpr hs, hz⟩)
  obtain ⟨P, hP, hbP, hPdisj⟩ := Ideal.exists_le_prime_disjoint b (primeComplPowers p y) hdisj
  have hPle : P ≤ p := by
    intro z hz
    by_contra hzp
    exact Set.disjoint_left.mp hPdisj hz ⟨z, hzp, 0, by simp⟩
  have hPge : p ≤ P := h.le_of_le ⟨hP, hbP⟩ hPle
  exact Set.disjoint_left.mp hPdisj (hPge hy) ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, 1, by simp⟩

/-- **`S_p(b)` is `p`-primary when `p` is a minimal prime ideal over `b`** (Atiyah–Macdonald,
Chapter 4, Exercise 11). -/
theorem isPrimary_saturation {b p : Ideal A} [hp : p.IsPrime] (h : b.IsMinimalPrime p) :
    (saturation p.primeCompl b).IsPrimary := by
  have hrad := radical_saturation_eq_of_isMinimalPrime h
  have hle := saturation_le_of_le_prime h.le
  rw [Ideal.isPrimary_iff]
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : A) ∈ saturation p.primeCompl b := htop ▸ Submodule.mem_top
    obtain ⟨s, hs, hs1⟩ := mem_saturation.mp h1
    exact (Ideal.mem_primeCompl_iff.mp hs) (h.le (by simpa using hs1))
  · intro x y hxy
    by_cases hx : x ∈ p
    · by_cases hy : y ∈ p
      · exact Or.inr (by rw [hrad]; exact hy)
      · have hyx : y * x ∈ saturation p.primeCompl b := by rwa [mul_comm] at hxy
        exact Or.inl (saturation_mul_mem (Ideal.mem_primeCompl_iff.mpr hy) hyx)
    · refine Or.inr (by rw [hrad]; exact hle (saturation_mul_mem (Ideal.mem_primeCompl_iff.mpr hx) hxy))

/-- Any `p`-primary ideal containing `b` contains `S_p(b)`. -/
theorem saturation_le_of_isPrimary {b p q : Ideal A} [hp : p.IsPrime]
    (hq : q.IsPrimary) (hqr : q.radical = p) (hbq : b ≤ q) :
    saturation p.primeCompl b ≤ q := by
  rintro y hy
  obtain ⟨s, hs, hsy⟩ := mem_saturation.mp hy
  have hsq : s ∉ q.radical := by rw [hqr]; exact Ideal.mem_primeCompl_iff.mp hs
  have hys : y * s ∈ q := by rw [mul_comm]; exact hbq hsy
  exact mem_of_mul_mem_of_notMem_radical hq hsq hys

/-! ## The conditions (L1) and (L2) -/

/-- Atiyah–Macdonald's condition (L1) (Chapter 4, Exercise 17): for every proper ideal `a` and
every prime ideal `p` there is `x ∉ p` such that `S_p(a) = (a : x)`. -/
def ConditionL1 : Prop :=
  ∀ (a : Ideal A), a ≠ ⊤ → ∀ (p : Ideal A) [p.IsPrime],
    ∃ x : A, x ∉ p ∧ saturation p.primeCompl a = a.colon (Ideal.span {x})

/-- Atiyah–Macdonald's condition (L2) (Chapter 4, Exercise 18): for every ideal `a` and every
descending chain `S₁ ⊇ S₂ ⊇ ⋯` of multiplicatively closed subsets of `A`, the saturations
`Sₙ(a)` are eventually constant. -/
def ConditionL2 : Prop :=
  ∀ (a : Ideal A) (S : ℕ → Submonoid A), (∀ n, S (n + 1) ≤ S n) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → saturation (S n) a = saturation (S N) a

/-- `(a : x) = { y | y * x ∈ a }`. -/
theorem mem_colon_singleton {a : Ideal A} {x y : A} :
    y ∈ a.colon (Ideal.span {x}) ↔ y * x ∈ a :=
  Ideal.mem_colon_span_singleton

/-! ## From primary decompositions to (L1) and (L2) -/

/-- A sequence of ideals that is antitone and takes at most the two values `⊤` and `q`
(with `q ≠ ⊤`) is eventually constant. -/
theorem exists_eventually_eq_of_antitone {f : ℕ → Ideal A} {q : Ideal A}
    (hmono : ∀ n, f (n + 1) ≤ f n) (h : ∀ n, f n = ⊤ ∨ f n = q) (hq : q ≠ ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = f N := by
  classical
  by_cases hex : ∃ n, f n = q
  · refine ⟨Nat.find hex, fun n hn => ?_⟩
    have hN : f (Nat.find hex) = q := Nat.find_spec hex
    have hle : f n ≤ f (Nat.find hex) := antitone_nat_of_succ_le hmono hn
    rw [hN] at hle
    rcases h n with h' | h'
    · rw [h'] at hle
      exact absurd (top_le_iff.mp hle) hq
    · rw [h', hN]
  · simp only [not_exists] at hex
    refine ⟨0, fun n _ => ?_⟩
    rcases h n with h' | h'
    · have hle : f n ≤ f 0 := antitone_nat_of_succ_le hmono (Nat.zero_le n)
      rw [h'] at hle
      exact h'.trans (top_le_iff.mp hle).symm
    · exact absurd h' (hex n)

/-- **(i) ⇒ (L2)**: if every ideal has a primary decomposition, then any descending chain of
multiplicatively closed sets gives eventually constant saturations. -/
theorem conditionL2_of_isLasker (h : IsLasker A A) : ConditionL2 (A := A) := by
  intro a S hS
  classical
  obtain ⟨T, hTinf, hTprim⟩ : ∃ T : Finset (Ideal A), T.inf id = a ∧ ∀ q ∈ T, q.IsPrimary :=
    h a
  have hex : ∀ q : Ideal A, q ∈ T →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → saturation (S n) q = saturation (S N) q := by
    intro q hq
    have hqne : q ≠ ⊤ := (Ideal.isPrimary_iff.mp (hTprim q hq)).1
    refine exists_eventually_eq_of_antitone (f := fun n => saturation (S n) q) ?_ ?_ hqne
    · intro n
      exact saturation_le_of_le (hS n) q
    · intro n
      by_cases hd : Disjoint ((S n : Set A)) (q.radical : Set A)
      · exact Or.inr (saturation_primary_eq_self (hTprim q hq) hd)
      · exact Or.inl (saturation_primary_eq_top hd)
  set Nf : Ideal A → ℕ := fun q => if hq : q ∈ T then Classical.choose (hex q hq) else 0 with hNf
  have hNf_spec : ∀ q (hq : q ∈ T) (n : ℕ), Nf q ≤ n →
      saturation (S n) q = saturation (S (Nf q)) q := by
    intro q hq n hn
    have hNfval : Nf q = Classical.choose (hex q hq) := by simp only [hNf, dif_pos hq]
    rw [hNfval] at hn ⊢
    exact Classical.choose_spec (hex q hq) n hn
  refine ⟨T.sup Nf, fun n hn => ?_⟩
  rw [← hTinf, saturation_finsetInf, saturation_finsetInf]
  refine Finset.inf_congr rfl (fun q hq => ?_)
  have h1 : saturation (S n) q = saturation (S (Nf q)) q :=
    hNf_spec q hq n (le_trans (Finset.le_sup hq) hn)
  have h2 : saturation (S (T.sup Nf)) q = saturation (S (Nf q)) q :=
    hNf_spec q hq (T.sup Nf) (Finset.le_sup hq)
  exact h1.trans h2.symm

/-- **(i) ⇒ (L1)**: if every ideal has a primary decomposition, then for every proper ideal `a`
and prime `p` there is `x ∉ p` with `S_p(a) = (a : x)`. -/
theorem conditionL1_of_isLasker (h : IsLasker A A) : ConditionL1 (A := A) := by
  intro a ha p hp
  classical
  haveI := hp
  obtain ⟨T, hTinf, hTprim⟩ : ∃ T : Finset (Ideal A), T.inf id = a ∧ ∀ q ∈ T, q.IsPrimary :=
    h a
  have hex : ∀ q : Ideal A, ¬ q.radical ≤ p → ∃ y : A, y ∈ q.radical ∧ y ∉ p := by
    intro q hq
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact hq (fun z hz => by_contra (fun hzp => hcon z hz hzp))
  set wit : Ideal A → A :=
    fun q => if h : q.radical ≤ p then 1 else Classical.choose (hex q h) with hwit
  have hwit_spec : ∀ q (hq : ¬ q.radical ≤ p), wit q ∈ q.radical ∧ wit q ∉ p := by
    intro q hq
    simp only [hwit, dif_neg hq]
    exact Classical.choose_spec (hex q hq)
  have hwit_one : ∀ q (hq : q.radical ≤ p), wit q = 1 := by
    intro q hq
    simp only [hwit, dif_pos hq]
  set x : A := T.prod wit with hx
  have hone : (1 : A) ∉ p := fun h1 => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)
  have hwit_notMem : ∀ q ∈ T, wit q ∉ p := by
    intro q hq
    by_cases hqp : q.radical ≤ p
    · rw [hwit_one q hqp]; exact hone
    · exact (hwit_spec q hqp).2
  have hprod : ∀ u : Finset (Ideal A), (∀ q ∈ u, wit q ∉ p) → u.prod wit ∉ p := by
    intro u
    induction u using Finset.induction with
    | empty => intro _; simpa using hone
    | insert b s hbs ih =>
      intro hmem
      rw [Finset.prod_insert hbs]
      intro hcon
      rcases hp.mem_or_mem hcon with h' | h'
      · exact hmem b (Finset.mem_insert_self b s) h'
      · exact ih (fun q hq => hmem q (Finset.mem_insert_of_mem hq)) h'
  have hxnotp : x ∉ p := by
    rw [hx]
    exact hprod T hwit_notMem
  have hxrad : ∀ q ∈ T, ¬ q.radical ≤ p → x ∈ q.radical := by
    intro q hq hqp
    have hmem : wit q ∈ q.radical := (hwit_spec q hqp).1
    have hxq : x = wit q * (T.erase q).prod wit := by
      rw [hx]
      exact (Finset.mul_prod_erase T wit hq).symm
    rw [hxq]
    exact q.radical.mul_mem_right _ hmem
  set e : Ideal A → ℕ :=
    fun q => if h : x ∈ q.radical then Classical.choose (Ideal.mem_radical_iff.mp h) else 0 with he
  have he_spec : ∀ q (h : x ∈ q.radical), x ^ (e q) ∈ q := by
    intro q hq
    simp only [he, dif_pos hq]
    exact Classical.choose_spec (Ideal.mem_radical_iff.mp hq)
  have hxN : ∀ q ∈ T, ¬ q.radical ≤ p → x ^ (T.sup e) ∈ q := by
    intro q hq hqp
    have hxe : x ∈ q.radical := hxrad q hq hqp
    have hle : e q ≤ T.sup e := Finset.le_sup hq
    have hfac : x ^ (T.sup e) = x ^ (T.sup e - e q) * x ^ (e q) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hfac]
    exact q.mul_mem_left _ (he_spec q hxe)
  refine ⟨x ^ (T.sup e), pow_notMem_of_notMem hp hxnotp _, ?_⟩
  rw [← hTinf, saturation_finsetInf, Submodule.colon_finsetInf]
  refine Finset.inf_congr rfl (fun q hq => ?_)
  simp only [id_eq]
  by_cases hqp : q.radical ≤ p
  · have hdisj : Disjoint (p.primeCompl : Set A) (q.radical : Set A) := by
      rw [Set.disjoint_left]
      intro s hs hsr
      exact (Ideal.mem_primeCompl_iff.mp hs) (hqp hsr)
    rw [saturation_primary_eq_self (hTprim q hq) hdisj]
    refine le_antisymm ?_ ?_
    · intro r hr
      exact mem_colon_singleton.mpr (q.mul_mem_right (x ^ (T.sup e)) hr)
    · intro r hr
      have hnotrad : x ∉ q.radical := fun hxr => hxnotp (hqp hxr)
      exact mem_of_mul_mem_of_notMem_radical (hTprim q hq)
        (pow_notMem_of_notMem (Ideal.isPrime_radical (hTprim q hq)) hnotrad _)
        (mem_colon_singleton.mp hr)
  · have hdisj : ¬ Disjoint (p.primeCompl : Set A) (q.radical : Set A) := by
      rw [Set.not_disjoint_iff]
      exact ⟨wit q, Ideal.mem_primeCompl_iff.mpr (hwit_spec q hqp).2, (hwit_spec q hqp).1⟩
    rw [saturation_primary_eq_top hdisj, eq_comm, Ideal.eq_top_iff_one, mem_colon_singleton,
      one_mul]
    exact hxN q hq hqp

/-! ## (L1) and (L2) imply that every ideal has a primary decomposition -/

/-- The complement of a prime ideal, as a multiplicatively closed set, with the primality
proof as an explicit argument. -/
def pc (p : Ideal A) (hp : p.IsPrime) : Submonoid A where
  carrier := {y | y ∉ p}
  one_mem' := fun h1 => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)
  mul_mem' := fun hx hy h => (hp.mem_or_mem h).elim hx hy

theorem mem_pc {p : Ideal A} {hp : p.IsPrime} {y : A} : y ∈ pc p hp ↔ y ∉ p := Iff.rfl

theorem pc_eq (p : Ideal A) (hp : p.IsPrime) : pc p hp = p.primeCompl :=
  Submonoid.ext (fun _ => Ideal.mem_primeCompl_iff)

theorem isPrimary_saturation_pc {b p : Ideal A} (hp : p.IsPrime) (h : b.IsMinimalPrime p) :
    (saturation (pc p hp) b).IsPrimary := by
  haveI := hp
  rw [pc_eq]
  exact isPrimary_saturation h

theorem radical_saturation_pc {b p : Ideal A} (hp : p.IsPrime) (h : b.IsMinimalPrime p) :
    (saturation (pc p hp) b).radical = p := by
  haveI := hp
  rw [pc_eq]
  exact radical_saturation_eq_of_isMinimalPrime h

/-- A component of a partial primary decomposition: a primary ideal `q`, its radical `p` and an
element `x ∉ p` with `(a : x) = S_p(a)`. -/
structure Comp (A : Type*) [CommRing A] where
  q : Ideal A
  p : Ideal A
  x : A
  hp : p.IsPrime

/-- The complement of the prime of a component. -/
def Comp.primeCompl {A : Type*} [CommRing A] (z : Comp A) : Submonoid A := pc z.p z.hp

theorem Comp.mem_primeCompl {A : Type*} [CommRing A] {z : Comp A} {y : A} :
    y ∈ z.primeCompl ↔ y ∉ z.p := Iff.rfl

/-- A prime ideal minimal over `b` (junk value for `b = ⊤`). -/
noncomputable def minPrime (b : Ideal A) : Ideal A :=
  if h : b ≠ ⊤ then (Classical.choice (Ideal.nonempty_minimalPrimes h) : b.minimalPrimes).1
  else ⊥

theorem minPrime_mem {b : Ideal A} (h : b ≠ ⊤) : b.IsMinimalPrime (minPrime b) := by
  have hval : minPrime b =
      (Classical.choice (Ideal.nonempty_minimalPrimes h) : b.minimalPrimes).1 := by
    simp only [minPrime, dif_pos h]
  rw [hval]
  exact (Classical.choice (Ideal.nonempty_minimalPrimes h) : b.minimalPrimes).2

/-- The element `x ∉ p` supplied by condition (L1). -/
noncomputable def l1Witness (hL1 : ConditionL1 (A := A)) (b p : Ideal A) (hp : p.IsPrime) : A :=
  if h : b ≠ ⊤ then
    letI := hp
    Classical.choose (hL1 b h p)
  else 0

theorem l1Witness_spec (hL1 : ConditionL1 (A := A)) {b p : Ideal A} (hp : p.IsPrime)
    (hb : b ≠ ⊤) :
    l1Witness hL1 b p hp ∉ p ∧
      saturation (pc p hp) b = b.colon (Ideal.span {l1Witness hL1 b p hp}) := by
  haveI := hp
  have hval : l1Witness hL1 b p hp = Classical.choose (hL1 b hb p) := by
    simp only [l1Witness, dif_pos hb]
  rw [hval]
  obtain ⟨h1, h2⟩ := Classical.choose_spec (hL1 b hb p)
  exact ⟨h1, by rw [pc_eq]; exact h2⟩

/-- A maximal element of a chain-closed set of ideals (Zorn). -/
noncomputable def maxIdeal (S : Set (Ideal A)) : Ideal A :=
  if h : ∃ m, Maximal (· ∈ S) m then Classical.choose h else ⊥

theorem maxIdeal_isMaximal {S : Set (Ideal A)}
    (h : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ≤ ub) :
    Maximal (· ∈ S) (maxIdeal S) := by
  have hex : ∃ m, Maximal (· ∈ S) m := zorn_le₀ S h
  simp only [maxIdeal, dif_pos hex]
  exact Classical.choose_spec hex

/-- The set of ideals among which the next partial component is chosen maximally. -/
def stepSet (a Q q b : Ideal A) (x : A) : Set (Ideal A) :=
  {c : Ideal A | b ⊔ Ideal.span {x} ≤ c ∧ (Q ⊓ q) ⊓ c = a}

/-- **Key step of Exercise 17.** Let `p` be minimal over `b`, `x ∉ p` with
`S_p(b) = (b : x)` and `q = S_p(b)`. Then `q ⊓ (b + (x)) = b`, so the ideal `b + (x)` lies in
the set of ideals along which the partial decomposition can be split. -/
theorem stepSet_mem0 {a Q b : Ideal A} (hL1 : ConditionL1 (A := A)) (hb : b ≠ ⊤)
    (hinv : a = Q ⊓ b) :
    b ⊔ Ideal.span {l1Witness hL1 b (minPrime b) (minPrime_mem hb).isPrime} ∈ stepSet a Q
      (saturation (pc (minPrime b) (minPrime_mem hb).isPrime) b) b
      (l1Witness hL1 b (minPrime b) (minPrime_mem hb).isPrime) := by
  have hmin := minPrime_mem hb
  have hp : (minPrime b).IsPrime := hmin.isPrime
  obtain ⟨hx, hcol2⟩ := l1Witness_spec hL1 hp hb
  have hkey : saturation (pc (minPrime b) hp) b ⊓
      (b ⊔ Ideal.span {l1Witness hL1 b (minPrime b) hp}) = b := by
    refine le_antisymm ?_ (le_inf (le_saturation _ _) le_sup_left)
    intro z hz
    obtain ⟨hzq, hzs⟩ := Ideal.mem_inf.mp hz
    obtain ⟨b₀, hb₀, x', hx', hsum⟩ := Submodule.mem_sup.mp hzs
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton.mp hx'
    rw [mul_comm (l1Witness hL1 b (minPrime b) hp) a'] at hsum
    have hax : a' * l1Witness hL1 b (minPrime b) hp ∈ saturation (pc (minPrime b) hp) b := by
      have h : (b₀ + a' * l1Witness hL1 b (minPrime b) hp) - b₀ ∈
          saturation (pc (minPrime b) hp) b :=
        Submodule.sub_mem _ (hsum ▸ hzq) (le_saturation _ _ hb₀)
      rwa [show (b₀ + a' * l1Witness hL1 b (minPrime b) hp) - b₀ =
        a' * l1Witness hL1 b (minPrime b) hp by ring] at h
    have ha : a' ∈ saturation (pc (minPrime b) hp) b :=
      saturation_mul_mem (mem_pc.mpr hx) (by rwa [mul_comm] at hax)
    rw [hcol2] at ha
    exact hsum ▸ b.add_mem hb₀ (mem_colon_singleton.mp ha)
  refine ⟨le_rfl, ?_⟩
  show (Q ⊓ saturation (pc (minPrime b) hp) b) ⊓ (b ⊔ Ideal.span
    {l1Witness hL1 b (minPrime b) hp}) = a
  rw [inf_assoc, hkey, ← hinv]

/-- The set `stepSet a Q q b x` is closed under unions of chains. -/
theorem stepSet_chain {a Q q b : Ideal A} {x : A}
    (hmem0 : b ⊔ Ideal.span {x} ∈ stepSet a Q q b x) :
    ∀ c ⊆ stepSet a Q q b x, IsChain (· ≤ ·) c → ∃ ub ∈ stepSet a Q q b x,
      ∀ s ∈ c, s ≤ ub := by
  intro c hcS hc
  rcases c.eq_empty_or_nonempty with rfl | hcne
  · exact ⟨_, hmem0, by simp⟩
  · have hsup : b ⊔ Ideal.span {x} ≤ sSup c := by
      obtain ⟨s₀, hs₀⟩ := hcne
      exact le_trans (hcS hs₀).1 (le_sSup hs₀)
    refine ⟨sSup c, ⟨hsup, ?_⟩, fun s hs => le_sSup hs⟩
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzQ, hzs⟩ := Ideal.mem_inf.mp hz
      obtain ⟨s₀, hs₀, hzs₀⟩ := (Submodule.mem_sSup_of_directed hcne hc.directedOn).mp hzs
      exact (hcS hs₀).2 ▸ Ideal.mem_inf.mpr ⟨hzQ, hzs₀⟩
    · exact hmem0.2.symm.le.trans (le_inf inf_le_left (inf_le_right.trans hsup))

/-- One step of the construction of Exercise 17: split off the component `S_p(b)` and pass to a
maximal ideal `c` along which the partial decomposition can still be completed. -/
noncomputable def stepAux (hL1 : ConditionL1 (A := A)) (a Q b : Ideal A) (hb : b ≠ ⊤)
    (u : Finset (Comp A)) : Ideal A × Ideal A × Finset (Comp A) :=
  let hp := (minPrime_mem hb).isPrime
  let x := l1Witness hL1 b (minPrime b) hp
  let q := saturation (pc (minPrime b) hp) b
  (Q ⊓ q, maxIdeal (stepSet a Q q b x), insert ⟨q, minPrime b, x, hp⟩ u)

/-- One step of the construction, with the case `b = ⊤` (nothing left to do) built in. -/
noncomputable def step (hL1 : ConditionL1 (A := A)) (a : Ideal A)
    (st : Ideal A × Ideal A × Finset (Comp A)) : Ideal A × Ideal A × Finset (Comp A) :=
  if hb : st.2.1 = ⊤ then st else stepAux hL1 a st.1 st.2.1 hb st.2.2

theorem stepAux_snd (hL1 : ConditionL1 (A := A)) (a Q b : Ideal A) (hb : b ≠ ⊤)
    (u : Finset (Comp A)) : (stepAux hL1 a Q b hb u).2.1 = maxIdeal (stepSet a Q
      (saturation (pc (minPrime b) (minPrime_mem hb).isPrime) b) b
      (l1Witness hL1 b (minPrime b) (minPrime_mem hb).isPrime)) := rfl

theorem stepAux_thd (hL1 : ConditionL1 (A := A)) (a Q b : Ideal A) (hb : b ≠ ⊤)
    (u : Finset (Comp A)) : (stepAux hL1 a Q b hb u).2.2 = insert ⟨saturation (pc (minPrime b)
      (minPrime_mem hb).isPrime) b, minPrime b, l1Witness hL1 b (minPrime b)
      (minPrime_mem hb).isPrime, (minPrime_mem hb).isPrime⟩ u := rfl

theorem stepAux_fst (hL1 : ConditionL1 (A := A)) (a Q b : Ideal A) (hb : b ≠ ⊤)
    (u : Finset (Comp A)) : (stepAux hL1 a Q b hb u).1 = Q ⊓ saturation (pc (minPrime b)
      (minPrime_mem hb).isPrime) b := rfl

/-- The orbit of the construction, starting from the empty partial decomposition of `a`. -/
noncomputable def orbit (hL1 : ConditionL1 (A := A)) (a : Ideal A) :
    ℕ → Ideal A × Ideal A × Finset (Comp A) :=
  fun n => Nat.rec (⊤, a, ∅) (fun _ st => step hL1 a st) n

/-- The running intersection of the components produced so far. -/
noncomputable def Qn (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) : Ideal A :=
  (orbit hL1 a n).1

/-- The ideal still to be decomposed after `n` steps. -/
noncomputable def bn (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) : Ideal A :=
  (orbit hL1 a n).2.1

/-- The components produced after `n` steps. -/
noncomputable def un (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) : Finset (Comp A) :=
  (orbit hL1 a n).2.2

/-- The invariant of the construction. -/
def GoodSt (a : Ideal A) (st : Ideal A × Ideal A × Finset (Comp A)) : Prop :=
  a = st.1 ⊓ st.2.1 ∧
  st.1 = (st.2.2.image Comp.q).inf id ∧
  ∀ z ∈ st.2.2, z.q.IsPrimary ∧ z.q.radical = z.p ∧ z.x ∈ st.2.1 ∧ z.x ∉ z.p

/-- One step preserves the invariant. -/
theorem stepAux_good (hL1 : ConditionL1 (A := A)) {a Q b : Ideal A} {u : Finset (Comp A)}
    (hb : b ≠ ⊤) (hinv : a = Q ⊓ b) (hQ : Q = (u.image Comp.q).inf id)
    (hu : ∀ z ∈ u, z.q.IsPrimary ∧ z.q.radical = z.p ∧ z.x ∈ b ∧ z.x ∉ z.p) :
    GoodSt a (stepAux hL1 a Q b hb u) := by
  have hmin := minPrime_mem hb
  have hp : (minPrime b).IsPrime := hmin.isPrime
  obtain ⟨hx, -⟩ := l1Witness_spec hL1 hp hb
  have hqprim : (saturation (pc (minPrime b) hp) b).IsPrimary := isPrimary_saturation_pc hp hmin
  have hqrad : (saturation (pc (minPrime b) hp) b).radical = minPrime b :=
    radical_saturation_pc hp hmin
  have hmem0 := stepSet_mem0 hL1 hb hinv
  have hmax := maxIdeal_isMaximal (stepSet_chain hmem0)
  have hfx : (stepAux hL1 a Q b hb u).1 = Q ⊓ saturation (pc (minPrime b) hp) b :=
    stepAux_fst hL1 a Q b hb u
  have hfs : (stepAux hL1 a Q b hb u).2.1 = maxIdeal (stepSet a Q
      (saturation (pc (minPrime b) hp) b) b (l1Witness hL1 b (minPrime b) hp)) :=
    stepAux_snd hL1 a Q b hb u
  have hft : (stepAux hL1 a Q b hb u).2.2 = insert ⟨saturation (pc (minPrime b) hp) b,
      minPrime b, l1Witness hL1 b (minPrime b) hp, hp⟩ u := stepAux_thd hL1 a Q b hb u
  refine ⟨?_, ?_, ?_⟩
  · rw [hfx, hfs, hmax.1.2]
  · rw [hfx, hft, Finset.image_insert, Finset.inf_insert, id_eq, ← hQ]
    exact inf_comm _ _
  · intro z hz
    have hz' : z = ⟨saturation (pc (minPrime b) hp) b, minPrime b,
        l1Witness hL1 b (minPrime b) hp, hp⟩ ∨ z ∈ u := by
      rw [hft, Finset.mem_insert] at hz
      exact hz
    rcases hz' with rfl | hz
    · refine ⟨hqprim, hqrad, ?_, hx⟩
      rw [hfs]
      exact hmax.1.1 (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
    · obtain ⟨h1, h2, h3, h4⟩ := hu z hz
      refine ⟨h1, h2, ?_, h4⟩
      rw [hfs]
      exact hmax.1.1 (Submodule.mem_sup_left h3)

/-- The invariant holds along the whole orbit. -/
theorem goodSt_orbit (hL1 : ConditionL1 (A := A)) (a : Ideal A) :
    ∀ n, GoodSt a (orbit hL1 a n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [orbit]
    · simp [orbit]
    · intro z hz
      simp [orbit] at hz
  | succ k ih =>
    obtain ⟨hinv, hQ, hu⟩ := ih
    by_cases hb : (orbit hL1 a k).2.1 = ⊤
    · have hsame : orbit hL1 a (k + 1) = orbit hL1 a k := by
        show step hL1 a (orbit hL1 a k) = orbit hL1 a k
        simp only [step, dif_pos hb]
      rw [hsame]
      exact ⟨hinv, hQ, hu⟩
    · have hstep : orbit hL1 a (k + 1) = stepAux hL1 a (orbit hL1 a k).1
          (orbit hL1 a k).2.1 hb (orbit hL1 a k).2.2 := by
        show step hL1 a (orbit hL1 a k) = _
        simp only [step, dif_neg hb]
      rw [hstep]
      exact stepAux_good hL1 hb hinv hQ hu

/-! ## Stage lemmas about the orbit -/

theorem orbit_succ_eq (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    orbit hL1 a (n + 1) = stepAux hL1 a (orbit hL1 a n).1 (orbit hL1 a n).2.1 hb
      (orbit hL1 a n).2.2 := by
  show step hL1 a (orbit hL1 a n) = _
  simp only [step, dif_neg hb]

/-- At a stage where something remains to be done, the next ideal is maximal for the
constraint of the construction. -/
theorem stage_max (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    Maximal (· ∈ stepSet a (orbit hL1 a n).1
      (saturation (pc (minPrime (orbit hL1 a n).2.1) (minPrime_mem hb).isPrime)
        (orbit hL1 a n).2.1) (orbit hL1 a n).2.1
      (l1Witness hL1 (orbit hL1 a n).2.1 (minPrime (orbit hL1 a n).2.1)
        (minPrime_mem hb).isPrime)) ((orbit hL1 a (n + 1)).2.1) := by
  have hinv := (goodSt_orbit hL1 a n).1
  have hmem0 := stepSet_mem0 hL1 (Q := (orbit hL1 a n).1) (b := (orbit hL1 a n).2.1) hb hinv
  have hmax := maxIdeal_isMaximal (stepSet_chain hmem0)
  have hbnext : (orbit hL1 a (n + 1)).2.1 = maxIdeal (stepSet a (orbit hL1 a n).1
      (saturation (pc (minPrime (orbit hL1 a n).2.1) (minPrime_mem hb).isPrime)
        (orbit hL1 a n).2.1) (orbit hL1 a n).2.1
      (l1Witness hL1 (orbit hL1 a n).2.1 (minPrime (orbit hL1 a n).2.1)
        (minPrime_mem hb).isPrime)) := by
    rw [orbit_succ_eq hL1 a n hb]
    exact stepAux_snd hL1 a _ _ hb _
  rw [hbnext]
  exact hmax

theorem stage_Qn (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    (orbit hL1 a (n + 1)).1 = (orbit hL1 a n).1 ⊓
      saturation (pc (minPrime (orbit hL1 a n).2.1) (minPrime_mem hb).isPrime)
        (orbit hL1 a n).2.1 := by
  rw [orbit_succ_eq hL1 a n hb]
  exact stepAux_fst hL1 a _ _ hb _

theorem stage_b_le (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    (orbit hL1 a n).2.1 ≤ (orbit hL1 a (n + 1)).2.1 :=
  le_trans le_sup_left (stage_max hL1 a n hb).1.1

theorem stage_x_mem (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    l1Witness hL1 (orbit hL1 a n).2.1 (minPrime (orbit hL1 a n).2.1)
      (minPrime_mem hb).isPrime ∈ (orbit hL1 a (n + 1)).2.1 :=
  (stage_max hL1 a n hb).1.1 (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem stage_x_notMem (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    l1Witness hL1 (orbit hL1 a n).2.1 (minPrime (orbit hL1 a n).2.1)
      (minPrime_mem hb).isPrime ∉ minPrime (orbit hL1 a n).2.1 :=
  (l1Witness_spec hL1 (minPrime_mem hb).isPrime hb).1

theorem stage_minPrime_le (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ)
    (hb : (orbit hL1 a n).2.1 ≠ ⊤) :
    (orbit hL1 a n).2.1 ≤ minPrime (orbit hL1 a n).2.1 :=
  (minPrime_mem hb).le

theorem un_subset (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) :
    (orbit hL1 a n).2.2 ⊆ (orbit hL1 a (n + 1)).2.2 := by
  by_cases hb : (orbit hL1 a n).2.1 = ⊤
  · have hsame : orbit hL1 a (n + 1) = orbit hL1 a n := by
      show step hL1 a (orbit hL1 a n) = orbit hL1 a n
      simp only [step, dif_pos hb]
    rw [hsame]
  · rw [orbit_succ_eq hL1 a n hb, stepAux_thd]
    exact Finset.subset_insert _ _

/-! ## The multiplicative sets attached to the construction -/

/-- The multiplicative set generated by `A - p` for all primes `p` of the components
produced so far, i.e. `A - (p₁ ∪ ⋯ ∪ pₙ)`. -/
noncomputable def Sfun (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) : Submonoid A :=
  (orbit hL1 a n).2.2.inf Comp.primeCompl

theorem mem_Sfun {hL1 : ConditionL1 (A := A)} {a : Ideal A} {n : ℕ} {y : A} :
    y ∈ Sfun hL1 a n ↔ ∀ z ∈ (orbit hL1 a n).2.2, y ∉ z.p := by
  rw [Sfun, Finset.inf_eq_iInf]
  constructor
  · intro h z hz
    exact Comp.mem_primeCompl.mp (Submonoid.mem_iInf.mp (Submonoid.mem_iInf.mp h z) hz)
  · intro h
    exact Submonoid.mem_iInf.mpr (fun z =>
      Submonoid.mem_iInf.mpr (fun hz => Comp.mem_primeCompl.mpr (h z hz)))

theorem Sfun_antitone (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) :
    Sfun hL1 a (n + 1) ≤ Sfun hL1 a n := by
  intro y hy
  rw [mem_Sfun] at hy ⊢
  exact fun z hz => hy z (un_subset hL1 a n hz)

/-- Prime avoidance: at every stage there is an element of the remaining ideal outside all the
primes produced so far. -/
theorem exists_mem_Sfun (hL1 : ConditionL1 (A := A)) (a : Ideal A) (n : ℕ) :
    ∃ y ∈ (orbit hL1 a n).2.1, y ∈ Sfun hL1 a n := by
  classical
  obtain ⟨-, -, hu⟩ := goodSt_orbit hL1 a n
  set P : Finset (Ideal A) := (orbit hL1 a n).2.2.image Comp.p with hP
  have hprime : ∀ p ∈ P, p.IsPrime := by
    intro p hp
    rw [hP, Finset.mem_image] at hp
    obtain ⟨z, -, rfl⟩ := hp
    exact z.hp
  have hnotle : ∀ p ∈ P, ¬(orbit hL1 a n).2.1 ≤ p := by
    intro p hp hle
    rw [hP, Finset.mem_image] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact (hu z hz).2.2.2 (hle (hu z hz).2.2.1)
  by_contra hcon
  have hsub : ((orbit hL1 a n).2.1 : Set A) ⊆ ⋃ p ∈ (P : Set (Ideal A)), (p : Set A) := by
    intro y hy
    by_contra hy'
    exact hcon ⟨y, hy, by
      rw [mem_Sfun]
      intro z hz hzp
      exact hy' (Set.mem_biUnion (by rw [hP]; exact Finset.mem_image_of_mem _ hz) hzp)⟩
  obtain ⟨p, hpP, hle⟩ :=
    (Ideal.subset_union_prime (a := ⊤) (b := ⊤) (fun i hi _ _ => hprime i hi)).mp hsub
  exact hnotle p hpP hle

/-- If `a = Q ⊓ b` where `Q` is the intersection of components that are fixed by `S` and `b`
saturates to the whole ring, then `S(a) = Q`. -/
theorem saturation_eq_inf_of_components {S : Submonoid A} {a Q b : Ideal A}
    {u : Finset (Comp A)} (hinv : a = Q ⊓ b) (hQ : Q = (u.image Comp.q).inf id)
    (hcomp : ∀ z ∈ u, saturation S z.q = z.q) (htop : saturation S b = ⊤) :
    saturation S a = Q := by
  rw [hinv, ← saturation_inf, htop, inf_top_eq, hQ, saturation_finsetInf]
  refine Finset.inf_congr rfl (fun q hq => ?_)
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
  simpa using hcomp z hz

/-- The saturation of `a` with respect to the multiplicative set of stage `n` is the running
intersection of the components. -/
theorem saturation_Sfun_eq (hL1 : ConditionL1 (A := A)) (a : Ideal A) :
    ∀ n, saturation (Sfun hL1 a n) a = (orbit hL1 a n).1 := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hS : Sfun hL1 a 0 = ⊤ := by
      rw [Sfun]
      rfl
    rw [hS, show (orbit hL1 a 0).1 = ⊤ from rfl]
    exact (saturation_eq_top_iff _ _).mpr ⟨0, Submonoid.mem_top 0, a.zero_mem⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hinv, hQ, hu⟩ := goodSt_orbit hL1 a (m + 1)
    have hcomp : ∀ z ∈ (orbit hL1 a (m + 1)).2.2,
        saturation (Sfun hL1 a (m + 1)) z.q = z.q := by
      intro z hz
      refine saturation_primary_eq_self (hu z hz).1 ?_
      rw [Set.disjoint_left]
      intro s hs hsr
      change s ∈ Sfun hL1 a (m + 1) at hs
      rw [mem_Sfun] at hs
      exact (hs z hz) ((hu z hz).2.1 ▸ hsr)
    have htop : saturation (Sfun hL1 a (m + 1)) (orbit hL1 a (m + 1)).2.1 = ⊤ := by
      refine (saturation_eq_top_iff _ _).mpr ?_
      obtain ⟨y, hy, hys⟩ := exists_mem_Sfun hL1 a (m + 1)
      exact ⟨y, hys, hy⟩
    exact saturation_eq_inf_of_components hinv hQ hcomp htop

/-! ## Termination of the construction using (L2) -/

/-- **(ii) ⇒ (i)**: a ring satisfying (L1) and (L2) has primary decompositions for all ideals. -/
theorem isLasker_of_conditions (hL1 : ConditionL1 (A := A)) (hL2 : ConditionL2 (A := A)) :
    IsLasker A A := by
  intro a
  classical
  obtain ⟨N, hN⟩ := hL2 a (Sfun hL1 a) (fun n => Sfun_antitone hL1 a n)
  have hQstab : ∀ n, N ≤ n → (orbit hL1 a n).1 = (orbit hL1 a N).1 := by
    intro n hn
    rw [← saturation_Sfun_eq hL1 a n, ← saturation_Sfun_eq hL1 a N]
    exact hN n hn
  by_cases hbN : (orbit hL1 a N).2.1 = ⊤
  · obtain ⟨hinv, hQ, hu⟩ := goodSt_orbit hL1 a N
    have hNa : (orbit hL1 a N).1 = a := by
      conv_rhs => rw [hinv]
      rw [hbN, inf_top_eq]
    refine ⟨(orbit hL1 a N).2.2.image Comp.q, ?_, ?_⟩
    · rw [← hQ]; exact hNa
    · intro q hq
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      exact (hu z hz).1
  · by_cases hbN1 : (orbit hL1 a (N + 1)).2.1 = ⊤
    · obtain ⟨hinv, hQ, hu⟩ := goodSt_orbit hL1 a (N + 1)
      have hN1a : (orbit hL1 a (N + 1)).1 = a := by
        conv_rhs => rw [hinv]
        rw [hbN1, inf_top_eq]
      refine ⟨(orbit hL1 a (N + 1)).2.2.image Comp.q, ?_, ?_⟩
      · rw [← hQ]; exact hN1a
      · intro q hq
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
        exact (hu z hz).1
    · exfalso
      have hQ1 : (orbit hL1 a (N + 1)).1 = (orbit hL1 a N).1 := hQstab (N + 1) (Nat.le_succ N)
      have hQ2 : (orbit hL1 a (N + 2)).1 = (orbit hL1 a N).1 := hQstab (N + 2) (by omega)
      have hmaxN := stage_max hL1 a N hbN
      have hbNle : (orbit hL1 a N).2.1 ≤ (orbit hL1 a (N + 1)).2.1 := stage_b_le hL1 a N hbN
      have hbN1le : (orbit hL1 a (N + 1)).2.1 ≤ (orbit hL1 a (N + 2)).2.1 :=
        stage_b_le hL1 a (N + 1) hbN1
      have hxNmem : l1Witness hL1 (orbit hL1 a N).2.1 (minPrime (orbit hL1 a N).2.1)
          (minPrime_mem hbN).isPrime ∈ (orbit hL1 a (N + 1)).2.1 := stage_x_mem hL1 a N hbN
      have hxN1mem : l1Witness hL1 (orbit hL1 a (N + 1)).2.1
          (minPrime (orbit hL1 a (N + 1)).2.1) (minPrime_mem hbN1).isPrime ∈
          (orbit hL1 a (N + 2)).2.1 := stage_x_mem hL1 a (N + 1) hbN1
      have hxN1not : l1Witness hL1 (orbit hL1 a (N + 1)).2.1
          (minPrime (orbit hL1 a (N + 1)).2.1) (minPrime_mem hbN1).isPrime ∉
          (orbit hL1 a (N + 1)).2.1 :=
        fun hmem => stage_x_notMem hL1 a (N + 1) hbN1
          ((stage_minPrime_le hL1 a (N + 1) hbN1) hmem)
      obtain ⟨hinv2, -, -⟩ := goodSt_orbit hL1 a (N + 2)
      have hmem : (orbit hL1 a (N + 2)).2.1 ∈ stepSet a (orbit hL1 a N).1
          (saturation (pc (minPrime (orbit hL1 a N).2.1) (minPrime_mem hbN).isPrime)
            (orbit hL1 a N).2.1) (orbit hL1 a N).2.1
          (l1Witness hL1 (orbit hL1 a N).2.1 (minPrime (orbit hL1 a N).2.1)
            (minPrime_mem hbN).isPrime) := by
        refine ⟨sup_le (le_trans hbNle hbN1le) (Ideal.span_le.mpr ?_), ?_⟩
        · intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hbN1le hxNmem
        · have hQN1 : (orbit hL1 a N).1 ⊓
              saturation (pc (minPrime (orbit hL1 a N).2.1) (minPrime_mem hbN).isPrime)
                (orbit hL1 a N).2.1 = (orbit hL1 a (N + 1)).1 :=
            (stage_Qn hL1 a N hbN).symm
          rw [hQN1, hQ1, ← hQ2, ← hinv2]
      have hle := hmaxN.2 hmem hbN1le
      exact hxN1not (hle hxN1mem)

/-! ## Atiyah–Macdonald, Chapter 4, Exercise 18 -/

/-- Every ideal of `A` has a primary decomposition: `a` is a finite intersection of primary
ideals.  The intersection may be empty (giving `⊤`), so that the unit ideal is covered, as in
the book. -/
def HasPrimaryDecompositions (A : Type*) [CommRing A] : Prop :=
  ∀ a : Ideal A, ∃ T : Finset (Ideal A), T.inf id = a ∧ ∀ q ∈ T, q.IsPrimary

theorem hasPrimaryDecompositions_iff_isLasker :
    HasPrimaryDecompositions A ↔ IsLasker A A := Iff.rfl

/-- **(i) ⇒ (ii)**: in a ring in which every ideal has a primary decomposition, condition (L1)
of Chapter 4, Exercise 17 and condition (L2) of Chapter 4, Exercise 18 both hold. -/
theorem conditions_of_hasPrimaryDecompositions (h : HasPrimaryDecompositions A) :
    ConditionL1 (A := A) ∧ ConditionL2 (A := A) :=
  ⟨conditionL1_of_isLasker h, conditionL2_of_isLasker h⟩

/-- **(ii) ⇒ (i)**: a ring satisfying (L1) and (L2) has a primary decomposition for every
ideal. -/
theorem hasPrimaryDecompositions_of_conditions
    (h : ConditionL1 (A := A) ∧ ConditionL2 (A := A)) : HasPrimaryDecompositions A :=
  isLasker_of_conditions h.1 h.2

/-- **Atiyah–Macdonald, Chapter 4, Exercise 18.**  For a ring `A` the following are equivalent:

(i) every ideal of `A` has a primary decomposition;
(ii) `A` satisfies (L1) (Chapter 4, Exercise 17) and (L2) (Chapter 4, Exercise 18). -/
theorem solution :
    HasPrimaryDecompositions A ↔ ConditionL1 (A := A) ∧ ConditionL2 (A := A) :=
  ⟨conditions_of_hasPrimaryDecompositions, hasPrimaryDecompositions_of_conditions⟩

/-- Exercise 4.18 in terms of Mathlib's `IsLasker` (the statement that every submodule, hence
every ideal of `A`, is a finite intersection of primary submodules). -/
theorem solution_isLasker :
    IsLasker A A ↔ ConditionL1 (A := A) ∧ ConditionL2 (A := A) :=
  ⟨fun h => ⟨conditionL1_of_isLasker h, conditionL2_of_isLasker h⟩,
    fun h => isLasker_of_conditions h.1 h.2⟩

/-- Sanity check: Noetherian rings satisfy (L1) and (L2) (by the Lasker–Noether theorem, which
Mathlib provides as `Submodule.isLasker`).  So condition (ii) is not vacuous. -/
theorem conditions_of_isNoetherianRing [IsNoetherianRing A] :
    ConditionL1 (A := A) ∧ ConditionL2 (A := A) :=
  ⟨conditionL1_of_isLasker (Submodule.isLasker A A),
    conditionL2_of_isLasker (Submodule.isLasker A A)⟩

/-- Sanity check: `ℤ` satisfies (L1) and (L2). -/
example : ConditionL1 (A := ℤ) ∧ ConditionL2 (A := ℤ) :=
  conditions_of_isNoetherianRing

/-- Sanity check: a field satisfies (L1) and (L2). -/
example (K : Type*) [Field K] : ConditionL1 (A := K) ∧ ConditionL2 (A := K) :=
  conditions_of_isNoetherianRing

#print axioms AtiyahMcdonald69.Ex_4_18.mem_saturation
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_inf
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_finsetInf
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_primary_eq_self
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_primary_eq_top
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_eq_top_iff
#print axioms AtiyahMcdonald69.Ex_4_18.isPrimary_saturation
#print axioms AtiyahMcdonald69.Ex_4_18.radical_saturation_eq_of_isMinimalPrime
#print axioms AtiyahMcdonald69.Ex_4_18.conditionL1_of_isLasker
#print axioms AtiyahMcdonald69.Ex_4_18.conditionL2_of_isLasker
#print axioms AtiyahMcdonald69.Ex_4_18.stepSet_mem0
#print axioms AtiyahMcdonald69.Ex_4_18.stepAux_good
#print axioms AtiyahMcdonald69.Ex_4_18.goodSt_orbit
#print axioms AtiyahMcdonald69.Ex_4_18.stage_max
#print axioms AtiyahMcdonald69.Ex_4_18.exists_mem_Sfun
#print axioms AtiyahMcdonald69.Ex_4_18.saturation_Sfun_eq
#print axioms AtiyahMcdonald69.Ex_4_18.isLasker_of_conditions
#print axioms AtiyahMcdonald69.Ex_4_18.conditions_of_hasPrimaryDecompositions
#print axioms AtiyahMcdonald69.Ex_4_18.hasPrimaryDecompositions_of_conditions
#print axioms AtiyahMcdonald69.Ex_4_18.solution
#print axioms AtiyahMcdonald69.Ex_4_18.solution_isLasker
#print axioms AtiyahMcdonald69.Ex_4_18.conditions_of_isNoetherianRing

end AtiyahMcdonald69.Ex_4_18
