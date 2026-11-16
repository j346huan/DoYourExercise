/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 4, Exercise 4.13.

The book's statement (Exercises to Chapter 4, no. 13):

  Let `A` be a ring and `𝔭` a prime ideal of `A`. The `n`-th symbolic power of `𝔭` is defined to
  be the ideal (in the notation of Exercise 12) `𝔭⁽ⁿ⁾ = S_𝔭(𝔭ⁿ)`, where `S_𝔭 = A - 𝔭`. Show that

  (i)   `𝔭⁽ⁿ⁾` is a `𝔭`-primary ideal;
  (ii)  if `𝔭ⁿ` has a primary decomposition, then `𝔭⁽ⁿ⁾` is its `𝔭`-primary component;
  (iii) if `𝔭⁽ᵐ⁾𝔭⁽ⁿ⁾` has a primary decomposition, then `𝔭⁽ᵐ⁺ⁿ⁾` is its `𝔭`-primary component;
  (iv)  `𝔭⁽ⁿ⁾ = 𝔭ⁿ` if and only if `𝔭ⁿ` is `𝔭`-primary.

Here `S_𝔭(I)` is the saturation of Exercise 4.12, i.e. the contraction of `I·A_𝔭` to `A`; we model
it as `sat 𝔭 I = (I.map (algebraMap A A_𝔭)).under A`, so that `𝔭⁽ⁿ⁾ = sat 𝔭 (𝔭ⁿ)`.

Remarks on the hypotheses of (ii) and (iii) (see also the last section of this file): "the
`𝔭`-primary component" is only well defined for a *minimal* primary decomposition, and the part of
minimality that is used (and that is necessary, see `component_not_unique`) is that the radicals of
the components are pairwise distinct.  No Noetherian hypothesis is needed: (ii) and (iii) assume a
decomposition of the relevant ideal instead.  This loses no generality: from an arbitrary primary
decomposition one obtains a minimal one by dropping redundant components and replacing components
with equal radical by their (primary, by `Ideal.IsPrimary.inf`) intersection.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_4_13

open Ideal

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false

variable {A : Type*} [CommRing A]

/-! ### Saturation at the complement of a prime ideal, and symbolic powers -/

/-- The saturation `S_𝔭(I)` of Exercise 4.12: the contraction of `I · A_𝔭` to `A`, i.e.
`I·A_𝔭 ∩ A`. -/
noncomputable def sat (p : Ideal A) [p.IsPrime] (I : Ideal A) : Ideal A :=
  (I.map (algebraMap A (Localization.AtPrime p))).under A

/-- The `n`-th symbolic power `𝔭⁽ⁿ⁾ = S_𝔭(𝔭ⁿ)` of a prime ideal `𝔭`. -/
noncomputable def symbolicPower (p : Ideal A) [p.IsPrime] (n : ℕ) : Ideal A := sat p (p ^ n)

variable (p : Ideal A) [hp : p.IsPrime]

theorem sat_def (I : Ideal A) :
    sat p I = (I.map (algebraMap A (Localization.AtPrime p))).under A := rfl

theorem symbolicPower_def (n : ℕ) :
    symbolicPower p n = (Ideal.map (algebraMap A (Localization.AtPrime p)) (p ^ n)).under A := rfl

/-! ### Elementary properties of the saturation -/

theorem sat_mono : Monotone (sat p) := by
  intro I J h x hx
  rw [sat_def, Ideal.under_def, Ideal.mem_comap] at hx ⊢
  exact Ideal.map_mono h hx

theorem le_sat (I : Ideal A) : I ≤ sat p I := by
  intro x hx
  rw [sat_def, Ideal.under_def, Ideal.mem_comap]
  exact Ideal.mem_map_of_mem _ hx

theorem sat_top : sat p (⊤ : Ideal A) = ⊤ := by
  rw [sat_def, Ideal.map_top, Ideal.under_def, Ideal.comap_top]

theorem sat_inf (I J : Ideal A) : sat p (I ⊓ J) = sat p I ⊓ sat p J := by
  simp only [sat, Ideal.under_def,
    IsLocalization.map_inf p.primeCompl (Localization.AtPrime p) I J, Ideal.comap_inf]

/-- The saturation of an ideal that is not contained in `𝔭` is the whole ring: it contains an
element of `A - 𝔭`, which becomes a unit in `A_𝔭`. -/
theorem sat_eq_top_of_not_le {q : Ideal A} (h : ¬ q ≤ p) : sat p q = ⊤ := by
  obtain ⟨s, hsq, hsp⟩ := Set.not_subset.1 h
  have hunit : IsUnit (algebraMap A (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p)
      (show p.primeCompl from ⟨s, by simpa using hsp⟩)
  have htop : q.map (algebraMap A (Localization.AtPrime p)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsq) hunit
  rw [sat_def, htop, Ideal.under_def, Ideal.comap_top]

/-- A `𝔭`-primary ideal is saturated with respect to `A - 𝔭`. -/
theorem sat_eq_self_of_isPrimary {q : Ideal A} (hq : q.IsPrimary) (hqp : q ≤ p) :
    sat p q = q := by
  rw [sat_def,
    IsLocalization.under_map_of_isPrimary_disjoint p.primeCompl (Localization.AtPrime p) hq
      (Set.disjoint_left.mpr fun x hx hx' => hx (hqp hx'))]

/-- **Saturation of a primary decomposition.**  The saturation of an intersection of primary ideals
is the intersection of the components not contained in `𝔭` (Atiyah–Macdonald, Lemma 4.4 /
Proposition 4.9, in the special case of the complement of a prime ideal). -/
theorem sat_finsetInf_of_isPrimary {s : Finset (Ideal A)}
    (hprim : ∀ q ∈ s, q.IsPrimary) :
    sat p (s.inf (fun q => q)) = s.inf (fun q => if q ≤ p then q else ⊤) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sat_top]
  | insert a s ha ih =>
    have hprim' : ∀ q ∈ s, q.IsPrimary := fun q hq => hprim q (Finset.mem_insert_of_mem hq)
    have hmain := ih hprim'
    have hprim_a : a.IsPrimary := hprim a (Finset.mem_insert_self a s)
    by_cases hle : a ≤ p
    · rw [Finset.inf_insert, sat_inf, hmain, Finset.inf_insert, if_pos hle,
        sat_eq_self_of_isPrimary p hprim_a hle]
    · rw [Finset.inf_insert, sat_inf, hmain, Finset.inf_insert, if_neg hle,
        sat_eq_top_of_not_le p hle]

/-! ### Part (i): symbolic powers of a prime ideal are primary -/

theorem isPrimary_pow_of_isMaximal {m : Ideal A} (hm : m.IsMaximal) {n : ℕ} (hn : n ≠ 0) :
    (m ^ n).IsPrimary := by
  refine Ideal.isPrimary_of_isMaximal_radical ?_
  rwa [Ideal.radical_pow _ hn, hm.isPrime.radical]

/-- **(i)** `𝔭⁽ⁿ⁾` is a `𝔭`-primary ideal. -/
theorem isPrimary_symbolicPower {n : ℕ} (hn : n ≠ 0) : (symbolicPower p n).IsPrimary := by
  have hmax : (p.map (algebraMap A (Localization.AtPrime p))).IsMaximal := inferInstance
  have h : ((p.map (algebraMap A (Localization.AtPrime p))) ^ n).IsPrimary :=
    isPrimary_pow_of_isMaximal hmax hn
  have h' := h.comap (algebraMap A (Localization.AtPrime p))
  simpa [symbolicPower_def, sat_def, Ideal.under_def, Ideal.map_pow] using h'

/-- The radical of `𝔭⁽ⁿ⁾` is `𝔭`. -/
theorem radical_symbolicPower {n : ℕ} (hn : n ≠ 0) : (symbolicPower p n).radical = p := by
  have hmax : (p.map (algebraMap A (Localization.AtPrime p))).IsMaximal := inferInstance
  rw [symbolicPower_def, Ideal.under_def, ← Ideal.comap_radical, Ideal.map_pow,
    Ideal.radical_pow _ hn, hmax.isPrime.radical]
  exact IsLocalization.under_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p) hp
    (Set.disjoint_left.mpr fun _ hx hx' => hx hx')

/-- **(i)**, restated: `𝔭⁽ⁿ⁾` is `𝔭`-primary, i.e. primary with radical `𝔭`. -/
theorem isPrimary_symbolicPower' {n : ℕ} (hn : n ≠ 0) :
    (symbolicPower p n).IsPrimary ∧ (symbolicPower p n).radical = p :=
  ⟨isPrimary_symbolicPower p hn, radical_symbolicPower p hn⟩

/-! ### Minimal primary decompositions and their components -/

/-- `s` is a minimal primary decomposition of `I`: `s` is a finite set of primary ideals with
pairwise distinct radicals whose intersection is `I`.  (Distinctness of the radicals is the part of
minimality that is used below; it is also necessary, see `component_not_unique`.) -/
structure IsMinimalPrimaryDecomposition (I : Ideal A) (s : Finset (Ideal A)) : Prop where
  isPrimary : ∀ q ∈ s, q.IsPrimary
  radicals_distinct : ∀ q ∈ s, ∀ q' ∈ s, q.radical = q'.radical → q = q'
  inf_eq : s.inf (fun q => q) = I

namespace IsMinimalPrimaryDecomposition

variable {p} {I : Ideal A} {s : Finset (Ideal A)}

/-- The `𝔭`-primary component of a minimal primary decomposition of `I` is the saturation
`S_𝔭(I)`, whenever `r(I) = 𝔭` and `S_𝔭(I) ≠ A`.  This is the common core of parts (ii) and (iii). -/
theorem exists_component_eq_sat (h : IsMinimalPrimaryDecomposition I s) (hr : I.radical = p)
    (hne : sat p I ≠ ⊤) : ∃ q ∈ s, q.radical = p ∧ q = sat p I := by
  classical
  have key : sat p I = s.inf (fun q => if q ≤ p then q else ⊤) := by
    rw [← h.inf_eq, sat_finsetInf_of_isPrimary p h.isPrimary]
  -- some component is contained in `𝔭`
  have htop : ∀ t : Finset (Ideal A), (∀ q ∈ t, ¬ q ≤ p) →
      t.inf (fun q => if q ≤ p then q else ⊤) = ⊤ := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      intro ht
      rw [Finset.inf_insert, if_neg (ht a (Finset.mem_insert_self a t)),
        ih (fun q hq => ht q (Finset.mem_insert_of_mem hq))]
      simp
  have hex : ∃ q ∈ s, q ≤ p := by
    by_contra hcon
    rw [not_exists] at hcon
    exact hne (by rw [key]; exact htop s fun q hq hqp => hcon q ⟨hq, hqp⟩)
  -- the radical of a component contained in `𝔭` is `𝔭`
  have hrad_of : ∀ q ∈ s, q ≤ p → q.radical = p := by
    intro q hqs hqp
    refine le_antisymm ?_ ?_
    · rw [← hp.radical]
      exact Ideal.radical_mono hqp
    · rw [← hr]
      exact Ideal.radical_mono (h.inf_eq.symm.le.trans (Finset.inf_le hqs))
  obtain ⟨q₀, hq₀s, hq₀p⟩ := hex
  refine ⟨q₀, hq₀s, hrad_of q₀ hq₀s hq₀p, ?_⟩
  rw [key]
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf fun q hq => ?_
    by_cases hqp : q ≤ p
    · rw [if_pos hqp,
        ← h.radicals_distinct q hq q₀ hq₀s (by rw [hrad_of q hq hqp, hrad_of q₀ hq₀s hq₀p])]
    · rw [if_neg hqp]
      exact le_top
  · calc s.inf (fun q => if q ≤ p then q else ⊤) ≤ (if q₀ ≤ p then q₀ else ⊤) :=
        Finset.inf_le hq₀s
      _ = q₀ := if_pos hq₀p

end IsMinimalPrimaryDecomposition

/-! ### Parts (ii) and (iii) -/

/-- **(ii)** If `𝔭ⁿ` has a minimal primary decomposition `s`, then `𝔭⁽ⁿ⁾` is its `𝔭`-primary
component. -/
theorem symbolicPower_eq_component {n : ℕ} (hn : n ≠ 0) {s : Finset (Ideal A)}
    (h : IsMinimalPrimaryDecomposition (p ^ n) s) :
    ∃ q ∈ s, q.radical = p ∧ q = symbolicPower p n := by
  have hr : (p ^ n).radical = p := by rw [Ideal.radical_pow _ hn, hp.radical]
  have hne : sat p (p ^ n) ≠ ⊤ := (isPrimary_symbolicPower p hn).1
  have h' := h.exists_component_eq_sat (p := p) hr hne
  simpa [symbolicPower] using h'

/-- The uniqueness form of (ii): every component of a minimal primary decomposition of `𝔭ⁿ` whose
radical is `𝔭` is the symbolic power `𝔭⁽ⁿ⁾`. -/
theorem eq_symbolicPower_of_mem {n : ℕ} (hn : n ≠ 0) {s : Finset (Ideal A)}
    (h : IsMinimalPrimaryDecomposition (p ^ n) s) {q : Ideal A} (hq : q ∈ s)
    (hqr : q.radical = p) : q = symbolicPower p n := by
  have hr : (p ^ n).radical = p := by rw [Ideal.radical_pow _ hn, hp.radical]
  obtain ⟨q₀, hq₀, hq₀r, hq₀eq⟩ :=
    h.exists_component_eq_sat (p := p) hr (isPrimary_symbolicPower p hn).1
  show q = sat p (p ^ n)
  rw [← hq₀eq, h.radicals_distinct q hq q₀ hq₀ (by rw [hqr, hq₀r])]

/-- **Auxiliary computation for (iii).**  The ideals `𝔭⁽ᵐ⁾𝔭⁽ⁿ⁾` and `𝔭ᵐ⁺ⁿ` have the same
extension to `A_𝔭`, hence the same saturation. -/
theorem sat_symbolicPower_mul (m n : ℕ) :
    sat p (symbolicPower p m * symbolicPower p n) = symbolicPower p (m + n) := by
  have h1 : (symbolicPower p m).map (algebraMap A (Localization.AtPrime p))
      = (p ^ m).map (algebraMap A (Localization.AtPrime p)) := by
    rw [symbolicPower_def]
    exact IsLocalization.map_under p.primeCompl (Localization.AtPrime p) _
  have h2 : (symbolicPower p n).map (algebraMap A (Localization.AtPrime p))
      = (p ^ n).map (algebraMap A (Localization.AtPrime p)) := by
    rw [symbolicPower_def]
    exact IsLocalization.map_under p.primeCompl (Localization.AtPrime p) _
  rw [sat_def, Ideal.map_mul, h1, h2, ← Ideal.map_mul, ← pow_add, symbolicPower_def]

/-- **(iii)** If `𝔭⁽ᵐ⁾𝔭⁽ⁿ⁾` has a minimal primary decomposition `s`, then `𝔭⁽ᵐ⁺ⁿ⁾` is its
`𝔭`-primary component. -/
theorem symbolicPower_mul_eq_component {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {s : Finset (Ideal A)}
    (h : IsMinimalPrimaryDecomposition (symbolicPower p m * symbolicPower p n) s) :
    ∃ q ∈ s, q.radical = p ∧ q = symbolicPower p (m + n) := by
  have hmn : m + n ≠ 0 := by omega
  have hr : (symbolicPower p m * symbolicPower p n).radical = p := by
    rw [Ideal.radical_mul, radical_symbolicPower p hm, radical_symbolicPower p hn, inf_idem]
  have h' := h.exists_component_eq_sat (p := p) hr (by
    rw [sat_symbolicPower_mul p]
    exact (isPrimary_symbolicPower p hmn).1)
  rwa [sat_symbolicPower_mul p] at h'

/-- The uniqueness form of (iii): every component of a minimal primary decomposition of
`𝔭⁽ᵐ⁾𝔭⁽ⁿ⁾` whose radical is `𝔭` is the symbolic power `𝔭⁽ᵐ⁺ⁿ⁾`. -/
theorem eq_symbolicPower_mul_of_mem {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {s : Finset (Ideal A)} (h : IsMinimalPrimaryDecomposition (symbolicPower p m * symbolicPower p n) s)
    {q : Ideal A} (hq : q ∈ s) (hqr : q.radical = p) : q = symbolicPower p (m + n) := by
  have hmn : m + n ≠ 0 := by omega
  have hr : (symbolicPower p m * symbolicPower p n).radical = p := by
    rw [Ideal.radical_mul, radical_symbolicPower p hm, radical_symbolicPower p hn, inf_idem]
  obtain ⟨q₀, hq₀, hq₀r, hq₀eq⟩ := h.exists_component_eq_sat (p := p) hr (by
    rw [sat_symbolicPower_mul p]
    exact (isPrimary_symbolicPower p hmn).1)
  rw [sat_symbolicPower_mul p] at hq₀eq
  show q = symbolicPower p (m + n)
  rw [← hq₀eq, h.radicals_distinct q hq q₀ hq₀ (by rw [hqr, hq₀r])]

/-! ### Part (iv) -/

/-- **(iv)** `𝔭⁽ⁿ⁾ = 𝔭ⁿ` if and only if `𝔭ⁿ` is `𝔭`-primary. -/
theorem symbolicPower_eq_pow_iff {n : ℕ} (hn : n ≠ 0) :
    symbolicPower p n = p ^ n ↔ (p ^ n).IsPrimary := by
  constructor
  · rintro h
    rw [← h]
    exact isPrimary_symbolicPower p hn
  · intro hq
    rw [symbolicPower]
    exact sat_eq_self_of_isPrimary p hq (Ideal.pow_le_self hn)

/-! ### Sanity checks on the definition -/

/-- The `n`-th symbolic power contains the `n`-th power. -/
theorem pow_le_symbolicPower (n : ℕ) : p ^ n ≤ symbolicPower p n := le_sat p (p ^ n)

/-- The first symbolic power of a prime ideal is the ideal itself. -/
theorem symbolicPower_one : symbolicPower p 1 = p := by
  rw [symbolicPower, pow_one]
  exact sat_eq_self_of_isPrimary p hp.isPrimary le_rfl

/-! ### Exercise 4.13, all four parts -/

/-- **Exercise 4.13** of Atiyah–Macdonald, all four parts, for `m, n ≥ 1`:

(i) `𝔭⁽ⁿ⁾` is `𝔭`-primary (and its radical is `𝔭`);
(ii) for every minimal primary decomposition `s` of `𝔭ⁿ`, the component of `s` with radical `𝔭` is
`𝔭⁽ⁿ⁾`;
(iii) for every minimal primary decomposition `s` of `𝔭⁽ᵐ⁾𝔭⁽ⁿ⁾`, the component of `s` with radical
`𝔭` is `𝔭⁽ᵐ⁺ⁿ⁾`;
(iv) `𝔭⁽ⁿ⁾ = 𝔭ⁿ` if and only if `𝔭ⁿ` is `𝔭`-primary. -/
theorem solution {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (symbolicPower p n).IsPrimary ∧ (symbolicPower p n).radical = p ∧
      (∀ s : Finset (Ideal A), IsMinimalPrimaryDecomposition (p ^ n) s →
        ∃ q ∈ s, q.radical = p ∧ q = symbolicPower p n) ∧
      (∀ s : Finset (Ideal A),
        IsMinimalPrimaryDecomposition (symbolicPower p m * symbolicPower p n) s →
          ∃ q ∈ s, q.radical = p ∧ q = symbolicPower p (m + n)) ∧
      (symbolicPower p n = p ^ n ↔ (p ^ n).IsPrimary) :=
  ⟨isPrimary_symbolicPower p hn, radical_symbolicPower p hn,
    fun _s hs => symbolicPower_eq_component p hn hs,
    fun _s hs => symbolicPower_mul_eq_component p hm hn hs,
    symbolicPower_eq_pow_iff p hn⟩

/-! ### The hypothesis of (ii) cannot be weakened: distinctness of the radicals is necessary

Parts (ii) and (iii) speak of "*the* `𝔭`-primary component" of a primary decomposition, which only
makes sense for a minimal decomposition.  The following example shows that the conclusion really
fails without the hypothesis `radicals_distinct`: a decomposition of `𝔪²` into `𝔪`-primary ideals can
have a component other than the symbolic power `𝔪⁽²⁾ = 𝔪²`. -/

/-- If `𝔪` is a maximal ideal with `𝔪² ≠ 𝔪`, then `𝔪² = 𝔪 ∩ 𝔪²` is a decomposition of `𝔪²` all of
whose components are `𝔪`-primary, and the component `𝔪` is *not* the symbolic power
`𝔪⁽²⁾ = 𝔪²`.  So in (ii) the "`𝔭`-primary component" is genuinely ambiguous without distinctness of
the radicals.  (Concrete instance: `A = ℤ`, `𝔪 = (2)`, `𝔪² = (4)`, see
`component_not_unique_int`.) -/
theorem component_not_unique {m : Ideal A} [hm : m.IsPrime] (hmax : m.IsMaximal)
    (hne : m ^ 2 ≠ m) :
    ∃ s : Finset (Ideal A), (∀ q ∈ s, q.IsPrimary) ∧ s.inf (fun q => q) = m ^ 2 ∧
      (∀ q ∈ s, q.radical = m) ∧ ∃ q ∈ s, q ≠ symbolicPower m 2 := by
  classical
  have hpow : (m ^ 2).IsPrimary := isPrimary_pow_of_isMaximal hmax (by norm_num)
  refine ⟨{m, m ^ 2}, ?_, ?_, ?_, m, by simp, ?_⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hm.isPrimary
    · exact hpow
  · rw [Finset.inf_insert, Finset.inf_singleton,
      inf_eq_right.mpr (Ideal.pow_le_self (n := 2) (by norm_num))]
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hm.radical
    · rw [Ideal.radical_pow _ (by norm_num : (2 : ℕ) ≠ 0), hm.radical]
  · intro h
    have h2 : symbolicPower m 2 = m ^ 2 :=
      (symbolicPower_eq_pow_iff m (by norm_num)).mpr hpow
    have : m = m ^ 2 := by
      calc m = symbolicPower m 2 := h
        _ = m ^ 2 := h2
    exact hne this.symm

/-- The concrete counterexample in `ℤ`: `(4) = (2) ∩ (2)²` is a decomposition of `(4) = (2)²` into
`(2)`-primary ideals, and the component `(2)` is not `(2)²`.  Since `(2)²` is `(2)`-primary, part
(iv) identifies the symbolic power `(2)⁽²⁾` with `(2)²`, so `(2)` is a `(2)`-primary component which
is not the symbolic power. -/
theorem component_not_unique_int :
    ∃ s : Finset (Ideal ℤ), (∀ q ∈ s, q.IsPrimary) ∧
      s.inf (fun q => q) = Ideal.span {(2 : ℤ)} ^ 2 ∧
      (∀ q ∈ s, q.radical = Ideal.span {(2 : ℤ)}) ∧
      ∃ q ∈ s, q ≠ Ideal.span {(2 : ℤ)} ^ 2 := by
  have hprime : Prime (2 : ℤ) := Int.prime_two
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by norm_num) |>.mpr hprime).isMaximal (by norm_num)
  have hsq : (Ideal.span {(2 : ℤ)}) ^ 2 = Ideal.span {(4 : ℤ)} := by
    rw [sq, Ideal.span_singleton_mul_span_singleton]
    norm_num
  have hne : (Ideal.span {(2 : ℤ)}) ^ 2 ≠ Ideal.span {(2 : ℤ)} := by
    rw [hsq]
    intro h
    have h2 : (2 : ℤ) ∈ Ideal.span {(4 : ℤ)} := by
      rw [h]
      exact Ideal.mem_span_singleton_self 2
    rw [Ideal.mem_span_singleton] at h2
    obtain ⟨k, hk⟩ := h2
    omega
  haveI : (Ideal.span {(2 : ℤ)}).IsPrime := hmax.isPrime
  have hpow : ((Ideal.span {(2 : ℤ)}) ^ 2).IsPrimary :=
    isPrimary_pow_of_isMaximal hmax (by norm_num)
  obtain ⟨s, h1, h2, h3, q, hq, hqne⟩ :=
    component_not_unique (m := Ideal.span {(2 : ℤ)}) hmax hne
  have hsp : symbolicPower (Ideal.span {(2 : ℤ)}) 2 = (Ideal.span {(2 : ℤ)}) ^ 2 :=
    (symbolicPower_eq_pow_iff (Ideal.span {(2 : ℤ)}) (by norm_num)).mpr hpow
  exact ⟨s, h1, h2, h3, q, hq, fun h => hqne (h.trans hsp.symm)⟩

/-! ### Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_4_13.isPrimary_symbolicPower
#print axioms AtiyahMcdonald69.Ex_4_13.radical_symbolicPower
#print axioms AtiyahMcdonald69.Ex_4_13.symbolicPower_eq_component
#print axioms AtiyahMcdonald69.Ex_4_13.symbolicPower_mul_eq_component
#print axioms AtiyahMcdonald69.Ex_4_13.symbolicPower_eq_pow_iff
#print axioms AtiyahMcdonald69.Ex_4_13.solution
#print axioms AtiyahMcdonald69.Ex_4_13.eq_symbolicPower_of_mem
#print axioms AtiyahMcdonald69.Ex_4_13.eq_symbolicPower_mul_of_mem
#print axioms AtiyahMcdonald69.Ex_4_13.symbolicPower_one
#print axioms AtiyahMcdonald69.Ex_4_13.component_not_unique
#print axioms AtiyahMcdonald69.Ex_4_13.component_not_unique_int

end AtiyahMcdonald69.Ex_4_13
