/-
Atiyah–Macdonald (1969), Chapter 8, Exercise 1.

Let `q₁ ∩ ⋯ ∩ qₙ = (0)` be a minimal primary decomposition of the zero ideal in a Noetherian
ring `A`, and let `qᵢ` be `pᵢ`-primary.  Let `pᵢ⁽ᵐ⁾` denote the `m`-th symbolic power of `pᵢ`
(Chapter 4, Exercise 13).  The exercise asserts:
* for each `i` there is `mᵢ ≠ 0` with `pᵢ⁽ᵐⁱ⁾ ⊆ qᵢ`;
* if `pᵢ` is an isolated prime of `(0)`, then `qᵢ = pᵢ⁽ᵐ⁾` for all sufficiently large `m`;
* if `pᵢ` is an embedded prime, then replacing `qᵢ` by `pᵢ⁽ᵐ⁾` (`m` large) gives infinitely
  many distinct minimal primary decompositions of `(0)`, differing only in the `i`-th component.
-/
import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace AtiyahMcdonald69.Ex_8_1

open Ideal

variable {R : Type*} [CommRing R]

/-- The `n`-th symbolic power `p⁽ⁿ⁾` of a prime ideal `p`: the contraction of `pⁿ` from the
localization `A_p` (Atiyah–Macdonald, Chapter 4, Exercise 13). -/
noncomputable def symPow (p : Ideal R) [p.IsPrime] (n : ℕ) : Ideal R :=
  ((p ^ n).map (algebraMap R (Localization.AtPrime p))).comap (algebraMap R (Localization.AtPrime p))

section Basic

variable {p : Ideal R} [hp : p.IsPrime]

lemma symPow_def (n : ℕ) :
    symPow p n = ((p ^ n).map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p)) := rfl

lemma symPow_one : symPow p 1 = p := by
  rw [symPow_def, pow_one]
  exact IsLocalization.under_map_of_isPrime_disjoint (I := p) p.primeCompl _ hp
    (Set.disjoint_left.mpr fun x hx hx' => hx hx')

lemma symPow_antitone {m n : ℕ} (h : m ≤ n) : symPow p n ≤ symPow p m :=
  Ideal.comap_mono (Ideal.map_mono (Ideal.pow_le_pow_right h))


/-- Extension of a symbolic power recovers the extension of the corresponding power. -/
lemma map_symPow (n : ℕ) :
    (symPow p n).map (algebraMap R (Localization.AtPrime p)) =
      (p ^ n).map (algebraMap R (Localization.AtPrime p)) := by
  refine le_antisymm ?_ ?_
  · exact Ideal.map_comap_le
  · exact Ideal.map_mono Ideal.le_comap_map

lemma isPrimary_symPow {n : ℕ} (hn : n ≠ 0) : (symPow p n).IsPrimary := by
  have hmax : p.map (algebraMap R (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)
  have hmax' : IsMaximal (IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
    IsLocalRing.maximalIdeal.isMaximal _
  rw [symPow_def, Ideal.map_pow, hmax]
  refine Ideal.IsPrimary.comap ?_ (algebraMap R (Localization.AtPrime p))
  refine Ideal.isPrimary_of_isMaximal_radical ?_
  rw [Ideal.radical_pow (IsLocalRing.maximalIdeal (Localization.AtPrime p)) hn,
    IsPrime.radical (IsMaximal.isPrime hmax')]
  exact hmax'

lemma radical_symPow {n : ℕ} (hn : n ≠ 0) : radical (symPow p n) = p := by
  have hmax : p.map (algebraMap R (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)
  have hdisj : Disjoint (p.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun x hx hx' => hx hx'
  have key : radical (p.map (algebraMap R (Localization.AtPrime p)) ^ n) =
      p.map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.radical_pow (p.map (algebraMap R (Localization.AtPrime p))) hn,
      IsPrime.radical (IsMaximal.isPrime (hmax ▸ IsLocalRing.maximalIdeal.isMaximal _))]
  rw [symPow_def, ← Ideal.comap_radical (f := algebraMap R (Localization.AtPrime p)), Ideal.map_pow,
    key]
  exact IsLocalization.under_map_of_isPrime_disjoint (I := p) p.primeCompl _ hp hdisj

end Basic

section Noetherian

variable [IsNoetherianRing R]

/-- The predicate "`t` is a minimal primary decomposition of the zero ideal". -/
abbrev IsMPD (t : Finset (Ideal R)) : Prop :=
  Submodule.IsMinimalPrimaryDecomposition (⊥ : Ideal R) t

/-- **(8.1), first assertion.**  Every primary component contains a nonzero symbolic power of
its associated prime. -/
theorem exists_symPow_le {p q : Ideal R} [p.IsPrime] (hq : q.IsPrimary) (hpq : radical q = p) :
    ∃ n : ℕ, n ≠ 0 ∧ symPow p n ≤ q := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := p) (J := q)
    (by rw [hpq]) (IsNoetherian.noetherian p)
  refine ⟨n + 1, Nat.succ_ne_zero n, ?_⟩
  have hpow : p ^ (n + 1) ≤ q := (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  have hdisj : Disjoint (p.primeCompl : Set R) (q : Set R) := by
    rw [Set.disjoint_left]
    intro x hx hxq
    exact hx (hpq ▸ le_radical hxq)
  calc symPow p (n + 1)
      = ((p ^ (n + 1)).map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) := rfl
    _ ≤ (q.map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) := Ideal.comap_mono (Ideal.map_mono hpow)
    _ = q := IsLocalization.under_map_of_isPrimary_disjoint (I := q) p.primeCompl _ hq hdisj

/-- The associated primes of `(0)` are among the radicals of the terms of *any* primary
decomposition of `(0)` (with pairwise distinct radicals). -/
theorem associatedPrimes_subset_radical_image {s : Finset (Ideal R)}
    (hinf : s.inf id = ⊥) (hprim : ∀ j ∈ s, j.IsPrimary)
    (hdist : (s : Set (Ideal R)).Pairwise fun a b => radical a ≠ radical b) :
    (⊥ : Ideal R).associatedPrimes ⊆ radical '' (s : Set (Ideal R)) := by
  obtain ⟨t, hts, htinf, htmin⟩ := Submodule.decomposition_erase_inf hinf
  have htdist : (t : Set (Ideal R)).Pairwise fun a b => radical a ≠ radical b :=
    hdist.mono fun x hx => hts hx
  have htdist' : (t : Set (Ideal R)).Pairwise
      fun a b => (a.colon Set.univ).radical ≠ (b.colon Set.univ).radical := by
    simpa only [Submodule.colon_univ] using htdist
  have ht : IsMPD t := ⟨htinf, fun j hj => hprim j (hts hj), htdist', htmin⟩
  have himg := Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes ht
  rw [← himg]
  rintro x ⟨j, hj, rfl⟩
  exact ⟨j, hts hj, by simp⟩

/-- A primary decomposition of `(0)` with pairwise distinct radicals, whose radicals are
associated primes of `(0)`, is minimal (irredundant). -/
theorem isMinimalPrimaryDecomposition_of_distinct {s : Finset (Ideal R)}
    (hinf : s.inf id = ⊥) (hprim : ∀ j ∈ s, j.IsPrimary)
    (hdist : (s : Set (Ideal R)).Pairwise fun a b => radical a ≠ radical b)
    (hass : radical '' (s : Set (Ideal R)) ⊆ (⊥ : Ideal R).associatedPrimes) :
    IsMPD s := by
  refine ⟨hinf, hprim, ?_, ?_⟩
  · simpa only [Submodule.colon_univ] using hdist
  · intro j hj hle
    have hinf' : (s.erase j).inf id = ⊥ := by
      have h1 : s.inf id = (s.erase j).inf id ⊓ j := by
        conv_lhs => rw [← Finset.insert_erase hj]
        rw [Finset.inf_insert, inf_comm]
        rfl
      rw [hinf, inf_eq_left.mpr hle] at h1
      exact h1.symm
    have hmem : radical j ∈ (⊥ : Ideal R).associatedPrimes := hass ⟨j, Finset.mem_coe.mpr hj, rfl⟩
    have hdist' : ((s.erase j : Finset (Ideal R)) : Set (Ideal R)).Pairwise
        fun a b => radical a ≠ radical b :=
      hdist.mono fun x hx => Finset.mem_of_mem_erase hx
    have hmem' := associatedPrimes_subset_radical_image hinf'
      (fun k hk => hprim k (Finset.mem_of_mem_erase hk)) hdist' hmem
    obtain ⟨k, hk, hkj⟩ := hmem'
    exact hdist (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hk)) (Finset.mem_coe.mpr hj)
      (Finset.ne_of_mem_erase hk) hkj

/-- **(8.1), isolated component.**  If `q` is the `p`-primary component of a minimal primary
decomposition of `(0)` and `p` is a minimal prime of `(0)`, then `q` is a symbolic power of `p`. -/
theorem eq_symPow_of_mem_minimalPrimes {t : Finset (Ideal R)} {q p : Ideal R} [p.IsPrime]
    (ht : IsMPD t) (hq : q ∈ t) (hpq : radical q = p)
    (hiso : p ∈ (⊥ : Ideal R).minimalPrimes) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ r ≥ n, q = symPow p r := by
  classical
  have hqprim : q.IsPrimary := ht.primary hq
  obtain ⟨n₀, hn₀, hle⟩ := exists_symPow_le (p := p) hqprim hpq
  have hmap : ∀ j ∈ t, j ≠ q → j.map (algebraMap R (Localization.AtPrime p)) = ⊤ := by
    intro j hj hne
    have hjprim : j.IsPrimary := ht.primary hj
    have hjp : radical j ≠ p := by
      intro h
      refine hne (Submodule.IsMinimalPrimaryDecomposition.injOn (⊥ : Ideal R) t ht
        (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hq) ?_)
      simpa only [Submodule.colon_univ, hpq] using h
    have hnotle : ¬ radical j ≤ p := by
      intro hlejp
      haveI : (radical j).IsPrime := isPrime_radical hjprim
      exact hjp (le_antisymm hlejp (hiso.2 ⟨‹(radical j).IsPrime›, bot_le⟩ hlejp))
    refine IsLocalization.map_eq_top_of_not_subset (M := p.primeCompl)
      (S := Localization.AtPrime p) (I := j) ?_
    intro hsub
    have hsub' : j ≤ p := by
      intro x hx
      have hx' : x ∉ (p.primeCompl : Set R) := hsub hx
      simpa using hx'
    have h1 : radical j ≤ radical p := Ideal.radical_mono hsub'
    rw [IsPrime.radical ‹p.IsPrime›] at h1
    exact hnotle h1
  have hqmap : q.map (algebraMap R (Localization.AtPrime p)) = ⊥ := by
    have h1 : (IsLocalization.mapFrameHom p.primeCompl (Localization.AtPrime p)) (t.inf id) =
        t.inf (fun j => j.map (algebraMap R (Localization.AtPrime p))) := by
      rw [map_finset_inf (IsLocalization.mapFrameHom p.primeCompl (Localization.AtPrime p)) t]
      rfl
    have h1' : (⊥ : Ideal (Localization.AtPrime p)) =
        t.inf (fun j => j.map (algebraMap R (Localization.AtPrime p))) := by
      rw [← h1, IsLocalization.mapFrameHom_apply, ht.inf_eq, Ideal.map_bot]
    rw [← Finset.insert_erase hq, Finset.inf_insert] at h1'
    have h2 : (t.erase q).inf (fun j => j.map (algebraMap R (Localization.AtPrime p))) = ⊤ := by
      rw [eq_top_iff, Finset.le_inf_iff]
      intro j hj
      exact le_of_eq (hmap j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)).symm
    rw [h2, inf_top_eq] at h1'
    exact h1'.symm
  have hnil : (p ^ n₀).map (algebraMap R (Localization.AtPrime p)) = ⊥ := by
    have h' : (symPow p n₀).map (algebraMap R (Localization.AtPrime p)) ≤ ⊥ := by
      calc (symPow p n₀).map (algebraMap R (Localization.AtPrime p))
          ≤ q.map (algebraMap R (Localization.AtPrime p)) := Ideal.map_mono hle
        _ = ⊥ := hqmap
    rw [← map_symPow (p := p) n₀]
    exact le_bot_iff.mp h'
  have hqsub : q ≤ (⊥ : Ideal (Localization.AtPrime p)).comap
      (algebraMap R (Localization.AtPrime p)) := by
    rw [← Ideal.map_le_iff_le_comap, hqmap]
  refine ⟨n₀, hn₀, fun r hr => ?_⟩
  have hle_r : symPow p r ≤ q := (symPow_antitone hr).trans hle
  have hnilr : (p ^ r).map (algebraMap R (Localization.AtPrime p)) = ⊥ := by
    have h' : (p ^ r).map (algebraMap R (Localization.AtPrime p)) ≤
        (p ^ n₀).map (algebraMap R (Localization.AtPrime p)) :=
      Ideal.map_mono (Ideal.pow_le_pow_right hr)
    rw [hnil] at h'
    exact le_bot_iff.mp h'
  have hbot : (⊥ : Ideal (Localization.AtPrime p)).comap
      (algebraMap R (Localization.AtPrime p)) = symPow p r :=
    congrArg (Ideal.comap (algebraMap R (Localization.AtPrime p))) hnilr.symm
  exact le_antisymm (hqsub.trans_eq hbot) hle_r

/-- **(8.1), embedded component: distinctness.**  If `q` corresponds to an embedded prime `p`,
then the symbolic powers `p⁽ᵐ⁾` (`m ≥ 1`) are pairwise distinct. -/
theorem symPow_injective_of_not_mem_minimalPrimes {t : Finset (Ideal R)} {q p : Ideal R}
    [p.IsPrime] (ht : IsMPD t) (hq : q ∈ t) (hpq : radical q = p)
    (hemb : p ∉ (⊥ : Ideal R).minimalPrimes) :
    ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → symPow p m = symPow p n → m = n := by
  obtain ⟨p', hp'mem, hp'le⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p) bot_le
  have hp'prime : p'.IsPrime := hp'mem.1.1
  have hp'ne : p' ≠ p := fun h => hemb (h ▸ hp'mem)
  have hdisj : Disjoint (p.primeCompl : Set R) (p' : Set R) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (hp'le hx')
  have hdisjP : Disjoint (p.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun x hx hx' => hx hx'
  have hprimeB : (p'.map (algebraMap R (Localization.AtPrime p))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ p' hp'prime hdisj
  have hltB : p'.map (algebraMap R (Localization.AtPrime p)) <
      p.map (algebraMap R (Localization.AtPrime p)) := by
    refine lt_of_le_of_ne (Ideal.map_mono hp'le) ?_
    intro heq
    have h1 : p' = p := by
      have e1 : (p'.map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) = p' :=
        IsLocalization.under_map_of_isPrime_disjoint (I := p') p.primeCompl _ hp'prime hdisj
      have e2 : (p.map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) = p :=
        IsLocalization.under_map_of_isPrime_disjoint (I := p) p.primeCompl _ ‹p.IsPrime› hdisjP
      rw [heq] at e1
      exact e1.symm.trans e2
    exact hp'ne h1
  have key : ∀ {m n : ℕ}, 1 ≤ m → m < n → symPow p m ≠ symPow p n := by
    intro m n hm hmn heq
    have h1 : (p.map (algebraMap R (Localization.AtPrime p))) ^ m =
        (p.map (algebraMap R (Localization.AtPrime p))) ^ n := by
      rw [← Ideal.map_pow, ← Ideal.map_pow, ← map_symPow (p := p) m, ← map_symPow (p := p) n,
        heq]
    have h2 : (p.map (algebraMap R (Localization.AtPrime p))) ^ m =
        (p.map (algebraMap R (Localization.AtPrime p))) ^ (m + 1) := by
      refine le_antisymm ?_ (Ideal.pow_le_pow_right (Nat.le_succ m))
      calc (p.map (algebraMap R (Localization.AtPrime p))) ^ m
          = (p.map (algebraMap R (Localization.AtPrime p))) ^ n := h1
        _ ≤ (p.map (algebraMap R (Localization.AtPrime p))) ^ (m + 1) :=
            Ideal.pow_le_pow_right hmn
    have h3 : (p.map (algebraMap R (Localization.AtPrime p))) ^ m = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (p.map (algebraMap R (Localization.AtPrime p))) _ (IsNoetherian.noetherian _) ?_ ?_
      · rw [smul_eq_mul]
        refine le_of_eq ?_
        calc (p.map (algebraMap R (Localization.AtPrime p))) ^ m
            = (p.map (algebraMap R (Localization.AtPrime p))) ^ (m + 1) := h2
          _ = (p.map (algebraMap R (Localization.AtPrime p))) ^ m *
              (p.map (algebraMap R (Localization.AtPrime p))) := by rw [pow_succ]
          _ = (p.map (algebraMap R (Localization.AtPrime p))) *
              (p.map (algebraMap R (Localization.AtPrime p))) ^ m := by rw [mul_comm]
      · rw [IsLocalRing.jacobson_eq_maximalIdeal, IsLocalization.AtPrime.map_eq_maximalIdeal]
        exact bot_ne_top
    have h5 : p.map (algebraMap R (Localization.AtPrime p)) ≤
        p'.map (algebraMap R (Localization.AtPrime p)) := by
      have hle_rad : p.map (algebraMap R (Localization.AtPrime p)) ≤
          (⊥ : Ideal (Localization.AtPrime p)).radical := by
        intro x hx
        refine Ideal.mem_radical_iff.mpr ⟨m, ?_⟩
        have hxm : x ^ m ∈ (p.map (algebraMap R (Localization.AtPrime p))) ^ m :=
          Ideal.pow_mem_pow hx m
        rwa [h3] at hxm
      exact hle_rad.trans ((Ideal.radical_mono bot_le).trans (le_of_eq (IsPrime.radical hprimeB)))
    exact (ne_of_lt hltB) (le_antisymm (Ideal.map_mono hp'le) h5)
  intro m n hm hn hmn
  rcases lt_trichotomy m n with h | h | h
  · exact absurd hmn (key hm h)
  · exact h
  · exact absurd hmn.symm (key hn h)

/-- **(8.1), embedded component: the infinite family.**  If `q` corresponds to an embedded prime
`p`, then for all sufficiently large `m` the symbolic power `p⁽ᵐ⁾` may replace `q`, giving a
minimal primary decomposition of `(0)` that differs from the original one only in this slot. -/
theorem exists_isMinimalPrimaryDecomposition_symPow {t : Finset (Ideal R)} {q p : Ideal R}
    [p.IsPrime] (ht : IsMPD t) (hq : q ∈ t) (hpq : radical q = p)
    (hemb : p ∉ (⊥ : Ideal R).minimalPrimes) :
    ∃ r₀ : ℕ, r₀ ≠ 0 ∧ ∀ r ≥ r₀, symPow p r ≤ q ∧
      IsMPD (t.erase q ∪ {symPow p r}) := by
  obtain ⟨r₀, hr₀, hle⟩ := exists_symPow_le (p := p) (ht.primary hq) hpq
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hle' : symPow p r ≤ q := (symPow_antitone hr).trans hle
  refine ⟨hle', ?_⟩
  have hr0 : r ≠ 0 := by omega
  have hq'prim : (symPow p r).IsPrimary := isPrimary_symPow hr0
  have hq'rad : radical (symPow p r) = p := radical_symPow hr0
  have htdist : (t : Set (Ideal R)).Pairwise fun a b => radical a ≠ radical b := by
    simpa only [Submodule.colon_univ] using ht.distinct
  have hinf : (t.erase q ∪ {symPow p r}).inf id = ⊥ := by
    rw [Finset.inf_union, Finset.inf_singleton]
    refine le_antisymm ?_ bot_le
    rw [← ht.inf_eq]
    have h1 : t.inf id = (t.erase q).inf id ⊓ q := by
      conv_lhs => rw [← Finset.insert_erase hq]
      rw [Finset.inf_insert, inf_comm]
      rfl
    rw [h1]
    exact inf_le_inf_left _ hle'
  have hprim : ∀ j ∈ t.erase q ∪ {symPow p r}, j.IsPrimary := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact ht.primary (Finset.mem_of_mem_erase hj)
    · exact hq'prim
  have hdist : ((t.erase q ∪ {symPow p r} : Finset (Ideal R)) : Set (Ideal R)).Pairwise
      fun a b => radical a ≠ radical b := by
    intro a ha b hb hab heq
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_singleton] at ha hb
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact htdist (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ha))
        (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hb)) hab heq
    · exact htdist (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ha)) (Finset.mem_coe.mpr hq)
        (Finset.ne_of_mem_erase ha) (by rw [heq, hq'rad, hpq])
    · exact htdist (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hb)) (Finset.mem_coe.mpr hq)
        (Finset.ne_of_mem_erase hb) (by rw [← heq, hq'rad, hpq])
    · exact hab rfl
  have hass : radical '' ((t.erase q ∪ {symPow p r}) : Set (Ideal R)) ⊆
      (⊥ : Ideal R).associatedPrimes := by
    rw [← ht.image_radical_eq_associated_primes]
    rintro x ⟨a, ha, rfl⟩
    simp only [Finset.mem_coe, Set.mem_union, Set.mem_singleton_iff] at ha
    rcases ha with ha | rfl
    · exact ⟨a, Finset.mem_coe.mpr (Finset.mem_of_mem_erase ha), by simp⟩
    · exact ⟨q, Finset.mem_coe.mpr hq, by simp [hq'rad, hpq]⟩
  exact isMinimalPrimaryDecomposition_of_distinct hinf hprim hdist (by simpa only [Finset.coe_union, Finset.coe_singleton] using hass)

/-- **(8.1), embedded component: infinitely many minimal decompositions.**  The family
`r ↦ (t \ {q}) ∪ {p⁽ʳ⁾}` consists of pairwise distinct minimal primary decompositions of `(0)`,
all agreeing with the given one except in the `q`-slot. -/
theorem embedded_infinitely_many {t : Finset (Ideal R)} {q p : Ideal R} [p.IsPrime]
    (ht : IsMPD t) (hq : q ∈ t) (hpq : radical q = p)
    (hemb : p ∉ (⊥ : Ideal R).minimalPrimes) :
    ∃ r₀ : ℕ, r₀ ≠ 0 ∧
      (∀ r ≥ r₀, IsMPD (t.erase q ∪ {symPow p r})) ∧
      (∀ ⦃m n : ℕ⦄, r₀ ≤ m → r₀ ≤ n →
        t.erase q ∪ {symPow p m} = t.erase q ∪ {symPow p n} → m = n) := by
  obtain ⟨r₀, hr₀, hfam⟩ := exists_isMinimalPrimaryDecomposition_symPow ht hq hpq hemb
  refine ⟨r₀, hr₀, fun r hr => (hfam r hr).2, ?_⟩
  intro m n hm hn hmn
  have htdist : (t : Set (Ideal R)).Pairwise fun a b => radical a ≠ radical b := by
    simpa only [Submodule.colon_univ] using ht.distinct
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hsym : symPow p m = symPow p n := by
    have hmem : symPow p m ∈ t.erase q ∪ {symPow p n} := by
      rw [← hmn]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    rw [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (by rw [radical_symPow hm0, hpq] :
        radical (symPow p m) = radical q)
        (htdist (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hmem)) (Finset.mem_coe.mpr hq)
          (Finset.ne_of_mem_erase hmem))
    · exact hmem
  exact symPow_injective_of_not_mem_minimalPrimes ht hq hpq hemb (Nat.one_le_iff_ne_zero.mpr hm0)
    (Nat.one_le_iff_ne_zero.mpr hn0) hsym

/-- **Atiyah–Macdonald, Chapter 8, Exercise 1, in full** (stated in terms of the radicals of
the given minimal primary decomposition of `(0)`). -/
theorem exercise_8_1 {t : Finset (Ideal R)} (ht : IsMPD t) :
    (∀ (q : Ideal R) (hq : q ∈ t), ∃ m : ℕ, m ≠ 0 ∧
        @symPow R _ (radical q) (isPrime_radical (ht.primary hq)) m ≤ q) ∧
    (∀ (q : Ideal R) (hq : q ∈ t), radical q ∈ (⊥ : Ideal R).minimalPrimes → ∃ m : ℕ, m ≠ 0 ∧
        ∀ r ≥ m, q = @symPow R _ (radical q) (isPrime_radical (ht.primary hq)) r) ∧
    (∀ (q : Ideal R) (hq : q ∈ t), radical q ∉ (⊥ : Ideal R).minimalPrimes →
      (∀ ⦃m n : ℕ⦄, 1 ≤ m → 1 ≤ n →
        @symPow R _ (radical q) (isPrime_radical (ht.primary hq)) m =
        @symPow R _ (radical q) (isPrime_radical (ht.primary hq)) n → m = n) ∧
      (∃ r₀ : ℕ, r₀ ≠ 0 ∧ ∀ r ≥ r₀,
        @symPow R _ (radical q) (isPrime_radical (ht.primary hq)) r ≤ q ∧
        IsMPD (t.erase q ∪ {@symPow R _ (radical q) (isPrime_radical (ht.primary hq)) r}))) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · haveI : (radical q).IsPrime := isPrime_radical (ht.primary hq)
    exact exists_symPow_le (ht.primary hq) rfl
  · haveI : (radical q).IsPrime := isPrime_radical (ht.primary hq)
    exact eq_symPow_of_mem_minimalPrimes ht hq rfl
  · haveI : (radical q).IsPrime := isPrime_radical (ht.primary hq)
    intro hemb
    refine ⟨?_, ?_⟩
    · intro m n hm hn hsym
      exact symPow_injective_of_not_mem_minimalPrimes ht hq rfl hemb hm hn hsym
    · exact exists_isMinimalPrimaryDecomposition_symPow ht hq rfl hemb

end Noetherian

end AtiyahMcdonald69.Ex_8_1

#print axioms AtiyahMcdonald69.Ex_8_1.exists_symPow_le
#print axioms AtiyahMcdonald69.Ex_8_1.eq_symPow_of_mem_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_8_1.symPow_injective_of_not_mem_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_8_1.exists_isMinimalPrimaryDecomposition_symPow
#print axioms AtiyahMcdonald69.Ex_8_1.embedded_infinitely_many
#print axioms AtiyahMcdonald69.Ex_8_1.exercise_8_1
