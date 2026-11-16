/-
# Atiyah–Macdonald (1969), Chapter 4, Exercise 23

The exercise reads: *"Prove analogues of Propositions 4.6 to 4.11."*
Chapter 4 develops primary decomposition for ideals of a ring `A`; the section
"Primary decomposition of modules" (Exercises 4.20–4.24) transposes the theory to submodules of a
fixed `A`-module `M`.  This file proves the six module analogues, for a submodule `N ≤ M` of an
`A`-module `M` with a minimal primary decomposition `N = ⋂_{q ∈ t} q`.

Notation (A–M Exercises 4.20/4.21; Mathlib's `Submodule.IsPrimary`, `Mathlib.RingTheory.Lasker`):
* `radIn N = r_M(N) = √(N : M) = √Ann (M ⧸ N)` (defined here, with `mem_radIn_iff`);
* `Q.IsPrimary`: every zero divisor on `M ⧸ Q` is nilpotent;
* `N.IsMinimalPrimaryDecomposition t`: `t.inf id = N`, every `q ∈ t` is primary, the `r_M(q)` are
  pairwise distinct, and every `q ∈ t` is necessary (irredundant).

## Contents (the analogues of the six propositions)

* `prop_4_6` — (4.6): every prime ideal containing `Ann (M ⧸ N)` contains some `r_M(q)`; and for a
  prime `p ⊇ Ann (M ⧸ N)`, `p` is minimal among such primes iff `p = r_M(q)` for some `q ∈ t` and
  `r_M(q)` is minimal among the `r_M(q')`, `q' ∈ t`.  (So the minimal primes over `Ann (M ⧸ N)` are
  exactly the minimal elements of `{r_M(q)}`, independently of the decomposition.)
* `prop_4_7` — (4.7): the zero divisors on `M ⧸ N` are exactly `⋃_{q ∈ t} r_M(q)`.
* `prop_4_8_i` — (4.8)(i): if `Q` is primary and `S ∩ r_M(Q) = ∅`, then `S⁻¹Q` is primary,
  `r(S⁻¹Q) = r_M(Q)` and `(S⁻¹Q) ∩ M = Q`.
* `prop_4_8_ii` — (4.8)(ii): if `Q` is primary and `S ∩ r_M(Q) ≠ ∅`, then `S⁻¹Q = S⁻¹M`.
* `prop_4_8_iii` — (4.8), converse for an arbitrary `R`-submodule `P ≤ S⁻¹M`: if `P` is primary and
  `S`-saturated (`S⁻¹(P ∩ M) = P`), then `P ∩ M` is primary with `r(P ∩ M) = r(P)`.  Together with
  (i) this is the bijection between primary submodules avoiding `S` and primary submodules of the
  localization.  As stated for arbitrary `R`-submodules the saturation is not automatic (`R = ℤ`,
  `S = {2ⁿ}`, `P = ℤ·(1/2) ≤ ℤ[1/2]`); in the book's setting, where `P` is an `S⁻¹A`-submodule,
  it is *proved* in `localized₀_comap_restrictScalars`, and `prop_4_8_iii'` gives the converse
  with no extra hypothesis.
* `prop_4_9` — (4.9): with `s = {q ∈ t : S ∩ r_M(q) = ∅}`, `S⁻¹N = ⋂_{q ∈ s} S⁻¹q`, the components
  `S⁻¹q` (`q ∈ s`) are primary with radical `r_M(q)`, and the contraction `S(N) = (S⁻¹N) ∩ M` equals
  `⋂_{q ∈ s} q` and is again a *minimal* primary decomposition.
* `prop_4_9_localized` — (4.9), localized side: the localized family `{S⁻¹q : q ∈ s}` is itself a
  `Submodule.IsMinimalPrimaryDecomposition` of `S⁻¹N`, i.e. it consists of primary submodules with
  pairwise distinct radicals, no component is superfluous, and its intersection is `S⁻¹N`.  These
  properties are derived from the componentwise contraction formula `prop_4_8_i` and from the
  minimality of the contracted decomposition.
* `prop_4_10` — (4.10) (second uniqueness theorem): for an isolated (= downward closed) set `Sig` of
  associated primes, `⋂ {q ∈ t : r_M(q) ∈ Sig}` is independent of the minimal primary decomposition.
* `prop_4_11` — (4.11): the isolated primary components are uniquely determined; in particular, for a
  minimal element `p` of the associated primes (e.g. a minimal prime over `Ann (M ⧸ N)`), the primary
  component with radical `p` is the same in every minimal primary decomposition.

## Audit of the natural proof

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-23

The natural proof follows the book closely.  Two points needed repair/extra hypotheses:
* in (4.7) it argues "the set `D(M)` of zero divisors clearly satisfies `√D(M) = D(M)`", which is
  circular (that is exactly what has to be shown).  The proof here instead uses the module analogue
  of (4.4), `mem_radical_colon_singleton_iff`, to get `a ∈ √(N : m)` and hence `a ∈ r_M(q)` for any
  `q` with `m ∉ q`; the reverse inclusion uses irredundancy of the decomposition, as in the book;
* in the converse part of (4.8) ("the inverse image of a primary submodule is primary") the natural
  proof glosses over the fact that extension and contraction are inverse only on `S`-saturated
  submodules; this is made explicit in `prop_4_8_iii`.

Everything is checked by the Lean 4 kernel (no `sorry`, `admit` or extra axioms); each public theorem
below is validated with `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`).
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace AtiyahMcdonald69.Ex_4_23

open Submodule

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `r_M(N)`, the radical of a submodule `N` of `M` (Atiyah–Macdonald, Exercise 4.20):
`r_M(N) = √(N : M) = √Ann(M ⧸ N)`. -/
def radIn (N : Submodule R M) : Ideal R := (N.colon Set.univ).radical

@[simp]
lemma radIn_def (N : Submodule R M) : radIn N = (N.colon Set.univ).radical := rfl

lemma mem_radIn_iff {N : Submodule R M} {a : R} :
    a ∈ radIn N ↔ ∃ n : ℕ, ∀ m : M, a ^ n • m ∈ N := by
  rw [radIn_def, Ideal.mem_radical_iff]
  exact exists_congr fun n => by simp [Submodule.mem_colon]

lemma radIn_mono {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) : radIn N₁ ≤ radIn N₂ :=
  Ideal.radical_mono (Submodule.colon_mono h le_rfl)

/-- The radical of an intersection of a minimal primary decomposition: `r_M(⋂ q) = ⋂ r_M(q)`. -/
lemma radIn_finsetInf {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) :
    radIn N = t.inf (fun q => radIn q) := by
  rw [← ht.inf_eq, radIn_def, Submodule.colon_finsetInf]
  exact map_finset_inf Ideal.radicalInfTopHom t (fun q => (q.colon Set.univ))

/-- The colon ideal `(N : x)` for a single element, in the presence of a minimal primary
decomposition: `√(N : x) = ⋂ {r_M(q) | q ∈ t, x ∉ q}` (module analogue of (4.4)). -/
lemma mem_radical_colon_singleton_iff {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) (a : R) (x : M) :
    a ∈ (N.colon {x}).radical ↔ ∀ q ∈ t, x ∉ q → a ∈ radIn q := by
  classical
  have h : (N.colon {x}).radical = (t.filter fun q => x ∉ q).inf (fun q => radIn q) := by
    rw [← ht.inf_eq, Submodule.colon_finsetInf]
    rw [show (t.inf fun i => (id i).colon {x}).radical
        = t.inf (fun q => (q.colon {x}).radical) from
      map_finset_inf Ideal.radicalInfTopHom t (fun i => (id i).colon {x})]
    rw [Finset.inf_congr rfl (fun q hq => (ht.primary hq).radical_colon_singleton_eq_ite x),
      Finset.inf_ite, Finset.inf_top, top_inf_eq]
    rfl
  rw [h, Submodule.mem_finsetInf]
  constructor
  · intro H q hq hxq
    exact H q (Finset.mem_filter.mpr ⟨hq, hxq⟩)
  · intro H q hq
    exact H q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

/-- **(4.6) for modules.** Let `N = ⋂_{q ∈ t} q` be a minimal primary decomposition and put
`p_q = r_M(q)`. Then
(i) every prime ideal containing `Ann(M ⧸ N)` contains some `p_q`, and
(ii) for a prime `p` containing `Ann(M ⧸ N)`, `p` is minimal among the primes containing
`Ann(M ⧸ N)` iff `p = p_q` for some `q ∈ t` and `p_q` is minimal among the `p_q`, `q ∈ t`. -/
theorem prop_4_6 {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) :
    (∀ p : Ideal R, p.IsPrime → N.colon Set.univ ≤ p → ∃ q ∈ t, radIn q ≤ p) ∧
      (∀ p : Ideal R, p.IsPrime → N.colon Set.univ ≤ p →
        ((∀ r : Ideal R, r.IsPrime → N.colon Set.univ ≤ r → r ≤ p → r = p) ↔
          ∃ q ∈ t, radIn q = p ∧ ∀ q' ∈ t, radIn q' ≤ p → radIn q' = p)) := by
  classical
  have hrad : radIn N = t.inf (fun q => radIn q) := radIn_finsetInf ht
  -- the radical of `Ann (M ⧸ N)` is the infimum of the `r_M(q)`
  have hinf_le : ∀ p : Ideal R, p.IsPrime → N.colon Set.univ ≤ p →
      t.inf (fun q => radIn q) ≤ p := by
    intro p hp hp'
    rw [← hrad]
    intro x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    exact hp.mem_of_pow_mem n (hp' hn)
  have key : ∀ p : Ideal R, p.IsPrime → N.colon Set.univ ≤ p → ∃ q ∈ t, radIn q ≤ p :=
    fun p hp hp' => hp.inf_le'.mp (hinf_le p hp hp')
  refine ⟨key, ?_⟩
  intro p hp hp'
  constructor
  · intro hmin
    obtain ⟨q, hq, hqp⟩ := key p hp hp'
    have hannq : N.colon Set.univ ≤ radIn q :=
      (Ideal.le_radical.trans (le_of_eq hrad)).trans (Finset.inf_le hq)
    have hqprime : (radIn q).IsPrime := (ht.primary hq).isPrime_radical_colon
    refine ⟨q, hq, hmin (radIn q) hqprime hannq hqp, ?_⟩
    intro q' hq' hle
    exact hmin (radIn q') (ht.primary hq').isPrime_radical_colon
      ((Ideal.le_radical.trans (le_of_eq hrad)).trans (Finset.inf_le hq')) hle
  · rintro ⟨q, hq, rfl, hminq⟩ r hrp hannr hrp'
    obtain ⟨q', hq', hle⟩ := key r hrp hannr
    have h1 : radIn q' = radIn q := hminq q' hq' (hle.trans hrp')
    exact le_antisymm hrp' (h1 ▸ hle)

/-- **(4.7) for modules.** The zero divisors on `M ⧸ N` are exactly the union of the `r_M(q)`,
`q ∈ t`, for a minimal primary decomposition `N = ⋂_{q ∈ t} q`. -/
theorem prop_4_7 {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) :
    {a : R | ∃ m : M, m ∉ N ∧ a • m ∈ N} = ⋃ q ∈ t, (radIn q : Set R) := by
  classical
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hmN, ham⟩
    have ha : a ∈ (N.colon {m}).radical := by
      rw [Ideal.mem_radical_iff]
      exact ⟨1, by rw [pow_one]; exact Submodule.mem_colon_singleton.mpr ham⟩
    have hmem : ∃ q ∈ t, m ∉ q := by
      by_contra h
      have h2 : m ∈ t.inf id := Submodule.mem_finsetInf.mpr (fun q hq => by
        by_contra hqm
        exact h ⟨q, hq, hqm⟩)
      rw [ht.inf_eq] at h2
      exact hmN h2
    obtain ⟨q, hq, hqm⟩ := hmem
    exact ⟨q, hq, (mem_radical_colon_singleton_iff ht a m).mp ha q hq hqm⟩
  · rintro ⟨q, hq, haq⟩
    obtain ⟨m, hm_mem, hm_notq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hq)
    have hmN : m ∉ N := by
      intro h
      have h' : m ∈ t.inf id := by rw [ht.inf_eq]; exact h
      exact hm_notq ((Finset.inf_le (f := id) hq) h')
    have haq' : a ∈ (q.colon Set.univ).radical := by rwa [radIn_def] at haq
    have hex : ∃ n : ℕ, a ^ n • m ∈ N := by
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp haq'
      refine ⟨n, ?_⟩
      rw [← ht.inf_eq, Submodule.mem_finsetInf]
      intro q' hq'
      by_cases h : q' = q
      · subst h
        exact (Submodule.mem_colon.mp hn) m (Set.mem_univ m)
      · have hm' : m ∈ q' := (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨h, hq'⟩)) hm_mem
        exact q'.smul_mem (a ^ n) hm'
    have hnpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · exfalso
        have hspec := Nat.find_spec hex
        rw [h, pow_zero, one_smul] at hspec
        exact hmN hspec
      · exact h
    refine ⟨a ^ (Nat.find hex - 1) • m, ?_, ?_⟩
    · intro hcon
      exact Nat.find_min hex (by omega) hcon
    · rw [smul_smul, ← pow_succ', Nat.sub_one_add_one (by omega)]
      exact Nat.find_spec hex



section Localization

variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : Submonoid R} {f : M →ₗ[R] N} [IsLocalizedModule p f]

/-- If `Q` is `p`-primary with `S ∩ p = ∅`, then elements of `S` act injectively on `M ⧸ Q`:
`a • m ∈ Q` with `a ∈ S` forces `m ∈ Q`. -/
lemma mem_of_smul_mem_of_disjoint {Q : Submodule R M} (hQ : Q.IsPrimary)
    (hdisj : Disjoint (p : Set R) (radIn Q : Set R)) {a : R} (ha : a ∈ p) {m : M}
    (hm : a • m ∈ Q) : m ∈ Q := by
  by_contra h
  exact (Set.disjoint_left.mp hdisj) ha ((hQ.mem_or_mem hm).resolve_left h)

/-- A fraction `m/s` lies in `S⁻¹Q` only if some element of `S` sends `m` into `Q`; this is the
key computation behind the contraction formula. -/
lemma exists_smul_mem_of_mem_comap {Q : Submodule R M} {x : M}
    (hx : f x ∈ Q.localized₀ p f) : ∃ u : p, u • x ∈ Q := by
  obtain ⟨m, hm, s, hs⟩ := (Submodule.mem_localized₀ p f (M' := Q) _).mp hx
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
  obtain ⟨c, hc⟩ : ∃ c : p, c • m = c • ((s : R) • x) :=
    IsLocalizedModule.exists_of_eq (S := p) hs
  refine ⟨c * s, ?_⟩
  have h1 : c • ((s : R) • x) ∈ Q := by
    rw [← hc]
    exact Q.smul_mem c hm
  have hbridge : c • ((s : R) • x) = ((c : R) * (s : R)) • x := by
    rw [Submonoid.smul_def, ← mul_smul]
  rwa [hbridge] at h1

/-- For `Q` primary with `S ∩ r_M(Q) = ∅`, a fraction `m/s` lies in `S⁻¹Q` iff `m ∈ Q`. -/
lemma mk'_mem_localized₀_iff {Q : Submodule R M} (hQ : Q.IsPrimary)
    (hdisj : Disjoint (p : Set R) (radIn Q : Set R)) (m : M) (s : p) :
    IsLocalizedModule.mk' f m s ∈ Q.localized₀ p f ↔ m ∈ Q := by
  constructor
  · intro h
    have h2 : s • IsLocalizedModule.mk' f m s ∈ Q.localized₀ p f :=
      (Q.localized₀ p f).smul_mem s h
    rw [IsLocalizedModule.mk'_cancel'] at h2
    obtain ⟨u, hu⟩ := exists_smul_mem_of_mem_comap (p := p) (f := f) h2
    exact mem_of_smul_mem_of_disjoint hQ hdisj u.2 hu
  · rintro hm
    exact ⟨m, hm, s, rfl⟩

/-- **(4.8) for modules, contraction.** If `Q` is primary and `S ∩ r_M(Q) = ∅`, then the
contraction of `S⁻¹Q` is `Q`. -/
theorem comap_localized₀_eq {Q : Submodule R M} (hQ : Q.IsPrimary)
    (hdisj : Disjoint (p : Set R) (radIn Q : Set R)) :
    (Q.localized₀ p f).comap f = Q := by
  refine le_antisymm ?_ (Submodule.map_le_iff_le_comap.mp (Submodule.map_le_localized₀ p f Q))
  intro x hx
  obtain ⟨u, hu⟩ := exists_smul_mem_of_mem_comap (p := p) (f := f) hx
  exact mem_of_smul_mem_of_disjoint hQ hdisj u.2 hu


/-- **(4.8) for modules, radical.** If `Q` is primary and `S ∩ r_M(Q) = ∅`, then
`r_N(S⁻¹Q) = r_M(Q)` (as ideals of `R`). -/
theorem radIn_localized₀ {Q : Submodule R M} (hQ : Q.IsPrimary)
    (hdisj : Disjoint (p : Set R) (radIn Q : Set R)) :
    radIn (Q.localized₀ p f) = radIn Q := by
  ext r
  rw [mem_radIn_iff, mem_radIn_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun m => ?_⟩
    have h1 : r ^ n • f m ∈ Q.localized₀ p f := hn (f m)
    rw [← map_smul] at h1
    have h2 : r ^ n • m ∈ (Q.localized₀ p f).comap f := h1
    rwa [comap_localized₀_eq hQ hdisj] at h2
  · rintro ⟨n, hn⟩
    refine ⟨n, fun y => ?_⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    exact (Submodule.mem_localized₀ p f (M' := Q) _).mpr
      ⟨r ^ n • m, hn m, s, IsLocalizedModule.mk'_smul f (r ^ n) m s⟩

/-- `a • ⊤ ≤ S` iff `a` acts by elements of `S`, for an element `a` of the base ring. -/
lemma smul_top_le_iff {S : Submodule R M} (a : R) :
    (a • (⊤ : Submodule R M) : Submodule R M) ≤ S ↔ ∀ m : M, a • m ∈ S := by
  rw [← Submodule.ideal_span_singleton_smul]
  constructor
  · intro h m
    simpa using Submodule.smul_le.mp h a (Ideal.mem_span_singleton_self a) m Submodule.mem_top
  · intro h
    refine Submodule.smul_le.mpr ?_
    intro b hb m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
    rw [mul_comm, mul_smul]
    exact S.smul_mem c (h m)

/-- **(4.8) for modules, primaryness of the localization.** If `Q` is primary and
`S ∩ r_M(Q) = ∅`, then `S⁻¹Q` is primary in `S⁻¹M`, with `r_N(S⁻¹Q) = r_M(Q)`
and `(S⁻¹Q) ∩ M = Q`. -/
theorem prop_4_8_i {Q : Submodule R M} (hQ : Q.IsPrimary)
    (hdisj : Disjoint (p : Set R) (radIn Q : Set R)) :
    (Q.localized₀ p f).IsPrimary ∧ radIn (Q.localized₀ p f) = radIn Q ∧
      (Q.localized₀ p f).comap f = Q := by
  have hcomap := comap_localized₀_eq (p := p) (f := f) hQ hdisj
  have hrad := radIn_localized₀ (p := p) (f := f) hQ hdisj
  refine ⟨⟨?_, ?_⟩, hrad, hcomap⟩
  · intro htop
    refine hQ.ne_top ?_
    rw [← hcomap, htop, Submodule.comap_top]
  · intro r y hry
    by_cases hy : y ∈ Q.localized₀ p f
    · exact Or.inl hy
    · right
      obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
      have hm : m ∉ Q := fun hm =>
        hy ((mk'_mem_localized₀_iff (p := p) (f := f) hQ hdisj m s).mpr hm)
      have hrm : r • m ∈ Q := by
        refine (mk'_mem_localized₀_iff (p := p) (f := f) hQ hdisj (r • m) s).mp ?_
        rw [IsLocalizedModule.mk'_smul f r m s]
        exact hry
      obtain ⟨n, hn⟩ := mem_radIn_iff.mp ((hQ.mem_or_mem hrm).resolve_left hm)
      exact ⟨n, (smul_top_le_iff (r ^ n)).mpr fun z => by
        obtain ⟨⟨m', s'⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f z
        exact (Submodule.mem_localized₀ p f (M' := Q) _).mpr
          ⟨r ^ n • m', hn m', s', IsLocalizedModule.mk'_smul f (r ^ n) m' s'⟩⟩

/-- **(4.8) for modules, vanishing.** If `Q` is primary and `S` meets `r_M(Q)`, then
`S⁻¹Q = S⁻¹M`. -/
theorem prop_4_8_ii {Q : Submodule R M} (_hQ : Q.IsPrimary)
    (hmeet : ∃ s ∈ p, s ∈ radIn Q) :
    Q.localized₀ p f = ⊤ := by
  obtain ⟨s, hsp, hs⟩ := hmeet
  obtain ⟨n, hn⟩ := mem_radIn_iff.mp hs
  refine le_antisymm le_top ?_
  intro y _
  obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
  have hpow : (⟨s ^ n, p.pow_mem hsp n⟩ : p) • m ∈ Q := by
    simpa [Submonoid.smul_def] using hn m
  have key : IsLocalizedModule.mk' f ((⟨s ^ n, p.pow_mem hsp n⟩ : p) • m)
      ((⟨s ^ n, p.pow_mem hsp n⟩ : p) * t) = IsLocalizedModule.mk' f m t :=
    IsLocalizedModule.mk'_cancel_left f m ⟨s ^ n, p.pow_mem hsp n⟩ t
  exact (Submodule.mem_localized₀ p f (M' := Q) _).mpr
    ⟨_, hpow, ⟨_, p.mul_mem (p.pow_mem hsp n) t.2⟩, key⟩

/-- **(4.8) for modules, converse direction.** Let `P ≤ S⁻¹M` be primary with
`S ∩ r(P) = ∅` and suppose `P` is `S`-saturated, i.e. `S⁻¹(P ∩ M) = P` (this always holds when
`P` is an `S⁻¹A`-submodule of an `S⁻¹A`-module). Then `P ∩ M` is primary in `M` with the same
radical and `S⁻¹(P ∩ M) = P`; together with `prop_4_8_i` this is the announced bijection. -/
theorem prop_4_8_iii {P : Submodule R N} (hP : P.IsPrimary)
    (hsat : (P.comap f).localized₀ p f = P) :
    (P.comap f).IsPrimary ∧ radIn (P.comap f) = radIn P := by
  have hrad1 : radIn P ≤ radIn (P.comap f) := by
    intro a ha
    obtain ⟨n, hn⟩ := mem_radIn_iff.mp ha
    refine mem_radIn_iff.mpr ⟨n, fun m => ?_⟩
    rw [Submodule.mem_comap, map_smul]
    exact hn (f m)
  have hrad2 : radIn (P.comap f) ≤ radIn P := by
    intro a ha
    obtain ⟨n, hn⟩ := mem_radIn_iff.mp ha
    have hle : (a ^ n • (⊤ : Submodule R M)) ≤ P.comap f :=
      (smul_top_le_iff (a ^ n)).mpr hn
    have hmono : (a ^ n • (⊤ : Submodule R M)).localized₀ p f ≤ P := by
      rw [← hsat]
      exact Submodule.localized₀_le_localized₀_of_smul_le p f (1 : p) (by simpa using hle)
    have heq : (a ^ n • (⊤ : Submodule R M)).localized₀ p f = a ^ n • (⊤ : Submodule R N) := by
      rw [← Submodule.ideal_span_singleton_smul (a ^ n) (⊤ : Submodule R M),
        Submodule.localized₀_smul, Submodule.localized₀_top,
        Submodule.ideal_span_singleton_smul]
    rw [heq] at hmono
    exact mem_radIn_iff.mpr ⟨n, (smul_top_le_iff (a ^ n)).mp hmono⟩
  refine ⟨⟨?_, ?_⟩, le_antisymm hrad2 hrad1⟩
  · intro htop
    have h1 : (⊤ : Submodule R M).localized₀ p f = P := by rw [← htop]; exact hsat
    rw [Submodule.localized₀_top] at h1
    exact hP.ne_top h1.symm
  · intro a z haz
    by_cases hz : z ∈ P.comap f
    · exact Or.inl hz
    · right
      have hz' : f z ∉ P := hz
      have haz' : a • f z ∈ P := by
        rw [← map_smul]
        exact haz
      have ha : a ∈ radIn P := (hP.mem_or_mem haz').resolve_left hz'
      obtain ⟨n, hn⟩ := mem_radIn_iff.mp (hrad1 ha)
      exact ⟨n, (smul_top_le_iff (a ^ n)).mpr hn⟩

/-- **(4.9) for modules.** Let `N = ⋂_{q ∈ t} q` be a minimal primary decomposition of `N` in `M`
and let `S` be a multiplicatively closed subset of `A`. Let `s` be the set of those `q ∈ t` with
`S ∩ r_M(q) = ∅`. Then
* `S⁻¹N = ⋂_{q ∈ s} S⁻¹q` is a (minimal) primary decomposition in the localized module, and
* its contraction `S(N) = (S⁻¹N) ∩ M` is `⋂_{q ∈ s} q`, a minimal primary decomposition of `S(N)`. -/
theorem prop_4_9 {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t)
    [DecidablePred fun q : Submodule R M => Disjoint (p : Set R) (radIn q : Set R)] :
    N.localized₀ p f
        = (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).inf
            (fun q => q.localized₀ p f) ∧
      (N.localized₀ p f).comap f
        = (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).inf id ∧
      (∀ q ∈ t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R)),
        (q.localized₀ p f).IsPrimary ∧ radIn (q.localized₀ p f) = radIn q) ∧
      ((N.localized₀ p f).comap f).IsMinimalPrimaryDecomposition
        (t.filter fun q => Disjoint (p : Set R) (radIn q : Set R)) := by
  classical
  have hbase : N.localized₀ p f = t.inf (fun q => q.localized₀ p f) := by
    rw [← ht.inf_eq]
    exact map_finset_inf (Submodule.localized₀FrameHom p f) t id
  have hstep : t.inf (fun q => q.localized₀ p f)
      = t.inf (fun q => if Disjoint (p : Set R) (radIn q : Set R)
          then q.localized₀ p f else ⊤) := by
    refine Finset.inf_congr rfl (fun q hq => ?_)
    by_cases h : Disjoint (p : Set R) (radIn q : Set R)
    · rw [if_pos h]
    · rw [if_neg h]
      exact prop_4_8_ii (p := p) (f := f) (ht.primary hq) (Set.not_disjoint_iff.mp h)
  have hfilter : t.inf (fun q => if Disjoint (p : Set R) (radIn q : Set R)
        then q.localized₀ p f else ⊤)
      = (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).inf
          (fun q => q.localized₀ p f) := by
    rw [Finset.inf_ite, Finset.inf_top, inf_top_eq]
  have ha : N.localized₀ p f
      = (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).inf
          (fun q => q.localized₀ p f) := hbase.trans (hstep.trans hfilter)
  have hcomap : (N.localized₀ p f).comap f
      = (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).inf id := by
    rw [ha, Submodule.comap_finsetInf]
    refine Finset.inf_congr rfl (fun q hq => ?_)
    exact (prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
      (Finset.mem_filter.mp hq).2).2.2
  refine ⟨ha, hcomap, ?_, ?_⟩
  · intro q hq
    exact ⟨(prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
      (Finset.mem_filter.mp hq).2).1,
      (prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
        (Finset.mem_filter.mp hq).2).2.1⟩
  refine ⟨hcomap.symm, ?_, ?_, ?_⟩
  · intro q hq
    exact ht.primary (Finset.mem_of_mem_filter q hq)
  · exact ht.distinct.mono (fun q hq => Finset.mem_of_mem_filter q hq)
  · intro q hq hle
    have hqt : q ∈ t := Finset.mem_of_mem_filter q hq
    refine ht.minimal hqt (le_trans ?_ hle)
    refine Finset.le_inf (fun r hr => ?_)
    exact Finset.inf_le (f := id) (Finset.mem_of_subset (Finset.erase_subset_erase q
      (Finset.filter_subset _ _)) hr)

attribute [local instance] Classical.decEq

/-- **(4.10) for modules (second uniqueness theorem).** Let `Sig` be an isolated set of primes
belonging to `N` (i.e. `Sig` is downward closed for the inclusion order on associated primes), and
let `N = ⋂_{q ∈ t} q` and `N = ⋂_{q' ∈ u} q'` be two minimal primary decompositions. Then the
intersection of the components whose radicals lie in `Sig` does not depend on the decomposition. -/
theorem prop_4_10 {N : Submodule R M} {t u : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) (hu : N.IsMinimalPrimaryDecomposition u)
    (Sig : Finset N.associatedPrimes) (hSig : IsLowerSet (Sig : Set N.associatedPrimes)) :
    ((t.attach.filter (fun q =>
        (⟨radIn q.1, ht.mem_associatedPrimes q.2⟩ : N.associatedPrimes) ∈ Sig)).inf (fun q => q.1))
      = ((u.attach.filter (fun q =>
        (⟨radIn q.1, hu.mem_associatedPrimes q.2⟩ : N.associatedPrimes) ∈ Sig)).inf (fun q => q.1)) := by
  set S : Submonoid R := ⨅ P ∈ Sig, P.1.primeCompl with hS
  have key : ∀ (d : Finset (Submodule R M)) (hd : N.IsMinimalPrimaryDecomposition d),
      (N.localized₀ S (LocalizedModule.mkLinearMap S M)).comap (LocalizedModule.mkLinearMap S M)
        = (d.attach.filter (fun q =>
          (⟨radIn q.1, hd.mem_associatedPrimes q.2⟩ : N.associatedPrimes) ∈ Sig)).inf (fun q => q.1) := by
    intro d hd
    set sd : Finset (Submodule R M) :=
      (d.attach.filter (fun q =>
        (⟨radIn q.1, hd.mem_associatedPrimes q.2⟩ : N.associatedPrimes) ∈ Sig)).image Subtype.val with hsd
    have hsub : sd ⊆ d := by
      intro q hq
      obtain ⟨q', hq', hqe⟩ := Finset.mem_image.mp hq
      rw [← hqe]
      exact q'.2
    have hmain := Submodule.IsMinimalPrimaryDecomposition.comap_localized₀_eq_iInf
      (N := N) hd Sig hSig sd hsub (by
        ext P
        constructor
        · intro hP
          obtain ⟨q, hq, hqP⟩ := Finset.mem_image.mp hP
          obtain ⟨q', hq', hqe⟩ := Finset.mem_image.mp hq
          rw [← hqP, ← hqe]
          exact Finset.mem_image.mpr
            ⟨(⟨radIn q'.1, hd.mem_associatedPrimes q'.2⟩ : N.associatedPrimes),
              (Finset.mem_filter.mp hq').2, rfl⟩
        · intro hP
          obtain ⟨P', hP', hPP⟩ := Finset.mem_image.mp hP
          set pv : Ideal R := (P' : Ideal R) with hpv
          have hmem : pv ∈ N.associatedPrimes := P'.2
          have hmem2 : pv ∈ (fun J => (J.colon Set.univ).radical) '' (d : Set (Submodule R M)) := by
            rw [hd.image_radical_eq_associated_primes]
            exact hmem
          obtain ⟨q, hq, hqP⟩ := hmem2
          have hqP' : radIn q = (P' : Ideal R) := hqP.trans hpv
          have hsub' : (⟨radIn q, hd.mem_associatedPrimes hq⟩ : N.associatedPrimes) = P' :=
            Subtype.ext hqP'
          have hmem' : (⟨radIn q, hd.mem_associatedPrimes hq⟩ : N.associatedPrimes) ∈ Sig := by
            rw [hsub']; exact hP'
          refine Finset.mem_image.mpr ⟨q, ?_, hqP'.trans hPP⟩
          exact Finset.mem_image.mpr ⟨⟨q, hq⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_attach d ⟨q, hq⟩, hmem'⟩, rfl⟩)
    rw [hmain, ← Finset.inf_eq_iInf, hsd]
    exact Finset.inf_image _ Subtype.val id
  rw [← key t ht, ← key u hu]

/-- **(4.11) for modules.** Let `p` be a minimal element of the set of primes belonging to `N`
(in particular `p` may be any minimal prime ideal over `Ann(M ⧸ N)`). Then its primary component is
independent of the chosen minimal primary decomposition: this is the case `Sig = {p}` of (4.10). -/
theorem prop_4_11 {N : Submodule R M} {t u : Finset (Submodule R M)}
    (ht : N.IsMinimalPrimaryDecomposition t) (hu : N.IsMinimalPrimaryDecomposition u)
    {p : Ideal R} (hp : p ∈ N.associatedPrimes)
    (hmin : ∀ r ∈ N.associatedPrimes, r ≤ p → r = p)
    {q : Submodule R M} (hq : q ∈ t) (hqp : radIn q = p)
    {q' : Submodule R M} (hq' : q' ∈ u) (hq'p : radIn q' = p) : q = q' := by
  classical
  have hSig : IsLowerSet (({⟨p, hp⟩} : Finset N.associatedPrimes) : Set N.associatedPrimes) := by
    intro P Q hQP hP
    rw [Finset.mem_coe, Finset.mem_singleton] at hP ⊢
    have hle : (Q : Ideal R) ≤ p := by
      rw [hP] at hQP
      exact hQP
    exact Subtype.ext (hmin Q.1 Q.2 hle)
  have h10 := prop_4_10 ht hu {⟨p, hp⟩} hSig
  have key : ∀ (d : Finset (Submodule R M)) (hd : N.IsMinimalPrimaryDecomposition d)
      (r : Submodule R M), r ∈ d → radIn r = p →
      (d.attach.filter (fun x =>
        (⟨radIn x.1, hd.mem_associatedPrimes x.2⟩ : N.associatedPrimes) ∈
          ({⟨p, hp⟩} : Finset N.associatedPrimes))).inf (fun x => x.1) = r := by
    intro d hd r hr hrp
    have hsingle : (d.attach.filter (fun x =>
        (⟨radIn x.1, hd.mem_associatedPrimes x.2⟩ : N.associatedPrimes) ∈
          ({⟨p, hp⟩} : Finset N.associatedPrimes))) = ({⟨r, hr⟩} : Finset {x // x ∈ d}) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_attach, Finset.mem_singleton, true_and]
      constructor
      · intro h
        have hx : radIn x.1 = radIn r := by
          rw [hrp]
          exact congrArg Subtype.val h
        exact Subtype.ext (hd.injOn N d x.2 hr hx)
      · intro h
        rw [h]
        exact Subtype.ext hrp
    rw [hsingle, Finset.inf_singleton]
  rw [key t ht q hq hqp, key u hu q' hq' hq'p] at h10
  exact h10

/-- **(4.9) for modules, localized side.**  The localized family
`{S⁻¹q | q ∈ t, S ∩ r_M(q) = ∅}` is itself a *minimal* primary decomposition of the localized
submodule `S⁻¹N`: it is primary componentwise, it has pairwise distinct radicals, no component is
redundant, and its intersection is `S⁻¹N`. -/
theorem prop_4_9_localized {N₀ : Submodule R M} {t : Finset (Submodule R M)}
    (ht : N₀.IsMinimalPrimaryDecomposition t)
    [DecidablePred fun q : Submodule R M => Disjoint (p : Set R) (radIn q : Set R)] :
    (N₀.localized₀ p f).IsMinimalPrimaryDecomposition
      ((t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).image
        (fun q => q.localized₀ p f)) := by
  classical
  have hprim : ∀ ⦃J : Submodule R N⦄,
      J ∈ (t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).image
        (fun q => q.localized₀ p f) → J.IsPrimary := by
    intro J hJ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hJ
    exact (prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
      (Finset.mem_filter.mp hq).2).1
  have hrad : ∀ q ∈ t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R)),
      radIn (q.localized₀ p f) = radIn q := fun q hq =>
    (prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
      (Finset.mem_filter.mp hq).2).2.1
  have hcomap : ∀ q ∈ t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R)),
      (q.localized₀ p f).comap f = q := fun q hq =>
    (prop_4_8_i (p := p) (f := f) (ht.primary (Finset.mem_of_mem_filter q hq))
      (Finset.mem_filter.mp hq).2).2.2
  refine ⟨?_, hprim, ?_, ?_⟩
  · rw [Finset.inf_image]
    exact ((prop_4_9 (p := p) (f := f) ht).1).symm
  · intro J₁ hJ₁ J₂ hJ₂ hne hradeq
    apply hne
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hJ₁
    obtain ⟨q₂, hq₂, rfl⟩ := Finset.mem_image.mp hJ₂
    have h1 := hrad q₁ hq₁
    have h2 := hrad q₂ hq₂
    have h12 : radIn q₁ = radIn q₂ := by rw [← h1, ← h2]; exact hradeq
    rw [ht.injOn N₀ t (Finset.mem_of_mem_filter q₁ hq₁) (Finset.mem_of_mem_filter q₂ hq₂) h12]
  · intro J hJ hle
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨x, hxmem, hxnot⟩ := SetLike.not_le_iff_exists.mp
      (ht.minimal (Finset.mem_of_mem_filter q₀ hq₀))
    have hx_in : f x ∈ (((t.filter (fun q => Disjoint (p : Set R) (radIn q : Set R))).image
        (fun q => q.localized₀ p f)).erase (q₀.localized₀ p f)).inf id := by
      rw [Submodule.mem_finsetInf]
      intro J' hJ'
      obtain ⟨hJ'ne, hJ'mem⟩ := Finset.mem_erase.mp hJ'
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hJ'mem
      have hq'ne : q' ≠ q₀ := by
        intro h
        exact hJ'ne (by rw [h])
      have hxq' : x ∈ q' :=
        (Finset.inf_le (f := id) (Finset.mem_erase.mpr
          ⟨hq'ne, Finset.mem_of_mem_filter q' hq'⟩)) hxmem
      exact (Submodule.mem_localized₀ p f (M' := q') _).mpr
        ⟨x, hxq', 1, IsLocalizedModule.mk'_one p f x⟩
    have : x ∈ (q₀.localized₀ p f).comap f := hle hx_in
    rw [hcomap q₀ hq₀] at this
    exact hxnot this

end Localization

section SModules

variable {S : Type*} [CommRing S] [Algebra R S] {p : Submonoid R} [IsLocalization p S]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable {f : M →ₗ[R] N} [IsLocalizedModule p f]

/-- For an `S⁻¹A`-submodule `P` of the localized module, extension recovers `P` from its contraction:
`S⁻¹(P ∩ M) = P`.  This is the saturation property used in the converse part of (4.8). -/
theorem localized₀_comap_restrictScalars (P : Submodule S N) :
    ((P.restrictScalars R).comap f).localized₀ p f = P.restrictScalars R := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨m, hm, s, rfl⟩ :=
      (Submodule.mem_localized₀ p f (M' := (P.restrictScalars R).comap f) x).mp hx
    have hfm : f m ∈ P := hm
    have hSm : ((algebraMap R S) (s : R)) • (IsLocalizedModule.mk' f m s) ∈ P := by
      rw [IsScalarTower.algebraMap_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
      exact hfm
    obtain ⟨u, hu⟩ := (IsLocalization.map_units S s).exists_left_inv
    have hxP : u • (((algebraMap R S) (s : R)) • IsLocalizedModule.mk' f m s) ∈ P :=
      P.smul_mem u hSm
    have heq : IsLocalizedModule.mk' f m s
        = u • (((algebraMap R S) (s : R)) • IsLocalizedModule.mk' f m s) := by
      rw [← mul_smul, hu, one_smul]
    rw [heq]
    exact hxP
  · intro y hy
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    refine (Submodule.mem_localized₀ p f (M' := (P.restrictScalars R).comap f) _).mpr ⟨m, ?_, s, rfl⟩
    have hfm : f m ∈ P := by
      rw [← IsLocalizedModule.mk'_cancel' f m s, Submonoid.smul_def]
      exact (P.restrictScalars R).smul_mem (s : R) hy
    exact hfm

/-- **(4.8), converse direction in the book's setting.**  If `P ≤ S⁻¹M` is an `S⁻¹A`-submodule that
is primary, then `P ∩ M` is primary in `M`, with the same radical, and `S⁻¹(P ∩ M) = P`.
Together with `prop_4_8_i` this is the bijection of Proposition 4.8. -/
theorem prop_4_8_iii' {P : Submodule S N} (hP : (P.restrictScalars R).IsPrimary) :
    ((P.restrictScalars R).comap f).IsPrimary ∧
      radIn ((P.restrictScalars R).comap f) = radIn (P.restrictScalars R) ∧
      ((P.restrictScalars R).comap f).localized₀ p f = P.restrictScalars R := by
  have h := prop_4_8_iii (p := p) (f := f) hP (localized₀_comap_restrictScalars (p := p) (f := f) P)
  exact ⟨h.1, h.2, localized₀_comap_restrictScalars (p := p) (f := f) P⟩

end SModules

end AtiyahMcdonald69.Ex_4_23
