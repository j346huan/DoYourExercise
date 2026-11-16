/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atiyah–Macdonald, Exercise 4.9

In a ring `A`, let `D(A)` denote the set of prime ideals `p` for which there exists `a ∈ A`
such that `p` is minimal in the set of prime ideals containing `(0 : a)`.  We show

1. `x ∈ A` is a zero divisor iff `x ∈ p` for some `p ∈ D(A)`;
2. for a multiplicatively closed subset `S`, after identifying `Spec (S⁻¹A)` with its image in
   `Spec A`, one has `D(S⁻¹A) = D(A) ∩ Spec (S⁻¹A)`;
3. if the zero ideal has a primary decomposition, then `D(A)` is the set of associated prime
   ideals of `0`.

The statements are formalized with Mathlib's `Ideal.minimalPrimes` ("minimal prime over an
ideal"), `Localization`/`IsLocalization` (for `S⁻¹A`) and `associatedPrimes A A` (the associated
primes of the zero ideal of `A`, i.e. of the module `A`; Mathlib defines `p` to be associated
to `0` when `p = (0 : x).radical` for some `x`, which is the definition valid for non-Noetherian
rings, cf. A–M Theorem 4.5).
-/

import Mathlib

-- So that `Finset.filter` can be used in statements without carrying `DecidablePred` arguments.
attribute [local instance] Classical.propDecidable

namespace AtiyahMcdonald69.Ex_4_9

variable {A : Type*} [CommRing A]

/-- The annihilator `(0 : a)` of an element `a`, as a colon ideal. -/
def ann (a : A) : Ideal A := Submodule.colon (⊥ : Ideal A) {a}

lemma mem_ann {a x : A} : x ∈ ann a ↔ x * a = 0 := by
  rw [ann, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]

@[simp]
lemma ann_zero : ann (0 : A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_ann, mul_zero]

lemma ann_eq_top_iff {a : A} : ann a = ⊤ ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ ann_zero⟩
  have h1 : (1 : A) ∈ ann a := h ▸ Submodule.mem_top
  rwa [mem_ann, one_mul] at h1

/-- `D A` is the set of prime ideals `p` for which there is `a : A` such that `p` is minimal
among the prime ideals containing the annihilator `(0 : a)`. -/
def D (A : Type*) [CommRing A] : Set (Ideal A) :=
  {p | p.IsPrime ∧ ∃ a : A, p ∈ (ann a).minimalPrimes}

set_option linter.style.haveILetI false in
/-- For `a ≠ 0` there is a prime ideal minimal over the annihilator `(0 : a)`. -/
lemma exists_minimal_prime_over_ann (a : A) (ha : a ≠ 0) :
    ∃ p ∈ (ann a).minimalPrimes, ann a ≤ p := by
  have h : ann a ≠ ⊤ := fun h => ha (ann_eq_top_iff.mp h)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (ann a) h
  haveI : m.IsMaximal := hm
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := ann a) hle
  exact ⟨p, hp, hp.le⟩

/-- **Exercise 4.9 (a)**: `x` is a zero divisor iff `x` lies in some `p ∈ D(A)`. -/
theorem notMem_nonZeroDivisors_iff_exists_mem_D (x : A) :
    x ∉ nonZeroDivisors A ↔ ∃ p ∈ D A, x ∈ p := by
  constructor
  · intro hx
    have hx' : ∃ y, x * y = 0 ∧ y ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by
        rw [mem_nonZeroDivisors_iff]
        exact ⟨h, fun y hy => h y (by rwa [mul_comm] at hy)⟩)
    obtain ⟨y, hxy, hy⟩ := hx'
    obtain ⟨p, hp, hlep⟩ := exists_minimal_prime_over_ann y hy
    exact ⟨p, ⟨hp.isPrime, y, hp⟩, hlep (mem_ann.mpr hxy)⟩
  · rintro ⟨p, ⟨-, a, ha⟩, hxp⟩
    obtain ⟨y, hya, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes ha hxp
    have hy : y * a ≠ 0 := fun h => hya (mem_ann.mpr h)
    have h0 : x * (y * a) = 0 := by rw [← mul_assoc]; exact mem_ann.mp hxy
    rw [mem_nonZeroDivisors_iff]
    intro h
    exact hy (h.1 _ h0)

/-- The literal form of part (a): `x` is a zero divisor (there is `y ≠ 0` with `xy = 0`) iff
`x` lies in some `p ∈ D(A)`. -/
theorem exists_mul_eq_zero_iff_exists_mem_D (x : A) :
    (∃ y : A, y ≠ 0 ∧ x * y = 0) ↔ ∃ p ∈ D A, x ∈ p := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine (notMem_nonZeroDivisors_iff_exists_mem_D x).mp ?_
    rw [mem_nonZeroDivisors_iff]
    intro h
    exact hy (h.1 y hxy)
  · intro h
    have hx := (notMem_nonZeroDivisors_iff_exists_mem_D x).mpr h
    by_contra hcon
    push Not at hcon
    exact hx (by
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun y hy => by_contra fun hy0 => hcon y hy0 hy,
        fun y hy => by_contra fun hy0 => hcon y hy0 (by rwa [mul_comm] at hy)⟩)

section Localization

variable {B : Type*} [CommRing B] [Algebra A B]

/-- Annihilators are unaffected by multiplication by a unit. -/
lemma ann_mul_unit {x u : B} (hu : IsUnit u) : ann (x * u) = ann x := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  ext y
  rw [mem_ann, mem_ann]
  constructor
  · intro h
    calc y * x = (y * x) * (u * v) := by rw [hv, mul_one]
      _ = (y * (x * u)) * v := by ring
      _ = 0 := by rw [h, zero_mul]
  · intro h
    rw [← mul_assoc, h, zero_mul]

/-- The annihilator of `r/s` in `S⁻¹A` is the annihilator of `r`. -/
lemma ann_mk' {T : Submonoid A} [IsLocalization T B] (r : A) (s : T) :
    ann (IsLocalization.mk' B r s) = ann (algebraMap A B r) := by
  have h := ann_mul_unit (x := IsLocalization.mk' B r s) (IsLocalization.map_units B s)
  rw [IsLocalization.mk'_spec B] at h
  exact h.symm

/-- `(0 : a)` commutes with localization: `(0 : a)S⁻¹A = (0 : a/1)`. -/
lemma ann_map (T : Submonoid A) [IsLocalization T B] (a : A) :
    (ann a).map (algebraMap A B) = ann (algebraMap A B a) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [mem_ann] at hy
    rw [Ideal.mem_comap, mem_ann]
    rw [← map_mul, hy, map_zero]
  · intro z hz
    rw [mem_ann] at hz
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    have h2 : algebraMap A B (r * a) = 0 := by
      rw [map_mul, ← IsLocalization.mk'_spec B r s, mul_right_comm, hz, zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff T B (r * a)).mp h2
    exact ⟨c, c.2, by rw [mem_ann, mul_assoc]; exact hc⟩

/-- **Exercise 4.9 (b)**: after identifying `Spec (S⁻¹A)` with its image in `Spec A` (i.e.
sending a prime `P` of `S⁻¹A` to its contraction `P ∩ A`), `D(S⁻¹A) = D(A) ∩ Spec (S⁻¹A)`.
We state it as: for a prime `P` of `S⁻¹A`, `P ∈ D(S⁻¹A) ↔ P ∩ A ∈ D(A)`. -/
theorem mem_D_localization_iff (T : Submonoid A) [IsLocalization T B] (P : Ideal B) [P.IsPrime] :
    P ∈ D B ↔ P.under A ∈ D A := by
  constructor
  · rintro ⟨-, b, hb⟩
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq T b
    rw [ann_mk' (T := T) r s, ← ann_map T r, IsLocalization.minimalPrimes_map T B (ann r),
      Set.mem_preimage] at hb
    exact ⟨inferInstance, r, hb⟩
  · rintro ⟨-, a, ha⟩
    refine ⟨inferInstance, algebraMap A B a, ?_⟩
    rw [← ann_map T a, IsLocalization.minimalPrimes_map T B (ann a)]
    exact ha

set_option linter.style.haveILetI false in
/-- **Exercise 4.9 (b)**, set form: `D(S⁻¹A) = D(A) ∩ Spec (S⁻¹A)`, i.e. a prime of `S⁻¹A`
belongs to `D(S⁻¹A)` exactly when its contraction to `A` belongs to `D(A)`. -/
theorem D_localization_eq (T : Submonoid A) [IsLocalization T B] :
    D B = {P : Ideal B | P.IsPrime ∧ P.under A ∈ D A} := by
  ext P
  constructor
  · rintro ⟨hP, hPD⟩
    haveI := hP
    exact ⟨hP, (mem_D_localization_iff T P).mp ⟨hP, hPD⟩⟩
  · rintro ⟨hP, hPD⟩
    haveI := hP
    exact (mem_D_localization_iff T P).mpr hPD

/-- The contraction map `Spec (S⁻¹A) → Spec A` is injective, which is what allows us to identify
`Spec (S⁻¹A)` with its image in `Spec A` in part (b). -/
theorem under_injective (T : Submonoid A) [IsLocalization T B] (P Q : Ideal B)
    (h : P.under A = Q.under A) : P = Q := by
  rw [← IsLocalization.map_under T B P, ← IsLocalization.map_under T B Q, h]

set_option linter.style.haveILetI false in
/-- The other half of the identification: a prime `p` of `A` disjoint from `S` lies in `D(A)`
iff `pS⁻¹A` lies in `D(S⁻¹A)`. -/
theorem mem_D_iff_map_mem_D_localization (T : Submonoid A) [IsLocalization T B]
    (p : Ideal A) [hp : p.IsPrime] (hT : Disjoint (T : Set A) (p : Set A)) :
    p ∈ D A ↔ p.map (algebraMap A B) ∈ D B := by
  haveI : (p.map (algebraMap A B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint T B p hp hT
  rw [mem_D_localization_iff T (p.map (algebraMap A B)),
    IsLocalization.under_map_of_isPrime_disjoint T B hp hT]

/-- Exercise 4.9 (b) for the localization `S⁻¹A` itself. -/
theorem D_localization (T : Submonoid A) :
    D (Localization T) = {P : Ideal (Localization T) | P.IsPrime ∧ P.under A ∈ D A} :=
  D_localization_eq T

end Localization

section PrimaryDecomposition

/-- A prime which is the radical of `I` is minimal among the primes containing `I`. -/
lemma mem_minimalPrimes_of_radical_eq {I p : Ideal A} (hp : p.IsPrime) (h : I.radical = p) :
    p ∈ I.minimalPrimes := by
  refine ⟨⟨hp, h ▸ Ideal.le_radical⟩, ?_⟩
  intro q hq hqp
  have h1 : I.radical ≤ q := hq.1.radical_le_iff.mpr hq.2
  rwa [h] at h1

/-- The radical of the annihilator of `a` is computed from a minimal primary decomposition of
the zero ideal: it is the intersection of the radicals of the primary components which do not
contain `a` (Atiyah–Macdonald's formula `r(0 : a) = ⋂_{a ∉ q_i} r(q_i)`). -/
lemma radical_ann_eq (t : Finset (Ideal A))
    (ht : Submodule.IsMinimalPrimaryDecomposition (⊥ : Ideal A) t) (a : A) :
    (ann a).radical = (t.filter (fun q => a ∉ q)).inf (fun q => q.radical) := by
  classical
  have h1 : ann a = t.inf (fun q => q.colon {a}) := by
    rw [ann, ← ht.inf_eq, Submodule.colon_finsetInf]
    rfl
  have h2 : (t.inf (fun q => q.colon {a})).radical = t.inf (fun q => (q.colon {a}).radical) := by
    rw [← Ideal.radicalInfTopHom_apply, map_finset_inf]
    rfl
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · rw [Finset.le_inf_iff]
    intro q hq
    rw [Finset.mem_filter] at hq
    calc (t.inf fun q => (q.colon {a}).radical) ≤ (q.colon {a}).radical := Finset.inf_le hq.1
      _ = q.radical := by
            rw [(ht.primary hq.1).radical_colon_singleton_of_notMem hq.2, Submodule.colon_univ]
  · rw [Finset.le_inf_iff]
    intro q hqt
    by_cases hq : a ∈ q
    · have htop : q.colon {a} = ⊤ :=
        (Submodule.colon_eq_top_iff_subset {a}).mpr (by simpa using hq)
      rw [htop, Ideal.radical_top]
      exact le_top
    · refine (Finset.inf_le (Finset.mem_filter.mpr ⟨hqt, hq⟩)).trans ?_
      rw [(ht.primary hqt).radical_colon_singleton_of_notMem hq, Submodule.colon_univ]

/-- One inclusion of part (c) needs no hypothesis: every associated prime of the zero ideal is
the radical of an annihilator, hence is minimal over it and so lies in `D(A)`. -/
theorem associatedPrimes_subset_D : associatedPrimes A A ⊆ D A := by
  rintro p ⟨hp, a, ha⟩
  exact ⟨hp, a, mem_minimalPrimes_of_radical_eq hp ha.symm⟩

/-- **Exercise 4.9 (c)**: if the zero ideal has a primary decomposition, then `D(A)` is the set
of associated prime ideals of the zero ideal. -/
theorem D_eq_associatedPrimes
    (h : ∃ t : Finset (Ideal A), t.inf id = ⊥ ∧ ∀ q ∈ t, q.IsPrimary) :
    D A = associatedPrimes A A := by
  classical
  obtain ⟨s, hs, hsp⟩ := h
  obtain ⟨t, ht_inf, ht_prim, ht_dist, ht_min⟩ :=
    Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition (N := (⊥ : Ideal A)) hs
      hsp
  have ht : Submodule.IsMinimalPrimaryDecomposition (⊥ : Ideal A) t :=
    ⟨ht_inf, ht_prim, ht_dist, ht_min⟩
  have hAss : (fun q : Ideal A => q.radical) '' t = associatedPrimes A A := by
    have h' := ht.image_radical_eq_associated_primes
    rw [show Submodule.associatedPrimes (⊥ : Ideal A) = associatedPrimes A A from rfl] at h'
    simpa only [Submodule.colon_univ] using h'
  rw [← hAss]
  refine Set.Subset.antisymm ?_ ?_
  · -- a prime minimal over some `(0 : a)` is the radical of a primary component
    rintro p ⟨hpprime, a, ha⟩
    -- (`a ≠ 0`, since `ann 0 = ⊤` has no minimal prime, so the filter below is nonempty and
    -- `IsPrime.inf_le'` will produce a component)
    have hle : (t.filter (fun q : Ideal A => a ∉ q)).inf (fun q => q.radical) ≤ p := by
      rw [← radical_ann_eq t ht a]
      exact hpprime.radical_le_iff.mpr ha.le
    obtain ⟨q, hq_mem, hqp⟩ := hpprime.inf_le'.mp hle
    rw [Finset.mem_filter] at hq_mem
    have hqprime : (Ideal.radical q).IsPrime := Ideal.isPrime_radical (ht.primary hq_mem.1)
    have hann : ann a ≤ Ideal.radical q := by
      intro x hx
      have hxa : x * a ∈ q := by rw [mem_ann.mp hx]; exact q.zero_mem
      rcases (ht.primary hq_mem.1).mem_or_mem (by simpa [smul_eq_mul] using hxa) with h' | h'
      · exact absurd h' hq_mem.2
      · rwa [Submodule.colon_univ] at h'
    have hpq : p = Ideal.radical q := le_antisymm (ha.2 ⟨hqprime, hann⟩ hqp) hqp
    exact ⟨q, hq_mem.1, hpq.symm⟩
  · -- conversely every radical of a component is of the form `r(0 : a)`
    rintro p ⟨q, hqt, rfl⟩
    have hmin := ht.minimal hqt
    rw [SetLike.not_le_iff_exists] at hmin
    obtain ⟨a, ha_inf, haq⟩ := hmin
    have ha_mem : ∀ r ∈ t.erase q, a ∈ r := by
      rw [← Submodule.mem_finsetInf]
      exact ha_inf
    have hfilter : t.filter (fun r => a ∉ r) = {q} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hrt, hra⟩
        by_contra hne
        exact hra (ha_mem r (Finset.mem_erase.mpr ⟨hne, hrt⟩))
      · rintro rfl
        exact ⟨hqt, haq⟩
    refine ⟨Ideal.isPrime_radical (ht.primary hqt), a, ?_⟩
    refine mem_minimalPrimes_of_radical_eq (Ideal.isPrime_radical (ht.primary hqt)) ?_
    rw [radical_ann_eq t ht a, hfilter, Finset.inf_singleton]

/-- In a Noetherian ring the zero ideal always has a primary decomposition (Lasker–Noether), so
part (c) applies unconditionally. -/
theorem D_eq_associatedPrimes_of_isNoetherian [IsNoetherianRing A] :
    D A = associatedPrimes A A := by
  obtain ⟨s, hs, hsp⟩ := Submodule.isLasker A A (⊥ : Ideal A)
  exact D_eq_associatedPrimes ⟨s, hs, hsp⟩

/-- The explicit form of part (c): for a minimal primary decomposition
`(0) = ⋂_{q ∈ t} q` of the zero ideal, `D(A)` is exactly the set of prime ideals `r(q)`
belonging to the decomposition. -/
theorem D_eq_image_radical (t : Finset (Ideal A))
    (ht : Submodule.IsMinimalPrimaryDecomposition (⊥ : Ideal A) t) :
    D A = (fun q : Ideal A => Ideal.radical q) '' t := by
  classical
  have h' := ht.image_radical_eq_associated_primes
  rw [show Submodule.associatedPrimes (⊥ : Ideal A) = associatedPrimes A A from rfl] at h'
  have hAss : (fun q : Ideal A => Ideal.radical q) '' t = associatedPrimes A A := by
    simpa only [Submodule.colon_univ] using h'
  rw [D_eq_associatedPrimes ⟨t, ht.inf_eq, ht.primary⟩, ← hAss]

/-- The hypothesis of part (c) is satisfiable: in `ℤ` the zero ideal is primary (indeed prime),
so `D(ℤ)` is the set of associated primes of `0`. -/
example : D ℤ = associatedPrimes ℤ ℤ := by
  refine D_eq_associatedPrimes ⟨{⊥}, ?_, ?_⟩
  · simp
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact (inferInstance : (⊥ : Ideal ℤ).IsPrime).isPrimary

/-- End-to-end check of part (c) in a concrete ring: in `ℤ` the zero ideal is prime hence
primary, and `D(ℤ) = {0}`. -/
example : D ℤ = {⊥} := by
  have ht : Submodule.IsMinimalPrimaryDecomposition (⊥ : Ideal ℤ) {⊥} := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact (inferInstance : (⊥ : Ideal ℤ).IsPrime).isPrimary
    · simp
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      simp
  rw [D_eq_image_radical {⊥} ht]
  simp

end PrimaryDecomposition

end AtiyahMcdonald69.Ex_4_9

#print axioms AtiyahMcdonald69.Ex_4_9.notMem_nonZeroDivisors_iff_exists_mem_D
#print axioms AtiyahMcdonald69.Ex_4_9.exists_mul_eq_zero_iff_exists_mem_D
#print axioms AtiyahMcdonald69.Ex_4_9.D_localization_eq
#print axioms AtiyahMcdonald69.Ex_4_9.under_injective
#print axioms AtiyahMcdonald69.Ex_4_9.D_localization
#print axioms AtiyahMcdonald69.Ex_4_9.mem_D_localization_iff
#print axioms AtiyahMcdonald69.Ex_4_9.mem_D_iff_map_mem_D_localization
#print axioms AtiyahMcdonald69.Ex_4_9.associatedPrimes_subset_D
#print axioms AtiyahMcdonald69.Ex_4_9.radical_ann_eq
#print axioms AtiyahMcdonald69.Ex_4_9.D_eq_associatedPrimes
#print axioms AtiyahMcdonald69.Ex_4_9.D_eq_associatedPrimes_of_isNoetherian
#print axioms AtiyahMcdonald69.Ex_4_9.D_eq_image_radical
