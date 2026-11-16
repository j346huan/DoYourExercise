import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 10.3

Let `A` be a Noetherian ring, `I` an ideal of `A` and `M` a finitely generated `A`-module.

(a) `⋂_{n>0} I^n M = ⋂_{m ⊇ I} ker (M → M_m)`, where `m` runs over the maximal ideals of `A`
    containing `I`.

(b) Hence the `I`-adic completion `M̂` of `M` vanishes if and only if
    `Supp M ∩ V(I) = ∅` in `Spec A`.

In this file `powersInter I` denotes `⋂_{n ≥ 0} I^n • ⊤`; since `I^0 • ⊤ = ⊤` this is the same
intersection as `⋂_{n ≥ 1} I^n M`. `maxLocalizationInter I` denotes the intersection of the
kernels of `M → M_m` over the maximal ideals `m ⊇ I`, and `zeroLocus I` denotes `V(I) ⊆ Spec A`.

The proof of (a) follows the book: Krull's intersection theorem identifies `⋂ n, I^n M` with the
set of `x ∈ M` that are annihilated by `1 - a` for some `a ∈ I`, i.e. with the `x` for which
`I ⊔ Ann(x) = ⊤`; this happens exactly when no maximal ideal containing `I` can contain `Ann(x)`,
which is exactly the condition that `x` maps to `0` in every `M_m` with `m ⊇ I` maximal.
Part (b) is deduced from (a) together with the description `Supp M = V(Ann M)`.

## Cross-check of the statement

The statement was checked against the two local book transcriptions
`.scratch/dl/amcd.tex` ("Page 114, Exercise 10.3") and
`.scratch/reference/atiyah-solutions.txt` (solution 10.3); they agree, and no false literal was
found. Two points of care, both harmless:

* the book's intersection runs over `n > 0`, whereas the `ℕ`-indexed infimum above includes
  `n = 0`, where `I ^ 0 • ⊤ = ⊤`; `powersInter_eq_iInf_pos` records the literal `n ≥ 1` form;
* the book's `M̂` is the inverse limit `lim ← M / I ^ n M`, which is `AdicCompletion I M`, and
  "`M̂ = 0`" is rendered as `Subsingleton (AdicCompletion I M)`.

The statements are also correct in the edge cases `I = ⊥` (then both sides of (a) are `0` for
finitely generated `M`, and `M̂ = M`) and `I = ⊤` (then `V(I) = ∅` and `M̂ = 0`, while the
intersection on the right of (a) is empty).
-/

namespace AtiyahMcdonald69.Ex_10_3

open Submodule

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- `⋂ n, I ^ n • ⊤`, the intersection of the powers of `I` acting on `M`.
(Since `I ^ 0 • ⊤ = ⊤`, this is the same as `⋂_{n ≥ 1} I ^ n M`.) -/
noncomputable def powersInter (I : Ideal A) : Submodule A M :=
  ⨅ n : ℕ, I ^ n • (⊤ : Submodule A M)

/-- `⋂_{m ⊇ I, m maximal} ker (M → M_m)`. -/
noncomputable def maxLocalizationInter (I : Ideal A) : Submodule A M :=
  ⨅ (p : PrimeSpectrum A), ⨅ (_ : p.asIdeal.IsMaximal), ⨅ (_ : I ≤ p.asIdeal),
    LinearMap.ker (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)

/-- `V(I)` as a subset of `Spec A`. -/
noncomputable abbrev zeroLocus (I : Ideal A) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus (I : Set A)

/-- The book's intersection `⋂_{n ≥ 1} I ^ n M`, written with an explicit positivity condition. -/
lemma powersInter_eq_iInf_pos (I : Ideal A) :
    powersInter (M := M) I = ⨅ (n : ℕ), ⨅ (_ : 0 < n), I ^ n • (⊤ : Submodule A M) := by
  rw [powersInter, le_antisymm_iff]
  constructor
  · exact le_iInf fun n => le_iInf fun _ => iInf_le _ n
  · refine le_iInf fun n => ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact le_trans (iInf_le (fun k : ℕ => ⨅ (_ : 0 < k), I ^ k • (⊤ : Submodule A M)) n)
        (iInf_le (fun (_ : 0 < n) => I ^ n • (⊤ : Submodule A M)) h)

lemma mem_maxLocalizationInter_iff {I : Ideal A} {x : M} :
    x ∈ maxLocalizationInter (M := M) I ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal →
        x ∈ LinearMap.ker (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) := by
  simp only [maxLocalizationInter, Submodule.mem_iInf]

/-- `x` maps to `0` in `M_m` if and only if `x` is killed by some `r ∉ m`. -/
lemma mem_ker_mkLinearMap_ann {p : PrimeSpectrum A} {x : M} :
    x ∈ LinearMap.ker (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) ↔
      ∃ r ∉ p.asIdeal, r • x = 0 := by
  rw [LocalizedModule.mem_ker_mkLinearMap_iff]
  exact ⟨fun ⟨r, hr, hrx⟩ => ⟨r, hr, hrx⟩, fun ⟨r, hr, hrx⟩ => ⟨r, hr, hrx⟩⟩

/-- `x` lies in the kernel of `M → M_m` for all maximal `m ⊇ I` if and only if `I ⊔ Ann(x) = ⊤`,
which is the same as being annihilated by `1 - a` for some `a ∈ I`. -/
lemma exists_smul_eq_self_iff_forall (I : Ideal A) (x : M) :
    (∃ r ∈ I, r • x = x) ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal → ∃ r ∉ p.asIdeal, r • x = 0 := by
  constructor
  · rintro ⟨r, hrI, hrx⟩ p hp hIp
    refine ⟨1 - r, ?_, ?_⟩
    · intro hmem
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      have hrp : r ∈ p.asIdeal := hIp hrI
      have : (1 - r) + r ∈ p.asIdeal := add_mem hmem hrp
      simpa using this
    · rw [sub_smul, one_smul, hrx, sub_self]
  · intro h
    by_contra hcon
    have htop : I ⊔ Submodule.annihilator (Submodule.span A {x}) ≠ ⊤ := by
      intro hEq
      apply hcon
      have h1 : (1 : A) ∈ I ⊔ Submodule.annihilator (Submodule.span A {x}) := by
        rw [hEq]; exact Submodule.mem_top
      rw [Submodule.mem_sup] at h1
      obtain ⟨a, haI, b, hb, hab⟩ := h1
      have hbx : b • x = 0 := (Submodule.mem_annihilator_span_singleton x b).mp hb
      refine ⟨a, haI, ?_⟩
      have h2 : a • x + b • x = x := by
        rw [← add_smul, hab, one_smul]
      rw [hbx, add_zero] at h2
      exact h2
    obtain ⟨p, hp, hIp⟩ :=
      Ideal.exists_le_maximal (I ⊔ Submodule.annihilator (Submodule.span A {x})) htop
    obtain ⟨r, hrp, hrx⟩ := h ⟨p, hp.isPrime⟩ hp (le_trans le_sup_left hIp)
    exact hrp (hIp (Ideal.mem_sup_right ((Submodule.mem_annihilator_span_singleton x r).mpr hrx)))

/-- `M_m = 0` for every maximal ideal `m ⊇ I` if and only if the intersection of the kernels
`ker (M → M_m)` is everything. -/
lemma maxLocalizationInter_eq_top_iff (I : Ideal A) :
    maxLocalizationInter (M := M) I = ⊤ ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  constructor
  · intro h p hp hpI
    refine LocalizedModule.subsingleton_iff_ker_eq_top.mpr ?_
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ maxLocalizationInter (M := M) I := by rw [h]; exact Submodule.mem_top
    exact (mem_maxLocalizationInter_iff.mp hx) p hp hpI
  · intro h
    rw [eq_top_iff]
    intro x _
    rw [mem_maxLocalizationInter_iff]
    intro p hp hpI
    have hsub := LocalizedModule.subsingleton_iff_ker_eq_top.mp (h p hp hpI)
    rw [hsub]
    exact Submodule.mem_top

/-- `Supp M ∩ V(I) = ∅` if and only if `M_m = 0` for every maximal ideal `m ⊇ I`. -/
theorem support_inter_zeroLocus_eq_empty_iff (I : Ideal A) :
    Module.support A M ∩ zeroLocus I = ∅ ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  constructor
  · intro h p hp hpI
    rw [← Module.notMem_support_iff]
    intro hsupp
    exact Set.eq_empty_iff_forall_notMem.mp h p ⟨hsupp, fun r hr => hpI hr⟩
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hpSupp, hpZ⟩
    have hpI : I ≤ p.asIdeal := fun r hr => hpZ hr
    obtain ⟨m, hmmax, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    have hmSupp : (⟨m, hmmax.isPrime⟩ : PrimeSpectrum A) ∈ Module.support A M :=
      Module.mem_support_mono hpm hpSupp
    have hm := h ⟨m, hmmax.isPrime⟩ hmmax (le_trans hpI hpm)
    rw [Module.mem_support_iff] at hmSupp
    exact (not_nontrivial_iff_subsingleton.mpr hm) hmSupp

/-- `M = I M` if and only if `Supp M ∩ V(I) = ∅`. -/
theorem smul_top_eq_top_iff_support [Module.Finite A M] (I : Ideal A) :
    I • (⊤ : Submodule A M) = ⊤ ↔ Module.support A M ∩ zeroLocus I = ∅ := by
  have h1 : (I • (⊤ : Submodule A M) = ⊤) ↔
      Subsingleton (M ⧸ (I • (⊤ : Submodule A M))) :=
    Submodule.Quotient.subsingleton_iff.symm
  have h2 : (Module.support A (M ⧸ (I • (⊤ : Submodule A M))) = ∅) ↔
      Subsingleton (M ⧸ (I • (⊤ : Submodule A M))) :=
    Module.support_eq_empty_iff
  have h3 : Module.support A (M ⧸ (I • (⊤ : Submodule A M))) =
      Module.support A M ∩ zeroLocus I := Module.support_quotient I
  rw [h1, ← h2, h3]

/-- The criterion `M = I M ↔ I + Ann M = ⊤` (Corollary 2.5 together with Krull's theorem). -/
theorem smul_top_eq_top_iff_sup_annihilator [Module.Finite A M] (I : Ideal A) :
    I • (⊤ : Submodule A M) = ⊤ ↔ I ⊔ Module.annihilator A M = ⊤ := by
  constructor
  · intro h
    obtain ⟨r, hrI, hr⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I (⊤ : Submodule A M)
        (Module.finite_def.mp ‹Module.Finite A M›) h.ge
    rw [Ideal.eq_top_iff_one]
    have hsub : (1 - r) ∈ Module.annihilator A M := by
      rw [Module.mem_annihilator]
      intro m
      rw [sub_smul, one_smul, hr m (Submodule.mem_top), sub_self]
    have hsum : r + (1 - r) ∈ I ⊔ Module.annihilator A M :=
      Submodule.add_mem_sup hrI hsub
    simpa using hsum
  · intro h
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : A) ∈ I ⊔ Module.annihilator A M := by rw [h]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    have hbx : b • x = 0 := Module.mem_annihilator.mp hb x
    have hx : a • x = x := by
      have h2 : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
      rw [hbx, add_zero] at h2
      exact h2
    rw [← hx]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

variable [IsNoetherianRing A] [Module.Finite A M]

/-- Krull's intersection theorem, in the form used for (a): an element of `M` lies in every
`I ^ n M` if and only if it is fixed by some `a ∈ I`. -/
lemma mem_powersInter_iff {I : Ideal A} {x : M} :
    x ∈ powersInter (M := M) I ↔ ∃ r ∈ I, r • x = x := by
  rw [powersInter, Ideal.mem_iInf_smul_pow_eq_bot_iff]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, r.2, hr⟩, fun ⟨r, hr, hrx⟩ => ⟨⟨r, hr⟩, hrx⟩⟩

/-- **Atiyah–Macdonald, Exercise 10.3 (a)**: for a Noetherian ring `A`, an ideal `I` and a
finitely generated `A`-module `M`, the intersection of the powers `I ^ n M` is the intersection
of the kernels of the localizations `M → M_m` at the maximal ideals `m ⊇ I`. -/
theorem powersInter_eq_maxLocalizationInter (I : Ideal A) :
    powersInter (M := M) I = maxLocalizationInter (M := M) I := by
  ext x
  rw [mem_powersInter_iff, mem_maxLocalizationInter_iff]
  exact (exists_smul_eq_self_iff_forall I x).trans
    ⟨fun h p hp hpI => mem_ker_mkLinearMap_ann.mpr (h p hp hpI),
     fun h p hp hpI => mem_ker_mkLinearMap_ann.mp (h p hp hpI)⟩

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- The `I`-adic completion of `M` (an inverse limit of the modules `M ⧸ I ^ n M`) vanishes if
and only if `⋂ n, I ^ n M = ⊤`. -/
lemma subsingleton_adicCompletion_iff (I : Ideal A) :
    Subsingleton (AdicCompletion I M) ↔ powersInter (M := M) I = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    rw [powersInter, Submodule.mem_iInf]
    intro n
    have h0 : AdicCompletion.of I M x = 0 := Subsingleton.elim _ _
    have h1 : AdicCompletion.eval I M n (AdicCompletion.of I M x) = 0 := by rw [h0, map_zero]
    rw [AdicCompletion.eval_of] at h1
    simpa using h1
  · intro h
    refine ⟨fun f g => ?_⟩
    have hpow : ∀ n : ℕ, I ^ n • (⊤ : Submodule A M) = ⊤ := by
      intro n
      refine le_antisymm le_top ?_
      calc (⊤ : Submodule A M) = powersInter (M := M) I := h.symm
        _ ≤ I ^ n • (⊤ : Submodule A M) := iInf_le _ n
    refine Subtype.ext (funext fun n => ?_)
    have : Subsingleton (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
      Submodule.Quotient.subsingleton_iff.mpr (hpow n)
    exact Subsingleton.elim _ _

omit [IsNoetherianRing A] [Module.Finite A M] in
lemma powersInter_eq_top_iff_smul_top (I : Ideal A) :
    powersInter (M := M) I = ⊤ ↔ I • (⊤ : Submodule A M) = ⊤ := by
  constructor
  · intro h
    refine le_antisymm le_top ?_
    calc (⊤ : Submodule A M) = powersInter (M := M) I := h.symm
      _ ≤ I ^ 1 • (⊤ : Submodule A M) := iInf_le _ 1
      _ = I • (⊤ : Submodule A M) := by rw [pow_one]
  · intro h
    rw [eq_top_iff]
    intro x _
    rw [powersInter, Submodule.mem_iInf]
    intro n
    have hpow : ∀ k : ℕ, I ^ k • (⊤ : Submodule A M) = ⊤ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, h, ih]
    rw [hpow n]
    exact Submodule.mem_top

lemma powersInter_eq_top_iff_maxLocalizationInter_eq_top (I : Ideal A) :
    powersInter (M := M) I = ⊤ ↔ maxLocalizationInter (M := M) I = ⊤ := by
  rw [powersInter_eq_maxLocalizationInter]

/-- The "maximal ideal" form of (b): the `I`-adic completion of `M` vanishes if and only if
`M_m = 0` for every maximal ideal `m ⊇ I`. -/
theorem adicCompletion_subsingleton_iff_forall_localized (I : Ideal A) :
    Subsingleton (AdicCompletion I M) ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  rw [subsingleton_adicCompletion_iff, ← maxLocalizationInter_eq_top_iff,
    powersInter_eq_top_iff_maxLocalizationInter_eq_top]

/-- **Atiyah–Macdonald, Exercise 10.3 (b)**: for a Noetherian ring `A`, an ideal `I` and a
finitely generated `A`-module `M`, the `I`-adic completion of `M` vanishes if and only if
`Supp M ∩ V(I) = ∅` in `Spec A`. -/
theorem adicCompletion_subsingleton_iff_support (I : Ideal A) :
    Subsingleton (AdicCompletion I M) ↔ Module.support A M ∩ zeroLocus I = ∅ :=
  (adicCompletion_subsingleton_iff_forall_localized I).trans
    (support_inter_zeroLocus_eq_empty_iff I).symm

/-- Atiyah–Macdonald, Chapter 3, Exercise 14 (the tool used in the book's proof of (a)):
`M = I M` if and only if `M_m = 0` for every maximal ideal `m ⊇ I`. -/
theorem smul_top_eq_top_iff_forall_localized (I : Ideal A) :
    I • (⊤ : Submodule A M) = ⊤ ↔
      ∀ (p : PrimeSpectrum A), p.asIdeal.IsMaximal → I ≤ p.asIdeal →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  rw [← powersInter_eq_top_iff_smul_top, powersInter_eq_top_iff_maxLocalizationInter_eq_top,
    maxLocalizationInter_eq_top_iff]

end AtiyahMcdonald69.Ex_10_3

#print axioms AtiyahMcdonald69.Ex_10_3.powersInter_eq_iInf_pos
#print axioms AtiyahMcdonald69.Ex_10_3.mem_powersInter_iff
#print axioms AtiyahMcdonald69.Ex_10_3.powersInter_eq_maxLocalizationInter
#print axioms AtiyahMcdonald69.Ex_10_3.adicCompletion_subsingleton_iff_support
#print axioms AtiyahMcdonald69.Ex_10_3.adicCompletion_subsingleton_iff_forall_localized
#print axioms AtiyahMcdonald69.Ex_10_3.smul_top_eq_top_iff_support
#print axioms AtiyahMcdonald69.Ex_10_3.smul_top_eq_top_iff_forall_localized
#print axioms AtiyahMcdonald69.Ex_10_3.smul_top_eq_top_iff_sup_annihilator
#print axioms AtiyahMcdonald69.Ex_10_3.support_inter_zeroLocus_eq_empty_iff
