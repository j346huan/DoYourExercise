import Mathlib

/-!
# Atiyah–Macdonald, Exercise 4.2

*Exercise 4.2 (Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 4).*
If `𝔞 = r(𝔞)` (i.e. `𝔞` is radical), then `𝔞` has no embedded prime ideals.

The book's running assumption in Chapter 4 is that `𝔞` is decomposable, i.e. has a primary
decomposition; the notion "embedded prime ideal of `𝔞`" is defined relative to a *minimal*
(irredundant, normal) primary decomposition `𝔞 = ⋂ᵢ qᵢ`, with `𝔭ᵢ = r(qᵢ)`: the `𝔭ᵢ` "belong to"
`𝔞` (they are its associated primes, independent of the decomposition by the first uniqueness
theorem 4.5), and the ones that are not minimal among the `𝔭ᵢ` are called embedded.

We formalize the assertion as: for every minimal primary decomposition `t` of a radical ideal `I`,
every associated prime `r(q)` (`q ∈ t`) is a minimal prime over `I`, and no associated prime
properly contains another. The sharp form that we prove as well is that the set of associated
primes of `I` is exactly the set of minimal primes over `I`.
-/

namespace AtiyahMcdonald69.Ex_4_2

open Ideal

variable {R : Type*} [CommRing R]

/-! ## The main proof -/

/-- The radical of a finite intersection of ideals is the intersection of the radicals. -/
lemma radical_inf_id (t : Finset (Ideal R)) :
    (t.inf id).radical = t.inf (fun s => s.radical) := by
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, radical_inf, ih]; rfl

/-- If `I = ⨅_{q ∈ t} r(q)` is the intersection of the associated primes of the minimal primary
decomposition `t`, then an associated prime `r(q)` cannot contain another one `r(q')` for
`q' ≠ q`: otherwise the `q`-th component of the decomposition would be redundant. -/
theorem erase_inf_le_of_radical_le {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t)
    (hinf : t.inf (fun s => s.radical) = I)
    {r q : Ideal R} (hr : r ∈ t) (hq : q ∈ t) (hrq : r ≠ q)
    (hle : r.radical ≤ q.radical) : (t.erase q).inf id ≤ q := by
  classical
  have hr' : r ∈ t.erase q := Finset.mem_erase.mpr ⟨hrq, hr⟩
  have hle' : (t.erase q).inf (fun s => s.radical) ≤ q.radical :=
    (Finset.inf_le (f := fun s => s.radical) hr').trans hle
  have h1 : (t.erase q).inf id ≤ (t.erase q).inf (fun s => s.radical) := by
    rw [Finset.le_inf_iff]
    intro s hs
    exact (Finset.inf_le (f := id) hs).trans le_radical
  have h2 : (t.erase q).inf (fun s => s.radical) ≤ t.inf (fun s => s.radical) := by
    rw [Finset.le_inf_iff]
    intro s hs
    rcases eq_or_ne s q with rfl | hsq
    · exact hle'
    · exact Finset.inf_le (f := fun s => s.radical) (Finset.mem_erase.mpr ⟨hsq, hs⟩)
  calc (t.erase q).inf id ≤ (t.erase q).inf (fun s => s.radical) := h1
    _ ≤ t.inf (fun s => s.radical) := h2
    _ = I := hinf
    _ ≤ q := by rw [← ht.inf_eq]; exact Finset.inf_le (f := id) hq

/-- For a radical ideal, the intersection of the associated primes of a minimal primary
decomposition is the ideal itself. -/
theorem inf_radical_eq {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) (hrad : I.IsRadical) :
    t.inf (fun s => s.radical) = I := by
  rw [← radical_inf_id t, ht.inf_eq, hrad.radical]

/-- **Atiyah–Macdonald, Exercise 4.2.** If `𝔞 = r(𝔞)` then every prime belonging to `𝔞` (i.e. every
`r(q)`, `q` a component of a minimal primary decomposition) is a minimal prime over `𝔞`; thus `𝔞`
has no embedded prime ideals. -/
theorem radical_mem_minimalPrimes {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) (hrad : I.IsRadical) :
    ∀ q ∈ t, q.radical ∈ I.minimalPrimes := by
  classical
  have hinf := inf_radical_eq ht hrad
  intro q hq
  refine ⟨⟨isPrime_radical (ht.primary hq), ?_⟩, ?_⟩
  · rw [← hinf]
    exact Finset.inf_le (f := fun s => s.radical) hq
  · intro p hp hpq
    obtain ⟨r, hrt, hrp⟩ := (IsPrime.inf_le' hp.1).mp (hinf ▸ hp.2)
    rcases eq_or_ne r q with rfl | hrq
    · exact hrp
    · exact absurd (erase_inf_le_of_radical_le ht hinf hrt hq hrq (hrp.trans hpq))
        (ht.minimal hq)

/-- **Atiyah–Macdonald, Exercise 4.2**, restated as "no embedded prime ideals": no associated
prime of a radical decomposable ideal is contained in another one. -/
theorem no_embedded_primes {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) (hrad : I.IsRadical) :
    ∀ q ∈ t, ∀ q' ∈ t, q'.radical ≤ q.radical → q'.radical = q.radical := by
  classical
  have hinf := inf_radical_eq ht hrad
  intro q hq q' hq' hle
  by_contra hne
  have hrq : q' ≠ q := fun h => hne (by rw [h])
  exact ht.minimal hq (erase_inf_le_of_radical_le ht hinf hq' hq hrq hle)

/-- **Atiyah–Macdonald, Exercise 4.2**, sharp form: for a radical ideal the associated primes are
exactly the minimal primes over it (this uses the first uniqueness theorem, Theorem 4.5). -/
theorem associatedPrimes_eq_minimalPrimes {I : Ideal R} {t : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) (hrad : I.IsRadical) :
    I.associatedPrimes = I.minimalPrimes := by
  classical
  rw [← ht.image_radical_eq_associated_primes]
  simp only [Submodule.colon_univ]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact radical_mem_minimalPrimes ht hrad q hq
  · intro hp
    exact IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical ht hp

/-- The set of prime ideals belonging to `I` does not depend on the minimal primary decomposition
chosen (Theorem 4.5), so "having no embedded prime ideals" is a property of the ideal and not of a
particular decomposition. -/
theorem radical_image_independent {I : Ideal R} {t s : Finset (Ideal R)}
    (ht : Submodule.IsMinimalPrimaryDecomposition I t)
    (hs : Submodule.IsMinimalPrimaryDecomposition I s) :
    (fun q => q.radical) '' (↑t : Set (Ideal R)) = (fun q => q.radical) '' (↑s : Set (Ideal R)) := by
  classical
  have h1 : (fun q => q.radical) '' (↑t : Set (Ideal R)) = I.associatedPrimes := by
    simpa only [Submodule.colon_univ] using ht.image_radical_eq_associated_primes
  have h2 : (fun q => q.radical) '' (↑s : Set (Ideal R)) = I.associatedPrimes := by
    simpa only [Submodule.colon_univ] using hs.image_radical_eq_associated_primes
  rw [h1, h2]

/-- **Atiyah–Macdonald, Exercise 4.2.** If `𝔞 = r(𝔞)` then `𝔞` has no embedded prime ideals. -/
theorem solution (I : Ideal R) (t : Finset (Ideal R))
    (ht : Submodule.IsMinimalPrimaryDecomposition I t) (hrad : I.IsRadical) :
    t.inf (fun s => s.radical) = I ∧
      (∀ q ∈ t, q.radical ∈ I.minimalPrimes) ∧
      (∀ q ∈ t, ∀ q' ∈ t, q'.radical ≤ q.radical → q'.radical = q.radical) ∧
      I.associatedPrimes = I.minimalPrimes :=
  ⟨inf_radical_eq ht hrad, radical_mem_minimalPrimes ht hrad, no_embedded_primes ht hrad,
    associatedPrimes_eq_minimalPrimes ht hrad⟩

/-- **Atiyah–Macdonald, Exercise 4.2**, with the hypotheses of a minimal primary decomposition
spelled out in the book's own terms: `I = ⋂_{q ∈ t} q` is a primary decomposition, the radicals of
the components are distinct, and no component is superfluous. -/
theorem solution_of_primary_decomposition (I : Ideal R) (t : Finset (Ideal R))
    (hinf : t.inf id = I) (hprim : ∀ q ∈ t, q.IsPrimary)
    (hdistinct : ∀ q ∈ t, ∀ q' ∈ t, q ≠ q' → (q.colon Set.univ).radical ≠ (q'.colon Set.univ).radical)
    (hirredundant : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) (hrad : I.IsRadical) :
    t.inf (fun s => s.radical) = I ∧
      (∀ q ∈ t, q.radical ∈ I.minimalPrimes) ∧
      (∀ q ∈ t, ∀ q' ∈ t, q'.radical ≤ q.radical → q'.radical = q.radical) ∧
      I.associatedPrimes = I.minimalPrimes :=
  solution I t ⟨hinf, hprim, fun a ha b hb hab => hdistinct a ha b hb hab, hirredundant⟩ hrad

/-- In a Noetherian ring every ideal has a minimal primary decomposition (Lasker's theorem), so the
hypotheses of Exercise 4.2 are satisfiable and the result is not vacuous. -/
theorem exists_isMinimalPrimaryDecomposition [IsNoetherianRing R] (I : Ideal R) :
    ∃ t : Finset (Ideal R), Submodule.IsMinimalPrimaryDecomposition I t :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker (R := R) (M := R)) I

/-- **Atiyah–Macdonald, Exercise 4.2**, in the standard Noetherian setting: for a radical ideal in a
Noetherian ring there exists a minimal primary decomposition, and in any such decomposition every
associated prime is a minimal prime over the ideal; equivalently, the associated primes of the
ideal are exactly its minimal primes. -/
theorem solution_noetherian [IsNoetherianRing R] (I : Ideal R) (hrad : I.IsRadical) :
    ∃ t : Finset (Ideal R), Submodule.IsMinimalPrimaryDecomposition I t ∧
      (∀ q ∈ t, q.radical ∈ I.minimalPrimes) ∧
      (∀ q ∈ t, ∀ q' ∈ t, q'.radical ≤ q.radical → q'.radical = q.radical) ∧
      I.associatedPrimes = I.minimalPrimes := by
  obtain ⟨t, ht⟩ := exists_isMinimalPrimaryDecomposition (R := R) I
  exact ⟨t, ht, radical_mem_minimalPrimes ht hrad, no_embedded_primes ht hrad,
    associatedPrimes_eq_minimalPrimes ht hrad⟩

/-- Sanity check / non-vacuity: a prime ideal is its own minimal primary decomposition. -/
theorem prime_isMinimalPrimaryDecomposition (P : Ideal R) [hP : P.IsPrime] :
    Submodule.IsMinimalPrimaryDecomposition P {P} := by
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro J hJ
    rw [Finset.mem_singleton] at hJ
    rw [hJ]
    exact IsPrime.isPrimary hP
  · intro J hJ
    rw [Finset.mem_singleton] at hJ
    rw [hJ]
    have htop : ({P} : Finset (Ideal R)).erase P = ∅ := by
      rw [Finset.erase_eq_empty_iff]; right; rfl
    rw [htop, Finset.inf_empty, top_le_iff]
    exact hP.ne_top

/-- A prime ideal has no embedded prime ideals: its only associated prime is itself. -/
theorem prime_associatedPrimes_eq (P : Ideal R) [hP : P.IsPrime] :
    P.associatedPrimes = P.minimalPrimes :=
  associatedPrimes_eq_minimalPrimes (prime_isMinimalPrimaryDecomposition P) (IsPrime.isRadical hP)

/-! ## Auditing the hypotheses

The statement has two hypotheses that cannot be weakened; the explicit counterexamples below are
stated over `ℤ`. -/

/-- `(4) ⊆ ℤ` is `(2)`-primary. -/
lemma span_four_primary : (Ideal.span {(4 : ℤ)}).IsPrimary := by
  have h2 : Prime (2 : ℤ) := by norm_num
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr h2
  have hrad : (Ideal.span {(4 : ℤ)}).radical = Ideal.span {(2 : ℤ)} := by
    have h : Ideal.span {(4 : ℤ)} = Ideal.span {(2 : ℤ)} * Ideal.span {(2 : ℤ)} := by
      rw [Ideal.span_singleton_mul_span_singleton]
      norm_num
    rw [h, Ideal.radical_mul, hp.radical, inf_idem]
  refine Ideal.isPrimary_of_isMaximal_radical ?_
  rw [hrad]
  exact Prime.isMaximal_span_singleton h2

/-- `{(4)}` is a minimal primary decomposition of `(4) ⊆ ℤ`. -/
lemma span_four_isMinimalPrimaryDecomposition :
    Submodule.IsMinimalPrimaryDecomposition (Ideal.span {(4 : ℤ)}) {Ideal.span {(4 : ℤ)}} := by
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro J hJ
    rw [Finset.mem_singleton] at hJ
    subst hJ
    exact span_four_primary
  · intro J hJ
    rw [Finset.mem_singleton] at hJ
    subst hJ
    have htop : ({Ideal.span {(4 : ℤ)}} : Finset (Ideal ℤ)).erase (Ideal.span {(4 : ℤ)}) = ∅ := by
      rw [Finset.erase_eq_empty_iff]; right; rfl
    rw [htop, Finset.inf_empty, top_le_iff, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]

/-- The converse of Exercise 4.2 is false: `(4) ⊆ ℤ` has no embedded prime ideals — its minimal
primary decomposition is the singleton `{(4)}` — but it is not radical. -/
theorem no_embedded_primes_not_radical :
    ∃ I : Ideal ℤ, I.IsPrimary ∧ ¬ I.IsRadical ∧ I.associatedPrimes = I.minimalPrimes := by
  refine ⟨Ideal.span {(4 : ℤ)}, span_four_primary, ?_, ?_⟩
  · intro hrad
    have h2 : Prime (2 : ℤ) := by norm_num
    have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr h2
    have hrad' : (Ideal.span {(4 : ℤ)}).radical = Ideal.span {(2 : ℤ)} := by
      have h : Ideal.span {(4 : ℤ)} = Ideal.span {(2 : ℤ)} * Ideal.span {(2 : ℤ)} := by
        rw [Ideal.span_singleton_mul_span_singleton]
        norm_num
      rw [h, Ideal.radical_mul, hp.radical, inf_idem]
    have h2mem : (2 : ℤ) ∈ Ideal.span {(4 : ℤ)} := by
      apply hrad
      rw [hrad']
      exact Ideal.mem_span_singleton.mpr dvd_rfl
    rw [Ideal.mem_span_singleton] at h2mem
    omega
  · have h1 : (Ideal.span {(4 : ℤ)}).associatedPrimes = {(Ideal.span {(4 : ℤ)}).radical} := by
      rw [← span_four_isMinimalPrimaryDecomposition.image_radical_eq_associated_primes]
      simp [Submodule.colon_univ]
    have h2 : (Ideal.span {(4 : ℤ)}).minimalPrimes = {(Ideal.span {(4 : ℤ)}).radical} :=
      Ideal.minimalPrimes_eq_subsingleton span_four_primary
    rw [h1, h2]

/-- The hypothesis that the primary decomposition be *minimal* cannot be dropped: `⊥ ⊆ ℤ` is a
radical ideal and `⊥ = ⊥ ⊓ (2)` is a primary decomposition whose prime components `⊥ ⊊ (2)` are
nested (the decomposition is not irredundant: `(2)` is superfluous). -/
theorem nested_primes_without_minimality :
    ∃ q₁ q₂ : Ideal ℤ, q₁ ≠ q₂ ∧ q₁ ⊓ q₂ = ⊥ ∧ (⊥ : Ideal ℤ).IsRadical ∧
      q₁.IsPrimary ∧ q₂.IsPrimary ∧ q₁.radical < q₂.radical := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr (by norm_num : Prime (2 : ℤ))
  have hbot : (⊥ : Ideal ℤ).IsRadical := isRadical_bot
  refine ⟨⊥, Ideal.span {(2 : ℤ)}, ?_, by simp, hbot, IsPrime.isPrimary isPrime_bot,
    IsPrime.isPrimary hp, ?_⟩
  · intro h
    have hle : Ideal.span {(2 : ℤ)} ≤ (⊥ : Ideal ℤ) := h.symm.le
    have h2 : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := hle (Ideal.mem_span_singleton.mpr dvd_rfl)
    simp at h2
  · have hbot' : (⊥ : Ideal ℤ).radical = ⊥ := Ideal.radical_bot_of_isReduced
    rw [hbot', hp.radical]
    refine ⟨bot_le, ?_⟩
    intro hle
    have h2 : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := hle (Ideal.mem_span_singleton.mpr dvd_rfl)
    simp at h2

end AtiyahMcdonald69.Ex_4_2

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_4_2.inf_radical_eq
#print axioms AtiyahMcdonald69.Ex_4_2.radical_mem_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_4_2.no_embedded_primes
#print axioms AtiyahMcdonald69.Ex_4_2.radical_image_independent
#print axioms AtiyahMcdonald69.Ex_4_2.associatedPrimes_eq_minimalPrimes
#print axioms AtiyahMcdonald69.Ex_4_2.solution
#print axioms AtiyahMcdonald69.Ex_4_2.solution_of_primary_decomposition
#print axioms AtiyahMcdonald69.Ex_4_2.solution_noetherian
#print axioms AtiyahMcdonald69.Ex_4_2.prime_associatedPrimes_eq
#print axioms AtiyahMcdonald69.Ex_4_2.no_embedded_primes_not_radical
#print axioms AtiyahMcdonald69.Ex_4_2.nested_primes_without_minimality
