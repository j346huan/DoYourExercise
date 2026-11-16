/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 5.10.

A ring homomorphism `f : A →+* B` is said to have the **going-up property** (resp. the
**going-down property**) if the conclusion of the going-up theorem (5.11) (resp. the
going-down theorem (5.16)) holds for `B` and its subring `f(A)`.  Let
`f* : Spec B → Spec A` be the associated map.  The exercise asks to prove

(i)  (a) `f*` is a closed map  ⟹  (b) `f` has going-up,
     (b) ⟺ (c) for every prime `q` of `B` with `p = qᶜ`, the induced map
     `Spec (B/q) → Spec (A/p)` is surjective;

(ii) (a') `f*` is an open map  ⟹  (b') `f` has going-down,
     (b') ⟺ (c') for every prime `q` of `B` with `p = qᶜ`, the induced map
     `Spec B_q → Spec A_p` is surjective.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_5_10

open PrimeSpectrum TopologicalSpace

variable {A B : Type*} [CommRing A] [CommRing B]

/-! ### The going-up and going-down properties -/

/-- `f : A →+* B` has the *going-up property*: given primes `p₁ ≤ p₂` of `A` and a prime
`q₁` of `B` contracting to `p₁`, there is a prime `q₂ ⊇ q₁` of `B` contracting to `p₂`. -/
def HasGoingUp (f : A →+* B) : Prop :=
  ∀ (p₁ p₂ : Ideal A) (q₁ : Ideal B), p₁.IsPrime → p₂.IsPrime → q₁.IsPrime →
    q₁.comap f = p₁ → p₁ ≤ p₂ → ∃ q₂ : Ideal B, q₂.IsPrime ∧ q₂.comap f = p₂ ∧ q₁ ≤ q₂

/-- `f : A →+* B` has the *going-down property*: given primes `p₂ ≤ p₁` of `A` and a prime
`q₁` of `B` contracting to `p₁`, there is a prime `q₂ ⊆ q₁` of `B` contracting to `p₂`. -/
def HasGoingDown (f : A →+* B) : Prop :=
  ∀ (p₁ p₂ : Ideal A) (q₁ : Ideal B), p₁.IsPrime → p₂.IsPrime → q₁.IsPrime →
    q₁.comap f = p₁ → p₂ ≤ p₁ → ∃ q₂ : Ideal B, q₂.IsPrime ∧ q₂.comap f = p₂ ∧ q₂ ≤ q₁

/-! ### (i) Closed maps and going-up

`(a) ⇒ (b)`: if `f*` is closed, `V(q₁)` is closed and its image contains `p₁ = q₁ᶜ`;
being closed it contains every specialization of `p₁`, in particular `p₂ ⊇ p₁`. -/

theorem hasGoingUp_of_isClosedMap (f : A →+* B) (hf : IsClosedMap (PrimeSpectrum.comap f)) :
    HasGoingUp f := by
  intro p₁ p₂ q₁ h₁ h₂ hq₁ hcom hle
  -- the prime points
  set x : PrimeSpectrum A := ⟨p₁, h₁⟩ with hx
  set y : PrimeSpectrum A := ⟨p₂, h₂⟩ with hy
  set z : PrimeSpectrum B := ⟨q₁, hq₁⟩ with hz
  have hzx : PrimeSpectrum.comap f z = x :=
    PrimeSpectrum.ext (by simp [x, z, hcom])
  -- `V(q₁)` is closed and contains `z`
  have hZ : IsClosed (PrimeSpectrum.zeroLocus (q₁ : Set B)) :=
    PrimeSpectrum.isClosed_zeroLocus (q₁ : Set B)
  have hzZ : z ∈ PrimeSpectrum.zeroLocus (q₁ : Set B) :=
    (PrimeSpectrum.mem_zeroLocus z q₁).mpr le_rfl
  -- hence its image is a closed set containing `p₁`
  have himg : IsClosed (PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q₁ : Set B)) :=
    hf _ hZ
  have hxmem : x ∈ PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q₁ : Set B) :=
    ⟨z, hzZ, hzx⟩
  -- `p₁ ⊆ p₂`, i.e. `p₁` specializes to `p₂`, so `p₂` lies in the closed image too
  have hspec : x ⤳ y := by
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact hle
  have hymem : y ∈ PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q₁ : Set B) :=
    Specializes.mem_closed hspec himg hxmem
  obtain ⟨z', hz', hz'eq⟩ := hymem
  have hq' : z'.asIdeal.IsPrime := z'.2
  refine ⟨z'.asIdeal, hq', ?_, ?_⟩
  · have := congrArg PrimeSpectrum.asIdeal hz'eq
    simpa [y] using this
  · exact (PrimeSpectrum.mem_zeroLocus z' q₁).mp hz'

/-! ### (i) The quotient reformulation

For a prime `q` of `B` let `p = qᶜ`.  The ring map `A ⧸ p →+* B ⧸ q` induced by `f`
gives `f* : Spec (B/q) → Spec (A/p)`; statement (c) says this map is surjective. -/

/-- The ring homomorphism `A ⧸ qᶜ →+* B ⧸ q` induced by `f`. -/
def quotientMapOf (f : A →+* B) (q : Ideal B) : A ⧸ q.comap f →+* B ⧸ q :=
  Ideal.quotientMap q f le_rfl

@[simp]
theorem quotientMapOf_mk (f : A →+* B) (q : Ideal B) (a : A) :
    quotientMapOf f q (Ideal.Quotient.mk (q.comap f) a) = Ideal.Quotient.mk q (f a) :=
  Ideal.quotientMap_mk

theorem quotientMapOf_comp (f : A →+* B) (q : Ideal B) :
    (quotientMapOf f q).comp (Ideal.Quotient.mk (q.comap f)) =
      (Ideal.Quotient.mk q).comp f :=
  Ideal.quotientMap_comp_mk le_rfl

/-- Statement (c) of the exercise: for every prime `q` of `B`, the map
`Spec (B/q) → Spec (A/qᶜ)` is surjective. -/
def QuotientSurjective (f : A →+* B) : Prop :=
  ∀ (q : Ideal B), ∀ _ : q.IsPrime,
    Function.Surjective (PrimeSpectrum.comap (quotientMapOf f q))

/-- `(b) ⇒ (c)`. -/
theorem quotientSurjective_of_hasGoingUp (f : A →+* B) (H : HasGoingUp f) :
    QuotientSurjective f := by
  intro q hq x
  haveI := hq
  -- the prime of `A` obtained by pulling back `x.asIdeal`
  have hp' : (q.comap f).IsPrime := Ideal.IsPrime.comap f
  haveI := hp'
  set p₂ : Ideal A := x.asIdeal.comap (Ideal.Quotient.mk (q.comap f)) with hp₂def
  have hp₂ : p₂.IsPrime := Ideal.IsPrime.comap _
  haveI := hp₂
  have hle : q.comap f ≤ p₂ := by
    rw [hp₂def]
    calc q.comap f = RingHom.ker (Ideal.Quotient.mk (q.comap f)) :=
          (Ideal.mk_ker (I := q.comap f)).symm
      _ ≤ Ideal.comap (Ideal.Quotient.mk (q.comap f)) x.asIdeal := Ideal.ker_le_comap _
  obtain ⟨q₂, hq₂, hq₂com, hqq₂⟩ := H (q.comap f) p₂ q hp' hp₂ hq rfl hle
  haveI := hq₂
  -- `q₂ ⧸ q` is a prime of `B ⧸ q`
  refine ⟨⟨q₂.map (Ideal.Quotient.mk q), ?_⟩, ?_⟩
  · apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hqq₂
  · -- the contraction of `q₂ ⧸ q` along `A ⧸ p →+* B ⧸ q` is `x.asIdeal`;
    -- it suffices to compare the contractions to `A`
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    have hmap : (q₂.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = q₂ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqq₂]
    have hxas : x.asIdeal = p₂.map (Ideal.Quotient.mk (q.comap f)) := by
      rw [hp₂def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have key : ((q₂.map (Ideal.Quotient.mk q)).comap (quotientMapOf f q)).comap
          (Ideal.Quotient.mk (q.comap f)) = x.asIdeal.comap (Ideal.Quotient.mk (q.comap f)) := by
      rw [Ideal.comap_comap, quotientMapOf_comp, ← Ideal.comap_comap, hmap, hq₂com, hxas,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (q.comap f))
      Ideal.Quotient.mk_surjective
      ((q₂.map (Ideal.Quotient.mk q)).comap (quotientMapOf f q)), key,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- `(c) ⇒ (b)`. -/
theorem hasGoingUp_of_quotientSurjective (f : A →+* B) (H : QuotientSurjective f) :
    HasGoingUp f := by
  intro p₁ p₂ q₁ h₁ h₂ hq₁ hcom hle
  subst hcom
  haveI := hq₁
  -- apply (c) to the prime `q₁` and to the prime `p₂ ⧸ p₁` of `A ⧸ p₁`
  have hp : (q₁.comap f).IsPrime := h₁
  haveI := hp
  have hle' : q₁.comap f ≤ p₂ := hle
  have hmap : (p₂.map (Ideal.Quotient.mk (q₁.comap f))).IsPrime := by
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hle'
  obtain ⟨y, hy⟩ := H q₁ hq₁ ⟨p₂.map (Ideal.Quotient.mk (q₁.comap f)), hmap⟩
  have hy' : y.asIdeal.comap (quotientMapOf f q₁) = p₂.map (Ideal.Quotient.mk (q₁.comap f)) :=
    congrArg PrimeSpectrum.asIdeal hy
  refine ⟨y.asIdeal.comap (Ideal.Quotient.mk q₁), Ideal.IsPrime.comap _, ?_, ?_⟩
  · rw [Ideal.comap_comap, ← quotientMapOf_comp, ← Ideal.comap_comap, hy',
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
  · calc q₁ = RingHom.ker (Ideal.Quotient.mk q₁) := (Ideal.mk_ker (I := q₁)).symm
      _ ≤ y.asIdeal.comap (Ideal.Quotient.mk q₁) := Ideal.ker_le_comap _


/-! ### (ii) Open maps and going-down

The key algebraic ingredient: if every `t ∉ q` is avoided by some prime of `B` lying over
`p`, then some prime of `B` lying over `p` is contained in `q`. -/

theorem exists_prime_le_of_forall_exists_prime (f : A →+* B) {p : Ideal A} (hp : p.IsPrime)
    {q : Ideal B} (hq : q.IsPrime)
    (H : ∀ t : B, t ∉ q → ∃ P : Ideal B, P.IsPrime ∧ P.comap f = p ∧ t ∉ P) :
    ∃ P : Ideal B, P.IsPrime ∧ P.comap f = p ∧ P ≤ q := by
  haveI := hp
  haveI := hq
  -- the multiplicative set generated by `f(pᶜ)` and `qᶜ`
  set M : Submonoid B :=
    Submonoid.closure ((f '' (p.primeCompl : Set A)) ∪ (q.primeCompl : Set B)) with hM
  -- every element of `M` is of the form `f a * t` with `a ∉ p`, `t ∉ q`
  have key : ∀ x ∈ M, ∃ a t, a ∉ p ∧ t ∉ q ∧ x = f a * t := by
    intro x hx
    rw [hM] at hx
    induction hx using Submonoid.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, ha, rfl⟩ | hy
      · exact ⟨a, 1, by simpa using ha, q.one_notMem, by rw [mul_one]⟩
      · exact ⟨1, y, p.one_notMem, by simpa using hy, by rw [map_one, one_mul]⟩
    | one => exact ⟨1, 1, p.one_notMem, q.one_notMem, by rw [map_one, one_mul]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a₁, t₁, ha₁, ht₁, hxy₁⟩ := ihx
      obtain ⟨a₂, t₂, ha₂, ht₂, hxy₂⟩ := ihy
      refine ⟨a₁ * a₂, t₁ * t₂, fun h => (hp.mem_or_mem h).elim ha₁ ha₂,
        fun h => (hq.mem_or_mem h).elim ht₁ ht₂, ?_⟩
      rw [hxy₁, hxy₂, map_mul]
      ring
  -- `Ideal.map f p` meets `M` trivially
  have hdisj : Disjoint (Ideal.map f p : Set B) (M : Set B) := by
    rw [Set.disjoint_left]
    intro x hxI hxM
    obtain ⟨a, t, ha, ht, rfl⟩ := key x hxM
    obtain ⟨P, hP, hPcom, htP⟩ := H t ht
    haveI := hP
    have hIP : Ideal.map f p ≤ P := by
      rw [← hPcom]
      exact Ideal.map_comap_le
    have hmem : f a * t ∈ P := hIP hxI
    have hfa : f a ∉ P := by
      intro h
      exact ha (hPcom ▸ h)
    rcases hP.mem_or_mem hmem with h' | h'
    · exact hfa h'
    · exact htP h'
  obtain ⟨P, hP, hIP, hPdisj⟩ := Ideal.exists_le_prime_disjoint (Ideal.map f p) M hdisj
  refine ⟨P, hP, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · -- `P.comap f ≤ p`
      intro a ha
      by_contra hap
      have hmemM : f a ∈ M := Submonoid.subset_closure (Or.inl ⟨a, by simpa using hap, rfl⟩)
      exact (Set.disjoint_left.mp hPdisj) ha hmemM
    · -- `p ≤ P.comap f`
      intro a ha
      exact hIP (Ideal.mem_map_of_mem f ha)
  · -- `P ≤ q`
    intro x hx
    by_contra hxq
    exact (Set.disjoint_left.mp hPdisj) hx (Submonoid.subset_closure (Or.inr (by simpa using hxq)))

/-- `(a') ⇒ (b')`: if `f*` is an open map then `f` has the going-down property. -/
theorem hasGoingDown_of_isOpenMap (f : A →+* B) (hf : IsOpenMap (PrimeSpectrum.comap f)) :
    HasGoingDown f := by
  intro p₁ p₂ q₁ h₁ h₂ hq₁ hcom hle
  refine exists_prime_le_of_forall_exists_prime (f := f) (p := p₂) (q := q₁)
    (hp := h₂) (hq := hq₁) ?_
  intro t ht
  -- `D(t)` is an open neighbourhood of `q₁`, and `p₁ = q₁ᶜ` lies in its image
  have hDt : IsOpen (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isOpen_basicOpen
  have hmem : (⟨q₁, hq₁⟩ : PrimeSpectrum B) ∈ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum B)) :=
    (PrimeSpectrum.mem_basicOpen t ⟨q₁, hq₁⟩).mpr ht
  have himg : IsOpen (PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum B))) :=
    hf _ hDt
  have hp₁mem : (⟨p₁, h₁⟩ : PrimeSpectrum A) ∈
      PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum B)) :=
    ⟨⟨q₁, hq₁⟩, hmem, PrimeSpectrum.ext (by simpa using hcom)⟩
  -- open sets are closed under generization, and `p₂ ⊆ p₁`
  have hspec : (⟨p₂, h₂⟩ : PrimeSpectrum A) ⤳ (⟨p₁, h₁⟩ : PrimeSpectrum A) := by
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact hle
  have hp₂mem := Specializes.mem_open hspec himg hp₁mem
  obtain ⟨z, hz, hzeq⟩ := hp₂mem
  refine ⟨z.asIdeal, z.2, ?_, ?_⟩
  · have := congrArg PrimeSpectrum.asIdeal hzeq
    simpa using this
  · exact (PrimeSpectrum.mem_basicOpen t z).mp hz

/-! ### (ii) The localization reformulation -/

/-- The ring homomorphism `A_p →+* B_q` induced by `f`, where `p = qᶜ`. -/
noncomputable def localRingHomOf (f : A →+* B) (q : Ideal B) [hq : q.IsPrime] :
    Localization.AtPrime (q.comap f) →+* Localization.AtPrime q :=
  haveI : (q.comap f).IsPrime := Ideal.IsPrime.comap f
  Localization.localRingHom (q.comap f) q f rfl

theorem localRingHomOf_apply (f : A →+* B) (q : Ideal B) [hq : q.IsPrime] (a : A) :
    localRingHomOf f q (algebraMap A (Localization.AtPrime (q.comap f)) a) =
      algebraMap B (Localization.AtPrime q) (f a) :=
  Localization.localRingHom_to_map (q.comap f) q f rfl a

/-- Statement (c') of the exercise: for every prime `q` of `B`, the induced map
`Spec B_q → Spec A_{qᶜ}` is surjective. -/
def LocalizationSurjective (f : A →+* B) : Prop :=
  ∀ (q : Ideal B), ∀ _ : q.IsPrime,
    Function.Surjective (PrimeSpectrum.comap (localRingHomOf f q))

/-- `(c') ⇒ (b')`. -/
theorem hasGoingDown_of_localizationSurjective (f : A →+* B)
    (H : LocalizationSurjective f) : HasGoingDown f := by
  intro p₁ p₂ q₁ h₁ h₂ hq₁ hcom hle
  subst hcom
  haveI := hq₁
  haveI hq' : (q₁.comap f).IsPrime := h₁
  -- the prime `p₂ A_{p₁}` of the localization at `p₁`
  have hle' : p₂ ≤ q₁.comap f := hle
  have hpl : (p₂.map (algebraMap A (Localization.AtPrime (q₁.comap f)))).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (q₁.comap f) hle'
  obtain ⟨y, hy⟩ := H q₁ hq₁ ⟨p₂.map (algebraMap A (Localization.AtPrime (q₁.comap f))), hpl⟩
  have hy' : y.asIdeal.comap (localRingHomOf f q₁) =
      p₂.map (algebraMap A (Localization.AtPrime (q₁.comap f))) :=
    congrArg PrimeSpectrum.asIdeal hy
  haveI := y.2
  -- the candidate prime of `B` below `q₁`
  refine ⟨y.asIdeal.under B, Ideal.IsPrime.under B y.asIdeal, ?_, ?_⟩
  · -- it contracts to `p₂`
    have hcomp : (localRingHomOf f q₁).comp
          (algebraMap A (Localization.AtPrime (q₁.comap f))) =
        (algebraMap B (Localization.AtPrime q₁)).comp f := by
      ext a
      exact localRingHomOf_apply f q₁ a
    rw [Ideal.under_def, Ideal.comap_comap, ← hcomp, ← Ideal.comap_comap, hy']
    exact Ideal.under_map_of_isLocalizationAtPrime (q₁.comap f) hle'
  · -- it is contained in `q₁`
    exact (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime q₁) q₁
      ⟨y.asIdeal, y.2⟩).2.2

/-- `(b') ⇒ (c')`. -/
theorem localizationSurjective_of_hasGoingDown (f : A →+* B) (H : HasGoingDown f) :
    LocalizationSurjective f := by
  intro q hq y
  haveI := hq
  haveI hq' : (q.comap f).IsPrime := Ideal.IsPrime.comap f
  -- the prime of `A` corresponding to `y`
  have hyA : y.asIdeal.comap (algebraMap A (Localization.AtPrime (q.comap f))) =
      y.asIdeal.under A := rfl
  have hp' : (y.asIdeal.under A).IsPrime := Ideal.IsPrime.under A y.asIdeal
  have hple : y.asIdeal.under A ≤ q.comap f :=
    (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime (q.comap f)) (q.comap f)
      ⟨y.asIdeal, y.2⟩).2.2
  obtain ⟨Q', hQ', hQ'com, hQ'le⟩ :=
    H (q.comap f) (y.asIdeal.under A) q hq' hp' hq rfl hple
  haveI := hQ'
  have hJ : (Q'.map (algebraMap B (Localization.AtPrime q))).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime q hQ'le
  refine ⟨⟨Q'.map (algebraMap B (Localization.AtPrime q)), hJ⟩, ?_⟩
  -- it suffices to compare the contractions to `A`
  refine PrimeSpectrum.localization_comap_injective (Localization.AtPrime (q.comap f))
    (q.comap f).primeCompl ?_
  have hcomp : (localRingHomOf f q).comp (algebraMap A (Localization.AtPrime (q.comap f))) =
      (algebraMap B (Localization.AtPrime q)).comp f := by
    ext a
    exact localRingHomOf_apply f q a
  have h1 : (Q'.map (algebraMap B (Localization.AtPrime q))).comap
      (algebraMap B (Localization.AtPrime q)) = Q' :=
    Ideal.under_map_of_isLocalizationAtPrime q hQ'le
  have hxas : (⟨Q'.map (algebraMap B (Localization.AtPrime q)), hJ⟩ :
      PrimeSpectrum (Localization.AtPrime q)).asIdeal =
      Q'.map (algebraMap B (Localization.AtPrime q)) := rfl
  have hLHS : (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime (q.comap f)))
        (PrimeSpectrum.comap (localRingHomOf f q)
          ⟨Q'.map (algebraMap B (Localization.AtPrime q)), hJ⟩)).asIdeal
      = Ideal.comap f Q' := by
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, hxas, Ideal.comap_comap,
      hcomp, ← Ideal.comap_comap, h1]
  have hRHS : (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime (q.comap f))) y).asIdeal
      = Ideal.comap f Q' := by
    rw [PrimeSpectrum.comap_asIdeal, hyA, ← hQ'com]
  apply PrimeSpectrum.ext
  rw [hLHS, hRHS]

/-! ### The exercise -/

/-- **Atiyah–Macdonald, Exercise 5.10.**  For a ring homomorphism `f : A →+* B` with
associated map `f* : Spec B → Spec A`:

(i)  if `f*` is closed then `f` has going-up, and going-up is equivalent to the
     surjectivity of `Spec (B/q) → Spec (A/qᶜ)` for every prime `q`;
(ii) if `f*` is open then `f` has going-down, and going-down is equivalent to the
     surjectivity of `Spec B_q → Spec A_{qᶜ}` for every prime `q`. -/
theorem solution (f : A →+* B) :
    (IsClosedMap (PrimeSpectrum.comap f) → HasGoingUp f) ∧
    (HasGoingUp f ↔ QuotientSurjective f) ∧
    (IsOpenMap (PrimeSpectrum.comap f) → HasGoingDown f) ∧
    (HasGoingDown f ↔ LocalizationSurjective f) :=
  ⟨hasGoingUp_of_isClosedMap f,
   ⟨quotientSurjective_of_hasGoingUp f, hasGoingUp_of_quotientSurjective f⟩,
   hasGoingDown_of_isOpenMap f,
   ⟨localizationSurjective_of_hasGoingDown f, hasGoingDown_of_localizationSurjective f⟩⟩

end AtiyahMcdonald69.Ex_5_10

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_5_10.hasGoingUp_of_isClosedMap
#print axioms AtiyahMcdonald69.Ex_5_10.quotientSurjective_of_hasGoingUp
#print axioms AtiyahMcdonald69.Ex_5_10.hasGoingUp_of_quotientSurjective
#print axioms AtiyahMcdonald69.Ex_5_10.exists_prime_le_of_forall_exists_prime
#print axioms AtiyahMcdonald69.Ex_5_10.hasGoingDown_of_isOpenMap
#print axioms AtiyahMcdonald69.Ex_5_10.hasGoingDown_of_localizationSurjective
#print axioms AtiyahMcdonald69.Ex_5_10.localizationSurjective_of_hasGoingDown
#print axioms AtiyahMcdonald69.Ex_5_10.solution
