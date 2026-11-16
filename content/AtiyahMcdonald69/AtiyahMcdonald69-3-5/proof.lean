import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 3, Exercise 5

Statement (from the text, Chapter 3 exercises, item 5 — recovered from
`.scratch/reference/atiyah-macdonald-original.txt`):

> Let `A` be a ring. Suppose that, for each prime ideal `𝔭`, the local ring `A_𝔭` has no
> nilpotent element `≠ 0`. Show that `A` has no nilpotent element `≠ 0`. If each `A_𝔭` is an
> integral domain, is `A` necessarily an integral domain?

Formalization:

* `reduced_of_localization_reduced` (with `no_nilpotent_of_no_nilpotent_localization` giving
  the book's elementwise phrasing) proves the first assertion: if no localization `A_𝔭` has a
  nonzero nilpotent element, then `A` has none;
* `isReduced_localization` proves the converse (a localization of a reduced ring is reduced),
  so `isReduced_iff_forall_isReduced_localizationAtPrime` states that being reduced — unlike
  being a domain — *is* a local property of a ring;
* `exRing_localization_isDomain` and `exRing_not_isDomain` answer the second question
  negatively, with the counterexample `𝔽₂ × 𝔽₂`: every localization at a prime ideal is an
  integral domain, but the ring is not an integral domain. This is packaged in
  `not_isDomain_of_forall_localizationAtPrime_isDomain`, and `solution` bundles both parts.
-/

namespace AtiyahMcdonald69.Ex_3_5

/-! ## Part 1: reducedness is detected at prime ideals -/

/-- A localization of a reduced ring is reduced: the converse of
`reduced_of_localization_reduced`.

Proof: write `y = a / s`. If `y ^ n = 0` with `n ≥ 1`, then `a ^ n / s ^ n = 0`, so `m * a ^ n = 0`
for some `m ∈ M`; hence `(m * a) ^ n = m ^ (n-1) * (m * a ^ n) = 0`, and since `A` is reduced,
`m * a = 0`, i.e. `a / s = 0`. (For `n = 0`, `1 = 0` in the localization, which is therefore
trivial.) -/
theorem isReduced_localization {A : Type*} [CommRing A] [IsReduced A] (M : Submonoid A) :
    IsReduced (Localization M) := by
  rw [isReduced_iff]
  intro y hy
  obtain ⟨n, hn⟩ := hy
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (S := Localization M) M y
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [pow_zero] at hn
    exact @Subsingleton.elim (Localization M) (subsingleton_of_zero_eq_one hn.symm) _ _
  · rw [← IsLocalization.mk'_pow] at hn
    rw [IsLocalization.mk'_eq_zero_iff] at hn
    obtain ⟨m, hm⟩ := hn
    -- `m * a` is nilpotent, hence zero because `A` is reduced
    have hnil : IsNilpotent ((m : A) * a) := by
      refine ⟨n, ?_⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      rw [hk] at hm ⊢
      have h2 : ((m : A) ^ k * (m : A)) * (a ^ k * a) =
          (m : A) ^ k * ((m : A) * a ^ (k + 1)) := by
        rw [pow_succ a k]
        ring
      rw [mul_pow, pow_succ (m : A) k, pow_succ a k, h2, hm, mul_zero]
    have hma : (m : A) * a = 0 := hnil.eq_zero
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨m, hma⟩

/-- **Atiyah–Macdonald, Exercise 3.5, first part.**
If for every prime ideal `𝔭` the local ring `A_𝔭` has no nonzero nilpotent element, then `A`
has no nonzero nilpotent element.

Proof: let `x` be nilpotent with `x ≠ 0`. Then the annihilator `J` of `x` (the annihilator of
the cyclic submodule `A ∙ x`) is a proper ideal, so it is contained in a maximal, hence prime,
ideal `𝔪`. As `J ≤ 𝔪`, no `s ∉ 𝔪` annihilates `x`, so the image of `x` in `A_𝔪` is nonzero
(by `IsLocalization.map_eq_zero_iff`); but that image is nilpotent because `x` is, which
contradicts reducedness of `A_𝔪`. -/
theorem reduced_of_localization_reduced {A : Type*} [CommRing A]
    (h : ∀ (p : Ideal A) [_hp : p.IsPrime], IsReduced (Localization p.primeCompl)) :
    IsReduced A := by
  rw [isReduced_iff]
  intro x hx
  by_contra hx0
  -- the annihilator of `x`
  set J : Ideal A := (Submodule.span A ({x} : Set A)).annihilator with hJ
  have hJnt : J ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ J := htop ▸ Submodule.mem_top
    rw [hJ, Submodule.mem_annihilator_span_singleton] at h1
    exact hx0 (by simpa using h1)
  obtain ⟨m, hmmax, hJm⟩ := Ideal.exists_le_maximal J hJnt
  have hmprime : m.IsPrime := hmmax.isPrime
  have hred : IsReduced (Localization m.primeCompl) := h m
  -- the image of the nilpotent element `x` in `A_m` is nilpotent
  have hnil : IsNilpotent (algebraMap A (Localization m.primeCompl) x) := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
  have hzero : algebraMap A (Localization m.primeCompl) x = 0 := hnil.eq_zero
  -- ... so it is zero, i.e. some `s ∉ m` annihilates `x`
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff m.primeCompl (Localization m.primeCompl) x).mp hzero
  have hsmem : (s : A) ∈ J := by
    rw [hJ, Submodule.mem_annihilator_span_singleton]
    exact hs
  exact s.2 (hJm hsmem)

/-- **Reducedness is a local property of a ring**: `A` has no nonzero nilpotent element if and
only if none of its localizations at prime ideals has. -/
theorem isReduced_iff_forall_isReduced_localizationAtPrime {A : Type*} [CommRing A] :
    IsReduced A ↔ ∀ (p : Ideal A) [_hp : p.IsPrime], IsReduced (Localization p.primeCompl) := by
  constructor
  · intro hA p hp
    exact @isReduced_localization A _ hA p.primeCompl
  · exact reduced_of_localization_reduced

/-- **Atiyah–Macdonald, Exercise 3.5, first part**, in the elementwise phrasing of the book: if
no localization `A_𝔭` has a nonzero nilpotent element, neither has `A`. -/
theorem no_nilpotent_of_no_nilpotent_localization {A : Type*} [CommRing A]
    (h : ∀ (p : Ideal A) [_hp : p.IsPrime], ∀ (n : ℕ) (y : Localization p.primeCompl),
      y ^ n = 0 → y = 0) :
    ∀ (n : ℕ) (x : A), x ^ n = 0 → x = 0 := by
  have hred : IsReduced A := by
    refine reduced_of_localization_reduced (fun p hp => ?_)
    rw [isReduced_iff]
    intro y hy
    obtain ⟨n, hn⟩ := hy
    exact h p n y hn
  rw [isReduced_iff] at hred
  intro n x hx
  exact hred x ⟨n, hx⟩

/-! ## Part 2: the answer to the second question is negative -/

/-- If `K` is a field, `S` any commutative ring and `q` a prime ideal of `K`, then localizing
`K × S` at the complement of the prime ideal `q × ⊤` gives an integral domain.

Indeed the first projection `K × S → K` maps the complement of `q × ⊤` into the units of the
field `K`, so it induces a ring homomorphism from the localization to `K`
(`IsLocalization.lift`), which is injective: if `x` and `y` have the same first coordinate,
then `(1, 0)` (which lies in the complement of `q × ⊤`) multiplies them to the same element.
A ring that embeds into a field is an integral domain. -/
theorem isDomain_localization_prod_left {K S : Type*} [Field K] [CommRing S]
    (q : Ideal K) [hq : q.IsPrime] [_hpq : (Ideal.prod q (⊤ : Ideal S)).IsPrime] :
    IsDomain (Localization (Ideal.prod q (⊤ : Ideal S)).primeCompl) := by
  set M : Submonoid (K × S) := (Ideal.prod q (⊤ : Ideal S)).primeCompl with hM
  have hmem : ∀ x : K × S, x ∈ M ↔ x.1 ∉ q := by
    intro x
    rw [hM, Ideal.mem_primeCompl_iff]
    simp [Ideal.mem_prod]
  have hfst_unit : ∀ y : M, IsUnit (RingHom.fst K S (y : K × S)) := by
    rintro ⟨⟨a, b⟩, hy⟩
    have ha : a ∉ q := (hmem (a, b)).mp hy
    have ha0 : a ≠ 0 := fun h => ha (h ▸ q.zero_mem)
    simpa using isUnit_iff_ne_zero.mpr ha0
  have hinj : Function.Injective (IsLocalization.lift (M := M) (S := Localization M)
      (g := RingHom.fst K S) hfst_unit) := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro hxy
      have h2 := congrArg (IsLocalization.lift (M := M) (S := Localization M)
        (g := RingHom.fst K S) hfst_unit) hxy
      simpa [IsLocalization.lift_eq] using h2
    · intro hxy
      have hxy' : x.1 = y.1 := hxy
      rw [IsLocalization.eq_iff_exists M (Localization M)]
      refine ⟨⟨(1, 0), ?_⟩, ?_⟩
      · rw [hmem]
        exact Ideal.IsPrime.one_notMem hq
      · ext <;> simp [hxy']
  refine (isDomain_iff_noZeroDivisors_and_nontrivial (Localization M)).mpr ⟨?_, ?_⟩
  · exact Function.Injective.noZeroDivisors _ hinj (map_zero _) (map_mul _)
  · exact IsLocalization.AtPrime.nontrivial (Localization M) (Ideal.prod q (⊤ : Ideal S))

/-- The mirror image of `isDomain_localization_prod_left`: localizing `K × S` at the
complement of the prime ideal `⊤ × q`, where `q` is a prime ideal of the field `S`, gives an
integral domain. -/
theorem isDomain_localization_prod_right {K S : Type*} [CommRing K] [Field S]
    (q : Ideal S) [hq : q.IsPrime] [_hpq : (Ideal.prod (⊤ : Ideal K) q).IsPrime] :
    IsDomain (Localization (Ideal.prod (⊤ : Ideal K) q).primeCompl) := by
  set M : Submonoid (K × S) := (Ideal.prod (⊤ : Ideal K) q).primeCompl with hM
  have hmem : ∀ x : K × S, x ∈ M ↔ x.2 ∉ q := by
    intro x
    rw [hM, Ideal.mem_primeCompl_iff]
    simp [Ideal.mem_prod]
  have hsnd_unit : ∀ y : M, IsUnit (RingHom.snd K S (y : K × S)) := by
    rintro ⟨⟨a, b⟩, hy⟩
    have hb : b ∉ q := (hmem (a, b)).mp hy
    have hb0 : b ≠ 0 := fun h => hb (h ▸ q.zero_mem)
    simpa using isUnit_iff_ne_zero.mpr hb0
  have hinj : Function.Injective (IsLocalization.lift (M := M) (S := Localization M)
      (g := RingHom.snd K S) hsnd_unit) := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro hxy
      have h2 := congrArg (IsLocalization.lift (M := M) (S := Localization M)
        (g := RingHom.snd K S) hsnd_unit) hxy
      simpa [IsLocalization.lift_eq] using h2
    · intro hxy
      have hxy' : x.2 = y.2 := hxy
      rw [IsLocalization.eq_iff_exists M (Localization M)]
      refine ⟨⟨(0, 1), ?_⟩, ?_⟩
      · rw [hmem]
        exact Ideal.IsPrime.one_notMem hq
      · ext <;> simp [hxy']
  refine (isDomain_iff_noZeroDivisors_and_nontrivial (Localization M)).mpr ⟨?_, ?_⟩
  · exact Function.Injective.noZeroDivisors _ hinj (map_zero _) (map_mul _)
  · exact IsLocalization.AtPrime.nontrivial (Localization M) (Ideal.prod (⊤ : Ideal K) q)

/-- The counterexample ring `𝔽₂ × 𝔽₂`. -/
abbrev exRing : Type := ZMod 2 × ZMod 2

/-- Every localization of `𝔽₂ × 𝔽₂` at a prime ideal is an integral domain.

The prime ideals of a product ring are the ideals `q × ⊤` and `⊤ × q` with `q` prime
(`Ideal.ideal_prod_prime`), and both localizations are integral domains by the two lemmas
above. -/
theorem exRing_localization_isDomain (p : Ideal exRing) [hp : p.IsPrime] :
    IsDomain (Localization p.primeCompl) := by
  rcases (Ideal.ideal_prod_prime p).mp hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact isDomain_localization_prod_left (S := ZMod 2) q (hq := hq) (_hpq := hp)
  · exact isDomain_localization_prod_right (K := ZMod 2) q (hq := hq) (_hpq := hp)

/-- `𝔽₂ × 𝔽₂` is not an integral domain: `(1,0) * (0,1) = 0` while both factors are nonzero. -/
theorem exRing_not_isDomain : ¬ IsDomain exRing := by
  intro h
  have hz : ((1, 0) : exRing) * ((0, 1) : exRing) = 0 := by simp
  have h1 : ((1, 0) : exRing) = 0 ∨ ((0, 1) : exRing) = 0 := mul_eq_zero.mp hz
  rcases h1 with h1 | h1 <;> simp at h1

/-- **Atiyah–Macdonald, Exercise 3.5, second question.**  The answer is no: there is a ring
which is not an integral domain although each of its localizations at a prime ideal is one.
(So being an integral domain is not a local property of a ring.) -/
theorem not_isDomain_of_forall_localizationAtPrime_isDomain :
    ∃ (A : Type) (_ : CommRing A),
      (∀ (p : Ideal A) [_hp : p.IsPrime], IsDomain (Localization p.primeCompl)) ∧ ¬ IsDomain A :=
  ⟨exRing, inferInstance, fun p hp => @exRing_localization_isDomain p hp, exRing_not_isDomain⟩

/-- The complete solution of Atiyah–Macdonald, Chapter 3, Exercise 5: the first assertion holds
in full (if no localization at a prime ideal has a nonzero nilpotent element, neither has the
ring), and the analogous assertion for integral domains fails. -/
theorem solution :
    (∀ (A : Type) [CommRing A],
        (∀ (p : Ideal A) [_hp : p.IsPrime], IsReduced (Localization p.primeCompl)) → IsReduced A)
      ∧ ¬ (∀ (A : Type) [CommRing A],
        (∀ (p : Ideal A) [_hp : p.IsPrime], IsDomain (Localization p.primeCompl)) → IsDomain A) := by
  refine ⟨fun A _ h => reduced_of_localization_reduced h, ?_⟩
  intro h
  exact exRing_not_isDomain (h exRing (fun p hp => @exRing_localization_isDomain p hp))

end AtiyahMcdonald69.Ex_3_5

#print axioms AtiyahMcdonald69.Ex_3_5.isReduced_localization
#print axioms AtiyahMcdonald69.Ex_3_5.reduced_of_localization_reduced
#print axioms AtiyahMcdonald69.Ex_3_5.isReduced_iff_forall_isReduced_localizationAtPrime
#print axioms AtiyahMcdonald69.Ex_3_5.no_nilpotent_of_no_nilpotent_localization
#print axioms AtiyahMcdonald69.Ex_3_5.isDomain_localization_prod_left
#print axioms AtiyahMcdonald69.Ex_3_5.isDomain_localization_prod_right
#print axioms AtiyahMcdonald69.Ex_3_5.exRing_localization_isDomain
#print axioms AtiyahMcdonald69.Ex_3_5.exRing_not_isDomain
#print axioms AtiyahMcdonald69.Ex_3_5.not_isDomain_of_forall_localizationAtPrime_isDomain
#print axioms AtiyahMcdonald69.Ex_3_5.solution
