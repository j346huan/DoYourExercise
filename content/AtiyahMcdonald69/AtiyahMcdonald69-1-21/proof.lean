import Mathlib

/-!
# Atiyah–Macdonald, Exercise 1.21

Formalisation of Exercise 21 of Chapter 1 of M. F. Atiyah and I. G. Macdonald,
*Introduction to Commutative Algebra* (Addison-Wesley, 1969), p. 13.

The book states: let `φ : A → B` be a ring homomorphism, `X = Spec(A)`, `Y = Spec(B)`.
If `q ∈ Y` then `φ⁻¹(q)` is a prime ideal of `A`, hence a point of `X`, so `φ` induces a
mapping `φ* : Y → X`. Prove:

(i) if `f ∈ A` then `φ*⁻¹(X_f) = Y_{φ(f)}`, and hence `φ*` is continuous;
(ii) if `𝔞` is an ideal of `A` then `φ*⁻¹(V(𝔞)) = V(𝔞ᵉ)`;
(iii) if `𝔟` is an ideal of `B` then `closure (φ*(V(𝔟))) = V(𝔟ᶜ)`;
(iv) if `φ` is surjective then `φ*` is a homeomorphism of `Y` onto the closed subset
  `V(Ker φ)` of `X`; in particular `Spec(A)` and `Spec(A/𝔑)` (with `𝔑` the nilradical)
  are naturally homeomorphic;
(v) `φ*(Y)` is dense in `X` if and only if `Ker(φ) ⊆ 𝔑`; in particular `φ` injective
  implies that `φ*(Y)` is dense in `X`;
(vi) for a second ring homomorphism `ψ : B → C` we have `(ψ ∘ φ)* = φ* ∘ ψ*`;
(vii) if `A` is an integral domain with just one non-zero prime ideal `𝔭`, `K` is a field of
  fractions of `A`, `B = (A/𝔭) × K` and `φ(x) = (x̄, x)` (where `x̄` is the image of `x` in
  `A/𝔭`), then `φ*` is bijective but is not a homeomorphism.

Formalisation dictionary (Mathlib names for the book's notation):

* `X = PrimeSpectrum A`, `Y = PrimeSpectrum B`, and `φ* = PrimeSpectrum.comap φ`, the map
  sending a prime `q` to the contraction `Ideal.comap φ q` (`part_0_asIdeal`);
* `X_f = PrimeSpectrum.basicOpen f`, the set of primes not containing `f`;
* `V(𝔞) = PrimeSpectrum.zeroLocus 𝔞`, the set of primes containing `𝔞`;
* `𝔞ᵉ = Ideal.map φ 𝔞`, `𝔟ᶜ = Ideal.comap φ 𝔟`, `𝔑 = nilradical A`;
* `closure` is the closure in the Zariski topology, `DenseRange` denseness of the range.

## Coverage

* preamble (`q ∈ Y ↦ φ⁻¹(q) ∈ X`): `part_0_isPrime`, `part_0_asIdeal`
* (i) `part_i_preimage_basicOpen`, `part_i_continuous`
* (ii) `part_ii`
* (iii) `part_iii`
* (iv) `part_iv_zeroLocus_isClosed`, `part_iv_homeomorph`, `part_iv_homeomorph_apply`,
  `part_iv_homeomorph_quotient_nilradical`, `part_iv_homeomorph_quotient_nilradical_apply`
* (v) `part_v`, `part_v_of_injective`
* (vi) `part_vi`
* (vii) `part_vii` (with `part_vii_bijective`, `part_vii_not_isHomeomorph` and the
  supporting lemmas `part_vii_isMaximal`, `part_vii_φ`, `part_vii_eq_of_isPrime`,
  `part_vii_comap_prod_bot_top`, `part_vii_comap_prod_top_bot`,
  `part_vii_isMaximal_prod_top_bot`)

Reference: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-21>
-/

namespace AtiyahMcdonald69.Ex_1_21

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The map `φ*` of the exercise, `q ↦ φ⁻¹(q)`: `PrimeSpectrum.comap` is exactly the
contraction of prime ideals along `φ`. -/
theorem part_0_asIdeal (φ : A →+* B) (q : PrimeSpectrum B) :
    (PrimeSpectrum.comap φ q).asIdeal = Ideal.comap φ q.asIdeal :=
  rfl

/-- The contraction `φ⁻¹(q)` of a prime ideal is again prime (the preamble of the exercise:
`q ∈ Y` gives a point `φ⁻¹(q) ∈ X`). -/
theorem part_0_isPrime (φ : A →+* B) (q : PrimeSpectrum B) :
    (Ideal.comap φ q.asIdeal).IsPrime :=
  (PrimeSpectrum.comap φ q).2

/-! ### Part (i): `φ*⁻¹(X_f) = Y_{φ(f)}`, hence `φ*` is continuous -/

/-- Exercise 1.21 (i), first assertion: `φ*⁻¹(X_f) = Y_{φ(f)}`. -/
theorem part_i_preimage_basicOpen (φ : A →+* B) (f : A) :
    PrimeSpectrum.comap φ ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) =
      (PrimeSpectrum.basicOpen (φ f) : Set (PrimeSpectrum B)) := by
  ext q
  simp

/-- Exercise 1.21 (i), second assertion: `φ*` is continuous. -/
theorem part_i_continuous (φ : A →+* B) : Continuous (PrimeSpectrum.comap φ) :=
  PrimeSpectrum.continuous_comap φ

/-! ### Part (ii): `φ*⁻¹(V(𝔞)) = V(𝔞ᵉ)` -/

/-- Exercise 1.21 (ii): if `𝔞` is an ideal of `A`, then `φ*⁻¹(V(𝔞)) = V(𝔞ᵉ)`. -/
theorem part_ii (φ : A →+* B) (𝔞 : Ideal A) :
    PrimeSpectrum.comap φ ⁻¹' (PrimeSpectrum.zeroLocus (𝔞 : Set A)) =
      PrimeSpectrum.zeroLocus ((𝔞.map φ : Ideal B) : Set B) := by
  ext q
  simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal,
    SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.symm

/-! ### Part (iii): `closure (φ*(V(𝔟))) = V(𝔟ᶜ)` -/

/-- Exercise 1.21 (iii): if `𝔟` is an ideal of `B`, then the closure of `φ*(V(𝔟))` is
`V(𝔟ᶜ)`. -/
theorem part_iii (φ : A →+* B) (𝔟 : Ideal B) :
    closure (PrimeSpectrum.comap φ '' (PrimeSpectrum.zeroLocus (𝔟 : Set B))) =
      PrimeSpectrum.zeroLocus ((𝔟.comap φ : Ideal A) : Set A) :=
  PrimeSpectrum.closure_image_comap_zeroLocus φ 𝔟

/-! ### Part (iv): for surjective `φ`, `φ*` is a homeomorphism onto the closed subset
`V(Ker φ)`; in particular `Spec(A) ≃ₜ Spec(A/𝔑)` -/

/-- `V(𝔟)` is closed, so `V(Ker φ)` is a closed subset of `X` (as asserted in (iv)). -/
theorem part_iv_zeroLocus_isClosed (φ : A →+* B) :
    IsClosed (PrimeSpectrum.zeroLocus (RingHom.ker φ : Set A)) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- Exercise 1.21 (iv): if `φ` is surjective, then `φ*` is a homeomorphism of `Y` onto the
closed subset `V(Ker φ)` of `X`. -/
noncomputable def part_iv_homeomorph (φ : A →+* B) (hφ : Function.Surjective φ) :
    PrimeSpectrum B ≃ₜ ↥(PrimeSpectrum.zeroLocus (RingHom.ker φ : Set A)) :=
  (PrimeSpectrum.isClosedEmbedding_comap_of_surjective B φ hφ).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_comap_of_surjective B φ hφ))

/-- The homeomorphism of (iv) is indeed the map `φ*` (corestricted to `V(Ker φ)`). -/
theorem part_iv_homeomorph_apply (φ : A →+* B) (hφ : Function.Surjective φ)
    (q : PrimeSpectrum B) :
    (part_iv_homeomorph φ hφ q : PrimeSpectrum A) = PrimeSpectrum.comap φ q :=
  rfl

/-- Exercise 1.21 (iv), the special case: `Spec(A)` and `Spec(A/𝔑)`, where `𝔑` is the
nilradical of `A`, are naturally homeomorphic (via the quotient map `A → A/𝔑`). -/
noncomputable def part_iv_homeomorph_quotient_nilradical (A : Type*) [CommRing A] :
    PrimeSpectrum (A ⧸ nilradical A) ≃ₜ PrimeSpectrum A :=
  (part_iv_homeomorph (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective).trans <|
    (Homeomorph.setCongr (by rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_nilradical])).trans
      (Homeomorph.Set.univ (PrimeSpectrum A))

/-- The homeomorphism `Spec(A/𝔑) ≃ₜ Spec(A)` is induced by the quotient map. -/
theorem part_iv_homeomorph_quotient_nilradical_apply (A : Type*) [CommRing A]
    (p : PrimeSpectrum (A ⧸ nilradical A)) :
    part_iv_homeomorph_quotient_nilradical A p =
      PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical A)) p :=
  rfl

/-! ### Part (v): `φ*(Y)` is dense in `X` iff `Ker(φ) ⊆ 𝔑` -/

/-- Exercise 1.21 (v): `φ*(Y)` is dense in `X` if and only if `Ker(φ) ⊆ 𝔑`. -/
theorem part_v (φ : A →+* B) :
    DenseRange (PrimeSpectrum.comap φ) ↔ RingHom.ker φ ≤ nilradical A :=
  PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ

/-- Exercise 1.21 (v), the stated consequence: if `φ` is injective, then `φ*(Y)` is dense
in `X`. -/
theorem part_v_of_injective (φ : A →+* B) (hφ : Function.Injective φ) :
    DenseRange (PrimeSpectrum.comap φ) := by
  rw [part_v, (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
  exact bot_le

/-! ### Part (vi): `(ψ ∘ φ)* = φ* ∘ ψ*` -/

/-- Exercise 1.21 (vi): `(ψ ∘ φ)* = φ* ∘ ψ*`.  (The book prints `(ψ ∘ ψ)*` in (vi); the
statement for `ψ ∘ φ` is the one used and proved here.) -/
theorem part_vi (φ : A →+* B) (ψ : B →+* C) :
    PrimeSpectrum.comap (ψ.comp φ) =
      (PrimeSpectrum.comap φ) ∘ (PrimeSpectrum.comap ψ) :=
  PrimeSpectrum.comap_comp φ ψ

/-! ### Part (vii): the example `B = (A/𝔭) × K`, `φ(x) = (x̄, x)`, where `𝔭` is the only
non-zero prime ideal of the domain `A` and `K` is a field of fractions of `A` -/

/-- A prime ideal of a field is the zero ideal. -/
theorem part_vii_eq_bot_of_isPrime_of_isField {F : Type*} [Field F] {q : Ideal F}
    (hq : q.IsPrime) : q = ⊥ := by
  by_contra h
  exact (Ring.not_isField_of_ne_of_ne h (Ideal.IsPrime.ne_top hq)) (Field.toIsField F)

/-- In the situation of (vii), the unique non-zero prime ideal `𝔭` is maximal. -/
theorem part_vii_isMaximal {A : Type*} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭 : 𝔭 ≠ ⊥) (huniq : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → q = 𝔭) : 𝔭.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · intro h1
    exact Ideal.IsPrime.ne_top ‹𝔭.IsPrime› ((Ideal.eq_top_iff_one 𝔭).mpr h1)
  · intro J x hJ hx hxJ
    by_cases hJtop : J = ⊤
    · rw [hJtop]; exact Submodule.mem_top
    · exfalso
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
      have h𝔭M : 𝔭 ≤ M := hJ.trans hJM
      have hMne : M ≠ ⊥ := fun h => h𝔭 (le_antisymm (h ▸ h𝔭M) bot_le)
      have hM𝔭 : M = 𝔭 := huniq M hM.isPrime hMne
      exact hx (hM𝔭 ▸ hJM hxJ)

/-- The ring homomorphism `φ(x) = (x̄, x)` of Exercise 1.21 (vii), where `x̄` is the image of
`x` in `A/𝔭` and `K` is a field of fractions of `A`. -/
noncomputable def part_vii_φ {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]
    (𝔭 : Ideal A) : A →+* (A ⧸ 𝔭) × K :=
  (Ideal.Quotient.mk 𝔭).prod (algebraMap A K)

theorem part_vii_isPrime_prod_bot_top {A K : Type*} [CommRing A] [Field K] (𝔭 : Ideal A)
    [𝔭.IsMaximal] : (Ideal.prod (⊥ : Ideal (A ⧸ 𝔭)) (⊤ : Ideal K)).IsPrime := by
  let _ : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  exact Ideal.isPrime_ideal_prod_top (I := ⊥)

theorem part_vii_isPrime_prod_top_bot {A K : Type*} [CommRing A] [Field K] (𝔭 : Ideal A)
    [𝔭.IsMaximal] : (Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K)).IsPrime := by
  let _ : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  exact Ideal.isPrime_ideal_prod_top' (I := ⊥)

/-- `φ*` sends the prime `⊥ × ⊤` of `(A/𝔭) × K` to `𝔭`. -/
theorem part_vii_comap_prod_bot_top {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]
    (𝔭 : Ideal A) :
    (Ideal.prod (⊥ : Ideal (A ⧸ 𝔭)) (⊤ : Ideal K)).comap (part_vii_φ (K := K) 𝔭) = 𝔭 := by
  ext x
  simp [part_vii_φ, Ideal.mem_prod, Ideal.Quotient.eq_zero_iff_mem]

/-- `φ*` sends the prime `⊤ × ⊥` of `(A/𝔭) × K` to `⊥`. -/
theorem part_vii_comap_prod_top_bot {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]
    [IsFractionRing A K] (𝔭 : Ideal A) :
    (Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K)).comap (part_vii_φ (K := K) 𝔭) = ⊥ := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_prod, Ideal.mem_bot, Submodule.mem_top, part_vii_φ,
    RingHom.prod_apply, true_and]
  exact ⟨fun h => (IsFractionRing.injective A K) (by simpa using h),
    fun h => by rw [h, map_zero]⟩

/-- `⊤ × ⊥` is a maximal ideal of `(A/𝔭) × K`. -/
theorem part_vii_isMaximal_prod_top_bot {A K : Type*} [CommRing A] [Field K] (𝔭 : Ideal A) :
    (Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K)).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · intro h
    rw [Ideal.mem_prod, Ideal.mem_bot] at h
    exact one_ne_zero h.2
  · intro J x hle hx hxJ
    have hx2 : x.2 ≠ 0 := by
      intro h0
      refine hx ?_
      rw [Ideal.mem_prod]
      exact ⟨Submodule.mem_top, h0⟩
    have h01 : (0, 1) ∈ J := by
      have hm := J.mul_mem_right (0, x.2⁻¹) hxJ
      rwa [Prod.mk_mul_mk, mul_zero, mul_inv_cancel₀ hx2] at hm
    have h10 : (1, 0) ∈ J := hle (by rw [Ideal.mem_prod]; exact ⟨Submodule.mem_top, rfl⟩)
    have hone : (1 : (A ⧸ 𝔭) × K) = (1, 0) + (0, 1) := Prod.ext (by simp) (by simp)
    rw [hone]
    exact J.add_mem h10 h01

/-- The only prime ideals of `(A/𝔭) × K` are `⊥ × ⊤` and `⊤ × ⊥`. -/
theorem part_vii_eq_of_isPrime {A K : Type*} [CommRing A] [Field K] (𝔭 : Ideal A)
    [𝔭.IsMaximal] (q : Ideal ((A ⧸ 𝔭) × K)) (hq : q.IsPrime) :
    q = Ideal.prod (⊥ : Ideal (A ⧸ 𝔭)) (⊤ : Ideal K) ∨
      q = Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K) := by
  let _ : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  rcases (Ideal.ideal_prod_prime q).mp hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · left
    rw [part_vii_eq_bot_of_isPrime_of_isField hp]
  · right
    rw [part_vii_eq_bot_of_isPrime_of_isField hp]

/-- Exercise 1.21 (vii), first assertion: `φ*` is bijective. -/
theorem part_vii_bijective {A K : Type*} [CommRing A] [IsDomain A] [Field K] (𝔭 : Ideal A)
    [𝔭.IsPrime] [Algebra A K] [IsFractionRing A K] (h𝔭 : 𝔭 ≠ ⊥)
    (huniq : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → q = 𝔭) :
    Function.Bijective (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭)) := by
  have hmax : 𝔭.IsMaximal := part_vii_isMaximal 𝔭 h𝔭 huniq
  let _ : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  constructor
  · intro q q' heq
    have h1 := part_vii_eq_of_isPrime (K := K) 𝔭 q.asIdeal q.2
    have h2 := part_vii_eq_of_isPrime (K := K) 𝔭 q'.asIdeal q'.2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact PrimeSpectrum.ext (h1.trans h2.symm)
    · exfalso
      have hq : (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭) q).asIdeal = 𝔭 := by
        rw [PrimeSpectrum.comap_asIdeal, h1]
        exact part_vii_comap_prod_bot_top 𝔭
      have hq' : (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭) q').asIdeal = ⊥ := by
        rw [PrimeSpectrum.comap_asIdeal, h2]
        exact part_vii_comap_prod_top_bot 𝔭
      refine h𝔭 ?_
      rw [← hq, heq, hq']
    · exfalso
      have hq : (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭) q).asIdeal = ⊥ := by
        rw [PrimeSpectrum.comap_asIdeal, h1]
        exact part_vii_comap_prod_top_bot 𝔭
      have hq' : (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭) q').asIdeal = 𝔭 := by
        rw [PrimeSpectrum.comap_asIdeal, h2]
        exact part_vii_comap_prod_bot_top 𝔭
      refine h𝔭 ?_
      rw [← hq', ← heq, hq]
    · exact PrimeSpectrum.ext (h1.trans h2.symm)
  · intro p
    have hp : p.asIdeal = ⊥ ∨ p.asIdeal = 𝔭 := by
      by_cases h : p.asIdeal = ⊥
      · exact Or.inl h
      · exact Or.inr (huniq p.asIdeal p.2 h)
    rcases hp with hp | hp
    · refine ⟨⟨_, part_vii_isPrime_prod_top_bot (K := K) 𝔭⟩, ?_⟩
      exact PrimeSpectrum.ext (by
        rw [PrimeSpectrum.comap_asIdeal, part_vii_comap_prod_top_bot, hp])
    · refine ⟨⟨_, part_vii_isPrime_prod_bot_top (K := K) 𝔭⟩, ?_⟩
      exact PrimeSpectrum.ext (by
        rw [PrimeSpectrum.comap_asIdeal, part_vii_comap_prod_bot_top, hp])

/-- Exercise 1.21 (vii), second assertion: `φ*` is not a homeomorphism. -/
theorem part_vii_not_isHomeomorph {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    (𝔭 : Ideal A) [𝔭.IsPrime] [Algebra A K] [IsFractionRing A K] (h𝔭 : 𝔭 ≠ ⊥)
    (huniq : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → q = 𝔭) :
    ¬ IsHomeomorph (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭)) := by
  have hmax : 𝔭.IsMaximal := part_vii_isMaximal 𝔭 h𝔭 huniq
  let _ : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  intro hh
  have hclosed : IsClosed
      ({⟨Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K),
        part_vii_isPrime_prod_top_bot (K := K) 𝔭⟩} :
        Set (PrimeSpectrum ((A ⧸ 𝔭) × K))) := by
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    simpa using part_vii_isMaximal_prod_top_bot (K := K) 𝔭
  have hnotclosed : ¬ IsClosed ({⟨(⊥ : Ideal A), Ideal.isPrime_bot⟩} : Set (PrimeSpectrum A)) := by
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    intro hbot
    have hb : (⊥ : Ideal A) = 𝔭 := hbot.eq_of_le (Ideal.IsPrime.ne_top ‹𝔭.IsPrime›) bot_le
    exact h𝔭 hb.symm
  have himage : PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭) ''
      {⟨Ideal.prod (⊤ : Ideal (A ⧸ 𝔭)) (⊥ : Ideal K),
        part_vii_isPrime_prod_top_bot (K := K) 𝔭⟩}
      = {⟨(⊥ : Ideal A), Ideal.isPrime_bot⟩} := by
    rw [Set.image_singleton, Set.singleton_eq_singleton_iff]
    exact PrimeSpectrum.ext (part_vii_comap_prod_top_bot 𝔭)
  have hcl := hh.isClosedMap _ hclosed
  rw [himage] at hcl
  exact hnotclosed hcl

/-- Exercise 1.21 (vii), both assertions together: `φ*` is bijective but not a
homeomorphism. -/
theorem part_vii {A K : Type*} [CommRing A] [IsDomain A] [Field K] (𝔭 : Ideal A) [𝔭.IsPrime]
    [Algebra A K] [IsFractionRing A K] (h𝔭 : 𝔭 ≠ ⊥)
    (huniq : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → q = 𝔭) :
    Function.Bijective (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭)) ∧
      ¬ IsHomeomorph (PrimeSpectrum.comap (part_vii_φ (K := K) 𝔭)) :=
  ⟨part_vii_bijective 𝔭 h𝔭 huniq, part_vii_not_isHomeomorph 𝔭 h𝔭 huniq⟩

/-- Exercise 1.21 (vii) with the canonical choice `K = FractionRing A` for the field of
fractions. -/
theorem part_vii_fractionRing {A : Type*} [CommRing A] [IsDomain A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭 : 𝔭 ≠ ⊥) (huniq : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → q = 𝔭) :
    Function.Bijective (PrimeSpectrum.comap (part_vii_φ (K := FractionRing A) 𝔭)) ∧
      ¬ IsHomeomorph (PrimeSpectrum.comap (part_vii_φ (K := FractionRing A) 𝔭)) :=
  part_vii 𝔭 h𝔭 huniq

end AtiyahMcdonald69.Ex_1_21
