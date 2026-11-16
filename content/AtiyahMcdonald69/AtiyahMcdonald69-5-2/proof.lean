import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 5.2

**Statement (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 5, Ex. 2).**
Let `A` be a subring of a ring `B` such that `B` is integral over `A`, and let
`f : A → Ω` be a homomorphism of `A` into an algebraically closed field `Ω`.
Show that `f` can be extended to a homomorphism of `B` into `Ω`.

The natural solution runs: put `𝔭 = ker f`, use lying over (5.10) to choose a prime
`𝔮 ⊆ B` with `𝔮 ∩ A = 𝔭`; then `B/𝔮` is integral over the domain `A/𝔭`, so its
fraction field is algebraic over the fraction field of `A/𝔭`; the embedding
`A/𝔭 → Ω` extends to the fraction field of `A/𝔭` and then to this algebraic extension,
since `Ω` is algebraically closed; composing with `B → B/𝔮` gives the required map.

Formalisation notes.
* `solution` is the book statement: `A → B` is an injective ring homomorphism (the
  Mathlib rendering of "`A` is a subring of `B`") and `B` is integral over `A`.
* `solution_subring` states the same result for a literal `Subring A` of `B`.
* `exists_ringHom_comp_eq_of_isIntegral` proves a strictly stronger statement, valid for an
  arbitrary integral homomorphism `A → B` whose kernel is killed by `f`.  The kernel
  hypothesis is not cosmetic: `not_exists_extension_int_quotient_two` and
  `generalization_false` show that the natural generalisation to an arbitrary integral
  homomorphism is *false*.  So the injectivity of `A → B` (i.e. that `A` really is a
  subring of `B`) is a load-bearing hypothesis of the exercise, and an instance of the
  phenomenon "a literal generalisation of a book statement is false, so the formalisation
  keeps the book's hypothesis and records a counterexample to the generalisation".
-/

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

namespace AtiyahMcdonald69.Ex_5_2

/-! ### The general form: lying over plus the extension lemma -/

/-- **Exercise 5.2, general form.**  Let `A → B` be an integral ring homomorphism and let
`f : A → Ω` be a ring homomorphism into an algebraically closed field whose kernel contains
`ker (A → B)`.  Then `f` extends to a ring homomorphism `B → Ω`.

Proof (following the natural solution).  Put `𝔭 = ker f`; it is prime because `Ω` is a
domain.  By lying over, `Mathlib`'s `Ideal.exists_ideal_over_prime_of_isIntegral` (which
only needs `ker (A → B) ≤ 𝔭`), there is a prime `𝔮 ⊆ B` with `𝔮 ∩ A = 𝔭`.  The induced
map `k : A/𝔭 →+* Ω` is injective, so `Ω` is a torsion-free `A/𝔭`-algebra.  Also
`A/𝔭 → B/𝔮` is injective and `B/𝔮` is integral, hence algebraic, over `A/𝔭`.  Since `Ω`
is algebraically closed, `k` extends along the algebraic extension of fraction fields
(`IsAlgClosed.lift`); composing with `B → B/𝔮` gives the desired extension. -/
theorem exists_ringHom_comp_eq_of_isIntegral
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Field Ω] [IsAlgClosed Ω]
    (hint : Algebra.IsIntegral A B) (f : A →+* Ω)
    (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker f) :
    ∃ g : B →+* Ω, g.comp (algebraMap A B) = f := by
  classical
  -- `ker f` is a prime ideal, as `Ω` is a domain.
  haveI hpkerprime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  -- Lying over (Atiyah–Macdonald (5.10)).
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) (RingHom.ker f) ⊥ hker
  haveI hQ : Q.IsPrime := hQprime
  -- Work with `p := Q ∩ A`, which equals `ker f`.
  set p : Ideal A := Q.comap (algebraMap A B) with hpdef
  -- From now on `hQcomap : p = RingHom.ker f`.
  haveI hpprime : p.IsPrime := by rw [hQcomap]; exact hpkerprime
  -- The map `k : A ⧸ p →+* Ω` induced by `f`; it is injective.
  have Hk : ∀ a : A, a ∈ p → f a = 0 := by
    intro a ha
    rw [← RingHom.mem_ker]
    exact hQcomap ▸ ha
  let k : (A ⧸ p) →+* Ω := Ideal.Quotient.lift p f Hk
  have hk_mk : ∀ a : A, k (Ideal.Quotient.mk p a) = f a := fun a => rfl
  have hk_inj : Function.Injective k :=
    RingHom.lift_injective_of_ker_le_ideal p Hk (by rw [hQcomap])
  -- View `Ω` as an `A ⧸ p`-algebra through `k`.
  letI : Algebra (A ⧸ p) Ω := k.toAlgebra
  have hk_alg : (algebraMap (A ⧸ p) Ω) = k := rfl
  haveI : Module.IsTorsionFree (A ⧸ p) Ω :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (by rw [hk_alg]; exact hk_inj)
  -- `A ⧸ p → B ⧸ Q` is injective, so `B ⧸ Q` is torsion free over `A ⧸ p`.
  have hquot_inj : Function.Injective (algebraMap (A ⧸ p) (B ⧸ Q)) :=
    Ideal.algebraMap_quotient_injective (R := A) (I := Q) (A := B)
  haveI : Module.IsTorsionFree (A ⧸ p) (B ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hquot_inj
  -- `B ⧸ Q` is integral over the domain `A ⧸ p`, hence algebraic.
  haveI : Algebra.IsIntegral (A ⧸ p) (B ⧸ Q) := by
    haveI : Q.LiesOver p := ⟨hpdef⟩
    exact Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (B := B) Q p
  -- `Ω` is algebraically closed, so `k` extends along the algebraic extension
  -- of fraction fields of `A ⧸ p → B ⧸ Q`.
  let φ : (B ⧸ Q) →ₐ[A ⧸ p] Ω := IsAlgClosed.lift
  refine ⟨(φ : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h1 : Ideal.Quotient.mk Q (algebraMap A B a)
      = algebraMap (A ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p a) := by
    simp
  change φ (Ideal.Quotient.mk Q (algebraMap A B a)) = f a
  rw [h1, AlgHom.commutes, hk_alg]
  exact hk_mk a

/-! ### The statement of the exercise -/

/-- **Atiyah–Macdonald, Exercise 5.2.**  Let `A` be a subring of a ring `B` (`A → B`
injective) such that `B` is integral over `A`, and let `f : A → Ω` be a ring homomorphism
into an algebraically closed field `Ω`.  Then `f` extends to a ring homomorphism `B → Ω`. -/
theorem solution
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Field Ω] [IsAlgClosed Ω]
    (hAB : Function.Injective (algebraMap A B))
    (hint : Algebra.IsIntegral A B) (f : A →+* Ω) :
    ∃ g : B →+* Ω, g.comp (algebraMap A B) = f := by
  refine exists_ringHom_comp_eq_of_isIntegral hint f ?_
  -- injectivity of `A → B` means `ker (A → B) = 0`, so the kernel hypothesis holds.
  have hbot : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp hAB
  rw [hbot]
  exact bot_le

/-- **Atiyah–Macdonald, Exercise 5.2, literal subring form.**  Let `A` be a subring of a
ring `B` such that `B` is integral over `A`, and let `f : A → Ω` be a homomorphism into an
algebraically closed field.  Then `f` extends to a homomorphism `B → Ω`. -/
theorem solution_subring
    {B Ω : Type*} [CommRing B] (A : Subring B) [Field Ω] [IsAlgClosed Ω]
    (hint : Algebra.IsIntegral A B) (f : A →+* Ω) :
    ∃ g : B →+* Ω, ∀ a : A, g (a : B) = f a := by
  obtain ⟨g, hg⟩ := solution (A := A) (B := B) (Ω := Ω) (by
    intro x y h
    exact Subtype.ext h) hint f
  exact ⟨g, fun a => DFunLike.congr_fun hg a⟩

/-! ### Auditing the hypotheses: the injectivity of `A → B` cannot be dropped

The exercise states the result for a subring `A ⊆ B`.  The natural solution uses lying over
in the form `∃ 𝔮, 𝔮 ∩ A = 𝔭`, which is valid without injectivity only under the extra
hypothesis `ker (A → B) ≤ ker f`.  The following pair of facts shows that this hypothesis
(hence the hypothesis `A ⊆ B`) is essential: `ℤ ⧸ (2)` is integral over `ℤ`, but there is
no extension of the canonical map `ℤ → ℂ` to `ℤ ⧸ (2) → ℂ`. -/

/-- `ℤ ⧸ (2)` is integral over `ℤ` (it is even module finite). -/
theorem isIntegral_int_quotient_two :
    Algebra.IsIntegral ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) := inferInstance

/-- There is no ring homomorphism `ℤ ⧸ (2) →+* ℂ` extending the canonical map `ℤ → ℂ`:
`2` is killed by `ℤ → ℤ ⧸ (2)` but not by `ℤ → ℂ`. -/
theorem not_exists_extension_int_quotient_two :
    ¬ ∃ g : (ℤ ⧸ Ideal.span {(2 : ℤ)}) →+* ℂ,
      g.comp (algebraMap ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)})) = Int.castRingHom ℂ := by
  rintro ⟨g, hg⟩
  have hzero : algebraMap ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) 2 = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self 2
  have h := DFunLike.congr_fun hg (2 : ℤ)
  simp only [RingHom.comp_apply] at h
  rw [hzero, map_zero] at h
  norm_num at h

/-- The naive generalisation of the exercise to an arbitrary integral homomorphism
`A → B` (with no hypothesis on `ker (A → B)`) is **false**: the identity of `ℤ` and the
quotient map `ℤ → ℤ ⧸ (2)` are both integral, but the canonical map `ℤ → ℂ` does not
extend to `ℤ ⧸ (2) → ℂ`.  Thus the hypothesis that `A` is a subring of `B` is essential
to the exercise as stated. -/
theorem generalization_false :
    ¬ (∀ (A B Ω : Type) [CommRing A] [CommRing B] [Algebra A B] [Field Ω] [IsAlgClosed Ω],
        Algebra.IsIntegral A B → ∀ f : A →+* Ω, ∃ g : B →+* Ω, g.comp (algebraMap A B) = f) := by
  intro h
  obtain ⟨g, hg⟩ :=
    h ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) ℂ isIntegral_int_quotient_two (Int.castRingHom ℂ)
  exact not_exists_extension_int_quotient_two ⟨g, hg⟩

/-- Non-vacuity: the book statement applies to the inclusion `ℝ ⊆ ℂ`. -/
example (f : ℝ →+* ℂ) : ∃ g : ℂ →+* ℂ, g.comp (algebraMap ℝ ℂ) = f :=
  solution Complex.ofReal_injective inferInstance f

end AtiyahMcdonald69.Ex_5_2

#print axioms AtiyahMcdonald69.Ex_5_2.solution
#print axioms AtiyahMcdonald69.Ex_5_2.solution_subring
#print axioms AtiyahMcdonald69.Ex_5_2.exists_ringHom_comp_eq_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_5_2.not_exists_extension_int_quotient_two
#print axioms AtiyahMcdonald69.Ex_5_2.generalization_false
