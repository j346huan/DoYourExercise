/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 9, Exercise 6.

**Statement.**  Let `M` be a finitely generated torsion module over a Dedekind domain `A`.
Then `M` is uniquely, up to permutation of the summands, a finite direct sum of modules
`A ⧸ p^{n}` with `p` a non-zero prime ideal of `A` and `n ≥ 1`.

Main result: `AtiyahMcdonald69.Ex_9_6.atiyah_macdonald_9_6`.

The proof develops, in order:
* `length_quot_pow` : `Module.length A (A ⧸ P ^ n) = n` for a non-zero prime `P`;
* `quotPowRingEquiv`, `quotPowLinearEquiv` : `A ⧸ P^n ≃ A_P ⧸ (P A_P)^n`;
* `exists_pow_decomposition` : a finitely generated module killed by `p^e` is a finite product
  of modules `A ⧸ p^{n_i}`;
* `exists_decomposition` : the global `A`-linear assembly;
* `length_quot_smul_top_model`, `truncSum_sub` : the multiplicity invariant
  `length (M ⧸ P^k • ⊤)` and the extraction of `#{i : p_i = P, k ≤ n_i}`;
* `exists_equiv_of_fiber_card` : equal fibre cardinalities give the permutation of summands.
-/
import Mathlib

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace AtiyahMcdonald69.Ex_9_6

open scoped Classical DirectSum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

/-! ### §1  Elementary facts about powers of a nonzero prime ideal -/

lemma isMaximal_of_prime_ne_bot (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) : P.IsMaximal :=
  Ideal.IsPrime.isMaximal ‹P.IsPrime› hP

lemma ideal_pow_ne_bot (P : Ideal A) (hP : P ≠ ⊥) (n : ℕ) : P ^ n ≠ ⊥ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact mul_ne_zero ih hP

lemma sup_span_singleton_eq_top {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) {s : A}
    (hs : s ∉ P) : P ⊔ Ideal.span {s} = ⊤ := by
  by_contra h
  haveI hmax : P.IsMaximal := isMaximal_of_prime_ne_bot P hP
  have hle : P ⊔ Ideal.span {s} ≤ P := (hmax.eq_of_le h le_sup_left).ge
  exact hs (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s)))

/-- An element outside a nonzero prime ideal is a unit modulo every power of that ideal. -/
lemma isUnit_quotient_mk_pow {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) {s : A}
    (hs : s ∉ P) (n : ℕ) : IsUnit (Ideal.Quotient.mk (P ^ n) s) := by
  haveI hmax : P.IsMaximal := isMaximal_of_prime_ne_bot P hP
  obtain ⟨y, i, hi, hy⟩ := Ideal.IsMaximal.exists_inv_pow P hs n
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ y, ?_⟩
  have h2 : (Ideal.Quotient.mk (P ^ n)) (y * s) = 1 := by
    have h0 : (Ideal.Quotient.mk (P ^ n)) (y * s) =
        (Ideal.Quotient.mk (P ^ n)) (y * s + i) := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero]
    rw [h0, hy, map_one]
  rw [mul_comm]
  exact h2

/-! ### §2  `A ⧸ P^n` versus `A_P ⧸ (P A_P)^n` -/

section Iso

variable {P : Ideal A} [P.IsPrime]

/-- The ring homomorphism `A_P →+* A ⧸ P^n` sending `a` to `a mod P^n`. -/
noncomputable def locToQuotPow (hP : P ≠ ⊥) (n : ℕ) :
    Localization.AtPrime P →+* A ⧸ P ^ n :=
  IsLocalization.lift (M := P.primeCompl) (g := Ideal.Quotient.mk (P ^ n))
    (fun y => isUnit_quotient_mk_pow hP y.2 n)

lemma locToQuotPow_algebraMap (hP : P ≠ ⊥) (n : ℕ) (a : A) :
    locToQuotPow (P := P) hP n (algebraMap A (Localization.AtPrime P) a) =
      Ideal.Quotient.mk _ a :=
  IsLocalization.lift_eq (fun y => isUnit_quotient_mk_pow hP y.2 n) a

/-- The ring homomorphism `A ⧸ P^n →+* A_P ⧸ (P A_P)^n`. -/
noncomputable def quotPowToLoc (n : ℕ) :
    (A ⧸ P ^ n) →+* (Localization.AtPrime P) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n) :=
  Ideal.Quotient.lift (P ^ n)
    ((Ideal.Quotient.mk _).comp (algebraMap A (Localization.AtPrime P)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

lemma quotPowToLoc_mk (n : ℕ) (a : A) :
    quotPowToLoc (P := P) n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime P) a) := rfl

/-- `A_P ⧸ (P A_P)^n →+* A ⧸ P^n`. -/
noncomputable def locQuotPowToQuot (hP : P ≠ ⊥) (n : ℕ) :
    ((Localization.AtPrime P) ⧸ Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n))
      →+* (A ⧸ P ^ n) :=
  Ideal.Quotient.lift _
    (locToQuotPow (P := P) hP n) (by
      intro x hx
      rw [IsLocalization.mem_map_algebraMap_iff (M := P.primeCompl)
        (S := Localization.AtPrime P)] at hx
      obtain ⟨⟨⟨a, ha⟩, ⟨m, hm⟩⟩, hEq⟩ := hx
      have h1 : locToQuotPow (P := P) hP n x *
            locToQuotPow (P := P) hP n (algebraMap A _ m) =
          locToQuotPow (P := P) hP n (algebraMap A _ a) := by
        rw [← map_mul, hEq]
      have h2 : locToQuotPow (P := P) hP n x *
            locToQuotPow (P := P) hP n (algebraMap A _ m) = 0 := by
        rw [h1, locToQuotPow_algebraMap]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
      have hunit : IsUnit (locToQuotPow (P := P) hP n (algebraMap A _ m)) := by
        rw [locToQuotPow_algebraMap]
        exact isUnit_quotient_mk_pow hP hm n
      exact (IsUnit.mul_right_eq_zero hunit).mp (by rw [mul_comm]; exact h2))

lemma locQuotPowToQuot_mk (hP : P ≠ ⊥) (n : ℕ) (x : Localization.AtPrime P) :
    locQuotPowToQuot (P := P) hP n (Ideal.Quotient.mk _ x) =
      locToQuotPow (P := P) hP n x := rfl

lemma quotPowToLoc_comp_locToQuotPow (hP : P ≠ ⊥) (n : ℕ) :
    (quotPowToLoc (P := P) n).comp (locToQuotPow (P := P) hP n) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) := by
  refine IsLocalization.ringHom_ext (M := P.primeCompl) (RingHom.ext (fun a => ?_))
  rw [RingHom.comp_apply, RingHom.comp_apply, locToQuotPow_algebraMap, quotPowToLoc_mk]
  rfl

lemma locQuotPowToQuot_comp_quotPowToLoc (hP : P ≠ ⊥) (n : ℕ) :
    (locQuotPowToQuot (P := P) hP n).comp (quotPowToLoc (P := P) n) = RingHom.id _ := by
  refine RingHom.ext (fun x => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := P ^ n) x
  rw [RingHom.comp_apply, RingHom.id_apply, quotPowToLoc_mk, locQuotPowToQuot_mk,
    locToQuotPow_algebraMap]

lemma quotPowToLoc_comp_locQuotPowToQuot (hP : P ≠ ⊥) (n : ℕ) :
    (quotPowToLoc (P := P) n).comp (locQuotPowToQuot (P := P) hP n) = RingHom.id _ := by
  refine RingHom.ext (fun x => ?_)
  obtain ⟨y, rfl⟩ :=
    Ideal.Quotient.mk_surjective
      (I := Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) x
  rw [RingHom.comp_apply, RingHom.id_apply, locQuotPowToQuot_mk]
  exact RingHom.congr_fun (quotPowToLoc_comp_locToQuotPow hP n) y

/-- The ring isomorphism `A ⧸ P^n ≃+* A_P ⧸ (P A_P)^n`. -/
noncomputable def quotPowRingEquiv (hP : P ≠ ⊥) (n : ℕ) :
    (A ⧸ P ^ n) ≃+* (Localization.AtPrime P) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n) :=
  RingEquiv.ofBijective (quotPowToLoc (P := P) n)
    ⟨fun x y hxy => by
      have h1 := RingHom.congr_fun (locQuotPowToQuot_comp_quotPowToLoc hP n)
      simp only [RingHom.comp_apply, RingHom.id_apply] at h1
      rw [← h1 x, ← h1 y, hxy],
     fun z => by
      refine ⟨locQuotPowToQuot (P := P) hP n z, ?_⟩
      have h1 := RingHom.congr_fun (quotPowToLoc_comp_locQuotPowToQuot hP n)
      simpa only [RingHom.comp_apply, RingHom.id_apply] using h1 z⟩

lemma smul_quot_pow_eq (hP : P ≠ ⊥) (n : ℕ) (a : A) (y : (Localization.AtPrime P) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) :
    a • y = Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime P) a) * y := by
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) y
  rw [show a • (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) y')
      = Ideal.Quotient.mk _ (a • y') from rfl, Algebra.smul_def, map_mul]

/-- **Key isomorphism**: `A ⧸ P^n` and `A_P ⧸ (P A_P)^n` are isomorphic `A`-modules. -/
noncomputable def quotPowLinearEquiv (hP : P ≠ ⊥) (n : ℕ) :
    (A ⧸ P ^ n) ≃ₗ[A] ((Localization.AtPrime P) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) :=
  LinearEquiv.ofBijective
    { toFun := quotPowToLoc (P := P) n
      map_add' := map_add _
      map_smul' := fun a x => by
        have hx : a • x = Ideal.Quotient.mk (P ^ n) a * x := by
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        rw [hx]
        show quotPowToLoc (P := P) n (Ideal.Quotient.mk (P ^ n) a * x) =
          a • quotPowToLoc (P := P) n x
        rw [smul_quot_pow_eq hP n a (quotPowToLoc (P := P) n x), map_mul, quotPowToLoc_mk] }
    (quotPowRingEquiv hP n).bijective

end Iso

/-! ### §3  The length of `A ⧸ P^n` -/

section Length

variable {P : Ideal A} [P.IsPrime]

/-- Ring isomorphisms preserve the length of a ring over itself. -/
lemma length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  haveI : IsScalarTower R S S :=
    ⟨fun r s x => by
      show (algebraMap R S r * s) * x = algebraMap R S r * (s * x)
      rw [mul_assoc]⟩
  have h1 : Module.length R R = Module.length R S :=
    (AlgEquiv.ofRingEquiv (f := e) (fun x => rfl)).toLinearEquiv.length_eq
  have h2 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective
  rw [h1, h2]

lemma surjective_algebraMap_quot_pow (hP : P ≠ ⊥) (n : ℕ) :
    Function.Surjective (algebraMap A ((Localization.AtPrime P) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n))) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)) z
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl y
  haveI hmax : P.IsMaximal := isMaximal_of_prime_ne_bot P hP
  obtain ⟨v, i, hi, hvi⟩ := Ideal.IsMaximal.exists_inv_pow P s.2 n
  have hkey : y = y * algebraMap A (Localization.AtPrime P) i +
      algebraMap A (Localization.AtPrime P) a * algebraMap A (Localization.AtPrime P) v := by
    conv_lhs => rw [show y = y * algebraMap A (Localization.AtPrime P) (v * (s : A) + i) from by
      rw [hvi, map_one, mul_one]]
    rw [map_add, map_mul, mul_add]
    have h2 : y * (algebraMap A (Localization.AtPrime P) v *
          algebraMap A (Localization.AtPrime P) (s : A)) =
        algebraMap A (Localization.AtPrime P) a * algebraMap A (Localization.AtPrime P) v := by
      rw [mul_comm (algebraMap A (Localization.AtPrime P) v), ← mul_assoc, hs]
    rw [h2, add_comm]
  have hzero : (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n))) y =
      (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)))
          (algebraMap A (Localization.AtPrime P) a) *
        (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)))
          (algebraMap A (Localization.AtPrime P) v) := by
    conv_lhs => rw [hkey]
    rw [map_add]
    rw [show (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n)))
        (y * algebraMap A (Localization.AtPrime P) i) = 0 from by
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hi), zero_add, map_mul]
  refine ⟨a * v, ?_⟩
  show (Ideal.Quotient.mk _) (algebraMap A (Localization.AtPrime P) (a * v)) =
    (Ideal.Quotient.mk _) y
  rw [hzero, map_mul, map_mul]

/-- `Module.length A (A ⧸ P^n) = n`. -/
theorem length_quot_pow (hP : P ≠ ⊥) (n : ℕ) : Module.length A (A ⧸ P ^ n) = n := by
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  have hmap : Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ n) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have e := quotPowRingEquiv hP n
  rw [hmap] at e
  have h1 : Module.length A (A ⧸ P ^ n) = Module.length (A ⧸ P ^ n) (A ⧸ P ^ n) :=
    Module.length_eq_of_surjective (S := A) (R := A ⧸ P ^ n) (M := A ⧸ P ^ n)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  have h2 : Module.length (A ⧸ P ^ n) (A ⧸ P ^ n) =
      Module.length ((Localization.AtPrime P) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n)
        ((Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n) :=
    length_self_eq_of_ringEquiv e
  have h3 : Module.length ((Localization.AtPrime P) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n)
        ((Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n) =
      Module.length (Localization.AtPrime P) ((Localization.AtPrime P) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n) := (
    Module.length_eq_of_surjective (S := Localization.AtPrime P)
      (R := (Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n)
      (M := (Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)).symm
  rw [h1, h2, h3]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ n

end Length

/-! ### §4  Local structure: a module killed by a power of a nonzero prime -/

section Local

variable {M : Type*} [AddCommGroup M] [Module A M]

omit [IsDedekindDomain A] in
/-- Restricting a finite product to the indices where the factors are nonzero. -/
lemma pi_subtype_of_subsingleton {ι : Type*} [Fintype ι] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] (s : ι → Prop) [DecidablePred s]
    (h : ∀ i, ¬ s i → Subsingleton (N i)) :
    Nonempty ((Π i, N i) ≃ₗ[A] (Π i : {i // s i}, N i)) := by
  refine ⟨{ toFun := fun f i => f i.1
            invFun := fun g i => if hi : s i then g ⟨i, hi⟩ else 0
            left_inv := fun f => by
              funext i
              by_cases hi : s i
              · simp [hi]
              · simp only [hi, dif_neg, not_false_iff]
                exact (h i hi).elim _ _
            right_inv := fun g => by
              funext i
              simp [i.2]
            map_add' := fun f g => rfl
            map_smul' := fun a f => rfl }⟩

section Uniformizer

variable {P : Ideal A} [P.IsPrime]

lemma span_singleton_eq_map_of_irreducible (h0 : P ≠ ⊥)
    {π : Localization.AtPrime P} (hπ : Irreducible π) :
    Ideal.span {π} = Ideal.map (algebraMap A (Localization.AtPrime P)) P := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A h0 _
  obtain ⟨-, Q, hQ, huniq⟩ :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime P)).mp ‹IsDiscreteValuationRing (Localization.AtPrime P)›
  have hprimeπ : Prime π := irreducible_iff_prime.mp hπ
  have h1 : Ideal.span {π} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hprimeπ.ne_zero
  have h1p : (Ideal.span {π}).IsPrime := by
    rw [Ideal.span_singleton_prime hprimeπ.ne_zero]
    exact hprimeπ
  have hmap : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)
  have h2 : Ideal.map (algebraMap A (Localization.AtPrime P)) P ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
      IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
    exact h0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)
  have h2p : (Ideal.map (algebraMap A (Localization.AtPrime P)) P).IsPrime := by
    rw [hmap]
    exact IsLocalRing.maximalIdeal.isMaximal _ |>.isPrime
  calc Ideal.span {π} = Q := huniq _ ⟨h1, h1p⟩
    _ = Ideal.map (algebraMap A (Localization.AtPrime P)) P := (huniq _ ⟨h2, h2p⟩).symm

end Uniformizer

/-- Structure of a finitely generated module killed by a power of a nonzero prime ideal. -/
theorem exists_pow_decomposition {p : Ideal A} [p.IsPrime] (h0 : p ≠ ⊥) {e : ℕ} (he : 0 < e)
    (N : Submodule A M) [Module.Finite A ↥N] (hN : Module.IsTorsionBySet A ↥N (p ^ e : Ideal A)) :
    ∃ (r : ℕ) (n : Fin r → ℕ), (∀ i, 0 < n i) ∧
      Nonempty (↥N ≃ₗ[A] (Π i : Fin r, A ⧸ (p ^ n i))) := by
  classical
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A h0 _
  letI hmod : Module (A ⧸ p ^ e) ↥N := hN.module
  have hsmul : ∀ (b : A) (y : ↥N), (Ideal.Quotient.mk (p ^ e) b) • y = b • y := by
    intro b y
    exact ((Module.IsTorsionBySet.semilinearMap hN).map_smul' b y).symm
  letI hmodL : Module (Localization.AtPrime p) ↥N :=
    Module.compHom ↥N (locToQuotPow h0 e)
  haveI hT : IsScalarTower A (Localization.AtPrime p) ↥N := by
    refine ⟨fun a r x => ?_⟩
    show (locToQuotPow h0 e) (a • r) • x = a • ((locToQuotPow h0 e) r • x)
    rw [Algebra.smul_def, map_mul, mul_smul, locToQuotPow_algebraMap]
    exact hsmul a _
  have hfin : Module.Finite (Localization.AtPrime p) ↥N := by
    obtain ⟨s, hs⟩ := ‹Module.Finite A ↥N›
    refine ⟨s, Submodule.eq_top_iff'.mpr (fun x => ?_)⟩
    have hx : x ∈ Submodule.span A (s : Set ↥N) := by rw [hs]; trivial
    have hle : Submodule.span A (s : Set ↥N) ≤
        (Submodule.span (Localization.AtPrime p) (s : Set ↥N)).restrictScalars A :=
      Submodule.span_le.mpr (fun y hy => Submodule.subset_span hy)
    exact hle hx
  have htor : Module.IsTorsion (Localization.AtPrime p) ↥N := by
    intro x
    obtain ⟨c, hc, hcne⟩ : ∃ c ∈ p ^ e, c ≠ 0 := by
      obtain ⟨a, ha, hane⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h0)
      exact ⟨a ^ e, Ideal.pow_mem_pow ha e, pow_ne_zero e hane⟩
    refine ⟨⟨algebraMap A (Localization.AtPrime p) c, mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
    · intro h
      exact hcne ((IsLocalization.injective (Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors) (by simpa using h))
    · show (locToQuotPow h0 e) (algebraMap A _ c) • x = 0
      rw [locToQuotPow_algebraMap]
      exact (hsmul c x).trans (hN (x := x) (a := ⟨c, hc⟩))
  obtain ⟨ι, hι, π, hπ, exx, ⟨φ⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := Localization.AtPrime p) (M := ↥N) htor
  have hsummand : ∀ i, Nonempty (((Localization.AtPrime p) ⧸ Ideal.span {π i ^ exx i}) ≃ₗ[A]
      (A ⧸ p ^ exx i)) := by
    intro i
    have hid : Ideal.span {π i ^ exx i} =
        Ideal.map (algebraMap A (Localization.AtPrime p)) (p ^ exx i) := by
      rw [← Ideal.span_singleton_pow, span_singleton_eq_map_of_irreducible h0 (hπ i),
        ← Ideal.map_pow]
    exact ⟨(Submodule.quotEquivOfEq (Ideal.span {π i ^ exx i})
      (Ideal.map (algebraMap A (Localization.AtPrime p)) (p ^ exx i)) hid).restrictScalars A |>.trans
      (quotPowLinearEquiv h0 (exx i)).symm⟩
  have stepA : Nonempty (↥N ≃ₗ[A]
      (⨁ i : ι, ((Localization.AtPrime p) ⧸ Ideal.span {π i ^ exx i}))) :=
    ⟨φ.restrictScalars A⟩
  obtain ⟨stepA⟩ := stepA
  have stepB : Nonempty (↥N ≃ₗ[A] (⨁ i : ι, A ⧸ p ^ exx i)) :=
    ⟨stepA.trans (DFinsupp.mapRange.linearEquiv (fun i => (hsummand i).some))⟩
  obtain ⟨stepB⟩ := stepB
  have stepC : Nonempty (↥N ≃ₗ[A] (Π i : ι, A ⧸ p ^ exx i)) :=
    ⟨stepB.trans (DirectSum.linearEquivFunOnFintype A ι (fun i => A ⧸ p ^ exx i))⟩
  obtain ⟨stepC⟩ := stepC
  have hpos : ∀ i, ¬ (0 < exx i) → Subsingleton (A ⧸ p ^ exx i) := by
    intro i hi
    have h0' : exx i = 0 := Nat.le_zero.mp (Nat.not_lt.mp hi)
    rw [h0', pow_zero, Ideal.one_eq_top]
    infer_instance
  obtain ⟨stepD⟩ := pi_subtype_of_subsingleton (A := A) (ι := ι)
    (N := fun i => A ⧸ p ^ exx i) (s := fun i => 0 < exx i) hpos
  let e' := Fintype.equivFin {i : ι // 0 < exx i}
  refine ⟨Fintype.card {i : ι // 0 < exx i}, fun j => exx (e'.symm j).1,
    fun j => (e'.symm j).2, ?_⟩
  exact ⟨stepC.trans (stepD.trans (LinearEquiv.piCongrLeft' A
    (fun i : {i : ι // 0 < exx i} => A ⧸ p ^ exx i.1) e'))⟩

end Local

/-! ### §5  Existence of the decomposition for a finitely generated torsion module -/

section Global

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **Existence.** A finitely generated torsion module over a Dedekind domain is a finite direct
sum of modules `A ⧸ p^n` with `p` a nonzero prime. -/
theorem exists_decomposition [Module.Finite A M] (hM : Module.IsTorsion A M) :
    ∃ (r : ℕ) (p : Fin r → Ideal A) (n : Fin r → ℕ),
      (∀ i, (p i).IsPrime) ∧ (∀ i, p i ≠ ⊥) ∧ (∀ i, 0 < n i) ∧
      Nonempty (M ≃ₗ[A] (Π i : Fin r, A ⧸ (p i) ^ (n i))) := by
  classical
  have hall := Submodule.isInternal_prime_power_torsion (R := A) (M := M) hM
  have hΨ : Nonempty (M ≃ₗ[A] (⨁ q : ↥(UniqueFactorizationMonoid.factors
      (⊤ : Submodule A M).annihilator).toFinset,
      ↥(Submodule.torsionBySet A M ((↑↑q ^ (UniqueFactorizationMonoid.factors
        (⊤ : Submodule A M).annihilator).count ↑↑q : Ideal A) : Set A)))) :=
    ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hall).symm⟩
  have hex : ∀ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
      ∃ (r : ℕ) (nn : Fin r → ℕ), (∀ i, 0 < nn i) ∧
        Nonempty (↥(Submodule.torsionBySet A M ((↑↑q ^ (UniqueFactorizationMonoid.factors
          (⊤ : Submodule A M).annihilator).count ↑↑q : Ideal A) : Set A))
          ≃ₗ[A] (Π i : Fin r, A ⧸ (((q : Ideal A) ^ (nn i) : Ideal A)))) := by
    intro q
    have hqmem : (q : Ideal A) ∈ UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator :=
      Multiset.mem_toFinset.mp q.2
    have hprime : Prime (q : Ideal A) := UniqueFactorizationMonoid.prime_of_factor _ hqmem
    haveI : (q : Ideal A).IsPrime := Ideal.isPrime_of_prime hprime
    have hcount : 0 < (UniqueFactorizationMonoid.factors
        (⊤ : Submodule A M).annihilator).count (q : Ideal A) := Multiset.count_pos.mpr hqmem
    haveI : Module.Finite A ↥(Submodule.torsionBySet A M
        (((q : Ideal A) ^ (UniqueFactorizationMonoid.factors
          (⊤ : Submodule A M).annihilator).count (q : Ideal A) : Ideal A) : Set A)) :=
      Module.Finite.of_injective (Submodule.subtype _) (Submodule.subtype_injective _)
    have htb : Module.IsTorsionBySet A ↥(Submodule.torsionBySet A M
        (((q : Ideal A) ^ (UniqueFactorizationMonoid.factors
          (⊤ : Submodule A M).annihilator).count (q : Ideal A) : Ideal A) : Set A))
        (((q : Ideal A) ^ (UniqueFactorizationMonoid.factors
          (⊤ : Submodule A M).annihilator).count (q : Ideal A) : Ideal A) : Set A) := by
      intro x a
      exact Subtype.ext ((Submodule.mem_torsionBySet_iff (R := A) (M := M)
        (s := (((q : Ideal A) ^ (UniqueFactorizationMonoid.factors
          (⊤ : Submodule A M).annihilator).count (q : Ideal A) : Ideal A) : Set A))
        (x := (x : M))).mp x.2 a)
    exact exists_pow_decomposition hprime.ne_zero hcount _ htb
  choose r nn hpos hfac using hex
  let Ind := (Σ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
      Fin (r q))
  obtain ⟨Ψ⟩ := hΨ
  have h1 : Nonempty ((⨁ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
      ↥(Submodule.torsionBySet A M ((↑↑q ^ (UniqueFactorizationMonoid.factors
        (⊤ : Submodule A M).annihilator).count ↑↑q : Ideal A) : Set A)))
      ≃ₗ[A] (⨁ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
        (Π i : Fin (r q), A ⧸ (((q : Ideal A) ^ (nn q i) : Ideal A))))) :=
    ⟨DFinsupp.mapRange.linearEquiv (fun q => (hfac q).some)⟩
  obtain ⟨h1⟩ := h1
  have h2 : Nonempty ((⨁ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
        (Π i : Fin (r q), A ⧸ (((q : Ideal A) ^ (nn q i) : Ideal A))))
      ≃ₗ[A] (⨁ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
        (⨁ i : Fin (r q), A ⧸ (((q : Ideal A) ^ (nn q i) : Ideal A))))) :=
    ⟨DFinsupp.mapRange.linearEquiv (fun q =>
      (DirectSum.linearEquivFunOnFintype A (Fin (r q)) (fun i => A ⧸ (((q : Ideal A) ^ (nn q i) : Ideal A)))).symm)⟩
  obtain ⟨h2⟩ := h2
  have h3 : Nonempty ((⨁ q : ↥(UniqueFactorizationMonoid.factors (⊤ : Submodule A M).annihilator).toFinset,
        (⨁ i : Fin (r q), A ⧸ (((q : Ideal A) ^ (nn q i) : Ideal A))))
      ≃ₗ[A] (⨁ x : Ind, A ⧸ (((x.1 : Ideal A)) ^ (nn x.1 x.2)))) :=
    ⟨(DirectSum.sigmaLcurryEquiv A).symm⟩
  obtain ⟨h3⟩ := h3
  have h4 : Nonempty ((⨁ x : Ind, A ⧸ (((x.1 : Ideal A)) ^ (nn x.1 x.2)))
      ≃ₗ[A] (Π x : Ind, A ⧸ (((x.1 : Ideal A)) ^ (nn x.1 x.2)))) :=
    ⟨DirectSum.linearEquivFunOnFintype A Ind (fun x => A ⧸ (((x.1 : Ideal A)) ^ (nn x.1 x.2)))⟩
  obtain ⟨h4⟩ := h4
  let e : Fin (Fintype.card Ind) ≃ Ind := (Fintype.equivFin Ind).symm
  refine ⟨Fintype.card Ind, fun j => ((e j).1 : Ideal A), fun j => nn (e j).1 (e j).2,
    ?_, ?_, ?_, ?_⟩
  · intro j
    exact Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor _
      (Multiset.mem_toFinset.mp (e j).1.2))
  · intro j
    exact (UniqueFactorizationMonoid.prime_of_factor _ (Multiset.mem_toFinset.mp (e j).1.2)).ne_zero
  · intro j
    exact hpos (e j).1 (e j).2
  · exact ⟨(Ψ.trans (h1.trans (h2.trans (h3.trans h4)))).trans
      (LinearEquiv.piCongrLeft A (fun x : Ind => A ⧸ (((x.1 : Ideal A)) ^ (nn x.1 x.2))) e).symm⟩

end Global

/-! ### §7  The multiplicity invariant `length (M ⧸ P^k • ⊤)` -/

section Mult

/-- `P^k • ⊤` in a finite product is the product of `P^k • ⊤`. -/
lemma smul_top_pi {ι : Type*} [Fintype ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
    [∀ i, Module A (N i)] (I : Ideal A) :
    (I • ⊤ : Submodule A (Π i, N i)) = Submodule.pi Set.univ (fun i => I • ⊤) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Submodule.mem_pi]
    intro i _
    have hmap : Submodule.map (LinearMap.proj (R := A) (φ := N) i) (I • (⊤ : Submodule A (Π j, N j)))
        ≤ I • (⊤ : Submodule A (N i)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl
        (Submodule.map_le_iff_le_comap.mpr (fun y _ => Submodule.mem_top))
    exact hmap (Submodule.mem_map_of_mem hx)
  · intro x hx
    have hsum : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single (fun i => x i)).symm
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hxi : x i ∈ I • (⊤ : Submodule A (N i)) := (Submodule.mem_pi.mp hx) i (Set.mem_univ i)
    have hmap : Submodule.map (LinearMap.single A N i) (I • (⊤ : Submodule A (N i)))
        ≤ I • (⊤ : Submodule A (Π j, N j)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl
        (Submodule.map_le_iff_le_comap.mpr (fun y _ => Submodule.mem_top))
    exact hmap (Submodule.mem_map_of_mem hxi)

end Mult

section PerFactor

/-- **Per-factor computation.** -/
theorem length_quot_smul_top {q P : Ideal A} [q.IsPrime] [P.IsPrime] (hq : q ≠ ⊥) (hP : P ≠ ⊥)
    (n k : ℕ) :
    Module.length A ((A ⧸ q ^ n) ⧸ (P ^ k • (⊤ : Submodule A (A ⧸ q ^ n)))) =
      ((if q = P then min k n else 0 : ℕ) : ℕ∞) := by
  have hS : (P ^ k • (⊤ : Submodule A (A ⧸ q ^ n))) =
      (Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k)).restrictScalars A := by
    have htop : (P ^ k : Ideal A) • (⊤ : Submodule A A) = (P ^ k : Ideal A) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hmap_top : Submodule.map (Algebra.linearMap A (A ⧸ q ^ n)) (⊤ : Submodule A A) = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
    have key : Submodule.map (Algebra.linearMap A (A ⧸ q ^ n)) (P ^ k : Ideal A)
        = (P ^ k : Ideal A) • (⊤ : Submodule A (A ⧸ q ^ n)) := by
      have h := Submodule.map_smul'' (I := (P ^ k : Ideal A)) (N := (⊤ : Submodule A A))
        (f := Algebra.linearMap A (A ⧸ q ^ n))
      rw [hmap_top, htop] at h
      exact h
    rw [← key, ← Ideal.Quotient.algebraMap_eq]
    haveI : RingHomSurjective (algebraMap A (A ⧸ q ^ n)) := ⟨Ideal.Quotient.mk_surjective⟩
    rw [Ideal.map_eq_submodule_map (algebraMap A (A ⧸ q ^ n)) (P ^ k)]
    rfl
  have hI : Module.length A ((A ⧸ q ^ n) ⧸ (Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k))) =
      Module.length A (A ⧸ (q ^ n ⊔ P ^ k)) := by
    have hX : Function.Surjective (algebraMap A ((A ⧸ q ^ n) ⧸
        Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k))) := by
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective
        (I := Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k)) z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := q ^ n) y
      exact ⟨x, rfl⟩
    have hY : Function.Surjective (algebraMap A (A ⧸ (q ^ n ⊔ P ^ k))) := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
    rw [Module.length_eq_of_surjective (S := A)
        (R := (A ⧸ q ^ n) ⧸ Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k))
        (M := (A ⧸ q ^ n) ⧸ Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k)) hX,
      length_self_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup (q ^ n) (P ^ k)),
      ← Module.length_eq_of_surjective (S := A) (R := A ⧸ (q ^ n ⊔ P ^ k))
        (M := A ⧸ (q ^ n ⊔ P ^ k)) hY]
  rw [hS, (Submodule.Quotient.restrictScalarsEquiv A
    (Ideal.map (Ideal.Quotient.mk (q ^ n)) (P ^ k))).length_eq, hI]
  by_cases h : q = P
  · rw [if_pos h, ← h]
    have hsup : q ^ n ⊔ q ^ k = q ^ min n k := by
      rcases le_total n k with hle | hle
      · rw [min_eq_left hle, sup_eq_left]; exact Ideal.pow_le_pow_right hle
      · rw [min_eq_right hle, sup_eq_right]; exact Ideal.pow_le_pow_right hle
    rw [hsup,
      show Module.length A (A ⧸ q ^ min n k) = ((min n k : ℕ) : ℕ∞) from length_quot_pow hq _,
      Nat.min_comm k n]
  · haveI hmaxq : q.IsMaximal := Ideal.IsPrime.isMaximal ‹q.IsPrime› hq
    haveI hmaxP : P.IsMaximal := Ideal.IsPrime.isMaximal ‹P.IsPrime› hP
    have h1 : q ⊔ P = ⊤ := hmaxq.coprime_of_ne hmaxP h
    have hsup : q ^ n ⊔ P ^ k = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr h1).pow (m := n) (n := k))
    rw [if_neg h, hsup]
    simp

end PerFactor

section Model

/-- The invariant for the standard model `Π i, A ⧸ p_i^{n_i}`. -/
theorem length_quot_smul_top_model {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ)
    (hp : ∀ i, (p i).IsPrime) (hp0 : ∀ i, p i ≠ ⊥)
    {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) (k : ℕ) :
    Module.length A ((Π i, A ⧸ (p i) ^ (n i)) ⧸
      (P ^ k • (⊤ : Submodule A (Π i, A ⧸ (p i) ^ (n i))))) =
      ((∑ i, if p i = P then min k (n i) else 0 : ℕ) : ℕ∞) := by
  classical
  rw [smul_top_pi, (Submodule.quotientPi (fun i => P ^ k • ⊤)).length_eq,
    Module.length_pi_of_fintype]
  have hterm : ∀ i, Module.length A ((A ⧸ (p i) ^ (n i)) ⧸
      (P ^ k • (⊤ : Submodule A (A ⧸ (p i) ^ (n i)))))
      = ((if p i = P then min k (n i) else 0 : ℕ) : ℕ∞) := by
    intro i
    haveI := hp i
    exact length_quot_smul_top (q := p i) (P := P) (hp0 i) hP (n i) k
  rw [show (∑ i, Module.length A ((A ⧸ (p i) ^ (n i)) ⧸
        (P ^ k • (⊤ : Submodule A (A ⧸ (p i) ^ (n i))))))
      = ∑ i, ((if p i = P then min k (n i) else 0 : ℕ) : ℕ∞) from
    Finset.sum_congr rfl (fun i _ => hterm i)]
  exact (Nat.cast_sum Finset.univ (fun i => if p i = P then min k (n i) else 0)).symm

end Model

/-! ### §8  Invariance of the invariant under linear equivalence -/

section Congr

lemma length_quot_smul_top_congr {M M' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') (P : Ideal A) (k : ℕ) :
    Module.length A (M ⧸ (P ^ k • (⊤ : Submodule A M))) =
      Module.length A (M' ⧸ (P ^ k • (⊤ : Submodule A M'))) := by
  have hmap : Submodule.map e.toLinearMap (P ^ k • (⊤ : Submodule A M))
      = P ^ k • (⊤ : Submodule A M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  have h₁ : (P ^ k • (⊤ : Submodule A M))
      ≤ (P ^ k • (⊤ : Submodule A M')).comap e.toLinearMap := by
    intro x hx
    rw [Submodule.mem_comap, ← hmap]
    exact Submodule.mem_map_of_mem hx
  have h₂ : (P ^ k • (⊤ : Submodule A M'))
      ≤ (P ^ k • (⊤ : Submodule A M)).comap e.symm.toLinearMap := by
    intro x hx
    rw [Submodule.mem_comap, ← hmap] at *
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    simpa using hy
  let f : M ⧸ (P ^ k • (⊤ : Submodule A M)) →ₗ[A] M' ⧸ (P ^ k • (⊤ : Submodule A M')) :=
    Submodule.mapQ _ _ e.toLinearMap h₁
  let g : M' ⧸ (P ^ k • (⊤ : Submodule A M')) →ₗ[A] M ⧸ (P ^ k • (⊤ : Submodule A M)) :=
    Submodule.mapQ _ _ e.symm.toLinearMap h₂
  have hgf : g.comp f = LinearMap.id := by
    refine LinearMap.ext (fun x => ?_)
    induction x using Submodule.Quotient.induction_on with
    | _ y => simp [f, g, Submodule.mapQ_apply]
  have hfg : f.comp g = LinearMap.id := by
    refine LinearMap.ext (fun x => ?_)
    induction x using Submodule.Quotient.induction_on with
    | _ y => simp [f, g, Submodule.mapQ_apply]
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 := LinearMap.congr_fun hgf x
    have h2 := LinearMap.congr_fun hgf y
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, hxy]
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨g x, ?_⟩
    have h1 := LinearMap.congr_fun hfg x
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    exact h1
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).length_eq

end Congr

/-! ### §9  The multiplicity arithmetic -/

section Arith

/-- The `k`-th truncated multiplicity sum. -/
noncomputable def truncSum {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ)
    (P : Ideal A) (k : ℕ) : ℕ :=
  ∑ i, if p i = P then min k (n i) else 0

lemma truncSum_def {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ)
    (P : Ideal A) (k : ℕ) :
    truncSum p n P k = ∑ i, if p i = P then min k (n i) else 0 := rfl


lemma truncSum_le {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ)
    (P : Ideal A) {k : ℕ} : truncSum p n P (k - 1) ≤ truncSum p n P k := by
  classical
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases h : p i = P
  · rw [if_pos h, if_pos h]
    exact min_le_min (Nat.sub_le k 1) le_rfl
  · rw [if_neg h, if_neg h]

lemma truncSum_sub {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ)
    (P : Ideal A) (k : ℕ) (hk1 : 1 ≤ k) :
    truncSum p n P k - truncSum p n P (k - 1)
      = (Finset.univ.filter (fun i => p i = P ∧ k ≤ n i)).card := by
  classical
  have hle := truncSum_le p n P (k := k)
  have hmain : truncSum p n P k = (Finset.univ.filter (fun i => p i = P ∧ k ≤ n i)).card
      + truncSum p n P (k - 1) := by
    rw [truncSum_def, truncSum_def, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : p i = P
    · simp only [h, if_true]
      by_cases hk : k ≤ n i
      · rw [if_pos (show True ∧ k ≤ n i from ⟨trivial, hk⟩), min_eq_left hk,
          min_eq_left (by omega)]
        omega
      · rw [if_neg (show ¬ (True ∧ k ≤ n i) by simpa using hk),
          min_eq_right (by omega), min_eq_right (by omega)]
        omega
    · have e0 : (if p i = P then min k (n i) else 0) = 0 := if_neg h
      have e1 : (if p i = P ∧ k ≤ n i then (1:ℕ) else 0) = 0 := if_neg (fun hh => h hh.1)
      have e2 : (if p i = P then min (k - 1) (n i) else 0) = 0 := if_neg h
      rw [e0, e1, e2, Nat.zero_add]
  exact (Nat.sub_eq_iff_eq_add hle).mpr hmain

end Arith

/-! ### §10  A combinatorial lemma: equal fibre cardinalities give a permutation -/

section Comb

lemma exists_equiv_of_fiber_card {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    {f : α → γ} {g : β → γ}
    (h : ∀ c : γ, (Finset.univ.filter (fun a => f a = c)).card
        = (Finset.univ.filter (fun b => g b = c)).card) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  let ee : (c : γ) → {a // f a = c} ≃ {b // g b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight ee).trans
    (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro a
  show g ((ee (f a) ⟨a, rfl⟩ : {b // g b = f a}) : β) = f a
  exact (ee (f a) ⟨a, rfl⟩).2

end Comb

/-! ### §11  Uniqueness and the main theorem -/

section Step

lemma card_eq_of_ge {ι : Type*} [Fintype ι] (p : ι → Ideal A) (n : ι → ℕ) (P : Ideal A) (m : ℕ) :
    (Finset.univ.filter (fun i => p i = P ∧ n i = m)).card
      = (Finset.univ.filter (fun i => p i = P ∧ m ≤ n i)).card
        - (Finset.univ.filter (fun i => p i = P ∧ m + 1 ≤ n i)).card := by
  classical
  have hsub : (Finset.univ.filter (fun i => p i = P ∧ m + 1 ≤ n i))
      ⊆ (Finset.univ.filter (fun i => p i = P ∧ m ≤ n i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, le_trans (Nat.le_succ m) hi.2⟩
  have heq : (Finset.univ.filter (fun i => p i = P ∧ m ≤ n i)) \
      (Finset.univ.filter (fun i => p i = P ∧ m + 1 ≤ n i))
      = Finset.univ.filter (fun i => p i = P ∧ n i = m) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h3' : ¬ (m + 1 ≤ n i) := fun hh => h3 ⟨h1, hh⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      subst h2
      exact ⟨⟨h1, le_rfl⟩, by omega⟩
  rw [← heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

end Step

section Main

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **Atiyah–Macdonald, Ch. 9, Ex. 6.**  A finitely generated torsion module over a Dedekind
domain is uniquely, up to permutation of the summands, a finite direct sum of modules
`A ⧸ p^{n}` with `p` a non-zero prime ideal and `n ≥ 1`. -/
theorem atiyah_macdonald_9_6 [Module.Finite A M] (hM : Module.IsTorsion A M) :
    ∃ (r : ℕ) (p : Fin r → Ideal A) (n : Fin r → ℕ),
      (∀ i, (p i).IsPrime) ∧ (∀ i, p i ≠ ⊥) ∧ (∀ i, 0 < n i) ∧
      Nonempty (M ≃ₗ[A] (Π i : Fin r, A ⧸ (p i) ^ (n i))) ∧
      ∀ (r' : ℕ) (p' : Fin r' → Ideal A) (n' : Fin r' → ℕ),
        (∀ i, (p' i).IsPrime) → (∀ i, p' i ≠ ⊥) → (∀ i, 0 < n' i) →
        Nonempty (M ≃ₗ[A] (Π i : Fin r', A ⧸ (p' i) ^ (n' i))) →
        ∃ e : Fin r ≃ Fin r', (∀ i, p i = p' (e i)) ∧ (∀ i, n i = n' (e i)) := by
  classical
  obtain ⟨r, p, n, hp, hp0, hn, ⟨Ψ⟩⟩ := exists_decomposition (M := M) hM
  refine ⟨r, p, n, hp, hp0, hn, ⟨Ψ⟩, ?_⟩
  intro r' p' n' hp' hp0' hn' hrep'
  obtain ⟨Ψ'⟩ := hrep'
  -- the truncated multiplicity sums agree
  have key : ∀ (P : Ideal A), P.IsPrime → P ≠ ⊥ → ∀ k : ℕ, 1 ≤ k →
      truncSum p n P k = truncSum p' n' P k := by
    intro P hP1 hP0 k hk
    have h1 : Module.length A (M ⧸ (P ^ k • (⊤ : Submodule A M)))
        = ((truncSum p n P k : ℕ) : ℕ∞) := by
      rw [length_quot_smul_top_congr Ψ P k]
      exact length_quot_smul_top_model p n hp hp0 hP0 k
    have h2 : Module.length A (M ⧸ (P ^ k • (⊤ : Submodule A M)))
        = ((truncSum p' n' P k : ℕ) : ℕ∞) := by
      rw [length_quot_smul_top_congr Ψ' P k]
      exact length_quot_smul_top_model p' n' hp' hp0' hP0 k
    have := h1.symm.trans h2
    exact_mod_cast this
  -- fibre cardinalities agree
  have hfib : ∀ c : Ideal A × ℕ,
      (Finset.univ.filter (fun i => (p i, n i) = c)).card
        = (Finset.univ.filter (fun i => (p' i, n' i) = c)).card := by
    rintro ⟨P, m⟩
    by_cases hmain : P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ m
    · obtain ⟨hP1, hP0, hm⟩ := hmain
      have e1 := card_eq_of_ge (A := A) p n P m
      have e2 := card_eq_of_ge (A := A) p' n' P m
      have c1 : (Finset.univ.filter (fun i => p i = P ∧ m ≤ n i)).card
          = truncSum p n P m - truncSum p n P (m - 1) := (truncSum_sub p n P m hm).symm
      have c2 : (Finset.univ.filter (fun i => p i = P ∧ m + 1 ≤ n i)).card
          = truncSum p n P (m + 1) - truncSum p n P m := (truncSum_sub p n P (m + 1) (by omega)).symm
      have d1 : (Finset.univ.filter (fun i => p' i = P ∧ m ≤ n' i)).card
          = truncSum p' n' P m - truncSum p' n' P (m - 1) := (truncSum_sub p' n' P m hm).symm
      have d2 : (Finset.univ.filter (fun i => p' i = P ∧ m + 1 ≤ n' i)).card
          = truncSum p' n' P (m + 1) - truncSum p' n' P m := (truncSum_sub p' n' P (m + 1) (by omega)).symm
      have k1 := key P hP1 hP0 m hm
      have k2 := key P hP1 hP0 (m + 1) (by omega)
      have hconv : (Finset.univ.filter (fun i => (p i, n i) = (P, m)))
          = Finset.univ.filter (fun i => p i = P ∧ n i = m) := by
        congr 1
        ext i
        simp [Prod.mk.injEq]
      have hconv' : (Finset.univ.filter (fun i => (p' i, n' i) = (P, m)))
          = Finset.univ.filter (fun i => p' i = P ∧ n' i = m) := by
        congr 1
        ext i
        simp [Prod.mk.injEq]
      have step1 : (Finset.univ.filter (fun i => p i = P ∧ n i = m)).card
          = (truncSum p n P m - truncSum p n P (m - 1))
            - (truncSum p n P (m + 1) - truncSum p n P m) := by
        rw [e1, c1, c2]
      have step1' : (Finset.univ.filter (fun i => p' i = P ∧ n' i = m)).card
          = (truncSum p' n' P m - truncSum p' n' P (m - 1))
            - (truncSum p' n' P (m + 1) - truncSum p' n' P m) := by
        rw [e2, d1, d2]
      have k0 : truncSum p n P (m - 1) = truncSum p' n' P (m - 1) := by
        rcases Nat.eq_zero_or_pos (m - 1) with h0 | h0
        · rw [h0, truncSum_def, truncSum_def]
          simp
        · exact key P hP1 hP0 (m - 1) h0
      rw [hconv, hconv', step1, step1', k0, k1, k2]
    · -- both fibres are empty
      have hone : Finset.univ.filter (fun i => (p i, n i) = (P, m)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun i _ hi => ?_)
        have h1 : p i = P := congrArg Prod.fst hi
        have h2 : n i = m := congrArg Prod.snd hi
        rcases not_and_or.mp hmain with h | h
        · exact h (h1 ▸ hp i)
        rcases not_and_or.mp h with h | h
        · exact h (h1 ▸ hp0 i)
        · have hnpos := hn i
          omega
      have htwo : Finset.univ.filter (fun i => (p' i, n' i) = (P, m)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun i _ hi => ?_)
        have h1 : p' i = P := congrArg Prod.fst hi
        have h2 : n' i = m := congrArg Prod.snd hi
        rcases not_and_or.mp hmain with h | h
        · exact h (h1 ▸ hp' i)
        rcases not_and_or.mp h with h | h
        · exact h (h1 ▸ hp0' i)
        · have hnpos := hn' i
          omega
      rw [hone, htwo]
      simp

  obtain ⟨e, he⟩ := exists_equiv_of_fiber_card (f := fun i => (p i, n i))
    (g := fun i => (p' i, n' i)) hfib
  exact ⟨e, fun i => (congrArg Prod.fst (he i)).symm, fun i => (congrArg Prod.snd (he i)).symm⟩

end Main


#print axioms AtiyahMcdonald69.Ex_9_6.atiyah_macdonald_9_6
#print axioms AtiyahMcdonald69.Ex_9_6.exists_decomposition
#print axioms AtiyahMcdonald69.Ex_9_6.exists_pow_decomposition
#print axioms AtiyahMcdonald69.Ex_9_6.length_quot_pow
#print axioms AtiyahMcdonald69.Ex_9_6.length_quot_smul_top_model
#print axioms AtiyahMcdonald69.Ex_9_6.truncSum_sub
#print axioms AtiyahMcdonald69.Ex_9_6.exists_equiv_of_fiber_card

end AtiyahMcdonald69.Ex_9_6
