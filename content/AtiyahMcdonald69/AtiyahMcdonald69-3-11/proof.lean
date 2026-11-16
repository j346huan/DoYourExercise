import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 3, Exercise 3.11

Let `A` be a ring and `𝔑` its nilradical.  The exercise asks to prove that the following
are equivalent:

1. `A / 𝔑` is absolutely flat (i.e. every module over it is flat, Chapter 2, Exercise 27);
2. every prime ideal of `A` is maximal;
3. `Spec A` is a `T1`-space (every singleton is closed);
4. `Spec A` is Hausdorff,

and that, when these hold, `Spec A` is compact and totally disconnected.

The formal statements use Mathlib's conventions: `AbsolutelyFlat R` is defined below as "every
`R`-module is flat" (Chapter 2, Exercise 27 of the book); conditions (iii) and (iv) are Mathlib's
`T1Space` and `T2Space` on `PrimeSpectrum A`; `CompactSpace` is quasi-compactness (which, together
with the Hausdorff condition (iv), is the book's "compact"); and `TotallyDisconnectedSpace` says
that every preconnected subset is a subsingleton, i.e. the only connected subsets are single
points.

A sanity check that the hypotheses are consistent is given at the end: a field satisfies all four
conditions.
-/

namespace AtiyahMcdonald69.Ex_3_11

set_option linter.style.haveILetI false

open PrimeSpectrum

universe u

/-- A ring `R` is *absolutely flat* if every module over it is flat
(Atiyah–Macdonald, Chapter 2, Exercise 27). -/
def AbsolutelyFlat (R : Type u) [CommRing R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Flat R M

section Basic

variable {R : Type u} [CommRing R]

/-! ## Absolutely flat rings have idempotent principal ideals -/

/-- In an absolutely flat ring every principal ideal is idempotent: for each `x` there is `y`
with `x = x ^ 2 * y`. -/
theorem exists_eq_self_mul_self_mul_of_absolutelyFlat (hR : AbsolutelyFlat R) (x : R) :
    ∃ y : R, x = x ^ 2 * y := by
  classical
  set I : Ideal R := Ideal.span {x} with hI
  haveI hflat : Module.Flat R (R ⧸ I) := hR _
  have hinj : Function.Injective (LinearMap.rTensor (R ⧸ I) (Submodule.subtype I)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.subtype_injective I)
  have hx : x ∈ I := hI ▸ Ideal.mem_span_singleton_self x
  have hx1 : x • (1 : R ⧸ I) = 0 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    show Ideal.Quotient.mk I x * 1 = 0
    rw [mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hzero : (⟨x, hx⟩ : I) ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
    refine hinj ?_
    rw [LinearMap.rTensor_tmul, map_zero]
    change (x : R) ⊗ₜ[R] (1 : R ⧸ I) = 0
    rw [show (x : R) ⊗ₜ[R] (1 : R ⧸ I) = (x • (1 : R)) ⊗ₜ[R] (1 : R ⧸ I) from by
      rw [smul_eq_mul, mul_one]]
    rw [TensorProduct.smul_tmul, hx1]
    simp
  have hq : (Submodule.Quotient.mk (⟨x, hx⟩ : I) : I ⧸ (I • ⊤ : Submodule R I)) = 0 := by
    have h2 : (TensorProduct.tensorQuotEquivQuotSMul (M := I) I).symm
        (Submodule.Quotient.mk (⟨x, hx⟩ : I)) = 0 := by
      rw [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
      exact hzero
    calc (Submodule.Quotient.mk (⟨x, hx⟩ : I) : I ⧸ (I • ⊤ : Submodule R I))
        = (TensorProduct.tensorQuotEquivQuotSMul (M := I) I)
            ((TensorProduct.tensorQuotEquivQuotSMul (M := I) I).symm
              (Submodule.Quotient.mk (⟨x, hx⟩ : I))) := by
          rw [LinearEquiv.apply_symm_apply]
      _ = 0 := by rw [h2, map_zero]
  have hmem : x ∈ I * I := by
    have h1 : (⟨x, hx⟩ : I) ∈ (I • ⊤ : Submodule R I) := (Submodule.Quotient.mk_eq_zero _).mp hq
    rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul] at h1
    exact h1
  have hx2 : x ∈ I ^ 2 := by rw [pow_two]; exact hmem
  rw [hI, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hx2
  obtain ⟨y, hy⟩ := hx2
  exact ⟨y, by rw [pow_two]; exact hy⟩

/-- A ring in which every element satisfies `x = x ^ 2 * y` has only maximal prime ideals. -/
theorem isMaximal_of_forall_exists_eq_mul_self_mul
    (h : ∀ x : R, ∃ y : R, x = x ^ 2 * y) : ∀ p : Ideal R, p.IsPrime → p.IsMaximal := by
  intro p hp
  refine (Ideal.isMaximal_iff (α := R)).mpr ⟨?_, ?_⟩
  · intro h1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)
  · intro J x hJ hx hxJ
    obtain ⟨y, hy⟩ := h x
    have hzero : x * (1 - x * y) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hy, sub_self]
    have hmem : (1 - x * y) ∈ p := by
      rcases hp.mem_or_mem (show x * (1 - x * y) ∈ p by rw [hzero]; exact p.zero_mem) with h' | h'
      · exact absurd h' hx
      · exact h'
    have hone : (1 : R) = x * y + (1 - x * y) := by ring
    rw [hone]
    exact J.add_mem (Ideal.mul_mem_right y J hxJ) (hJ hmem)

/-! ## The key nilpotency lemma

If every prime ideal of `R` is maximal, then for a prime ideal `p` and `x ∈ p`, some element
`s ∉ p` makes `s * x` nilpotent.  This is the crucial step in passing from condition (ii) to
conditions (iii) and (iv), and also in showing that `R` is a von Neumann regular ring.
-/

/-- **Key lemma.** -/
theorem exists_notMem_mul_isNilpotent (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal)
    {p : Ideal R} (hp : p.IsPrime) {x : R} (hx : x ∈ p) :
    ∃ s : R, s ∉ p ∧ IsNilpotent (s * x) := by
  classical
  -- Every prime is a minimal prime.
  have hmin : p ∈ minimalPrimes R := by
    refine (IsMinimalPrime.iff_minimal p).mpr ⟨hp, ?_⟩
    intro q hq hqp
    rw [(hmax q hq).eq_of_le hp.ne_top hqp]
  -- The localization at `p` has a single prime ideal.
  haveI hiloc : IsLocalization.AtPrime (Localization.AtPrime p) p := inferInstance
  have hloc : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  haveI := hloc
  have hsub : Subsingleton (PrimeSpectrum (Localization.AtPrime p)) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hmin _
  haveI := hsub
  have hPprime : (p.map (algebraMap R (Localization.AtPrime p))).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime p (p := p) le_rfl
  -- hence the nilradical is `p` extended
  have hnil : nilradical (Localization.AtPrime p) = p.map (algebraMap R (Localization.AtPrime p)) := by
    rw [nilradical_eq_sInf]
    refine le_antisymm (sInf_le hPprime) (le_sInf ?_)
    intro J hJ
    have hEq : J = p.map (algebraMap R (Localization.AtPrime p)) := by
      have h := Subsingleton.elim (⟨J, hJ⟩ : PrimeSpectrum (Localization.AtPrime p))
        ⟨_, hPprime⟩
      exact congr_arg PrimeSpectrum.asIdeal h
    rw [hEq]
  have hmem : algebraMap R (Localization.AtPrime p) x ∈ nilradical (Localization.AtPrime p) := by
    rw [hnil]
    exact Ideal.mem_map_of_mem _ hx
  rw [mem_nilradical] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hzero : algebraMap R (Localization.AtPrime p) (x ^ n)
      = algebraMap R (Localization.AtPrime p) 0 := by
    rw [map_pow, hn, map_zero]
  rw [IsLocalization.eq_iff_exists p.primeCompl (Localization.AtPrime p)] at hzero
  obtain ⟨c, hc⟩ := hzero
  rw [mul_zero] at hc
  have hcn : (c : R) ≠ 0 := by
    rintro h0
    exact c.2 (h0 ▸ p.zero_mem)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hc
    exact c.2 (by rw [hc]; exact p.zero_mem)
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  refine ⟨(c : R), c.2, k + 1, ?_⟩
  have hc' : (c : R) * x ^ (k + 1) = 0 := hc
  calc ((c : R) * x) ^ (k + 1) = (c : R) ^ (k + 1) * x ^ (k + 1) := mul_pow (c : R) x (k + 1)
    _ = ((c : R) ^ k * (c : R)) * x ^ (k + 1) := by rw [pow_succ]
    _ = (c : R) ^ k * ((c : R) * x ^ (k + 1)) := by ring
    _ = 0 := by rw [hc', mul_zero]

/-! ## From the key lemma to von Neumann regularity

In a *reduced* ring all of whose prime ideals are maximal, the key lemma gives
`(x) + Ann(x) = ⊤` for every `x`, whence `x = x ^ 2 * y`.  Such rings are therefore von Neumann
regular, and in a von Neumann regular ring every finitely generated ideal is generated by an
idempotent, so every ideal inclusion splits and every module is flat.
-/

/-- In a reduced ring, the key lemma yields `s * x = 0` (not merely nilpotent). -/
theorem exists_notMem_mul_eq_zero_of_isReduced [IsReduced R]
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal)
    {p : Ideal R} (hp : p.IsPrime) {x : R} (hx : x ∈ p) :
    ∃ s : R, s ∉ p ∧ s * x = 0 := by
  obtain ⟨s, hs, n, hn⟩ := exists_notMem_mul_isNilpotent hmax hp hx
  exact ⟨s, hs, IsReduced.eq_zero _ ⟨n, hn⟩⟩

/-- The annihilator of `x` as an ideal. -/
def elemAnn (x : R) : Ideal R := LinearMap.ker (LinearMap.lsmul R R x)

theorem mem_elemAnn {x y : R} : y ∈ elemAnn x ↔ x * y = 0 := by
  rw [elemAnn, LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul]

/-- In a reduced ring all of whose primes are maximal, `(x) + Ann(x) = ⊤`. -/
theorem span_singleton_sup_elemAnn_eq_top [IsReduced R]
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) (x : R) :
    Ideal.span {x} ⊔ elemAnn x = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hx : x ∈ m := hle ((le_sup_left : Ideal.span {x} ≤ Ideal.span {x} ⊔ elemAnn x)
    (Ideal.mem_span_singleton_self x))
  obtain ⟨s, hs, hsx⟩ := exists_notMem_mul_eq_zero_of_isReduced hmax hm.isPrime hx
  refine hs (hle ?_)
  refine Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, s, ?_, by simp⟩
  rw [mem_elemAnn, mul_comm]
  exact hsx

/-- A reduced ring all of whose primes are maximal is von Neumann regular. -/
theorem exists_eq_mul_self_mul_of_isReduced_primes_maximal [IsReduced R]
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) (x : R) :
    ∃ y : R, x = x ^ 2 * y := by
  have htop := span_singleton_sup_elemAnn_eq_top hmax x
  have h1 : (1 : R) ∈ Ideal.span {x} ⊔ elemAnn x := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  rw [Ideal.mem_span_singleton] at ha
  obtain ⟨y, rfl⟩ := ha
  rw [mem_elemAnn] at hb
  have hone : (1 : R) = x * y + b := hab.symm
  refine ⟨y, ?_⟩
  calc x = x * 1 := (mul_one x).symm
    _ = x * (x * y + b) := by rw [hone]
    _ = x ^ 2 * y + x * b := by ring
    _ = x ^ 2 * y := by rw [hb, add_zero]

/-! ### Idempotents and finitely generated ideals -/

theorem isIdempotentElem_of_eq_sq_mul (a b : R) (h : a = a ^ 2 * b) :
    IsIdempotentElem (a * b) := by
  show (a * b) * (a * b) = a * b
  calc (a * b) * (a * b) = a ^ 2 * b ^ 2 := by ring
    _ = (a ^ 2 * b) * b := by ring
    _ = a * b := by rw [← h]

theorem span_singleton_eq_span_singleton_mul (a b : R) (h : a = a ^ 2 * b) :
    Ideal.span {a} = Ideal.span {a * b} := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    refine ⟨a, ?_⟩
    calc a = a ^ 2 * b := h
      _ = (a * b) * a := by ring
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨b, rfl⟩

/-- The sum of two principal ideals generated by idempotents is again principal, generated by an
idempotent. -/
theorem span_singleton_sup_span_singleton {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    Ideal.span {e} ⊔ Ideal.span {f} = Ideal.span {e + f - e * f} := by
  have hg : IsIdempotentElem (e + f - e * f) := he.add_sub_mul hf
  have hge : (e + f - e * f) * e = e := by
    have h : (e + f - e * f) * e = (e * e) * (1 - f) + e * f := by ring
    rw [h, he.eq]
    ring
  have hgf : (e + f - e * f) * f = f := by
    have h : (e + f - e * f) * f = (f * f) * (1 - e) + f * e := by ring
    rw [h, hf.eq]
    ring
  refine le_antisymm ?_ ?_
  · rw [sup_le_iff]
    constructor
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨e, hge.symm⟩
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨f, hgf.symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have h1 : e ∈ Ideal.span {e} ⊔ Ideal.span {f} :=
      (le_sup_left : Ideal.span {e} ≤ Ideal.span {e} ⊔ Ideal.span {f})
        (Ideal.mem_span_singleton_self e)
    have h2 : f ∈ Ideal.span {e} ⊔ Ideal.span {f} :=
      (le_sup_right : Ideal.span {f} ≤ Ideal.span {e} ⊔ Ideal.span {f})
        (Ideal.mem_span_singleton_self f)
    exact Submodule.sub_mem _ (Submodule.add_mem _ h1 h2) (Ideal.mul_mem_right f _ h1)

/-- In a ring where every principal ideal is idempotent, every finitely generated ideal is
generated by an idempotent. -/
theorem exists_isIdempotentElem_span_of_fg (h : ∀ x : R, ∃ y : R, x = x ^ 2 * y)
    {I : Ideal R} (hI : I.FG) : ∃ e : R, IsIdempotentElem e ∧ I = Ideal.span {e} := by
  classical
  obtain ⟨S, hS⟩ := hI
  have key : ∀ S : Finset R, ∃ e : R, IsIdempotentElem e ∧
      Ideal.span ((S : Set R)) = Ideal.span {e} := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp [IsIdempotentElem], by simp⟩
    | insert a S ha ih =>
      obtain ⟨e, he, hSe⟩ := ih
      obtain ⟨b, hb⟩ := h a
      have hab : IsIdempotentElem (a * b) := isIdempotentElem_of_eq_sq_mul a b hb
      have hsum : IsIdempotentElem (a * b + e - a * b * e) := hab.add_sub_mul he
      refine ⟨a * b + e - a * b * e, hsum, ?_⟩
      rw [Finset.coe_insert, Ideal.span_insert, hSe,
        span_singleton_eq_span_singleton_mul a b hb, span_singleton_sup_span_singleton hab he]
  obtain ⟨e, he, hSe⟩ := key S
  exact ⟨e, he, by rw [← hS, hSe]⟩

/-- Multiplying an element of the principal ideal generated by an idempotent `e` by `e` does
nothing. -/
theorem mul_idempotent_of_mem_span {e : R} (he : IsIdempotentElem e) {y : R}
    (hy : y ∈ Ideal.span {e}) : y * e = y := by
  rw [Ideal.mem_span_singleton] at hy
  obtain ⟨c, rfl⟩ := hy
  calc (e * c) * e = (e * e) * c := by ring
    _ = e * c := by rw [he.eq]

/-- A von Neumann regular ring is absolutely flat: every module is flat. -/
theorem absolutelyFlat_of_forall_exists_eq_mul_self_mul
    (h : ∀ x : R, ∃ y : R, x = x ^ 2 * y) : AbsolutelyFlat R := by
  intro M _ _
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_span_of_fg h hI
  set J : Ideal R := Ideal.span {e} with hJ
  -- the retraction `R → J`, `r ↦ r * e`
  set ret : R →ₗ[R] J :=
    { toFun := fun r => ⟨r * e, by
        rw [hJ, Ideal.mem_span_singleton]
        exact ⟨r, by ring⟩⟩
      map_add' := fun a b => by ext; simp [add_mul]
      map_smul' := fun a b => by ext; simp [mul_assoc] } with hret_def
  have hret : ret ∘ₗ (Submodule.subtype J) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show (x : R) * e = (x : R)
    exact mul_idempotent_of_mem_span he x.2
  have hcomp : LinearMap.rTensor M ret ∘ₗ LinearMap.rTensor M (Submodule.subtype J)
      = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hret, LinearMap.rTensor_id]
  intro x y hxy
  have h := congrArg (fun z => (LinearMap.rTensor M ret) z) hxy
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomp, LinearMap.id_apply,
    LinearMap.id_apply] at h
  exact h

/-! ## Primes and the prime spectrum -/

/-- Every prime ideal contains the nilradical. -/
theorem nilradical_le_of_isPrime {p : Ideal R} (hp : p.IsPrime) : nilradical R ≤ p := by
  intro x hx
  rw [mem_nilradical] at hx
  obtain ⟨n, hn⟩ := hx
  exact hp.mem_of_pow_mem n (by rw [hn]; exact p.zero_mem)

/-- Condition (ii) is equivalent to condition (iii): `Spec A` is a `T1`-space. -/
theorem primes_maximal_iff_t1Space :
    (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ↔ T1Space (PrimeSpectrum R) := by
  constructor
  · intro h
    exact T1Space.mk fun x =>
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr (h x.asIdeal x.2)
  · intro h p hp
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨p, hp⟩).mp (T1Space.t1 _)

/-- Condition (ii) implies condition (iv): `Spec A` is Hausdorff. -/
theorem t2Space_primeSpectrum_of_primes_maximal
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) : T2Space (PrimeSpectrum R) := by
  rw [t2Space_iff]
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hne
  have hpq : p ≠ q := fun h => hne (PrimeSpectrum.ext h)
  have hsup : p ⊔ q = ⊤ := (hmax p hp).coprime_of_ne (hmax q hq) hpq
  have h1 : (1 : R) ∈ p ⊔ q := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have haq : a ∉ q := by
    intro haq
    have hone : (1 : R) ∈ q := by rw [← hab]; exact q.add_mem haq hb
    exact (hmax q hq).ne_top ((Ideal.eq_top_iff_one q).mpr hone)
  obtain ⟨s, hs, n, hn⟩ := exists_notMem_mul_isNilpotent hmax hp ha
  refine ⟨(PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R)),
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)),
    PrimeSpectrum.isOpen_basicOpen, PrimeSpectrum.isOpen_basicOpen, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.mem_basicOpen s ⟨p, hp⟩).mpr hs
  · exact (PrimeSpectrum.mem_basicOpen a ⟨q, hq⟩).mpr haq
  · rw [Set.disjoint_left]
    intro r hr1 hr2
    have hsr : s ∉ r.asIdeal := (PrimeSpectrum.mem_basicOpen s r).mp hr1
    have har : a ∉ r.asIdeal := (PrimeSpectrum.mem_basicOpen a r).mp hr2
    have hmem : s * a ∈ r.asIdeal :=
      r.2.mem_of_pow_mem n (by rw [hn]; exact r.asIdeal.zero_mem)
    rcases r.2.mem_or_mem hmem with h' | h'
    · exact hsr h'
    · exact har h'

/-- A point of the spectrum and a distinct point can be separated by a basic open set. -/
theorem exists_basicOpen_mem_notMem (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal)
    {x y : PrimeSpectrum R} (hne : x ≠ y) :
    ∃ f : R, x ∈ PrimeSpectrum.basicOpen f ∧ y ∉ PrimeSpectrum.basicOpen f := by
  haveI : T1Space (PrimeSpectrum R) := (primes_maximal_iff_t1Space (R := R)).mp hmax
  have hopen : IsOpen ({y}ᶜ : Set (PrimeSpectrum R)) := (T1Space.t1 y).isOpen_compl
  have hx : x ∈ ({y}ᶜ : Set (PrimeSpectrum R)) := by simpa using hne
  obtain ⟨v, ⟨f, rfl⟩, hxv, hv⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hopen
  exact ⟨f, hxv, fun hy => hv hy rfl⟩

/-- Conditions (ii)–(iv) imply that `Spec A` is totally disconnected. -/
theorem totallyDisconnectedSpace_primeSpectrum_of_primes_maximal
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) :
    TotallyDisconnectedSpace (PrimeSpectrum R) := by
  haveI : T2Space (PrimeSpectrum R) := t2Space_primeSpectrum_of_primes_maximal hmax
  refine ⟨fun t _ ht => ?_⟩
  intro x hx y hy
  by_contra hne
  obtain ⟨f, hf, hyf⟩ := exists_basicOpen_mem_notMem hmax (x := x) (y := y) hne
  have hU : IsClopen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    ⟨(PrimeSpectrum.isCompact_basicOpen f).isClosed, PrimeSpectrum.isOpen_basicOpen⟩
  exact hyf (ht.subset_isClopen hU ⟨x, hx, hf⟩ hy)

/-! ## Passing to the quotient by the nilradical -/


/-- The quotient of a ring by its nilradical is reduced. -/
theorem isReduced_quotient_nilradical : IsReduced (R ⧸ nilradical R) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_nilradical] at hn
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical]
  exact hn.of_pow

/-- Condition (ii) is invariant under passing to the quotient by the nilradical. -/
theorem primes_maximal_quotient_nilradical_iff :
    (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ↔
      (∀ P : Ideal (R ⧸ nilradical R), P.IsPrime → P.IsMaximal) := by
  constructor
  · intro hmax P hP
    have hp : (Ideal.comap (Ideal.Quotient.mk (nilradical R)) P).IsPrime :=
      Ideal.comap_isPrime _ _
    have hmap : Ideal.map (Ideal.Quotient.mk (nilradical R))
        (Ideal.comap (Ideal.Quotient.mk (nilradical R)) P) = P :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
    have hker : RingHom.ker (Ideal.Quotient.mk (nilradical R)) ≤
        Ideal.comap (Ideal.Quotient.mk (nilradical R)) P := by
      rw [Ideal.mk_ker]
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact P.zero_mem
    haveI : (Ideal.comap (Ideal.Quotient.mk (nilradical R)) P).IsMaximal := hmax _ hp
    rw [← hmap]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  · intro hmax p hp
    have hker : RingHom.ker (Ideal.Quotient.mk (nilradical R)) ≤ p := by
      rw [Ideal.mk_ker]
      exact nilradical_le_of_isPrime hp
    haveI : p.IsPrime := hp
    have hP : (Ideal.map (Ideal.Quotient.mk (nilradical R)) p).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    haveI : (Ideal.map (Ideal.Quotient.mk (nilradical R)) p).IsMaximal := hmax _ hP
    have hcm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective (K := Ideal.map (Ideal.Quotient.mk (nilradical R)) p)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_of_le_left hker] at hcm
    exact hcm

/-- Condition (i) implies condition (ii). -/
theorem primes_maximal_of_absolutelyFlat_quotient
    (h : AbsolutelyFlat (R ⧸ nilradical R)) : ∀ p : Ideal R, p.IsPrime → p.IsMaximal :=
  (primes_maximal_quotient_nilradical_iff (R := R)).mpr fun P hP =>
    isMaximal_of_forall_exists_eq_mul_self_mul
      (fun x => exists_eq_self_mul_self_mul_of_absolutelyFlat h x) P hP

/-- Condition (ii) implies condition (i). -/
theorem absolutelyFlat_quotient_nilradical_of_primes_maximal
    (hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal) : AbsolutelyFlat (R ⧸ nilradical R) := by
  haveI := isReduced_quotient_nilradical (R := R)
  have hmax' := (primes_maximal_quotient_nilradical_iff (R := R)).mp hmax
  exact absolutelyFlat_of_forall_exists_eq_mul_self_mul
    (fun x => exists_eq_mul_self_mul_of_isReduced_primes_maximal hmax' x)

end Basic

/-! ## The main theorem -/

section Main

variable (A : Type u) [CommRing A]

/-- Exercise 3.11, (i) ⇔ (ii). -/
theorem solution_absolutelyFlat_iff_primes_maximal :
    AbsolutelyFlat (A ⧸ nilradical A) ↔ (∀ p : Ideal A, p.IsPrime → p.IsMaximal) :=
  ⟨primes_maximal_of_absolutelyFlat_quotient,
    absolutelyFlat_quotient_nilradical_of_primes_maximal⟩

/-- Exercise 3.11, (ii) ⇔ (iii). -/
theorem solution_primes_maximal_iff_t1Space :
    (∀ p : Ideal A, p.IsPrime → p.IsMaximal) ↔ T1Space (PrimeSpectrum A) :=
  primes_maximal_iff_t1Space

/-- Exercise 3.11, (iii) ⇔ (iv). -/
theorem solution_t1Space_iff_t2Space :
    T1Space (PrimeSpectrum A) ↔ T2Space (PrimeSpectrum A) :=
  ⟨fun h => t2Space_primeSpectrum_of_primes_maximal ((primes_maximal_iff_t1Space (R := A)).mpr h),
    fun h => @T2Space.t1Space (PrimeSpectrum A) _ h⟩

/-- Exercise 3.11, the second part: under these conditions `Spec A` is compact and totally
disconnected. -/
theorem solution_compact_and_totallyDisconnected
    (h : AbsolutelyFlat (A ⧸ nilradical A)) :
    CompactSpace (PrimeSpectrum A) ∧ TotallyDisconnectedSpace (PrimeSpectrum A) :=
  ⟨inferInstance,
    totallyDisconnectedSpace_primeSpectrum_of_primes_maximal
      ((solution_absolutelyFlat_iff_primes_maximal A).mp h)⟩

/-- **Atiyah–Macdonald, Chapter 3, Exercise 3.11.**  For a ring `A` with nilradical `𝔑`, the
following are equivalent: (i) `A / 𝔑` is absolutely flat; (ii) every prime ideal of `A` is
maximal; (iii) `Spec A` is a `T1`-space; (iv) `Spec A` is Hausdorff.  Moreover, under these
conditions `Spec A` is compact and totally disconnected. -/
theorem solution :
    (AbsolutelyFlat (A ⧸ nilradical A) ↔ (∀ p : Ideal A, p.IsPrime → p.IsMaximal)) ∧
    ((∀ p : Ideal A, p.IsPrime → p.IsMaximal) ↔ T1Space (PrimeSpectrum A)) ∧
    (T1Space (PrimeSpectrum A) ↔ T2Space (PrimeSpectrum A)) ∧
    (AbsolutelyFlat (A ⧸ nilradical A) → CompactSpace (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :=
  ⟨solution_absolutelyFlat_iff_primes_maximal A, solution_primes_maximal_iff_t1Space A,
    solution_t1Space_iff_t2Space A, solution_compact_and_totallyDisconnected A⟩

end Main

/-- Sanity check: a field satisfies condition (i) (hence all of them), since every module over a
field is free, hence flat. -/
example (K : Type u) [Field K] : AbsolutelyFlat K := fun M _ _ => by
  haveI : Module.Free K M := Module.Free.of_divisionRing K M
  infer_instance

#print axioms AtiyahMcdonald69.Ex_3_11.solution
#print axioms AtiyahMcdonald69.Ex_3_11.solution_absolutelyFlat_iff_primes_maximal
#print axioms AtiyahMcdonald69.Ex_3_11.solution_primes_maximal_iff_t1Space
#print axioms AtiyahMcdonald69.Ex_3_11.solution_t1Space_iff_t2Space
#print axioms AtiyahMcdonald69.Ex_3_11.solution_compact_and_totallyDisconnected

end AtiyahMcdonald69.Ex_3_11

