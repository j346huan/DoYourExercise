import Mathlib

/-!
# Atiyah–Macdonald (1969), Exercise 5.15

Let `A` be an integrally closed domain with field of fractions `K`, let `L` be a finite
extension field of `K` and let `B` be the integral closure of `A` in `L`.  Then for every
prime ideal `P` of `A` the set of prime ideals of `B` contracting to `P` is finite, i.e.
`Spec B → Spec A` has finite fibres.

The proof follows the book's reduction:
* if `L/K` is purely inseparable, there is exactly one prime of `B` above `P`, namely
  the set of all `x ∈ B` with `x ^ (p ^ m) ∈ P` for some `m`;
* if `L/K` is separable we embed `L` into a finite Galois extension `M/K`; the primes of
  the integral closure `C` of `A` in `M` above `P` form a single orbit under `Gal(M/K)`,
  hence are finite, and every prime of `B` above `P` is the contraction of one of them;
* the general case is reduced to these two by separating the maximal separable
  subextension.
-/

namespace AtiyahMcdonald69.Ex_5_15

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

/-! ## The purely inseparable case -/

section PurelyInseparable

variable {A K L : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The candidate prime in the purely inseparable case: the set of all `x ∈ B` such that
`x ^ (p ^ n) ∈ P` for some `n`. -/
def pthRootSet (p : ℕ) (P : Ideal A) : Set (integralClosure A L) :=
  {x | ∃ n : ℕ, x ^ p ^ n ∈ P.map (algebraMap A (integralClosure A L))}

/-- In the purely inseparable case the prime of the integral closure above `P` is unique
and is given by the book's formula: the set of all `x ∈ B` such that `x ^ (p ^ m) ∈ P`
for some `m ≥ 0`. -/
theorem eq_primesOver_of_isPurelyInseparable
    (p : ℕ) [ExpChar K p] [IsPurelyInseparable K L]
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime]
    {q : Ideal (integralClosure A L)} (hq : q ∈ P.primesOver (integralClosure A L)) :
    q = pthRootSet (A := A) (L := L) p P := by
  ext x
  constructor
  · -- `x ∈ q` implies `x ^ (p ^ n)` is integral over `A` and lies in `K`
    intro hx
    have hxint : IsIntegral A (x : L) := x.2
    obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem (F := K) (E := L) (q := p) (x := (x : L))
    -- `k` is integral over `A`
    have hkint : IsIntegral A k := by
      rw [← isIntegral_algebraMap_iff (algebraMap K L).injective]
      rw [hk]
      exact hxint.pow (p ^ n)
    obtain ⟨a, ha⟩ := hcl k hkint
    refine ⟨n, ?_⟩
    have hxa : (x : L) ^ p ^ n = algebraMap A L a := by
      rw [← hk, ← ha, ← IsScalarTower.algebraMap_apply A K L]
    have hmem : algebraMap A (integralClosure A L) a = x ^ p ^ n := by
      apply Subtype.coe_injective
      push_cast
      exact hxa.symm
    have hLO : q.LiesOver P := hq.2
    have hmem' : a ∈ P := by
      rw [Ideal.mem_of_liesOver (A := A) (P := q) (p := P) a, hmem]
      exact q.pow_mem_of_mem hx (p ^ n) (pow_pos (expChar_pos (R := K) p) n)
    exact hmem ▸ Ideal.mem_map_of_mem (algebraMap A (integralClosure A L)) hmem'
  · -- if `x ^ (p ^ n) ∈ P` then `x ∈ q` because `q` is prime and contains `P`
    rintro ⟨n, hn⟩
    have hmap : P.map (algebraMap A (integralClosure A L)) ≤ q := by
      rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq hq.2.over
    exact hq.1.mem_of_pow_mem (p ^ n) (hmap hn)

/-- In the purely inseparable case there is at most one prime of `B` over `P`. -/
theorem eq_of_mem_primesOver_of_isPurelyInseparable
    (p : ℕ) [ExpChar K p] [IsPurelyInseparable K L]
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime]
    {q q' : Ideal (integralClosure A L)}
    (hq : q ∈ P.primesOver (integralClosure A L))
    (hq' : q' ∈ P.primesOver (integralClosure A L)) : q = q' := by
  exact SetLike.ext' ((eq_primesOver_of_isPurelyInseparable p hcl P hq).trans
    (eq_primesOver_of_isPurelyInseparable p hcl P hq').symm)

/-- In the purely inseparable case the fibre is finite (it is a singleton). -/
theorem finite_primesOver_of_isPurelyInseparable
    (p : ℕ) [ExpChar K p] [IsPurelyInseparable K L]
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite := by
  rcases (P.primesOver (integralClosure A L)).eq_empty_or_nonempty with h | ⟨q, hq⟩
  · rw [h]
    exact Set.finite_empty
  · refine Set.Finite.subset (Set.finite_singleton q) ?_
    intro q' hq'
    rw [Set.mem_singleton_iff]
    exact eq_of_mem_primesOver_of_isPurelyInseparable p hcl P hq' hq

/-- If `A → L` is injective then so is `A → B`, `B` the integral closure of `A` in `L`. -/
theorem algebraMap_integralClosure_injective {A L : Type*} [CommRing A] [Field L]
    [Algebra A L] (h : Function.Injective (algebraMap A L)) :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  intro x y hxy
  apply h
  simpa using congrArg (fun z : integralClosure A L => (z : L)) hxy

/-- Lying over for the integral closure: every prime of `A` is below some prime of `B`. -/
theorem exists_mem_primesOver {A L : Type*} [CommRing A] [Field L] [Algebra A L]
    (P : Ideal A) [P.IsPrime]
    (hinj : Function.Injective (algebraMap A (integralClosure A L))) :
    ∃ q ∈ P.primesOver (integralClosure A L), True := by
  have hker : RingHom.ker (algebraMap A (integralClosure A L)) ≤ P := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := hinj (by rw [hx, map_zero])
    rw [hx0]
    exact P.zero_mem
  obtain ⟨Q, -, hQprime, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := integralClosure A L) P ⊥ hker
  exact ⟨Q, ⟨hQprime, hQ.symm ▸ Ideal.over_under Q⟩, trivial⟩

end PurelyInseparable

/-! ## The separable case, via a finite Galois extension -/

section GaloisCase

variable {A K M : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- The fixed points of the action of `Gal(M/K)` on the integral closure of `A` in `M`
are exactly the elements of `A`: a fixed point lies in `K` (fixed field of a Galois
extension) and is integral over `A`, hence in `A` since `A` is integrally closed in `K`. -/
theorem isInvariant_integralClosure
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x) :
    Algebra.IsInvariant A (integralClosure A M) (M ≃ₐ[K] M) where
  isInvariant x hx := by
    have hfix : ∀ σ : M ≃ₐ[K] M, σ (x : M) = (x : M) := by
      intro σ
      have h : σ • x = x := hx σ
      have h2 : ((σ • x : integralClosure A M) : M) = σ (x : M) := rfl
      rw [← h2, h]
    have hxK : (x : M) ∈ Set.range (algebraMap K M) :=
      (IsGalois.mem_range_algebraMap_iff_fixed (x : M)).mpr hfix
    obtain ⟨k, hk⟩ := hxK
    have hint : IsIntegral A k := by
      rw [← isIntegral_algebraMap_iff (algebraMap K M).injective, hk]
      exact x.2
    obtain ⟨a, ha⟩ := hcl k hint
    refine ⟨a, Subtype.ext ?_⟩
    change algebraMap A M a = (x : M)
    rw [IsScalarTower.algebraMap_apply A K M, ha, hk]

/-- In the Galois case the primes of the integral closure above `P` form a single orbit
under `Gal(M/K)`, hence are finite. -/
theorem finite_primesOver_of_isGalois
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A M)).Finite := by
  have : Algebra.IsInvariant A (integralClosure A M) (M ≃ₐ[K] M) :=
    isInvariant_integralClosure hcl
  have : Finite (M ≃ₐ[K] M) := Finite.algEquiv
  rcases (P.primesOver (integralClosure A M)).eq_empty_or_nonempty with h | ⟨Q, hQ⟩
  · rw [h]
    exact Set.finite_empty
  · have : Q.IsPrime := hQ.1
    have : Q.LiesOver P := hQ.2
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A (integralClosure A M) (M ≃ₐ[K] M) P Q]
    exact Finite.finite_mulAction_orbit Q

end GaloisCase

section Tower

variable {A K L M : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- A `K`-algebra map `L →ₐ[K] M` induces a ring map between the integral closures of `A`. -/
noncomputable def mapIntegralClosure (φ : L →ₐ[K] M) :
    integralClosure A L →+* integralClosure A M where
  toFun x := ⟨φ (x : L), IsIntegral.map φ x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem mapIntegralClosure_injective (φ : L →ₐ[K] M) (hφ : Function.Injective φ) :
    Function.Injective (mapIntegralClosure (A := A) φ) := by
  intro x y hxy
  refine Subtype.ext (hφ ?_)
  exact congrArg (fun z : integralClosure A M => (z : M)) hxy

/-- Separable case, reduction step: if `L` embeds into a finite Galois extension `M` of `K`,
then the fibre of `Spec B → Spec A` over `P` is finite. -/
theorem finite_primesOver_of_algHom_isGalois
    (φ : L →ₐ[K] M) (hφ : Function.Injective φ)
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite := by
  set f : integralClosure A L →+* integralClosure A M := mapIntegralClosure (A := A) φ with hf
  have finj : Function.Injective f := mapIntegralClosure_injective φ hφ
  let : Algebra (integralClosure A L) (integralClosure A M) := f.toAlgebra
  have hst : IsScalarTower A (integralClosure A L) (integralClosure A M) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap A M x = φ (algebraMap A L x)
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L]
    exact (φ.commutes (algebraMap A K x)).symm
  have hint : Algebra.IsIntegral (integralClosure A L) (integralClosure A M) :=
    ⟨fun y => (Algebra.IsIntegral.isIntegral (R := A) y).tower_top⟩
  have hC : (P.primesOver (integralClosure A M)).Finite := finite_primesOver_of_isGalois hcl P
  refine Set.Finite.subset (hC.image (fun Q => Q.comap f)) ?_
  intro q hq
  have hker : RingHom.ker (algebraMap (integralClosure A L) (integralClosure A M)) ≤ q := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : f x = 0 := hx
    have hx0 : x = 0 := finj (by rw [hx', map_zero])
    rw [hx0]
    exact q.zero_mem
  have hqprime : q.IsPrime := hq.1
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := integralClosure A L)
      (S := integralClosure A M) q ⊥ hker
  refine ⟨Q, ⟨hQprime, ⟨?_⟩⟩, hQcomap⟩
  have h1 : (Q.under (integralClosure A L)).under A = P := by
    rw [show Q.under (integralClosure A L) = q from hQcomap]
    exact hq.2.over.symm
  rw [← Ideal.under_under (A := A) (B := integralClosure A L) Q]
  exact h1.symm

end Tower

section SeparableCase

variable {A K L : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

/-- Separable case of Atiyah–Macdonald 5.15: if `L/K` is finite separable, then the fibre
of `Spec B → Spec A` over a prime `P` is finite.  The proof embeds `L` into the normal
closure `M` of `L` inside an algebraic closure of `K`, uses that `M/K` is finite Galois,
and that every prime of `B` above `P` is the contraction of a prime of the integral
closure `C` of `A` in `M`. -/
theorem finite_primesOver_of_isSeparable
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (hsep : Algebra.IsSeparable K L) (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite := by
  let Ω := AlgebraicClosure K
  let φ : L →ₐ[K] Ω := IsAlgClosed.lift
  have hφ : Function.Injective φ := RingHom.injective φ.toRingHom
  let L' : IntermediateField K Ω := φ.fieldRange
  have hL'fd : FiniteDimensional K L' := LinearMap.finiteDimensional_range φ.toLinearMap
  have hL'sep : Algebra.IsSeparable K L' := by
    refine ⟨fun x => ?_⟩
    rw [← isSeparable_map_iff (IsScalarTower.toAlgHom K L' Ω) (algebraMap L' Ω).injective]
    change IsSeparable K (x : Ω)
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp x.2
    rw [show (x : Ω) = φ y from hy.symm]
    exact IsSeparable.map φ hφ (Algebra.IsSeparable.isSeparable K y)
  let M : IntermediateField K Ω := IntermediateField.normalClosure K ↥L' Ω
  have hMfd : FiniteDimensional K M := normalClosure.is_finiteDimensional K ↥L' Ω
  have hMnorm : Normal K M := normalClosure.normal K ↥L' Ω
  have hMsep : Algebra.IsSeparable K M := by
    have hle : M ≤ separableClosure K Ω := by
      rw [normalClosure_le_iff]
      intro f x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      rw [mem_separableClosure_iff]
      exact IsSeparable.map f (RingHom.injective f.toRingHom)
        (Algebra.IsSeparable.isSeparable K y)
    refine ⟨fun x => ?_⟩
    rw [← isSeparable_map_iff (IsScalarTower.toAlgHom K M Ω)
      (algebraMap M Ω).injective]
    exact mem_separableClosure_iff.mp (hle x.2)
  have : FiniteDimensional K M := hMfd
  have : Normal K M := hMnorm
  have : Algebra.IsSeparable K M := hMsep
  have : IsGalois K M := ⟨⟩
  have hle : L' ≤ M := IntermediateField.le_normalClosure L'
  have hmem : ∀ x : L, φ x ∈ L' := fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
  let φ' : L →ₐ[K] M := φ.codRestrict M.toSubalgebra (fun x => hle (hmem x))
  refine finite_primesOver_of_algHom_isGalois (A := A) (K := K) (L := L) (M := M) φ' ?_ hcl P
  intro x y hxy
  exact hφ (congrArg Subtype.val hxy)

end SeparableCase

section GeneralCaseLift

variable {A : Type*} [CommRing A] {K : Type*} [Field K] {L : Type*} [Field L]
  [Algebra K L] [Algebra A K] [Algebra A L] [IsScalarTower A K L]

/-- The canonical map between the integral closures of `A` induced by an intermediate field
`E ⊆ L`: both are subrings of `L`. -/
noncomputable def mapIntegralClosureOfLe (E : IntermediateField K L) :
    integralClosure A ↥E →+* integralClosure A L where
  toFun d := ⟨algebraMap ↥E L (d : ↥E), by
    have hST : IsScalarTower A ↥E L := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      show algebraMap A L x = algebraMap ↥E L (algebraMap A ↥E x)
      rw [IntermediateField.algebraMap_apply, IsScalarTower.algebraMap_apply A K ↥E,
        IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
    exact IsIntegral.map (IsScalarTower.toAlgHom A ↥E L) d.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem mapIntegralClosureOfLe_injective (E : IntermediateField K L) :
    Function.Injective (mapIntegralClosureOfLe (A := A) E) := by
  intro x y hxy
  refine Subtype.ext ?_
  exact (algebraMap ↥E L).injective (congrArg (fun z : integralClosure A L => (z : L)) hxy)

end GeneralCaseLift

section GeneralCase

variable {A K L : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

/-- In positive characteristic, passing to the maximal separable subextension does not change
the fibre: if `E ⊆ L` is the separable closure of `K` in `L`, `D` and `B` are the integral
closures of `A` in `E` and `L`, then two primes of `B` above the same prime of `D`
coincide, because every element of `B` has a `p`-power in `D`. -/
theorem primesOver_lift_unique
    (p : ℕ) [CharP K p] [Fact p.Prime]
    (q q' : Ideal (integralClosure A L))
    (hq : q.IsPrime) (hq' : q'.IsPrime)
    (heq : q.comap (mapIntegralClosureOfLe (A := A) (separableClosure K L)) =
      q'.comap (mapIntegralClosureOfLe (A := A) (separableClosure K L))) :
    q = q' := by
  let E := separableClosure K L
  haveI hST : IsScalarTower A E L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    show algebraMap A L x = algebraMap E L (algebraMap A E x)
    rw [IntermediateField.algebraMap_apply, IsScalarTower.algebraMap_apply A K E,
      IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
  have hexp : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  have hpure : IsPurelyInseparable E L := inferInstance
  have key : ∀ {r r' : Ideal (integralClosure A L)}, r.IsPrime → r'.IsPrime →
      (r.comap (mapIntegralClosureOfLe (A := A) E) =
        r'.comap (mapIntegralClosureOfLe (A := A) E)) →
      ∀ x : integralClosure A L, x ∈ r → x ∈ r' := by
    intro r r' hr hr' heq' x hx
    have hxint : IsIntegral A (x : L) := x.2
    obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem (F := E) (E := L) (q := p) (x := (x : L))
    have hkint : IsIntegral A k := by
      rw [← isIntegral_algebraMap_iff (algebraMap E L).injective, hk]
      exact hxint.pow (p ^ n)
    set d : integralClosure A E := ⟨k, hkint⟩ with hd
    have hfd : (mapIntegralClosureOfLe (A := A) E) d = x ^ p ^ n := by
      apply Subtype.ext
      show algebraMap E L k = ((x : L) ^ p ^ n)
      exact hk
    have hdq : (mapIntegralClosureOfLe (A := A) E) d ∈ r := by
      rw [hfd]
      exact r.pow_mem_of_mem hx (p ^ n) (pow_pos (expChar_pos (R := K) p) n)
    rw [← Ideal.mem_comap] at hdq
    rw [heq'] at hdq
    rw [Ideal.mem_comap] at hdq
    rw [hfd] at hdq
    exact hr'.mem_of_pow_mem (p ^ n) hdq
  exact Ideal.ext fun x => ⟨key hq hq' heq x, key hq' hq heq.symm x⟩

/-- **Atiyah–Macdonald, Exercise 5.15**: for `A` an integrally closed domain with fraction
field `K`, `L/K` a finite extension and `B` the integral closure of `A` in `L`, every fibre
of `Spec B → Spec A` is finite. -/
theorem finite_primesOver_finiteDimensional
    (hcl : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x)
    (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite := by
  classical
  by_cases h0 : CharZero K
  · have hsep : Algebra.IsSeparable K L := inferInstance
    exact finite_primesOver_of_isSeparable hcl hsep P
  · obtain ⟨p, hpp, hcharp⟩ : ∃ p : ℕ, p.Prime ∧ CharP K p := by
      refine ⟨ringChar K, ?_, inferInstance⟩
      rcases CharP.char_is_prime_or_zero K (ringChar K) with h | h
      · exact h
      · exact absurd ((CharP.ringChar_zero_iff_CharZero (R := K)).mp h) h0
    haveI : CharP K p := hcharp
    haveI : Fact p.Prime := ⟨hpp⟩
    let E := separableClosure K L
    set f : integralClosure A ↥E →+* integralClosure A L :=
      mapIntegralClosureOfLe (A := A) E with hf
    have hDE : (P.primesOver (integralClosure A ↥E)).Finite :=
      finite_primesOver_of_isSeparable (K := K) (L := ↥E) hcl inferInstance P
    have hST' : IsScalarTower A ↥E L := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      show algebraMap A L x = algebraMap ↥E L (algebraMap A ↥E x)
      rw [IntermediateField.algebraMap_apply, IsScalarTower.algebraMap_apply A K ↥E,
        IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
    let : Algebra (integralClosure A ↥E) (integralClosure A L) := f.toAlgebra
    have hst : IsScalarTower A (integralClosure A ↥E) (integralClosure A L) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap A L x = algebraMap ↥E L (algebraMap A ↥E x)
      rfl
    let lift : Ideal (integralClosure A ↥E) → Ideal (integralClosure A L) := fun q₀ =>
      if h : ∃ Q : Ideal (integralClosure A L), Q.IsPrime ∧ Q.comap f = q₀
        then Classical.choose h else ⊥
    have lift_spec : ∀ (q₀ : Ideal (integralClosure A ↥E))
        (h : ∃ Q : Ideal (integralClosure A L), Q.IsPrime ∧ Q.comap f = q₀),
        (lift q₀).IsPrime ∧ (lift q₀).comap f = q₀ := by
      intro q₀ h
      have : lift q₀ = Classical.choose h := by
        simp only [lift, dif_pos h]
      rw [this]
      exact Classical.choose_spec h
    refine Set.Finite.subset (hDE.image lift) ?_
    intro q hq
    have hq₀ : q.comap f ∈ P.primesOver (integralClosure A ↥E) := by
      haveI : q.IsPrime := hq.1
      refine ⟨Ideal.comap_isPrime f q, ⟨?_⟩⟩
      have h1 : Ideal.under A (q.comap f) = Ideal.under A q := by
        rw [← Ideal.under_under (A := A) (B := integralClosure A ↥E) q]
        rfl
      rw [h1]
      exact hq.2.over
    refine ⟨q.comap f, hq₀, ?_⟩
    have hex : ∃ Q : Ideal (integralClosure A L), Q.IsPrime ∧ Q.comap f = q.comap f :=
      ⟨q, hq.1, rfl⟩
    exact (primesOver_lift_unique p (lift (q.comap f)) q (lift_spec _ hex).1 hq.1
      (lift_spec _ hex).2)

end GeneralCase

/-! ## The statements in the form of the book -/

section BookForm

variable {A K L : Type*}
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- `A` integrally closed in its field of fractions `K`, in elementwise form. -/
theorem integrallyClosed_condition (x : K) (hx : IsIntegral A x) :
    ∃ a : A, algebraMap A K a = x :=
  (isIntegrallyClosed_iff K).1 ‹IsIntegrallyClosed A› hx

/-- **Atiyah–Macdonald 5.15** (general case): if `A` is an integrally closed domain with
field of fractions `K`, `L/K` a finite extension and `B` the integral closure of `A` in
`L`, then for every prime ideal `P` of `A` the set of primes of `B` contracting to `P` is
finite, i.e. `Spec B → Spec A` has finite fibres. -/
theorem atiyah_macdonald_5_15 [FiniteDimensional K L] (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite :=
  finite_primesOver_finiteDimensional (integrallyClosed_condition (K := K)) P

/-- **Atiyah–Macdonald 5.15**, separable case. -/
theorem atiyah_macdonald_5_15_separable [FiniteDimensional K L]
    (hsep : Algebra.IsSeparable K L) (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite :=
  finite_primesOver_of_isSeparable (integrallyClosed_condition (K := K)) hsep P

/-- **Atiyah–Macdonald 5.15**, purely inseparable case: there is a unique prime of `B` above
`P` (so `Spec B → Spec A` is bijective), and it is the set of all `x ∈ B` with
`x ^ (p ^ m) ∈ P` for some `m`. -/
theorem atiyah_macdonald_5_15_purelyInseparable (p : ℕ) [CharP K p] [Fact p.Prime]
    [IsPurelyInseparable K L] (P : Ideal A) [P.IsPrime] :
    (P.primesOver (integralClosure A L)).Finite ∧
      (∀ q ∈ P.primesOver (integralClosure A L),
        q = {x : integralClosure A L |
          ∃ n : ℕ, x ^ p ^ n ∈ P.map (algebraMap A (integralClosure A L))}) ∧
      (∃! q, q ∈ P.primesOver (integralClosure A L)) := by
  have hinj : Function.Injective (algebraMap A L) := by
    intro x y hxy
    rw [IsScalarTower.algebraMap_apply A K L] at hxy
    rw [IsScalarTower.algebraMap_apply A K L] at hxy
    exact IsFractionRing.injective A K ((algebraMap K L).injective hxy)
  obtain ⟨q₀, hq₀, -⟩ := exists_mem_primesOver P (algebraMap_integralClosure_injective hinj)
  refine ⟨finite_primesOver_of_isPurelyInseparable p
      (integrallyClosed_condition (A := A) (K := K)) P,
    fun q hq => eq_primesOver_of_isPurelyInseparable p
      (integrallyClosed_condition (A := A) (K := K)) P hq,
    ⟨q₀, hq₀, fun q hq => eq_of_mem_primesOver_of_isPurelyInseparable p
      (integrallyClosed_condition (A := A) (K := K)) P hq hq₀⟩⟩

end BookForm

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_5_15.atiyah_macdonald_5_15
#print axioms AtiyahMcdonald69.Ex_5_15.atiyah_macdonald_5_15_separable
#print axioms AtiyahMcdonald69.Ex_5_15.atiyah_macdonald_5_15_purelyInseparable
#print axioms AtiyahMcdonald69.Ex_5_15.finite_primesOver_of_isGalois
#print axioms AtiyahMcdonald69.Ex_5_15.finite_primesOver_of_algHom_isGalois
#print axioms AtiyahMcdonald69.Ex_5_15.finite_primesOver_finiteDimensional
#print axioms AtiyahMcdonald69.Ex_5_15.finite_primesOver_of_isSeparable
#print axioms AtiyahMcdonald69.Ex_5_15.finite_primesOver_of_isPurelyInseparable
#print axioms AtiyahMcdonald69.Ex_5_15.eq_primesOver_of_isPurelyInseparable
#print axioms AtiyahMcdonald69.Ex_5_15.primesOver_lift_unique
#print axioms AtiyahMcdonald69.Ex_5_15.isInvariant_integralClosure

end AtiyahMcdonald69.Ex_5_15
