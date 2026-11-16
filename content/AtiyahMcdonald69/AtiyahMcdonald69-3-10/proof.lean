import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 3, Exercise 10

The exercise, as printed in the book (Chapter 3, *Modules of fractions*, exercises, p. 44):

> **10.** Let `A` be a ring.
> i) If `A` is absolutely flat (Chapter 2, Exercise 27) and `S` is any multiplicatively
>    closed subset of `A`, then `S⁻¹A` is absolutely flat.
> ii) `A` is absolutely flat ⇔ `A_m` is a field for each maximal ideal `m`.

Formalization choices.

* A multiplicatively closed subset is a `Submonoid A`; `S⁻¹A` is `Localization S`, and
  `A_m` is `Localization.AtPrime m`.  Nothing is assumed about `S` (it may contain `0`, in
  which case `S⁻¹A` is the zero ring) and `A` is allowed to be the zero ring.
* "Absolutely flat" is `IsAbsolutelyFlat` below: *every* `A`-module is flat.  The
  quantification is over modules in the same universe as `A`, the standard universe
  restriction of "every module" (this is the universe in which `Module.Flat` itself tests
  tensor maps).  "`A_m` is a field" is the data-free predicate `IsField`.
* The book's own solution of (i) quotes Exercise 2.27, whose criterion is "absolutely flat
  ⇔ every principal ideal is idempotent", and finishes with the computation
  `a = a ^ 2 * x ↦ a / s = (s * x) * (a / s) ^ 2`.  We instead prove (i) by the local
  character of flatness (`Module.flat_iff_of_isLocalization`: for a localization `S⁻¹A`,
  an `S⁻¹A`-module is flat over `S⁻¹A` iff it is flat over `A`), which is the module-level
  form of the same statement and needs no unproved converse of 2.27.  One direction of the
  2.27 criterion is nevertheless proved below (`exists_eq_sq_mul_of_isAbsolutelyFlat`).
* Part (ii) `⇒` reduces to the ring-theoretic fact that a *local* absolutely flat ring is a
  field, proved here from scratch (`isField_of_isAbsolutelyFlat`); the maximality of `m` is
  used only through locality of `A_m`.  Part (ii) `⇐` is the flatness criterion "flat
  locally at maximal ideals" (`Module.flat_of_localized_maximal`), with `A_m` a field so
  that every `A_m`-module is free, hence flat.
-/

universe u

open scoped nonZeroDivisors

namespace AtiyahMcdonald69.Ex_3_10

open Module

/-- `A` is *absolutely flat* (Atiyah–Macdonald, Chapter 2, Exercise 27) if every `A`-module
is flat. -/
def IsAbsolutelyFlat (A : Type u) [CommRing A] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Flat A M

/-! ### Examples of absolutely flat rings -/

/-- A field is absolutely flat: every module over a field is free, hence flat. -/
theorem isAbsolutelyFlat_of_field (K : Type u) [Field K] : IsAbsolutelyFlat K :=
  fun _ _ _ => Module.Flat.of_free

/-! ### A local absolutely flat ring is a field -/

/-- A local absolutely flat ring is a field.  This is the ring-theoretic input of (ii) `⇒`:
the only obstruction to being a field in a local ring is a nonzero element of the maximal
ideal, and absolute flatness makes every principal ideal idempotent. -/
theorem isField_of_isAbsolutelyFlat {R : Type u} [CommRing R] [IsLocalRing R]
    (h : IsAbsolutelyFlat R) : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  -- `R ⧸ (x)` is flat, so the principal ideal `(x)` is *pure*.
  have hpure : (Ideal.span {x}).Pure := h (R ⧸ Ideal.span {x})
  -- Purity gives `x = x * y` with `y ∈ (x)`.
  obtain ⟨y, hy, hxy⟩ :=
    Ideal.exists_eq_mul_of_pure (I := Ideal.span {x}) (Ideal.subset_span rfl)
  have hspan : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    simpa using hx
  -- As `x` lies in the maximal ideal, so does `y`, hence `1 - y` is a unit and `x = 0`.
  have hy' : y ∈ nonunits R := (IsLocalRing.mem_maximalIdeal y).mp (hspan hy)
  have hunit : IsUnit (1 - y) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits y hy'
  have hzero : x * (1 - y) = 0 := by rw [mul_sub, mul_one, ← hxy, sub_self]
  simpa using hunit.mul_left_eq_zero.mp hzero

/-- In an absolutely flat ring every principal ideal is idempotent: for all `x` there is `y`
with `x = x ^ 2 * y`.  This is the criterion of Chapter 2, Exercise 27 used implicitly by
the book's solution of (i). -/
theorem exists_eq_sq_mul_of_isAbsolutelyFlat {R : Type u} [CommRing R]
    (h : IsAbsolutelyFlat R) (x : R) : ∃ y : R, x = x ^ 2 * y := by
  have hpure : (Ideal.span {x}).Pure := h (R ⧸ Ideal.span {x})
  obtain ⟨y, hy, hxy⟩ :=
    Ideal.exists_eq_mul_of_pure (I := Ideal.span {x}) (Ideal.subset_span rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨c, ?_⟩
  calc x = x * y := hxy
    _ = x * (x * c) := by rw [hc]
    _ = x ^ 2 * c := by ring

/-- In an absolutely flat ring every ideal is idempotent (`I * I = I`), the remark following
Chapter 2, Exercise 27 in the book; it specializes to `(x) * (x) = (x)` for principal
ideals. -/
theorem isIdempotentElem_ideal_of_isAbsolutelyFlat {R : Type u} [CommRing R]
    (h : IsAbsolutelyFlat R) (I : Ideal R) : IsIdempotentElem I := by
  have hpure : I.Pure := h (R ⧸ I)
  exact Ideal.isIdempotentElem_of_pure I

/-! ### Part (i) -/

/-- Exercise 3.10 (i): a localization of an absolutely flat ring is absolutely flat. -/
theorem part_i (A : Type u) [CommRing A] (S : Submonoid A) (h : IsAbsolutelyFlat A) :
    IsAbsolutelyFlat (Localization S) := by
  intro M _ _
  -- view `M` as an `A`-module by restriction of scalars along `A → S⁻¹A`
  let : Module A M := Module.compHom M (algebraMap A (Localization S))
  have hst : IsScalarTower A (Localization S) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- flatness of an `S⁻¹A`-module is the flatness of its underlying `A`-module
  exact (Module.flat_iff_of_isLocalization (Localization S) S M).mpr (h M)

/-! ### Part (ii) -/

/-- Exercise 3.10 (ii), `⇒`: the localization of an absolutely flat ring at a maximal ideal
is a field. -/
theorem isField_localization_of_isAbsolutelyFlat (A : Type u) [CommRing A]
    (h : IsAbsolutelyFlat A) (m : Ideal A) [m.IsMaximal] :
    IsField (Localization.AtPrime m) :=
  isField_of_isAbsolutelyFlat (part_i A m.primeCompl h)

/-- Exercise 3.10 (ii), `⇐`: if all localizations at maximal ideals are fields, every
`A`-module is flat. -/
theorem isAbsolutelyFlat_of_isField_localization (A : Type u) [CommRing A]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsField (Localization.AtPrime m)) :
    IsAbsolutelyFlat A := by
  intro M _ _
  -- flatness is local at the maximal ideals
  refine Module.flat_of_localized_maximal M (fun P hP => ?_)
  rw [← Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
    (LocalizedModule P.primeCompl M)]
  -- over a field every module is free, hence flat
  let : Field (Localization.AtPrime P) := (h P).toField
  exact Module.Flat.of_free

/-- Exercise 3.10 (ii): `A` is absolutely flat iff `A_m` is a field for every maximal
ideal `m`. -/
theorem part_ii (A : Type u) [CommRing A] :
    IsAbsolutelyFlat A ↔ ∀ (m : Ideal A) [m.IsMaximal], IsField (Localization.AtPrime m) :=
  ⟨fun h m _ => isField_localization_of_isAbsolutelyFlat A h m,
   fun h => isAbsolutelyFlat_of_isField_localization A h⟩

/-- Exercise 3.10 (ii), `⇒`, for an arbitrary prime ideal: the argument proving
`isField_of_isAbsolutelyFlat` only uses that `A_p` is local, so the maximality of the ideal
is not needed on this side.  Consequently the condition in (ii) may be tested on all prime
ideals; see `part_ii_prime`. -/
theorem isField_localization_of_isAbsolutelyFlat_of_isPrime (A : Type u) [CommRing A]
    (h : IsAbsolutelyFlat A) (p : Ideal A) [p.IsPrime] :
    IsField (Localization.AtPrime p) :=
  isField_of_isAbsolutelyFlat (part_i A p.primeCompl h)

/-- Exercise 3.10 (ii) with the maximal ideals replaced by arbitrary prime ideals.  The `⇒`
direction here is *stronger* than (ii) `⇒`, since the argument for
`isField_of_isAbsolutelyFlat` only uses that `A_p` is local; the `⇐` direction is weaker than
(ii) `⇐` and follows from it.  So the condition in (ii) may be tested on all prime
ideals. -/
theorem part_ii_prime (A : Type u) [CommRing A] :
    IsAbsolutelyFlat A ↔ ∀ (p : Ideal A) [p.IsPrime], IsField (Localization.AtPrime p) :=
  ⟨fun h p _ => isField_localization_of_isAbsolutelyFlat_of_isPrime A h p,
   fun h => (part_ii A).mpr fun m _ => h m⟩

/-! ### The exercise -/

/-- Atiyah–Macdonald, Chapter 3, Exercise 10, both parts. -/
theorem solution :
    (∀ (A : Type u) [CommRing A] (S : Submonoid A), IsAbsolutelyFlat A →
      IsAbsolutelyFlat (Localization S)) ∧
    (∀ (A : Type u) [CommRing A],
      IsAbsolutelyFlat A ↔ ∀ (m : Ideal A) [m.IsMaximal], IsField (Localization.AtPrime m)) :=
  ⟨part_i, part_ii⟩

/-! ### The zero ring

The book allows the zero ring.  It has no maximal ideals, so the condition in (ii) is
vacuous there, and indeed the zero ring is absolutely flat; no `Nontrivial` hypothesis is
needed anywhere in this exercise. -/

/-- A subsingleton ring (in particular the zero ring) is absolutely flat: it has no maximal
ideals, so the criterion of part (ii) is vacuous. -/
theorem isAbsolutelyFlat_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] :
    IsAbsolutelyFlat R := by
  refine (part_ii R).mpr fun m hm => ?_
  have htop : (⊤ : Ideal R) ≤ m := by
    intro x _
    rw [Subsingleton.elim x 0]
    exact m.zero_mem
  exact absurd (le_antisymm le_top htop) hm.ne_top

/-- The zero ring `ℤ ⧸ (1)` is absolutely flat; part (ii) is not vacuous by accident but
consistent with the zero ring, as it must be for the book's statement to be true. -/
theorem isAbsolutelyFlat_int_quotient_top : IsAbsolutelyFlat (ℤ ⧸ (⊤ : Ideal ℤ)) :=
  isAbsolutelyFlat_of_subsingleton _

/-! ### Auditing the statement: what cannot be weakened or reversed

Part (i) has no converse: localizing at the non-zero-divisors of `ℤ` produces the field `ℚ`,
which is absolutely flat, while `ℤ` is not.  So "some (every) localization is absolutely
flat" does not imply absolute flatness of the ring, and part (i) cannot be upgraded to an
equivalence.  (`ℤ` is a domain in which `2` is a non-zero-divisor but `2 •` is zero on
`ℤ ⧸ (2)`, so `ℤ ⧸ (2)` is not flat.) -/

/-- `ℤ` is not absolutely flat. -/
theorem not_isAbsolutelyFlat_int : ¬ IsAbsolutelyFlat ℤ := by
  intro h
  -- `ℤ ⧸ (2)` would have to be flat, hence torsion free, but `2 • 1 = 0` there
  have hflat : Module.Flat ℤ (ZMod 2) := h (ZMod 2)
  have := hflat
  have hreg : IsSMulRegular (ZMod 2) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (r := (2 : ℤ)) (by simp)
  have h1 : (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • (0 : ZMod 2) := by
    simp only [smul_zero]
    decide
  exact one_ne_zero (hreg h1)

/-- The total ring of fractions of `ℤ` is its fraction field (`ℚ`), which is absolutely
flat. -/
theorem isAbsolutelyFlat_localization_nonZeroDivisors_int :
    IsAbsolutelyFlat (Localization (nonZeroDivisors ℤ)) := by
  intro M _ _
  let : Field (Localization (nonZeroDivisors ℤ)) := inferInstance
  exact Module.Flat.of_free

/-- The converse of part (i) fails: there are a ring `A` and a multiplicatively closed
`S ⊆ A` with `S⁻¹A` absolutely flat, although `A` is not. -/
theorem localization_absolutelyFlat_not_absolutelyFlat :
    ∃ (A : Type) (_ : CommRing A) (S : Submonoid A),
      IsAbsolutelyFlat (Localization S) ∧ ¬ IsAbsolutelyFlat A :=
  ⟨ℤ, inferInstance, nonZeroDivisors ℤ,
    isAbsolutelyFlat_localization_nonZeroDivisors_int, not_isAbsolutelyFlat_int⟩

/-- In part (ii) the word "field" cannot be weakened to "domain": `ℤ` is a domain, all of
whose localizations at maximal ideals are domains, yet `ℤ` is not absolutely flat. -/
theorem not_absolutelyFlat_of_isDomain_localization :
    ∃ (A : Type) (_ : CommRing A),
      (∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) ∧ ¬ IsAbsolutelyFlat A :=
  ⟨ℤ, inferInstance, fun _ _ => inferInstance, not_isAbsolutelyFlat_int⟩

end AtiyahMcdonald69.Ex_3_10
