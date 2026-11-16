import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 3, Exercise 12

Let `A` be an integral domain and `M` an `A`-module. An element `x ∈ M` is a *torsion
element* of `M` if `Ann(x) ≠ 0`, that is, if `x` is killed by some nonzero element of `A`.
The exercise asks to show that

* the torsion elements of `M` form a submodule `T(M)` (the *torsion submodule*);
* (i) `M ⧸ T(M)` is torsion-free;
* (ii) `f(T(M)) ⊆ T(N)` for every `A`-linear map `f : M → N`;
* (iii) if `0 → M' → M → M''` is exact, then `0 → T(M') → T(M) → T(M'')` is exact;
* (iv) `T(M)` is the kernel of `x ↦ 1 ⊗ x : M → K ⊗[A] M`, where `K` is the field of
  fractions of `A`.

Natural-language solution (DoYourExercise, AtiyahMcdonald69-3-12): advisory only.  The
formalization below follows the book's constructions.  The torsion submodule is defined by
the book's condition "killed by some nonzero element", and is proved to coincide with the
annihilator condition `Ann x ≠ 0` (`mem_torsionSubmodule_iff_annihilator_ne_bot`) and with
Mathlib's `Submodule.torsion` (`torsionSubmodule_eq_torsion`).  Part (iv) is proved through
actual localization/tensor-product technology: `x ↦ 1 ⊗ x` is a localization of `M` at the
nonzero elements of `A` (`IsLocalization.tensorProduct_isLocalizedModule`), the modern form
of the book's hint that `K` is the directed union of the submodules `A · (1/s)`, so
`1 ⊗ x = 0` exactly when some nonzero `a` kills `x`.  Part (iv) is stated for an arbitrary
field of fractions `K` of `A`, with `K = FractionRing A` as a special case.

The last section records that the integral-domain hypothesis in the first part is *not*
redundant, with an explicit counterexample over `ℤ × ℤ`.
-/

namespace AtiyahMcdonald69.Ex_3_12

open TensorProduct

variable {A : Type*} [CommRing A] [IsDomain A]

/-! ## The torsion elements and the torsion submodule -/

section TorsionSet

variable (A)

/-- The torsion elements of an `A`-module `M`: the elements killed by some nonzero element
of `A`, i.e. the elements with nonzero annihilator. -/
def torsionSet (M : Type*) [AddCommGroup M] [Module A M] : Set M :=
  {x | ∃ a : A, a ≠ 0 ∧ a • x = 0}

variable {A}

theorem zero_mem_torsionSet {M : Type*} [AddCommGroup M] [Module A M] :
    (0 : M) ∈ torsionSet A M :=
  ⟨1, one_ne_zero, smul_zero 1⟩

/-- The sum of two torsion elements is torsion: if `a` kills `x` and `b` kills `y`, then
`a * b ≠ 0` kills `x + y`. This is where the absence of zero divisors is used. -/
theorem add_mem_torsionSet {M : Type*} [AddCommGroup M] [Module A M] {x y : M}
    (hx : x ∈ torsionSet A M) (hy : y ∈ torsionSet A M) : x + y ∈ torsionSet A M := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
    rw [smul_add, mul_smul, mul_smul, smul_comm a b x]
  rw [h, hax, hby, smul_zero, smul_zero, add_zero]

omit [IsDomain A] in
theorem smul_mem_torsionSet {M : Type*} [AddCommGroup M] [Module A M] (r : A) {x : M}
    (hx : x ∈ torsionSet A M) : r • x ∈ torsionSet A M := by
  obtain ⟨a, ha, hax⟩ := hx
  exact ⟨a, ha, by rw [smul_comm a r x, hax, smul_zero]⟩

end TorsionSet

/-- The torsion submodule `T(M)` of an `A`-module `M`: the submodule of torsion elements.
This is the first assertion of Exercise 3.12. -/
def torsionSubmodule (A : Type*) [CommRing A] [IsDomain A] (M : Type*) [AddCommGroup M]
    [Module A M] : Submodule A M where
  carrier := torsionSet A M
  zero_mem' := zero_mem_torsionSet
  add_mem' := fun hx hy => add_mem_torsionSet hx hy
  smul_mem' := fun r _ hx => smul_mem_torsionSet r hx

@[simp]
theorem mem_torsionSubmodule {M : Type*} [AddCommGroup M] [Module A M] {x : M} :
    x ∈ torsionSubmodule A M ↔ ∃ a : A, a ≠ 0 ∧ a • x = 0 :=
  Iff.rfl

/-- The book's definition of torsion element via annihilators: `x` is torsion iff the
annihilator ideal of `A ∙ x` is nonzero (it is the torsion ideal of `x`). -/
theorem mem_torsionSubmodule_iff_annihilator_ne_bot {M : Type*} [AddCommGroup M] [Module A M]
    (x : M) : x ∈ torsionSubmodule A M ↔ (Submodule.span A {x}).annihilator ≠ ⊥ := by
  rw [mem_torsionSubmodule, Submodule.annihilator_span_singleton, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, (Ideal.mem_torsionOf_iff x a).mpr hax, ha⟩
  · rintro ⟨a, ha, ha0⟩
    exact ⟨a, ha0, (Ideal.mem_torsionOf_iff x a).mp ha⟩

/-- The same statement in Mathlib's notation: `x` is a torsion element iff its torsion
ideal (the annihilator of `A ∙ x`) is nonzero, which is the book's condition `Ann(x) ≠ 0`. -/
theorem mem_torsionSubmodule_iff_torsionOf_ne_bot {M : Type*} [AddCommGroup M] [Module A M]
    (x : M) : x ∈ torsionSubmodule A M ↔ Ideal.torsionOf A M x ≠ ⊥ := by
  rw [mem_torsionSubmodule_iff_annihilator_ne_bot, Submodule.annihilator_span_singleton,
    Ideal.torsionOf]

/-- The book's torsion submodule is Mathlib's `Submodule.torsion`: over an integral domain
the nonzero elements are exactly the nonzero-divisors. -/
theorem torsionSubmodule_eq_torsion (M : Type*) [AddCommGroup M] [Module A M] :
    torsionSubmodule A M = Submodule.torsion A M := by
  ext x
  rw [mem_torsionSubmodule, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hax⟩
  · rintro ⟨a, hax⟩
    exact ⟨a.1, nonZeroDivisors.ne_zero a.2, hax⟩

/-! ## Part (i): the quotient by the torsion submodule is torsion-free -/

theorem torsionSubmodule_quotient_eq_bot (M : Type*) [AddCommGroup M] [Module A M] :
    torsionSubmodule A (M ⧸ torsionSubmodule A M) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨m⟩ ⟨a, ha, hax⟩
  have hax' : (torsionSubmodule A M).mkQ (a • m) = 0 := by
    rw [map_smul, Submodule.mkQ_apply]
    exact hax
  have h1 : a • m ∈ torsionSubmodule A M := by
    rw [← Submodule.ker_mkQ (torsionSubmodule A M), LinearMap.mem_ker]
    exact hax'
  obtain ⟨b, hb, hbm⟩ := mem_torsionSubmodule.mp h1
  have hm : m ∈ torsionSubmodule A M :=
    mem_torsionSubmodule.mpr
      ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr hm

/-- Part (i) stated in the book's terminology: `M ⧸ T(M)` is torsion-free. -/
theorem isTorsionFree_quotient (M : Type*) [AddCommGroup M] [Module A M] :
    Module.IsTorsionFree A (M ⧸ torsionSubmodule A M) := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, ← torsionSubmodule_eq_torsion]
  exact torsionSubmodule_quotient_eq_bot M

/-- The book's definition of torsion-freeness: `T(M) = 0` iff `M` is torsion-free. -/
theorem isTorsionFree_iff_torsionSubmodule_eq_bot (M : Type*) [AddCommGroup M] [Module A M] :
    Module.IsTorsionFree A M ↔ torsionSubmodule A M = ⊥ := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, ← torsionSubmodule_eq_torsion]

/-! ## Part (ii): torsion elements map to torsion elements -/

theorem map_torsionSubmodule_le {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    Submodule.map f (torsionSubmodule A M) ≤ torsionSubmodule A N := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hax⟩ := mem_torsionSubmodule.mp hx
  exact mem_torsionSubmodule.mpr ⟨a, ha, by rw [← map_smul, hax, map_zero]⟩

/-- Part (ii) elementwise: a module homomorphism maps torsion elements to torsion
elements. -/
theorem map_mem_torsionSubmodule {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) {x : M}
    (hx : x ∈ torsionSubmodule A M) : f x ∈ torsionSubmodule A N :=
  map_torsionSubmodule_le f (Submodule.mem_map_of_mem hx)

/-! ## Part (iii): exactness is inherited -/

/-- Restriction of a linear map to the torsion submodules; well defined by part (ii). -/
def torsionSubmoduleMap {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : M →ₗ[A] N) : torsionSubmodule A M →ₗ[A] torsionSubmodule A N :=
  ((f.comp (torsionSubmodule A M).subtype)).codRestrict (torsionSubmodule A N)
    fun x => map_torsionSubmodule_le f (Submodule.mem_map_of_mem x.2)

@[simp]
theorem torsionSubmoduleMap_apply {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : torsionSubmodule A M) :
    ((torsionSubmoduleMap f) x : N) = f x :=
  rfl

theorem torsionSubmoduleMap_injective {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Injective (torsionSubmoduleMap f) := by
  intro x y hxy
  refine Subtype.ext (hf ?_)
  exact congrArg Subtype.val hxy

theorem exact_torsionSubmoduleMap {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M''] (f : M' →ₗ[A] M)
    (g : M →ₗ[A] M'') (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (torsionSubmoduleMap f) (torsionSubmoduleMap g) := by
  intro x
  constructor
  · intro hx
    have hx0 : g x.1 = 0 := congrArg Subtype.val hx
    have hmem : x.1 ∈ LinearMap.range f := by
      rw [← LinearMap.exact_iff.mp hfg]
      exact hx0
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨a, ha, hax⟩ := mem_torsionSubmodule.mp x.2
    have hay : a • y = 0 := by
      apply hf
      rw [map_smul, hy, hax, map_zero]
    exact ⟨⟨y, mem_torsionSubmodule.mpr ⟨a, ha, hay⟩⟩, Subtype.ext (by simpa using hy)⟩
  · rintro ⟨y, rfl⟩
    have h0 : g (f y.1) = 0 := by
      have hmem : f y.1 ∈ LinearMap.range f := ⟨y.1, rfl⟩
      rw [← LinearMap.exact_iff.mp hfg] at hmem
      exact LinearMap.mem_ker.mp hmem
    exact Subtype.ext h0

/-! ## Part (iv): the torsion submodule as the kernel of `x ↦ 1 ⊗ x` -/

/-- If a nonzero `a` kills `x`, then `1 ⊗ x = 0` in `K ⊗[A] M`, since `a` is invertible in
the fraction field `K`. -/
theorem tmul_one_eq_zero_of_smul_eq_zero (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] {M : Type*} [AddCommGroup M] [Module A M] {x : M} {a : A}
    (ha : a ≠ 0) (hax : a • x = 0) : (1 : K) ⊗ₜ[A] x = 0 := by
  have h1 : (algebraMap A K a) • ((1 : K) ⊗ₜ[A] x) = 0 := by
    rw [IsScalarTower.algebraMap_smul]
    rw [← TensorProduct.tmul_smul a (1 : K) x, hax, TensorProduct.tmul_zero]
  have hne : algebraMap A K a ≠ 0 := by
    intro h
    exact ha (IsFractionRing.injective A K (by simpa using h))
  calc (1 : K) ⊗ₜ[A] x
      = (algebraMap A K a)⁻¹ • ((algebraMap A K a) • ((1 : K) ⊗ₜ[A] x)) :=
        (inv_smul_smul₀ hne _).symm
    _ = 0 := by rw [h1, smul_zero]

/-- The book's hint for part (iv), made precise: the field of fractions is the directed
union of its submodules `A · s⁻¹` (`s ≠ 0`). -/
theorem iSup_span_inv_eq_top (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    (⨆ s : nonZeroDivisors A, Submodule.span A ({(algebraMap A K (s : A))⁻¹} : Set K)) =
      ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) (S := K) z
  have hfs : algebraMap A K (s : A) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero s.2
      (IsFractionRing.injective A K (h.trans (map_zero _).symm))
  have hz : z = a • (algebraMap A K (s : A))⁻¹ := by
    calc z = z * algebraMap A K (s : A) * (algebraMap A K (s : A))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hfs, mul_one]
      _ = algebraMap A K a * (algebraMap A K (s : A))⁻¹ := by rw [hs]
      _ = a • (algebraMap A K (s : A))⁻¹ := (Algebra.smul_def a _).symm
  rw [hz]
  exact Submodule.mem_iSup_of_mem s
    (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _)))

/-- Conversely, if `1 ⊗ x = 0` in `K ⊗[A] M`, then some nonzero element of `A` kills `x`:
`x ↦ 1 ⊗ x` is a localization of `M` at the nonzero elements of `A`. -/
theorem exists_smul_eq_zero_of_tmul_one_eq_zero (K : Type*) [CommRing K] [Algebra A K]
    [IsFractionRing A K] {M : Type*} [AddCommGroup M] [Module A M] {x : M}
    (hx : (1 : K) ⊗ₜ[A] x = 0) : ∃ a : A, a ≠ 0 ∧ a • x = 0 := by
  have : IsLocalizedModule (nonZeroDivisors A) ((TensorProduct.mk A K M) (1 : K)) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors A) K
  have h0 : (TensorProduct.mk A K M) (1 : K) x = (TensorProduct.mk A K M) (1 : K) 0 := by
    rw [TensorProduct.mk_apply, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    exact hx
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A)
    ((TensorProduct.mk A K M) (1 : K))).mp h0
  refine ⟨(c : A), nonZeroDivisors.ne_zero c.2, ?_⟩
  rw [Submonoid.smul_def] at hc
  simpa using hc

/-- Part (iv) of Exercise 3.12: `T(M)` is the kernel of `x ↦ 1 ⊗ x : M → K ⊗[A] M`, for any
field of fractions `K` of `A`. -/
theorem torsionSubmodule_eq_ker_tmul_one (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type*) [AddCommGroup M] [Module A M] :
    torsionSubmodule A M = LinearMap.ker ((TensorProduct.mk A K M) (1 : K)) := by
  ext x
  rw [mem_torsionSubmodule, LinearMap.mem_ker, TensorProduct.mk_apply]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact tmul_one_eq_zero_of_smul_eq_zero K ha hax
  · intro hx
    exact exists_smul_eq_zero_of_tmul_one_eq_zero K hx

/-- Part (iv) elementwise: `x` is a torsion element iff `1 ⊗ x = 0`. -/
theorem mem_torsionSubmodule_iff_tmul_one_eq_zero (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] {M : Type*} [AddCommGroup M] [Module A M] (x : M) :
    x ∈ torsionSubmodule A M ↔ (1 : K) ⊗ₜ[A] x = 0 := by
  rw [torsionSubmodule_eq_ker_tmul_one K M, LinearMap.mem_ker, TensorProduct.mk_apply]

/-- Part (iv) in the book's formulation, with `K` the field of fractions of `A`. -/
theorem torsionSubmodule_eq_ker_tmul_one_fractionRing (M : Type*) [AddCommGroup M]
    [Module A M] :
    torsionSubmodule A M = LinearMap.ker ((TensorProduct.mk A (FractionRing A) M) 1) :=
  torsionSubmodule_eq_ker_tmul_one (FractionRing A) M

/-! ## The complete exercise -/

/-- Exercise 3.12 of Atiyah–Macdonald, all four parts, with every object universally
quantified. -/
theorem solution :
    (∀ (M : Type*) [AddCommGroup M] [Module A M],
        torsionSubmodule A (M ⧸ torsionSubmodule A M) = ⊥) ∧
      (∀ (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
        (f : M →ₗ[A] N), Submodule.map f (torsionSubmodule A M) ≤ torsionSubmodule A N) ∧
      (∀ (M' M M'' : Type*) [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
        [AddCommGroup M''] [Module A M''] (f : M' →ₗ[A] M) (g : M →ₗ[A] M''),
          Function.Injective f → Function.Exact f g →
            Function.Injective (torsionSubmoduleMap f) ∧
              Function.Exact (torsionSubmoduleMap f) (torsionSubmoduleMap g)) ∧
      (∀ (M : Type*) [AddCommGroup M] [Module A M],
        torsionSubmodule A M =
          LinearMap.ker ((TensorProduct.mk A (FractionRing A) M) 1)) :=
  ⟨fun M _ _ => torsionSubmodule_quotient_eq_bot M,
    fun _ _ _ _ _ _ f => map_torsionSubmodule_le f,
    fun _ _ _ _ _ _ _ _ _ f g hf hfg =>
      ⟨torsionSubmoduleMap_injective f hf, exact_torsionSubmoduleMap f g hf hfg⟩,
    fun M _ _ => torsionSubmodule_eq_ker_tmul_one_fractionRing M⟩

/-! ## Sanity checks: the definitions are not vacuous

`ℤ` is torsion-free as a module over itself, `ZMod 2` is entirely torsion, and part (iv)
detects this: `1 ⊗ 1` vanishes in `ℚ ⊗[ℤ] ZMod 2` but not in `ℚ ⊗[ℤ] ℤ`. -/

theorem torsionSubmodule_int_self : torsionSubmodule ℤ ℤ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := mem_torsionSubmodule.mp hx
  rw [smul_eq_mul] at hax
  exact (mul_eq_zero.mp hax).resolve_left ha

theorem torsionSubmodule_zmod_two : torsionSubmodule ℤ (ZMod 2) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  refine mem_torsionSubmodule.mpr ⟨2, by norm_num, ?_⟩
  rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 from ZMod.natCast_self 2]
  exact zero_mul x

theorem tmul_one_zmod_two : (1 : ℚ) ⊗ₜ[ℤ] (1 : ZMod 2) = 0 := by
  apply tmul_one_eq_zero_of_smul_eq_zero (K := ℚ) (a := 2) (x := (1 : ZMod 2))
  · norm_num
  · rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 from ZMod.natCast_self 2]
    exact zero_mul 1

theorem tmul_one_int_ne_zero : (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ) ≠ 0 := by
  intro h
  have hmem : (1 : ℤ) ∈ torsionSubmodule ℤ ℤ :=
    (mem_torsionSubmodule_iff_tmul_one_eq_zero ℚ 1).mpr h
  rw [torsionSubmodule_int_self] at hmem
  exact one_ne_zero hmem

/-! ## The integral-domain hypothesis is not redundant

If `A` has zero divisors, the torsion elements need not be closed under addition, so
"torsion elements form a submodule" genuinely needs `A` to be an integral domain.  For
`A = ℤ × ℤ` (a commutative ring with zero divisors), the elements `(1,0)` and `(0,1)` are
killed by the nonzero elements `(0,1)` and `(1,0)` respectively, but their sum `(1,1)` is
not killed by any nonzero element. -/

theorem torsionSet_add_not_mem_int_prod :
    ∃ x y : ℤ × ℤ,
      x ∈ torsionSet (ℤ × ℤ) (ℤ × ℤ) ∧ y ∈ torsionSet (ℤ × ℤ) (ℤ × ℤ) ∧
        x + y ∉ torsionSet (ℤ × ℤ) (ℤ × ℤ) := by
  refine ⟨(1, 0), (0, 1), ⟨(0, 1), by simp, ?_⟩, ⟨(1, 0), by simp, ?_⟩, ?_⟩
  · ext <;> simp
  · ext <;> simp
  · rintro ⟨⟨a, b⟩, hab, hsum⟩
    apply hab
    ext
    · simpa [Prod.smul_mk] using congrArg Prod.fst hsum
    · simpa [Prod.smul_mk] using congrArg Prod.snd hsum

end AtiyahMcdonald69.Ex_3_12

#print axioms AtiyahMcdonald69.Ex_3_12.solution
#print axioms AtiyahMcdonald69.Ex_3_12.torsionSubmodule_eq_ker_tmul_one
#print axioms AtiyahMcdonald69.Ex_3_12.exact_torsionSubmoduleMap
#print axioms AtiyahMcdonald69.Ex_3_12.torsionSubmodule_quotient_eq_bot
#print axioms AtiyahMcdonald69.Ex_3_12.map_torsionSubmodule_le
#print axioms AtiyahMcdonald69.Ex_3_12.isTorsionFree_quotient
#print axioms AtiyahMcdonald69.Ex_3_12.isTorsionFree_iff_torsionSubmodule_eq_bot
#print axioms AtiyahMcdonald69.Ex_3_12.torsionSubmodule_eq_torsion
#print axioms AtiyahMcdonald69.Ex_3_12.mem_torsionSubmodule_iff_tmul_one_eq_zero
#print axioms AtiyahMcdonald69.Ex_3_12.torsionSet_add_not_mem_int_prod
#print axioms AtiyahMcdonald69.Ex_3_12.tmul_one_int_ne_zero
#print axioms AtiyahMcdonald69.Ex_3_12.tmul_one_zmod_two
#print axioms AtiyahMcdonald69.Ex_3_12.iSup_span_inv_eq_top
