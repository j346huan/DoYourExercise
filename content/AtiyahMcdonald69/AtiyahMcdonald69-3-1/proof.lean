import Mathlib

/-
# Atiyah–Macdonald (1969), Chapter 3, Exercise 3.1

*Statement (book, Ch. 3, Exercise 1).* Let `S` be a multiplicatively closed subset of a
ring `A`, and let `M` be a finitely generated `A`-module. Prove that `S⁻¹M = 0` if and
only if there exists `s ∈ S` such that `sM = 0`.

The book's notation `S⁻¹M` is `LocalizedModule S M` here, and `sM = 0` means that the
scalar `s` annihilates every element of `M`.

The natural solution runs: if `sM = 0`, then every fraction `m/t` equals
`(s • m)/(s * t) = 0`. Conversely, if `S⁻¹M = 0` and `m₁,…,mₙ` generate `M`, choose
`sᵢ ∈ S` with `sᵢ mᵢ = 0`; then `s = ∏ sᵢ ∈ S` kills every generator, hence `sM = 0`.

In the formalisation the finiteness step is isolated as an abstract compactness statement
for a directed family of submodules indexed by a submonoid: a finitely generated submodule
of the directed union lies in one member. The localization side is done with the fraction
normal form `LocalizedModule.mk_eq`, which is exactly Atiyah–Macdonald's
"bring to a common denominator".
-/

namespace AtiyahMcdonald69.Ex_3_1

open Submodule

universe u v

section Compactness

variable {A : Type u} [CommSemiring A] {M : Type v} [AddCommMonoid M] [Module A M]

/-- **Compactness for a directed family of submodules indexed by a submonoid.**
If `K a ≤ K (b * a)` for all `a b : S`, then a finitely generated submodule of
`⨆ a, K a` is already contained in a single `K a`.

This is the abstract finite-generation principle behind Atiyah–Macdonald's Exercise 3.1:
only finitely many "witnesses" are needed, and they are combined using the multiplication
of the index monoid. -/
theorem Submodule.exists_le_of_fg_le_iSup {S : Submonoid A} {K : S → Submodule A M}
    (hK : ∀ a b : S, K a ≤ K (b * a)) (N : Submodule A M) (hN : N.FG)
    (h : N ≤ ⨆ s, K s) : ∃ s : S, N ≤ K s := by
  classical
  have hdir : Directed (· ≤ ·) K := fun a b =>
    ⟨a * b, by simpa [mul_comm] using hK a b, hK b a⟩
  -- a finite set of witnesses for a finite generating set
  have key : ∀ t : Finset M, (∀ m ∈ t, m ∈ N) → ∃ s : S, ∀ m ∈ t, m ∈ K s := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; exact ⟨1, by simp⟩
    | insert a t ha ih =>
      intro ht
      obtain ⟨s₁, hs₁⟩ := ih fun m hm => ht m (Finset.mem_insert_of_mem hm)
      obtain ⟨s₀, hs₀⟩ :=
        (Submodule.mem_iSup_of_directed K hdir).mp (h (ht a (Finset.mem_insert_self a t)))
      refine ⟨s₀ * s₁, ?_⟩
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · simpa [mul_comm] using hK s₀ s₁ hs₀
      · exact (hK s₁ s₀) (hs₁ m hm)
  obtain ⟨t, ht⟩ := hN
  obtain ⟨s, hs⟩ := key t fun m hm => ht ▸ subset_span hm
  refine ⟨s, ?_⟩
  rw [← ht]
  exact span_le.mpr hs

end Compactness

section Localization

variable {A : Type u} [CommRing A] {M : Type v} [AddCommMonoid M] [Module A M]

/-- The fraction `m / s` of `S⁻¹M` is zero exactly when some element of `S` kills `m`.
This is Atiyah–Macdonald's common-denominator computation. -/
theorem mk_eq_zero_iff {S : Submonoid A} (m : M) (s : S) :
    LocalizedModule.mk m s = 0 ↔ ∃ u ∈ S, u • m = 0 := by
  constructor
  · intro h
    rw [← LocalizedModule.zero_mk (S := S) (1 : S), LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨(u : A), u.2, by simpa [Submonoid.smul_def] using hu⟩
  · rintro ⟨u, huS, hu⟩
    rw [← LocalizedModule.zero_mk (S := S) (1 : S), LocalizedModule.mk_eq]
    exact ⟨⟨u, huS⟩, by rw [Submonoid.mk_smul, Submonoid.mk_smul]; simpa using hu⟩

/-- Elementwise criterion for the vanishing of `S⁻¹M`, valid for an arbitrary `A`-module
(no finite generation needed): the localized module is a subsingleton iff every element of
`M` is killed by some element of `S`. -/
theorem localizedModule_subsingleton_iff_forall_exists (S : Submonoid A) :
    Subsingleton (LocalizedModule S M) ↔ ∀ m : M, ∃ s ∈ S, s • m = 0 := by
  constructor
  · intro h m
    exact (mk_eq_zero_iff m 1).mp (Subsingleton.elim _ _)
  · rintro h
    refine ⟨fun x y => ?_⟩
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      induction y using LocalizedModule.induction_on with
      | _ m' s' =>
        have hx : LocalizedModule.mk m s = 0 := (mk_eq_zero_iff m s).mpr (h m)
        have hy : LocalizedModule.mk m' s' = 0 :=
          (mk_eq_zero_iff m' s').mpr (h m')
        rw [hx, hy]

/-- **The finiteness step of Exercise 3.1.** If every element of a finitely generated
module is killed by some element of `S`, then a single element of `S` kills the whole
module: the kernels of the scalars from `S` form a directed family of submodules indexed by
the submonoid `S`, and `M` is finitely generated. -/
theorem exists_smul_eq_zero_of_finite (S : Submonoid A) [Module.Finite A M]
    (h : ∀ m : M, ∃ s ∈ S, s • m = 0) : ∃ s ∈ S, ∀ m : M, s • m = 0 := by
  classical
  have hK : ∀ a b : S,
      LinearMap.ker (LinearMap.lsmul A M (a : A)) ≤ LinearMap.ker (LinearMap.lsmul A M (b * a : A)) :=
    fun a b m hm => by
      rw [LinearMap.mem_ker] at hm ⊢
      rw [LinearMap.lsmul_apply] at hm ⊢
      rw [mul_smul, hm, smul_zero]
  have hle : (⊤ : Submodule A M) ≤ ⨆ s : S, LinearMap.ker (LinearMap.lsmul A M (s : A)) := by
    intro m _
    rw [Submodule.mem_iSup_of_directed _ (fun a b =>
      ⟨a * b, by simpa [mul_comm] using hK a b, hK b a⟩)]
    obtain ⟨s, hs, hsm⟩ := h m
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply]
    simpa using hsm
  obtain ⟨s, hs⟩ :=
    Submodule.exists_le_of_fg_le_iSup (K := fun s : S => LinearMap.ker (LinearMap.lsmul A M (s : A)))
      hK ⊤ Module.Finite.fg_top hle
  exact ⟨s, s.2, fun m => by
    have := hs (Submodule.mem_top : m ∈ (⊤ : Submodule A M))
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at this
    exact this⟩

/-- **The converse direction of Exercise 3.1** (no finiteness needed): if `s ∈ S` annihilates
`M`, then `S⁻¹M = 0`; indeed `m / t = (s • m) / (s * t) = 0`. -/
theorem subsingleton_of_exists_smul_eq_zero (S : Submonoid A) {s : A} (hs : s ∈ S)
    (h : ∀ m : M, s • m = 0) : Subsingleton (LocalizedModule S M) :=
  (localizedModule_subsingleton_iff_forall_exists S).mpr fun m => ⟨s, hs, h m⟩

/-- **Atiyah–Macdonald (1969), Chapter 3, Exercise 3.1.** For a multiplicatively closed
subset `S` of a ring `A` and a finitely generated `A`-module `M`, the localized module
`S⁻¹M` vanishes if and only if some `s ∈ S` annihilates `M`. -/
theorem solution (S : Submonoid A) [Module.Finite A M] :
    Subsingleton (LocalizedModule S M) ↔ ∃ s ∈ S, ∀ m : M, s • m = 0 :=
  ⟨fun h =>
      exists_smul_eq_zero_of_finite S ((localizedModule_subsingleton_iff_forall_exists S).mp h),
    fun ⟨_, hs, h⟩ => subsingleton_of_exists_smul_eq_zero S hs h⟩

/-- The scalar-multiplication submodule `sM` is zero exactly when `s` annihilates `M`. -/
theorem smul_top_eq_bot_iff (s : A) :
    Ideal.span {s} • (⊤ : Submodule A M) = ⊥ ↔ ∀ m : M, s • m = 0 := by
  constructor
  · intro h m
    have hm : s • m ∈ Ideal.span {s} • (⊤ : Submodule A M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self s) Submodule.mem_top
    rw [h] at hm
    simpa using hm
  · intro h
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr m _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [mul_comm, ← smul_smul, h m, smul_zero]
    exact Submodule.zero_mem _

/-- **Exercise 3.1 in the book's own notation**: `S⁻¹M = 0` if and only if `sM = 0` for
some `s ∈ S`, where `sM = 0` is read as the vanishing of the submodule `sM ⊆ M`. -/
theorem solution' (S : Submonoid A) [Module.Finite A M] :
    Subsingleton (LocalizedModule S M) ↔ ∃ s ∈ S, Ideal.span {s} • (⊤ : Submodule A M) = ⊥ := by
  rw [solution S]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (smul_top_eq_bot_iff s).mpr h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (smul_top_eq_bot_iff s).mp h⟩

end Localization

end AtiyahMcdonald69.Ex_3_1

/-
## Audit of the statement and of the natural solution

The exercise is printed in Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 3 (`Rings and Modules of Fractions`), Exercises, number 1:

> Let `A` be a ring, `S` a multiplicatively closed subset of `A`, and let `M` be a finitely
> generated `A`-module. Prove that `S⁻¹M = 0` if and only if there exists `s ∈ S` such that
> `sM = 0`.

No hypothesis is omitted in the formal statement below: `S` is a `Submonoid A` and `M`
carries `Module.Finite A M`.  Nothing else is used — in particular `A` need not be
Noetherian, `S` need not be saturated (compare Exercise 3.7), and `A` need not be a domain.

Finite generation is essential, and only in the direction `S⁻¹M = 0 → ∃ s ∈ S, s • M = 0`:
the converse holds for an arbitrary module (`subsingleton_of_exists_smul_eq_zero`).
Without finite generation the statement fails: take `A = ℤ`, `S = ℤ ∖ {0}` and
`M = ⨁_p ℤ/pℤ`, the direct sum over all primes `p`.  Since `ℚ ⊗_ℤ ℤ/pℤ = 0` for every
prime `p`, the elementwise criterion `localizedModule_subsingleton_iff_forall_exists`
(each single element of `M` is killed by some nonzero integer, namely by the product of the
primes occurring in its finite support) gives `S⁻¹M = 0`; but no nonzero integer `s`
satisfies `s • M = 0`, because `s` does not annihilate the summand `ℤ/pℤ` for any prime
`p ∤ s`.  The same phenomenon appears for `A = ℤ`, `S = {2ⁿ : n ∈ ℕ}` and
`M = ℤ[1/2]/ℤ`: every element is `2`-power torsion, so the localization vanishes, while no
single `2ⁿ` annihilates the whole group.

`Subsingleton (LocalizedModule S M)` is the formal reading of `S⁻¹M = 0`: the localized
module is an `A`-module, so `Subsingleton` is equivalent to it being a zero object.

The natural solution's finiteness step ("choose `sᵢ ∈ S` with `sᵢ mᵢ = 0` for a finite
generating set, then `s = ∏ sᵢ` kills `M`") is isolated above as
`Submodule.exists_le_of_fg_le_iSup`: the kernels of the scalars from `S` form a directed
family of submodules indexed by the multiplicative monoid `S`, and a finitely generated
submodule of such a directed union already lies in a single member, the product being
formed in `S`.
-/

#print axioms AtiyahMcdonald69.Ex_3_1.Submodule.exists_le_of_fg_le_iSup
#print axioms AtiyahMcdonald69.Ex_3_1.mk_eq_zero_iff
#print axioms AtiyahMcdonald69.Ex_3_1.localizedModule_subsingleton_iff_forall_exists
#print axioms AtiyahMcdonald69.Ex_3_1.exists_smul_eq_zero_of_finite
#print axioms AtiyahMcdonald69.Ex_3_1.subsingleton_of_exists_smul_eq_zero
#print axioms AtiyahMcdonald69.Ex_3_1.smul_top_eq_bot_iff
#print axioms AtiyahMcdonald69.Ex_3_1.solution
#print axioms AtiyahMcdonald69.Ex_3_1.solution'
