/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 3.16

The book's statement (Chapter 3, "Rings and Modules of Fractions", exercise 16):

Let `B` be a flat `A`-algebra. Then the following conditions are equivalent:
  i)   `𝔞ᵉᶜ = 𝔞` for all ideals `𝔞` of `A`;
  ii)  `Spec(B) → Spec(A)` is surjective;
  iii) for every maximal ideal `𝔪` of `A` we have `𝔪ᵉ ≠ (1)`;
  iv)  if `M` is any non-zero `A`-module, then `M_B ≠ 0`;
  v)   for every `A`-module `M`, the mapping `x ↦ 1 ⊗ x` of `M` into `M_B = B ⊗[A] M` is injective.

Such a `B` is then said to be *faithfully flat* over `A`.

Here `M_B := B ⊗[A] M`, `𝔞ᵉ = 𝔞B` is the extension of `𝔞` to `B` and `𝔞ᶜ` its contraction.

The file formalizes the five conditions (`CondI` … `CondV`) and proves the cycle of
implications i) ⇒ ii) ⇒ iii) ⇒ iv) ⇒ v) ⇒ i) that the book's proof describes, whence the
equivalence; a last section identifies condition iii) with Mathlib's `Module.FaithfullyFlat`.

Everything is stated for a commutative ring `A`, a commutative ring `B` and an `Algebra A B`;
the only extra hypothesis is `Module.Flat A B` (flatness of `B` as an `A`-module).  All modules
in conditions (iv) and (v) live in the same universe as `A` and `B`; the statements are
universe-polymorphic in that level.
-/

import Mathlib

namespace AtiyahMcdonald69.Ex_3_16

universe u

open TensorProduct

/-! ### The five conditions -/

section Conditions

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- (i) Every ideal of `A` is the contraction of its extension to `B`: `𝔞ᵉᶜ = 𝔞`. -/
def CondI : Prop :=
  ∀ I : Ideal A, Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) I) = I

/-- (ii) The map `Spec B → Spec A` is surjective. -/
def CondII : Prop :=
  Function.Surjective (PrimeSpectrum.comap (algebraMap A B))

/-- (iii) For every maximal ideal `𝔪` of `A`, `𝔪ᵉ ≠ (1)`. -/
def CondIII : Prop :=
  ∀ m : Ideal A, m.IsMaximal → Ideal.map (algebraMap A B) m ≠ ⊤

/-- (iv) For every non-zero `A`-module `M`, the base change `M_B = B ⊗[A] M` is non-zero. -/
def CondIV : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Nontrivial M → Nontrivial (B ⊗[A] M)

/-- (v) For every `A`-module `M`, the natural map `x ↦ 1 ⊗ x : M → M_B` is injective. -/
def CondV : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Function.Injective (TensorProduct.mk A B M 1)

end Conditions

/-! ### (ii) in terms of contractions of primes

The book phrases (ii) as surjectivity of `Spec B → Spec A`; the equivalent pointwise form
"every prime of `A` is the contraction of a prime of `B`" is recorded here as well. -/

section Pointwise

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Condition (ii) is equivalent to: every prime ideal of `A` is the contraction of a prime
ideal of `B`. -/
theorem condII_iff_forall_exists :
    CondII A B ↔
      ∀ p : Ideal A, p.IsPrime → ∃ q : Ideal B, q.IsPrime ∧ Ideal.comap (algebraMap A B) q = p := by
  constructor
  · intro h p hp
    obtain ⟨q, hq⟩ := h ⟨p, hp⟩
    exact ⟨q.asIdeal, q.isPrime, by rw [← PrimeSpectrum.comap_asIdeal, hq]⟩
  · intro h p
    obtain ⟨q, hq, hqp⟩ := h p.asIdeal p.isPrime
    have hqtop : q ≠ ⊤ := by
      intro htop
      rw [htop, Ideal.comap_top] at hqp
      exact p.isPrime.ne_top hqp.symm
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext (by rw [PrimeSpectrum.comap_asIdeal]; exact hqp)⟩

end Pointwise

/-! ### The cycle of implications -/

section Cycle

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- (i) ⇒ (ii): if every ideal of `A` is contracted from `B`, then every prime of `A` is the
contraction of a prime of `B`, i.e. `Spec B → Spec A` is surjective. -/
theorem cond_i_imp_cond_ii (h : CondI A B) : CondII A B := fun p =>
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr (h p.asIdeal)

/-- (ii) ⇒ (iii): a maximal ideal `𝔪` is the contraction of a prime `𝔮` of `B`, so that
`𝔪ᵉ ⊆ 𝔮 ≠ (1)`. -/
theorem cond_ii_imp_cond_iii (h : CondII A B) : CondIII A B := by
  intro m hm htop
  obtain ⟨q, hq⟩ := h ⟨m, hm.isPrime⟩
  have hmq : m = Ideal.comap (algebraMap A B) q.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) q, hq]
  have hle : Ideal.map (algebraMap A B) m ≤ q.asIdeal := by
    rw [hmq]
    exact Ideal.map_comap_le
  exact q.isPrime.ne_top (top_le_iff.mp (htop ▸ hle))

/-- (iii) ⇒ (iv): if `0 ≠ x ∈ M`, then `Ax ≅ A ⧸ 𝔞` with `𝔞 = Ann(x)` proper.  Pick a maximal
ideal `𝔪 ⊇ 𝔞`.  Then `B ⊗[A] (Ax) ≅ B ⧸ 𝔞B ≠ 0` because `𝔞B ⊆ 𝔪B ≠ (1)`, and flatness
embeds `(Ax) ⊗[A] B` into `M ⊗[A] B`, hence `B ⊗[A] (Ax)` into `B ⊗[A] M`. -/
theorem cond_iii_imp_cond_iv [Module.Flat A B] (h : CondIII A B) : CondIV A B := by
  intro M _ _ hM
  obtain ⟨x, hx⟩ := nontrivial_iff_exists_ne (0 : M) |>.mp hM
  -- the cyclic submodule `Ax`, exhibited as a quotient of `A`
  let f : A →ₗ[A] M := LinearMap.toSpanSingleton A M x
  let a : Ideal A := LinearMap.ker f
  -- `𝔞 = Ann(x)` is a proper ideal
  have ha : a ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ a := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, show f 1 = x from LinearMap.toSpanSingleton_apply_one A M x] at h1
    exact hx h1
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal a ha
  -- `𝔞B ≠ (1)` because `𝔞B ⊆ 𝔪B ≠ (1)`
  have haB : Ideal.map (algebraMap A B) a ≠ ⊤ := fun htop =>
    h m hm (top_le_iff.mp (htop ▸ Ideal.map_mono ham))
  -- `B ⊗[A] A ⧸ 𝔞 ≅ B ⧸ 𝔞B` is non-zero
  have hquot : Nontrivial (B ⧸ Ideal.map (algebraMap A B) a) :=
    Ideal.Quotient.nontrivial_iff.mpr haB
  have htens : Nontrivial (B ⊗[A] (A ⧸ a)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B a).symm.toEquiv.nontrivial
  -- so is `Ax ⊗[A] B`
  have hcyc : Nontrivial (LinearMap.range f ⊗[A] B) := by
    have h1 : Nontrivial ((A ⧸ a) ⊗[A] B) :=
      (TensorProduct.comm A B (A ⧸ a)).toEquiv.symm.nontrivial
    exact (TensorProduct.congr f.quotKerEquivRange (LinearEquiv.refl A B)).toEquiv.symm.nontrivial
  -- flatness embeds `Ax ⊗[A] B` into `M ⊗[A] B`
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.range f).subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hMB : Nontrivial (M ⊗[A] B) := hinj.nontrivial
  exact (TensorProduct.comm A M B).toEquiv.symm.nontrivial

/-- (iv) ⇒ (v): let `N` be the kernel of `x ↦ 1 ⊗ x`.  By flatness `B ⊗[A] N → B ⊗[A] M` is
injective, and it is the zero map because `1 ⊗ n = 0` and `b ⊗ n = b • (1 ⊗ n)` for `n ∈ N`.
Hence `B ⊗[A] N = 0`, so `N = 0` by (iv). -/
theorem cond_iv_imp_cond_v [Module.Flat A B] (h : CondIV A B) : CondV A B := by
  intro M _ _
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro n hn
  by_contra hn0
  -- `N = ker (1 ⊗ ·)` is non-trivial
  have hN : Nontrivial ↥(LinearMap.ker (TensorProduct.mk A B M 1)) :=
    nontrivial_iff_exists_ne (0 : ↥(LinearMap.ker (TensorProduct.mk A B M 1))) |>.mpr
      ⟨⟨n, hn⟩, fun h0 => hn0 (congrArg Subtype.val h0)⟩
  -- hence `B ⊗[A] N` is non-trivial by (iv)
  have hBN : Nontrivial (B ⊗[A] ↥(LinearMap.ker (TensorProduct.mk A B M 1))) := h _ hN
  -- but `B ⊗[A] N → B ⊗[A] M` is the zero map
  have hzero : LinearMap.lTensor B (LinearMap.ker (TensorProduct.mk A B M 1)).subtype = 0 := by
    refine TensorProduct.ext' fun b y => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.zero_apply]
    have hy : (1 : B) ⊗ₜ[A] (y : M) = 0 := y.2
    calc b ⊗ₜ[A] (y : M) = b • ((1 : B) ⊗ₜ[A] (y : M)) := by
          rw [TensorProduct.smul_tmul']
          simp
      _ = 0 := by rw [hy, smul_zero]
  -- flatness makes that map injective, so `B ⊗[A] N` is trivial
  have hinj :
      Function.Injective (LinearMap.lTensor B (LinearMap.ker (TensorProduct.mk A B M 1)).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hsub : Subsingleton (B ⊗[A] ↥(LinearMap.ker (TensorProduct.mk A B M 1))) := by
    rw [subsingleton_iff_forall_eq 0]
    intro z
    apply hinj
    rw [hzero]
    simp
  exact not_subsingleton_iff_nontrivial.mpr hBN hsub

/-- (v) ⇒ (i): apply (v) to `A ⧸ 𝔞`.  The composite `A ⧸ 𝔞 → B ⊗[A] (A ⧸ 𝔞) ≅ B ⧸ 𝔞B` is
injective, and its kernel is `𝔞ᵉᶜ ⧸ 𝔞`. -/
theorem cond_v_imp_cond_i (h : CondV A B) : CondI A B := by
  intro I
  refine le_antisymm ?_ Ideal.le_comap_map
  have inj : Function.Injective
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars A ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp, AlgEquiv.toLinearMap, ← LinearEquiv.restrictScalars_toLinearMap]
    exact (LinearEquiv.injective _).comp (h (A ⧸ I))
  intro x hx
  rw [Ideal.mem_comap] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply inj
  have h0 : ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
    simp [← Algebra.algebraMap_eq_smul_one, hx]
  simp [h0]

end Cycle

/-! ### The equivalence of the five conditions

Each condition is derived from the previous one in the cycle; the backward implications are
compositions along the cycle. -/

section Equivalence

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- (i) ⇒ (iii), through condition (ii). -/
theorem cond_i_imp_cond_iii [Module.Flat A B] (h : CondI A B) : CondIII A B :=
  cond_ii_imp_cond_iii (cond_i_imp_cond_ii h)

/-- (i) ⇒ (iv), through conditions (ii) and (iii). -/
theorem cond_i_imp_cond_iv [Module.Flat A B] (h : CondI A B) : CondIV A B :=
  cond_iii_imp_cond_iv (cond_i_imp_cond_iii h)

/-- (i) ⇒ (v), through conditions (ii), (iii) and (iv). -/
theorem cond_i_imp_cond_v [Module.Flat A B] (h : CondI A B) : CondV A B :=
  cond_iv_imp_cond_v (cond_i_imp_cond_iv h)

/-- (ii) ⇒ (i), through conditions (iii), (iv) and (v). -/
theorem cond_ii_imp_cond_i [Module.Flat A B] (h : CondII A B) : CondI A B :=
  cond_v_imp_cond_i (cond_iv_imp_cond_v (cond_iii_imp_cond_iv (cond_ii_imp_cond_iii h)))

/-- (iii) ⇒ (i), through conditions (iv) and (v). -/
theorem cond_iii_imp_cond_i [Module.Flat A B] (h : CondIII A B) : CondI A B :=
  cond_v_imp_cond_i (cond_iv_imp_cond_v (cond_iii_imp_cond_iv h))

/-- (iii) ⇒ (ii), through conditions (iv), (v) and (i). -/
theorem cond_iii_imp_cond_ii [Module.Flat A B] (h : CondIII A B) : CondII A B :=
  cond_i_imp_cond_ii (cond_iii_imp_cond_i h)

/-- (iii) ⇒ (v), through condition (iv). -/
theorem cond_iii_imp_cond_v [Module.Flat A B] (h : CondIII A B) : CondV A B :=
  cond_iv_imp_cond_v (cond_iii_imp_cond_iv h)

/-- (iv) ⇒ (i), through condition (v). -/
theorem cond_iv_imp_cond_i [Module.Flat A B] (h : CondIV A B) : CondI A B :=
  cond_v_imp_cond_i (cond_iv_imp_cond_v h)

/-- (iv) ⇒ (ii), through conditions (v) and (i). -/
theorem cond_iv_imp_cond_ii [Module.Flat A B] (h : CondIV A B) : CondII A B :=
  cond_i_imp_cond_ii (cond_iv_imp_cond_i h)

/-- (iv) ⇒ (iii), through conditions (v), (i) and (ii). -/
theorem cond_iv_imp_cond_iii [Module.Flat A B] (h : CondIV A B) : CondIII A B :=
  cond_i_imp_cond_iii (cond_iv_imp_cond_i h)

/-- (v) ⇒ (ii), through condition (i). -/
theorem cond_v_imp_cond_ii [Module.Flat A B] (h : CondV A B) : CondII A B :=
  cond_i_imp_cond_ii (cond_v_imp_cond_i h)

/-- (v) ⇒ (iii), through conditions (i) and (ii). -/
theorem cond_v_imp_cond_iii [Module.Flat A B] (h : CondV A B) : CondIII A B :=
  cond_i_imp_cond_iii (cond_v_imp_cond_i h)

/-- (v) ⇒ (iv), through conditions (i), (ii) and (iii). -/
theorem cond_v_imp_cond_iv [Module.Flat A B] (h : CondV A B) : CondIV A B :=
  cond_i_imp_cond_iv (cond_v_imp_cond_i h)

/-- Condition (i) implies all the others. -/
theorem cond_i_imp_all [Module.Flat A B] (h : CondI A B) :
    CondII A B ∧ CondIII A B ∧ CondIV A B ∧ CondV A B :=
  ⟨cond_i_imp_cond_ii h, cond_i_imp_cond_iii h, cond_i_imp_cond_iv h, cond_i_imp_cond_v h⟩

/-- **Atiyah–Macdonald, Exercise 3.16.** Let `B` be a flat `A`-algebra.  Condition (i) is
equivalent to the conjunction of conditions (ii)–(v). -/
theorem cond_i_iff_all [Module.Flat A B] :
    CondI A B ↔ CondII A B ∧ CondIII A B ∧ CondIV A B ∧ CondV A B :=
  ⟨cond_i_imp_all, fun h => cond_v_imp_cond_i h.2.2.2⟩

/-- **Atiyah–Macdonald, Exercise 3.16.** Let `B` be a flat `A`-algebra.  Then the five
conditions (i)–(v) are equivalent. -/
theorem solution [Module.Flat A B] :
    (CondI A B ↔ CondII A B) ∧ (CondII A B ↔ CondIII A B) ∧
      (CondIII A B ↔ CondIV A B) ∧ (CondIV A B ↔ CondV A B) ∧ (CondV A B ↔ CondI A B) :=
  ⟨⟨cond_i_imp_cond_ii, cond_ii_imp_cond_i⟩,
   ⟨cond_ii_imp_cond_iii, cond_iii_imp_cond_ii⟩,
   ⟨cond_iii_imp_cond_iv, cond_iv_imp_cond_iii⟩,
   ⟨cond_iv_imp_cond_v, cond_v_imp_cond_iv⟩,
   ⟨cond_v_imp_cond_i, cond_i_imp_cond_v⟩⟩

/-- Any one of the five conditions implies all of them (for a flat `A`-algebra `B`). -/
theorem all_of_cond_i [Module.Flat A B] (h : CondI A B) :
    CondI A B ∧ CondII A B ∧ CondIII A B ∧ CondIV A B ∧ CondV A B :=
  ⟨h, cond_i_imp_cond_ii h, cond_i_imp_cond_iii h, cond_i_imp_cond_iv h, cond_i_imp_cond_v h⟩

/-- **Atiyah–Macdonald, Exercise 3.16** (all pairwise implications).  For a flat `A`-algebra
`B` any one of the five conditions implies all the others. -/
theorem all_imp [Module.Flat A B]
    (h : CondI A B ∨ CondII A B ∨ CondIII A B ∨ CondIV A B ∨ CondV A B) :
    CondI A B ∧ CondII A B ∧ CondIII A B ∧ CondIV A B ∧ CondV A B := by
  obtain (h | h | h | h | h) := h
  · exact all_of_cond_i h
  · exact all_of_cond_i (cond_ii_imp_cond_i h)
  · exact all_of_cond_i (cond_iii_imp_cond_i h)
  · exact all_of_cond_i (cond_iv_imp_cond_i h)
  · exact all_of_cond_i (cond_v_imp_cond_i h)

/-- **Atiyah–Macdonald, Exercise 3.16** in `List.TFAE` form: for a flat `A`-algebra `B`,
the five conditions are equivalent. -/
theorem solution_tfae [Module.Flat A B] :
    List.TFAE [CondI A B, CondII A B, CondIII A B, CondIV A B, CondV A B] := by
  tfae_have 1 → 2 := cond_i_imp_cond_ii
  tfae_have 2 → 3 := cond_ii_imp_cond_iii
  tfae_have 3 → 4 := cond_iii_imp_cond_iv
  tfae_have 4 → 5 := cond_iv_imp_cond_v
  tfae_have 5 → 1 := cond_v_imp_cond_i
  tfae_finish

end Equivalence

/-! ### Faithful flatness

The book concludes: "`B` is said to be faithfully flat over `A`".  We relate condition (iii)
to Mathlib's class `Module.FaithfullyFlat`, whose definition is flatness together with
(iii) (phrased as `𝔪 • ⊤ ≠ ⊤` for maximal ideals `𝔪`). -/

section FaithfullyFlat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- For a flat `A`-algebra `B`, condition (iii) is faithful flatness of `B` over `A`. -/
theorem cond_iii_iff_faithfullyFlat [Module.Flat A B] :
    Module.FaithfullyFlat A B ↔ CondIII A B := by
  constructor
  · intro h m hm htop
    apply h.submodule_ne_top hm
    rw [Ideal.smul_top_eq_map, htop, Submodule.restrictScalars_top]
  · intro h
    refine ⟨fun m hm => ?_⟩
    intro htop
    apply h m hm
    have h1 : Submodule.restrictScalars A (Ideal.map (algebraMap A B) m) = ⊤ := by
      rw [← Ideal.smul_top_eq_map]
      exact htop
    exact (Submodule.restrictScalars_eq_top_iff A B B).mp h1

/-- **Atiyah–Macdonald, Exercise 3.16** (faithful flatness).  For a flat `A`-algebra `B`,
faithful flatness is equivalent to each of the five conditions. -/
theorem faithfullyFlat_iff_all [Module.Flat A B] :
    Module.FaithfullyFlat A B ↔
      CondI A B ∧ CondII A B ∧ CondIII A B ∧ CondIV A B ∧ CondV A B := by
  rw [cond_iii_iff_faithfullyFlat]
  exact ⟨fun h => ⟨cond_iii_imp_cond_i h, cond_iii_imp_cond_ii h, h, cond_iii_imp_cond_iv h,
      cond_iii_imp_cond_v h⟩, fun h => h.2.2.1⟩

end FaithfullyFlat


/-! ### Examples

The conditions are not vacuous, and flatness alone is not enough.

* `ℤ[X]` is faithfully flat over `ℤ`, so all five conditions hold;
* `ℚ` is flat over `ℤ`, but `(2)ᵉᶜ = ℤ ≠ (2)` in `ℚ`, so condition (i) fails — hence, since
  the five conditions are equivalent, (ii)–(v) fail as well (the book's conclusion: `B` has to
  be *faithfully* flat, not merely flat). -/

section Examples

/-- `ℤ[X]` is faithfully flat over `ℤ`, hence satisfies all five conditions of the exercise. -/
theorem example_polynomial :
    CondI ℤ (Polynomial ℤ) ∧ CondII ℤ (Polynomial ℤ) ∧ CondIII ℤ (Polynomial ℤ) ∧
      CondIV ℤ (Polynomial ℤ) ∧ CondV ℤ (Polynomial ℤ) :=
  all_of_cond_i
    (cond_iii_imp_cond_i (cond_iii_iff_faithfullyFlat.mp (inferInstance : Module.FaithfullyFlat ℤ (Polynomial ℤ))))

/-- `ℚ` is flat over `ℤ`, but `(2)ᵉᶜ = ℤ ≠ (2)` in `ℚ`: condition (i) fails. -/
theorem not_condI_int_rat : ¬ CondI ℤ ℚ := by
  intro h
  have h2 : (2 : ℚ) ∈ Ideal.map (algebraMap ℤ ℚ) (Ideal.span {(2 : ℤ)}) := by
    have h' := Ideal.mem_map_of_mem (algebraMap ℤ ℚ) (Ideal.subset_span (Set.mem_singleton (2 : ℤ)))
    simpa using h'
  have h1 : (1 : ℚ) ∈ Ideal.map (algebraMap ℤ ℚ) (Ideal.span {(2 : ℤ)}) := by
    have h' := Ideal.mul_mem_left (Ideal.map (algebraMap ℤ ℚ) (Ideal.span {(2 : ℤ)})) (1 / 2 : ℚ) h2
    simpa using h'
  have hmem : (1 : ℤ) ∈
      Ideal.comap (algebraMap ℤ ℚ) (Ideal.map (algebraMap ℤ ℚ) (Ideal.span {(2 : ℤ)})) := by
    rw [Ideal.mem_comap]
    simpa using h1
  rw [h (Ideal.span {(2 : ℤ)}), Ideal.mem_span_singleton] at hmem
  norm_num at hmem

/-- For `ℚ` over `ℤ` condition (iv) fails as well. -/
theorem not_condIV_int_rat : ¬ CondIV ℤ ℚ := fun h => not_condI_int_rat (cond_iv_imp_cond_i h)

/-- For `ℚ` over `ℤ` condition (v) fails: `(1 : ℤ/2ℤ) ⊗ 1 = 0` in `ℚ ⊗[ℤ] (ℤ/2ℤ)`. -/
theorem not_condV_int_rat : ¬ CondV ℤ ℚ := fun h => not_condI_int_rat (cond_v_imp_cond_i h)

end Examples

end AtiyahMcdonald69.Ex_3_16
