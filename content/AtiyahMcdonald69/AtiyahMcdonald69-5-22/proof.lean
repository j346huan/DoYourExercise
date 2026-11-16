import Mathlib
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open Ideal Polynomial

namespace AtiyahMcdonald69.Ex_5_22

noncomputable abbrev genLoc (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Type _ :=
  Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))

lemma genLoc_sub_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
  rw [Algebra.algebraMapSubmonoid]
  exact map_le_nonZeroDivisors_of_injective _ hinj le_rfl

lemma genLoc_finiteType {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) :
    Algebra.FiniteType (FractionRing A) (genLoc A B) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  refine ⟨s.image (algebraMap B (genLoc A B)), ?_⟩
  set C := genLoc A B with hC
  have hT : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B :=
    genLoc_sub_le hinj
  haveI : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  set S' : Subalgebra (FractionRing A) C :=
    Algebra.adjoin (FractionRing A) ((s.image (algebraMap B C) : Finset C) : Set C) with hS'
  have hmem : ∀ x ∈ s, algebraMap B C x ∈ S' := fun x hx =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  have hgen : ∀ x : B, algebraMap B C x ∈ S' := by
    intro x
    have hx : x ∈ Algebra.adjoin A (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact hmem y hy
    | algebraMap r =>
        have h : algebraMap B C (algebraMap A B r) =
            algebraMap (FractionRing A) C (algebraMap A (FractionRing A) r) := by
          rw [← IsScalarTower.algebraMap_apply A B C,
            ← IsScalarTower.algebraMap_apply A (FractionRing A) C]
        rw [h]; exact S'.algebraMap_mem _
    | add u v _ _ hu hv => rw [map_add]; exact S'.add_mem hu hv
    | mul u v _ _ hu hv => rw [map_mul]; exact S'.mul_mem hu hv
  have hkey : ∀ a ∈ nonZeroDivisors A,
      algebraMap B C (algebraMap A B a) =
        algebraMap (FractionRing A) C (algebraMap A (FractionRing A) a) := by
    intro a _
    rw [← IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply A (FractionRing A) C]
  have hinv : ∀ (a : A) (ha : a ∈ nonZeroDivisors A),
      ∃ u ∈ S', u * algebraMap B C (algebraMap A B a) = 1 := by
    intro a ha
    have hKa : algebraMap A (FractionRing A) a ≠ 0 := by
      intro h
      exact (nonZeroDivisors.ne_zero ha) (IsFractionRing.injective A (FractionRing A) (by simpa using h))
    refine ⟨algebraMap (FractionRing A) C ((algebraMap A (FractionRing A) a)⁻¹), S'.algebraMap_mem _, ?_⟩
    rw [hkey a ha, ← map_mul, inv_mul_cancel₀ hKa, map_one]
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, t⟩, ht⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) z
  obtain ⟨a, ha, hta⟩ := t.2
  obtain ⟨u, huS, hu⟩ := hinv a ha
  have hz : z = algebraMap B C x * u := by
    have h1 : z * algebraMap B C (algebraMap A B a) = algebraMap B C x := by
      rw [← hta] at ht
      exact ht
    have hu' : algebraMap B C (algebraMap A B a) * u = 1 := by rw [mul_comm]; exact hu
    calc z = z * 1 := (mul_one z).symm
      _ = z * (algebraMap B C (algebraMap A B a) * u) := by rw [hu']
      _ = (z * algebraMap B C (algebraMap A B a)) * u := by rw [mul_assoc]
      _ = algebraMap B C x * u := by rw [h1]
  rw [hz]
  exact S'.mul_mem (hgen x) huS

end AtiyahMcdonald69.Ex_5_22

namespace AtiyahMcdonald69.Ex_5_22

theorem exists_isMaximal_not_mem {R : Type*} [CommRing R] [Nontrivial R] {x : R}
    (hx : x ∉ jacobson (⊥ : Ideal R)) : ∃ m : Ideal R, m.IsMaximal ∧ x ∉ m := by
  by_contra h
  push Not at h
  refine hx (mem_jacobson_bot.2 fun y => ?_)
  by_contra hy
  have hne : Ideal.span ({x * y + 1} : Set R) ≠ ⊤ := by
    intro htop
    exact hy (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have h1 : x * y + 1 ∈ m := hle (Ideal.subset_span (Set.mem_singleton _))
  have hx_m : x ∈ m := h m hm
  exact hm.ne_top (by
    rw [Ideal.eq_top_iff_one]
    simpa using m.sub_mem h1 (m.mul_mem_right y hx_m))

/-- Clearing denominators: an integral nonzero element divides a nonzero element of the base. -/
theorem exists_mul_eq_of_isIntegral {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] {v : S} (hv : v ≠ 0) (h : IsIntegral R v) (hS : IsDomain S) :
    ∃ c : R, c ≠ 0 ∧ ∃ V : S, v * V = algebraMap R S c := by
  classical
  obtain ⟨p, hpm, hpv⟩ := h
  have hpv' : Polynomial.aeval v p = 0 := hpv
  have hex : ∃ n, ∃ q : R[X], q.Monic ∧ Polynomial.aeval v q = 0 ∧ q.natDegree = n :=
    ⟨p.natDegree, p, hpm, hpv', rfl⟩
  obtain ⟨q, hqm, hqv, hqdeg⟩ := Nat.find_spec hex
  have hmin : ∀ r : R[X], r.Monic → Polynomial.aeval v r = 0 → q.natDegree ≤ r.natDegree := by
    intro r hrm hrv
    have h1 := Nat.find_min' hex ⟨r, hrm, hrv, rfl⟩
    omega
  have hqne : q ≠ 0 := hqm.ne_zero
  have hc0 : q.coeff 0 ≠ 0 := by
    intro h0
    set r : R[X] := q.divX with hr
    have hsplit : q = Polynomial.X * r := by
      have h := Polynomial.divX_mul_X_add q
      rw [h0, Polynomial.C_0, add_zero, ← hr] at h
      rw [← h, mul_comm]
    have hqmono : r.Monic := by
      have h := hqm
      rw [hsplit] at h
      exact Polynomial.Monic.of_mul_monic_left Polynomial.monic_X h
    have hrne : r ≠ 0 := hqmono.ne_zero
    have hq0 : Polynomial.aeval v r = 0 := by
      have h1 : v * Polynomial.aeval v r = 0 := by
        have h2 := hqv
        rw [hsplit, map_mul, Polynomial.aeval_X] at h2
        exact h2
      exact (mul_eq_zero.mp h1).resolve_left hv
    have hdeg : r.natDegree < q.natDegree := by
      rw [hsplit, Polynomial.natDegree_X_mul hrne]
      exact Nat.lt_succ_self _
    have := hmin r hqmono hq0
    omega
  refine ⟨q.coeff 0, hc0, -(Polynomial.aeval v q.divX), ?_⟩
  have h2 : Polynomial.aeval v q.divX * v + algebraMap R S (q.coeff 0) = 0 := by
    have h := Polynomial.divX_mul_X_add q
    have h3 := congrArg (Polynomial.aeval v) h
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h3
    rw [hqv] at h3
    exact h3
  linear_combination -h2


section QuotientLemmas

lemma ft_quotient {K C : Type*} [Field K] [CommRing C] [Algebra K C] [Algebra.FiniteType K C]
    (n : Ideal C) : Algebra.FiniteType K (C ⧸ n) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K n) (Ideal.Quotient.mkₐ_surjective _ _)

lemma finite_quotient {K C : Type*} [Field K] [CommRing C] [Algebra K C] [Algebra.FiniteType K C]
    [IsJacobsonRing K] (n : Ideal C) [n.IsMaximal] : Module.Finite K (C ⧸ n) :=
  @finite_of_finite_type_of_isJacobsonRing K (C ⧸ n) _ (Ideal.Quotient.field n) _
    (inferInstance) (ft_quotient n)

lemma algebraic_quotient {K C : Type*} [Field K] [CommRing C] [Algebra K C]
    [Algebra.FiniteType K C] [IsJacobsonRing K] (n : Ideal C) [n.IsMaximal] :
    Algebra.IsAlgebraic K (C ⧸ n) :=
  @Algebra.IsAlgebraic.of_finite K (C ⧸ n) _ _ _ _ (finite_quotient n)

lemma frac_intClosure {A K F : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field F] [Algebra A F] [Algebra K F] [IsScalarTower A K F]
    [FiniteDimensional K F] : IsFractionRing (integralClosure A F) F :=
  integralClosure.isFractionRing_of_finite_extension (A := A) K F

end QuotientLemmas

/-- Every nonzero element of `B` misses a maximal ideal (Exercise 5.22, key step). -/
theorem exists_isMaximal_not_mem_of_ne_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    (hJ : Ideal.jacobson (⊥ : Ideal A) = ⊥) {v : B} (hv0 : v ≠ 0) :
    ∃ m : Ideal B, m.IsMaximal ∧ v ∉ m := by
  classical
  have hT : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B :=
    genLoc_sub_le hinj
  haveI hCdom : IsDomain (genLoc A B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  have hBC : Function.Injective (algebraMap B (genLoc A B)) := IsLocalization.injective _ hT
  haveI hft : Algebra.FiniteType (FractionRing A) (genLoc A B) := genLoc_finiteType hinj
  haveI hJK : IsJacobsonRing (FractionRing A) := inferInstance
  haveI hJC : IsJacobsonRing (genLoc A B) := isJacobsonRing_of_finiteType (A := FractionRing A)
  have hCbot : Ideal.jacobson (⊥ : Ideal (genLoc A B)) = ⊥ := by
    rw [← Ideal.radical_eq_jacobson]
    exact Ideal.radical_bot_of_isReduced
  have hvC : algebraMap B (genLoc A B) v ≠ 0 := fun h => hv0 (hBC (by simpa using h))
  obtain ⟨n, hn, hvn⟩ := exists_isMaximal_not_mem (R := genLoc A B)
    (x := algebraMap B (genLoc A B) v) (by rw [hCbot]; exact hvC)
  haveI hnmax : n.IsMaximal := hn
  set p : Ideal B := n.comap (algebraMap B (genLoc A B)) with hpdef
  have hvp : v ∉ p := fun h => hvn h
  have hftF : Algebra.FiniteType (FractionRing A) ((genLoc A B) ⧸ n) := ft_quotient n
  haveI hfinF : Module.Finite (FractionRing A) ((genLoc A B) ⧸ n) := finite_quotient n
  haveI halgF : Algebra.IsAlgebraic (FractionRing A) ((genLoc A B) ⧸ n) := algebraic_quotient n
  haveI hFfield : Field ((genLoc A B) ⧸ n) := Ideal.Quotient.field n
  haveI halgA : Algebra.IsAlgebraic A ((genLoc A B) ⧸ n) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
      (C := (genLoc A B) ⧸ n)).mpr halgF
  let g : B →+* ((genLoc A B) ⧸ n) := (Ideal.Quotient.mk n).comp (algebraMap B (genLoc A B))
  have hgv : g v ≠ 0 := by
    intro h
    apply hvp
    have h' : (Ideal.Quotient.mk n) (algebraMap B (genLoc A B) v) = 0 := h
    have h'' : algebraMap B (genLoc A B) v ∈ n := Ideal.Quotient.eq_zero_iff_mem.mp h'
    exact h''

  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  obtain ⟨b, hb, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := A)
    (insert (g v) (s.image g)) (alg := halgA)
  -- ## Step 4: the ring `A_b` and the integral `A_b`-subalgebra `T ⊆ F`
  have hb_mem : b ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hb
  have h1 : IsUnit (algebraMap B (genLoc A B) (algebraMap A B b)) :=
    IsLocalization.map_units (genLoc A B)
      ⟨algebraMap A B b, Algebra.mem_algebraMapSubmonoid_of_mem ⟨b, hb_mem⟩⟩
  have h2 : IsUnit (algebraMap A (genLoc A B) b) := by
    rw [IsScalarTower.algebraMap_apply A B (genLoc A B)]
    exact h1
  have hb_unit : IsUnit (algebraMap A ((genLoc A B) ⧸ n) b) := by
    rw [IsScalarTower.algebraMap_apply A (genLoc A B) ((genLoc A B) ⧸ n)]
    exact h2.map _
  -- ## Step 5: `A_b` acts on `F`
  let Ab := Localization.Away b
  letI : Algebra Ab ((genLoc A B) ⧸ n) := (IsLocalization.Away.lift (R := A) b hb_unit).toAlgebra
  have hcompat : ∀ a : A, (algebraMap Ab ((genLoc A B) ⧸ n)) (algebraMap A Ab a)
      = algebraMap A ((genLoc A B) ⧸ n) a := by
    intro a
    rw [RingHom.algebraMap_toAlgebra]
    exact IsLocalization.Away.lift_eq (R := A) b hb_unit a
  haveI : IsScalarTower A Ab ((genLoc A B) ⧸ n) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hcompat a).symm)
  -- ## Step 6: the `A_b`-subalgebra `T ⊆ F`
  set zs : Finset ((genLoc A B) ⧸ n) := insert (g v) (s.image g) with hzs
  have hmem_zs : ∀ z ∈ zs, IsIntegral A (algebraMap A ((genLoc A B) ⧸ n) b * z) := by
    intro z hz
    have := hint z hz
    simpa [Algebra.smul_def] using this
  have hbAb_unit : IsUnit (algebraMap A Ab b) := IsLocalization.Away.algebraMap_isUnit b
  let T : Subalgebra Ab ((genLoc A B) ⧸ n) :=
    Algebra.adjoin Ab ((fun z => algebraMap A ((genLoc A B) ⧸ n) b * z) '' (zs : Set _))
  have hT_int : Algebra.IsIntegral Ab T :=
    Algebra.IsIntegral.adjoin fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      exact (hmem_zs w hw).tower_top
  have hinvT : ∃ u ∈ T, u * algebraMap A ((genLoc A B) ⧸ n) b = 1 := by
    obtain ⟨vAb, hvAb⟩ := IsUnit.exists_left_inv hbAb_unit
    refine ⟨algebraMap Ab ((genLoc A B) ⧸ n) vAb, T.algebraMap_mem _, ?_⟩
    rw [← hcompat b, ← map_mul, hvAb, map_one]
  have hzsT : ∀ z ∈ zs, z ∈ T := by
    intro z hz
    obtain ⟨u, huT, hu⟩ := hinvT
    have hmem : algebraMap A ((genLoc A B) ⧸ n) b * z ∈ T :=
      Algebra.subset_adjoin ⟨z, hz, rfl⟩
    have hEq : z = u * (algebraMap A ((genLoc A B) ⧸ n) b * z) := by
      rw [← mul_assoc, hu, one_mul]
    rw [hEq]
    exact T.mul_mem huT hmem
  -- ## Step 7: the ring hom `B →+* T`
  have hgT_mem : ∀ x : B, g x ∈ T := by
    intro x
    have hx : x ∈ Algebra.adjoin A (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact hzsT (g y) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
    | algebraMap a =>
        have h1 : g (algebraMap A B a) = algebraMap Ab ((genLoc A B) ⧸ n) (algebraMap A Ab a) := by
          rw [show g (algebraMap A B a) = algebraMap A ((genLoc A B) ⧸ n) a from
            (IsScalarTower.algebraMap_apply A B ((genLoc A B) ⧸ n) a).symm, hcompat a]
        rw [h1]
        exact T.algebraMap_mem _
    | add y z _ _ hy hz => rw [map_add]; exact T.add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact T.mul_mem hy hz
  let gT : B →+* T := g.codRestrict T hgT_mem
  have hgT_coe : ∀ x : B, (gT x : (genLoc A B) ⧸ n) = g x := fun x => rfl
  have hgTv : gT v ≠ 0 := by
    intro h
    apply hgv
    rw [← hgT_coe v, h]
    rfl
  -- ## Step 8: constant term for `v`
  have hb_nzd : b ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hb
  haveI hAb_dom : IsDomain Ab := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (Submonoid.powers_le.mpr hb_nzd)
  obtain ⟨c, hc0, V, hV⟩ := exists_mul_eq_of_isIntegral (R := Ab) (S := T) (v := gT v)
      hgTv (hT_int.isIntegral (gT v)) (inferInstance)
  -- ## Step 9: write `c = c₀ / b^k`
  obtain ⟨⟨c₀, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers b) c
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (M := A) (t : A) b).mp t.2
  have hAb_inj : Function.Injective (algebraMap A Ab) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr hb_nzd)
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    have hbk : (b ^ k : A) ≠ 0 := pow_ne_zero k hb
    have hbk' : algebraMap A Ab (b ^ k) ≠ 0 :=
      fun h => hbk (hAb_inj (by rw [h, map_zero]))
    have hzero : c * algebraMap A Ab (b ^ k) = 0 := by
      rw [show algebraMap A Ab (b ^ k) = algebraMap A Ab (t : A) from by rw [hk], ht, h0, map_zero]
    exact hc0 ((mul_eq_zero.mp hzero).resolve_right hbk')
  -- ## Step 10: the maximal ideal of `A` and of `A_b`
  have hbc0 : b * c₀ ≠ 0 := mul_ne_zero hb hc₀ne
  obtain ⟨𝔪, h𝔪max, h𝔪bc⟩ : ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ b * c₀ ∉ 𝔪 :=
    exists_isMaximal_not_mem (R := A) (x := b * c₀) (by rw [hJ]; exact hbc0)
  have hb𝔪 : b ∉ 𝔪 := fun h => h𝔪bc (𝔪.mul_mem_right c₀ h)
  have hc₀𝔪 : c₀ ∉ 𝔪 := fun h => h𝔪bc (𝔪.mul_mem_left b h)
  -- ## Step 11: `A → F` and `A_b → F` are injective
  have hinjAF : Function.Injective (algebraMap A ((genLoc A B) ⧸ n)) := by
    intro a₁ a₂ h
    have hsub : algebraMap A ((genLoc A B) ⧸ n) (a₁ - a₂) = 0 := by
      rw [map_sub, h, sub_self]
    have hzero : a₁ - a₂ = 0 := by
      by_contra hne
      have hunit : IsUnit (algebraMap A (genLoc A B) (a₁ - a₂)) := by
        rw [IsScalarTower.algebraMap_apply A B (genLoc A B)]
        exact IsLocalization.map_units (genLoc A B) ⟨algebraMap A B (a₁ - a₂),
          Algebra.mem_algebraMapSubmonoid_of_mem ⟨a₁ - a₂, mem_nonZeroDivisors_of_ne_zero hne⟩⟩
      have hmem : algebraMap A (genLoc A B) (a₁ - a₂) ∈ n :=
        Ideal.Quotient.eq_zero_iff_mem.mp hsub
      exact hn.ne_top (Ideal.eq_top_of_isUnit_mem n hmem hunit)
    exact sub_eq_zero.mp hzero
  have hinjAbF : Function.Injective (algebraMap Ab ((genLoc A B) ⧸ n)) := by
    have key : ∀ x : Ab, algebraMap Ab ((genLoc A B) ⧸ n) x = 0 → x = 0 := by
      intro x hx
      obtain ⟨⟨a₀, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers b) x
      have h1 : algebraMap A ((genLoc A B) ⧸ n) a₀ = 0 := by
        have h2 : algebraMap Ab ((genLoc A B) ⧸ n) x *
            algebraMap A ((genLoc A B) ⧸ n) (s : A) =
            algebraMap A ((genLoc A B) ⧸ n) a₀ := by
          have h3 : algebraMap Ab ((genLoc A B) ⧸ n) (x * algebraMap A Ab (s : A))
              = algebraMap Ab ((genLoc A B) ⧸ n) (algebraMap A Ab a₀) := by rw [hs]
          rw [map_mul] at h3
          simpa only [IsScalarTower.algebraMap_apply A Ab ((genLoc A B) ⧸ n)] using h3
        rw [hx, zero_mul] at h2
        exact h2.symm
      have ha₀ : a₀ = 0 := hinjAF (by simpa using h1)
      rw [ha₀, map_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_right
        (IsLocalization.map_units Ab ⟨(s : A), s.2⟩).ne_zero
    intro x y hxy
    have h : x - y = 0 := key (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  have hkerAbT : RingHom.ker (algebraMap Ab T) = ⊥ := by
    rw [← RingHom.injective_iff_ker_eq_bot]
    intro x y hxy
    apply hinjAbF
    rw [IsScalarTower.algebraMap_apply Ab T ((genLoc A B) ⧸ n),
      IsScalarTower.algebraMap_apply Ab T ((genLoc A B) ⧸ n), hxy]
  -- ## Step 12: the maximal ideal `N = 𝔪·A_b` of `A_b`
  set N : Ideal Ab := Ideal.map (algebraMap A Ab) 𝔪 with hNdef
  have hdisj : Disjoint (Submonoid.powers b : Set A) (𝔪 : Set A) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact hb𝔪
  have hNcomap : Ideal.comap (algebraMap A Ab) N = 𝔪 := by
    rw [hNdef]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers b) Ab
      h𝔪max.isPrime hdisj
  haveI hNmax : N.IsMaximal := by
    have h : (Ideal.comap (algebraMap A Ab) N).IsMaximal := by
      rw [hNcomap]; exact h𝔪max
    exact Ideal.IsMaximal.of_isLocalization_of_disjoint (M := Submonoid.powers b) (J := N)
  have hbN : algebraMap A Ab b ∉ N := by
    intro hmem
    exact hb𝔪 (by rw [← hNcomap]; exact hmem)
  have hc₀N : algebraMap A Ab c₀ ∉ N := by
    intro hmem
    exact hc₀𝔪 (by rw [← hNcomap]; exact hmem)
  have hcN : c ∉ N := by
    intro hc
    apply hc₀N
    have hmem : c * algebraMap A Ab (b ^ k) ∈ N := N.mul_mem_right _ hc
    rwa [show algebraMap A Ab (b ^ k) = algebraMap A Ab (t : A) from by rw [hk], ht] at hmem
  haveI h𝔪prime : 𝔪.IsPrime := h𝔪max.isPrime
  -- ## Step 13: `A ⧸ 𝔪 → A_b ⧸ N` is surjective
  have hsurj : ∀ y : Ab, ∃ a : A, Ideal.Quotient.mk N y = Ideal.Quotient.mk N (algebraMap A Ab a) := by
    intro y
    obtain ⟨⟨a₀, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers b) y
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (M := A) (s : A) b).mp s.2
    have hs𝔪 : (s : A) ∉ 𝔪 := by
      intro hcon
      have hmem : b ^ k ∈ 𝔪 := by rwa [hk]
      exact hb𝔪 (h𝔪prime.mem_of_pow_mem k hmem)
    obtain ⟨a₁, i, hi, hai⟩ := h𝔪max.exists_inv hs𝔪
    have hmem : a₁ * (s : A) - 1 ∈ 𝔪 := by
      have h1 : a₁ * (s : A) - 1 = -i := by
        linear_combination hai
      rw [h1]
      exact 𝔪.neg_mem hi
    refine ⟨a₀ * a₁, ?_⟩
    have hq : y - algebraMap A Ab (a₀ * a₁) ∈ N := by
      have h3 : algebraMap A Ab a₁ * algebraMap A Ab (s : A) - 1 ∈ N := by
        have h4 : algebraMap A Ab (a₁ * (s : A) - 1) ∈ N := Ideal.mem_map_of_mem _ hmem
        rwa [map_sub, map_mul, map_one] at h4
      have h5 : y - algebraMap A Ab (a₀ * a₁) =
          -(y * (algebraMap A Ab a₁ * algebraMap A Ab (s : A) - 1)) := by
        rw [map_mul, ← hs]
        ring
      rw [h5]
      exact N.neg_mem (N.mul_mem_left y h3)
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  -- ## Step 14: lying over
  haveI hTint : Algebra.IsIntegral Ab T := hT_int
  obtain ⟨𝔮, h𝔮max, h𝔮comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := Ab) (S := T)
    N (by rw [hkerAbT]; exact bot_le)
  haveI h𝔮max' : 𝔮.IsMaximal := h𝔮max
  -- ## Step 15: the field `L = T ⧸ 𝔮` and the map `B → L`
  haveI hLfield : Field (T ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  let φ : B →+* (T ⧸ 𝔮) := (Ideal.Quotient.mk 𝔮).comp gT
  have hφv : φ v ≠ 0 := by
    intro h
    have h2 : gT v ∈ 𝔮 := Ideal.Quotient.eq_zero_iff_mem.mp h
    have h3 : algebraMap Ab T c ∈ 𝔮 := by
      rw [← hV]
      exact 𝔮.mul_mem_right V h2
    have h4 : c ∈ Ideal.comap (algebraMap Ab T) 𝔮 := h3
    rw [h𝔮comap] at h4
    exact hcN h4
  -- ## Step 16: the image of `A_b` in `L` is the image of `A`
  have hAT : ∀ a : A, algebraMap Ab T (algebraMap A Ab a) = gT (algebraMap A B a) := by
    intro a
    apply Subtype.ext
    show algebraMap Ab ((genLoc A B) ⧸ n) (algebraMap A Ab a) = g (algebraMap A B a)
    rw [show g (algebraMap A B a) = algebraMap A ((genLoc A B) ⧸ n) a from
      (IsScalarTower.algebraMap_apply A B ((genLoc A B) ⧸ n) a).symm]
    exact hcompat a
  have hident : ∀ y : Ab, ∃ a : A, (Ideal.Quotient.mk 𝔮) (algebraMap Ab T y)
      = (Ideal.Quotient.mk 𝔮) (gT (algebraMap A B a)) := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    refine ⟨a, ?_⟩
    have h1 : y - algebraMap A Ab a ∈ Ideal.comap (algebraMap Ab T) 𝔮 := by
      rw [h𝔮comap]
      have h2 : Ideal.Quotient.mk N y - Ideal.Quotient.mk N (algebraMap A Ab a) = 0 := by
        rw [ha, sub_self]
      rwa [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h2
    have h2 : algebraMap Ab T y - algebraMap Ab T (algebraMap A Ab a) ∈ 𝔮 := by
      have h3 := h1
      rw [Ideal.mem_comap] at h3
      rwa [map_sub] at h3
    rw [← hAT a, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  -- ## Step 17: `φ` is surjective, hence `ker φ` is maximal
  have hk_sub : ∀ y : Ab, (Ideal.Quotient.mk 𝔮) (algebraMap Ab T y) ∈ φ.range := by
    intro y
    obtain ⟨a, ha⟩ := hident y
    rw [ha]
    exact ⟨algebraMap A B a, rfl⟩
  have hzmem : ∀ (z : (genLoc A B) ⧸ n) (hz : z ∈ (zs : Set ((genLoc A B) ⧸ n))),
      (Ideal.Quotient.mk 𝔮) ⟨z, hzsT z (Finset.mem_coe.mp hz)⟩ ∈ φ.range := by
    intro z hz
    rw [Finset.mem_coe, hzs, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact ⟨v, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨y, rfl⟩
  set P' : Subalgebra Ab ((genLoc A B) ⧸ n) :=
    { carrier := {y | ∃ hy : y ∈ T, (Ideal.Quotient.mk 𝔮) ⟨y, hy⟩ ∈ φ.range}
      one_mem' := ⟨T.one_mem, by
        rw [show (⟨1, T.one_mem⟩ : T) = 1 from Subtype.ext rfl, map_one]
        exact φ.range.one_mem⟩
      mul_mem' := by
        rintro y z ⟨hy, hpy⟩ ⟨hz, hpz⟩
        refine ⟨T.mul_mem hy hz, ?_⟩
        rw [show (⟨y * z, T.mul_mem hy hz⟩ : T) = ⟨y, hy⟩ * ⟨z, hz⟩ from Subtype.ext rfl,
          map_mul]
        exact φ.range.mul_mem hpy hpz
      add_mem' := by
        rintro y z ⟨hy, hpy⟩ ⟨hz, hpz⟩
        refine ⟨T.add_mem hy hz, ?_⟩
        rw [show (⟨y + z, T.add_mem hy hz⟩ : T) = ⟨y, hy⟩ + ⟨z, hz⟩ from Subtype.ext rfl,
          map_add]
        exact φ.range.add_mem hpy hpz
      zero_mem' := ⟨T.zero_mem, by
        rw [show (⟨0, T.zero_mem⟩ : T) = 0 from Subtype.ext rfl, map_zero]
        exact φ.range.zero_mem⟩
      algebraMap_mem' := fun c => ⟨T.algebraMap_mem c, by simpa using hk_sub c⟩ } with hP'def
  have hgens : ∀ z ∈ (zs : Set ((genLoc A B) ⧸ n)),
      (algebraMap A ((genLoc A B) ⧸ n) b * z) ∈ P' := by
    intro z hz
    refine ⟨Algebra.subset_adjoin ⟨z, hz, rfl⟩, ?_⟩
    have h1 : algebraMap A ((genLoc A B) ⧸ n) b =
        algebraMap Ab ((genLoc A B) ⧸ n) (algebraMap A Ab b) :=
      IsScalarTower.algebraMap_apply A Ab ((genLoc A B) ⧸ n) b
    have h2 : (⟨algebraMap A ((genLoc A B) ⧸ n) b * z,
        Algebra.subset_adjoin ⟨z, hz, rfl⟩⟩ : T) =
        algebraMap Ab T (algebraMap A Ab b) * ⟨z, hzsT z (Finset.mem_coe.mp hz)⟩ := by
      apply Subtype.ext
      show algebraMap A ((genLoc A B) ⧸ n) b * z =
        algebraMap Ab ((genLoc A B) ⧸ n) (algebraMap A Ab b) * z
      rw [h1]
    rw [h2, map_mul]
    exact φ.range.mul_mem (hk_sub (algebraMap A Ab b)) (hzmem z hz)
  have hgens' : ((fun z => algebraMap A ((genLoc A B) ⧸ n) b * z) '' (zs : Set _)) ⊆ (P' : Set _) := by
    rintro x ⟨z, hz, rfl⟩
    exact hgens z hz
  have hTle : T ≤ P' := Algebra.adjoin_le (S := P') hgens'
  have hsurjφ : Function.Surjective φ := by
    intro y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective (I := 𝔮) y
    have hmem := hTle t.2
    change ∃ hy : (t : (genLoc A B) ⧸ n) ∈ T,
      (Ideal.Quotient.mk 𝔮) ⟨(t : (genLoc A B) ⧸ n), hy⟩ ∈ φ.range at hmem
    obtain ⟨_, hpy⟩ := hmem
    obtain ⟨b, hb⟩ := hpy
    exact ⟨b, hb⟩
  have hker_max : (RingHom.ker φ).IsMaximal := by
    refine Ideal.isMaximal_iff.mpr ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_one]
      exact one_ne_zero
    · intro J x hIJ hxker hxJ
      have hx0 : φ x ≠ 0 := fun h => hxker (RingHom.mem_ker.mpr h)
      have hxq : gT x ∉ 𝔮 := fun h => hx0 (show (Ideal.Quotient.mk 𝔮) (gT x) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr h)
      obtain ⟨t, i, hi, hti⟩ := h𝔮max.exists_inv hxq
      have h1 : (Ideal.Quotient.mk 𝔮 t) * φ x = 1 := by
        have h2 : (Ideal.Quotient.mk 𝔮) (t * gT x + i) = 1 := by rw [hti, map_one]
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero, map_mul] at h2
        exact h2
      have hz : φ x * (Ideal.Quotient.mk 𝔮 t) = 1 := by
        rw [mul_comm]
        exact h1
      obtain ⟨y, hy⟩ := hsurjφ (Ideal.Quotient.mk 𝔮 t)
      have h3 : φ (x * y) = 1 := by
        rw [map_mul, hy]
        exact hz
      have h2 : x * y - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, h3, map_one, sub_self]
      have h4 : x * y ∈ J := J.mul_mem_right y hxJ
      simpa using J.sub_mem h4 (hIJ h2)
  exact ⟨RingHom.ker φ, hker_max, fun hv => hφv (RingHom.mem_ker.mp hv)⟩

/-- **Atiyah–Macdonald (1969), Exercise 5.22.** Let `A` be a subring of an integral domain `B`
such that `B` is a finitely generated `A`-algebra. If the Jacobson radical of `A` is zero, then
the Jacobson radical of `B` is zero. -/
theorem jacobson_eq_bot_of_isDomain_of_finiteType (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDomain B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    (hJ : Ideal.jacobson (⊥ : Ideal A) = ⊥) :
    Ideal.jacobson (⊥ : Ideal B) = ⊥ := by
  haveI hntriv : Nontrivial A :=
    ⟨⟨0, 1, fun h => zero_ne_one (by
      rw [← map_zero (algebraMap A B), ← map_one (algebraMap A B), h])⟩⟩
  haveI hdom : IsDomain A :=
    { hinj.isCancelMulZero (algebraMap A B) (map_zero _) (fun x y => map_mul _ x y) with
      exists_pair_ne := hntriv.exists_pair_ne }
  rw [eq_bot_iff]
  intro v hv
  by_contra hne
  obtain ⟨m, hm, hvm⟩ := exists_isMaximal_not_mem_of_ne_zero hinj hJ hne
  exact hvm (sInf_le (show m ∈ {J : Ideal B | ⊥ ≤ J ∧ IsMaximal J} from ⟨bot_le, hm⟩) hv)

end AtiyahMcdonald69.Ex_5_22

/-! ## Axiom check -/

#print axioms AtiyahMcdonald69.Ex_5_22.jacobson_eq_bot_of_isDomain_of_finiteType
#print axioms AtiyahMcdonald69.Ex_5_22.exists_isMaximal_not_mem_of_ne_zero
