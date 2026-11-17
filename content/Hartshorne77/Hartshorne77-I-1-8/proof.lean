import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace Hartshorne77.Ex_I_1_8

section Krull

variable {A : Type*} [CommRing A]

/-- In a Noetherian domain, a prime minimal over a nonzero principal ideal has height one. -/
theorem Ideal.height_eq_one_of_mem_minimalPrimes [IsNoetherianRing A] [IsDomain A]
    {t : A} (ht : t ≠ 0) {p : Ideal A} (hp : p ∈ (Ideal.span {t}).minimalPrimes) :
    p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
  have h1 : (1 : ℕ∞) ≤ (Ideal.span {t}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  refine le_trans h1 ?_
  rw [Ideal.height_eq_inf_minimalPrimes]
  exact iInf₂_le p hp

/-- The image of a prime minimal over `I` in `A ⧸ I` has height zero. -/
theorem Ideal.height_map_quotient_eq_zero [IsNoetherianRing A] {I P : Ideal A}
    (h : P ∈ I.minimalPrimes) : (P.map (Ideal.Quotient.mk I)).height = 0 := by
  have hP : P.IsPrime := h.isPrime
  have : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime h.le
  have key : P.map (Ideal.Quotient.mk I) ∈ minimalPrimes (A ⧸ I) := by
    rw [Ideal.minimalPrimes_eq_comap] at h
    obtain ⟨Q, hQ, hQP⟩ := h
    rw [← hQP]
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
    exact hQ
  rw [Ideal.height_eq_zero_iff]
  exact key

/-- Height and dimension are preserved by integral injective extensions of domains. -/
theorem Ideal.height_eq_height_under_of_isIntegral {B S : Type*} [CommRing B] [CommRing S]
    [IsDomain B] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S] [FaithfulSMul B S]
    [IsNoetherianRing B] [IsNoetherianRing S] [Algebra.HasGoingDown B S] {P : Ideal S} [P.IsPrime] :
    P.height = (P.under B).height := by
  have : P.LiesOver (P.under B) := ⟨rfl⟩
  have h2 : (P.map (Ideal.Quotient.mk ((P.under B).map (algebraMap B S)))).height = 0 :=
    Ideal.height_map_quotient_eq_zero (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := B) P)
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under B) P, h2, add_zero]

end Krull

section IntegralDim

variable {B S : Type*} [CommRing B] [CommRing S] [IsDomain B] [IsDomain S] [Algebra B S]
  [Algebra.IsIntegral B S] [FaithfulSMul B S] [IsNoetherianRing B] [IsNoetherianRing S]
  [Algebra.HasGoingDown B S]

/-- Integral injective extensions of Noetherian domains have the same Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective : ringKrullDim S = ringKrullDim B := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := P)
    rw [h]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro q hq
    obtain ⟨Q, -, hQprime, hQeq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := S) q (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B S)]; exact bot_le)
    haveI := hQprime
    have h := Ideal.height_eq_height_under_of_isIntegral (B := B) (P := Q)
    show q.height ≤ ringKrullDim S
    rw [← hQeq, ← h]
    exact Ideal.height_le_ringKrullDim_of_isPrime

end IntegralDim

section Concat

variable {A : Type*} [CommRing A]

/-- Concatenation of chains: if `p` is a prime of height one in a domain, then passing to
`A ⧸ p` lowers heights by at most one. -/
theorem Ideal.height_map_quotient_add_one_le [IsNoetherianRing A] [IsDomain A] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1) :
    (q.map (Ideal.Quotient.mk p)).height + 1 ≤ q.height := by
  have hp0 : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hp
    exact zero_ne_one hp
  haveI : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨lq, hlq, hlenq⟩ := Ideal.exists_ltSeries_length_eq_height (q.map (Ideal.Quotient.mk p))
  set F : LTSeries (PrimeSpectrum A) :=
    lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk p))
      (RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective) with hF
  have hbot : (⊥ : PrimeSpectrum A) < F.head := by
    have hple : p ≤ F.head.asIdeal := by
      rw [hF]
      show p ≤ Ideal.comap (Ideal.Quotient.mk p) _
      rw [← Ideal.map_le_iff_le_comap]
      simp
    exact (bot_lt_iff_ne_bot.mpr hp0).trans_le hple
  let G : LTSeries (PrimeSpectrum A) := F.cons ⊥ hbot
  have hFlast : F.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    rw [hF]
    change PrimeSpectrum.comap (Ideal.Quotient.mk p) (RelSeries.last lq) = _
    rw [hlq]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hcomap : Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (A ⧸ p)) = p := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, sup_of_le_left hpq]
  have hlenF : F.length = lq.length := by simp [F]
  have hlenG : G.length = F.length + 1 := by simp [G]
  have hGlast : G.last = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) := by
    change (F.cons ⊥ hbot).last = _
    rw [RelSeries.last_cons, hFlast]
  have hlen : G.length = (q.map (Ideal.Quotient.mk p)).height + 1 := by
    rw [hlenG, hlenF, ← hlenq]
    push_cast
    ring
  rw [← hlen]
  have h := Order.length_le_height (p := G) (x := (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A))
    (le_of_eq hGlast)
  rwa [← PrimeSpectrum.height_eq_orderHeight] at h

end Concat
section PointHeight

variable (k : Type*) [Field k]

/-- Substitution sending `X i` to the constant `a i` for `i < j`, and fixing the other variables. -/
noncomputable def substBelow {s : ℕ} (j : ℕ) (a : Fin s → k) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  MvPolynomial.aeval fun i => if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k)
    else MvPolynomial.X i

lemma substBelow_X {s : ℕ} (j : ℕ) (a : Fin s → k) (i : Fin s) :
    substBelow k j a (MvPolynomial.X i) =
      if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i := by
  simp [substBelow]

lemma substBelow_zero {s : ℕ} (a : Fin s → k) : substBelow k 0 a = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substBelow_X]

lemma substBelow_succ {s : ℕ} (j : ℕ) (a : Fin s → k) :
    substBelow k (j + 1) a = (MvPolynomial.aeval fun (i : Fin s) =>
      if (i : ℕ) = j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i).comp
      (substBelow k j a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, substBelow_X, substBelow_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega), MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  · rw [if_neg h]
    by_cases h2 : (i : ℕ) = j
    · rw [MvPolynomial.aeval_X, if_pos h2, if_pos (by omega)]
    · rw [MvPolynomial.aeval_X, if_neg h2, if_neg (by omega)]

lemma ker_substBelow_antitone {s : ℕ} (j : ℕ) (a : Fin s → k) :
    RingHom.ker (substBelow k j a) ≤ RingHom.ker (substBelow k (j + 1) a) := by
  intro f hf
  simp only [RingHom.mem_ker] at hf ⊢
  rw [substBelow_succ, AlgHom.comp_apply, hf, map_zero]

lemma X_sub_C_mem_ker_substBelow_succ {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∈
      RingHom.ker (substBelow k (j + 1) a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_pos (show ((⟨j, hj⟩ : Fin s) : ℕ) < j + 1 from by simp)]
  simp

lemma X_sub_C_notMem_ker_substBelow {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∉
      RingHom.ker (substBelow k j a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_neg (show ¬ ((⟨j, hj⟩ : Fin s) : ℕ) < j from by simp)]
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => a ⟨j, hj⟩ + 1)) h
  simp at h2

end PointHeight

section Height

variable (k : Type*) [Field k]

/-- The ideal of polynomials vanishing at a point of affine `s`-space has height `s`. -/
theorem vanishingIdeal_singleton_height (s : ℕ) (a : Fin s → k) :
    (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height = ↑s := by
  have hker : RingHom.ker (substBelow k s a) = MvPolynomial.vanishingIdeal k {a} := by
    have heq : substBelow k s a =
        (Algebra.ofId k (MvPolynomial (Fin s) k)).comp (MvPolynomial.aeval a) := by
      rw [MvPolynomial.comp_aeval]
      apply MvPolynomial.algHom_ext
      intro i
      rw [substBelow_X, if_pos i.isLt, MvPolynomial.aeval_X, Algebra.ofId_apply,
        MvPolynomial.algebraMap_eq]
    have hinj : Function.Injective (algebraMap k (MvPolynomial (Fin s) k)) :=
      FaithfulSMul.algebraMap_injective k _
    rw [heq]
    ext p
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Algebra.ofId_apply,
      MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : (MvPolynomial.aeval a) p = 0 := hinj (by simpa using h)
      intro x hx
      rw [hx]
      exact h0
    · intro h
      rw [h a rfl, map_zero]
  have hlower : (↑s : ℕ∞) ≤ (MvPolynomial.vanishingIdeal k {a} :
      Ideal (MvPolynomial (Fin s) k)).height := by
    rw [← hker]
    have key : ∀ j ≤ s, (↑j : ℕ∞) ≤ (RingHom.ker (substBelow k j a)).height := by
      intro j
      induction j with
      | zero => intro _; exact bot_le
      | succ m ih =>
        intro hm
        have hms : m < s := by omega
        have h1 : (RingHom.ker (substBelow k m a)).IsPrime := RingHom.ker_isPrime _
        have h2 : (RingHom.ker (substBelow k (m + 1) a)).IsPrime := RingHom.ker_isPrime _
        have hlt : RingHom.ker (substBelow k m a) < RingHom.ker (substBelow k (m + 1) a) :=
          lt_of_le_of_ne (ker_substBelow_antitone k m a)
            (fun heq => X_sub_C_notMem_ker_substBelow k m hms a (heq ▸
              X_sub_C_mem_ker_substBelow_succ k m hms a))
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have him := ih (by omega : m ≤ s)
        calc (↑(m + 1) : ℕ∞) = (↑m : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (substBelow k m a)).height + 1 := by gcongr
          _ ≤ (RingHom.ker (substBelow k (m + 1) a)).height := hstep
    exact key s le_rfl
  have hupper : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height ≤ ↑s := by
    haveI : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).IsMaximal :=
      inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := MvPolynomial.vanishingIdeal k {a})
      (Ideal.IsMaximal.ne_top ‹(MvPolynomial.vanishingIdeal k {a} :
        Ideal (MvPolynomial (Fin s) k)).IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  exact le_antisymm hupper hlower

end Height

section DimensionDrop

variable {A : Type*} [CommRing A]

/-- Quotient by a prime of height one decreases the Krull dimension by at most one. -/
theorem ringKrullDim_quotient_add_one_le_of_height_eq_one [IsNoetherianRing A] [IsDomain A]
    {p : Ideal A} [hp : p.IsPrime] (h1 : p.height = 1) [FiniteRingKrullDim (A ⧸ p)] :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by
  have key : ∀ (M : Ideal (A ⧸ p)), M.IsMaximal → (↑(M.height + 1) : WithBot ℕ∞) ≤ ringKrullDim A := by
    intro M hM
    haveI := hM
    have hcomap : (Ideal.comap (Ideal.Quotient.mk p) M).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hpcomap : p ≤ Ideal.comap (Ideal.Quotient.mk p) M := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
      exact bot_le
    have hmap : (Ideal.comap (Ideal.Quotient.mk p) M).map (Ideal.Quotient.mk p) = M :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
    have h := Ideal.height_map_quotient_add_one_le (p := p)
      (q := Ideal.comap (Ideal.Quotient.mk p) M) hpcomap h1
    rw [hmap] at h
    have h' : (↑(M.height + 1) : WithBot ℕ∞) ≤ ↑((Ideal.comap (Ideal.Quotient.mk p) M).height) := by
      rw [WithBot.coe_le_coe]
      exact h
    exact h'.trans (Ideal.height_le_ringKrullDim_of_ne_top hcomap.ne_top)
  obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := A ⧸ p)
  calc ringKrullDim (A ⧸ p) + 1 = (↑M.height : WithBot ℕ∞) + 1 := by rw [← hMh]
    _ = ↑(M.height + 1) := by rw [WithBot.coe_add]; norm_cast
    _ ≤ ringKrullDim A := key M hMmax

end DimensionDrop

section Hypersurface

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A hypersurface in affine `s`-space has dimension one less than `s`. -/
theorem MvPolynomial.ringKrullDim_quotient_span_singleton {s : ℕ}
    {g : MvPolynomial (Fin s) k} (hg : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime] :
    ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1
      = ringKrullDim (MvPolynomial (Fin s) k) := by
  haveI hBnoeth : IsNoetherianRing (MvPolynomial (Fin s) k) := inferInstance
  have hgu : ¬ IsUnit g := fun h => hgp.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have htop : Ideal.span {g} ≠ ⊤ := hgp.ne_top
  haveI hquo : Nontrivial (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr htop
  have hh : (Ideal.span {g}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg) hgu
  have hmaxB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  haveI hfin : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top
        (by rw [hmaxB]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le (Ideal.span {g}))
  refine le_antisymm (ringKrullDim_quotient_add_one_le_of_height_eq_one hh) ?_
  obtain ⟨m, hmmax, hgm⟩ := Ideal.exists_le_maximal (Ideal.span {g}) htop
  haveI := hmmax
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hmmax
  have hms : m.height = ↑s := by
    rw [ha]
    exact vanishingIdeal_singleton_height k s a
  have hkey : (↑m.height : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by
    haveI : (Ideal.map (Ideal.Quotient.mk (Ideal.span {g})) m).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hgm
    have h1 : m.height ≤ (m.map (Ideal.Quotient.mk (Ideal.span {g}))).height +
        (Ideal.span {g}).spanFinrank :=
      Ideal.height_le_height_add_spanFinrank_of_le hgm
    have h2 : (Ideal.span {g}).spanFinrank ≤ 1 := by
      simpa using Submodule.spanFinrank_span_le_encard ({g} : Set (MvPolynomial (Fin s) k))
    have h4 : (↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) :=
      Ideal.height_le_ringKrullDim_of_isPrime
    have h1' : (↑m.height : WithBot ℕ∞) ≤
        ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := by
      exact_mod_cast h1
    calc (↑m.height : WithBot ℕ∞)
        ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + ↑(Ideal.span {g}).spanFinrank := h1'
      _ ≤ ↑((m.map (Ideal.Quotient.mk (Ideal.span {g}))).height) + 1 := by
          gcongr
          exact_mod_cast h2
      _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := by gcongr
  calc ringKrullDim (MvPolynomial (Fin s) k) = (↑s : WithBot ℕ∞) := hmaxB
    _ = (↑m.height : WithBot ℕ∞) := by rw [hms]; norm_num
    _ ≤ ringKrullDim (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) + 1 := hkey

end Hypersurface

section MainAlgebra

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **Hartshorne I.1.8, algebraic form.**  Let `S` be a finitely generated domain over an
algebraically closed field `k`, let `t ∈ S` be nonzero and not a unit, and let `p` be a prime
minimal over `(t)`.  Then `dim S/p = dim S - 1`, i.e. `dim S/p + 1 = dim S`. -/
theorem ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes
    {S : Type*} [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    {t : S} (ht : t ≠ 0) (htu : ¬ IsUnit t) {p : Ideal S} [hp : p.IsPrime]
    (hpm : p ∈ (Ideal.span {t}).minimalPrimes) :
    ringKrullDim (S ⧸ p) + 1 = ringKrullDim S := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have h1 : p.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes ht hpm
  -- Noether normalization
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k S
  let : Algebra (MvPolynomial (Fin s) k) S := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) S = g.toRingHom := RingHom.algebraMap_toAlgebra _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) S := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hginj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) S := by
    have : Module.Finite (MvPolynomial (Fin s) k) S := hgfin
    infer_instance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) k) S := inferInstance
  have hB : ringKrullDim (MvPolynomial (Fin s) k) = ↑s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hS : ringKrullDim S = ↑s := by
    rw [ringKrullDim_eq_of_integral_injective (B := MvPolynomial (Fin s) k), hB]
  -- upper bound
  haveI : FiniteRingKrullDim (S ⧸ p) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · exact ne_top_of_le_ne_top (by rw [hS]; exact fun h => ENat.natCast_ne_top s (WithBot.coe_injective h))
        (ringKrullDim_quotient_le p)
  have hupper : ringKrullDim (S ⧸ p) + 1 ≤ ringKrullDim S :=
    ringKrullDim_quotient_add_one_le_of_height_eq_one h1
  -- the contraction `q` of `p` to the polynomial ring
  set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq
  haveI hqprime : q.IsPrime := Ideal.IsPrime.under _ p
  have hq1 : q.height = 1 := by
    rw [hq, ← Ideal.height_eq_height_under_of_isIntegral (B := MvPolynomial (Fin s) k) (P := p), h1]
  -- `q` is principal
  have hqne : q ≠ ⊥ := fun h => by
    rw [h] at hq1
    exact absurd hq1 (by simp)
  obtain ⟨h, hh⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq1
  have hqspan : q = Ideal.span {h} := hh
  have hhne : h ≠ 0 := by
    rintro rfl
    exact hqne (by rw [hqspan, Ideal.span_singleton_eq_bot])
  haveI hqspanprime : (Ideal.span {h}).IsPrime := hqspan ▸ hqprime
  have hgen : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = ringKrullDim (MvPolynomial (Fin s) k) := by
    rw [hqspan]
    exact MvPolynomial.ringKrullDim_quotient_span_singleton k hhne
  -- lower bound via chain lifting
  haveI : FiniteRingKrullDim (MvPolynomial (Fin s) k ⧸ q) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top]
    refine ⟨?_, ?_⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial))
    · have h2 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) + 1 = (↑s : WithBot ℕ∞) := by
        rw [hgen, hB]
      intro htop'
      rw [htop'] at h2
      exact absurd h2.symm (by
        intro h; exact ENat.natCast_ne_top s (WithBot.coe_injective h))
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs
    · exfalso
      rw [hs0] at hS
      have hp0 : (↑p.height : WithBot ℕ∞) ≤ (↑(0 : ℕ) : WithBot ℕ∞) := by
        rw [← hS]
        exact Ideal.height_le_ringKrullDim_of_isPrime
      have hp0' : p.height ≤ (0 : ℕ∞) := by simpa using hp0
      rw [h1] at hp0'
      simp at hp0'
    · exact hs
  have hs1 : (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := by
    have h3 : s = (s - 1) + 1 := (Nat.sub_add_cancel hspos).symm
    rw [h3]
    push_cast
    ring
  have hsm1 : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) = (↑(s - 1) : WithBot ℕ∞) := by
    have h2 := hgen
    rw [hB] at h2
    rw [hs1] at h2
    exact ENat.WithBot.add_one_cancel.mp h2
  have hlow : ringKrullDim (MvPolynomial (Fin s) k ⧸ q) ≤ ringKrullDim (S ⧸ p) := by
    rw [hsm1]
    haveI hLO : p.LiesOver q := ⟨hq⟩
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : FaithfulSMul (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    haveI : Algebra.HasGoingUp (MvPolynomial (Fin s) k ⧸ q) (S ⧸ p) := inferInstance
    obtain ⟨M, hMmax, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin s) k ⧸ q)
    haveI := hMmax
    obtain ⟨l, hl, hlen⟩ := Ideal.exists_ltSeries_length_eq_height M
    have hMheight : M.height = (↑(s - 1) : ℕ∞) := by
      have h : (↑M.height : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by
        rw [hMh, hsm1]
      exact WithBot.coe_injective h
    have hlen' : l.length = s - 1 := by
      have h : (↑l.length : ℕ∞) = ↑(s - 1) := by rw [hlen, hMheight]
      exact Nat.cast_injective h
    have hhead : (RelSeries.head l).asIdeal.IsPrime := (RelSeries.head l).isPrime
    obtain ⟨Q, -, hQprime, hQover⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := MvPolynomial (Fin s) k ⧸ q)
        (S := S ⧸ p) ((RelSeries.head l).asIdeal) (I := ⊥)
        (by rw [Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
    haveI := hQprime
    haveI hQlo : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQover.symm⟩
    obtain ⟨L, hLlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    have hL : L.length = s - 1 := by rw [hLlen, hlen']
    have hL' : (↑L.length : WithBot ℕ∞) = (↑(s - 1) : WithBot ℕ∞) := by rw [hL]
    calc (↑(s - 1) : WithBot ℕ∞) = (↑L.length : WithBot ℕ∞) := hL'.symm
      _ ≤ ↑(⨆ p : LTSeries (PrimeSpectrum (S ⧸ p)), (↑p.length : ℕ∞)) := by
          exact WithBot.coe_le_coe.mpr
            (le_iSup (fun p : LTSeries (PrimeSpectrum (S ⧸ p)) => (↑p.length : ℕ∞)) L)
      _ = ringKrullDim (S ⧸ p) := by
          rw [← Order.krullDim_eq_iSup_length]
          rfl
  refine le_antisymm hupper ?_
  rw [hS]
  calc (↑s : WithBot ℕ∞) = ↑(s - 1) + 1 := hs1
    _ ≤ ringKrullDim (S ⧸ p) + 1 := by
        have h2 := hlow
        rw [hsm1] at h2
        exact add_le_add h2 (le_refl (1 : WithBot ℕ∞))

end MainAlgebra

section Zariski

variable (k : Type*) [Field k] (n : ℕ)

/-- The zero loci of the ideals of `k[X_1,…,X_n]`, i.e. the closed sets of the Zariski topology
on affine `n`-space `k^n`. -/
def zarClosed : Set (Set (Fin n → k)) :=
  {s | ∃ I : Ideal (MvPolynomial (Fin n) k), s = MvPolynomial.zeroLocus k I}

lemma zarClosed_empty : (∅ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊤, by simp⟩

lemma zarClosed_univ : (Set.univ : Set (Fin n → k)) ∈ zarClosed k n :=
  ⟨⊥, by rw [MvPolynomial.zeroLocus_bot]; exact rfl⟩

lemma zeroLocus_mul (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k (I * J) =
      MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra h
    simp only [Set.mem_union, not_or] at h
    obtain ⟨h1, h2⟩ := h
    simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at h1 h2
    obtain ⟨p, hp, hp0⟩ := h1
    obtain ⟨q, hq, hq0⟩ := h2
    have hpq : (MvPolynomial.aeval x) (p * q) = 0 := hx (p * q) (Ideal.mul_mem_mul hp hq)
    rw [map_mul] at hpq
    rcases mul_eq_zero.mp hpq with h | h
    · exact hp0 h
    · exact hq0 h
  · intro x hx
    rcases hx with h | h
    · exact fun p hp => h p (Ideal.mul_le_left hp)
    · exact fun p hp => h p (Ideal.mul_le_right hp)

lemma zarClosed_sInter {A : Set (Set (Fin n → k))} (hA : A ⊆ zarClosed k n) :
    ⋂₀ A ∈ zarClosed k n := by
  refine ⟨MvPolynomial.vanishingIdeal k (⋂₀ A),
    le_antisymm (MvPolynomial.zeroLocus_vanishingIdeal_le _) ?_⟩
  intro x hx s hs
  obtain ⟨I, hI⟩ := hA hs
  rw [hI]
  intro p hp
  exact hx p fun y hy => by
    have hy' : y ∈ MvPolynomial.zeroLocus k I := hI ▸ (hy s hs)
    exact hy' p hp

lemma zarClosed_union {s t : Set (Fin n → k)} (hs : s ∈ zarClosed k n)
    (ht : t ∈ zarClosed k n) : s ∪ t ∈ zarClosed k n := by
  obtain ⟨I, rfl⟩ := hs
  obtain ⟨J, rfl⟩ := ht
  exact ⟨I * J, (zeroLocus_mul k n I J).symm⟩

/-- The Zariski topology on affine `n`-space over `k`. -/
noncomputable instance : TopologicalSpace (Fin n → k) :=
  TopologicalSpace.ofClosed (zarClosed k n) (zarClosed_empty k n)
    (fun A hA => zarClosed_sInter k n hA) (fun a ha b hb => zarClosed_union k n ha hb)

lemma isOpen_iff_zarClosed {s : Set (Fin n → k)} : IsOpen s ↔ sᶜ ∈ zarClosed k n :=
  Iff.rfl

lemma isClosed_iff_zarClosed {s : Set (Fin n → k)} : IsClosed s ↔ s ∈ zarClosed k n := by
  rw [← isOpen_compl_iff, isOpen_iff_zarClosed, compl_compl]

lemma isClosed_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    IsClosed (MvPolynomial.zeroLocus k I) := by
  rw [isClosed_iff_zarClosed]
  exact ⟨I, rfl⟩

end Zariski

section Dictionary

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

lemma vanishingIdeal_singleton_mem_zeroLocus_iff (x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    p ∈ MvPolynomial.vanishingIdeal k {x} ↔ (MvPolynomial.aeval x) p = 0 :=
  MvPolynomial.mem_vanishingIdeal_singleton_iff x p

/-- The zero locus of a prime ideal is an irreducible closed set. -/
lemma zeroLocus_irreducible {P : Ideal (MvPolynomial (Fin n) k)} (hP : P.IsPrime) :
    IsIrreducible (MvPolynomial.zeroLocus k P) := by
  haveI := hP
  have hIV : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) = P :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
  constructor
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) P
    rw [hempty, MvPolynomial.vanishingIdeal_empty] at h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ P := by
      rw [← hP.radical, ← h]
      exact Submodule.mem_top
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z1 z2 hz1 hz2 hsub
    rw [isClosed_iff_zarClosed] at hz1 hz2
    obtain ⟨I, hI⟩ := hz1
    obtain ⟨J, hJ⟩ := hz2
    have hIJ : I * J ≤ P := by
      rw [← hIV, ← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, zeroLocus_mul]
      rw [hI, hJ] at hsub
      exact hsub
    rcases (Ideal.IsPrime.mul_le hP).mp hIJ with h | h
    · left
      rw [hI]
      exact MvPolynomial.zeroLocus_anti_mono h
    · right
      rw [hJ]
      exact MvPolynomial.zeroLocus_anti_mono h

/-- The vanishing ideal of an irreducible closed set is prime. -/
lemma vanishingIdeal_isPrime {Z : Set (Fin n → k)} (hZc : IsClosed Z) (hZi : IsIrreducible Z) :
    (MvPolynomial.vanishingIdeal k Z).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ MvPolynomial.vanishingIdeal k Z := h ▸ Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have hz1 : ((1 : MvPolynomial (Fin n) k) : MvPolynomial (Fin n) k) ∈
          MvPolynomial.vanishingIdeal k Z := h1
      have := (MvPolynomial.mem_vanishingIdeal_iff).mp hz1 z hz
      simp at this
    rw [hempty] at hZi
    exact hZi.1.ne_empty rfl
  · intro x y hxy
    by_contra h
    simp only [not_or] at h
    obtain ⟨hx, hy⟩ := h
    have hcover : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {x}) ∪
        MvPolynomial.zeroLocus k (Ideal.span {y}) := by
      intro z hz
      have hxyz : (MvPolynomial.aeval z) (x * y) = 0 := hxy z hz
      rw [map_mul] at hxyz
      rcases mul_eq_zero.mp hxyz with h' | h'
      · left
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
      · right
        rw [MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        rw [Ideal.mem_span_singleton] at hp
        obtain ⟨c, rfl⟩ := hp
        rw [map_mul, h']
        simp
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hZi.2) _ _
      (isClosed_zeroLocus k n (Ideal.span {x})) (isClosed_zeroLocus k n (Ideal.span {y})) hcover
      with h' | h'
    · exact hx fun z hz => h' hz x (Ideal.mem_span_singleton_self x)
    · exact hy fun z hz => h' hz y (Ideal.mem_span_singleton_self y)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_radical (I : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
  refine le_antisymm (MvPolynomial.zeroLocus_anti_mono Ideal.le_radical) ?_
  calc MvPolynomial.zeroLocus k I ⊆
        MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) :=
        MvPolynomial.zeroLocus_vanishingIdeal_le _
    _ ⊆ MvPolynomial.zeroLocus k I.radical :=
        MvPolynomial.zeroLocus_anti_mono (MvPolynomial.radical_le_vanishingIdeal_zeroLocus I)

/-- A closed set is the zero locus of its vanishing ideal. -/
lemma zeroLocus_vanishingIdeal_of_isClosed {Z : Set (Fin n → k)} (hZ : IsClosed Z) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z) = Z := by
  rw [isClosed_iff_zarClosed] at hZ
  obtain ⟨I, rfl⟩ := hZ
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, zeroLocus_radical]

end Dictionary

section Dimension

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- The dimension of an affine algebraic set, as the supremum of the lengths of chains of
irreducible closed subsets (Hartshorne I.1). -/
noncomputable def varietyDim (Y : Set (Fin n → k)) : WithBot ℕ∞ :=
  Order.krullDim {Z : Set (Fin n → k) // Z ⊆ Y ∧ IsIrreducible Z ∧ IsClosed Z}

/-- The dimension of the affine algebraic set defined by an ideal equals the Krull dimension of the
coordinate ring. -/
theorem varietyDim_zeroLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    varietyDim k n (MvPolynomial.zeroLocus k I) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
  have key : ∀ (Z : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z}), I ≤ MvPolynomial.vanishingIdeal k Z.1 := by
    rintro ⟨Z, hZ, -, -⟩
    rw [← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
    exact hZ
  set F : {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧
      IsClosed Z} → (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    fun Z => OrderDual.toDual
      ⟨⟨MvPolynomial.vanishingIdeal k Z.1, vanishingIdeal_isPrime k n Z.2.2.2 Z.2.2.1⟩, key Z⟩ with hF
  set G : (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ →
      {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧ IsIrreducible Z ∧ IsClosed Z} :=
    fun p => ⟨MvPolynomial.zeroLocus k (OrderDual.ofDual p).1.asIdeal,
      ⟨fun x hx => by
        rw [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
        exact fun q hq => hx q ((OrderDual.ofDual p).2 hq),
       zeroLocus_irreducible k n (OrderDual.ofDual p).1.isPrime,
       isClosed_zeroLocus k n _⟩⟩ with hG
  have hFinj : Function.Injective F := by
    intro Z1 Z2 heq
    have h1 : MvPolynomial.vanishingIdeal k Z1.1 = MvPolynomial.vanishingIdeal k Z2.1 := by
      have := congrArg (fun x => (OrderDual.ofDual x : ↥(PrimeSpectrum.zeroLocus
        (I : Set (MvPolynomial (Fin n) k)))).1.asIdeal) heq
      simpa [hF] using this
    have hZ1 := zeroLocus_vanishingIdeal_of_isClosed k n Z1.2.2.2
    have hZ2 := zeroLocus_vanishingIdeal_of_isClosed k n Z2.2.2.2
    exact Subtype.ext (by rw [← hZ1, ← hZ2, h1])
  have hFmono : Monotone F := by
    intro Z1 Z2 hle
    simp only [hF, OrderDual.toDual_le_toDual]
    exact Subtype.mk_le_mk.mpr
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (MvPolynomial.vanishingIdeal_anti_mono hle))
  have hGinj : Function.Injective G := by
    intro p1 p2 heq
    have h1 : MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal =
        MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal := by
      have := congrArg Subtype.val heq
      simpa [hG] using this
    have h2 : (OrderDual.ofDual p1).1.asIdeal = (OrderDual.ofDual p2).1.asIdeal := by
      have e1 : (OrderDual.ofDual p1).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p1).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      have e2 : (OrderDual.ofDual p2).1.asIdeal = MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k (OrderDual.ofDual p2).1.asIdeal) :=
        (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _).symm
      rw [e1, e2, h1]
    have : (OrderDual.ofDual p1).1 = (OrderDual.ofDual p2).1 := PrimeSpectrum.ext h2
    have : OrderDual.ofDual p1 = OrderDual.ofDual p2 := Subtype.ext this
    exact OrderDual.ofDual.injective this
  have hGmono : Monotone G := by
    intro p1 p2 hle
    have hlt : OrderDual.ofDual p2 ≤ OrderDual.ofDual p1 := hle
    have h2 : (OrderDual.ofDual p2).1.asIdeal ≤ (OrderDual.ofDual p1).1.asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt
    exact MvPolynomial.zeroLocus_anti_mono h2
  have hmain : Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} ≤
      Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ :=
    Order.krullDim_le_of_strictMono F (hFmono.strictMono_of_injective hFinj)
  have hmain2 : Order.krullDim (↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))))ᵒᵈ ≤
      Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
        IsIrreducible Z ∧ IsClosed Z} :=
    Order.krullDim_le_of_strictMono G (hGmono.strictMono_of_injective hGinj)
  have hiso : Order.krullDim ↥(PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin n) k))) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ I) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  show Order.krullDim {Z : Set (Fin n → k) // Z ⊆ MvPolynomial.zeroLocus k I ∧
      IsIrreducible Z ∧ IsClosed Z} = ringKrullDim (MvPolynomial (Fin n) k ⧸ I)
  rw [le_antisymm hmain hmain2, Order.krullDim_orderDual]
  exact hiso

end Dimension

section Main

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- **Hartshorne, Algebraic Geometry, Exercise I.1.8.**  Let `Y` be an irreducible affine variety
of dimension `r` in `A^n` and let `H = V(f)` be a hypersurface, with `Y ⊄ H`.  Then every
irreducible component `Z` of `Y ∩ H` has dimension `r - 1`; equivalently `dim Z + 1 = dim Y`. -/
theorem hartshorne_exercise_I_1_8
    (Y : Set (Fin n → k)) (f : MvPolynomial (Fin n) k)
    (hYc : IsClosed Y) (hYi : IsIrreducible Y) (hf : f ≠ 0)
    (hne : ∃ y ∈ Y, (MvPolynomial.aeval y) f ≠ 0)
    (Z : Set (Fin n → k)) (hZY : Z ⊆ Y)
    (hZf : Z ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}))
    (hZi : IsIrreducible Z) (hZc : IsClosed Z)
    (hZmax : ∀ W : Set (Fin n → k), W ⊆ Y → W ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) →
      IsIrreducible W → IsClosed W → Z ⊆ W → W ⊆ Z) :
    varietyDim k n Z + 1 = varietyDim k n Y := by
  set IY := MvPolynomial.vanishingIdeal k Y with hIY
  set q := MvPolynomial.vanishingIdeal k Z with hq
  haveI hYprime : IY.IsPrime := vanishingIdeal_isPrime k n hYc hYi
  haveI hqprime : q.IsPrime := vanishingIdeal_isPrime k n hZc hZi
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ IY) := Ideal.Quotient.isDomain _
  have hIYq : IY ≤ q := MvPolynomial.vanishingIdeal_anti_mono hZY
  have hfq : f ∈ q := fun z hz => hZf hz f (Ideal.mem_span_singleton_self f)
  have hYeq : MvPolynomial.zeroLocus k IY = Y := zeroLocus_vanishingIdeal_of_isClosed k n hYc
  -- ## `q` is minimal over `IY ⊔ (f)`
  have hmin : q ∈ (IY ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqprime, sup_le hIYq ((Ideal.span_singleton_le_iff_mem _).mpr hfq)⟩, ?_⟩
    rintro q' ⟨hq'prime, hq'le⟩ hq'q
    haveI := hq'prime
    have h1 : IY ≤ q' := le_trans le_sup_left hq'le
    have hspanle : (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)) ≤ IY ⊔ Ideal.span {f} :=
      le_sup_of_le_right (le_refl (Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)))
    have hWY : MvPolynomial.zeroLocus k q' ⊆ Y := by
      rw [← hYeq]
      exact MvPolynomial.zeroLocus_anti_mono h1
    have hWf : MvPolynomial.zeroLocus k q' ⊆ MvPolynomial.zeroLocus k (Ideal.span {f}) :=
      MvPolynomial.zeroLocus_anti_mono (le_trans hspanle hq'le)
    have hWirr : IsIrreducible (MvPolynomial.zeroLocus k q') := zeroLocus_irreducible k n hq'prime
    have hWc : IsClosed (MvPolynomial.zeroLocus k q') := isClosed_zeroLocus k n _
    have hZW : Z ⊆ MvPolynomial.zeroLocus k q' := by
      rw [← zeroLocus_vanishingIdeal_of_isClosed k n hZc]
      exact MvPolynomial.zeroLocus_anti_mono hq'q
    have hWZ : MvPolynomial.zeroLocus k q' ⊆ Z := hZmax _ hWY hWf hWirr hWc hZW
    have h4 : q ≤ q' := by
      have h5 : MvPolynomial.vanishingIdeal k Z ≤ MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k q') :=
        MvPolynomial.vanishingIdeal_anti_mono (k := k) (K := k) hWZ
      have h6 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k q') = q' :=
        MvPolynomial.IsPrime.vanishingIdeal_zeroLocus q'
      rw [h6, ← hq] at h5
      exact h5
    exact h4
  -- ## pass to the coordinate ring of `Y`
  set t : MvPolynomial (Fin n) k ⧸ IY := Ideal.Quotient.mk IY f with ht
  set P : Ideal (MvPolynomial (Fin n) k ⧸ IY) := q.map (Ideal.Quotient.mk IY) with hP
  haveI hPprime : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIYq
  have hcomap : Ideal.comap (Ideal.Quotient.mk IY) P = q := by
    rw [hP, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have hb : Ideal.comap (Ideal.Quotient.mk IY) (⊥ : Ideal (MvPolynomial (Fin n) k ⧸ IY)) = IY := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [hb, sup_of_le_left hIYq]
  have ht0 : t ≠ 0 := by
    intro h0
    have hmem : f ∈ IY := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← ht]
      exact h0
    obtain ⟨y, hy, hfy⟩ := hne
    exact hfy (mem_vanishingIdeal_iff.mp hmem y hy)
  have htP : t ∈ P := by
    rw [ht, hP]
    exact Ideal.mem_map_of_mem _ hfq
  have htunit : ¬ IsUnit t := by
    intro hunit
    have hspan : Ideal.span {t} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr htP
    have hPtop : P = ⊤ := top_le_iff.mp (hspan ▸ hle)
    have hqtop : q = ⊤ := by
      have h1 : Ideal.comap (Ideal.Quotient.mk IY) P = ⊤ := by rw [hPtop]; simp
      rw [hcomap] at h1
      exact h1
    have h1q : (1 : MvPolynomial (Fin n) k) ∈ q := by rw [hqtop]; exact Submodule.mem_top
    have hempty : Z = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have h2 := (MvPolynomial.mem_vanishingIdeal_iff.mp h1q) z hz
      simp at h2
    exact hZi.1.ne_empty hempty
  have hPmin : P ∈ (Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨hPprime, (Ideal.span_singleton_le_iff_mem _).mpr htP⟩, ?_⟩
    rintro P' ⟨hP'prime, hP'le⟩ hP'P
    haveI := hP'prime
    have hq'le : (IY ⊔ Ideal.span {f}) ≤ Ideal.comap (Ideal.Quotient.mk IY) P' := by
      refine sup_le ?_ ?_
      · exact Ideal.le_comap_of_map_le (by
          rw [Ideal.map_quotient_self]
          exact bot_le)
      · refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
        have h8 : t ∈ P' := hP'le (Ideal.mem_span_singleton_self t)
        rwa [ht] at h8
    have hq'q : Ideal.comap (Ideal.Quotient.mk IY) P' ≤ q := by
      rw [← hcomap]
      exact Ideal.comap_mono hP'P
    have hqle : q ≤ Ideal.comap (Ideal.Quotient.mk IY) P' :=
      hmin.2 ⟨Ideal.IsPrime.comap (Ideal.Quotient.mk IY), hq'le⟩ hq'q
    have hfin : P ≤ P' := by
      have h7 : P ≤ (Ideal.comap (Ideal.Quotient.mk IY) P').map (Ideal.Quotient.mk IY) := by
        rw [hP]
        exact Ideal.map_mono hqle
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h7
    exact hfin
  -- ## the algebraic input
  have hmain := ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes k ht0 htunit hPmin
  -- ## the two dimensions
  have hZq : MvPolynomial.zeroLocus k q = Z := zeroLocus_vanishingIdeal_of_isClosed k n hZc
  have h1 : varietyDim k n Z = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) := by
    rw [← hZq]
    exact varietyDim_zeroLocus k n q
  have h2 : varietyDim k n Y = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := by
    rw [← hYeq]
    exact varietyDim_zeroLocus k n IY
  have hiso : ringKrullDim (MvPolynomial (Fin n) k ⧸ q) =
      ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) := by
    have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk IY)) = q := by
      ext x
      show (Ideal.Quotient.mk P) ((Ideal.Quotient.mk IY) x) = 0 ↔ x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hcomap, Ideal.mem_comap]
    have hiso' : (MvPolynomial (Fin n) k ⧸ q) ≃+* ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
    exact ringKrullDim_eq_of_ringEquiv hiso'
  calc varietyDim k n Z + 1 = ringKrullDim (MvPolynomial (Fin n) k ⧸ q) + 1 := by rw [h1]
    _ = ringKrullDim ((MvPolynomial (Fin n) k ⧸ IY) ⧸ P) + 1 := by rw [hiso]
    _ = ringKrullDim (MvPolynomial (Fin n) k ⧸ IY) := hmain
    _ = varietyDim k n Y := h2.symm

end Main

#print axioms Hartshorne77.Ex_I_1_8.hartshorne_exercise_I_1_8
#print axioms Hartshorne77.Ex_I_1_8.ringKrullDim_quotient_add_one_eq_of_mem_minimalPrimes
#print axioms Hartshorne77.Ex_I_1_8.varietyDim_zeroLocus
#print axioms Hartshorne77.Ex_I_1_8.MvPolynomial.ringKrullDim_quotient_span_singleton
#print axioms Hartshorne77.Ex_I_1_8.vanishingIdeal_isPrime
#print axioms Hartshorne77.Ex_I_1_8.ringKrullDim_eq_of_integral_injective
#print axioms Hartshorne77.Ex_I_1_8.zeroLocus_irreducible
#print axioms Hartshorne77.Ex_I_1_8.vanishingIdeal_singleton_height
