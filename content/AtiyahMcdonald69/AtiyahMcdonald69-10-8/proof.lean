import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section
open MvPowerSeries
open scoped ENNReal

namespace AtiyahMcdonald69.Ex_10_8

variable {σ : Type*}

/-- The `ℓ¹`-majorant `∑ ‖f_α‖ r^{|α|}` of a formal power series at radius `r`. -/
def l1 (r : NNReal) (f : MvPowerSeries σ ℂ) : ℝ≥0∞ :=
  ∑' α : σ →₀ ℕ, ENNReal.ofReal ‖coeff α f‖ * (r : ℝ≥0∞) ^ (Finsupp.degree α)

section basics

variable {r r' : NNReal} {f g : MvPowerSeries σ ℂ}

lemma l1_congr_coeff (h : ∀ α, ‖coeff α f‖ ≤ ‖coeff α g‖) : l1 r f ≤ l1 r g :=
  ENNReal.tsum_le_tsum fun α => mul_le_mul_left (ENNReal.ofReal_le_ofReal (h α)) _

lemma l1_mono_radius (h : r' ≤ r) : l1 r' f ≤ l1 r f := by
  refine ENNReal.tsum_le_tsum fun α => ?_
  refine mul_le_mul_right ?_ _
  exact pow_le_pow_left' (by exact_mod_cast h) _

lemma l1_add_le : l1 r (f + g) ≤ l1 r f + l1 r g := by
  simp only [l1]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun α => ?_
  rw [map_add]
  refine (mul_le_mul_left (ENNReal.ofReal_le_ofReal (norm_add_le _ _)) _).trans ?_
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), add_mul]

end basics

section mul

lemma tsum_antidiagonal {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
    (H : A × A → ℝ≥0∞) :
    (∑' n : A, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, H p) = ∑' p : A × A, H p := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := A)).tsum_eq H,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  simp [Finset.sum_attach]

lemma tsum_prod_mul {F G : (σ →₀ ℕ) → ℝ≥0∞} :
    (∑' p : (σ →₀ ℕ) × (σ →₀ ℕ), F p.1 * G p.2) = (∑' a, F a) * (∑' b, G b) := by
  rw [ENNReal.tsum_prod (f := fun a b => F a * G b)]
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

lemma l1_mul_le [DecidableEq σ] (r : NNReal) (f g : MvPowerSeries σ ℂ) :
    l1 r (f * g) ≤ l1 r f * l1 r g := by
  have step1 : l1 r (f * g) ≤
      ∑' α : σ →₀ ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal α,
        (ENNReal.ofReal ‖coeff p.1 f‖ * (r : ℝ≥0∞) ^ (Finsupp.degree p.1)) *
        (ENNReal.ofReal ‖coeff p.2 g‖ * (r : ℝ≥0∞) ^ (Finsupp.degree p.2)) := by
    refine ENNReal.tsum_le_tsum fun α => ?_
    rw [coeff_mul]
    refine (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (norm_sum_le _ _)) _).trans_eq ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = α := by simpa using hp
    have hdeg : Finsupp.degree α = Finsupp.degree p.1 + Finsupp.degree p.2 := by
      rw [← map_add Finsupp.degree, hp']
    rw [hdeg, pow_add, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    ring
  refine step1.trans_eq ?_
  rw [tsum_antidiagonal]
  unfold l1
  exact tsum_prod_mul (F := fun a => ENNReal.ofReal ‖coeff a f‖ * (r : ℝ≥0∞) ^ (Finsupp.degree a))
    (G := fun a => ENNReal.ofReal ‖coeff a g‖ * (r : ℝ≥0∞) ^ (Finsupp.degree a))

end mul

section subring

lemma l1_monomial [DecidableEq σ] (r : NNReal) (m : σ →₀ ℕ) (a : ℂ) :
    l1 r (monomial m a : MvPowerSeries σ ℂ)
      = ENNReal.ofReal ‖a‖ * (r : ℝ≥0∞) ^ (Finsupp.degree m) := by
  rw [l1]
  rw [tsum_eq_single m]
  · rw [coeff_monomial_same]
  · intro b hb
    rw [coeff_monomial, if_neg hb, norm_zero, ENNReal.ofReal_zero, zero_mul]

lemma l1_one [DecidableEq σ] : l1 (1 : NNReal) (1 : MvPowerSeries σ ℂ) = 1 := by
  have h := l1_monomial (σ := σ) (1 : NNReal) 0 (1 : ℂ)
  simpa using h

end subring



/-! ## The subring of convergent power series -/

section subring

variable {σ : Type*} [DecidableEq σ]

/-- The subring of power series converging on a neighbourhood of the origin. -/
def ConvPS (σ : Type*) [DecidableEq σ] : Subring (MvPowerSeries σ ℂ) where
  carrier := {f | ∃ r : NNReal, 0 < r ∧ l1 r f ≠ ⊤}
  one_mem' := ⟨1, one_pos, by rw [l1_one]; simp⟩
  zero_mem' := ⟨1, one_pos, by simp [l1]⟩
  mul_mem' := by
    rintro f g ⟨r, hr, hf⟩ ⟨s, hs, hg⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ ?_) (l1_mul_le _ f g)
    · exact ne_top_of_le_ne_top hf (l1_mono_radius (min_le_left _ _))
    · exact ne_top_of_le_ne_top hg (l1_mono_radius (min_le_right _ _))
  add_mem' := by
    rintro f g ⟨r, hr, hf⟩ ⟨s, hs, hg⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩) (l1_add_le (r := min r s))
    · exact ne_top_of_le_ne_top hf (l1_mono_radius (min_le_left _ _))
    · exact ne_top_of_le_ne_top hg (l1_mono_radius (min_le_right _ _))
  neg_mem' := by
    rintro f ⟨r, hr, hf⟩
    refine ⟨r, hr, ne_top_of_le_ne_top hf (l1_congr_coeff ?_)⟩
    intro α
    rw [map_neg, norm_neg]

/-- Vanishing of the coefficients of total degree `< k`. -/
def VanishBelow (k : ℕ) (f : MvPowerSeries σ ℂ) : Prop :=
  ∀ α, Finsupp.degree α < k → coeff α f = 0

omit [DecidableEq σ] in
lemma vanishBelow_zero (f : MvPowerSeries σ ℂ) : VanishBelow 0 f := by
  intro α h; omega

lemma vanishBelow_mono {k l : ℕ} (hkl : k ≤ l) {f : MvPowerSeries σ ℂ}
    (hf : VanishBelow l f) : VanishBelow k f :=
  fun α hα => hf α (by omega)

lemma vanishBelow_mul {k l : ℕ} {f g : MvPowerSeries σ ℂ}
    (hf : VanishBelow k f) (hg : VanishBelow l g) : VanishBelow (k + l) (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  have hdeg : Finsupp.degree α = Finsupp.degree p.1 + Finsupp.degree p.2 := by
    rw [← map_add Finsupp.degree, hp']
  rcases lt_or_ge (Finsupp.degree p.1) k with h1 | h1
  · rw [hf p.1 h1]; simp
  · rw [hg p.2 (by omega)]; simp

lemma vanishBelow_pow {f : MvPowerSeries σ ℂ} (hf : VanishBelow 1 f) (m : ℕ) :
    VanishBelow m (f ^ m) := by
  induction m with
  | zero => simpa using vanishBelow_zero (1 : MvPowerSeries σ ℂ)
  | succ m ih =>
    rw [pow_succ]
    have := vanishBelow_mul ih hf
    simpa [Nat.succ_eq_add_one] using this

end subring


/-! ## Splitting off one variable -/

section decomp

variable [DecidableEq σ] [Fintype σ]

/-- The series whose `β`-th coefficient is `(β_i+1)/(|β|+1) * f_{β+e_i}`. -/
def shiftCoeff (f : MvPowerSeries σ ℂ) (i : σ) : MvPowerSeries σ ℂ :=
  fun β => ((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1) * coeff (β + Finsupp.single i 1) f

lemma coeff_shiftCoeff (f : MvPowerSeries σ ℂ) (i : σ) (β : σ →₀ ℕ) :
    coeff β (shiftCoeff f i) =
      ((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1) * coeff (β + Finsupp.single i 1) f :=
  rfl

lemma X_eq_monomial (i : σ) :
    (X i : MvPowerSeries σ ℂ) = monomial (Finsupp.single i 1) (1 : ℂ) := rfl

lemma coeff_X_mul (i : σ) (h : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) :
    coeff α (X i * h) =
      if Finsupp.single i 1 ≤ α then coeff (α - Finsupp.single i 1) h else 0 := by
  rw [X_eq_monomial, coeff_monomial_mul]
  simp

lemma sum_X_mul_shiftCoeff (f : MvPowerSeries σ ℂ) (h0 : coeff (0 : σ →₀ ℕ) f = 0) :
    (∑ i, X i * shiftCoeff f i) = f := by
  ext α
  rw [map_sum]
  simp only [coeff_X_mul]
  by_cases hα : α = 0
  · subst hα
    rw [h0]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by
      intro h
      have := Finsupp.single_le_iff.mp h
      simp at this)]
  · have hd : Finsupp.degree α ≠ 0 := by
      simpa [Finsupp.degree_eq_zero_iff] using hα
    have key : ∀ i ∈ (Finset.univ : Finset σ),
        (if Finsupp.single i 1 ≤ α then coeff (α - Finsupp.single i 1) (shiftCoeff f i) else 0)
          = (α i : ℂ) / ((Finsupp.degree α : ℕ) : ℂ) * coeff α f := by
      intro i _
      by_cases hi : Finsupp.single i 1 ≤ α
      · rw [if_pos hi]
        have hai : α i ≠ 0 := by
          have h : 1 ≤ α i := Finsupp.single_le_iff.mp hi
          omega
        have hsub : (α - Finsupp.single i 1 : σ →₀ ℕ) + Finsupp.single i 1 = α :=
          Finsupp.sub_add_single_one_cancel hai
        have hdeg : Finsupp.degree (α - Finsupp.single i 1 : σ →₀ ℕ) + 1 = Finsupp.degree α := by
          have := congrArg Finsupp.degree hsub
          simpa using this
        have hcoord : ((α - Finsupp.single i 1 : σ →₀ ℕ)) i = α i - 1 := by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        rw [coeff_shiftCoeff, hsub, hcoord]
        have h1 : (↑(α i - 1) : ℂ) + 1 = (α i : ℂ) := by
          have h' : α i - 1 + 1 = α i := Nat.sub_add_cancel (by omega : 1 ≤ α i)
          rw [← h']; push_cast; ring
        have h2 : (↑(Finsupp.degree (α - Finsupp.single i 1 : σ →₀ ℕ)) : ℂ) + 1
            = (↑(Finsupp.degree α) : ℂ) := by
          rw [← hdeg]; push_cast; ring
        rw [h1, h2]
      · rw [if_neg hi]
        have h0i : α i = 0 := by
          have h2 : ¬ (1 ≤ α i) := fun h => hi (Finsupp.single_le_iff.mpr h)
          omega
        rw [h0i, Nat.cast_zero, zero_div, zero_mul]
    rw [Finset.sum_congr rfl key]
    rw [← Finset.sum_mul, ← Finset.sum_div]
    have hsum : (∑ i : σ, (α i : ℂ)) = ((Finsupp.degree α : ℕ) : ℂ) := by
      rw [Finsupp.degree_eq_sum]
      push_cast
      rfl
    rw [hsum]
    have hd' : ((Finsupp.degree α : ℕ) : ℂ) ≠ 0 := by
      simpa using hd
    rw [div_self hd', one_mul]

/-- The scalar factor occurring in `shiftCoeff` has norm at most one. -/
lemma norm_shiftFactor_le_one (β : σ →₀ ℕ) (i : σ) :
    ‖((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1)‖ ≤ 1 := by
  have hcast : ((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1)
      = ((((β i : ℝ) + 1) / (((Finsupp.degree β : ℕ) : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hnn : 0 ≤ ((β i : ℝ) + 1) / (((Finsupp.degree β : ℕ) : ℝ) + 1) :=
    div_nonneg (by positivity) (by positivity)
  refine ⟨by linarith, ?_⟩
  rw [div_le_one (by positivity)]
  have := Finsupp.le_degree i β
  have h' : ((β i : ℕ) : ℝ) ≤ ((Finsupp.degree β : ℕ) : ℝ) := by exact_mod_cast this
  linarith

lemma mul_l1_shiftCoeff_le (r : NNReal) (f : MvPowerSeries σ ℂ) (i : σ) :
    (r : ℝ≥0∞) * l1 r (shiftCoeff f i) ≤ l1 r f := by
  have hterm : ∀ β : σ →₀ ℕ,
      (r : ℝ≥0∞) *
          (ENNReal.ofReal ‖coeff β (shiftCoeff f i)‖ * (r : ℝ≥0∞) ^ Finsupp.degree β)
        ≤ ENNReal.ofReal ‖coeff (β + Finsupp.single i 1) f‖ *
            (r : ℝ≥0∞) ^ Finsupp.degree (β + Finsupp.single i 1) := by
    intro β
    rw [coeff_shiftCoeff]
    have hn : ENNReal.ofReal
        ‖((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1) * coeff (β + Finsupp.single i 1) f‖
        ≤ ENNReal.ofReal ‖coeff (β + Finsupp.single i 1) f‖ := by
      refine ENNReal.ofReal_le_ofReal ?_
      refine (norm_mul _ _).trans_le ?_
      refine (mul_le_mul_of_nonneg_right (norm_shiftFactor_le_one β i) (norm_nonneg _)).trans ?_
      rw [one_mul]
    calc (r : ℝ≥0∞) *
          (ENNReal.ofReal ‖((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1) *
            coeff (β + Finsupp.single i 1) f‖ * (r : ℝ≥0∞) ^ Finsupp.degree β)
        = ENNReal.ofReal ‖((β i : ℂ) + 1) / (((Finsupp.degree β : ℕ) : ℂ) + 1) *
            coeff (β + Finsupp.single i 1) f‖ *
          ((r : ℝ≥0∞) * (r : ℝ≥0∞) ^ Finsupp.degree β) := by ring
      _ ≤ ENNReal.ofReal ‖coeff (β + Finsupp.single i 1) f‖ *
          ((r : ℝ≥0∞) * (r : ℝ≥0∞) ^ Finsupp.degree β) := by gcongr
      _ = ENNReal.ofReal ‖coeff (β + Finsupp.single i 1) f‖ *
          (r : ℝ≥0∞) ^ Finsupp.degree (β + Finsupp.single i 1) := by
        rw [map_add, Finsupp.degree_single, pow_succ]
        ring
  have h1 : (r : ℝ≥0∞) * l1 r (shiftCoeff f i)
      = ∑' β, (r : ℝ≥0∞) *
          (ENNReal.ofReal ‖coeff β (shiftCoeff f i)‖ * (r : ℝ≥0∞) ^ Finsupp.degree β) := by
    rw [l1, ENNReal.tsum_mul_left]
  rw [h1]
  calc ∑' β, (r : ℝ≥0∞) *
        (ENNReal.ofReal ‖coeff β (shiftCoeff f i)‖ * (r : ℝ≥0∞) ^ Finsupp.degree β)
      ≤ ∑' β, ENNReal.ofReal ‖coeff (β + Finsupp.single i 1) f‖ *
          (r : ℝ≥0∞) ^ Finsupp.degree (β + Finsupp.single i 1) := ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' α, ENNReal.ofReal ‖coeff α f‖ * (r : ℝ≥0∞) ^ Finsupp.degree α :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun a : σ →₀ ℕ => a + Finsupp.single i 1) (fun a b hab => by simpa using hab) _
    _ = l1 r f := rfl

lemma shiftCoeff_mem (f : MvPowerSeries σ ℂ) (hf : f ∈ ConvPS σ) (i : σ) :
    shiftCoeff f i ∈ ConvPS σ := by
  obtain ⟨r, hr, hlt⟩ := hf
  refine ⟨r, hr, ?_⟩
  intro htop
  have hpos : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have h := mul_l1_shiftCoeff_le (σ := σ) r f i
  rw [htop, ENNReal.mul_top hpos] at h
  exact hlt (top_le_iff.mp h)

/-! ## The Neumann series and the unit criterion -/

lemma l1_one' (r : NNReal) : l1 r (1 : MvPowerSeries σ ℂ) = 1 := by
  have h := l1_monomial (σ := σ) r 0 (1 : ℂ)
  simpa using h

lemma l1_neg' (r : NNReal) (f : MvPowerSeries σ ℂ) : l1 r (-f) = l1 r f := by
  refine le_antisymm (l1_congr_coeff fun α => by simp) (l1_congr_coeff fun α => ?_)
  rw [map_neg, norm_neg]

lemma l1_pow_le (r : NNReal) (f : MvPowerSeries σ ℂ) (k : ℕ) :
    l1 r (f ^ k) ≤ (l1 r f) ^ k := by
  induction k with
  | zero => simp [l1_one']
  | succ k ih =>
    calc l1 r (f ^ k * f) ≤ l1 r (f ^ k) * l1 r f := l1_mul_le r _ _
      _ ≤ (l1 r f) ^ k * l1 r f := mul_le_mul_left ih _
      _ = (l1 r f) ^ (k + 1) := by rw [pow_succ]

lemma l1_mul_radius_le {r : NNReal} (t : NNReal) (ht : t ≤ 1) (f : MvPowerSeries σ ℂ)
    (h0 : MvPowerSeries.constantCoeff f = 0) : l1 (t * r) f ≤ (t : ℝ≥0∞) * l1 r f := by
  have hmain : l1 (t * r) f ≤
      ∑' α, (t : ℝ≥0∞) * (ENNReal.ofReal ‖coeff α f‖ * (r : ℝ≥0∞) ^ Finsupp.degree α) := by
    rw [l1]
    refine ENNReal.tsum_le_tsum fun α => ?_
    by_cases hα : coeff α f = 0
    · simp [hα]
    · have hd : 1 ≤ Finsupp.degree α := by
        rcases Nat.eq_zero_or_pos (Finsupp.degree α) with h0' | h0'
        · exfalso
          apply hα
          have hz : α = 0 := by
            rw [← Finsupp.degree_eq_zero_iff]
            exact h0'
          rw [hz]
          simpa using h0
        · exact h0'
      rw [show ((t * r : NNReal) : ℝ≥0∞) = (t : ℝ≥0∞) * (r : ℝ≥0∞) from by push_cast; ring]
      rw [mul_pow]
      have ht' : (t : ℝ≥0∞) ^ Finsupp.degree α ≤ (t : ℝ≥0∞) := by
        obtain ⟨e, he⟩ : ∃ e, Finsupp.degree α = e + 1 := ⟨Finsupp.degree α - 1, by omega⟩
        rw [he, pow_succ]
        calc (t : ℝ≥0∞) ^ e * (t : ℝ≥0∞) ≤ 1 * (t : ℝ≥0∞) := by
              gcongr
              exact pow_le_one₀ (by positivity : (0 : ℝ≥0∞) ≤ t) (by exact_mod_cast ht : (t : ℝ≥0∞) ≤ 1)
          _ = (t : ℝ≥0∞) := one_mul _
      calc ENNReal.ofReal ‖coeff α f‖ *
            ((t : ℝ≥0∞) ^ Finsupp.degree α * (r : ℝ≥0∞) ^ Finsupp.degree α)
          = (t : ℝ≥0∞) ^ Finsupp.degree α *
              (ENNReal.ofReal ‖coeff α f‖ * (r : ℝ≥0∞) ^ Finsupp.degree α) := by ring
        _ ≤ (t : ℝ≥0∞) *
              (ENNReal.ofReal ‖coeff α f‖ * (r : ℝ≥0∞) ^ Finsupp.degree α) :=
            mul_le_mul_left ht' _
  rwa [ENNReal.tsum_mul_left] at hmain

/-- The coefficientwise Neumann series `∑_k (-h)^k` of a series with zero constant term. -/
def neuSeries (h : MvPowerSeries σ ℂ) : MvPowerSeries σ ℂ :=
  fun α => ∑ k ∈ Finset.range (Finsupp.degree α + 1), coeff α ((-h) ^ k)

lemma vanishBelow_neg {k : ℕ} {f : MvPowerSeries σ ℂ} (hf : VanishBelow k f) :
    VanishBelow k (-f) := by
  intro α hα
  rw [map_neg, hf α hα, neg_zero]

lemma vanishBelow_iff {f : MvPowerSeries σ ℂ} :
    VanishBelow 1 f ↔ MvPowerSeries.constantCoeff f = 0 := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h α hα
    have h0 : Finsupp.degree α = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff] at h0
    rw [h0]
    simpa using h

lemma coeff_finset_sum_pow (h : MvPowerSeries σ ℂ) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (∑ k ∈ Finset.range N, (-h) ^ k) = ∑ k ∈ Finset.range N, coeff α ((-h) ^ k) := by
  rw [map_sum]

lemma vanishBelow_neuSeries_sub_geom (h : MvPowerSeries σ ℂ)
    (h0 : MvPowerSeries.constantCoeff h = 0) (N : ℕ) :
    VanishBelow N (neuSeries h - ∑ k ∈ Finset.range N, (-h) ^ k) := by
  intro α hα
  have hc : coeff α (neuSeries h) =
      ∑ k ∈ Finset.range (Finsupp.degree α + 1), coeff α ((-h) ^ k) := rfl
  rw [map_sub, coeff_finset_sum_pow, hc]
  have hv : VanishBelow 1 (-h) := vanishBelow_neg (vanishBelow_iff.mpr h0)
  have key : ∀ k ∈ Finset.range N, k ∉ Finset.range (Finsupp.degree α + 1) →
      coeff α ((-h) ^ k) = 0 := by
    intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk'
    exact vanishBelow_pow hv k α (by omega)
  rw [← Finset.sum_subset (Finset.range_mono (by omega : Finsupp.degree α + 1 ≤ N)) key]
  exact sub_self _

lemma geom_mul_one_add (h : MvPowerSeries σ ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (-h) ^ k) * (1 + h) = 1 - (-h) ^ N := by
  have h1 : (-h - 1 : MvPowerSeries σ ℂ) = -(1 + h) := by ring
  have h2 := geom_sum_mul (-h) N
  rw [h1, mul_neg] at h2
  have h3 := congrArg Neg.neg h2
  simpa [neg_sub] using h3

lemma one_add_mul_neuSeries (h : MvPowerSeries σ ℂ)
    (h0 : MvPowerSeries.constantCoeff h = 0) : (1 + h) * neuSeries h = 1 := by
  ext α
  set N := Finsupp.degree α + 1 with hN
  have hvan : VanishBelow N (neuSeries h - ∑ k ∈ Finset.range N, (-h) ^ k) :=
    vanishBelow_neuSeries_sub_geom h h0 N
  have hprod : VanishBelow (0 + N)
      ((1 + h) * (neuSeries h - ∑ k ∈ Finset.range N, (-h) ^ k)) :=
    vanishBelow_mul (vanishBelow_zero _) hvan
  have hzero : coeff α ((1 + h) * (neuSeries h - ∑ k ∈ Finset.range N, (-h) ^ k)) = 0 :=
    hprod α (by omega)
  rw [mul_sub, map_sub, sub_eq_zero] at hzero
  rw [hzero, mul_comm (1 + h), geom_mul_one_add, map_sub]
  have hN' : coeff α ((-h) ^ N) = 0 := by
    have := vanishBelow_pow (vanishBelow_neg (vanishBelow_iff.mpr h0)) N
    exact this α (by omega)
  rw [hN', sub_zero]


lemma l1_neuSeries_le (r : NNReal) (h : MvPowerSeries σ ℂ)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    l1 r (neuSeries h) ≤ ∑' k : ℕ, (l1 r h) ^ k := by
  have hterm : ∀ α : σ →₀ ℕ,
      ENNReal.ofReal ‖coeff α (neuSeries h)‖ * (r : ℝ≥0∞) ^ Finsupp.degree α
        ≤ ∑' k : ℕ,
            ENNReal.ofReal ‖coeff α ((-h) ^ k)‖ * (r : ℝ≥0∞) ^ Finsupp.degree α := by
    intro α
    have hsum : coeff α (neuSeries h) =
        ∑ k ∈ Finset.range (Finsupp.degree α + 1), coeff α ((-h) ^ k) := rfl
    rw [hsum]
    have h1 : ENNReal.ofReal ‖∑ k ∈ Finset.range (Finsupp.degree α + 1), coeff α ((-h) ^ k)‖
        ≤ ENNReal.ofReal (∑ k ∈ Finset.range (Finsupp.degree α + 1),
            ‖coeff α ((-h) ^ k)‖) :=
      ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    refine (mul_le_mul_left h1 _).trans_eq ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _), Finset.sum_mul]
    rw [tsum_eq_sum (s := Finset.range (Finsupp.degree α + 1)) (by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      have hz : coeff α ((-h) ^ k) = 0 :=
        vanishBelow_pow (vanishBelow_neg (vanishBelow_iff.mpr h0)) k α (by omega)
      rw [hz]
      simp)]
  calc l1 r (neuSeries h)
      = ∑' α, ENNReal.ofReal ‖coeff α (neuSeries h)‖ * (r : ℝ≥0∞) ^ Finsupp.degree α := rfl
    _ ≤ ∑' α, ∑' k : ℕ,
          ENNReal.ofReal ‖coeff α ((-h) ^ k)‖ * (r : ℝ≥0∞) ^ Finsupp.degree α :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' k : ℕ, ∑' α,
          ENNReal.ofReal ‖coeff α ((-h) ^ k)‖ * (r : ℝ≥0∞) ^ Finsupp.degree α :=
        ENNReal.tsum_comm
    _ = ∑' k : ℕ, l1 r ((-h) ^ k) := rfl
    _ ≤ ∑' k : ℕ, (l1 r h) ^ k := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        refine (l1_pow_le r (-h) k).trans ?_
        rw [l1_neg']

lemma tsum_pow_ne_top {H : ℝ≥0∞} (hH : H ≤ 1/2) : (∑' k : ℕ, H ^ k) ≠ ⊤ := by
  have hHne : H ≠ ⊤ := by
    rintro rfl
    have h1 : (⊤ : ℝ≥0∞) ≤ 1/2 := hH
    simp at h1
  set x : NNReal := H.toNNReal with hx
  have hxH : (x : ℝ≥0∞) = H := ENNReal.coe_toNNReal hHne
  have hxle : x ≤ 1/2 := by
    have h1 : (x : ℝ≥0∞) ≤ ((1/2 : NNReal) : ℝ≥0∞) := by rw [hxH]; simpa using hH
    simpa using ENNReal.coe_le_coe.mp h1
  have hx1 : x < 1 := lt_of_le_of_lt hxle (by norm_num)
  have hcoe : (∑' k : ℕ, H ^ k) = ((∑' k : ℕ, x ^ k : NNReal) : ℝ≥0∞) := by
    rw [← hxH]
    simp only [← ENNReal.coe_pow]
    exact (ENNReal.coe_tsum (NNReal.summable_geometric hx1)).symm
  rw [hcoe, NNReal.tsum_geometric hx1]
  exact ENNReal.coe_ne_top

lemma neuSeries_mem (h : MvPowerSeries σ ℂ) (hh : h ∈ ConvPS σ)
    (h0 : MvPowerSeries.constantCoeff h = 0) : neuSeries h ∈ ConvPS σ := by
  obtain ⟨r, hr, hlt⟩ := hh
  set L := l1 r h with hL
  obtain ⟨x, hx⟩ : ∃ x : NNReal, L = (x : ℝ≥0∞) := ⟨L.toNNReal, (ENNReal.coe_toNNReal hlt).symm⟩
  set t : NNReal := (1/2) / (x + 1) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htle : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    have hx0 : (0 : NNReal) ≤ x := by positivity
    linarith
  have htx : t * x ≤ 1/2 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : NNReal) < x + 1)]
    nlinarith
  refine ⟨t * r, mul_pos htpos hr, ?_⟩
  have hH : l1 (t * r) h ≤ 1/2 := by
    refine (l1_mul_radius_le t htle h h0).trans ?_
    have hcoe2 : ((t * x : NNReal) : ℝ≥0∞) ≤ 1/2 := by
      rw [show (1/2 : ℝ≥0∞) = ((1/2 : NNReal) : ℝ≥0∞) from by norm_num, ENNReal.coe_le_coe]
      exact htx
    calc (t : ℝ≥0∞) * l1 r h = ((t * x : NNReal) : ℝ≥0∞) := by
          rw [← hL, hx, ENNReal.coe_mul]
      _ ≤ 1/2 := hcoe2
  have hfin : (∑' k : ℕ, (l1 (t * r) h) ^ k) ≠ ⊤ := tsum_pow_ne_top hH
  exact ne_top_of_le_ne_top hfin (l1_neuSeries_le (t * r) h h0)

lemma C_mem (a : ℂ) : (MvPowerSeries.C a : MvPowerSeries σ ℂ) ∈ ConvPS σ := by
  have h : (MvPowerSeries.C a : MvPowerSeries σ ℂ) = monomial 0 a := rfl
  refine ⟨1, one_pos, ?_⟩
  rw [h, l1_monomial]
  simp

lemma constantCoeff_ne_zero_of_isUnit (f : ConvPS σ) (hf : IsUnit f) :
    MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) ≠ 0 := by
  have hmap : IsUnit (MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ)) :=
    hf.map ((MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ →+* ℂ).comp (ConvPS σ).subtype)
  simpa using isUnit_iff_ne_zero.mp hmap

/-- **Part (i) of the exercise.** A convergent power series is a unit exactly when its constant
term is non-zero. -/
theorem isUnit_of_constantCoeff_ne_zero (f : ConvPS σ)
    (hf : MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) ≠ 0) : IsUnit f := by
  set c : ℂ := MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) with hc
  have hc0 : c ≠ 0 := hf
  have hCc : (MvPowerSeries.C c⁻¹ : MvPowerSeries σ ℂ) ∈ ConvPS σ := C_mem c⁻¹
  set Fc : ConvPS σ := ⟨MvPowerSeries.C c⁻¹, hCc⟩ with hFc
  set g : ConvPS σ := Fc * f with hgdef
  have hgc : MvPowerSeries.constantCoeff (g : MvPowerSeries σ ℂ) = 1 := by
    show MvPowerSeries.constantCoeff
      ((MvPowerSeries.C c⁻¹ : MvPowerSeries σ ℂ) * (f : MvPowerSeries σ ℂ)) = 1
    rw [map_mul, MvPowerSeries.constantCoeff_C, inv_mul_cancel₀ hc0]
  set h : ConvPS σ := g - 1 with hhdef
  have hh0 : MvPowerSeries.constantCoeff (h : MvPowerSeries σ ℂ) = 0 := by
    show MvPowerSeries.constantCoeff ((g : MvPowerSeries σ ℂ) - 1) = 0
    rw [map_sub, map_one, hgc, sub_self]
  have hneu : neuSeries (h : MvPowerSeries σ ℂ) ∈ ConvPS σ :=
    neuSeries_mem _ h.property hh0
  set v : ConvPS σ := ⟨neuSeries (h : MvPowerSeries σ ℂ), hneu⟩ with hvdef
  have hg1 : g * v = 1 := by
    refine Subtype.ext ?_
    show (g : MvPowerSeries σ ℂ) * neuSeries (h : MvPowerSeries σ ℂ) = 1
    have hge : (g : MvPowerSeries σ ℂ) = 1 + (h : MvPowerSeries σ ℂ) := by
      show (g : MvPowerSeries σ ℂ) = 1 + ((g : MvPowerSeries σ ℂ) - 1)
      ring
    rw [hge]
    exact one_add_mul_neuSeries _ hh0
  have hfe : f = (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * g := by
    refine Subtype.ext ?_
    show (f : MvPowerSeries σ ℂ) = MvPowerSeries.C c *
      ((MvPowerSeries.C c⁻¹ : MvPowerSeries σ ℂ) * (f : MvPowerSeries σ ℂ))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  have hFmul : (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * Fc = 1 := by
    refine Subtype.ext ?_
    show MvPowerSeries.C c * (MvPowerSeries.C c⁻¹ : MvPowerSeries σ ℂ) = 1
    rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  refine isUnit_iff_exists_inv.mpr ⟨v * Fc, ?_⟩
  rw [hfe]
  calc (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * g * (v * Fc)
      = (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * (g * v) * Fc := by ring
    _ = (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * 1 * Fc := by rw [hg1]
    _ = (⟨MvPowerSeries.C c, C_mem c⟩ : ConvPS σ) * Fc := by rw [mul_one]
    _ = 1 := hFmul

instance instNontrivialConvPS : Nontrivial (ConvPS σ) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have := congrArg (fun x : ConvPS σ => MvPowerSeries.constantCoeff (x : MvPowerSeries σ ℂ)) h
  simp at this

/-- **Part (i) of the exercise**: the ring of convergent power series is local. -/
theorem isLocalRing_convPS : IsLocalRing (ConvPS σ) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  have ha0 : MvPowerSeries.constantCoeff (a : MvPowerSeries σ ℂ) = 0 := by
    by_contra h
    exact ha (isUnit_of_constantCoeff_ne_zero a h)
  have hb0 : MvPowerSeries.constantCoeff (b : MvPowerSeries σ ℂ) = 0 := by
    by_contra h
    exact hb (isUnit_of_constantCoeff_ne_zero b h)
  intro hab
  have hsum : MvPowerSeries.constantCoeff ((a + b : ConvPS σ) : MvPowerSeries σ ℂ) = 0 := by
    show MvPowerSeries.constantCoeff ((a : MvPowerSeries σ ℂ) + (b : MvPowerSeries σ ℂ)) = 0
    rw [map_add, ha0, hb0, add_zero]
  exact constantCoeff_ne_zero_of_isUnit (a + b) hab hsum


/-! ## The maximal ideal and the vanishing ideals -/

/-- The `ℂ`-valued constant-term homomorphism of the ring of convergent power series. -/
def constHom (σ : Type*) [DecidableEq σ] : ConvPS σ →+* ℂ :=
  (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ →+* ℂ).comp (ConvPS σ).subtype

/-- The maximal ideal of the ring of convergent power series. -/
def maxIdeal (σ : Type*) [DecidableEq σ] : Ideal (ConvPS σ) := RingHom.ker (constHom σ)

lemma mem_maxIdeal {f : ConvPS σ} :
    f ∈ maxIdeal σ ↔ MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) = 0 :=
  Iff.rfl

lemma constHom_apply (f : ConvPS σ) :
    constHom σ f = MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) := rfl

/-- The ideal of series vanishing to order at least `k`. -/
def vanishIdeal (k : ℕ) : Ideal (ConvPS σ) where
  carrier := {f | VanishBelow k (f : MvPowerSeries σ ℂ)}
  zero_mem' := by intro α _; simp
  add_mem' := by
    intro a b ha hb α hα
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    show coeff α ((a : MvPowerSeries σ ℂ) + (b : MvPowerSeries σ ℂ)) = 0
    rw [map_add, ha α hα, hb α hα, add_zero]
  smul_mem' := by
    intro c a ha α hα
    simp only [Set.mem_ofPred_eq] at ha ⊢
    exact vanishBelow_mul (vanishBelow_zero _) ha α (by simpa using hα)

lemma vanishIdeal_one : vanishIdeal (σ := σ) 1 = maxIdeal σ := by
  ext f
  rw [mem_maxIdeal]
  exact vanishBelow_iff

lemma vanishIdeal_mul_le (a b : ℕ) :
    vanishIdeal (σ := σ) a * vanishIdeal (σ := σ) b ≤ vanishIdeal (σ := σ) (a + b) := by
  rw [Ideal.mul_le]
  intro x hx y hy
  exact vanishBelow_mul hx hy

lemma vanishIdeal_zero : vanishIdeal (σ := σ) 0 = ⊤ := by
  refine le_antisymm le_top ?_
  intro f _ α hα
  omega

lemma pow_le_vanishIdeal (k : ℕ) :
    maxIdeal (σ := σ) ^ k ≤ vanishIdeal (σ := σ) k := by
  induction k with
  | zero => rw [pow_zero, vanishIdeal_zero]; exact le_top
  | succ k ih =>
    calc maxIdeal (σ := σ) ^ (k + 1) = maxIdeal (σ := σ) ^ k * maxIdeal (σ := σ) := by
          rw [pow_succ]
      _ ≤ vanishIdeal (σ := σ) k * vanishIdeal (σ := σ) 1 :=
          mul_le_mul' ih (le_of_eq (vanishIdeal_one).symm)
      _ ≤ vanishIdeal (σ := σ) (k + 1) := vanishIdeal_mul_le k 1

lemma X_mem (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ ℂ) ∈ ConvPS σ := by
  have h : (MvPowerSeries.X i : MvPowerSeries σ ℂ) = monomial (Finsupp.single i 1) 1 := rfl
  refine ⟨1, one_pos, ?_⟩
  rw [h, l1_monomial]
  simp

lemma constantCoeff_X (i : σ) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries σ ℂ) = 0 := by
  show coeff (0 : σ →₀ ℕ) (MvPowerSeries.X i : MvPowerSeries σ ℂ) = 0
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have := congrArg (fun f : σ →₀ ℕ => f i) h
  simp at this

lemma shiftCoeff_vanish {f : MvPowerSeries σ ℂ} {k : ℕ} (hf : VanishBelow (k + 1) f)
    (i : σ) : VanishBelow k (shiftCoeff f i) := by
  intro β hβ
  rw [coeff_shiftCoeff]
  have hd : Finsupp.degree (β + Finsupp.single i 1) = Finsupp.degree β + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [hf _ (by omega), mul_zero]

end decomp


/-! ## The variable ideal of the formal power series ring -/

section varideal

variable [DecidableEq σ] [Fintype σ]

/-- The ideal of series vanishing to order at least `k`, inside the formal power series ring. -/
def vanishIdealC (k : ℕ) : Ideal (MvPowerSeries σ ℂ) where
  carrier := {f | VanishBelow k f}
  zero_mem' := by intro α _; simp
  add_mem' := by
    intro a b ha hb α hα
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha α hα, hb α hα, add_zero]
  smul_mem' := by
    intro c a ha α hα
    simp only [Set.mem_ofPred_eq] at ha ⊢
    exact vanishBelow_mul (vanishBelow_zero _) ha α (by simpa using hα)

/-- The ideal generated by the variables in the formal power series ring. -/
def varIdeal (σ : Type*) [DecidableEq σ] : Ideal (MvPowerSeries σ ℂ) :=
  Ideal.span (Set.range fun i : σ => (MvPowerSeries.X i : MvPowerSeries σ ℂ))

lemma X_mem_varIdeal (i : σ) :
    (MvPowerSeries.X i : MvPowerSeries σ ℂ) ∈ varIdeal σ :=
  Ideal.subset_span ⟨i, rfl⟩

lemma varIdeal_le_vanishIdealC_one : varIdeal (σ := σ) ≤ vanishIdealC 1 := by
  rw [varIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  intro α hα
  have h : α = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]; omega
  subst h
  exact constantCoeff_X i

lemma vanishIdealC_one_le_varIdeal : vanishIdealC (σ := σ) 1 ≤ varIdeal σ := by
  intro f hf
  have h0 : coeff (0 : σ →₀ ℕ) f = 0 := hf 0 (by simp)
  have hdec := sum_X_mul_shiftCoeff f h0
  rw [← hdec]
  refine Ideal.sum_mem _ fun i _ => ?_
  exact Ideal.mul_mem_right _ _ (X_mem_varIdeal i)

lemma varIdeal_eq : varIdeal (σ := σ) = vanishIdealC 1 :=
  le_antisymm varIdeal_le_vanishIdealC_one vanishIdealC_one_le_varIdeal

instance instAdicCompleteVarIdeal : IsAdicComplete (varIdeal (σ := σ)) (MvPowerSeries σ ℂ) :=
  inferInstanceAs (IsAdicComplete
    (Ideal.span (Set.range fun i : σ => (MvPowerSeries.X i : MvPowerSeries σ ℂ)))
    (MvPowerSeries σ ℂ))

end varideal

variable [DecidableEq σ] [Fintype σ]

lemma vanishIdealC_zero : vanishIdealC (σ := σ) 0 = ⊤ := by
  refine le_antisymm le_top ?_
  intro f _ α hα
  omega

lemma vanishIdealC_mul_le (a b : ℕ) :
    vanishIdealC (σ := σ) a * vanishIdealC (σ := σ) b ≤ vanishIdealC (σ := σ) (a + b) := by
  rw [Ideal.mul_le]
  intro x hx y hy
  exact vanishBelow_mul hx hy

lemma varIdeal_pow_le_vanishIdealC (n : ℕ) :
    varIdeal (σ := σ) ^ n ≤ vanishIdealC (σ := σ) n := by
  induction n with
  | zero => rw [pow_zero, vanishIdealC_zero]; exact le_top
  | succ n ih =>
    calc varIdeal (σ := σ) ^ (n + 1) = varIdeal (σ := σ) ^ n * varIdeal (σ := σ) := by
          rw [pow_succ]
      _ ≤ vanishIdealC (σ := σ) n * vanishIdealC (σ := σ) 1 :=
          mul_le_mul' ih varIdeal_le_vanishIdealC_one
      _ ≤ vanishIdealC (σ := σ) (n + 1) := vanishIdealC_mul_le n 1

lemma vanishIdealC_le_varIdeal_pow (n : ℕ) :
    vanishIdealC (σ := σ) n ≤ varIdeal (σ := σ) ^ n := by
  induction n with
  | zero => intro f _; rw [pow_zero]; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff (0 : σ →₀ ℕ) f = 0 := hf 0 (by simp)
    have hdec := sum_X_mul_shiftCoeff f h0
    rw [← hdec, pow_succ]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hmem : shiftCoeff f i ∈ varIdeal (σ := σ) ^ n := by
      refine ih ?_
      intro β hβ
      rw [coeff_shiftCoeff]
      have hd : Finsupp.degree (β + Finsupp.single i 1) = Finsupp.degree β + 1 := by
        rw [map_add, Finsupp.degree_single]
      rw [hf _ (by omega), mul_zero]
    have h2 := Ideal.mul_mem_mul hmem (X_mem_varIdeal i)
    rwa [mul_comm (shiftCoeff f i) (X i)] at h2

lemma vanishIdealC_eq_varIdeal_pow (n : ℕ) :
    vanishIdealC (σ := σ) n = varIdeal (σ := σ) ^ n :=
  le_antisymm (vanishIdealC_le_varIdeal_pow n) (varIdeal_pow_le_vanishIdealC n)

lemma poly_mem_convPS (p : MvPolynomial σ ℂ) : (p : MvPowerSeries σ ℂ) ∈ ConvPS σ := by
  classical
  refine ⟨1, one_pos, ?_⟩
  rw [l1, tsum_eq_sum (s := p.support) (by
    intro α hα
    rw [MvPolynomial.coeff_coe, MvPolynomial.notMem_support_iff.mp hα]
    simp)]
  exact ENNReal.sum_ne_top.mpr (fun α _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))

lemma shiftCoeff_vanishB {f : MvPowerSeries σ ℂ} {k : ℕ} (hf : VanishBelow (k + 1) f)
    (i : σ) : VanishBelow k (shiftCoeff f i) := by
  intro β hβ
  rw [coeff_shiftCoeff]
  have hd : Finsupp.degree (β + Finsupp.single i 1) = Finsupp.degree β + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [hf _ (by omega), mul_zero]

/-- The hard direction: a convergent series vanishing to order `k` lies in `𝔪^k`. -/
theorem vanishIdeal_le_pow (k : ℕ) : vanishIdeal (σ := σ) k ≤ maxIdeal (σ := σ) ^ k := by
  induction k with
  | zero => intro f _; rw [pow_zero]; simp
  | succ k ih =>
    intro f hf
    have h0 : MvPowerSeries.constantCoeff (f : MvPowerSeries σ ℂ) = 0 := by
      show coeff (0 : σ →₀ ℕ) (f : MvPowerSeries σ ℂ) = 0
      exact hf 0 (by simp)
    have hdec : (∑ i, (⟨MvPowerSeries.X i, X_mem i⟩ : ConvPS σ) *
        (⟨shiftCoeff (f : MvPowerSeries σ ℂ) i, shiftCoeff_mem _ f.property i⟩ : ConvPS σ)) = f := by
      refine Subtype.ext ?_
      push_cast
      exact sum_X_mul_shiftCoeff _ h0
    rw [← hdec, pow_succ]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hmem : (⟨shiftCoeff (f : MvPowerSeries σ ℂ) i,
        shiftCoeff_mem _ f.property i⟩ : ConvPS σ) ∈ vanishIdeal (σ := σ) k := by
      show VanishBelow k (shiftCoeff (f : MvPowerSeries σ ℂ) i)
      exact shiftCoeff_vanishB hf i
    have hx : (⟨MvPowerSeries.X i, X_mem i⟩ : ConvPS σ) ∈ maxIdeal (σ := σ) :=
      mem_maxIdeal.mpr (constantCoeff_X i)
    have h2 : (⟨shiftCoeff (f : MvPowerSeries σ ℂ) i, shiftCoeff_mem _ f.property i⟩ : ConvPS σ) *
        (⟨MvPowerSeries.X i, X_mem i⟩ : ConvPS σ) ∈ maxIdeal (σ := σ) ^ (k + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih hmem) hx
    rwa [mul_comm] at h2

theorem mem_maxIdeal_pow_iff {k : ℕ} {f : ConvPS σ} :
    f ∈ maxIdeal (σ := σ) ^ k ↔ VanishBelow k (f : MvPowerSeries σ ℂ) :=
  ⟨fun h => pow_le_vanishIdeal k h, fun h => vanishIdeal_le_pow k h⟩

/-- The projection `B → C/𝔪^n`. -/
noncomputable def toQuot (n : ℕ) :
    ConvPS σ →+* MvPowerSeries σ ℂ ⧸ varIdeal (σ := σ) ^ n :=
  (Ideal.Quotient.mk _).comp (ConvPS σ).subtype

lemma ker_toQuot (n : ℕ) : RingHom.ker (toQuot (σ := σ) n) = maxIdeal σ ^ n := by
  ext f
  have h1 : toQuot (σ := σ) n f = Ideal.Quotient.mk (varIdeal σ ^ n) (f : MvPowerSeries σ ℂ) := rfl
  rw [RingHom.mem_ker, h1, Ideal.Quotient.eq_zero_iff_mem, mem_maxIdeal_pow_iff]
  show ((f : MvPowerSeries σ ℂ) ∈ varIdeal (σ := σ) ^ n) ↔
    ((f : MvPowerSeries σ ℂ) ∈ vanishIdealC (σ := σ) n)
  rw [vanishIdealC_eq_varIdeal_pow]

lemma toQuot_surjective (n : ℕ) : Function.Surjective (toQuot (σ := σ) n) := by
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨⟨(MvPowerSeries.truncTotal n c : MvPolynomial σ ℂ), poly_mem_convPS _⟩, ?_⟩
  show Ideal.Quotient.mk _ ((MvPowerSeries.truncTotal n c : MvPolynomial σ ℂ) :
      MvPowerSeries σ ℂ) = Ideal.Quotient.mk _ c
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← vanishIdealC_eq_varIdeal_pow]
  intro α hα
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal (p := c) hα, sub_self]

/-- The truncation isomorphism `B/𝔪^n ≃+* C/(z)^n`. -/
noncomputable def levelEquiv (n : ℕ) :
    (ConvPS σ ⧸ maxIdeal σ ^ n) ≃+*
      (MvPowerSeries σ ℂ ⧸ varIdeal (σ := σ) ^ n) :=
  (Ideal.quotientEquiv (maxIdeal σ ^ n) (RingHom.ker (toQuot (σ := σ) n))
      (RingEquiv.refl (ConvPS σ)) (by
        show RingHom.ker (toQuot (σ := σ) n) = Ideal.map (RingHom.id (ConvPS σ)) (maxIdeal σ ^ n)
        rw [Ideal.map_id]
        exact ker_toQuot n)).trans
    (RingHom.quotientKerEquivOfSurjective (f := toQuot (σ := σ) n) (toQuot_surjective n))

/-! ## The completion of `B` is `C` -/

section completion

lemma levelEquiv_mk (n : ℕ) (b : ConvPS σ) :
    levelEquiv (σ := σ) n (Ideal.Quotient.mk (maxIdeal σ ^ n) b) =
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) (b : MvPowerSeries σ ℂ) := by
  simp only [levelEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- The truncation of a formal power series, as an element of `B`. -/
noncomputable def truncPS (n : ℕ) (c : MvPowerSeries σ ℂ) : ConvPS σ :=
  ⟨(MvPowerSeries.truncTotal n c : MvPolynomial σ ℂ), poly_mem_convPS _⟩

lemma coeff_truncPS (n : ℕ) (c : MvPowerSeries σ ℂ) {α : σ →₀ ℕ}
    (hα : Finsupp.degree α < n) :
    MvPowerSeries.coeff α ((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) =
      MvPowerSeries.coeff α c := by
  show MvPolynomial.coeff α (MvPowerSeries.truncTotal n c) = MvPowerSeries.coeff α c
  rw [MvPowerSeries.coeff_truncTotal (p := c) hα]

lemma mk_truncPS_eq (n : ℕ) (c : MvPowerSeries σ ℂ) :
    Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) ((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) =
      Ideal.Quotient.mk (varIdeal σ ^ n) c := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← vanishIdealC_eq_varIdeal_pow]
  intro α hα
  have h1 : MvPowerSeries.coeff α ((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) =
      MvPowerSeries.coeff α c := coeff_truncPS n c hα
  have h2 : MvPowerSeries.coeff α (((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) - c) = 0 := by
    rw [map_sub, h1, sub_self]
  exact h2

lemma ideal_smul_top (I : Ideal (ConvPS σ)) : I • ⊤ = I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

lemma mk_eq_mk_pow {m n : ℕ} (hle : m ≤ n) (g : AdicCompletion.AdicCauchySequence
    (maxIdeal σ) (ConvPS σ)) :
    Ideal.Quotient.mk (maxIdeal σ ^ m) (g.val n) =
      Ideal.Quotient.mk (maxIdeal σ ^ m) (g.val m) := by
  have h := AdicCompletion.AdicCauchySequence.mk_eq_mk hle g
  have h2 := congrArg (Ideal.quotientEquivAlgOfEq (ConvPS σ) (ideal_smul_top (maxIdeal σ ^ m))) h
  simpa [Ideal.quotientEquivAlgOfEq_mk] using h2

/-- The compatible family defining the comparison `AdicCompletion 𝔪 B → C`. -/
noncomputable def phiFam (n : ℕ) : AdicCompletion (maxIdeal σ) (ConvPS σ) →+*
    MvPowerSeries σ ℂ ⧸ varIdeal (σ := σ) ^ n :=
  ((levelEquiv (σ := σ) n).toRingHom).comp
    ((AdicCompletion.evalₐ (maxIdeal σ) n).toRingHom)

lemma phiFam_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (varIdeal (σ := σ)) hle).comp (phiFam n) = phiFam m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h g =>
    show Ideal.Quotient.factorPow (varIdeal (σ := σ)) hle
      ((levelEquiv (σ := σ) n) (AdicCompletion.evalₐ (maxIdeal σ) n
        (AdicCompletion.mk (maxIdeal σ) (ConvPS σ) g))) =
      (levelEquiv (σ := σ) m) (AdicCompletion.evalₐ (maxIdeal σ) m
        (AdicCompletion.mk (maxIdeal σ) (ConvPS σ) g))
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, levelEquiv_mk, levelEquiv_mk]
    have hc := mk_eq_mk_pow hle g
    have hcc := congrArg (levelEquiv (σ := σ) m) hc
    rw [levelEquiv_mk, levelEquiv_mk] at hcc
    rw [← hcc]
    rfl

/-- The comparison map from the `𝔪`-adic completion of `B` to `C`. -/
noncomputable def Phi : AdicCompletion (maxIdeal σ) (ConvPS σ) →+* MvPowerSeries σ ℂ :=
  IsAdicComplete.liftRingHom (varIdeal (σ := σ)) phiFam phiFam_compat

/-- The compatible family defining the comparison `C → AdicCompletion 𝔪 B`. -/
noncomputable def psiFam (n : ℕ) : MvPowerSeries σ ℂ →+*
    ConvPS σ ⧸ maxIdeal (σ := σ) ^ n :=
  ((levelEquiv (σ := σ) n).symm.toRingHom).comp (Ideal.Quotient.mk _)

lemma psiFam_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maxIdeal (σ := σ)) hle).comp (psiFam n) = psiFam m := by
  ext c
  show Ideal.Quotient.factorPow (maxIdeal (σ := σ)) hle
    ((levelEquiv (σ := σ) n).symm (Ideal.Quotient.mk (varIdeal σ ^ n) c)) =
    (levelEquiv (σ := σ) m).symm (Ideal.Quotient.mk (varIdeal σ ^ m) c)
  have e1 : (levelEquiv (σ := σ) n).symm (Ideal.Quotient.mk (varIdeal σ ^ n) c) =
      Ideal.Quotient.mk (maxIdeal σ ^ n) (truncPS n c) := by
    rw [RingEquiv.symm_apply_eq, levelEquiv_mk, mk_truncPS_eq]
  have e2 : (levelEquiv (σ := σ) m).symm (Ideal.Quotient.mk (varIdeal σ ^ m) c) =
      Ideal.Quotient.mk (maxIdeal σ ^ m) (truncPS m c) := by
    rw [RingEquiv.symm_apply_eq, levelEquiv_mk, mk_truncPS_eq]
  rw [e1, e2]
  have hfac : Ideal.Quotient.factorPow (maxIdeal (σ := σ)) hle
      (Ideal.Quotient.mk (maxIdeal σ ^ n) (truncPS n c)) =
      Ideal.Quotient.mk (maxIdeal σ ^ m) (truncPS n c) := rfl
  rw [hfac, Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maxIdeal_pow_iff]
  intro α hα
  have h1 : MvPowerSeries.coeff α ((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) =
      MvPowerSeries.coeff α c := coeff_truncPS n c (by omega)
  have h2 : MvPowerSeries.coeff α ((truncPS m c : ConvPS σ) : MvPowerSeries σ ℂ) =
      MvPowerSeries.coeff α c := coeff_truncPS m c hα
  have h3 : MvPowerSeries.coeff α (((truncPS n c - truncPS m c : ConvPS σ) :
      MvPowerSeries σ ℂ)) = 0 := by
    rw [show ((truncPS n c - truncPS m c : ConvPS σ) : MvPowerSeries σ ℂ) =
        ((truncPS n c : ConvPS σ) : MvPowerSeries σ ℂ) -
        ((truncPS m c : ConvPS σ) : MvPowerSeries σ ℂ) from rfl, map_sub, h1, h2, sub_self]
  exact h3

/-- The comparison map from `C` to the `𝔪`-adic completion of `B`. -/
noncomputable def Psi : MvPowerSeries σ ℂ →+* AdicCompletion (maxIdeal σ) (ConvPS σ) :=
  AdicCompletion.liftRingHom (maxIdeal σ) psiFam psiFam_compat

lemma Phi_mk (n : ℕ) (x : AdicCompletion (maxIdeal σ) (ConvPS σ)) :
    Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) (Phi x) = phiFam n x :=
  IsAdicComplete.mk_liftRingHom (varIdeal (σ := σ)) phiFam phiFam_compat n x

lemma evalₐ_Psi (n : ℕ) (c : MvPowerSeries σ ℂ) :
    AdicCompletion.evalₐ (maxIdeal σ) n (Psi c) = psiFam n c :=
  AdicCompletion.evalₐ_liftRingHom (maxIdeal (σ := σ)) psiFam psiFam_compat n c

set_option maxHeartbeats 1000000 in
lemma Phi_comp_Psi : Phi.comp Psi = RingHom.id (MvPowerSeries σ ℂ) := by
  have key : ∀ (n : ℕ) (c : MvPowerSeries σ ℂ),
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) ((Phi.comp Psi) c) =
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) ((RingHom.id (MvPowerSeries σ ℂ)) c) := by
   intro n c
   have h1 : (Phi.comp Psi) c = Phi (Psi c) := rfl
   rw [h1, RingHom.id_apply, Phi_mk]
   show (levelEquiv (σ := σ) n) (AdicCompletion.evalₐ (maxIdeal σ) n (Psi c)) =
     Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) c
   rw [evalₐ_Psi]
   show (levelEquiv (σ := σ) n)
     ((levelEquiv (σ := σ) n).symm (Ideal.Quotient.mk (varIdeal σ ^ n) c)) =
     Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) c
   rw [RingEquiv.apply_symm_apply]
  refine RingHom.ext (fun c => ?_)
  exact congrFun (IsHausdorff.funext' (I := varIdeal (σ := σ)) (f := Phi.comp Psi)
    (g := RingHom.id (MvPowerSeries σ ℂ)) key) c

set_option maxHeartbeats 1000000 in
lemma Psi_comp_Phi : Psi.comp Phi = RingHom.id (AdicCompletion (maxIdeal σ) (ConvPS σ)) := by
  refine RingHom.ext (fun x => ?_)
  refine AdicCompletion.ext_evalₐ (fun n => ?_)
  show AdicCompletion.evalₐ (maxIdeal σ) n ((Psi.comp Phi) x) =
    AdicCompletion.evalₐ (maxIdeal σ) n ((RingHom.id (AdicCompletion (maxIdeal σ) (ConvPS σ))) x)
  have h1 : (Psi.comp Phi) x = Psi (Phi x) := rfl
  rw [h1, RingHom.id_apply, evalₐ_Psi]
  show (levelEquiv (σ := σ) n).symm (Ideal.Quotient.mk (varIdeal σ ^ n) (Phi x)) =
    AdicCompletion.evalₐ (maxIdeal σ) n x
  rw [show Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) (Phi x) = phiFam n x from Phi_mk n x]
  show (levelEquiv (σ := σ) n).symm
    ((levelEquiv (σ := σ) n) (AdicCompletion.evalₐ (maxIdeal σ) n x)) =
    AdicCompletion.evalₐ (maxIdeal σ) n x
  rw [RingEquiv.symm_apply_apply]

/-- **Part (ii) of the exercise**: the `𝔪`-adic completion of the ring of convergent power
series is the ring of formal power series. -/
noncomputable def completionEquiv :
    AdicCompletion (maxIdeal σ) (ConvPS σ) ≃+* MvPowerSeries σ ℂ where
  toFun := Phi
  invFun := Psi
  left_inv x := by
    have h := congrArg (fun f => f x) Psi_comp_Phi
    simpa using h
  right_inv c := by
    have h := congrArg (fun f => f c) Phi_comp_Psi
    simpa using h
  map_mul' := Phi.map_mul
  map_add' := Phi.map_add

end completion

/-! ## The `A`-algebra structures and flatness -/

section flatness

/-- Polynomials as convergent power series. -/
noncomputable def polyToB : MvPolynomial σ ℂ →+* ConvPS σ where
  toFun p := ⟨(p : MvPowerSeries σ ℂ), poly_mem_convPS p⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro p q; ext; simp
  map_mul' := by intro p q; ext; simp

instance : Algebra (MvPolynomial σ ℂ) (ConvPS σ) := polyToB.toAlgebra

instance instScalarTowerPBC :
    IsScalarTower (MvPolynomial σ ℂ) (ConvPS σ) (MvPowerSeries σ ℂ) where
  smul_assoc r b c := by
    have h : (algebraMap (MvPolynomial σ ℂ) (MvPowerSeries σ ℂ)) r =
        (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)) ((algebraMap (MvPolynomial σ ℂ)
          (ConvPS σ)) r) := rfl
    simp only [Algebra.smul_def]
    rw [h, map_mul, mul_assoc]

lemma mem_idealOfVars_iff_constantCoeff (p : MvPolynomial σ ℂ) :
    p ∈ MvPolynomial.idealOfVars σ ℂ ↔ MvPolynomial.constantCoeff p = 0 := by
  have h1 : p ∈ MvPolynomial.idealOfVars σ ℂ ↔
      ∀ x ∈ p.support, 1 ≤ Finsupp.degree x := by
    rw [← pow_one (MvPolynomial.idealOfVars σ ℂ)]
    exact MvPolynomial.mem_pow_idealOfVars_iff (p := p) 1
  rw [h1, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff]
  constructor
  · intro hp
    by_contra hc
    have hmem : (0 : σ →₀ ℕ) ∈ p.support := Finsupp.mem_support_iff.mpr hc
    have := hp 0 hmem
    simp at this
  · intro hp x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hx) hp
    have hd : Finsupp.degree x ≠ 0 := fun h => hx0 ((Finsupp.degree_eq_zero_iff x).mp h)
    omega

lemma idealOfVars_isPrime : (MvPolynomial.idealOfVars σ ℂ).IsPrime := by
  have h : MvPolynomial.idealOfVars σ ℂ =
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ ℂ →+* ℂ) := by
    ext p
    rw [RingHom.mem_ker]
    exact mem_idealOfVars_iff_constantCoeff p
  rw [h]
  exact RingHom.ker_isPrime _

instance instIsPrimeIdealOfVars : Ideal.IsPrime (MvPolynomial.idealOfVars σ ℂ) :=
  idealOfVars_isPrime

lemma isUnit_polyToB (y : Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ)) :
    IsUnit (polyToB (σ := σ) (y : MvPolynomial σ ℂ)) := by
  have hy : MvPolynomial.constantCoeff (y : MvPolynomial σ ℂ) ≠ 0 := fun h =>
    y.2 (mem_idealOfVars_iff_constantCoeff _ |>.mpr h)
  refine isUnit_of_constantCoeff_ne_zero _ ?_
  show MvPowerSeries.constantCoeff ((y : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) ≠ 0
  have h : MvPowerSeries.constantCoeff ((y : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
      MvPolynomial.constantCoeff (y : MvPolynomial σ ℂ) := rfl
  rw [h]
  exact hy

lemma isUnit_polyToC (y : Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ)) :
    IsUnit ((y : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hy : MvPolynomial.constantCoeff (y : MvPolynomial σ ℂ) ≠ 0 := fun h =>
    y.2 (mem_idealOfVars_iff_constantCoeff _ |>.mpr h)
  have h : MvPowerSeries.constantCoeff ((y : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
      MvPolynomial.constantCoeff (y : MvPolynomial σ ℂ) := rfl
  rw [h]
  exact hy

/-- The localization of the polynomial ring at the origin. -/
abbrev Origin (σ : Type*) [Fintype σ] [DecidableEq σ] :=
  Localization.AtPrime (MvPolynomial.idealOfVars σ ℂ)

noncomputable def locToB :
    Origin σ →ₐ[MvPolynomial σ ℂ] ConvPS σ :=
  IsLocalization.liftAlgHom (M := Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ))
    (f := Algebra.ofId (MvPolynomial σ ℂ) (ConvPS σ)) (fun y => isUnit_polyToB y)

noncomputable def locToC :
    Origin σ →ₐ[MvPolynomial σ ℂ] MvPowerSeries σ ℂ :=
  IsLocalization.liftAlgHom (M := Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ))
    (f := Algebra.ofId (MvPolynomial σ ℂ) (MvPowerSeries σ ℂ)) (fun y => isUnit_polyToC y)

noncomputable def locToBRingHom : Origin σ →+* ConvPS σ := (locToB (σ := σ)).toRingHom

noncomputable def locToCRingHom : Origin σ →+* MvPowerSeries σ ℂ := (locToC (σ := σ)).toRingHom

instance : Algebra (Origin σ) (ConvPS σ) := locToBRingHom.toAlgebra

instance : Algebra (Origin σ) (MvPowerSeries σ ℂ) := locToCRingHom.toAlgebra

instance instTowerPAB : IsScalarTower (MvPolynomial σ ℂ) (Origin σ) (ConvPS σ) where
  smul_assoc r b c := by
    have h : (algebraMap (MvPolynomial σ ℂ) (ConvPS σ)) r =
        (algebraMap (Origin σ) (ConvPS σ)) ((algebraMap (MvPolynomial σ ℂ) (Origin σ)) r) :=
      ((locToB (σ := σ)).commutes r).symm
    simp only [Algebra.smul_def]
    rw [h, map_mul, mul_assoc]

instance instTowerPAC : IsScalarTower (MvPolynomial σ ℂ) (Origin σ) (MvPowerSeries σ ℂ) where
  smul_assoc r b c := by
    have h : (algebraMap (MvPolynomial σ ℂ) (MvPowerSeries σ ℂ)) r =
        (algebraMap (Origin σ) (MvPowerSeries σ ℂ))
          ((algebraMap (MvPolynomial σ ℂ) (Origin σ)) r) :=
      ((locToC (σ := σ)).commutes r).symm
    simp only [Algebra.smul_def]
    rw [h, map_mul, mul_assoc]

lemma algebraMap_origin_C_eq (a : Origin σ) :
    (algebraMap (Origin σ) (MvPowerSeries σ ℂ)) a =
      (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)) ((algebraMap (Origin σ) (ConvPS σ)) a) := by
  have key : (algebraMap (Origin σ) (MvPowerSeries σ ℂ)) =
      (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)).comp
        (algebraMap (Origin σ) (ConvPS σ)) := by
    refine IsLocalization.ringHom_ext (M := Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ))
      (j := algebraMap (Origin σ) (MvPowerSeries σ ℂ))
      (k := (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)).comp
        (algebraMap (Origin σ) (ConvPS σ))) ?_
    refine RingHom.ext (fun x => ?_)
    change locToC (σ := σ) ((algebraMap (MvPolynomial σ ℂ) (Origin σ)) x) =
      (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ))
        (locToB (σ := σ) ((algebraMap (MvPolynomial σ ℂ) (Origin σ)) x))
    rw [AlgHom.commutes (locToB (σ := σ)), AlgHom.commutes (locToC (σ := σ))]
    rfl
  rw [key]
  rfl

instance instTowerABC : IsScalarTower (Origin σ) (ConvPS σ) (MvPowerSeries σ ℂ) where
  smul_assoc r b c := by
    simp only [Algebra.smul_def]
    rw [algebraMap_origin_C_eq, map_mul, mul_assoc]

end flatness

section flat2

lemma flat_P_C : Module.Flat (MvPolynomial σ ℂ) (MvPowerSeries σ ℂ) :=
  haveI : Module.Flat (MvPolynomial σ ℂ)
      (AdicCompletion (MvPolynomial.idealOfVars σ ℂ) (MvPolynomial σ ℂ)) :=
    AdicCompletion.flat_of_isNoetherian _
  Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv σ ℂ).toLinearEquiv

lemma flat_A_C : Module.Flat (Origin σ) (MvPowerSeries σ ℂ) :=
  (Module.flat_iff_of_isLocalization (R := MvPolynomial σ ℂ) (S := Origin σ)
    (p := Ideal.primeCompl (MvPolynomial.idealOfVars σ ℂ))
    (M := MvPowerSeries σ ℂ)).mpr (flat_P_C (σ := σ))

attribute [instance] isLocalRing_convPS

lemma maxIdeal_eq_maximalIdeal : maxIdeal (σ := σ) = IsLocalRing.maximalIdeal (ConvPS σ) := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx hunit
    exact constantCoeff_ne_zero_of_isUnit x hunit (by simpa [mem_maxIdeal] using hx)
  · intro hx
    by_contra hc
    exact hx (isUnit_of_constantCoeff_ne_zero x (by simpa [mem_maxIdeal] using hc))

instance instIsMaximalMaxIdeal : (maxIdeal (σ := σ)).IsMaximal := by
  rw [maxIdeal_eq_maximalIdeal]
  infer_instance

lemma le_maxIdeal_of_ne_top {I : Ideal (ConvPS σ)} (hI : I ≠ ⊤) : I ≤ maxIdeal (σ := σ) := by
  intro x hx
  by_contra hc
  have hc' : MvPowerSeries.constantCoeff (x : MvPowerSeries σ ℂ) ≠ 0 := by
    simpa [mem_maxIdeal] using hc
  exact hI (Ideal.eq_top_of_isUnit_mem I hx (isUnit_of_constantCoeff_ne_zero x hc'))

/-- Exercise 10.7 in the case used here: the `𝔪`-adic completion of a Noetherian local ring is
faithfully flat, stated for the concrete maximal ideal of `B`. -/
theorem faithfullyFlat_maxIdeal [IsNoetherianRing (ConvPS σ)] :
    Module.FaithfullyFlat (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ)) := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨AdicCompletion.flat_of_isNoetherian (maxIdeal (σ := σ)), ?_⟩
  intro I hI htop
  have hle : I ≤ maxIdeal (σ := σ) := le_maxIdeal_of_ne_top hI
  have hmax := AdicCompletion.isMaximal_map_of_le (maxIdeal (σ := σ)) (maxIdeal (σ := σ))
    le_rfl (Ideal.fg_of_isNoetherianRing _)
  have hm : maxIdeal (σ := σ) •
      (⊤ : Submodule (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))) ≠ ⊤ := by
    intro h
    rw [Ideal.smul_top_eq_map] at h
    refine hmax.ne_top ((Submodule.restrictScalars_inj (ConvPS σ)
      (AdicCompletion (maxIdeal σ) (ConvPS σ))
      (AdicCompletion (maxIdeal σ) (ConvPS σ))).mp ?_)
    rw [h, Submodule.restrictScalars_top]
  have h1 : I • (⊤ : Submodule (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))) ≤
      maxIdeal (σ := σ) • ⊤ := Submodule.smul_mono hle le_rfl
  rw [htop] at h1
  exact hm (top_le_iff.mp h1)

set_option maxHeartbeats 1000000 in
lemma Phi_comp_algebraMap :
    Phi.comp (algebraMap (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))) =
      (ConvPS σ).subtype := by
  have key : ∀ (n : ℕ) (b : ConvPS σ),
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n)
        ((Phi.comp (algebraMap (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ)))) b) =
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) (((ConvPS σ).subtype) b) := by
    intro n b
    have hof : (algebraMap (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))) b =
        AdicCompletion.of (maxIdeal σ) (ConvPS σ) b := rfl
    rw [RingHom.comp_apply, hof]
    show Ideal.Quotient.mk (varIdeal (σ := σ) ^ n)
        (Phi (AdicCompletion.of (maxIdeal σ) (ConvPS σ) b)) =
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) ((b : ConvPS σ) : MvPowerSeries σ ℂ)
    rw [Phi_mk]
    show (levelEquiv (σ := σ) n)
        (AdicCompletion.evalₐ (maxIdeal σ) n (AdicCompletion.of (maxIdeal σ) (ConvPS σ) b)) =
      Ideal.Quotient.mk (varIdeal (σ := σ) ^ n) ((b : ConvPS σ) : MvPowerSeries σ ℂ)
    rw [AdicCompletion.evalₐ_of, levelEquiv_mk]
  refine RingHom.ext (fun b => ?_)
  exact congrFun (IsHausdorff.funext' (I := varIdeal (σ := σ))
    (f := Phi.comp (algebraMap (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))))
    (g := (ConvPS σ).subtype) key) b

/-- The completion equivalence as an algebra equivalence over `B`. -/
noncomputable def completionAlgEquiv :
    MvPowerSeries σ ℂ ≃ₐ[ConvPS σ] AdicCompletion (maxIdeal σ) (ConvPS σ) :=
  AlgEquiv.ofRingEquiv (f := (completionEquiv (σ := σ)).symm) (fun b => by
    have h := congrFun (congrArg DFunLike.coe (Phi_comp_algebraMap (σ := σ))) b
    show (completionEquiv (σ := σ)).symm ((algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)) b) =
      (algebraMap (ConvPS σ) (AdicCompletion (maxIdeal σ) (ConvPS σ))) b
    rw [show (algebraMap (ConvPS σ) (MvPowerSeries σ ℂ)) b =
      completionEquiv (σ := σ) ((algebraMap (ConvPS σ)
        (AdicCompletion (maxIdeal σ) (ConvPS σ))) b) from h.symm]
    exact RingEquiv.symm_apply_apply _ _)

attribute [instance] faithfullyFlat_maxIdeal

/-- The formal power series ring is faithfully flat over the convergent power series ring. -/
theorem faithfullyFlat_B_C [IsNoetherianRing (ConvPS σ)] :
    Module.FaithfullyFlat (ConvPS σ) (MvPowerSeries σ ℂ) :=
  Module.FaithfullyFlat.of_linearEquiv (ConvPS σ)
    (AdicCompletion (maxIdeal σ) (ConvPS σ))
    (completionAlgEquiv (σ := σ)).toLinearEquiv

end flat2

section descent

open scoped TensorProduct

/-- Exercise 3.17 in the form needed: flatness descends along a faithfully flat algebra. -/
theorem flat_of_faithfullyFlat_of_flat {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Module.Flat A C] [Module.FaithfullyFlat B C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have hflat : Function.Injective ⇑(LinearMap.lTensor C f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have key : Function.Injective
      ⇑(LinearMap.lTensor C (TensorProduct.AlgebraTensorModule.lTensor B B f)) := by
    have square : ∀ z : C ⊗[B] (B ⊗[A] N),
        ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N')
            (⇑(LinearMap.lTensor C (TensorProduct.AlgebraTensorModule.lTensor B B f)) z)
          = ⇑(LinearMap.lTensor C f)
            (⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c w =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul b n => simp
        | add w₁ w₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    intro x y hxy
    have hEq : ⇑(LinearMap.lTensor C f)
          (⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N) x)
        = ⇑(LinearMap.lTensor C f)
          (⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N) y) := by
      rw [← square x, ← square y, hxy]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N).injective (hflat hEq)
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective (R := B) (M := C)
    (f := TensorProduct.AlgebraTensorModule.lTensor B B f)).mp key

end descent

/-- **Part (iii) of the exercise**: assuming `B` Noetherian, `B` is flat over the local ring `A`
of the origin. -/
theorem part_iii [IsNoetherianRing (ConvPS σ)] :
    Module.Flat (Origin σ) (ConvPS σ) := by
  haveI := flat_A_C (σ := σ)
  haveI := faithfullyFlat_B_C (σ := σ)
  exact flat_of_faithfullyFlat_of_flat (A := Origin σ) (B := ConvPS σ) (C := MvPowerSeries σ ℂ)

/-- **Atiyah–Macdonald, Chapter 10, Exercise 8** (all parts), for `σ = Fin n`.

`ConvPS (Fin n)` is the ring `B = ℂ{z₁,…,zₙ}` of power series converging near the origin,
`MvPowerSeries (Fin n) ℂ` is the ring `C = ℂ[[z₁,…,zₙ]]` of formal power series, and
`Origin (Fin n)` is the local ring `A = ℂ[z₁,…,zₙ]_(z)` of the origin.

(i) `B` is a local ring;
(ii) its maximal-ideal completion is `C`;
(iii) if `B` is Noetherian then `B` is flat over `A`. -/
theorem solution (n : ℕ) [IsNoetherianRing (ConvPS (Fin n))] :
    IsLocalRing (ConvPS (Fin n)) ∧
      Nonempty (AdicCompletion (maxIdeal (Fin n)) (ConvPS (Fin n)) ≃+* MvPowerSeries (Fin n) ℂ) ∧
      Module.Flat (Origin (Fin n)) (ConvPS (Fin n)) :=
  ⟨isLocalRing_convPS, ⟨completionEquiv⟩, part_iii⟩

end AtiyahMcdonald69.Ex_10_8
