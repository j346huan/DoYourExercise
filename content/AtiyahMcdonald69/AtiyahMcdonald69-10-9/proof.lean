/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 10 (Completions), Exercise 9.

**Original statement** (Hensel's lemma, "version 1").  Let `A` be a complete local ring with
maximal ideal `m`, let `f ∈ A[X]` be monic of degree `n`, and suppose that its reduction
`f̄ ∈ (A/m)[X]` factorizes as `f̄ = ḡ * h̄` where `ḡ` and `h̄` are coprime monic polynomials of
degrees `r` and `n - r` respectively.  Then `f` factorizes as `f = g * h` with `g, h ∈ A[X]`
monic of degrees `r` and `n - r`, reducing to `ḡ` and `h̄` modulo `m`.

**Coverage.**  The theorem `solution` below states exactly this: all quantifiers and degree
conditions of the original statement are kept (the degree condition `r + s = n` is an explicit
hypothesis, as in the book, where `r = deg ḡ` and `n - r = deg h̄`).  "Complete local ring" is
formalized as `IsAdicComplete (maximalIdeal A) A`, which is Mathlib's form of the statement that
the `m`-adic completion map `A → lim A/m^i` is a bijection (Hausdorff + every Cauchy sequence
converges), cf. A–M Chapter 10.

**Approach.**  We follow the successive-approximation proof of the book's hint
(`g_k h_k ≡ f mod m^k`, then pass to the limit): starting from arbitrary monic lifts `G, H` of
`ḡ, h̄`, each step solves the linearized equation modulo `m^(k+1)` by division with remainder by
the monic polynomials (this is where coprimality modulo `m` is used), the corrections have
coefficients in `m^k`, so coefficient sequences are Cauchy; `IsPrecomplete` produces limits
`g, h`, and Hausdorffness (`IsHausdorff`) shows that the limit is monic, reduces to `ḡ, h̄` and
satisfies `g * h = f`.

**Source of the natural-language proof.**
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-10-9

The book's hint is known to be slightly imprecise about the degree bookkeeping (the correction
terms must be reduced modulo the monic factors to keep the degrees `r`, `n - r`); this is
handled explicitly here by division with remainder.

**Statement adaptation.**  For reuse, the same argument is proved for a slightly more general
situation (`hensel_factor`): an arbitrary commutative ring `A` that is complete with respect to
an ideal `I` (`I ≠ ⊤`, so that `A ⧸ I` is nontrivial).  The exercise statement is the special case
`I = maximalIdeal A` of a local ring, which is `solution` below; the two are the same statement,
`hensel_factor` merely carries the extra generality.  Here "coprime" is `IsCoprime ḡ h̄`, i.e. the
existence of a Bézout relation `a * ḡ + b * h̄ = 1`, the standard form of coprimality.

**Non-vacuity.**  The hypotheses are satisfiable: `ℤ_[3]` is a local ring that is complete for its
maximal ideal, and `X * (X - 1)` reduces to the product of the coprime monic polynomials `X` and
`X - 1` (see `nonvacuous.lean`, which applies `solution` in this case).

**Contents.**  `CoeffIn` (coefficient-wise membership in an ideal), `polyLift` (coefficient-wise
lifting of a polynomial along `A → A ⧸ I`), `exists_mul_add_of_coprime` (the division lemma in
the residue ring), `HenselData`/`GoodPair`/`Correction` (the data of one approximation step),
`state` (the recursive sequence of approximations), `limG`/`limH`/`gfinal`/`hfinal` (the limits),
and finally `hensel_factor` and `solution`.
-/
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Ideal.BigOperators

namespace AtiyahMcdonald69.Ex_10_9

open Polynomial

set_option maxHeartbeats 800000

-- Style linters off: the mathematical content is unaffected (no `sorry`, no axioms).
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {A : Type*} [CommRing A]

/-! ### Tracking coefficients inside an ideal -/

/-- `CoeffIn I p` means that every coefficient of the polynomial `p` lies in the ideal `I`. -/
def CoeffIn (I : Ideal A) (p : A[X]) : Prop := ∀ k, p.coeff k ∈ I

namespace CoeffIn

variable {I J K : Ideal A} {p q : A[X]}

theorem zero (I : Ideal A) : CoeffIn I (0 : A[X]) := fun k => by simp

theorem add (hp : CoeffIn I p) (hq : CoeffIn I q) : CoeffIn I (p + q) := fun k => by
  rw [coeff_add]; exact I.add_mem (hp k) (hq k)

theorem neg (hp : CoeffIn I p) : CoeffIn I (-p) := fun k => by
  rw [coeff_neg]; exact I.neg_mem (hp k)

theorem sub (hp : CoeffIn I p) (hq : CoeffIn I q) : CoeffIn I (p - q) := fun k => by
  rw [coeff_sub]; exact I.sub_mem (hp k) (hq k)

theorem mono {I J : Ideal A} (h : I ≤ J) (hp : CoeffIn I p) : CoeffIn J p := fun k => h (hp k)

theorem C_mul (a : A) (hp : CoeffIn I p) : CoeffIn I (C a * p) := fun k => by
  rw [coeff_C_mul]; exact I.mul_mem_left a (hp k)

theorem C {a : A} (ha : a ∈ I) : CoeffIn I (Polynomial.C a) := fun k => by
  rw [coeff_C]
  split_ifs with hk
  · exact ha
  · exact I.zero_mem

theorem C_mul_of_mem {a : A} (ha : a ∈ I) (p : A[X]) : CoeffIn I (Polynomial.C a * p) :=
  fun k => by
  rw [coeff_C_mul]; exact I.mul_mem_right _ ha

theorem top (p : A[X]) : CoeffIn (⊤ : Ideal A) p := fun _ => trivial

theorem mul (hp : CoeffIn I p) (hq : CoeffIn J q) : CoeffIn (I * J) (p * q) := fun k => by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hp i.1) (hq i.2)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → A[X]} (h : ∀ i ∈ s, CoeffIn I (f i)) :
    CoeffIn I (∑ i ∈ s, f i) := fun k => by
  rw [finsetSum_coeff]
  exact Ideal.sum_mem _ fun i hi => h i hi k

theorem of_map_eq_zero {I : Ideal A} {p : A[X]} (h : p.map (Ideal.Quotient.mk I) = 0) :
    CoeffIn I p := fun k => by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h, coeff_zero]

theorem map_eq_zero {I : Ideal A} {p : A[X]} (h : CoeffIn I p) :
    p.map (Ideal.Quotient.mk I) = 0 := by
  ext k
  rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact h k

end CoeffIn

/-! ### Lifting a polynomial from `A ⧸ I` to `A`, coefficient by coefficient -/

section Lift

variable (I : Ideal A)

/-- A normalized section of the quotient map `A → A ⧸ I` (sending `1` to `1` and `0` to `0`). -/
noncomputable def secQuot (a : A ⧸ I) : A := by
  classical
  exact if a = 1 then 1 else if a = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective a)

theorem mk_secQuot (a : A ⧸ I) : Ideal.Quotient.mk I (secQuot I a) = a := by
  unfold secQuot
  split_ifs with h1 h0
  · rw [h1, map_one]
  · rw [h0, map_zero]
  · exact Classical.choose_spec (Ideal.Quotient.mk_surjective a)

@[simp] theorem secQuot_one : secQuot I (1 : A ⧸ I) = 1 := by
  unfold secQuot; rw [if_pos rfl]

theorem secQuot_zero [Nontrivial (A ⧸ I)] : secQuot I (0 : A ⧸ I) = 0 := by
  unfold secQuot
  rw [if_neg (Ne.symm one_ne_zero), if_pos rfl]

theorem secQuot_ne_zero [Nontrivial (A ⧸ I)] {a : A ⧸ I} (h : a ≠ 0) : secQuot I a ≠ 0 := by
  intro h0
  apply h
  rw [← mk_secQuot I a, h0, map_zero]

/-- The coefficient-wise lift of a polynomial along `A → A ⧸ I`. -/
noncomputable def polyLift (p : (A ⧸ I)[X]) : A[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C (secQuot I (p.coeff k)) * X ^ k

theorem coeff_polyLift (p : (A ⧸ I)[X]) (n : ℕ) :
    (polyLift I p).coeff n = if n ≤ p.natDegree then secQuot I (p.coeff n) else 0 := by
  rw [polyLift, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem polyLift_zero [Nontrivial (A ⧸ I)] : polyLift I (0 : (A ⧸ I)[X]) = 0 := by
  ext n
  rw [coeff_polyLift]
  simp only [coeff_zero]
  split_ifs with h
  · rw [secQuot_zero]
  · rfl

theorem natDegree_polyLift [Nontrivial (A ⧸ I)] (p : (A ⧸ I)[X]) :
    (polyLift I p).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [polyLift_zero]
  · apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [coeff_polyLift, if_neg (by omega)]
    · have hlead : p.coeff p.natDegree ≠ 0 := by
        rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hp
      apply le_natDegree_of_ne_zero
      rw [coeff_polyLift, if_pos le_rfl]
      exact secQuot_ne_zero I hlead

theorem polyLift_map (p : (A ⧸ I)[X]) : (polyLift I p).map (Ideal.Quotient.mk I) = p := by
  ext n
  rw [coeff_map, coeff_polyLift]
  split_ifs with h
  · exact mk_secQuot I (p.coeff n)
  · rw [map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n)).symm

theorem isMonicOfDegree_polyLift [Nontrivial (A ⧸ I)] {p : (A ⧸ I)[X]} (hmon : p.Monic) :
    IsMonicOfDegree (polyLift I p) p.natDegree where
  natDegree_eq := natDegree_polyLift I p
  monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one p.natDegree (le_of_eq (natDegree_polyLift I p)) ?_
    rw [coeff_polyLift, if_pos le_rfl, hmon.coeff_natDegree, secQuot_one]

theorem degree_polyLift [Nontrivial (A ⧸ I)] (p : (A ⧸ I)[X]) :
    (polyLift I p).degree = p.degree := by
  by_cases hp : p = 0
  · rw [hp, polyLift_zero, degree_zero, degree_zero]
  · have hq : polyLift I p ≠ 0 := fun h =>
      hp (by rw [← polyLift_map (I := I) p, h, Polynomial.map_zero])
    rw [degree_eq_natDegree hq, degree_eq_natDegree hp, natDegree_polyLift I p]

end Lift


/-! ### Elementary degree bounds -/

section DegreeBound

variable {k : Type*} [CommRing k]

theorem degree_add_lt {p q : k[X]} {m : ℕ} (hp : p.degree < (m : WithBot ℕ))
    (hq : q.degree < (m : WithBot ℕ)) : (p + q).degree < (m : WithBot ℕ) :=
  (degree_add_le _ _).trans_lt (max_lt hp hq)

theorem degree_sub_lt {p q : k[X]} {m : ℕ} (hp : p.degree < (m : WithBot ℕ))
    (hq : q.degree < (m : WithBot ℕ)) : (p - q).degree < (m : WithBot ℕ) :=
  (degree_sub_le _ _).trans_lt (max_lt hp hq)

theorem degree_mul_lt {p q : k[X]} {m n : ℕ} (hp : p.degree < (m : WithBot ℕ))
    (hq : q.degree ≤ (n : WithBot ℕ)) : (p * q).degree < ((m + n : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne p 0 with hp0 | hp0
  · rw [hp0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
  rcases eq_or_ne (p * q) 0 with h0 | h0
  · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
  · have hp' : p.natDegree < m := by
      have h1 : p.degree = ((p.natDegree : ℕ) : WithBot ℕ) := degree_eq_natDegree hp0
      rw [h1] at hp; exact WithBot.coe_lt_coe.mp hp
    have hq' : q.natDegree ≤ n := by
      have h1 : q.degree = ((q.natDegree : ℕ) : WithBot ℕ) := degree_eq_natDegree hq0
      rw [h1] at hq; exact WithBot.coe_le_coe.mp hq
    have hmain : (p * q).natDegree < m + n :=
      calc (p * q).natDegree ≤ p.natDegree + q.natDegree := natDegree_mul_le
        _ < m + n := by omega
    rw [degree_eq_natDegree h0]
    exact_mod_cast hmain

theorem degree_C_mul_lt {p : k[X]} {m : ℕ} (a : k) (hp : p.degree < (m : WithBot ℕ)) :
    (C a * p).degree < (m : WithBot ℕ) := by
  rw [mul_comm]
  simpa using degree_mul_lt (q := C a) hp (n := 0) (by simpa using degree_le_natDegree (p := C a))

theorem natDegree_lt_of_degree_lt {p : k[X]} {m : ℕ} (hp0 : p ≠ 0)
    (hp : p.degree < (m : WithBot ℕ)) : p.natDegree < m := by
  have h1 : p.degree = ((p.natDegree : ℕ) : WithBot ℕ) := degree_eq_natDegree hp0
  rw [h1] at hp
  exact WithBot.coe_lt_coe.mp hp

end DegreeBound

/-- Division-style decomposition in the residue ring: if `g` and `h` are coprime monic
polynomials and `Δ` has degree below `deg g + deg h`, then `Δ = u * h + g * v` with
`deg u < deg g` and `deg v < deg h`. -/
theorem exists_mul_add_of_coprime {k : Type*} [CommRing k] [Nontrivial k]
    {g h : k[X]} (hg : g.Monic) (hh : h.Monic) (hcop : IsCoprime g h)
    {Δ : k[X]} (hΔ : Δ.degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ)) :
    ∃ u v : k[X], u.degree < (g.natDegree : WithBot ℕ) ∧
      v.degree < (h.natDegree : WithBot ℕ) ∧ Δ = u * h + g * v := by
  obtain ⟨a, b, hab⟩ := hcop
  set q : k[X] := (Δ * b) /ₘ g with hq
  set u : k[X] := (Δ * b) %ₘ g with hu
  set v : k[X] := (Δ - u * h) /ₘ g with hv
  have hΔb : u + g * q = Δ * b := by
    rw [hu, hq]; exact modByMonic_add_div (Δ * b) g
  have hu_lt : u.degree < (g.natDegree : WithBot ℕ) := by
    rw [hu, ← degree_eq_natDegree hg.ne_zero]
    exact degree_modByMonic_lt _ hg
  have hdvd : g ∣ Δ - u * h := by
    have key : Δ - u * h - g * (Δ * a + q * h) = 0 := by
      calc Δ - u * h - g * (Δ * a + q * h) = Δ - (u + g * q) * h - g * Δ * a := by ring
        _ = Δ - (Δ * b) * h - g * Δ * a := by rw [hΔb]
        _ = Δ - ((Δ * a) * g + (Δ * b) * h) := by ring
        _ = Δ - Δ * (a * g + b * h) := by ring
        _ = 0 := by rw [hab, mul_one, sub_self]
    exact ⟨Δ * a + q * h, sub_eq_zero.mp key⟩
  refine ⟨u, v, hu_lt, ?_, ?_⟩
  · have hu_lt' : u.degree < (g.natDegree : WithBot ℕ) := hu_lt
    have hdeg : (u * h).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) :=
      degree_mul_lt hu_lt' (q := h) (n := h.natDegree) (by rw [degree_eq_natDegree hh.ne_zero])
    have hp_deg : (Δ - u * h).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) :=
      degree_sub_lt hΔ hdeg
    rw [hv]
    rcases eq_or_ne (Δ - u * h) 0 with hp0 | hp0
    · rw [hp0, zero_divByMonic, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hp_nat : (Δ - u * h).natDegree < g.natDegree + h.natDegree :=
        natDegree_lt_of_degree_lt hp0 hp_deg
      have hnat : ((Δ - u * h) /ₘ g).natDegree = (Δ - u * h).natDegree - g.natDegree := by
        rw [natDegree_divByMonic _ hg]
      rcases eq_or_ne ((Δ - u * h) /ₘ g) 0 with hv0 | hv0
      · rw [hv0, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hge : g.natDegree ≤ (Δ - u * h).natDegree := by
          have hpne : Δ - u * h ≠ 0 := by
            intro h0
            exact hv0 (by rw [h0, zero_divByMonic])
          have h1 : ¬ (Δ - u * h).degree < g.degree := fun hlt =>
            hv0 ((divByMonic_eq_zero_iff hg).mpr hlt)
          have hgdeg : g.degree = ((g.natDegree : ℕ) : WithBot ℕ) := degree_eq_natDegree hg.ne_zero
          have hpdeg : (Δ - u * h).degree = (((Δ - u * h).natDegree : ℕ) : WithBot ℕ) :=
            degree_eq_natDegree hpne
          rw [hpdeg, hgdeg] at h1
          exact Nat.le_of_not_lt (fun hlt => h1 (by exact_mod_cast hlt))
        have hfin : (Δ - u * h).natDegree - g.natDegree < h.natDegree :=
          Nat.sub_lt_iff_lt_add' hge |>.mpr hp_nat
        rw [degree_eq_natDegree hv0, hnat]
        exact_mod_cast hfin
  · have hmod : (Δ - u * h) %ₘ g = 0 := (modByMonic_eq_zero_iff_dvd hg).mpr hdvd
    have hsplit := modByMonic_add_div (Δ - u * h) g
    rw [hmod, zero_add] at hsplit
    rw [hv, hsplit]
    ring

/-! ### The data of Hensel's lemma, and the successive-approximation step -/

section Hensel

variable {I : Ideal A} [Nontrivial (A ⧸ I)] [Nontrivial A] [IsAdicComplete I A]

/-- Writing a polynomial as the sum of its monomials of degree below `n`. -/
theorem eq_sum_range_coeff (p : A[X]) {n : ℕ} (h : p.degree < (n : WithBot ℕ)) :
    p = ∑ i ∈ Finset.range n, C (p.coeff i) * X ^ i := by
  ext k
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hk : k < n
  · rw [if_pos (Finset.mem_range.mpr hk)]
  · rw [if_neg (by simpa using hk)]
    exact coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le h (by exact_mod_cast Nat.le_of_not_lt hk))

/-- The hypotheses of Hensel's lemma, packaged. -/
structure HenselData (I : Ideal A) where
  f : A[X]
  gbar : (A ⧸ I)[X]
  hbar : (A ⧸ I)[X]
  r : ℕ
  s : ℕ
  n : ℕ
  f_monic : f.Monic
  gbar_monic : gbar.Monic
  hbar_monic : hbar.Monic
  coprime : IsCoprime gbar hbar
  deg_eq : r + s = n
  f_deg : f.natDegree = n
  gbar_deg : gbar.natDegree = r
  hbar_deg : hbar.natDegree = s
  factor : f.map (Ideal.Quotient.mk I) = gbar * hbar

variable (D : HenselData I)

/-- A monic lift of `ḡ`. -/
noncomputable def hG : A[X] := polyLift I D.gbar

/-- A monic lift of `h̄`. -/
noncomputable def hH : A[X] := polyLift I D.hbar

theorem hG_isMonicOfDegree : IsMonicOfDegree (hG D) D.r := by
  rw [hG, ← D.gbar_deg]
  exact isMonicOfDegree_polyLift I D.gbar_monic

theorem hH_isMonicOfDegree : IsMonicOfDegree (hH D) D.s := by
  rw [hH, ← D.hbar_deg]
  exact isMonicOfDegree_polyLift I D.hbar_monic

theorem hG_monic : (hG D).Monic := (hG_isMonicOfDegree D).monic

theorem hH_monic : (hH D).Monic := (hH_isMonicOfDegree D).monic

theorem hG_natDegree : (hG D).natDegree = D.r := (hG_isMonicOfDegree D).natDegree_eq

theorem hH_natDegree : (hH D).natDegree = D.s := (hH_isMonicOfDegree D).natDegree_eq

theorem hG_map : (hG D).map (Ideal.Quotient.mk I) = D.gbar := by
  rw [hG]; exact polyLift_map I D.gbar

theorem hH_map : (hH D).map (Ideal.Quotient.mk I) = D.hbar := by
  rw [hH]; exact polyLift_map I D.hbar

theorem hGH_isMonicOfDegree : IsMonicOfDegree (hG D * hH D) D.n := by
  have h := (hG_isMonicOfDegree D).mul (hH_isMonicOfDegree D)
  rwa [D.deg_eq] at h

/-- The difference of two monic polynomials of the same degree has smaller degree. -/
theorem degree_sub_lt_of_monicOfDegree {p q : A[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) : (p - q).degree < (n : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · rw [h0, isMonicOfDegree_zero_iff] at hp hq
    rw [hp, hq, sub_self, degree_zero, h0]
    exact WithBot.bot_lt_coe 0
  · have h := IsMonicOfDegree.natDegree_sub_lt (Nat.pos_iff_ne_zero.mp hn) hp hq
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast h)

/-- Adding a polynomial of smaller degree to a monic polynomial of degree `n`. -/
theorem isMonicOfDegree_add_of_degree_lt {p q : A[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : q.degree < (n : WithBot ℕ)) : IsMonicOfDegree (p + q) n := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simpa using hp
  · exact hp.add_right (natDegree_lt_of_degree_lt hq0 hq)

/-- The intermediate data of the approximation: a pair `(g, h)` that is monic of the right
degrees, reduces to `(ḡ, h̄)`, and satisfies `f - g * h ∈ I^j` with `deg (f - g * h) < n`. -/
structure GoodPair (D : HenselData I) (j : ℕ) where
  g : A[X]
  h : A[X]
  g_monic : g.Monic
  g_deg : g.natDegree = D.r
  h_monic : h.Monic
  h_deg : h.natDegree = D.s
  g_map : g.map (Ideal.Quotient.mk I) = D.gbar
  h_map : h.map (Ideal.Quotient.mk I) = D.hbar
  err_deg : (D.f - g * h).degree < (D.n : WithBot ℕ)
  err_coeff : CoeffIn (I ^ j) (D.f - g * h)

/-- The starting point of the iteration: arbitrary monic lifts of `ḡ` and `h̄`. -/
noncomputable def base : GoodPair D 1 where
  g := hG D
  h := hH D
  g_monic := hG_monic D
  g_deg := hG_natDegree D
  h_monic := hH_monic D
  h_deg := hH_natDegree D
  g_map := hG_map D
  h_map := hH_map D
  err_deg := degree_sub_lt_of_monicOfDegree ⟨D.f_deg, D.f_monic⟩ (hGH_isMonicOfDegree D)
  err_coeff := by
    rw [pow_one]
    apply CoeffIn.of_map_eq_zero
    simp only [Polynomial.map_sub, Polynomial.map_mul, hG_map, hH_map, D.factor, sub_self]

/-- For `i < n` there are polynomials `u, v` of degrees `< r`, `< s` whose combination
`u * H + G * v` agrees with `X^i` modulo `I`. -/
theorem exists_lift_solution (D : HenselData I) (i : ℕ) (hi : i < D.n) :
    ∃ p : A[X] × A[X], p.1.degree < (D.r : WithBot ℕ) ∧ p.2.degree < (D.s : WithBot ℕ) ∧
      CoeffIn I (X ^ i - (p.1 * hH D + hG D * p.2)) := by
  have h1 : i < D.r + D.s := Nat.lt_of_lt_of_le hi (le_of_eq D.deg_eq.symm)
  have hdeg : ((X : (A ⧸ I)[X]) ^ i).degree
      < ((D.gbar.natDegree + D.hbar.natDegree : ℕ) : WithBot ℕ) := by
    rw [D.gbar_deg, D.hbar_deg, degree_X_pow]
    exact_mod_cast h1
  obtain ⟨u, v, hu, hv, heq⟩ := exists_mul_add_of_coprime D.gbar_monic D.hbar_monic D.coprime hdeg
  refine ⟨(polyLift I u, polyLift I v), ?_, ?_, ?_⟩
  · rw [degree_polyLift, ← D.gbar_deg]; exact hu
  · rw [degree_polyLift, ← D.hbar_deg]; exact hv
  · apply CoeffIn.of_map_eq_zero
    have hX : Polynomial.map (Ideal.Quotient.mk I) ((X : A[X]) ^ i) = (X : (A ⧸ I)[X]) ^ i := by
      simp only [Polynomial.map_pow, Polynomial.map_X]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, polyLift_map, hG_map,
      hH_map]
    rw [hX, heq, sub_self]

/-- A choice of the correction pair for `X^i`. -/
noncomputable def sol (D : HenselData I) (i : ℕ) : A[X] × A[X] :=
  if h : i < D.n then Classical.choose (exists_lift_solution D i h) else (0, 0)

theorem sol_fst_deg (D : HenselData I) {i : ℕ} (hi : i < D.n) :
    (sol D i).1.degree < (D.r : WithBot ℕ) := by
  rw [sol, dif_pos hi]
  exact (Classical.choose_spec (exists_lift_solution D i hi)).1

theorem sol_snd_deg (D : HenselData I) {i : ℕ} (hi : i < D.n) :
    (sol D i).2.degree < (D.s : WithBot ℕ) := by
  rw [sol, dif_pos hi]
  exact (Classical.choose_spec (exists_lift_solution D i hi)).2.1

theorem sol_coeff (D : HenselData I) {i : ℕ} (hi : i < D.n) :
    CoeffIn I (X ^ i - ((sol D i).1 * hH D + hG D * (sol D i).2)) := by
  rw [sol, dif_pos hi]
  exact (Classical.choose_spec (exists_lift_solution D i hi)).2.2

/-- The correction produced at one step of the iteration. -/
structure Correction (D : HenselData I) (j : ℕ) (S : GoodPair D j) where
  u : A[X]
  v : A[X]
  u_deg : u.degree < (D.r : WithBot ℕ)
  v_deg : v.degree < (D.s : WithBot ℕ)
  u_coeff : CoeffIn (I ^ j) u
  v_coeff : CoeffIn (I ^ j) v
  err : CoeffIn (I ^ (j + 1)) (D.f - (S.g + u) * (S.h + v))

theorem correction_exists (D : HenselData I) (j : ℕ) (hj : 1 ≤ j) (S : GoodPair D j) :
    Nonempty (Correction D j S) := by
  classical
  set Δ : A[X] := D.f - S.g * S.h with hΔdef
  have hΔdeg : Δ.degree < (D.n : WithBot ℕ) := S.err_deg
  have hΔcoeff : CoeffIn (I ^ j) Δ := S.err_coeff
  have hHsub : CoeffIn I (hH D - S.h) := by
    apply CoeffIn.of_map_eq_zero
    simp only [Polynomial.map_sub, hH_map, S.h_map, sub_self]
  have hGsub : CoeffIn I (hG D - S.g) := by
    apply CoeffIn.of_map_eq_zero
    simp only [Polynomial.map_sub, hG_map, S.g_map, sub_self]
  set u : A[X] := ∑ i ∈ Finset.range D.n, C (Δ.coeff i) * (sol D i).1 with hudef
  set v : A[X] := ∑ i ∈ Finset.range D.n, C (Δ.coeff i) * (sol D i).2 with hvdef
  have u_deg : u.degree < (D.r : WithBot ℕ) := by
    rw [hudef]
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe D.r)).mpr ?_)
    exact fun i hi => degree_C_mul_lt _ (sol_fst_deg D (Finset.mem_range.mp hi))
  have v_deg : v.degree < (D.s : WithBot ℕ) := by
    rw [hvdef]
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe D.s)).mpr ?_)
    exact fun i hi => degree_C_mul_lt _ (sol_snd_deg D (Finset.mem_range.mp hi))
  have u_coeff : CoeffIn (I ^ j) u := by
    rw [hudef]
    exact CoeffIn.sum _ fun i _ => CoeffIn.C_mul_of_mem (hΔcoeff i) _
  have v_coeff : CoeffIn (I ^ j) v := by
    rw [hvdef]
    exact CoeffIn.sum _ fun i _ => CoeffIn.C_mul_of_mem (hΔcoeff i) _
  have hsum1 : (∑ i ∈ Finset.range D.n,
        C (Δ.coeff i) * ((sol D i).1 * hH D + hG D * (sol D i).2)) = u * hH D + hG D * v := by
    rw [hudef, hvdef, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum2 : (∑ i ∈ Finset.range D.n, C (Δ.coeff i) * X ^ i) -
        (∑ i ∈ Finset.range D.n, C (Δ.coeff i) * ((sol D i).1 * hH D + hG D * (sol D i).2)) =
      ∑ i ∈ Finset.range D.n,
        C (Δ.coeff i) * (X ^ i - ((sol D i).1 * hH D + hG D * (sol D i).2)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have herr : D.f - (S.g + u) * (S.h + v) =
      (∑ i ∈ Finset.range D.n,
        C (Δ.coeff i) * (X ^ i - ((sol D i).1 * hH D + hG D * (sol D i).2))) +
        u * (hH D - S.h) + (hG D - S.g) * v - u * v := by
    have e1 : (∑ i ∈ Finset.range D.n,
        C (Δ.coeff i) * (X ^ i - ((sol D i).1 * hH D + hG D * (sol D i).2))) =
        (∑ i ∈ Finset.range D.n, C (Δ.coeff i) * X ^ i) -
        (∑ i ∈ Finset.range D.n, C (Δ.coeff i) * ((sol D i).1 * hH D + hG D * (sol D i).2)) :=
      hsum2.symm
    rw [e1, hsum1, ← eq_sum_range_coeff _ hΔdeg, hΔdef]
    ring
  refine ⟨⟨u, v, u_deg, v_deg, u_coeff, v_coeff, ?_⟩⟩
  rw [herr, pow_succ]
  refine CoeffIn.add (CoeffIn.add (CoeffIn.add (CoeffIn.sum _ ?_) ?_) ?_) ?_
  · intro i hi
    exact CoeffIn.mul (CoeffIn.C (hΔcoeff i)) (sol_coeff D (Finset.mem_range.mp hi))
  · exact CoeffIn.mul u_coeff hHsub
  · have h := CoeffIn.mul hGsub v_coeff
    rw [Ideal.mul_comm] at h
    exact h
  · have h : CoeffIn (I ^ (j + j)) (u * v) := by
      simpa [← pow_add] using CoeffIn.mul u_coeff v_coeff
    exact CoeffIn.mono (Ideal.pow_le_pow_right (Nat.add_le_add_left hj j)) (CoeffIn.neg h)


end Hensel

/-! ### One step of the iteration, and the sequence of approximations -/

section Iteration

variable {I : Ideal A} [Nontrivial (A ⧸ I)] [Nontrivial A] [IsAdicComplete I A]

/-- The correction chosen at one step. -/
noncomputable def correction (D : HenselData I) (j : ℕ) (hj : 1 ≤ j) (S : GoodPair D j) :
    Correction D j S :=
  Classical.choice (correction_exists D j hj S)

/-- One step of the approximation. -/
noncomputable def stepFun (D : HenselData I) (j : ℕ) (hj : 1 ≤ j) (S : GoodPair D j) :
    GoodPair D (j + 1) :=
  let c := correction D j hj S
  { g := S.g + c.u
    h := S.h + c.v
    g_monic := (isMonicOfDegree_add_of_degree_lt ⟨S.g_deg, S.g_monic⟩ c.u_deg).monic
    g_deg := (isMonicOfDegree_add_of_degree_lt ⟨S.g_deg, S.g_monic⟩ c.u_deg).natDegree_eq
    h_monic := (isMonicOfDegree_add_of_degree_lt ⟨S.h_deg, S.h_monic⟩ c.v_deg).monic
    h_deg := (isMonicOfDegree_add_of_degree_lt ⟨S.h_deg, S.h_monic⟩ c.v_deg).natDegree_eq
    g_map := by
      have h : CoeffIn I c.u := CoeffIn.mono (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hj)) c.u_coeff
      rw [Polynomial.map_add, S.g_map, CoeffIn.map_eq_zero h, add_zero]
    h_map := by
      have h : CoeffIn I c.v := CoeffIn.mono (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hj)) c.v_coeff
      rw [Polynomial.map_add, S.h_map, CoeffIn.map_eq_zero h, add_zero]
    err_deg := by
      have h1 : D.f - (S.g + c.u) * (S.h + c.v)
          = (D.f - S.g * S.h) - (c.u * S.h + S.g * c.v) - c.u * c.v := by ring
      rw [h1]
      have h3 : (c.u * S.h).degree < (D.n : WithBot ℕ) := by
        have h := degree_mul_lt c.u_deg (q := S.h) (n := D.s) (by rw [degree_eq_natDegree S.h_monic.ne_zero, S.h_deg])
        rwa [D.deg_eq] at h
      have h4 : (S.g * c.v).degree < (D.n : WithBot ℕ) := by
        rw [mul_comm]
        have h := degree_mul_lt c.v_deg (q := S.g) (n := D.r) (by rw [degree_eq_natDegree S.g_monic.ne_zero, S.g_deg])
        rwa [Nat.add_comm, D.deg_eq] at h
      have h5 : (c.u * c.v).degree < (D.n : WithBot ℕ) := by
        have h := degree_mul_lt c.u_deg (q := c.v) (n := D.s) c.v_deg.le
        rwa [D.deg_eq] at h
      exact degree_sub_lt (degree_sub_lt S.err_deg (degree_add_lt h3 h4)) h5
    err_coeff := c.err }

/-- The sequence of approximations: `state j` is the `j+1`-st approximation. -/
noncomputable def state (D : HenselData I) : (j : ℕ) → GoodPair D (j + 1)
  | 0 => base D
  | (j + 1) => stepFun D (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) (state D j)

theorem state_g_coeff_top (D : HenselData I) (j : ℕ) : (state D j).g.coeff D.r = 1 := by
  rw [← (state D j).g_deg]
  exact (state D j).g_monic.coeff_natDegree

theorem state_h_coeff_top (D : HenselData I) (j : ℕ) : (state D j).h.coeff D.s = 1 := by
  rw [← (state D j).h_deg]
  exact (state D j).h_monic.coeff_natDegree

theorem state_g_sub (D : HenselData I) (l m : ℕ) (hml : m ≤ l) :
    CoeffIn (I ^ (m + 1)) ((state D l).g - (state D m).g) := by
  induction l with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hml
    rw [pow_one]
    simpa using CoeffIn.zero I
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hml with h | h
    · subst h
      simpa using CoeffIn.zero (I ^ (l + 1 + 1))
    · have hm' : m ≤ l := Nat.lt_succ_iff.mp h
      have hstep : (state D (l + 1)).g
          = (state D l).g + (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l))
            (state D l)).u := rfl
      have h2 : (state D l).g + (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l))
            (state D l)).u - (state D m).g
          = ((state D l).g - (state D m).g) +
            (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l)) (state D l)).u := by ring
      rw [hstep, h2]
      refine CoeffIn.add (ih hm') (CoeffIn.mono ?_ 
        (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l)) (state D l)).u_coeff)
      exact Ideal.pow_le_pow_right (Nat.succ_le_succ hm')

theorem state_h_sub (D : HenselData I) (l m : ℕ) (hml : m ≤ l) :
    CoeffIn (I ^ (m + 1)) ((state D l).h - (state D m).h) := by
  induction l with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hml
    rw [pow_one]
    simpa using CoeffIn.zero I
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hml with h | h
    · subst h
      simpa using CoeffIn.zero (I ^ (l + 1 + 1))
    · have hm' : m ≤ l := Nat.lt_succ_iff.mp h
      have hstep : (state D (l + 1)).h
          = (state D l).h + (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l))
            (state D l)).v := rfl
      have h2 : (state D l).h + (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l))
            (state D l)).v - (state D m).h
          = ((state D l).h - (state D m).h) +
            (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l)) (state D l)).v := by ring
      rw [hstep, h2]
      refine CoeffIn.add (ih hm') (CoeffIn.mono ?_
        (correction D (l + 1) (Nat.succ_le_succ (Nat.zero_le l)) (state D l)).v_coeff)
      exact Ideal.pow_le_pow_right (Nat.succ_le_succ hm')

end Iteration

/-! ### Passing to the limit -/

section Limit

variable {I : Ideal A} [Nontrivial (A ⧸ I)] [Nontrivial A] [IsAdicComplete I A]

/-- Two elements of `A` that are congruent modulo every power of `I` are equal. -/
theorem eq_of_sub_mem_all {x y : A} (h : ∀ n : ℕ, x - y ∈ I ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := A) inferInstance (x - y) fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact h n

theorem cauchyG (D : HenselData I) (k : ℕ) : ∀ {m n : ℕ}, m ≤ n →
    (fun j => (state D j).g.coeff k) m ≡ (fun j => (state D j).g.coeff k) n
      [SMOD (I ^ m • ⊤ : Submodule A A)] := by
  intro m n hmn
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
  have h := state_g_sub D n m hmn
  have h1 : (state D n).g.coeff k - (state D m).g.coeff k ∈ I ^ (m + 1) := by
    have hh := h k
    rwa [coeff_sub] at hh
  have h2 : (state D m).g.coeff k - (state D n).g.coeff k ∈ I ^ (m + 1) := by
    have := neg_mem h1
    rwa [neg_sub] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ m) h2

theorem cauchyH (D : HenselData I) (k : ℕ) : ∀ {m n : ℕ}, m ≤ n →
    (fun j => (state D j).h.coeff k) m ≡ (fun j => (state D j).h.coeff k) n
      [SMOD (I ^ m • ⊤ : Submodule A A)] := by
  intro m n hmn
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
  have h := state_h_sub D n m hmn
  have h1 : (state D n).h.coeff k - (state D m).h.coeff k ∈ I ^ (m + 1) := by
    have hh := h k
    rwa [coeff_sub] at hh
  have h2 : (state D m).h.coeff k - (state D n).h.coeff k ∈ I ^ (m + 1) := by
    have := neg_mem h1
    rwa [neg_sub] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ m) h2

/-- The limit of the `k`-th coefficient of the `g`-approximations. -/
noncomputable def limG (D : HenselData I) (k : ℕ) : A :=
  Classical.choose (IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun j => (state D j).g.coeff k) (cauchyG D k))

/-- The limit of the `k`-th coefficient of the `h`-approximations. -/
noncomputable def limH (D : HenselData I) (k : ℕ) : A :=
  Classical.choose (IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun j => (state D j).h.coeff k) (cauchyH D k))

theorem limG_spec (D : HenselData I) (k m : ℕ) :
    (state D m).g.coeff k ≡ limG D k [SMOD (I ^ m • ⊤ : Submodule A A)] :=
  Classical.choose_spec (IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun j => (state D j).g.coeff k) (cauchyG D k)) m

theorem limH_spec (D : HenselData I) (k m : ℕ) :
    (state D m).h.coeff k ≡ limH D k [SMOD (I ^ m • ⊤ : Submodule A A)] :=
  Classical.choose_spec (IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun j => (state D j).h.coeff k) (cauchyH D k)) m

theorem sub_limG_mem (D : HenselData I) (k m : ℕ) :
    (state D m).g.coeff k - limG D k ∈ I ^ m := by
  have h := limG_spec D k m
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  exact h

theorem sub_limH_mem (D : HenselData I) (k m : ℕ) :
    (state D m).h.coeff k - limH D k ∈ I ^ m := by
  have h := limH_spec D k m
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  exact h

/-- The limit of the `g`-approximations, as a polynomial of degree at most `r`. -/
noncomputable def gfinal (D : HenselData I) : A[X] :=
  ∑ k ∈ Finset.range (D.r + 1), C (limG D k) * X ^ k

/-- The limit of the `h`-approximations, as a polynomial of degree at most `s`. -/
noncomputable def hfinal (D : HenselData I) : A[X] :=
  ∑ k ∈ Finset.range (D.s + 1), C (limH D k) * X ^ k

theorem coeff_gfinal (D : HenselData I) (k : ℕ) :
    (gfinal D).coeff k = if k ≤ D.r then limG D k else 0 := by
  rw [gfinal, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_hfinal (D : HenselData I) (k : ℕ) :
    (hfinal D).coeff k = if k ≤ D.s then limH D k else 0 := by
  rw [hfinal, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem limG_top (D : HenselData I) : limG D D.r = 1 := by
  refine eq_of_sub_mem_all (I := I) (fun n => ?_)
  have h := sub_limG_mem D D.r (n + 1)
  have h1 : (state D (n + 1)).g.coeff D.r = 1 := state_g_coeff_top D (n + 1)
  have h2 : limG D D.r - 1 ∈ I ^ (n + 1) := by
    rw [← h1]
    have := neg_mem h
    rwa [neg_sub] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) h2

theorem limH_top (D : HenselData I) : limH D D.s = 1 := by
  refine eq_of_sub_mem_all (I := I) (fun n => ?_)
  have h := sub_limH_mem D D.s (n + 1)
  have h1 : (state D (n + 1)).h.coeff D.s = 1 := state_h_coeff_top D (n + 1)
  have h2 : limH D D.s - 1 ∈ I ^ (n + 1) := by
    rw [← h1]
    have := neg_mem h
    rwa [neg_sub] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) h2

theorem gfinal_coeff_r (D : HenselData I) : (gfinal D).coeff D.r = 1 := by
  rw [coeff_gfinal, if_pos le_rfl]
  exact limG_top D

theorem hfinal_coeff_s (D : HenselData I) : (hfinal D).coeff D.s = 1 := by
  rw [coeff_hfinal, if_pos le_rfl]
  exact limH_top D

theorem gfinal_natDegree (D : HenselData I) : (gfinal D).natDegree = D.r := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_gfinal, if_neg (by omega)]
  · rw [gfinal_coeff_r]; exact one_ne_zero

theorem hfinal_natDegree (D : HenselData I) : (hfinal D).natDegree = D.s := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_hfinal, if_neg (by omega)]
  · rw [hfinal_coeff_s]; exact one_ne_zero

theorem gfinal_monic (D : HenselData I) : (gfinal D).Monic := by
  rw [Monic.def, leadingCoeff, gfinal_natDegree, gfinal_coeff_r]

theorem hfinal_monic (D : HenselData I) : (hfinal D).Monic := by
  rw [Monic.def, leadingCoeff, hfinal_natDegree, hfinal_coeff_s]

theorem coeff_gfinal_equiv (D : HenselData I) (i m : ℕ) :
    (gfinal D).coeff i - (state D (m + 1)).g.coeff i ∈ I ^ (m + 1) := by
  by_cases hi : i ≤ D.r
  · rw [coeff_gfinal, if_pos hi]
    have h := sub_limG_mem D i (m + 1)
    have := neg_mem h
    rwa [neg_sub] at this
  · rw [coeff_gfinal, if_neg hi]
    have hzero : (state D (m + 1)).g.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [(state D (m + 1)).g_deg]; omega)
    rw [hzero, sub_zero]
    exact (I ^ (m + 1)).zero_mem

theorem coeff_hfinal_equiv (D : HenselData I) (i m : ℕ) :
    (hfinal D).coeff i - (state D (m + 1)).h.coeff i ∈ I ^ (m + 1) := by
  by_cases hi : i ≤ D.s
  · rw [coeff_hfinal, if_pos hi]
    have h := sub_limH_mem D i (m + 1)
    have := neg_mem h
    rwa [neg_sub] at this
  · rw [coeff_hfinal, if_neg hi]
    have hzero : (state D (m + 1)).h.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [(state D (m + 1)).h_deg]; omega)
    rw [hzero, sub_zero]
    exact (I ^ (m + 1)).zero_mem

theorem coeff_mul_equiv (D : HenselData I) (l k : ℕ) :
    (gfinal D * hfinal D).coeff k
      - ((state D (l + 1)).g * (state D (l + 1)).h).coeff k ∈ I ^ (l + 1) := by
  rw [coeff_mul, coeff_mul, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  have h1 := coeff_gfinal_equiv D i.1 l
  have h2 := coeff_hfinal_equiv D i.2 l
  have e : (gfinal D).coeff i.1 * (hfinal D).coeff i.2
      - (state D (l + 1)).g.coeff i.1 * (state D (l + 1)).h.coeff i.2
      = ((gfinal D).coeff i.1 - (state D (l + 1)).g.coeff i.1) * (hfinal D).coeff i.2
        + (state D (l + 1)).g.coeff i.1
          * ((hfinal D).coeff i.2 - (state D (l + 1)).h.coeff i.2) := by ring
  rw [e]
  have hA : ((gfinal D).coeff i.1 - (state D (l + 1)).g.coeff i.1) * (hfinal D).coeff i.2
      ∈ I ^ (l + 1) := Ideal.mul_mem_right ((hfinal D).coeff i.2) (I ^ (l + 1)) h1
  have hB : (state D (l + 1)).g.coeff i.1
      * ((hfinal D).coeff i.2 - (state D (l + 1)).h.coeff i.2) ∈ I ^ (l + 1) :=
    Ideal.mul_mem_left (I ^ (l + 1)) ((state D (l + 1)).g.coeff i.1) h2
  exact (I ^ (l + 1)).add_mem hA hB

theorem gfinal_mul_hfinal (D : HenselData I) : gfinal D * hfinal D = D.f := by
  ext k
  refine eq_of_sub_mem_all (I := I) fun n => ?_
  have h1 := coeff_mul_equiv D n k
  have h2 : ((state D (n + 1)).g * (state D (n + 1)).h).coeff k - D.f.coeff k
      ∈ I ^ (n + 1) := by
    have h := (state D (n + 1)).err_coeff k
    have h' : D.f.coeff k - ((state D (n + 1)).g * (state D (n + 1)).h).coeff k
        ∈ I ^ ((n + 1) + 1) := by
      rwa [coeff_sub] at h
    have hle : I ^ ((n + 1) + 1) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
    have := neg_mem (hle h')
    rwa [neg_sub] at this
  have hsum : (gfinal D * hfinal D).coeff k - D.f.coeff k ∈ I ^ (n + 1) := by
    have e : (gfinal D * hfinal D).coeff k - D.f.coeff k
        = ((gfinal D * hfinal D).coeff k
            - ((state D (n + 1)).g * (state D (n + 1)).h).coeff k)
          + (((state D (n + 1)).g * (state D (n + 1)).h).coeff k - D.f.coeff k) := by ring
    rw [e]
    exact (I ^ (n + 1)).add_mem h1 h2
  exact Ideal.pow_le_pow_right (Nat.le_succ n) hsum

theorem gfinal_map (D : HenselData I) :
    (gfinal D).map (Ideal.Quotient.mk I) = D.gbar := by
  ext k
  have h2 : Ideal.Quotient.mk I ((state D 1).g.coeff k) = D.gbar.coeff k := by
    rw [← coeff_map, (state D 1).g_map]
  rw [coeff_map, coeff_gfinal]
  by_cases hk : k ≤ D.r
  · rw [if_pos hk]
    have h := sub_limG_mem D k 1
    have hmem : limG D k - (state D 1).g.coeff k ∈ I := by
      have h' : (state D 1).g.coeff k - limG D k ∈ I ^ 1 := h
      rw [pow_one] at h'
      have := neg_mem h'
      rwa [neg_sub] at this
    have h1 : Ideal.Quotient.mk I (limG D k) = Ideal.Quotient.mk I ((state D 1).g.coeff k) := by
      rw [Ideal.Quotient.eq]
      exact hmem
    rw [h1, h2]
  · rw [if_neg hk, map_zero]
    rw [← h2]
    have hzero : (state D 1).g.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [(state D 1).g_deg]; omega)
    rw [hzero, map_zero]

theorem hfinal_map (D : HenselData I) :
    (hfinal D).map (Ideal.Quotient.mk I) = D.hbar := by
  ext k
  have h2 : Ideal.Quotient.mk I ((state D 1).h.coeff k) = D.hbar.coeff k := by
    rw [← coeff_map, (state D 1).h_map]
  rw [coeff_map, coeff_hfinal]
  by_cases hk : k ≤ D.s
  · rw [if_pos hk]
    have h := sub_limH_mem D k 1
    have hmem : limH D k - (state D 1).h.coeff k ∈ I := by
      have h' : (state D 1).h.coeff k - limH D k ∈ I ^ 1 := h
      rw [pow_one] at h'
      have := neg_mem h'
      rwa [neg_sub] at this
    have h1 : Ideal.Quotient.mk I (limH D k) = Ideal.Quotient.mk I ((state D 1).h.coeff k) := by
      rw [Ideal.Quotient.eq]
      exact hmem
    rw [h1, h2]
  · rw [if_neg hk, map_zero]
    rw [← h2]
    have hzero : (state D 1).h.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [(state D 1).h_deg]; omega)
    rw [hzero, map_zero]

end Limit

/-! ### Hensel's lemma (factorization form) -/

section Final

variable {I : Ideal A} [Nontrivial (A ⧸ I)] [Nontrivial A] [IsAdicComplete I A]

/-- Hensel's lemma in the coprime-factorization form, for any `I`-adically complete ring:
a monic polynomial whose reduction modulo `I` factorizes into coprime monic factors lifts to a
factorization with the same degrees. -/
theorem hensel_factor {f : A[X]} (hf : f.Monic) {gbar hbar : (A ⧸ I)[X]} (hg : gbar.Monic)
    (hh : hbar.Monic) (hcop : IsCoprime gbar hbar)
    (hdeg : gbar.natDegree + hbar.natDegree = f.natDegree)
    (hfac : f.map (Ideal.Quotient.mk I) = gbar * hbar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ g.natDegree = gbar.natDegree ∧
      h.natDegree = hbar.natDegree ∧ g.map (Ideal.Quotient.mk I) = gbar ∧
      h.map (Ideal.Quotient.mk I) = hbar ∧ g * h = f := by
  let D : HenselData I :=
    { f := f
      gbar := gbar
      hbar := hbar
      r := gbar.natDegree
      s := hbar.natDegree
      n := f.natDegree
      f_monic := hf
      gbar_monic := hg
      hbar_monic := hh
      coprime := hcop
      deg_eq := hdeg
      f_deg := rfl
      gbar_deg := rfl
      hbar_deg := rfl
      factor := hfac }
  exact ⟨gfinal D, hfinal D, gfinal_monic D, hfinal_monic D, gfinal_natDegree D,
    hfinal_natDegree D, gfinal_map D, hfinal_map D, gfinal_mul_hfinal D⟩

end Final

/-- **Atiyah–Macdonald, Chapter 10, Exercise 9** (Hensel's lemma, version 1).

Let `A` be a complete local ring with maximal ideal `m`, let `f ∈ A[X]` be monic of degree `n`,
and suppose that the reduction `f̄ ∈ (A/m)[X]` of `f` factorizes as `f̄ = ḡ * h̄`, where `ḡ` and
`h̄` are coprime monic polynomials of degrees `r` and `n - r`.  Then `f` factorizes as `f = g * h`
with `g, h ∈ A[X]` monic of degrees `r` and `n - r`, whose reductions modulo `m` are `ḡ` and `h̄`.

"Complete local ring" is expressed by `IsAdicComplete (maximalIdeal A) A`, i.e. `A` is Hausdorff
and every Cauchy sequence for the `m`-adic topology converges, which is equivalent to the natural
map `A → lim A/m^i` being a bijection (A–M, Chapter 10). -/
theorem solution (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : A[X]) (hf : f.Monic)
    (gbar hbar : (A ⧸ IsLocalRing.maximalIdeal A)[X])
    (hg : gbar.Monic) (hh : hbar.Monic) (hcop : IsCoprime gbar hbar)
    (hdeg : gbar.natDegree + hbar.natDegree = f.natDegree)
    (hfac : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = gbar * hbar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ g.natDegree = gbar.natDegree ∧
      h.natDegree = hbar.natDegree ∧
      g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = gbar ∧
      h.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = hbar ∧ g * h = f :=
  hensel_factor hf hg hh hcop hdeg hfac

end AtiyahMcdonald69.Ex_10_9

/-! ### Axiom check (no `sorry`, no extra axioms) -/

#print axioms AtiyahMcdonald69.Ex_10_9.hensel_factor
#print axioms AtiyahMcdonald69.Ex_10_9.solution
