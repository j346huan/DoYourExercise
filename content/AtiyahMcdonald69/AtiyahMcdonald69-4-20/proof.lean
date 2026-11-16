/-
Atiyah–Macdonald 1969, Exercise 4.20: the radical of a submodule.

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-20
-/
import Mathlib

/-!
# Atiyah–Macdonald, Exercise 4.20

Let `A` be a commutative ring, `M` an `A`-module and `N ≤ M` a submodule.  The radical of `N`
in `M` is defined to be
`rM N = {x : A | x ^ q • M ⊆ N for some q > 0}` (`rMset` below).

We show that `rM N` is an ideal, that `rM N = (N : M).radical = (Ann (M ⧸ N)).radical`
(`rMset_eq_radical`, `rM_eq_radical_colon`, `rM_eq_radical_annihilator`), and we state and
prove the formulae for `rM` analogous to Atiyah–Macdonald (1.13):

* (i)   `(N : M) ≤ rM N`                                                   (`colon_le_rM`)
* (ii)  `rM N` is a radical ideal                                          (`rM_radical`)
* (iii) `rM (N ⊓ P) = rM N ⊓ rM P` and `rM (I • N) = rM (I • ⊤) ⊓ rM N`    (`rM_inf`, `rM_smul`),
        whence `rM ((I * J) • ⊤) = rM (I • ⊤) ⊓ rM (J • ⊤)`               (`rM_mul_smul`)
* (iv)  `rM N = ⊤ ↔ N = ⊤`                                                 (`rM_eq_top_iff`)
* (v)   `(rM N + rM P).radical ≤ rM (N ⊔ P)`                              (`radical_add_le_rM_sup`),
        and the inclusion is strict in general                              (`not_radical_add_eq`)
* (vi)  for a prime `p` and `n > 0`, `p ≤ rM (p ^ n • ⊤) = rM (p • ⊤)`
        (`le_rM_pow_smul_top`, `rM_pow_smul_top_eq`); if moreover `M` is finitely generated and
        `p ≥ Ann M`, then `rM (p ^ n • ⊤) = p`                    (`rM_prime_pow_smul_top_eq`)
-/

open scoped Pointwise

namespace AtiyahMcdonald69.Ex_4_20

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ## Membership in the radical of the annihilator -/

/-- For `x : A`, `x` lies in the radical of `Ann (M ⧸ N)` iff some positive power of `x` maps
`M` into `N`.  This is the technical form of `rM N = (Ann (M ⧸ N)).radical`. -/
theorem mem_radical_annihilator_iff (N : Submodule A M) (x : A) :
    x ∈ (Module.annihilator A (M ⧸ N)).radical ↔
      ∃ q : ℕ, 0 < q ∧ ∀ m : M, x ^ q • m ∈ N := by
  rw [Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    have key : ∀ m : M, x ^ n • m ∈ N := by
      intro m
      have h : (Submodule.Quotient.mk (x ^ n • m) : M ⧸ N) = 0 := by
        rw [Submodule.Quotient.mk_smul]
        exact (Module.mem_annihilator (R := A) (M := M ⧸ N)).mp hn (Submodule.Quotient.mk m)
      exact (Submodule.Quotient.mk_eq_zero (p := N) (x := x ^ n • m)).mp h
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have htop : N = ⊤ := by
        rw [eq_top_iff]
        intro m _
        refine (Submodule.Quotient.mk_eq_zero (p := N) (x := m)).mp ?_
        simpa using
          (Module.mem_annihilator (R := A) (M := M ⧸ N)).mp hn (Submodule.Quotient.mk m)
      exact ⟨1, one_pos, fun m => htop ▸ Submodule.mem_top⟩
    · exact ⟨n, hnpos, key⟩
  · rintro ⟨q, -, hq⟩
    refine ⟨q, ?_⟩
    rw [Module.mem_annihilator]
    intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N y
    have h : (Submodule.Quotient.mk (x ^ q • m) : M ⧸ N) = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := N) (x := x ^ q • m)).mpr (hq m)
    rwa [Submodule.Quotient.mk_smul] at h

/-! ## The radical of a submodule -/

/-- The set defined in Atiyah–Macdonald, Exercise 4.20: the radical of `N` in `M`. -/
def rMset (N : Submodule A M) : Set A := {x | ∃ q : ℕ, 0 < q ∧ ∀ m : M, x ^ q • m ∈ N}

/-- **The radical of a submodule** `N` of `M`, as an ideal: the radical of the annihilator of
`M ⧸ N`.  By `rMset_eq_radical` this is exactly the set of the exercise, so in particular that
set is an ideal. -/
def rM (N : Submodule A M) : Ideal A := (Module.annihilator A (M ⧸ N)).radical

/-- **Atiyah–Macdonald, Exercise 4.20**: `{x | x ^ q • M ⊆ N for some q > 0}` is (the carrier of)
an ideal, namely the radical of `Ann (M ⧸ N)`. -/
theorem rMset_eq_radical (N : Submodule A M) :
    rMset N = ((Module.annihilator A (M ⧸ N)).radical : Set A) := by
  ext x
  show (∃ q : ℕ, 0 < q ∧ ∀ m : M, x ^ q • m ∈ N) ↔
    x ∈ (Module.annihilator A (M ⧸ N)).radical
  exact (mem_radical_annihilator_iff N x).symm

/-- Characteristic property of `rM N`: `x ∈ rM N` iff some positive power of `x` maps `M`
into `N`. -/
@[simp]
theorem mem_rM_iff {N : Submodule A M} {x : A} :
    x ∈ rM N ↔ ∃ q : ℕ, 0 < q ∧ ∀ m : M, x ^ q • m ∈ N :=
  mem_radical_annihilator_iff N x

/-- **`rM N = (Ann (M ⧸ N)).radical`** — the second equality of Atiyah–Macdonald, Exercise 4.20. -/
theorem rM_eq_radical_annihilator (N : Submodule A M) :
    rM N = (Module.annihilator A (M ⧸ N)).radical := rfl

/-- **`rM N = (N : M).radical`** — the first equality of Atiyah–Macdonald, Exercise 4.20, where
`(N : M) = N.colon ⊤` is the colon ideal of `N` by `M`. -/
theorem rM_eq_radical_colon (N : Submodule A M) :
    rM N = (N.colon (⊤ : Submodule A M)).radical := by
  rw [rM_eq_radical_annihilator, Submodule.annihilator_quotient]
  rfl

/-! ## The formulae analogous to Atiyah–Macdonald (1.13) -/

/-- (i) `(N : M) ⊆ rM N`. -/
theorem colon_le_rM (N : Submodule A M) : N.colon (⊤ : Submodule A M) ≤ rM N := by
  rw [rM_eq_radical_colon]
  exact Ideal.le_radical

/-- (ii) The radical of the radical is itself (the analogue of `r (r a) = r a`). -/
theorem rM_radical (N : Submodule A M) : (rM N).radical = rM N := by
  rw [rM_eq_radical_annihilator, Ideal.radical_idem]

/-- (ii), as a radical ideal. -/
theorem rM_isRadical (N : Submodule A M) : (rM N).IsRadical :=
  Ideal.radical_eq_iff.mp (rM_radical N)

/-- `rM` is monotone in the submodule. -/
theorem rM_mono {N P : Submodule A M} (h : N ≤ P) : rM N ≤ rM P := by
  intro x hx
  rw [mem_rM_iff] at hx ⊢
  obtain ⟨q, hq, hqx⟩ := hx
  exact ⟨q, hq, fun m => h (hqx m)⟩

/-- (iii) `rM (N ∩ P) = rM N ∩ rM P`. -/
theorem rM_inf (N P : Submodule A M) : rM (N ⊓ P) = rM N ⊓ rM P := by
  simp only [rM_eq_radical_colon, Submodule.inf_colon, Ideal.radical_inf]

/-! ### A commutation lemma -/

/-- If `y` maps `M` into `N`, then it maps `I • ⊤ = IM` into `I • N = IN`. -/
theorem smul_mem_ideal_smul {I : Ideal A} {N : Submodule A M} {y : A}
    (h : ∀ m : M, y • m ∈ N) {z : M} (hz : z ∈ I • (⊤ : Submodule A M)) :
    y • z ∈ I • N := by
  have h1 : I • (⊤ : Submodule A M) ≤ (I • N).comap (LinearMap.lsmul A M y) := by
    rw [Submodule.smul_le]
    intro d hd w _
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_comm y d w]
    exact Submodule.smul_mem_smul hd (h w)
  simpa using h1 hz

/-- (iii) `rM (I • N) = rM (I • ⊤) ∩ rM N`. -/
theorem rM_smul (I : Ideal A) (N : Submodule A M) :
    rM (I • N) = rM (I • (⊤ : Submodule A M)) ⊓ rM N := by
  refine le_antisymm (le_inf (rM_mono (Submodule.smul_mono le_rfl le_top))
    (rM_mono Submodule.smul_le_right)) ?_
  intro x hx
  rw [Ideal.mem_inf, mem_rM_iff, mem_rM_iff] at hx
  obtain ⟨⟨n, hn, hn'⟩, ⟨m, hm, hm'⟩⟩ := hx
  rw [mem_rM_iff]
  refine ⟨n + m, Nat.add_pos_left hn m, fun z => ?_⟩
  have hz : x ^ n • z ∈ I • (⊤ : Submodule A M) := hn' z
  have heq : x ^ (n + m) • z = x ^ m • (x ^ n • z) := by
    rw [pow_add, mul_comm (x ^ n), mul_smul]
  rw [heq]
  exact smul_mem_ideal_smul hm' hz

/-- (iii), the exact analogue of `r (I * J) = r I ∩ r J`. -/
theorem rM_mul_smul (I J : Ideal A) :
    rM ((I * J) • (⊤ : Submodule A M)) =
      rM (I • (⊤ : Submodule A M)) ⊓ rM (J • (⊤ : Submodule A M)) := by
  rw [Submodule.mul_smul, rM_smul]

/-- (iv) `rM N = ⊤` iff `N = ⊤` (the analogue of `r a = (1) ↔ a = (1)`). -/
theorem rM_eq_top_iff {N : Submodule A M} : rM N = ⊤ ↔ N = ⊤ := by
  constructor
  · intro h
    have h1 : (1 : A) ∈ rM N := h ▸ Submodule.mem_top
    rw [mem_rM_iff] at h1
    obtain ⟨q, -, hq⟩ := h1
    rw [eq_top_iff]
    intro m _
    simpa using hq m
  · rintro rfl
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rM_iff]
    exact ⟨1, one_pos, fun m => by simp⟩

/-- (v) `r (rM N + rM P) ⊆ rM (N + P)`. -/
theorem radical_add_le_rM_sup (N P : Submodule A M) :
    (rM N + rM P).radical ≤ rM (N ⊔ P) :=
  (rM_isRadical (N ⊔ P)).radical_le_iff.mpr
    (add_le (rM_mono le_sup_left) (rM_mono le_sup_right))

/-! ## The analogue of (1.13)(vi): prime ideals and powers -/

/-- (vi), first part: `p ⊆ rM (p ^ n • ⊤)` for `n > 0`. -/
theorem le_rM_pow_smul_top (p : Ideal A) {n : ℕ} (hn : 0 < n) :
    p ≤ rM (p ^ n • (⊤ : Submodule A M)) := by
  intro x hx
  rw [mem_rM_iff]
  exact ⟨n, hn, fun m => Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (Submodule.mem_top)⟩

/-- (vi), second part: `rM (p ^ n • ⊤) = rM (p • ⊤)` for `n > 0`, proved via the multiplicativity
formula `rM_smul`. -/
theorem rM_pow_succ_smul_top_eq (p : Ideal A) (n : ℕ) :
    rM (p ^ (n + 1) • (⊤ : Submodule A M)) = rM (p • (⊤ : Submodule A M)) := by
  induction n with
  | zero => rw [pow_one]
  | succ k ih =>
    have hpk : p ^ (k + 1 + 1) • (⊤ : Submodule A M) =
        p ^ (k + 1) • (p • (⊤ : Submodule A M)) := by
      rw [pow_succ]
      exact Submodule.smul_assoc _ _ _
    rw [hpk, rM_smul, ih, inf_idem]

/-- (vi), second part: `rM (p ^ n • ⊤) = rM (p • ⊤)` for `n > 0`. -/
theorem rM_pow_smul_top_eq (p : Ideal A) {n : ℕ} (hn : 0 < n) :
    rM (p ^ n • (⊤ : Submodule A M)) = rM (p • (⊤ : Submodule A M)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact rM_pow_succ_smul_top_eq p m

/-- (vi), third part: if `p` is prime, `M` is finitely generated and `p` contains the
annihilator of `M`, then `rM (p ^ n • ⊤) = p` for `n > 0` (the analogue of `r (p ^ n) = p`). -/
theorem rM_prime_pow_smul_top_eq (p : Ideal A) (hp : p.IsPrime) (hfg : Module.Finite A M)
    (hann : Module.annihilator A M ≤ p) {n : ℕ} (hn : 0 < n) :
    rM (p ^ n • (⊤ : Submodule A M)) = p := by
  have : Module.Finite A M := hfg
  refine le_antisymm ?_ (le_rM_pow_smul_top p hn)
  rw [rM_pow_smul_top_eq p hn]
  intro x hx
  rw [mem_rM_iff] at hx
  obtain ⟨q, -, hqx⟩ := hx
  -- `p` lies in the support of `M ⧸ pM`, hence annihilates nothing outside `p`
  have hsupp : (⟨p, hp⟩ : PrimeSpectrum A) ∈
      Module.support A (M ⧸ (p • (⊤ : Submodule A M))) := by
    rw [Module.support_quotient]
    exact ⟨Module.mem_support_iff_of_finite.mpr hann,
      PrimeSpectrum.mem_zeroLocus _ _ |>.mpr le_rfl⟩
  have hann' : Module.annihilator A (M ⧸ (p • (⊤ : Submodule A M))) ≤ p :=
    Module.mem_support_iff_of_finite.mp hsupp
  have hxann : x ^ q ∈ Module.annihilator A (M ⧸ (p • (⊤ : Submodule A M))) := by
    rw [Module.mem_annihilator]
    intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ y
    have h : (Submodule.Quotient.mk (x ^ q • m) : M ⧸ (p • (⊤ : Submodule A M))) = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := p • (⊤ : Submodule A M)) (x := x ^ q • m)).mpr
        (hqx m)
    rwa [Submodule.Quotient.mk_smul] at h
  exact hp.mem_of_pow_mem q (hann' hxann)

/-! ## (v) is not an equality -/

/-- The inclusion of (v) is strict in general: for `M = ℚ × ℚ`, `N = ℚ × 0` and `P = 0 × ℚ` we
have `rM N = rM P = 0` while `N + P = M`, so `r (rM N + rM P) = 0 ≠ A = rM (N + P)`. -/
theorem not_radical_add_eq :
    ∃ N P : Submodule ℚ (ℚ × ℚ), (rM N + rM P).radical ≠ rM (N ⊔ P) := by
  refine ⟨LinearMap.ker (LinearMap.snd ℚ ℚ ℚ), LinearMap.ker (LinearMap.fst ℚ ℚ ℚ), ?_⟩
  have hNcol : (LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)).colon
      (⊤ : Submodule ℚ (ℚ × ℚ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem := (Submodule.mem_colon (N := (LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) :
      Submodule ℚ (ℚ × ℚ))) (S := (⊤ : Submodule ℚ (ℚ × ℚ)))).mp hx ((0 : ℚ), (1 : ℚ))
      Submodule.mem_top
    have hx0 : x = 0 := by simpa using hmem
    simp [hx0]
  have hPcol : (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)).colon
      (⊤ : Submodule ℚ (ℚ × ℚ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem := (Submodule.mem_colon (N := (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) :
      Submodule ℚ (ℚ × ℚ))) (S := (⊤ : Submodule ℚ (ℚ × ℚ)))).mp hx ((1 : ℚ), (0 : ℚ))
      Submodule.mem_top
    have hx0 : x = 0 := by simpa using hmem
    simp [hx0]
  have hNr : rM (LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) = ⊥ := by
    rw [rM_eq_radical_colon, hNcol, Ideal.radical_bot_of_isReduced]
  have hPr : rM (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) = ⊥ := by
    rw [rM_eq_radical_colon, hPcol, Ideal.radical_bot_of_isReduced]
  have hsup : (LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) ⊔
      (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hdecomp : ((a, b) : ℚ × ℚ) = (a, 0) + (0, b) := by simp
    rw [hdecomp]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (by simp))
      (Submodule.mem_sup_right (by simp))
  have hL : (rM (LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) +
      rM (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ))).radical = ⊥ := by
    rw [hNr, hPr]
    simp
  have hR : rM ((LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ)) ⊔
      (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) : Submodule ℚ (ℚ × ℚ))) = ⊤ := by
    rw [hsup, rM_eq_top_iff]
  intro h
  rw [hL, hR] at h
  exact bot_ne_top h

/-! ## The bundled statement -/

/-- Atiyah–Macdonald, Exercise 4.20: the identification of `rM N` with `(N : M).radical` and with
`(Ann (M ⧸ N)).radical`, together with the formulae (i)–(v) and the unconditional part of (vi).
(The remaining part of (vi) is `rM_prime_pow_smul_top_eq`.) -/
theorem solution :
    (∀ N : Submodule A M, rM N = (N.colon (⊤ : Submodule A M)).radical) ∧
    (∀ N : Submodule A M, rM N = (Module.annihilator A (M ⧸ N)).radical) ∧
    (∀ N : Submodule A M, N.colon (⊤ : Submodule A M) ≤ rM N) ∧
    (∀ N : Submodule A M, (rM N).IsRadical) ∧
    (∀ N P : Submodule A M, rM (N ⊓ P) = rM N ⊓ rM P) ∧
    (∀ (I : Ideal A) (N : Submodule A M), rM (I • N) = rM (I • (⊤ : Submodule A M)) ⊓ rM N) ∧
    (∀ N : Submodule A M, rM N = ⊤ ↔ N = ⊤) ∧
    (∀ N P : Submodule A M, (rM N + rM P).radical ≤ rM (N ⊔ P)) ∧
    (∀ (p : Ideal A) (n : ℕ), 0 < n → p ≤ rM (p ^ n • (⊤ : Submodule A M)) ∧
      rM (p ^ n • (⊤ : Submodule A M)) = rM (p • (⊤ : Submodule A M))) :=
  ⟨rM_eq_radical_colon, rM_eq_radical_annihilator, colon_le_rM, rM_isRadical, rM_inf, rM_smul,
    fun N => rM_eq_top_iff (N := N), radical_add_le_rM_sup,
    fun p n hn => ⟨le_rM_pow_smul_top p hn, rM_pow_smul_top_eq (n := n) p hn⟩⟩

/-- The "in particular, `r_M(N)` is an ideal" part of the exercise: the set `rMset N` is the
carrier of an ideal. -/
theorem exists_ideal_coe_eq_rMset (N : Submodule A M) :
    ∃ I : Ideal A, rMset N = (I : Set A) :=
  ⟨rM N, rMset_eq_radical N⟩

end AtiyahMcdonald69.Ex_4_20

/-! ## Axiom check -/

#print axioms AtiyahMcdonald69.Ex_4_20.mem_radical_annihilator_iff
#print axioms AtiyahMcdonald69.Ex_4_20.mem_rM_iff
#print axioms AtiyahMcdonald69.Ex_4_20.smul_mem_ideal_smul
#print axioms AtiyahMcdonald69.Ex_4_20.rM_mono
#print axioms AtiyahMcdonald69.Ex_4_20.rM_isRadical
#print axioms AtiyahMcdonald69.Ex_4_20.rM_pow_succ_smul_top_eq
#print axioms AtiyahMcdonald69.Ex_4_20.rMset_eq_radical
#print axioms AtiyahMcdonald69.Ex_4_20.rM_eq_radical_colon
#print axioms AtiyahMcdonald69.Ex_4_20.rM_eq_radical_annihilator
#print axioms AtiyahMcdonald69.Ex_4_20.colon_le_rM
#print axioms AtiyahMcdonald69.Ex_4_20.rM_radical
#print axioms AtiyahMcdonald69.Ex_4_20.rM_inf
#print axioms AtiyahMcdonald69.Ex_4_20.rM_smul
#print axioms AtiyahMcdonald69.Ex_4_20.rM_mul_smul
#print axioms AtiyahMcdonald69.Ex_4_20.rM_eq_top_iff
#print axioms AtiyahMcdonald69.Ex_4_20.radical_add_le_rM_sup
#print axioms AtiyahMcdonald69.Ex_4_20.le_rM_pow_smul_top
#print axioms AtiyahMcdonald69.Ex_4_20.rM_pow_smul_top_eq
#print axioms AtiyahMcdonald69.Ex_4_20.rM_prime_pow_smul_top_eq
#print axioms AtiyahMcdonald69.Ex_4_20.not_radical_add_eq
#print axioms AtiyahMcdonald69.Ex_4_20.exists_ideal_coe_eq_rMset
#print axioms AtiyahMcdonald69.Ex_4_20.solution
