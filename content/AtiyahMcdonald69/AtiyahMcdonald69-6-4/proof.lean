/-
# Atiyah–Macdonald (1969), Exercise 6.4

Book statement (Chapter 6, "Chain Conditions", Exercise 4):

> Let `M` be a Noetherian `A`-module and let `𝔞` be the annihilator of `M` in `A`.
> Prove that `A/𝔞` is Noetherian. Does a similar result hold with Artinian in place of
> Noetherian?

Source audit. The 1969 text does not add "finitely generated" to the hypothesis; this is
harmless because a Noetherian module over a unital ring is finitely generated
(`Module.IsNoetherian.finite`), and that is exactly how the natural proof uses it. The second
question has the answer **no**; the standard counterexample (also in the published solution
manuals) is `A = ℤ` with `M = ℤ[1/p]/ℤ` the Prüfer `p`-group, which is an Artinian faithful
`ℤ`-module, while `ℤ/Ann(M) = ℤ` is not an Artinian ring. Both directions are formalized below,
so the `IsArtinian`-analogue is recorded as a *disproof*, not as a theorem.

## Main results

* `isNoetherianRing_quotient_annihilator` — the positive assertion of the exercise.
* `pruefer` — the Prüfer `p`-group `ℤ[1/p]/ℤ` as a submodule of `ℚ ⧸ ℤ`.
* `pruefer_isArtinian` — it is an Artinian `ℤ`-module.
* `annihilator_pruefer` — it is faithful: `Ann_ℤ(M) = 0`.
* `not_isArtinianRing_int` — `ℤ` is not an Artinian ring.
* `artinian_analogue_counterexample`, `artinian_analogue_false` — the Artinian analogue of the
  exercise fails, i.e. the answer to the book's question is negative.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_6_4

open Submodule

set_option linter.style.haveILetI false

/-! ## 1. The assertion of the exercise -/

/-- **Atiyah–Macdonald, Exercise 6.4 (Noetherian part).**
If `M` is a Noetherian `A`-module and `𝔞 = Ann_A(M)`, then `A / 𝔞` is a Noetherian ring.

(The book does not say "finitely generated"; that is harmless, since a Noetherian module is
finitely generated, cf. `Module.IsNoetherian.finite`.) -/
theorem isNoetherianRing_quotient_annihilator (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] [IsNoetherian A M] : IsNoetherianRing (A ⧸ Module.annihilator A M) := by
  classical
  haveI : Module.Finite A M := Module.IsNoetherian.finite A M
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  -- evaluation map `a ↦ (a • s_1, …, a • s_n)`; its kernel is the annihilator of `M`
  let φ : A →ₗ[A] (Fin n → M) := LinearMap.pi fun i => LinearMap.toSpanSingleton A M (s i)
  have hφ : ∀ (a : A) (i : Fin n), φ a i = a • s i := fun a i => by simp [φ]
  have hker : LinearMap.ker φ = Module.annihilator A M := by
    refine le_antisymm ?_ ?_
    · intro a ha
      rw [LinearMap.mem_ker] at ha
      rw [Module.mem_annihilator]
      intro m
      have hkey : ∀ x ∈ Submodule.span A (Set.range s), a • x = 0 := by
        apply Submodule.span_induction
        · rintro x ⟨i, rfl⟩
          simpa [hφ] using congrFun ha i
        · simp
        · intro x y _ _ ihx ihy
          rw [smul_add, ihx, ihy, add_zero]
        · intro b x _ ih
          rw [smul_comm, ih, smul_zero]
      have hm : m ∈ Submodule.span A (Set.range s) := by rw [hs]; exact trivial
      exact hkey m hm
    · intro a ha
      rw [LinearMap.mem_ker]
      funext i
      simpa [hφ] using Module.mem_annihilator.mp ha (s i)
  haveI : IsNoetherian A (Fin n → M) := isNoetherian_pi'
  haveI : IsNoetherian A (LinearMap.range φ) := inferInstance
  have e : (A ⧸ Module.annihilator A M) ≃ₗ[A] LinearMap.range φ :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivRange φ)
  haveI : IsNoetherian A (A ⧸ Module.annihilator A M) :=
    isNoetherian_of_surjective e.symm.toLinearMap (LinearMap.range_eq_top.mpr e.symm.surjective)
  exact isNoetherian_of_tower A ‹IsNoetherian A (A ⧸ Module.annihilator A M)›

/-! ## 2. `ℤ` is not an Artinian ring -/

/-- The ideals `(2^n)` form a strictly decreasing sequence in `ℤ`. -/
theorem span_two_pow_strictAnti (n : ℕ) :
    (Ideal.span {((2 : ℤ) ^ (n + 1))} : Ideal ℤ) < Ideal.span {((2 : ℤ) ^ n)} := by
  have hle : Ideal.span {((2 : ℤ) ^ (n + 1))} ≤ Ideal.span {((2 : ℤ) ^ n)} := by
    rw [Submodule.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨2, by rw [pow_succ]⟩
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hmem : (2 : ℤ) ^ n ∈ Ideal.span {((2 : ℤ) ^ (n + 1))} := by
    rw [heq]
    exact Submodule.mem_span_singleton_self _
  rw [Ideal.mem_span_singleton] at hmem
  have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  have h1 : (2 : ℤ) ^ (n + 1) ≤ (2 : ℤ) ^ n := Int.le_of_dvd hpos hmem
  have h2 : (2 : ℤ) ^ n < (2 : ℤ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [hpos]
  omega

/-- **`ℤ` is not an Artinian ring.** -/
theorem not_isArtinianRing_int : ¬ IsArtinianRing ℤ := by
  intro h
  have hwf : WellFounded ((· < ·) : Ideal ℤ → Ideal ℤ → Prop) := h.wf
  obtain ⟨I, hI, hmin⟩ :=
    hwf.has_min (Set.range fun n => (Ideal.span {((2 : ℤ) ^ (n + 1))} : Ideal ℤ)) ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨k, rfl⟩ := hI
  exact hmin _ ⟨k + 1, rfl⟩ (span_two_pow_strictAnti (k + 1))




open Submodule


/-- The point `1/p^k` of the rational circle `ℚ ⧸ ℤ`. -/
noncomputable def pc (p k : ℕ) : AddCircle (1 : ℚ) := ((1 / (p : ℚ) ^ k : ℚ) : AddCircle (1 : ℚ))

/-- The Prüfer `p`-group, as the `p`-power torsion subgroup of `ℚ ⧸ ℤ`. -/
def pruefer (p : ℕ) : Submodule ℤ (AddCircle (1 : ℚ)) where
  carrier := {x | ∃ n : ℕ, (p : ℕ) ^ n • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by
      rw [pow_add, mul_smul, smul_add, smul_add,
        smul_comm ((p : ℕ) ^ m) ((p : ℕ) ^ n) x, hm, smul_zero, hn, smul_zero, add_zero]⟩
  smul_mem' := by
    rintro a x ⟨n, hn⟩
    exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩

lemma mem_pruefer {p : ℕ} {x : AddCircle (1 : ℚ)} :
    x ∈ pruefer p ↔ ∃ n : ℕ, (p : ℕ) ^ n • x = 0 := Iff.rfl

/-- `C p k` is the cyclic subgroup generated by `1/p^k`. -/
noncomputable def C (p k : ℕ) : Submodule ℤ (AddCircle (1 : ℚ)) := Submodule.span ℤ {pc p k}

lemma mem_C_iff {p : ℕ} {x : AddCircle (1 : ℚ)} {k : ℕ} :
    x ∈ C p k ↔ ∃ a : ℤ, a • pc p k = x := Submodule.mem_span_singleton

/-- Every integer is zero in `ℚ ⧸ ℤ`. -/
lemma coe_int_eq_zero (m : ℤ) : ((m : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by rw [zsmul_eq_mul, mul_one]⟩

/-- Natural-number and integer scalar multiplication agree. -/
lemma natCast_zsmul_eq (n : ℕ) (y : AddCircle (1 : ℚ)) : (n : ℤ) • y = n • y := by simp

lemma smul_pc_self {p : ℕ} (hp : p ≠ 0) (k : ℕ) : (p : ℕ) ^ k • pc p k = 0 := by
  rw [pc, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div]
  have h : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k (by exact_mod_cast hp)
  rw [Nat.cast_pow, div_self h, AddCircle.coe_period (p := (1 : ℚ))]

lemma smul_pc_of_le {p : ℕ} (hp : p ≠ 0) {j k : ℕ} (hjk : j ≤ k) :
    (p : ℕ) ^ k • pc p j = 0 := by
  rw [pc, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  push_cast
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hidx : j + (k - j) = k := Nat.add_sub_cancel' hjk
  have key : (p : ℚ) ^ k * (1 / (p : ℚ) ^ j) = ((p ^ (k - j) : ℕ) : ℚ) := by
    rw [← hidx, pow_add]
    push_cast
    field_simp
    congr 1
    omega
  rw [key]
  exact coe_int_eq_zero _

lemma pc_mem_pruefer {p : ℕ} (hp : p ≠ 0) (k : ℕ) : pc p k ∈ pruefer p := ⟨k, smul_pc_self hp k⟩

lemma C_zero (p : ℕ) : C p 0 = ⊥ := by
  have h : pc p 0 = 0 := by
    rw [pc, pow_zero, div_one]
    exact AddCircle.coe_period (p := (1 : ℚ))
  rw [C, h]
  simp

lemma zsmul_eq_zero_of_mem_C {p : ℕ} (hp : p ≠ 0) {k : ℕ} {x : AddCircle (1 : ℚ)}
    (hx : x ∈ C p k) : ((p : ℤ) ^ k) • x = 0 := by
  obtain ⟨a, rfl⟩ := mem_C_iff.mp hx
  have hz : ((p : ℤ) ^ k) • pc p k = 0 := by
    rw [show ((p : ℤ) ^ k) = (((p : ℕ) ^ k : ℕ) : ℤ) from by push_cast; ring,
      natCast_zsmul_eq, smul_pc_self hp k]
  calc ((p : ℤ) ^ k) • (a • pc p k) = (((p : ℤ) ^ k) * a) • pc p k := (mul_smul _ _ _).symm
    _ = (a * (p : ℤ) ^ k) • pc p k := by rw [mul_comm]
    _ = a • (((p : ℤ) ^ k) • pc p k) := mul_smul _ _ _
    _ = 0 := by rw [hz, smul_zero]

lemma smul_eq_zero_of_mem_C {p : ℕ} (hp : p ≠ 0) {k : ℕ} {x : AddCircle (1 : ℚ)}
    (hx : x ∈ C p k) : (p : ℕ) ^ k • x = 0 := by
  have e : (((p : ℕ) ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; ring
  rw [← natCast_zsmul_eq, e]
  exact zsmul_eq_zero_of_mem_C hp hx

lemma mem_C_of_smul_eq_zero {p : ℕ} (hp : 2 ≤ p) {k : ℕ} {x : AddCircle (1 : ℚ)}
    (hx : (p : ℕ) ^ k • x = 0) : x ∈ C p k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, one_smul] at hx
    rw [hx]
    exact (C p 0).zero_mem
  haveI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  have hk0 : 0 < p ^ k := pow_pos (by omega) k
  obtain ⟨m, -, hm⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) (u := x) (n := p ^ k) hk0).mp hx
  rw [mem_C_iff]
  refine ⟨(m : ℤ), ?_⟩
  rw [pc, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← hm]
  congr 1
  push_cast
  rw [mul_one_div, mul_one]

lemma C_mono {p : ℕ} (hp : 2 ≤ p) {j k : ℕ} (hjk : j ≤ k) : C p j ≤ C p k := by
  rw [C, Submodule.span_singleton_le_iff_mem]
  exact mem_C_of_smul_eq_zero hp (smul_pc_of_le (by omega) hjk)

lemma addOrderOf_pc {p : ℕ} (hp : 1 < p) (k : ℕ) : addOrderOf (pc p k) = p ^ k := by
  haveI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  have h : 0 < p ^ k := pow_pos (by omega) k
  have hh := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := p ^ k) h
  simpa [pc] using hh

lemma C_le_C_iff {p : ℕ} (hp : p.Prime) {j k : ℕ} : C p j ≤ C p k ↔ j ≤ k := by
  refine ⟨?_, C_mono hp.two_le⟩
  intro h
  by_contra hjk
  have hkj : k < j := by omega
  have hmem : pc p j ∈ C p k := h (Submodule.subset_span (by simp))
  have hz : (p : ℕ) ^ k • pc p j = 0 := smul_eq_zero_of_mem_C hp.ne_zero hmem
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_pc hp.one_lt j] at hz
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hz
  omega

lemma exists_addOrderOf_eq_pow {p : ℕ} (hp : p.Prime) {x : AddCircle (1 : ℚ)}
    (hx : x ∈ pruefer p) : ∃ j, addOrderOf x = p ^ j := by
  obtain ⟨n, hn⟩ := mem_pruefer.mp hx
  have hdvd : addOrderOf x ∣ p ^ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨j, hj⟩

/-- An element of additive order `p^j` generates the full `p^j`-torsion. -/
lemma span_singleton_eq_C_of_addOrderOf {p : ℕ} (hp : p.Prime) {j : ℕ}
    {x : AddCircle (1 : ℚ)} (hx : addOrderOf x = p ^ j) : Submodule.span ℤ {x} = C p j := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · have h1 : addOrderOf x = 1 := by rw [hx, hj0, pow_zero]
    have hx0 : x = 0 := AddMonoid.addOrderOf_eq_one_iff.mp h1
    rw [hx0, hj0, C_zero]
    simp
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    refine mem_C_of_smul_eq_zero hp.two_le ?_
    rw [← hx]
    exact addOrderOf_nsmul_eq_zero x
  · rw [C, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    haveI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
    have hpos : 0 < p ^ j := pow_pos hp.pos j
    obtain ⟨m, -, hgcd, hmx⟩ :=
      (AddCircle.addOrderOf_eq_pos_iff (p := (1 : ℚ)) (u := x) (n := p ^ j) hpos).mp hx
    have hcop : IsCoprime (m : ℤ) ((p ^ j : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hgcd
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u, ?_⟩
    have hcast : (u : ℚ) * (m : ℚ) + (v : ℚ) * (p : ℚ) ^ j = 1 := by
      have h' := congrArg (fun z : ℤ => (z : ℚ)) huv
      push_cast at h'
      simpa using h'
    have hq : (u : ℚ) * ((m : ℚ) / (p : ℚ) ^ j * 1) = 1 / (p : ℚ) ^ j - (v : ℚ) := by
      have hp0 : (p : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      field_simp
      linarith [hcast]
    have hstep : u • x = ((1 / (p : ℚ) ^ j - (v : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
      rw [← hmx, ← AddCircle.coe_zsmul, zsmul_eq_mul]
      push_cast
      rw [hq]
    rw [hstep, pc, AddCircle.coe_sub, coe_int_eq_zero, sub_zero]

/-- **Structure of the submodules of the Prüfer group**: every `ℤ`-submodule of `pruefer p` is
either the whole group or one of the cyclic subgroups `C p k`. -/
theorem eq_C_or_eq_pruefer {p : ℕ} (hp : p.Prime) {W : Submodule ℤ (AddCircle (1 : ℚ))}
    (hW : W ≤ pruefer p) : (∃ k, W = C p k) ∨ W = pruefer p := by
  classical
  by_cases h : ∃ k, ¬ (C p k ≤ W)
  · set K := Nat.find h with hKdef
    have hK : ¬ (C p K ≤ W) := by
      rw [hKdef]
      exact Nat.find_spec h
    have hKmin : ∀ k, ¬ (C p k ≤ W) → K ≤ k := by
      intro k hk
      rw [hKdef]
      exact Nat.find_min' h hk
    have hbelow : ∀ k < K, C p k ≤ W := by
      intro k hk
      by_contra hc
      exact absurd (hKmin k hc) (by omega)
    left
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · have hWbot : W ≤ ⊥ := by
        intro x hx
        by_contra hne
        simp only [Submodule.mem_bot] at hne
        obtain ⟨j, hj⟩ := exists_addOrderOf_eq_pow hp (hW hx)
        have hspan : Submodule.span ℤ {x} ≤ W := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact hx
        have hCj : C p j ≤ W := by
          rw [← span_singleton_eq_C_of_addOrderOf hp hj]
          exact hspan
        rw [hK0] at hK
        exact hK (le_trans (C_mono hp.two_le (Nat.zero_le j)) hCj)
      exact ⟨0, by rw [C_zero, eq_bot_iff.mpr hWbot]⟩
    · refine ⟨K - 1, le_antisymm ?_ (hbelow (K - 1) (by omega))⟩
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact (C p (K - 1)).zero_mem
      · obtain ⟨j, hj⟩ := exists_addOrderOf_eq_pow hp (hW hx)
        have hspan : Submodule.span ℤ {x} ≤ W := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact hx
        have hCj : C p j ≤ W := by
          rw [← span_singleton_eq_C_of_addOrderOf hp hj]
          exact hspan
        have hjk : j < K := by
          by_contra hc
          exact hK (le_trans (C_mono hp.two_le (by omega)) hCj)
        refine C_mono hp.two_le (Nat.le_sub_one_of_lt hjk) ?_
        rw [← span_singleton_eq_C_of_addOrderOf hp hj]
        exact Submodule.mem_span_singleton_self x
  · right
    have hle : ∀ k, C p k ≤ W := fun k => by
      by_contra hc
      exact h ⟨k, hc⟩
    refine le_antisymm hW ?_
    intro x hx
    obtain ⟨n, hn⟩ := mem_pruefer.mp hx
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, pow_zero, one_smul] at hn
      rw [hn]
      exact W.zero_mem
    · exact hle n (mem_C_of_smul_eq_zero hp.two_le hn)

/-- **The Prüfer `p`-group is an Artinian `ℤ`-module.** -/
theorem pruefer_isArtinian {p : ℕ} (hp : p.Prime) : IsArtinian ℤ ↥(pruefer p) := by
  classical
  rw [← set_has_minimal_iff_artinian]
  intro a ha
  set f : Submodule ℤ ↥(pruefer p) → Submodule ℤ (AddCircle (1 : ℚ)) :=
    fun W => W.map (pruefer p).subtype with hf
  have hf_inj : Function.Injective f := Submodule.map_injective_of_injective Subtype.val_injective
  have hfle : ∀ W, f W ≤ pruefer p := fun W => Submodule.map_subtype_le _ W
  have hfmono : ∀ {V W}, V ≤ W → f V ≤ f W := fun h => Submodule.map_mono h
  have hf_strict : ∀ {V W}, V < W → f V < f W := by
    intro V W h
    exact lt_of_le_of_ne (hfmono h.le) (fun heq => h.ne (hf_inj heq))
  have hftop : f ⊤ = pruefer p := by
    show Submodule.map (pruefer p).subtype ⊤ = pruefer p
    rw [Submodule.map_top, Submodule.range_subtype]
  by_cases hcase : ∃ k, ∃ W ∈ a, f W = C p k
  · obtain ⟨k, ⟨W, hWa, hWk⟩, hmin⟩ :
        ∃ k, (∃ W ∈ a, f W = C p k) ∧ ∀ j, (∃ V ∈ a, f V = C p j) → k ≤ j :=
      ⟨Nat.find hcase, Nat.find_spec hcase, fun j hj => Nat.find_min' hcase hj⟩
    refine ⟨W, hWa, ?_⟩
    rintro I hIa hIlt
    have hlt : f I < C p k := by rw [← hWk]; exact hf_strict hIlt
    rcases eq_C_or_eq_pruefer hp (hfle I) with ⟨j, hj⟩ | hj
    · have hle : C p j ≤ C p k := by
        rw [← hj, ← hWk]
        rw [← hWk] at hlt
        exact hlt.le
      have hjk : j ≤ k := (C_le_C_iff hp).mp hle
      have hjk' : j < k := by
        rcases lt_or_eq_of_le hjk with h' | h'
        · exact h'
        · exact absurd (by rw [hj, h'] : f I = C p k) (ne_of_lt hlt)
      exact absurd (hmin j ⟨I, hIa, hj⟩) (by omega)
    · rw [hj] at hlt
      have h2 : C p k ≤ pruefer p := hWk ▸ hfle W
      exact absurd h2 (not_le_of_gt hlt)
  · have hall : ∀ W ∈ a, W = ⊤ := by
      intro W hWa
      rcases eq_C_or_eq_pruefer hp (hfle W) with ⟨j, hj⟩ | hj
      · exact (hcase ⟨j, W, hWa, hj⟩).elim
      · rw [← hf_inj.eq_iff, hftop]
        exact hj
    obtain ⟨W₀, hW₀⟩ := ha
    refine ⟨⊤, ?_, ?_⟩
    · rw [← hall W₀ hW₀]
      exact hW₀
    · intro I hIa hIlt
      rw [hall I hIa] at hIlt
      exact absurd hIlt (lt_irrefl ⊤)

/-- **The Prüfer `p`-group is a faithful `ℤ`-module.** -/
theorem annihilator_pruefer {p : ℕ} (hp : p.Prime) :
    Module.annihilator ℤ ↥(pruefer p) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  by_contra hane
  have hdvd : ∀ k : ℕ, ((p : ℤ) ^ k) ∣ a := by
    intro k
    have hmem : a • (⟨pc p k, pc_mem_pruefer hp.ne_zero k⟩ : ↥(pruefer p)) = 0 :=
      Module.mem_annihilator.mp ha _
    have hzero : a • pc p k = 0 := by
      have := congrArg (Subtype.val) hmem
      simpa using this
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_pc hp.one_lt k] at hzero
    have e : (((p : ℕ) ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; ring
    rwa [e] at hzero
  have hk := hdvd (a.natAbs + 1)
  have hdvd' : ((p : ℕ) ^ (a.natAbs + 1)) ∣ a.natAbs := by
    have h' : ((p : ℤ) ^ (a.natAbs + 1)).natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr hk
    simpa using h'
  have h1 : (p : ℕ) ^ (a.natAbs + 1) ≤ a.natAbs := by
    refine Nat.le_of_dvd (by omega) hdvd'
  have h2 : a.natAbs < 2 ^ (a.natAbs + 1) := by
    calc a.natAbs < 2 ^ a.natAbs := Nat.lt_two_pow_self
      _ ≤ 2 ^ (a.natAbs + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (a.natAbs + 1) ≤ p ^ (a.natAbs + 1) := Nat.pow_le_pow_left hp.two_le _
  omega


/-! ## 3. The Artinian analogue fails -/

/-- The counterexample to the Artinian analogue: for `A = ℤ` and `M = ℤ[1/p]/ℤ` the module `M`
is Artinian and faithful, yet `A ⧸ Ann_A(M) ≃ ℤ` is not an Artinian ring. -/
theorem artinian_analogue_counterexample {p : ℕ} (hp : p.Prime) :
    IsArtinian ℤ ↥(pruefer p) ∧ Module.annihilator ℤ ↥(pruefer p) = ⊥ ∧
      ¬ IsArtinianRing (ℤ ⧸ Module.annihilator ℤ ↥(pruefer p)) := by
  refine ⟨pruefer_isArtinian hp, annihilator_pruefer hp, ?_⟩
  rw [annihilator_pruefer hp]
  intro h
  haveI : IsArtinianRing (ℤ ⧸ (⊥ : Ideal ℤ)) := h
  exact not_isArtinianRing_int (RingEquiv.isArtinianRing (RingEquiv.quotientBot ℤ))

/-- **Answer to the question of Exercise 6.4: no.** The assertion "if `M` is an Artinian
`A`-module then `A ⧸ Ann_A(M)` is an Artinian ring" is false; `A = ℤ`, `M = ℤ[1/p]/ℤ` is a
counterexample (`artinian_analogue_counterexample`). -/
theorem artinian_analogue_false :
    ¬ ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M],
      IsArtinian A M → IsArtinianRing (A ⧸ Module.annihilator A M) := by
  intro h
  exact (artinian_analogue_counterexample Nat.prime_two).2.2
    ((h ℤ ↥(pruefer 2)) (pruefer_isArtinian Nat.prime_two))

/-- **Exercise 6.4, both parts, in one statement.** The Noetherian assertion holds and the
Artinian analogue fails. -/
theorem solution :
    (∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [IsNoetherian A M],
        IsNoetherianRing (A ⧸ Module.annihilator A M)) ∧
      ¬ ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M],
          IsArtinian A M → IsArtinianRing (A ⧸ Module.annihilator A M) :=
  ⟨isNoetherianRing_quotient_annihilator, artinian_analogue_false⟩

end AtiyahMcdonald69.Ex_6_4

/-! ## Axiom audit (no `sorryAx`, no extra axioms) -/

#print axioms AtiyahMcdonald69.Ex_6_4.isNoetherianRing_quotient_annihilator
#print axioms AtiyahMcdonald69.Ex_6_4.not_isArtinianRing_int
#print axioms AtiyahMcdonald69.Ex_6_4.pruefer_isArtinian
#print axioms AtiyahMcdonald69.Ex_6_4.annihilator_pruefer
#print axioms AtiyahMcdonald69.Ex_6_4.artinian_analogue_counterexample
#print axioms AtiyahMcdonald69.Ex_6_4.artinian_analogue_false
#print axioms AtiyahMcdonald69.Ex_6_4.solution
