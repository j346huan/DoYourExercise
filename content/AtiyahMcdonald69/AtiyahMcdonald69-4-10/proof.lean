/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 4,
Exercise 4.10.

For a prime ideal `𝔭` of a ring `A`, `S_𝔭(0)` denotes the kernel of the
canonical homomorphism `A → A_𝔭` (localization at `𝔭`).  The exercise states

  (i)   `S_𝔭(0) ⊆ 𝔭`;
  (ii)  `r(S_𝔭(0)) = 𝔭 ↔ 𝔭` is a minimal prime ideal of `A`;
  (iii) if `𝔭 ⊇ 𝔭'`, then `S_𝔭(0) ⊆ S_𝔭'(0)`;
  (iv)  `⋂_{𝔭 ∈ D(A)} S_𝔭(0) = 0`, where `D(A)` is the set of prime ideals
        minimal over some annihilator ideal `(0 : a)` (Exercise 4.9).

All four parts are proved below (`SAtPrime`, `D`, and the named theorems
`SAtPrime_le`, `radical_SAtPrime_eq_iff`, `SAtPrime_anti`, `iInf_D_SAtPrime`,
bundled as `solution`).

The last section contains a checked counterexample showing that the inclusion
in (iii) cannot be reversed (`𝔭 ⊆ 𝔭' ↛ S_𝔭(0) ⊆ S_𝔭'(0)`); see
`cex_not_monotone`.  This matters because some informal solution texts state
(iii) in the reversed, false form.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_4_10

variable {A : Type*} [CommRing A]

/-! ## `S_𝔭(0)` and its elementary description -/

/-- For a prime ideal `𝔭` of `A`, `SAtPrime 𝔭` is `S_𝔭(0)`: the kernel of the
canonical homomorphism `A → A_𝔭`. -/
noncomputable def SAtPrime (p : Ideal A) [p.IsPrime] : Ideal A :=
  RingHom.ker (algebraMap A (Localization.AtPrime p))

/-- Elements of `S_𝔭(0)` are exactly the elements annihilated by some element
outside `𝔭`. -/
theorem mem_SAtPrime_iff (p : Ideal A) [p.IsPrime] (x : A) :
    x ∈ SAtPrime p ↔ ∃ s : A, s ∉ p ∧ s * x = 0 := by
  rw [SAtPrime, RingHom.mem_ker, IsLocalization.map_eq_zero_iff p.primeCompl
    (Localization.AtPrime p) x]
  exact ⟨fun ⟨⟨s, hs⟩, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨⟨s, hs⟩, h⟩⟩

/-! ## Part (i): `S_𝔭(0) ⊆ 𝔭` -/

theorem SAtPrime_le (p : Ideal A) [p.IsPrime] : SAtPrime p ≤ p := by
  intro x hx
  obtain ⟨s, hs, h⟩ := (mem_SAtPrime_iff p x).1 hx
  have hsp : s * x ∈ p := h ▸ p.zero_mem
  exact ((show p.IsPrime from inferInstance).mem_or_mem hsp).resolve_left hs

/-! ## Part (iii): monotonicity in `𝔭` -/

theorem SAtPrime_anti {p p' : Ideal A} [p.IsPrime] [p'.IsPrime] (h : p' ≤ p) :
    SAtPrime p ≤ SAtPrime p' := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (mem_SAtPrime_iff p x).1 hx
  exact (mem_SAtPrime_iff p' x).2 ⟨s, fun hs' => hs (h hs'), hxs⟩

/-! ## Part (ii): the radical of `S_𝔭(0)` -/

/-- The nilradical of `A_𝔭` is `𝔭A_𝔭` when `𝔭` is a minimal prime of `A`. -/
theorem nilradical_localization (p : Ideal A) [p.IsPrime] (hmin : IsMinimalPrime p) :
    (⊥ : Ideal (Localization.AtPrime p)).radical
      = p.map (algebraMap A (Localization.AtPrime p)) := by
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime p) p (I := ⊥) hmin
  simpa only [Ideal.map_bot] using h

theorem radical_SAtPrime_of_isMinimalPrime (p : Ideal A) [hp : p.IsPrime]
    (hmin : IsMinimalPrime p) : (SAtPrime p).radical = p := by
  have key := nilradical_localization p hmin
  refine le_antisymm ?_ ?_
  · rw [Ideal.IsPrime.radical_le_iff hp]
    exact SAtPrime_le p
  · intro x hx
    have hx' : algebraMap A (Localization.AtPrime p) x
        ∈ (⊥ : Ideal (Localization.AtPrime p)).radical := by
      rw [key]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx'
    rw [Ideal.mem_radical_iff]
    refine ⟨n, ?_⟩
    rw [SAtPrime, RingHom.mem_ker]
    simpa only [Ideal.mem_bot, map_pow] using hn

theorem isMinimalPrime_of_radical_SAtPrime (p : Ideal A) [hp : p.IsPrime]
    (h : (SAtPrime p).radical = p) : IsMinimalPrime p := by
  refine ⟨⟨hp, bot_le⟩, ?_⟩
  intro q hq hqp
  obtain ⟨hq, -⟩ := hq
  have h1 : SAtPrime p ≤ q := (SAtPrime_anti hqp).trans (SAtPrime_le q)
  have h2 : (SAtPrime p).radical ≤ q := (Ideal.IsPrime.radical_le_iff hq).2 h1
  rw [h] at h2
  exact h2

theorem radical_SAtPrime_eq_iff (p : Ideal A) [p.IsPrime] :
    (SAtPrime p).radical = p ↔ IsMinimalPrime p :=
  ⟨isMinimalPrime_of_radical_SAtPrime p, radical_SAtPrime_of_isMinimalPrime p⟩

/-! ## Part (iv): the intersection over `D(A)` -/

/-- `(0 : a)`, the annihilator of the element `a`. -/
def ann (a : A) : Ideal A := Submodule.colon (⊥ : Ideal A) ({a} : Set A)

theorem mem_ann_iff (a x : A) : x ∈ ann a ↔ x * a = 0 := by
  rw [ann, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]

/-- `D(A)` (Exercise 4.9): the set of prime ideals minimal over some
annihilator ideal `(0 : a)`. -/
def D (A : Type*) [CommRing A] : Set (Ideal A) :=
  {p | ∃ a : A, p ∈ (ann a).minimalPrimes}

instance instIsPrimeD (p : D A) : (p : Ideal A).IsPrime := by
  obtain ⟨a, ha⟩ := p.2
  exact ha.isPrime

theorem iInf_D_SAtPrime : (⨅ p : D A, SAtPrime (p : Ideal A)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  by_contra hx0
  have hx0' : x ≠ 0 := by simpa using hx0
  have hne : ann x ≠ ⊤ := by
    intro hone
    have h1 : (1 : A) ∈ ann x := hone ▸ Submodule.mem_top
    rw [mem_ann_iff, one_mul] at h1
    exact hx0' h1
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have := hp.isPrime
  have hxD : x ∈ SAtPrime p := by
    have hmem := Ideal.mem_iInf.1 hx (⟨p, x, hp⟩ : D A)
    simpa using hmem
  obtain ⟨s, hs, hsx⟩ := (mem_SAtPrime_iff p x).1 hxD
  exact hs (hp.le ((mem_ann_iff x s).2 hsx))

/-- `D(A)` is non-empty in a non-trivial ring, so the intersection in (iv) is
not an empty one. -/
theorem nonempty_D [Nontrivial A] : (D A).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x : A, x ≠ 0 := exists_ne 0
  have hne : ann x ≠ ⊤ := by
    intro hone
    have h1 : (1 : A) ∈ ann x := hone ▸ Submodule.mem_top
    rw [mem_ann_iff, one_mul] at h1
    exact hx h1
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  exact ⟨p, x, hp⟩

theorem forall_D_SAtPrime_iff (x : A) :
    (∀ p : D A, x ∈ SAtPrime (p : Ideal A)) ↔ x = 0 := by
  constructor
  · intro hx
    have hmem : x ∈ (⨅ p : D A, SAtPrime (p : Ideal A)) := Ideal.mem_iInf.2 hx
    rw [iInf_D_SAtPrime] at hmem
    simpa using hmem
  · rintro rfl p
    exact Submodule.zero_mem _

/-! ## The exercise, bundled -/

/-- Atiyah–Macdonald, Chapter 4, Exercise 4.10, all four parts.
`SAtPrime p` is `S_𝔭(0) = ker(A → A_𝔭)` and `D A` is the set `D(A)` of Exercise 4.9. -/
theorem solution :
    (∀ (p : Ideal A) [p.IsPrime], SAtPrime p ≤ p) ∧
    (∀ (p : Ideal A) [p.IsPrime], (SAtPrime p).radical = p ↔ IsMinimalPrime p) ∧
    (∀ (p p' : Ideal A) [p.IsPrime] [p'.IsPrime], p' ≤ p → SAtPrime p ≤ SAtPrime p') ∧
    (⨅ p : D A, SAtPrime (p : Ideal A)) = ⊥ :=
  ⟨SAtPrime_le, fun p => radical_SAtPrime_eq_iff p, fun _ _ => SAtPrime_anti, iInf_D_SAtPrime⟩

/-! ## A counterexample to the reversed inclusion of (iii)

The statement of (iii) is *not* symmetric: for `𝔭 ⊆ 𝔭'` it is false in general
that `S_𝔭(0) ⊆ S_𝔭'(0)` (see e.g. the informal solution reproduced in
`.scratch/DoYourExercise`, which mis-states (iii) in this reversed form).

The counterexample is the ring `A = ℤ[ε]/(ε², 2ε) = ℤ ⊕ ℤ/2`, realized as
`TrivSqZeroExt ℤ (ZMod 2)`.  Its prime ideals include `𝔭 = ker(A → ℤ)`,
`(a, m) ↦ a`, and the preimage `𝔭'` of `(2) ⊆ ℤ`; then `𝔭 ⊆ 𝔭'` and
`Ann(ε) = 𝔭'`, so `ε ∈ S_𝔭(0)` (it is killed by `2 ∉ 𝔭`) but
`ε ∉ S_𝔭'(0)`. -/

section Counterexample

/-- The projection `ℤᵐᵒᵖ →+* ℤ`; used to build the (commutative) ring structure on
`TrivSqZeroExt ℤ (ZMod 2)`. -/
def unopHomInt : ℤᵐᵒᵖ →+* ℤ where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_mul' := fun a b => by simp [mul_comm]
  map_zero' := rfl
  map_add' := fun a b => rfl

local instance : Module ℤᵐᵒᵖ (ZMod 2) := Module.compHom (ZMod 2) unopHomInt

local instance : IsCentralScalar ℤ (ZMod 2) := ⟨fun _ _ => rfl⟩

/-- `ℤ[ε]/(ε², 2ε)`, realized as `ℤ ⊕ ℤ/2`. -/
abbrev cexRing : Type := TrivSqZeroExt ℤ (ZMod 2)

/-- The projection `cexRing →+* ℤ`, `(a, m) ↦ a`. -/
abbrev cexFst : cexRing →+* ℤ := TrivSqZeroExt.fstHom ℤ ℤ (ZMod 2)

/-- The class of `ε`. -/
def cexEps : cexRing := TrivSqZeroExt.inr (1 : ZMod 2)

/-- `(2) ⊆ ℤ`, as the kernel of `ℤ → ZMod 2`. -/
def cexTwo : Ideal ℤ := RingHom.ker (Int.castRingHom (ZMod 2))

local instance : cexTwo.IsPrime := RingHom.ker_isPrime _

/-- `𝔭 = ker(A → ℤ)`, the prime `(ε)`. -/
def cexP : Ideal cexRing := RingHom.ker cexFst

/-- `𝔭' =` preimage of `(2)`, the prime `(2, ε)`. -/
def cexP' : Ideal cexRing := Ideal.comap cexFst cexTwo

local instance : cexP.IsPrime := RingHom.ker_isPrime cexFst

local instance : cexP'.IsPrime := Ideal.comap_isPrime cexFst cexTwo

theorem cexFst_apply (g : cexRing) : cexFst g = g.fst := rfl

theorem mem_cexTwo_iff (n : ℤ) : n ∈ cexTwo ↔ ((n : ℤ) : ZMod 2) = 0 := Iff.rfl

/-- `(0 : ε) = 𝔭'`: an element of `A` annihilates `ε` exactly when its `ℤ`-part
is even. -/
theorem mul_cexEps_eq_zero_iff (g : cexRing) : g * cexEps = 0 ↔ g ∈ cexP' := by
  have key : (g * cexEps = 0) ↔ ((g.fst : ℤ) : ZMod 2) = 0 := by
    constructor
    · intro h
      have h2 : (g * cexEps).snd = g.fst • (1 : ZMod 2) := by
        rw [cexEps, TrivSqZeroExt.snd_mul]; simp
      have h3 : g.fst • (1 : ZMod 2) = 0 := by rw [← h2, h]; rfl
      simpa [zsmul_eq_mul] using h3
    · intro h
      have h1 : (g * cexEps).fst = 0 := by rw [cexEps, TrivSqZeroExt.fst_mul]; simp
      have h2 : (g * cexEps).snd = 0 := by
        rw [cexEps, TrivSqZeroExt.snd_mul]; simpa [zsmul_eq_mul] using h
      exact TrivSqZeroExt.ext h1 h2
  rw [key, cexP', Ideal.mem_comap, mem_cexTwo_iff, cexFst_apply]

theorem cexEps_ne_zero : cexEps ≠ 0 := by
  intro h
  have h2 : cexEps.snd = (0 : cexRing).snd := by rw [h]
  rw [cexEps] at h2
  simp at h2

theorem two_notMem_cexP : (2 : cexRing) ∉ cexP := by
  intro h
  have h2 : cexFst (2 : cexRing) = 0 := h
  rw [map_ofNat] at h2
  exact two_ne_zero h2

theorem two_mul_cexEps : (2 : cexRing) * cexEps = 0 := by
  rw [mul_cexEps_eq_zero_iff]
  show cexFst (2 : cexRing) ∈ cexTwo
  rw [mem_cexTwo_iff, map_ofNat]
  decide

theorem cexP_le_cexP' : cexP ≤ cexP' := by
  intro g hg
  rw [← mul_cexEps_eq_zero_iff]
  rw [cexP, RingHom.mem_ker] at hg
  have h1 : (g * cexEps).fst = 0 := by rw [cexEps, TrivSqZeroExt.fst_mul]; simp
  have h2 : (g * cexEps).snd = 0 := by
    rw [cexEps, TrivSqZeroExt.snd_mul]
    have hg' : g.fst = 0 := hg
    rw [hg']; simp
  exact TrivSqZeroExt.ext h1 h2

theorem cexEps_mem_SAtPrime : cexEps ∈ SAtPrime cexP :=
  (mem_SAtPrime_iff cexP cexEps).2 ⟨2, two_notMem_cexP, two_mul_cexEps⟩

theorem cexEps_notMem_SAtPrime : cexEps ∉ SAtPrime cexP' := by
  intro h
  obtain ⟨s, hs, hse⟩ := (mem_SAtPrime_iff cexP' cexEps).1 h
  exact hs ((mul_cexEps_eq_zero_iff s).1 hse)

/-- **The inclusion of Exercise 4.10(iii) cannot be reversed**: `𝔭 ⊆ 𝔭'` while
`S_𝔭(0) ⊄ S_𝔭'(0)`. -/
theorem cex_not_monotone : cexP ≤ cexP' ∧ ¬ SAtPrime cexP ≤ SAtPrime cexP' :=
  ⟨cexP_le_cexP', fun h => cexEps_notMem_SAtPrime (h cexEps_mem_SAtPrime)⟩

end Counterexample

end AtiyahMcdonald69.Ex_4_10

#print axioms AtiyahMcdonald69.Ex_4_10.SAtPrime_le
#print axioms AtiyahMcdonald69.Ex_4_10.SAtPrime_anti
#print axioms AtiyahMcdonald69.Ex_4_10.radical_SAtPrime_eq_iff
#print axioms AtiyahMcdonald69.Ex_4_10.iInf_D_SAtPrime
#print axioms AtiyahMcdonald69.Ex_4_10.forall_D_SAtPrime_iff
#print axioms AtiyahMcdonald69.Ex_4_10.nonempty_D
#print axioms AtiyahMcdonald69.Ex_4_10.solution
#print axioms AtiyahMcdonald69.Ex_4_10.cex_not_monotone
