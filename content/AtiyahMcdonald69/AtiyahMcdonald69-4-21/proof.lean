/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 4 (Primary decomposition), Exercise 4.21, page 57.

The exercise (statement recovered from the book; the OCR of the source text is broken at
this point, see the solutions file `dl/amcd.tex`, page 57, Exercise 4.21):

  An element `x ∈ A` defines an endomorphism `φ_x` of `M`, namely `m ↦ x • m`. The element
  `x` is said to be a *zero-divisor* (resp. *nilpotent*) in `M` if `φ_x` is not injective
  (resp. is nilpotent). A submodule `Q` of `M` is *primary* in `M` if `Q ≠ M` and every
  zero-divisor in `M/Q` is nilpotent.

  Show that if `Q` is primary in `M`, then `(Q : M)` is a primary ideal and hence `r_M(Q)`
  is a prime ideal `p`. We say that `Q` is `p`-primary (in `M`).

  Prove the analogues of (4.3) and (4.4).

Here `(Q : M) = {a ∈ A : aM ⊆ Q}` and, as in Exercise 4.20,
`r_M(Q) = {x ∈ A : x^q M ⊆ Q for some q > 0}`.

Natural proof: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-21>
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_4_21

open Submodule

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ## The definitions of Exercise 4.21 -/

/-- The endomorphism `φ_x : M → M`, `m ↦ x • m`, attached to `x ∈ A`. -/
def phi (x : A) : M →ₗ[A] M := LinearMap.lsmul A M x

@[simp] lemma phi_apply (x : A) (m : M) : phi (M := M) x m = x • m := rfl

lemma phi_pow_apply (x : A) (n : ℕ) (m : M) : ((phi (M := M) x) ^ n) m = x ^ n • m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, phi_apply, map_smul, ih, smul_smul, ← pow_succ']

/-- `x ∈ A` is a *zero-divisor in `M`* if the endomorphism `φ_x` is not injective. -/
def IsZeroDivisorIn (x : A) : Prop := ¬ Function.Injective (phi (M := M) x)

/-- `x ∈ A` is *nilpotent in `M`* if the endomorphism `φ_x` is nilpotent. -/
def IsNilpotentIn (x : A) : Prop := ∃ n : ℕ, ∀ m : M, x ^ n • m = 0

/-- A submodule `Q` of `M` is *primary in `M`* if `Q ≠ M` and every zero-divisor in `M/Q`
is nilpotent. -/
def IsPrimarySubmodule (Q : Submodule A M) : Prop :=
  Q ≠ ⊤ ∧ ∀ x : A, IsZeroDivisorIn (M := M ⧸ Q) x → IsNilpotentIn (M := M ⧸ Q) x

/-- `(Q : M)` is a primary ideal when `Q` is primary; `r_M(Q) = r(Q : M)`, the radical of
that ideal (Exercise 4.20). -/
def radicalInM (Q : Submodule A M) : Ideal A := (Q.colon Set.univ).radical

/-- `Q` is `p`-primary in `M`. -/
def IsPPrimary (Q : Submodule A M) (p : Ideal A) : Prop :=
  IsPrimarySubmodule Q ∧ radicalInM Q = p

/-- `(Q : x) = {m ∈ M : x • m ∈ Q}` for `x ∈ A`, the analogue for submodules of `(q : x)`. -/
def colonElem (Q : Submodule A M) (x : A) : Submodule A M := Q.comap (phi x)

/-! ## Elementary reformulations of the definitions -/

lemma isZeroDivisorIn_iff_exists {x : A} :
    IsZeroDivisorIn (M := M) x ↔ ∃ m : M, m ≠ 0 ∧ x • m = 0 := by
  constructor
  · intro h
    by_contra hc
    simp only [not_exists, not_and] at hc
    refine h fun a b hab => ?_
    rw [phi_apply, phi_apply] at hab
    have hsub : x • (a - b) = 0 := by rw [smul_sub, hab, sub_self]
    have hne : a - b = 0 := by
      by_contra hne
      exact hc (a - b) hne hsub
    rwa [sub_eq_zero] at hne
  · rintro ⟨m, hm, hzero⟩ h
    exact hm (h (by simp [hzero]))

lemma isNilpotentIn_iff_pow_eq_zero {x : A} :
    IsNilpotentIn (M := M) x ↔ ∃ n : ℕ, phi (M := M) x ^ n = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, LinearMap.ext fun m => by rw [LinearMap.zero_apply, phi_pow_apply]; exact hn m⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun m => by
      have h := congrArg (fun f : M →ₗ[A] M => f m) hn
      rwa [LinearMap.zero_apply, phi_pow_apply] at h⟩

lemma smul_top_le_iff {Q : Submodule A M} {r : A} :
    r • (⊤ : Submodule A M) ≤ Q ↔ ∀ m : M, r • m ∈ Q := by
  constructor
  · intro h m
    refine h ?_
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨m, trivial, rfl⟩
  · intro h m hm
    rw [Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    exact h b

lemma isNilpotentIn_iff_smul_top_eq_bot {x : A} :
    IsNilpotentIn (M := M) x ↔ ∃ n : ℕ, x ^ n • (⊤ : Submodule A M) = ⊥ := by
  rw [isNilpotentIn_iff_pow_eq_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Submodule.eq_bot_iff]
    intro m hm
    rw [Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    have h := congrArg (fun f : M →ₗ[A] M => f b) hn
    rwa [LinearMap.zero_apply, phi_pow_apply] at h
  · rintro ⟨n, hn⟩
    refine ⟨n, LinearMap.ext fun m => ?_⟩
    have hmem : x ^ n • m ∈ x ^ n • (⊤ : Submodule A M) := by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨m, trivial, rfl⟩
    rw [hn] at hmem
    rw [phi_pow_apply]
    simpa using hmem

/-! ## The book's definition agrees with the element-wise one -/

/-- A submodule is primary in the sense of Exercise 4.21 (every zero-divisor of `M ⧸ Q` is
nilpotent) iff `r • m ∈ Q` forces `m ∈ Q` or `r` to be nilpotent on `M ⧸ Q`. -/
theorem isPrimarySubmodule_iff {Q : Submodule A M} :
    IsPrimarySubmodule Q ↔ Q.IsPrimary := by
  have key : ∀ x : A,
      (IsZeroDivisorIn (M := M ⧸ Q) x → IsNilpotentIn (M := M ⧸ Q) x) ↔
      (∀ y : M ⧸ Q, y ≠ 0 → x • y = 0 →
        ∃ n : ℕ, x ^ n • (⊤ : Submodule A (M ⧸ Q)) = ⊥) := by
    intro x
    rw [isZeroDivisorIn_iff_exists, isNilpotentIn_iff_smul_top_eq_bot]
    exact ⟨fun h y hy0 hxy => h ⟨y, hy0, hxy⟩, fun h ⟨y, hy0, hxy⟩ => h y hy0 hxy⟩
  rw [Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul, IsPrimarySubmodule]
  simp only [key]

/-! ## `(Q : M)` is a primary ideal, and `r_M(Q)` is a prime ideal -/

/-- **Exercise 4.21, first part.** If `Q` is primary in `M`, then `(Q : M)` is a primary ideal
of `A`. -/
theorem colon_univ_isPrimary {Q : Submodule A M} (hQ : IsPrimarySubmodule Q) :
    (Q.colon Set.univ).IsPrimary := by
  have hQ' : Q.IsPrimary := isPrimarySubmodule_iff.mp hQ
  refine Ideal.isPrimary_iff.mpr ⟨?_, fun {x y} hxy => ?_⟩
  · intro htop
    refine hQ.1 ?_
    rw [eq_top_iff]
    rw [Submodule.colon_eq_top_iff_subset] at htop
    exact fun m _ => htop (Set.mem_univ m)
  · by_cases hx : x ∈ Q.colon Set.univ
    · exact Or.inl hx
    · refine Or.inr ?_
      obtain ⟨m, hm⟩ : ∃ m : M, x • m ∉ Q := by
        simpa only [Submodule.mem_colon, Set.mem_univ, forall_const, not_forall] using hx
      have h1 : y • (x • m) ∈ Q := by
        have h2 := Submodule.mem_colon.mp hxy m (Set.mem_univ m)
        simpa only [mul_smul, smul_comm x y m] using h2
      exact (Submodule.IsPrimary.mem_or_mem hQ' h1).resolve_left hm

/-- Consequently `r_M(Q) = r(Q : M)` is a prime ideal `p`, so that `Q` is `p`-primary. -/
theorem radicalInM_isPrime {Q : Submodule A M} (hQ : IsPrimarySubmodule Q) :
    (radicalInM Q).IsPrime :=
  Submodule.IsPrimary.isPrime_radical_colon (isPrimarySubmodule_iff.mp hQ)

/-- The definition of `r_M(Q)` of Exercise 4.20: the radical of `Q` in `M` is the set of
`x ∈ A` with `x^q M ⊆ Q` for some `q > 0`. -/
theorem mem_radicalInM {Q : Submodule A M} {x : A} :
    x ∈ radicalInM Q ↔ ∃ q : ℕ, 0 < q ∧ x ^ q • (⊤ : Submodule A M) ≤ Q := by
  rw [radicalInM, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [Submodule.mem_colon] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · refine ⟨1, one_pos, smul_top_le_iff.mpr fun m => ?_⟩
      simpa using hn (x • m) (Set.mem_univ (x • m))
    · exact ⟨n, hpos, smul_top_le_iff.mpr fun m => hn m (Set.mem_univ m)⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, Submodule.mem_colon.mpr fun m _ => smul_top_le_iff.mp hn m⟩

/-- `r_M(Q)` is the radical of the annihilator of `M ⧸ Q`. -/
theorem radicalInM_eq_radical_annihilator (Q : Submodule A M) :
    radicalInM Q = (Module.annihilator A (M ⧸ Q)).radical := by
  rw [radicalInM, Submodule.annihilator_quotient]

/-! ## The analogue of (4.3): intersections of `p`-primary submodules -/

/-- **Exercise 4.21, analogue of (4.3).** If `Q i` are `p`-primary in `M` for `i` in a finite
non-empty index type, then `⨅ i, Q i` is `p`-primary in `M`. -/
theorem iInf_isPrimary {ι : Type*} [Fintype ι] [Nonempty ι]
    {Q : ι → Submodule A M} {p : Ideal A}
    (h : ∀ i, IsPrimarySubmodule (Q i)) (hp : ∀ i, radicalInM (Q i) = p) :
    IsPrimarySubmodule (⨅ i, Q i) ∧ radicalInM (⨅ i, Q i) = p := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hmem : i₀ ∈ (Finset.univ : Finset ι) := Finset.mem_univ i₀
  have hpar : ∀ ⦃y : ι⦄, y ∈ (Finset.univ : Finset ι) →
      ((Q y).colon Set.univ).radical = ((Q i₀).colon Set.univ).radical := by
    intro y _
    have h1 : ((Q y).colon Set.univ).radical = p := hp y
    have h2 : ((Q i₀).colon Set.univ).radical = p := hp i₀
    rw [h1, h2]
  have hinf : (Finset.univ.inf Q : Submodule A M) = ⨅ i, Q i := by
    rw [Finset.inf_eq_iInf]
    simp
  have hprim : (⨅ i, Q i).IsPrimary := by
    rw [← hinf]
    exact Submodule.isPrimary_finsetInf hmem (fun {y} _ => isPrimarySubmodule_iff.mp (h y)) hpar
  refine ⟨isPrimarySubmodule_iff.mpr hprim, ?_⟩
  have h1 : radicalInM (⨅ i, Q i)
      = ((Finset.univ : Finset ι).inf fun i => (Q i).colon Set.univ).radical := by
    rw [radicalInM, iInf_colon]
    congr 1
    rw [Finset.inf_eq_iInf]
    simp
  have h2 : ((Q i₀).colon Set.univ).radical = p := hp i₀
  rw [h1, Ideal.radical_finset_inf hmem hpar, h2]

/-! ## The analogue of (4.4): the colon `(Q : x)` for `x ∈ M` -/

/-- **Exercise 4.21, analogue of (4.4)(i)** for `x ∈ M`: if `m ∈ Q` then `(Q : m) = A`. -/
theorem colon_singleton_eq_top {Q : Submodule A M} {m : M} (hm : m ∈ Q) :
    Q.colon {m} = ⊤ := by
  rw [Submodule.colon_eq_top_iff_subset]
  simpa using hm

/-- **Exercise 4.21, analogue of (4.4)(ii)** for `x ∈ M`: if `Q` is `p`-primary and `m ∉ Q`,
then `(Q : m) = {a ∈ A : a • m ∈ Q}` is a `p`-primary ideal of `A`. -/
theorem colon_singleton_isPrimary {Q : Submodule A M} {p : Ideal A}
    (hQ : IsPrimarySubmodule Q) (hp : radicalInM Q = p) {m : M} (hm : m ∉ Q) :
    (Q.colon {m}).IsPrimary ∧ (Q.colon {m}).radical = p := by
  have hQ' : Q.IsPrimary := isPrimarySubmodule_iff.mp hQ
  have hrad : (Q.colon {m}).radical = (Q.colon Set.univ).radical :=
    Submodule.IsPrimary.radical_colon_singleton_of_notMem hQ' hm
  have hp' : (Q.colon Set.univ).radical = p := hp
  refine ⟨Ideal.isPrimary_iff.mpr ⟨?_, fun {a b} hab => ?_⟩, by rw [hrad, hp']⟩
  · intro htop
    rw [Submodule.colon_eq_top_iff_subset] at htop
    exact hm (htop rfl)
  · by_cases ha : a ∈ Q.colon {m}
    · exact Or.inl ha
    · refine Or.inr ?_
      rw [hrad]
      have ham : a • m ∉ Q := by simpa [Submodule.mem_colon_singleton] using ha
      have hab' : (a * b) • m ∈ Q := by simpa [Submodule.mem_colon_singleton] using hab
      have h1 : b • (a • m) ∈ Q := by simpa only [mul_smul, smul_comm a b m] using hab'
      exact (Submodule.IsPrimary.mem_or_mem hQ' h1).resolve_left ham

/-! ## The analogue of (4.4): the colon `(Q : x)` for `x ∈ A` -/

lemma mem_colonElem {Q : Submodule A M} {x : A} {m : M} :
    m ∈ colonElem Q x ↔ x • m ∈ Q := by
  simp [colonElem, phi]

/-- **Exercise 4.21, analogue of (4.4)(i)** for `x ∈ A`: if `x ∈ (Q : M)`, i.e. `xM ⊆ Q`,
then `(Q : x) = M`. -/
theorem colonElem_eq_top {Q : Submodule A M} {x : A} (hx : x ∈ Q.colon Set.univ) :
    colonElem Q x = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  rw [mem_colonElem]
  simpa using Submodule.mem_colon.mp hx m (Set.mem_univ m)

/-- **Exercise 4.21, analogue of (4.4)(ii)** for `x ∈ A`: if `Q` is `p`-primary and
`x ∉ (Q : M)`, then `(Q : x) = {m ∈ M : x • m ∈ Q}` is `p`-primary in `M`. -/
theorem colonElem_isPrimary {Q : Submodule A M} {p : Ideal A}
    (hQ : IsPrimarySubmodule Q) (hp : radicalInM Q = p) {x : A}
    (hx : x ∉ Q.colon Set.univ) :
    IsPrimarySubmodule (colonElem Q x) ∧ radicalInM (colonElem Q x) = p := by
  have hQ' : Q.IsPrimary := isPrimarySubmodule_iff.mp hQ
  have hp' : (Q.colon Set.univ).radical = p := hp
  have hQle : Q ≤ colonElem Q x := by
    intro m hm
    rw [mem_colonElem]
    exact Q.smul_mem x hm
  have hx' : ∃ m : M, x • m ∉ Q := by
    simpa only [Submodule.mem_colon, Set.mem_univ, forall_const, not_forall] using hx
  have hne : colonElem Q x ≠ ⊤ := by
    intro htop
    obtain ⟨m, hm⟩ := hx'
    apply hm
    have : m ∈ colonElem Q x := by rw [htop]; exact Submodule.mem_top
    simpa [mem_colonElem] using this
  have hrad : radicalInM (colonElem Q x) = p := by
    refine le_antisymm ?_ ?_
    · intro a ha
      rw [radicalInM, Ideal.mem_radical_iff] at ha
      obtain ⟨n, hn⟩ := ha
      obtain ⟨m₀, hm₀⟩ := hx'
      have h1 : a ^ n • (⊤ : Submodule A M) ≤ colonElem Q x :=
        smul_top_le_iff.mpr fun m => Submodule.mem_colon.mp hn m (Set.mem_univ m)
      have h2 : a ^ n • m₀ ∈ colonElem Q x :=
        h1 (by rw [Submodule.mem_smul_pointwise_iff_exists]; exact ⟨m₀, trivial, rfl⟩)
      have h3 : a ^ n • (x • m₀) ∈ Q := by
        rw [smul_comm (a ^ n) x m₀]
        exact mem_colonElem.mp h2
      have h4 : a ^ n ∈ (Q.colon Set.univ).radical :=
        (Submodule.IsPrimary.mem_or_mem hQ' h3).resolve_left hm₀
      rw [← hp']
      exact Ideal.mem_radical_of_pow_mem h4
    · rw [← hp']
      refine Ideal.radical_mono ?_
      exact Submodule.colon_mono hQle (Set.Subset.refl _)
  have hP : (colonElem Q x).IsPrimary := by
    refine ⟨hne, fun {a m} ham => ?_⟩
    by_cases hm : m ∈ colonElem Q x
    · exact Or.inl hm
    · refine Or.inr ?_
      have hm' : x • m ∉ Q := by
        intro h
        exact hm (by simpa [mem_colonElem] using h)
      have h2 : x • (a • m) ∈ Q := by simpa [mem_colonElem] using ham
      have h3 : a • (x • m) ∈ Q := by simpa only [mul_smul, smul_comm x a m] using h2
      have h4 : a ∈ (Q.colon Set.univ).radical :=
        (Submodule.IsPrimary.mem_or_mem hQ' h3).resolve_left hm'
      show a ∈ ((colonElem Q x).colon Set.univ).radical
      rw [show ((colonElem Q x).colon Set.univ).radical = p from hrad, ← hp']
      exact h4
  exact ⟨isPrimarySubmodule_iff.mpr hP, hrad⟩

/-- **Exercise 4.21, analogue of (4.4)(iii)** for `x ∈ A`: if `Q` is `p`-primary and `x ∉ p`,
then `(Q : x) = Q`. -/
theorem colonElem_eq_self {Q : Submodule A M} {p : Ideal A}
    (hQ : IsPrimarySubmodule Q) (hp : radicalInM Q = p) {x : A} (hx : x ∉ p) :
    colonElem Q x = Q := by
  have hQ' : Q.IsPrimary := isPrimarySubmodule_iff.mp hQ
  have hp' : (Q.colon Set.univ).radical = p := hp
  refine le_antisymm (fun m hm => ?_) (fun m hm => ?_)
  · by_contra hmQ
    have h1 : x • m ∈ Q := by simpa [mem_colonElem] using hm
    have h2 : x ∈ (Q.colon Set.univ).radical :=
      (Submodule.IsPrimary.mem_or_mem hQ' h1).resolve_left hmQ
    exact hx (by rwa [← hp'])
  · rw [mem_colonElem]
    exact Q.smul_mem x hm

/-! ## The exercise, as a single statement -/

/-- **Atiyah–Macdonald, Exercise 4.21**, in full.

Let `A` be a commutative ring, `M` an `A`-module and `Q ≤ M` a submodule. Recall the
definitions of Exercise 4.21: `x ∈ A` is a *zero-divisor in `M`* if `φ_x : m ↦ x • m` is not
injective and *nilpotent in `M`* if `φ_x` is nilpotent; `Q` is *primary in `M`* if `Q ≠ M` and
every zero-divisor in `M ⧸ Q` is nilpotent; `Q` is *`p`-primary* if it is primary and
`r_M(Q) = p`, where `r_M(Q) = {x ∈ A : x^q M ⊆ Q for some q > 0}` (Exercise 4.20).

Then:
1. `(Q : M)` is a primary ideal, `(Q : M) ≠ A`, `r_M(Q) = r(Q : M)` is a prime ideal `p`, and
   `Q` is `p`-primary (this is the first part of the exercise);
2. (analogue of (4.3)) the intersection of finitely many `p`-primary submodules of `M` is
   `p`-primary;
3. (analogue of (4.4), `x ∈ M`) if `Q` is `p`-primary and `m ∈ M`, then `(Q : m) = A` when
   `m ∈ Q`, and `(Q : m)` is a `p`-primary ideal with `r(Q : m) = p` when `m ∉ Q`;
4. (analogue of (4.4), `x ∈ A`) if `Q` is `p`-primary and `x ∈ A`, then `(Q : x) = M` when
   `x ∈ (Q : M)`, `(Q : x)` is `p`-primary in `M` when `x ∉ (Q : M)`, and `(Q : x) = Q` when
   `x ∉ p`. -/
theorem solution :
    (∀ x : A, IsNilpotentIn (M := M) x ↔ ∃ n : ℕ, phi (M := M) x ^ n = 0)
    ∧ (∀ Q : Submodule A M, IsPrimarySubmodule Q ↔ Q.IsPrimary)
    ∧ (∀ Q : Submodule A M, IsPrimarySubmodule Q → (Q.colon Set.univ).IsPrimary)
    ∧ (∀ Q : Submodule A M, IsPrimarySubmodule Q → (Q.colon Set.univ) ≠ ⊤)
    ∧ (∀ Q : Submodule A M, IsPrimarySubmodule Q → (radicalInM Q).IsPrime)
    ∧ (∀ (Q : Submodule A M) (x : A),
        x ∈ radicalInM Q ↔ ∃ q : ℕ, 0 < q ∧ x ^ q • (⊤ : Submodule A M) ≤ Q)
    ∧ (∀ (ι : Type) [Fintype ι] [Nonempty ι] (Q : ι → Submodule A M) (p : Ideal A),
        (∀ i, IsPPrimary (Q i) p) → IsPPrimary (⨅ i, Q i) p)
    ∧ (∀ (Q : Submodule A M) (p : Ideal A), IsPPrimary Q p →
        ∀ m : M, m ∈ Q → Q.colon {m} = ⊤)
    ∧ (∀ (Q : Submodule A M) (p : Ideal A), IsPPrimary Q p →
        ∀ m : M, m ∉ Q → (Q.colon {m}).IsPrimary ∧ (Q.colon {m}).radical = p)
    ∧ (∀ (Q : Submodule A M), IsPrimarySubmodule Q →
        ∀ x : A, x ∈ Q.colon Set.univ → colonElem Q x = ⊤)
    ∧ (∀ (Q : Submodule A M) (p : Ideal A), IsPPrimary Q p →
        ∀ x : A, x ∉ Q.colon Set.univ → IsPPrimary (colonElem Q x) p)
    ∧ (∀ (Q : Submodule A M) (p : Ideal A), IsPPrimary Q p →
        ∀ x : A, x ∉ p → colonElem Q x = Q) := by
  refine ⟨fun x => isNilpotentIn_iff_pow_eq_zero, fun Q => isPrimarySubmodule_iff,
    fun Q hQ => colon_univ_isPrimary hQ,
    fun Q hQ => (colon_univ_isPrimary hQ).ne_top,
    fun Q hQ => radicalInM_isPrime hQ,
    fun Q x => mem_radicalInM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ι _ _ Q p h
    exact iInf_isPrimary (fun i => (h i).1) fun i => (h i).2
  · rintro Q p ⟨_, _⟩ m hm
    exact colon_singleton_eq_top hm
  · rintro Q p ⟨hQ, hp⟩ m hm
    exact colon_singleton_isPrimary hQ hp hm
  · rintro Q _ x hx
    exact colonElem_eq_top hx
  · rintro Q p ⟨hQ, hp⟩ x hx
    exact colonElem_isPrimary hQ hp hx
  · rintro Q p ⟨hQ, hp⟩ x hx
    exact colonElem_eq_self hQ hp hx

#print axioms AtiyahMcdonald69.Ex_4_21.isPrimarySubmodule_iff
#print axioms AtiyahMcdonald69.Ex_4_21.colon_univ_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_21.radicalInM_isPrime
#print axioms AtiyahMcdonald69.Ex_4_21.mem_radicalInM
#print axioms AtiyahMcdonald69.Ex_4_21.radicalInM_eq_radical_annihilator
#print axioms AtiyahMcdonald69.Ex_4_21.mem_colonElem
#print axioms AtiyahMcdonald69.Ex_4_21.iInf_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_21.colon_singleton_eq_top
#print axioms AtiyahMcdonald69.Ex_4_21.colon_singleton_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_21.colonElem_eq_top
#print axioms AtiyahMcdonald69.Ex_4_21.colonElem_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_21.colonElem_eq_self
#print axioms AtiyahMcdonald69.Ex_4_21.solution

end AtiyahMcdonald69.Ex_4_21
