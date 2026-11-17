/-
# Hartshorne, Algebraic Geometry, Exercise I.2.9: the projective closure of an affine variety
-/

import Mathlib

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_2_9

/-! ## 1. Projective space as the set of lines through the origin -/

variable {k : Type*} [Field k]

/-- The (finite) set of indices at which `v` does not vanish. -/
def nzIdx {n : ℕ} (v : Fin (n + 1) → k) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter fun i => v i ≠ 0

theorem nzIdx_nonempty {n : ℕ} {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    (nzIdx v).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  exact hv (funext fun i => by
    have hi : i ∉ nzIdx v := by rw [h]; exact Finset.notMem_empty i
    simpa [nzIdx] using hi)

/-- The first index at which `v` does not vanish. -/
def firstIdx {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) : Fin (n + 1) :=
  (nzIdx v).min' (nzIdx_nonempty hv)

theorem firstIdx_mem {n : ℕ} {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    v (firstIdx v hv) ≠ 0 := by
  classical
  have h := Finset.min'_mem (nzIdx v) (nzIdx_nonempty hv)
  exact (Finset.mem_filter.mp h).2

theorem firstIdx_min {n : ℕ} {v : Fin (n + 1) → k} (hv : v ≠ 0) {j : Fin (n + 1)}
    (hj : j < firstIdx v hv) : v j = 0 := by
  classical
  by_contra h
  have h' : j ∈ nzIdx v := by simp [nzIdx, h]
  have hle : firstIdx v hv ≤ j := Finset.min'_le (nzIdx v) j h'
  omega

/-- The canonical normalized representative of the line spanned by a nonzero vector:
the first nonzero coordinate is rescaled to `1`. -/
def normalize {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) : Fin (n + 1) → k :=
  fun j => if j < firstIdx v hv then 0 else v j / v (firstIdx v hv)

theorem normalize_self {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    normalize v hv (firstIdx v hv) = 1 := by
  simp only [normalize, lt_irrefl, ↓reduceIte]
  exact div_self (firstIdx_mem hv)

theorem normalize_lt {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) {j : Fin (n + 1)}
    (hj : j < firstIdx v hv) : normalize v hv j = 0 := by
  simp only [normalize, hj, ↓reduceIte]

theorem normalize_ne_zero {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    normalize v hv ≠ 0 := by
  intro h
  have := normalize_self v hv
  rw [h] at this
  exact zero_ne_one this

/-- A projective point of `Pⁿ`: the canonical representative of a line through the origin,
i.e. a nonzero vector of `k^{n+1}` whose first nonzero coordinate is `1`. -/
def ProjPoint (k : Type*) [Field k] (n : ℕ) : Type _ :=
  {v : Fin (n + 1) → k // v ≠ 0 ∧ ∃ i, v i = 1 ∧ ∀ j, j < i → v j = 0}

namespace ProjPoint

theorem rep_ne_zero {n : ℕ} (P : ProjPoint k n) : P.1 ≠ 0 := P.2.1

theorem exists_normal {n : ℕ} (P : ProjPoint k n) :
    ∃ i, P.1 i = 1 ∧ ∀ j, j < i → P.1 j = 0 := P.2.2

/-- The canonical representative of the projective point defined by a nonzero vector. -/
def mk {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) : ProjPoint k n :=
  ⟨normalize v hv, normalize_ne_zero v hv, firstIdx v hv, normalize_self v hv,
    fun _ hj => normalize_lt v hv hj⟩

/-- The line through the origin spanned by `v`. -/
def lineOf {n : ℕ} (v : Fin (n + 1) → k) : Set (Fin (n + 1) → k) :=
  {w | ∃ c : k, w = c • v}

theorem mem_lineOf {n : ℕ} (v w : Fin (n + 1) → k) :
    w ∈ lineOf v ↔ ∃ c : k, w = c • v := Iff.rfl

theorem normalize_eq_smul {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    normalize v hv = (v (firstIdx v hv))⁻¹ • v := by
  funext j
  by_cases hj : j < firstIdx v hv
  · rw [normalize_lt v hv hj, Pi.smul_apply, smul_eq_mul, firstIdx_min hv hj, mul_zero]
  · simp only [normalize, hj, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, div_eq_mul_inv]


theorem mk_val {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    (mk v hv).1 = normalize v hv := rfl

theorem mk_self {n : ℕ} (P : ProjPoint k n) : mk P.1 P.rep_ne_zero = P := by
  obtain ⟨i, hi1, hi0⟩ := P.exists_normal
  apply Subtype.ext
  have hfi : firstIdx P.1 P.rep_ne_zero = i := by
    refine le_antisymm ?_ ?_
    · classical
      exact Finset.min'_le (nzIdx P.1) i (by simp [nzIdx, hi1])
    · by_contra h
      have h1 : firstIdx P.1 P.rep_ne_zero < i := not_le.mp h
      exact (firstIdx_mem P.rep_ne_zero) (hi0 _ h1)
  funext j
  simp only [mk_val, normalize, hfi]
  rcases lt_trichotomy j i with h | h | h
  · rw [if_pos h, hi0 j h]
  · subst h
    rw [if_neg (lt_irrefl _), div_self (by rw [hi1]; exact one_ne_zero)]
    exact hi1.symm
  · rw [if_neg (not_lt.mpr (le_of_lt h)), hi1, div_one]

theorem lineOf_mk {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    lineOf (mk v hv).1 = lineOf v := by
  ext w
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a * (v (firstIdx v hv))⁻¹, ?_⟩
    rw [mk_val, normalize_eq_smul, smul_smul]
  · rintro ⟨a, rfl⟩
    refine ⟨a * v (firstIdx v hv), ?_⟩
    rw [mk_val, normalize_eq_smul, smul_smul, mul_assoc, mul_inv_cancel₀ (firstIdx_mem hv), mul_one]

theorem eq_of_lineOf_eq {n : ℕ} {P Q : ProjPoint k n} (h : lineOf P.1 = lineOf Q.1) : P = Q := by
  obtain ⟨iP, hiP1, hiP0⟩ := P.exists_normal
  obtain ⟨iQ, hiQ1, hiQ0⟩ := Q.exists_normal
  have hmem : Q.1 ∈ lineOf P.1 := by rw [h]; exact ⟨1, (one_smul k Q.1).symm⟩
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact Q.rep_ne_zero hc
  have hQi : Q.1 iP = c := by rw [hc, Pi.smul_apply, smul_eq_mul, hiP1, mul_one]
  have hne : Q.1 iP ≠ 0 := by rw [hQi]; exact hc0
  have hle : iQ ≤ iP := by
    by_contra hlt
    exact hne (hiQ0 iP (not_le.mp hlt))
  have heq : iQ = iP := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have h1 : Q.1 iQ = 0 := by
        rw [hc, Pi.smul_apply, smul_eq_mul, hiP0 iQ hlt, mul_zero]
      rw [hiQ1] at h1
      exact one_ne_zero h1
    · exact heq
  have hc1 : c = 1 := by rw [← hQi, ← heq]; exact hiQ1
  apply Subtype.ext
  rw [hc, hc1, one_smul]

theorem existsUnique_lineOf {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃! P : ProjPoint k n, lineOf P.1 = lineOf v :=
  ⟨mk v hv, lineOf_mk v hv,
    fun _ hQ => eq_of_lineOf_eq (hQ.trans (lineOf_mk v hv).symm)⟩

/-- **Faithfulness of the model**: the canonical normalized vectors of `Pⁿ` are exactly the
lines through the origin of `k^{n+1}`. -/
theorem lineEquiv {n : ℕ} :
    ∀ L : {L : Set (Fin (n + 1) → k) // ∃ v, v ≠ 0 ∧ L = lineOf v},
      ∃! P : ProjPoint k n, lineOf P.1 = L.1 := by
  rintro ⟨L, v, hv, rfl⟩
  exact existsUnique_lineOf v hv

/-- The standard identification `Aⁿ → Pⁿ`, `a ↦ [1 : a₁ : … : aₙ]`. -/
def iota {n : ℕ} (a : Fin n → k) : ProjPoint k n :=
  ⟨Fin.cons 1 a, by
    intro h
    have := congrFun h 0
    simp at this, 0, by simp, by
    intro j hj
    exact absurd hj (Nat.not_lt_zero j)⟩

@[simp]
theorem iota_apply_zero {n : ℕ} (a : Fin n → k) : (iota a).1 0 = 1 := by
  simp [iota]

@[simp]
theorem iota_apply_succ {n : ℕ} (a : Fin n → k) (i : Fin n) :
    (iota a).1 i.succ = a i := by
  simp [iota]

theorem iota_injective {n : ℕ} : Function.Injective (iota (k := k) (n := n)) := by
  intro a b h
  funext i
  have := congrFun (congrArg Subtype.val h) i.succ
  simpa using this

/-- Vanishing of a polynomial at a projective point, evaluated at the canonical representative. -/
def vanishes {n : ℕ} (F : MvPolynomial (Fin (n + 1)) k) (P : ProjPoint k n) : Prop :=
  MvPolynomial.aeval (R := k) P.1 F = 0

theorem vanishes_aeval_iota {n : ℕ} (F : MvPolynomial (Fin (n + 1)) k) (a : Fin n → k) :
    vanishes F (iota a) ↔ MvPolynomial.aeval (R := k) (Fin.cons 1 a) F = 0 := by
  rw [vanishes]
  constructor
  · intro h; exact h
  · intro h; exact h

/-- The zero locus in `Pⁿ` of a set of polynomials. -/
def projZeroLocus {n : ℕ} (T : Set (MvPolynomial (Fin (n + 1)) k)) : Set (ProjPoint k n) :=
  {P | ∀ F ∈ T, vanishes F P}

theorem mem_projZeroLocus {n : ℕ} {T : Set (MvPolynomial (Fin (n + 1)) k)} {P : ProjPoint k n} :
    P ∈ projZeroLocus T ↔ ∀ F ∈ T, vanishes F P := Iff.rfl

/-- A subset of `Pⁿ` is Zariski closed if it is the zero locus of a set of homogeneous
polynomials. -/
def IsProjClosed {n : ℕ} (S : Set (ProjPoint k n)) : Prop :=
  ∃ T : Set (MvPolynomial (Fin (n + 1)) k), (∀ F ∈ T, F.IsHomogeneous F.totalDegree) ∧
    S = projZeroLocus T

theorem isProjClosed_empty {n : ℕ} : IsProjClosed (∅ : Set (ProjPoint k n)) := by
  refine ⟨{1}, ?_, ?_⟩
  · intro F hF
    rw [Set.mem_singleton_iff] at hF
    subst hF
    simpa using (MvPolynomial.isHomogeneous_one (σ := Fin (n + 1)) (R := k))
  · ext P
    constructor
    · intro h; exact h.elim
    · intro h
      have h1 := h 1 (by simp)
      simp [vanishes] at h1

theorem isProjClosed_univ {n : ℕ} : IsProjClosed (Set.univ : Set (ProjPoint k n)) := by
  refine ⟨∅, ?_, ?_⟩
  · intro F hF; exact absurd hF (by simp)
  · ext P; simp [projZeroLocus]

theorem isProjClosed_iInter {n : ℕ} {ι : Type*} {S : ι → Set (ProjPoint k n)}
    (hS : ∀ i, IsProjClosed (S i)) : IsProjClosed (⋂ i, S i) := by
  classical
  choose T hT hTS using hS
  refine ⟨⋃ i, T i, ?_, ?_⟩
  · intro F hF
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hF
    exact hT i F hi
  · ext P
    simp only [Set.mem_iInter, mem_projZeroLocus, Set.mem_iUnion]
    constructor
    · intro h F ⟨i, hi⟩
      have hPi : P ∈ projZeroLocus (T i) := by rw [← hTS i]; exact h i
      exact hPi F hi
    · intro h i
      rw [hTS i]
      intro F hF
      exact h F ⟨i, hF⟩

theorem isProjClosed_sInter {n : ℕ} {S : Set (Set (ProjPoint k n))}
    (hS : ∀ s ∈ S, IsProjClosed s) : IsProjClosed (⋂₀ S) := by
  classical
  choose T hT hTS using fun s : S => hS s.1 s.2
  refine ⟨⋃ s : S, T s, ?_, ?_⟩
  · intro F hF
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hF
    exact hT s F hs
  · ext P
    simp only [Set.mem_sInter, mem_projZeroLocus, Set.mem_iUnion]
    constructor
    · intro h F
      rintro ⟨s, hFs⟩
      have hPs : P ∈ projZeroLocus (T s) := by rw [← hTS s]; exact h s.1 s.2
      exact hPs F hFs
    · intro h s hs
      rw [show s = projZeroLocus (T ⟨s, hs⟩) from hTS ⟨s, hs⟩]
      intro F hF
      exact h F ⟨⟨s, hs⟩, hF⟩

theorem isHomogeneous_mul_totalDegree {n : ℕ} {F G : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous F.totalDegree) (hG : G.IsHomogeneous G.totalDegree) :
    (F * G).IsHomogeneous (F * G).totalDegree := by
  rcases eq_or_ne F 0 with rfl | hF0
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) (R := k) (0 : k))
  rcases eq_or_ne G 0 with rfl | hG0
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) (R := k) (0 : k))
  have hmul : (F * G).IsHomogeneous (F.totalDegree + G.totalDegree) := hF.mul hG
  have htd : (F * G).totalDegree = F.totalDegree + G.totalDegree := hmul.totalDegree (mul_ne_zero hF0 hG0)
  rw [htd]
  exact hmul

theorem isProjClosed_union {n : ℕ} {S U : Set (ProjPoint k n)}
    (hS : IsProjClosed S) (hU : IsProjClosed U) : IsProjClosed (S ∪ U) := by
  classical
  obtain ⟨T, hT, rfl⟩ := hS
  obtain ⟨T', hT', rfl⟩ := hU
  refine ⟨{F * G | (F : MvPolynomial (Fin (n + 1)) k) (G : MvPolynomial (Fin (n + 1)) k)
      (_ : F ∈ T) (_ : G ∈ T')}, ?_, ?_⟩
  · rintro F ⟨F₀, G₀, hF₀, hG₀, rfl⟩
    exact isHomogeneous_mul_totalDegree (hT F₀ hF₀) (hT' G₀ hG₀)
  · ext P
    constructor
    · rintro (h | h)
      · rintro F ⟨F₀, G₀, hF₀, hG₀, rfl⟩
        have hz : MvPolynomial.aeval (R := k) P.1 F₀ = 0 := h F₀ hF₀
        simp only [vanishes, map_mul, hz, zero_mul]
      · rintro F ⟨F₀, G₀, hF₀, hG₀, rfl⟩
        have hz : MvPolynomial.aeval (R := k) P.1 G₀ = 0 := h G₀ hG₀
        simp only [vanishes, map_mul, hz, mul_zero]
    · intro h
      by_contra hcon
      rw [Set.mem_union] at hcon
      have h1 : ¬ P ∈ projZeroLocus T := fun hh => hcon (Or.inl hh)
      have h2 : ¬ P ∈ projZeroLocus T' := fun hh => hcon (Or.inr hh)
      simp only [mem_projZeroLocus] at h1 h2
      push Not at h1 h2
      obtain ⟨F₀, hF₀, hzF⟩ := h1
      obtain ⟨G₀, hG₀, hzG⟩ := h2
      have hmem : F₀ * G₀ ∈ {F * G | (F : MvPolynomial (Fin (n + 1)) k)
          (G : MvPolynomial (Fin (n + 1)) k) (_ : F ∈ T) (_ : G ∈ T')} :=
        ⟨F₀, G₀, hF₀, hG₀, rfl⟩
      have hz := h (F₀ * G₀) hmem
      simp only [vanishes, map_mul] at hz
      exact (mul_ne_zero hzF hzG) hz

/-- The Zariski topology on `Pⁿ`. -/
@[instance_reducible]
def projTopology (k : Type*) [Field k] (n : ℕ) : TopologicalSpace (ProjPoint k n) where
  IsOpen S := IsProjClosed Sᶜ
  isOpen_univ := by simpa using isProjClosed_empty (k := k) (n := n)
  isOpen_inter := by
    intro S U hS hU
    rw [Set.compl_inter]
    exact isProjClosed_union hS hU
  isOpen_sUnion := by
    intro S hS
    rw [Set.compl_sUnion]
    refine isProjClosed_sInter ?_
    rintro s ⟨t, ht, rfl⟩
    exact hS t ht

attribute [instance 100] projTopology

theorem isClosed_iff_projClosed {n : ℕ} {S : Set (ProjPoint k n)} :
    IsClosed S ↔ IsProjClosed S := by
  constructor
  · intro h
    have h' : (projTopology k n).IsOpen Sᶜ := h.isOpen_compl
    have h'' : IsProjClosed (Sᶜ)ᶜ := h'
    rwa [compl_compl] at h''
  · intro h
    refine ⟨? _⟩
    show IsProjClosed (Sᶜ)ᶜ
    rwa [compl_compl]

theorem isClosed_projZeroLocus {n : ℕ} {T : Set (MvPolynomial (Fin (n + 1)) k)}
    (hT : ∀ F ∈ T, F.IsHomogeneous F.totalDegree) : IsClosed (projZeroLocus T) :=
  isClosed_iff_projClosed.mpr ⟨T, hT, rfl⟩

theorem isClosed_vanishes {n : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous F.totalDegree) : IsClosed {P : ProjPoint k n | vanishes F P} :=
  isClosed_iff_projClosed.mpr ⟨{F}, by simpa using hF, by ext P; simp [projZeroLocus]⟩

/-- The projective closure of a subset `Y ⊆ Aⁿ`. -/
def projectiveClosure {n : ℕ} (Y : Set (Fin n → k)) : Set (ProjPoint k n) :=
  closure (iota '' Y)

theorem subset_projectiveClosure {n : ℕ} (Y : Set (Fin n → k)) :
    iota '' Y ⊆ projectiveClosure Y := subset_closure

theorem projectiveClosure_minimal {n : ℕ} {Y : Set (Fin n → k)} {S : Set (ProjPoint k n)}
    (hS : IsClosed S) (h : iota '' Y ⊆ S) : projectiveClosure Y ⊆ S :=
  closure_minimal h hS

/-- `I(Y)` for a projective algebraic set: the ideal generated by the homogeneous polynomials
vanishing on `Y` (Hartshorne's definition). -/
def projVanishingIdeal {n : ℕ} (Z : Set (ProjPoint k n)) : Ideal (MvPolynomial (Fin (n + 1)) k) :=
  Ideal.span {F | F.IsHomogeneous F.totalDegree ∧ ∀ P ∈ Z, vanishes F P}

theorem subset_projVanishingIdeal {n : ℕ} {Z : Set (ProjPoint k n)}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous F.totalDegree)
    (h : ∀ P ∈ Z, vanishes F P) : F ∈ projVanishingIdeal Z :=
  Ideal.subset_span ⟨hF, h⟩

theorem projVanishingIdeal_le_ker {n : ℕ} {Z : Set (ProjPoint k n)} {P : ProjPoint k n}
    (hP : P ∈ Z) : projVanishingIdeal Z ≤ RingHom.ker (MvPolynomial.aeval (R := k) P.1) := by
  rw [projVanishingIdeal, Ideal.span_le]
  rintro F ⟨-, hF⟩
  exact hF P hP

/-! ## 2. Dehomogenization `α` and homogenization `β` -/

/-- Dehomogenization `α`: put `x₀ = 1`, i.e. `α(F) = F(1, x₁, …, xₙ)`. -/
def dehom (k : Type*) [Field k] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (Fin.cons 1 (fun i => MvPolynomial.X i))

@[simp]
theorem dehom_X_zero {n : ℕ} : dehom k n (MvPolynomial.X 0) = 1 := by
  simp [dehom]

@[simp]
theorem dehom_X_succ {n : ℕ} {i : Fin n} : dehom k n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [dehom]

theorem aeval_dehom {n : ℕ} (a : Fin n → k) (F : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial.aeval (R := k) a (dehom k n F) = MvPolynomial.aeval (R := k) (Fin.cons 1 a) F := by
  have h : (MvPolynomial.aeval (R := k) a).comp (dehom k n) =
      MvPolynomial.aeval (R := k) (Fin.cons 1 a) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  exact AlgHom.congr_fun h F

/-- Homogenization `β_N`: homogenize `f` to total degree `N`,
`β_N(f) = ∑ᵢ x₀^(N-i) · (homogeneous component of f of degree i)`. -/
noncomputable def homogenize (k : Type*) [Field k] (n : ℕ) (N : ℕ)
    (f : MvPolynomial (Fin n) k) : MvPolynomial (Fin (n + 1)) k :=
  (MvPolynomial.finSuccEquiv k n).symm
    (∑ i ∈ Finset.range (N + 1),
      Polynomial.C (MvPolynomial.homogeneousComponent (N - i) f) * Polynomial.X ^ i)

theorem homogenize_zero {n N : ℕ} : homogenize k n N 0 = 0 := by
  simp [homogenize]

theorem homogenize_add {n N : ℕ} (f g : MvPolynomial (Fin n) k) :
    homogenize k n N (f + g) = homogenize k n N f + homogenize k n N g := by
  simp only [homogenize, map_add, Finset.sum_add_distrib, add_mul]

theorem homogenize_sum {n N : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) k) :
    homogenize k n N (∑ i ∈ s, f i) = ∑ i ∈ s, homogenize k n N (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [homogenize_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, homogenize_add, ih]

theorem finSuccEquiv_C {n : ℕ} (a : k) :
    MvPolynomial.finSuccEquiv k n (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  have h2 : (MvPolynomial.finSuccEquiv k n).symm (Polynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
    simpa using RingHom.congr_fun (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := k) n) a
  rw [← h2, AlgEquiv.apply_symm_apply]

theorem finSuccEquiv_rename_succ {n : ℕ} (g : MvPolynomial (Fin n) k) :
    MvPolynomial.finSuccEquiv k n (MvPolynomial.rename Fin.succ g) = Polynomial.C g := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using finSuccEquiv_C (k := k) (n := n) a
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, hp, MvPolynomial.finSuccEquiv_X_succ,
      ← Polynomial.C_mul]

theorem finSuccEquiv_symm_C_mul_X_pow {n : ℕ} (g : MvPolynomial (Fin n) k) (i : ℕ) :
    (MvPolynomial.finSuccEquiv k n).symm (Polynomial.C g * Polynomial.X ^ i) =
      MvPolynomial.rename Fin.succ g * MvPolynomial.X 0 ^ i := by
  apply (MvPolynomial.finSuccEquiv k n).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, map_pow, finSuccEquiv_rename_succ,
    MvPolynomial.finSuccEquiv_X_zero]

theorem dehom_rename_succ {n : ℕ} (g : MvPolynomial (Fin n) k) :
    dehom k n (MvPolynomial.rename Fin.succ g) = g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [dehom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, hp, dehom_X_succ]

theorem dehom_X_zero_pow {n : ℕ} (i : ℕ) :
    dehom k n ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k) ^ i) = 1 := by
  rw [map_pow, dehom_X_zero, one_pow]

theorem dehom_finSuccEquiv_symm_C_mul_X_pow {n : ℕ} (g : MvPolynomial (Fin n) k) (i : ℕ) :
    dehom k n ((MvPolynomial.finSuccEquiv k n).symm (Polynomial.C g * Polynomial.X ^ i)) = g := by
  rw [finSuccEquiv_symm_C_mul_X_pow, map_mul, dehom_rename_succ, dehom_X_zero_pow, mul_one]

theorem dehom_homogenize {n N : ℕ} (f : MvPolynomial (Fin n) k) :
    dehom k n (homogenize k n N f) =
      ∑ i ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent (N - i) f := by
  simp only [homogenize, map_sum]
  exact Finset.sum_congr rfl fun i _ => dehom_finSuccEquiv_symm_C_mul_X_pow _ _

theorem sum_homogeneousComponent_range {n : ℕ} {f : MvPolynomial (Fin n) k} {N : ℕ}
    (hN : f.totalDegree ≤ N) :
    (∑ i ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent (N - i) f) = f := by
  have h1 : (∑ i ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent (N - i) f)
      = ∑ i ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent i f := by
    rw [← Finset.sum_range_reflect (fun i => MvPolynomial.homogeneousComponent i f) (N + 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_sub_cancel]
  have h2 : (∑ i ∈ Finset.range (f.totalDegree + 1), MvPolynomial.homogeneousComponent i f)
      = ∑ i ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent i f := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hN))
    · intro i hi1 hi2
      rw [Finset.mem_range, not_lt] at hi2
      exact MvPolynomial.homogeneousComponent_eq_zero (n := i) (φ := f) (by omega)
  rw [h1, ← h2, MvPolynomial.sum_homogeneousComponent]

theorem dehom_homogenize_eq {n N : ℕ} {f : MvPolynomial (Fin n) k} (hN : f.totalDegree ≤ N) :
    dehom k n (homogenize k n N f) = f := by
  rw [dehom_homogenize, sum_homogeneousComponent_range hN]

theorem homogenize_isHomogeneous {n N : ℕ} (f : MvPolynomial (Fin n) k) :
    (homogenize k n N f).IsHomogeneous N := by
  rw [homogenize]
  rw [map_sum]
  refine IsHomogeneous.sum _ _ _ ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rw [finSuccEquiv_symm_C_mul_X_pow]
  have h1 : (MvPolynomial.homogeneousComponent (N - i) f).IsHomogeneous (N - i) :=
    MvPolynomial.homogeneousComponent_isHomogeneous (N - i) f
  have h2 : (MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent (N - i) f)).IsHomogeneous
      (N - i) := h1.rename_isHomogeneous
  have h3 : ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k) ^ i).IsHomogeneous i := by
    have hx : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X (R := k) (0 : Fin (n + 1))
    simpa using hx.pow i
  have h4 := h2.mul h3
  rwa [Nat.sub_add_cancel (by omega)] at h4

theorem homogenize_homogeneousComponent {n N i : ℕ} {f : MvPolynomial (Fin n) k}
    (h : f.IsHomogeneous i) (hi : i ≤ N) :
    homogenize k n N f = (MvPolynomial.finSuccEquiv k n).symm
      (Polynomial.C f * Polynomial.X ^ (N - i)) := by
  rw [homogenize, Finset.sum_eq_single (N - i)]
  · rw [Nat.sub_sub_self hi, MvPolynomial.homogeneousComponent_eq_self h]
  · intro j hj hji
    rw [Finset.mem_range] at hj
    rw [MvPolynomial.homogeneousComponent_of_mem (n := i) (m := N - j)
      (MvPolynomial.mem_homogeneousSubmodule i f |>.mpr h)]
    rw [if_neg (show N - j ≠ i by omega), Polynomial.C_0, zero_mul]
  · intro hi'
    exact absurd (Finset.mem_range.mpr (by omega)) hi'

theorem homogenize_dehom {n D : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous D) : homogenize k n D (dehom k n F) = F := by
  classical
  rcases eq_or_ne F 0 with rfl | hF0
  · simp [homogenize_zero]
  set Φ : Polynomial (MvPolynomial (Fin n) k) := MvPolynomial.finSuccEquiv k n F with hΦdef
  have hΦsymm : (MvPolynomial.finSuccEquiv k n).symm Φ = F := by
    rw [hΦdef]
    exact (MvPolynomial.finSuccEquiv k n).symm_apply_apply F
  have hnd : Φ.natDegree ≤ D := by
    rw [hΦdef, MvPolynomial.natDegree_finSuccEquiv]
    exact le_trans (MvPolynomial.degreeOf_le_totalDegree F 0) (by rw [hF.totalDegree hF0])
  have hΦsum : Φ = ∑ i ∈ Finset.range (D + 1), Polynomial.C (Φ.coeff i) * Polynomial.X ^ i :=
    Polynomial.as_sum_range_C_mul_X_pow' _ (by omega)
  have hFsum : F = ∑ i ∈ Finset.range (D + 1), (MvPolynomial.finSuccEquiv k n).symm
      (Polynomial.C (Φ.coeff i) * Polynomial.X ^ i) := by
    rw [← hΦsymm]
    conv_lhs => rw [hΦsum]
    rw [map_sum]
  have hdehom : dehom k n F = ∑ i ∈ Finset.range (D + 1), Φ.coeff i := by
    rw [hFsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => dehom_finSuccEquiv_symm_C_mul_X_pow _ _
  have hcoh : ∀ i ∈ Finset.range (D + 1), (Φ.coeff i).IsHomogeneous (D - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h := hF.finSuccEquiv_coeff_isHomogeneous (φ := F) i (D - i) (by omega)
    rwa [← hΦdef] at h
  rw [hdehom, homogenize_sum]
  conv_rhs => rw [hFsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [homogenize_homogeneousComponent (hcoh i (Finset.mem_range.mpr hi)) (by omega),
    Nat.sub_sub_self (by omega)]

/-! ## 3. Homogenizing the vanishing ideal: part (a) of the exercise -/

/-- `β f`: homogenization of `f` to its total degree (the map `β` of the proof of I.2.2). -/
def homogenizeDeg (k : Type*) [Field k] (n : ℕ) (f : MvPolynomial (Fin n) k) :
    MvPolynomial (Fin (n + 1)) k :=
  homogenize k n f.totalDegree f

theorem homogenizeDeg_isHomogeneous {n : ℕ} (f : MvPolynomial (Fin n) k) :
    (homogenizeDeg k n f).IsHomogeneous (homogenizeDeg k n f).totalDegree := by
  rw [homogenizeDeg]
  rcases eq_or_ne (homogenize k n f.totalDegree f) 0 with h0 | h0
  · rw [h0]
    simpa using (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) (R := k) (0 : k))
  · rw [(homogenize_isHomogeneous f).totalDegree h0]
    exact homogenize_isHomogeneous f

theorem aeval_homogenizeDeg {n : ℕ} (a : Fin n → k) (f : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval (R := k) (Fin.cons 1 a) (homogenizeDeg k n f) =
      MvPolynomial.aeval (R := k) a f := by
  rw [homogenizeDeg, ← aeval_dehom, dehom_homogenize_eq le_rfl]

theorem totalDegree_finset_sum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) k) {N : ℕ} (h : ∀ i ∈ s, (f i).totalDegree ≤ N) :
    (∑ i ∈ s, f i).totalDegree ≤ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (h a (Finset.mem_insert_self a s)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem dehom_eq_sum_coeff {n D : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous D) (hF0 : F ≠ 0) :
    dehom k n F = ∑ i ∈ Finset.range (D + 1), (MvPolynomial.finSuccEquiv k n F).coeff i := by
  classical
  set Φ : Polynomial (MvPolynomial (Fin n) k) := MvPolynomial.finSuccEquiv k n F with hΦdef
  have hΦsymm : (MvPolynomial.finSuccEquiv k n).symm Φ = F := by
    rw [hΦdef]
    exact (MvPolynomial.finSuccEquiv k n).symm_apply_apply F
  have hnd : Φ.natDegree ≤ D := by
    rw [hΦdef, MvPolynomial.natDegree_finSuccEquiv]
    exact le_trans (MvPolynomial.degreeOf_le_totalDegree F 0) (by rw [hF.totalDegree hF0])
  have hΦsum : Φ = ∑ i ∈ Finset.range (D + 1), Polynomial.C (Φ.coeff i) * Polynomial.X ^ i :=
    Polynomial.as_sum_range_C_mul_X_pow' _ (by omega)
  have hFsum : F = ∑ i ∈ Finset.range (D + 1), (MvPolynomial.finSuccEquiv k n).symm
      (Polynomial.C (Φ.coeff i) * Polynomial.X ^ i) := by
    rw [← hΦsymm]
    conv_lhs => rw [hΦsum]
    rw [map_sum]
  rw [hFsum, map_sum]
  exact Finset.sum_congr rfl fun i _ => dehom_finSuccEquiv_symm_C_mul_X_pow _ _

theorem totalDegree_dehom_le {n D : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous D) : (dehom k n F).totalDegree ≤ D := by
  rcases eq_or_ne F 0 with rfl | hF0
  · simp [dehom]
  rw [dehom_eq_sum_coeff hF hF0]
  refine totalDegree_finset_sum_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h := hF.finSuccEquiv_coeff_isHomogeneous (φ := F) i (D - i) (by omega)
  exact le_trans h.totalDegree_le (by omega)

theorem homogenize_shift {n N : ℕ} {f : MvPolynomial (Fin n) k} (hN : f.totalDegree ≤ N) :
    homogenize k n N f =
      MvPolynomial.X 0 ^ (N - f.totalDegree) * homogenize k n f.totalDegree f := by
  have hhom : (MvPolynomial.X 0 ^ (N - f.totalDegree) * homogenize k n f.totalDegree f)
      |>.IsHomogeneous N := by
    have h1 : (homogenize k n f.totalDegree f).IsHomogeneous f.totalDegree :=
      homogenize_isHomogeneous f
    have h2 : ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k) ^
        (N - f.totalDegree)).IsHomogeneous (N - f.totalDegree) := by
      have hx : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X (R := k) 0
      simpa using hx.pow (N - f.totalDegree)
    have h3 := h2.mul h1
    rwa [Nat.sub_add_cancel hN] at h3
  have hdeh : dehom k n (MvPolynomial.X 0 ^ (N - f.totalDegree) *
      homogenize k n f.totalDegree f) = f := by
    rw [map_mul, map_pow, dehom_X_zero, one_pow, one_mul, dehom_homogenize_eq le_rfl]
  rw [← homogenize_dehom hhom, hdeh]

/-- **Hartshorne I.2.9 (a)**: for every subset `Y ⊆ Aⁿ`, the homogeneous vanishing ideal of the
projective closure `Y̅ ⊆ Pⁿ` is generated by the homogenizations `β f`, `f ∈ I(Y)`. -/
theorem projVanishingIdeal_projectiveClosure (n : ℕ) (Y : Set (Fin n → k)) :
    projVanishingIdeal (projectiveClosure Y) =
      Ideal.span (homogenizeDeg k n '' MvPolynomial.vanishingIdeal k Y) := by
  refine le_antisymm ?_ ?_
  · rw [projVanishingIdeal, Ideal.span_le]
    rintro G ⟨hG, hvan⟩
    have hfmem : dehom k n G ∈ MvPolynomial.vanishingIdeal k Y := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro a ha
      rw [aeval_dehom]
      exact hvan (iota a) (subset_projectiveClosure Y ⟨a, ha, rfl⟩)
    have hG_eq : G = homogenizeDeg k n (dehom k n G) *
        MvPolynomial.X 0 ^ (G.totalDegree - (dehom k n G).totalDegree) := by
      rw [homogenizeDeg, mul_comm,
        ← homogenize_shift (totalDegree_dehom_le hG), homogenize_dehom hG]
    rw [hG_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨dehom k n G, hfmem, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    refine subset_projVanishingIdeal (homogenizeDeg_isHomogeneous f) ?_
    have hcl : IsClosed {P : ProjPoint k n | vanishes (homogenizeDeg k n f) P} :=
      isClosed_vanishes (homogenizeDeg_isHomogeneous f)
    have hsub : iota '' Y ⊆ {P : ProjPoint k n | vanishes (homogenizeDeg k n f) P} := by
      rintro _ ⟨a, ha, rfl⟩
      show MvPolynomial.aeval (R := k) (Fin.cons 1 a) (homogenizeDeg k n f) = 0
      rw [aeval_homogenizeDeg]
      exact MvPolynomial.mem_vanishingIdeal_iff.mp hf a ha
    intro P hP
    exact projectiveClosure_minimal hcl hsub hP


/-! ## 4. The twisted cubic: generators of `I(Y)` -/

section TwistedCubic

/-- The twisted cubic `Y = {(t, t², t³) | t ∈ k} ⊆ A³`. -/
def twistedCubic : Set (Fin 3 → k) :=
  {P | P 1 = P 0 ^ 2 ∧ P 2 = P 0 ^ 3}

/-- The point `(t, t², t³)`. -/
def cubicPoint (t : k) : Fin 3 → k := ![t, t ^ 2, t ^ 3]

theorem cubicPoint_mem (t : k) : cubicPoint t ∈ twistedCubic (k := k) := by
  simp [cubicPoint, twistedCubic]

theorem eq_cubicPoint_of_mem {P : Fin 3 → k} (hP : P ∈ twistedCubic (k := k)) :
    P = cubicPoint (P 0) := by
  funext j
  fin_cases j <;> simp [cubicPoint, twistedCubic] at hP ⊢
  · exact hP.1
  · exact hP.2

/-- The ideal `(y - x², z - x³) ⊆ k[x,y,z]`. -/
def twistedCubicIdeal : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2,
    MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3} : Set (MvPolynomial (Fin 3) k))

/-- The substitution `k[x,y,z] → k[t]`, `x ↦ t`, `y ↦ t²`, `z ↦ t³`. -/
def cubicSubst : MvPolynomial (Fin 3) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (![Polynomial.X, Polynomial.X ^ 2, Polynomial.X ^ 3] : Fin 3 → Polynomial k)

/-- The substitution `k[t] → k[x,y,z]`, `t ↦ x`. -/
def cubicEmbed : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k :=
  Polynomial.aeval (MvPolynomial.X 0)

@[simp]
theorem cubicSubst_X_zero : cubicSubst (k := k) (MvPolynomial.X 0) = Polynomial.X := by
  simp [cubicSubst]

@[simp]
theorem cubicSubst_X_one : cubicSubst (k := k) (MvPolynomial.X 1) = Polynomial.X ^ 2 := by
  simp [cubicSubst]

@[simp]
theorem cubicSubst_X_two : cubicSubst (k := k) (MvPolynomial.X 2) = Polynomial.X ^ 3 := by
  simp [cubicSubst]

@[simp]
theorem cubicEmbed_X : cubicEmbed (k := k) Polynomial.X = MvPolynomial.X 0 := by
  simp [cubicEmbed]

/-- Every polynomial is congruent to a polynomial in `x` modulo `(y - x², z - x³)`. -/
theorem sub_embed_subst_mem (f : MvPolynomial (Fin 3) k) :
    f - cubicEmbed (k := k) (cubicSubst (k := k) f) ∈ twistedCubicIdeal (k := k) := by
  let S : Subalgebra k (MvPolynomial (Fin 3) k) :=
    { carrier := {f | f - cubicEmbed (k := k) (cubicSubst (k := k) f) ∈ twistedCubicIdeal (k := k)}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        change f + g - cubicEmbed (k := k) (cubicSubst (k := k) (f + g)) ∈ twistedCubicIdeal (k := k)
        have hf' : f - cubicEmbed (k := k) (cubicSubst (k := k) f) ∈ twistedCubicIdeal (k := k) := hf
        have hg' : g - cubicEmbed (k := k) (cubicSubst (k := k) g) ∈ twistedCubicIdeal (k := k) := hg
        have key : f + g - cubicEmbed (k := k) (cubicSubst (k := k) (f + g)) =
            (f - cubicEmbed (k := k) (cubicSubst (k := k) f)) + (g - cubicEmbed (k := k) (cubicSubst (k := k) g)) := by
          rw [map_add, map_add]; ring
        rw [key]
        exact add_mem hf' hg'
      mul_mem' := by
        intro f g hf hg
        change f * g - cubicEmbed (k := k) (cubicSubst (k := k) (f * g)) ∈ twistedCubicIdeal (k := k)
        have hf' : f - cubicEmbed (k := k) (cubicSubst (k := k) f) ∈ twistedCubicIdeal (k := k) := hf
        have hg' : g - cubicEmbed (k := k) (cubicSubst (k := k) g) ∈ twistedCubicIdeal (k := k) := hg
        have key : f * g - cubicEmbed (k := k) (cubicSubst (k := k) (f * g)) =
            (f - cubicEmbed (k := k) (cubicSubst (k := k) f)) * g +
              cubicEmbed (k := k) (cubicSubst (k := k) f) * (g - cubicEmbed (k := k) (cubicSubst (k := k) g)) := by
          rw [map_mul, map_mul]; ring
        rw [key]
        exact add_mem (Ideal.mul_mem_right g _ hf')
          (Ideal.mul_mem_left _ (cubicEmbed (k := k) (cubicSubst (k := k) f)) hg')
      algebraMap_mem' := by
        intro r
        change algebraMap k (MvPolynomial (Fin 3) k) r -
          cubicEmbed (k := k) (cubicSubst (k := k) (algebraMap k (MvPolynomial (Fin 3) k) r)) ∈ twistedCubicIdeal (k := k)
        have h1 : cubicSubst (k := k) (algebraMap k (MvPolynomial (Fin 3) k) r) =
            algebraMap k (Polynomial k) r := (cubicSubst (k := k)).commutes r
        have h2 : cubicEmbed (k := k) (algebraMap k (Polynomial k) r) =
            algebraMap k (MvPolynomial (Fin 3) k) r := (cubicEmbed (k := k)).commutes r
        rw [h1, h2, sub_self]
        exact Submodule.zero_mem _ }
  have htop : (⊤ : Subalgebra k (MvPolynomial (Fin 3) k)) ≤ S := by
    rw [← MvPolynomial.adjoin_range_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change MvPolynomial.X 0 - cubicEmbed (k := k) (cubicSubst (k := k) (MvPolynomial.X 0)) ∈
        twistedCubicIdeal (k := k)
      simp [cubicSubst, cubicEmbed]
    · change MvPolynomial.X 1 - cubicEmbed (k := k) (cubicSubst (k := k) (MvPolynomial.X 1)) ∈
        twistedCubicIdeal (k := k)
      have hsub : cubicEmbed (k := k) (cubicSubst (k := k) (MvPolynomial.X 1)) = MvPolynomial.X 0 ^ 2 := by
        simp [cubicSubst, cubicEmbed]
      rw [hsub]
      exact Ideal.subset_span (by simp)
    · change MvPolynomial.X 2 - cubicEmbed (k := k) (cubicSubst (k := k) (MvPolynomial.X 2)) ∈
        twistedCubicIdeal (k := k)
      have hsub : cubicEmbed (k := k) (cubicSubst (k := k) (MvPolynomial.X 2)) = MvPolynomial.X 0 ^ 3 := by
        simp [cubicSubst, cubicEmbed]
      rw [hsub]
      exact Ideal.subset_span (by simp)
  exact htop (by simp)

theorem cubicSubst_eq_zero_iff (f : MvPolynomial (Fin 3) k) :
    cubicSubst (k := k) f = 0 ↔ f ∈ twistedCubicIdeal (k := k) := by
  constructor
  · intro h
    have h' := sub_embed_subst_mem (k := k) f
    rwa [h, map_zero, sub_zero] at h'
  · intro h
    have hgen : ({MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2,
        MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3} : Set (MvPolynomial (Fin 3) k)) ⊆
        RingHom.ker (cubicSubst (k := k) : MvPolynomial (Fin 3) k →+* Polynomial k) := by
      rintro q (rfl | rfl)
      · simp
      · simp
    have hle : twistedCubicIdeal (k := k) ≤
        RingHom.ker (cubicSubst (k := k) : MvPolynomial (Fin 3) k →+* Polynomial k) :=
      Ideal.span_le.2 hgen
    have := hle h
    simpa using this

theorem ker_cubicSubst :
    RingHom.ker (cubicSubst (k := k) : MvPolynomial (Fin 3) k →+* Polynomial k) = twistedCubicIdeal (k := k) := by
  ext f
  rw [RingHom.mem_ker]
  exact cubicSubst_eq_zero_iff (k := k) f

theorem aeval_cubicPoint (t : k) (f : MvPolynomial (Fin 3) k) :
    MvPolynomial.aeval (R := k) (cubicPoint t) f = (cubicSubst (k := k) f).eval t := by
  have h : (MvPolynomial.aeval (R := k) (cubicPoint t)) = (Polynomial.aeval t).comp (cubicSubst (k := k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cubicPoint, cubicSubst]
  rw [h]
  rfl

theorem vanishingIdeal_twistedCubic [IsAlgClosed k] :
    MvPolynomial.vanishingIdeal k (twistedCubic (k := k)) = twistedCubicIdeal (k := k) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf
    rw [← cubicSubst_eq_zero_iff]
    refine Polynomial.funext fun t => ?_
    have h1 := aeval_cubicPoint (k := k) t f
    rw [hf (cubicPoint t) (cubicPoint_mem t)] at h1
    simpa using h1.symm
  · intro f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro P hP
    have hsub : cubicSubst (k := k) f = 0 := (cubicSubst_eq_zero_iff (k := k) f).2 hf
    rw [eq_cubicPoint_of_mem hP, aeval_cubicPoint, hsub]
    simp

end TwistedCubic


/-! ## 5. The projective twisted cubic `Y̅ ⊆ P³` -/

section ProjectiveTwistedCubic

/-- The twisted cubic curve `Y̅ ⊆ P³`, i.e. the projective closure of the affine twisted cubic. -/
def projTwistedCubic : Set (ProjPoint k 3) := projectiveClosure (twistedCubic (k := k))

/-- The homogeneous ideal `(x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`. -/
def projTwistedIdeal : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2,
    MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2,
    MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2} : Set (MvPolynomial (Fin 4) k))

/-- The parametrization `[s : t] ↦ [s³ : s²t : st² : t³]`, as a map of polynomial rings. -/
def cubicTheta : MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (fun i : Fin 4 =>
    if i = 0 then MvPolynomial.X 0 ^ 3
    else if i = 1 then MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1
    else if i = 2 then MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
    else MvPolynomial.X 1 ^ 3)

/-- `x₀ = 1, x₁ = t, x₂ = t², x₃ = t³`. -/
theorem cons_one_cubicPoint (t : k) :
    (Fin.cons 1 (cubicPoint t) : Fin 4 → k) = ![1, t, t ^ 2, t ^ 3] := by
  funext j
  fin_cases j <;> simp [cubicPoint]

theorem cubicTheta_monomial (m : Fin 4 →₀ ℕ) (c : k) :
    cubicTheta (MvPolynomial.monomial m c) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ (3 * m 0 + 2 * m 1 + m 2) *
        MvPolynomial.X 1 ^ (m 1 + 2 * m 2 + 3 * m 3) := by
  rw [cubicTheta, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod]
  have h4 : m.support ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.prod_subset h4]
  · rw [Fin.prod_univ_four]
    show MvPolynomial.C c * ((MvPolynomial.X 0 ^ 3) ^ m 0 *
      (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) ^ m 1 *
      (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2) ^ m 2 * (MvPolynomial.X 1 ^ 3) ^ m 3) = _
    simp only [mul_pow]
    ring
  · intro i _ hi
    simp only [Finsupp.mem_support_iff, not_not] at hi
    rw [hi]
    simp

theorem cubicTheta_isHomogeneous {G : MvPolynomial (Fin 4) k} {D : ℕ}
    (hG : G.IsHomogeneous D) : (cubicTheta G).IsHomogeneous (3 * D) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum G]
  rw [map_sum]
  refine IsHomogeneous.sum _ _ _ ?_
  intro m hm
  have hmdeg : m.degree = D := by
    have h := hG (d := m) (MvPolynomial.mem_support_iff.mp hm)
    have h2 : (Finsupp.weight (fun _ : Fin 4 => (1 : ℕ))) m = D := h
    simpa only [Finsupp.degree_eq_weight_one] using h2
  rw [cubicTheta_monomial]
  have hdeg : (3 * m 0 + 2 * m 1 + m 2) + (m 1 + 2 * m 2 + 3 * m 3) = 3 * D := by
    have hsum : m 0 + m 1 + m 2 + m 3 = D := by
      rw [← hmdeg, Finsupp.degree_eq_sum, Fin.sum_univ_four]
    omega
  have h1 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (R := k) 0
  have h2 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (R := k) 1
  have h := (h1.pow (3 * m 0 + 2 * m 1 + m 2)).mul (h2.pow (m 1 + 2 * m 2 + 3 * m 3))
  have hc : (MvPolynomial.C (G.coeff m) : MvPolynomial (Fin 2) k).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (R := k) (σ := Fin 2) (r := G.coeff m)
  have hfinal := hc.mul h
  simp only [zero_add, one_mul] at hfinal
  rw [mul_assoc, ← hdeg]
  exact hfinal

theorem rename_swap_rename_swap (P : MvPolynomial (Fin 2) k) :
    MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = P := by
  have h1 : (⇑(Equiv.swap (0 : Fin 2) 1)) ∘ (⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.rename_rename, h1]
  exact AlgHom.congr_fun MvPolynomial.rename_id P

/-! ## 6. Closing the gap: `I(Y̅) = J` and the non-generation statement -/

section ClosingTheGap

variable {k : Type*} [Field k]

/-- The homogeneous component of a product with a homogeneous right factor. -/
theorem homogeneousComponent_mul_right {m : ℕ} {p h : MvPolynomial (Fin m) k} {e : ℕ}
    (hh : h.IsHomogeneous e) (N : ℕ) :
    MvPolynomial.homogeneousComponent N (p * h) =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        if N = i + e then MvPolynomial.homogeneousComponent i p * h else 0 := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
  rw [Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    have hhom : (MvPolynomial.homogeneousComponent i p * h).IsHomogeneous (i + e) :=
      (MvPolynomial.homogeneousComponent_isHomogeneous i p).mul hh
    rw [MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mpr hhom)]

theorem homogeneousComponent_mul_right_of_le {m : ℕ} {p h : MvPolynomial (Fin m) k} {e N : ℕ}
    (hh : h.IsHomogeneous e) (hN : e ≤ N) :
    MvPolynomial.homogeneousComponent N (p * h) =
      MvPolynomial.homogeneousComponent (N - e) p * h := by
  rw [homogeneousComponent_mul_right hh N, Finset.sum_eq_single (N - e)]
  · rw [if_pos (by omega : N = N - e + e)]
  · intro i _ hi
    rw [if_neg (by omega : ¬ (N = i + e))]
  · intro hmem
    rw [Finset.mem_range] at hmem
    rw [if_pos (by omega : N = N - e + e),
      MvPolynomial.homogeneousComponent_eq_zero (n := N - e) (φ := p) (by omega)]
    simp

theorem homogeneousComponent_mul_right_of_lt {m : ℕ} {p h : MvPolynomial (Fin m) k} {e N : ℕ}
    (hh : h.IsHomogeneous e) (hN : N < e) :
    MvPolynomial.homogeneousComponent N (p * h) = 0 := by
  rw [homogeneousComponent_mul_right hh N]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg (by omega : ¬ (N = i + e))]

/-- Homogenization of a product with a homogeneous factor of the complementary degree. -/
theorem homogenize_mul_homogeneous {n : ℕ} {p h : MvPolynomial (Fin n) k} {e N : ℕ}
    (hh : h.IsHomogeneous e) (hp : p.IsHomogeneous (N - e)) (hN : e ≤ N) :
    homogenize k n N (p * h) = homogenize k n (N - e) p * homogenize k n e h := by
  have hp' : p.totalDegree ≤ N - e := hp.totalDegree_le
  have hh' : h.totalDegree ≤ e := hh.totalDegree_le
  have hhom : (homogenize k n (N - e) p * homogenize k n e h).IsHomogeneous N := by
    have h1 : (homogenize k n (N - e) p).IsHomogeneous (N - e) := homogenize_isHomogeneous p
    have h2 : (homogenize k n e h).IsHomogeneous e := homogenize_isHomogeneous h
    have h3 := h1.mul h2
    rwa [Nat.sub_add_cancel hN] at h3
  have hdeh : dehom k n (homogenize k n (N - e) p * homogenize k n e h) = p * h := by
    rw [map_mul, dehom_homogenize_eq hp', dehom_homogenize_eq hh']
  rw [← hdeh, homogenize_dehom hhom]

/-! ### The three homogeneous generators of `J` and the parametrization -/

theorem isHomogeneous_projGen_one :
    (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2 :
      MvPolynomial (Fin 4) k).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X (R := k) 0).mul
    (MvPolynomial.isHomogeneous_X (R := k) 2)).sub
    ((MvPolynomial.isHomogeneous_X (R := k) 1).pow 2)

theorem isHomogeneous_projGen_two :
    (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 :
      MvPolynomial (Fin 4) k).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X (R := k) 0).mul
    (MvPolynomial.isHomogeneous_X (R := k) 3)).sub
    ((MvPolynomial.isHomogeneous_X (R := k) 1).mul
      (MvPolynomial.isHomogeneous_X (R := k) 2))

theorem isHomogeneous_projGen_three :
    (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2 :
      MvPolynomial (Fin 4) k).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X (R := k) 1).mul
    (MvPolynomial.isHomogeneous_X (R := k) 3)).sub
    ((MvPolynomial.isHomogeneous_X (R := k) 2).pow 2)

theorem cons_one_X :
    (Fin.cons 1 (fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) k)) : Fin 4 →
      MvPolynomial (Fin 3) k) =
      ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2] := by
  funext j
  fin_cases j <;> rfl

theorem dehom_apply_four (G : MvPolynomial (Fin 4) k) :
    dehom k 3 G = MvPolynomial.aeval (R := k)
      (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2] :
        Fin 4 → MvPolynomial (Fin 3) k) G := by
  rw [dehom, cons_one_X]

theorem dehom_projGen_one :
    dehom k 3 (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) =
      MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 := by
  rw [dehom_apply_four]
  simp

theorem dehom_projGen_two :
    dehom k 3 (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) =
      MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1 := by
  rw [dehom_apply_four]
  simp

theorem dehom_projGen_three :
    dehom k 3 (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2) =
      MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2 := by
  rw [dehom_apply_four]
  simp

theorem homogenize_projGen_one :
    homogenize k 3 2 (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2) =
      MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2 := by
  rw [← dehom_projGen_one, homogenize_dehom isHomogeneous_projGen_one]

theorem homogenize_projGen_two :
    homogenize k 3 2 (MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) =
      MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 := by
  rw [← dehom_projGen_two, homogenize_dehom isHomogeneous_projGen_two]

theorem homogenize_projGen_three :
    homogenize k 3 2 (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) =
      MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2 := by
  rw [← dehom_projGen_three, homogenize_dehom isHomogeneous_projGen_three]

theorem dehom_uz :
    dehom k 3 (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3) =
      MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 := by
  rw [dehom_apply_four]
  simp

theorem homogenize_affGen_two :
    homogenize k 3 3 (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3) =
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3 := by
  have hhom : (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3 :
      MvPolynomial (Fin 4) k).IsHomogeneous 3 :=
    (((MvPolynomial.isHomogeneous_X (R := k) 0).pow 2).mul
      (MvPolynomial.isHomogeneous_X (R := k) 3)).sub
      ((MvPolynomial.isHomogeneous_X (R := k) 1).pow 3)
  rw [← dehom_uz, homogenize_dehom hhom]

/-- `x₀²x₃ - x₁³ = x₀·(x₀x₃ - x₁x₂) + x₁·(x₀x₂ - x₁²)` lies in `J`. -/
theorem X0_sq_mul_X3_sub_X1_cube_mem :
    MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3 ∈
      projTwistedIdeal (k := k) := by
  have hkey : (MvPolynomial.X 0 : MvPolynomial (Fin 4) k) *
        (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) +
      MvPolynomial.X 1 * (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) =
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3 := by ring
  rw [← hkey]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem projGen_one_mem : MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2 ∈
    projTwistedIdeal (k := k) :=
  Ideal.subset_span (by simp)

theorem projGen_two_mem : MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 ∈
    projTwistedIdeal (k := k) :=
  Ideal.subset_span (by simp)

theorem projGen_three_mem : MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2 ∈
    projTwistedIdeal (k := k) :=
  Ideal.subset_span (by simp)

end ClosingTheGap


theorem aeval_theta (G : MvPolynomial (Fin 4) k) (t : k) :
    MvPolynomial.aeval (R := k) (![1, t] : Fin 2 → k) (cubicTheta G) =
      MvPolynomial.aeval (R := k) (Fin.cons 1 (cubicPoint t)) G := by
  have hcomp : (MvPolynomial.aeval (R := k) (![1, t] : Fin 2 → k)).comp (cubicTheta (k := k)) =
      MvPolynomial.aeval (R := k) (Fin.cons 1 (cubicPoint t)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cubicTheta, cubicPoint]
  exact AlgHom.congr_fun hcomp G

theorem Polynomial_eval_aeval_binary (t : k) (P : MvPolynomial (Fin 2) k) :
    Polynomial.eval t (MvPolynomial.aeval (R := k) (![Polynomial.X, (1 : Polynomial k)] :
      Fin 2 → Polynomial k) P) = MvPolynomial.aeval (R := k) (![t, 1] : Fin 2 → k) P := by
  have h : ((Polynomial.aeval t : Polynomial k →ₐ[k] k)).comp
      (MvPolynomial.aeval (R := k) (![Polynomial.X, (1 : Polynomial k)] :
        Fin 2 → Polynomial k)) =
      MvPolynomial.aeval (R := k) (![t, 1] : Fin 2 → k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  have h2 := AlgHom.congr_fun h P
  simpa [Polynomial.aeval_def] using h2

/-- A homogeneous binary form of degree `e` that vanishes at every point `[1 : t]` is zero. -/
theorem binaryForm_eq_zero [Infinite k] {H : MvPolynomial (Fin 2) k} {e : ℕ}
    (hH : H.IsHomogeneous e) (h : ∀ t : k, MvPolynomial.aeval (R := k) (![1, t] : Fin 2 → k) H = 0) :
    H = 0 := by
  classical
  have hhom : (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) H).IsHomogeneous e :=
    hH.rename_isHomogeneous
  have heval : ∀ t : k,
      MvPolynomial.aeval (R := k) (![t, 1] : Fin 2 → k)
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) H) = 0 := by
    intro t
    have hcomp : (MvPolynomial.aeval (R := k) (![t, 1] : Fin 2 → k)) =
        (MvPolynomial.aeval (R := k) (![1, t] : Fin 2 → k)).comp
          (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp
    rw [hcomp, AlgHom.comp_apply, rename_swap_rename_swap]
    exact h t
  have hpoly : MvPolynomial.aeval (R := k) (![Polynomial.X, (1 : Polynomial k)] :
      Fin 2 → Polynomial k) (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) H) = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial_eval_aeval_binary, Polynomial.eval_zero]
    exact heval t
  have hzero := Polynomial.homogenize_eq_of_isHomogeneous (p := (0 : Polynomial k)) hhom hpoly
  rw [Polynomial.homogenize_zero] at hzero
  have hcongr := congrArg (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)) hzero.symm
  rwa [rename_swap_rename_swap, map_zero] at hcongr

/-- For `f ∈ I(Y)`, the homogenization `β f` is killed by the parametrization `θ`. -/
theorem cubicTheta_homogenize_eq_zero [IsAlgClosed k] {f : MvPolynomial (Fin 3) k}
    (hf : f ∈ twistedCubicIdeal (k := k)) :
    cubicTheta (homogenize k 3 f.totalDegree f) = 0 := by
  refine binaryForm_eq_zero (cubicTheta_isHomogeneous (homogenize_isHomogeneous f)) fun t => ?_
  rw [aeval_theta, ← aeval_dehom, dehom_homogenize_eq le_rfl]
  refine MvPolynomial.mem_vanishingIdeal_iff.mp ?_ (cubicPoint t) (cubicPoint_mem t)
  rwa [vanishingIdeal_twistedCubic]


section NormalForm

/-- The first generator `x₀x₂ - x₁²` of `J`. -/
abbrev projGen_one : MvPolynomial (Fin 4) k := MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2

/-- The second generator `x₀x₃ - x₁x₂` of `J`. -/
abbrev projGen_two : MvPolynomial (Fin 4) k := MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2

/-- The third generator `x₁x₃ - x₂²` of `J`. -/
abbrev projGen_three : MvPolynomial (Fin 4) k := MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2

/-- The embedding `k[u,z] → k[u,x,y,z]`, `u ↦ x₀`, `z ↦ x₃`. -/
def uzEmb : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 4) k :=
  MvPolynomial.aeval (![MvPolynomial.X 0, MvPolynomial.X 3] : Fin 2 → MvPolynomial (Fin 4) k)

/-- The substitution `u ↦ s³`, `z ↦ t³` on `k[u,z]`. -/
def cubeSubst : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (![MvPolynomial.X 0 ^ 3, MvPolynomial.X 1 ^ 3] : Fin 2 → MvPolynomial (Fin 2) k)

@[simp]
theorem uzEmb_X_zero : uzEmb (k := k) (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [uzEmb]

@[simp]
theorem uzEmb_X_one : uzEmb (k := k) (MvPolynomial.X 1) = MvPolynomial.X 3 := by
  simp [uzEmb]

@[simp]
theorem uzEmb_C (a : k) : uzEmb (k := k) (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [uzEmb]

theorem cubicTheta_comp_uzEmb :
    (cubicTheta (k := k)).comp (uzEmb (k := k)) = cubeSubst (k := k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [uzEmb, cubeSubst, cubicTheta]

theorem cubicTheta_uzEmb (A : MvPolynomial (Fin 2) k) :
    cubicTheta (uzEmb A) = cubeSubst A :=
  AlgHom.congr_fun (cubicTheta_comp_uzEmb (k := k)) A

@[simp]
theorem cubicTheta_X_zero : cubicTheta (k := k) (MvPolynomial.X 0) =
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 3 := by
  simp [cubicTheta]

@[simp]
theorem cubicTheta_X_one : cubicTheta (k := k) (MvPolynomial.X 1) =
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 * MvPolynomial.X 1 := by
  simp [cubicTheta]

@[simp]
theorem cubicTheta_X_two : cubicTheta (k := k) (MvPolynomial.X 2) =
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ^ 2 := by
  simp [cubicTheta]

@[simp]
theorem cubicTheta_X_three : cubicTheta (k := k) (MvPolynomial.X 3) =
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 3 := by
  simp [cubicTheta]

/-- Multiplying a normal form by `x₀ = u` keeps the normal-form shape. -/
theorem normal_form_mul_X0 {A B C : MvPolynomial (Fin 2) k} {H : MvPolynomial (Fin 4) k}
    (hH : H ∈ projTwistedIdeal (k := k)) :
    ∃ A' B' C' H', H' ∈ projTwistedIdeal (k := k) ∧
      (uzEmb A + MvPolynomial.X 1 * uzEmb B + MvPolynomial.X 2 * uzEmb C + H) *
        MvPolynomial.X 0 =
        uzEmb A' + MvPolynomial.X 1 * uzEmb B' + MvPolynomial.X 2 * uzEmb C' + H' :=
  ⟨MvPolynomial.X 0 * A, MvPolynomial.X 0 * B, MvPolynomial.X 0 * C, H * MvPolynomial.X 0,
    Ideal.mul_mem_right _ _ hH, by simp only [map_mul, uzEmb_X_zero]; ring⟩

/-- Multiplying a normal form by `x₃ = z` keeps the normal-form shape. -/
theorem normal_form_mul_X3 {A B C : MvPolynomial (Fin 2) k} {H : MvPolynomial (Fin 4) k}
    (hH : H ∈ projTwistedIdeal (k := k)) :
    ∃ A' B' C' H', H' ∈ projTwistedIdeal (k := k) ∧
      (uzEmb A + MvPolynomial.X 1 * uzEmb B + MvPolynomial.X 2 * uzEmb C + H) *
        MvPolynomial.X 3 =
        uzEmb A' + MvPolynomial.X 1 * uzEmb B' + MvPolynomial.X 2 * uzEmb C' + H' :=
  ⟨MvPolynomial.X 1 * A, MvPolynomial.X 1 * B, MvPolynomial.X 1 * C, H * MvPolynomial.X 3,
    Ideal.mul_mem_right _ _ hH, by simp only [map_mul, uzEmb_X_one]; ring⟩

/-- Multiplying a normal form by `x₁ = x` keeps the normal-form shape. -/
theorem normal_form_mul_X1 {A B C : MvPolynomial (Fin 2) k} {H : MvPolynomial (Fin 4) k}
    (hH : H ∈ projTwistedIdeal (k := k)) :
    ∃ A' B' C' H', H' ∈ projTwistedIdeal (k := k) ∧
      (uzEmb A + MvPolynomial.X 1 * uzEmb B + MvPolynomial.X 2 * uzEmb C + H) *
        MvPolynomial.X 1 =
        uzEmb A' + MvPolynomial.X 1 * uzEmb B' + MvPolynomial.X 2 * uzEmb C' + H' := by
  refine ⟨MvPolynomial.X 0 * MvPolynomial.X 1 * C, A, MvPolynomial.X 0 * B,
    H * MvPolynomial.X 1 - projGen_one (k := k) * uzEmb B - projGen_two (k := k) * uzEmb C,
    ?_, ?_⟩
  · refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hH) ?_) ?_
    · exact Ideal.mul_mem_right (uzEmb B) _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right (uzEmb C) _ (Ideal.subset_span (by simp))
  · simp only [map_mul, uzEmb_X_zero, uzEmb_X_one]
    ring

/-- Multiplying a normal form by `x₂ = y` keeps the normal-form shape. -/
theorem normal_form_mul_X2 {A B C : MvPolynomial (Fin 2) k} {H : MvPolynomial (Fin 4) k}
    (hH : H ∈ projTwistedIdeal (k := k)) :
    ∃ A' B' C' H', H' ∈ projTwistedIdeal (k := k) ∧
      (uzEmb A + MvPolynomial.X 1 * uzEmb B + MvPolynomial.X 2 * uzEmb C + H) *
        MvPolynomial.X 2 =
        uzEmb A' + MvPolynomial.X 1 * uzEmb B' + MvPolynomial.X 2 * uzEmb C' + H' := by
  refine ⟨MvPolynomial.X 0 * MvPolynomial.X 1 * B, MvPolynomial.X 1 * C, A,
    H * MvPolynomial.X 2 - projGen_two (k := k) * uzEmb B - projGen_three (k := k) * uzEmb C,
    ?_, ?_⟩
  · refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hH) ?_) ?_
    · exact Ideal.mul_mem_right (uzEmb B) _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right (uzEmb C) _ (Ideal.subset_span (by simp))
  · simp only [map_mul, uzEmb_X_zero, uzEmb_X_one]
    ring

/-- **Normal form** modulo `J = (x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`: every polynomial is
`A + x·B + y·C` with `A, B, C ∈ k[u,z]`, modulo `J`. -/
theorem exists_normal_form (G : MvPolynomial (Fin 4) k) :
    ∃ (A B C : MvPolynomial (Fin 2) k) (H : MvPolynomial (Fin 4) k),
      H ∈ projTwistedIdeal (k := k) ∧
      G = uzEmb A + MvPolynomial.X 1 * uzEmb B + MvPolynomial.X 2 * uzEmb C + H := by
  induction G using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, 0, 0, 0, Submodule.zero_mem _, by simp⟩
  | add p q hp hq =>
    obtain ⟨A₁, B₁, C₁, H₁, hH₁, rfl⟩ := hp
    obtain ⟨A₂, B₂, C₂, H₂, hH₂, rfl⟩ := hq
    refine ⟨A₁ + A₂, B₁ + B₂, C₁ + C₂, H₁ + H₂, Submodule.add_mem _ hH₁ hH₂, ?_⟩
    simp only [map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨A, B, C, H, hH, rfl⟩ := hp
    match i with
    | ⟨0, _⟩ => exact normal_form_mul_X0 hH
    | ⟨1, _⟩ => exact normal_form_mul_X1 hH
    | ⟨2, _⟩ => exact normal_form_mul_X2 hH
    | ⟨3, _⟩ => exact normal_form_mul_X3 hH




section Separation

/-- The exponent vector `3 • m` produced by `cubeSubst` on the monomial `X^m`. -/
def cubeExp (m : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (3 * m 0) + Finsupp.single 1 (3 * m 1)

/-- The exponent vector of `x₀²x₁`. -/
def e21 : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 1

/-- The exponent vector of `x₀x₁²`. -/
def e12 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 2

@[simp] theorem cubeExp_zero (m : Fin 2 →₀ ℕ) : cubeExp m 0 = 3 * m 0 := by
  simp [cubeExp]

@[simp] theorem cubeExp_one (m : Fin 2 →₀ ℕ) : cubeExp m 1 = 3 * m 1 := by
  simp [cubeExp]

theorem cubeExp_injective : Function.Injective cubeExp := by
  intro m m' h
  have h0 : m 0 = m' 0 := by
    have h' := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    simp only [cubeExp_zero] at h'
    omega
  have h1 : m 1 = m' 1 := by
    have h' := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp only [cubeExp_one] at h'
    omega
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] theorem cubeSubst_X_zero :
    cubeSubst (k := k) (MvPolynomial.X 0) = MvPolynomial.X 0 ^ 3 := by
  simp [cubeSubst]

@[simp] theorem cubeSubst_X_one :
    cubeSubst (k := k) (MvPolynomial.X 1) = MvPolynomial.X 1 ^ 3 := by
  simp [cubeSubst]

@[simp] theorem cubeSubst_C (a : k) :
    cubeSubst (k := k) (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [cubeSubst]

/-- A monomial as `C c * X 0 ^ m 0 * X 1 ^ m 1`. -/
theorem monomial_eq_two (m : Fin 2 →₀ ℕ) (c : k) :
    (MvPolynomial.monomial m c : MvPolynomial (Fin 2) k) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ (m 0) * MvPolynomial.X 1 ^ (m 1) := by
  rw [MvPolynomial.monomial_eq]
  simp [Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

/-- The monomial `X 0 ^ a * X 1 ^ b`. -/
theorem X_pow_mul_X_pow_eq_monomial (a b : ℕ) :
    ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ a * MvPolynomial.X 1 ^ b) =
      MvPolynomial.monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  simp

theorem cubeSubst_monomial (m : Fin 2 →₀ ℕ) (c : k) :
    cubeSubst (k := k) (MvPolynomial.monomial m c) = MvPolynomial.monomial (cubeExp m) c := by
  rw [monomial_eq_two, monomial_eq_two]
  simp only [map_mul, map_pow, cubeSubst_X_zero, cubeSubst_X_one, cubeSubst_C]
  rw [← pow_mul, ← pow_mul]
  simp [cubeExp]

/-- Coefficients of `cubeSubst A` in the residue class `≡ 0` modulo `3` are the coefficients of
`A`. -/
theorem coeff_cubeSubst_cubeExp (m : Fin 2 →₀ ℕ) (A : MvPolynomial (Fin 2) k) :
    MvPolynomial.coeff (cubeExp m) (cubeSubst A) = MvPolynomial.coeff m A := by
  induction A using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]
  | monomial m' c =>
    rw [cubeSubst_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases h : m' = m
    · subst h; simp
    · have h' : cubeExp m' ≠ cubeExp m := fun heq => h (cubeExp_injective heq)
      rw [if_neg h', if_neg h]

/-- Coefficients of `cubeSubst A` at an exponent whose first coordinate is not divisible by `3`
vanish. -/
theorem coeff_cubeSubst_eq_zero_of_not_dvd {p q : ℕ} (hp : ¬ 3 ∣ p)
    (A : MvPolynomial (Fin 2) k) :
    MvPolynomial.coeff (Finsupp.single 0 p + Finsupp.single 1 q) (cubeSubst A) = 0 := by
  induction A using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ, add_zero]
  | monomial m c =>
    rw [cubeSubst_monomial, MvPolynomial.coeff_monomial, if_neg]
    intro heq
    exact hp ⟨m 0, by
      have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
      simpa using h0.symm⟩

/-- Coefficients of `cubeSubst A` at an exponent whose second coordinate is not divisible by `3`
vanish. -/
theorem coeff_cubeSubst_eq_zero_of_not_dvd_right {p q : ℕ} (hq : ¬ 3 ∣ q)
    (A : MvPolynomial (Fin 2) k) :
    MvPolynomial.coeff (Finsupp.single 0 p + Finsupp.single 1 q) (cubeSubst A) = 0 := by
  induction A using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ, add_zero]
  | monomial m c =>
    rw [cubeSubst_monomial, MvPolynomial.coeff_monomial, if_neg]
    intro heq
    exact hq ⟨m 1, by
      have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
      simpa using h1.symm⟩

/-- Coefficients of `monomial s 1 * cubeSubst B` at `s + cubeExp m` are the coefficients of `B`. -/
theorem coeff_monomial_mul_cubeSubst_self (s : Fin 2 →₀ ℕ) (m : Fin 2 →₀ ℕ)
    (B : MvPolynomial (Fin 2) k) :
    MvPolynomial.coeff (s + cubeExp m) (MvPolynomial.monomial s (1 : k) * cubeSubst B) =
      MvPolynomial.coeff m B := by
  rw [MvPolynomial.coeff_monomial_mul, one_mul, coeff_cubeSubst_cubeExp]

/-- Coefficients of `monomial s 1 * cubeSubst B` vanish away from the exponents `s + cubeExp m`. -/
theorem coeff_monomial_mul_cubeSubst_eq_zero {s E : Fin 2 →₀ ℕ}
    (h : ∀ m : Fin 2 →₀ ℕ, E ≠ s + cubeExp m) (B : MvPolynomial (Fin 2) k) :
    MvPolynomial.coeff E (MvPolynomial.monomial s (1 : k) * cubeSubst B) = 0 := by
  induction B using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, mul_add, MvPolynomial.coeff_add, hP, hQ, add_zero]
  | monomial m c =>
    simp only [cubeSubst_monomial, MvPolynomial.monomial_mul, one_mul,
      MvPolynomial.coeff_monomial]
    exact if_neg (Ne.symm (h m))

theorem e21_add_cubeExp (m : Fin 2 →₀ ℕ) :
    e21 + cubeExp m = Finsupp.single 0 (3 * m 0 + 2) + Finsupp.single 1 (3 * m 1 + 1) := by
  ext i
  fin_cases i <;> (simp [e21, cubeExp]; omega)

theorem e12_add_cubeExp (m : Fin 2 →₀ ℕ) :
    e12 + cubeExp m = Finsupp.single 0 (3 * m 0 + 1) + Finsupp.single 1 (3 * m 1 + 2) := by
  ext i
  fin_cases i <;> (simp [e12, cubeExp]; omega)

/-- **Separation**: if `A(s³,t³) + s²t·B(s³,t³) + st²·C(s³,t³) = 0`, then `A = B = C = 0`.
The three summands occupy the residue classes `(0,0)`, `(2,1)` and `(1,2)` modulo `3` in the
exponent vectors, so their coefficients can be read off separately. -/
theorem separation {A B C : MvPolynomial (Fin 2) k}
    (h : cubeSubst A + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 * cubeSubst B +
      MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * cubeSubst C = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hBm : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 * MvPolynomial.X 1) =
      MvPolynomial.monomial e21 1 := by
    simpa [e21] using X_pow_mul_X_pow_eq_monomial (k := k) 2 1
  have hCm : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ^ 2) =
      MvPolynomial.monomial e12 1 := by
    simpa [e12] using X_pow_mul_X_pow_eq_monomial (k := k) 1 2
  have keyA : ∀ m : Fin 2 →₀ ℕ, MvPolynomial.coeff m A = 0 := by
    intro m
    have h1 := congrArg (MvPolynomial.coeff (cubeExp m)) h
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_zero] at h1
    rw [hBm, hCm] at h1
    have e1 : MvPolynomial.coeff (cubeExp m) (cubeSubst A) = MvPolynomial.coeff m A :=
      coeff_cubeSubst_cubeExp m A
    have e2 : MvPolynomial.coeff (cubeExp m) (MvPolynomial.monomial e21 1 * cubeSubst B) = 0 :=
      coeff_monomial_mul_cubeSubst_eq_zero (s := e21) (E := cubeExp m) (fun m' heq => by
        have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
        simp [e21, cubeExp] at h0
        omega) B
    have e3 : MvPolynomial.coeff (cubeExp m) (MvPolynomial.monomial e12 1 * cubeSubst C) = 0 :=
      coeff_monomial_mul_cubeSubst_eq_zero (s := e12) (E := cubeExp m) (fun m' heq => by
        have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
        simp [e12, cubeExp] at h0
        omega) C
    rw [e1, e2, e3, add_zero, add_zero] at h1
    exact h1
  have keyB : ∀ m : Fin 2 →₀ ℕ, MvPolynomial.coeff m B = 0 := by
    intro m
    have h1 := congrArg (MvPolynomial.coeff (e21 + cubeExp m)) h
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_zero] at h1
    rw [hBm, hCm] at h1
    have e1 : MvPolynomial.coeff (e21 + cubeExp m) (cubeSubst A) = 0 := by
      rw [e21_add_cubeExp m]
      exact coeff_cubeSubst_eq_zero_of_not_dvd (p := 3 * m 0 + 2) (q := 3 * m 1 + 1) (by
        rintro ⟨c, hc⟩
        omega) A
    have e2 : MvPolynomial.coeff (e21 + cubeExp m)
        (MvPolynomial.monomial e21 1 * cubeSubst B) = MvPolynomial.coeff m B :=
      coeff_monomial_mul_cubeSubst_self e21 m B
    have e3 : MvPolynomial.coeff (e21 + cubeExp m) (MvPolynomial.monomial e12 1 * cubeSubst C) = 0 :=
      coeff_monomial_mul_cubeSubst_eq_zero (s := e12) (E := e21 + cubeExp m) (fun m' heq => by
        have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
        simp [e12, e21, cubeExp] at h0
        omega) C
    rw [e1, e2, e3, zero_add, add_zero] at h1
    exact h1
  have keyC : ∀ m : Fin 2 →₀ ℕ, MvPolynomial.coeff m C = 0 := by
    intro m
    have h1 := congrArg (MvPolynomial.coeff (e12 + cubeExp m)) h
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_zero] at h1
    rw [hBm, hCm] at h1
    have e1 : MvPolynomial.coeff (e12 + cubeExp m) (cubeSubst A) = 0 := by
      rw [e12_add_cubeExp m]
      exact coeff_cubeSubst_eq_zero_of_not_dvd (p := 3 * m 0 + 1) (q := 3 * m 1 + 2) (by
        rintro ⟨c, hc⟩
        omega) A
    have e2 : MvPolynomial.coeff (e12 + cubeExp m) (MvPolynomial.monomial e21 1 * cubeSubst B) = 0 :=
      coeff_monomial_mul_cubeSubst_eq_zero (s := e21) (E := e12 + cubeExp m) (fun m' heq => by
        have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
        simp [e12, e21, cubeExp] at h0
        omega) B
    have e3 : MvPolynomial.coeff (e12 + cubeExp m) (MvPolynomial.monomial e12 1 * cubeSubst C) =
        MvPolynomial.coeff m C :=
      coeff_monomial_mul_cubeSubst_self e12 m C
    rw [e1, e2, e3, zero_add, zero_add] at h1
    exact h1
  exact ⟨MvPolynomial.ext _ _ fun m => by rw [keyA m]; simp,
    MvPolynomial.ext _ _ fun m => by rw [keyB m]; simp,
    MvPolynomial.ext _ _ fun m => by rw [keyC m]; simp⟩

end Separation

end NormalForm

end ProjectiveTwistedCubic



/-! ## 7. `ker θ = J`, hence `I(Y̅) = J`, and the non-generation of `I(Y̅)`

The parametrization `θ : k[x₀,x₁,x₂,x₃] → k[s,t]`, `x₀ ↦ s³`, `x₁ ↦ s²t`, `x₂ ↦ st²`,
`x₃ ↦ t³` has kernel exactly `J = (x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`.  The nontrivial
inclusion `ker θ ⊆ J` is reduced, via the normal form `G = A + x₁B + x₂C + H` with
`A, B, C ∈ k[x₀,x₃]` and `H ∈ J`, to the coefficient separation `separation`. -/

section FinalAssembly

variable {k : Type*} [Field k]

/-- `θ` kills the first generator `x₀x₂ - x₁²` of `J`. -/
theorem cubicTheta_projGen_one : cubicTheta (k := k) (projGen_one (k := k)) = 0 := by
  show cubicTheta (k := k) (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) = 0
  simp only [map_sub, map_mul, map_pow, cubicTheta_X_zero, cubicTheta_X_one, cubicTheta_X_two]
  ring

/-- `θ` kills the second generator `x₀x₃ - x₁x₂` of `J`. -/
theorem cubicTheta_projGen_two : cubicTheta (k := k) (projGen_two (k := k)) = 0 := by
  show cubicTheta (k := k) (MvPolynomial.X 0 * MvPolynomial.X 3 -
    MvPolynomial.X 1 * MvPolynomial.X 2) = 0
  simp only [map_sub, map_mul, cubicTheta_X_zero, cubicTheta_X_one, cubicTheta_X_two,
    cubicTheta_X_three]
  ring

/-- `θ` kills the third generator `x₁x₃ - x₂²` of `J`. -/
theorem cubicTheta_projGen_three : cubicTheta (k := k) (projGen_three (k := k)) = 0 := by
  show cubicTheta (k := k) (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2) = 0
  simp only [map_sub, map_mul, map_pow, cubicTheta_X_one, cubicTheta_X_two, cubicTheta_X_three]
  ring

/-- `θ` kills every element of `J`. -/
theorem cubicTheta_eq_zero_of_mem {G : MvPolynomial (Fin 4) k}
    (hG : G ∈ projTwistedIdeal (k := k)) : cubicTheta (k := k) G = 0 := by
  have hle : projTwistedIdeal (k := k) ≤ RingHom.ker (cubicTheta (k := k)).toRingHom := by
    rw [projTwistedIdeal, Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact cubicTheta_projGen_one
    · exact cubicTheta_projGen_two
    · exact cubicTheta_projGen_three
  exact hle hG

/-- **The kernel of the parametrization of the projective twisted cubic**:
`ker θ ⊆ J = (x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`. -/
theorem ker_cubicTheta_le (G : MvPolynomial (Fin 4) k) (hG : cubicTheta (k := k) G = 0) :
    G ∈ projTwistedIdeal (k := k) := by
  obtain ⟨A, B, C, H, hH, rfl⟩ := exists_normal_form (k := k) G
  have hH0 : cubicTheta (k := k) H = 0 := cubicTheta_eq_zero_of_mem hH
  have hkey : cubeSubst A + (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 * MvPolynomial.X 1 *
      cubeSubst B + MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * cubeSubst C = 0 := by
    have h := hG
    simp only [map_add, map_mul, cubicTheta_uzEmb, cubicTheta_X_one, cubicTheta_X_two] at h
    rw [hH0, add_zero] at h
    exact h
  obtain ⟨hA, hB, hC⟩ := separation hkey
  rw [hA, hB, hC]
  simpa using hH

/-- If `θ G = 0`, then `G` vanishes at every point of the affine twisted cubic. -/
theorem aeval_cubicPoint_eq_zero {G : MvPolynomial (Fin 4) k}
    (hG : cubicTheta (k := k) G = 0) (t : k) :
    MvPolynomial.aeval (R := k) (Fin.cons 1 (cubicPoint t)) G = 0 := by
  rw [← aeval_theta, hG, map_zero]

/-- A homogeneous polynomial vanishing on the affine twisted cubic belongs to `I(Y̅)`. -/
theorem mem_projVanishingIdeal_of_aeval_cubicPoint {g : MvPolynomial (Fin 4) k} {e : ℕ}
    (hg : g.IsHomogeneous e)
    (h : ∀ t : k, MvPolynomial.aeval (R := k) (Fin.cons 1 (cubicPoint t)) g = 0) :
    g ∈ projVanishingIdeal (projTwistedCubic (k := k)) := by
  have hhom : g.IsHomogeneous g.totalDegree := by
    rcases eq_or_ne g 0 with h0 | h0
    · rw [h0]
      simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 4) (R := k) (0 : k))
    · rw [hg.totalDegree h0]
      exact hg
  rw [projTwistedCubic]
  refine subset_projVanishingIdeal hhom ?_
  have hcl : IsClosed {P : ProjPoint k 3 | vanishes g P} := isClosed_vanishes hhom
  intro P hP
  refine projectiveClosure_minimal hcl ?_ hP
  rintro _ ⟨a, ha, rfl⟩
  rw [eq_cubicPoint_of_mem ha]
  exact h _

/-- `J ⊆ I(Y̅)`: each of the three generators vanishes on the projective twisted cubic. -/
theorem projTwistedIdeal_le_projVanishingIdeal :
    projTwistedIdeal (k := k) ≤ projVanishingIdeal (projTwistedCubic (k := k)) := by
  rw [projTwistedIdeal, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_projVanishingIdeal_of_aeval_cubicPoint isHomogeneous_projGen_one
      fun t => aeval_cubicPoint_eq_zero cubicTheta_projGen_one t
  · exact mem_projVanishingIdeal_of_aeval_cubicPoint isHomogeneous_projGen_two
      fun t => aeval_cubicPoint_eq_zero cubicTheta_projGen_two t
  · exact mem_projVanishingIdeal_of_aeval_cubicPoint isHomogeneous_projGen_three
      fun t => aeval_cubicPoint_eq_zero cubicTheta_projGen_three t

/-- `I(Y̅) ⊆ J`: a homogeneous polynomial vanishing on `Y̅` is killed by `θ`, hence lies in `J`. -/
theorem projVanishingIdeal_le_projTwistedIdeal [Infinite k] :
    projVanishingIdeal (projTwistedCubic (k := k)) ≤ projTwistedIdeal (k := k) := by
  rw [projVanishingIdeal, Ideal.span_le]
  rintro F ⟨hF, hvan⟩
  refine ker_cubicTheta_le F ?_
  refine binaryForm_eq_zero (cubicTheta_isHomogeneous hF) fun t => ?_
  rw [aeval_theta]
  exact hvan (iota (cubicPoint t)) (subset_projectiveClosure (twistedCubic (k := k))
    ⟨cubicPoint t, cubicPoint_mem t, rfl⟩)

/-- **Hartshorne I.2.9 (b), the ideal computation**: the homogeneous vanishing ideal of the
projective twisted cubic is `J = (x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`. -/
theorem projVanishingIdeal_projTwistedCubic [Infinite k] :
    projVanishingIdeal (projTwistedCubic (k := k)) = projTwistedIdeal (k := k) :=
  le_antisymm projVanishingIdeal_le_projTwistedIdeal projTwistedIdeal_le_projVanishingIdeal

/-! ### The homogenizations of the two affine generators -/

/-- The total degree of `y - x²` is `2`. -/
theorem totalDegree_affGen_one :
    (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 3) k).totalDegree = 2 := by
  refine le_antisymm ?_ ?_
  · calc (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 3) k).totalDegree
        ≤ max (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) k).totalDegree
            ((MvPolynomial.X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) k)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ = 2 := by
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X_pow]
        norm_num
  · have hmem : (Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) ∈
        (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 3) k).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_X,
        MvPolynomial.coeff_X_pow]
      have hne : (Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) ≠
          Finsupp.single (0 : Fin 3) 2 := by
        intro h
        have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
        simp at h1
      simp [hne]
    have h2 := MvPolynomial.le_totalDegree hmem
    simp only [Finsupp.sum_single_index] at h2
    exact h2

/-- The total degree of `z - x³` is `3`. -/
theorem totalDegree_affGen_two :
    (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 3) k).totalDegree = 3 := by
  refine le_antisymm ?_ ?_
  · calc (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 3) k).totalDegree
        ≤ max (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) k).totalDegree
            ((MvPolynomial.X (0 : Fin 3) ^ 3 : MvPolynomial (Fin 3) k)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ = 3 := by
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X_pow]
        norm_num
  · have hmem : (Finsupp.single (0 : Fin 3) 3 : Fin 3 →₀ ℕ) ∈
        (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 3) k).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_X,
        MvPolynomial.coeff_X_pow]
      have hne : (Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) ≠
          Finsupp.single (0 : Fin 3) 3 := by
        intro h
        have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) h
        simp at h1
      simp [hne]
    have h2 := MvPolynomial.le_totalDegree hmem
    simp only [Finsupp.sum_single_index] at h2
    exact h2

/-- `β(y - x²) = x₀x₂ - x₁²`. -/
theorem homogenizeDeg_affGen_one :
    homogenizeDeg k 3 (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2) = projGen_one (k := k) := by
  rw [homogenizeDeg, totalDegree_affGen_one]
  exact homogenize_projGen_one

/-- `β(z - x³) = x₀²x₃ - x₁³`. -/
theorem homogenizeDeg_affGen_two :
    homogenizeDeg k 3 (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3) =
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3 := by
  rw [homogenizeDeg, totalDegree_affGen_two]
  exact homogenize_affGen_two

/-! ### Non-generation: `β(y - x²)` and `β(z - x³)` do not generate `I(Y̅)` -/

/-- The dual-number evaluation `k[u,x,y,z] → k[ε]/(ε²)`, `u, z ↦ 0`, `x ↦ ε`, `y ↦ 1`. -/
def dualTest (k : Type*) [Field k] : MvPolynomial (Fin 4) k →ₐ[k] DualNumber k :=
  MvPolynomial.aeval (![0, (DualNumber.eps : DualNumber k), 1, 0] : Fin 4 → DualNumber k)

theorem dualTest_quad :
    dualTest k (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) = 0 := by
  simp [dualTest]

theorem dualTest_cubic :
    dualTest k (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3) = 0 := by
  simp [dualTest, pow_succ]

theorem dualTest_eps_ne_zero : (DualNumber.eps : DualNumber k) ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.snd h
  simp at h1

theorem dualTest_projGen_two :
    dualTest k (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) =
      -DualNumber.eps := by
  simp [dualTest]

/-- **Hartshorne I.2.9 (b), the non-generation statement**: the homogenizations of the two
generators `y - x²`, `z - x³` of the affine ideal `I(Y)` do not generate `I(Y̅)`; the missing
generator is `x₀x₃ - x₁x₂`, which the dual-number evaluation detects. -/
theorem homogenized_affine_generators_not_generate :
    Ideal.span ({homogenizeDeg k 3 (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2),
      homogenizeDeg k 3 (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3)} :
        Set (MvPolynomial (Fin 4) k)) ≠ projTwistedIdeal (k := k) := by
  intro hEq
  rw [homogenizeDeg_affGen_one, homogenizeDeg_affGen_two] at hEq
  have hmem : (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 :
      MvPolynomial (Fin 4) k) ∈
      Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2,
        MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3} :
        Set (MvPolynomial (Fin 4) k)) := by
    rw [hEq]
    exact projGen_two_mem
  have hle : Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2,
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 ^ 3} :
      Set (MvPolynomial (Fin 4) k)) ≤ RingHom.ker (dualTest k).toRingHom := by
    rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact dualTest_quad
    · exact dualTest_cubic
  have h0 : dualTest k (MvPolynomial.X 0 * MvPolynomial.X 3 -
      MvPolynomial.X 1 * MvPolynomial.X 2) = 0 := hle hmem
  rw [dualTest_projGen_two] at h0
  exact dualTest_eps_ne_zero (neg_eq_zero.mp h0)

/-- **Hartshorne, Algebraic Geometry, Exercise I.2.9**, all parts, over an algebraically
closed field `k`:

* (a) for any subset `Y ⊆ Aⁿ` the homogeneous vanishing ideal of the projective closure is
  generated by the homogenizations `β f`, `f ∈ I(Y)`;
* (b) for the twisted cubic `Y = {(t,t²,t³)}`, `I(Y) = (y - x², z - x³)` and
  `I(Y̅) = (x₀x₂ - x₁², x₀x₃ - x₁x₂, x₁x₃ - x₂²)`, while the homogenizations of the two
  affine generators do not generate `I(Y̅)`. -/
theorem hartshorne_ex_I_2_9 [IsAlgClosed k] :
    (projVanishingIdeal (projectiveClosure (twistedCubic (k := k))) =
        Ideal.span (homogenizeDeg k 3 '' MvPolynomial.vanishingIdeal k (twistedCubic (k := k)))) ∧
      (MvPolynomial.vanishingIdeal k (twistedCubic (k := k)) = twistedCubicIdeal (k := k)) ∧
      (projTwistedIdeal (k := k) =
        Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2,
          MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2,
          MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 2 ^ 2} :
          Set (MvPolynomial (Fin 4) k))) ∧
      (projVanishingIdeal (projTwistedCubic (k := k)) = projTwistedIdeal (k := k)) ∧
      (Ideal.span ({homogenizeDeg k 3 (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2),
        homogenizeDeg k 3 (MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3)} :
          Set (MvPolynomial (Fin 4) k)) ≠ projTwistedIdeal (k := k)) :=
  ⟨projVanishingIdeal_projectiveClosure 3 (twistedCubic (k := k)),
    vanishingIdeal_twistedCubic,
    rfl,
    projVanishingIdeal_projTwistedCubic,
    homogenized_affine_generators_not_generate⟩

end FinalAssembly

end ProjPoint

end Hartshorne77.Ex_I_2_9


/-! ### Axiom audit -/

namespace Hartshorne77.Ex_I_2_9.ProjPoint

#print axioms vanishingIdeal_twistedCubic
#print axioms homogenize_dehom

end Hartshorne77.Ex_I_2_9.ProjPoint

#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.projVanishingIdeal_projectiveClosure
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.dehom_homogenize_eq
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.homogenize_shift
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.cubicTheta_monomial

/-! ### Axiom audit of the decisive results -/

#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.separation
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.ker_cubicTheta_le
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.projVanishingIdeal_projTwistedCubic
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.projVanishingIdeal_projectiveClosure
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.homogenized_affine_generators_not_generate
#print axioms Hartshorne77.Ex_I_2_9.ProjPoint.hartshorne_ex_I_2_9
