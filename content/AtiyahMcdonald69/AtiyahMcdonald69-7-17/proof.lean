/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter VII (Noetherian rings),
Exercise 17.  Public page:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-17

Statement, recovered from the textbook (the recorded `proof.tex` contains only the proof; the
book's wording is cross-checked in `.scratch/reference/atiyah-solutions.txt`):

  "Let `A` be a ring and `M` a Noetherian `A`-module. Show that every submodule `N ≠ M` of `M`
   has a primary decomposition."

The exercise states its own terminology:

  "A submodule `P` of `M` is said to be *irreducible* if it cannot be expressed as the
   intersection of two submodules of `M` properly containing `P`."

and the book's Chapter 4 definition (p. 51) is: `Q` is primary in `M` if `Q ≠ M` and whenever
`a • x ∈ Q` (`a ∈ A`, `x ∈ M`), then `x ∈ Q` or `aⁿ ∈ (Q : M)` for some `n > 0`.

Contents of this file (all with the book's own definitions, not abstractions):

* `IsIrredSubmodule` — the book's definition of an irreducible submodule, literally (it is *not*
  the order-theoretic `InfIrred`, which additionally excludes the top element).
* `isIrredSubmodule_iff_infIrred` — on proper submodules the two notions agree.
* `IsPrimarySubmodule` — the book's definition of a primary submodule, literally, and
  `isPrimary_iff_exists_pos_pow`, `isPrimarySubmodule_iff` — its agreement with Mathlib's
  `Submodule.IsPrimary`.
* `exists_finset_inf_isIrredSubmodule` — every submodule of a Noetherian module is a finite
  intersection of irreducible submodules: the ascending chain argument of (7.11) carried over to
  modules, as the textbook says.
* `exists_finset_inf_isIrredSubmodule_of_ne_top` — the same with every component proper.
* `mkQ_eq_zero_iff`, `isIrredSubmodule_bot_quotient` — irreducibility passes to `M ⧸ Q`.
* `isPrimarySubmodule_bot` — the book's kernel-chain argument: `0` irreducible in a Noetherian
  module (which is nonzero) is primary.
* `isPrimarySubmodule_of_isIrredSubmodule` — every proper irreducible submodule is primary,
  proved by the book's reduction to the quotient; `isPrimary_of_isIrredSubmodule` is an
  independent cross-check of the same fact through Mathlib's `InfIrred.isPrimary`.
* `exists_finset_inf_isPrimary`, `solution` — **Exercise 7.17**.
* `exists_isMinimalPrimaryDecomposition` — the stronger reduced (minimal) form of the
  decomposition, with distinct radicals and every component necessary.

No `sorry`, no `admit`, no new axioms.
-/
import Mathlib

open scoped Pointwise

namespace AtiyahMcdonald69.Ex_7_17

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ### Irreducible submodules -/

/-- Atiyah–Macdonald's definition (Chapter 7, Exercise 17): a submodule `P` of `M` is
*irreducible* if it cannot be expressed as the intersection of two submodules of `M` properly
containing `P`. -/
def IsIrredSubmodule (P : Submodule A M) : Prop :=
  ¬ ∃ P₁ P₂ : Submodule A M, P < P₁ ∧ P < P₂ ∧ P₁ ⊓ P₂ = P

/-- Mathlib's `InfIrred` is the same notion on proper submodules; note that `⊤` is irreducible in
the book's sense (nothing properly contains it) but not `InfIrred`. -/
theorem isIrredSubmodule_iff_infIrred {P : Submodule A M} (hP : P ≠ ⊤) :
    IsIrredSubmodule P ↔ InfIrred P := by
  constructor
  · intro h
    refine ⟨by simpa [not_isMax_iff_ne_top] using hP, ?_⟩
    intro b c hbc
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hb, hc⟩ := hcon
    refine h ⟨b, c, ?_, ?_, hbc⟩
    · exact lt_of_le_of_ne (hbc ▸ inf_le_left) (Ne.symm hb)
    · exact lt_of_le_of_ne (hbc ▸ inf_le_right) (Ne.symm hc)
  · rintro ⟨-, h⟩ ⟨P₁, P₂, h1, h2, hP'⟩
    rcases h hP' with h' | h'
    · exact (ne_of_gt h1) h'
    · exact (ne_of_gt h2) h'

/-! ### Primary submodules -/

/-- Atiyah–Macdonald's definition (Chapter 4, p. 51, in the form used in Exercise 7.17): `Q` is
primary in `M` if `Q ≠ M` and whenever `a • x ∈ Q` (`a ∈ A`, `x ∈ M`) then `x ∈ Q` or
`aⁿ ∈ (Q : M)` for some `n > 0`, where `(Q : M) = Q.colon ⊤` is the annihilator of `M ⧸ Q`. -/
def IsPrimarySubmodule (Q : Submodule A M) : Prop :=
  Q ≠ ⊤ ∧ ∀ (a : A) (x : M), a • x ∈ Q → x ∈ Q ∨ ∃ n : ℕ, 0 < n ∧ a ^ n ∈ Q.colon (⊤ : Submodule A M)

/-- Mathlib's `Submodule.IsPrimary` is verbatim the book's definition, with the exponent required
to be positive. -/
theorem isPrimary_iff_exists_pos_pow (Q : Submodule A M) :
    Q.IsPrimary ↔ Q ≠ ⊤ ∧ ∀ (a : A) (x : M), a • x ∈ Q →
      x ∈ Q ∨ ∃ n : ℕ, 0 < n ∧ a ^ n ∈ Q.colon (⊤ : Submodule A M) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a x hax
    rcases h.2 hax with hx | ⟨n, hn⟩
    · exact Or.inl hx
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact absurd (top_le_iff.mp (by simpa using hn)) h.1
      · exact Or.inr ⟨n, hpos, (Submodule.mem_colon_iff_le (N := Q) (N' := ⊤)).2 hn⟩
  · rintro ⟨hQ, h⟩
    refine ⟨hQ, ?_⟩
    intro a x hax
    rcases h a x hax with hx | ⟨n, hn, hmem⟩
    · exact Or.inl hx
    · exact Or.inr ⟨n, (Submodule.mem_colon_iff_le (N := Q) (N' := ⊤)).1 hmem⟩

/-- The book's definition of *primary* (`IsPrimarySubmodule`) agrees with Mathlib's
`Submodule.IsPrimary`. -/
theorem isPrimarySubmodule_iff (Q : Submodule A M) : IsPrimarySubmodule Q ↔ Q.IsPrimary :=
  (isPrimary_iff_exists_pos_pow Q).symm

/-! ### Finite intersections of irreducible submodules -/

/-- The ascending chain condition argument of (7.11), carried over to modules: every submodule of
a Noetherian module is a finite intersection of irreducible submodules. -/
theorem exists_finset_inf_isIrredSubmodule [IsNoetherian A M] (N : Submodule A M) :
    ∃ s : Finset (Submodule A M), s.inf id = N ∧ ∀ J ∈ s, IsIrredSubmodule J := by
  classical
  refine WellFoundedGT.induction (motive := fun N : Submodule A M =>
    ∃ s : Finset (Submodule A M), s.inf id = N ∧ ∀ J ∈ s, IsIrredSubmodule J) N ?_
  intro N ih
  by_cases h : IsIrredSubmodule N
  · exact ⟨{N}, by simp, by simpa using h⟩
  · simp only [IsIrredSubmodule, not_not] at h
    obtain ⟨P₁, P₂, h1, h2, hP⟩ := h
    obtain ⟨s₁, hs₁, hI₁⟩ := ih P₁ h1
    obtain ⟨s₂, hs₂, hI₂⟩ := ih P₂ h2
    refine ⟨s₁ ∪ s₂, ?_, ?_⟩
    · rw [Finset.inf_union, hs₁, hs₂, hP]
    · intro J hJ
      rcases Finset.mem_union.mp hJ with hJ | hJ
      · exact hI₁ J hJ
      · exact hI₂ J hJ

section InfEraseTop

variable (s : Finset (Submodule A M))

/-- Dropping a `⊤` from a finite intersection does not change it. -/
private theorem inf_erase_top : (s.erase ⊤).inf id = s.inf id := by
  classical
  by_cases h : (⊤ : Submodule A M) ∈ s
  · rw [← Finset.insert_erase h]
    simp
  · rw [Finset.erase_eq_of_notMem h]

end InfEraseTop

/-- Every submodule `N ≠ ⊤` is a nonempty finite intersection of proper irreducible submodules. -/
theorem exists_finset_inf_isIrredSubmodule_of_ne_top [IsNoetherian A M] {N : Submodule A M}
    (hN : N ≠ ⊤) :
    ∃ s : Finset (Submodule A M), s.Nonempty ∧ s.inf id = N ∧
      ∀ J ∈ s, IsIrredSubmodule J ∧ J ≠ ⊤ := by
  classical
  obtain ⟨s, hs, hI⟩ := exists_finset_inf_isIrredSubmodule N
  have hinf : (s.erase ⊤).inf id = N := by rw [inf_erase_top, hs]
  refine ⟨s.erase ⊤, ?_, hinf, ?_⟩
  · rcases Finset.eq_empty_or_nonempty (s.erase ⊤) with h | h
    · rw [h] at hinf
      simp at hinf
      exact absurd hinf.symm hN
    · exact h
  · intro J hJ
    exact ⟨hI J (Finset.mem_of_mem_erase hJ), Finset.ne_of_mem_erase hJ⟩

/-! ### Proper irreducible submodules are primary (the book's argument) -/

/-- The kernel of `M → M ⧸ Q`. -/
theorem mkQ_eq_zero_iff (Q : Submodule A M) (m : M) : Q.mkQ m = 0 ↔ m ∈ Q := by
  constructor
  · intro h
    have h' : m ∈ LinearMap.ker (Q.mkQ) := h
    rwa [Submodule.ker_mkQ] at h'
  · intro h
    have h' : m ∈ LinearMap.ker (Q.mkQ) := by rwa [Submodule.ker_mkQ]
    exact h'

/-- Irreducibility passes to the quotient at `⊥`, as used in the textbook ("we may take `Q = 0`"). -/
theorem isIrredSubmodule_bot_quotient {Q : Submodule A M} (h : IsIrredSubmodule Q) :
    IsIrredSubmodule (⊥ : Submodule A (M ⧸ Q)) := by
  rintro ⟨P₁, P₂, h1, h2, hinf⟩
  have hlt : ∀ P : Submodule A (M ⧸ Q), ⊥ < P → Q < Submodule.comap Q.mkQ P := by
    intro P hP
    have hPne : P ≠ ⊥ := ne_of_gt hP
    refine lt_of_le_of_ne ?_ ?_
    · intro m hm
      rw [Submodule.mem_comap, (mkQ_eq_zero_iff Q m).mpr hm]
      exact P.zero_mem
    · intro heq
      obtain ⟨z, hzP, hz0⟩ : ∃ z ∈ P, z ≠ 0 := by
        by_contra hc
        simp only [not_exists, not_and, not_not] at hc
        exact hPne (le_antisymm (fun z hz => by simpa using hc z hz) bot_le)
      obtain ⟨m, hm⟩ := Q.mkQ_surjective z
      have hmP : m ∈ Submodule.comap Q.mkQ P := by
        rw [Submodule.mem_comap, hm]
        exact hzP
      have hmQ : m ∈ Q := heq ▸ hmP
      have hz : Q.mkQ m = 0 := (mkQ_eq_zero_iff Q m).mpr hmQ
      rw [hm] at hz
      exact hz0 hz
  refine h ⟨Submodule.comap Q.mkQ P₁, Submodule.comap Q.mkQ P₂, hlt P₁ h1, hlt P₂ h2, ?_⟩
  rw [← Submodule.comap_inf, hinf, Submodule.comap_bot, Submodule.ker_mkQ]

/-- The kernel-chain step of the textbook proof: in a Noetherian module, an irreducible `0` is
primary.  (`0 ≠ M` is needed for primariness itself; in the application `M` is `M ⧸ Q` with
`Q ≠ M`, so it holds.) -/
theorem isPrimarySubmodule_bot [IsNoetherian A M]
    (hne : (⊥ : Submodule A M) ≠ ⊤)
    (h : IsIrredSubmodule (⊥ : Submodule A M)) : IsPrimarySubmodule (⊥ : Submodule A M) := by
  refine ⟨hne, ?_⟩
  intro a x hax
  by_cases hx : x ∈ (⊥ : Submodule A M)
  · exact Or.inl hx
  right
  have hax0 : a • x = 0 := by simpa using hax
  -- the stabilising chain of kernels of multiplication by `aⁿ`
  let f : ℕ → M →ₗ[A] M := fun n => a ^ n • LinearMap.id
  let K : ℕ → Submodule A M := fun n => LinearMap.ker (f n)
  have hK : ∀ n (z : M), z ∈ K n ↔ a ^ n • z = 0 := by
    intro n z
    simp [K, f]
  have hmono : Monotone K := by
    intro n m hnm z hz
    rw [hK n z] at hz
    rw [hK m z]
    rw [← Nat.sub_add_cancel hnm, pow_add, mul_smul, hz, smul_zero]
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨K, hmono⟩
  have hNK : K N = K (N + 1) := hN (N + 1) (Nat.le_succ N)
  have hdisj : a ^ N • (⊤ : Submodule A M) ⊓ Submodule.span A {x} = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨z₀, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z (a ^ N) ⊤).mp hz1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz2
    rw [Submodule.mem_bot]
    have h₁ : a • (a ^ N • z₀) = 0 := by rw [← hc, smul_comm, hax0, smul_zero]
    have h₂ : a ^ (N + 1) • z₀ = 0 := by rw [pow_succ', mul_smul]; exact h₁
    have h₃ : z₀ ∈ K N := by
      rw [hNK, hK]
      exact h₂
    exact (hK N z₀).mp h₃
  have hspan : Submodule.span A {x} ≠ ⊥ := by
    intro hb
    refine hx ?_
    have hmem : x ∈ Submodule.span A {x} := Submodule.mem_span_singleton_self x
    rw [hb] at hmem
    exact hmem
  -- `0 = a^N M ∩ Ax` with `Ax ≠ 0` and `0` irreducible forces `a^N M = 0`
  have htop : a ^ N • (⊤ : Submodule A M) = ⊥ := by
    by_contra hne'
    refine h ⟨a ^ N • ⊤, Submodule.span A {x}, ?_, ?_, hdisj⟩
    · exact lt_of_le_of_ne bot_le (Ne.symm hne')
    · exact lt_of_le_of_ne bot_le (Ne.symm hspan)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  rw [Submodule.mem_colon_iff_le]
  have hkill : ∀ w : M, a ^ N • w = 0 := by
    intro w
    have hmem : a ^ N • w ∈ a ^ N • (⊤ : Submodule A M) :=
      Submodule.smul_mem_pointwise_smul w (a ^ N) ⊤ trivial
    rw [htop] at hmem
    simpa using hmem
  intro z hz
  rw [Submodule.mem_bot]
  obtain ⟨z₀, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z (a ^ (N + 1)) ⊤).mp hz
  rw [pow_succ', mul_smul, hkill, smul_zero]

/-- A proper irreducible submodule of a Noetherian module is primary — the textbook's reduction
to `M ⧸ Q`, then `isPrimarySubmodule_bot`. -/
theorem isPrimarySubmodule_of_isIrredSubmodule [IsNoetherian A M] {Q : Submodule A M}
    (hQ : Q ≠ ⊤) (h : IsIrredSubmodule Q) : IsPrimarySubmodule Q := by
  have hbotne : (⊥ : Submodule A (M ⧸ Q)) ≠ ⊤ := by
    intro heq
    obtain ⟨m, -, hm⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hQ)
    have h1 : Q.mkQ m ∈ (⊥ : Submodule A (M ⧸ Q)) := by
      rw [heq]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    exact hm ((mkQ_eq_zero_iff Q m).mp h1)
  have hbot : IsPrimarySubmodule (⊥ : Submodule A (M ⧸ Q)) :=
    isPrimarySubmodule_bot hbotne (isIrredSubmodule_bot_quotient h)
  refine ⟨hQ, ?_⟩
  intro a x hax
  by_cases hx : x ∈ Q
  · exact Or.inl hx
  right
  have hx0 : Q.mkQ x ≠ 0 := fun h0 => hx ((mkQ_eq_zero_iff Q x).mp h0)
  have hmk : a • Q.mkQ x = 0 := by
    rw [← map_smul]
    exact (mkQ_eq_zero_iff Q (a • x)).mpr hax
  rcases hbot.2 a (Q.mkQ x) (by rwa [Submodule.mem_bot]) with hzx | ⟨n, hn, hmem⟩
  · exact absurd hzx hx0
  · refine ⟨n, hn, ?_⟩
    rw [Submodule.mem_colon_iff_le]
    have h2 : a ^ n • (⊤ : Submodule A (M ⧸ Q)) ≤ ⊥ :=
      (Submodule.mem_colon_iff_le).mp hmem
    have hkill : ∀ w : M, a ^ n • w ∈ Q := by
      intro w
      have hmem' : a ^ n • (Q.mkQ w) ∈ a ^ n • (⊤ : Submodule A (M ⧸ Q)) :=
        Submodule.smul_mem_pointwise_smul (Q.mkQ w) (a ^ n) ⊤ trivial
      have h0 : a ^ n • (Q.mkQ w) = 0 := by
        have h3 := h2 hmem'
        rwa [Submodule.mem_bot] at h3
      rw [← map_smul] at h0
      exact (mkQ_eq_zero_iff Q (a ^ n • w)).mp h0
    intro m hm
    obtain ⟨m₀, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m (a ^ n) ⊤).mp hm
    exact hkill m₀

/-- Cross-check of the previous result through Mathlib: on proper submodules the book's notion of
irreducibility is `InfIrred`, and Mathlib's `InfIrred.isPrimary` proves the same statement by the
same kernel-chain argument. -/
theorem isPrimary_of_isIrredSubmodule [IsNoetherian A M] {Q : Submodule A M} (hQ : Q ≠ ⊤)
    (h : IsIrredSubmodule Q) : Q.IsPrimary :=
  ((isIrredSubmodule_iff_infIrred hQ).mp h).isPrimary

/-! ### Exercise 7.17 -/

/-- Exercise 7.17 in Mathlib's language: every `N ≠ M` is a nonempty finite intersection of
primary submodules. -/
theorem exists_finset_inf_isPrimary [IsNoetherian A M] (N : Submodule A M) (hN : N ≠ ⊤) :
    ∃ s : Finset (Submodule A M), s.Nonempty ∧ s.inf id = N ∧ ∀ J ∈ s, J.IsPrimary := by
  obtain ⟨s, hne, hinf, hI⟩ := exists_finset_inf_isIrredSubmodule_of_ne_top hN
  exact ⟨s, hne, hinf, fun J hJ => isPrimary_of_isIrredSubmodule (hI J hJ).2 (hI J hJ).1⟩

/-- **Atiyah–Macdonald, Chapter VII, Exercise 17.**  Let `A` be a ring and `M` a Noetherian
`A`-module; then every submodule `N ≠ M` of `M` has a primary decomposition, i.e. it is a
nonempty finite intersection of primary submodules of `M` (primary in the book's sense). -/
theorem solution [IsNoetherian A M] (N : Submodule A M) (hN : N ≠ ⊤) :
    ∃ s : Finset (Submodule A M), s.Nonempty ∧ s.inf id = N ∧ ∀ J ∈ s, IsPrimarySubmodule J := by
  obtain ⟨s, hne, hinf, hI⟩ := exists_finset_inf_isIrredSubmodule_of_ne_top hN
  exact ⟨s, hne, hinf, fun J hJ => isPrimarySubmodule_of_isIrredSubmodule (hI J hJ).2 (hI J hJ).1⟩

/-! ### The reduced form -/

/-- The decomposition can moreover be taken minimal (reduced): the radicals `√(Qᵢ : M)` are
distinct and no `Qᵢ` contains the intersection of the others, as in the Chapter 4 theory. -/
theorem exists_isMinimalPrimaryDecomposition [IsNoetherian A M] (N : Submodule A M) :
    ∃ s : Finset (Submodule A M), N.IsMinimalPrimaryDecomposition s :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker A M) N

end AtiyahMcdonald69.Ex_7_17

#print axioms AtiyahMcdonald69.Ex_7_17.solution
#print axioms AtiyahMcdonald69.Ex_7_17.exists_finset_inf_isIrredSubmodule
#print axioms AtiyahMcdonald69.Ex_7_17.exists_finset_inf_isIrredSubmodule_of_ne_top
#print axioms AtiyahMcdonald69.Ex_7_17.isIrredSubmodule_bot_quotient
#print axioms AtiyahMcdonald69.Ex_7_17.isPrimarySubmodule_bot
#print axioms AtiyahMcdonald69.Ex_7_17.isPrimarySubmodule_of_isIrredSubmodule
#print axioms AtiyahMcdonald69.Ex_7_17.isPrimary_of_isIrredSubmodule
#print axioms AtiyahMcdonald69.Ex_7_17.isPrimarySubmodule_iff
#print axioms AtiyahMcdonald69.Ex_7_17.exists_finset_inf_isPrimary
#print axioms AtiyahMcdonald69.Ex_7_17.exists_isMinimalPrimaryDecomposition
