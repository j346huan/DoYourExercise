import Mathlib

/-!
# Atiyah–Macdonald (1969), Chapter 4, Exercise 4.6

The book's exercise (Chapter 4, §"Exercises", no. 6): *Let `X` be an infinite compact Hausdorff
space, `C(X)` the ring of real-valued continuous functions on `X`. Is the zero ideal decomposable
in this ring?*

The answer is **no** (`solution`): for every infinite compact Hausdorff `X` there are no `n : ℕ`
and primary ideals `q 0, …, q (n-1)` of `C(X, ℝ)` with `⊥ = ⨅ i, q i`. Equivalently
(`not_decomposable_finset`), `⊥` is not a finite intersection of primary ideals, i.e. the ring
`C(X, ℝ)` is not a Lasker ring (`not_isLasker`). The converse holds as well
(`decomposable_of_finite`): for finite `X` the zero ideal *is* decomposable, as the intersection
of the finitely many prime ideals `m x`, `x : X` — so the infinitude hypothesis is essential.

## Proof route (the book's own route)

* For `x : X` the ideal `m x = {f | f x = 0}` is the kernel of evaluation at `x`, which is
  surjective onto the field `ℝ`; so `m x` is a maximal ideal (the maximality part of Chapter 1,
  Exercise 26).
* A primary ideal is contained in at most one of the ideals `m x` (`primary_le_m_unique`):
  if `q ≤ m x` and `q ≤ m y` with `x ≠ y`, Urysohn's lemma produces `f, g` with `f x ≠ 0`,
  `g y ≠ 0` and `f * g = 0` (`exists_mul_eq_zero`); from `f * g ∈ q` we get `f ∈ q` or
  `g ∈ q.radical`, and either alternative forces a contradiction at `x`, resp. at `y`.
* If `⊥ = ⨅ i, q i` were a primary decomposition, then `m x ⊇ ⨅ i, q i` forces `m x ⊇ q i` for
  some `i` (`exists_component_le_m`: a prime ideal containing an intersection of ideals contains
  one of them); assigning to `x` such an index `i` gives an injection `X → Fin n`, so `X` would
  be finite — contradicting the hypothesis.

Everything is proved from `import Mathlib` alone; the main declarations depend only on the
standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace AtiyahMcdonald69.Ex_4_6

open ContinuousMap

section Basic

variable {X : Type*} [TopologicalSpace X]

/-- The ideal of continuous real-valued functions vanishing at a point `x`. -/
def m (x : X) : Ideal C(X, ℝ) := RingHom.ker (ContinuousMap.evalAlgHom ℝ ℝ x)

@[simp]
theorem mem_m {x : X} {f : C(X, ℝ)} : f ∈ m x ↔ f x = 0 := by
  simp [m]

/-- Evaluation at a point is surjective (constant functions), so `m x` is a maximal ideal. -/
theorem eval_surjective (x : X) : Function.Surjective (ContinuousMap.evalAlgHom ℝ ℝ x) :=
  fun r => ⟨ContinuousMap.const (α := X) r, by simp⟩

theorem isMaximal_m (x : X) : (m x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (eval_surjective x)

theorem isPrime_m (x : X) : (m x).IsPrime := RingHom.ker_isPrime _

theorem radical_le_m {q : Ideal C(X, ℝ)} {x : X} (hq : q ≤ m x) : q.radical ≤ m x :=
  (isPrime_m x).radical_le_iff.mpr hq

/-- Every prime ideal `m x` contains one of the primary components of a decomposition of `⊥`. -/
theorem exists_component_le_m {s : Finset (Ideal C(X, ℝ))} (hbot : s.inf id = ⊥) (x : X) :
    ∃ q ∈ s, q ≤ m x := by
  have hle : s.inf id ≤ m x := by rw [hbot]; exact bot_le
  exact (isPrime_m x).inf_le'.mp hle

/-- The intersection of all the prime ideals `m x`, for `x` ranging over `X`, is the zero ideal
(in any topological space: a continuous function is zero iff it vanishes everywhere). -/
theorem iInf_m_eq_bot : ⨅ x : X, m x = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  ext x
  exact mem_m.mp (Ideal.mem_iInf.mp hf x)

end Basic

section CompactHausdorff

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Urysohn's lemma, in the form needed here: distinct points of a compact Hausdorff space are
separated by two continuous functions with disjoint supports. -/
theorem exists_mul_eq_zero {x y : X} (hxy : x ≠ y) :
    ∃ f g : C(X, ℝ), f x ≠ 0 ∧ g y ≠ 0 ∧ f * g = 0 := by
  classical
  -- First separate the two points by a continuous function with values in `[0, 1]`.
  obtain ⟨φ, hφx, hφy, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x))
      (isClosed_singleton (x := y)) (by simpa [Set.disjoint_singleton_left] using hxy)
  -- The two disjoint open sets where `φ < 1/2`, resp. `φ > 1/2`, separate `x` and `y`.
  set U : Set X := φ ⁻¹' Set.Iio (1 / 2 : ℝ) with hU
  set V : Set X := φ ⁻¹' Set.Ioi (1 / 2 : ℝ) with hV
  have hUopen : IsOpen U := isOpen_Iio.preimage φ.continuous
  have hVopen : IsOpen V := isOpen_Ioi.preimage φ.continuous
  have hxU : x ∈ U := by
    have h : φ x = 0 := hφx (Set.mem_singleton x)
    rw [hU, Set.mem_preimage, Set.mem_Iio, h]
    norm_num
  have hyV : y ∈ V := by
    have h : φ y = 1 := hφy (Set.mem_singleton y)
    rw [hV, Set.mem_preimage, Set.mem_Ioi, h]
    norm_num
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    rw [hU, Set.mem_preimage, Set.mem_Iio] at hzU
    rw [hV, Set.mem_preimage, Set.mem_Ioi] at hzV
    linarith
  -- Bump function supported in `U` and taking the value `1` at `x`.
  obtain ⟨f, hf0, hfx, -⟩ :=
    exists_continuous_zero_one_of_isClosed hUopen.isClosed_compl
      (isClosed_singleton (x := x)) (by simpa [Set.disjoint_singleton_right] using hxU)
  -- Bump function supported in `V` and taking the value `1` at `y`.
  obtain ⟨g, hg0, hgy, -⟩ :=
    exists_continuous_zero_one_of_isClosed hVopen.isClosed_compl
      (isClosed_singleton (x := y)) (by simpa [Set.disjoint_singleton_right] using hyV)
  refine ⟨f, g, ?_, ?_, ?_⟩
  · have : f x = 1 := hfx (Set.mem_singleton x)
    rw [this]; norm_num
  · have : g y = 1 := hgy (Set.mem_singleton y)
    rw [this]; norm_num
  · ext z
    simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply]
    by_cases hz : z ∈ U
    · have hzV : z ∉ V := fun h => Set.disjoint_left.mp hdisj hz h
      have hg0' : g z = 0 := hg0 (by
        rw [Set.mem_compl_iff]
        exact hzV)
      rw [hg0', mul_zero]
    · have hf0' : f z = 0 := hf0 (by
        rw [Set.mem_compl_iff]
        exact hz)
      rw [hf0', zero_mul]

/-- Distinct points give distinct ideals `m x`. -/
theorem m_injective : Function.Injective (m (X := X)) := by
  intro x y hxy
  by_contra h
  obtain ⟨φ, hφx, hφy, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x))
      (isClosed_singleton (x := y)) (by simpa [Set.disjoint_singleton_left] using h)
  have hxm : φ ∈ m x := by
    rw [mem_m]
    exact hφx (Set.mem_singleton x)
  have hym : φ ∉ m y := by
    rw [mem_m]
    rw [hφy (Set.mem_singleton y)]
    norm_num
  exact hym (hxy ▸ hxm)

/-- A primary ideal is contained in at most one of the prime ideals `m x`. -/
theorem primary_le_m_unique {q : Ideal C(X, ℝ)} (hq : q.IsPrimary) {x y : X}
    (hx : q ≤ m x) (hy : q ≤ m y) : x = y := by
  by_contra hxy
  obtain ⟨f, g, hfx, hgy, hfg⟩ := exists_mul_eq_zero (X := X) hxy
  have hfgq : f * g ∈ q := by rw [hfg]; exact q.zero_mem
  have hradx : q.radical ≤ m x := radical_le_m hx
  have hrady : q.radical ≤ m y := radical_le_m hy
  rcases (Ideal.isPrimary_iff.mp hq).2 hfgq with hfq | hgr
  · have : f x = 0 := mem_m.mp (hx hfq)
    exact hfx this
  · have : g y = 0 := mem_m.mp (hrady hgr)
    exact hgy this

section Main

variable [Infinite X]

/-- **Atiyah–Macdonald, Exercise 4.6 (finset form).** In the ring `C(X, ℝ)` of real-valued
continuous functions on an infinite compact Hausdorff space, the zero ideal is not a finite
intersection of primary ideals. -/
theorem not_decomposable_finset :
    ¬ ∃ s : Finset (Ideal C(X, ℝ)), (∀ q ∈ s, q.IsPrimary) ∧ s.inf id = ⊥ := by
  rintro ⟨s, hs, hbot⟩
  -- Every prime `m x` contains one of the primary components.
  choose q hqs hqm using exists_component_le_m (X := X) (s := s) hbot
  -- Distinct points give distinct components, so `X` injects into the finite set `s`.
  let g : X → ↥(s : Set (Ideal C(X, ℝ))) := fun x => ⟨q x, by simpa using hqs x⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    have hqe : q x = q y := congrArg Subtype.val hxy
    have hx : q x ≤ m x := hqm x
    rw [hqe] at hx
    exact primary_le_m_unique (hs (q y) (by simpa using hqs y)) hx (hqm y)
  exact ‹Infinite X›.not_finite (@Finite.of_injective X ↥(s : Set (Ideal C(X, ℝ)))
    s.finite_toSet.to_subtype g hinj)

/-- **Atiyah–Macdonald, Exercise 4.6.** The zero ideal of `C(X, ℝ)`, for `X` an infinite compact
Hausdorff space, is not decomposable: there are no `n : ℕ` and primary ideals `q 0, …, q (n-1)`
with `⊥ = ⨅ i, q i`. -/
theorem solution :
    ¬ ∃ (n : ℕ) (q : Fin n → Ideal C(X, ℝ)), (∀ i, (q i).IsPrimary) ∧ ⨅ i, q i = ⊥ := by
  rintro ⟨n, q, hq, hbot⟩
  refine not_decomposable_finset (X := X) ⟨Finset.univ.image q, ?_, ?_⟩
  · intro q' hq'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq'
    exact hq i
  · rw [Finset.inf_image, Finset.inf_eq_iInf]
    simpa using hbot

/-- Restated in Mathlib's language of Lasker rings: `C(X, ℝ)`, for `X` an infinite compact
Hausdorff space, is *not* a Lasker ring. -/
theorem not_isLasker : ¬ IsLasker C(X, ℝ) C(X, ℝ) := by
  intro h
  obtain ⟨s, hbot, hprim⟩ := h ⊥
  exact not_decomposable_finset (X := X) ⟨s, fun q hq => hprim hq, hbot⟩

end Main

end CompactHausdorff

section FiniteX

variable {X : Type*} [TopologicalSpace X]

/-- For a *finite* topological space, the zero ideal of `C(X, ℝ)` *is* decomposable, as the
intersection of the finitely many prime (hence primary) ideals `m x`. So the hypothesis that `X`
is infinite in Exercise 4.6 is essential. -/
theorem decomposable_of_finite [Finite X] :
    ∃ s : Finset (Ideal C(X, ℝ)), (∀ q ∈ s, q.IsPrimary) ∧ s.inf id = ⊥ := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  refine ⟨Finset.univ.image (fun i : Fin n => m (e.symm i)), ?_, ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact (isPrime_m (e.symm i)).isPrimary
  · rw [Finset.inf_image, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, id_eq]
    rw [show (⨅ i ∈ (Finset.univ : Finset (Fin n)), m (e.symm i))
        = ⨅ i : Fin n, m (e.symm i) by simp]
    refine le_antisymm (fun f hf => ?_) bot_le
    rw [Submodule.mem_bot]
    ext x
    have hx : f ∈ m (e.symm (e x)) := Ideal.mem_iInf.mp hf (e x)
    rw [Equiv.symm_apply_apply] at hx
    exact mem_m.mp hx

end FiniteX


end AtiyahMcdonald69.Ex_4_6
/-! ### Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_4_6.solution
#print axioms AtiyahMcdonald69.Ex_4_6.not_decomposable_finset
#print axioms AtiyahMcdonald69.Ex_4_6.not_isLasker
#print axioms AtiyahMcdonald69.Ex_4_6.primary_le_m_unique
#print axioms AtiyahMcdonald69.Ex_4_6.exists_mul_eq_zero
#print axioms AtiyahMcdonald69.Ex_4_6.decomposable_of_finite
