/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 7, Exercise 10.

Reference: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-7-10>

Statement (book): *Let `M` be a Noetherian `A`-module. Show that `M[x]` (Chapter 2,
Exercise 6) is a Noetherian `A[x]`-module.*

Formal translation.  `A[x]` is `Polynomial A`; `M[x]` is `PolynomialModule A M`
(`PolynomialModule R M` is by definition the type of finitely supported families
`ℕ →₀ M`, i.e. formal sums `∑ mᵢ xⁱ`, and it carries the canonical `R[X]`-module
structure `PolynomialModule.polynomialModule` in which `X` acts by shifting
coefficients, exactly the multiplication of Chapter 2, Exercise 6).  Hence the
exercise is the statement `IsNoetherian A M → IsNoetherian A[X] (PolynomialModule A M)`.

Proof: the standard leading-coefficient argument, which specializes the proof of the
Hilbert basis theorem (7.5) to the case `M = A`.  Let `N ⊆ M[x]` be an `A[x]`-submodule,
let `P ⊆ M` be the `A`-submodule of all top coefficients of elements of `N`; `P` is
finitely generated over `A`, say by `m₁,…,mₙ`.  Choose `pᵢ ∈ N` with top coefficient
`mᵢ` at degree `rᵢ`, let `r = max rᵢ` and let `N'` be the `A[x]`-span of the `pᵢ`.
Subtracting suitable `A`-multiples of `x^{d-rᵢ}pᵢ` from any `f ∈ N` of degree `d ≥ r`
lowers its degree, so `f - g ∈ N` has degree `< r` for some `g ∈ N'`.  The elements of
`N` of degree `< r` form a submodule of the finitely generated `A`-module
`M ⊕ Mx ⊕ ⋯ ⊕ Mx^{r-1}`, hence are finitely generated over `A`.  Therefore `N` is
finitely generated over `A[x]`.
-/
import Mathlib

open Polynomial PolynomialModule

namespace AtiyahMcdonald69.Ex_7_10

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-! ### The degree of an element of `M[x]` -/

/-- The degree of a polynomial with coefficients in `M` (with `deg 0 = 0`). -/
noncomputable def deg (p : PolynomialModule A M) : ℕ := p.coeff.support.sup id

lemma coeff_eq_zero_of_deg_lt {p : PolynomialModule A M} {k : ℕ} (h : deg p < k) :
    p.coeff k = 0 := by
  by_contra hk
  have hmem : k ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hk
  have hle : k ≤ deg p := Finset.le_sup (f := id) hmem
  omega

lemma deg_le_of_vanishing {p : PolynomialModule A M} {d : ℕ}
    (h : ∀ k, d < k → p.coeff k = 0) : deg p ≤ d := by
  refine Finset.sup_le (f := id) fun b hb => ?_
  by_contra hbd
  exact absurd (h b (Nat.lt_of_not_le hbd)) (Finsupp.mem_support_iff.mp hb)

@[simp] lemma deg_zero : deg (0 : PolynomialModule A M) = 0 := by simp [deg]

/-- The functional "coefficient of `xᵏ`" as an additive homomorphism. -/
def coeffHom (k : ℕ) : PolynomialModule A M →+ M where
  toFun p := p.coeff k
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coeff_sub (x y : PolynomialModule A M) (k : ℕ) :
    (x - y).coeff k = x.coeff k - y.coeff k :=
  map_sub (coeffHom k) x y

lemma coeff_smul (a : A) (x : PolynomialModule A M) (k : ℕ) :
    (a • x).coeff k = a • x.coeff k := by
  have h := congrFun (congrArg (fun f : ℕ →₀ M => (⇑f : ℕ → M))
    ((PolynomialModule.coeffLinearEquiv (R := A) (S := A) (M := M)).map_smul a x)) k
  exact h

lemma eq_zero_of_forall_coeff_eq_zero {p : PolynomialModule A M}
    (h : ∀ k, p.coeff k = 0) : p = 0 :=
  PolynomialModule.ext (Finsupp.ext fun k => by simpa using h k)

/-! ### The `A`-submodule of top coefficients occurring in a submodule of `M[x]` -/

/-- `leadCoeff N` is the `A`-submodule of `M` consisting of all coefficients that occur as
the top (i.e. highest) coefficient of some element of `N`. -/
def leadCoeff (N : Submodule (Polynomial A) (PolynomialModule A M)) : Submodule A M where
  carrier := {m | ∃ p ∈ N, ∃ d : ℕ, p.coeff d = m ∧ ∀ k, d < k → p.coeff k = 0}
  zero_mem' := ⟨0, N.zero_mem, 0, by simp⟩
  add_mem' := by
    rintro m m' ⟨p, hp, d, hd, hv⟩ ⟨q, hq, d', hd', hv'⟩
    rcases le_total d d' with h | h
    · refine ⟨monomial (d' - d) (1 : A) • p + q, N.add_mem (N.smul_mem _ hp) hq, d', ?_, ?_⟩
      · have h1 : (monomial (d' - d) (1 : A) • p).coeff d' = p.coeff d := by
          rw [PolynomialModule.monomial_smul_apply, if_pos (by omega),
            show d' - (d' - d) = d from by omega, one_smul]
        have h2 : (monomial (d' - d) (1 : A) • p + q).coeff d'
            = (monomial (d' - d) (1 : A) • p).coeff d' + q.coeff d' := by simp
        rw [h2, h1, hd, hd']
      · intro k hk
        have h2 : (monomial (d' - d) (1 : A) • p + q).coeff k
            = (monomial (d' - d) (1 : A) • p).coeff k + q.coeff k := by simp
        rw [h2, PolynomialModule.monomial_smul_apply, if_pos (by omega),
          hv _ (by omega), smul_zero, hv' k hk, add_zero]
    · refine ⟨monomial (d - d') (1 : A) • q + p, N.add_mem (N.smul_mem _ hq) hp, d, ?_, ?_⟩
      · have h1 : (monomial (d - d') (1 : A) • q).coeff d = q.coeff d' := by
          rw [PolynomialModule.monomial_smul_apply, if_pos (by omega),
            show d - (d - d') = d' from by omega, one_smul]
        have h2 : (monomial (d - d') (1 : A) • q + p).coeff d
            = (monomial (d - d') (1 : A) • q).coeff d + p.coeff d := by simp
        rw [h2, h1, hd', hd, add_comm]
      · intro k hk
        have h2 : (monomial (d - d') (1 : A) • q + p).coeff k
            = (monomial (d - d') (1 : A) • q).coeff k + p.coeff k := by simp
        rw [h2, PolynomialModule.monomial_smul_apply, if_pos (by omega),
          hv' _ (by omega), smul_zero, hv k hk, add_zero]
  smul_mem' := by
    rintro a m ⟨p, hp, d, hd, hv⟩
    refine ⟨monomial 0 a • p, N.smul_mem _ hp, d, ?_, ?_⟩
    · rw [PolynomialModule.monomial_smul_apply, if_pos (Nat.zero_le d), Nat.sub_zero, hd]
    · intro k hk
      rw [PolynomialModule.monomial_smul_apply, if_pos (Nat.zero_le k), Nat.sub_zero, hv k hk,
        smul_zero]

lemma mem_leadCoeff {N : Submodule (Polynomial A) (PolynomialModule A M)} {m : M} :
    m ∈ leadCoeff N ↔
      ∃ p ∈ N, ∃ d : ℕ, p.coeff d = m ∧ ∀ k, d < k → p.coeff k = 0 :=
  Iff.rfl

/-- Polynomials whose coefficients vanish in all degrees `≥ r`. -/
def degreeLE (r : ℕ) : Submodule A (PolynomialModule A M) where
  carrier := {f | ∀ k : ℕ, r ≤ k → f.coeff k = 0}
  zero_mem' := by intro k _; rfl
  add_mem' := by
    intro x y hx hy k hk
    simp [hx k hk, hy k hk]
  smul_mem' := by
    intro a x hx k hk
    rw [coeff_smul, hx k hk, smul_zero]

lemma coeff_monomial_smul_top {p : PolynomialModule A M} {r d : ℕ} {a : A} {m : M}
    (hrd : r ≤ d) (hd : p.coeff r = m) :
    (monomial (d - r) a • p).coeff d = a • m := by
  rw [PolynomialModule.monomial_smul_apply, if_pos (by omega),
    show d - (d - r) = r from by omega, hd]

lemma coeff_monomial_smul_above {p : PolynomialModule A M} {r d : ℕ} {a : A}
    (hrd : r ≤ d) (hv : ∀ k, r < k → p.coeff k = 0) {k : ℕ} (hk : d < k) :
    (monomial (d - r) a • p).coeff k = 0 := by
  rw [PolynomialModule.monomial_smul_apply, if_pos (by omega), hv _ (by omega), smul_zero]

/-- A set spanning a submodule over `A` also spans over `A[x]`. -/
lemma span_le_span_tower (s : Set (PolynomialModule A M)) :
    Submodule.span A s ≤ (Submodule.span (Polynomial A) s).restrictScalars A :=
  Submodule.span_le.mpr fun _ hx => Submodule.subset_span hx

/-- **Atiyah–Macdonald, Exercise 7.10**, in the form "every submodule is finitely
generated". -/
theorem fg_of_submodule [IsNoetherian A M]
    (N : Submodule (Polynomial A) (PolynomialModule A M)) : N.FG := by
  -- The module of top coefficients is finitely generated over `A`.
  obtain ⟨n, mf, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (leadCoeff N))
  -- Choose, for every generator, an element of `N` having it as top coefficient.
  have hmem : ∀ i : Fin n,
      ∃ p : PolynomialModule A M, p ∈ N ∧ ∃ d : ℕ, p.coeff d = mf i ∧
        ∀ k, d < k → p.coeff k = 0 := fun i => mem_leadCoeff.mp (by
          rw [← hspan]
          exact Submodule.subset_span (Set.mem_range_self i))
  choose p hpN rest using hmem
  choose r hr hrv using rest
  -- The degree bound.
  let r₀ : ℕ := Finset.univ.sup r
  have hrle : ∀ i : Fin n, r i ≤ r₀ := fun i => Finset.le_sup (f := r) (Finset.mem_univ i)
  -- The submodule generated by the chosen elements.
  let N' : Submodule (Polynomial A) (PolynomialModule A M) :=
    Submodule.span (Polynomial A) (Set.range p)
  have hpN' : ∀ i : Fin n, p i ∈ N' := fun i => Submodule.subset_span (Set.mem_range_self i)
  have hN'le : N' ≤ N := Submodule.span_le.mpr (Set.range_subset_iff.mpr hpN)
  -- Key approximation: every element of `N` is congruent modulo `N'` to an element of
  -- degree `< r₀`.
  have key : ∀ f ∈ N, ∃ g ∈ N', ∀ k : ℕ, r₀ ≤ k → (f - g).coeff k = 0 := by
    suffices H : ∀ d : ℕ, ∀ f ∈ N, deg f ≤ d →
        ∃ g ∈ N', ∀ k : ℕ, r₀ ≤ k → (f - g).coeff k = 0 from
      fun f hf => H (deg f) f hf le_rfl
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf hdf
      by_cases hsmall : deg f < r₀
      · refine ⟨0, N'.zero_mem, fun k hk => ?_⟩
        simp only [sub_zero]
        exact coeff_eq_zero_of_deg_lt (by omega)
      · have hsmall' : r₀ ≤ deg f := not_lt.mp hsmall
        -- the top coefficient of `f` lies in `P`
        have hm : f.coeff (deg f) ∈ leadCoeff N :=
          mem_leadCoeff.mpr ⟨f, hf, deg f, rfl, fun k hk => coeff_eq_zero_of_deg_lt hk⟩
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (by
          rw [hspan]; exact hm)
        -- the approximating element
        let g₀ : PolynomialModule A M := ∑ i : Fin n, monomial (deg f - r i) (c i) • p i
        have hg₀N : g₀ ∈ N := by
          apply N.sum_mem
          intro i _
          exact N.smul_mem _ (hpN i)
        have hg₀N' : g₀ ∈ N' := by
          apply Submodule.sum_mem
          intro i _
          exact N'.smul_mem _ (hpN' i)
        have htop : g₀.coeff (deg f) = f.coeff (deg f) := by
          have h1 : g₀.coeff (deg f)
              = ∑ i : Fin n, (monomial (deg f - r i) (c i) • p i).coeff (deg f) := by
            simp [g₀, PolynomialModule.coeff_sum]
          rw [h1]
          calc ∑ i : Fin n, (monomial (deg f - r i) (c i) • p i).coeff (deg f)
              = ∑ i : Fin n, c i • mf i :=
                Finset.sum_congr rfl fun i _ =>
                  coeff_monomial_smul_top (le_trans (hrle i) hsmall') (hr i)
            _ = f.coeff (deg f) := hc
        have habove : ∀ k, deg f < k → g₀.coeff k = 0 := by
          intro k hk
          have h1 : g₀.coeff k
              = ∑ i : Fin n, (monomial (deg f - r i) (c i) • p i).coeff k := by
            simp [g₀, PolynomialModule.coeff_sum]
          rw [h1]
          exact Finset.sum_eq_zero fun i _ =>
            coeff_monomial_smul_above (le_trans (hrle i) hsmall') (hrv i) hk
        rcases Nat.eq_zero_or_pos (deg f) with h0 | hpos
        · -- `f` itself is the approximation
          refine ⟨g₀, hg₀N', fun k hk => ?_⟩
          have hall : ∀ j, (f - g₀).coeff j = 0 := by
            intro j
            rcases lt_or_eq_of_le (show deg f ≤ j from by omega) with hj | hj
            · rw [coeff_sub, habove j hj, sub_zero]
              exact coeff_eq_zero_of_deg_lt hj
            · rw [coeff_sub, ← hj, htop, sub_self]
          rw [eq_zero_of_forall_coeff_eq_zero hall]
          simp
        · -- subtract and use the induction hypothesis
          obtain ⟨g₁, hg₁N', hg₁⟩ := ih (d - 1) (by omega) (f - g₀) (N.sub_mem hf hg₀N) (by
            refine deg_le_of_vanishing fun k hk => ?_
            rcases lt_or_eq_of_le (show deg f ≤ k from by omega) with hk' | hk'
            · rw [coeff_sub, habove k hk', sub_zero]
              exact coeff_eq_zero_of_deg_lt hk'
            · rw [coeff_sub, ← hk', htop, sub_self])
          refine ⟨g₀ + g₁, N'.add_mem hg₀N' hg₁N', fun k hk => ?_⟩
          rw [show f - (g₀ + g₁) = (f - g₀) - g₁ from by abel]
          exact hg₁ k hk
  -- The bounded-degree part of `N` is finitely generated over `A`.
  let A₀ : Submodule A (PolynomialModule A M) := N.restrictScalars A ⊓ degreeLE r₀
  let φ : PolynomialModule A M →ₗ[A] (Fin r₀ → M) :=
    { toFun := fun f i => f.coeff i
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro a x; funext i; simp [coeff_smul] }
  have hinj : ∀ x ∈ A₀, ∀ y ∈ A₀, φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hsub : x - y ∈ A₀ := A₀.sub_mem hx hy
    have hz : x - y = 0 := by
      refine eq_zero_of_forall_coeff_eq_zero fun k => ?_
      by_cases hk : k < r₀
      · have h1 : φ (x - y) ⟨k, hk⟩ = 0 := by rw [map_sub, hxy, sub_self]; rfl
        simpa [φ] using h1
      · exact hsub.2 k (by omega)
    exact sub_eq_zero.mp hz
  obtain ⟨s, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (A₀.map φ))
  have hgsM : ∀ j : Fin s, gs j ∈ A₀.map φ := fun j => by
    rw [← hgs]; exact Submodule.subset_span (Set.mem_range_self j)
  choose ps hpsA hpsφ using fun j => (Submodule.mem_map (f := φ)).mp (hgsM j)
  have hA₀le : A₀ ≤ Submodule.span A (Set.range ps) := by
    intro f hf
    have hmem : φ f ∈ Submodule.span A (Set.range gs) := by
      rw [hgs]; exact Submodule.mem_map_of_mem hf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hmem
    have hsum : (∑ j : Fin s, c j • ps j) ∈ A₀ :=
      Submodule.sum_mem _ fun j _ => A₀.smul_mem _ (hpsA j)
    have hfeq : f = ∑ j : Fin s, c j • ps j := by
      refine hinj f hf _ hsum ?_
      have hφ : φ (∑ j : Fin s, c j • ps j) = ∑ j : Fin s, c j • gs j := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by simp [hpsφ j]
      rw [hφ]
      exact hc.symm
    rw [hfeq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- Assembly: `N` is generated by the two finite families.
  have hgen : ∀ f ∈ N, f ∈ Submodule.span (Polynomial A) (Set.range p ∪ Set.range ps) := by
    intro f hf
    obtain ⟨g, hgN', hgv⟩ := key f hf
    have hhN : f - g ∈ N := N.sub_mem hf (hN'le hgN')
    have hhA : f - g ∈ A₀ := ⟨hhN, fun k hk => hgv k hk⟩
    have hh : f - g ∈ Submodule.span (Polynomial A) (Set.range ps) := by
      have h1 : f - g ∈ (Submodule.span (Polynomial A) (Set.range ps)).restrictScalars A :=
        span_le_span_tower (Set.range ps) (hA₀le hhA)
      exact h1
    have _ : f - g ∈ (Submodule.span (Polynomial A) (Set.range ps)).restrictScalars A :=
      span_le_span_tower (Set.range ps) (hA₀le hhA)
    have hg : g ∈ Submodule.span (Polynomial A) (Set.range p) := hgN'
    have hg' : g ∈ Submodule.span (Polynomial A) (Set.range p ∪ Set.range ps) :=
      Submodule.span_mono Set.subset_union_left hg
    have hh' : f - g ∈ Submodule.span (Polynomial A) (Set.range p ∪ Set.range ps) :=
      Submodule.span_mono Set.subset_union_right hh
    rw [show f = g + (f - g) from by abel]
    exact Submodule.add_mem _ hg' hh'
  have hcle : Submodule.span (Polynomial A) (Set.range p ∪ Set.range ps) ≤ N := by
    refine Submodule.span_le.mpr ?_
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hpN i
    · exact (hpsA j).1
  have heq : N = Submodule.span (Polynomial A) (Set.range p ∪ Set.range ps) :=
    le_antisymm hgen hcle
  rw [heq]
  exact Submodule.fg_def.mpr ⟨_, (Set.finite_range p).union (Set.finite_range ps), rfl⟩

/-- **Atiyah–Macdonald, Exercise 7.10.** If `M` is a Noetherian `A`-module, then `M[x]`
is a Noetherian `A[x]`-module. -/
theorem solution (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [IsNoetherian A M] : IsNoetherian (Polynomial A) (PolynomialModule A M) :=
  isNoetherian_def.mpr fun N => fg_of_submodule N

/-! ### Consistency of the model with the book's construction -/

section Checks

open scoped TensorProduct

/-- Chapter 2, Exercise 6 of the book: `M[x]` is `A[x] ⊗[A] M`, compatibly with the
`A[x]`-module structure.  This confirms that `PolynomialModule A M` is the module
`M[x]` of the exercise. -/
example : Nonempty (PolynomialModule A M ≃ₗ[Polynomial A] (Polynomial A ⊗[A] M)) :=
  ⟨(PolynomialModule.polynomialTensorProductLEquivPolynomialModule A M).symm⟩

/-- The statement is instantiated by a concrete Noetherian module structure. -/
example : IsNoetherian (Polynomial ℤ) (PolynomialModule ℤ ℤ) := solution ℤ ℤ

end Checks

end AtiyahMcdonald69.Ex_7_10
