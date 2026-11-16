/-
Copyright: formalization for the Atiyah–Macdonald formalization project.

# Atiyah–Macdonald (1969), Chapter 11, Exercise 11.3

## The exercise (original statement)

Chapter 11, p. 126:

> **Exercise 11.3.** Extend (11.25) to non-algebraically-closed fields.

The referenced Theorem (11.25) of the book is the dimension theorem for affine varieties over an
algebraically closed field: for an irreducible variety `V` over an algebraically closed field `k`,
the local dimension of `V` at any point equals `dim V`.  In the algebraic form used by the book
(`A = A(V)`, the coordinate ring, which is a finitely generated `k`-algebra and an integral domain;
points of `V` correspond to maximal ideals `m` of `A`; the local dimension at that point is
`dim A_m = ht m`, and `dim V = dim A`), the statement reads:

  for *any* field `k`, any finitely generated `k`-algebra `A` which is an integral domain, and any
  maximal ideal `m` of `A`,
    `dim A_m = dim A = trdeg_k K(A)`,  where `K(A) = Frac A`.

Every hypothesis of (11.25) is preserved: `k` is an arbitrary field (the point of the exercise),
`A` is a finitely generated `k`-algebra (`Algebra.FiniteType`), `A` is an integral domain
(`IsDomain`), and `m` is a maximal ideal (`Ideal.IsMaximal`).  No further hypothesis is added:
`k` algebraically closed is *not* assumed.  The transcendence degree is formalized both as
`Algebra.trdeg k A` (supremum of the cardinalities of `k`-algebraically independent subsets of `A`)
and, matching the book's `trdeg_k K(A)`, as `Algebra.trdeg k (FractionRing A)`; the two agree for
domains (`trdeg_eq_trdeg_fractionRing`).

## Formal content

* `height_le_height_comap_of_isIntegral` : in an integral extension, `ht P ≤ ht (P ∩ R)`
  (incomparability, chain contraction).
* `height_comap_le_height_of_isIntegrallyClosed` : if moreover `R` is integrally closed (a UFD, in
  particular a polynomial ring over a field), then `ht (P ∩ R) ≤ ht P` (going down, chain lifting).
* `height_eq_of_isMaximal_mvPolynomial` : every maximal ideal of `k[X₁,…,X_d]` has height `d`.
* `local_height_eq_trdeg` : `ht m = trdeg_k A` for `m` maximal — the essential content (both
  inequalities; the reverse one `trdeg_k A ≤ ht m` is the substance here).
* `trdeg_eq_trdeg_fractionRing` : `trdeg_k A = trdeg_k K(A)`.
* `ringKrullDim_eq_trdeg`, `local_ringKrullDim_eq_trdeg`, `local_dim_eq_dim`, `solution` : the
  dimension theorem in the form of (11.25), extended to arbitrary fields.
* `ringKrullDim_eq_trdeg_fractionRing`, `local_ringKrullDim_eq_trdeg_fractionRing` : the same in the
  book's notation `trdeg_k K(A)`.
* `local_dim_eq_dim_of_isAlgClosed` : (11.25) itself, as a special case.

The proof follows the natural solution and the book's hints: Noether normalization
(`exists_finite_inj_algHom_of_fg`) gives `B = k[x₁,…,x_d] ⊆ A` finite with `d = trdeg_k A`;
contracting a maximal ideal of `A` gives a maximal ideal of `B`; `B`, being a polynomial ring over a
field, is a UFD, hence integrally closed, so heights are preserved by this finite integral extension
(both inequalities: incomparability and going down); and the height of a maximal ideal of a
polynomial ring over an *arbitrary* field is computed by induction on the number of variables, the
non-algebraically-closed case of the Zariski lemma entering through the statement that contractions
of maximal ideals along `R → R[X]` are maximal for a Jacobson ring `R`.
-/

import Mathlib

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Polynomial

namespace AtiyahMcdonald69.Ex_11_3

/-! ## 1. Heights of primes in integral extensions -/

section IntegralHeight

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Incomparability, in height form.** -/
theorem height_le_height_comap_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal S) [hP : P.IsPrime] :
    P.height ≤ (P.comap (algebraMap R S)).height := by
  have hf : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro x y hxy
    exact Ideal.IsIntegral.comap_lt_comap hxy
  have h := Order.height_le_height_apply_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) hf
    (⟨P, hP⟩ : PrimeSpectrum S)
  have h1 : Order.height (⟨P, hP⟩ : PrimeSpectrum S) = P.height :=
    (PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩).symm
  have h2 : Order.height ((PrimeSpectrum.comap (algebraMap R S)) ⟨P, hP⟩) =
      (P.comap (algebraMap R S)).height :=
    (PrimeSpectrum.height_eq_orderHeight _).symm
  rw [h1, h2] at h
  exact h

/-- **Going down, in height form.** -/
theorem height_comap_le_height_of_isIntegrallyClosed [Algebra.IsIntegral R S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S] [FaithfulSMul R S] [IsNoetherianRing R]
    (P : Ideal S) [P.IsPrime] :
    (P.comap (algebraMap R S)).height ≤ P.height := by
  haveI : Algebra.HasGoingDown R S := inferInstance
  obtain ⟨l, hlast, hlen⟩ :=
    Ideal.exists_ltSeries_length_eq_height (P.comap (algebraMap R S))
  have hlo : P.LiesOver (RelSeries.last l).asIdeal := by
    rw [hlast]
    exact ⟨rfl⟩
  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P (lo := hlo)
  have h1 : (((L.length : ℕ)) : ℕ∞) ≤ Order.height (RelSeries.last L) := Order.length_le_height_last
  rw [← PrimeSpectrum.height_eq_orderHeight] at h1
  rw [hLlast] at h1
  calc (P.comap (algebraMap R S)).height = ((l.length : ℕ) : ℕ∞) := hlen.symm
    _ = ((L.length : ℕ) : ℕ∞) := by rw [hLlen]
    _ ≤ P.height := h1

/-- For an integral extension of domains over an integrally closed Noetherian base, the height of a
prime equals the height of its contraction. -/
theorem height_eq_height_comap_of_isIntegrallyClosed [Algebra.IsIntegral R S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S] [FaithfulSMul R S] [IsNoetherianRing R]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.comap (algebraMap R S)).height :=
  le_antisymm (height_le_height_comap_of_isIntegral P)
    (height_comap_le_height_of_isIntegrallyClosed P)

end IntegralHeight

/-! ## 2. Heights of maximal ideals of a polynomial ring over a field -/

section PolyHeight

/-- The constants ideal of a maximal ideal of `R[X]` is strictly contained in it. -/
theorem map_C_lt_of_isMaximal {R : Type*} [CommRing R] [Nontrivial R]
    (P : Ideal R[X]) [hP : P.IsMaximal] :
    (P.comap (C : R →+* R[X])).map (C : R →+* R[X]) < P := by
  set q : Ideal R := P.comap (C : R →+* R[X]) with hq
  have hle : q.map (C : R →+* R[X]) ≤ P := Ideal.map_le_iff_le_comap.mpr le_rfl
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hq_ne_top : q ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ q := by rw [h]; simp
    have h2 : C (1 : R) ∈ P := Ideal.mem_comap.mp h1
    refine hP.ne_top ((Ideal.eq_top_iff_one P).mpr ?_)
    simpa using h2
  have hX_notMem : (X : R[X]) ∉ P := by
    rw [← heq]
    intro hmem
    refine hq_ne_top ((Ideal.eq_top_iff_one q).mpr ?_)
    have h1 : (1 : R) ∈ q := by
      have := (Ideal.mem_map_C_iff.mp hmem) 1
      simpa using this
    exact h1
  -- `P ⊔ (X) = ⊤`, so `1 = a + X * c` with `a ∈ P`
  have hlt : P < P ⊔ Ideal.span ({(X : R[X])} : Set R[X]) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq'
    exact hX_notMem (heq' ▸ (le_sup_right : Ideal.span ({(X : R[X])} : Set R[X]) ≤
      P ⊔ Ideal.span ({(X : R[X])} : Set R[X])) (Ideal.subset_span (Set.mem_singleton _)))
  have htop : P ⊔ Ideal.span ({(X : R[X])} : Set R[X]) = ⊤ := hP.1.2 _ hlt
  have hone : (1 : R[X]) ∈ P ⊔ Ideal.span ({(X : R[X])} : Set R[X]) := by
    rw [htop]; simp
  rw [Submodule.mem_sup] at hone
  obtain ⟨a, ha, b, hb, hab⟩ := hone
  rw [Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  have hmem : ((X : R[X]) * c - 1) ∈ P := by
    have : (X : R[X]) * c - 1 = -a := by rw [← hab]; ring
    rw [this]
    exact neg_mem ha
  rw [← heq] at hmem
  have hcoeff : ((-1 : R)) ∈ q := by
    have := (Ideal.mem_map_C_iff.mp hmem) 0
    simpa using this
  refine hq_ne_top ((Ideal.eq_top_iff_one q).mpr ?_)
  simpa using neg_mem hcoeff

/-- **Height of maximal ideals of a polynomial ring.** -/
theorem height_eq_of_isMaximal_mvPolynomial (k : Type*) [Field k] (d : ℕ)
    (N : Ideal (MvPolynomial (Fin d) k)) (hN : N.IsMaximal) : N.height = (d : ℕ∞) := by
  induction d with
  | zero =>
    haveI : N.IsMaximal := hN
    refine le_antisymm ?_ (zero_le)
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := N)
    have hdim : ringKrullDim (MvPolynomial (Fin 0) k) = ((0 : ℕ) : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  | succ d ih =>
    haveI : N.IsMaximal := hN
    let e := MvPolynomial.finSuccEquiv k d
    set P : Ideal (Polynomial (MvPolynomial (Fin d) k)) :=
      Ideal.map (e : MvPolynomial (Fin (d + 1)) k →+* Polynomial (MvPolynomial (Fin d) k)) N
      with hPdef
    haveI hPmax : P.IsMaximal := by
      rw [hPdef]
      exact hN.map_bijective (e : MvPolynomial (Fin (d + 1)) k →+* Polynomial (MvPolynomial (Fin d) k)) e.bijective
    have hPN : P.height = N.height := by
      rw [hPdef]
      exact RingEquiv.height_map (e.toRingEquiv) N
    have hp : (P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k))).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    haveI : (P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k))).IsMaximal := hp
    have hunder : P.under (MvPolynomial (Fin d) k) =
        P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k)) := by
      rw [Ideal.under_def, Polynomial.algebraMap_eq]
    haveI : P.LiesOver (P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k))) :=
      ⟨hunder.symm⟩
    have hstep : P.height =
        (P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k))).height + 1 :=
      Polynomial.height_eq_height_add_one _ P
    rw [← hPN, hstep,
      ih (P.comap (C : MvPolynomial (Fin d) k →+* Polynomial (MvPolynomial (Fin d) k))) hp]
    push_cast
    ring

end PolyHeight


universe u

/-! ## 3. The dimension theorem for finitely generated algebras over a field -/

section Main

variable (k A : Type u) [Field k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- **Exercise 11.3, essential content (local form).** -/
theorem local_height_eq_trdeg (m : Ideal A) [m.IsMaximal] :
    m.height = (Algebra.trdeg k A).toENat := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  algebraize [g.toRingHom]
  haveI hfin : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  haveI hFaith : FaithfulSMul (MvPolynomial (Fin s) k) A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact hginj
  haveI hInt : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    Algebra.IsIntegral.of_finite _ _
  have hmc : (m.comap (algebraMap (MvPolynomial (Fin s) k) A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hheight : m.height = (m.comap (algebraMap (MvPolynomial (Fin s) k) A)).height :=
    height_eq_height_comap_of_isIntegrallyClosed m
  have hK : (m.comap (algebraMap (MvPolynomial (Fin s) k) A)).height = (s : ℕ∞) :=
    height_eq_of_isMaximal_mvPolynomial k s _ hmc
  have hsplit := trdeg_add_eq (R := k) (S := MvPolynomial (Fin s) k) (A := A)
  have hzero : Algebra.trdeg (MvPolynomial (Fin s) k) A = 0 := trdeg_eq_zero
  have hpoly : Algebra.trdeg k (MvPolynomial (Fin s) k) = (s : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin]
    simp
  rw [hzero, add_zero, hpoly] at hsplit
  calc m.height = (m.comap (algebraMap (MvPolynomial (Fin s) k) A)).height := hheight
    _ = (s : ℕ∞) := hK
    _ = (Algebra.trdeg k A).toENat := by simp [← hsplit]

/-- **Exercise 11.3 (global form).** -/
theorem ringKrullDim_eq_trdeg :
    ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    haveI : m.IsMaximal := hm
    rw [local_height_eq_trdeg k A m]
  · obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal A) bot_ne_top
    haveI : m.IsMaximal := hm
    calc ((Algebra.trdeg k A).toENat : WithBot ℕ∞) = (m.height : WithBot ℕ∞) := by
          rw [local_height_eq_trdeg k A m]
      _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime

/-- **Exercise 11.3, local form with local rings.** -/
theorem local_ringKrullDim_eq_trdeg (m : Ideal A) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    local_height_eq_trdeg k A m]

/-- **(11.25) extended: local dimension equals global dimension** at every point. -/
theorem local_dim_eq_dim (m : Ideal A) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim A ∧
      ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) :=
  ⟨by rw [local_ringKrullDim_eq_trdeg k A m, ringKrullDim_eq_trdeg k A],
    ringKrullDim_eq_trdeg k A⟩

/-- **Atiyah–Macdonald, Exercise 11.3.** -/
theorem solution :
    (∀ (m : Ideal A) (_ : m.IsMaximal),
        ringKrullDim (Localization.AtPrime m) = ringKrullDim A) ∧
      ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) ∧
      (∀ (m : Ideal A) (_ : m.IsMaximal), m.height = (Algebra.trdeg k A).toENat) := by
  refine ⟨?_, ringKrullDim_eq_trdeg k A, ?_⟩
  · intro m hm
    haveI : m.IsMaximal := hm
    exact (local_dim_eq_dim k A m).1
  · intro m hm
    haveI : m.IsMaximal := hm
    exact local_height_eq_trdeg k A m

end Main


/-! ## 3b. Transcendence degree of the fraction field (the book's `trdeg_k K(A)`) -/

section FractionField

variable (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The transcendence degree of a domain over a field equals the transcendence degree of its field
of fractions: every element of `Frac A` is a root of a linear polynomial over `A`. -/
theorem trdeg_eq_trdeg_fractionRing :
    Algebra.trdeg k (FractionRing A) = Algebra.trdeg k A := by
  have h := trdeg_add_eq (R := k) (S := A) (A := FractionRing A)
  have hzero : Algebra.trdeg A (FractionRing A) = 0 := by
    haveI halg : Algebra.IsAlgebraic A (FractionRing A) := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, y, _hy, hxy⟩ := IsFractionRing.div_surjective A z
      rw [← hxy, div_eq_mul_inv]
      exact (isAlgebraic_algebraMap x).mul (IsAlgebraic.inv (isAlgebraic_algebraMap y))
    exact trdeg_eq_zero
  rw [hzero, add_zero] at h
  exact h.symm

/-- **Exercise 11.3 in the book's own notation.**  For a finitely generated `k`-algebra `A` which is
an integral domain and a maximal ideal `m`, the local dimension at `m` equals the transcendence
degree `trdeg_k K(A)` of the field of fractions. -/
theorem local_ringKrullDim_eq_trdeg_fractionRing [Algebra.FiniteType k A] (m : Ideal A)
    [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) =
      ((Algebra.trdeg k (FractionRing A)).toENat : WithBot ℕ∞) := by
  rw [local_ringKrullDim_eq_trdeg k A m, trdeg_eq_trdeg_fractionRing k A]

/-- **Exercise 11.3 in the book's own notation**, global form. -/
theorem ringKrullDim_eq_trdeg_fractionRing [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k (FractionRing A)).toENat : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_trdeg k A, trdeg_eq_trdeg_fractionRing k A]

end FractionField


/-! ## 4. Consequences and consistency checks -/

section Sanity

/-- **(11.25) itself.**  Over an algebraically closed field the book's Theorem (11.25) is the special
case of the extension to arbitrary fields. -/
theorem local_dim_eq_dim_of_isAlgClosed (K A : Type u) [Field K] [IsAlgClosed K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim A ∧
      ringKrullDim A = ((Algebra.trdeg K A).toENat : WithBot ℕ∞) :=
  local_dim_eq_dim K A m

/-- Consistency check: the dimension of affine `n`-space over any field is `n`, recovered from the
dimension theorem (it is also `MvPolynomial.ringKrullDim_of_isNoetherianRing`). -/
theorem ringKrullDim_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  have hmain := ringKrullDim_eq_trdeg k (MvPolynomial (Fin n) k)
  have h : Algebra.trdeg k (MvPolynomial (Fin n) k) = (n : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin]
    simp
  rw [h] at hmain
  rw [hmain]
  simp

end Sanity

end AtiyahMcdonald69.Ex_11_3

/-! ## Axiom check for the main declarations -/

#print axioms AtiyahMcdonald69.Ex_11_3.height_le_height_comap_of_isIntegral
#print axioms AtiyahMcdonald69.Ex_11_3.height_comap_le_height_of_isIntegrallyClosed
#print axioms AtiyahMcdonald69.Ex_11_3.height_eq_height_comap_of_isIntegrallyClosed
#print axioms AtiyahMcdonald69.Ex_11_3.map_C_lt_of_isMaximal
#print axioms AtiyahMcdonald69.Ex_11_3.height_eq_of_isMaximal_mvPolynomial
#print axioms AtiyahMcdonald69.Ex_11_3.trdeg_eq_trdeg_fractionRing
#print axioms AtiyahMcdonald69.Ex_11_3.local_height_eq_trdeg
#print axioms AtiyahMcdonald69.Ex_11_3.ringKrullDim_eq_trdeg
#print axioms AtiyahMcdonald69.Ex_11_3.local_ringKrullDim_eq_trdeg
#print axioms AtiyahMcdonald69.Ex_11_3.local_dim_eq_dim
#print axioms AtiyahMcdonald69.Ex_11_3.solution
#print axioms AtiyahMcdonald69.Ex_11_3.ringKrullDim_eq_trdeg_fractionRing
#print axioms AtiyahMcdonald69.Ex_11_3.local_ringKrullDim_eq_trdeg_fractionRing
#print axioms AtiyahMcdonald69.Ex_11_3.local_dim_eq_dim_of_isAlgClosed
#print axioms AtiyahMcdonald69.Ex_11_3.ringKrullDim_mvPolynomial
