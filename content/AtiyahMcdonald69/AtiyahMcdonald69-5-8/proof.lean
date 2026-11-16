/-
# Atiyah–Macdonald (1969), Chapter 5, Exercise 8

## The exercise

Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter V (Integral Dependence and
Valuations), Exercise 8:

* (i) Let `A` be a subring of an integral domain `B`, and let `C` be the integral closure of `A` in
  `B`.  Let `f`, `g` be monic polynomials in `B[x]` such that `f * g ∈ C[x]`.  Then `f`, `g` are in
  `C[x]`.
* (ii) Prove the same result without assuming that `B` (or `A`) is an integral domain.

## Encoding

* "`A` is a subring of `B`" is encoded as a commutative algebra structure `Algebra A B` together
  with `Function.Injective (algebraMap A B)`.
* "`C` is the integral closure of `A` in `B`" is `integralClosure A B : Subalgebra A B`; its
  carrier is the set of elements of `B` integral over `A`.
* "`p ∈ C[x]`" is encoded as `p ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)`, i.e. `p`
  is the image of a polynomial with coefficients in `C`.  See `mem_lifts_iff_coeff` for the
  equivalent coefficient-wise form.

The injectivity hypothesis `_hAB` in `ex_5_8_i` and `ex_5_8_ii` is not used by the proofs: the
results are proved for an arbitrary algebra `A → B`, and the hypothesis is kept only because the
book states the exercise for a subring `A` of `B`.  In particular nothing is silently assumed.

## Main results

* `AtiyahMcdonald69.Ex_5_8.ex_5_8_i` — part (i) (`B` an integral domain).
* `AtiyahMcdonald69.Ex_5_8.ex_5_8_ii` — part (ii) (arbitrary commutative rings).
* `AtiyahMcdonald69.Ex_5_8.ex_5_8_i_coeff`, `...ex_5_8_ii_coeff` — the coefficient-wise forms.
* `AtiyahMcdonald69.Ex_5_8.mem_lifts_of_monic_dvd` — the divisor form: a monic divisor in `B[x]` of
  a monic polynomial in `C[x]` lies in `C[x]` (the form used in Exercise 5.9).
* `AtiyahMcdonald69.Ex_5_8.monic_hypothesis_necessary` — the monicity hypothesis is essential.
* `AtiyahMcdonald69.Ex_5_8.mem_of_add_mem_of_mul_mem` — the consequence for linear factors:
  if `b + c` and `b * c` lie in `C` then `b, c` lie in `C` (a near-converse of (5.7)).

## Proofs

Part (i) follows the argument sketched in the book: pass to a field `Ω` containing `B`
(`Ω := AlgebraicClosure (FractionRing B)`) in which `f` and `g` split; every root is a root of the
monic polynomial `f * g` over `C`, hence integral over `C`; the coefficients of `f` and `g` are
elementary symmetric functions of the roots, hence integral over `C` (Mathlib's
`Polynomial.isIntegral_coeff_of_factors` is precisely this step); finally an element of `B`
integral over `C` lies in `C`, since `C` is integrally closed in `B`.

Part (ii) replaces the field `Ω` by the splitting ring `S ⊇ B` produced by
`Polynomial.Monic.exists_splits_map` (an iterated adjunction of roots of monic polynomials); the
remainder of the argument is identical.  Both parts share the generic lemmas
`isIntegral_coeff_map_of_splits` and `coeff_mem_integralClosure_of_splits`, which are stated for an
arbitrary commutative `B`-algebra `S` in which `f` splits.

A third, independent proof of the general statement is `ex_5_8_ii_coeff'`, which feeds the monic
divisor `f` of the monic polynomial `f * g` over `C` directly into
`Polynomial.isIntegral_coeff_of_dvd`.
-/
import Mathlib

open Polynomial

namespace AtiyahMcdonald69.Ex_5_8

set_option autoImplicit false

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-! ### Basic interface for "`p ∈ C[x]`" -/

/-- For `C = integralClosure A B`, membership of `p : B[X]` in `C[x]` (i.e. in the image of `C[X]`)
is equivalent to all coefficients of `p` lying in `C`. -/
theorem mem_lifts_iff_coeff (p : B[X]) :
    p ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) ↔
      ∀ i, p.coeff i ∈ integralClosure A B := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  constructor
  · rintro h i
    obtain ⟨y, hy⟩ := h i
    rw [← hy]
    exact y.2
  · intro h i
    exact ⟨⟨_, h i⟩, rfl⟩

/-- A monic polynomial in `C[x]` is the image of a monic polynomial over `C`. -/
theorem exists_monic_lift (p : B[X]) (hp : p.Monic)
    (h : p ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) :
    ∃ P : (↥(integralClosure A B))[X], P.Monic ∧
      P.map (algebraMap ↥(integralClosure A B) B) = p := by
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts p).mp h
  exact ⟨P, Polynomial.monic_of_injective (FaithfulSMul.algebraMap_injective _ _)
    (hP.symm ▸ hp), hP⟩

/-- A root of a monic polynomial over `C` (in any commutative `C`-algebra) is integral over `C`. -/
theorem isIntegral_of_isRoot_map {S : Type*} [CommRing S]
    [Algebra ↥(integralClosure A B) S] {P : (↥(integralClosure A B))[X]} (hP : P.Monic) {x : S}
    (hx : (P.map (algebraMap ↥(integralClosure A B) S)).IsRoot x) :
    IsIntegral ↥(integralClosure A B) x :=
  ⟨P, hP, by rwa [eval₂_eq_eval_map]⟩

/-! ### The splitting step

Let `S` be a commutative `B`-algebra, compatible with the `C`-algebra structure, in which `f`
splits into linear factors.  Since `f * g` is a monic polynomial over `C`, every root of `f` in `S`
is integral over `C`; the coefficients of `f` are elementary symmetric functions of those roots,
hence integral over `C` as well. -/

/-- **Splitting step.**  If `f` splits in a commutative `B`-algebra `S` (compatible with `C`) and
`f * g` is a monic polynomial over `C`, then the coefficients of `f`, viewed in `S`, are integral
over `C`. -/
theorem isIntegral_coeff_map_of_splits {S : Type*} [CommRing S] [Algebra B S]
    [Algebra ↥(integralClosure A B) S]
    (hcomm : algebraMap ↥(integralClosure A B) S =
      (algebraMap B S).comp (algebraMap ↥(integralClosure A B) B))
    {f g : B[X]} (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B))
    (hsplit : (f.map (algebraMap B S)).Splits) (i : ℕ) :
    IsIntegral ↥(integralClosure A B) ((f.map (algebraMap B S)).coeff i) := by
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift (f * g) (hf.mul hg) hfg
  have hmap : P.map (algebraMap ↥(integralClosure A B) S) = (f * g).map (algebraMap B S) := by
    conv_rhs => rw [← hPmap]
    rw [Polynomial.map_map, ← hcomm]
  have hroots : ∀ x : S, (f.map (algebraMap B S)).IsRoot x →
      IsIntegral ↥(integralClosure A B) x := by
    intro x hx
    refine isIntegral_of_isRoot_map (P := P) hP ?_
    show (P.map (algebraMap ↥(integralClosure A B) S)).eval x = 0
    rw [hmap, Polynomial.map_mul (f := algebraMap B S) (p := f) (q := g), eval_mul,
      show (map (algebraMap B S) f).eval x = 0 from hx, zero_mul]
  exact Polynomial.isIntegral_coeff_of_factors (f.map (algebraMap B S))
    (by rw [(hf.map _).leadingCoeff]; exact isIntegral_one) hsplit hroots i

/-- Descent: if the image of the coefficient `f.coeff i` in a ring `S` containing `B` is integral
over `C`, then `f.coeff i` itself is integral over `C`. -/
theorem isIntegral_coeff_of_isIntegral_coeff_map {S : Type*} [CommRing S] [Algebra B S]
    [Algebra ↥(integralClosure A B) S]
    (hcomm : algebraMap ↥(integralClosure A B) S =
      (algebraMap B S).comp (algebraMap ↥(integralClosure A B) B))
    (hinj : Function.Injective (algebraMap B S)) (f : B[X]) (i : ℕ)
    (h : IsIntegral ↥(integralClosure A B) ((f.map (algebraMap B S)).coeff i)) :
    IsIntegral ↥(integralClosure A B) (f.coeff i) := by
  rw [Polynomial.coeff_map] at h
  have h' : (algebraMap ↥(integralClosure A B) S).IsIntegralElem (algebraMap B S (f.coeff i)) := h
  rw [hcomm] at h'
  exact (RingHom.IsIntegralElem.map_iff (f := algebraMap ↥(integralClosure A B) B)
    (g := algebraMap B S) hinj).mp h'

/-- Combining the splitting step with descent: the coefficients of `f` are integral over `C`,
hence lie in `C` because `C` is integrally closed in `B`. -/
theorem coeff_mem_integralClosure_of_splits {S : Type*} [CommRing S] [Algebra B S]
    [Algebra ↥(integralClosure A B) S]
    (hcomm : algebraMap ↥(integralClosure A B) S =
      (algebraMap B S).comp (algebraMap ↥(integralClosure A B) B))
    (hinj : Function.Injective (algebraMap B S)) {f g : B[X]} (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B))
    (hsplit : (f.map (algebraMap B S)).Splits) (i : ℕ) :
    f.coeff i ∈ integralClosure A B :=
  isIntegral_trans (R := A) (A := ↥(integralClosure A B)) (B := B) _
    (isIntegral_coeff_of_isIntegral_coeff_map hcomm hinj f i
      (isIntegral_coeff_map_of_splits hcomm hf hg hfg hsplit i))

/-! ### Part (i): `B` is an integral domain

Here `Ω := AlgebraicClosure (FractionRing B)` is a field containing `B` in which `f` splits. -/

section Domain

variable [IsDomain B]

/-- **Exercise 5.8 (i), coefficient form.**  `f`, `g` monic in `B[x]`, `B` an integral domain,
`f * g ∈ C[x]`: every coefficient of `f` lies in `C`. -/
theorem ex_5_8_i_coeff (f g : B[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) (i : ℕ) :
    f.coeff i ∈ integralClosure A B := by
  let Ω := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B Ω) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) Ω]
    exact (algebraMap (FractionRing B) Ω).injective.comp
      (IsFractionRing.injective B (FractionRing B))
  have hsplit : (f.map (algebraMap B Ω)).Splits := IsAlgClosed.splits _
  exact coeff_mem_integralClosure_of_splits rfl hinj hf hg hfg hsplit i

/-- **Exercise 5.8 (i).**  Let `A` be a subring of an integral domain `B` and let `C` be the
integral closure of `A` in `B`.  If `f`, `g` are monic polynomials in `B[x]` with `f * g ∈ C[x]`,
then `f`, `g ∈ C[x]`. -/
theorem ex_5_8_i (_hAB : Function.Injective (algebraMap A B)) (f g : B[X]) (hf : f.Monic)
    (hg : g.Monic) (h : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) :
    f ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) ∧
      g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) := by
  refine ⟨(mem_lifts_iff_coeff f).mpr fun i => ex_5_8_i_coeff f g hf hg h i,
    (mem_lifts_iff_coeff g).mpr fun i => ?_⟩
  rw [mul_comm] at h
  exact ex_5_8_i_coeff g f hg hf h i

end Domain

/-! ### Part (ii): arbitrary commutative rings

The field `Ω` is replaced by any commutative ring `S` containing `B` over which `f` splits; such an
`S` exists by `Polynomial.Monic.exists_splits_map`, which adjoins roots one at a time. -/

/-- **Exercise 5.8 (ii), coefficient form.**  `B` is an arbitrary commutative ring; `f`, `g` monic
in `B[x]` with `f * g ∈ C[x]`: every coefficient of `f` lies in `C`. -/
theorem ex_5_8_ii_coeff (f g : B[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) (i : ℕ) :
    f.coeff i ∈ integralClosure A B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · -- a subsingleton ring: the claim is trivial
    have h0 : f.coeff i = 0 := @Subsingleton.elim B hB _ _
    rw [h0]
    exact (integralClosure A B).zero_mem
  -- a ring `S ⊇ B` in which `f` splits into linear factors
  obtain ⟨S, _, _, _, _, _, hsplit⟩ := hf.exists_splits_map (R := B)
  exact coeff_mem_integralClosure_of_splits rfl (FaithfulSMul.algebraMap_injective B S)
    hf hg hfg hsplit i

/-- **Exercise 5.8 (ii).**  Let `A` be a subring of a commutative ring `B` and let `C` be the
integral closure of `A` in `B`.  If `f`, `g` are monic polynomials in `B[x]` with `f * g ∈ C[x]`,
then `f`, `g ∈ C[x]`.  No integral-domain hypothesis is needed. -/
theorem ex_5_8_ii (_hAB : Function.Injective (algebraMap A B)) (f g : B[X]) (hf : f.Monic)
    (hg : g.Monic) (h : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) :
    f ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) ∧
      g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) := by
  refine ⟨(mem_lifts_iff_coeff f).mpr fun i => ex_5_8_ii_coeff f g hf hg h i,
    (mem_lifts_iff_coeff g).mpr fun i => ?_⟩
  rw [mul_comm] at h
  exact ex_5_8_ii_coeff g f hg hf h i

/-! ### An independent proof of the general statement

`Polynomial.isIntegral_coeff_of_dvd` states that the coefficients of a monic divisor of a monic
polynomial over `C` are integral over `C`.  Applying it to the divisor `f` of `f * g` gives a second,
shorter proof of `ex_5_8_ii_coeff`, independent of the splitting-ring construction above. -/

/-- **Exercise 5.8 (ii), coefficient form, second proof.** -/
theorem ex_5_8_ii_coeff' (f g : B[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) (i : ℕ) :
    f.coeff i ∈ integralClosure A B := by
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift (f * g) (hf.mul hg) hfg
  have hint : IsIntegral ↥(integralClosure A B) (f.coeff i) :=
    Polynomial.isIntegral_coeff_of_dvd P f hP hf ⟨g, hPmap⟩ i
  exact isIntegral_trans (R := A) (A := ↥(integralClosure A B)) (B := B) _ hint

/-- **Exercise 5.8, divisor form.**  A monic divisor in `B[x]` of a monic polynomial in `C[x]` lies
in `C[x]`.  This is the form in which Exercise 5.9 uses the result. -/
theorem mem_lifts_of_monic_dvd {p q : B[X]} (hp : p.Monic) (hq : q.Monic)
    (hpl : p ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B)) (hdvd : q ∣ p) :
    q ∈ Polynomial.lifts (algebraMap ↥(integralClosure A B) B) := by
  obtain ⟨r, rfl⟩ := hdvd
  have hr : r.Monic := Monic.of_mul_monic_left hq hp
  exact (mem_lifts_iff_coeff q).mpr fun i => ex_5_8_ii_coeff q r hq hr hpl i

/-! ### Linear factors: a near-converse of (5.7)

Taking `f = x - b` and `g = x - c` in Exercise 5.8 gives: if `b + c` and `b * c` lie in `C`, then
`b` and `c` lie in `C`.  This is the remark following Exercise 5.8 in the standard solutions. -/

/-- If `b + c` and `b * c` both lie in `C = integralClosure A B`, then `b` and `c` lie in `C`. -/
theorem mem_of_add_mem_of_mul_mem (b c : B) (hadd : b + c ∈ integralClosure A B)
    (hmul : b * c ∈ integralClosure A B) :
    b ∈ integralClosure A B ∧ c ∈ integralClosure A B := by
  have hcoeff : ∀ i, ((X - C b) * (X - C c)).coeff i ∈ integralClosure A B := by
    intro i
    have hpoly : (X - C b) * (X - C c) = X ^ 2 - C (b + c) * X + C (b * c) := by
      simp only [map_add, map_mul]
      ring
    rw [hpoly]
    match i with
    | 0 => simpa using hmul
    | 1 => simpa using neg_mem hadd
    | 2 => simp
    | (k + 3) => simp [Polynomial.coeff_X_pow]
  have hfg : (X - C b) * (X - C c) ∈
      Polynomial.lifts (algebraMap ↥(integralClosure A B) B) :=
    (mem_lifts_iff_coeff _).mpr hcoeff
  have hb : (-b) ∈ integralClosure A B := by
    have := ex_5_8_ii_coeff (X - C b) (X - C c) (monic_X_sub_C b) (monic_X_sub_C c) hfg 0
    simpa using this
  have hc : (-c) ∈ integralClosure A B := by
    have hfg' : (X - C c) * (X - C b) ∈
        Polynomial.lifts (algebraMap ↥(integralClosure A B) B) := by
      rwa [mul_comm]
    have := ex_5_8_ii_coeff (X - C c) (X - C b) (monic_X_sub_C c) (monic_X_sub_C b) hfg' 0
    simpa using this
  exact ⟨neg_mem_iff.mp hb, neg_mem_iff.mp hc⟩

/-! ### The monicity hypothesis is essential

Exercise 5.8 assumes that both `f` and `g` are monic, and this cannot be dropped: over
`A = ℤ ⊆ B = ℚ` the monic polynomial `X - 1/2` multiplied by the non-monic constant `2` has
coefficients in `C = ℤ`, while `X - 1/2` does not lie in `C[x]`.  (Exchanging the roles of `f` and
`g` gives the same counterexample to dropping the monicity of `f`.) -/

/-- `1/2` is not integral over `ℤ`, i.e. `1/2 ∉ C` for `A = ℤ ⊆ B = ℚ`. -/
theorem half_not_mem_integralClosure : (-(1 / 2) : ℚ) ∉ integralClosure ℤ ℚ := by
  intro h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h : IsIntegral ℤ (-(1 / 2) : ℚ))
  have h2 : ((2 * n : ℤ) : ℚ) = ((-1 : ℤ) : ℚ) := by
    push_cast
    have hn' : (n : ℚ) = -(1 / 2) := by simpa using hn
    linarith
  have h3 : (2 * n : ℤ) = -1 := by exact_mod_cast h2
  omega

/-- The monicity assumption on `g` in Exercise 5.8 is essential. -/
theorem monic_hypothesis_necessary :
    ∃ f g : ℚ[X], f.Monic ∧
      f * g ∈ Polynomial.lifts (algebraMap ↥(integralClosure ℤ ℚ) ℚ) ∧
      f ∉ Polynomial.lifts (algebraMap ↥(integralClosure ℤ ℚ) ℚ) := by
  refine ⟨X - C (1 / 2 : ℚ), C 2, monic_X_sub_C _, ?_, ?_⟩
  · -- `(X - 1/2) * 2 = 2X - 1` has coefficients in `ℤ`
    have hpoly : (X - C (1 / 2 : ℚ)) * C 2 = C 2 * X - C 1 := by
      rw [sub_mul, ← C_mul]
      norm_num
    rw [hpoly]
    refine (Polynomial.mem_lifts _).mpr ⟨C (⟨(2 : ℚ),
      algebraMap_mem (integralClosure ℤ ℚ) (2 : ℤ)⟩ : ↥(integralClosure ℤ ℚ)) * X -
      C (⟨(1 : ℚ), algebraMap_mem (integralClosure ℤ ℚ) (1 : ℤ)⟩ :
        ↥(integralClosure ℤ ℚ)), ?_⟩
    simp
  · -- but `X - 1/2` itself is not in `C[x]`
    intro hmem
    apply half_not_mem_integralClosure
    have h1 : (X - C (1 / 2 : ℚ)).coeff 0 ∈ integralClosure ℤ ℚ :=
      (mem_lifts_iff_coeff _).mp hmem 0
    have hcoeff : (X - C (1 / 2 : ℚ)).coeff 0 = -(1 / 2) := by simp
    rwa [hcoeff] at h1

/-! ### Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_5_8.ex_5_8_i
#print axioms AtiyahMcdonald69.Ex_5_8.ex_5_8_ii
#print axioms AtiyahMcdonald69.Ex_5_8.ex_5_8_i_coeff
#print axioms AtiyahMcdonald69.Ex_5_8.ex_5_8_ii_coeff
#print axioms AtiyahMcdonald69.Ex_5_8.ex_5_8_ii_coeff'
#print axioms AtiyahMcdonald69.Ex_5_8.mem_lifts_of_monic_dvd
#print axioms AtiyahMcdonald69.Ex_5_8.mem_of_add_mem_of_mul_mem
#print axioms AtiyahMcdonald69.Ex_5_8.monic_hypothesis_necessary

end AtiyahMcdonald69.Ex_5_8
