/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 5, Exercise 23.

Original statement (from `.scratch/reference/atiyah-macdonald-original.txt`):

  23. Let A be a ring. Show that the following are equivalent:
  i) Every prime ideal in A is an intersection of maximal ideals.
  ii) In every homomorphic image of A the nilradical is equal to the Jacobson radical.
  iii) Every prime ideal in A which is not maximal is equal to the intersection of the prime
  ideals which contain it strictly.
  A ring A with the three equivalent properties above is called a Jacobson ring.

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-5-23
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_5_23

open Ideal

universe u

/-- Condition (i): every prime ideal of `A` is the intersection of a set of maximal ideals. -/
def Cond_i (A : Type u) [CommRing A] : Prop :=
  ∀ P : Ideal A, P.IsPrime → ∃ M : Set (Ideal A), (∀ J ∈ M, J.IsMaximal) ∧ P = sInf M

/-- Condition (ii): in every homomorphic image `A ⧸ I` of `A` the nilradical is equal to the
Jacobson radical. -/
def Cond_ii (A : Type u) [CommRing A] : Prop :=
  ∀ I : Ideal A, Ideal.jacobson (⊥ : Ideal (A ⧸ I)) = nilradical (A ⧸ I)

/-- Condition (iii): every prime ideal of `A` which is not maximal is equal to the intersection of
the prime ideals which contain it strictly. -/
def Cond_iii (A : Type u) [CommRing A] : Prop :=
  ∀ P : Ideal A, P.IsPrime → ¬ P.IsMaximal → P = sInf {Q : Ideal A | P < Q ∧ Q.IsPrime}

/-- Condition (ii) spelled out in the form "in every homomorphic image of `A`": for every
surjective ring homomorphism `f : A →+* B`, the nilradical of `B` is equal to its Jacobson
radical.  (`Cond_ii` uses the quotients `A ⧸ I` instead; the two are equivalent, see
`cond_ii_iff_cond_ii'`.) -/
def Cond_ii' (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] (f : A →+* B), Function.Surjective f →
    Ideal.jacobson (⊥ : Ideal B) = nilradical B

variable {A : Type u} [CommRing A]

/-! ### Two general helpers on `sInf` of ideals -/

lemma sInf_sdiff_top (M : Set (Ideal A)) : sInf (M \ {⊤}) = sInf M := by
  refine le_antisymm ?_ (sInf_le_sInf Set.sdiff_subset)
  refine le_sInf fun J hJ => ?_
  by_cases h : J = ⊤
  · rw [h]
    exact le_top
  · exact sInf_le (show J ∈ M \ {⊤} from ⟨hJ, by simpa using h⟩)

/-- The nilradical is the radical of the zero ideal. -/
lemma nilradical_eq_radical_bot (R : Type u) [CommRing R] :
    nilradical R = (⊥ : Ideal R).radical := rfl

/-! ### (i) `↔` the Jacobson radical of every prime ideal is itself

The heart of (i) is that every prime ideal `P` satisfies `P.jacobson = P`; this is exactly
Mathlib's class `IsJacobsonRing`, whose defining condition (`I.radical = I.jacobson` for radical `I`)
Mathlib proves equivalent to `P.jacobson = P` for prime ideals. -/

lemma isJacobsonRing_of_cond_i (h : Cond_i A) : IsJacobsonRing A := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  obtain ⟨M, hM, hPinf⟩ := h P hP
  rw [hPinf]
  refine le_antisymm ?_ le_jacobson
  refine le_sInf fun J hJ => ?_
  have hJmax : J.IsMaximal := hM J hJ
  have hJac : J.jacobson = J := Ideal.jacobson_eq_self_of_isMaximal (I := J) (H := hJmax)
  calc (sInf M).jacobson ≤ J.jacobson := Ideal.jacobson_mono (sInf_le hJ)
    _ = J := hJac

lemma cond_i_of_isJacobsonRing (h : IsJacobsonRing A) : Cond_i A := by
  intro P hP
  obtain ⟨M, hM, hPinf⟩ := Ideal.eq_jacobson_iff_sInf_maximal.mp (h.out hP.isRadical)
  refine ⟨M \ {⊤}, ?_, hPinf.trans (sInf_sdiff_top M).symm⟩
  intro J hJ
  obtain ⟨hJM, hJtop⟩ := hJ
  rcases hM J hJM with hmax | htop
  · exact hmax
  · exact absurd htop hJtop

/-! ### (i) `↔` (ii) -/

lemma radical_eq_jacobson_of_cond_i (h : Cond_i A) :
    ∀ I : Ideal A, I.radical = I.jacobson := by
  intro I
  have hJac : IsJacobsonRing A := isJacobsonRing_of_cond_i h
  exact Ideal.radical_eq_jacobson (H := hJac) I

lemma cond_i_of_radical_eq_jacobson (h : ∀ I : Ideal A, I.radical = I.jacobson) :
    Cond_i A := by
  intro P hP
  have hPj : P.jacobson = P := by
    rw [← h P, hP.radical]
  obtain ⟨M, hM, hPinf⟩ := Ideal.eq_jacobson_iff_sInf_maximal.mp hPj
  refine ⟨M \ {⊤}, ?_, hPinf.trans (sInf_sdiff_top M).symm⟩
  intro J hJ
  obtain ⟨hJM, hJtop⟩ := hJ
  rcases hM J hJM with hmax | htop
  · exact hmax
  · exact absurd htop hJtop

/-- Condition (ii) is the same as: for every ideal `I`, the radical of `I` equals its Jacobson
radical.  This is Mathlib's `Ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot`
applied to each ideal. -/
lemma cond_ii_iff_radical_eq_jacobson :
    Cond_ii A ↔ ∀ I : Ideal A, I.radical = I.jacobson := by
  have key : ∀ I : Ideal A,
      ((⊥ : Ideal (A ⧸ I)).radical = (⊥ : Ideal (A ⧸ I)).jacobson ↔
        I.radical = I.jacobson) :=
    fun I => (Ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot (I := I)).symm
  constructor
  · intro h I
    exact (key I).mp (h I).symm
  · intro h I
    exact ((key I).mpr (h I)).symm

lemma cond_i_iff_cond_ii : Cond_i A ↔ Cond_ii A := by
  rw [cond_ii_iff_radical_eq_jacobson]
  exact ⟨radical_eq_jacobson_of_cond_i, cond_i_of_radical_eq_jacobson⟩

/-! ### (ii) for quotients `↔` (ii) for arbitrary homomorphic images -/

lemma eq_of_comap_eq {B : Type u} [CommRing B] {f : A →+* B} (hf : Function.Surjective f)
    {X Y : Ideal B} (h : Ideal.comap f X = Ideal.comap f Y) : X = Y := by
  rw [← Ideal.map_comap_of_surjective f hf X, ← Ideal.map_comap_of_surjective f hf Y, h]

lemma comap_jacobson_bot_eq_comap_nilradical {B : Type u} [CommRing B] {f : A →+* B}
    (hf : Function.Surjective f) (h : (RingHom.ker f).radical = (RingHom.ker f).jacobson) :
    Ideal.comap f (Ideal.jacobson (⊥ : Ideal B)) = Ideal.comap f (nilradical B) := by
  rw [Ideal.comap_jacobson_of_surjective hf, nilradical_eq_radical_bot, Ideal.comap_radical,
    ← RingHom.ker_eq_comap_bot, ← h]

lemma cond_ii_imp_cond_ii' (h : Cond_ii A) : Cond_ii' A := by
  intro B _ f hf
  have hrad : (RingHom.ker f).radical = (RingHom.ker f).jacobson :=
    (cond_ii_iff_radical_eq_jacobson.mp h) (RingHom.ker f)
  exact eq_of_comap_eq hf (comap_jacobson_bot_eq_comap_nilradical hf hrad)

lemma cond_ii'_imp_cond_ii (h : Cond_ii' A) : Cond_ii A := by
  intro I
  exact h (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Conditions (ii) for quotients and for arbitrary homomorphic images agree. -/
lemma cond_ii_iff_cond_ii' : Cond_ii A ↔ Cond_ii' A :=
  ⟨cond_ii_imp_cond_ii', cond_ii'_imp_cond_ii⟩

/-! ### (i) `⟹` (iii) -/

lemma cond_i_imp_cond_iii (h1 : Cond_i A) : Cond_iii A := by
  intro P hP hPnotmax
  obtain ⟨M, hMmax, hPinf⟩ := h1 P hP
  refine le_antisymm (le_sInf fun Q hQ => le_of_lt hQ.1) ?_
  calc sInf {Q : Ideal A | P < Q ∧ Q.IsPrime} ≤ sInf M := by
        refine le_sInf fun J hJ => ?_
        have hPJ : P ≤ J := hPinf.le.trans (sInf_le hJ)
        have hne : P ≠ J := by
          intro heq
          exact hPnotmax (heq.symm ▸ hMmax J hJ)
        exact sInf_le ⟨lt_of_le_of_ne hPJ hne, (hMmax J hJ).isPrime⟩
    _ = P := hPinf.symm

/-! ### (iii) `⟹` (i)

Suppose that `P` is a prime ideal and that `x ∈ P.jacobson` with `x ∉ P`.  Using Zorn's lemma we
find a prime ideal `Q ≥ P` with `x ∉ Q` which is maximal among the ideals containing `P` and
disjoint from the multiplicative set of powers of `x`.  Every prime ideal strictly containing `Q`
then has to contain `x`, while `Q` itself is not maximal (any maximal ideal containing it contains
`x ∈ P.jacobson`).  Hence condition (iii) fails for `Q`. -/

/-- Key construction for (iii) `⟹` (i).  If `P` is a prime ideal and `x ∉ P`, there is a prime
ideal `Q ≥ P` with `x ∉ Q` such that every prime ideal strictly containing `Q` contains `x`. -/
lemma exists_prime_ge_maximal_notMem {P : Ideal A} {x : A} (hP : P.IsPrime) (hx : x ∉ P) :
    ∃ Q : Ideal A, P ≤ Q ∧ Q.IsPrime ∧ x ∉ Q ∧
      ∀ R : Ideal A, Q < R → R.IsPrime → x ∈ R := by
  have hPdisj : Disjoint (P : Set A) (Submonoid.powers x) :=
    ((Ideal.disjoint_powers_iff_notMem (I := P) x hP.isRadical).mpr hx).symm
  obtain ⟨Q, hPQ, hQmax⟩ := zorn_le_nonempty₀
    (s := {I : Ideal A | Disjoint (I : Set A) (Submonoid.powers x)})
    (fun c hc hchain y hy => by
      refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      refine Set.disjoint_left.mpr fun a ha hpow => ?_
      obtain ⟨z, hz, haz⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hchain.directedOn).mp ha
      exact Set.disjoint_left.mp (hc hz) haz hpow)
    P hPdisj
  have hQdisj : Disjoint (Q : Set A) (Submonoid.powers x) := hQmax.prop
  have hQprime : Q.IsPrime :=
    Ideal.isPrime_of_maximally_disjoint Q (Submonoid.powers x) hQdisj (fun J hJ hJdisj => by
      have h1 : J ≤ Q := hQmax.le_of_ge hJdisj hJ.le
      exact absurd h1 (not_le_of_gt hJ))
  have hxQ : x ∉ Q := fun h => Set.disjoint_left.mp hQdisj h (Submonoid.mem_powers x)
  refine ⟨Q, hPQ, hQprime, hxQ, ?_⟩
  intro R hQR hRprime
  by_contra hxR
  have hRdisj : Disjoint (R : Set A) (Submonoid.powers x) :=
    ((Ideal.disjoint_powers_iff_notMem (I := R) x hRprime.isRadical).mpr hxR).symm
  have h1 : R ≤ Q := hQmax.le_of_ge hRdisj hQR.le
  exact absurd h1 (not_le_of_gt hQR)

lemma jacobson_le_of_cond_iii (h3 : Cond_iii A) ⦃P : Ideal A⦄ (hP : P.IsPrime) :
    P.jacobson ≤ P := by
  by_contra hcon
  obtain ⟨x, hxJ, hxP⟩ := Set.not_subset.mp hcon
  obtain ⟨Q, hPQ, hQprime, hxQ, hQup⟩ := exists_prime_ge_maximal_notMem hP hxP
  have hQnotmax : ¬ Q.IsMaximal := by
    rintro hQmax
    refine hxQ ?_
    have h2 : P.jacobson ≤ Q.jacobson := Ideal.jacobson_mono hPQ
    have h3 : Q.jacobson = Q := Ideal.jacobson_eq_self_of_isMaximal (I := Q) (H := hQmax)
    rw [h3] at h2
    exact h2 hxJ
  have hQeq : Q = sInf {R : Ideal A | Q < R ∧ R.IsPrime} := h3 Q hQprime hQnotmax
  have hxmem : x ∈ sInf {R : Ideal A | Q < R ∧ R.IsPrime} :=
    Ideal.mem_sInf.mpr fun R hR => hQup R hR.1 hR.2
  have hxQ' : x ∈ Q := by
    rw [hQeq]
    exact hxmem
  exact hxQ hxQ'

lemma cond_iii_imp_cond_i (h3 : Cond_iii A) : Cond_i A := by
  intro P hP
  refine ⟨{J : Ideal A | P ≤ J ∧ J.IsMaximal}, fun J hJ => hJ.2, ?_⟩
  show P = P.jacobson
  exact le_antisymm Ideal.le_jacobson (jacobson_le_of_cond_iii h3 hP)

lemma cond_i_iff_cond_iii : Cond_i A ↔ Cond_iii A :=
  ⟨cond_i_imp_cond_iii, cond_iii_imp_cond_i⟩

lemma cond_ii_iff_cond_iii : Cond_ii A ↔ Cond_iii A := by
  rw [cond_ii_iff_radical_eq_jacobson]
  exact ⟨fun h => cond_i_imp_cond_iii (cond_i_of_radical_eq_jacobson h),
    fun h => radical_eq_jacobson_of_cond_i (cond_iii_imp_cond_i h)⟩

/-! ### The exercise -/

/-- **Atiyah–Macdonald, Exercise 5.23.**  For a commutative ring `A` the following are equivalent:
(i) every prime ideal of `A` is an intersection of maximal ideals;
(ii) in every homomorphic image of `A` the nilradical equals the Jacobson radical;
(iii) every non-maximal prime ideal of `A` is the intersection of the prime ideals strictly
containing it. -/
theorem solution : Cond_i A ↔ Cond_ii A ∧ Cond_iii A :=
  ⟨fun h1 => ⟨cond_i_iff_cond_ii.mp h1, cond_i_imp_cond_iii h1⟩,
    fun h => cond_i_iff_cond_ii.mpr h.1⟩

/-- The three conditions of Exercise 5.23 are pairwise equivalent. -/
theorem solution_pairwise :
    (Cond_i A ↔ Cond_ii A) ∧ (Cond_ii A ↔ Cond_iii A) ∧ (Cond_i A ↔ Cond_iii A) :=
  ⟨cond_i_iff_cond_ii, cond_ii_iff_cond_iii, cond_i_iff_cond_iii⟩

/-- Exercise 5.23 with condition (ii) stated literally for every homomorphic image of `A`. -/
theorem solution' : Cond_i A ↔ Cond_ii' A ∧ Cond_iii A := by
  rw [← cond_ii_iff_cond_ii']
  exact solution

/-- A ring satisfying the equivalent conditions of Exercise 5.23 is a Jacobson ring, and this
matches Mathlib's `IsJacobsonRing`. -/
theorem cond_i_iff_isJacobsonRing : Cond_i A ↔ IsJacobsonRing A :=
  ⟨isJacobsonRing_of_cond_i, cond_i_of_isJacobsonRing⟩

/-! ### Consistency checks: the conditions are non-vacuous

`ℚ` is a field and `ℚ[X]` is a Jacobson ring that is not Artinian, so these instances show that the
three conditions are satisfied by genuinely different rings. -/

example : Cond_i ℚ := cond_i_of_isJacobsonRing inferInstance

example : Cond_iii ℚ := cond_i_imp_cond_iii (cond_i_of_isJacobsonRing inferInstance)

example : Cond_i (Polynomial ℚ) := cond_i_of_isJacobsonRing inferInstance

example : Cond_ii (Polynomial ℚ) :=
  cond_i_iff_cond_ii.mp (cond_i_of_isJacobsonRing inferInstance)

end AtiyahMcdonald69.Ex_5_23
