/-
Hartshorne (1977), *Algebraic Geometry*, Chapter I, §1, Exercise 1.5.

Source statement (Hartshorne, Exercise I.1.5):
"A `k`-algebra `B` is isomorphic to the affine coordinate ring of some algebraic set in
`A^n`, for some `n`, if and only if `B` is a finitely generated `k`-algebra with no
nilpotent elements."

As throughout Chapter I, `k` is an algebraically closed field and `A^n = k^n` is affine
`n`-space with the Zariski topology, whose closed sets are exactly the zero loci of sets of
polynomials (`isClosed_iff_exists_zeroLocusSet`).  For `X ⊆ k^n` the affine coordinate ring
is `k[X] = k[x_1,…,x_n]/I(X)`, where `I(X)` is the ideal of polynomials vanishing on `X`
(`coordinateRing`); its elements are represented by polynomials and multiplied by polynomial
multiplication, i.e. by pointwise multiplication of polynomial functions on `X`.

Both directions are proved for the actual point sets:

* `finiteType_coordinateRing`, `isReduced_coordinateRing` : `k[X]` is a finitely generated
  `k`-algebra without nilpotent elements (for every `X`, closed or not);
* `exists_isClosed_algEquiv` : a finitely generated reduced `k`-algebra `B` is
  `k`-isomorphic to `k[V(I)]`, where `I` is the kernel of a surjection `k[x_1,…,x_n] ↠ B`
  and `V(I) ⊆ k^n` is the zero locus of `I`.  The proof uses Hilbert's Nullstellensatz in
  the form `I(V(I)) = √I` (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) together
  with reducedness, which gives `√I = I`.

The joint statement is `hartshorne_I_1_5`.  Moreover `coordinateRingAlgEquivPolynomialFunctions`
identifies `k[X]` with the ring of polynomial functions `X → k` (the range of polynomial
evaluation `polyEval X`), so the coordinate ring used here is literally the ring of polynomial
functions on the point set `X`.

Refinement (the exercise's proof sketch in the corpus speaks of *affine varieties*, which in
Hartshorne's Chapter I means *irreducible* algebraic sets): `exists_irreducible_algEquiv`
shows that `B` can be realised as the coordinate ring of an irreducible algebraic set
exactly when `B` is a domain, and `isDomain_coordinateRing` is the converse.  The exercise as
printed in the book only asks for algebraic sets, which is the statement `hartshorne_I_1_5`.
-/
import Mathlib

namespace Hartshorne77.Ex_I_1_5

/-! ## Zero loci and the Zariski topology on `k^n` -/

section ZeroLocus

variable {k : Type*} [Field k]

/-- The zero locus in `k^n` of a set `S` of polynomials: the set of points at which every
polynomial of `S` evaluates to zero. -/
def zeroLocusSet {n : ℕ} (S : Set (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  {x | ∀ p ∈ S, MvPolynomial.aeval x p = 0}

@[simp]
theorem mem_zeroLocusSet {n : ℕ} {S : Set (MvPolynomial (Fin n) k)} {x : Fin n → k} :
    x ∈ zeroLocusSet S ↔ ∀ p ∈ S, MvPolynomial.aeval x p = 0 :=
  Iff.rfl

/-- Polynomial evaluation computed by `aeval` is ordinary polynomial evaluation. -/
theorem aeval_apply_eq_eval {n : ℕ} (x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval x p = MvPolynomial.eval x p := by
  rw [MvPolynomial.aeval_eq_eval]

/-- The zero locus of the empty set of polynomials is all of `k^n`. -/
theorem zeroLocusSet_empty {n : ℕ} :
    zeroLocusSet (k := k) (∅ : Set (MvPolynomial (Fin n) k)) = Set.univ := by
  ext x
  simp [zeroLocusSet]

/-- The zero locus of the constant polynomial `1` is empty. -/
theorem zeroLocusSet_singleton_one {n : ℕ} :
    zeroLocusSet (k := k) ({(1 : MvPolynomial (Fin n) k)} : Set (MvPolynomial (Fin n) k)) =
      ∅ := by
  ext x
  simp [zeroLocusSet]

theorem zeroLocusSet_anti_mono {n : ℕ} {S T : Set (MvPolynomial (Fin n) k)} (h : S ⊆ T) :
    zeroLocusSet T ⊆ zeroLocusSet S :=
  fun _ hx p hp => hx p (h hp)

/-- Zero loci convert unions of sets of polynomials into intersections. -/
theorem zeroLocusSet_iUnion {n : ℕ} {ι : Type*} (S : ι → Set (MvPolynomial (Fin n) k)) :
    zeroLocusSet (k := k) (⋃ i, S i) = ⋂ i, zeroLocusSet (S i) := by
  ext x
  simp only [zeroLocusSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  exact ⟨fun h i p hp => h p ⟨i, hp⟩, fun h p ⟨i, hp⟩ => h i p hp⟩

/-- A point is a common zero of all products `p * q` with `p ∈ S`, `q ∈ T` iff it is a common
zero of `S` or of `T`: over a field a product vanishes iff one factor does. -/
theorem zeroLocusSet_mul_union {n : ℕ} (S T : Set (MvPolynomial (Fin n) k)) :
    zeroLocusSet (k := k) (Set.image2 (· * ·) S T) = zeroLocusSet S ∪ zeroLocusSet T := by
  ext x
  simp only [zeroLocusSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image2]
  constructor
  · intro h
    by_contra hx
    rw [not_or] at hx
    simp only [not_forall] at hx
    obtain ⟨⟨p, hpS, hp0⟩, ⟨q, hqT, hq0⟩⟩ := hx
    refine mul_ne_zero hp0 hq0 ?_
    rw [← map_mul]
    exact h (p * q) ⟨p, hpS, q, hqT, rfl⟩
  · rintro (h | h)
    · rintro p ⟨a, ha, b, hb, rfl⟩
      rw [map_mul, h a ha, zero_mul]
    · rintro p ⟨a, ha, b, hb, rfl⟩
      rw [map_mul, h b hb, mul_zero]

/-- An intersection of zero loci is a zero locus. -/
theorem sInter_of_zeroLocusSet {n : ℕ} {A : Set (Set (Fin n → k))}
    (hA : ∀ a ∈ A, ∃ S : Set (MvPolynomial (Fin n) k), a = zeroLocusSet S) :
    ∃ S : Set (MvPolynomial (Fin n) k), ⋂₀ A = zeroLocusSet S := by
  classical
  have hg : ∀ a : A, ∃ S : Set (MvPolynomial (Fin n) k),
      (a : Set (Fin n → k)) = zeroLocusSet S := fun a => hA a.1 a.2
  refine ⟨⋃ a : A, Classical.choose (hg a), ?_⟩
  rw [zeroLocusSet_iUnion, Set.sInter_eq_iInter]
  exact Set.iInter_congr fun a => Classical.choose_spec (hg a)

/-- The Zariski topology on affine `n`-space `k^n`: a set is open iff it is the complement of
a zero locus of a set of polynomials. -/
instance zariskiTopology {n : ℕ} : TopologicalSpace (Fin n → k) where
  IsOpen U := ∃ S : Set (MvPolynomial (Fin n) k), Uᶜ = zeroLocusSet S
  isOpen_univ := by
    refine ⟨{1}, ?_⟩
    rw [Set.compl_univ]
    exact (zeroLocusSet_singleton_one (k := k) (n := n)).symm
  isOpen_inter U V hU hV := by
    obtain ⟨S, hS⟩ := hU
    obtain ⟨T, hT⟩ := hV
    refine ⟨Set.image2 (· * ·) S T, ?_⟩
    rw [Set.compl_inter, hS, hT, zeroLocusSet_mul_union]
  isOpen_sUnion A hA := by
    rw [Set.compl_sUnion]
    exact sInter_of_zeroLocusSet (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := ha
      exact hA b hb)

/-- In the Zariski topology the closed sets are exactly the zero loci. -/
theorem isClosed_iff_exists_zeroLocusSet {n : ℕ} {X : Set (Fin n → k)} :
    IsClosed X ↔ ∃ S : Set (MvPolynomial (Fin n) k), X = zeroLocusSet S := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := h.isOpen_compl
    exact ⟨S, by rw [← compl_compl X, hS]⟩
  · rintro ⟨S, rfl⟩
    exact ⟨⟨S, by rw [compl_compl]⟩⟩

/-- The zero locus of a set of polynomials is the zero locus of the ideal it generates. -/
theorem zeroLocusSet_eq_zeroLocus_span {n : ℕ} (S : Set (MvPolynomial (Fin n) k)) :
    zeroLocusSet (k := k) S = MvPolynomial.zeroLocus k (Ideal.span S) := by
  rw [MvPolynomial.zeroLocus_span]
  rfl

/-- Mathlib's ideal-indexed zero locus coincides with `zeroLocusSet` on the underlying set. -/
theorem zeroLocus_ideal_eq_zeroLocusSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I = zeroLocusSet (k := k) (I : Set (MvPolynomial (Fin n) k)) :=
  rfl

/-- The union of the zero loci of two ideals is the zero locus of their product. -/
theorem zeroLocus_union_mul {n : ℕ} (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J =
      MvPolynomial.zeroLocus k (I * J) := by
  ext x
  simp only [Set.mem_union, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · rintro (h | h) p hp
    · exact h p (Ideal.mul_le_left hp)
    · exact h p (Ideal.mul_le_right hp)
  · intro h
    by_contra hx
    rw [not_or] at hx
    simp only [not_forall] at hx
    obtain ⟨⟨p, hpI, hp0⟩, ⟨q, hqJ, hq0⟩⟩ := hx
    exact mul_ne_zero hp0 hq0 (by rw [← map_mul]; exact h (p * q) (Ideal.mul_mem_mul hpI hqJ))

/-! ## The affine coordinate ring -/

/-- The affine coordinate ring `k[X] = k[x_1,…,x_n]/I(X)` of a subset `X ⊆ k^n`. -/
abbrev coordinateRing {n : ℕ} (X : Set (Fin n → k)) : Type _ :=
  MvPolynomial (Fin n) k ⧸ MvPolynomial.vanishingIdeal k X

/-- Every coordinate ring is a finitely generated `k`-algebra (generated by the coordinate
functions). -/
theorem finiteType_coordinateRing {n : ℕ} (X : Set (Fin n → k)) :
    Algebra.FiniteType k (coordinateRing X) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (MvPolynomial.vanishingIdeal k X))
    (Ideal.Quotient.mkₐ_surjective k (MvPolynomial.vanishingIdeal k X))

/-- The vanishing ideal of any set of points is radical. -/
theorem isRadical_vanishingIdeal {n : ℕ} (X : Set (Fin n → k)) :
    (MvPolynomial.vanishingIdeal k X).IsRadical := by
  intro p hp
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hp
  intro x hx
  have h : MvPolynomial.aeval x (p ^ m) = 0 := hm x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

/-- Every coordinate ring has no nilpotent elements. -/
theorem isReduced_coordinateRing {n : ℕ} (X : Set (Fin n → k)) :
    IsReduced (coordinateRing X) :=
  (Ideal.isRadical_iff_quotient_reduced _).1 (isRadical_vanishingIdeal X)

/-! ## The coordinate ring as the ring of polynomial functions on `X` -/

section PolyFunctions

variable {k : Type*} [Field k]

/-- Evaluation of polynomials at points of `X ⊆ k^n`, viewed as a function on `X`. -/
noncomputable def polyEval {n : ℕ} (X : Set (Fin n → k)) :
    MvPolynomial (Fin n) k →ₐ[k] (X → k) where
  toFun p x := MvPolynomial.aeval (x : Fin n → k) p
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp
  map_zero' := by ext x; simp
  map_add' p q := by ext x; simp
  commutes' c := by ext x; simp

/-- The `k`-algebra of polynomial functions on `X ⊆ k^n`: the range of polynomial
evaluation on `X`. -/
noncomputable def polynomialFunctions {n : ℕ} (X : Set (Fin n → k)) : Subalgebra k (X → k) :=
  (polyEval X).range

/-- The kernel of polynomial evaluation on `X` is precisely the vanishing ideal of `X`. -/
theorem ker_polyEval {n : ℕ} (X : Set (Fin n → k)) :
    RingHom.ker (polyEval X) = MvPolynomial.vanishingIdeal k X := by
  ext p
  rw [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro h x hx
    have h' := congrFun h ⟨x, hx⟩
    simpa [polyEval] using h'
  · intro h
    ext x
    simpa [polyEval] using h x.1 x.2

/-- **`k[X]` is the `k`-algebra of polynomial functions on `X`**: the coordinate ring
`k[x_1,…,x_n]/I(X)` is the ring of restrictions to `X` of polynomial functions on `k^n`. -/
noncomputable def coordinateRingAlgEquivPolynomialFunctions {n : ℕ} (X : Set (Fin n → k)) :
    coordinateRing X ≃ₐ[k] polynomialFunctions X :=
  (Ideal.quotientEquivAlgOfEq k (ker_polyEval X).symm).trans
    (Ideal.quotientKerEquivRange (polyEval X))

end PolyFunctions

end ZeroLocus

/-! ## The converse direction: reduced finitely generated algebras are coordinate rings -/

section Converse

variable (k : Type*) [Field k] [IsAlgClosed k]

attribute [local instance] finiteType_coordinateRing isReduced_coordinateRing

/-- **Nullstellensatz, point-set form.**  For every subset `X ⊆ k^n`, the vanishing ideal of
the zero locus of `I(X)` is `I(X)`. -/
theorem vanishingIdeal_zeroLocus_vanishingIdeal {n : ℕ} (X : Set (Fin n → k)) :
    MvPolynomial.vanishingIdeal k
        (zeroLocusSet (k := k) (MvPolynomial.vanishingIdeal k X : Set (MvPolynomial (Fin n) k))) =
      MvPolynomial.vanishingIdeal k X := by
  have hrad := isRadical_vanishingIdeal (k := k) X
  rw [← zeroLocus_ideal_eq_zeroLocusSet, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  exact hrad.radical

/-- **Hartshorne I.1.5, converse.**  A finitely generated `k`-algebra without nilpotent
elements is the affine coordinate ring of an algebraic set in `A^n` for some `n`. -/
theorem exists_isClosed_algEquiv (B : Type*) [CommRing B] [Algebra k B]
    (hfg : Algebra.FiniteType k B) (hred : IsReduced B) :
    ∃ (n : ℕ) (X : Set (Fin n → k)), IsClosed X ∧ Nonempty (B ≃ₐ[k] coordinateRing X) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hfg
  have hrad : (RingHom.ker f).IsRadical :=
    (RingHom.ker_isRadical_iff_reduced_of_surjective hf).2 hred
  have hvan : MvPolynomial.vanishingIdeal k
      (zeroLocusSet (k := k) (RingHom.ker f : Set (MvPolynomial (Fin n) k))) = RingHom.ker f := by
    rw [← zeroLocus_ideal_eq_zeroLocusSet, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
    exact hrad.radical
  refine ⟨n, zeroLocusSet (k := k) (RingHom.ker f : Set (MvPolynomial (Fin n) k)),
    (isClosed_iff_exists_zeroLocusSet).2 ⟨_, rfl⟩, ?_⟩
  exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    (Ideal.quotientEquivAlgOfEq k hvan.symm)⟩

/-- **Hartshorne I.1.5.**  A `k`-algebra `B` is isomorphic to the affine coordinate ring of
some algebraic set in `A^n` (for some `n`) if and only if `B` is a finitely generated
`k`-algebra with no nilpotent elements. -/
theorem hartshorne_I_1_5 (B : Type*) [CommRing B] [Algebra k B] :
    (∃ (n : ℕ) (X : Set (Fin n → k)), IsClosed X ∧ Nonempty (B ≃ₐ[k] coordinateRing X)) ↔
      Algebra.FiniteType k B ∧ IsReduced B := by
  constructor
  · rintro ⟨n, X, -, ⟨e⟩⟩
    refine ⟨?_, ?_⟩
    · exact Algebra.FiniteType.of_surjective (e.symm : coordinateRing X →ₐ[k] B) e.symm.surjective
    · refine ⟨fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hx
      refine e.injective ?_
      rw [map_zero]
      exact eq_zero_of_pow_eq_zero (n := m) (by rw [← map_pow, hm, map_zero])
  · rintro ⟨hfg, hred⟩
    exact exists_isClosed_algEquiv k B hfg hred

end Converse

/-! ## Refinement: irreducible algebraic sets (varieties) and domains -/

section Irreducible

variable (k : Type*) [Field k] [IsAlgClosed k]

attribute [local instance] finiteType_coordinateRing isReduced_coordinateRing

/-- The zero locus of a prime ideal is irreducible. -/
theorem isIrreducible_zeroLocus_of_isPrime {n : ℕ} {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsPrime) : IsIrreducible (MvPolynomial.zeroLocus k I) := by
  have hprime : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (P := I) (h := hI)
  have hne : (MvPolynomial.zeroLocus k I).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have htop : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = ⊤ := by
      rw [h, MvPolynomial.vanishingIdeal_empty]
    rw [hprime] at htop
    exact hI.ne_top htop
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro z₁ z₂ hz₁ hz₂ hsub
  obtain ⟨S, rfl⟩ := (isClosed_iff_exists_zeroLocusSet (k := k)).1 hz₁
  obtain ⟨T, rfl⟩ := (isClosed_iff_exists_zeroLocusSet (k := k)).1 hz₂
  rw [zeroLocusSet_eq_zeroLocus_span, zeroLocusSet_eq_zeroLocus_span] at hsub ⊢
  have hsub' : MvPolynomial.zeroLocus k I ⊆
      MvPolynomial.zeroLocus k (Ideal.span S * Ideal.span T) := by
    rw [zeroLocus_union_mul] at hsub
    exact hsub
  have hle : Ideal.span S * Ideal.span T ≤ I := by
    have h := (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal (K := k)).1 hsub'
    rwa [hprime] at h
  rcases hI.mul_le.1 hle with h | h
  · left
    exact MvPolynomial.zeroLocus_anti_mono h
  · right
    exact MvPolynomial.zeroLocus_anti_mono h

omit [IsAlgClosed k] in
/-- The vanishing ideal of an irreducible set of points is prime; hence its affine coordinate
ring is a domain.  (Algebraic closedness of `k` is not needed for this direction.) -/
theorem isDomain_coordinateRing {n : ℕ} {X : Set (Fin n → k)} (hX : IsIrreducible X) :
    IsDomain (coordinateRing X) := by
  have hprime : (MvPolynomial.vanishingIdeal k X).IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      obtain ⟨x, hx⟩ := hX.nonempty
      have h1 : (1 : MvPolynomial (Fin n) k) ∈ MvPolynomial.vanishingIdeal k X := by
        rw [htop]
        exact Submodule.mem_top
      simpa using h1 x hx
    · intro f g hfg
      have hsub : X ⊆ zeroLocusSet (k := k) ({f} : Set (MvPolynomial (Fin n) k)) ∪
          zeroLocusSet (k := k) ({g} : Set (MvPolynomial (Fin n) k)) := by
        rw [← zeroLocusSet_mul_union]
        rintro x hx p ⟨a, rfl, b, rfl, rfl⟩
        exact hfg x hx
      have hc1 : IsClosed (zeroLocusSet (k := k) ({f} : Set (MvPolynomial (Fin n) k))) :=
        (isClosed_iff_exists_zeroLocusSet (k := k)).2 ⟨_, rfl⟩
      have hc2 : IsClosed (zeroLocusSet (k := k) ({g} : Set (MvPolynomial (Fin n) k))) :=
        (isClosed_iff_exists_zeroLocusSet (k := k)).2 ⟨_, rfl⟩
      have hpre := hX.isPreirreducible
      rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
      rcases hpre _ _ hc1 hc2 hsub with h | h
      · left
        intro x hx
        simpa using h hx
      · right
        intro x hx
        simpa using h hx
  exact (Ideal.Quotient.isDomain_iff_prime _).2 hprime

/-- A finitely generated `k`-algebra that is a domain is the affine coordinate ring of an
*irreducible* algebraic set, i.e. of an affine variety in Hartshorne's sense. -/
theorem exists_irreducible_algEquiv (B : Type*) [CommRing B] [Algebra k B] [IsDomain B]
    (hfg : Algebra.FiniteType k B) :
    ∃ (n : ℕ) (X : Set (Fin n → k)), IsClosed X ∧ IsIrreducible X ∧
      Nonempty (B ≃ₐ[k] coordinateRing X) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hfg
  have hprime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hvan : MvPolynomial.vanishingIdeal k
      (zeroLocusSet (k := k) (RingHom.ker f : Set (MvPolynomial (Fin n) k))) = RingHom.ker f := by
    rw [← zeroLocus_ideal_eq_zeroLocusSet,
      MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (P := RingHom.ker f) (h := hprime)]
  refine ⟨n, zeroLocusSet (k := k) (RingHom.ker f : Set (MvPolynomial (Fin n) k)),
    (isClosed_iff_exists_zeroLocusSet (k := k)).2 ⟨_, rfl⟩, ?_, ?_⟩
  · rw [← zeroLocus_ideal_eq_zeroLocusSet]
    exact isIrreducible_zeroLocus_of_isPrime (k := k) hprime
  · exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
      (Ideal.quotientEquivAlgOfEq k hvan.symm)⟩

end Irreducible

end Hartshorne77.Ex_I_1_5

/-! ## Axiom audit -/

#print axioms Hartshorne77.Ex_I_1_5.isClosed_iff_exists_zeroLocusSet
#print axioms Hartshorne77.Ex_I_1_5.finiteType_coordinateRing
#print axioms Hartshorne77.Ex_I_1_5.isRadical_vanishingIdeal
#print axioms Hartshorne77.Ex_I_1_5.isReduced_coordinateRing
#print axioms Hartshorne77.Ex_I_1_5.vanishingIdeal_zeroLocus_vanishingIdeal
#print axioms Hartshorne77.Ex_I_1_5.exists_isClosed_algEquiv
#print axioms Hartshorne77.Ex_I_1_5.hartshorne_I_1_5
#print axioms Hartshorne77.Ex_I_1_5.isIrreducible_zeroLocus_of_isPrime
#print axioms Hartshorne77.Ex_I_1_5.isDomain_coordinateRing
#print axioms Hartshorne77.Ex_I_1_5.exists_irreducible_algEquiv
#print axioms Hartshorne77.Ex_I_1_5.ker_polyEval
#print axioms Hartshorne77.Ex_I_1_5.coordinateRingAlgEquivPolynomialFunctions
