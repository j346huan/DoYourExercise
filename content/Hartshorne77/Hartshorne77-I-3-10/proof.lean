import Mathlib

/-!
# Hartshorne I.3.10: subvarieties and restriction of morphisms

Regular functions are locally polynomial quotients (affine) or locally quotients of
equally homogeneous forms (projective), and morphisms preserve all such functions.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped Topology Set.Notation
open MvPolynomial

namespace Hartshorne77.Ex_I_3_10

/-! ## Affine space and its Zariski topology -/

/-- Affine `n`-space over `k`, as a point set. -/
abbrev ASpace (k : Type*) (n : ℕ) : Type _ := Fin n → k

/-- The polynomial ring `k[x_1,…,x_n]`. -/
abbrev Poly (k : Type*) [CommSemiring k] (n : ℕ) : Type _ := MvPolynomial (Fin n) k

section Zariski

variable {k : Type*} [Field k]

/-- A subset of `A^n` is Zariski closed if it is the zero locus of an ideal of polynomials. -/
def IsZarClosed (n : ℕ) (S : Set (ASpace k n)) : Prop :=
  ∃ I : Ideal (Poly k n), S = MvPolynomial.zeroLocus k I

theorem isZarClosed_empty (n : ℕ) : IsZarClosed (k := k) n ∅ :=
  ⟨⊤, by simp⟩

theorem isZarClosed_univ (n : ℕ) : IsZarClosed (k := k) n Set.univ :=
  ⟨⊥, by simp⟩

/-- Arbitrary intersections of zero loci are zero loci. -/
theorem zeroLocus_iInter {n : ℕ} {ι : Type*} (I : ι → Ideal (Poly k n)) :
    (⋂ i, MvPolynomial.zeroLocus k (I i)) = MvPolynomial.zeroLocus k (⨆ i, I i) := by
  ext x
  simp only [Set.mem_iInter, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have hle : (⨆ i, I i) ≤ RingHom.ker (MvPolynomial.aeval (R := k) x) := by
      refine iSup_le fun i => ?_
      intro q hq
      exact h i q hq
    have := hle hp
    simpa using this
  · intro h i p hp
    exact h p (le_iSup I i hp)

/-- The union of two zero loci is a zero locus. -/
theorem zeroLocus_union {n : ℕ} (I J : Ideal (Poly k n)) :
    MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J =
      MvPolynomial.zeroLocus k (I ⊓ J) := by
  refine le_antisymm ?_ ?_
  · rintro x (hx | hx) p hp
    · exact hx p hp.1
    · exact hx p hp.2
  · intro x hx
    by_contra h
    simp only [Set.mem_union, not_or, MvPolynomial.mem_zeroLocus_iff, not_forall] at h
    obtain ⟨⟨p, hpI, hp0⟩, ⟨q, hqJ, hq0⟩⟩ := h
    have hmem : p * q ∈ I ⊓ J := ⟨I.mul_mem_right q hpI, J.mul_mem_left p hqJ⟩
    have hzero := hx (p * q) hmem
    rw [map_mul] at hzero
    exact mul_ne_zero hp0 hq0 hzero

/-- Arbitrary intersections of Zariski closed sets are Zariski closed. -/
theorem isZarClosed_sInter {n : ℕ} {S : Set (Set (ASpace k n))}
    (hS : ∀ s ∈ S, IsZarClosed n s) : IsZarClosed (k := k) n (⋂₀ S) := by
  classical
  let J : S → Ideal (Poly k n) := fun s => Classical.choose (hS s.1 s.2)
  have hJ : ∀ s : S, (s : Set (ASpace k n)) = MvPolynomial.zeroLocus k (J s) :=
    fun s => Classical.choose_spec (hS s.1 s.2)
  refine ⟨⨆ s : S, J s, ?_⟩
  rw [← zeroLocus_iInter (fun s : S => J s)]
  ext x
  simp only [Set.mem_sInter, Set.mem_iInter]
  constructor
  · intro h s
    rw [← hJ s]
    exact h s.1 s.2
  · intro h s hs
    have h' := h ⟨s, hs⟩
    rw [← hJ ⟨s, hs⟩] at h'
    exact h'

theorem isZarClosed_union {n : ℕ} {S T : Set (ASpace k n)}
    (hS : IsZarClosed n S) (hT : IsZarClosed n T) : IsZarClosed n (S ∪ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  exact ⟨I ⊓ J, zeroLocus_union I J⟩

/-- The Zariski topology on `A^n = k^n`: a set is open iff its complement is a zero locus. -/
@[instance_reducible]
def zariskiTopology (k : Type*) [Field k] (n : ℕ) : TopologicalSpace (ASpace k n) where
  IsOpen S := IsZarClosed (k := k) n Sᶜ
  isOpen_univ := by simpa using isZarClosed_empty (k := k) n
  isOpen_inter S T hS hT := by
    rw [Set.compl_inter]
    exact isZarClosed_union hS hT
  isOpen_sUnion S hS := by
    rw [Set.compl_sUnion]
    refine isZarClosed_sInter ?_
    rintro t ⟨s, hs, rfl⟩
    exact hS s hs

attribute [instance 100] zariskiTopology

variable {n m : ℕ}

theorem isOpen_iff {S : Set (ASpace k n)} :
    IsOpen S ↔ IsZarClosed (k := k) n Sᶜ := Iff.rfl

theorem isClosed_iff {S : Set (ASpace k n)} :
    IsClosed S ↔ IsZarClosed (k := k) n S := by
  constructor
  · intro h
    have h' := h.isOpen_compl
    rwa [isOpen_iff, compl_compl] at h'
  · intro h
    exact ⟨by rw [isOpen_iff, compl_compl]; exact h⟩

theorem isClosed_zeroLocus (I : Ideal (Poly k n)) :
    IsClosed (MvPolynomial.zeroLocus k I) :=
  isClosed_iff.2 ⟨I, rfl⟩

theorem isOpen_compl_zeroLocus (p : Poly k n) :
    IsOpen {x : ASpace k n | MvPolynomial.aeval x p ≠ 0} := by
  rw [isOpen_iff]
  refine ⟨Ideal.span {p}, ?_⟩
  ext x
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h q hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [map_mul, show MvPolynomial.aeval x p = 0 from h, zero_mul]
  · intro h
    exact h p (Ideal.subset_span rfl)

/-! ### Polynomial maps from `k`-algebra maps -/

/-- Evaluation at a point, as a `k`-algebra homomorphism. -/
abbrev ev {n : ℕ} (x : ASpace k n) : Poly k n →ₐ[k] k := MvPolynomial.aeval x

@[simp]
theorem ev_X {n : ℕ} (x : ASpace k n) (i : Fin n) : ev x (MvPolynomial.X i) = x i := by
  simp [ev]

/-- Evaluation of a polynomial at a point, as a plain function. -/
abbrev pev {n : ℕ} (x : ASpace k n) (p : Poly k n) : k := MvPolynomial.aeval x p

/-- The map on points induced by a `k`-algebra homomorphism of polynomial rings. -/
def pointMap {n m : ℕ} (g : Poly k n →ₐ[k] Poly k m) : ASpace k m → ASpace k n :=
  fun x j => MvPolynomial.aeval (R := k) x (g (MvPolynomial.X j))

theorem aeval_pointMap {n m : ℕ} (g : Poly k n →ₐ[k] Poly k m)
    (x : ASpace k m) (p : Poly k n) :
    MvPolynomial.aeval (R := k) (pointMap g x) p = MvPolynomial.aeval (R := k) x (g p) := by
  have h : (MvPolynomial.aeval (R := k) (pointMap g x)) =
      (MvPolynomial.aeval (R := k) x).comp g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [pointMap]
  rw [h]
  rfl

/-- Polynomial maps are continuous for the Zariski topology. -/
theorem continuous_pointMap {n m : ℕ} (g : Poly k n →ₐ[k] Poly k m) :
    Continuous (pointMap g) := by
  rw [continuous_iff_isClosed]
  intro S hS
  rw [isClosed_iff] at hS ⊢
  obtain ⟨I, rfl⟩ := hS
  refine ⟨Ideal.map (g : Poly k n →+* Poly k m) I, ?_⟩
  ext x
  rw [Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have hker : Ideal.map (g : Poly k n →+* Poly k m) I ≤
        RingHom.ker (MvPolynomial.aeval (R := k) x : Poly k m →+* k) := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      have hq' := h q hq
      rwa [aeval_pointMap] at hq'
    have := hker hp
    simpa using this
  · intro h p hp
    rw [aeval_pointMap]
    exact h (g p) (Ideal.mem_map_of_mem (g : Poly k n →+* Poly k m) hp)

end Zariski



/-- The restriction of a function to subtypes with an image-containment condition. -/
def restrictedMap {A B : Type*} {X : Set A} {Y : Set B} {X' : Set A} {Y' : Set B}
    (hXX' : X' ⊆ X) (φ : X → Y) (hmap : ∀ x : X', (φ ⟨x.1, hXX' x.2⟩).1 ∈ Y') :
    X' → Y' := fun x => ⟨(φ ⟨x.1, hXX' x.2⟩).1, hmap x⟩

/-- Open-in-closure is another of the equivalent formulations of local closedness. -/
theorem locallyClosed_iff_open_in_closure {X : Type*} [TopologicalSpace X]
    (S : Set X) : IsLocallyClosed S ↔ IsOpen (closure S ↓∩ S) :=
  (isLocallyClosed_tfae S).out 0 4

/-- Classical affine regularity, with an explicit source variety and an open subset of it.
Keeping the two levels explicit prevents Lean from changing the carrier of a pre-image. -/
def RegularOn {k : Type*} [Field k] {n : ℕ} (X : Set (ASpace k n))
    (V : Set X) (f : V → k) : Prop :=
  ∀ x : V, ∃ (p q : Poly k n) (U : Set V), IsOpen U ∧ x ∈ U ∧
    (∀ y ∈ U, pev y.1.1 q ≠ 0) ∧ ∀ y ∈ U, f y * pev y.1.1 q = pev y.1.1 p

/-- Pull back a function on an open subset of the target to its pre-image. -/
def pullback {A B C : Type*} {X : Set A} {Y : Set B}
    (φ : X → Y) {V : Set Y} (f : V → C) : (φ ⁻¹' V : Set X) → C :=
  fun x => f ⟨φ x.1, x.2⟩

/-- Continuous maps pulling every regular function back to a regular function. -/
def IsMorphism {k : Type*} [Field k] {n m : ℕ}
    (X : Set (ASpace k n)) (Y : Set (ASpace k m)) (φ : X → Y) : Prop :=
  Continuous φ ∧ ∀ (V : Set Y), IsOpen V → ∀ f : V → k, RegularOn Y V f →
    RegularOn X (φ ⁻¹' V) (pullback φ f)

/-- Restriction to irreducible locally closed subvarieties, in the affine case. -/
theorem isMorphism_restrict_affine {k : Type*} [Field k] {n m : ℕ}
    {X : Set (ASpace k n)} {Y : Set (ASpace k m)}
    {X' : Set (ASpace k n)} {Y' : Set (ASpace k m)}
    (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y)
    (_hXi : IsIrreducible X') (_hXl : IsLocallyClosed X')
    (_hYi : IsIrreducible Y') (_hYl : IsLocallyClosed Y')
    (φ : X → Y) (hmap : ∀ x : X', (φ ⟨x.1, hXX' x.2⟩).1 ∈ Y')
    (hφ : IsMorphism X Y φ) :
    IsMorphism X' Y' (restrictedMap hXX' φ hmap) := by
  let ψ : X' → Y' := restrictedMap hXX' φ hmap
  have hc : Continuous ψ := by
    have hc0a : Continuous (fun x : X' => (φ ⟨x.1, hXX' x.2⟩ : Y).1) :=
      continuous_subtype_val.comp (hφ.1.comp (Continuous.subtype_mk continuous_subtype_val _))
    exact Continuous.subtype_mk hc0a (fun x => (ψ x).2)
  refine ⟨hc, fun V hV f hf x => ?_⟩
  obtain ⟨p, q, U, hU, hxU, hpq, hfrep⟩ := hf ⟨ψ x.1, x.2⟩
  let W : Set Y := {y | pev y.1 q ≠ 0}
  have hW : IsOpen W :=
    (isOpen_compl_zeroLocus q).preimage continuous_subtype_val
  let F : W → k := fun y => pev y.1.1 p / pev y.1.1 q
  have hF : RegularOn Y W F := by
    intro y
    refine ⟨p, q, Set.univ, isOpen_univ, Set.mem_univ _, fun z hz => z.2, fun z hz => ?_⟩
    dsimp [F]
    exact (eq_div_iff z.2).mp rfl
  have hxW : pev (φ ⟨x.1.1, hXX' x.1.2⟩ : Y).1 q ≠ 0 := by
    exact hpq ⟨ψ x.1, x.2⟩ hxU
  let z0 : φ ⁻¹' W := ⟨⟨x.1.1, hXX' x.1.2⟩, hxW⟩
  obtain ⟨P, Q, T, hT, hzT, hQne, hRep⟩ := hφ.2 W hW F hF z0
  let L : Set (ψ ⁻¹' V) :=
    (fun z : ψ ⁻¹' V => (⟨ψ z.1, z.2⟩ : V)) ⁻¹' U
  have hCL : Continuous (fun z : ψ ⁻¹' V => (⟨ψ z.1, z.2⟩ : V)) :=
    Continuous.subtype_mk (hc.comp continuous_subtype_val) _
  have hL : IsOpen L :=
    hU.preimage hCL
  let J : L → (φ ⁻¹' W : Set X) := fun z =>
    ⟨⟨z.1.1.1, hXX' z.1.1.2⟩, hpq ⟨ψ z.1, z.1.2⟩ z.2⟩
  have hinc : Continuous (fun z : L => (⟨z.1.1.1, hXX' z.1.1.2⟩ : X)) :=
    Continuous.subtype_mk (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  have hJ : Continuous J := Continuous.subtype_mk hinc (fun z => (J z).2)
  let T' := J ⁻¹' T
  let T'' : Set (ψ ⁻¹' V) := Subtype.val '' T'
  have hT' : IsOpen T' := hT.preimage hJ
  have hT'' : IsOpen T'' := hL.isOpenEmbedding_subtypeVal.isOpenMap _ hT'
  refine ⟨P, Q, T'', hT'', ?_, (fun z hz => ?_), fun z hz => ?_⟩
  · exact ⟨⟨x, hxU⟩, hzT, rfl⟩
  · obtain ⟨zL, hmem, rfl⟩ := hz
    exact hQne (J zL) hmem
  obtain ⟨zL, hmem, rfl⟩ := hz
  have hfq : f ⟨ψ zL.1.1, zL.1.2⟩ =
      pev (ψ zL.1.1).1 p / pev (ψ zL.1.1).1 q :=
    (eq_div_iff (hpq ⟨ψ zL.1.1, zL.1.2⟩ zL.2)).2
      (hfrep ⟨ψ zL.1.1, zL.1.2⟩ zL.2)
  change f ⟨ψ zL.1.1, zL.1.2⟩ * pev zL.1.1.1 Q = pev zL.1.1.1 P
  rw [hfq]
  exact hRep (J zL) hmem

variable {k : Type*} [Field k] {n : ℕ}

/-! ## Homogeneity: scalars and monomials -/

/-- In a homogeneous polynomial of degree `d` every monomial that occurs has total degree `d`. -/
theorem degree_of_mem_support {m : ℕ} {A : MvPolynomial (Fin m) k} {d : ℕ}
    (hA : A.IsHomogeneous d) {e : Fin m →₀ ℕ} (he : e ∈ A.support) :
    Finsupp.degree e = d := by
  have h1 : A ∈ MvPolynomial.homogeneousSubmodule (Fin m) k d := hA
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at h1
  rw [AddMonoidAlgebra.mem_supported] at h1
  exact h1 (Finset.mem_coe.mpr he)

/-- Evaluating a homogeneous polynomial of degree `d` at a scalar multiple of a point. -/
theorem eval_smul_of_isHomogeneous {m : ℕ} {A : MvPolynomial (Fin m) k} {d : ℕ}
    (hA : A.IsHomogeneous d) (c : k) (v : Fin m → k) :
    A.eval (c • v) = c ^ d * A.eval v := by
  conv_lhs => rw [MvPolynomial.eval_eq']
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : Finsupp.degree e = d := degree_of_mem_support hA he
  have h1 : (∏ i, (c • v) i ^ e i) = c ^ d * ∏ i, v i ^ e i := by
    have h2 : ∀ i, (c • v) i ^ e i = c ^ e i * v i ^ e i := by
      intro i; rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    have hsum : (∑ i, e i) = d := by rw [← Finsupp.degree_eq_sum]; exact hdeg
    rw [Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hsum]
  rw [h1]; ring

/-! ## Projective space -/

/-- Projective `n`-space over `k`: the set of lines in `k^{n+1}`. -/
abbrev Proj (k : Type*) [Field k] (n : ℕ) := Projectivization k (Fin (n + 1) → k)

namespace Proj

/-- `vanish A P` says that the homogeneous polynomial `A` vanishes at the point `P`;
`H_i = {P | vanish (X i) P}` is the `i`-th coordinate hyperplane. -/
def vanish (A : MvPolynomial (Fin (n + 1)) k) (P : Proj k n) : Prop := A.eval P.rep = 0

theorem vanish_mk {A : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    vanish A (Projectivization.mk k v hv) ↔ A.eval v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  have ha' : (a : k) • v = (Projectivization.mk k v hv).rep := by
    rw [← ha]; rfl
  have hmain : A.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * A.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hA]
  simp only [vanish, hmain]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero d hane)
  · intro h; rw [h, mul_zero]

/-- The value at `P` of a ratio `A / B` of homogeneous polynomials of the same degree. -/
def ratio (A B : MvPolynomial (Fin (n + 1)) k) (P : Proj k n) : k :=
  A.eval P.rep / B.eval P.rep

theorem ratio_mk {A B : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hA : A.IsHomogeneous d)
    (hB : B.IsHomogeneous d) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ratio A B (Projectivization.mk k v hv) = A.eval v / B.eval v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  have ha' : (a : k) • v = (Projectivization.mk k v hv).rep := by
    rw [← ha]; rfl
  have h1 : A.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * A.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hA]
  have h2 : B.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * B.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hB]
  simp only [ratio, h1, h2, mul_div_mul_left _ _ (pow_ne_zero d hane)]

/-- The Zariski topology on `P^n`: open sets are unions of basic open sets
`D_+(A) = {P | A(P) ≠ 0}` for homogeneous forms `A`. -/
def IsProjOpen (V : Set (Proj k n)) : Prop :=
  ∀ P ∈ V, ∃ (A : MvPolynomial (Fin (n + 1)) k) (d : ℕ),
    A.IsHomogeneous d ∧ A.eval P.rep ≠ 0 ∧ {Q | A.eval Q.rep ≠ 0} ⊆ V

theorem isProjOpen_univ : IsProjOpen (Set.univ : Set (Proj k n)) := by
  intro P _
  exact ⟨1, 0, isHomogeneous_one _ _, by simp, Set.subset_univ _⟩

theorem isProjOpen_inter {V W : Set (Proj k n)} (hV : IsProjOpen V) (hW : IsProjOpen W) :
    IsProjOpen (V ∩ W) := by
  intro P hP
  obtain ⟨A, d, hA, hAP, hAV⟩ := hV P hP.1
  obtain ⟨B, e, hB, hBP, hBW⟩ := hW P hP.2
  refine ⟨A * B, d + e, hA.mul hB, ?_, ?_⟩
  · simp only [eval_mul]; exact mul_ne_zero hAP hBP
  · intro Q hQ
    simp only [eval_mul] at hQ
    exact ⟨hAV (fun h => hQ (by rw [h, zero_mul])),
      hBW (fun h => hQ (by rw [h, mul_zero]))⟩

theorem isProjOpen_sUnion (S : Set (Set (Proj k n))) (hS : ∀ s ∈ S, IsProjOpen s) :
    IsProjOpen (⋃₀ S) := by
  intro P hP
  obtain ⟨s, hsS, hPs⟩ := Set.mem_sUnion.mp hP
  obtain ⟨A, d, hA, hAP, hAs⟩ := hS s hsS P hPs
  exact ⟨A, d, hA, hAP, fun Q hQ => Set.mem_sUnion.mpr ⟨s, hsS, hAs hQ⟩⟩

set_option warn.classDefReducibility false in
/-- The Zariski topology on `P^n`. -/
instance instTopologicalSpace : TopologicalSpace (Proj k n) where
  IsOpen := IsProjOpen
  isOpen_univ := isProjOpen_univ
  isOpen_inter := fun _ _ => isProjOpen_inter
  isOpen_sUnion := fun S hS => isProjOpen_sUnion S hS

end Proj



namespace Proj

/-- Classical projective regularity, again with an explicit source variety and an open
subset of it. -/
def RegularOn (X : Set (Proj k n)) (V : Set X) (f : V → k) : Prop :=
  ∀ x : V, ∃ (U : Set V), IsOpen U ∧ x ∈ U ∧ ∃ (g h : Poly k (n + 1)) (e : ℕ),
    g.IsHomogeneous e ∧ h.IsHomogeneous e ∧
      (∀ z ∈ U, h.eval (z.1 : Proj k n).rep ≠ 0) ∧
      ∀ z ∈ U, f z = ratio g h (z.1 : Proj k n)

/-- Continuous maps pulling back every classical regular function. -/
def IsMorphism {n m : ℕ} (X : Set (Proj k n)) (Y : Set (Proj k m)) (φ : X → Y) : Prop :=
  Continuous φ ∧ ∀ (V : Set Y), IsOpen V → ∀ f : V → k, RegularOn Y V f →
    RegularOn X (φ ⁻¹' V) (pullback φ f)

/-- Restriction to irreducible locally closed subvarieties, in the projective case. -/
theorem isMorphism_restrict_projective {n m : ℕ}
    {X : Set (Proj k n)} {Y : Set (Proj k m)}
    {X' : Set (Proj k n)} {Y' : Set (Proj k m)}
    (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y)
    (_hXi : IsIrreducible X') (_hXl : IsLocallyClosed X')
    (_hYi : IsIrreducible Y') (_hYl : IsLocallyClosed Y')
    (φ : X → Y) (hmap : ∀ x : X', (φ ⟨x.1, hXX' x.2⟩).1 ∈ Y')
    (hφ : IsMorphism X Y φ) :
    IsMorphism X' Y' (restrictedMap hXX' φ hmap) := by
  let ψ : X' → Y' := restrictedMap hXX' φ hmap
  have hc : Continuous ψ := by
    have hc0a : Continuous (fun x : X' => (φ ⟨x.1, hXX' x.2⟩ : Y).1) :=
      continuous_subtype_val.comp (hφ.1.comp (Continuous.subtype_mk continuous_subtype_val _))
    exact Continuous.subtype_mk hc0a (fun x => (ψ x).2)
  refine ⟨hc, fun V hV f hf x => ?_⟩
  obtain ⟨U, hU, hxU, g, h, e, hg, hh, hpq, hfrep⟩ := hf ⟨ψ x.1, x.2⟩
  let W : Set Y := {y | h.eval y.1.rep ≠ 0}
  have hW : IsOpen W := by
    change IsOpen (Subtype.val ⁻¹' {P : Proj k m | h.eval P.rep ≠ 0})
    apply IsOpen.preimage continuous_subtype_val
    change IsProjOpen {P : Proj k m | h.eval P.rep ≠ 0}
    intro P hP
    exact ⟨h, e, hh, hP, fun z hz => hz⟩
  let F : W → k := fun y => ratio g h (y.1 : Proj k m)
  have hF : RegularOn Y W F := by
    intro y
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, g, h, e, hg, hh,
      fun z hz => z.2, fun z hz => rfl⟩
  have hxW : h.eval (φ ⟨x.1.1, hXX' x.1.2⟩ : Y).1.rep ≠ 0 := by
    exact hpq ⟨ψ x.1, x.2⟩ hxU
  let z0 : φ ⁻¹' W := ⟨⟨x.1.1, hXX' x.1.2⟩, hxW⟩
  obtain ⟨T, hT, hzT, G, H, E, hG, hH, hQne, hRep⟩ := hφ.2 W hW F hF z0
  let L : Set (ψ ⁻¹' V) :=
    (fun z : ψ ⁻¹' V => (⟨ψ z.1, z.2⟩ : V)) ⁻¹' U
  have hCL : Continuous (fun z : ψ ⁻¹' V => (⟨ψ z.1, z.2⟩ : V)) :=
    Continuous.subtype_mk (hc.comp continuous_subtype_val) _
  have hL : IsOpen L :=
    hU.preimage hCL
  let J : L → (φ ⁻¹' W : Set X) := fun z =>
    ⟨⟨z.1.1.1, hXX' z.1.1.2⟩, hpq ⟨ψ z.1, z.1.2⟩ z.2⟩
  have hinc : Continuous (fun z : L => (⟨z.1.1.1, hXX' z.1.1.2⟩ : X)) :=
    Continuous.subtype_mk (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  have hJ : Continuous J := Continuous.subtype_mk hinc (fun z => (J z).2)
  let T' := J ⁻¹' T
  let T'' : Set (ψ ⁻¹' V) := Subtype.val '' T'
  have hT' : IsOpen T' := hT.preimage hJ
  have hT'' : IsOpen T'' := hL.isOpenEmbedding_subtypeVal.isOpenMap _ hT'
  refine ⟨T'', hT'', ?_, G, H, E, hG, hH, (fun z hz => ?_), fun z hz => ?_⟩
  · exact ⟨⟨x, hxU⟩, hzT, rfl⟩
  · obtain ⟨zL, hmem, rfl⟩ := hz
    exact hQne (J zL) hmem
  obtain ⟨zL, hmem, rfl⟩ := hz
  have hfq : f ⟨ψ zL.1.1, zL.1.2⟩ = ratio g h (ψ zL.1.1).1 :=
    hfrep ⟨ψ zL.1.1, zL.1.2⟩ zL.2
  change f ⟨ψ zL.1.1, zL.1.2⟩ = ratio G H zL.1.1.1
  rw [hfq]
  exact hRep (J zL) hmem

end Proj

/-- **Hartshorne I.3.10** for classical quasi-affine and quasi-projective varieties:
local closedness, and restriction of morphisms in both settings. -/
theorem hartshorne_I_3_10 {k : Type*} [Field k] :
    (∀ {X : Type*} [TopologicalSpace X] (S : Set X),
      IsLocallyClosed S ↔ IsOpen (closure S ↓∩ S)) ∧
    (∀ {n m : ℕ} {X : Set (ASpace k n)} {Y : Set (ASpace k m)}
      {X' : Set (ASpace k n)} {Y' : Set (ASpace k m)}
      (φ : X → Y) (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y),
      IsIrreducible X' → IsLocallyClosed X' → IsIrreducible Y' → IsLocallyClosed Y' →
      ∀ (hmap : ∀ x : X', (φ ⟨x.1, hXX' x.2⟩).1 ∈ Y'), IsMorphism X Y φ →
      IsMorphism X' Y' (restrictedMap hXX' φ hmap)) ∧
    (∀ {n m : ℕ} {X : Set (Proj k n)} {Y : Set (Proj k m)}
      {X' : Set (Proj k n)} {Y' : Set (Proj k m)}
      (φ : X → Y) (hXX' : X' ⊆ X) (hYY' : Y' ⊆ Y),
      IsIrreducible X' → IsLocallyClosed X' → IsIrreducible Y' → IsLocallyClosed Y' →
      ∀ (hmap : ∀ x : X', (φ ⟨x.1, hXX' x.2⟩).1 ∈ Y'), Proj.IsMorphism X Y φ →
      Proj.IsMorphism X' Y' (restrictedMap hXX' φ hmap)) := by
  refine ⟨locallyClosed_iff_open_in_closure, ?_, ?_⟩
  · intro n m X Y X' Y' φ hXX' hYY' hXi hXl hYi hYl hmap hφ
    exact isMorphism_restrict_affine hXX' hYY' hXi hXl hYi hYl φ hmap hφ
  · intro n m X Y X' Y' φ hXX' hYY' hXi hXl hYi hYl hmap hφ
    exact Proj.isMorphism_restrict_projective hXX' hYY' hXi hXl hYi hYl φ hmap hφ

#print axioms hartshorne_I_3_10
#print axioms isMorphism_restrict_affine
#print axioms Proj.isMorphism_restrict_projective
#print axioms locallyClosed_iff_open_in_closure
#print axioms Proj.ratio_mk

end Hartshorne77.Ex_I_3_10
