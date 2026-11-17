import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Hartshorne77.Ex_I_3_7

noncomputable section

open MvPolynomial

abbrev Vec (k : Type*) (n : ℕ) : Type _ := Fin (n + 1) → k

variable {k : Type*} [Field k] {n : ℕ}

def projRel (v w : {v : Vec k n // v ≠ 0}) : Prop := ∃ c : k, c ≠ 0 ∧ v.1 = c • w.1

theorem projRel_equivalence : Equivalence (projRel (k := k) (n := n)) where
  refl v := ⟨1, one_ne_zero, by simp⟩
  symm := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  trans := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨c, hc, h₁⟩ ⟨d, hd, h₂⟩
    exact ⟨c * d, mul_ne_zero hc hd, by rw [h₁, h₂, smul_smul]⟩

def projSetoid (k : Type*) [Field k] (n : ℕ) : Setoid {v : Vec k n // v ≠ 0} :=
  ⟨projRel, projRel_equivalence⟩

def P (k : Type*) [Field k] (n : ℕ) : Type _ := Quotient (projSetoid k n)

namespace P

def mk {v : Vec k n} (hv : v ≠ 0) : P k n := Quotient.mk _ ⟨v, hv⟩

theorem mk_eq_mk_iff {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (n := n) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w :=
  Quotient.eq

theorem mk_eq_mk_iff' {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk (k := k) (n := n) hv = mk hw ↔ ∃ c : k, c ≠ 0 ∧ c • v = w := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem mk_smul {c : k} (hc : c ≠ 0) {v : Vec k n} (hv : v ≠ 0) :
    mk (k := k) (n := n) (show c • v ≠ 0 from smul_ne_zero hc hv) = mk hv := by
  rw [mk_eq_mk_iff]
  exact ⟨c, hc, rfl⟩

theorem mk_smul' {c : k} (hc : c ≠ 0) {v : Vec k n} (hv : v ≠ 0) (hcv : c • v ≠ 0) :
    mk (k := k) (n := n) hcv = mk hv :=
  mk_smul hc hv

theorem exists_mk (p : P k n) : ∃ (v : Vec k n) (hv : v ≠ 0), mk hv = p := by
  induction p using Quotient.inductionOn with
  | h x => exact ⟨x.1, x.2, rfl⟩

def Line (k : Type*) [Field k] (n : ℕ) : Type _ :=
  {L : Submodule k (Vec k n) // Module.finrank k L = 1}

namespace Line

def ofVec (v : Vec k n) (hv : v ≠ 0) : Line k n :=
  ⟨Submodule.span k {v}, finrank_span_singleton hv⟩

theorem exists_ne_zero (L : Line k n) : ∃ v : Vec k n, v ∈ L.1 ∧ v ≠ 0 := by
  have hne : L.1 ≠ ⊥ := by
    intro h
    have h0 : Module.finrank k L.1 = 0 := by rw [h]; simp
    have h2 := L.2
    rw [h0] at h2
    exact zero_ne_one h2
  exact L.1.exists_mem_ne_zero_of_ne_bot hne

theorem span_eq_of_mem (L : Line k n) {v : Vec k n} (hv : v ∈ L.1) (hv0 : v ≠ 0) :
    Submodule.span k {v} = L.1 := by
  have hle : Submodule.span k {v} ≤ L.1 := Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)
  have h1 : Module.finrank k (Submodule.span k {v}) = 1 := finrank_span_singleton hv0
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, L.2])

theorem ofVec_eq_iff {v w : Vec k n} (hv : v ≠ 0) (hw : w ≠ 0) :
    ofVec v hv = ofVec w hw ↔ ∃ c : k, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro h
    have hspan : Submodule.span k {v} = Submodule.span k ({w} : Set (Vec k n)) :=
      congrArg Subtype.val h
    have hwmem : v ∈ Submodule.span k ({w} : Set (Vec k n)) := by
      rw [← hspan]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).1 hwmem
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    rw [zero_smul] at hc
    exact hv hc.symm
  · rintro ⟨c, hc, h⟩
    apply Subtype.ext
    have hv' : v ∈ Submodule.span k ({w} : Set (Vec k n)) := by
      rw [h]
      exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    have hw' : w ∈ Submodule.span k ({v} : Set (Vec k n)) := by
      have hwv : w = c⁻¹ • v := by
        rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hwv]
      exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (by simp))
    exact le_antisymm (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv'))
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hw'))

end Line

/-- The chosen nonzero point of a line, as a vector. -/
def LineRep (L : Line k n) : Vec k n := (Line.exists_ne_zero L).choose

theorem LineRep_mem (L : Line k n) : LineRep L ∈ L.1 := ((Line.exists_ne_zero L).choose_spec).1

theorem LineRep_ne_zero (L : Line k n) : LineRep L ≠ 0 := ((Line.exists_ne_zero L).choose_spec).2

def ofLine (L : Line k n) : P k n := mk (LineRep_ne_zero L)

theorem ofLine_eq_mk (L : Line k n) {v : Vec k n} (hv : v ∈ L.1) (hv0 : v ≠ 0) :
    ofLine L = mk hv0 := by
  have h1 : ofLine L = mk (LineRep_ne_zero L) := rfl
  rw [h1, mk_eq_mk_iff]
  have hspan : Submodule.span k {LineRep L} = Submodule.span k ({v} : Set (Vec k n)) := by
    rw [Line.span_eq_of_mem L (LineRep_mem L) (LineRep_ne_zero L),
      Line.span_eq_of_mem L hv hv0]
  have hmem : LineRep L ∈ Submodule.span k ({v} : Set (Vec k n)) := by
    rw [← hspan]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).1 hmem
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  exact LineRep_ne_zero L hc.symm

def toLine : P k n → Line k n :=
  Quotient.lift (fun x : {v : Vec k n // v ≠ 0} => Line.ofVec x.1 x.2) (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, h⟩
    exact (Line.ofVec_eq_iff hv hw).2 ⟨c, hc, h⟩)

theorem toLine_mk {v : Vec k n} (hv : v ≠ 0) :
    toLine (mk hv) = Line.ofVec v hv :=
  rfl

theorem toLine_mk_span {v : Vec k n} (hv : v ≠ 0) :
    (toLine (mk hv)).1 = Submodule.span k {v} := rfl

def equivLine : P k n ≃ Line k n where
  toFun := toLine
  invFun := ofLine
  left_inv := by
    intro p
    obtain ⟨v, hv, rfl⟩ := exists_mk p
    rw [toLine_mk]
    exact ofLine_eq_mk (Line.ofVec v hv) (Submodule.subset_span (by simp)) hv
  right_inv := by
    intro L
    have h1 : toLine (ofLine L) = Line.ofVec (LineRep L) (LineRep_ne_zero L) := by
      rw [ofLine, toLine_mk]
    rw [h1]
    exact Subtype.ext (Line.span_eq_of_mem L (LineRep_mem L) (LineRep_ne_zero L))

end P


/-! ## 2. Vanishing of homogeneous polynomials at projective points -/

/-- The polynomial ring `S = k[x_0,…,x_n]`. -/
abbrev Poly (k : Type*) [CommSemiring k] (n : ℕ) : Type _ := MvPolynomial (Fin (n + 1)) k

namespace P

variable {f g : Poly k n} {d : ℕ}

/-- **Homogeneity of evaluation**: for a homogeneous polynomial `f` of degree `d` and any
scalar `c`, `f(c·v) = c^d f(v)`.  This is what makes "`f` vanishes at the projective point"
independent of the chosen representative of the point. -/
theorem eval_smul_of_isHomogeneous (hf : f.IsHomogeneous d) (c : k) (v : Vec k n) :
    MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul]
  have hdeg : d = ∑ i ∈ s.support, s i := hf.degree_eq_sum_deg_support hs
  have h1 : (∏ i ∈ s.support, (c * v i) ^ (s i)) =
      (∏ i ∈ s.support, c ^ (s i)) * (∏ i ∈ s.support, (v i) ^ (s i)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => mul_pow c (v i) (s i))
  have h2 : (∏ i ∈ s.support, c ^ (s i)) = c ^ d := by
    rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
  rw [h1, h2]
  ring

/-- `f` vanishes at the projective point `p` if it vanishes at every representative of `p`.
(For homogeneous `f` this is independent of the representative, see
`formVanishesAt_mk_iff`.) -/
def FormVanishesAt (f : Poly k n) (p : P k n) : Prop :=
  ∀ (v : Vec k n) (hv : v ≠ 0), mk hv = p → MvPolynomial.eval v f = 0

theorem formVanishesAt_mk {v : Vec k n} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) → MvPolynomial.eval v f = 0 :=
  fun h => h v hv rfl

/-- Vanishing of a homogeneous polynomial at a projective point is well defined: it does not
depend on the representative. -/
theorem formVanishesAt_mk_iff (hf : f.IsHomogeneous d) {v : Vec k n} (hv : v ≠ 0) :
    FormVanishesAt f (mk hv) ↔ MvPolynomial.eval v f = 0 := by
  refine ⟨formVanishesAt_mk hv, ?_⟩
  intro h w hw hwp
  obtain ⟨c, hc, hwv⟩ := (mk_eq_mk_iff hw hv).1 hwp
  rw [hwv, eval_smul_of_isHomogeneous hf, h, mul_zero]

/-- The projective zero locus (Hartshorne's `V(T)`) of a set `T` of polynomials: the set of
points at which every polynomial of `T` vanishes.  For sets of *homogeneous* polynomials this
is Hartshorne's `V(T) ⊆ P^n`. -/
def zeroLocus (T : Set (Poly k n)) : Set (P k n) :=
  {p | ∀ f ∈ T, FormVanishesAt f p}

@[simp]
theorem mem_zeroLocus_iff {T : Set (Poly k n)} (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d)
    {v : Vec k n} (hv : v ≠ 0) :
    mk hv ∈ zeroLocus T ↔ ∀ f ∈ T, MvPolynomial.eval v f = 0 := by
  constructor
  · intro h f hf
    exact formVanishesAt_mk hv (h f hf)
  · intro h f hf
    obtain ⟨d, hd⟩ := hT f hf
    rw [formVanishesAt_mk_iff hd hv]
    exact h f hf

theorem zeroLocus_empty : zeroLocus (∅ : Set (Poly k n)) = Set.univ := by
  ext p
  simp [zeroLocus]

theorem zeroLocus_mono {T T' : Set (Poly k n)} (h : T ⊆ T') :
    zeroLocus T' ⊆ zeroLocus T :=
  fun _ hp f hf => hp f (h hf)

theorem zeroLocus_iUnion {ι : Type*} (T : ι → Set (Poly k n)) :
    zeroLocus (⋃ i, T i) = ⋂ i, zeroLocus (T i) := by
  ext p
  simp only [zeroLocus, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun h i f hf => h f ⟨i, hf⟩, fun h f ⟨i, hf⟩ => h i f hf⟩

theorem zeroLocus_union (T T' : Set (Poly k n)) :
    zeroLocus (T ∪ T') = zeroLocus T ∩ zeroLocus T' := by
  ext p
  simp only [zeroLocus, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun ⟨h1, h2⟩ f hf => hf.elim (h1 f) (h2 f)⟩

end P


namespace P

/-- The zero locus of the constant polynomial `1` is empty. -/
theorem zeroLocus_one_eq_empty :
    zeroLocus ({(1 : Poly k n)} : Set (Poly k n)) = ∅ := by
  have h1 : ∀ f ∈ ({(1 : Poly k n)} : Set (Poly k n)), ∃ d, f.IsHomogeneous d := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, MvPolynomial.isHomogeneous_one (σ := Fin (n + 1)) (R := k)⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff h1 hv]
  simp

/-- A union of projective zero loci is the zero locus of the products: over a field a product
vanishes iff one of the factors does.  This is Hartshorne's computation
`V(T_1) ∪ V(T_2) = V({fg : f ∈ T_1, g ∈ T_2})`, which makes the zero loci the closed sets of
a topology. -/
theorem zeroLocus_image2_mul_union {T T' : Set (Poly k n)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) (hT' : ∀ f ∈ T', ∃ d, f.IsHomogeneous d) :
    zeroLocus (Set.image2 (· * ·) T T') = zeroLocus T ∪ zeroLocus T' := by
  have hTT' : ∀ h ∈ Set.image2 (· * ·) T T', ∃ d, h.IsHomogeneous d := by
    rintro _ ⟨f, hf, g, hg, rfl⟩
    obtain ⟨d, hd⟩ := hT f hf
    obtain ⟨e, he⟩ := hT' g hg
    exact ⟨d + e, hd.mul he⟩
  ext p
  obtain ⟨v, hv, rfl⟩ := exists_mk p
  rw [mem_zeroLocus_iff hTT' hv, Set.mem_union, mem_zeroLocus_iff hT hv,
    mem_zeroLocus_iff hT' hv]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hfT, hfv⟩, ⟨g, hgT, hgv⟩⟩ := hc
    have h0 := h (f * g) ⟨f, hfT, g, hgT, rfl⟩
    rw [map_mul] at h0
    exact mul_ne_zero hfv hgv h0
  · rintro (h | h) h₁ h₂
    · obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
      rw [map_mul, h p₁ hp₁, zero_mul]
    · obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
      rw [map_mul, h p₂ hp₂, mul_zero]

/-! ## 3. The Zariski topology on `P^n` -/

set_option warn.classDefReducibility false in
/-- **The Zariski topology on `P^n`**: a set is open iff it is the complement of the zero
locus `V(T)` of a set `T` of homogeneous polynomials (Hartshorne I.2, p. 10). -/
def zariskiTopology : TopologicalSpace (P k n) where
  IsOpen U := ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ U = (zeroLocus T)ᶜ
  isOpen_univ := by
    have h1 : ∀ f ∈ ({(1 : Poly k n)} : Set (Poly k n)), ∃ d, f.IsHomogeneous d := by
      intro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨0, MvPolynomial.isHomogeneous_one (σ := Fin (n + 1)) (R := k)⟩
    exact ⟨{1}, h1, by rw [zeroLocus_one_eq_empty, Set.compl_empty]⟩
  isOpen_inter := by
    rintro U V ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
    refine ⟨Set.image2 (· * ·) T T', ?_, ?_⟩
    · rintro _ ⟨f, hf, g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hT f hf
      obtain ⟨e, he⟩ := hT' g hg
      exact ⟨d + e, hd.mul he⟩
    · rw [zeroLocus_image2_mul_union hT hT', Set.compl_union]
  isOpen_sUnion := by
    intro A hA
    have hA' : ∀ a : A, ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧
        (a : Set (P k n)) = (zeroLocus T)ᶜ := fun a => hA a a.2
    choose T hT hTA using hA'
    refine ⟨⋃ a : A, T a, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, hfa⟩ := Set.mem_iUnion.1 hf
      exact hT a f hfa
    · rw [zeroLocus_iUnion, Set.sUnion_eq_iUnion, Set.compl_iInter]
      exact Set.iUnion_congr fun a => hTA a

instance : TopologicalSpace (P k n) := zariskiTopology (k := k) (n := n)

/-- The closed sets of `P^n` are exactly the zero loci of sets of homogeneous
polynomials. -/
theorem isClosed_iff_exists_zeroLocus {Z : Set (P k n)} :
    IsClosed Z ↔ ∃ T : Set (Poly k n), (∀ f ∈ T, ∃ d, f.IsHomogeneous d) ∧ Z = zeroLocus T := by
  constructor
  · intro h
    obtain ⟨T, hT, hU⟩ := h.isOpen_compl
    exact ⟨T, hT, by rw [← compl_compl Z, hU, compl_compl]⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩

theorem isClosed_zeroLocus {T : Set (Poly k n)}
    (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) : IsClosed (zeroLocus T) :=
  isClosed_iff_exists_zeroLocus.2 ⟨T, hT, rfl⟩

end P


namespace P

/-! ### Vanishing ideals -/

/-- The set of all polynomials vanishing at every representative of every point of `Y`. -/
def VanishOn (Y : Set (P k n)) : Set (Poly k n) :=
  fun f => ∀ p ∈ Y, FormVanishesAt f p

theorem mem_vanishOn_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ VanishOn Y ↔ ∀ p ∈ Y, FormVanishesAt f p := Iff.rfl

/-- `VanishOn Y` is an ideal of `S = k[x_0,…,x_n]`. -/
def vanishOnIdeal (Y : Set (P k n)) : Ideal (Poly k n) where
  carrier := VanishOn Y
  zero_mem' := by
    intro p hp v hv _
    simp
  add_mem' := by
    intro f g hf hg p hp v hv hvp
    rw [map_add, hf p hp v hv hvp, hg p hp v hv hvp, add_zero]
  smul_mem' := by
    intro c f hf p hp v hv hvp
    rw [smul_eq_mul, map_mul, hf p hp v hv hvp, mul_zero]

theorem mem_vanishOnIdeal_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ vanishOnIdeal Y ↔ ∀ p ∈ Y, FormVanishesAt f p := Iff.rfl

/-- The homogeneous polynomials vanishing on `Y ⊆ P^n`. -/
def vanishingForms (Y : Set (P k n)) : Set (Poly k n) :=
  fun f => ∃ d, f.IsHomogeneous d ∧ ∀ p ∈ Y, FormVanishesAt f p

theorem mem_vanishingForms_iff {Y : Set (P k n)} {f : Poly k n} :
    f ∈ vanishingForms Y ↔ ∃ d, f.IsHomogeneous d ∧ ∀ p ∈ Y, FormVanishesAt f p :=
  Iff.rfl

theorem vanishingForms_subset_vanishOn (Y : Set (P k n)) :
    vanishingForms Y ⊆ vanishOnIdeal Y := by
  intro f h
  obtain ⟨d, hd, hf⟩ := mem_vanishingForms_iff.1 h
  exact mem_vanishOnIdeal_iff.2 hf

/-- **Hartshorne's `I(Y)`**: the ideal generated by the homogeneous polynomials vanishing on
`Y ⊆ P^n`. -/
def vanishingIdeal (Y : Set (P k n)) : Ideal (Poly k n) :=
  Ideal.span (vanishingForms Y)

theorem vanishingForms_mono {Y Y' : Set (P k n)} (h : Y ⊆ Y') :
    vanishingForms Y' ⊆ vanishingForms Y := by
  intro f hf
  obtain ⟨d, hd, hf'⟩ := mem_vanishingForms_iff.1 hf
  exact mem_vanishingForms_iff.2 ⟨d, hd, fun p hp => hf' p (h hp)⟩

theorem vanishingIdeal_le_vanishOn (Y : Set (P k n)) : vanishingIdeal Y ≤ vanishOnIdeal Y :=
  Ideal.span_le.2 (vanishingForms_subset_vanishOn Y)

/-- The vanishing ideal is monotone: a smaller set has a larger vanishing ideal. -/
theorem vanishingIdeal_mono {Y Y' : Set (P k n)} (h : Y ⊆ Y') :
    vanishingIdeal Y' ≤ vanishingIdeal Y :=
  Ideal.span_mono (vanishingForms_mono h)

theorem vanishingForms_homogeneous (Y : Set (P k n)) :
    ∀ f ∈ vanishingForms Y, ∃ d, f.IsHomogeneous d := by
  intro f h
  obtain ⟨d, hd, -⟩ := mem_vanishingForms_iff.1 h
  exact ⟨d, hd⟩

/-- Any ideal generated by polynomials vanishing on `Z` vanishes on `Z`. -/
theorem span_le_vanishOn {S : Set (Poly k n)} {Z : Set (P k n)}
    (h : S ⊆ vanishOnIdeal Z) : Ideal.span S ≤ vanishOnIdeal Z :=
  Ideal.span_le.2 h

/-- The zero locus of `I(Y)` is the zero locus of the homogeneous polynomials vanishing on
`Y`: only homogeneous generators are needed to test vanishing at a point. -/
theorem vanishingForms_le_vanishOn_zeroLocus (Y : Set (P k n)) :
    vanishingForms Y ⊆ vanishOnIdeal (zeroLocus (vanishingForms Y)) := by
  intro g hg p hp
  exact hp g hg

theorem zeroLocus_vanishingIdeal_eq_zeroLocus_forms (Y : Set (P k n)) :
    zeroLocus (vanishingIdeal Y : Set (Poly k n)) = zeroLocus (vanishingForms Y) := by
  refine le_antisymm (zeroLocus_mono (Ideal.subset_span (s := vanishingForms Y))) ?_
  intro p hp f hf
  exact mem_vanishOnIdeal_iff.1
    (span_le_vanishOn (vanishingForms_le_vanishOn_zeroLocus Y) hf) p hp

/-- `V(I(Y))` is closed. -/
theorem isClosed_zeroLocus_vanishingIdeal (Y : Set (P k n)) :
    IsClosed (zeroLocus (vanishingIdeal Y : Set (Poly k n))) := by
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms]
  exact isClosed_zeroLocus (vanishingForms_homogeneous Y)

/-- `Y` is contained in `V(I(Y))`. -/
theorem subset_zeroLocus_vanishingIdeal (Y : Set (P k n)) :
    Y ⊆ zeroLocus (vanishingIdeal Y : Set (Poly k n)) := by
  intro p hp f hf
  exact mem_vanishOnIdeal_iff.1 (vanishingIdeal_le_vanishOn Y hf) p hp

/-- **`V(I(Z)) = Z` for closed `Z ⊆ P^n`** (the closed case of Hartshorne Ex. I.2.3(e)). -/
theorem zeroLocus_vanishingIdeal_eq {Z : Set (P k n)} (hZ : IsClosed Z) :
    zeroLocus (vanishingIdeal Z : Set (Poly k n)) = Z := by
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hZ
  refine le_antisymm ?_ (subset_zeroLocus_vanishingIdeal (zeroLocus T))
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms]
  refine zeroLocus_mono ?_
  intro f hf
  obtain ⟨d, hd⟩ := hT f hf
  exact mem_vanishingForms_iff.2 ⟨d, hd, fun p hp => hp f hf⟩

/-- The closure of a set is the intersection of the closed sets containing it. -/
theorem closure_eq_sInter (Y : Set (P k n)) :
    closure Y = ⋂₀ {F : Set (P k n) | IsClosed F ∧ Y ⊆ F} := by
  refine le_antisymm ?_ ?_
  · refine Set.subset_sInter ?_
    rintro F ⟨hFc, hYF⟩
    exact closure_minimal hYF hFc
  · exact Set.sInter_subset_of_mem ⟨isClosed_closure, subset_closure⟩

/-- **`V(I(Y)) = closure Y`** for an arbitrary `Y ⊆ P^n` (Hartshorne Ex. I.2.3(e)). -/
theorem zeroLocus_vanishingIdeal_eq_closure (Y : Set (P k n)) :
    zeroLocus (vanishingIdeal Y : Set (Poly k n)) = closure Y := by
  refine le_antisymm ?_ (closure_minimal (subset_zeroLocus_vanishingIdeal Y)
    (isClosed_zeroLocus_vanishingIdeal Y))
  rw [zeroLocus_vanishingIdeal_eq_zeroLocus_forms, closure_eq_sInter]
  intro p hp
  rw [Set.mem_sInter]
  intro F hF
  obtain ⟨hFc, hYF⟩ := hF
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_exists_zeroLocus.1 hFc
  intro f hf
  obtain ⟨d, hd⟩ := hT f hf
  exact hp f (mem_vanishingForms_iff.2 ⟨d, hd, fun q hq => hYF hq f hf⟩)

end P


namespace P

/-! ## 4. Part (a): `P^n` is a noetherian topological space

Hartshorne's proof: a descending chain of closed subsets `F_0 ⊇ F_1 ⊇ …` gives an ascending
chain of homogeneous ideals `I(F_0) ⊆ I(F_1) ⊆ …` in the noetherian ring `S = k[x_0,…,x_n]`,
which stabilizes; since `V(I(F)) = F` for closed `F`, the closed sets stabilize. -/

/-- **Part (a) of Hartshorne Ex. I.2.5**: every descending sequence of closed subsets of
`P^n` is eventually constant, i.e. `P^n` is a noetherian topological space. -/
theorem dcc_closed (F : ℕ → Set (P k n)) (hF : ∀ i, IsClosed (F i))
    (hanti : ∀ i, F (i + 1) ⊆ F i) :
    ∃ N, ∀ i, N ≤ i → F i = F N := by
  -- the vanishing ideals form an ascending chain
  have hmono : ∀ i, vanishingIdeal (F i) ≤ vanishingIdeal (F (i + 1)) :=
    fun i => vanishingIdeal_mono (hanti i)
  have hmono' : Monotone fun i => vanishingIdeal (F i) := monotone_nat_of_le_succ hmono
  -- which stabilizes because `S` is noetherian
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun i => vanishingIdeal (F i), hmono'⟩ : ℕ →o Ideal (Poly k n))
  refine ⟨N, fun i hi => ?_⟩
  have hI : vanishingIdeal (F i) = vanishingIdeal (F N) := (hN i hi).symm
  calc F i = zeroLocus (vanishingIdeal (F i) : Set (Poly k n)) :=
        (zeroLocus_vanishingIdeal_eq (hF i)).symm
    _ = zeroLocus (vanishingIdeal (F N) : Set (Poly k n)) := by rw [hI]
    _ = F N := zeroLocus_vanishingIdeal_eq (hF N)

/-- `P^n` is a noetherian topological space, in Mathlib's sense (ascending chain condition
for open subsets), equivalent to `dcc_closed`. -/
theorem noetherianSpace : TopologicalSpace.NoetherianSpace (P k n) := by
  rw [TopologicalSpace.NoetherianSpace, wellFoundedGT_iff_monotone_chain_condition]
  intro U
  -- `U` is a monotone sequence of open subsets
  have hclosed : ∀ i, IsClosed ((U i : Set (P k n))ᶜ) := fun i =>
    (show IsOpen ((U i : Set (P k n))) from (U i).2).isClosed_compl
  have hanti : ∀ i, (U (i + 1) : Set (P k n))ᶜ ⊆ (U i : Set (P k n))ᶜ :=
    fun i => compl_anti (U.monotone (Nat.le_succ i))
  obtain ⟨N, hN⟩ := dcc_closed (fun i => (U i : Set (P k n))ᶜ) hclosed hanti
  refine ⟨N, fun m hm => ?_⟩
  exact TopologicalSpace.Opens.ext (by simpa using (congrArg compl (hN m hm)).symm)

end P

namespace P

variable {k : Type*} [Field k] {n : ℕ}

/-! ## 6. The affine cone over a projective set, and the standard affine charts -/

/-- **The affine cone** over `Y ⊆ P^n`: the union of the lines through the origin in `k^{n+1}`
corresponding to the points of `Y`, together with the origin. -/
def cone (Y : Set (P k n)) : Set (Vec k n) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, mk hv ∈ Y}

theorem mem_cone_iff {Y : Set (P k n)} {v : Vec k n} (hv : v ≠ 0) :
    v ∈ cone Y ↔ mk hv ∈ Y := by
  constructor
  · rintro (h | ⟨hw, hm⟩)
    · exact absurd h hv
    · exact hm
  · intro h
    exact Or.inr ⟨hv, h⟩

theorem zero_mem_cone (Y : Set (P k n)) : (0 : Vec k n) ∈ cone Y := Or.inl rfl

/-- The affine cone is a union of lines through the origin: it is stable under multiplication
by nonzero scalars. -/
theorem smul_mem_cone_iff {Y : Set (P k n)} {c : k} (hc : c ≠ 0) (v : Vec k n) :
    c • v ∈ cone Y ↔ v ∈ cone Y := by
  by_cases hv : v = 0
  · subst hv
    simp
  · have hcv : c • v ≠ 0 := smul_ne_zero hc hv
    rw [mem_cone_iff hcv, mem_cone_iff hv, mk_smul' hc hv hcv]

/-- The affine cone over the projective zero locus `V(T)` of homogeneous polynomials is the
affine zero locus of `T` (together with the origin; the origin is only missing when `T`
contains a nonzero constant). -/
theorem cone_zeroLocus {T : Set (Poly k n)} (hT : ∀ f ∈ T, ∃ d, f.IsHomogeneous d) :
    cone (zeroLocus T) = {v : Vec k n | ∀ f ∈ T, MvPolynomial.eval v f = 0} ∪ {0} := by
  ext v
  by_cases hv : v = 0
  · subst hv
    simp [zero_mem_cone]
  · rw [mem_cone_iff hv, mem_zeroLocus_iff hT hv, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    exact ⟨fun h => Or.inl h, fun h => h.resolve_right hv⟩



end P
section PointHeight

variable (k : Type*) [Field k]

/-- Substitution sending `X i` to the constant `a i` for `i < j`, and fixing the other variables. -/
noncomputable def substBelow {s : ℕ} (j : ℕ) (a : Fin s → k) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  MvPolynomial.aeval fun i => if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k)
    else MvPolynomial.X i

lemma substBelow_X {s : ℕ} (j : ℕ) (a : Fin s → k) (i : Fin s) :
    substBelow k j a (MvPolynomial.X i) =
      if (i : ℕ) < j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i := by
  simp [substBelow]

lemma substBelow_zero {s : ℕ} (a : Fin s → k) : substBelow k 0 a = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substBelow_X]

lemma substBelow_succ {s : ℕ} (j : ℕ) (a : Fin s → k) :
    substBelow k (j + 1) a = (MvPolynomial.aeval fun (i : Fin s) =>
      if (i : ℕ) = j then (MvPolynomial.C (a i) : MvPolynomial (Fin s) k) else MvPolynomial.X i).comp
      (substBelow k j a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, substBelow_X, substBelow_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (by omega), MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  · rw [if_neg h]
    by_cases h2 : (i : ℕ) = j
    · rw [MvPolynomial.aeval_X, if_pos h2, if_pos (by omega)]
    · rw [MvPolynomial.aeval_X, if_neg h2, if_neg (by omega)]

lemma ker_substBelow_antitone {s : ℕ} (j : ℕ) (a : Fin s → k) :
    RingHom.ker (substBelow k j a) ≤ RingHom.ker (substBelow k (j + 1) a) := by
  intro f hf
  simp only [RingHom.mem_ker] at hf ⊢
  rw [substBelow_succ, AlgHom.comp_apply, hf, map_zero]

lemma X_sub_C_mem_ker_substBelow_succ {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∈
      RingHom.ker (substBelow k (j + 1) a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_pos (show ((⟨j, hj⟩ : Fin s) : ℕ) < j + 1 from by simp)]
  simp

lemma X_sub_C_notMem_ker_substBelow {s : ℕ} (j : ℕ) (hj : j < s) (a : Fin s → k) :
    (MvPolynomial.X ⟨j, hj⟩ - MvPolynomial.C (a ⟨j, hj⟩)) ∉
      RingHom.ker (substBelow k j a) := by
  simp only [RingHom.mem_ker, map_sub, substBelow_X]
  rw [if_neg (show ¬ ((⟨j, hj⟩ : Fin s) : ℕ) < j from by simp)]
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => a ⟨j, hj⟩ + 1)) h
  simp at h2

end PointHeight

section Height

variable (k : Type*) [Field k]

/-- The ideal of polynomials vanishing at a point of affine `s`-space has height `s`. -/
theorem vanishingIdeal_singleton_height (s : ℕ) (a : Fin s → k) :
    (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height = ↑s := by
  have hker : RingHom.ker (substBelow k s a) = MvPolynomial.vanishingIdeal k {a} := by
    have heq : substBelow k s a =
        (Algebra.ofId k (MvPolynomial (Fin s) k)).comp (MvPolynomial.aeval a) := by
      rw [MvPolynomial.comp_aeval]
      apply MvPolynomial.algHom_ext
      intro i
      rw [substBelow_X, if_pos i.isLt, MvPolynomial.aeval_X, Algebra.ofId_apply,
        MvPolynomial.algebraMap_eq]
    have hinj : Function.Injective (algebraMap k (MvPolynomial (Fin s) k)) :=
      FaithfulSMul.algebraMap_injective k _
    rw [heq]
    ext p
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Algebra.ofId_apply,
      MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : (MvPolynomial.aeval a) p = 0 := hinj (by simpa using h)
      intro x hx
      rw [hx]
      exact h0
    · intro h
      rw [h a rfl, map_zero]
  have hlower : (↑s : ℕ∞) ≤ (MvPolynomial.vanishingIdeal k {a} :
      Ideal (MvPolynomial (Fin s) k)).height := by
    rw [← hker]
    have key : ∀ j ≤ s, (↑j : ℕ∞) ≤ (RingHom.ker (substBelow k j a)).height := by
      intro j
      induction j with
      | zero => intro _; exact bot_le
      | succ m ih =>
        intro hm
        have hms : m < s := by omega
        have h1 : (RingHom.ker (substBelow k m a)).IsPrime := RingHom.ker_isPrime _
        have h2 : (RingHom.ker (substBelow k (m + 1) a)).IsPrime := RingHom.ker_isPrime _
        have hlt : RingHom.ker (substBelow k m a) < RingHom.ker (substBelow k (m + 1) a) :=
          lt_of_le_of_ne (ker_substBelow_antitone k m a)
            (fun heq => X_sub_C_notMem_ker_substBelow k m hms a (heq ▸
              X_sub_C_mem_ker_substBelow_succ k m hms a))
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have him := ih (by omega : m ≤ s)
        calc (↑(m + 1) : ℕ∞) = (↑m : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (substBelow k m a)).height + 1 := by gcongr
          _ ≤ (RingHom.ker (substBelow k (m + 1) a)).height := hstep
    exact key s le_rfl
  have hupper : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).height ≤ ↑s := by
    haveI : (MvPolynomial.vanishingIdeal k {a} : Ideal (MvPolynomial (Fin s) k)).IsMaximal :=
      inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := MvPolynomial.vanishingIdeal k {a})
      (Ideal.IsMaximal.ne_top ‹(MvPolynomial.vanishingIdeal k {a} :
        Ideal (MvPolynomial (Fin s) k)).IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  exact le_antisymm hupper hlower

end Height

/-! ## 7. The ideal `m₀` of the origin of `k^{n+1}` -/

section AffineOrigin

variable (k : Type*) [Field k] (n : ℕ)

/-- `m₀ = (x₀,…,xₙ)`, the maximal ideal of the origin of `k^{n+1}`: the vanishing ideal of the
point `0` (Hartshorne's `𝔪` for the origin of affine space). -/
def m0 : Ideal (Poly k n) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Poly k n))

lemma X_mem_m0 (i : Fin (n + 1)) : (MvPolynomial.X i : Poly k n) ∈ m0 k n :=
  Ideal.subset_span ⟨i, rfl⟩

/-- A polynomial belongs to `m₀` exactly when it vanishes at the origin. -/
theorem mem_m0_iff {f : Poly k n} :
    f ∈ m0 k n ↔ MvPolynomial.eval (0 : Vec k n) f = 0 := by
  have hspan : m0 k n = Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (n + 1)))) := by
    rw [m0, Set.image_univ]
  rw [hspan, MvPolynomial.mem_ideal_span_X_image, MvPolynomial.eval_zero,
    MvPolynomial.constantCoeff_eq]
  constructor
  · intro h
    by_contra hc
    have h0 : (0 : Fin (n + 1) →₀ ℕ) ∈ f.support := by
      rwa [MvPolynomial.mem_support_iff]
    obtain ⟨i, -, hi⟩ := h 0 h0
    exact hi (by simp)
  · intro h m hm
    by_contra hc
    simp only [not_exists] at hc
    have hm0 : m = 0 := Finsupp.ext fun a => by
      by_contra hne
      exact hc a ⟨Set.mem_univ a, hne⟩
    subst hm0
    have hne : MvPolynomial.coeff (0 : Fin (n + 1) →₀ ℕ) f ≠ 0 := by
      rwa [MvPolynomial.mem_support_iff] at hm
    exact hne h

/-- `m₀` is a maximal ideal: `k[x₀,…,xₙ]/m₀ = k`. -/
theorem m0_isMaximal : (m0 k n).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨?_, ?_⟩
  · intro h1
    have h2 : MvPolynomial.eval (0 : Vec k n) (1 : Poly k n) = 0 := (mem_m0_iff k n).mp h1
    simp at h2
  · intro J x hJ hx hxJ
    have hxe : MvPolynomial.eval (0 : Vec k n) x ≠ 0 := fun h => hx ((mem_m0_iff k n).mpr h)
    set c := MvPolynomial.eval (0 : Vec k n) x with hc
    have hmem : x - MvPolynomial.C c ∈ m0 k n := by
      rw [mem_m0_iff]
      simp [hc]
    have h1 : MvPolynomial.C c ∈ J := by
      have h2 := J.sub_mem hxJ (hJ hmem)
      simpa using h2
    have hunit : IsUnit (MvPolynomial.C c : Poly k n) :=
      ⟨⟨MvPolynomial.C c, MvPolynomial.C c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hxe, map_one],
        by rw [← map_mul, inv_mul_cancel₀ hxe, map_one]⟩, rfl⟩
    obtain ⟨v, hv⟩ := hunit
    have h2 : (1 : Poly k n) ∈ J := by
      have hmul : (↑v : Poly k n) * ↑v⁻¹ ∈ J := J.mul_mem_right _ (hv ▸ h1)
      rwa [Units.mul_inv] at hmul
    exact h2

end AffineOrigin

/-! ## 8. The origin is the only point of the affine zero locus -/

section RadicalBridge

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- The vanishing ideal of the origin is `m₀`. -/
theorem vanishingIdeal_singleton_zero :
    (MvPolynomial.vanishingIdeal k {(0 : Vec k n)} : Ideal (Poly k n)) = m0 k n := by
  ext f
  rw [MvPolynomial.mem_vanishingIdeal_iff, mem_m0_iff]
  simp

/-- **Nullstellensatz bridge.**  If the affine zero locus of `I` is contained in the origin,
then `m₀ ⊆ √I`. -/
theorem m0_le_radical_of_zeroLocus_subset (I : Ideal (Poly k n))
    (hI : MvPolynomial.zeroLocus k I ⊆ {(0 : Vec k n)}) : m0 k n ≤ I.radical := by
  have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I
  rw [← vanishingIdeal_singleton_zero k n, ← h]
  exact MvPolynomial.vanishingIdeal_anti_mono hI

end RadicalBridge

/-! ## 9. Graded vanishing: if every variable is nilpotent mod `I`, all high-degree forms are in `I` -/

section GradedVanishing

variable (k : Type*) [Field k] (n : ℕ)

/-- **Key degree computation.**  If `xᵢ^(cᵢ) ∈ I` for every variable, then every homogeneous
polynomial whose degree is at least `∑ cᵢ` lies in `I` (a monomial of degree `d ≥ ∑ cᵢ` is
divisible by one of the `xᵢ^(cᵢ)` — pigeonhole). -/
theorem mem_of_isHomogeneous_of_forall_X_pow_mem (I : Ideal (Poly k n)) (c : Fin (n + 1) → ℕ)
    (hc : ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ I)
    (f : Poly k n) (d : ℕ) (hf : f.IsHomogeneous d) (hd : ∑ i, c i ≤ d) : f ∈ I := by
  have hdeg : ∀ m ∈ f.support, ∑ i ∈ m.support, m i = d := by
    intro m hm
    exact (hf.degree_eq_sum_deg_support hm).symm
  have hsum : ∀ m ∈ f.support, ∑ i, m i = d := by
    intro m hm
    rw [← hdeg m hm]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => by simpa using hi)).symm
  have hmono : ∀ m ∈ f.support, MvPolynomial.monomial m (MvPolynomial.coeff m f) ∈ I := by
    intro m hm
    have hex : ∃ i, c i ≤ m i := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      have h1 : ∑ i, m i < ∑ i, c i :=
        Finset.sum_lt_sum (fun i _ => le_of_lt (hcon i)) ⟨0, Finset.mem_univ 0, hcon 0⟩
      rw [hsum m hm] at h1
      exact absurd h1 (not_lt.mpr hd)
    obtain ⟨i, hi⟩ := hex
    have hXi : (MvPolynomial.X i : Poly k n) ^ (m i) ∈ I := by
      have hsplit : m i = c i + (m i - c i) := (Nat.add_sub_cancel' hi).symm
      rw [hsplit, pow_add]
      exact Ideal.mul_mem_right _ _ (hc i)
    have hdec : (MvPolynomial.X i : Poly k n) ^ (m i) *
        MvPolynomial.monomial (m - Finsupp.single i (m i)) (MvPolynomial.coeff m f)
          = MvPolynomial.monomial m (MvPolynomial.coeff m f) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
      congr 2
      · exact add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (le_refl (m i)))
      · simp
    rw [← hdec]
    exact Ideal.mul_mem_right _ _ hXi
  rw [MvPolynomial.as_sum f]
  refine Ideal.sum_mem _ ?_
  intro m hm
  exact hmono m hm

/-- Consequently every prime containing `I` contains `m₀`. -/
theorem m0_le_of_isPrime (I : Ideal (Poly k n)) (c : Fin (n + 1) → ℕ)
    (hc : ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ I) {P : Ideal (Poly k n)}
    (hP : P.IsPrime) (hIP : I ≤ P) : m0 k n ≤ P := by
  rw [m0, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hP.mem_of_pow_mem _ (hIP (hc i))

/-- If `m₀ ⊆ √I` then there are exponents `cᵢ` with `xᵢ^(cᵢ) ∈ I`. -/
theorem exists_X_pow_mem (I : Ideal (Poly k n)) (h : m0 k n ≤ I.radical) :
    ∃ c : Fin (n + 1) → ℕ, ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ I :=
  ⟨fun i => Classical.choose (Ideal.mem_radical_iff.mp (h (X_mem_m0 k n i))),
    fun i => Classical.choose_spec (Ideal.mem_radical_iff.mp (h (X_mem_m0 k n i)))⟩

/-- `k[x₀,…,xₙ]/I` is zero-dimensional when `I ⊆ m₀` and a power of every variable lies in `I`. -/
theorem krullDimLE_zero_quotient (I : Ideal (Poly k n)) (hI : I ≤ m0 k n) (c : Fin (n + 1) → ℕ)
    (hc : ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ I) :
    Ring.KrullDimLE 0 (Poly k n ⧸ I) := by
  rw [Ring.krullDimLE_zero_iff]
  intro P' hP'
  have hQprime : (P'.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.IsPrime.comap _
  have hIQ : I ≤ P'.comap (Ideal.Quotient.mk I) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P'.zero_mem
  have hm0Q : m0 k n ≤ P'.comap (Ideal.Quotient.mk I) := m0_le_of_isPrime k n I c hc hQprime hIQ
  have hQne : P'.comap (Ideal.Quotient.mk I) ≠ ⊤ := hQprime.ne_top
  have hQeq : P'.comap (Ideal.Quotient.mk I) = m0 k n :=
    ((m0_isMaximal k n).eq_of_le hQne hm0Q).symm
  have hP'map : P' = (m0 k n).map (Ideal.Quotient.mk I) := by
    rw [← hQeq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hP'map]
  haveI hmax : (m0 k n).IsMaximal := m0_isMaximal k n
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]; exact hI)

end GradedVanishing

/-! ## 10. Part (a): any two curves in `P²` meet -/

section PartA

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A nonzero form of positive degree vanishes at the origin. -/
lemma homog_pos_mem_m0 (n : ℕ) {f : Poly k n} (hf : ∃ d, 0 < d ∧ f.IsHomogeneous d) :
    f ∈ m0 k n := by
  obtain ⟨d, hd, hfd⟩ := hf
  rw [mem_m0_iff, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  by_contra hc
  have hmem : (0 : Fin (n + 1) →₀ ℕ) ∈ f.support := by
    rwa [MvPolynomial.mem_support_iff]
  have h := hfd.degree_eq_sum_deg_support hmem
  simp at h
  omega

/-- An ideal generated by forms of positive degree is contained in `m₀`. -/
lemma span_forms_le_m0 (n : ℕ) (f g : Poly k n) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf : ∃ d, 0 < d ∧ f.IsHomogeneous d) (hg : ∃ d, 0 < d ∧ g.IsHomogeneous d) :
    Ideal.span ({f, g} : Set (Poly k n)) ≤ m0 k n := by
  rw [Ideal.span_le]
  rintro x (rfl | rfl)
  · exact homog_pos_mem_m0 k n hf
  · exact homog_pos_mem_m0 k n hg

/-- **Hartshorne, Algebraic Geometry, Exercise I.3.7(a).**  Any two curves in the projective
plane `P²` have a nonempty intersection.

Curves in `P²` are, by Ex. I.2.8, exactly the zero loci `V(h)` of irreducible forms `h` of
positive degree, so it suffices (and is stronger) to prove the statement for two arbitrary
nonzero forms `f, g` of positive degree: their projective zero loci meet. -/
theorem hartshorne_I_3_7_a (f g : Poly k 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf : ∃ d, 0 < d ∧ f.IsHomogeneous d) (hg : ∃ d, 0 < d ∧ g.IsHomogeneous d) :
    (P.zeroLocus ({f} : Set (Poly k 2)) ∩ P.zeroLocus {g}).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- (1) the affine zero locus of `I = (f,g)` is contained in the origin
  have hZ : MvPolynomial.zeroLocus k (Ideal.span ({f, g} : Set (Poly k 2)))
      ⊆ {(0 : Vec k 2)} := by
    intro u hu
    by_contra hu0
    have hu0' : u ≠ 0 := by simpa using hu0
    have hfu : MvPolynomial.eval u f = 0 := by
      have := hu f (Ideal.subset_span (by simp))
      simpa using this
    have hgu : MvPolynomial.eval u g = 0 := by
      have := hu g (Ideal.subset_span (by simp))
      simpa using this
    have hmem : (P.mk hu0' : P k 2) ∈ P.zeroLocus ({f} : Set (Poly k 2)) ∩ P.zeroLocus {g} := by
      constructor
      · rw [P.mem_zeroLocus_iff (by rintro x rfl; obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩) hu0']
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hfu
      · rw [P.mem_zeroLocus_iff (by rintro x rfl; obtain ⟨d, -, hd⟩ := hg; exact ⟨d, hd⟩) hu0']
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hgu
    rw [hempty] at hmem
    exact hmem
  -- (2) Nullstellensatz: `m₀ ⊆ √I`, so some power of each variable lies in `I`
  have hm0rad : m0 k 2 ≤ (Ideal.span ({f, g} : Set (Poly k 2))).radical :=
    m0_le_radical_of_zeroLocus_subset k 2 _ hZ
  obtain ⟨c, hc⟩ := exists_X_pow_mem k 2 _ hm0rad
  have hIle : Ideal.span ({f, g} : Set (Poly k 2)) ≤ m0 k 2 :=
    span_forms_le_m0 k 2 f g hf0 hg0 hf hg
  have hcoe : (↑({f, g} : Finset (Poly k 2)) : Set (Poly k 2)) = {f, g} := by
    rw [Finset.coe_insert, Finset.coe_singleton]
  -- (3) `m₀` is minimal over the two-generator ideal `I`, so its height is at most 2
  have hmin : m0 k 2 ∈ (Ideal.span (↑({f, g} : Finset (Poly k 2)))).minimalPrimes := by
    rw [hcoe]
    refine ⟨⟨(m0_isMaximal k 2).isPrime, hIle⟩, ?_⟩
    rintro q' ⟨hq'prime, hq'le⟩ hq'm0
    exact m0_le_of_isPrime k 2 (Ideal.span ({f, g} : Set (Poly k 2))) c hc hq'prime hq'le
  have hheight : (m0 k 2).height ≤ (({f, g} : Finset (Poly k 2)).card : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  -- (4) but the height of `m₀` in `k[x₀,x₁,x₂]` is three
  have h3 : (m0 k 2).height = 3 := by
    rw [← vanishingIdeal_singleton_zero k 2]
    exact vanishingIdeal_singleton_height (s := 3) (a := 0)
  rw [h3] at hheight
  have hc2 : (({f, g} : Finset (Poly k 2))).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le f {g}) ?_
    simp
  have hle : (3 : ℕ∞) ≤ (2 : ℕ∞) := le_trans hheight (by exact_mod_cast hc2)
  norm_num at hle

end PartA

/-! ## 11. The restriction of a polynomial to the line `t ↦ t • v` -/

section LineSubstitution

variable {k : Type*} [Field k] {n : ℕ}

namespace P

/-- For a fixed vector `v : k^{n+1}`, the one-variable polynomial `t ↦ f (t • v)`. -/
def substLine (v : Vec k n) : Poly k n →ₐ[k] Polynomial k :=
  MvPolynomial.aeval fun i => Polynomial.C (v i) * Polynomial.X

@[simp] theorem substLine_X (v : Vec k n) (i : Fin (n + 1)) :
    substLine v (MvPolynomial.X i) = Polynomial.C (v i) * Polynomial.X := by
  simp [substLine]

theorem substLine_eval (v : Vec k n) (f : Poly k n) (t : k) :
    (substLine v f).eval t = MvPolynomial.eval (t • v) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [substLine]
  | add f g hf hg =>
      rw [map_add, Polynomial.eval_add, hf, hg, MvPolynomial.eval_add]
  | mul_X f i hf =>
      rw [map_mul, Polynomial.eval_mul, hf, substLine_X, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [Pi.smul_apply, smul_eq_mul]
      ring

/-- Coefficients of a finite sum of monomials `C (a j) * X^j` for `j ≤ D`. -/
theorem coeff_sum_range_C_mul_X (a : ℕ → k) :
    ∀ (D d : ℕ),
      (∑ j ∈ Finset.range (D + 1), Polynomial.C (a j) * Polynomial.X ^ j).coeff d
        = if d ≤ D then a d else 0
  | 0, d => by
      rw [Finset.sum_range_one, pow_zero, mul_one, Polynomial.coeff_C]
      by_cases h : d = 0
      · subst h; simp
      · rw [if_neg h, if_neg (by omega)]
  | D + 1, d => by
      rw [Finset.sum_range_succ, Polynomial.coeff_add, coeff_sum_range_C_mul_X a D d,
        Polynomial.coeff_C_mul_X_pow]
      by_cases h : d ≤ D
      · rw [if_pos h, if_neg (by omega : ¬ d = D + 1), if_pos (by omega : d ≤ D + 1), add_zero]
      · by_cases h4 : d = D + 1
        · subst h4
          rw [if_neg (by omega : ¬ (D + 1 ≤ D)), if_pos rfl,
            if_pos (le_refl (D + 1)), zero_add]
        · rw [if_neg h, if_neg h4, if_neg (by omega : ¬ d ≤ D + 1), add_zero]

/-- The coefficient of `X^d` in `t ↦ f(t • v)` is the value of the degree-`d` homogeneous
component of `f` at `v`. -/
theorem substLine_coeff [Infinite k] (v : Vec k n) (f : Poly k n) (d : ℕ) :
    (substLine v f).coeff d = MvPolynomial.eval v (MvPolynomial.homogeneousComponent d f) := by
  classical
  set D := f.totalDegree
  set Q : Polynomial k :=
    ∑ j ∈ Finset.range (D + 1),
      Polynomial.C (MvPolynomial.eval v (MvPolynomial.homogeneousComponent j f)) *
        Polynomial.X ^ j with hQ
  have hfun : ∀ t : k, Polynomial.eval t (substLine v f) = Polynomial.eval t Q := by
    intro t
    rw [substLine_eval, hQ, Polynomial.eval_finsetSum]
    have hsplit : MvPolynomial.eval (t • v) f
        = ∑ j ∈ Finset.range (D + 1),
            MvPolynomial.eval (t • v) (MvPolynomial.homogeneousComponent j f) := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := f)]
      rw [map_sum]
    rw [hsplit]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous j f) t v,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hPQ : substLine v f = Q := by
    refine Polynomial.eq_of_infinite_eval_eq (substLine v f) Q ?_
    refine Set.Infinite.mono (s := Set.univ) (fun t _ => hfun t) (Set.infinite_univ)
  rw [hPQ, hQ, coeff_sum_range_C_mul_X]
  by_cases hd : d ≤ D
  · rw [if_pos hd]
  · rw [if_neg hd, MvPolynomial.homogeneousComponent_eq_zero (φ := f) (n := d) (by omega),
      map_zero]

/-- **Line test.**  If a polynomial vanishes at every nonzero multiple of `v`, then each of its
homogeneous components vanishes at `v`. -/
theorem eval_homogeneousComponent_eq_zero_of_eval_line [Infinite k] {v : Vec k n}
    (f : Poly k n) (h : ∀ t : k, t ≠ 0 → MvPolynomial.eval (t • v) f = 0) (d : ℕ) :
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent d f) = 0 := by
  have hinf : Set.Infinite {t : k | Polynomial.IsRoot (substLine v f) t} := by
    have hne : Set.Infinite (Set.univ \ ({0} : Set k)) :=
      Set.infinite_univ.sdiff (Set.finite_singleton 0)
    refine hne.mono ?_
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    show Polynomial.eval t (substLine v f) = 0
    rw [substLine_eval]
    exact h t ht0
  have hroot : substLine v f = 0 := Polynomial.eq_zero_of_infinite_isRoot _ hinf
  rw [← substLine_coeff v f d, hroot]
  simp

end P

end LineSubstitution

/-! ## 12. The coordinate ring of an irreducible projective variety is a domain -/

section Primality

variable {k : Type*} [Field k] [Infinite k] {n : ℕ}

namespace P

/-- Vanishing of a polynomial at a projective point is detected on its homogeneous components. -/
theorem formVanishesAt_iff_forall_homogeneousComponent {f : Poly k n} {x : P k n} :
    FormVanishesAt f x ↔ ∀ d, FormVanishesAt (MvPolynomial.homogeneousComponent d f) x := by
  constructor
  · intro h d v hv hx
    refine eval_homogeneousComponent_eq_zero_of_eval_line f (fun t ht => ?_) d
    exact h (t • v) (smul_ne_zero ht hv)
      ((mk_smul' ht hv (smul_ne_zero ht hv)).trans hx)
  · intro h v hv hx
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := f)]
    rw [map_sum]
    exact Finset.sum_eq_zero fun d _ => h d v hv hx

/-- The set of points at which a polynomial vanishes is closed. -/
theorem isClosed_formVanishesAt (f : Poly k n) :
    IsClosed {x : P k n | FormVanishesAt f x} := by
  have hset : {x : P k n | FormVanishesAt f x}
      = ⋂ d, zeroLocus ({(MvPolynomial.homogeneousComponent d f)} : Set (Poly k n)) := by
    ext x
    simp only [Set.mem_iInter, zeroLocus, Set.mem_singleton_iff, forall_eq]
    exact formVanishesAt_iff_forall_homogeneousComponent
  rw [hset]
  exact isClosed_iInter fun d => isClosed_zeroLocus (by
    rintro g rfl
    exact ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d f⟩)

/-- At a point, a product of two polynomials vanishes only if one factor does. -/
theorem formVanishesAt_mul {f g : Poly k n} {x : P k n}
    (h : FormVanishesAt (f * g) x) : FormVanishesAt f x ∨ FormVanishesAt g x := by
  classical
  obtain ⟨v, hv, rfl⟩ := exists_mk x
  have hline : ∀ t : k, t ≠ 0 → Polynomial.eval t (substLine v f * substLine v g) = 0 := by
    intro t ht
    rw [Polynomial.eval_mul, substLine_eval, substLine_eval, ← MvPolynomial.eval_mul]
    exact h (t • v) (smul_ne_zero ht hv) (mk_smul ht hv)
  have hinf : Set.Infinite {t : k | Polynomial.IsRoot (substLine v f * substLine v g) t} := by
    have hne : Set.Infinite (Set.univ \ ({0} : Set k)) :=
      Set.infinite_univ.sdiff (Set.finite_singleton 0)
    refine hne.mono ?_
    intro t ht
    show Polynomial.eval t (substLine v f * substLine v g) = 0
    exact hline t (by simpa using ht)
  have hzero : substLine v f * substLine v g = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ hinf
  have key : ∀ h : Poly k n, substLine v h = 0 → FormVanishesAt h (mk hv) := by
    intro h hz
    rw [formVanishesAt_iff_forall_homogeneousComponent]
    intro d
    rw [formVanishesAt_mk_iff (MvPolynomial.homogeneousComponent_isHomogeneous d h) hv,
      ← substLine_coeff v h d, hz]
    simp
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact Or.inl (key f hz)
  · exact Or.inr (key g hz)

/-- **The coordinate ring of an irreducible projective variety is a domain**: the ideal of all
polynomials vanishing on an irreducible closed subset of `Pⁿ` is prime. -/
theorem isPrime_vanishOnIdeal {Y : Set (P k n)} (hY : IsIrreducible Y) :
    (vanishOnIdeal Y).IsPrime := by
  classical
  refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hY.nonempty
    obtain ⟨v, hv, rfl⟩ := exists_mk x
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), v i ≠ 0 := by
      simpa using Function.ne_iff.mp hv
    have hmem : MvPolynomial.X i ∈ vanishOnIdeal Y := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := mem_vanishOnIdeal_iff.mp hmem (mk hv) hx v hv rfl
    rw [MvPolynomial.eval_X] at h0
    exact hi h0
  · intro f g hfg
    have hcover : Y ⊆ {x : P k n | FormVanishesAt f x} ∪ {x : P k n | FormVanishesAt g x} := by
      intro x hx
      rcases formVanishesAt_mul (mem_vanishOnIdeal_iff.mp hfg x hx) with h' | h'
      exacts [Or.inl h', Or.inr h']
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hY.isPreirreducible) _ _
      (isClosed_formVanishesAt f) (isClosed_formVanishesAt g) hcover with h' | h'
    · exact Or.inl fun x hx => h' hx
    · exact Or.inr fun x hx => h' hx

end P

end Primality
/-! ## 11. Graded pieces of the homogeneous coordinate ring `B = k[x₀,…,xₙ]/p` -/

section GradedPieces

variable (k : Type*) [Field k] (n : ℕ) (p : Ideal (Poly k n))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-`d` graded piece of `B = k[x₀,…,xₙ]/p`: the image of the homogeneous
polynomials of degree `d`. -/
noncomputable def Bd (d : ℕ) : Submodule k (Poly k n ⧸ p) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d).map (Ideal.Quotient.mkₐ k p).toLinearMap

lemma mk_mem_Bd {d : ℕ} {G : Poly k n} (hG : G.IsHomogeneous d) :
    Ideal.Quotient.mk p G ∈ Bd k n p d :=
  Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ k p).toLinearMap)
    (by simpa using hG)

lemma Bd_fg (d : ℕ) : (Bd k n p d).FG :=
  Submodule.FG.map (f := (Ideal.Quotient.mkₐ k p).toLinearMap)
    (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 1)) k d)

instance Bd_finite (d : ℕ) : FiniteDimensional k ↥(Bd k n p d) :=
  (Submodule.fg_iff_finiteDimensional _).mp (Bd_fg k n p d)

lemma exists_homog_of_mem_Bd {x : Poly k n ⧸ p} {d : ℕ} (hx : x ∈ Bd k n p d) :
    ∃ G : Poly k n, G.IsHomogeneous d ∧ Ideal.Quotient.mk p G = x := by
  obtain ⟨G, hG, hGx⟩ := Submodule.mem_map.mp hx
  exact ⟨G, hG, hGx⟩

end GradedPieces

section PartBAlgebra

variable (k : Type*) [Field k] (n : ℕ) (p : Ideal (Poly k n))

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Hcomp : ∀ ⦃x : Poly k n⦄, x ∈ p → ∀ d, MvPolynomial.homogeneousComponent d x ∈ p)

include Hcomp

/-- Components of an element of the homogeneous ideal `p` lie in `p`. -/
lemma homogComponent_mem {x : Poly k n} (hx : x ∈ p) (d : ℕ) :
    MvPolynomial.homogeneousComponent d x ∈ p :=
  Hcomp hx d

/-- **Graded independence in `B`.**  If the images in `B` of homogeneous polynomials of pairwise
distinct degrees sum to zero, then each of them is already zero. -/
lemma mk_eq_zero_of_sum_eq_zero {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, d i = d j → i = j) (G : ι → Poly k n)
    (hG : ∀ i, (G i).IsHomogeneous (d i)) (h : ∑ i ∈ s, Ideal.Quotient.mk p (G i) = 0) :
    ∀ i ∈ s, Ideal.Quotient.mk p (G i) = 0 := by
  intro i hi
  have hmem : (∑ j ∈ s, G j) ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    exact h
  have hcomp := homogComponent_mem k n p Hcomp hmem (d i)
  rw [map_sum] at hcomp
  have hzero : ∀ j ∈ s, j ≠ i → MvPolynomial.homogeneousComponent (d i) (G j) = 0 := by
    intro j hj hji
    rw [MvPolynomial.homogeneousComponent_of_mem (n := d j) (hG j)]
    rw [if_neg]
    exact fun he => hji (hd j hj i hi he.symm)
  rw [Finset.sum_eq_single i hzero (fun hni => absurd hi hni),
    MvPolynomial.homogeneousComponent_of_mem (n := d i) (hG i), if_pos rfl] at hcomp
  rwa [Ideal.Quotient.eq_zero_iff_mem]

/-- **Divisibility by `f` inside a graded piece.**  If `x` lies in the degree-`d` piece of `B` and
`x = f·y`, then `x = f·y'` for some `y'` in the degree-`d - e` piece. -/
lemma div_step {f : Poly k n} {e : ℕ} (hf : f.IsHomogeneous e)
    {y x : Poly k n ⧸ p} {d : ℕ} (hde : e ≤ d) (hx : x ∈ Bd k n p d)
    (hyx : Ideal.Quotient.mk p f * y = x) :
    ∃ y' ∈ Bd k n p (d - e), Ideal.Quotient.mk p f * y' = x := by
  obtain ⟨G, hG, rfl⟩ := exists_homog_of_mem_Bd k n p hx
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : f * Y - G ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hyx, sub_self]
  refine ⟨Ideal.Quotient.mk p (MvPolynomial.homogeneousComponent (d - e) Y),
    mk_mem_Bd k n p (MvPolynomial.homogeneousComponent_isHomogeneous (d - e) Y), ?_⟩
  have hcomp : MvPolynomial.homogeneousComponent d (f * Y) - G ∈ p := by
    have h := homogComponent_mem k n p Hcomp hmem d
    rwa [map_sub, MvPolynomial.homogeneousComponent_eq_self hG] at h
  have hkey : MvPolynomial.homogeneousComponent d (f * Y)
      = f * MvPolynomial.homogeneousComponent (d - e) Y := by
    by_cases hin : d - e ∈ Finset.range (Y.totalDegree + 1)
    · have hdecomp : Y = ∑ j ∈ Finset.range (Y.totalDegree + 1),
          MvPolynomial.homogeneousComponent j Y :=
        (MvPolynomial.sum_homogeneousComponent (φ := Y)).symm
      conv_lhs => rw [hdecomp, Finset.mul_sum]
      rw [map_sum, Finset.sum_eq_single (d - e)]
      · rw [MvPolynomial.homogeneousComponent_of_mem (n := e + (d - e))
          (hf.mul (MvPolynomial.homogeneousComponent_isHomogeneous _ Y))]
        rw [if_pos (by omega)]
      · intro j _ hne
        rw [MvPolynomial.homogeneousComponent_of_mem (n := e + j)
          (hf.mul (MvPolynomial.homogeneousComponent_isHomogeneous _ Y))]
        rw [if_neg (by omega)]
      · intro hnot
        exact absurd hin hnot
    · have hlt : Y.totalDegree < d - e := by
        have h2 : ¬ (d - e < Y.totalDegree + 1) := fun h => hin (Finset.mem_range.mpr h)
        omega
      have hzero1 : MvPolynomial.homogeneousComponent (d - e) Y = 0 :=
        MvPolynomial.homogeneousComponent_eq_zero (n := d - e) (φ := Y) hlt
      have hzero2 : MvPolynomial.homogeneousComponent d (f * Y) = 0 := by
        refine MvPolynomial.homogeneousComponent_eq_zero (n := d) (φ := f * Y) ?_
        have h1 : (f * Y).totalDegree ≤ f.totalDegree + Y.totalDegree :=
          MvPolynomial.totalDegree_mul f Y
        have h2 : f.totalDegree ≤ e := hf.totalDegree_le
        omega
      rw [hzero1, hzero2, mul_zero]
  rw [← map_mul, ← hkey, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hcomp

/-- **Iterated division.**  Inside the graded pieces of `B`, an element of degree `D ≥ K` can be
divided by a power `f^j` of `f`, as long as the degree stays at least `K`. -/
lemma exists_div_pow {f : Poly k n} {e K : ℕ} (hf : f.IsHomogeneous e)
    (hdiv : ∀ {D : ℕ}, K ≤ D → ∀ x ∈ Bd k n p D, x ∈ Ideal.span {Ideal.Quotient.mk p f}) :
    ∀ (j D : ℕ), K ≤ D → j * e ≤ D - K → ∀ x ∈ Bd k n p D,
      ∃ u ∈ Bd k n p (D - j * e), (Ideal.Quotient.mk p f) ^ j * u = x := by
  intro j
  induction j with
  | zero =>
    intro D hD _ x hx
    exact ⟨x, by simpa using hx, by simp⟩
  | succ j ih =>
    intro D hD hj x hx
    have hje : (j + 1) * e = j * e + e := Nat.succ_mul j e
    have heD : e ≤ D := by omega
    have hxspan : x ∈ Ideal.span {Ideal.Quotient.mk p f} := hdiv hD x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxspan
    have hxey : Ideal.Quotient.mk p f * y = x := by rw [hy, mul_comm]
    obtain ⟨u₁, hu₁, hfu₁⟩ := div_step k n p Hcomp hf heD hx hxey
    have hKD' : K ≤ D - e := by omega
    have hj' : j * e ≤ (D - e) - K := by omega
    obtain ⟨u, hu, hju⟩ := ih (D - e) hKD' hj' u₁ hu₁
    refine ⟨u, ?_, ?_⟩
    · have hdeg : D - (j + 1) * e = D - e - j * e := by omega
      rwa [hdeg]
    · have hmul : (Ideal.Quotient.mk p f) ^ (j + 1) * u
          = Ideal.Quotient.mk p f * ((Ideal.Quotient.mk p f) ^ j * u) := by ring
      rw [hmul, hju, hfu₁]

end PartBAlgebra

/-! ## 12. Part (b): a projective variety of dimension `≥ 1` meets every hypersurface -/

section PartBAux

variable (k : Type*) [Field k] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Vanishing of all elements of a homogeneous ideal at a representative gives membership in the
projective zero locus. -/
theorem mem_zeroLocus_of_forall_eval_eq_zero (q : Ideal (Poly k n))
    (hqh : ∀ ⦃x : Poly k n⦄, x ∈ q → ∀ d, MvPolynomial.homogeneousComponent d x ∈ q)
    {u : Vec k n} (hu : u ≠ 0) (h : ∀ g ∈ q, MvPolynomial.eval u g = 0) :
    P.mk hu ∈ P.zeroLocus (q : Set (Poly k n)) := by
  intro g hg v hv hvu
  have heq : P.mk hv = P.mk hu := hvu
  obtain ⟨c, hc, hcv⟩ := (P.mk_eq_mk_iff hv hu).mp heq
  subst hcv
  have hsum : g = ∑ j ∈ Finset.range (g.totalDegree + 1),
      MvPolynomial.homogeneousComponent j g :=
    (MvPolynomial.sum_homogeneousComponent (φ := g)).symm
  conv_lhs => rw [hsum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [P.eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous j g) c u,
    h _ (hqh hg j), mul_zero]

/-- An element of the degree-`D` piece lies in the ideal generated by `f` as soon as the degree is
at least the Nullstellensatz exponent. -/
theorem Bd_le_span_mk {p : Ideal (Poly k n)}
    {f : Poly k n} {c : Fin (n + 1) → ℕ}
    (hc : ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ p ⊔ Ideal.span {f})
    {D : ℕ} (hD : ∑ i, c i ≤ D) :
    ∀ x ∈ Bd k n p D, x ∈ Ideal.span {Ideal.Quotient.mk p f} := by
  intro x hx
  obtain ⟨G, hG, rfl⟩ := exists_homog_of_mem_Bd k n p hx
  have hGmem : G ∈ p ⊔ Ideal.span {f} :=
    mem_of_isHomogeneous_of_forall_X_pow_mem k n (p ⊔ Ideal.span {f}) c hc G D hG hD
  have hmap : (p ⊔ Ideal.span {f}).map (Ideal.Quotient.mk p) = Ideal.span {Ideal.Quotient.mk p f} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_quotient_self, bot_sup_eq]
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) hGmem
  rwa [hmap] at hm

end PartBAux

section AlgClosedElem

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, an algebraic element of a field extension lies in the
base field. -/
theorem algebraic_imp_mem {F : Type*} [Field F] [Algebra k F] {x : F}
    (h : ∃ P : Polynomial k, P ≠ 0 ∧ Polynomial.eval₂ (algebraMap k F) x P = 0) :
    ∃ c : k, algebraMap k F c = x := by
  classical
  obtain ⟨P, hP0, hPx⟩ := h
  have hex : ∃ m, ∃ Q : Polynomial k, Q.natDegree = m ∧ Q ≠ 0 ∧
      Polynomial.eval₂ (algebraMap k F) x Q = 0 := ⟨P.natDegree, P, rfl, hP0, hPx⟩
  obtain ⟨Q, hQn, hQ0, hQx⟩ := Nat.find_spec hex
  have hmin : ∀ R : Polynomial k, R ≠ 0 → Polynomial.eval₂ (algebraMap k F) x R = 0 →
      Nat.find hex ≤ R.natDegree := fun R hR0 hRx => Nat.find_min' hex ⟨R, rfl, hR0, hRx⟩
  have hdeg : 0 < Q.natDegree := by
    rcases Nat.eq_zero_or_pos Q.natDegree with h0 | h1
    · exfalso
      have hc : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [hc] at hQx hQ0
      simp only [Polynomial.eval₂_C] at hQx
      have hinj : Function.Injective (algebraMap k F) := RingHom.injective (algebraMap k F)
      exact hQ0 (Polynomial.C_eq_zero.mpr (hinj (by simpa using hQx)))
    · exact h1
  obtain ⟨a, ha⟩ : ∃ a : k, Q.IsRoot a := by
    apply IsAlgClosed.exists_root
    rw [Polynomial.degree_eq_natDegree hQ0]
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hdeg)
  obtain ⟨Q₁, hQ₁⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  have hQ₁0 : Q₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQ₁
    exact hQ0 hQ₁
  have hQ₁deg : Q₁.natDegree < Q.natDegree := by
    rw [hQ₁]
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hQ₁0,
      Polynomial.natDegree_X_sub_C]
    omega
  have h2 : Polynomial.eval₂ (algebraMap k F) x Q
      = (x - algebraMap k F a) * Polynomial.eval₂ (algebraMap k F) x Q₁ := by
    rw [hQ₁]
    simp
  by_cases hxa : x - algebraMap k F a = 0
  · exact ⟨a, (sub_eq_zero.mp hxa).symm⟩
  · have hQ₁x : Polynomial.eval₂ (algebraMap k F) x Q₁ = 0 := by
      rw [h2] at hQx
      exact (mul_eq_zero.mp hQx).resolve_left hxa
    have := hmin Q₁ hQ₁0 hQ₁x
    omega

end AlgClosedElem
/-! ## 13. Part (b), main theorem -/

section PartBMain

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If two vectors are not proportional, some `2 × 2` minor is nonzero. -/
theorem exists_minor_ne_zero {v w : Vec k n} (hv : v ≠ 0)
    (h : ¬ ∃ c : k, w = c • v) : ∃ i j : Fin (n + 1), v i * w j ≠ v j * w i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  apply h
  refine ⟨w i / v i, ?_⟩
  funext j
  have h1 : v j * w i = v i * w j := hcon j i
  show w j = w i / v i * v j
  rw [div_mul_eq_mul_div, eq_div_iff hi, mul_comm (w j) (v i), mul_comm (w i) (v j)]
  exact h1.symm

/-! ## 14. The ratio `x^e / f` is a scalar: the Hilbert-polynomial style counting argument -/

section PartBCore

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Powers of a degree-one element of `B` lie in the matching graded piece. -/
theorem pow_mem_Bd_one {J : Ideal (Poly k n)} {x : Poly k n ⧸ J} (hx : x ∈ Bd k n J 1)
    (m : ℕ) : x ^ m ∈ Bd k n J m := by
  obtain ⟨G, hG, rfl⟩ := exists_homog_of_mem_Bd k n J hx
  rw [← map_pow]
  exact mk_mem_Bd k n J (by simpa using hG.pow m)

/-- If `B = S/J` is a domain and every element of degree `≥ K` is divisible by `f`, then for any
nonzero degree-one element `x` the ratio `x^e / f` is algebraic over `k`, hence (for `k`
algebraically closed) a scalar: `x^e = lam * f`. -/
theorem exists_smul_of_mem_Bd_one {J : Ideal (Poly k n)} (hJp : J.IsPrime)
    (Hcomp : ∀ ⦃y : Poly k n⦄, y ∈ J → ∀ d, MvPolynomial.homogeneousComponent d y ∈ J)
    {f : Poly k n} {e K : ℕ} (he : 0 < e) (hfh : f.IsHomogeneous e) (hf0 : f ∉ J)
    (hdiv : ∀ {D : ℕ}, K ≤ D → ∀ y ∈ Bd k n J D, y ∈ Ideal.span {Ideal.Quotient.mk J f})
    {x : Poly k n ⧸ J} (hx : x ∈ Bd k n J 1) (hx0 : x ≠ 0) :
    ∃ lam : k, x ^ e = lam • Ideal.Quotient.mk J f := by
  classical
  haveI hdom : IsDomain (Poly k n ⧸ J) := Ideal.Quotient.isDomain J
  have key : ∀ j : ℕ, ∃ u ∈ Bd k n J K, (Ideal.Quotient.mk J f) ^ j * u = x ^ (K + j * e) := by
    intro j
    obtain ⟨u, hu, huz⟩ :=
      exists_div_pow k n J Hcomp (f := f) (e := e) (K := K) hfh hdiv j (K + j * e)
        (Nat.le_add_right _ _) (by omega) (x ^ (K + j * e)) (pow_mem_Bd_one hx _)
    exact ⟨u, by rwa [Nat.add_sub_cancel] at hu, huz⟩
  choose u hu hfu using key
  set N := Module.finrank k ↥(Bd k n J K)
  have hdepend : ¬ LinearIndependent k
      (fun j : Fin (N + 1) => (⟨u (j : ℕ), hu (j : ℕ)⟩ : ↥(Bd k n J K))) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at h1
    omega
  rw [Fintype.linearIndependent_iff] at hdepend
  push Not at hdepend
  obtain ⟨cc, hcc, j0, hcc0⟩ := hdepend
  have hccamb : ∑ j : Fin (N + 1), cc j • u (j : ℕ) = 0 := by
    have h1 := congrArg (fun y : ↥(Bd k n J K) => (y : Poly k n ⧸ J)) hcc
    simpa using h1
  -- the relation Σ cc_j f^(N-j) x^(K+je) = 0 in `B`
  have hrelB : ∑ j : Fin (N + 1),
      cc j • ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e)) = 0 := by
    have h1 : (Ideal.Quotient.mk J f) ^ N *
        (∑ j : Fin (N + 1), cc j • u (j : ℕ)) = 0 := by
      rw [hccamb, mul_zero]
    rw [Finset.mul_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    have hpow : (Ideal.Quotient.mk J f) ^ N
        = (Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * (Ideal.Quotient.mk J f) ^ (j : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    calc cc j • ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e))
        = cc j • ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) *
            ((Ideal.Quotient.mk J f) ^ (j : ℕ) * u (j : ℕ))) := by rw [hfu (j : ℕ)]
      _ = cc j • ((Ideal.Quotient.mk J f) ^ N * u (j : ℕ)) := by rw [hpow, mul_assoc]
      _ = (Ideal.Quotient.mk J f) ^ N * (cc j • u (j : ℕ)) := (mul_smul_comm _ _ _).symm
  -- pass to the fraction field
  set F := FractionRing (Poly k n ⧸ J) with hFdef
  set Ff : F := algebraMap (Poly k n ⧸ J) F (Ideal.Quotient.mk J f) with hFfdef
  set Xf : F := algebraMap (Poly k n ⧸ J) F x with hXfdef
  have hinj : Function.Injective (algebraMap (Poly k n ⧸ J) F) := IsFractionRing.injective _ _
  have hFf : Ff ≠ 0 := by
    rw [hFfdef]
    intro h
    refine hf0 ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hinj (by rw [h, map_zero])
  have hXf : Xf ≠ 0 := by
    rw [hXfdef]
    intro h
    exact hx0 (hinj (by rw [h, map_zero]))
  have hrelB' : ∑ j : Fin (N + 1),
      algebraMap k (Poly k n ⧸ J) (cc j) *
        ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e)) = 0 := by
    have hsum_eq : ∑ j : Fin (N + 1),
        algebraMap k (Poly k n ⧸ J) (cc j) *
          ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e))
        = ∑ j : Fin (N + 1),
            cc j • ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (Algebra.smul_def (cc j)
        ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e))).symm
    rw [hsum_eq, hrelB]
  have hmap : ∑ j : Fin (N + 1),
      algebraMap k F (cc j) * (Xf ^ (K + (j : ℕ) * e) * Ff ^ (N - (j : ℕ))) = 0 := by
    have h1 : algebraMap (Poly k n ⧸ J) F
        (∑ j : Fin (N + 1),
          algebraMap k (Poly k n ⧸ J) (cc j) *
            ((Ideal.Quotient.mk J f) ^ (N - (j : ℕ)) * x ^ (K + (j : ℕ) * e))) = 0 := by
      rw [hrelB', map_zero]
    rw [map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, ← hFfdef, ← hXfdef]
    rw [IsScalarTower.algebraMap_apply k (Poly k n ⧸ J) F]
    ring
  -- the termwise identity eliminating `f`
  have hterm : ∀ j : Fin (N + 1),
      Xf ^ K * (Ff ^ N * (algebraMap k F (cc j) * (Xf ^ e / Ff) ^ (j : ℕ)))
        = algebraMap k F (cc j) * (Xf ^ (K + (j : ℕ) * e) * Ff ^ (N - (j : ℕ))) := by
    intro j
    have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    have hXe : Xf ^ (K + (j : ℕ) * e) = Xf ^ K * (Xf ^ e) ^ (j : ℕ) := by
      rw [mul_comm ((j : ℕ)) e, pow_add, pow_mul]
    have hkey : Ff ^ N * (Xf ^ e / Ff) ^ (j : ℕ)
        = (Xf ^ e) ^ (j : ℕ) * Ff ^ (N - (j : ℕ)) := by
      have h1 : (Xf ^ e / Ff) ^ (j : ℕ) = (Xf ^ e) ^ (j : ℕ) * (Ff ^ (j : ℕ))⁻¹ := by
        rw [div_pow, div_eq_mul_inv]
      rw [h1, pow_sub₀ Ff hFf hj]
      ring
    calc Xf ^ K * (Ff ^ N * (algebraMap k F (cc j) * (Xf ^ e / Ff) ^ (j : ℕ)))
        = Xf ^ K * (algebraMap k F (cc j) * (Ff ^ N * (Xf ^ e / Ff) ^ (j : ℕ))) := by ring
      _ = Xf ^ K * (algebraMap k F (cc j) *
            ((Xf ^ e) ^ (j : ℕ) * Ff ^ (N - (j : ℕ)))) := by rw [hkey]
      _ = algebraMap k F (cc j) * (Xf ^ (K + (j : ℕ) * e) * Ff ^ (N - (j : ℕ))) := by
            rw [hXe]; ring
  have hzero : ∑ j : Fin (N + 1), algebraMap k F (cc j) * (Xf ^ e / Ff) ^ (j : ℕ) = 0 := by
    have h2 : Xf ^ K * (Ff ^ N *
        (∑ j : Fin (N + 1), algebraMap k F (cc j) * (Xf ^ e / Ff) ^ (j : ℕ))) = 0 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j]
      exact hmap
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (pow_ne_zero K hXf)
    · exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero N hFf)
  -- `x^e / f` is algebraic over `k`, hence a scalar
  have halg : ∃ P : Polynomial k, P ≠ 0 ∧
      Polynomial.eval₂ (algebraMap k F) (Xf ^ e / Ff) P = 0 := by
    refine ⟨∑ j : Fin (N + 1), Polynomial.C (cc j) * Polynomial.X ^ (j : ℕ), ?_, ?_⟩
    · intro hP
      refine hcc0 ?_
      have hdist : (∑ j : Fin (N + 1), Polynomial.C (cc j) * Polynomial.X ^ (j : ℕ)).coeff (j0 : ℕ)
          = ∑ j : Fin (N + 1),
              (Polynomial.C (cc j) * Polynomial.X ^ (j : ℕ)).coeff (j0 : ℕ) := by simp
      have hcoeff : (∑ j : Fin (N + 1),
            (Polynomial.C (cc j) * Polynomial.X ^ (j : ℕ)).coeff (j0 : ℕ)) = cc j0 := by
        rw [Finset.sum_eq_single j0]
        · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
        · intro b _ hb
          rw [Polynomial.coeff_C_mul_X_pow, if_neg]
          intro hbj
          exact hb (Fin.ext hbj).symm
        · intro hnot
          exact absurd (Finset.mem_univ j0) hnot
      have hcoe : (∑ j : Fin (N + 1), Polynomial.C (cc j) * Polynomial.X ^ (j : ℕ)).coeff (j0 : ℕ)
          = cc j0 := by rw [hdist, hcoeff]
      rw [hP, Polynomial.coeff_zero] at hcoe
      exact hcoe.symm
    · rw [Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact hzero
  obtain ⟨lam, hlam⟩ := algebraic_imp_mem halg
  refine ⟨lam, ?_⟩
  apply hinj
  have key : algebraMap (Poly k n ⧸ J) F (lam • Ideal.Quotient.mk J f)
      = algebraMap k F lam * Ff := by
    rw [show lam • Ideal.Quotient.mk J f
        = algebraMap k (Poly k n ⧸ J) lam * Ideal.Quotient.mk J f from
          Algebra.smul_def lam (Ideal.Quotient.mk J f),
      map_mul,
      show algebraMap (Poly k n ⧸ J) F (algebraMap k (Poly k n ⧸ J) lam) = algebraMap k F lam
        from by rw [IsScalarTower.algebraMap_apply k (Poly k n ⧸ J) F],
      hFfdef]
  rw [key, map_pow, ← hXfdef, hlam]
  exact (div_mul_cancel₀ (Xf ^ e) hFf).symm

end PartBCore

/-! ## 15. Part (b): a projective variety of dimension `≥ 1` meets every hypersurface -/

section PartBEngine

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A topological space of dimension `≥ 1` has at least two points. -/
theorem two_points_of_one_le_topologicalKrullDim {X : Type*} [TopologicalSpace X]
    (h : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X) : ∃ x y : X, x ≠ y := by
  have h1 : (1 : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds X) := h
  rw [Order.one_le_krullDim_iff] at h1
  obtain ⟨Z, W, hZW⟩ := h1
  have hsub : (Z : Set X) ⊆ (W : Set X) := hZW.le
  have hne : (Z : Set X) ≠ (W : Set X) :=
    fun h' => hZW.ne (TopologicalSpace.IrreducibleCloseds.ext h')
  obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
  have hex : ∃ y ∈ (W : Set X), y ∉ (Z : Set X) := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hsub hcon)
  obtain ⟨y, hyW, hyZ⟩ := hex
  exact ⟨x, y, fun hxy => hyZ (hxy ▸ hx)⟩

/-- **Hartshorne, Algebraic Geometry, Exercise I.3.7(b): the algebraic core.**  Let `B = S/J` with
`J` a prime homogeneous ideal, `f` a form of positive degree which is a nonzerodivisor modulo `J`
and such that every element of large degree is divisible by `f`.  Then `Z(J)` cannot contain two
distinct points. -/
theorem part_b_core (J : Ideal (Poly k n)) (hJp : J.IsPrime)
    (Hcomp : ∀ ⦃y : Poly k n⦄, y ∈ J → ∀ d, MvPolynomial.homogeneousComponent d y ∈ J)
    (f : Poly k n) (e : ℕ) (he : 0 < e) (hfh : f.IsHomogeneous e) (hfJ : f ∉ J)
    (c : Fin (n + 1) → ℕ)
    (hc : ∀ i, (MvPolynomial.X i : Poly k n) ^ (c i) ∈ J ⊔ Ideal.span {f})
    (v w : Vec k n) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ¬ ∃ t : k, w = t • v)
    (hJv : ∀ g ∈ J, MvPolynomial.eval v g = 0)
    (hJw : ∀ g ∈ J, MvPolynomial.eval w g = 0) : False := by
  classical
  haveI hdom : IsDomain (Poly k n ⧸ J) := Ideal.Quotient.isDomain J
  obtain ⟨i, j, hij⟩ := exists_minor_ne_zero k n hv hvw
  -- two independent linear forms adapted to the two points
  set Z : Poly k n :=
    MvPolynomial.C (w j) * MvPolynomial.X i - MvPolynomial.C (w i) * MvPolynomial.X j with hZ
  set W : Poly k n :=
    MvPolynomial.C (v j) * MvPolynomial.X i - MvPolynomial.C (v i) * MvPolynomial.X j with hW
  have hZhom : Z.IsHomogeneous 1 := by
    rw [hZ]
    exact (MvPolynomial.isHomogeneous_C_mul_X (w j) i).sub
      (MvPolynomial.isHomogeneous_C_mul_X (w i) j)
  have hWhom : W.IsHomogeneous 1 := by
    rw [hW]
    exact (MvPolynomial.isHomogeneous_C_mul_X (v j) i).sub
      (MvPolynomial.isHomogeneous_C_mul_X (v i) j)
  have hZev : MvPolynomial.eval v Z = w j * v i - w i * v j := by simp [hZ]
  have hZew : MvPolynomial.eval w Z = 0 := by simp [hZ]; ring
  have hWev : MvPolynomial.eval v W = 0 := by simp [hW]; ring
  have hWew : MvPolynomial.eval w W = v j * w i - v i * w j := by simp [hW]
  have hZne : MvPolynomial.eval v Z ≠ 0 := by
    rw [hZev]
    intro h0
    apply hij
    have h1 : w j * v i = w i * v j := sub_eq_zero.mp h0
    calc v i * w j = w j * v i := by ring
      _ = w i * v j := h1
      _ = v j * w i := by ring
  have hWne : MvPolynomial.eval w W ≠ 0 := by
    rw [hWew]
    intro h0
    apply hij
    have h1 : v j * w i = v i * w j := sub_eq_zero.mp h0
    calc v i * w j = v j * w i := h1.symm
      _ = w i * v j := by ring
      _ = v j * w i := by ring
  have hZne0 : w j * v i - w i * v j ≠ 0 := fun h => hZne (by rw [hZev]; exact h)
  have hWne0 : v j * w i - v i * w j ≠ 0 := fun h => hWne (by rw [hWew]; exact h)
  set z : Poly k n ⧸ J := Ideal.Quotient.mk J Z with hzdef
  set wq : Poly k n ⧸ J := Ideal.Quotient.mk J W with hwdef
  have hzBd : z ∈ Bd k n J 1 := mk_mem_Bd k n J hZhom
  have hwBd : wq ∈ Bd k n J 1 := mk_mem_Bd k n J hWhom
  have hzmem : Z ∉ J := fun h => hZne (hJv Z h)
  have hwmem : W ∉ J := fun h => hWne (hJw W h)
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    intro h
    exact hzmem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hw0 : wq ≠ 0 := by
    rw [hwdef]
    intro h
    exact hwmem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hindep : ∀ a b : k, a • z + b • wq = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hmem : MvPolynomial.C a * Z + MvPolynomial.C b * W ∈ J := by
      have h1 : Ideal.Quotient.mk J (MvPolynomial.C a * Z + MvPolynomial.C b * W) = 0 := by
        rw [show Ideal.Quotient.mk J (MvPolynomial.C a * Z + MvPolynomial.C b * W)
            = a • z + b • wq from ?_, hab]
        rw [map_add, map_mul, map_mul, ← hzdef, ← hwdef]
        rw [show Ideal.Quotient.mk J (MvPolynomial.C a) = algebraMap k (Poly k n ⧸ J) a from rfl,
          show Ideal.Quotient.mk J (MvPolynomial.C b) = algebraMap k (Poly k n ⧸ J) b from rfl,
          ← Algebra.smul_def, ← Algebra.smul_def]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hv1 : a * (w j * v i - w i * v j) = 0 := by
      have h2 := hJv _ hmem
      simpa [map_add, map_mul, hZev, hWev] using h2
    have hw1 : b * (v j * w i - v i * w j) = 0 := by
      have h2 := hJw _ hmem
      simpa [map_add, map_mul, hZew, hWew] using h2
    exact ⟨(mul_eq_zero.mp hv1).resolve_right hZne0, (mul_eq_zero.mp hw1).resolve_right hWne0⟩
  -- every element of degree `≥ ∑ c i` is divisible by `f`
  have hdiv : ∀ {D : ℕ}, (∑ i, c i) ≤ D →
      ∀ y ∈ Bd k n J D, y ∈ Ideal.span {Ideal.Quotient.mk J f} :=
    fun {D} hD => Bd_le_span_mk (k := k) (n := n) (p := J) (f := f) (c := c) hc hD
  obtain ⟨lam, hlam⟩ :=
    exists_smul_of_mem_Bd_one (k := k) (n := n) hJp Hcomp (f := f) (e := e)
      (K := ∑ i, c i) he hfh hfJ hdiv hzBd hz0
  obtain ⟨mu, hmu⟩ :=
    exists_smul_of_mem_Bd_one (k := k) (n := n) hJp Hcomp (f := f) (e := e)
      (K := ∑ i, c i) he hfh hfJ hdiv hwBd hw0
  -- both ratios are scalars; comparing them contradicts linear independence
  set F := FractionRing (Poly k n ⧸ J)
  have hinj : Function.Injective (algebraMap (Poly k n ⧸ J) F) := IsFractionRing.injective _ _
  set Ff : F := algebraMap (Poly k n ⧸ J) F (Ideal.Quotient.mk J f) with hFfdef
  set Zf : F := algebraMap (Poly k n ⧸ J) F z with hZfdef
  set Wf : F := algebraMap (Poly k n ⧸ J) F wq with hWfdef
  have hmap_smul : ∀ (cc : k) (y : Poly k n ⧸ J),
      algebraMap (Poly k n ⧸ J) F (cc • y)
        = algebraMap k F cc * algebraMap (Poly k n ⧸ J) F y := by
    intro cc y
    rw [show cc • y = algebraMap k (Poly k n ⧸ J) cc * y from Algebra.smul_def cc y, map_mul,
      show algebraMap (Poly k n ⧸ J) F (algebraMap k (Poly k n ⧸ J) cc) = algebraMap k F cc from by
        rw [IsScalarTower.algebraMap_apply k (Poly k n ⧸ J) F]]
  have hFf : Ff ≠ 0 := by
    rw [hFfdef]
    intro h
    refine hfJ ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hinj (by rw [h, map_zero])
  have hWf : Wf ≠ 0 := by
    rw [hWfdef]
    intro h
    exact hw0 (hinj (by rw [h, map_zero]))
  have hZpow : Zf ^ e = algebraMap k F lam * Ff := by
    rw [hZfdef, ← map_pow, hlam, hmap_smul, hFfdef]
  have hWpow : Wf ^ e = algebraMap k F mu * Ff := by
    rw [hWfdef, ← map_pow, hmu, hmap_smul, hFfdef]
  have hratio : (Zf / Wf) ^ e = algebraMap k F (lam / mu) := by
    rw [div_pow, hZpow, hWpow, map_div₀, mul_div_mul_right _ _ hFf]
  have halg : ∃ P : Polynomial k, P ≠ 0 ∧
      Polynomial.eval₂ (algebraMap k F) (Zf / Wf) P = 0 := by
    refine ⟨Polynomial.X ^ e - Polynomial.C (lam / mu),
      Polynomial.X_pow_sub_C_ne_zero he _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, hratio,
      sub_self]
  obtain ⟨nu, hnu⟩ := algebraic_imp_mem halg
  have hz_eq : z = nu • wq := by
    apply hinj
    rw [show algebraMap (Poly k n ⧸ J) F z = Zf from hZfdef.symm, hmap_smul nu wq,
      show algebraMap (Poly k n ⧸ J) F wq = Wf from hWfdef.symm, hnu, div_mul_cancel₀ _ hWf]
  have hzero : (1 : k) • z + (-nu) • wq = 0 := by
    rw [one_smul, hz_eq, neg_smul, add_neg_cancel]
  exact one_ne_zero (hindep 1 (-nu) hzero).1

end PartBEngine

end PartBMain

/-! ## 16. Part (b) and (a): the statements of Hartshorne's exercise -/

section PartBY

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

/-- **Hartshorne, Algebraic Geometry, Exercise I.3.7(b).**  A projective variety `Y ⊆ Pⁿ` of
dimension `≥ 1` meets every hypersurface `V(f)` (here `f` is any nonzero form of positive
degree, which covers the irreducible forms defining hypersurfaces). -/
theorem hartshorne_I_3_7_b (Y : Set (P k n)) (hYcl : IsClosed Y) (hYirr : IsIrreducible Y)
    (hdim : (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥Y)
    (f : Poly k n) (e : ℕ) (he : 0 < e) (hfh : f.IsHomogeneous e) :
    (Y ∩ P.zeroLocus ({f} : Set (Poly k n))).Nonempty := by
  classical
  obtain ⟨x, y, hxy⟩ := two_points_of_one_le_topologicalKrullDim hdim
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- the vanishing ideal of `Y` is prime, and graded
  have hJp : (P.vanishOnIdeal Y).IsPrime := P.isPrime_vanishOnIdeal hYirr
  have Hcomp : ∀ ⦃g : Poly k n⦄, g ∈ P.vanishOnIdeal Y → ∀ d,
      MvPolynomial.homogeneousComponent d g ∈ P.vanishOnIdeal Y := by
    intro g hg d
    rw [P.mem_vanishOnIdeal_iff] at hg ⊢
    exact fun p hp => (P.formVanishesAt_iff_forall_homogeneousComponent.mp (hg p hp)) d
  have hfJ : f ∉ P.vanishOnIdeal Y := by
    rw [P.mem_vanishOnIdeal_iff]
    intro hall
    obtain ⟨v, hv, hvx⟩ := P.exists_mk (x : P k n)
    have h2 : MvPolynomial.eval v f = 0 := P.formVanishesAt_mk hv (by rw [hvx]; exact hall x x.2)
    have hmem2 : (x : P k n) ∈ P.zeroLocus ({f} : Set (Poly k n)) := by
      rw [← hvx, P.mem_zeroLocus_iff (by rintro g rfl; exact ⟨e, hfh⟩) hv]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact h2
    have hmem : (x : P k n) ∈ Y ∩ P.zeroLocus ({f} : Set _) := ⟨x.2, hmem2⟩
    rw [hempty] at hmem
    exact Set.notMem_empty _ hmem
  -- Nullstellensatz: `m₀ ⊆ √(I(Y) + (f))`
  have hZaff : MvPolynomial.zeroLocus k (P.vanishOnIdeal Y ⊔ Ideal.span {f})
      ⊆ {(0 : Vec k n)} := by
    intro u hu
    by_contra hu0
    have hu0' : u ≠ 0 := by simpa using hu0
    have huJ : ∀ g ∈ P.vanishOnIdeal Y, MvPolynomial.eval u g = 0 :=
      fun g hg => hu g (Ideal.mem_sup_left hg)
    have huf : MvPolynomial.eval u f = 0 :=
      hu f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    obtain ⟨T, hT, hYT⟩ := P.isClosed_iff_exists_zeroLocus.mp hYcl
    have hmem : (P.mk hu0' : P k n) ∈ Y := by
      rw [hYT]
      intro g hg
      obtain ⟨dg, hdg⟩ := hT g hg
      rw [P.formVanishesAt_mk_iff hdg hu0']
      refine huJ g ?_
      rw [P.mem_vanishOnIdeal_iff]
      intro p hp
      rw [hYT] at hp
      exact hp g hg
    have hfz : (P.mk hu0' : P k n) ∈ P.zeroLocus ({f} : Set (Poly k n)) := by
      rw [P.mem_zeroLocus_iff (by rintro g rfl; exact ⟨e, hfh⟩) hu0']
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact huf
    have hmem' : (P.mk hu0' : P k n) ∈ Y ∩ P.zeroLocus ({f} : Set _) := ⟨hmem, hfz⟩
    rw [hempty] at hmem'
    exact Set.notMem_empty _ hmem'
  have hm0rad : m0 k n ≤ (P.vanishOnIdeal Y ⊔ Ideal.span {f}).radical :=
    m0_le_radical_of_zeroLocus_subset k n _ hZaff
  obtain ⟨c, hc⟩ := exists_X_pow_mem k n _ hm0rad
  -- representatives of the two points
  obtain ⟨v, hv, hvx⟩ := P.exists_mk (x : P k n)
  obtain ⟨w, hw, hwx⟩ := P.exists_mk (y : P k n)
  have hxy' : P.mk hv ≠ P.mk hw := by
    intro h
    apply hxy
    apply Subtype.ext
    rw [← hvx, ← hwx]
    exact h
  have hvw : ¬ ∃ t : k, w = t • v := by
    rintro ⟨t, ht⟩
    have htne : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hw ht
    exact hxy' ((P.mk_eq_mk_iff' hv hw).mpr ⟨t, htne, ht.symm⟩)
  have hJv : ∀ g ∈ P.vanishOnIdeal Y, MvPolynomial.eval v g = 0 := by
    intro g hg
    exact P.formVanishesAt_mk hv (by rw [hvx]; exact P.mem_vanishOnIdeal_iff.mp hg (x : P k n) x.2)
  have hJw : ∀ g ∈ P.vanishOnIdeal Y, MvPolynomial.eval w g = 0 := by
    intro g hg
    exact P.formVanishesAt_mk hw (by rw [hwx]; exact P.mem_vanishOnIdeal_iff.mp hg (y : P k n) y.2)
  exact part_b_core (k := k) (n := n) (P.vanishOnIdeal Y) hJp Hcomp f e he hfh hfJ c hc
    v w hv hw hvw hJv hJw

/-- **Hartshorne I.3.7(b)** with the hypersurface `H = V(f)` given by an irreducible form. -/
theorem hartshorne_I_3_7_b_hypersurface (Y : Set (P k n)) (hYcl : IsClosed Y)
    (hYirr : IsIrreducible Y) (hdim : (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥Y)
    (f : Poly k n) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    (Y ∩ P.zeroLocus ({f} : Set (Poly k n))).Nonempty :=
  hartshorne_I_3_7_b Y hYcl hYirr hdim f d hd hf

end PartBY

section PartACurves

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- **Hartshorne, Algebraic Geometry, Exercise I.3.7(a)**: any two curves in `P²` meet.  A curve in
`P²` is the zero locus of an irreducible form of positive degree (Hartshorne, Ex. I.2.8). -/
theorem hartshorne_I_3_7_a_curves (f g : Poly k 2) (d₁ d₂ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hf : f.IsHomogeneous d₁) (hg : g.IsHomogeneous d₂) (hfirr : Irreducible f)
    (hgirr : Irreducible g) :
    (P.zeroLocus ({f} : Set (Poly k 2)) ∩ P.zeroLocus {g}).Nonempty :=
  hartshorne_I_3_7_a k f g hfirr.ne_zero hgirr.ne_zero ⟨d₁, h₁, hf⟩ ⟨d₂, h₂, hg⟩

end PartACurves

/-! ## 17. Axiom audit -/

#print axioms Hartshorne77.Ex_I_3_7.hartshorne_I_3_7_a
#print axioms Hartshorne77.Ex_I_3_7.hartshorne_I_3_7_a_curves
#print axioms Hartshorne77.Ex_I_3_7.hartshorne_I_3_7_b
#print axioms Hartshorne77.Ex_I_3_7.hartshorne_I_3_7_b_hypersurface
#print axioms Hartshorne77.Ex_I_3_7.part_b_core
#print axioms Hartshorne77.Ex_I_3_7.exists_smul_of_mem_Bd_one
#print axioms Hartshorne77.Ex_I_3_7.pow_mem_Bd_one
#print axioms Hartshorne77.Ex_I_3_7.Bd_le_span_mk
#print axioms Hartshorne77.Ex_I_3_7.mk_eq_zero_of_sum_eq_zero
#print axioms Hartshorne77.Ex_I_3_7.div_step
#print axioms Hartshorne77.Ex_I_3_7.exists_div_pow
#print axioms Hartshorne77.Ex_I_3_7.mem_zeroLocus_of_forall_eval_eq_zero
#print axioms Hartshorne77.Ex_I_3_7.mem_of_isHomogeneous_of_forall_X_pow_mem
#print axioms Hartshorne77.Ex_I_3_7.krullDimLE_zero_quotient
#print axioms Hartshorne77.Ex_I_3_7.m0_le_radical_of_zeroLocus_subset
#print axioms Hartshorne77.Ex_I_3_7.exists_X_pow_mem
#print axioms Hartshorne77.Ex_I_3_7.algebraic_imp_mem
#print axioms Hartshorne77.Ex_I_3_7.exists_minor_ne_zero
#print axioms Hartshorne77.Ex_I_3_7.two_points_of_one_le_topologicalKrullDim
#print axioms Hartshorne77.Ex_I_3_7.P.substLine_coeff
#print axioms Hartshorne77.Ex_I_3_7.P.eval_homogeneousComponent_eq_zero_of_eval_line
#print axioms Hartshorne77.Ex_I_3_7.P.formVanishesAt_iff_forall_homogeneousComponent
#print axioms Hartshorne77.Ex_I_3_7.P.isClosed_formVanishesAt
#print axioms Hartshorne77.Ex_I_3_7.P.formVanishesAt_mul
#print axioms Hartshorne77.Ex_I_3_7.P.isPrime_vanishOnIdeal

end

end Hartshorne77.Ex_I_3_7
