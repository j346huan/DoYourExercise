import Mathlib

/-!  Hartshorne I.1.9 -- point-set infrastructure for affine n-space over a field. -/

open MvPolynomial Set

namespace Hartshorne77.Ex_I_1_9

variable {k : Type*} [Field k] {n : ℕ}

/-- The zero locus of an ideal of `k[x_1,...,x_n]` inside `k^n`. -/
def Z (I : Ideal (MvPolynomial (Fin n) k)) : Set (Fin n → k) := MvPolynomial.zeroLocus k I

/-- The vanishing ideal of a subset of `k^n`. -/
def I (V : Set (Fin n → k)) : Ideal (MvPolynomial (Fin n) k) := MvPolynomial.vanishingIdeal k V

theorem mem_Z {I₀ : Ideal (MvPolynomial (Fin n) k)} {x : Fin n → k} :
    x ∈ Z I₀ ↔ ∀ p ∈ I₀, aeval x p = 0 := Iff.rfl

theorem mem_I {V : Set (Fin n → k)} {p : MvPolynomial (Fin n) k} :
    p ∈ I V ↔ ∀ x ∈ V, aeval x p = 0 := Iff.rfl

theorem z_bot : Z (⊥ : Ideal (MvPolynomial (Fin n) k)) = univ := MvPolynomial.zeroLocus_bot
theorem z_top : Z (⊤ : Ideal (MvPolynomial (Fin n) k)) = (∅ : Set (Fin n → k)) :=
  MvPolynomial.zeroLocus_top
theorem i_empty : I (∅ : Set (Fin n → k)) = ⊤ := MvPolynomial.vanishingIdeal_empty

theorem z_mono {I₀ J₀ : Ideal (MvPolynomial (Fin n) k)} (h : I₀ ≤ J₀) : Z J₀ ⊆ Z I₀ :=
  MvPolynomial.zeroLocus_anti_mono h

theorem i_mono {V W : Set (Fin n → k)} (h : V ⊆ W) : I W ≤ I V :=
  MvPolynomial.vanishingIdeal_anti_mono h

/-- Galois adjunction: `V ⊆ Z I₀ ↔ I₀ ≤ I V`. -/
theorem le_z_iff_le_i {V : Set (Fin n → k)} {I₀ : Ideal (MvPolynomial (Fin n) k)} :
    V ⊆ Z I₀ ↔ I₀ ≤ I V := MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal

theorem subset_z_i (V : Set (Fin n → k)) : V ⊆ Z (I V) := MvPolynomial.zeroLocus_vanishingIdeal_le V

theorem z_sup (I₀ J₀ : Ideal (MvPolynomial (Fin n) k)) : Z I₀ ∩ Z J₀ = Z (I₀ ⊔ J₀) := by
  apply le_antisymm
  · rintro x ⟨h1, h2⟩ p hp
    rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, rfl⟩
    rw [map_add, h1 a ha, h2 b hb, add_zero]
  · intro x hx
    exact ⟨z_mono le_sup_left hx, z_mono le_sup_right hx⟩

/-- Over a field, the union of two zero loci is the zero locus of the intersection.
(Hartshorne, proof of Prop. 1.1, uses that `k` has no zero divisors.) -/
theorem z_inf (I₀ J₀ : Ideal (MvPolynomial (Fin n) k)) : Z I₀ ∪ Z J₀ = Z (I₀ ⊓ J₀) := by
  apply le_antisymm
  · rintro x (hx | hx)
    · exact z_mono inf_le_left hx
    · exact z_mono inf_le_right hx
  · intro x hx
    by_cases h : x ∈ Z I₀
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [mem_Z, not_forall] at h
      obtain ⟨f, hfI, hf⟩ := h
      intro g hgJ
      have hmem : f * g ∈ I₀ ⊓ J₀ := ⟨I₀.mul_mem_right g hfI, J₀.mul_mem_left f hgJ⟩
      have hz : aeval x (f * g) = 0 := hx (f * g) hmem
      rw [map_mul] at hz
      exact (mul_eq_zero.mp hz).resolve_left hf

theorem z_iSup {ι : Type*} (I₀ : ι → Ideal (MvPolynomial (Fin n) k)) :
    Z (⨆ i, I₀ i) = {x | ∀ i, x ∈ Z (I₀ i)} := by
  apply le_antisymm
  · intro x hx i
    exact z_mono (le_iSup I₀ i) hx
  · intro x hx p hp
    have hle : (⨆ i, I₀ i) ≤ I {x} := by
      refine iSup_le fun i => ?_
      exact le_z_iff_le_i (V := {x}) (I₀ := I₀ i) |>.mp (singleton_subset_iff.mpr (hx i))
    exact mem_I.mp (hle hp) x rfl

/-- The Zariski topology on `k^n`: open sets are complements of zero loci. -/
instance : TopologicalSpace (Fin n → k) where
  IsOpen s := ∃ I₀ : Ideal (MvPolynomial (Fin n) k), s = (Z I₀)ᶜ
  isOpen_univ := ⟨⊤, by rw [z_top, compl_empty]⟩
  isOpen_inter := by
    rintro s t ⟨I₀, rfl⟩ ⟨J₀, rfl⟩
    refine ⟨I₀ ⊓ J₀, ?_⟩
    rw [← z_inf]
    exact (compl_union _ _).symm
  isOpen_sUnion := by
    rintro S hS
    have h2 : ∀ s : S, ∃ J₀ : Ideal (MvPolynomial (Fin n) k), (s : Set (Fin n → k)) = (Z J₀)ᶜ :=
      fun s => hS s s.2
    choose J₀ hJ using h2
    refine ⟨⨆ s : S, J₀ s, ?_⟩
    have hmain : (Z (⨆ s : S, J₀ s))ᶜ = ⋃ s : S, (Z (J₀ s))ᶜ := by
      rw [z_iSup]
      ext x
      simp only [mem_compl_iff, Set.mem_ofPred_eq, mem_iUnion, not_forall]
    rw [sUnion_eq_iUnion, hmain]
    exact iUnion_congr hJ

theorem isClosed_iff (s : Set (Fin n → k)) :
    IsClosed s ↔ ∃ I₀ : Ideal (MvPolynomial (Fin n) k), s = Z I₀ := by
  rw [← isOpen_compl_iff]
  constructor
  · rintro ⟨I₀, hI⟩
    exact ⟨I₀, compl_inj_iff.mp hI⟩
  · rintro ⟨I₀, rfl⟩
    exact ⟨I₀, rfl⟩

theorem isClosed_Z (I₀ : Ideal (MvPolynomial (Fin n) k)) : IsClosed (Z I₀) :=
  (isClosed_iff _).mpr ⟨I₀, rfl⟩

theorem isOpen_compl_Z (I₀ : Ideal (MvPolynomial (Fin n) k)) : IsOpen (Z I₀)ᶜ :=
  ⟨I₀, rfl⟩

/-- Zero loci are closed, so the closure of `V` is contained in `Z (I V)`. -/
theorem closure_le_z_i (V : Set (Fin n → k)) : closure V ⊆ Z (I V) :=
  closure_minimal (subset_z_i V) (isClosed_Z _)


/-- The zero locus of a single polynomial. -/
def Zf (f : MvPolynomial (Fin n) k) : Set (Fin n → k) := Z (Ideal.span {f})

theorem isClosed_Zf (f : MvPolynomial (Fin n) k) : IsClosed (Zf f) := isClosed_Z _

theorem Zf_eq (f : MvPolynomial (Fin n) k) : Zf f = {x : Fin n → k | aeval x f = 0} := by
  rw [Zf, Z, MvPolynomial.zeroLocus_span]
  simp

theorem mem_Zf {f : MvPolynomial (Fin n) k} {x : Fin n → k} : x ∈ Zf f ↔ aeval x f = 0 := by
  rw [Zf_eq]; rfl

section Nullstellensatz

variable [IsAlgClosed k]

/-- Hilbert's Nullstellensatz: `I (Z I₀) = √I₀`. -/
theorem i_z_eq_radical (I₀ : Ideal (MvPolynomial (Fin n) k)) : I (Z I₀) = I₀.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I₀

/-- For a prime ideal, `I (Z p) = p` (Nullstellensatz + `p` radical). -/
theorem i_z_eq_self (p : Ideal (MvPolynomial (Fin n) k)) [hp : p.IsPrime] : I (Z p) = p :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus p

omit [IsAlgClosed k] in
/-- `Z (I V)` is the closure of `V`. -/
theorem z_i_eq_closure (V : Set (Fin n → k)) : Z (I V) = closure V := by
  apply le_antisymm
  · obtain ⟨J₀, hJ⟩ := (isClosed_iff (closure V)).mp isClosed_closure
    have h1 : J₀ ≤ I V :=
      (le_z_iff_le_i (V := V) (I₀ := J₀)).mp (by rw [← hJ]; exact subset_closure)
    calc Z (I V) ⊆ Z J₀ := z_mono h1
      _ = closure V := hJ.symm
  · exact closure_le_z_i V

omit [IsAlgClosed k] in
/-- For a closed set, `Z (I s) = s`. -/
theorem z_i_eq_self {s : Set (Fin n → k)} (h : IsClosed s) : Z (I s) = s := by
  rw [z_i_eq_closure, h.closure_eq]

omit [IsAlgClosed k] in
/-- The vanishing ideal of an irreducible closed set is prime. -/
theorem isPrime_i_of_isClosed_isIrreducible {s : Set (Fin n → k)} (_hc : IsClosed s)
    (hi : IsIrreducible s) : (I s).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ I s := htop ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := hi.nonempty
    have h2 : aeval x (1 : MvPolynomial (Fin n) k) = 0 := mem_I.mp h1 x hx
    rw [map_one] at h2
    exact one_ne_zero h2
  · intro f g hfg
    by_cases hf : f ∈ I s
    · exact Or.inl hf
    · refine Or.inr ?_
      have hsub : s ⊆ Zf f ∪ Zf g := by
        intro x hx
        have h0 : aeval x (f * g) = 0 := mem_I.mp hfg x hx
        rw [map_mul] at h0
        rcases mul_eq_zero.mp h0 with h' | h'
        · exact Or.inl (mem_Zf.mpr h')
        · exact Or.inr (mem_Zf.mpr h')
      rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hi.isPreirreducible)
        (Zf f) (Zf g) (isClosed_Zf f) (isClosed_Zf g) hsub with h' | h'
      · exact absurd ((le_z_iff_le_i (V := s) (I₀ := Ideal.span {f})).mp h'
          (Ideal.subset_span (Set.mem_singleton f))) hf
      · intro x hx
        exact mem_Zf.mp (h' hx)

/-- The zero locus of a prime ideal is irreducible. -/
theorem isIrreducible_Z (p : Ideal (MvPolynomial (Fin n) k)) [hp : p.IsPrime] :
    IsIrreducible (Z p) := by
  have hne : (Z p).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hp.ne_top (by rw [← i_z_eq_self p, h, i_empty])
  refine ⟨hne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro z₁ z₂ hc₁ hc₂ hsub
  by_contra hcon
  have hz₁ : ¬ (Z p ⊆ z₁) := fun h => hcon (Or.inl h)
  have hz₂ : ¬ (Z p ⊆ z₂) := fun h => hcon (Or.inr h)
  have hf : ∃ f ∈ I z₁, f ∉ p := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hz₁ (by rw [← z_i_eq_self hc₁]; exact z_mono hall)
  have hg : ∃ g ∈ I z₂, g ∉ p := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hz₂ (by rw [← z_i_eq_self hc₂]; exact z_mono hall)
  obtain ⟨f, hf₁, hf₂⟩ := hf
  obtain ⟨g, hg₁, hg₂⟩ := hg
  have hmem : f * g ∈ I (Z p) := by
    refine mem_I.mpr fun x hx => ?_
    have hx' : x ∈ z₁ ∪ z₂ := hsub hx
    rcases hx' with h | h
    · rw [map_mul, mem_I.mp hf₁ x h, zero_mul]
    · rw [map_mul, mem_I.mp hg₁ x h, mul_zero]
  rw [i_z_eq_self p] at hmem
  exact (hp.mem_or_mem hmem).elim hf₂ hg₂

end Nullstellensatz


/-- Irreducible closed subsets of `Z a`, viewed as irreducible closed subsets of the ambient `k^n`.
This is the point-set side of the dictionary between subvarieties of `Z a` and prime ideals
containing `a`. -/
def Irr (a : Ideal (MvPolynomial (Fin n) k)) : Type _ :=
  {S : Set (Fin n → k) // IsClosed S ∧ IsIrreducible S ∧ S ⊆ Z a}

namespace Irr

variable {a : Ideal (MvPolynomial (Fin n) k)}

instance : SetLike (Irr a) (Fin n → k) where
  coe S := S.1
  coe_injective := by
    rintro ⟨S, hS⟩ ⟨T, hT⟩ rfl
    rfl

instance : PartialOrder (Irr a) := fast_instance% .ofSetLike (Irr a) (Fin n → k)

theorem isClosed (S : Irr a) : IsClosed (S : Set (Fin n → k)) := S.2.1
theorem isIrreducible (S : Irr a) : IsIrreducible (S : Set (Fin n → k)) := S.2.2.1
theorem subset (S : Irr a) : (S : Set (Fin n → k)) ⊆ Z a := S.2.2.2
theorem ext {S T : Irr a} (h : (S : Set (Fin n → k)) = (T : Set (Fin n → k))) : S = T :=
  Subtype.ext h
theorem le_def {S T : Irr a} : S ≤ T ↔ (S : Set (Fin n → k)) ⊆ (T : Set (Fin n → k)) := Iff.rfl

end Irr

section Dimension

variable [IsAlgClosed k]

/-- An irreducible closed subset of `Z a` gives a prime ideal containing `a`. -/
noncomputable def irrToPrime (a : Ideal (MvPolynomial (Fin n) k)) (S : Irr a) :
    PrimeSpectrum.zeroLocus (a : Set (MvPolynomial (Fin n) k)) :=
  ⟨⟨I S.1, isPrime_i_of_isClosed_isIrreducible S.isClosed S.isIrreducible⟩, by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact le_trans (le_vanishingIdeal_zeroLocus a) (i_mono S.subset)⟩

/-- A prime ideal containing `a` gives an irreducible closed subset of `Z a`. -/
noncomputable def primeToIrr (a : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum.zeroLocus (a : Set (MvPolynomial (Fin n) k))) : Irr a :=
  ⟨Z q.1.asIdeal, isClosed_Z q.1.asIdeal, isIrreducible_Z q.1.asIdeal, z_mono q.2⟩

theorem primeToIrr_irrToPrime (a : Ideal (MvPolynomial (Fin n) k)) (S : Irr a) :
    primeToIrr a (irrToPrime a S) = S := by
  apply Irr.ext
  exact z_i_eq_self S.isClosed

theorem irrToPrime_primeToIrr (a : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum.zeroLocus (a : Set (MvPolynomial (Fin n) k))) :
    irrToPrime a (primeToIrr a q) = q := by
  apply Subtype.ext
  apply PrimeSpectrum.ext
  exact i_z_eq_self q.1.asIdeal

/-- **The dictionary**: irreducible closed subsets of `Z a` are order-antitone to the prime
ideals containing `a`; this is the point-set form of `Y ↦ I(Y)`. -/
noncomputable def irrOrderIso (a : Ideal (MvPolynomial (Fin n) k)) :
    Irr a ≃o (PrimeSpectrum.zeroLocus (a : Set (MvPolynomial (Fin n) k)))ᵒᵈ where
  toFun S := OrderDual.toDual (irrToPrime a S)
  invFun q := primeToIrr a (OrderDual.ofDual q)
  left_inv S := primeToIrr_irrToPrime a S
  right_inv q := by
    apply OrderDual.toDual_inj.mpr
    exact irrToPrime_primeToIrr a (OrderDual.ofDual q)
  map_rel_iff' {S T} := by
    constructor
    · intro h
      -- `irrToPrime a S ≥ irrToPrime a T`, i.e. `I T ≤ I S`, hence `S ⊆ Z(I S) ⊆ Z(I T) ⊇ T`
      have hle : (I T.1) ≤ (I S.1) := h
      have hz : Z (I S.1) ⊆ Z (I T.1) := z_mono hle
      have hST : (S : Set (Fin n → k)) ⊆ Z a := S.subset
      calc (S : Set (Fin n → k)) = Z (I S.1) := (z_i_eq_self S.isClosed).symm
        _ ⊆ Z (I T.1) := hz
        _ = (T : Set (Fin n → k)) := z_i_eq_self T.isClosed
    · intro h
      exact i_mono (Irr.le_def.mp h)

/-- **The dimension of `Z a` equals the Krull dimension of the coordinate ring.** -/
theorem krullDim_Irr (a : Ideal (MvPolynomial (Fin n) k)) :
    Order.krullDim (Irr a) = ringKrullDim (MvPolynomial (Fin n) k ⧸ a) := by
  rw [ringKrullDim_quotient]
  rw [← Order.krullDim_orderDual (α := PrimeSpectrum.zeroLocus (a : Set (MvPolynomial (Fin n) k)))]
  exact Order.krullDim_eq_of_orderIso (irrOrderIso a)

end Dimension


section Subspace

open TopologicalSpace in
/-- Passing an irreducible closed subset of the subspace `Z a` to the ambient space. -/
noncomputable def toIrr (a : Ideal (MvPolynomial (Fin n) k))
    (T : TopologicalSpace.IrreducibleCloseds ↥(Z a)) : Irr a :=
  ⟨closure ((Subtype.val : ↥(Z a) → (Fin n → k)) '' (T : Set ↥(Z a))), isClosed_closure,
    (T.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn).closure,
    closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) (isClosed_Z a)⟩

open TopologicalSpace in
/-- Passing an irreducible closed subset of the ambient space contained in `Z a` to the subspace. -/
noncomputable def ofIrr (a : Ideal (MvPolynomial (Fin n) k)) (S : Irr a) :
    TopologicalSpace.IrreducibleCloseds ↥(Z a) :=
  ⟨{x : ↥(Z a) | (x : Fin n → k) ∈ (S : Set (Fin n → k))},
    (by
      refine ⟨⟨⟨S.isIrreducible.nonempty.choose, S.subset S.isIrreducible.nonempty.choose_spec⟩,
        S.isIrreducible.nonempty.choose_spec⟩, ?_⟩
      rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hc₁ hc₂ hsub
      obtain ⟨F₁, hF₁, hz₁⟩ := isClosed_induced_iff.mp hc₁
      obtain ⟨F₂, hF₂, hz₂⟩ := isClosed_induced_iff.mp hc₂
      have hSF : (S : Set (Fin n → k)) ⊆ F₁ ∪ F₂ := by
        intro y hy
        have hyT : (⟨y, S.subset hy⟩ : ↥(Z a)) ∈
            {x : ↥(Z a) | (x : Fin n → k) ∈ (S : Set (Fin n → k))} := hy
        have hmem := hsub hyT
        rw [← hz₁, ← hz₂] at hmem
        exact hmem
      rcases (isPreirreducible_iff_isClosed_union_isClosed.mp S.isIrreducible.isPreirreducible)
        F₁ F₂ hF₁ hF₂ hSF with h | h
      · left
        rw [← hz₁]
        exact fun x hx => h hx
      · right
        rw [← hz₂]
        exact fun x hx => h hx),
    (isClosed_induced_iff.mpr ⟨(S : Set (Fin n → k)), S.isClosed, rfl⟩)⟩

theorem ofIrr_toIrr (a : Ideal (MvPolynomial (Fin n) k))
    (T : TopologicalSpace.IrreducibleCloseds ↥(Z a)) : ofIrr a (toIrr a T) = T := by
  apply TopologicalSpace.IrreducibleCloseds.ext
  ext x
  constructor
  · intro hx
    -- x ∈ closure of the image, and T is closed: T = val ⁻¹' F
    obtain ⟨F, hF, hTF⟩ := isClosed_induced_iff.mp T.isClosed
    have hsub : ((Subtype.val : ↥(Z a) → (Fin n → k)) '' (T : Set ↥(Z a))) ⊆ F := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : y ∈ (Subtype.val : ↥(Z a) → (Fin n → k)) ⁻¹' F := by
        rw [hTF]; exact hy
      exact h1
    have hcl : closure ((Subtype.val : ↥(Z a) → (Fin n → k)) '' (T : Set ↥(Z a))) ⊆ F :=
      closure_minimal hsub hF
    rw [← hTF]
    exact hcl hx
  · intro hx
    exact subset_closure ⟨x, hx, rfl⟩

theorem toIrr_ofIrr (a : Ideal (MvPolynomial (Fin n) k)) (S : Irr a) :
    toIrr a (ofIrr a S) = S := by
  apply Irr.ext
  show closure ((Subtype.val : ↥(Z a) → (Fin n → k)) ''
      ((ofIrr a S : Set ↥(Z a)))) = (S : Set (Fin n → k))
  have himg : ((Subtype.val : ↥(Z a) → (Fin n → k)) ''
      ((ofIrr a S : Set ↥(Z a))))
      = (S : Set (Fin n → k)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, S.subset hy⟩, hy, rfl⟩
  rw [himg, S.isClosed.closure_eq]

theorem toIrr_mono (a : Ideal (MvPolynomial (Fin n) k))
    {T T' : TopologicalSpace.IrreducibleCloseds ↥(Z a)} (h : T ≤ T') :
    toIrr a T ≤ toIrr a T' := by
  apply Irr.le_def.mpr
  exact closure_mono (Set.image_mono (f := (Subtype.val : ↥(Z a) → (Fin n → k)))
    (show (T : Set ↥(Z a)) ⊆ (T' : Set ↥(Z a)) from h))

theorem ofIrr_mono (a : Ideal (MvPolynomial (Fin n) k)) {S S' : Irr a} (h : S ≤ S') :
    ofIrr a S ≤ ofIrr a S' := by
  intro x hx
  exact Irr.le_def.mp h hx

open TopologicalSpace in
/-- **Dimension of a closed set**: chains of irreducible closed subsets of the subspace `Z a`
are the same as chains of irreducible closed subsets of `k^n` contained in `Z a`. -/
noncomputable def subspaceOrderIso (a : Ideal (MvPolynomial (Fin n) k)) :
    TopologicalSpace.IrreducibleCloseds ↥(Z a) ≃o Irr a where
  toFun := toIrr a
  invFun := ofIrr a
  left_inv := ofIrr_toIrr a
  right_inv := toIrr_ofIrr a
  map_rel_iff' {T T'} := by
    constructor
    · intro h
      have h2 : ofIrr a (toIrr a T) ≤ ofIrr a (toIrr a T') := ofIrr_mono a h
      rwa [ofIrr_toIrr, ofIrr_toIrr] at h2
    · intro h
      exact toIrr_mono a h

open TopologicalSpace in
/-- The dimension of `Z a` (supremum of lengths of chains of irreducible closed subsets) is the
Krull dimension of the coordinate ring. -/
theorem topologicalKrullDim_Z [IsAlgClosed k] (a : Ideal (MvPolynomial (Fin n) k)) :
    topologicalKrullDim ↥(Z a) = ringKrullDim (MvPolynomial (Fin n) k ⧸ a) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (subspaceOrderIso a), krullDim_Irr]

open TopologicalSpace in
/-- In particular `dim A^n = n`: the affine space `A^n = k^n` has Krull dimension `n`
(Hartshorne's `dim`, i.e. the supremum of lengths of chains of irreducible closed subsets). -/
theorem topologicalKrullDim_affineSpace [IsAlgClosed k] :
    topologicalKrullDim (Fin n → k) = (n : ℕ∞) := by
  have h : (Z (⊥ : Ideal (MvPolynomial (Fin n) k))) = (univ : Set (Fin n → k)) := z_bot
  have hd : topologicalKrullDim ↥(Z (⊥ : Ideal (MvPolynomial (Fin n) k)))
      = topologicalKrullDim (Fin n → k) := by
    rw [h]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
  rw [← hd, topologicalKrullDim_Z]
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial (Fin n) k)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

end Subspace


section Components

variable [IsAlgClosed k]

/-- **Components correspond to minimal primes.** An irreducible closed subset `Z p` of `Z a` is a
component of `Z a` (i.e. maximal among irreducible closed subsets of `Z a`) if and only if `p` is a
minimal prime over `a`. -/
theorem isMinimalPrime_iff_component (a : Ideal (MvPolynomial (Fin n) k))
    (p : Ideal (MvPolynomial (Fin n) k)) (hp : p.IsPrime) :
    Ideal.IsMinimalPrime a p ↔
      (IsIrreducible (Z p) ∧ Z p ⊆ Z a ∧ ∀ W : Set (Fin n → k), IsClosed W → IsIrreducible W →
        Z p ⊆ W → W ⊆ Z a → W = Z p) := by
  constructor
  · intro hmin
    refine ⟨isIrreducible_Z p, z_mono hmin.le, ?_⟩
    intro W hWc hWi h1 h2
    have hq : (I W).IsPrime := isPrime_i_of_isClosed_isIrreducible hWc hWi
    have haq : a ≤ I W := le_trans (le_vanishingIdeal_zeroLocus a) (i_mono h2)
    have hqp : I W ≤ p := le_trans (i_mono h1) (le_of_eq (i_z_eq_self p))
    have heq : p = I W := (hmin.eq_of_le ⟨hq, haq⟩ hqp).symm
    rw [← z_i_eq_self hWc, heq]
  · rintro ⟨-, hsub, hmax⟩
    have hap : a ≤ p := by
      have h1 : I (Z a) ≤ I (Z p) := i_mono hsub
      rw [i_z_eq_self p] at h1
      exact le_trans (le_vanishingIdeal_zeroLocus a) h1
    refine ⟨⟨hp, hap⟩, ?_⟩
    rintro q ⟨hq, haq⟩ hqp
    have h1 : Z p ⊆ Z q := z_mono hqp
    have h2 : Z q ⊆ Z a := z_mono haq
    have heq : Z q = Z p := hmax (Z q) (isClosed_Z q) (isIrreducible_Z q) h1 h2
    have : q = I (Z q) := (i_z_eq_self q).symm
    rw [this, heq, i_z_eq_self p]

/-- **Reduction of I.1.9 to algebra**: the dimension of a component `W` of `Z a` equals the Krull
dimension of the coordinate ring `k[x_1,...,x_n]/I(W)`. -/
theorem topologicalKrullDim_component (_a : Ideal (MvPolynomial (Fin n) k))
    {W : Set (Fin n → k)} (hWc : IsClosed W) :
    topologicalKrullDim ↥W = ringKrullDim (MvPolynomial (Fin n) k ⧸ I W) := by
  have h : W = Z (I W) := (z_i_eq_self hWc).symm
  have step : topologicalKrullDim ↥W = topologicalKrullDim ↥(Z (I W)) := by
    conv_lhs => rw [h]
  rw [step]
  exact topologicalKrullDim_Z (I W)

end Components

end Hartshorne77.Ex_I_1_9
