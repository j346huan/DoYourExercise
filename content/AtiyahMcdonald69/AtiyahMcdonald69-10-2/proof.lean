import Mathlib

/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 10.2 (p. 114)

Book statement (Chapter 10, "Completions", Exercise 2):

  "In Exercise 1, let A_n = α⁻¹(pⁿB), and consider the exact sequence
     0 → A_n → A → A/A_n → 0.
   Show that lim is not right exact, and compute lim¹ A_n."
   (notation of Exercise 10.1: A = ⊕_{j≥1} ℤ/pℤ, B = ⊕_{j≥1} ℤ/pʲℤ, and
    α = ⊕_j α_j : A → B the direct sum of the injections α_j : ℤ/pℤ → ℤ/pʲℤ, 1 ↦ p^{j-1}.)

We index the copies of ℤ/p by ℕ starting at 0, so the j-th copy lands in ℤ/p^{j+1} via
multiplication by p^j.  Carlson's solution manual confirms the expected answer
lim¹ A_n ≅ (∏_j ℤ/pℤ)/(⊕_j ℤ/pℤ).

The data of Exercise 10.1 are constructed explicitly here (`A`, `B`, `alphaComp`, `alpha`,
`pPow`, `pPowSub`), and the following is proved, for every prime p:

* `Asub_eq_comap`  : A_n = α⁻¹(pⁿB) = ⊕_{j ≥ n} ℤ/p;
* `short_exact`    : 0 → A_n → A → A/A_n → 0 is exact for every n;
* `subsingleton_ALim` : lim A_n = 0;
* `limConstEquiv`, `subsingleton_lim1_const` : the constant system has limit A and lim¹ = 0;
* `limQuotEquiv`   : lim (A/A_n) ≅ ∏_j ℤ/p;
* `limMap_QF_eq_incl` : under these identifications the map lim A → lim (A/A_n) is the
                     inclusion of the direct sum into the product;
* `not_surjective_limMap_QF` : **lim is not right exact** (that map is not surjective);
* `lim1Equiv`      : **lim¹ A_n ≅ (∏_j ℤ/p)/(⊕_j ℤ/p)**;
* `nontrivial_lim1`, `not_surjective_incl` : lim¹ A_n ≠ 0.

For an ℕᵒᵖ-indexed inverse system of abelian groups (G_n, f_n) we realise lim and lim¹ as the
kernel and cokernel of the difference map d(x)_n = x_n - f_n(x_{n+1}) on ∏_n G_n; this is the
standard concrete description of the inverse limit and of its first derived functor lim¹.
All proofs are complete: no sorry and no axioms beyond Lean's three standard ones.
-/


set_option maxHeartbeats 4000000

namespace AtiyahMcdonald69.Ex_10_2

noncomputable section

/-! ## §1. Inverse systems indexed by `ℕ`, limits and first derived limits -/

section System

variable (G : ℕ → Type*) [∀ n, AddCommGroup (G n)]

/-- The difference map `x ↦ (x n - f n (x (n+1)))_n` on the product of the terms. -/
def diffHom (f : ∀ n, G (n+1) →+ G n) : (∀ n, G n) →+ (∀ n, G n) where
  toFun x := fun n => x n - f n (x (n+1))
  map_zero' := by
    funext n
    simp only [Pi.zero_apply, map_zero, sub_self]
  map_add' := by
    intro x y
    funext n
    simp only [Pi.add_apply, map_add]
    abel

@[simp] lemma diffHom_apply (f : ∀ n, G (n+1) →+ G n) (x : ∀ n, G n) (n : ℕ) :
    diffHom G f x n = x n - f n (x (n+1)) := rfl

/-- The inverse limit: the subgroup of compatible families of the product. -/
def lim (f : ∀ n, G (n+1) →+ G n) : AddSubgroup (∀ n, G n) := (diffHom G f).ker

lemma mem_lim (f : ∀ n, G (n+1) →+ G n) (x : ∀ n, G n) :
    x ∈ lim G f ↔ ∀ n, f n (x (n+1)) = x n := by
  rw [lim, AddMonoidHom.mem_ker]
  constructor
  · intro h n
    have h' := congrFun h n
    simp only [diffHom_apply, Pi.zero_apply, sub_eq_zero] at h'
    exact h'.symm
  · intro h
    funext n
    simp only [diffHom_apply, Pi.zero_apply]
    exact sub_eq_zero.mpr (h n).symm

/-- The first derived limit `lim¹`: the cokernel of the difference map.  For `ℕᵒᵖ`-indexed
systems of abelian groups this is the standard description of `lim¹`. -/
abbrev lim1 (f : ∀ n, G (n+1) →+ G n) : Type _ := (∀ n, G n) ⧸ (diffHom G f).range

/-- A morphism of inverse systems induces a map on the limits. -/
def limMap {G' : ℕ → Type*} [∀ n, AddCommGroup (G' n)]
    (f : ∀ n, G (n+1) →+ G n) (f' : ∀ n, G' (n+1) →+ G' n)
    (φ : ∀ n, G n →+ G' n) (hφ : ∀ n, (φ n).comp (f n) = (f' n).comp (φ (n+1))) :
    lim G f →+ lim G' f' where
  toFun x :=
    ⟨fun n => φ n (x.val n), by
      rw [mem_lim]
      intro n
      have hx : f n (x.val (n+1)) = x.val n := (mem_lim G f x.val).mp x.property n
      have hcomm := DFunLike.congr_fun (hφ n) (x.val (n+1))
      simp only [AddMonoidHom.comp_apply] at hcomm
      rw [← hcomm, hx]⟩
  map_zero' := by
    ext n
    exact map_zero _
  map_add' := by
    intro x y
    ext n
    exact map_add _ _ _

@[simp] lemma limMap_apply {G' : ℕ → Type*} [∀ n, AddCommGroup (G' n)]
    {f : ∀ n, G (n+1) →+ G n} {f' : ∀ n, G' (n+1) →+ G' n} (φ : ∀ n, G n →+ G' n)
    (hφ : ∀ n, (φ n).comp (f n) = (f' n).comp (φ (n+1))) (x : lim G f) (n : ℕ) :
    (limMap (G := G) (G' := G') f f' φ hφ x).val n = φ n (x.val n) := rfl

end System

/-! ## §2. The group `A = ⊕_j ℤ/p` and the subgroups `A_n = ⊕_{j ≥ n} ℤ/p` -/

section Data

variable (p : ℕ) [hp : Fact p.Prime]

instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- `A = ⊕_{j ≥ 0} ℤ/pℤ`, the countable direct sum of copies of `ℤ/p`. -/
abbrev A : Type := Π₀ _ : ℕ, ZMod p

/-- The `n`-th term of the inverse system: `A_n = ⊕_{j ≥ n} ℤ/pℤ`.  In §6 this is identified
with `α⁻¹(p^n B)` for the map `α : A → B` of Exercise 10.1. -/
def Asub (n : ℕ) : AddSubgroup (A p) where
  carrier := {a | ∀ j, j < n → a j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' := by
    intro a b ha hb j hj
    simp only [DFinsupp.add_apply, ha j hj, hb j hj, add_zero]
  neg_mem' := by
    intro a ha j hj
    simp only [DFinsupp.neg_apply, ha j hj, neg_zero]

lemma mem_Asub {n : ℕ} {a : A p} : a ∈ Asub (p := p) n ↔ ∀ j, j < n → a j = 0 := Iff.rfl

lemma Asub_antitone : Antitone (Asub (p := p)) := by
  intro m n hmn a ha j hj
  exact ha j (lt_of_lt_of_le hj hmn)

/-- The family of types underlying the system `(A_n)`. -/
abbrev AsysT : ℕ → Type := fun n => Asub (p := p) n

/-- The transition map `A_{n+1} → A_n` (an inclusion). -/
def AsysF : ∀ n, AsysT p (n+1) →+ AsysT p n :=
  fun n => AddSubgroup.inclusion (Asub_antitone (p := p) (Nat.le_succ n))

lemma AsysF_coe (n : ℕ) (x : AsysT p (n+1)) :
    ((AsysF p n x : AsysT p n) : A p) = (x : A p) := rfl

/-- The limit of the system `(A_n)`. -/
abbrev ALim : AddSubgroup (∀ n, AsysT p n) := lim (AsysT p) (AsysF p)

/-- `⋂_n A_n = 0`. -/
theorem iInf_Asub : (⨅ n, Asub (p := p) n) = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro a ha
  rw [AddSubgroup.mem_iInf] at ha
  by_contra h
  have hex : ∃ j, a j ≠ 0 := by
    by_contra h'
    exact h (DFinsupp.ext fun j => by
      by_contra hj
      exact h' ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hex
  exact hj (ha (j+1) j (Nat.lt_succ_self j))

/-- The limit of the system `(A_n)` is trivial. -/
theorem subsingleton_ALim : Subsingleton (ALim p) := by
  have key0 : ∀ (z : ALim p) (m : ℕ), (z.val m : A p) = (z.val 0 : A p) := by
    intro z m
    induction m with
    | zero => rfl
    | succ m ih =>
      have h := (mem_lim (AsysT p) (AsysF p) z.val).mp z.property m
      have h2 : (z.val (m+1) : A p) = (z.val m : A p) := by
        rw [← AsysF_coe (p := p) m (z.val (m+1)), h]
      rw [h2, ih]
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ (z : ALim p) (m : ℕ), (z.val m : A p) = 0 := by
    intro z m
    have hmem : (z.val m : A p) ∈ ⨅ n, Asub (p := p) n := by
      rw [AddSubgroup.mem_iInf]
      intro n
      rw [(key0 z m).trans (key0 z n).symm]
      exact (z.val n).property
    rw [iInf_Asub (p := p)] at hmem
    simpa using hmem
  have hxy : x.val = y.val := by
    funext m
    exact Subtype.ext ((hzero x m).trans (hzero y m).symm)
  exact Subtype.ext hxy

/-! ## §3. The constant system on `A`, the system of quotients `A ⧸ A_n` -/

/-- The constant system on `A` (identity transition maps). -/
abbrev constT : ℕ → Type := fun _ => A p

/-- The transition maps of the constant system. -/
def constF : ∀ n, constT p (n+1) →+ constT p n := fun _ => AddMonoidHom.id (A p)

/-- The system of quotients `A ⧸ A_n`. -/
abbrev QT : ℕ → Type := fun n => A p ⧸ Asub (p := p) n

/-- The projection `A ⧸ A_{n+1} →+ A ⧸ A_n`. -/
def QF (n : ℕ) : QT p (n+1) →+ QT p n :=
  QuotientAddGroup.lift (Asub (p := p) (n+1)) (QuotientAddGroup.mk' (Asub (p := p) n))
    (by
      intro x hx
      simpa using Asub_antitone (p := p) (Nat.le_succ n) hx)

lemma QF_mk (n : ℕ) (a : A p) :
    QF p n (QuotientAddGroup.mk' (Asub (p := p) (n+1)) a)
      = QuotientAddGroup.mk' (Asub (p := p) n) a :=
  QuotientAddGroup.lift_mk' (Asub (p := p) (n+1)) _ a

/-- The system morphism from the constant system on `A` to `(A ⧸ A_n)`. -/
def toQF (n : ℕ) : constT p n →+ QT p n := QuotientAddGroup.mk' (Asub (p := p) n)

lemma toQF_compat : ∀ n, (toQF p n).comp (constF p n) = (QF p n).comp (toQF p (n+1)) := by
  intro n
  apply AddMonoidHom.ext
  intro a
  simp only [AddMonoidHom.comp_apply, constF, toQF, AddMonoidHom.id_apply]
  exact (QF_mk (p := p) (n := n) (a := a)).symm

/-- `mk' a = mk' b` in `A ⧸ A_n` as soon as `a - b ∈ A_n`. -/
lemma mk'_eq_of_sub_mem {n : ℕ} {a b : A p} (h : a - b ∈ Asub (p := p) n) :
    QuotientAddGroup.mk' (Asub (p := p) n) a = QuotientAddGroup.mk' (Asub (p := p) n) b := by
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨b - a, ?_, by abel⟩
  simpa using (Asub (p := p) n).neg_mem h

/-- Conversely, equal classes give a difference in `A_n`. -/
lemma sub_mem_of_mk'_eq {n : ℕ} {a b : A p}
    (h : QuotientAddGroup.mk' (Asub (p := p) n) a = QuotientAddGroup.mk' (Asub (p := p) n) b) :
    a - b ∈ Asub (p := p) n := by
  rw [QuotientAddGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz, hzab⟩ := h
  have h' : a - b = -z := by
    rw [← hzab]
    abel
  rw [h']
  exact (Asub (p := p) n).neg_mem hz

/-- `truncFun n = e_0 + ⋯ + e_{n-1}`, the truncation of the all-ones family. -/
def truncFun (n : ℕ) : A p := ∑ j ∈ Finset.range n, DFinsupp.single j (1 : ZMod p)

lemma truncFun_apply_lt {n j : ℕ} (hj : j < n) : truncFun p n j = 1 := by
  simp only [truncFun, DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · exact DFinsupp.single_eq_same
  · intro b _ hb
    exact DFinsupp.single_eq_of_ne (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

lemma truncFun_apply_of_le {n j : ℕ} (hj : n ≤ j) : truncFun p n j = 0 := by
  simp only [truncFun, DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  exact DFinsupp.single_eq_of_ne (by
    intro h
    exact absurd (h ▸ Finset.mem_range.mp hb) (Nat.not_lt.mpr hj))

lemma truncFun_succ (n : ℕ) : truncFun p (n+1) = truncFun p n + DFinsupp.single n (1 : ZMod p) := by
  simp only [truncFun, Finset.sum_range_succ]

lemma truncFun_compat (n : ℕ) : truncFun p (n+1) - truncFun p n ∈ Asub (p := p) n := by
  rw [truncFun_succ p n, add_sub_cancel_left]
  intro j hj
  exact DFinsupp.single_eq_of_ne (ne_of_lt hj)

/-- The element of `lim (A ⧸ A_n)` given by the classes of the truncations of the
constant family `1`. -/
def onesElem : lim (QT p) (QF p) :=
  ⟨fun n => QuotientAddGroup.mk' (Asub (p := p) n) (truncFun p n), by
    rw [mem_lim]
    intro n
    rw [QF_mk]
    exact mk'_eq_of_sub_mem (p := p) (n := n) (truncFun_compat p n)⟩

/-- **The limit functor is not right exact.**  The system morphism `A → A ⧸ A_n`
(surjective in every degree) does not stay surjective in the limit: the class of the
constant family `1` in `lim (A ⧸ A_n)` is not the image of any element of `lim A = A`. -/
theorem not_surjective_limMap_QF :
    ¬ Function.Surjective
      (limMap (G := constT p) (G' := QT p) (constF p) (QF p) (toQF p) (toQF_compat p)) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (onesElem p)
  -- `x` is a constant family
  have hxconst : ∀ n : ℕ, x.val n = x.val 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := (mem_lim (constT p) (constF p) x.val).mp x.property n
      simp only [constF, AddMonoidHom.id_apply] at h
      rw [h, ih]
  -- every coordinate of `x.val 0` equals `1`
  have hcoord : ∀ j : ℕ, x.val 0 j = 1 := by
    intro j
    have h1 : (limMap (G := constT p) (G' := QT p) (constF p) (QF p) (toQF p) (toQF_compat p) x).val (j+1)
        = (onesElem p).val (j+1) := by rw [hx]
    simp only [limMap_apply, toQF, onesElem] at h1
    have h2 : x.val (j+1) = x.val 0 := hxconst (j+1)
    rw [h2] at h1
    have h3 := sub_mem_of_mk'_eq (p := p) (n := j+1) h1
    have h4 : (x.val 0) j - truncFun p (j+1) j = 0 := by
      simpa only [DFinsupp.sub_apply] using h3 j (Nat.lt_succ_self j)
    rw [truncFun_apply_lt (p := p) (n := j+1) (j := j) (Nat.lt_succ_self j)] at h4
    exact sub_eq_zero.mp h4
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (x.val 0).support
  have hmem : N ∈ (x.val 0).support := by
    rw [DFinsupp.mem_support_iff]
    rw [hcoord]
    exact one_ne_zero
  exact absurd (hN hmem) (by simp)

/-! ## §4. Computation of `lim¹ A_n`: it is `(∏_j ℤ/p) / (⊕_j ℤ/p)` -/

/-- The product `∏_j ℤ/p`. -/
abbrev prodc : Type := ∀ _ : ℕ, ZMod p

/-- The canonical inclusion `⊕_j ℤ/p → ∏_j ℤ/p` of the direct sum into the product. -/
def incl : A p →+ prodc p where
  toFun a := fun j => a j
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] lemma incl_apply (a : A p) (j : ℕ) : incl p a j = a j := rfl

/-- The map `Θ` whose cokernel computes `lim¹` for the system `(A_n)`: it sums the `j`-th
coordinates of the terms `0, …, j` of the family. -/
def Theta : (∀ n, AsysT p n) →+ prodc p where
  toFun x := fun j => ∑ m ∈ Finset.range (j+1), ((x m : A p) j)
  map_zero' := by
    funext j
    refine Finset.sum_eq_zero fun m _ => ?_
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero, DFinsupp.zero_apply]
  map_add' := by
    intro x y
    funext j
    simp only [Pi.add_apply, AddSubgroup.coe_add, DFinsupp.add_apply, Finset.sum_add_distrib]

lemma Theta_apply (x : ∀ n, AsysT p n) (j : ℕ) :
    Theta p x j = ∑ m ∈ Finset.range (j+1), ((x m : A p) j) := rfl

/-- `Θ ∘ d = incl ∘ (evaluation at 0)`: the telescoping identity. -/
lemma Theta_diffHom (x : ∀ n, AsysT p n) :
    Theta p (diffHom (AsysT p) (AsysF p) x) = incl p ((x 0 : A p)) := by
  funext j
  rw [Theta_apply, incl_apply]
  have hterm : ∀ m : ℕ, ((diffHom (AsysT p) (AsysF p) x) m : A p) j
      = ((x m : A p) j) - ((x (m+1) : A p) j) := by
    intro m
    simp only [diffHom_apply, AddSubgroup.coe_sub, DFinsupp.sub_apply]
    rfl
  simp only [hterm]
  have hg := Finset.sum_range_sub (fun m => ((x m : A p) j)) (j+1)
  have h' : ∑ m ∈ Finset.range (j+1), (((x m : A p) j) - ((x (m+1) : A p) j))
      = -∑ m ∈ Finset.range (j+1), (((x (m+1) : A p) j) - ((x m : A p) j)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by abel
  rw [h', hg]
  have hzero : ((x (j+1) : A p) j) = 0 := (x (j+1)).property j (Nat.lt_succ_self j)
  rw [hzero]
  abel

/-- The family exhibiting surjectivity of `Θ`. -/
def shiftElem (c : prodc p) (n : ℕ) : AsysT p n :=
  ⟨DFinsupp.single n (c n), by
    intro i hi
    exact DFinsupp.single_eq_of_ne (by omega)⟩

lemma shiftElem_coe (c : prodc p) (n : ℕ) : ((shiftElem p c n : A p)) = DFinsupp.single n (c n) :=
  rfl

/-- `Θ` is surjective. -/
lemma Theta_surj (c : prodc p) : Theta p (fun n => shiftElem p c n) = c := by
  funext j
  rw [Theta_apply]
  have hterm : ∀ m : ℕ, ((shiftElem p c m : A p) j) = if m = j then c j else 0 := by
    intro m
    rw [shiftElem_coe]
    by_cases h : m = j
    · rw [if_pos h, h, DFinsupp.single_eq_same]
    · rw [if_neg h]
      exact DFinsupp.single_eq_of_ne (Ne.symm h)
  simp only [hterm]
  rw [Finset.sum_ite_eq' (Finset.range (j+1)) j (fun _ => c j)]
  simp

/-- The preimage of the direct sum under `Θ` is exactly the image of the difference map. -/
lemma Theta_mem_range {x : ∀ n, AsysT p n} {g : A p} (h : Theta p x = incl p g) :
    x ∈ (diffHom (AsysT p) (AsysF p)).range := by
  have hy : ∀ n, (g - ∑ m ∈ Finset.range n, ((x m : A p))) ∈ Asub (p := p) n := by
    intro n j hj
    have hgj : g j = Theta p x j := by rw [h]; rfl
    rw [DFinsupp.sub_apply, hgj, Theta_apply, DFinsupp.finsetSum_apply]
    have hsub : ∑ m ∈ Finset.range (j+1), ((x m : A p) j)
        = ∑ m ∈ Finset.range n, ((x m : A p) j) := by
      have hle : j + 1 ≤ n := by omega
      refine Finset.sum_subset (Finset.range_mono hle) ?_
      intro b hb hb'
      refine (x b).property j ?_
      simp only [Finset.mem_range] at hb hb'
      omega
    rw [hsub, sub_self]
  refine ⟨fun n => ⟨g - ∑ m ∈ Finset.range n, ((x m : A p)), hy n⟩, ?_⟩
  funext n
  apply Subtype.ext
  show (g - ∑ m ∈ Finset.range n, ((x m : A p)))
      - (AsysF p n ⟨g - ∑ m ∈ Finset.range (n+1), ((x m : A p)), hy (n+1)⟩ : A p) = (x n : A p)
  rw [AsysF_coe]
  show (g - ∑ m ∈ Finset.range n, ((x m : A p))) - (g - ∑ m ∈ Finset.range (n+1), ((x m : A p)))
    = (x n : A p)
  rw [Finset.sum_range_succ]
  abel

/-- `lim¹ A_n → (∏_j ℤ/p)/(⊕_j ℤ/p)`, induced by `Θ`. -/
def lim1ToQuot : lim1 (AsysT p) (AsysF p) →+ (prodc p ⧸ (incl p).range) :=
  QuotientAddGroup.lift ((diffHom (AsysT p) (AsysF p)).range)
    ((QuotientAddGroup.mk' (incl p).range).comp (Theta p))
    (by
      rintro z ⟨x, rfl⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      rw [Theta_diffHom]
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨x 0, rfl⟩)

lemma lim1ToQuot_mk (x : ∀ n, AsysT p n) :
    lim1ToQuot p (QuotientAddGroup.mk' _ x) = QuotientAddGroup.mk' (incl p).range (Theta p x) :=
  QuotientAddGroup.lift_mk' _ _ x

theorem lim1ToQuot_bijective : Function.Bijective (lim1ToQuot p) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (N := (diffHom (AsysT p) (AsysF p)).range) a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (N := (diffHom (AsysT p) (AsysF p)).range) b
    rw [lim1ToQuot_mk, lim1ToQuot_mk] at hab
    have hmem : Theta p (x - y) ∈ (incl p).range := by
      rw [map_sub]
      rw [QuotientAddGroup.mk'_eq_mk'] at hab
      obtain ⟨z, hz, hzxy⟩ := hab
      have h' : Theta p x - Theta p y = -z := by rw [← hzxy]; abel
      rw [h']
      exact (incl p).range.neg_mem hz
    obtain ⟨g, hg⟩ := hmem
    have hxyrange : x - y ∈ (diffHom (AsysT p) (AsysF p)).range := Theta_mem_range p hg.symm
    rw [QuotientAddGroup.mk'_eq_mk']
    exact ⟨-(x - y), (diffHom (AsysT p) (AsysF p)).range.neg_mem hxyrange, by abel⟩
  · intro c
    obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective (N := (incl p).range) c
    refine ⟨QuotientAddGroup.mk' _ (fun n => shiftElem p d n), ?_⟩
    rw [lim1ToQuot_mk, Theta_surj]

/-- **The computation of `lim¹`**: `lim¹ A_n ≅ (∏_j ℤ/p)/(⊕_j ℤ/p)`. -/
def lim1Equiv : lim1 (AsysT p) (AsysF p) ≃+ (prodc p ⧸ (incl p).range) :=
  AddEquiv.ofBijective (lim1ToQuot p) (lim1ToQuot_bijective p)


-- convenience: the unused-section-variable linter is irrelevant here
set_option linter.unusedSectionVars false

/-! ## §5. The data of Exercise 10.1: `A_n = α⁻¹(p^n B)` -/

/-- `B = ⊕_{j ≥ 0} ℤ/p^{j+1}ℤ`. -/
abbrev B : Type := Π₀ j : ℕ, ZMod (p^(j+1))

/-- The `j`-th component `ℤ/p → ℤ/p^{j+1}` of `α`, sending `1` to `p^j`. -/
def alphaComp (j : ℕ) : ZMod p →+ ZMod (p^(j+1)) :=
  ZMod.lift p
    ⟨zmultiplesHom _ ((p : ZMod (p^(j+1)))^j), by
      rw [zmultiplesHom_apply, zsmul_eq_mul]
      push_cast
      rw [← pow_succ', ← Nat.cast_pow, ZMod.natCast_self]⟩

lemma lift_natCast (n : ℕ) {M : Type*} [AddGroup M] (f : {f : ℤ →+ M // f (n:ℤ) = 0})
    (k : ℕ) : ZMod.lift n f ((k : ℕ) : ZMod n) = f.val (k : ℤ) := by
  rw [← Int.cast_natCast (R := ZMod n) k]
  exact ZMod.lift_coe n f (k : ℤ)

lemma alphaComp_natCast (j k : ℕ) :
    alphaComp p j ((k : ℕ) : ZMod p) = ((k * p^j : ℕ) : ZMod (p^(j+1))) := by
  unfold alphaComp
  rw [lift_natCast, zmultiplesHom_apply, zsmul_eq_mul]
  push_cast
  ring

lemma alphaComp_apply (j : ℕ) (x : ZMod p) :
    alphaComp p j x = ((x.val * p^j : ℕ) : ZMod (p^(j+1))) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact alphaComp_natCast p j x.val

/-- `α` is injective in each component. -/
lemma alphaComp_eq_zero {j : ℕ} {x : ZMod p} (h : alphaComp p j x = 0) : x = 0 := by
  rw [alphaComp_apply] at h
  have hdvd : p^(j+1) ∣ x.val * p^j := (ZMod.natCast_eq_zero_iff _ _).mp h
  have hdvd' : p^j * p ∣ p^j * x.val := by
    rw [pow_succ, mul_comm x.val (p^j)] at hdvd
    exact hdvd
  have hpj : 0 < p^j := pow_pos hp.out.pos j
  have hpdvd : p ∣ x.val := (Nat.mul_dvd_mul_iff_left hpj).mp hdvd'
  have hlt : x.val < p := ZMod.val_lt x
  have hzero : x.val = 0 := by
    rcases Nat.eq_zero_or_pos x.val with h0 | h0
    · exact h0
    · exact absurd hpdvd (Nat.not_dvd_of_pos_of_lt h0 hlt)
  exact (ZMod.val_eq_zero x).mp hzero

/-- The map `α = ⊕_j α_j : A → B` of Exercise 10.1. -/
def alpha : A p →+ B p := DFinsupp.mapRange.addMonoidHom (fun j => alphaComp p j)

lemma alpha_apply (a : A p) (j : ℕ) : alpha p a j = alphaComp p j (a j) := by
  have h : alpha p a = DFinsupp.mapRange (fun i x => alphaComp p i x)
      (fun i => (alphaComp p i).map_zero) a := rfl
  rw [h, DFinsupp.mapRange_apply]

/-- Multiplication by `p^n` on `B`. -/
def pPow (n : ℕ) : B p →+ B p where
  toFun z := p^n • z
  map_zero' := nsmul_zero (p^n)
  map_add' x y := nsmul_add x y (p^n)

lemma pPow_apply (n : ℕ) (z : B p) (j : ℕ) : pPow p n z j = p^n • z j := by
  show (p^n • z) j = p^n • z j
  exact DFinsupp.nsmul_apply _ _ _

/-- `p^n B`, the image of multiplication by `p^n` on `B`. -/
abbrev pPowSub (n : ℕ) : AddSubgroup (B p) := (pPow p n).range

lemma nsmul_pow_eq_zero {n j : ℕ} (h : j+1 ≤ n) (x : ZMod (p^(j+1))) : p^n • x = 0 := by
  have hcast : ((p^n : ℕ) : ZMod (p^(j+1))) = 0 :=
    (ZMod.natCast_eq_zero_iff (p^n) (p^(j+1))).mpr (pow_dvd_pow p h)
  rw [nsmul_eq_mul, hcast, zero_mul]

/-- On the image of `α`, a section of multiplication by `p^n` in degree `j`. -/
def betaComp (n j : ℕ) : ZMod p → ZMod (p^(j+1)) :=
  fun x => if j < n then 0 else ((x.val * p^(j-n) : ℕ) : ZMod (p^(j+1)))

lemma betaComp_zero (n j : ℕ) : betaComp (p := p) n j 0 = 0 := by
  simp only [betaComp, ZMod.val_zero, Nat.zero_mul, Nat.cast_zero]
  split_ifs <;> rfl

/-- A section of multiplication by `p^n` on the image of `α` (non-linear on purpose: only the
value on `α(a)` is relevant). -/
def beta (n : ℕ) : A p → B p :=
  DFinsupp.mapRange (fun j => betaComp (p := p) n j) (fun j => betaComp_zero p n j)

lemma beta_apply (n : ℕ) (a : A p) (j : ℕ) : beta p n a j = betaComp (p := p) n j (a j) :=
  DFinsupp.mapRange_apply _ _ a j

/-- `p^n · β_n(a) = α(a)` for `a ∈ A_n`. -/
lemma pPow_beta {n : ℕ} {a : A p} (ha : a ∈ Asub (p := p) n) :
    pPow p n (beta p n a) = alpha p a := by
  apply DFinsupp.ext
  intro j
  rw [pPow_apply, beta_apply, alpha_apply]
  by_cases hjn : j < n
  · have haz : a j = 0 := ha j hjn
    rw [haz, betaComp, if_pos hjn, alphaComp_apply]
    simp only [ZMod.val_zero, Nat.zero_mul, Nat.cast_zero, nsmul_zero]
  · rw [betaComp, if_neg hjn]
    have hnj : n ≤ j := Nat.not_lt.mp hjn
    rw [alphaComp_apply, nsmul_eq_mul, ← Nat.cast_mul]
    congr 1
    have hpow : p^n * p^(j-n) = p^j := by
      rw [← pow_add, Nat.add_sub_cancel' hnj]
    rw [← hpow]
    ring

/-- **Exercise 10.1/10.2, identification of the system.**  For the map
`α = ⊕_j α_j : A → B` of Exercise 10.1, `α⁻¹(p^n B) = A_n = ⊕_{j ≥ n} ℤ/p`. -/
theorem Asub_eq_comap (n : ℕ) : Asub (p := p) n = (pPowSub p n).comap (alpha p) := by
  ext a
  constructor
  · intro ha
    rw [AddSubgroup.mem_comap]
    exact ⟨beta p n a, pPow_beta (p := p) ha⟩
  · intro ha
    rw [AddSubgroup.mem_comap] at ha
    obtain ⟨z, hz⟩ := ha
    intro j hj
    have hcomp : alphaComp p j (a j) = 0 := by
      have h2 : alpha p a j = alphaComp p j (a j) := alpha_apply p a j
      rw [← h2, ← hz, pPow_apply]
      exact nsmul_pow_eq_zero (p := p) (by omega) _
    exact alphaComp_eq_zero (p := p) hcomp


/-! ## §6. The limit of the constant system, exactness of the defining sequences, and
non-vanishing of `lim¹` -/

/-- The limit of the constant system `A` is `A` itself. -/
def limConstEquiv : lim (constT p) (constF p) ≃+ A p where
  toFun x := x.val 0
  invFun a := ⟨fun _ => a, by rw [mem_lim]; intro n; rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    have h : ∀ m, x.val m = x.val 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        have hh := (mem_lim (constT p) (constF p) x.val).mp x.property m
        simp only [constF, AddMonoidHom.id_apply] at hh
        rw [hh, ih]
    exact (h n).symm
  right_inv a := rfl
  map_add' x y := rfl

/-- The difference map of the constant system is surjective. -/
theorem diffHom_const_range : (diffHom (constT p) (constF p)).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  intro z
  refine ⟨fun n => -(∑ i ∈ Finset.range n, z i), ?_⟩
  funext n
  simp only [diffHom_apply, constF, AddMonoidHom.id_apply, Finset.sum_range_succ]
  abel

/-- `lim¹` of the constant system vanishes. -/
theorem subsingleton_lim1_const : Subsingleton (lim1 (constT p) (constF p)) := by
  rw [lim1, QuotientAddGroup.subsingleton_iff, diffHom_const_range]

/-- For every `n` the sequence `0 → A_n → A → A ⧸ A_n → 0` is exact. -/
theorem short_exact (n : ℕ) :
    (QuotientAddGroup.mk' (Asub (p := p) n)).ker = Asub (p := p) n ∧
      Function.Surjective (QuotientAddGroup.mk' (Asub (p := p) n)) :=
  ⟨QuotientAddGroup.ker_mk' _, QuotientAddGroup.mk'_surjective (Asub (p := p) n)⟩

/-- The inclusion `⊕_j ℤ/p → ∏_j ℤ/p` is not surjective. -/
theorem not_surjective_incl : ¬ Function.Surjective (incl p) := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (fun _ => 1)
  have hcoord : ∀ j, a j = (1 : ZMod p) := by
    intro j
    have h := congrFun ha j
    simpa only [incl_apply, Pi.one_apply] using h
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range a.support
  have hmem : N ∈ a.support := by
    rw [DFinsupp.mem_support_iff, hcoord]
    exact one_ne_zero
  exact absurd (hN hmem) (by simp)

/-- `lim¹ A_n` does not vanish. -/
theorem nontrivial_lim1 : ¬ Subsingleton (lim1 (AsysT p) (AsysF p)) := by
  intro hsub
  apply not_surjective_incl p
  have hall : ∀ x y : prodc p ⧸ (incl p).range, x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := (lim1Equiv p).surjective x
    obtain ⟨b, rfl⟩ := (lim1Equiv p).surjective y
    rw [Subsingleton.elim a b]
  intro c
  have h := hall (QuotientAddGroup.mk' (incl p).range c) 0
  have h' : QuotientAddGroup.mk' (incl p).range c = QuotientAddGroup.mk' (incl p).range 0 := h
  rw [QuotientAddGroup.mk'_eq_mk'] at h'
  obtain ⟨z, hz, hcz⟩ := h'
  obtain ⟨a, ha⟩ := hz
  have hcz' : c = -z := (eq_neg_iff_add_eq_zero).mpr hcz
  refine ⟨-a, ?_⟩
  rw [map_neg, ha]
  exact hcz'.symm

/-! ## §7. The limit of the system `(A ⧸ A_n)` is the product `∏_j ℤ/p` -/

section LimQuot

/-- The `j`-th coordinate functional on `A`. -/
def coord (j : ℕ) : A p →+ ZMod p :=
  (Pi.evalAddMonoidHom (fun _ => ZMod p) j).comp (incl p)

@[simp] lemma coord_apply (a : A p) (j : ℕ) : coord p j a = a j := rfl

/-- The `j`-th coordinate functional on `A ⧸ A_{j+1}`. -/
def ev (j : ℕ) : QT p (j+1) →+ ZMod p :=
  QuotientAddGroup.lift (Asub (p := p) (j+1)) (coord p j) (by
    intro x hx
    rw [AddMonoidHom.mem_ker, coord_apply]
    exact hx j (Nat.lt_succ_self j))

/-- The projection `A ⧸ A_N → A ⧸ A_n` for `n ≤ N`. -/
def proj {n N : ℕ} (h : n ≤ N) : QT p N →+ QT p n :=
  QuotientAddGroup.lift (Asub (p := p) N) (QuotientAddGroup.mk' (Asub (p := p) n)) (by
    intro x hx
    simpa using Asub_antitone (p := p) h hx)

@[simp] lemma ev_coe (j : ℕ) (a : A p) : ev p j (a : QT p (j+1)) = a j :=
  QuotientAddGroup.lift_mk' _ _ a

@[simp] lemma proj_coe {n N : ℕ} (h : n ≤ N) (a : A p) :
    proj (p := p) h (a : QT p N) = (a : QT p n) :=
  QuotientAddGroup.lift_mk' _ _ a

@[simp] lemma proj_mk' {n N : ℕ} (h : n ≤ N) (a : A p) :
    proj (p := p) h (QuotientAddGroup.mk' (Asub (p := p) N) a)
      = QuotientAddGroup.mk' (Asub (p := p) n) a :=
  QuotientAddGroup.lift_mk' _ _ a

lemma coe_eq_of_sub_mem {n : ℕ} {a b : A p} (h : a - b ∈ Asub (p := p) n) :
    (a : QT p n) = (b : QT p n) :=
  mk'_eq_of_sub_mem (p := p) h

lemma proj_self (n : ℕ) : proj (p := p) (le_refl n) = AddMonoidHom.id (QT p n) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ a => rw [proj_coe, AddMonoidHom.id_apply]

lemma proj_proj {m n N : ℕ} (h1 : m ≤ n) (h2 : n ≤ N) :
    (proj (p := p) h1).comp (proj (p := p) h2) = proj (p := p) (le_trans h1 h2) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ a => simp only [AddMonoidHom.comp_apply, proj_coe]

lemma QF_coe (n : ℕ) (a : A p) : QF p n (a : QT p (n+1)) = (a : QT p n) :=
  QuotientAddGroup.lift_mk' _ _ a

/-- One step of compatibility, expressed with the projections. -/
lemma lim_proj_succ (y : lim (QT p) (QF p)) (k : ℕ) :
    y.val k = proj (p := p) (Nat.le_succ k) (y.val (k+1)) := by
  have hstep : y.val k = QF p k (y.val (k+1)) :=
    ((mem_lim (QT p) (QF p) y.val).mp y.property k).symm
  rw [hstep]
  induction (y.val (k+1)) using QuotientAddGroup.induction_on with
  | _ a => rw [QF_coe, proj_coe]

/-- In a compatible family, every term is the projection of any later term. -/
lemma lim_proj_eq (y : lim (QT p) (QF p)) {n N : ℕ} (h : n ≤ N) :
    y.val n = proj (p := p) h (y.val N) := by
  induction N, h using Nat.le_induction with
  | base => rw [proj_self]; rfl
  | succ k hk ih =>
    rw [ih, lim_proj_succ (p := p) y k]
    exact DFunLike.congr_fun (proj_proj (p := p) hk (Nat.le_succ k)) (y.val (k+1))

/-- The terms of a compatible family of the constant system are all equal. -/
lemma const_val_eq (z : lim (constT p) (constF p)) (m : ℕ) : z.val m = z.val 0 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hh := (mem_lim (constT p) (constF p) z.val).mp z.property k
    simp only [constF, AddMonoidHom.id_apply] at hh
    rw [hh, ih]

/-- The truncation `∑_{j<n} c_j` of a family `c`. -/
def truncEl (c : prodc p) (n : ℕ) : A p :=
  ∑ j ∈ Finset.range n, DFinsupp.single j (c j)

lemma truncEl_succ (c : prodc p) (n : ℕ) :
    truncEl p c (n+1) = truncEl p c n + DFinsupp.single n (c n) := by
  simp only [truncEl, Finset.sum_range_succ]

lemma truncEl_apply_lt {c : prodc p} {n j : ℕ} (hj : j < n) : truncEl p c n j = c j := by
  simp only [truncEl, DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · exact DFinsupp.single_eq_same
  · intro b _ hb
    exact DFinsupp.single_eq_of_ne (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

lemma truncEl_diff (c : prodc p) (n : ℕ) :
    truncEl p c (n+1) - truncEl p c n ∈ Asub (p := p) n := by
  rw [truncEl_succ, add_sub_cancel_left]
  intro j hj
  exact DFinsupp.single_eq_of_ne (ne_of_lt hj)

/-- The family of classes of the truncations of `c`, an element of `lim (A ⧸ A_n)`. -/
def PsiQuot : prodc p →+ lim (QT p) (QF p) where
  toFun c :=
    ⟨fun n => (truncEl p c n : QT p n), by
      rw [mem_lim]
      intro n
      rw [QF_coe]
      exact coe_eq_of_sub_mem (p := p) (truncEl_diff p c n)⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    have h0 : truncEl p 0 n = (0 : A p) := by
      simp only [truncEl, Pi.zero_apply, DFinsupp.single_zero, Finset.sum_const_zero]
    show ((truncEl p 0 n : A p) : QT p n) = ((0 : A p) : QT p n)
    rw [h0]
  map_add' := by
    intro x y
    apply Subtype.ext
    funext n
    have he : truncEl p (x + y) n = truncEl p x n + truncEl p y n := by
      simp only [truncEl, Pi.add_apply, DFinsupp.single_add, Finset.sum_add_distrib]
    show ((truncEl p (x + y) n : A p) : QT p n)
      = ((truncEl p x n : A p) : QT p n) + ((truncEl p y n : A p) : QT p n)
    rw [he]
    exact map_add (QuotientAddGroup.mk' (Asub (p := p) n)) _ _

/-- Extraction of the coordinates from a compatible family of classes. -/
def PhiQuot : lim (QT p) (QF p) →+ prodc p where
  toFun y := fun j => ev p j (y.val (j+1))
  map_zero' := by
    funext j
    simp
  map_add' := by
    intro x y
    funext j
    simp

lemma PhiQuot_PsiQuot (c : prodc p) : PhiQuot p (PsiQuot p c) = c := by
  funext j
  show ev p j ((truncEl p c (j+1) : QT p (j+1))) = c j
  rw [ev_coe]
  exact truncEl_apply_lt (p := p) (Nat.lt_succ_self j)

lemma PsiQuot_PhiQuot (y : lim (QT p) (QF p)) : PsiQuot p (PhiQuot p y) = y := by
  apply Subtype.ext
  funext n
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (Asub (p := p) n) (y.val n)
  show (truncEl p (PhiQuot p y) n : QT p n) = y.val n
  rw [← ha]
  apply coe_eq_of_sub_mem
  intro j hj
  have hcoord : (truncEl p (PhiQuot p y) n) j = ev p j (y.val (j+1)) := by
    rw [truncEl_apply_lt (p := p) hj]
    rfl
  have hproj : y.val (j+1) = proj (p := p) (show j+1 ≤ n from hj) (y.val n) :=
    lim_proj_eq (p := p) y (show j+1 ≤ n from hj)
  have h2 : y.val (j+1) = (a : QT p (j+1)) := by
    rw [hproj, ← ha]
    simpa only [QuotientAddGroup.mk'_apply] using
      (proj_mk' (p := p) (show j+1 ≤ n from hj) a)
  rw [DFinsupp.sub_apply, hcoord, h2, ev_coe, sub_self]

/-- **The limit of `(A ⧸ A_n)` is the product**: `lim (A ⧸ A_n) ≅ ∏_j ℤ/p`. -/
def limQuotEquiv : lim (QT p) (QF p) ≃+ prodc p where
  toFun := PhiQuot p
  invFun := PsiQuot p
  left_inv := PsiQuot_PhiQuot p
  right_inv := PhiQuot_PsiQuot p
  map_add' := fun x y => map_add (PhiQuot p) x y

/-- Under the identifications `lim A ≅ A` and `lim (A ⧸ A_n) ≅ ∏_j ℤ/p`, the map induced by
the surjections `A → A ⧸ A_n` is the inclusion of the direct sum into the product. -/
theorem limMap_QF_eq_incl (x : lim (constT p) (constF p)) :
    PhiQuot p (limMap (G := constT p) (G' := QT p) (constF p) (QF p) (toQF p) (toQF_compat p) x)
      = incl p (limConstEquiv p x) := by
  funext j
  have h1 : x.val (j+1) = x.val 0 := const_val_eq (p := p) x (j+1)
  show ev p j ((toQF p (j+1)) (x.val (j+1))) = (incl p (limConstEquiv p x)) j
  rw [toQF, QuotientAddGroup.mk'_apply, ev_coe, incl_apply]
  exact congrArg (fun z => z j) h1

end LimQuot


end Data

/-! ## §8. Summary of what has been proved -/

section Summary

variable (p : ℕ) [hp : Fact p.Prime]

instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Atiyah–Macdonald, Exercise 10.2 (Chapter 10, Completions).**  With `A = ⊕_{j} ℤ/p`,
`B = ⊕_j ℤ/p^{j+1}`, `α = ⊕_j α_j` (Exercise 10.1) and `A_n = α⁻¹(p^n B) = ⊕_{j ≥ n} ℤ/p`:

1. `A_n = α⁻¹(p^n B)` (`Asub_eq_comap`);
2. `0 → A_n → A → A/A_n → 0` is exact for every `n` (`short_exact`);
3. `lim¹` of the constant system vanishes (`subsingleton_lim1_const`) and `lim` of the constant
   system is `A` (`limConstEquiv`);
4. `lim A_n = 0` (`subsingleton_ALim`);
5. `lim` is **not** right exact: the map `lim A → lim (A ⧸ A_n)` induced by the surjections
   `A → A ⧸ A_n` is not surjective (`not_surjective_limMap_QF`);
6. `lim¹ A_n ≅ (∏_j ℤ/p)/(⊕_j ℤ/p)` (`lim1Equiv`) and in particular `lim¹ A_n ≠ 0`
   (`nontrivial_lim1`). -/
theorem atiyah_macdonald_10_2 :
    (∀ n : ℕ, Asub (p := p) n = (pPowSub p n).comap (alpha p)) ∧
    (∀ n : ℕ, (QuotientAddGroup.mk' (Asub (p := p) n)).ker = Asub (p := p) n) ∧
    Subsingleton (lim1 (constT p) (constF p)) ∧
    Subsingleton (ALim p) ∧
    (¬ Function.Surjective
        (limMap (G := constT p) (G' := QT p) (constF p) (QF p) (toQF p) (toQF_compat p))) ∧
    Nonempty (lim1 (AsysT p) (AsysF p) ≃+ (prodc p ⧸ (incl p).range)) ∧
    ¬ Subsingleton (lim1 (AsysT p) (AsysF p)) :=
  ⟨Asub_eq_comap p, fun n => (short_exact p n).1, subsingleton_lim1_const p,
    subsingleton_ALim p,
    not_surjective_limMap_QF p, ⟨lim1Equiv p⟩, nontrivial_lim1 p⟩


/-- **The book's exact sequence, explicitly.**  The limit of the quotient system is the product
`∏_j ℤ/p`, and the map on limits induced by the surjections `A → A ⧸ A_n` is the inclusion
`⊕_j ℤ/p → ∏_j ℤ/p` of the direct sum into the product. -/
theorem atiyah_macdonald_10_2_limit_quotients :
    Nonempty (lim (QT p) (QF p) ≃+ prodc p) ∧
      (∀ x : lim (constT p) (constF p),
        PhiQuot p (limMap (G := constT p) (G' := QT p) (constF p) (QF p) (toQF p)
          (toQF_compat p) x) = incl p (limConstEquiv p x)) :=
  ⟨⟨limQuotEquiv p⟩, limMap_QF_eq_incl p⟩

end Summary

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_10_2.Asub_eq_comap
#print axioms AtiyahMcdonald69.Ex_10_2.short_exact
#print axioms AtiyahMcdonald69.Ex_10_2.subsingleton_ALim
#print axioms AtiyahMcdonald69.Ex_10_2.limConstEquiv
#print axioms AtiyahMcdonald69.Ex_10_2.subsingleton_lim1_const
#print axioms AtiyahMcdonald69.Ex_10_2.not_surjective_limMap_QF
#print axioms AtiyahMcdonald69.Ex_10_2.lim1Equiv
#print axioms AtiyahMcdonald69.Ex_10_2.nontrivial_lim1
#print axioms AtiyahMcdonald69.Ex_10_2.limQuotEquiv
#print axioms AtiyahMcdonald69.Ex_10_2.limMap_QF_eq_incl
#print axioms AtiyahMcdonald69.Ex_10_2.atiyah_macdonald_10_2
#print axioms AtiyahMcdonald69.Ex_10_2.atiyah_macdonald_10_2_limit_quotients


end

end AtiyahMcdonald69.Ex_10_2
