import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Atiyah–Macdonald (1969), Exercise 10.1

Let `p` be a prime, `A = ⨁_{j ≥ 0} ℤ/p` and `B = ⨁_{j ≥ 0} ℤ/p^(j+1)`, and let
`α : A → B` be the direct sum of the injections `α_j : ℤ/p → ℤ/p^(j+1)`, `1 ↦ p^j`.

The exercise asks to show:

* the `p`-adic completion of `A` is `A` itself;
* the completion of `A` for the topology induced from the `p`-adic topology of `B`
  is the direct *product* `∏_{j} ℤ/p`;
* `p`-adic completion is not a right exact functor on the category of all `ℤ`-modules.
-/

namespace AtiyahMcdonald69.Ex_10_1

/-! ## `p`-adic completions of abelian groups -/

section General

variable (p : ℕ)
variable {M : Type*} [AddCommGroup M]
variable {N : Type*} [AddCommGroup N]

/-- The subgroup `p^n M` of `M`. -/
def pPow (n : ℕ) : AddSubgroup M where
  carrier := {x | ∃ y, (p ^ n) • y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x z ⟨y, rfl⟩ ⟨w, rfl⟩
    exact ⟨y + w, by rw [smul_add]⟩
  neg_mem' := by
    rintro x ⟨y, rfl⟩
    exact ⟨-y, by rw [smul_neg]⟩

lemma mem_pPow {n : ℕ} {x : M} : x ∈ pPow p n ↔ ∃ y, (p ^ n) • y = x := Iff.rfl

lemma pPow_succ_le (n : ℕ) :
    pPow (M := M) p (n + 1) ≤ pPow (M := M) p n := by
  rintro x ⟨y, rfl⟩
  exact ⟨(p : ℕ) • y, by rw [smul_smul, pow_succ]⟩

end General

section InvLim

variable {M : Type*} [AddCommGroup M]
variable {𝒩 : ℕ → AddSubgroup M}

/-- The canonical transition map `M/N (n+1) →+ M/N n` of an inverse system of submodules. -/
def transMap (hmono : ∀ n, 𝒩 (n + 1) ≤ 𝒩 n) (n : ℕ) : M ⧸ 𝒩 (n + 1) →+ M ⧸ 𝒩 n :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id M)
    (fun _ hx => AddSubgroup.mem_comap.mpr (hmono n hx))

lemma transMap_mk (hmono : ∀ n, 𝒩 (n + 1) ≤ 𝒩 n) (n : ℕ) (x : M) :
    transMap hmono n (QuotientAddGroup.mk x : M ⧸ 𝒩 (n + 1))
      = (QuotientAddGroup.mk x : M ⧸ 𝒩 n) := by
  rw [transMap, QuotientAddGroup.map_mk]
  rfl

/-- The inverse limit `lim_n M/N n` as a subgroup of the product. -/
def invLimSub (hmono : ∀ n, 𝒩 (n + 1) ≤ 𝒩 n) : AddSubgroup (∀ n, M ⧸ 𝒩 n) where
  carrier := {x | ∀ n, transMap hmono n (x (n + 1)) = x n}
  zero_mem' := fun n => by simp [transMap]
  add_mem' := fun {x y} hx hy n => by
    show transMap hmono n ((x + y) (n + 1)) = (x + y) n
    rw [Pi.add_apply, Pi.add_apply, map_add, hx n, hy n]
  neg_mem' := fun {x} hx n => by
    show transMap hmono n ((-x) (n + 1)) = (-x) n
    rw [Pi.neg_apply, Pi.neg_apply, map_neg, hx n]

end InvLim

section General2

variable (p : ℕ)
variable {M : Type*} [AddCommGroup M]
variable {N : Type*} [AddCommGroup N]

/-- The transition map of the `p`-adic filtration. -/
def pTrans (n : ℕ) : M ⧸ pPow p (n + 1) →+ M ⧸ pPow p n :=
  transMap (𝒩 := fun k => pPow (M := M) p k) (fun n => pPow_succ_le p n) n

lemma pTrans_def (n : ℕ) :
    pTrans (M := M) p n = transMap (𝒩 := fun n => pPow (M := M) p n)
      (fun n => pPow_succ_le p n) n := rfl

lemma pTrans_mk (n : ℕ) (x : M) :
    pTrans p n (QuotientAddGroup.mk x : M ⧸ pPow p (n + 1))
      = (QuotientAddGroup.mk x : M ⧸ pPow p n) :=
  transMap_mk (𝒩 := fun n => pPow (M := M) p n) (fun n => pPow_succ_le p n) n x

/-- The `p`-adic completion `lim_n M/p^nM`, as a subgroup of the product. -/
def pComplSub : AddSubgroup (∀ n, M ⧸ pPow p n) :=
  invLimSub (𝒩 := fun n => pPow (M := M) p n) (fun n => pPow_succ_le p n)

/-- The `p`-adic completion of `M` as an abelian group. -/
abbrev PCompl (M : Type*) [AddCommGroup M] : Type _ := ↥(pComplSub (p := p) (M := M))

lemma pTrans_injective_of_bot (n : ℕ) (h : pPow (M := M) p n = ⊥) :
    Function.Injective (pTrans (M := M) p n) := by
  rw [pTrans_def, ← AddMonoidHom.ker_eq_bot_iff]
  show (transMap (𝒩 := fun k => pPow (M := M) p k) (fun n => pPow_succ_le p n) n).ker = ⊥
  rw [transMap, QuotientAddGroup.ker_map]
  rw [h]
  simp

/-- The canonical map `M → lim_n M/p^nM`. -/
def pComplOf : M →+ PCompl p M where
  toFun x := ⟨fun n => (QuotientAddGroup.mk x : M ⧸ pPow p n), fun n => pTrans_mk p n x⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero (QuotientAddGroup.mk' (pPow p n))
  map_add' := by
    intro x y
    apply Subtype.ext
    funext n
    exact map_add (QuotientAddGroup.mk' (pPow p n)) x y

@[simp] lemma pComplOf_apply (x : M) (n : ℕ) :
    ((pComplOf p x : PCompl p M) : ∀ n, M ⧸ pPow p n) n
      = (QuotientAddGroup.mk x : M ⧸ pPow p n) := rfl

/-- The map induced on `n`-th quotients by `f : M →+ N`. -/
def pMapHom (f : M →+ N) (n : ℕ) : M ⧸ pPow p n →+ N ⧸ pPow p n :=
  QuotientAddGroup.map (pPow (M := M) p n) (pPow (M := N) p n) f (fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨f y, by rw [map_nsmul]⟩)

@[simp] lemma pMapHom_mk (f : M →+ N) (n : ℕ) (x : M) :
    pMapHom p f n (QuotientAddGroup.mk x : M ⧸ pPow p n)
      = (QuotientAddGroup.mk (f x) : N ⧸ pPow p n) := by
  rw [pMapHom, QuotientAddGroup.map_mk]

lemma pTrans_comm (f : M →+ N) (n : ℕ) (z : M ⧸ pPow p (n + 1)) :
    pTrans p n (pMapHom p f (n + 1) z) = pMapHom p f n (pTrans p n z) := by
  refine QuotientAddGroup.induction_on z ?_
  intro a
  rw [pMapHom_mk, pTrans_mk, pTrans_mk, pMapHom_mk]

lemma pMapHom_comp (f : M →+ N) {Q : Type*} [AddCommGroup Q] (g : N →+ Q) (n : ℕ) :
    (pMapHom p g n).comp (pMapHom p f n) = pMapHom p (g.comp f) n := by
  apply AddMonoidHom.ext
  intro z
  refine QuotientAddGroup.induction_on z ?_
  intro a
  rw [AddMonoidHom.comp_apply, pMapHom_mk, pMapHom_mk, pMapHom_mk]
  rfl

/-- Functoriality of the `p`-adic completion. -/
def pComplMap (f : M →+ N) : PCompl p M →+ PCompl p N where
  toFun x := ⟨fun n => pMapHom p f n (x.1 n), by
    intro n
    exact (pTrans_comm p f n (x.1 (n + 1))).trans (congrArg _ (x.2 n))⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero _
  map_add' := by
    intro x y
    apply Subtype.ext
    funext n
    exact map_add _ (x.1 n) (y.1 n)

@[simp] lemma pComplMap_apply (f : M →+ N) (x : PCompl p M) (n : ℕ) :
    ((pComplMap p f x : PCompl p N) : ∀ n, N ⧸ pPow p n) n
      = pMapHom p f n (x.1 n) := rfl

lemma pComplMap_comp (f : M →+ N) {Q : Type*} [AddCommGroup Q] (g : N →+ Q) :
    (pComplMap p g).comp (pComplMap p f) = pComplMap p (g.comp f) := by
  ext x n
  exact DFunLike.congr_fun (pMapHom_comp p f g n) (x.1 n)

lemma pComplSub_property (x : PCompl p M) (n : ℕ) : pTrans p n (x.1 (n + 1)) = x.1 n := x.2 n

lemma pComplMap_of (f : M →+ N) (x : M) :
    pComplMap p f (pComplOf p x) = pComplOf p (f x) := by
  apply Subtype.ext
  funext n
  rw [pComplMap_apply, pComplOf_apply, pMapHom_mk, pComplOf_apply]

end General2

/-! ## The groups `A` and `B` -/

section Concrete

variable (p : ℕ) [Fact p.Prime]

lemma hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le

lemma hp_pos_int : (0 : ℤ) < (p : ℤ) := by
  have h : 0 < p := by linarith [hp_two p]
  exact_mod_cast h

/-- `C j = ℤ/p^(j+1)`. -/
abbrev C (j : ℕ) : Type := ZMod (p ^ (j + 1))

/-- `B = ⨁_{j} ℤ/p^(j+1)`, the countable direct sum. -/
abbrev B : Type := Π₀ j : ℕ, C p j

/-- `A = ⨁_{j} ℤ/p`, the countable direct sum. -/
abbrev A : Type := Π₀ _ : ℕ, ZMod p

/-- Multiplication by `p^j` on `ℤ/p^(j+1)`. -/
def mulPow (j : ℕ) : C p j →+ C p j where
  toFun y := ((p ^ j : ℕ) : C p j) * y
  map_zero' := by simp
  map_add' := by intro a b; rw [mul_add]

/-- The injection `ℤ/p → ℤ/p^(j+1)`, `x ↦ p^j x`. -/
def alphaStep (j : ℕ) : ZMod p →+ C p j :=
  ZMod.lift p ⟨(mulPow p j).comp (Int.castAddHom (C p j)), by
    show ((p ^ j : ℕ) : C p j) * ((p : ℤ) : C p j) = 0
    push_cast
    rw [← pow_succ, ← Nat.cast_pow, ZMod.natCast_self]⟩

lemma alphaStep_intCast (j : ℕ) (z : ℤ) :
    alphaStep p j ((z : ℤ) : ZMod p) = ((p ^ j : ℕ) : C p j) * ((z : ℤ) : C p j) := by
  rw [alphaStep, ZMod.lift_coe]
  rfl

lemma alphaStep_one (j : ℕ) : alphaStep p j 1 = ((p ^ j : ℕ) : C p j) := by
  have h := alphaStep_intCast p j 1
  simpa using h

/-- `α : A → B`, the direct sum of the injections `alphaStep j`. -/
def alpha : A p →+ B p := DFinsupp.mapRange.addMonoidHom (fun j => alphaStep p j)

@[simp] lemma alpha_apply (a : A p) (j : ℕ) : alpha p a j = alphaStep p j (a j) := by
  simp [alpha]

lemma alphaStep_injective (j : ℕ) : Function.Injective (alphaStep p j) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  rw [alphaStep_intCast, alphaStep_intCast] at hxy
  have hsub : ((((p ^ j : ℕ) : ℤ) * (a - b) : ℤ) : C p j) = 0 := by
    rw [Int.cast_mul, Int.cast_sub, Int.cast_natCast, mul_sub, hxy, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsub
  have h1 : ((p ^ (j + 1) : ℕ) : ℤ) = ((p ^ j : ℕ) : ℤ) * (p : ℤ) := by
    push_cast
    rw [pow_succ']
    ring
  rw [h1] at hsub
  have hpj : ((p ^ j : ℕ) : ℤ) ≠ 0 := by
    have h0 : (0 : ℕ) < p := by linarith [hp_two p]
    have hpos : (0 : ℕ) < p ^ j := pow_pos h0 j
    have hpos' : (0 : ℤ) < ((p ^ j : ℕ) : ℤ) := by exact_mod_cast hpos
    linarith
  have hdvd : (p : ℤ) ∣ (a - b) := (mul_dvd_mul_iff_left hpj).1 hsub
  rw [ZMod.intCast_eq_intCast_iff]
  refine Int.modEq_iff_dvd.mpr ?_
  rw [← neg_sub]
  exact dvd_neg.mpr hdvd

lemma alpha_injective : Function.Injective (alpha p) := by
  intro a b hab
  ext j
  exact alphaStep_injective p j (by
    have h := congrArg (fun x : B p => x j) hab
    simpa using h)


/-! ### The `p`-adic completion of `A` is `A` -/

lemma nsmul_p_eq_zero_A (a : A p) : (p : ℕ) • a = 0 := by
  refine DFinsupp.ext fun j => ?_
  rw [DFinsupp.nsmul_apply, DFinsupp.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

lemma pPow_A_eq_top : pPow (M := A p) p 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact ⟨x, by rw [pow_zero, one_smul]⟩

lemma pPow_A_eq_bot {n : ℕ} (hn : 1 ≤ n) : pPow (M := A p) p n = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, ← smul_smul, nsmul_p_eq_zero_A, smul_zero]
  exact zero_mem _

lemma quot_top_subsingleton : Subsingleton (A p ⧸ pPow (M := A p) p 0) := by
  rw [pPow_A_eq_top]
  exact ⟨fun u v => by
    refine QuotientAddGroup.induction_on u ?_
    intro s
    refine QuotientAddGroup.induction_on v ?_
    intro t
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact AddSubgroup.mem_top _⟩

/-- The `p`-adic completion of `A` is `A`: the canonical map is bijective. -/
theorem pCompl_A_bijective : Function.Bijective (pComplOf (p := p) (M := A p)) := by
  constructor
  · intro a b hab
    have h := congrArg (fun z : PCompl p (A p) => z.1 1) hab
    simp only [pComplOf_apply] at h
    rw [pPow_A_eq_bot p (n := 1) (le_refl 1)] at h
    rw [QuotientAddGroup.eq_iff_sub_mem] at h
    exact sub_eq_zero.mp h
  · intro x
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (pPow (M := A p) p 1) (x.1 1)
    refine ⟨a, ?_⟩
    apply Subtype.ext
    funext n
    induction n with
    | zero =>
        exact @Subsingleton.elim (A p ⧸ pPow (M := A p) p 0) (quot_top_subsingleton p) _ _
    | succ k ih =>
        cases k with
        | zero =>
            show ((pComplOf p) a).1 1 = x.1 1
            exact ha
        | succ j =>
            have hbot : pPow (M := A p) p (j + 1) = ⊥ := pPow_A_eq_bot p (by omega)
            refine pTrans_injective_of_bot p (j + 1) hbot ?_
            rw [pComplSub_property p x (j + 1), pComplSub_property p (pComplOf p a) (j + 1)]
            exact ih


/-- The `p`-adic completion of `A` is `A` (as an additive equivalence). -/
noncomputable def pComplAEquiv : PCompl p (A p) ≃+ A p :=
  (AddEquiv.ofBijective (pComplOf (p := p) (M := A p)) (pCompl_A_bijective p)).symm

/-! ### The element `ξ ∈ lim_n B/p^n B` -/

/-- In `ℤ/p^(j+1)`, the class of `p^n` vanishes as soon as `j < n`. -/
lemma natCast_pow_eq_zero_of_lt {n j : ℕ} (h : j < n) :
    ((p ^ n : ℕ) : C p j) = 0 :=
  (CharP.cast_eq_zero_iff (C p j) (p ^ (j + 1)) (p ^ n)).mpr (pow_dvd_pow p (by omega))

/-- Elements of `p^n B` have vanishing coordinates in degrees `< n`. -/
lemma mem_pPow_B_apply_eq_zero {n : ℕ} {b : B p} (hb : b ∈ pPow (M := B p) p n) {j : ℕ}
    (hj : j < n) : b j = 0 := by
  obtain ⟨c, rfl⟩ := hb
  rw [DFinsupp.nsmul_apply, nsmul_eq_mul, natCast_pow_eq_zero_of_lt p hj, zero_mul]

/-- `∑_{j<n} p^j e_j ∈ B`. -/
def xiRep (n : ℕ) : B p := ∑ j ∈ Finset.range n, DFinsupp.single j ((p ^ j : ℕ) : C p j)

lemma xiRep_apply_of_lt {n j : ℕ} (hj : j < n) : xiRep p n j = ((p ^ j : ℕ) : C p j) := by
  rw [xiRep, DFinsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [DFinsupp.single_eq_same]
  · intro b _ hbj
    exact DFinsupp.single_eq_of_ne hbj.symm
  · intro hnot
    exact absurd (Finset.mem_range.mpr hj) hnot

lemma xiRep_apply_of_le {n j : ℕ} (hj : n ≤ j) : xiRep p n j = 0 := by
  rw [xiRep, DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero ?_
  intro b hb
  exact DFinsupp.single_eq_of_ne (by have := Finset.mem_range.mp hb; omega)

lemma xiRep_succ (n : ℕ) :
    xiRep p (n + 1) = xiRep p n + DFinsupp.single n ((p ^ n : ℕ) : C p n) := by
  simp only [xiRep, Finset.sum_range_succ]

lemma nsmul_single_B (n : ℕ) :
    (p ^ n : ℕ) • (DFinsupp.single n (1 : C p n))
      = DFinsupp.single n ((p ^ n : ℕ) : C p n) := by
  refine DFinsupp.ext fun j => ?_
  rcases eq_or_ne j n with rfl | hj
  · rw [DFinsupp.nsmul_apply, DFinsupp.single_eq_same, DFinsupp.single_eq_same, nsmul_eq_mul,
      mul_one]
  · rw [DFinsupp.nsmul_apply, DFinsupp.single_eq_of_ne hj, DFinsupp.single_eq_of_ne hj,
      smul_zero]

lemma xiRep_diff_mem (n : ℕ) :
    xiRep p (n + 1) - xiRep p n ∈ pPow (M := B p) p n := by
  rw [xiRep_succ, add_sub_cancel_left]
  exact ⟨DFinsupp.single n (1 : C p n), nsmul_single_B p n⟩

/-- The element `ξ = (∑_{j<n} p^j e_j)_n` of the `p`-adic completion of `B`. -/
def xi : PCompl p (B p) :=
  ⟨fun n => (QuotientAddGroup.mk (xiRep p n) : B p ⧸ pPow p n), by
    intro n
    rw [← pTrans_def, pTrans_mk, QuotientAddGroup.eq_iff_sub_mem]
    exact xiRep_diff_mem p n⟩

/-! ### `α : A → B` is the direct sum of the inclusions -/

lemma alpha_single_one (j : ℕ) :
    alpha p (DFinsupp.single j (1 : ZMod p))
      = DFinsupp.single j ((p ^ j : ℕ) : C p j) := by
  refine DFinsupp.ext fun i => ?_
  rw [alpha_apply]
  rcases eq_or_ne i j with rfl | hi
  · rw [DFinsupp.single_eq_same, DFinsupp.single_eq_same, alphaStep_one]
  · rw [DFinsupp.single_eq_of_ne hi, DFinsupp.single_eq_of_ne hi]
    exact map_zero _

/-- `a_n = ∑_{j<n} e_j ∈ A`. -/
def aRep (n : ℕ) : A p := ∑ j ∈ Finset.range n, DFinsupp.single j (1 : ZMod p)

lemma alpha_aRep (n : ℕ) : alpha p (aRep p n) = xiRep p n := by
  rw [aRep, xiRep, map_sum]
  exact Finset.sum_congr rfl fun j _ => alpha_single_one p j

/-- The quotient map `B → B/αA`. -/
def quotAlphaHom : B p →+ B p ⧸ AddMonoidHom.range (alpha p) :=
  QuotientAddGroup.mk' (AddMonoidHom.range (alpha p))

lemma quotAlphaHom_xiRep (n : ℕ) : quotAlphaHom p (xiRep p n) = 0 := by
  rw [quotAlphaHom, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
  exact ⟨aRep p n, alpha_aRep p n⟩

/-- The quotient `B/αA`. -/
abbrev Bq : Type _ := B p ⧸ AddMonoidHom.range (alpha p)

/-- The completed quotient map `B̂ → (B/αA)^`. -/
def quotCompl : PCompl p (B p) →+ PCompl p (Bq p) :=
  pComplMap p (M := B p) (N := Bq p) (quotAlphaHom p)

/-- The completed inclusion `Â → B̂`. -/
def alphaCompl : PCompl p (A p) →+ PCompl p (B p) :=
  pComplMap p (M := A p) (N := B p) (alpha p)

lemma pComplMap_quot_xi : quotCompl p (xi p) = 0 := by
  apply Subtype.ext
  funext n
  show pMapHom p (M := B p) (N := Bq p) (quotAlphaHom p) n
      (QuotientAddGroup.mk (xiRep p n)) = 0
  rw [pMapHom_mk, quotAlphaHom_xiRep]
  rfl

/-- `ξ` is not in the image of the completed map `Â → B̂` (whose image is the direct sum). -/
lemma of_alpha_ne_xi (a : A p) : pComplOf p (alpha p a) ≠ xi p := by
  intro h
  have hcoord : ∀ j, a j = 1 := by
    intro j
    have h1 : (QuotientAddGroup.mk (alpha p a) : B p ⧸ pPow p (j + 1))
        = QuotientAddGroup.mk (xiRep p (j + 1)) := by
      have hh := congrArg (fun z : PCompl p (B p) => z.1 (j + 1)) h
      simpa only [pComplOf_apply, xi] using hh
    rw [QuotientAddGroup.eq_iff_sub_mem] at h1
    have h2 := mem_pPow_B_apply_eq_zero p h1 (j := j) (by omega : j < j + 1)
    rw [DFinsupp.sub_apply, xiRep_apply_of_lt p (n := j + 1) (by omega : j < j + 1)] at h2
    have h3 : (alpha p a) j = ((p ^ j : ℕ) : C p j) := sub_eq_zero.mp h2
    rw [alpha_apply, ← alphaStep_one] at h3
    exact alphaStep_injective p j h3
  set N := a.support.sup id + 1 with hNdef
  have hNmem : N ∉ a.support := by
    intro hc
    have hle : N ≤ a.support.sup id := Finset.le_sup (f := id) hc
    omega
  have hzero : a N = 0 := by
    by_contra hne
    exact hNmem (DFinsupp.mem_support_iff.mpr hne)
  have hone : a N = 1 := hcoord N
  rw [hone] at hzero
  have hp1 : (1 : ZMod p) ≠ 0 := by
    intro hc
    rw [← Nat.cast_one] at hc
    have hdvd : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp hc
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h2 := hp_two p
    omega
  exact hp1 hzero


lemma one_ne_zero_zmod : (1 : ZMod p) ≠ 0 := by
  intro hc
  rw [← Nat.cast_one] at hc
  have hdvd : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp hc
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hp_two p
  omega

/-! ### The completion of `A` for the topology induced from the `p`-adic topology of `B` -/

/-- The filtration of `A` induced by the `p`-adic filtration of `B` along `α`. -/
def Nind (n : ℕ) : AddSubgroup (A p) := AddSubgroup.comap (alpha p) (pPow (M := B p) p n)

lemma Nind_antitone (n : ℕ) : Nind p (n + 1) ≤ Nind p n :=
  AddSubgroup.comap_mono (pPow_succ_le p n)

/-- The completion of `A` for the topology induced from `B`. -/
abbrev PComplInd : Type _ := ↥(invLimSub (𝒩 := fun n => Nind p n) (Nind_antitone p))

lemma Nind_apply_eq_zero {n : ℕ} {a : A p} (ha : a ∈ Nind p n) {j : ℕ} (hj : j < n) :
    a j = 0 := by
  have hb : alpha p a ∈ pPow (M := B p) p n := ha
  have h0 : (alpha p a) j = 0 := mem_pPow_B_apply_eq_zero p hb hj
  rw [alpha_apply] at h0
  refine alphaStep_injective p j ?_
  rw [h0, map_zero]

/-- The value of `α` in the `j`-th coordinate, in terms of the canonical representative. -/
lemma alphaStep_val (j : ℕ) (x : ZMod p) :
    alphaStep p j x = ((p ^ j : ℕ) : C p j) * ((x.val : ℕ) : C p j) := by
  haveI : NeZero p := ⟨by have := hp_two p; omega⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  have h := alphaStep_intCast p j ((x.val : ℤ))
  simpa using h

/-- The coordinate-wise division by `p^n` of an element of `A` seen in `B`. -/
def cOf (n : ℕ) (a : A p) : B p :=
  DFinsupp.mapRange
    (fun j x => if n ≤ j then ((p ^ (j - n) : ℕ) : C p j) * ((x.val : ℕ) : C p j) else 0)
    (fun _ => by split_ifs <;> simp) a

lemma cOf_apply (n : ℕ) (a : A p) (j : ℕ) :
    cOf p n a j
      = if n ≤ j then ((p ^ (j - n) : ℕ) : C p j) * (((a j).val : ℕ) : C p j) else 0 := by
  rw [cOf, DFinsupp.mapRange_apply]

lemma Nind_mem_of_coord {n : ℕ} {a : A p} (ha : ∀ j < n, a j = 0) : a ∈ Nind p n := by
  refine ⟨cOf p n a, ?_⟩
  refine DFinsupp.ext fun j => ?_
  rw [DFinsupp.nsmul_apply, alpha_apply, cOf_apply]
  by_cases hj : j < n
  · rw [if_neg (by omega), smul_zero, ha j hj, map_zero]
  · have hn : n ≤ j := by omega
    rw [if_pos hn, alphaStep_val, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← pow_add,
      Nat.add_sub_cancel' hn]

/-- The induced filtration of `A` consists of the elements whose first `n` coordinates vanish. -/
lemma mem_Nind_iff {n : ℕ} {a : A p} : a ∈ Nind p n ↔ ∀ j < n, a j = 0 where
  mp h := fun j hj => Nind_apply_eq_zero (p := p) (j := j) h hj
  mpr h := Nind_mem_of_coord p h

/-- The canonical map `A → lim_n A/(A ∩ p^n B)`. -/
def indComplOf : A p →+ PComplInd p where
  toFun a := ⟨fun n => (QuotientAddGroup.mk a : A p ⧸ Nind p n), by
    intro n
    rw [transMap_mk]⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero (QuotientAddGroup.mk' (Nind p n))
  map_add' := by
    intro a b
    apply Subtype.ext
    funext n
    exact map_add (QuotientAddGroup.mk' (Nind p n)) a b

/-- Evaluation of the `j`-th coordinate of an element of `A`. -/
def evalCoord (j : ℕ) : A p →+ ZMod p where
  toFun a := a j
  map_zero' := DFinsupp.zero_apply j
  map_add' := fun a b => DFinsupp.add_apply a b j

/-- The `j`-th coordinate, read off in the `(j+1)`-st quotient `A/(A ∩ p^(j+1) B)`. -/
def coordHom (j : ℕ) : A p ⧸ Nind p (j + 1) →+ ZMod p :=
  QuotientAddGroup.lift (Nind p (j + 1)) (evalCoord p j) (fun a ha => by
    have h : evalCoord p j a = 0 := by
      show a j = 0
      exact mem_Nind_iff p |>.mp ha j (by omega)
    exact AddMonoidHom.mem_ker.mp h)

lemma coordHom_mk (j : ℕ) (a : A p) :
    coordHom p j (QuotientAddGroup.mk a : A p ⧸ Nind p (j + 1)) = a j :=
  QuotientAddGroup.lift_mk _ _ a

/-- Coordinates of a compatible family in `lim_n A/(A ∩ p^n B)`. -/
def Phi : PComplInd p →+ (ℕ → ZMod p) where
  toFun x := fun j => coordHom p j (x.1 (j + 1))
  map_zero' := by
    funext j
    exact map_zero (coordHom p j)
  map_add' := by
    intro x y
    funext j
    exact map_add (coordHom p j) _ _

/-- Truncation of a function to its first `n` values. -/
def truncA (n : ℕ) (f : ℕ → ZMod p) : A p :=
  DFinsupp.mk (Finset.range n) (fun j => f j.1)

lemma truncA_apply (n : ℕ) (f : ℕ → ZMod p) (j : ℕ) :
    truncA p n f j = if j < n then f j else 0 := by
  rw [truncA, DFinsupp.mk_apply]
  by_cases h : j < n
  · rw [dif_pos (Finset.mem_range.mpr h), if_pos h]
  · rw [dif_neg (by simpa using h), if_neg h]

def truncHom (n : ℕ) : (ℕ → ZMod p) →+ A p where
  toFun f := truncA p n f
  map_zero' := by
    refine DFinsupp.ext fun j => ?_
    rw [truncA_apply]
    split_ifs <;> simp
  map_add' := by
    intro f g
    refine DFinsupp.ext fun j => ?_
    rw [truncA_apply, DFinsupp.add_apply, truncA_apply, truncA_apply]
    split_ifs <;> simp

lemma truncHom_apply (n : ℕ) (f : ℕ → ZMod p) (j : ℕ) :
    truncHom p n f j = if j < n then f j else 0 := truncA_apply p n f j

/-- The map from the product to the completion: a function is sent to its truncations. -/
def Psi : (ℕ → ZMod p) →+ PComplInd p where
  toFun f := ⟨fun n => (QuotientAddGroup.mk (truncHom p n f) : A p ⧸ Nind p n), by
    intro n
    rw [transMap_mk, QuotientAddGroup.eq_iff_sub_mem]
    refine mem_Nind_iff p |>.mpr fun j hj => ?_
    rw [DFinsupp.sub_apply, truncHom_apply, truncHom_apply,
      if_pos (show j < n + 1 by omega), if_pos hj]
    simp⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    show (QuotientAddGroup.mk (truncHom p n 0) : A p ⧸ Nind p n) = 0
    rw [map_zero]
    exact map_zero (QuotientAddGroup.mk' (Nind p n))
  map_add' := by
    intro f g
    apply Subtype.ext
    funext n
    show (QuotientAddGroup.mk (truncHom p n (f + g)) : A p ⧸ Nind p n)
      = QuotientAddGroup.mk (truncHom p n f) + QuotientAddGroup.mk (truncHom p n g)
    rw [map_add]
    exact map_add (QuotientAddGroup.mk' (Nind p n)) _ _

/-- A compatible family is determined by its coordinates. -/
lemma coord_eq_of_level : ∀ (n : ℕ) (x : PComplInd p) (a : A p),
    (QuotientAddGroup.mk a : A p ⧸ Nind p n) = x.1 n →
      ∀ j < n, coordHom p j (x.1 (j + 1)) = a j
  | 0, _, _, _, j, hj => absurd hj (by omega)
  | (k + 1), x, a, ha, j, hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjeq
      · have hk : (QuotientAddGroup.mk a : A p ⧸ Nind p k) = x.1 k := by
          rw [show x.1 k
            = transMap (𝒩 := fun n => Nind p n) (Nind_antitone p) k (x.1 (k + 1))
            from (x.2 k).symm, ← ha, transMap_mk]
        exact coord_eq_of_level k x a hk j hjk
      · subst hjeq
        rw [← ha, coordHom_mk]

lemma Phi_Psi (f : ℕ → ZMod p) : Phi p (Psi p f) = f := by
  funext j
  show coordHom p j ((Psi p f).1 (j + 1)) = f j
  rw [show (Psi p f).1 (j + 1)
      = (QuotientAddGroup.mk (truncHom p (j + 1) f) : A p ⧸ Nind p (j + 1)) from rfl,
    coordHom_mk, truncHom_apply, if_pos (by omega : j < j + 1)]

lemma Psi_Phi (x : PComplInd p) : Psi p (Phi p x) = x := by
  apply Subtype.ext
  funext n
  obtain ⟨a, ha⟩ := Quotient.exists_rep (x.1 n)
  show (QuotientAddGroup.mk (truncHom p n (Phi p x)) : A p ⧸ Nind p n) = x.1 n
  rw [← ha, QuotientAddGroup.eq_iff_sub_mem]
  refine mem_Nind_iff p |>.mpr fun j hj => ?_
  rw [DFinsupp.sub_apply, truncHom_apply, if_pos hj]
  have hcoord : (Phi p x) j = a j := coord_eq_of_level p n x a ha j hj
  rw [hcoord, sub_self]

/-- The completion of `A` for the topology induced from `B` is the product `∏_j ℤ/p`. -/
noncomputable def indComplEquiv : PComplInd p ≃+ (ℕ → ZMod p) where
  toFun := Phi p
  invFun := Psi p
  left_inv := Psi_Phi p
  right_inv := Phi_Psi p
  map_add' := (Phi p).map_add

lemma Phi_indComplOf (a : A p) : Phi p (indComplOf p a) = a := by
  funext j
  show coordHom p j ((indComplOf p a).1 (j + 1)) = a j
  rw [show (indComplOf p a).1 (j + 1)
      = (QuotientAddGroup.mk a : A p ⧸ Nind p (j + 1)) from rfl, coordHom_mk]

/-- `A` maps into the product only as the direct sum: the canonical map is not surjective. -/
theorem indComplOf_not_surjective : ¬ Function.Surjective (indComplOf (p := p)) := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (Psi p (fun _ => 1))
  have h1 : Phi p (Psi p (fun _ => 1)) = Phi p (indComplOf p a) := by rw [ha]
  rw [Phi_Psi, Phi_indComplOf] at h1
  have hsupp : ∀ j, a j = 1 := by
    intro j
    have hc := congrFun h1 j
    simpa using hc.symm
  obtain ⟨j, hj⟩ : ∃ j, a j = 0 := by
    refine ⟨a.support.sup id + 1, ?_⟩
    by_contra hne
    have hmem : a.support.sup id + 1 ∈ a.support := DFinsupp.mem_support_iff.mpr hne
    have hle : a.support.sup id + 1 ≤ a.support.sup id := Finset.le_sup (f := id) hmem
    omega
  rw [hsupp j] at hj
  exact one_ne_zero_zmod p hj


/-! ### `p`-adic completion is not right exact -/

lemma quotAlphaHom_surjective : Function.Surjective (quotAlphaHom p) :=
  QuotientAddGroup.mk'_surjective (AddMonoidHom.range (alpha p))

lemma quotAlphaHom_exact : Function.Exact (alpha p) (quotAlphaHom p) := by
  intro y
  constructor
  · intro hy
    rw [quotAlphaHom, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk'] at hy
    exact hy
  · rintro ⟨x, rfl⟩
    rw [quotAlphaHom, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact ⟨x, rfl⟩

/-- The completed sequence `Â → B̂ → (B/αA)^` is not exact at `B̂`: `ξ` lies in the kernel
of the completed quotient map but not in the image of the completed `α`. -/
theorem completed_not_exact :
    ∃ z : PCompl p (B p), quotCompl p z = 0 ∧
      ∀ y : PCompl p (A p), alphaCompl p y ≠ z := by
  refine ⟨xi p, pComplMap_quot_xi p, ?_⟩
  intro y hy
  obtain ⟨a, rfl⟩ := pCompl_A_bijective p |>.2 y
  rw [show alphaCompl p (pComplOf p a) = pComplOf p (alpha p a) from pComplMap_of p (alpha p) a]
    at hy
  exact of_alpha_ne_xi p a hy

/-- Atiyah–Macdonald, Exercise 10.1: the `p`-adic completion of `A = ⨁_j ℤ/p` is `A`. -/
theorem exercise_A_complete : Nonempty (PCompl p (A p) ≃+ A p) := ⟨pComplAEquiv p⟩

/-- Atiyah–Macdonald, Exercise 10.1: the completion of `A` for the topology induced from
the `p`-adic topology of `B = ⨁_j ℤ/p^(j+1)` is the product `∏_j ℤ/p` (and `A` maps into
it as the direct sum only). -/
theorem exercise_induced_completion_is_product :
    Nonempty (PComplInd p ≃+ (ℕ → ZMod p)) ∧ ¬ Function.Surjective (indComplOf (p := p)) :=
  ⟨⟨indComplEquiv p⟩, indComplOf_not_surjective p⟩

/-- Atiyah–Macdonald, Exercise 10.1: `p`-adic completion is not a right exact functor on
the category of all `ℤ`-modules. -/
theorem p_adic_completion_not_right_exact :
    ¬ (∀ (M' M M'' : Type) [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
        (f : M' →+ M) (g : M →+ M''), Function.Exact f g → Function.Surjective g →
        Function.Exact (pComplMap p (M := M') (N := M) f)
          (pComplMap p (M := M) (N := M'') g)) := by
  intro H
  have hex := @H (A p) (B p) (Bq p) _ _ _ (alpha p) (quotAlphaHom p)
    (quotAlphaHom_exact p) (quotAlphaHom_surjective p)
  obtain ⟨z, hz, hz'⟩ := completed_not_exact p
  obtain ⟨y, hy⟩ := (hex z).mp hz
  exact hz' y hy

#print axioms AtiyahMcdonald69.Ex_10_1.alpha_injective
#print axioms AtiyahMcdonald69.Ex_10_1.pCompl_A_bijective
#print axioms AtiyahMcdonald69.Ex_10_1.pComplAEquiv
#print axioms AtiyahMcdonald69.Ex_10_1.exercise_A_complete
#print axioms AtiyahMcdonald69.Ex_10_1.exercise_induced_completion_is_product
#print axioms AtiyahMcdonald69.Ex_10_1.quotCompl
#print axioms AtiyahMcdonald69.Ex_10_1.pComplMap_quot_xi
#print axioms AtiyahMcdonald69.Ex_10_1.of_alpha_ne_xi
#print axioms AtiyahMcdonald69.Ex_10_1.completed_not_exact
#print axioms AtiyahMcdonald69.Ex_10_1.p_adic_completion_not_right_exact

end Concrete

end AtiyahMcdonald69.Ex_10_1
