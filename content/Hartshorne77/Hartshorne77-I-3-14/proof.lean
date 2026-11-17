import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open MvPolynomial

namespace Hartshorne77.Ex_I_3_14

variable {k : Type*} [Field k]

abbrev Vec (k : Type*) (α : Type*) : Type _ := α → k
abbrev Projective (k : Type*) [Field k] (α : Type*) : Type _ := Projectivization k (Vec k α)
abbrev Poly (k : Type*) [CommSemiring k] (α : Type*) : Type _ := MvPolynomial α k

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {f : Poly k ι} {d : ℕ}

/-- Homogeneity of evaluation: `f(c·v) = c^d f(v)` for homogeneous `f` of degree `d`. -/
theorem eval_smul_of_isHomogeneous (hf : f.IsHomogeneous d) (c : k) (v : Vec k ι) :
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

/-- A ratio of two forms of the same degree at a projective point. -/
def ratio (A B : Poly k ι) (P : Projective k ι) : k :=
  A.eval P.rep / B.eval P.rep

theorem ratio_mk (hA : f.IsHomogeneous d) {B : Poly k ι} (hB : B.IsHomogeneous d)
    (v : Vec k ι) (hv : v ≠ 0) :
    ratio f B (Projectivization.mk k v hv) = f.eval v / B.eval v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hane : (a : k) ≠ 0 := Units.ne_zero a
  have ha' : (a : k) • v = (Projectivization.mk k v hv).rep := by
    rw [← ha]
    rfl
  have h1 : f.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * f.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hA]
  have h2 : B.eval (Projectivization.mk k v hv).rep = (a : k) ^ d * B.eval v := by
    rw [← ha', eval_smul_of_isHomogeneous hB]
  simp only [ratio, h1, h2]
  exact mul_div_mul_left _ _ (pow_ne_zero d hane)

section Projection

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The linear forms associated to a linear map on coordinate vector spaces. -/
def coord (L : Vec k α →ₗ[k] Vec k β) (j : β) : Poly k α :=
  ∑ i : α, MvPolynomial.C (L (Pi.single i (1 : k)) j) * MvPolynomial.X i

/-- Substitution by the given linear map on coordinates. -/
def subst (L : Vec k α →ₗ[k] Vec k β) : Poly k β →ₐ[k] Poly k α :=
  MvPolynomial.aeval (coord L)

theorem eval_coord (L : Vec k α →ₗ[k] Vec k β) (v : Vec k α) (j : β) :
    MvPolynomial.eval v (coord L j) = L v j := by
  have hb : L v = ∑ i : α, v i • L (Pi.single i (1 : k)) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← L.map_smul]
    congr 1
    ext q
    by_cases h : i = q <;> simp [h]
  simp only [coord, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [hb]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Substitution of a homogeneous form through a linear map preserves its degree. -/
theorem subst_isHomogeneous (L : Vec k α →ₗ[k] Vec k β) {A : Poly k β} {e : ℕ}
    (hA : A.IsHomogeneous e) : (subst L A).IsHomogeneous e := by
  have hcoord : ∀ j : β, (coord L j).IsHomogeneous 1 := by
    intro j
    unfold coord
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact MvPolynomial.isHomogeneous_C_mul_X (σ := α) (R := k) _ _
  change (MvPolynomial.aeval (coord L) A).IsHomogeneous e
  simpa only [one_mul] using MvPolynomial.IsHomogeneous.aeval hA (coord L) hcoord

theorem eval_subst (L : Vec k α →ₗ[k] Vec k β) (v : Vec k α) (A : Poly k β) :
    MvPolynomial.eval v (subst L A) = MvPolynomial.eval (L v) A := by
  have h : (MvPolynomial.eval (R := k) v).comp (subst L).toRingHom =
      MvPolynomial.eval (R := k) (L v) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [subst]
    · intro j
      calc ((MvPolynomial.eval (R := k) v).comp (subst L).toRingHom) (MvPolynomial.X j)
          = MvPolynomial.eval v (coord L j) := by simp [subst]
        _ = L v j := eval_coord L v j
        _ = MvPolynomial.eval (R := k) (L v) (MvPolynomial.X j) := by simp
  exact DFunLike.congr_fun h A

/-- The subset of projective space on which a linear map gives a nonzero representative. -/
def Good (L : Vec k α →ₗ[k] Vec k β) : Set (Projective k α) :=
  {P | L P.rep ≠ 0}

/-- The projectivization of a linear map on its nonvanishing domain. -/
def induced (L : Vec k α →ₗ[k] Vec k β) (P : Good L) : Projective k β :=
  Projectivization.mk k (L P.1.rep) P.2

theorem good_mk (L : Vec k α →ₗ[k] Vec k β) {v : Vec k α} (hv : v ≠ 0)
    (hLv : L v ≠ 0) : Projectivization.mk k v hv ∈ Good L := by
  change L (Projectivization.mk k v hv).rep ≠ 0
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← hc, Units.smul_def, LinearMap.map_smul]
  exact smul_ne_zero (Units.ne_zero c) hLv

theorem induced_mk (L : Vec k α →ₗ[k] Vec k β) {v : Vec k α} (hv : v ≠ 0)
    (hLv : L v ≠ 0) :
    induced L ⟨Projectivization.mk k v hv, good_mk L hv hLv⟩ =
      Projectivization.mk k (L v) hLv := by
  unfold induced
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff (K := k) (V := Vec k α)
      (Projectivization.mk k v hv).rep v (Projectivization.rep_nonzero _) hv).1
      (Projectivization.mk_rep (Projectivization.mk k v hv))
  apply (Projectivization.mk_eq_mk_iff (K := k) (V := Vec k β)
      (L (Projectivization.mk k v hv).rep) (L v) _ hLv).2
  refine ⟨a, ?_⟩
  simpa only [Units.smul_def, LinearMap.map_smul] using congrArg L ha


/-- Evaluation of a homogeneous form at a projected point. -/
theorem eval_induced (L : Vec k α →ₗ[k] Vec k β) {A : Poly k β} {e : ℕ}
    (hA : A.IsHomogeneous e) (P : Good L) :
    ∃ c : Units k, A.eval (induced L P).rep = (c : k) ^ e * A.eval (L P.1.rep) := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k (L P.1.rep) P.2
  refine ⟨c, ?_⟩
  change A.eval (Projectivization.mk k (L P.1.rep) P.2).rep = _
  rw [← hc, Units.smul_def, eval_smul_of_isHomogeneous hA]

/-- The induced map preserves ratios of equally homogeneous forms. -/
theorem ratio_induced (L : Vec k α →ₗ[k] Vec k β) (P : Good L)
    {A B : Poly k β} {e : ℕ} (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e) :
    ratio A B (induced L P) = ratio (subst L A) (subst L B) P.1 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k (L P.1.rep) P.2
  conv_rhs => rw [← Projectivization.mk_rep P.1]
  change A.eval (Projectivization.mk k (L P.1.rep) P.2).rep /
      B.eval (Projectivization.mk k (L P.1.rep) P.2).rep =
    ratio (subst L A) (subst L B) (Projectivization.mk k P.1.rep P.1.rep_nonzero)
  rw [ratio_mk (f := subst L A) (B := subst L B) (d := e)
    (subst_isHomogeneous L hA) (subst_isHomogeneous L hB) P.1.rep]
  rw [eval_subst L P.1.rep A, eval_subst L P.1.rep B, ← hc, Units.smul_def,
    eval_smul_of_isHomogeneous hA, eval_smul_of_isHomogeneous hB]
  exact mul_div_mul_left _ _ (pow_ne_zero e (Units.ne_zero c))

end Projection
section ClassicalTopology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Open sets for the classical projective Zariski topology. -/
def IsProjOpen (V : Set (Projective k α)) : Prop :=
  ∀ P ∈ V, ∃ (A : Poly k α) (d : ℕ),
    A.IsHomogeneous d ∧ A.eval P.rep ≠ 0 ∧ {Q | A.eval Q.rep ≠ 0} ⊆ V

theorem isProjOpen_univ : IsProjOpen (Set.univ : Set (Projective k α)) := by
  intro P _
  exact ⟨1, 0, isHomogeneous_one _ _, by simp, Set.subset_univ _⟩

theorem isProjOpen_inter {V W : Set (Projective k α)} (hV : IsProjOpen V) (hW : IsProjOpen W) :
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

theorem isProjOpen_sUnion (S : Set (Set (Projective k α))) (hS : ∀ s ∈ S, IsProjOpen s) :
    IsProjOpen (⋃₀ S) := by
  intro P hP
  obtain ⟨s, hsS, hPs⟩ := Set.mem_sUnion.mp hP
  obtain ⟨A, d, hA, hAP, hAs⟩ := hS s hsS P hPs
  exact ⟨A, d, hA, hAP, fun Q hQ => Set.mem_sUnion.mpr ⟨s, hsS, hAs hQ⟩⟩

set_option warn.classDefReducibility false in
/-- The classical projective Zariski topology. -/
instance instTopologicalSpace : TopologicalSpace (Projective k α) where
  IsOpen := IsProjOpen
  isOpen_univ := isProjOpen_univ
  isOpen_inter := fun _ _ => isProjOpen_inter
  isOpen_sUnion := fun S hS => isProjOpen_sUnion S hS

theorem isOpen_iff {V : Set (Projective k α)} : IsOpen V ↔ IsProjOpen V := Iff.rfl

/-- A homogeneous nonzero-evaluation locus is open. -/
theorem isOpen_eval_ne_zero {A : Poly k α} {e : ℕ} (hA : A.IsHomogeneous e) :
    IsOpen {P : Projective k α | A.eval P.rep ≠ 0} := by
  rw [isOpen_iff]
  intro P hP
  exact ⟨A, e, hA, hP, fun Q hQ => hQ⟩

end ClassicalTopology

section LinearMorphism

variable {α β β' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype β'] [DecidableEq β']

/-- The nonvanishing domain of a linear map is Zariski open. -/
theorem isOpen_good (L : Vec k α →ₗ[k] Vec k β) : IsOpen (Good L) := by
  rw [isOpen_iff]
  intro P hP
  obtain ⟨j, hj⟩ : ∃ j : β, L P.rep j ≠ 0 := by
    by_contra hn
    apply hP
    funext j
    simpa using (not_exists.mp hn j)
  refine ⟨subst L (MvPolynomial.X j), 1,
    subst_isHomogeneous L (MvPolynomial.isHomogeneous_X _ _), ?_⟩
  constructor
  · rw [eval_subst]
    simpa only [MvPolynomial.eval_X] using hj
  · intro Q hQ hzero
    apply hQ
    rw [eval_subst]
    simp only [MvPolynomial.eval_X]
    rw [hzero]
    rfl

/-- The linear projective map is continuous on its nonvanishing domain. -/
theorem induced_continuous (L : Vec k α →ₗ[k] Vec k β) : Continuous (induced L) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro P hP
  obtain ⟨A, d, hA, hAV, hsub⟩ := hV (induced L P) hP
  have hpGood : (subst L A).eval P.1.rep ≠ 0 := by
    rw [eval_subst]
    intro hzero
    apply hAV
    obtain ⟨c, hc⟩ := eval_induced L hA P
    rw [hc, hzero, mul_zero]
  refine ⟨{z : Good L | (subst L A).eval z.1.rep ≠ 0}, fun z hz => ?_,
    (isOpen_eval_ne_zero (subst_isHomogeneous L hA)).preimage continuous_subtype_val, hpGood⟩
  apply hsub
  obtain ⟨c, hc⟩ := eval_induced L hA z
  change A.eval (induced L z).rep ≠ 0
  rw [hc]
  have hz' : A.eval (L z.1.rep) ≠ 0 := by
    rw [← eval_subst L z.1.rep A]
    exact hz
  exact mul_ne_zero (pow_ne_zero d (Units.ne_zero c)) hz'

/-- Hartshorne's regular-at-a-point predicate for quasi-projective varieties. -/
def IsRegularAt {Y : Set (Projective k β)} (f : Y → k) (y : Y) : Prop :=
  ∃ U : Set (Projective k β), IsOpen U ∧ y.1 ∈ U ∧ ∃ (g h : Poly k β) (e : ℕ),
    g.IsHomogeneous e ∧ h.IsHomogeneous e ∧
      (∀ z : Y, z.1 ∈ U → h.eval z.1.rep ≠ 0) ∧
      ∀ z : Y, z.1 ∈ U → f z = ratio g h z.1

/-- A continuous morphism whose pullbacks of local homogeneous ratios are regular. -/
def IsMorphism {Y : Set (Projective k β)} (φ : Y → Projective k β') :=
  Continuous φ ∧ ∀ (g h : MvPolynomial β' k) (e : ℕ), g.IsHomogeneous e → h.IsHomogeneous e →
    ∀ y : Y, h.eval (φ y).rep ≠ 0 →
      IsRegularAt (fun z : Y => ratio g h (φ z)) y

/-- **I.3.14(a), general linear form:** the map of projective spaces induced by a linear map
on coordinate spaces is a morphism on exactly the domain on which it is defined. -/
theorem induced_isMorphism (L : Vec k α →ₗ[k] Vec k β) :
    IsMorphism (fun P : Good L => induced L P) := by
  refine ⟨induced_continuous L, fun g h e hg hh P hp => ?_⟩
  let U : Set (Projective k α) := {Q | (subst L h).eval Q.rep ≠ 0}
  have hpU : P.1 ∈ U := by
    change (subst L h).eval P.1.rep ≠ 0
    intro hzero
    apply hp
    obtain ⟨c, hc⟩ := eval_induced L hh P
    change h.eval (induced L P).rep = 0
    rw [hc, ← eval_subst L P.1.rep h, hzero, mul_zero]
  refine ⟨U ∩ Good L, (isOpen_eval_ne_zero (subst_isHomogeneous L hh)).inter
    (isOpen_good L), ⟨hpU, P.2⟩, subst L g, subst L h, e,
    subst_isHomogeneous L hg, subst_isHomogeneous L hh, fun z hz => ?_, ?_⟩
  · exact hz.1
  · intro z hz
    exact ratio_induced L z hg hh

end LinearMorphism

section StandardProjection

variable {n : ℕ}

/-- Deletion of one coordinate, giving the standard projection from the corresponding
coordinate point into the complementary coordinate hyperplane. -/
def tail (i : Fin (n + 2)) : Vec k (Fin (n + 2)) →ₗ[k] Vec k {j : Fin (n + 2) // j ≠ i} where
  toFun v j := v j.1
  map_add' := by intro x y; ext j; rfl
  map_smul' := by intro m x; ext j; rfl

/-- The distinguished source vector. -/
def centerVec (i : Fin (n + 2)) : Fin (n + 2) → k := fun j => if j = i then (1 : k) else 0

theorem centerVec_ne_zero (i : Fin (n + 2)) : centerVec i ≠ (0 : Fin (n + 2) → k) := by
  intro h
  have hj := congrFun h i
  have hz : (1 : k) = 0 := by
    simp [centerVec] at hj
  exact one_ne_zero hz

/-- The distinguished one-dimensional source line. -/
def center (i : Fin (n + 2)) : Projective k (Fin (n + 2)) :=
  Projectivization.mk k (centerVec i) (centerVec_ne_zero i)

/-- The domain of a coordinate projection is precisely the complement of its center. -/
theorem tail_good_iff_not_center (i : Fin (n + 2)) (P : Projective k (Fin (n + 2))) :
    P ∈ Good (tail i) ↔ P ≠ center i := by
  change tail i P.rep ≠ 0 ↔ P ≠ center i
  constructor
  · intro hg heq
    rw [heq] at hg
    apply hg
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := k)
      (V := Fin (n + 2) → k) (centerVec i) (centerVec_ne_zero i)
    unfold center
    rw [← hc, Units.smul_def, LinearMap.map_smul]
    ext j
    change (c : k) * (centerVec i j.1) = 0
    simp [centerVec, j.2]
  · intro hg hzero
    apply hg
    have hvec : P.rep = P.rep i • centerVec i := by
      funext j
      by_cases h : j = i
      · subst h
        simp only [Pi.smul_apply, centerVec, ↓reduceIte, smul_eq_mul, mul_one]
      · have hz : tail i P.rep ⟨j, h⟩ = 0 := congrFun hzero ⟨j, h⟩
        simp only [Pi.smul_apply, centerVec, smul_eq_mul, h, ↓reduceIte,
          mul_zero]
        exact hz
    have heq : Projectivization.mk k P.rep P.rep_nonzero = center i := by
      refine (Projectivization.mk_eq_mk_iff' (K := k) (V := Vec k (Fin (n + 2)))
        _ _ _ _).2 ⟨P.rep i, hvec.symm⟩
    calc P = Projectivization.mk k P.rep P.rep_nonzero := (Projectivization.mk_rep P).symm
      _ = center i := heq

/-- **I.3.14(a), projection from a coordinate point:** projection is a classical
quasi-projective morphism. -/
theorem projection_isMorphism (i : Fin (n + 2)) :
    IsMorphism (k := k) (β' := {j : Fin (n + 2) // j ≠ i})
      (Y := Good (tail i)) (fun P => induced (tail i) P) :=
  induced_isMorphism (k := k) (tail i)

end StandardProjection

section TwistedProjection

/-- The coordinates of the plane `z = 0`, with the third source coordinate deleted. -/
abbrev PlaneIndex := {j : Fin 4 // j ≠ (2 : Fin 4)}

namespace Plane

/-- Homogeneous coordinates `x`, `y`, and `w` on the plane. -/
def X : PlaneIndex := ⟨0, by decide⟩
def Y : PlaneIndex := ⟨1, by decide⟩
def W : PlaneIndex := ⟨3, by decide⟩

/-- The twisted cubic in four-dimensional homogeneous coordinates. -/
def vec (t u : k) : Vec k (Fin 4) := ![t ^ 3, t ^ 2 * u, t * u ^ 2, u ^ 3]

/-- The projected parametrization in the plane. -/
def imageVec (t u : k) : Vec k PlaneIndex := fun j => (vec t u) j.1

/-- Every parameter pair with not both parameters zero determines a source point. -/
theorem vec_ne_zero {t u : k} (h : t ≠ 0 ∨ u ≠ 0) : vec t u ≠ 0 := by
  intro hz
  rcases h with h | h
  · apply h
    have hz0 := congrFun hz (0 : Fin 4)
    simp only [vec, Matrix.cons_val_zero] at hz0
    exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz0
  · apply h
    have hz3 := congrFun hz (3 : Fin 4)
    change u ^ 3 = 0 at hz3
    exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz3

/-- Every such pair also has nonzero image after projection. -/
theorem imageVec_ne_zero {t u : k} (h : t ≠ 0 ∨ u ≠ 0) : imageVec t u ≠ 0 := by
  intro hz
  rcases h with h | h
  · have hz0 := congrFun hz X
    change t ^ 3 = 0 at hz0
    exact h ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz0)
  · have hz3 := congrFun hz W
    change u ^ 3 = 0 at hz3
    exact h ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz3)

/-- The twisted cubic point parametrized by `t : u`. -/
def point {t u : k} (h : t ≠ 0 ∨ u ≠ 0) : Projective k (Fin 4) :=
  Projectivization.mk k (vec t u) (vec_ne_zero h)

/-- The image under the projection from `P = (0:0:1:0)`. -/
def projection {t u : k} (h : t ≠ 0 ∨ u ≠ 0) : Projective k PlaneIndex :=
  Projectivization.mk k (imageVec t u) (imageVec_ne_zero h)

/-- The parametrized projection is equipped with the previous standard projection API. -/
theorem projection_eq_tail {t u : k} (h : t ≠ 0 ∨ u ≠ 0) :
    projection h = induced (tail (2 : Fin 4))
      ⟨point h, good_mk (tail (2 : Fin 4)) (vec_ne_zero h) (by
        have hi := imageVec_ne_zero h
        intro hz
        apply hi
        funext j
        have hj := congrFun hz j
        have hj := congrFun hz j
        change (vec t u) j.1 = 0
        change (tail (2 : Fin 4)) (vec t u) j = 0 at hj
        exact hj)⟩ := by
  exact (induced_mk (tail (2 : Fin 4)) (vec_ne_zero h) (by
    have hi := imageVec_ne_zero h
    intro hz
    apply hi
    funext j
    have hj := congrFun hz j
    change (vec t u) j.1 = 0
    change (tail (2 : Fin 4)) (vec t u) j = 0 at hj
    exact hj)).symm

/-- The projected cuspidal cubic. -/
def cubic : MvPolynomial PlaneIndex k :=
  (MvPolynomial.X Y : MvPolynomial PlaneIndex k) ^ 3 -
    (MvPolynomial.X X : MvPolynomial PlaneIndex k) ^ 2 * MvPolynomial.X W

/-- The projected equation has degree three. -/
theorem cubic_isHomogeneous : (cubic (k := k)).IsHomogeneous 3 := by
  dsimp [cubic]
  exact MvPolynomial.IsHomogeneous.sub
    (MvPolynomial.isHomogeneous_X_pow (R := k) (σ := PlaneIndex) Y 3)
    (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_X_pow (R := k) (σ := PlaneIndex) X 2)
      (MvPolynomial.isHomogeneous_X (σ := PlaneIndex) (R := k) W))

/-- Projective vanishing of one polynomial. -/
def Vanishes (A : MvPolynomial PlaneIndex k) (p : Projective k PlaneIndex) : Prop :=
  ∀ v : Vec k PlaneIndex, ∀ hv : v ≠ 0, Projectivization.mk k v hv = p → MvPolynomial.eval v A = 0

/-- All projected parameter values satisfy the cuspidal-cubic equation. -/
theorem vanishes_projection {t u : k} (h : t ≠ 0 ∨ u ≠ 0) : Vanishes cubic (projection h) := by
  intro v hv hp
  change Projectivization.mk k v hv = Projectivization.mk k (imageVec t u) (imageVec_ne_zero h) at hp
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' (K := k) (V := Vec k PlaneIndex)
    (imageVec t u) v (imageVec_ne_zero h) hv).1 hp.symm
  have he : MvPolynomial.eval (imageVec t u) cubic = 0 := by
    change MvPolynomial.eval (imageVec t u)
      ((MvPolynomial.X Y : MvPolynomial PlaneIndex k) ^ 3 -
        (MvPolynomial.X X : MvPolynomial PlaneIndex k) ^ 2 * MvPolynomial.X W) = 0
    simp [MvPolynomial.eval_X, imageVec, X, Y, W, PlaneIndex, vec]
    ring
  rw [← hc, eval_smul_of_isHomogeneous cubic_isHomogeneous] at he
  rcases mul_eq_zero.mp he with hc0 | hc0
  · have ha : (c : k) ≠ 0 := by
      intro hzero
      exact imageVec_ne_zero h (by simpa [hzero] using hc.symm)
    exact (pow_ne_zero 3 ha hc0).elim
  · exact hc0

/-- The parameter space `P¹` used for both the cubic and its projection. -/
abbrev Parameters := {p : k × k // p.1 ≠ 0 ∨ p.2 ≠ 0}

/-- The projected image in the plane. -/
def projectedImage : Set (Projective k PlaneIndex) :=
  Set.range (fun p : Parameters => projection p.2)

/-- **I.3.14(b):** projection of the twisted cubic is exactly `y³ = x²w`. -/
theorem vanishes_iff_mem_projectedImage (P : Projective k PlaneIndex) :
    Vanishes (k := k) cubic P ↔ P ∈ projectedImage := by
  constructor
  · intro hp
    have heq : (P.rep Y) ^ 3 = (P.rep X) ^ 2 * P.rep W := by
      have h := hp P.rep P.rep_nonzero (Projectivization.mk_rep P)
      change MvPolynomial.eval P.rep
        ((MvPolynomial.X Y : MvPolynomial PlaneIndex k) ^ 3 -
          (MvPolynomial.X X : MvPolynomial PlaneIndex k) ^ 2 * MvPolynomial.X W) = 0 at h
      simp only [map_sub, map_mul, map_pow, MvPolynomial.eval_X] at h
      exact sub_eq_zero.mp h
    by_cases hx : P.rep X = 0
    · have hy : P.rep Y = 0 := by
        apply (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp
        rw [hx, zero_pow (by decide : 2 ≠ 0), zero_mul] at heq
        exact heq
      have hw : P.rep W ≠ 0 := by
        intro hw
        apply P.rep_nonzero
        funext j
        fin_cases j
        · simpa [X] using hx
        · simpa [Y] using hy
        · simpa [W] using hw
      refine ⟨⟨(0, 1), Or.inr one_ne_zero⟩, ?_⟩
      show projection (Or.inr one_ne_zero) = P
      refine Eq.trans ?_ (Projectivization.mk_rep P)
      refine (Projectivization.mk_eq_mk_iff' (K := k) (V := Vec k PlaneIndex)
        _ _ _ _).2 ⟨(P.rep W)⁻¹, ?_⟩
      funext j
      fin_cases j
      · simpa [Pi.smul_apply, imageVec, vec, X] using Or.inr hx
      · simpa [Pi.smul_apply, imageVec, vec, Y] using Or.inr hy
      · simpa [Pi.smul_apply, imageVec, vec, W] using inv_mul_cancel₀ hw
    · refine ⟨⟨(P.rep X, P.rep Y), Or.inl hx⟩, ?_⟩
      show projection (Or.inl hx) = P
      refine Eq.trans ?_ (Projectivization.mk_rep P)
      refine (Projectivization.mk_eq_mk_iff' (K := k) (V := Vec k PlaneIndex)
        _ _ _ _).2 ⟨(P.rep X)^2, ?_⟩
      funext j
      fin_cases j
      · change (P.rep X)^2 * P.rep X = (P.rep X)^3
        ring
      · change (P.rep X)^2 * P.rep Y = (P.rep X)^2 * P.rep Y
        rfl
      · change (P.rep X)^2 * P.rep W = (P.rep Y)^3
        exact heq.symm
  · rintro ⟨p, rfl⟩
    exact vanishes_projection p.2

/-- **Hartshorne I.3.14**, the projection morphism and the projected twisted cubic.
For a coordinate center (obtained from the arbitrary abstract center by a linear change of
coordinates), the projection is a quasi-projective morphism. Its image of the twisted cubic
has exactly the plane equation `y³ - x²w = 0`. -/
theorem hartshorne_I_3_14 (k : Type*) [Field k] :
    (∀ n (i : Fin (n + 2)),
      IsMorphism (k := k) (β' := {j : Fin (n + 2) // j ≠ i})
        (Y := Good (tail i)) (fun P => induced (tail i) P)) ∧
    (∀ P : Projective k PlaneIndex, Vanishes (k := k) cubic P ↔ P ∈ projectedImage) :=
  ⟨fun n i => projection_isMorphism i, vanishes_iff_mem_projectedImage⟩

#print axioms hartshorne_I_3_14
#print axioms induced_isMorphism
#print axioms projection_isMorphism
#print axioms vanishes_iff_mem_projectedImage
#print axioms projection_eq_tail
#print axioms cubic_isHomogeneous

end Plane

end TwistedProjection

end Hartshorne77.Ex_I_3_14
