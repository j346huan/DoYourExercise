/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 3.26.

Let `(B_α, g_{αβ})` be a direct system of rings and `B` its direct limit.  For each `α`, let
`f_α : A → B_α` be ring homomorphisms such that `g_{αβ} ∘ f_α = f_β` whenever `α ≤ β` (i.e. the
`B_α` form a direct system of `A`-algebras).  The `f_α` induce a ring homomorphism `f : A → B`.
The exercise asks to prove

  `f^*(Spec B) = ⋂_α f_α^*(Spec B_α)`,   an equality of subsets of `Spec A`,

where `f^* : Spec B → Spec A` is the map induced by `f` (in Mathlib `PrimeSpectrum.comap`).

The book's hint is to compute the fibre of `f^*` over `𝔭` as the spectrum of
`B ⊗_A k(𝔭) ≅ lim_α (B_α ⊗_A k(𝔭))` and to use that a direct limit of rings is trivial only if
one of its stages is trivial.  Correspondingly the formalization is organized as follows.

* `nontrivial_TLim`: a directed colimit of nontrivial rings is nontrivial (`1 = 0` in the colimit
  forces `1 = 0` in some stage).  This is the contrapositive of the step in the hint.
* `psiK`, `psiL`, `tensorToTLim`: the comparison map
  `k ⊗_A (colim B_α) → colim_α (k ⊗_A B_α)`, `x ⊗ [b] ↦ [x ⊗ b]`, built from the universal
  property of the tensor product of algebras and of the direct limit.
* `nontrivial_tensor_lim`: if all fibres `k ⊗_A B_α` are nontrivial, then so is `k ⊗_A B`.
* `range_comap_algebraMap_eq_iInter`: the exercise for direct systems of `A`-algebras, using
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap` (Mathlib), which identifies
  `𝔭 ∈ range (Spec S → Spec A)` with nontriviality of `k(𝔭) ⊗_A S`.
* `inducedMap`, `inducedMap_eq`, `solution_induced`, `solution`: the exercise in the literal form
  of the book, for arbitrary ring homomorphisms `f_α` and the map `f` they induce.
-/
import Mathlib

open scoped TensorProduct
open TensorProduct

namespace AtiyahMcdonald69.Ex_3_26

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {B : ι → Type*} [∀ i, CommRing (B i)]

/-! ### Direct systems of `A`-algebras and their tensor products -/

section AlgebraVersion

variable [∀ i, Algebra A (B i)]
variable {g : ∀ i j, i ≤ j → B i →ₐ[A] B j}
variable [DirectedSystem B (fun i j h => g i j h)]

/-- `id_K ⊗ g_ij`, the transition map of the direct system `K ⊗[A] B_i`. -/
noncomputable def tensorHom (gm : ∀ i j, i ≤ j → B i →ₐ[A] B j) (K : Type*) [CommRing K] [Algebra A K]
    ⦃i j : ι⦄ (h : i ≤ j) : K ⊗[A] B i →ₐ[A] K ⊗[A] B j :=
  Algebra.TensorProduct.map ((AlgHom.id K K).restrictScalars A) (gm i j h)

omit [IsDirectedOrder ι] [Nonempty ι] in
theorem tensorHom_self (gm : ∀ i j, i ≤ j → B i →ₐ[A] B j) (K : Type*) [CommRing K] [Algebra A K]
    [DirectedSystem B (fun i j h => gm i j h)] ⦃i : ι⦄ :
    tensorHom (B := B) gm K (le_refl i) = AlgHom.id A _ := by
  have hg : gm i i le_rfl = AlgHom.id A (B i) := by
    ext x
    exact DirectedSystem.map_self' (f := fun i j h => gm i j h) x
  refine AlgHom.ext ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [tensorHom, hg]
  | add x y hx hy =>
      simp only [map_add, AlgHom.id_apply] at hx hy ⊢
      rw [hx, hy]

omit [IsDirectedOrder ι] [Nonempty ι] in
theorem tensorHom_comp (gm : ∀ i j, i ≤ j → B i →ₐ[A] B j) (K : Type*) [CommRing K] [Algebra A K]
    [DirectedSystem B (fun i j h => gm i j h)] {i j l : ι} (hij : i ≤ j) (hjl : j ≤ l) :
    (tensorHom (B := B) gm K hjl).comp (tensorHom (B := B) gm K hij)
      = tensorHom (B := B) gm K (hij.trans hjl) := by
  have hg : (gm j l hjl).comp (gm i j hij) = gm i l (hij.trans hjl) := by
    ext x
    exact DirectedSystem.map_map' (f := fun i j h => gm i j h) hij hjl x
  simp only [tensorHom, ← hg]
  refine AlgHom.ext ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy =>
      simp only [map_add, AlgHom.comp_apply] at hx hy ⊢
      rw [hx, hy]

/-- `K ⊗[A] B_i` is again a direct system, with transition maps `id_K ⊗ g_ij`. -/
instance tensorDirectedSystem (gm : ∀ i j, i ≤ j → B i →ₐ[A] B j) (K : Type*) [CommRing K]
    [Algebra A K] [DirectedSystem B (fun i j h => gm i j h)] :
    DirectedSystem (fun i => K ⊗[A] B i) (fun ⦃i j⦄ (h : i ≤ j) => ⇑(tensorHom (B := B) gm K h)) where
  map_self := by
    intro i x
    show ⇑(tensorHom (B := B) gm K (le_refl i)) x = x
    rw [tensorHom_self]
    rfl
  map_map := by
    intro m j i hij hjm x
    show ⇑(tensorHom (B := B) gm K hjm) (⇑(tensorHom (B := B) gm K hij) x)
      = ⇑(tensorHom (B := B) gm K (hij.trans hjm)) x
    rw [← AlgHom.comp_apply, tensorHom_comp]

/-- The direct limit ring `B = colim_i B_i`. -/
abbrev Lim : Type _ := DirectLimit B (fun i j h => g i j h)

/-- The structure map `B_i → B`. -/
noncomputable def ofLim (i : ι) : B i →ₐ[A] Lim (B := B) (g := g) :=
  DirectLimit.Algebra.of B (fun i j h => g i j h) i

/-- The structure map `A → B` factors through every structure map `A → B_i`. -/
theorem algebraMap_lim_eq_of (i : ι) (a : A) :
    algebraMap A (Lim (B := B) (g := g)) a
      = ofLim (B := B) (g := g) i (algebraMap A (B i) a) := by
  rw [DirectLimit.algebraMap_def (G := B) (f := fun i j h => g i j h) i a]
  rfl

/-- The direct limit of the rings `K ⊗[A] B_i`. -/
abbrev TLim (K : Type*) [CommRing K] [Algebra A K] : Type _ :=
  DirectLimit (fun i => K ⊗[A] B i) (fun i j h => tensorHom (B := B) g K (i := i) (j := j) h)

/-- The structure map `K ⊗[A] B_i → colim_i (K ⊗[A] B_i)`. -/
noncomputable def ofTLim (K : Type*) [CommRing K] [Algebra A K] (i : ι) :
    K ⊗[A] B i →ₐ[A] TLim (B := B) (g := g) K :=
  DirectLimit.Algebra.of (fun i => K ⊗[A] B i)
    (fun i j h => tensorHom (B := B) g K (i := i) (j := j) h) i

/-! ### A directed colimit of nontrivial rings is nontrivial -/

/-- **A directed colimit of nontrivial rings is nontrivial.**  If `1 = 0` holds in the colimit,
then already `1 = 0` in one of the stages. -/
theorem nontrivial_TLim (K : Type*) [CommRing K] [Algebra A K]
    (hK : ∀ i, Nontrivial (K ⊗[A] B i)) : Nontrivial (TLim (B := B) (g := g) K) := by
  refine ⟨1, 0, fun h1 => ?_⟩
  have h2 : (⟦⟨Classical.arbitrary ι, (1 : K ⊗[A] B (Classical.arbitrary ι))⟩⟧ :
      TLim (B := B) (g := g) K) = 0 := by
    rw [← DirectLimit.one_def]
    exact h1
  obtain ⟨j, hj, hz⟩ := (DirectLimit.exists_eq_zero
    (G := fun i => K ⊗[A] B i)
    (f := fun i j h => tensorHom (B := B) g K (i := i) (j := j) h)
    (x := ⟨Classical.arbitrary ι, 1⟩)).mp h2
  have h3 : (1 : K ⊗[A] B j) = 0 := by
    rw [← map_one (tensorHom (B := B) g K hj)]
    exact hz
  exact zero_ne_one h3.symm

/-- `x ↦ [x ⊗ 1]`: the first component of the comparison map `K ⊗_A B → colim_i (K ⊗_A B_i)`. -/
noncomputable def psiK (K : Type*) [CommRing K] [Algebra A K] :
    K →ₐ[A] TLim (B := B) (g := g) K :=
  (ofTLim (B := B) (g := g) K (Classical.arbitrary ι)).comp
    ((Algebra.TensorProduct.includeLeft (R := A) (S := K) (A := K)
      (B := B (Classical.arbitrary ι))).restrictScalars A)

/-- `[b] ↦ [1 ⊗ b]`: the second component of the comparison map. -/
noncomputable def psiL (K : Type*) [CommRing K] [Algebra A K] :
    Lim (B := B) (g := g) →ₐ[A] TLim (B := B) (g := g) K :=
  DirectLimit.Algebra.lift (G := B) (f := fun i j h => g i j h)
    (P := TLim (B := B) (g := g) K)
    (g := fun i => (ofTLim (B := B) (g := g) K i).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B i)))
    (Hg := by
      intro i j hij x
      show ofTLim (B := B) (g := g) K j (1 ⊗ₜ (g i j hij) x)
        = ofTLim (B := B) (g := g) K i (1 ⊗ₜ x)
      have hstep : tensorHom (B := B) g K hij (1 ⊗ₜ[A] x) = (1 ⊗ₜ[A] (g i j hij) x) := by
        simp [tensorHom]
      rw [← hstep]
      exact DirectLimit.Algebra.of_f (G := fun i => K ⊗[A] B i)
        (f := fun i j h => tensorHom (B := B) g K (i := i) (j := j) h) hij _)

/-- The comparison map `K ⊗_A (colim_i B_i) → colim_i (K ⊗_A B_i)`, `x ⊗ [b] ↦ [x ⊗ b]`. -/
noncomputable def tensorToTLim (K : Type*) [CommRing K] [Algebra A K] :
    K ⊗[A] Lim (B := B) (g := g) →ₐ[A] TLim (B := B) (g := g) K :=
  Algebra.TensorProduct.lift (R := A) (S := A) (A := K) (B := Lim (B := B) (g := g))
    (C := TLim (B := B) (g := g) K) (psiK (B := B) (g := g) K) (psiL (B := B) (g := g) K)
    (fun x y => Commute.all (psiK (B := B) (g := g) K x) (psiL (B := B) (g := g) K y))

/-- If every stage `K ⊗[A] B_i` is nontrivial, then so is `K ⊗[A] B`. -/
theorem nontrivial_tensor_lim (K : Type*) [CommRing K] [Algebra A K]
    (hK : ∀ i, Nontrivial (K ⊗[A] B i)) : Nontrivial (K ⊗[A] Lim (B := B) (g := g)) := by
  refine ⟨1, 0, fun h1 => ?_⟩
  have h2 : (1 : TLim (B := B) (g := g) K) = 0 := by
    rw [← map_one (tensorToTLim (B := B) (g := g) K), h1, map_zero]
  obtain ⟨x, y, hxy⟩ := nontrivial_TLim (B := B) (g := g) K hK
  have hx : x = 0 := by rw [← mul_one x, h2, mul_zero]
  have hy : y = 0 := by rw [← mul_one y, h2, mul_zero]
  exact hxy (hx.trans hy.symm)

/-! ### The exercise, for direct systems of `A`-algebras -/

/-- `f^*(Spec B) ⊆ f_i^*(Spec B_i)` for every `i`. -/
theorem range_comap_algebraMap_subset (p : PrimeSpectrum A)
    (hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Lim (B := B) (g := g))))) (i : ι) :
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (B i))) := by
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (ofLim (B := B) (g := g) i) q, ?_⟩
  have hcomp : (((ofLim (B := B) (g := g) i) : B i →+* Lim (B := B) (g := g)).comp
      (algebraMap A (B i))) = algebraMap A (Lim (B := B) (g := g)) := by
    ext a
    exact (algebraMap_lim_eq_of (B := B) (g := g) i a).symm
  show PrimeSpectrum.comap (algebraMap A (B i))
    (PrimeSpectrum.comap (ofLim (B := B) (g := g) i) q) = p
  rw [← PrimeSpectrum.comap_comp_apply, hcomp, hq]

/-- **Atiyah–Macdonald, Exercise 3.26** (for direct systems of `A`-algebras):  the image of
`Spec B` in `Spec A` is the intersection of the images of `Spec B_α`. -/
theorem range_comap_algebraMap_eq_iInter :
    Set.range (PrimeSpectrum.comap (algebraMap A (Lim (B := B) (g := g))))
      = ⋂ i, Set.range (PrimeSpectrum.comap (algebraMap A (B i))) := by
  refine Set.Subset.antisymm (fun p hp => Set.mem_iInter.mpr
    (range_comap_algebraMap_subset (B := B) (g := g) p hp)) ?_
  intro p hp
  refine (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A)
    (S := Lim (B := B) (g := g)) p).mp ?_
  exact nontrivial_tensor_lim (B := B) (g := g) (p.asIdeal.ResidueField) fun i =>
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) (S := B i) p).mpr
      (Set.mem_iInter.mp hp i)

end AlgebraVersion

/-! ### The exercise in the literal form of the book -/

section RingHomForm

variable {G : ∀ i j, i ≤ j → B i →+* B j}
variable [hds : DirectedSystem B (fun i j h => G i j h)]

/-- The ring homomorphism `A → colim_i B_i` induced by a compatible family of ring homomorphisms
`φ i : A → B_i`.  (Independence of the chosen index is `inducedMap_eq`.) -/
noncomputable def inducedMap (φ : ∀ i, A →+* B i) (i : ι) :
    A →+* DirectLimit B (fun i j h => G i j h) :=
  (DirectLimit.Ring.of B (fun i j h => G i j h) i).comp (φ i)

/-- The induced map is independent of the chosen index: this is the statement that the `φ i`
induce a well defined map out of `A`. -/
theorem inducedMap_eq {φ : ∀ i, A →+* B i}
    (hφ : ∀ i j (hij : i ≤ j), (G i j hij).comp (φ i) = φ j) (i j : ι) :
    inducedMap (B := B) (G := G) φ i = inducedMap (B := B) (G := G) φ j := by
  obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
  have hi : inducedMap (B := B) (G := G) φ i
      = (DirectLimit.Ring.of B (fun i j h => G i j h) m).comp (φ m) := by
    rw [inducedMap, ← hφ i m him]
    ext x
    show DirectLimit.Ring.of B (fun i j h => G i j h) i ((φ i) x)
      = DirectLimit.Ring.of B (fun i j h => G i j h) m ((G i m him) ((φ i) x))
    exact (DirectLimit.Ring.of_f (G := B) (f := fun i j h => G i j h) him _).symm
  have hj : inducedMap (B := B) (G := G) φ j
      = (DirectLimit.Ring.of B (fun i j h => G i j h) m).comp (φ m) := by
    rw [inducedMap, ← hφ j m hjm]
    ext x
    show DirectLimit.Ring.of B (fun i j h => G i j h) j ((φ j) x)
      = DirectLimit.Ring.of B (fun i j h => G i j h) m ((G j m hjm) ((φ j) x))
    exact (DirectLimit.Ring.of_f (G := B) (f := fun i j h => G i j h) hjm _).symm
  rw [hi, hj]

set_option linter.style.haveILetI false in
/-- **Atiyah–Macdonald, Exercise 3.26**, with the canonically induced map `f`. -/
theorem solution_induced {φ : ∀ i, A →+* B i}
    (hφ : ∀ i j (hij : i ≤ j), (G i j hij).comp (φ i) = φ j) :
    Set.range (PrimeSpectrum.comap (inducedMap (B := B) (G := G) φ (Classical.arbitrary ι)))
      = ⋂ i, Set.range (PrimeSpectrum.comap (φ i)) := by
  -- regard the `B i` as `A`-algebras via `φ i`; then `G i j h` is `A`-linear by `hφ`
  letI : ∀ i, Algebra A (B i) := fun i => (φ i).toAlgebra
  have hmap : ∀ i, (algebraMap A (B i) : A →+* B i) = φ i := fun _ => rfl
  have hlin : ∀ (i j : ι) (hij : i ≤ j) (a : A), (G i j hij) ((φ i) a) = (φ j) a :=
    fun i j hij a => congrFun (congrArg DFunLike.coe (hφ i j hij)) a
  -- the `A`-algebra homomorphism version of `G i j h`
  let gm : ∀ i j, i ≤ j → B i →ₐ[A] B j := fun i j hij =>
    AlgHom.ofLinearMap
      { toFun := ⇑(G i j hij)
        map_add' := fun x y => map_add (G i j hij) x y
        map_smul' := fun a x => by
          simp only [Algebra.smul_def, map_mul]
          rw [show (G i j hij) ((algebraMap A (B i)) a) = (algebraMap A (B j)) a from ?_]
          · rfl
          · rw [hmap i, hmap j]
            exact hlin i j hij a }
      (map_one (G i j hij)) (fun x y => map_mul (G i j hij) x y)
  haveI : DirectedSystem B (fun i j h => gm i j h) := hds
  -- the induced map agrees with the structure map `A → colim_i B_i`
  have hpt : (inducedMap (B := B) (G := G) φ (Classical.arbitrary ι) :
        A →+* DirectLimit B (fun i j h => G i j h))
      = (algebraMap A (Lim (B := B) (g := gm)) :
        A →+* DirectLimit B (fun i j h => G i j h)) := by
    ext r
    show (DirectLimit.Ring.of B (fun i j h => G i j h) (Classical.arbitrary ι))
        ((φ (Classical.arbitrary ι)) r) = (algebraMap A (Lim (B := B) (g := gm))) r
    have halgdef : (algebraMap A (Lim (B := B) (g := gm))) r
        = (⟦⟨Classical.arbitrary ι,
            algebraMap A (B (Classical.arbitrary ι)) r⟩⟧ : Lim (B := B) (g := gm)) :=
      DirectLimit.algebraMap_def (G := B) (f := fun i j h => gm i j h)
        (Classical.arbitrary ι) r
    rw [halgdef]
    rfl
  have key : Set.range (PrimeSpectrum.comap (inducedMap (B := B) (G := G) φ (Classical.arbitrary ι)))
      = Set.range (PrimeSpectrum.comap (algebraMap A (Lim (B := B) (g := gm)))) := by
    show Set.range (PrimeSpectrum.comap (inducedMap (B := B) (G := G) φ (Classical.arbitrary ι) :
        A →+* DirectLimit B (fun i j h => G i j h)))
      = Set.range (PrimeSpectrum.comap (algebraMap A (Lim (B := B) (g := gm)) :
        A →+* DirectLimit B (fun i j h => G i j h)))
    exact congrArg (fun f => Set.range (PrimeSpectrum.comap f)) hpt
  rw [key]
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    exact Set.mem_iInter.mpr fun i =>
      (by simpa only [hmap] using
        range_comap_algebraMap_subset (B := B) (g := gm) p hp i)
  · intro p hp
    refine (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A)
      (S := Lim (B := B) (g := gm)) p).mp ?_
    exact nontrivial_tensor_lim (B := B) (g := gm) (p.asIdeal.ResidueField) fun i =>
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) (S := B i) p).mpr
        (by simpa only [hmap] using Set.mem_iInter.mp hp i)

set_option linter.style.haveILetI false in
/-- **Atiyah–Macdonald, Exercise 3.26.**  Let `(B_α, g_{αβ})` be a direct system of rings with
direct limit `B`, let `f_α : A → B_α` be ring homomorphisms satisfying `g_{αβ} ∘ f_α = f_β`, and
let `f : A → B` be the induced homomorphism.  Then `f^*(Spec B) = ⋂_α f_α^*(Spec B_α)`. -/
theorem solution {φ : ∀ i, A →+* B i}
    (hφ : ∀ i j (hij : i ≤ j), (G i j hij).comp (φ i) = φ j)
    {f : A →+* DirectLimit B (fun i j h => G i j h)}
    (hf : f = inducedMap (B := B) (G := G) φ (Classical.arbitrary ι)) :
    Set.range (PrimeSpectrum.comap f)
      = ⋂ i, Set.range (PrimeSpectrum.comap (φ i)) := by
  rw [hf]
  exact solution_induced (B := B) (G := G) hφ

end RingHomForm

end AtiyahMcdonald69.Ex_3_26

#print axioms AtiyahMcdonald69.Ex_3_26.solution
#print axioms AtiyahMcdonald69.Ex_3_26.solution_induced
#print axioms AtiyahMcdonald69.Ex_3_26.range_comap_algebraMap_eq_iInter
#print axioms AtiyahMcdonald69.Ex_3_26.nontrivial_tensor_lim
