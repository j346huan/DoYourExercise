/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 7
(Noetherian rings), Exercise 15, page 86.

**Textbook statement** (recovered from `.scratch/dl/amcd.tex`,
"Page 86, Exercise 7.15", and cross-checked against
`.scratch/reference/atiyah-solutions.txt`, `7.15`, and the natural-language
solution in `.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-7-15/proof.tex`):

  "Let `A` be a Noetherian local ring, `𝔪` its maximal ideal and `k` its residue
   field, and let `M` be a finitely generated `A`-module.  Then the following are
   equivalent:
     (i)   `M` is free;
     (ii)  `M` is flat;
     (iii) the mapping of `𝔪 ⊗ M` into `A ⊗ M` is injective;
     (iv)  `Tor₁^A(k, M) = 0`."

(The local LaTeX transcription prints `Tor_i^A(k,M)`; the other two local sources,
and the book's own hint for (iv) ⇒ (i) — which uses only the exact sequence
`0 → k⊗E → k⊗F → k⊗M → 0` — identify this as `Tor₁`.  We formalize `Tor₁`.)

Formalization choices, spelled out because (iv) mentions the derived functor `Tor₁`.

* `𝔪 := IsLocalRing.maximalIdeal A`, `k := IsLocalRing.ResidueField A`.
* Condition (iii) is stated *literally* as injectivity of the `A`-linear map
  `𝔪 ⊗[A] M → A ⊗[A] M` induced by `𝔪 ↪ A` (`residueTensorMap`).
* Condition (iv) needs `Tor₁^A(k, M)`.  Mathlib has the *abstract* left derived
  functor `CategoryTheory.Tor C n : C ⥤ C ⥤ C` for a monoidal abelian category `C`
  with projective resolutions (`Mathlib/CategoryTheory/Monoidal/Tor.lean`), but that
  file states "for now we have almost nothing to say about it": it does not compute
  `Tor` on modules and does not even prove `Tor ≅ Tor'`, so it gives no usable
  `Tor₁^A(k, M)`.  We therefore use the standard value on the two-term projective
  presentation of `k`: applying the long exact Tor sequence to
  `0 → 𝔪 → A → k → 0` and using `Tor₁^A(A, M) = 0` (`A` is free, hence projective)
  gives `Tor₁^A(k, M) ≅ ker(𝔪 ⊗ M → A ⊗ M)` — exactly the book's computation for
  (iii) ⇒ (iv).  We therefore *define* `torOne M := ker(𝔪 ⊗ M → A ⊗ M)` and
  condition (iv) as `torOne M = ⊥`.
  Because the definition is a model and not the functor itself, we do not stop
  there: `torOne_eq_bot_iff_lTensor_ker` *proves*, for an arbitrary free
  presentation `0 → E → F → M → 0`, that `torOne M = ⊥` is equivalent to
  injectivity of `k ⊗ E → k ⊗ F`, which is the form of `Tor₁^A(k,M) = 0` that
  the book actually uses in (iv) ⇒ (i).  Both directions of that equivalence are
  proved; the "double limit" comparison is the zigzag lemma
  `lTensor_injective_of_exact_of_exact_of_rTensor_injective`.

Main results:
* `exercise_7_15` — the four conditions are equivalent, proved along the book's
  own chain (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i).
* `exercise_7_15_iff` — the same content as a plain conjunction of the pairwise
  equivalences.
* `free_iff_flat`, `flat_iff_injectiveResidueTensorMap`,
  `injectiveResidueTensorMap_iff_torOne_eq_bot`, `torOne_eq_bot_iff_free` — the
  individual equivalences.
* `torOne_eq_bot_iff_lTensor_ker` (and `..._subtype`) — `Tor₁(k,M) = 0` in the
  presentation form `k ⊗ E → k ⊗ F` injective, for an arbitrary free presentation
  `0 → E → F → M → 0`; proved in both directions, so the model `torOne` is
  presentation-independent.
* `free_of_torOne_eq_bot_via_hint` — the book's hint for (iv) ⇒ (i) formalized
  end to end (basis of `M/𝔪M` lifted to a presentation, `k ⊗ E = 0`, Nakayama).
* `free_of_flat_of_isLocalRing` — (ii) ⇒ (i) does not need Noetherian.
* `injectiveResidueTensorMap_iff_maximalIdealTensorMul` — (iii) is the
  injectivity of `𝔪 ⊗ M → M`, `a ⊗ m ↦ a • m` (`maximalIdealTensorMul_tmul`),
  read through the canonical isomorphism `A ⊗[A] M ≃ M`.
* `residueTensorMap_tmul`, `mem_torOne_iff` — the explicit form of the map of
  (iii) and of the elements of `Tor₁`.

Note on the two uses of Mathlib in the hard direction: `free_of_injectiveResidueTensorMap`
cites `Module.free_of_maximalIdeal_rTensor_injective` (Mathlib's formalization of
(iii) ⇒ (i)), and `free_of_torOne_eq_bot_via_hint` cites
`Module.free_of_lTensor_residueField_injective` (Mathlib's formalization of the
last step of the book's hint: `k ⊗ E = 0` + Nakayama).  Everything else — the
statement, the model of `Tor₁`, the presentation independence, the assembly of
the equivalences — is proved here.

Verification: `/opt/lean/bin/lean -DwarningAsError=true answer.lean`;
`#print axioms` at the end shows only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nakayama

open scoped TensorProduct

-- `Module.Free`, `Module.Flat`, `Module.Finite` … are `Prop`-valued classes; `haveI` is
-- the idiomatic way to use a hypothesis of such a type as an instance.
set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_7_15

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-! ### The four conditions -/

/-- The `A`-linear map `𝔪 ⊗[A] M → A ⊗[A] M` of condition (iii). -/
noncomputable def residueTensorMap (M : Type*) [AddCommGroup M] [Module A M] :
    IsLocalRing.maximalIdeal A ⊗[A] M →ₗ[A] A ⊗[A] M :=
  (IsLocalRing.maximalIdeal A).subtype.rTensor M

/-- Condition (iii): the mapping of `𝔪 ⊗ M` into `A ⊗ M` is injective. -/
def InjectiveResidueTensorMap (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  Function.Injective (residueTensorMap (A := A) M)

/-- The multiplication map `𝔪 ⊗[A] M → M`, `a ⊗ m ↦ a • m`.  Under the canonical
identification `A ⊗[A] M ≃ M` it is the map of condition (iii). -/
noncomputable def maximalIdealTensorMul (M : Type*) [AddCommGroup M] [Module A M] :
    IsLocalRing.maximalIdeal A ⊗[A] M →ₗ[A] M :=
  (TensorProduct.lid A M).toLinearMap.comp (residueTensorMap (A := A) M)

/-- `Tor₁^A(k, M)`, computed from the two-term free presentation
`0 → 𝔪 → A → k → 0` of the residue field: the kernel of
`𝔪 ⊗[A] M → A ⊗[A] M`. -/
noncomputable def torOne (M : Type*) [AddCommGroup M] [Module A M] :
    Submodule A (IsLocalRing.maximalIdeal A ⊗[A] M) :=
  LinearMap.ker (residueTensorMap (A := A) M)

/-- Condition (iv): `Tor₁^A(k, M) = 0`. -/
def TorOneVanishes (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  torOne (A := A) M = ⊥

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The map of condition (iii) on simple tensors: it is induced by `𝔪 ↪ A`. -/
lemma residueTensorMap_tmul (a : IsLocalRing.maximalIdeal A) (m : M) :
    residueTensorMap (A := A) M (a ⊗ₜ[A] m) = (a : A) ⊗ₜ[A] m := by
  simp [residueTensorMap]

/-- The elements of `Tor₁^A(k, M)` are exactly the elements of `𝔪 ⊗[A] M` that die
in `A ⊗[A] M`, i.e. the kernel of the map of condition (iii). -/
lemma mem_torOne_iff (x : IsLocalRing.maximalIdeal A ⊗[A] M) :
    x ∈ torOne (A := A) M ↔ residueTensorMap (A := A) M x = 0 :=
  LinearMap.mem_ker

lemma maximalIdealTensorMul_tmul (a : IsLocalRing.maximalIdeal A) (m : M) :
    maximalIdealTensorMul (A := A) M (a ⊗ₜ[A] m) = (a : A) • m := by
  simp [maximalIdealTensorMul, residueTensorMap]

/-- Injectivity of `𝔪 ⊗ M → A ⊗ M` is injectivity of the multiplication map
`𝔪 ⊗ M → M`: the canonical isomorphism `A ⊗[A] M ≃ M` carries one to the other. -/
theorem injectiveResidueTensorMap_iff_maximalIdealTensorMul :
    InjectiveResidueTensorMap (A := A) M ↔
      Function.Injective (maximalIdealTensorMul (A := A) M) := by
  constructor
  · intro h x y hxy
    exact h ((TensorProduct.lid A M).injective hxy)
  · intro h x y hxy
    exact h (by simp [maximalIdealTensorMul, hxy])

/-- (iii) ⇔ (iv): in the model `Tor₁^A(k,M) = ker(𝔪 ⊗ M → A ⊗ M)` this is the
book's long exact sequence computation. -/
theorem injectiveResidueTensorMap_iff_torOne_eq_bot :
    InjectiveResidueTensorMap (A := A) M ↔ TorOneVanishes (A := A) M :=
  LinearMap.ker_eq_bot.symm

/-! ### The implications -/

omit [IsLocalRing A] in
/-- (i) ⇒ (ii): a free module is flat. -/
theorem flat_of_free (h : Module.Free A M) : Module.Flat A M := by
  haveI := h
  exact inferInstance

/-- (ii) ⇒ (iii): flatness makes `𝔪 ↪ A` stay injective after tensoring with `M`. -/
theorem injectiveResidueTensorMap_of_flat (h : Module.Flat A M) :
    InjectiveResidueTensorMap (A := A) M := by
  haveI := h
  exact Module.Flat.rTensor_preserves_injective_linearMap (R := A) (M := M)
    (N := IsLocalRing.maximalIdeal A) (P := A) (IsLocalRing.maximalIdeal A).subtype
    Subtype.val_injective

/-- (iii) ⇒ (i), over a Noetherian ring.  The book's argument: lift a `k`-basis of
`M/𝔪M` to generators `x₁,…,xₙ` of `M` (Nakayama, (2.8)), let `E` be the kernel of
`Aⁿ ↠ M`; then `E ⊆ 𝔪Aⁿ`, `E` is finitely generated (Noetherian), and `k ⊗ E = 0`
forces `E = 0`.  `Module.free_of_maximalIdeal_rTensor_injective` is Mathlib's
formalization of this argument (its proof goes through `k ⊗ E = 0` and Nakayama,
exactly as in the book's hint for (iv) ⇒ (i)). -/
theorem free_of_injectiveResidueTensorMap [IsNoetherianRing A] [Module.Finite A M]
    (h : InjectiveResidueTensorMap (A := A) M) : Module.Free A M := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact Module.free_of_maximalIdeal_rTensor_injective h

/-- (ii) ⇒ (i) with **no** Noetherian hypothesis: a finitely generated flat module
over a local ring is free.  This records that the Noetherian hypothesis in the
exercise is used only for (iii) ⇒ (i) and (iv) ⇒ (i) (to get `E` finitely
generated / `M` finitely presented). -/
theorem free_of_flat_of_isLocalRing [Module.Finite A M] (h : Module.Flat A M) :
    Module.Free A M := by
  haveI := h
  exact Module.free_of_flat_of_isLocalRing

/-- (iv) ⇒ (i). -/
theorem free_of_torOne_eq_bot [IsNoetherianRing A] [Module.Finite A M]
    (h : TorOneVanishes (A := A) M) : Module.Free A M :=
  free_of_injectiveResidueTensorMap (A := A) (M := M)
    ((injectiveResidueTensorMap_iff_torOne_eq_bot (A := A) (M := M)).mpr h)

/-- (i) ⇒ (iv). -/
theorem torOne_eq_bot_of_free (h : Module.Free A M) : TorOneVanishes (A := A) M :=
  (injectiveResidueTensorMap_iff_torOne_eq_bot (A := A) (M := M)).mp
    (injectiveResidueTensorMap_of_flat (A := A) (M := M) (flat_of_free h))

/-! ### `Tor₁(k, M)` in presentation form

The definition `torOne` above uses the two-term presentation `0 → 𝔪 → A → k → 0` of
the residue field.  `Tor` can also be computed from a presentation of `M`: for an
exact sequence `0 → E → F → M → 0` with `F` free, `Tor₁^A(k, M)` is
`ker(k ⊗ E → k ⊗ F)`.  The next theorem proves that the two models agree, i.e. that
the model `torOne` really is `Tor₁^A(k, M)` in the form in which the book uses it.
Both directions are proved: the forward one is the "double limit" comparison
(`lTensor_injective_of_exact_of_exact_of_rTensor_injective`, tensor the two exact
sequences with each other and chase), the backward one runs the book's hint for
(iv) ⇒ (i) (`Module.free_of_lTensor_residueField_injective`). -/
section Presentation

variable {E F : Type*} [AddCommGroup E] [Module A E] [AddCommGroup F] [Module A F]

theorem torOne_eq_bot_iff_lTensor_ker [IsNoetherianRing A] [Module.Finite A M]
    [Module.Free A F] [Module.Finite A F] [Module.Finite A E]
    (f : E →ₗ[A] F) (g : F →ₗ[A] M) (hex : Function.Exact f g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) :
    TorOneVanishes (A := A) M ↔
      Function.Injective (f.lTensor (IsLocalRing.ResidueField A)) := by
  constructor
  · intro h
    exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (f₁ := (IsLocalRing.maximalIdeal A).subtype) (f₂ := (IsLocalRing.maximalIdeal A).mkQ)
      (g₁ := f) (g₂ := g) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
      hex hsurj
      ((injectiveResidueTensorMap_iff_torOne_eq_bot (A := A) (M := M)).mpr h)
      (Module.Flat.lTensor_preserves_injective_linearMap (R := A) (M := A) f hinj)
  · intro h
    haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
    have hfree : Module.Free A M :=
      Module.free_of_lTensor_residueField_injective f g hsurj hex h
    exact (injectiveResidueTensorMap_iff_torOne_eq_bot (A := A) (M := M)).mp
      (injectiveResidueTensorMap_of_flat (A := A) (M := M) (flat_of_free hfree))



/-- The presentation form of `Tor₁^A(k,M) = 0` for the kernel of a given surjection
`F ↠ M` with `F` free: this is precisely the shape `0 → k⊗E → k⊗F → k⊗M → 0` in
which the book uses (iv). -/
theorem torOne_eq_bot_iff_lTensor_ker_subtype [IsNoetherianRing A] [Module.Finite A M]
    [Module.Free A F] [Module.Finite A F]
    (g : F →ₗ[A] M) (hsurj : Function.Surjective g) :
    TorOneVanishes (A := A) M ↔
      Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField A)
        (LinearMap.ker g).subtype) := by
  haveI : Module.Finite A (LinearMap.ker g) := inferInstance
  exact torOne_eq_bot_iff_lTensor_ker (LinearMap.ker g).subtype g
    (LinearMap.exact_subtype_ker_map g) (fun _ _ hh => Subtype.ext hh) hsurj


set_option maxHeartbeats 500000 in
/-- The book's own hint for (iv) ⇒ (i), formalized end to end.  Choose `x₁,…,xₙ ∈ M`
whose images `1 ⊗ xᵢ` in `k ⊗[A] M ≅ M/𝔪M` form a `k`-basis; Nakayama ((2.8), here
`IsLocalRing.span_eq_top_of_tmul_eq_basis`) says they generate `M`.  Let
`φ : Aⁿ ↠ M` be the induced surjection and `E = ker φ`.  Then `0 → E → Aⁿ → M → 0`
is exact and `Tor₁(k,M) = 0` says `k ⊗ E → k ⊗ Aⁿ` is injective; both `k ⊗ Aⁿ` and
`k ⊗ M` are the `k`-vector space spanned by the `1 ⊗ xᵢ` and `1 ⊗ φ` is onto, so
`k ⊗ E = 0`, hence `E = 0` by Nakayama (`E` being finitely generated because `A`
is Noetherian), and `M ≅ Aⁿ`.  In Mathlib this final step is exactly
`Module.free_of_lTensor_residueField_injective`. -/
theorem free_of_torOne_eq_bot_via_hint [IsNoetherianRing A] [Module.Finite A M]
    (h : TorOneVanishes (A := A) M) : Module.Free A M := by
  classical
  let b := Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M)
  have hsurj : Function.Surjective (TensorProduct.mk A (IsLocalRing.ResidueField A) M 1) :=
    TensorProduct.mk_surjective A M (IsLocalRing.ResidueField A) Ideal.Quotient.mk_surjective
  choose x hx using fun i => hsurj (b i)
  have hsp : Submodule.span A (Set.range x) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (R := A) x b (fun i => by simpa using hx i)
  let φ : (Fin (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M)) →₀ A) →ₗ[A] M := Finsupp.linearCombination A x
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  haveI : Module.Finite A (LinearMap.ker φ) := inferInstance
  exact Module.free_of_lTensor_residueField_injective (M := ↥(LinearMap.ker φ))
    (N := (Fin (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M)) →₀ A)) (P := M)
    (LinearMap.ker φ).subtype φ hφ (LinearMap.exact_subtype_ker_map φ)
    ((torOne_eq_bot_iff_lTensor_ker_subtype φ hφ).mp h)

end Presentation

/-! ### Assembly: the four conditions are equivalent -/

theorem free_iff_flat [IsNoetherianRing A] [Module.Finite A M] :
    Module.Free A M ↔ Module.Flat A M :=
  ⟨flat_of_free,
   fun h => free_of_injectiveResidueTensorMap
     (injectiveResidueTensorMap_of_flat (A := A) (M := M) h)⟩

theorem flat_iff_injectiveResidueTensorMap [IsNoetherianRing A] [Module.Finite A M] :
    Module.Flat A M ↔ InjectiveResidueTensorMap (A := A) M :=
  ⟨fun h => injectiveResidueTensorMap_of_flat (A := A) (M := M) h,
   fun h => flat_of_free (free_of_injectiveResidueTensorMap h)⟩

theorem injectiveResidueTensorMap_iff_free [IsNoetherianRing A] [Module.Finite A M] :
    InjectiveResidueTensorMap (A := A) M ↔ Module.Free A M :=
  ⟨fun h => free_of_injectiveResidueTensorMap h,
   fun h => injectiveResidueTensorMap_of_flat (A := A) (M := M) (flat_of_free h)⟩

theorem torOne_eq_bot_iff_free [IsNoetherianRing A] [Module.Finite A M] :
    TorOneVanishes (A := A) M ↔ Module.Free A M :=
  ⟨fun h => free_of_torOne_eq_bot h, torOne_eq_bot_of_free⟩

/-- **Atiyah–Macdonald, Chapter 7, Exercise 15.**  For a Noetherian local ring
`(A, 𝔪, k)` and a finitely generated `A`-module `M`, the four conditions are
equivalent. -/
theorem exercise_7_15 [IsNoetherianRing A] [Module.Finite A M] :
    [Module.Free A M, Module.Flat A M, InjectiveResidueTensorMap (A := A) M,
      TorOneVanishes (A := A) M].TFAE := by
  tfae_have 1 → 2 := fun h => flat_of_free (A := A) (M := M) h
  tfae_have 2 → 3 := fun h => injectiveResidueTensorMap_of_flat (A := A) (M := M) h
  tfae_have 3 → 4 := fun h => (injectiveResidueTensorMap_iff_torOne_eq_bot (A := A) (M := M)).mp h
  tfae_have 4 → 1 := fun h => free_of_torOne_eq_bot_via_hint (A := A) (M := M) h
  tfae_finish

/-- The content of the exercise as a plain conjunction of the pairwise
equivalences (equivalent to `exercise_7_15`). -/
theorem exercise_7_15_iff [IsNoetherianRing A] [Module.Finite A M] :
    (Module.Free A M ↔ Module.Flat A M) ∧
      (Module.Flat A M ↔ InjectiveResidueTensorMap (A := A) M) ∧
      (InjectiveResidueTensorMap (A := A) M ↔ TorOneVanishes (A := A) M) ∧
      (TorOneVanishes (A := A) M ↔ Module.Free A M) :=
  ⟨free_iff_flat, flat_iff_injectiveResidueTensorMap,
    injectiveResidueTensorMap_iff_torOne_eq_bot, torOne_eq_bot_iff_free⟩

end AtiyahMcdonald69.Ex_7_15

#print axioms AtiyahMcdonald69.Ex_7_15.exercise_7_15
#print axioms AtiyahMcdonald69.Ex_7_15.exercise_7_15_iff
#print axioms AtiyahMcdonald69.Ex_7_15.free_of_injectiveResidueTensorMap
#print axioms AtiyahMcdonald69.Ex_7_15.torOne_eq_bot_iff_lTensor_ker
#print axioms AtiyahMcdonald69.Ex_7_15.free_of_flat_of_isLocalRing
#print axioms AtiyahMcdonald69.Ex_7_15.free_of_torOne_eq_bot_via_hint
#print axioms AtiyahMcdonald69.Ex_7_15.torOne_eq_bot_iff_lTensor_ker_subtype
