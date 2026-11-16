/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 6.3 (p. 78)

## Statement in the book

> Let `M` be an `A`-module and let `N₁, N₂` be submodules of `M`. If `M/N₁` and `M/N₂`
> are Noetherian, so is `M/(N₁ ∩ N₂)`. Similarly with Artinian in place of Noetherian.

Both assertions hold: there is no false generalisation hidden in this exercise, so the
deliverable proves both affirmatively (`isNoetherian_quotient_inf`,
`isArtinian_quotient_inf`) and bundles them as `solution`.  As a bonus, the finite
generalisation recorded in the book's solution literature (finitely many submodules
`Nᵢ` with Noetherian, resp. Artinian, quotients) is proved as well
(`isNoetherian_quotient_finset_inf`, `isArtinian_quotient_finset_inf`); this is exactly
the form needed in Exercise 6.4(a).

## Two independent proofs

**Proof 1 (`quotientInfDiag`, …).**  The A-linear "diagonal" map

  `M/(N₁ ∩ N₂) → M/N₁ × M/N₂`,   `x + (N₁ ∩ N₂) ↦ (x + N₁, x + N₂)`

is injective (`quotientInfDiag_ker`).  A finite product of Noetherian (resp. Artinian)
modules is Noetherian (resp. Artinian), and every submodule of such a module is again
Noetherian (resp. Artinian).  Hence `M/(N₁ ∩ N₂)` is Noetherian (resp. Artinian).

**Proof 2 (`quotientIncl`, …, following the book's hint).**  The book's hint uses the
exact sequence

  `0 → N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂) → M/N₂ → 0`

(the printed hint is the same sequence with `N₁` and `N₂` interchanged), together with
the second isomorphism theorem, which identifies `N₂/(N₁ ∩ N₂)` with
`(N₁ + N₂)/N₁ ⊆ M/N₁`.  This is the route taken by the website's `proof.tex`.
Formalised here: `quotientIncl` and `quotientProjN₂` are the two maps,
`range_quotientIncl_eq_ker` proves exactness, `quotientInjN₁` is the injection
`N₂/(N₁ ∩ N₂) → M/N₁` (the content of the second isomorphism theorem), and
`isNoetherian_of_range_eq_ker` / `isArtinian_of_range_eq_ker` then yield the result.

## Source audit

The local OCR transcription of the 1969 scan
(`.scratch/reference/atiyah-macdonald-original.txt`) is truncated at Corollary 6.11 and
does **not** contain the Chapter 6 exercises, so the statement was cross-checked against
three independent restatements, which agree verbatim with the statement above:

* the LaTeX transcription of the book (`.scratch/dl/amcd.tex`, "Page 78, Exercise 6.3",
  which also records the hint `0 → N₁/(N₁∩N₂) → M/(N₁∩N₂) → M/N₁ → 0`);
* an independent solutions document (`.scratch/reference/atiyah-solutions.txt`, §6.3);
* a second independent solutions document (`.scratch/dl/carlson.txt`, §6.3).

All sources agree that the Noetherian *and* the Artinian versions are true.  The
infinite-intersection analogue is **not** part of the book's statement and is false in
general (for a `k`-vector space with basis `e₁, e₂, …` and `Nᵢ` spanned by all basis
vectors except `eᵢ`, every `M/Nᵢ ≅ k` but `⋂ᵢ Nᵢ = 0`, so `M/⋂ᵢ Nᵢ = M` is
infinite-dimensional); only the finite intersection is asserted below.
-/

import Mathlib

-- The hypotheses of Exercise 6.3 are instance-valued (`IsNoetherian`, `IsArtinian`), so
-- they are introduced with `haveI` inside the proofs below; this is the intended use.
set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_6_3

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ## Proof 1: the diagonal embedding `M/(N₁ ∩ N₂) → M/N₁ × M/N₂` -/

/-- The A-linear map `M/(N₁ ∩ N₂) → M/N₁ × M/N₂` sending `x + (N₁ ∩ N₂)` to
`(x + N₁, x + N₂)`.  It is induced from the product of the two quotient maps, which
vanishes on `N₁ ∩ N₂`. -/
noncomputable def quotientInfDiag (N₁ N₂ : Submodule A M) :
    (M ⧸ (N₁ ⊓ N₂)) →ₗ[A] ((M ⧸ N₁) × (M ⧸ N₂)) :=
  (N₁ ⊓ N₂).liftQ ((Submodule.mkQ N₁).prod (Submodule.mkQ N₂)) (by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ])

/-- The kernel of the diagonal map is trivial. -/
lemma quotientInfDiag_ker (N₁ N₂ : Submodule A M) :
    LinearMap.ker (quotientInfDiag N₁ N₂) = ⊥ := by
  rw [quotientInfDiag]
  refine (N₁ ⊓ N₂).ker_liftQ_eq_bot ((Submodule.mkQ N₁).prod (Submodule.mkQ N₂)) ?_ ?_
  rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]

/-- The diagonal map `M/(N₁ ∩ N₂) → M/N₁ × M/N₂` is injective. -/
lemma quotientInfDiag_injective (N₁ N₂ : Submodule A M) :
    Function.Injective (quotientInfDiag N₁ N₂) :=
  LinearMap.ker_eq_bot.mp (quotientInfDiag_ker N₁ N₂)

/-! ## Exercise 6.3 -/

/-- **Atiyah–Macdonald, Exercise 6.3, Noetherian part.**
Let `M` be an `A`-module and `N₁, N₂ ⊆ M` submodules.  If `M/N₁` and `M/N₂` are
Noetherian `A`-modules, then so is `M/(N₁ ∩ N₂)`. -/
theorem isNoetherian_quotient_inf (N₁ N₂ : Submodule A M)
    (h₁ : IsNoetherian A (M ⧸ N₁)) (h₂ : IsNoetherian A (M ⧸ N₂)) :
    IsNoetherian A (M ⧸ (N₁ ⊓ N₂)) := by
  haveI := h₁
  haveI := h₂
  exact isNoetherian_of_injective (quotientInfDiag N₁ N₂) (quotientInfDiag_injective N₁ N₂)

/-- **Atiyah–Macdonald, Exercise 6.3, Artinian part.**
Let `M` be an `A`-module and `N₁, N₂ ⊆ M` submodules.  If `M/N₁` and `M/N₂` are
Artinian `A`-modules, then so is `M/(N₁ ∩ N₂)`. -/
theorem isArtinian_quotient_inf (N₁ N₂ : Submodule A M)
    (h₁ : IsArtinian A (M ⧸ N₁)) (h₂ : IsArtinian A (M ⧸ N₂)) :
    IsArtinian A (M ⧸ (N₁ ⊓ N₂)) := by
  haveI := h₁
  haveI := h₂
  exact isArtinian_of_injective (quotientInfDiag N₁ N₂) (quotientInfDiag_injective N₁ N₂)

/-- **Exercise 6.3 as a single assertion**: the Noetherian and the Artinian statements. -/
theorem solution :
    (∀ (N₁ N₂ : Submodule A M), IsNoetherian A (M ⧸ N₁) → IsNoetherian A (M ⧸ N₂) →
      IsNoetherian A (M ⧸ (N₁ ⊓ N₂))) ∧
    (∀ (N₁ N₂ : Submodule A M), IsArtinian A (M ⧸ N₁) → IsArtinian A (M ⧸ N₂) →
      IsArtinian A (M ⧸ (N₁ ⊓ N₂))) :=
  ⟨fun _ _ h₁ h₂ => isNoetherian_quotient_inf _ _ h₁ h₂,
   fun _ _ h₁ h₂ => isArtinian_quotient_inf _ _ h₁ h₂⟩

/-! ## Proof 2: the book's hint, via the exact sequence
`0 → N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂) → M/N₂ → 0` -/

/-- The first map of the exact sequence: `N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂)`, induced by the
inclusion `N₂ ⊆ M`. -/
noncomputable def quotientIncl (N₁ N₂ : Submodule A M) :
    (N₂ ⧸ (N₁ ⊓ N₂).comap N₂.subtype) →ₗ[A] (M ⧸ (N₁ ⊓ N₂)) :=
  ((N₁ ⊓ N₂).comap N₂.subtype).liftQ (((N₁ ⊓ N₂).mkQ).comp N₂.subtype) (by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ])

/-- The second map of the exact sequence: `M/(N₁ ∩ N₂) → M/N₂`, induced by the
identity of `M` (it is well defined because `N₁ ∩ N₂ ≤ N₂`). -/
noncomputable def quotientProjN₂ (N₁ N₂ : Submodule A M) :
    (M ⧸ (N₁ ⊓ N₂)) →ₗ[A] (M ⧸ N₂) :=
  (N₁ ⊓ N₂).liftQ (Submodule.mkQ N₂) (by
    rw [Submodule.ker_mkQ]
    exact inf_le_right)

/-- The injection `N₂/(N₁ ∩ N₂) → M/N₁` induced by the inclusion `N₂ ⊆ M`.  Its
existence is the content of the second isomorphism theorem,
`N₂/(N₁ ∩ N₂) ≅ (N₁ + N₂)/N₁ ⊆ M/N₁`. -/
noncomputable def quotientInjN₁ (N₁ N₂ : Submodule A M) :
    (N₂ ⧸ (N₁ ⊓ N₂).comap N₂.subtype) →ₗ[A] (M ⧸ N₁) :=
  ((N₁ ⊓ N₂).comap N₂.subtype).liftQ ((Submodule.mkQ N₁).comp N₂.subtype) (by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.comap_mono inf_le_left)

lemma quotientIncl_apply (N₁ N₂ : Submodule A M) (x : ↥N₂) :
    quotientIncl N₁ N₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : M) := rfl

lemma quotientProjN₂_apply (N₁ N₂ : Submodule A M) (x : M) :
    quotientProjN₂ N₁ N₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

lemma quotientInjN₁_apply (N₁ N₂ : Submodule A M) (x : ↥N₂) :
    quotientInjN₁ N₁ N₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : M) := rfl

/-- The map `N₂/(N₁ ∩ N₂) → M/N₁` is injective: an element of `N₂` mapping into `N₁`
lies in `N₁ ∩ N₂`. -/
lemma quotientInjN₁_ker (N₁ N₂ : Submodule A M) :
    LinearMap.ker (quotientInjN₁ N₁ N₂) = ⊥ := by
  rw [quotientInjN₁]
  refine ((N₁ ⊓ N₂).comap N₂.subtype).ker_liftQ_eq_bot _ ?_ ?_
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  intro x hx
  exact ⟨hx, x.2⟩

/-- **Exactness** of `0 → N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂) → M/N₂ → 0`: the image of the
first map is the kernel of the second.  (Injectivity of the first map is
`quotientInjN₁_ker`, transported along the second isomorphism theorem; surjectivity of
the second map is not needed.) -/
lemma range_quotientIncl_eq_ker (N₁ N₂ : Submodule A M) :
    LinearMap.range (quotientIncl N₁ N₂) = LinearMap.ker (quotientProjN₂ N₁ N₂) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      rw [LinearMap.mem_ker, quotientIncl_apply, quotientProjN₂_apply,
        Submodule.Quotient.mk_eq_zero]
      exact y.2
  · intro hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.mem_ker, quotientProjN₂_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, by rw [quotientIncl_apply]⟩

/-- **Exercise 6.3, Noetherian part**, second proof: the book's hint via the exact
sequence `0 → N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂) → M/N₂ → 0`. -/
theorem isNoetherian_quotient_inf_exact (N₁ N₂ : Submodule A M)
    (h₁ : IsNoetherian A (M ⧸ N₁)) (h₂ : IsNoetherian A (M ⧸ N₂)) :
    IsNoetherian A (M ⧸ (N₁ ⊓ N₂)) := by
  haveI := h₁
  haveI := h₂
  haveI : IsNoetherian A (N₂ ⧸ (N₁ ⊓ N₂).comap N₂.subtype) :=
    isNoetherian_of_injective (quotientInjN₁ N₁ N₂)
      (LinearMap.ker_eq_bot.mp (quotientInjN₁_ker N₁ N₂))
  exact isNoetherian_of_range_eq_ker (quotientIncl N₁ N₂) (quotientProjN₂ N₁ N₂)
    (range_quotientIncl_eq_ker N₁ N₂)

/-- **Exercise 6.3, Artinian part**, second proof: the book's hint via the exact
sequence `0 → N₂/(N₁ ∩ N₂) → M/(N₁ ∩ N₂) → M/N₂ → 0`. -/
theorem isArtinian_quotient_inf_exact (N₁ N₂ : Submodule A M)
    (h₁ : IsArtinian A (M ⧸ N₁)) (h₂ : IsArtinian A (M ⧸ N₂)) :
    IsArtinian A (M ⧸ (N₁ ⊓ N₂)) := by
  haveI := h₁
  haveI := h₂
  haveI : IsArtinian A (N₂ ⧸ (N₁ ⊓ N₂).comap N₂.subtype) :=
    isArtinian_of_injective (quotientInjN₁ N₁ N₂)
      (LinearMap.ker_eq_bot.mp (quotientInjN₁_ker N₁ N₂))
  exact isArtinian_of_range_eq_ker (quotientIncl N₁ N₂) (quotientProjN₂ N₁ N₂)
    (range_quotientIncl_eq_ker N₁ N₂)

/-! ## Finite-intersection generalisation

Not part of the book's text: if finitely many submodules `Nᵢ` have Noetherian
(resp. Artinian) quotients, then so does `M/(⋂ᵢ Nᵢ)`.  Only the *finite* intersection is
asserted (see the module docstring for a counterexample to the infinite version). -/

/-- Finite-intersection generalisation of Exercise 6.3, Noetherian part. -/
theorem isNoetherian_quotient_finset_inf {ι : Type*} (s : Finset ι)
    (N : ι → Submodule A M) (h : ∀ i ∈ s, IsNoetherian A (M ⧸ N i)) :
    IsNoetherian A (M ⧸ (s.inf N)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.inf_empty]
      infer_instance
  | insert a s ha ih =>
      rw [Finset.inf_insert]
      exact isNoetherian_quotient_inf (N a) (s.inf N) (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Finite-intersection generalisation of Exercise 6.3, Artinian part. -/
theorem isArtinian_quotient_finset_inf {ι : Type*} (s : Finset ι)
    (N : ι → Submodule A M) (h : ∀ i ∈ s, IsArtinian A (M ⧸ N i)) :
    IsArtinian A (M ⧸ (s.inf N)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.inf_empty]
      infer_instance
  | insert a s ha ih =>
      rw [Finset.inf_insert]
      exact isArtinian_quotient_inf (N a) (s.inf N) (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## Non-vacuity check

The Artinian statement genuinely uses its hypotheses: `ℤ` itself is not Artinian, while
`ℤ/2` and `ℤ/3` are, so the theorem produces the Artinian module `ℤ/6`. -/

example : IsArtinian ℤ (ℤ ⧸ (Ideal.span {(2 : ℤ)} ⊓ Ideal.span {(3 : ℤ)})) :=
  isArtinian_quotient_inf _ _ inferInstance inferInstance

/-! ## Axiom check

The exports below must depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular no `sorryAx`. -/

#print axioms isNoetherian_quotient_inf
#print axioms isArtinian_quotient_inf
#print axioms solution
#print axioms isNoetherian_quotient_inf_exact
#print axioms isArtinian_quotient_inf_exact
#print axioms isNoetherian_quotient_finset_inf
#print axioms isArtinian_quotient_finset_inf

end AtiyahMcdonald69.Ex_6_3
