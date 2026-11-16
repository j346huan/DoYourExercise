/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra*, Exercise 3.14

**Statement (book, p. 45).** Let `M` be an `A`-module and `𝔞` an ideal of `A`. Suppose that
`M_𝔪 = 0` for all maximal ideals `𝔪 ⊇ 𝔞`. Prove that `M = 𝔞M`.

Localizations are formalized as `LocalizedModule 𝔪.primeCompl M`, the localization of the
module `M` at the submonoid `A \ 𝔪`; `M = 𝔞M` is the statement `𝔞 • ⊤ = ⊤` for the
submodule `𝔞M ≤ M`.

Contents.

* `solution` — the exercise exactly as stated in the book.  The book imposes no finiteness
  hypothesis on `M`, and none is needed: the hypothesis at a maximal ideal `𝔪` containing
  `𝔞` says that every `x : M` is killed by some `s ∉ 𝔪`, i.e. `Ann(x) ⊄ 𝔪`; hence
  `𝔞 + Ann(x) = ⊤` and `x = a • x` for some `a ∈ 𝔞`.
* `subsingleton_of_localized_subsingleton` — the local criterion for vanishing
  (`Corollary 3.9` of the book) for *arbitrary* modules: if `M_𝔪 = 0` for all maximal
  ideals `𝔪`, then `M = 0`.  The book states it for finitely generated modules, via
  `Proposition 3.8`; only the weaker Proposition 3.8 needs finite generation, and the
  criterion itself does not.
* `subsingleton_of_forall_subsingleton_localized_of_le_annihilator` — the same criterion
  restricted to the maximal ideals containing a fixed ideal `𝔟 ≤ Ann(M)`.
* `exists_smul_eq_zero_of_subsingleton_localized` — `Proposition 3.8`: for a finitely
  generated `M`, `M_S = 0` means that some `s ∈ S` kills `M`.
* `le_annihilator_quotient`, `subsingleton_localized_quotient` — the quotient step of the
  book's argument: `𝔞` annihilates `M/𝔞M` (so that `M/𝔞M` is an `A/𝔞`-module, via the
  Mathlib instance `Module (A ⧸ 𝔞) (M ⧸ 𝔞 • ⊤)`), and `(M/𝔞M)_𝔪 = M_𝔪/𝔞M_𝔪 = 0`
  whenever `M_𝔪 = 0`.
* `solution_via_quotient` — the book's route, for arbitrary `M`: `M/𝔞M` is annihilated by
  `𝔞` and all of its localizations at maximal ideals above `𝔞` vanish, so `M/𝔞M = 0` by
  the local criterion.
* `solution_fg` — the finitely generated variant often quoted for this exercise.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_3_14

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ### Elementary preliminaries -/

/-- The annihilator ideal of a single element `x` of an `A`-module `M`, namely
`Ann(x) = {a : A | a • x = 0}`. -/
def annIdeal (x : M) : Ideal A := (Submodule.span A {x}).annihilator

theorem mem_annIdeal {x : M} {a : A} : a ∈ annIdeal x ↔ a • x = 0 :=
  Submodule.mem_annihilator_span_singleton (R := A) (M := M) x a

theorem annIdeal_ne_top {x : M} (hx : x ≠ 0) : (annIdeal (A := A) x) ≠ ⊤ := by
  intro h
  have h1 : (1 : A) ∈ annIdeal x := (Ideal.eq_top_iff_one _).1 h
  have hone : (1 : A) • x = 0 := mem_annIdeal.1 h1
  rw [one_smul] at hone
  exact hx hone

/-- If `x = a • x` with `a ∈ 𝔞`, then `x ∈ 𝔞M`. -/
theorem mem_smul_top_of_smul_eq_self {𝔞 : Ideal A} {x : M} {a : A}
    (ha : a ∈ 𝔞) (hx : a • x = x) : x ∈ 𝔞 • (⊤ : Submodule A M) := by
  rw [← hx]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-! ### The exercise -/

/-- **Exercise 3.14** (Atiyah–Macdonald).  Let `M` be an `A`-module and `𝔞` an ideal of
`A`.  If `M_𝔪 = 0` for every maximal ideal `𝔪 ⊇ 𝔞`, then `M = 𝔞M`. -/
theorem solution (𝔞 : Ideal A)
    (h : ∀ (m : Ideal A) [m.IsMaximal], 𝔞 ≤ m →
      Subsingleton (LocalizedModule m.primeCompl M)) :
    𝔞 • (⊤ : Submodule A M) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  -- For every `x` the ideal `𝔞 + Ann(x)` is the whole ring.
  have hsup : 𝔞 ⊔ annIdeal x = ⊤ := by
    by_contra hne
    -- Otherwise some maximal ideal `𝔪` contains it, and the hypothesis kills `x` there.
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmax : m.IsMaximal := hm
    have h𝔞m : 𝔞 ≤ m := le_trans le_sup_left hle
    have hsub : Subsingleton (LocalizedModule m.primeCompl M) := h m h𝔞m
    rw [LocalizedModule.subsingleton_iff] at hsub
    -- hence there is `s ∉ 𝔪` with `s • x = 0`, i.e. `s ∈ Ann(x) ≤ 𝔪`: contradiction
    obtain ⟨s, hs, hsx⟩ := hsub x
    exact hs (hle (Submodule.mem_sup_right ((mem_annIdeal).2 hsx)))
  -- Decompose `1 = a + b` with `a ∈ 𝔞` and `b ∈ Ann(x)`.
  have h1 : (1 : A) ∈ 𝔞 ⊔ annIdeal x := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hbx : b • x = 0 := (mem_annIdeal).1 hb
  have hx : a • x = x := by
    have hsum : (a + b) • x = x := by rw [hab, one_smul]
    rw [add_smul, hbx, add_zero] at hsum
    exact hsum
  exact mem_smul_top_of_smul_eq_self ha hx

/-! ### The local criterion for vanishing (`Corollary 3.9`)

The book's `Corollary 3.9` assumes `M` finitely generated and is deduced from
`Proposition 3.8`.  The criterion itself holds for arbitrary modules: a nonzero element
`x` has a proper annihilator, which is contained in a maximal ideal. -/

/-- **Corollary 3.9** (local criterion for vanishing): if `M_𝔪 = 0` for every maximal
ideal `𝔪`, then `M = 0`.  No finiteness hypothesis is needed. -/
theorem subsingleton_of_localized_subsingleton
    (h : ∀ (m : Ideal A) [m.IsMaximal], Subsingleton (LocalizedModule m.primeCompl M)) :
    Subsingleton M := by
  refine (subsingleton_iff_forall_eq 0).2 fun x ↦ ?_
  by_contra hx
  -- a nonzero `x` has a proper annihilator, hence one contained in a maximal ideal
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (annIdeal (A := A) x) (annIdeal_ne_top hx)
  have hmax : m.IsMaximal := hm
  have hsub : Subsingleton (LocalizedModule m.primeCompl M) := h m
  rw [LocalizedModule.subsingleton_iff] at hsub
  obtain ⟨s, hs, hsx⟩ := hsub x
  exact hs (hle ((mem_annIdeal).2 hsx))

/-- The local criterion for vanishing, restricted to the maximal ideals containing a fixed
ideal `𝔟 ≤ Ann(M)`; this is the form used for the quotient `M/𝔞M` below. -/
theorem subsingleton_of_forall_subsingleton_localized_of_le_annihilator
    (𝔟 : Ideal A) (h𝔟 : 𝔟 ≤ Module.annihilator A M)
    (h : ∀ (m : Ideal A) [m.IsMaximal], 𝔟 ≤ m →
      Subsingleton (LocalizedModule m.primeCompl M)) :
    Subsingleton M := by
  -- `Ann(M) ≤ Ann(x)` for every `x : M`
  have hb : ∀ x : M, 𝔟 ≤ annIdeal x := fun x ↦ le_trans h𝔟 (by
    rw [annIdeal, ← Submodule.annihilator_top]
    exact Submodule.annihilator_mono le_top)
  refine (subsingleton_iff_forall_eq 0).2 fun x ↦ ?_
  by_contra hx
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (annIdeal (A := A) x) (annIdeal_ne_top hx)
  have hmax : m.IsMaximal := hm
  have hsub : Subsingleton (LocalizedModule m.primeCompl M) := h m (le_trans (hb x) hle)
  rw [LocalizedModule.subsingleton_iff] at hsub
  obtain ⟨s, hs, hsx⟩ := hsub x
  exact hs (hle ((mem_annIdeal).2 hsx))

/-! ### `Proposition 3.8` (needs finite generation) -/

/-- **Proposition 3.8**: if `M` is a finitely generated `A`-module and `M_S = 0`, then some
`s ∈ S` annihilates `M`.  This is where finite generation enters the book's treatment. -/
theorem exists_smul_eq_zero_of_subsingleton_localized [Module.Finite A M] {S : Submonoid A}
    (hS : Subsingleton (LocalizedModule S M)) : ∃ s ∈ S, ∀ x : M, s • x = 0 := by
  classical
  -- `M` is spanned by a finite set
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.1 (Module.finite_def.1 ‹Module.Finite A M›)
  -- every element of `M` is killed by some element of `S`
  choose r hrS hr using fun x : M => (LocalizedModule.subsingleton_iff.1 hS) x
  refine ⟨∏ x ∈ hTfin.toFinset, r x, Submonoid.prod_mem S fun x _ ↦ hrS x, ?_⟩
  -- the product kills every generator, hence all of `M`
  intro y
  have hspan : Submodule.span A ((hTfin.toFinset : Finset M) : Set M) = ⊤ := by
    rw [hTfin.coe_toFinset, hTspan]
  have hy : y ∈ Submodule.span A ((hTfin.toFinset : Finset M) : Set M) := by
    rw [hspan]; exact Submodule.mem_top
  have hle : Submodule.span A ((hTfin.toFinset : Finset M) : Set M) ≤
      LinearMap.ker (LinearMap.lsmul A M (∏ x ∈ hTfin.toFinset, r x)) := by
    rw [Submodule.span_le]
    intro z hz
    refine LinearMap.mem_ker.2 ?_
    rw [LinearMap.lsmul_apply]
    have hz' : z ∈ hTfin.toFinset := hz
    rw [← Finset.mul_prod_erase _ (fun x ↦ r x) hz', mul_smul, smul_comm, hr z, smul_zero]
  exact LinearMap.mem_ker.1 (hle hy)

/-! ### The quotient step `(M/𝔞M)_𝔪 = M_𝔪/𝔞M_𝔪 = 0` -/

/-- The ideal `𝔞` annihilates the quotient module `M/𝔞M`; this is what lets `M/𝔞M` be
regarded as an `A/𝔞`-module (Mathlib turns `Module.IsTorsionBySet R M I` into a module
structure over `R ⧸ I`). -/
theorem le_annihilator_quotient (𝔞 : Ideal A) :
    𝔞 ≤ Module.annihilator A (M ⧸ 𝔞 • (⊤ : Submodule A M)) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (𝔞 • (⊤ : Submodule A M)) x
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

-- `M/𝔞M` is a module over `A ⧸ 𝔞` (Mathlib instance): this is the book's "regard `M/𝔞M`
-- as an `A/𝔞`-module".
example (𝔞 : Ideal A) : Module (A ⧸ 𝔞) (M ⧸ 𝔞 • (⊤ : Submodule A M)) := inferInstance

/-- If `M_𝔪 = 0` then `(M/𝔞M)_𝔪 = 0`. -/
theorem subsingleton_localized_quotient {S : Submonoid A} (𝔞 : Ideal A)
    (hS : Subsingleton (LocalizedModule S M)) :
    Subsingleton (LocalizedModule S (M ⧸ 𝔞 • (⊤ : Submodule A M))) := by
  rw [LocalizedModule.subsingleton_iff] at hS ⊢
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (𝔞 • (⊤ : Submodule A M)) x
  obtain ⟨s, hs, hsy⟩ := hS y
  exact ⟨s, hs, by
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, hsy, Submodule.Quotient.mk_zero]⟩

/-- The formal counterpart of the book's "every maximal ideal of `A/𝔞` has the form
`𝔪/𝔞`": every maximal ideal of `A ⧸ 𝔞` is the image of a maximal ideal of `A` containing
`𝔞`.  (This is not needed in the proof below — there the same information is used in the
equivalent form `𝔞 ≤ Ann(M/𝔞M)` — but it records the ideal-theoretic step of the book's
argument.) -/
theorem exists_maximal_map_quotient (𝔞 : Ideal A) (m : Ideal (A ⧸ 𝔞)) (hm : m.IsMaximal) :
    ∃ M : Ideal A, M.IsMaximal ∧ 𝔞 ≤ M ∧ M.map (Ideal.Quotient.mk 𝔞) = m := by
  have hmax : m.IsMaximal := hm
  refine ⟨m.comap (Ideal.Quotient.mk 𝔞), ?_, ?_, ?_⟩
  · exact Ideal.comap_isMaximal_of_surjective (f := Ideal.Quotient.mk 𝔞)
      Ideal.Quotient.mk_surjective
  · intro a ha
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact m.zero_mem
  · exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective m

/-- **Exercise 3.14**, by the book's route: `M/𝔞M` is annihilated by `𝔞` (i.e. it is a
module over `A/𝔞`), and all its localizations at maximal ideals above `𝔞` vanish because
they are localizations of `M_𝔪`; the local criterion gives `M/𝔞M = 0`, that is, `M = 𝔞M`.

Passing to `A/𝔞` explicitly would use `exists_maximal_map_quotient` and the identification
of `(A ⧸ 𝔞)`-localization at `𝔪/𝔞` with `A`-localization at `𝔪`; we instead use the
equivalent annihilator formulation `𝔞 ≤ Ann(M/𝔞M)`, which is exactly the module-theoretic
content of "`M/𝔞M` is an `A/𝔞`-module". -/
theorem solution_via_quotient (𝔞 : Ideal A)
    (h : ∀ (m : Ideal A) [m.IsMaximal], 𝔞 ≤ m →
      Subsingleton (LocalizedModule m.primeCompl M)) :
    𝔞 • (⊤ : Submodule A M) = ⊤ := by
  -- the ideal `𝔞` annihilates `M/𝔞M`
  have hann : 𝔞 ≤ Module.annihilator A (M ⧸ 𝔞 • (⊤ : Submodule A M)) :=
    le_annihilator_quotient 𝔞
  have hzero : Subsingleton (M ⧸ 𝔞 • (⊤ : Submodule A M)) :=
    subsingleton_of_forall_subsingleton_localized_of_le_annihilator (M := M ⧸ 𝔞 • ⊤) 𝔞 hann
      fun m hm h𝔞m ↦ subsingleton_localized_quotient 𝔞 (h m h𝔞m)
  rwa [Submodule.Quotient.subsingleton_iff] at hzero

/-! ### The finitely generated variant -/

/-- The finitely generated variant of the exercise (a formal consequence of `solution`,
which needs no finiteness hypothesis). -/
theorem solution_fg [Module.Finite A M] (𝔞 : Ideal A)
    (h : ∀ (m : Ideal A) [m.IsMaximal], 𝔞 ≤ m →
      Subsingleton (LocalizedModule m.primeCompl M)) :
    𝔞 • (⊤ : Submodule A M) = ⊤ :=
  solution 𝔞 h

end AtiyahMcdonald69.Ex_3_14

/-! ### Axiom audit

Every export below depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); there is no `sorry`, no `admit`, no custom axiom and no assumed conclusion
anywhere in this file. -/

#print axioms AtiyahMcdonald69.Ex_3_14.solution
#print axioms AtiyahMcdonald69.Ex_3_14.solution_via_quotient
#print axioms AtiyahMcdonald69.Ex_3_14.solution_fg
#print axioms AtiyahMcdonald69.Ex_3_14.subsingleton_of_localized_subsingleton
#print axioms AtiyahMcdonald69.Ex_3_14.subsingleton_of_forall_subsingleton_localized_of_le_annihilator
#print axioms AtiyahMcdonald69.Ex_3_14.exists_smul_eq_zero_of_subsingleton_localized
#print axioms AtiyahMcdonald69.Ex_3_14.subsingleton_localized_quotient
#print axioms AtiyahMcdonald69.Ex_3_14.le_annihilator_quotient
#print axioms AtiyahMcdonald69.Ex_3_14.exists_maximal_map_quotient
#print axioms AtiyahMcdonald69.Ex_3_14.mem_smul_top_of_smul_eq_self
