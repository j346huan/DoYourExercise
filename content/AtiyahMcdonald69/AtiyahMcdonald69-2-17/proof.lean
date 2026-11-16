/-
Atiyah–Macdonald (1969), Chapter 2, Exercise 2.17 — formalization in Lean 4 / Mathlib.
-/
import Mathlib

/-!
# Atiyah–Macdonald, Exercise 2.17

*Statement* (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 2, Ex. 17):

> Let `(Mᵢ)ᵢ∈I` be a family of submodules of an `A`-module, such that for each pair of
> indices `i, j ∈ I` there exists `k ∈ I` such that `Mᵢ + Mⱼ ⊆ M_k`. Define `i ≤ j` to mean
> `Mᵢ ⊆ Mⱼ` and let `μᵢⱼ : Mᵢ → Mⱼ` be the embedding of `Mᵢ` in `Mⱼ`. Show that
> `lim Mᵢ = Σ Mᵢ = ∪ Mᵢ`. In particular, any `A`-module is the direct limit of its
> finitely generated submodules.

*Formal reading of the objects.*

* The index set is a set `S` of submodules of `N`; the order `i ≤ j ⟺ Mᵢ ⊆ Mⱼ` is the
  order inherited from `Submodule R N`. The pair condition `Mᵢ + Mⱼ ⊆ M_k` is exactly
  directedness of `S` for this order: `isDirectedOrder_iff_pairSup` below.
* `Σ Mᵢ` is `sum S := sSup S`, characterised as *the smallest submodule containing all
  `Mᵢ`* in `isLeast_sum`, matching AM's definition of the sum of submodules
  ("Operations on submodules"). `∪ Mᵢ` is `⋃ i, (Mᵢ : Set N)`.
* `lim Mᵢ` is Mathlib's `DirectLimit` of the direct system `sys : ∀ i j, i ≤ j → Mᵢ → Mⱼ`
  of the embeddings `μᵢⱼ`, i.e. exactly AM 2.14's construction (quotient of the direct sum
  by the relations `xᵢ = μᵢⱼ xᵢ`).
* `A` is a commutative ring `R`, `N` is an `R`-module.

*Two points of care.*

1. The order `i ≤ j` is *defined* as `Mᵢ ⊆ Mⱼ`, so the family is monotone by construction;
   `sys` is the resulting direct system and `instDirectedSystem` verifies axioms (1) and (2)
   of AM 2.14.
2. Nonemptiness of the index set is needed (AM's "directed set" is nonempty); without it the
   conclusion is false: for the empty family the union is `∅`, which is not even a
   submodule, while the sum is `{0}`. This is `empty_union_ne_sum`; the main theorems are
   therefore stated with `[Nonempty S]`.

Main output: `directLimitEquiv` (`lim Mᵢ ≃ₗ Σ Mᵢ`), together with the set-theoretic
identity `coe_sum_eq_iUnion` (`Σ Mᵢ = ∪ Mᵢ`), the universal property of the union
`existsUnique_lift`, the bundled form `atiyah_mcdonald_2_17`, and the "in particular"
statements `directLimit_fg` / `fg_sUnion_eq_univ`.

*Audit of the natural proof* (`.scratch/DoYourExercise/.../AtiyahMcdonald69-2-17`):
it uses "every finite sum of elements of the `Mᵢ` lies in one `M_k`" (here
`exists_mem_finset_sum`, and used in `unionSub.add_mem'`), AM 2.16 to get the canonical
map `lim Mᵢ → ∪ Mᵢ` (here `DirectLimit.Module.lift`, with `toSum_of` recording its
values), and AM 2.15 for injectivity. The last step is unnecessary for a *union*: the
canonical maps `Mᵢ → ∪ Mᵢ` are injective, so `toSum_eq_zero`/`toSum_injective` give
injectivity directly, without the elementwise criterion of 2.15. The other omission is
nonemptiness of `I`, recorded above.

Only style linters are disabled (`unusedSectionVars`, `unusedVariables` in the anonymous
`DirectedSystem` fields, and `style.haveILetI`, where `haveI` is needed for instance
resolution); no theorem is weakened.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace AtiyahMcdonald69.Ex_2_17

open Submodule

universe u v

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]

/-! ## The direct system of a family of submodules

The index type is a set `S` of submodules of `N`, ordered by inclusion. -/

/-- The transition maps `μᵢⱼ : Mᵢ → Mⱼ` of the direct system: for `i ≤ j` (that is,
`Mᵢ ⊆ Mⱼ`) the embedding of `Mᵢ` in `Mⱼ` (AM 2.17). -/
@[reducible] def sys {S : Set (Submodule R N)} :
    ∀ i j : S, i ≤ j → ↥(i : Submodule R N) →ₗ[R] ↥(j : Submodule R N) :=
  fun _ _ h => Submodule.inclusion h

/-- The transition maps are the embeddings of the members. -/
theorem coe_sys {S : Set (Submodule R N)} {i j : S} (h : i ≤ j)
    (x : ↥(i : Submodule R N)) :
    ((sys (S := S) i j h x : ↥(j : Submodule R N)) : N) = (x : N) :=
  Submodule.coe_inclusion h x

/-- The sum `Σ Mᵢ` of the family `S`: the smallest submodule containing all the members
(AM, "Operations on submodules"). -/
def sum (S : Set (Submodule R N)) : Submodule R N := sSup S

/-- Every member is contained in the sum. -/
theorem le_sum (S : Set (Submodule R N)) (i : S) : (i : Submodule R N) ≤ sum S :=
  le_sSup i.2

namespace Family

variable (S : Set (Submodule R N)) [Nonempty S] [IsDirectedOrder S]

/-- Axioms (1) and (2) of AM 2.14: the embeddings `μᵢⱼ` make the family a direct system. -/
instance instDirectedSystem :
    DirectedSystem (fun i : S => ↥(i : Submodule R N)) (sys (S := S) · · ·) where
  map_self := fun _ _ => rfl
  map_map := fun _ _ _ _ _ _ => rfl

/-! ## The union of a directed family is a submodule and equals the sum -/

/-- The union of a directed family of submodules is a submodule: a sum of two elements lies
in a member containing both members ("every finite sum of elements of the `Mᵢ` lies in one
`M_k`"). -/
def unionSub : Submodule R N where
  carrier := {x : N | ∃ i : S, x ∈ (i : Submodule R N)}
  zero_mem' :=
    ⟨Classical.arbitrary S, Submodule.zero_mem (Classical.arbitrary S : Submodule R N)⟩
  add_mem' := by
    rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, (k : Submodule R N).add_mem (hik hi) (hjk hj)⟩
  smul_mem' := by
    rintro a x ⟨i, hi⟩
    exact ⟨i, (i : Submodule R N).smul_mem a hi⟩

/-- Membership in the union. -/
theorem mem_unionSub_iff {x : N} : x ∈ unionSub S ↔ ∃ i : S, x ∈ (i : Submodule R N) :=
  Iff.rfl

/-- The union of a directed family of submodules is its sum. -/
theorem unionSub_eq_iSup : unionSub S = ⨆ i : S, (i : Submodule R N) := by
  refine le_antisymm ?_ (iSup_le fun i x hx => ⟨i, hx⟩)
  rintro x ⟨i, hi⟩
  exact le_iSup (fun j : S => (j : Submodule R N)) i hi

/-- The sum of a directed family is its union. -/
theorem sum_eq_iSup : sum S = ⨆ i : S, (i : Submodule R N) := sSup_eq_iSup' S

/-- `Σ Mᵢ = sSup S`. -/
theorem sum_eq_sSup : sum S = sSup S := rfl

/-- `Σ Mᵢ = ∪ Mᵢ` for a directed family of submodules. -/
theorem coe_sum_eq_iUnion :
    ((sum S : Submodule R N) : Set N) = ⋃ i : S, ((i : Submodule R N) : Set N) := by
  have h : sum S = unionSub S := by rw [sum_eq_iSup, unionSub_eq_iSup]
  rw [h]
  ext x
  rw [Set.mem_iUnion]
  exact mem_unionSub_iff S

/-- Membership in the sum: an element lies in the sum of a directed family of submodules if
and only if it lies in one member. -/
theorem mem_sum_iff {x : N} : x ∈ sum S ↔ ∃ i : S, x ∈ (i : Submodule R N) := by
  have h : sum S = unionSub S := by rw [sum_eq_iSup, unionSub_eq_iSup]
  rw [h]
  exact mem_unionSub_iff S

/-- AM's description of the sum: `Σ Mᵢ` is the smallest submodule containing all `Mᵢ`. -/
theorem isLeast_sum : IsLeast {T : Submodule R N | ∀ i : S, (i : Submodule R N) ≤ T} (sum S) :=
  ⟨fun i => le_sSup i.2, fun _ hT => sSup_le fun i hi => hT ⟨i, hi⟩⟩

/-- Every finite sum of elements of the members of a directed family lies in a single
member (the argument of the natural proof that `∪ Mᵢ` is a submodule). -/
theorem exists_mem_finset_sum (x : ∀ i : S, ↥(i : Submodule R N)) (t : Finset S) :
    ∃ k : S, (Finset.sum t fun i => ((x i : ↥(i : Submodule R N)) : N)) ∈
      (k : Submodule R N) := by
  classical
  induction t using Finset.induction with
  | empty =>
      refine ⟨Classical.arbitrary S, ?_⟩
      simp
  | insert a t ha ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨l, hal, hkl⟩ := exists_ge_ge a k
      refine ⟨l, ?_⟩
      rw [Finset.sum_insert ha]
      exact (l : Submodule R N).add_mem (hal (x a).2) (hkl hk)

/-! ## The direct limit of the family is the union -/

/-- The canonical map from the direct limit of a directed family of submodules to the sum
(equivalently, the union) of the family, obtained from the universal property of the direct
limit applied to the embeddings `Mᵢ ↪ Σ Mᵢ`. -/
noncomputable def toSum :
    DirectLimit (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) →ₗ[R] ↥(sum S) :=
  DirectLimit.Module.lift R S (fun i : S => ↥(i : Submodule R N)) (sys (S := S))
    (fun i => Submodule.inclusion (le_sum S i))
    (fun _ _ h x => Subtype.ext (by
      rw [Submodule.coe_inclusion, Submodule.coe_inclusion]
      exact coe_sys (R := R) h x))

/-- The canonical map to the sum is compatible with the maps `μᵢ` from the members. -/
@[simp] theorem toSum_of (i : S) (x : ↥(i : Submodule R N)) :
    toSum S (DirectLimit.Module.of R S (fun i : S => ↥(i : Submodule R N))
      (sys (S := S)) i x) = Submodule.inclusion (le_sum S i) x :=
  DirectLimit.Module.lift_of (g := fun i => Submodule.inclusion (le_sum S i))
    (Hg := fun _ _ h x => Subtype.ext (by
      rw [Submodule.coe_inclusion, Submodule.coe_inclusion]
      exact coe_sys (R := R) h x)) (i := i) (x := x)

/-- The canonical map from the direct limit to the sum is injective: on a member `Mᵢ` it is
the embedding of `Mᵢ` in `N`. (The natural proof derives injectivity from AM 2.15; for the
union the direct argument is simpler.) -/
theorem toSum_eq_zero {z : DirectLimit (fun i : S => ↥(i : Submodule R N)) (sys (S := S))}
    (hz : toSum S z = 0) : z = 0 := by
  obtain ⟨i, y, hzy⟩ := DirectLimit.exists_eq_mk (f := sys (S := S)) z
  subst hzy
  have hzy' : toSum S (DirectLimit.Module.of R S (fun i : S => ↥(i : Submodule R N))
      (sys (S := S)) i y) = 0 := hz
  have hy : (y : N) = 0 := by
    have h := congrArg (fun t : ↥(sum S) => (t : N)) hzy'
    rw [toSum_of, Submodule.coe_inclusion] at h
    exact h.trans (by simp)
  have hy0 : y = 0 := Subtype.ext hy
  change DirectLimit.Module.of R S (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) i y = 0
  rw [hy0, map_zero]

/-- The canonical map from the direct limit to the sum is injective. -/
theorem toSum_injective : Function.Injective (toSum S) := by
  intro x y hxy
  have h : toSum S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.1 (toSum_eq_zero S h)

/-- The canonical map from the direct limit to the sum is surjective: every element of the
sum lies in some member. -/
theorem toSum_surjective : Function.Surjective (toSum S) := by
  intro z
  obtain ⟨i, hi⟩ := (mem_sum_iff S).1 z.2
  refine ⟨DirectLimit.Module.of R S (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) i
    ⟨z.1, hi⟩, ?_⟩
  rw [toSum_of]
  exact Subtype.ext rfl

/-- **AM 2.17**: the direct limit of a directed family of submodules of `N` is the sum of
the family (which is the union of the family, `coe_sum_eq_iUnion`). -/
noncomputable def directLimitEquiv :
    DirectLimit (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) ≃ₗ[R] ↥(sum S) :=
  LinearEquiv.ofBijective (toSum S) ⟨toSum_injective S, toSum_surjective S⟩

/-- `directLimitEquiv` sends the class of `x ∈ Mᵢ` to `x`, i.e. it is the canonical map of
the direct limit followed by the embedding of `Mᵢ` in the sum. -/
theorem directLimitEquiv_of (i : S) (x : ↥(i : Submodule R N)) :
    directLimitEquiv S (DirectLimit.Module.of R S (fun i : S => ↥(i : Submodule R N))
      (sys (S := S)) i x) = Submodule.inclusion (le_sum S i) x :=
  toSum_of S i x

/-! ## The union satisfies the universal property of the direct limit -/

/-- **AM 2.17** via AM 2.16: the sum (= union) of the family, with the embeddings of the
members, satisfies the characterising property of the direct limit: every compatible family
of maps from the members factors uniquely through it. -/
theorem existsUnique_lift {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i : S, ↥(i : Submodule R N) →ₗ[R] P)
    (hg : ∀ i j (h : i ≤ j) x, g j (sys (S := S) i j h x) = g i x) :
    ∃! Φ : ↥(sum S) →ₗ[R] P, ∀ i, Φ ∘ₗ Submodule.inclusion (le_sum S i) = g i := by
  set F : DirectLimit (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) →ₗ[R] P :=
    DirectLimit.Module.lift R S (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) g hg
  set Φ : ↥(sum S) →ₗ[R] P := F.comp (directLimitEquiv S).symm.toLinearMap
  have hΦ : ∀ i, Φ ∘ₗ Submodule.inclusion (le_sum S i) = g i := by
    intro i
    ext x
    have hx : directLimitEquiv S (DirectLimit.Module.of R S
        (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) i x) =
        Submodule.inclusion (le_sum S i) x := directLimitEquiv_of S i x
    show F ((directLimitEquiv S).symm (Submodule.inclusion (le_sum S i) x)) = g i x
    rw [← hx, LinearEquiv.symm_apply_apply]
    exact DirectLimit.Module.lift_of (g := g) (Hg := hg) (i := i) (x := x)
  refine ⟨Φ, hΦ, ?_⟩
  intro Ψ hΨ
  ext z
  obtain ⟨i, hi⟩ := (mem_sum_iff S).1 z.2
  have hz : Submodule.inclusion (le_sum S i) ⟨z.1, hi⟩ = z := Subtype.ext rfl
  have h1 : Ψ (Submodule.inclusion (le_sum S i) ⟨z.1, hi⟩) = g i ⟨z.1, hi⟩ :=
    congrArg (fun L : ↥(i : Submodule R N) →ₗ[R] P => L ⟨z.1, hi⟩) (hΨ i)
  have h2 : Φ (Submodule.inclusion (le_sum S i) ⟨z.1, hi⟩) = g i ⟨z.1, hi⟩ :=
    congrArg (fun L : ↥(i : Submodule R N) →ₗ[R] P => L ⟨z.1, hi⟩) (hΦ i)
  rw [hz] at h1 h2
  rw [h1, h2]

/-- **AM 2.17**, bundled: for a nonempty directed family of submodules, the union is the sum
and the direct limit of the system of embeddings is the sum. -/
theorem atiyah_mcdonald_2_17 :
    ((sum S : Submodule R N) : Set N) = ⋃ i : S, ((i : Submodule R N) : Set N) ∧
    Nonempty (DirectLimit (fun i : S => ↥(i : Submodule R N)) (sys (S := S)) ≃ₗ[R]
      ↥(sum S)) :=
  ⟨coe_sum_eq_iUnion S, ⟨directLimitEquiv S⟩⟩

end Family

/-! ## The hypothesis of AM 2.17 -/

/-- The hypothesis of AM 2.17 — for each pair `i, j` there is `k` with `Mᵢ + Mⱼ ⊆ M_k` — is
exactly directedness of the family ordered by inclusion. `Mᵢ + Mⱼ` is `p ⊔ q`. -/
theorem isDirectedOrder_iff_pairSup (S : Set (Submodule R N)) :
    IsDirectedOrder S ↔ ∀ p ∈ S, ∀ q ∈ S, ∃ r ∈ S, p ⊔ q ≤ r := by
  constructor
  · intro h
    haveI : IsDirectedOrder S := h
    rintro p hp q hq
    obtain ⟨r, hpr, hqr⟩ := exists_ge_ge (⟨p, hp⟩ : S) (⟨q, hq⟩ : S)
    exact ⟨r.1, r.2, sup_le hpr hqr⟩
  · intro h
    refine ⟨fun p q => ?_⟩
    obtain ⟨r, hr, hle⟩ := h p.1 p.2 q.1 q.2
    exact ⟨⟨r, hr⟩, le_sup_left.trans hle, le_sup_right.trans hle⟩

/-- AM 2.17 under its literal hypothesis: if the family is nonempty and `Mᵢ + Mⱼ ⊆ M_k` for
some `k`, then `Σ Mᵢ = ∪ Mᵢ`. -/
theorem union_eq_sum_of_pairSup (S : Set (Submodule R N)) (hne : S.Nonempty)
    (h : ∀ p ∈ S, ∀ q ∈ S, ∃ r ∈ S, p ⊔ q ≤ r) :
    ((sSup S : Submodule R N) : Set N) = ⋃ i : S, ((i : Submodule R N) : Set N) := by
  haveI : IsDirectedOrder S := (isDirectedOrder_iff_pairSup S).2 h
  haveI : Nonempty S := hne.to_subtype
  exact Family.coe_sum_eq_iUnion S

/-! ## Nonemptiness of the index set is necessary -/

section EmptyCase

/-- For the empty family the hypothesis of AM 2.17 holds vacuously, but the union is `∅`,
which is not a submodule: the sum is `{0}`. So the conclusion `Σ Mᵢ = ∪ Mᵢ` fails, and the
nonemptiness hypothesis in the main theorems cannot be dropped. -/
theorem empty_union_ne_sum :
    ((sSup (∅ : Set (Submodule R N)) : Submodule R N) : Set N) ≠
      ⋃ i : (∅ : Set (Submodule R N)), ((i : Submodule R N) : Set N) := by
  intro h
  have h0 : (0 : N) ∈ ((sSup (∅ : Set (Submodule R N)) : Submodule R N) : Set N) :=
    (sSup (∅ : Set (Submodule R N))).zero_mem
  rw [h, Set.mem_iUnion] at h0
  obtain ⟨i, -⟩ := h0
  exact i.2

/-- The pair hypothesis of AM 2.17 is vacuous for the empty family: this is why
`empty_union_ne_sum` shows that nonemptiness of the index set is an essential hypothesis. -/
theorem empty_family_pairSup :
    ∀ p ∈ (∅ : Set (Submodule R N)), ∀ q ∈ (∅ : Set (Submodule R N)),
      ∃ r ∈ (∅ : Set (Submodule R N)), p ⊔ q ≤ r := by
  simp

end EmptyCase

/-! ## Finitely generated submodules

The last sentence of AM 2.17: every module is the direct limit of its finitely generated
submodules. -/

section FinitelyGenerated

instance instNonemptyFgIndex : Nonempty ↥{p : Submodule R N | p.FG} :=
  ⟨⟨⊥, Submodule.fg_bot⟩⟩

instance instIsDirectedFgIndex : IsDirectedOrder ↥{p : Submodule R N | p.FG} :=
  ⟨fun p q =>
    ⟨⟨p.1 ⊔ q.1, p.2.sup q.2⟩,
      show (p : Submodule R N) ≤ p.1 ⊔ q.1 from le_sup_left,
      show (q : Submodule R N) ≤ p.1 ⊔ q.1 from le_sup_right⟩⟩

/-- The finitely generated submodules sum to the whole module. -/
theorem fg_sSup_eq_top : (sSup {p : Submodule R N | p.FG}) = ⊤ := by
  rw [sSup_eq_iSup', ← top_le_iff]
  intro x _
  refine le_iSup (fun p : ↥{p : Submodule R N | p.FG} => (p : Submodule R N))
    ⟨Submodule.span R {x}, Submodule.fg_span (Set.finite_singleton x)⟩ ?_
  exact Submodule.subset_span (Set.mem_singleton x)

/-- The union of the finitely generated submodules of `N` is `N`. -/
theorem fg_sUnion_eq_univ :
    (⋃ p : ↥{p : Submodule R N | p.FG}, ((p : Submodule R N) : Set N)) = Set.univ := by
  rw [← Family.coe_sum_eq_iUnion (S := {p : Submodule R N | p.FG}), Family.sum_eq_sSup,
    fg_sSup_eq_top]
  simp

/-- **AM 2.17, "in particular"**: every module is the direct limit of the direct system of
its finitely generated submodules (with the inclusion maps). -/
theorem directLimit_fg :
    Nonempty (DirectLimit (fun p : ↥{p : Submodule R N | p.FG} => ↥(p : Submodule R N))
      (sys (S := {p : Submodule R N | p.FG})) ≃ₗ[R] N) := by
  refine ⟨?_⟩
  have e := Family.directLimitEquiv (S := {p : Submodule R N | p.FG})
  rw [Family.sum_eq_sSup, fg_sSup_eq_top] at e
  exact e.trans Submodule.topEquiv

/-- **AM 2.17, "in particular"**, bundled: the finitely generated submodules cover `N` and
their direct limit is `N`. -/
theorem atiyah_mcdonald_2_17_fg :
    (⋃ p : ↥{p : Submodule R N | p.FG}, ((p : Submodule R N) : Set N)) = Set.univ ∧
    Nonempty (DirectLimit (fun p : ↥{p : Submodule R N | p.FG} => ↥(p : Submodule R N))
      (sys (S := {p : Submodule R N | p.FG})) ≃ₗ[R] N) :=
  ⟨fg_sUnion_eq_univ, directLimit_fg⟩

end FinitelyGenerated

/-! ## Axiom check -/

#print axioms Family.directLimitEquiv
#print axioms Family.existsUnique_lift
#print axioms Family.atiyah_mcdonald_2_17
#print axioms union_eq_sum_of_pairSup
#print axioms directLimit_fg
#print axioms empty_union_ne_sum

end AtiyahMcdonald69.Ex_2_17
