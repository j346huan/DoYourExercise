/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 7.19.

The exercise (p. 86) reads: let `𝔞` be an ideal in the Noetherian ring `A`, and let
`𝔞 = ⋂_{i=1}^{r} 𝔟_i = ⋂_{j=1}^{s} 𝔠_j` be two minimal decompositions of `𝔞` as intersections of
irreducible ideals.  Prove that `r = s` and that, possibly after re-indexing the `𝔠_j`,
`r(𝔟_i) = r(𝔠_i)` for all `i`.  State and prove an analogous result for modules.

Here "minimal" means irredundant (`𝔟_i` is not implied by the other components), and several
components may share a radical `r(𝔟_i)` — determining those multiplicities is exactly the content.

Main declarations of this file:

* `ex_7_19` : the indexed ideal form quoted above, concluding `∃ e : Fin r ≃ Fin s,
  ∀ i, (b i).radical = (c (e i)).radical`.
* `ex_7_19_ideal` : the same statement for `Finset`s of ideals, giving `s.card = t.card` and the
  number of components with any prescribed radical as an invariant.
* `multiplicity_eq`, `card_eq` : the analogous results for submodules of a Noetherian module, with
  `r_M(N) = (N : M).radical` (Atiyah–Macdonald, Chapter 4, Exercise 20).
* `card_eq_of_infIrred_decomposition` : the number of components of an irredundant intersection of
  irreducible submodules depends only on the intersection.

Proof outline.  In a Noetherian module every irreducible submodule is primary, so an irredundant
intersection of irreducibles is an irredundant intersection of primaries.  Saturating at the
complement of a prime `p` cuts out exactly those components whose radical is contained in `p`;
this makes the *cumulative* number of components with radical `≤ p` an invariant of the submodule
being decomposed.  The replacement (exchange) lemma for irredundant decompositions into
inf-irreducibles shows that the number of components of such a decomposition of a fixed submodule is
invariant as well, which gives every cumulative count; a finite-poset argument converts cumulative
counts into counts.
-/
import Mathlib

open Submodule

open scoped Classical

namespace AtiyahMcdonald69.Ex_7_19

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### The radical of a submodule -/

/-- `r_M(N)`, the radical of the submodule `N` in `M` (Atiyah–Macdonald, Chapter 4, Exercise 20). -/
abbrev rad (N : Submodule R M) : Ideal R := (N.colon Set.univ).radical

/-! ### Saturation

For a submonoid `S` of `R`, the `S`-saturation of `N` is the set of `x` with `s • x ∈ N` for some
`s ∈ S`.  It is a submodule, it commutes with finite intersections, and it leaves a primary
submodule alone unless `S` meets its radical. -/

/-- The saturation of a submodule `N` with respect to a submonoid `S`. -/
def sat (S : Submonoid R) (N : Submodule R M) : Submodule R M where
  carrier := {x | ∃ s ∈ S, s • x ∈ N}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, S.mul_mem ha hb, ?_⟩
    have : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b x]
    rw [this]
    exact N.add_mem (N.smul_mem b hx) (N.smul_mem a hy)
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    exact ⟨a, ha, by rw [smul_comm]; exact N.smul_mem c hx⟩

@[simp]
theorem mem_sat {S : Submonoid R} {N : Submodule R M} {x : M} :
    x ∈ sat S N ↔ ∃ s ∈ S, s • x ∈ N := Iff.rfl

theorem le_sat (S : Submonoid R) (N : Submodule R M) : N ≤ sat S N :=
  fun _ hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem sat_mono (S : Submonoid R) {N N' : Submodule R M} (h : N ≤ N') : sat S N ≤ sat S N' :=
  fun _ hx => by obtain ⟨s, hs, hx⟩ := hx; exact ⟨s, hs, h hx⟩

theorem sat_top (S : Submonoid R) : sat S (⊤ : Submodule R M) = ⊤ :=
  le_antisymm le_top (le_sat S ⊤)

theorem sat_inf (S : Submonoid R) (N N' : Submodule R M) : sat S (N ⊓ N') = sat S N ⊓ sat S N' := by
  refine le_antisymm (le_inf (sat_mono S inf_le_left) (sat_mono S inf_le_right)) ?_
  rintro x ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩
  refine ⟨a * b, S.mul_mem ha hb, ?_⟩
  have h1 : (a * b) • x = b • (a • x) := by rw [mul_smul, smul_comm]
  have h2 : (a * b) • x = a • (b • x) := by rw [mul_smul]
  exact ⟨by rw [h1]; exact N.smul_mem b hx, by rw [h2]; exact N'.smul_mem a hy⟩

theorem sat_finsetInf {ι : Type*} (S : Submonoid R) (t : Finset ι) (f : ι → Submodule R M) :
    sat S (t.inf f) = t.inf fun i => sat S (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [sat_top]
  | insert a t ha ih => rw [Finset.inf_insert, sat_inf, Finset.inf_insert, ih]

/-- Saturation does not change a primary submodule whose radical avoids `S`. -/
theorem sat_eq_self_of_isPrimary {S : Submonoid R} {Q : Submodule R M} (hQ : Q.IsPrimary)
    (h : ∀ s ∈ S, s ∉ rad Q) : sat S Q = Q := by
  refine le_antisymm (fun x hx => ?_) (le_sat S Q)
  obtain ⟨s, hs, hx⟩ := hx
  exact (hQ.mem_or_mem hx).resolve_right (h s hs)

/-- Saturation turns a primary submodule into the whole module when `S` meets its radical. -/
theorem sat_eq_top_of_mem_radical {S : Submonoid R} {Q : Submodule R M} {r : R} (hr : r ∈ S)
    (hrQ : r ∈ rad Q) : sat S Q = ⊤ := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrQ
  refine le_antisymm le_top fun x _ => ?_
  exact ⟨r ^ n, Submonoid.pow_mem S hr n, Submodule.mem_colon.mp hn x trivial⟩

/-! ### Which components survive saturation at a prime -/

section Surviving

variable {α : Type*}

/-- Selector form of the infimum over a finset. -/
theorem Finset.inf_ite [SemilatticeInf α] [OrderTop α] (t : Finset (Submodule R M))
    (p : Submodule R M → Prop) [DecidablePred p] (f : Submodule R M → α) :
    t.inf (fun i => if p i then f i else ⊤) = (t.filter p).inf f := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.inf_insert, ih, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.inf_insert]
    · rw [top_inf_eq]

end Surviving

/-- Saturating an irredundant primary decomposition at the complement of a prime `p` cuts out
exactly the components whose radical is contained in `p`. -/
theorem sat_primeCompl_inf {p : Ideal R} [hp : p.IsPrime] {t : Finset (Submodule R M)}
    (hQ : ∀ q ∈ t, q.IsPrimary) :
    sat p.primeCompl (t.inf id) = (t.filter fun q => rad q ≤ p).inf id := by
  classical
  rw [sat_finsetInf]
  trans t.inf (fun q => if rad q ≤ p then q else ⊤)
  · refine Finset.inf_congr rfl ?_
    intro q hq
    by_cases h : rad q ≤ p
    · rw [if_pos h]
      refine sat_eq_self_of_isPrimary (hQ q hq) ?_
      intro s hs hs'
      exact (Ideal.mem_primeCompl_iff.mp hs) (h hs')
    · rw [if_neg h]
      obtain ⟨r, hrq, hrp⟩ := Set.not_subset.mp h
      exact sat_eq_top_of_mem_radical (Ideal.mem_primeCompl_iff.mpr hrp) hrq
  · exact Finset.inf_ite t (fun q => rad q ≤ p) id

/-! ### Passing to a quotient

Submodules of `M ⧸ W` correspond to submodules of `M` containing `W`.  We record the facts we
need: `map (mkQ W)` does not change inf-irreducibility of a submodule containing `W`, the image of
`W` is `⊥`, and `map (mkQ W)` commutes with finite infima of submodules containing `W`. -/

theorem eq_of_comap_mkQ_eq {W : Submodule R M} {X Y : Submodule R (M ⧸ W)}
    (h : comap (mkQ W) X = comap (mkQ W) Y) : X = Y := by
  conv_lhs => rw [← map_comap_eq_self (f := mkQ W) (q := X) (by simp)]
  conv_rhs => rw [← map_comap_eq_self (f := mkQ W) (q := Y) (by simp)]
  rw [h]

theorem map_mkQ_self (W : Submodule R M) : map (mkQ W) W = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero W).mpr hy

theorem map_mkQ_finsetInf {W : Submodule R M} {ι : Type*} {t : Finset ι}
    {V : ι → Submodule R M} (hW : ∀ v ∈ t, W ≤ V v) :
    map (mkQ W) (t.inf V) = t.inf (fun v => map (mkQ W) (V v)) := by
  refine eq_of_comap_mkQ_eq ?_
  calc comap (mkQ W) (map (mkQ W) (t.inf V))
      = W ⊔ t.inf V := comap_map_mkQ W _
    _ = t.inf V := sup_eq_right.mpr (Finset.le_inf hW)
    _ = t.inf (fun v => W ⊔ V v) :=
        Finset.inf_congr rfl fun v hv => (sup_eq_right.mpr (hW v hv)).symm
    _ = t.inf (fun v => comap (mkQ W) (map (mkQ W) (V v))) :=
        Finset.inf_congr rfl fun v _ => (comap_map_mkQ W (V v)).symm
    _ = comap (mkQ W) (t.inf (fun v => map (mkQ W) (V v))) :=
        (Submodule.comap_finsetInf _ _ _).symm

theorem InfIrred.map_mkQ {W v : Submodule R M} (hWv : W ≤ v) (h : InfIrred v) :
    InfIrred (map (mkQ W) v) := by
  constructor
  · intro hmax
    have h1 : map (mkQ W) v = ⊤ := hmax.eq_top
    have h2 : v = ⊤ := by
      have h3 : W ⊔ v = ⊤ := (map_mkQ_eq_top W v).mp h1
      rwa [sup_eq_right.mpr hWv] at h3
    exact h.1 (isMax_iff_eq_top.mpr h2)
  · intro b c hbc
    set B := comap (mkQ W) b with hB
    set C := comap (mkQ W) c with hC
    have hB' : map (mkQ W) B = b := map_comap_eq_self (by simp)
    have hC' : map (mkQ W) C = c := map_comap_eq_self (by simp)
    have hBC : B ⊓ C = v := by
      calc B ⊓ C = comap (mkQ W) b ⊓ comap (mkQ W) c := rfl
        _ = comap (mkQ W) (b ⊓ c) := (comap_inf b c (mkQ W)).symm
        _ = comap (mkQ W) (map (mkQ W) v) := by rw [hbc]
        _ = W ⊔ v := comap_map_mkQ W v
        _ = v := sup_eq_right.mpr hWv
    rcases h.2 hBC with h' | h'
    · left; rw [← hB', h']
    · right; rw [← hC', h']

/-! ### The replacement (exchange) lemma -/

theorem Finset.map_inf_of_injective {M' : Type*} [AddCommGroup M'] [Module R M']
    {ι : Type*} (φ : M →ₗ[R] M') (hφ : Function.Injective φ) {t : Finset ι}
    (ht : t.Nonempty) (V : ι → Submodule R M) :
    map φ (t.inf V) = t.inf (fun v => map φ (V v)) := by
  classical
  induction t using Finset.induction with
  | empty => exact absurd ht (by simp)
  | insert a t ha ih =>
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [Finset.inf_insert, Submodule.map_inf φ hφ, Finset.inf_insert, ih hne]

theorem Finset.inf_inf_const {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (V : ι → Submodule R M)
    (N : Submodule R M) : t.inf (fun v => V v ⊓ N) = t.inf V ⊓ N := by
  classical
  induction t using Finset.induction with
  | empty => exact absurd ht (by simp)
  | insert a t ha ih =>
    rw [Finset.inf_insert]
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [ih hne, Finset.inf_insert]
      simp [inf_assoc, inf_left_comm]

/-- `map (LinearMap.prod (mkQ u₁) (mkQ u₂))` of a submodule contained in `u₂` lands in the
product of its first coordinate with `⊥`. -/
theorem map_prod_mkQ_inf {u₁ u₂ v : Submodule R M} (hv : v ≤ u₂) :
    map (LinearMap.prod (mkQ u₁) (mkQ u₂)) v = (map (mkQ u₁) v).prod (⊥ : Submodule R (M ⧸ u₂)) := by
  refine le_antisymm ?_ ?_
  · rintro ⟨x, y⟩ hxy
    obtain ⟨z, hz, hzφ⟩ := mem_map.mp hxy
    have hx : (mkQ u₁) z = x := by simpa using congrArg Prod.fst hzφ
    have hy : (mkQ u₂) z = y := by simpa using congrArg Prod.snd hzφ
    refine mem_prod.mpr ⟨mem_map.mpr ⟨z, hz, hx⟩, ?_⟩
    rw [mem_bot, ← hy]
    exact (Submodule.Quotient.mk_eq_zero u₂).mpr (hv hz)
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hxA, hy⟩ := mem_prod.mp hxy
    rw [mem_bot] at hy
    obtain ⟨z, hz, hzx⟩ := mem_map.mp hxA
    refine mem_map.mpr ⟨z, hz, ?_⟩
    have hz2 : (mkQ u₂) z = 0 := (Submodule.Quotient.mk_eq_zero u₂).mpr (hv hz)
    have hz1 : (mkQ u₁) z = x := by simpa using hzx
    rw [show (LinearMap.prod (mkQ u₁) (mkQ u₂)) z = ((mkQ u₁) z, (mkQ u₂) z) from rfl,
      hz1, hz2, hy.symm]

/-- Emerton's replacement lemma at the bottom of a module. -/
theorem exists_inf_eq_bot {u₁ u₂ : Submodule R M} (hu : u₁ ⊓ u₂ = ⊥) (hu₁ : InfIrred u₁)
    {ι : Type*} {t : Finset ι} {V : ι → Submodule R M} (htne : t.Nonempty) (ht : t.inf V = ⊥) :
    ∃ v ∈ t, V v ⊓ u₂ = ⊥ := by
  classical
  have hX : t.inf (fun v => V v ⊓ u₂) = ⊥ := by
    rw [Finset.inf_inf_const htne, ht, bot_inf_eq]
  set φ : M →ₗ[R] (M ⧸ u₁) × (M ⧸ u₂) := LinearMap.prod (mkQ u₁) (mkQ u₂) with hφdef
  have hker : φ.ker = ⊥ := by
    rw [hφdef, LinearMap.ker_prod, ker_mkQ, ker_mkQ, hu]
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker
  have hmap : t.inf (fun v => map φ (V v ⊓ u₂)) = ⊥ := by
    rw [← Finset.map_inf_of_injective φ hinj htne, hX, Submodule.map_bot]
  have hcongr : t.inf (fun v => map φ (V v ⊓ u₂))
      = t.inf (fun v => (map (mkQ u₁) (V v ⊓ u₂)).prod (⊥ : Submodule R (M ⧸ u₂))) :=
    Finset.inf_congr rfl fun v _ => map_prod_mkQ_inf (u₁ := u₁) (u₂ := u₂) inf_le_right
  have hprod : t.inf (fun v => (map (mkQ u₁) (V v ⊓ u₂)).prod (⊥ : Submodule R (M ⧸ u₂))) = ⊥ := by
    rw [← hcongr, hmap]
  have hA : t.inf (fun v => map (mkQ u₁) (V v ⊓ u₂)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x, 0) ∈ t.inf (fun v => (map (mkQ u₁) (V v ⊓ u₂)).prod (⊥ : Submodule R (M ⧸ u₂))) := by
      rw [Submodule.mem_finsetInf] at hx ⊢
      intro v hv
      exact mem_prod.mpr ⟨hx v hv, by simp⟩
    rw [hprod] at h1
    have h2 : (x, 0) = ((0 : M ⧸ u₁), (0 : M ⧸ u₂)) := by simpa using h1
    exact (mem_bot _).mpr (congr_arg Prod.fst h2)
  have hbot : InfIrred (⊥ : Submodule R (M ⧸ u₁)) := by
    have h := InfIrred.map_mkQ (v := u₁) (W := u₁) le_rfl hu₁
    rwa [map_mkQ_self] at h
  obtain ⟨v, hv, hvbot⟩ := hbot.finset_inf_eq hA
  refine ⟨v, hv, le_antisymm ?_ bot_le⟩
  have hle : V v ⊓ u₂ ≤ u₁ := by
    have h2 : V v ⊓ u₂ ≤ comap (mkQ u₁) ⊥ := by
      rw [← hvbot]
      exact map_le_iff_le_comap.mp le_rfl
    rwa [comap_bot, ker_mkQ] at h2
  intro x hx
  have h1 : x ∈ u₁ := hle hx
  have h3 : x ∈ u₁ ⊓ u₂ := mem_inf.mpr ⟨h1, (mem_inf.mp hx).2⟩
  rw [hu] at h3
  exact (mem_bot _).mp h3

/-- The replacement (exchange) lemma for irredundant decompositions into inf-irreducibles. -/
theorem exists_inf_eq_of_infIrred {W u₁ u₂ : Submodule R M} (hu : u₁ ⊓ u₂ = W)
    (hu₁ : InfIrred u₁) {ι : Type*} {t : Finset ι} {V : ι → Submodule R M}
    (htne : t.Nonempty) (ht : t.inf V = W) : ∃ v ∈ t, V v ⊓ u₂ = W := by
  classical
  have hW₁ : W ≤ u₁ := hu ▸ inf_le_left
  have hW₂ : W ≤ u₂ := hu ▸ inf_le_right
  have hWv : ∀ v ∈ t, W ≤ V v := fun v hv => ht ▸ Finset.inf_le hv
  have hq : map (mkQ W) u₁ ⊓ map (mkQ W) u₂ = ⊥ := by
    refine eq_of_comap_mkQ_eq ?_
    calc comap (mkQ W) (map (mkQ W) u₁ ⊓ map (mkQ W) u₂)
        = comap (mkQ W) (map (mkQ W) u₁) ⊓ comap (mkQ W) (map (mkQ W) u₂) :=
          comap_inf _ _ _
      _ = (W ⊔ u₁) ⊓ (W ⊔ u₂) := by rw [comap_map_mkQ, comap_map_mkQ]
      _ = u₁ ⊓ u₂ := by rw [sup_eq_right.mpr hW₁, sup_eq_right.mpr hW₂]
      _ = W := hu
      _ = comap (mkQ W) ⊥ := by rw [comap_bot, ker_mkQ]
  have htq : t.inf (fun v => map (mkQ W) (V v)) = ⊥ := by
    rw [← map_mkQ_finsetInf hWv, ht, map_mkQ_self]
  obtain ⟨v, hv, hvq⟩ := exists_inf_eq_bot hq (InfIrred.map_mkQ hW₁ hu₁) htne htq
  refine ⟨v, hv, ?_⟩
  have h' := congr_arg (comap (mkQ W)) hvq
  simp only [comap_inf, comap_bot, ker_mkQ, comap_map_mkQ,
    sup_eq_right.mpr (hWv v hv), sup_eq_right.mpr hW₂] at h'
  exact h'

/-! ### The number of components is an invariant -/

/-- If `s` and `t` are irredundant decompositions of the same submodule into inf-irreducibles,
then `t` has at most as many members as `s`. -/
theorem card_le_of_infIrred_decomposition {s t : Finset (Submodule R M)} {W : Submodule R M}
    (hs : s.inf id = W) (hsi : ∀ q ∈ s, InfIrred q)
    (ht : t.inf id = W) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) : t.card ≤ s.card := by
  classical
  have key : ∀ s' : Finset (Submodule R M), ∀ J : Finset (Submodule R M),
      (∀ q ∈ s', InfIrred q) → s'.inf id ⊓ J.inf id = W → J ⊆ t →
      ∃ J' ⊆ t, J'.card ≤ J.card + s'.card ∧ J'.inf id = W := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
      intro J _ hJ _
      exact ⟨J, ‹J ⊆ t›, by simp, by simpa using hJ⟩
    | insert a s' ha ih =>
      intro J hs' hJ hJt
      rcases t.eq_empty_or_nonempty with rfl | htne
      · have hW : W = ⊤ := by rw [← ht]; simp
        exact ⟨∅, by simp, by simp, by simp [hW]⟩
      obtain ⟨v, hvt, hvW⟩ := exists_inf_eq_of_infIrred
        (u₁ := a) (u₂ := s'.inf id ⊓ J.inf id) (W := W)
        (by rw [Finset.inf_insert] at hJ; rwa [← inf_assoc])
        (hs' a (Finset.mem_insert_self a s')) htne ht
      obtain ⟨J', hJ't, hcard, hJW⟩ := ih (insert v J)
        (fun q hq => hs' q (Finset.mem_insert_of_mem hq))
        (by rw [Finset.inf_insert, ← hvW]; simp [inf_left_comm])
        (Finset.insert_subset hvt hJt)
      refine ⟨J', hJ't, ?_, hJW⟩
      have h1 : (insert v J).card ≤ J.card + 1 := Finset.card_insert_le v J
      have h2 : (insert a s').card = s'.card + 1 := Finset.card_insert_of_notMem ha
      omega
  obtain ⟨J, hJt, hcard, hJW⟩ := key s ∅ (fun q hq => hsi q hq) (by simpa using hs)
    (Finset.empty_subset t)
  have hJeq : J = t := by
    by_contra hne
    obtain ⟨v, hvt, hvJ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hJt, hne⟩)
    have hJsub : J ⊆ t.erase v := fun q hq => Finset.mem_erase.mpr ⟨fun h => hvJ (h ▸ hq), hJt hq⟩
    have h1 : (t.erase v).inf id ≤ J.inf id := Finset.inf_mono hJsub
    have h2 : t.inf id ≤ (t.erase v).inf id := Finset.inf_mono (Finset.erase_subset v t)
    have h3 : (t.erase v).inf id = W := le_antisymm (hJW ▸ h1) (ht ▸ h2)
    have h4 : W ≤ v := ht ▸ Finset.inf_le hvt
    exact htirr v hvt (h3 ▸ h4)
  rw [← hJeq]
  simpa using hcard

/-- The number of components of an irredundant decomposition of a submodule into
inf-irreducibles is independent of the decomposition. -/
theorem card_eq_of_infIrred_decomposition {s t : Finset (Submodule R M)} {W : Submodule R M}
    (hs : s.inf id = W) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = W) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) : s.card = t.card :=
  le_antisymm (card_le_of_infIrred_decomposition ht hti hs hsi hsirr)
    (card_le_of_infIrred_decomposition hs hsi ht hti htirr)

/-! ### From cumulative counts to counts -/

/-- On a finite partially ordered set, a function is determined by its cumulative sums over
principal down-sets. -/
theorem eq_of_cumulative_sum_eq {α : Type*} [PartialOrder α] (P : Finset α) (m m' : α → ℕ)
    (h : ∀ p ∈ P, ∑ q ∈ P.filter (· ≤ p), m q = ∑ q ∈ P.filter (· ≤ p), m' q) :
    ∀ p ∈ P, m p = m' p := by
  classical
  suffices key : ∀ n, ∀ p ∈ P, (P.filter (fun q => q < p)).card = n → m p = m' p by
    intro p hp
    exact key _ p hp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp hcard
    have hsplit : P.filter (· ≤ p) = insert p (P.filter (· < p)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq, hqp⟩
        by_cases h' : q = p
        · exact Or.inl h'
        · exact Or.inr ⟨hq, lt_of_le_of_ne hqp h'⟩
      · rintro (rfl | ⟨hq, hqp⟩)
        · exact ⟨hp, le_rfl⟩
        · exact ⟨hq, hqp.le⟩
    have hnotmem : p ∉ P.filter (· < p) := by simp
    have hh := h p hp
    rw [hsplit, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem] at hh
    have hsum : ∑ q ∈ P.filter (· < p), m q = ∑ q ∈ P.filter (· < p), m' q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqP, hqp⟩ := hq
      have hlt : (P.filter (fun r => r < q)).card < n := by
        rw [← hcard]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
        · intro r hr
          rw [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, lt_trans hr.2 hqp⟩
        · intro heq
          have hmem : q ∈ P.filter (fun r => r < p) := by
            rw [Finset.mem_filter]
            exact ⟨hqP, hqp⟩
          rw [← heq] at hmem
          simp at hmem
      exact ih _ hlt q hqP rfl
    rw [hsum] at hh
    omega

/-- Counting by fibres: the cumulative number of components with radical `≤ p` is the sum of the
multiplicities of the primes occurring below `p`. -/
theorem cumulative_eq_sum_multiplicity {s : Finset (Submodule R M)} {P : Finset (Ideal R)}
    (hP : ∀ q ∈ s, rad q ∈ P) (p : Ideal R) :
    (s.filter fun q => rad q ≤ p).card
      = ∑ r ∈ P.filter (· ≤ p), (s.filter fun q => rad q = r).card := by
  classical
  have hmaps : Set.MapsTo (fun q => rad q) ((s.filter fun q => rad q ≤ p) : Set (Submodule R M))
      ((P.filter (· ≤ p)) : Set (Ideal R)) := by
    intro q hq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq ⊢
    exact ⟨hP q hq.1, hq.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_filter] at hr
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, _⟩, hqr⟩; exact ⟨hq, hqr⟩
  · rintro ⟨hq, hqr⟩; exact ⟨⟨hq, hqr ▸ hr.2⟩, hqr⟩

/-! ### Multiplicities -/

section Noetherian

variable [IsNoetherian R M]

/-- For a prime `p`, the number of components whose radical is contained in `p` depends only on the
decomposed submodule. -/
theorem cumulative_card_eq {s t : Finset (Submodule R M)} {W : Submodule R M}
    (hs : s.inf id = W) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = W) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q)
    {p : Ideal R} (hp : p.IsPrime) :
    (s.filter fun q => rad q ≤ p).card = (t.filter fun q => rad q ≤ p).card := by
  classical
  have hps : ∀ q ∈ s, q.IsPrimary := fun q hq => InfIrred.isPrimary (hsi q hq)
  have hpt : ∀ q ∈ t, q.IsPrimary := fun q hq => InfIrred.isPrimary (hti q hq)
  have hKs : sat p.primeCompl W = (s.filter fun q => rad q ≤ p).inf id := by
    rw [← hs, sat_primeCompl_inf (p := p) hps]
  have hKt : sat p.primeCompl W = (t.filter fun q => rad q ≤ p).inf id := by
    rw [← ht, sat_primeCompl_inf (p := p) hpt]
  refine card_eq_of_infIrred_decomposition hKs.symm (fun q hq => hsi q (Finset.mem_filter.mp hq).1)
    (fun q hq hle => ?_) hKt.symm (fun q hq => hti q (Finset.mem_filter.mp hq).1) (fun q hq hle => ?_)
  · exact hsirr q (Finset.mem_filter.mp hq).1
      (le_trans (Finset.inf_mono fun x hx => by
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, (Finset.mem_filter.mp hx.2).1⟩) hle)
  · exact htirr q (Finset.mem_filter.mp hq).1
      (le_trans (Finset.inf_mono fun x hx => by
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, (Finset.mem_filter.mp hx.2).1⟩) hle)

/-- Atiyah–Macdonald, Exercise 7.19, module form: in two irredundant decompositions of a submodule
of a Noetherian module as intersections of irreducible submodules, each prime ideal occurs as the
radical of the same number of components. -/
theorem multiplicity_eq {s t : Finset (Submodule R M)} {W : Submodule R M}
    (hs : s.inf id = W) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = W) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) (p : Ideal R) :
    (s.filter fun q => rad q = p).card = (t.filter fun q => rad q = p).card := by
  classical
  set P : Finset (Ideal R) := s.image rad ∪ t.image rad with hP
  have hPs : ∀ q ∈ s, rad q ∈ P := fun q hq => by
    rw [hP]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq)
  have hPt : ∀ q ∈ t, rad q ∈ P := fun q hq => by
    rw [hP]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq)
  have hPprime : ∀ r ∈ P, r.IsPrime := by
    intro r hr
    rw [hP, Finset.mem_union] at hr
    rcases hr with hr | hr
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact (InfIrred.isPrimary (hsi q hq)).isPrime_radical_colon
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact (InfIrred.isPrimary (hti q hq)).isPrime_radical_colon
  have hcum : ∀ r ∈ P, ∑ x ∈ P.filter (· ≤ r), (s.filter fun q => rad q = x).card
      = ∑ x ∈ P.filter (· ≤ r), (t.filter fun q => rad q = x).card := by
    intro r hr
    rw [← cumulative_eq_sum_multiplicity hPs r, ← cumulative_eq_sum_multiplicity hPt r,
      cumulative_card_eq hs hsi hsirr ht hti htirr (hPprime r hr)]
  by_cases hp : p ∈ P
  · exact eq_of_cumulative_sum_eq P _ _ hcum p hp
  · have hs0 : s.filter (fun q => rad q = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq hqr
      exact hp (hqr ▸ hPs q hq)
    have ht0 : t.filter (fun q => rad q = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq hqr
      exact hp (hqr ▸ hPt q hq)
    rw [hs0, ht0]

/-- Atiyah–Macdonald, Exercise 7.19, module form: the two irredundant decompositions have the same
number of components. -/
theorem card_eq {s t : Finset (Submodule R M)} {W : Submodule R M}
    (hs : s.inf id = W) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = W) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) : s.card = t.card := by
  classical
  set P : Finset (Ideal R) := s.image rad ∪ t.image rad with hP
  have hPs : ∀ q ∈ s, rad q ∈ P := fun q hq => by
    rw [hP]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq)
  have hPt : ∀ q ∈ t, rad q ∈ P := fun q hq => by
    rw [hP]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq)
  have hs' : s.card = ∑ p ∈ P, (s.filter fun q => rad q = p).card :=
    Finset.card_eq_sum_card_fiberwise (M := Ideal R) (s := s) (t := P) (f := fun q => rad q)
      (fun q hq => hPs q hq)
  have ht' : t.card = ∑ p ∈ P, (t.filter fun q => rad q = p).card :=
    Finset.card_eq_sum_card_fiberwise (M := Ideal R) (s := t) (t := P) (f := fun q => rad q)
      (fun q hq => hPt q hq)
  rw [hs', ht']
  exact Finset.sum_congr rfl fun p _ => multiplicity_eq hs hsi hsirr ht hti htirr p

end Noetherian

/-! ### The ideal form of Exercise 7.19 -/

section IdealForm

variable {A : Type*} [CommRing A]

/-- Atiyah–Macdonald, Exercise 7.19, module form in the geometric shape of the exercise: `N` is a
submodule of a finitely generated module over a Noetherian ring (cf. the remark "more generally, let
`N` be a submodule of a finitely generated module over a Noetherian ring"). -/
theorem ex_7_19_module {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] {N : Submodule R M}
    {s t : Finset (Submodule R M)}
    (hs : s.inf id = N) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = N) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) :
    s.card = t.card ∧ ∀ p : Ideal R,
      (s.filter fun q => rad q = p).card = (t.filter fun q => rad q = p).card :=
  ⟨card_eq hs hsi hsirr ht hti htirr, fun p => multiplicity_eq hs hsi hsirr ht hti htirr p⟩

/-- For an ideal `q`, the radical of `q` regarded as a submodule of the regular module is the
radical of `q`. -/
theorem rad_ideal (q : Ideal A) : rad (q : Submodule A A) = q.radical := by
  have h : (q : Submodule A A).colon (Set.univ : Set A) = q := by
    ext x
    simp
  rw [rad, h]

variable [IsNoetherianRing A] {𝔞 : Ideal A}

/-- **Atiyah–Macdonald, Exercise 7.19** (ideal form).  Let `𝔞` be an ideal of a Noetherian ring `A`
and let `𝔞 = ⋂_{i < r} 𝔟ᵢ = ⋂_{j < s} 𝔠ⱼ` be two minimal decompositions of `𝔞` as intersections of
irreducible ideals.  Then `r = s`, and each prime occurs as the radical of the same number of
components in the two decompositions — i.e. after re-indexing, `r(𝔟ᵢ) = r(𝔠ᵢ)` for all `i`. -/
theorem ex_7_19_ideal {s t : Finset (Ideal A)}
    (hs : s.inf id = 𝔞) (hsi : ∀ q ∈ s, InfIrred q)
    (hsirr : ∀ q ∈ s, ¬ (s.erase q).inf id ≤ q)
    (ht : t.inf id = 𝔞) (hti : ∀ q ∈ t, InfIrred q)
    (htirr : ∀ q ∈ t, ¬ (t.erase q).inf id ≤ q) :
    s.card = t.card ∧ ∀ p : Ideal A,
      (s.filter fun q => q.radical = p).card = (t.filter fun q => q.radical = p).card := by
  have key : ∀ p : Ideal A, (s.filter fun q => rad q = p).card = (t.filter fun q => rad q = p).card :=
    multiplicity_eq hs hsi hsirr ht hti htirr
  have key' : ∀ p : Ideal A,
      (s.filter fun q => q.radical = p).card = (t.filter fun q => q.radical = p).card := by
    intro p
    have h1 : s.filter (fun q => q.radical = p) = s.filter (fun q => rad (q : Submodule A A) = p) := by
      refine Finset.filter_congr ?_
      intro q _
      rw [rad_ideal]
    have h2 : t.filter (fun q => q.radical = p) = t.filter (fun q => rad (q : Submodule A A) = p) := by
      refine Finset.filter_congr ?_
      intro q _
      rw [rad_ideal]
    rw [h1, h2]
    exact key p
  exact ⟨card_eq hs hsi hsirr ht hti htirr, key'⟩

end IdealForm

/-! ### Re-indexing the two decompositions -/

/-- A combinatorial fact: two finite families in the same target have the same number of members in
each fibre if and only if they agree after a re-indexing. -/
theorem exists_equiv_of_card_filter_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]
    (f : ι → α) (g : κ → α)
    (h : ∀ a, (Finset.univ.filter fun i => f i = a).card
            = (Finset.univ.filter fun j => g j = a).card) :
    ∃ e : ι ≃ κ, ∀ i, f i = g (e i) := by
  classical
  have hc : ∀ a, Fintype.card {i // f i = a} = Fintype.card {j // g j = a} := by
    intro a
    rw [Fintype.card_subtype, Fintype.card_subtype, h a]
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun a => Fintype.equivOfCardEq (hc a)).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  exact (((Fintype.equivOfCardEq (hc (f i))) ⟨i, rfl⟩).2).symm

section IndexedForm

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {𝔞 : Ideal A}

/-- **Atiyah–Macdonald, Exercise 7.19**, in the indexed form in which it is stated: two minimal
decompositions `𝔞 = ⋂ᵢ 𝔟ᵢ = ⋂ⱼ 𝔠ⱼ` of an ideal of a Noetherian ring as intersections of irreducible
ideals have the same number of members, and after re-indexing the components have the same radicals.
(The family `b : Fin r → Ideal A` is required to be an irredundant intersection of irreducible
ideals equal to `𝔞`, and likewise for `c`.) -/
theorem ex_7_19 {r s : ℕ} {b : Fin r → Ideal A} {c : Fin s → Ideal A}
    (hb : (Finset.univ.inf b) = 𝔞) (hbi : ∀ i, InfIrred (b i))
    (hbirr : ∀ i, ¬ ((Finset.univ.erase i).inf b) ≤ b i)
    (hc : (Finset.univ.inf c) = 𝔞) (hci : ∀ i, InfIrred (c i))
    (hcirr : ∀ i, ¬ ((Finset.univ.erase i).inf c) ≤ c i) :
    ∃ e : Fin r ≃ Fin s, ∀ i, (b i).radical = (c (e i)).radical := by
  classical
  have hbinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    have hmem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hne h.symm, Finset.mem_univ j⟩
    exact hbirr i (le_trans (Finset.inf_le hmem) (le_of_eq hij.symm))
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hmem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hne h.symm, Finset.mem_univ j⟩
    exact hcirr i (le_trans (Finset.inf_le hmem) (le_of_eq hij.symm))
  have erase_image : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Ideal A) (i : κ),
      Function.Injective f →
      ((Finset.univ.image f).erase (f i)) = (Finset.univ.erase i).image f := by
    intro κ _ _ f i hinj
    ext q
    constructor
    · intro hq
      rw [Finset.mem_erase] at hq
      obtain ⟨hqne, hqmem⟩ := hq
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hqmem
      exact Finset.mem_image.mpr ⟨j, by
        rw [Finset.mem_erase]
        exact ⟨fun h => hqne (by rw [h]), Finset.mem_univ j⟩, rfl⟩
    · intro hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_erase] at hj ⊢
      exact ⟨fun h => hj.1 (hinj h), Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hsb : ((Finset.univ.image b).inf id) = 𝔞 := by
    rw [Finset.inf_image]
    simpa using hb
  have hsbi : ∀ q ∈ Finset.univ.image b, InfIrred q := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact hbi i
  have hsbirr : ∀ q ∈ Finset.univ.image b, ¬ ((Finset.univ.image b).erase q).inf id ≤ q := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    rw [erase_image (κ := Fin r) b i hbinj, Finset.inf_image]
    simpa using hbirr i
  have hsc : ((Finset.univ.image c).inf id) = 𝔞 := by
    rw [Finset.inf_image]
    simpa using hc
  have hsci : ∀ q ∈ Finset.univ.image c, InfIrred q := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact hci i
  have hscirr : ∀ q ∈ Finset.univ.image c, ¬ ((Finset.univ.image c).erase q).inf id ≤ q := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    rw [erase_image (κ := Fin s) c i hcinj, Finset.inf_image]
    simpa using hcirr i
  obtain ⟨-, hcount⟩ := ex_7_19_ideal hsb hsbi hsbirr hsc hsci hscirr
  have filter_image : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Ideal A),
      Function.Injective f → ∀ p : Ideal A,
      (Finset.univ.image f).filter (fun q => q.radical = p)
        = (Finset.univ.filter fun i => (f i).radical = p).image f := by
    intro κ _ _ f hinj p
    ext q
    constructor
    · intro hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqmem, hqp⟩ := hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hqmem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hqp⟩, rfl⟩
    · intro hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi.2⟩
  refine exists_equiv_of_card_filter_eq (fun i => (b i).radical) (fun j => (c j).radical) fun p => ?_
  have h' := hcount p
  rw [filter_image (κ := Fin r) b hbinj p, filter_image (κ := Fin s) c hcinj p,
    Finset.card_image_of_injOn hbinj.injOn, Finset.card_image_of_injOn hcinj.injOn] at h'
  exact h'

end IndexedForm

end AtiyahMcdonald69.Ex_7_19

/-! ### Axiom check -/

#print axioms AtiyahMcdonald69.Ex_7_19.ex_7_19
#print axioms AtiyahMcdonald69.Ex_7_19.ex_7_19_ideal
#print axioms AtiyahMcdonald69.Ex_7_19.multiplicity_eq
#print axioms AtiyahMcdonald69.Ex_7_19.card_eq
#print axioms AtiyahMcdonald69.Ex_7_19.ex_7_19_module
#print axioms AtiyahMcdonald69.Ex_7_19.card_eq_of_infIrred_decomposition
