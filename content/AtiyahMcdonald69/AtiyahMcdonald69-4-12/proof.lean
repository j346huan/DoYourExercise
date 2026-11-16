/-
Atiyah--Macdonald, *Introduction to Commutative Algebra*, Chapter 4, Exercise 12.

Statement (book): Let `A` be a ring and `S` a multiplicatively closed subset of `A`.
For an ideal `a` of `A`, let `S(a)` denote the contraction of `S⁻¹a` in `A`; the ideal
`S(a)` is the *saturation* of `a` with respect to `S`. Prove that

  (i)   `S(a) ∩ S(b) = S(a ∩ b)`,
  (ii)  `S(r(a)) = r(S(a))`,
  (iii) `S(a) = (1)` iff `a` meets `S`,
  (iv)  `S₁(S₂(a)) = (S₁S₂)(a)`,
  (v)   if `a` has a primary decomposition, then the set of ideals `S(a)`, where `S` runs
        through all multiplicatively closed subsets of `A`, is finite.

Formalisation notes.
* Multiplicatively closed subsets are represented by `Submonoid A` (in particular `1 ∈ S`),
  and the saturation is `saturation S a = (a.map (algebraMap A (Localization S))).under A`,
  i.e. literally the contraction of the extension of `a` to the localisation.
* `mem_saturation` is the membership criterion `x ∈ S(𝔞) ↔ ∃ s ∈ S, s * x ∈ 𝔞` recalled in
  the solution of the exercise; all four identities (i)--(iv) are deduced from it.
* The product `S₁S₂` of multiplicatively closed sets is the submonoid `S₁ ⊔ S₂` of `A`
  (its carrier set is the pointwise product, see `coe_sup_eq_mul`).
* For (v) the hypothesis "`a` has a primary decomposition" is the existence of a finite set
  `s` of primary ideals with `a = s.inf id`, exactly as in the book; primary ideals are
  Mathlib's `Ideal.IsPrimary` (`x * y ∈ q → x ∈ q ∨ y ∈ radical q`). The proof follows the
  natural one: a primary component `q` saturates to `q` if `radical q` is disjoint from `S`
  and to `(1)` otherwise, so at most `2 ^ #s` ideals occur
  (`exists_saturation_eq_finsetInf` makes this explicit).

Main declarations: `saturation_inf`, `saturation_radical`, `saturation_eq_top_iff`,
`saturation_saturation`, `finite_saturations`, and the bundled `solution`.
-/
import Mathlib

open scoped Classical Pointwise

namespace AtiyahMcdonald69.Ex_4_12

universe u

variable {A : Type u} [CommRing A]

/-- The saturation of an ideal `a` with respect to a submonoid `S`: the contraction of
`S⁻¹a` in `A` (Atiyah--Macdonald, Chapter 4, Exercise 12). -/
def saturation (S : Submonoid A) (a : Ideal A) : Ideal A :=
  (a.map (algebraMap A (Localization S))).under A

/-- Membership criterion for the saturation: `x ∈ S(a)` iff `s * x ∈ a` for some `s ∈ S`. -/
theorem mem_saturation {S : Submonoid A} {a : Ideal A} {x : A} :
    x ∈ saturation S a ↔ ∃ s ∈ S, s * x ∈ a := by
  rw [saturation, Ideal.mem_under]
  exact IsLocalization.algebraMap_mem_map_algebraMap_iff S (Localization S) a x

/-- Every ideal is contained in its saturation. -/
theorem le_saturation (S : Submonoid A) (a : Ideal A) : a ≤ saturation S a := by
  intro x hx
  exact mem_saturation.mpr ⟨1, S.one_mem, by simpa using hx⟩

/-- The saturation of the whole ring is the whole ring. -/
theorem saturation_top (S : Submonoid A) : saturation S (⊤ : Ideal A) = ⊤ := by
  rw [saturation, Ideal.map_top, Ideal.under_def, Ideal.comap_top]

/-- Exercise 4.12 (i): `S(a) ∩ S(b) = S(a ∩ b)`. -/
theorem saturation_inf (S : Submonoid A) (a b : Ideal A) :
    saturation S a ⊓ saturation S b = saturation S (a ⊓ b) := by
  ext x
  simp only [Ideal.mem_inf, mem_saturation]
  constructor
  · rintro ⟨⟨s, hs, hsa⟩, t, ht, htb⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_, ?_⟩
    · rw [show s * t * x = t * (s * x) by ring]; exact a.mul_mem_left t hsa
    · rw [mul_assoc]; exact b.mul_mem_left s htb
  · rintro ⟨s, hs, hsa, hsb⟩
    exact ⟨⟨s, hs, hsa⟩, s, hs, hsb⟩

/-- Exercise 4.12 (ii): `S(r(a)) = r(S(a))`. -/
theorem saturation_radical (S : Submonoid A) (a : Ideal A) :
    saturation S a.radical = (saturation S a).radical := by
  ext x
  simp only [mem_saturation, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨s, hs, n, hn⟩
    exact ⟨n, s ^ n, S.pow_mem hs n, by rw [← mul_pow]; exact hn⟩
  · rintro ⟨n, s, hs, hsn⟩
    refine ⟨s, hs, n + 1, ?_⟩
    have h : (s * x) ^ (n + 1) = (s ^ n * x) * (s * x ^ n) := by
      rw [pow_succ, mul_pow]; ring
    rw [h]; exact a.mul_mem_left (s ^ n * x) hsn

/-- Exercise 4.12 (iii): `S(a) = (1)` iff `a` meets `S`. -/
theorem saturation_eq_top_iff (S : Submonoid A) (a : Ideal A) :
    saturation S a = ⊤ ↔ ∃ s ∈ S, s ∈ a := by
  rw [Ideal.eq_top_iff_one, mem_saturation]
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa using h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa using h⟩

/-- The carrier of `S₁ ⊔ S₂` is the pointwise product `S₁S₂` of the two multiplicatively
closed sets, so `saturation (S₁ ⊔ S₂) a` is `S₁S₂(a)` in the notation of the exercise. -/
theorem coe_sup_eq_mul (S₁ S₂ : Submonoid A) :
    (↑(S₁ ⊔ S₂) : Set A) = ↑S₁ * ↑S₂ :=
  Submonoid.coe_sup S₁ S₂

/-- Exercise 4.12 (iv): `S₁(S₂(a)) = (S₁S₂)(a)`. -/
theorem saturation_saturation (S₁ S₂ : Submonoid A) (a : Ideal A) :
    saturation S₁ (saturation S₂ a) = saturation (S₁ ⊔ S₂) a := by
  ext x
  simp only [mem_saturation]
  constructor
  · rintro ⟨s₁, h₁, s₂, h₂, h⟩
    refine ⟨s₁ * s₂, ?_, ?_⟩
    · rw [← SetLike.mem_coe, coe_sup_eq_mul]
      exact Set.mem_mul.mpr ⟨s₁, h₁, s₂, h₂, rfl⟩
    · rw [show s₁ * s₂ * x = s₂ * (s₁ * x) by ring]; exact h
  · rintro ⟨t, ht, hxt⟩
    rw [← SetLike.mem_coe, coe_sup_eq_mul] at ht
    obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := Set.mem_mul.mp ht
    exact ⟨s₁, h₁, s₂, h₂, by rw [show s₁ * s₂ * x = s₂ * (s₁ * x) by ring] at hxt; exact hxt⟩

/-! ### Sanity checks on the degenerate multiplicatively closed sets -/

/-- Only `1` belongs to `⊥ : Submonoid A`, so nothing is inverted and no ideal moves. -/
theorem saturation_bot (a : Ideal A) : saturation (⊥ : Submonoid A) a = a := by
  refine le_antisymm ?_ (le_saturation _ a)
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_saturation.mp hx
  rw [Submonoid.mem_bot] at hs
  rwa [hs, one_mul] at hxs

/-- `⊤ : Submonoid A` contains `0`, so `S⁻¹A` is the zero ring and every saturation is `(1)`. -/
theorem saturation_top_submonoid (a : Ideal A) : saturation (⊤ : Submonoid A) a = ⊤ :=
  (saturation_eq_top_iff _ a).mpr ⟨0, Submonoid.mem_top 0, a.zero_mem⟩

/-! ### Saturation of a finite intersection of primary ideals -/

/-- The saturation of a finite intersection is the intersection of the saturations. -/
theorem saturation_finsetInf {ι : Type*} (S : Submonoid A) (t : Finset ι)
    (f : ι → Ideal A) :
    saturation S (t.inf f) = t.inf (fun i => saturation S (f i)) := by
  induction t using Finset.induction with
  | empty => rw [Finset.inf_empty, Finset.inf_empty, saturation_top]
  | insert a s _ ih => rw [Finset.inf_insert, Finset.inf_insert, ← saturation_inf, ih]

/-- A finite infimum in which the terms outside a given finite set are `⊤` is the infimum
over that finite set. -/
theorem inf_ite_eq {ι : Type*} (t : Finset ι) (p : ι → Prop) [DecidablePred p]
    (q : ι → Ideal A) : t.inf (fun i => if p i then q i else ⊤) = (t.filter p).inf q := by
  induction t using Finset.induction with
  | empty => rw [Finset.inf_empty, Finset.filter_empty, Finset.inf_empty]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.filter_insert]
    by_cases h : p a
    · rw [if_pos h, if_pos h, Finset.inf_insert, ih]
    · rw [if_neg h, if_neg h, ih, top_inf_eq]

/-- A primary ideal whose radical is disjoint from `S` saturates to itself. -/
theorem saturation_primary_eq_self {q : Ideal A} (hq : q.IsPrimary) {S : Submonoid A}
    (h : Disjoint (S : Set A) (q.radical : Set A)) : saturation S q = q := by
  refine le_antisymm ?_ (le_saturation S q)
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_saturation.mp hx
  rw [mul_comm] at hxs
  rcases (Ideal.isPrimary_iff.mp hq).2 hxs with h1 | h1
  · exact h1
  · exact absurd h1 (Set.disjoint_left.mp h hs)

/-- A primary ideal whose radical meets `S` saturates to the whole ring. -/
theorem saturation_primary_eq_top {q : Ideal A} {S : Submonoid A}
    (h : ¬ Disjoint (S : Set A) (q.radical : Set A)) : saturation S q = ⊤ := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨s, hs, hsr⟩ := h
  have hsr' : s ∈ q.radical := hsr
  rw [Ideal.mem_radical_iff] at hsr'
  obtain ⟨n, hn⟩ := hsr'
  exact saturation_eq_top_iff _ _ |>.mpr ⟨s ^ n, S.pow_mem hs n, hn⟩

/-- Sharpening of Exercise 4.12 (v): the saturation of a finite intersection of primary
ideals is the intersection of a *subfamily* of the given primary ideals, so at most `2 ^ n`
of them occur for `n` primary components. -/
theorem exists_saturation_eq_finsetInf {s : Finset (Ideal A)} (hs : ∀ q ∈ s, q.IsPrimary)
    {a : Ideal A} (ha : a = s.inf id) (S : Submonoid A) :
    ∃ t : Finset (Ideal A), t ⊆ s ∧ saturation S a = t.inf id := by
  classical
  refine ⟨s.filter (fun q => Disjoint (S : Set A) (q.radical : Set A)), ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_filter] at hq
    exact hq.1
  · rw [ha, saturation_finsetInf]
    simp only [id_eq]
    have hcongr : s.inf (fun i : Ideal A => saturation S i)
        = s.inf (fun i : Ideal A => if Disjoint (S : Set A) (i.radical : Set A)
            then i else ⊤) := by
      refine Finset.inf_congr rfl (fun q hq => ?_)
      by_cases h : Disjoint (S : Set A) (q.radical : Set A)
      · rw [if_pos h]; exact saturation_primary_eq_self (hs q hq) h
      · rw [if_neg h]; exact saturation_primary_eq_top h
    rw [hcongr, inf_ite_eq s (fun q : Ideal A => Disjoint (S : Set A) (q.radical : Set A))
      (fun i : Ideal A => i)]
    rfl

/-- Exercise 4.12 (v): if `a` has a primary decomposition, then the set of saturations
`S(a)`, as `S` ranges over the multiplicatively closed subsets of `A`, is finite. -/
theorem finite_saturations {s : Finset (Ideal A)} (hs : ∀ q ∈ s, q.IsPrimary) {a : Ideal A}
    (ha : a = s.inf id) :
    {I : Ideal A | ∃ S : Submonoid A, saturation S a = I}.Finite := by
  classical
  have hfin : ((↑(s.powerset.image (fun u : Finset (Ideal A) => u.inf id)) :
      Set (Ideal A))).Finite :=
    (s.powerset.image (fun u : Finset (Ideal A) => u.inf id)).finite_toSet
  refine Set.Finite.subset hfin ?_
  rintro I ⟨S, rfl⟩
  obtain ⟨t, hts, hEq⟩ := exists_saturation_eq_finsetInf hs ha S
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨t, Finset.mem_powerset.mpr hts, hEq.symm⟩

/-- Exercise 4.12 (v) in the literal form "`a` is decomposable", i.e. `a` admits *some* finite
primary decomposition. -/
theorem finite_saturations_of_decomposable (a : Ideal A)
    (h : ∃ s : Finset (Ideal A), (∀ q ∈ s, q.IsPrimary) ∧ a = s.inf id) :
    {I : Ideal A | ∃ S : Submonoid A, saturation S a = I}.Finite := by
  obtain ⟨s, hs, ha⟩ := h
  exact finite_saturations hs ha

/-- In a Noetherian ring every ideal is decomposable (Lasker--Noether, implemented in
Mathlib as `Submodule.isLasker`), so by Exercise 4.12 (v) every ideal has only finitely many
saturations. This corollary is not part of the exercise; it records that the hypothesis of
part (v) is automatic in the Noetherian case. -/
theorem finite_saturations_of_noetherian [IsNoetherianRing A] (a : Ideal A) :
    {I : Ideal A | ∃ S : Submonoid A, saturation S a = I}.Finite := by
  obtain ⟨s, hs, hprim⟩ := Submodule.isLasker A A (a : Submodule A A)
  exact finite_saturations (fun q hq => hprim hq) hs.symm

/-- Atiyah--Macdonald, Chapter 4, Exercise 12, all five parts bundled. -/
theorem solution (S S₁ S₂ : Submonoid A) (a b : Ideal A) {s : Finset (Ideal A)}
    (hs : ∀ q ∈ s, q.IsPrimary) (ha : a = s.inf id) :
    (saturation S a ⊓ saturation S b = saturation S (a ⊓ b)) ∧
    (saturation S a.radical = (saturation S a).radical) ∧
    (saturation S a = ⊤ ↔ ∃ x ∈ S, x ∈ a) ∧
    (saturation S₁ (saturation S₂ a) = saturation (S₁ ⊔ S₂) a) ∧
    ({I : Ideal A | ∃ T : Submonoid A, saturation T a = I}.Finite) :=
  ⟨saturation_inf S a b, saturation_radical S a, saturation_eq_top_iff S a,
    saturation_saturation S₁ S₂ a, finite_saturations hs ha⟩

end AtiyahMcdonald69.Ex_4_12

#print axioms AtiyahMcdonald69.Ex_4_12.mem_saturation
#print axioms AtiyahMcdonald69.Ex_4_12.saturation_inf
#print axioms AtiyahMcdonald69.Ex_4_12.saturation_radical
#print axioms AtiyahMcdonald69.Ex_4_12.saturation_eq_top_iff
#print axioms AtiyahMcdonald69.Ex_4_12.saturation_saturation
#print axioms AtiyahMcdonald69.Ex_4_12.exists_saturation_eq_finsetInf
#print axioms AtiyahMcdonald69.Ex_4_12.finite_saturations
#print axioms AtiyahMcdonald69.Ex_4_12.finite_saturations_of_decomposable
#print axioms AtiyahMcdonald69.Ex_4_12.finite_saturations_of_noetherian
#print axioms AtiyahMcdonald69.Ex_4_12.solution
