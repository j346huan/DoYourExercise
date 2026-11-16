/-
# Atiyah–Macdonald (1969), Chapter 3, Exercise 7

Let `A` be a commutative ring and `S ⊆ A` a multiplicatively closed subset (in the sense of
Atiyah–Macdonald: `1 ∈ S` and `x, y ∈ S → x * y ∈ S`, i.e. a `Submonoid A`). `S` is *saturated*
if `x * y ∈ S ↔ x ∈ S ∧ y ∈ S`.

We formalise the three assertions of the exercise.

(i) `S` is saturated if and only if `A \ S` is a union of prime ideals of `A`.

(ii) For every multiplicatively closed `S` there is a unique smallest saturated multiplicatively
closed subset `S̄` containing `S`; it is the complement in `A` of the union of the prime ideals
which do not meet `S`. It consists of the `x` having a multiple in `S`.

(iii) If `S = 1 + 𝔞` for an ideal `𝔞`, then `S̄` is the inverse image of `(A ⧸ 𝔞)ˣ`, i.e. the set of
elements whose image in `A ⧸ 𝔞` is a unit.

Main results (all in the namespace `AtiyahMcdonald69.Ex_3_7`):

* `isSaturated_iff_exists_prime_cover`, `compl_eq_iUnion_primes` — part (i);
* `eq_saturation_iff` (unique smallest saturated set containing `S`),
  `compl_saturation_eq_iUnion_primes` / `mem_saturation_iff_forall_prime` (the saturation is the
  complement of the union of the prime ideals not meeting `S`), and
  `mem_saturation_iff_isUnit_algebraMap` (the saturation is the inverse image of the units of the
  localization `S⁻¹A`) — part (ii);
* `mem_saturation_onePlus_iff_isUnit` (the answer to (iii)), together with the equivalent
  descriptions `mem_saturation_onePlus_iff_forall_prime` and
  `mem_saturation_onePlus_iff_forall_maximal`, and `saturation_onePlus_eq_preimage_units`;
* `solution`, bundling the statements of the three parts;
* an audit of two points of the natural proof: `exists_prime_disjoint_onePlus_not_le` (a prime
  disjoint from `1 + 𝔞` need not contain `𝔞`) and `empty_saturated_not_union_of_primes` (the
  hypothesis `1 ∈ S` cannot be dropped).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_3_7

variable {A : Type*} [CommRing A]

/-!
## Part (i): saturated multiplicatively closed subsets and unions of prime ideals
-/

/-- A multiplicatively closed subset `S` of a ring is *saturated* if a product lies in `S` exactly
when both factors do. -/
def IsSaturated (S : Submonoid A) : Prop := ∀ x y : A, x * y ∈ S ↔ x ∈ S ∧ y ∈ S

theorem isSaturated_iff_forall_mul_mem {S : Submonoid A} :
    IsSaturated S ↔ ∀ x y : A, x * y ∈ S → x ∈ S ∧ y ∈ S where
  mp h := fun x y hxy => (h x y).1 hxy
  mpr h := fun x y => ⟨h x y, fun ⟨hx, hy⟩ => S.mul_mem hx hy⟩

theorem IsSaturated.mul_mem {S : Submonoid A} (hS : IsSaturated S) {x y : A} (h : x * y ∈ S) :
    x ∈ S ∧ y ∈ S :=
  (hS x y).1 h

/-- The complement of a saturated multiplicatively closed subset is a union of prime ideals:
every `x ∉ S` lies in a prime ideal disjoint from `S`. This is the nontrivial half of (i) and is
proved by extending the principal ideal `(x)`, which is disjoint from `S`, to a prime ideal. -/
theorem exists_prime_of_not_mem {S : Submonoid A} (hS : IsSaturated S) {x : A} (hx : x ∉ S) :
    ∃ p : Ideal A, p.IsPrime ∧ x ∈ p ∧ Disjoint (p : Set A) (S : Set A) := by
  have hdisj : Disjoint (Ideal.span {x} : Set A) (S : Set A) := by
    rw [Set.disjoint_left]
    intro y hy hyS
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy
    exact hx ((hS x a).1 hyS).1
  obtain ⟨p, hp, hle, hpd⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {x}) S hdisj
  exact ⟨p, hp, hle (Ideal.subset_span (Set.mem_singleton x)), hpd⟩

/-- Part (i), forward direction: a saturated multiplicatively closed set is the complement of the
union of the prime ideals disjoint from it. -/
theorem compl_eq_setOf_exists_prime {S : Submonoid A} (hS : IsSaturated S) :
    (S : Set A)ᶜ = {x : A | ∃ p : Ideal A, p.IsPrime ∧ Disjoint (p : Set A) (S : Set A) ∧ x ∈ p} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨p, hp, hxp, hpd⟩ := exists_prime_of_not_mem hS hx
    exact ⟨p, hp, hpd, hxp⟩
  · rintro ⟨p, -, hpd, hxp⟩
    exact Set.disjoint_left.mp hpd hxp

/-- Part (i), forward direction, in union form: `A \ S` is the union of the prime ideals which do
not meet `S`. -/
theorem compl_eq_iUnion_primes {S : Submonoid A} (hS : IsSaturated S) :
    (S : Set A)ᶜ = ⋃ p : {p : Ideal A // p.IsPrime ∧ Disjoint (p : Set A) (S : Set A)},
      (p.1 : Set A) := by
  rw [compl_eq_setOf_exists_prime hS]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop, SetLike.mem_coe,
    and_assoc]

/-- Part (i) of Atiyah–Macdonald, Exercise 3.7: `S` is saturated if and only if `A \ S` is a union
of prime ideals. -/
theorem isSaturated_iff_exists_prime_cover (S : Submonoid A) :
    IsSaturated S ↔
      ∃ P : Set (Ideal A), (∀ p ∈ P, p.IsPrime) ∧ ∀ x : A, x ∉ S ↔ ∃ p ∈ P, x ∈ p := by
  constructor
  · intro hS
    refine ⟨{p : Ideal A | p.IsPrime ∧ Disjoint (p : Set A) (S : Set A)}, fun p hp => hp.1, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨p, hp, hxp, hpd⟩ := exists_prime_of_not_mem hS hx
      exact ⟨p, ⟨hp, hpd⟩, hxp⟩
    · rintro ⟨p, ⟨-, hpd⟩, hxp⟩
      exact Set.disjoint_left.mp hpd hxp
  · rintro ⟨P, -, hcover⟩
    refine isSaturated_iff_forall_mul_mem.2 fun x y hxy => ⟨?_, ?_⟩
    · by_contra hx
      obtain ⟨p, hpP, hxp⟩ := (hcover x).1 hx
      exact (hcover (x * y)).2 ⟨p, hpP, p.mul_mem_right y hxp⟩ hxy
    · by_contra hy
      obtain ⟨p, hpP, hyp⟩ := (hcover y).1 hy
      exact (hcover (x * y)).2 ⟨p, hpP, p.mul_mem_left x hyp⟩ hxy

/-!
## Part (ii): the saturation of a multiplicatively closed subset
-/

/-- The saturation of a multiplicatively closed subset `S`: the set of elements `x` having a
multiple `a * x` in `S`. -/
def saturation (S : Submonoid A) : Submonoid A where
  carrier := {x : A | ∃ a : A, a * x ∈ S}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [show a * b * (x * y) = a * x * (b * y) by ring]
    exact S.mul_mem ha hb

theorem mem_saturation_iff {S : Submonoid A} {x : A} :
    x ∈ saturation S ↔ ∃ a : A, a * x ∈ S :=
  Iff.rfl

theorem le_saturation (S : Submonoid A) : S ≤ saturation S := fun _ hx => ⟨1, by rwa [one_mul]⟩

theorem saturation_isSaturated (S : Submonoid A) : IsSaturated (saturation S) := by
  intro x y
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨⟨a * y, ?_⟩, ⟨a * x, ?_⟩⟩
    · rw [show a * y * x = a * (x * y) by ring]; exact ha
    · rw [show a * x * y = a * (x * y) by ring]; exact ha
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a * b, by rw [show a * b * (x * y) = a * x * (b * y) by ring]; exact S.mul_mem ha hb⟩

theorem le_of_isSaturated_of_le {S T : Submonoid A} (hST : S ≤ T) (hT : IsSaturated T) :
    saturation S ≤ T := by
  rintro x ⟨a, ha⟩
  exact ((hT a x).1 (hST ha)).2

/-- Part (ii) of Atiyah–Macdonald, Exercise 3.7: `saturation S` is the unique smallest saturated
multiplicatively closed subset containing `S`. -/
theorem eq_saturation_iff {S T : Submonoid A} :
    T = saturation S ↔
      S ≤ T ∧ IsSaturated T ∧ ∀ U : Submonoid A, S ≤ U → IsSaturated U → T ≤ U := by
  constructor
  · rintro rfl
    exact ⟨le_saturation S, saturation_isSaturated S,
      fun U hSU hU => le_of_isSaturated_of_le hSU hU⟩
  · rintro ⟨hST, hT, hmin⟩
    exact le_antisymm (hmin _ (le_saturation S) (saturation_isSaturated S))
      (le_of_isSaturated_of_le hST hT)

theorem saturation_eq_self_iff {S : Submonoid A} : saturation S = S ↔ IsSaturated S := by
  constructor
  · rintro h
    rw [← h]
    exact saturation_isSaturated S
  · intro hS
    exact le_antisymm (le_of_isSaturated_of_le le_rfl hS) (le_saturation S)

/-- Part (ii): `x` lies in the saturation of `S` exactly when `x` lies in no prime ideal disjoint
from `S`; equivalently, the saturation is the complement of the union of the prime ideals which do
not meet `S`. -/
theorem mem_saturation_iff_forall_prime {S : Submonoid A} {x : A} :
    x ∈ saturation S ↔ ∀ p : Ideal A, p.IsPrime → Disjoint (p : Set A) (S : Set A) → x ∉ p := by
  constructor
  · rintro ⟨a, ha⟩ p _ hpd hxp
    exact Set.disjoint_left.mp hpd (p.mul_mem_left a hxp) ha
  · intro h
    by_contra hx
    have hdisj : Disjoint (Ideal.span {x} : Set A) (S : Set A) := by
      rw [Set.disjoint_left]
      intro y hy hyS
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy
      exact hx ⟨a, by rwa [mul_comm] at hyS⟩
    obtain ⟨p, hp, hle, hpd⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {x}) S hdisj
    exact h p hp hpd (hle (Ideal.subset_span (Set.mem_singleton x)))

/-- The saturation of `S` is the complement of the union of the prime ideals which do not meet
`S`. -/
theorem compl_saturation_eq_setOf_exists_prime (S : Submonoid A) :
    (saturation S : Set A)ᶜ =
      {x : A | ∃ p : Ideal A, p.IsPrime ∧ Disjoint (p : Set A) (S : Set A) ∧ x ∈ p} := by
  ext x
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq, SetLike.mem_coe, mem_saturation_iff_forall_prime]
  constructor
  · intro h
    by_contra hx
    exact h fun p hp hd hxp => hx ⟨p, hp, hd, hxp⟩
  · rintro ⟨p, hp, hd, hxp⟩ h
    exact h p hp hd hxp

/-- The same, in union form. -/
theorem compl_saturation_eq_iUnion_primes (S : Submonoid A) :
    (saturation S : Set A)ᶜ =
      ⋃ p : {p : Ideal A // p.IsPrime ∧ Disjoint (p : Set A) (S : Set A)}, (p.1 : Set A) := by
  rw [compl_saturation_eq_setOf_exists_prime]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop, SetLike.mem_coe,
    and_assoc]

/-- Part (ii) in localization form: the saturation of `S` is the inverse image of the units of the
localization `S⁻¹A`. (This is the general form of part (iii), where `S = 1 + 𝔞`.) -/
theorem mem_saturation_iff_isUnit_algebraMap (S : Submonoid A) (x : A) :
    x ∈ saturation S ↔ IsUnit (algebraMap A (Localization S) x) := by
  rw [IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a * x, ha, a, by rw [mul_comm]⟩
  · rintro ⟨m, hm, a, ha⟩
    exact ⟨a, by rw [mul_comm, ← ha]; exact hm⟩

/-!
## Part (iii): the saturation of `1 + 𝔞`
-/

/-- The multiplicatively closed subset `1 + I` of a ring, as the set of elements congruent to `1`
modulo `I`. -/
def onePlus (I : Ideal A) : Submonoid A where
  carrier := {x : A | x - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    show x * y - 1 ∈ I
    have h : x * y - 1 = (x - 1) * y + (y - 1) := by ring
    rw [h]
    exact I.add_mem (I.mul_mem_right y hx) hy

theorem mem_onePlus_iff (I : Ideal A) {x : A} : x ∈ onePlus I ↔ x - 1 ∈ I := Iff.rfl

theorem mem_onePlus_iff_exists (I : Ideal A) {x : A} :
    x ∈ onePlus I ↔ ∃ y ∈ I, x = 1 + y := by
  rw [mem_onePlus_iff]
  constructor
  · intro h
    exact ⟨x - 1, h, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- The saturation of `1 + 𝔞` in the form "some multiple lies in `1 + 𝔞`". -/
theorem mem_saturation_onePlus_iff_exists (I : Ideal A) (x : A) :
    x ∈ saturation (onePlus I) ↔ ∃ y : A, y * x - 1 ∈ I :=
  exists_congr fun _ => mem_onePlus_iff I

/-- Part (iii) of Atiyah–Macdonald, Exercise 3.7: if `S = 1 + 𝔞`, the saturation of `S` is the
inverse image of the group of units of `A ⧸ 𝔞`. -/
theorem mem_saturation_onePlus_iff_isUnit (I : Ideal A) (x : A) :
    x ∈ saturation (onePlus I) ↔ IsUnit (Ideal.Quotient.mk I x) := by
  rw [mem_saturation_iff]
  constructor
  · rintro ⟨a, ha⟩
    have ha' : a * x - 1 ∈ I := ha
    refine isUnit_iff_exists.2 ⟨Ideal.Quotient.mk I a, ?_, ?_⟩
    · rw [mul_comm, ← map_mul, Ideal.Quotient.mk_eq_one_iff_sub_mem]
      exact ha'
    · rw [← map_mul, Ideal.Quotient.mk_eq_one_iff_sub_mem]
      exact ha'
  · intro hu
    obtain ⟨b, hb, -⟩ := isUnit_iff_exists.1 hu
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.mk_eq_one_iff_sub_mem] at hb
    refine ⟨a, ?_⟩
    rw [mem_onePlus_iff]
    simpa only [mul_comm a x] using hb

/-- Part (iii), as an equality of sets: the saturation of `1 + 𝔞` is the preimage of the units of
`A ⧸ 𝔞`. -/
theorem saturation_onePlus_eq_preimage_units (I : Ideal A) :
    (saturation (onePlus I) : Set A) = Ideal.Quotient.mk I ⁻¹' {u : A ⧸ I | IsUnit u} := by
  ext x
  rw [SetLike.mem_coe, Set.mem_preimage]
  exact mem_saturation_onePlus_iff_isUnit I x

/-- A prime ideal containing `𝔞` does not meet `1 + 𝔞`. -/
theorem disjoint_onePlus_of_le {I p : Ideal A} (hp : p.IsPrime) (hIp : I ≤ p) :
    Disjoint (p : Set A) ((onePlus I : Submonoid A) : Set A) := by
  rw [Set.disjoint_left]
  intro y hyp hy1
  have h1 : y - 1 ∈ p := hIp hy1
  have h2 : (1 : A) ∈ p := by
    have h3 : y - (y - 1) = 1 := by ring
    rw [← h3]
    exact p.sub_mem hyp h1
  exact hp.ne_top ((Ideal.eq_top_iff_one p).2 h2)

/-- If `1 = a + b` with `a ∈ p` and `b ∈ 𝔞`, then `a ∈ p` meets `1 + 𝔞`. -/
theorem not_mem_sup_of_disjoint_onePlus {I p : Ideal A}
    (hpd : Disjoint (p : Set A) ((onePlus I : Submonoid A) : Set A)) :
    (1 : A) ∉ p ⊔ I := by
  rw [Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, hab⟩
  have hmem : a ∈ onePlus I := by
    rw [mem_onePlus_iff]
    have h : a - 1 = -b := by rw [← hab]; ring
    rw [h]
    exact I.neg_mem hb
  exact Set.disjoint_left.mp hpd ha (SetLike.mem_coe.mpr hmem)

/-- If `x` is not in the saturation of `1 + 𝔞`, some maximal ideal containing `𝔞` contains `x`. -/
theorem exists_maximal_of_not_mem_saturation_onePlus {I : Ideal A} {x : A}
    (hx : x ∉ saturation (onePlus I)) :
    ∃ m : Ideal A, m.IsMaximal ∧ I ≤ m ∧ x ∈ m := by
  have hmem : x ∈ (saturation (onePlus I) : Set A)ᶜ := hx
  rw [compl_saturation_eq_setOf_exists_prime, Set.mem_ofPred_eq] at hmem
  obtain ⟨p, hp, hpd, hpx⟩ := hmem
  have hne : p ⊔ I ≠ ⊤ := fun htop =>
    not_mem_sup_of_disjoint_onePlus hpd (htop ▸ Submodule.mem_top)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (p ⊔ I) hne
  exact ⟨m, hm, le_trans le_sup_right hle, hle (Submodule.mem_sup_left hpx)⟩

/-- Part (iii), in the form of the union of the prime ideals containing `𝔞`: the saturation of
`1 + 𝔞` is the set of elements lying in no prime ideal containing `𝔞`. -/
theorem mem_saturation_onePlus_iff_forall_prime (I : Ideal A) (x : A) :
    x ∈ saturation (onePlus I) ↔ ∀ p : Ideal A, p.IsPrime → I ≤ p → x ∉ p := by
  constructor
  · intro hx p hp hIp hxp
    exact mem_saturation_iff_forall_prime.1 hx p hp (disjoint_onePlus_of_le hp hIp) hxp
  · intro h
    by_contra hx
    obtain ⟨m, hm, hIm, hxm⟩ := exists_maximal_of_not_mem_saturation_onePlus hx
    exact h m hm.isPrime hIm hxm

/-- Part (iii), in the form given in the solutions: the saturation of `1 + 𝔞` is the complement of
the union of the maximal ideals containing `𝔞`. -/
theorem mem_saturation_onePlus_iff_forall_maximal (I : Ideal A) (x : A) :
    x ∈ saturation (onePlus I) ↔ ∀ m : Ideal A, m.IsMaximal → I ≤ m → x ∉ m := by
  rw [mem_saturation_onePlus_iff_forall_prime]
  constructor
  · intro h m hm hIm
    exact h m hm.isPrime hIm
  · intro h p hp hIp hxp
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal p hp.ne_top
    exact h m hm (le_trans hIp hle) (hle hxp)

/-- `p` meets `1 + 𝔞` exactly when `1 ∈ p + 𝔞`. -/
theorem disjoint_onePlus_iff_one_not_mem_sup {I p : Ideal A} :
    Disjoint (p : Set A) ((onePlus I : Submonoid A) : Set A) ↔ (1 : A) ∉ p ⊔ I := by
  refine ⟨not_mem_sup_of_disjoint_onePlus, fun h => ?_⟩
  rw [Set.disjoint_left]
  intro y hyp hy1
  have h1 : y - 1 ∈ I := hy1
  have h2 : y - (y - 1) ∈ p ⊔ I :=
    Submodule.sub_mem (p ⊔ I) (Submodule.mem_sup_left hyp) (Submodule.mem_sup_right h1)
  rw [show y - (y - 1) = 1 by ring] at h2
  exact h h2

/-!
## Auditing the natural proof: where hypotheses cannot be dropped

The natural proof of part (i) uses that a multiplicatively closed set contains `1`, and the answer
to (iii) needs care: the prime ideals which are disjoint from `1 + 𝔞` are *not* exactly the prime
ideals containing `𝔞` (only the unions of the two families coincide, which is what
`mem_saturation_onePlus_iff_forall_prime` says). Both points are made precise below.
-/

/-- A prime ideal disjoint from `1 + 𝔞` need not contain `𝔞`: in `ℤ` the prime ideal `(0)` is
disjoint from `1 + (2)`, the set of odd integers, yet `(2) ⊄ (0)`. -/
theorem exists_prime_disjoint_onePlus_not_le :
    ∃ p : Ideal ℤ, p.IsPrime ∧
      Disjoint (p : Set ℤ) ((onePlus (Ideal.span {(2 : ℤ)}) : Submonoid ℤ) : Set ℤ) ∧
      ¬ Ideal.span {(2 : ℤ)} ≤ p := by
  refine ⟨⊥, inferInstance, ?_, ?_⟩
  · rw [disjoint_onePlus_iff_one_not_mem_sup, bot_sup_eq, Ideal.mem_span_singleton]
    norm_num
  · intro h
    have h2 : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := h (Ideal.subset_span (Set.mem_singleton 2))
    simp only [Ideal.mem_bot] at h2
    omega

/-- The hypothesis `1 ∈ S` cannot be dropped from part (i): for a multiplicatively closed set `S`
not required to contain `1`, the statement fails. In `ℤ` the empty set is vacuously saturated, but
`ℤ = A \ ∅` is not a union of prime ideals, since no prime ideal contains `1`. -/
theorem empty_saturated_not_union_of_primes :
    (∀ x y : ℤ, x * y ∈ (∅ : Set ℤ) → x ∈ (∅ : Set ℤ) ∧ y ∈ (∅ : Set ℤ)) ∧
      ¬ ∃ P : Set (Ideal ℤ), (∀ p ∈ P, p.IsPrime) ∧
        ∀ x : ℤ, x ∉ (∅ : Set ℤ) ↔ ∃ p ∈ P, x ∈ p := by
  refine ⟨fun _ _ h => by simp at h, ?_⟩
  rintro ⟨P, hP, hcover⟩
  obtain ⟨p, hpP, hp1⟩ := (hcover 1).1 (by simp)
  exact (hP p hpP).ne_top ((Ideal.eq_top_iff_one p).2 hp1)

/-- Atiyah–Macdonald, Chapter 3, Exercise 7, all three parts. -/
theorem solution (S : Submonoid A) (I : Ideal A) (x : A) :
    (IsSaturated S ↔
        ∃ P : Set (Ideal A), (∀ p ∈ P, p.IsPrime) ∧ ∀ y : A, y ∉ S ↔ ∃ p ∈ P, y ∈ p) ∧
      (IsSaturated S →
        (S : Set A)ᶜ =
          ⋃ p : {p : Ideal A // p.IsPrime ∧ Disjoint (p : Set A) (S : Set A)}, (p.1 : Set A)) ∧
      (S ≤ saturation S ∧ IsSaturated (saturation S) ∧
        ∀ T : Submonoid A,
          (T = saturation S ↔
            S ≤ T ∧ IsSaturated T ∧ ∀ U : Submonoid A, S ≤ U → IsSaturated U → T ≤ U)) ∧
      ((saturation S : Set A)ᶜ =
        ⋃ p : {p : Ideal A // p.IsPrime ∧ Disjoint (p : Set A) (S : Set A)}, (p.1 : Set A)) ∧
      (x ∈ saturation (onePlus I) ↔ IsUnit (Ideal.Quotient.mk I x)) ∧
      (x ∈ saturation (onePlus I) ↔ ∀ p : Ideal A, p.IsPrime → I ≤ p → x ∉ p) ∧
      (x ∈ saturation S ↔ IsUnit (algebraMap A (Localization S) x)) :=
  ⟨isSaturated_iff_exists_prime_cover S, fun hS => compl_eq_iUnion_primes hS,
    ⟨le_saturation S, saturation_isSaturated S, fun _ => eq_saturation_iff⟩,
    compl_saturation_eq_iUnion_primes S, mem_saturation_onePlus_iff_isUnit I x,
    mem_saturation_onePlus_iff_forall_prime I x, mem_saturation_iff_isUnit_algebraMap S x⟩

end AtiyahMcdonald69.Ex_3_7
