import Mathlib
set_option maxHeartbeats 1000000

/-!
# Atiyah–Macdonald (1969), Chapter 2, Exercise 28

Formalization of Exercise 28 of Chapter 2 of Atiyah–Macdonald,
*Introduction to Commutative Algebra*:

> 28. A Boolean ring is absolutely flat. The ring of Chapter 1, Exercise 7 is
> absolutely flat. Every homomorphic image of an absolutely flat ring is absolutely
> flat. If a local ring is absolutely flat, then it is a field.
> If `A` is absolutely flat, every non-unit in `A` is a zero-divisor.

Recall (Chapter 2, Exercise 27) that a ring `A` is *absolutely flat* if every
`A`-module is flat.

The formal statements below are, in order:

* `absolutelyFlat_of_booleanRing` — a Boolean ring is absolutely flat;
* `absolutelyFlat_of_pow_eq_self` — the ring of Chapter 1, Exercise 7 (every element
  satisfies `x ^ n = x` for some `n > 1`) is absolutely flat;
* `absolutelyFlat_of_surjective` / `absolutelyFlat_quotient` — every homomorphic image
  of an absolutely flat ring is absolutely flat;
* `isField_of_absolutelyFlat_of_isLocalRing` — an absolutely flat local ring is a field;
* `exists_mul_eq_zero_of_not_isUnit` — in an absolutely flat ring every non-unit is a
  zero-divisor.

As the exercise relies on Chapter 2, Exercise 27, the two directions of the
equivalence "absolutely flat ⇔ every principal ideal is idempotent" are also proved
here from scratch (`principalIdealIdempotent_of_absolutelyFlat`,
`absolutelyFlat_of_principalIdealIdempotent`).

Absolute flatness is stated for modules in the universe of the ring, which is the
universe-restricted reading of "every `A`-module is flat" used in this formalization.
-/

namespace AtiyahMcdonald69.Ex_2_28

universe u

variable {A : Type u} [CommRing A]

/-- A commutative ring `A` is **absolutely flat** if every `A`-module is flat
(Atiyah–Macdonald, Chapter 2, Exercise 27). -/
def AbsolutelyFlat (A : Type u) [CommRing A] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Flat A M

/-- Elementwise form of "every principal ideal is idempotent": every element is a
multiple of its own square. This is condition (ii)/(v) of Atiyah–Macdonald,
Chapter 2, Exercise 27. -/
def PrincipalIdealIdempotent (A : Type u) [CommRing A] : Prop :=
  ∀ x : A, ∃ a : A, x = a * x * x

/-- The ideal-theoretic form of Chapter 2, Exercise 27 (ii): every principal ideal is
idempotent, i.e. `(x) * (x) = (x)` for all `x`. -/
def PrincipalIdealIdempotentIdeal (A : Type u) [CommRing A] : Prop :=
  ∀ x : A, Ideal.span ({x} : Set A) * Ideal.span ({x} : Set A) = Ideal.span ({x} : Set A)

/-- The elementwise and the ideal-theoretic forms of "every principal ideal is
idempotent" agree: `x ∈ (x) * (x) = (x²)` says exactly that `x = a * x * x`. -/
theorem principalIdealIdempotent_iff_principalIdealIdempotentIdeal :
    PrincipalIdealIdempotent A ↔ PrincipalIdealIdempotentIdeal A := by
  constructor
  · intro h x
    rw [Ideal.span_singleton_mul_span_singleton]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨x, rfl⟩
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      obtain ⟨a, ha⟩ := h x
      refine ⟨a, ?_⟩
      calc x = a * x * x := ha
        _ = x * x * a := by ring
  · intro h x
    have hx : x ∈ Ideal.span ({x * x} : Set A) := by
      rw [← Ideal.span_singleton_mul_span_singleton, h x]
      exact Ideal.mem_span_singleton_self x
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    calc x = x * x * a := ha
      _ = a * x * x := by ring

/-- **(i) ⇒ (ii) of Chapter 2, Exercise 27, in elementwise form.**

If every `A`-module is flat then for every `x` there is `a` with `x = a * x * x`.

The proof is the textbook one: `A ⧸ (x)` is flat, so every relation in it is a trivial
relation (equational criterion for flatness).  Applying this to the relation
`x • 1 = 0` in `A ⧸ (x)` exhibits `1` as a finite sum `∑ aᵢ yᵢ` with `x * aᵢ = 0`;
lifting `yᵢ` to `A` shows that `1 - ∑ aᵢ rᵢ ∈ (x)`, whence
`x = x * 1 ∈ (x) * (x) = (x²)`. -/
theorem principalIdealIdempotent_of_absolutelyFlat (h : AbsolutelyFlat A) :
    PrincipalIdealIdempotent A := by
  classical
  intro x
  -- the flat module `A ⧸ (x)`
  have hflat : Module.Flat A (A ⧸ Ideal.span ({x} : Set A)) := h _
  -- the relation `x • 1 = 0` in `A ⧸ (x)`
  have hrel : ∑ _i : Fin 1, x • (1 : A ⧸ Ideal.span ({x} : Set A)) = 0 := by
    rw [Fin.sum_univ_one, Algebra.smul_def, mul_one]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self x)
  obtain ⟨k, a, y, hxy, hxa⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A)
      (M := A ⧸ Ideal.span ({x} : Set A)) (f := fun _ : Fin 1 => x)
      (x := fun _ : Fin 1 => (1 : A ⧸ Ideal.span ({x} : Set A))) hrel
  have hxy0 : (1 : A ⧸ Ideal.span ({x} : Set A)) = ∑ j : Fin k, a 0 j • y j := hxy 0
  have hxa0 : ∀ j : Fin k, x * a 0 j = 0 := by
    intro j
    have h := hxa j
    rwa [Fin.sum_univ_one] at h
  -- lift the elements `y j` of `A ⧸ (x)` to `A`
  have hysurj : ∀ j : Fin k, ∃ r : A, Ideal.Quotient.mk _ r = y j :=
    fun j => Ideal.Quotient.mk_surjective (y j)
  choose r hr using hysurj
  -- `1 = ∑ j, a 0 j * r j` in `A ⧸ (x)`
  have hS : Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (∑ j : Fin k, a 0 j * r j)
      = 1 := by
    rw [map_sum]
    have hterm : ∀ j : Fin k,
        Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (a 0 j * r j)
          = a 0 j • y j := by
      intro j
      rw [map_mul, hr j, Algebra.smul_def]
      rfl
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact hxy0.symm
  -- hence `1 - ∑ j, a 0 j * r j ∈ (x)`
  have hmem : (1 - ∑ j : Fin k, a 0 j * r j) ∈ Ideal.span ({x} : Set A) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hS, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  -- `x * a 0 j = 0` for all `j`
  have hxa' : ∀ j : Fin k, x * a 0 j = 0 := hxa0
  -- `1 = (∑ j, a 0 j * r j) + x * c`
  have h1 : (1 : A) = (∑ j : Fin k, a 0 j * r j) + x * c := by
    rw [← hc]; ring
  refine ⟨c, ?_⟩
  calc x = x * 1 := by rw [mul_one]
    _ = x * ((∑ j : Fin k, a 0 j * r j) + x * c) := by rw [h1]
    _ = x * (∑ j : Fin k, a 0 j * r j) + x * (x * c) := by rw [mul_add]
    _ = (∑ j : Fin k, x * (a 0 j * r j)) + x * (x * c) := by rw [Finset.mul_sum]
    _ = (∑ j : Fin k, (x * a 0 j) * r j) + x * (x * c) := by
          simp only [mul_assoc]
    _ = c * (x * x) := by
          have hsum : (∑ j : Fin k, (x * a 0 j) * r j) = 0 :=
            Finset.sum_eq_zero fun j _ => by rw [hxa' j, zero_mul]
          rw [hsum, zero_add]
          ring
    _ = c * x * x := by rw [mul_assoc]

/-- A principal ideal generated by an element which is a multiple of its own square is
generated by an idempotent: if `x = a * x * x` then `e = a * x` is idempotent and
`(x) = (e)`. -/
theorem exists_idempotent_span_of_principal {x : A} (hx : ∃ a : A, x = a * x * x) :
    ∃ e : A, e * e = e ∧ Ideal.span ({x} : Set A) = Ideal.span ({e} : Set A) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a * x, ?_, ?_⟩
  · calc (a * x) * (a * x) = a * (a * x * x) := by ring
      _ = a * x := by rw [← ha]
  · refine le_antisymm ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨x, ha⟩
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨a, by rw [mul_comm a x]⟩

/-- The sum of two principal ideals generated by idempotents is again a principal ideal
generated by an idempotent: `(e) + (f) = (e + f - e * f)`. -/
theorem span_singleton_sup_span_singleton {e f : A} (he : e * e = e) (hf : f * f = f) :
    Ideal.span ({e} : Set A) ⊔ Ideal.span ({f} : Set A) =
      Ideal.span ({e + f - e * f} : Set A) := by
  have hef : e * f * e = e * f := by
    rw [mul_assoc e f e, mul_comm f e, ← mul_assoc, he]
  refine le_antisymm ?_ ?_
  · rw [sup_le_iff]
    constructor
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      refine ⟨e, ?_⟩
      have h : (e + f - e * f) * e = e := by
        calc (e + f - e * f) * e = e * e + f * e - e * f * e := by ring
          _ = e := by rw [hef, he]; ring
      exact h.symm
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      refine ⟨f, ?_⟩
      have h : (e + f - e * f) * f = f := by
        calc (e + f - e * f) * f = e * f + f * f - e * f * f := by ring
          _ = f := by rw [mul_assoc e f f, hf]; ring
      exact h.symm
  · rw [Ideal.span_singleton_le_iff_mem]
    have he' : e ∈ Ideal.span ({e} : Set A) ⊔ Ideal.span ({f} : Set A) :=
      Submodule.mem_sup_left (Ideal.mem_span_singleton_self e)
    have hf' : f ∈ Ideal.span ({e} : Set A) ⊔ Ideal.span ({f} : Set A) :=
      Submodule.mem_sup_right (Ideal.mem_span_singleton_self f)
    exact sub_mem (add_mem he' hf') (Ideal.mul_mem_right f _ he')

/-- Every finitely generated ideal of a ring in which every element is a multiple of its
own square is generated by a single idempotent. -/
theorem exists_idempotent_span_of_fg (h : PrincipalIdealIdempotent A) ⦃I : Ideal A⦄
    (hI : I.FG) : ∃ e : A, e * e = e ∧ I = Ideal.span ({e} : Set A) := by
  classical
  have key : ∀ S : Finset A, ∃ e : A, e * e = e ∧
      Ideal.span (↑S : Set A) = Ideal.span ({e} : Set A) := by
    intro S
    induction S using Finset.induction with
    | empty => exact ⟨0, by ring, by simp⟩
    | insert x S hx ih =>
        obtain ⟨e, he, heS⟩ := ih
        obtain ⟨f, hf, hfx⟩ := exists_idempotent_span_of_principal (h x)
        refine ⟨f + e - f * e, IsIdempotentElem.add_sub_mul hf he, ?_⟩
        calc Ideal.span (↑(insert x S) : Set A)
            = Ideal.span ({x} : Set A) ⊔ Ideal.span (↑S : Set A) := by
              rw [Finset.coe_insert, Ideal.span_insert]
          _ = Ideal.span ({f} : Set A) ⊔ Ideal.span ({e} : Set A) := by rw [heS, hfx]
          _ = Ideal.span ({f + e - f * e} : Set A) :=
              span_singleton_sup_span_singleton hf he
  obtain ⟨S, hS⟩ := hI
  obtain ⟨e, he, hSe⟩ := key S
  exact ⟨e, he, by rw [← hS, hSe]⟩

/-- **(ii) ⇒ (i) of Chapter 2, Exercise 27, in elementwise form.**

If every element `x` is a multiple of its square then every module is flat: by the
ideal criterion for flatness it suffices to test finitely generated ideals `I`, and
such an `I` is generated by an idempotent `e`, so that the inclusion `I → A` is split
by `r ↦ r * e`; a direct summand of the (flat) module `A` is flat, so `I ⊗ M → M` is
injective. -/
theorem absolutelyFlat_of_principalIdealIdempotent (h : PrincipalIdealIdempotent A) :
    AbsolutelyFlat A := by
  intro M hAdd hMod
  classical
  refine Module.Flat.iff_rTensor_injective.mpr ?_
  intro I hI
  obtain ⟨e, he, hIe⟩ := exists_idempotent_span_of_fg h hI
  have heI : e ∈ I := by rw [hIe]; exact Ideal.mem_span_singleton_self e
  -- multiplying an element of `I` by `e` does not change it
  have hmul : ∀ i : I, (i : A) * e = (i : A) := by
    intro i
    have hi : (i : A) ∈ Ideal.span ({e} : Set A) := by
      rw [← hIe]
      exact i.2
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hi
    rw [hr]
    calc e * r * e = e * (r * e) := by rw [mul_assoc]
      _ = e * (e * r) := by rw [mul_comm r e]
      _ = e * e * r := by rw [mul_assoc]
      _ = e * r := by rw [he]
  -- the splitting `A → I`, `r ↦ r * e`
  let s : A →ₗ[A] I :=
    { toFun := fun r => r • (⟨e, heI⟩ : I)
      map_add' := fun r r' => add_smul r r' _
      map_smul' := fun r r' => smul_assoc r r' _ }
  have hcomp : s.comp I.subtype = LinearMap.id := by
    ext i
    simpa [s] using hmul i
  have hleft : ∀ z, LinearMap.rTensor M s (LinearMap.rTensor M I.subtype z) = z := by
    intro z
    have h1 : (LinearMap.rTensor M s).comp (LinearMap.rTensor M I.subtype) = LinearMap.id := by
      rw [← LinearMap.rTensor_comp, hcomp]
      exact LinearMap.rTensor_id M I
    exact congrArg (fun f => f z) h1
  intro u v huv
  have := congrArg (LinearMap.rTensor M s) huv
  rw [hleft u, hleft v] at this
  exact this

/-! ### Exercise 28 proper -/

/-- Chapter 2, Exercise 27 (conditions (i) ⇔ (ii)/(v)), in elementwise form: a ring is
absolutely flat iff every element is a multiple of its own square. -/
theorem absolutelyFlat_iff_principalIdealIdempotent :
    AbsolutelyFlat A ↔ PrincipalIdealIdempotent A :=
  ⟨principalIdealIdempotent_of_absolutelyFlat, absolutelyFlat_of_principalIdealIdempotent⟩

/-- **Exercise 28, first sentence**: a Boolean ring (a ring in which `x * x = x` for all
`x`) is absolutely flat. -/
theorem absolutelyFlat_of_booleanRing (h : ∀ x : A, x * x = x) : AbsolutelyFlat A :=
  absolutelyFlat_of_principalIdealIdempotent fun x => ⟨1, by rw [one_mul, h x]⟩

/-- **Exercise 28, second sentence**: the ring of Chapter 1, Exercise 7, i.e. a ring in
which every element satisfies `x ^ n = x` for some `n > 1` (depending on `x`), is
absolutely flat. -/
theorem absolutelyFlat_of_pow_eq_self (h : ∀ x : A, ∃ n : ℕ, 1 < n ∧ x ^ n = x) :
    AbsolutelyFlat A := by
  refine absolutelyFlat_of_principalIdealIdempotent fun x => ?_
  obtain ⟨n, hn, hx⟩ := h x
  refine ⟨x ^ (n - 2), ?_⟩
  have h2 : 2 ≤ n := hn
  calc x = x ^ n := hx.symm
    _ = x ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel h2]
    _ = x ^ (n - 2) * x ^ 2 := by rw [pow_add]
    _ = x ^ (n - 2) * (x * x) := by rw [pow_two]
    _ = x ^ (n - 2) * x * x := by rw [mul_assoc]

/-- **Exercise 28, third sentence**: every homomorphic image of an absolutely flat ring
is absolutely flat. -/
theorem absolutelyFlat_of_surjective {B : Type u} [CommRing B] (h : AbsolutelyFlat A)
    (f : A →+* B) (hf : Function.Surjective f) : AbsolutelyFlat B := by
  refine absolutelyFlat_of_principalIdealIdempotent fun y => ?_
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨a, ha⟩ := principalIdealIdempotent_of_absolutelyFlat h x
  exact ⟨f a, by rw [← map_mul, ← map_mul, ← ha]⟩

/-- **Exercise 28, fourth sentence**: a local ring which is absolutely flat is a
field. -/
theorem isField_of_absolutelyFlat_of_isLocalRing [IsLocalRing A] (h : AbsolutelyFlat A) :
    IsField A := by
  classical
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro y hy
  obtain ⟨a, ha⟩ := principalIdealIdempotent_of_absolutelyFlat h y
  -- `a * y` is an idempotent lying in the maximal ideal
  have he : (a * y) * (a * y) = a * y := by
    calc (a * y) * (a * y) = a * (a * y * y) := by ring
      _ = a * y := by rw [← ha]
  have hmem : a * y ∈ IsLocalRing.maximalIdeal A := by
    have h : y * a ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_right a _ hy
    rwa [mul_comm y a] at h
  -- hence `1 - a * y` is a unit, being the summand of a non-unit
  have hunit : IsUnit (1 - a * y) := by
    have hnu : ¬ IsUnit (a * y) := by
      have h := (IsLocalRing.mem_maximalIdeal (a * y)).mp hmem
      simpa [nonunits] using h
    have hsum : a * y + (1 - a * y) = 1 := by ring
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
    · exact absurd h hnu
    · exact h
  obtain ⟨u, hu⟩ := hunit
  have hzero : (a * y) * (1 - a * y) = 0 := by
    calc (a * y) * (1 - a * y) = a * y - (a * y) * (a * y) := by ring
      _ = 0 := by rw [he]; ring
  have haz : a * y = 0 := by
    have hu' : (1 - a * y) * ↑u⁻¹ = 1 := by rw [← hu]; exact Units.mul_inv u
    calc a * y = (a * y) * 1 := by rw [mul_one]
      _ = (a * y) * ((1 - a * y) * ↑u⁻¹) := by rw [hu']
      _ = ((a * y) * (1 - a * y)) * ↑u⁻¹ := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hzero, zero_mul]
  have hy0 : y = 0 := by
    calc y = a * y * y := ha
      _ = 0 := by rw [haz, zero_mul]
  rw [Submodule.mem_bot]
  exact hy0

/-- **Exercise 28, fourth sentence, elementwise form**: in an absolutely flat local ring
every nonzero element is a unit. -/
theorem isUnit_of_ne_zero_of_absolutelyFlat_of_isLocalRing [IsLocalRing A]
    (h : AbsolutelyFlat A) {x : A} (hx : x ≠ 0) : IsUnit x := by
  obtain ⟨b, hb⟩ := (isField_of_absolutelyFlat_of_isLocalRing h).mul_inv_cancel hx
  exact IsUnit.of_mul_eq_one b hb

/-- **Exercise 28, fourth sentence, ideal-theoretic form**: the maximal ideal of an
absolutely flat local ring is zero. -/
theorem maximalIdeal_eq_bot_of_absolutelyFlat [IsLocalRing A] (h : AbsolutelyFlat A) :
    IsLocalRing.maximalIdeal A = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (isField_of_absolutelyFlat_of_isLocalRing h)

/-- **Exercise 28, fifth sentence**: in an absolutely flat ring, every non-unit is a
zero-divisor. -/
theorem exists_mul_eq_zero_of_not_isUnit (h : AbsolutelyFlat A) {x : A}
    (hx : ¬ IsUnit x) : ∃ y : A, y ≠ 0 ∧ x * y = 0 := by
  obtain ⟨a, ha⟩ := principalIdealIdempotent_of_absolutelyFlat h x
  refine ⟨1 - a * x, ?_, ?_⟩
  · intro hzero
    have hax : x * a = 1 := by rw [mul_comm]; exact (sub_eq_zero.mp hzero).symm
    exact hx (IsUnit.of_mul_eq_one a hax)
  · calc x * (1 - a * x) = x - a * (x * x) := by ring
      _ = x - x := by rw [← mul_assoc, ← ha]
      _ = 0 := by ring

/-- **Exercise 28, third sentence, concrete form**: any quotient ring of an absolutely
flat ring is absolutely flat. -/
theorem absolutelyFlat_quotient (h : AbsolutelyFlat A) (I : Ideal A) :
    AbsolutelyFlat (A ⧸ I) :=
  absolutelyFlat_of_surjective h (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

end AtiyahMcdonald69.Ex_2_28

/-! ### Axiom audit -/

#print axioms AtiyahMcdonald69.Ex_2_28.principalIdealIdempotent_iff_principalIdealIdempotentIdeal
#print axioms AtiyahMcdonald69.Ex_2_28.principalIdealIdempotent_of_absolutelyFlat
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_of_principalIdealIdempotent
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_iff_principalIdealIdempotent
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_of_booleanRing
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_of_pow_eq_self
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_of_surjective
#print axioms AtiyahMcdonald69.Ex_2_28.absolutelyFlat_quotient
#print axioms AtiyahMcdonald69.Ex_2_28.isField_of_absolutelyFlat_of_isLocalRing
#print axioms AtiyahMcdonald69.Ex_2_28.isUnit_of_ne_zero_of_absolutelyFlat_of_isLocalRing
#print axioms AtiyahMcdonald69.Ex_2_28.maximalIdeal_eq_bot_of_absolutelyFlat
#print axioms AtiyahMcdonald69.Ex_2_28.exists_mul_eq_zero_of_not_isUnit
