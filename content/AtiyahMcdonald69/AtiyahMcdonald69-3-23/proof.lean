/-
Formalization of Atiyah–Macdonald (1969), Chapter 3, Exercise 23.

# The presheaf of rings on the basis of basic open sets of `Spec A`

**Statement** (Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 3, Exercise 23).

Let `A` be a ring, `X = Spec A`, and let `U` be a basic open set in `X` (i.e. `U = X_f` for some
`f ∈ A`, Chapter 1, Exercise 17).

* (i) If `U = X_f`, the ring `A(U) = A_f` depends only on `U` and not on `f`.
* (ii) Let `U' = X_g` be another basic open set with `U' ⊆ U`.  Then there is an equation
  `g ^ n = u * f` for some integer `n > 0` and some `u ∈ A`, and the map `ρ : A(U) → A(U')`
  (i.e. `A_f → A_g`) given by `a / f ^ m ↦ a * u ^ m / g ^ (m * n)` is a homomorphism, the
  *restriction homomorphism*.  It depends only on `U` and `U'`.
* (iii) If `U = U'` then `ρ` is the identity map.
* (iv) If `U ⊇ U' ⊇ U''` are basic open sets, the corresponding triangle of restriction
  homomorphisms commutes.
* (v) For `x = 𝔭 ∈ X`, `lim_{U ∋ x} A(U) ≅ A_𝔭`; the stalk of this presheaf at `x` is the local
  ring `A_𝔭`.

**Formalization choices.**  `X_f` is `PrimeSpectrum.basicOpen f : Opens (PrimeSpectrum A)`,
`A_f = A(X_f)` is `Localization.Away f`, and the local ring `A_𝔭` is `Localization.AtPrime 𝔭`.
The restriction homomorphism along `X_g ⊆ X_f` is `restriction`, built from the universal property
of localization (`IsLocalization.liftAlgHom`), and `restriction_mk'` proves that it computes by the
explicit formula of the exercise.  Direct limits are characterized by their universal property
(Atiyah–Macdonald, Ch. 2, Exercise 16), so `existsUnique_stalk_lift` — the existence and
uniqueness of a map out of `A_𝔭` compatible with an arbitrary compatible family of maps out of
the `A_f` — is literally the statement that `A_𝔭` is the direct limit of the `A_f` over the basic
neighbourhoods of `𝔭`; `exists_toAtPrime_eq` and `exists_restriction_eq_of_toAtPrime_eq` add the
concrete "every element of `A_𝔭` comes from some `A_f`" and "kernel is the union of the kernels"
descriptions of that isomorphism.

**Index of results.**

* (i) `sectionRingEquiv` (canonical isomorphism `A_f ≃ₐ[A] A_g` when `X_f = X_g`),
  `subsingleton_sectionRingEquiv`/`sectionRingEquiv_unique` (it is the unique such isomorphism),
  `sectionRingEquiv_rfl`, `restriction_congr` (compatibility with restriction).
* (ii) `exists_pow_eq_mul_of_basicOpen_le` (`g ^ n = u * f`, `n > 0`),
  `restriction` (the restriction homomorphism), `restriction_mk'` (the formula
  `a / f ^ m ↦ a * u ^ m / g ^ (m * n)`), `restriction_mk'_indep` (independence of the choice of
  `n` and `u`), `restriction_one`, `restriction_mul`, `restriction_add`, `restriction_algebraMap`.
* (iii) `restriction_self`, `restriction_comp_restriction_of_basicOpen_eq`.
* (iv) `restriction_comp_restriction`.
* (v) `toAtPrime` (the canonical maps `A_f → A_𝔭`), `toAtPrime_restriction` (they form a cocone),
  `existsUnique_stalk_lift` (universal property of the direct limit), `ringHom_ext_of_toAtPrime`,
  `exists_toAtPrime_eq`, `exists_restriction_eq_zero_of_toAtPrime_eq_zero`,
  `exists_restriction_eq_of_toAtPrime_eq`.
* The presheaf itself: `BasicOpenIndex`, `presheafOnBasis` (a contravariant functor from the poset
  of basic open sets to `CommRingCat`, whose functor laws are exactly (iii) and (iv)).
-/
import Mathlib

universe u

namespace AtiyahMcdonald69.Ex_3_23

open PrimeSpectrum

variable {A : Type*} [CommRing A]

/-! ## Auxiliary constructions and lemmas -/

/-- `f ^ m`, regarded as an element of the submonoid of powers of `f`.  An element of `A_f` is
thus written `IsLocalization.mk' (Localization.Away f) a (powMem f m)`, matching the book's
notation `a / f ^ m`. -/
def powMem (f : A) (m : ℕ) : Submonoid.powers f :=
  ⟨f ^ m, (Submonoid.mem_powers_iff (f ^ m) f).mpr ⟨m, rfl⟩⟩

@[simp]
theorem coe_powMem (f : A) (m : ℕ) : (powMem f m : A) = f ^ m := rfl

/-- If `X_g ⊆ X_f` then `f` is a unit in `A_g`. -/
theorem isUnit_algebraMap_of_basicOpen_le {f g : A} (h : basicOpen g ≤ basicOpen f) :
    IsUnit (algebraMap A (Localization.Away g) f) :=
  (basicOpen_le_basicOpen_iff_algebraMap_isUnit (S := Localization.Away g)).mp h

/-- **(ii)**, first assertion: if `X_g ⊆ X_f`, then `g ^ n = u * f` for some `n > 0` and some
`u ∈ A`. -/
theorem exists_pow_eq_mul_of_basicOpen_le {f g : A} (h : basicOpen g ≤ basicOpen f) :
    ∃ (n : ℕ) (_ : 0 < n) (u : A), g ^ n = u * f := by
  have h1 : g ∈ (Ideal.span ({f} : Set A)).radical := (basicOpen_le_basicOpen_iff g f).mp h
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hn
  exact ⟨n + 1, Nat.succ_pos n, u * g, by rw [pow_succ, hu]; ring⟩

/-- Every element of the submonoid of powers of `f` is a unit in `A_g` as soon as `X_g ⊆ X_f`. -/
theorem isUnit_algebraMap_of_mem_powers {f g : A} (h : basicOpen g ≤ basicOpen f) {x : A}
    (hx : x ∈ Submonoid.powers f) : IsUnit (algebraMap A (Localization.Away g) x) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hx
  rw [map_pow]
  exact (isUnit_algebraMap_of_basicOpen_le h).pow n

/-- The same statement, in the form needed by the universal property of `A_f`. -/
theorem isUnit_algebraMap_powers_of_basicOpen_le {f g : A} (h : basicOpen g ≤ basicOpen f) :
    ∀ y : Submonoid.powers f, IsUnit (algebraMap A (Localization.Away g) (y : A)) :=
  fun y => isUnit_algebraMap_of_mem_powers h y.2

/-! ## (ii) The restriction homomorphism -/

/-- The restriction homomorphism `ρ : A(U) → A(U')`, that is `A_f → A_g`, associated with an
inclusion `U' = X_g ⊆ X_f = U` of basic open sets.  It is the unique `A`-algebra homomorphism
`A_f → A_g`; it exists because `f` is a unit in `A_g`. -/
noncomputable def restriction {f g : A} (h : basicOpen g ≤ basicOpen f) :
    Localization.Away f →ₐ[A] Localization.Away g :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (S := Localization.Away f)
    (P := Localization.Away g) (f := Algebra.ofId A (Localization.Away g))
    (isUnit_algebraMap_powers_of_basicOpen_le h)

theorem restriction_algebraMap {f g : A} (h : basicOpen g ≤ basicOpen f) (a : A) :
    restriction h (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away g) a :=
  IsLocalization.lift_eq (isUnit_algebraMap_powers_of_basicOpen_le h) a

/-- The restriction homomorphism is the identity on the image of `A`. -/
theorem restriction_comp_algebraMap {f g : A} (h : basicOpen g ≤ basicOpen f) :
    (restriction h).comp (Algebra.ofId A (Localization.Away f)) =
      Algebra.ofId A (Localization.Away g) :=
  AlgHom.ext (restriction_algebraMap h)

/-- **(ii)**: the restriction map `ρ` is a ring homomorphism: it preserves `1`, products and
sums. -/
theorem restriction_one {f g : A} (h : basicOpen g ≤ basicOpen f) : restriction h 1 = 1 :=
  map_one _

theorem restriction_mul {f g : A} (h : basicOpen g ≤ basicOpen f) (x y : Localization.Away f) :
    restriction h (x * y) = restriction h x * restriction h y :=
  map_mul _ _ _

theorem restriction_add {f g : A} (h : basicOpen g ≤ basicOpen f) (x y : Localization.Away f) :
    restriction h (x + y) = restriction h x + restriction h y :=
  map_add _ _ _

/-- **(ii)**: the restriction homomorphism is computed by the formula of the exercise:
`a / f ^ m ↦ a * u ^ m / g ^ (m * n)`, where `g ^ n = u * f`. -/
theorem restriction_mk' {f g : A} (h : basicOpen g ≤ basicOpen f) {n : ℕ} (_hn : 0 < n) {u : A}
    (hu : g ^ n = u * f) (a : A) (m : ℕ) :
    restriction h (IsLocalization.mk' (Localization.Away f) a (powMem f m)) =
      IsLocalization.mk' (Localization.Away g) (a * u ^ m) (powMem g (m * n)) := by
  have hg := isUnit_algebraMap_powers_of_basicOpen_le h
  refine (IsLocalization.lift_mk'_spec (M := Submonoid.powers f) (S := Localization.Away f)
    (P := Localization.Away g) (g := algebraMap A (Localization.Away g)) hg a _ (powMem f m)).mpr ?_
  have hv :
      IsLocalization.mk' (Localization.Away g) (a * u ^ m) (powMem g (m * n)) *
          algebraMap A (Localization.Away g) (g ^ (m * n)) =
        algebraMap A (Localization.Away g) (a * u ^ m) :=
    IsLocalization.mk'_spec (Localization.Away g) (a * u ^ m) (powMem g (m * n))
  have hfu : f ^ m * u ^ m = g ^ (m * n) := by
    rw [← mul_pow, mul_comm f u, ← hu, ← pow_mul, Nat.mul_comm]
  have hstep : f ^ m * (a * u ^ m) = a * g ^ (m * n) := by
    rw [show f ^ m * (a * u ^ m) = a * (f ^ m * u ^ m) by ring, hfu]
  have hunit : IsUnit (algebraMap A (Localization.Away g) (g ^ (m * n))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit g).pow _
  have key :
      algebraMap A (Localization.Away g) (f ^ m) *
          IsLocalization.mk' (Localization.Away g) (a * u ^ m) (powMem g (m * n)) *
            algebraMap A (Localization.Away g) (g ^ (m * n)) =
        algebraMap A (Localization.Away g) a *
          algebraMap A (Localization.Away g) (g ^ (m * n)) := by
    rw [mul_assoc, hv, ← map_mul, hstep, map_mul]
  exact ((IsUnit.mul_left_inj hunit).mp key).symm

/-- **(ii)**: the value of the restriction homomorphism does not depend on the choice of the
equation `g ^ n = u * f` (nor on `n`) used to write down the formula. -/
theorem restriction_mk'_indep {f g : A} (h : basicOpen g ≤ basicOpen f) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {u u' : A} (hu : g ^ n = u * f) (hu' : g ^ n' = u' * f) (a : A) (m : ℕ) :
    IsLocalization.mk' (Localization.Away g) (a * u ^ m) (powMem g (m * n)) =
      IsLocalization.mk' (Localization.Away g) (a * u' ^ m) (powMem g (m * n')) := by
  rw [← restriction_mk' h hn hu a m, ← restriction_mk' h hn' hu' a m]

/-! ## Uniqueness of `A`-algebra maps out of a localized ring -/

/-- Two `A`-algebra homomorphisms out of `A_f` with the same target agree; equivalently, the
identity is the only `A`-algebra endomorphism of `A_f`. -/
theorem algHom_subsingleton_away (f : A) (B : Type*) [CommSemiring B] [Algebra A B] :
    Subsingleton (Localization.Away f →ₐ[A] B) :=
  IsLocalization.algHom_subsingleton (Submonoid.powers f) (S := Localization.Away f) (P := B)

/-- Uniqueness: any two `A`-algebra homomorphisms `A_f → B` are equal. -/
theorem away_algHom_ext {f : A} {B : Type*} [CommSemiring B] [Algebra A B]
    (u v : Localization.Away f →ₐ[A] B) : u = v :=
  @Subsingleton.elim _ (algHom_subsingleton_away f B) u v

/-! ## (iii) Restriction along equal basic open sets is the identity -/

/-- **(iii)**: the restriction along `X_f ⊆ X_f` is the identity. -/
theorem restriction_self (f : A) :
    restriction (le_refl (basicOpen f)) = AlgHom.id A (Localization.Away f) :=
  away_algHom_ext _ _

/-- **(iii)**: if `X_f = X_g`, then the two restriction homomorphisms `A_f → A_g` and
`A_g → A_f` are mutually inverse: after the identification of (i), restriction along `U = U'` is
the identity. -/
theorem restriction_comp_restriction_of_basicOpen_eq {f g : A} (h : basicOpen f = basicOpen g) :
    (restriction h.ge).comp (restriction h.le) = AlgHom.id A (Localization.Away g) ∧
      (restriction h.le).comp (restriction h.ge) = AlgHom.id A (Localization.Away f) :=
  ⟨away_algHom_ext _ _, away_algHom_ext _ _⟩

/-! ## (iv) Transitivity of restriction -/

/-- **(iv)**: if `U ⊇ U' ⊇ U''` are basic open sets then restricting twice is restricting
directly. -/
theorem restriction_comp_restriction {f g h : A} (h₁ : basicOpen g ≤ basicOpen f)
    (h₂ : basicOpen h ≤ basicOpen g) :
    (restriction h₂).comp (restriction h₁) = restriction (le_trans h₂ h₁) :=
  away_algHom_ext _ _

/-! ## (i) The ring `A(U)` depends only on `U` -/

/-- **(i)**: if `X_f = X_g` then there is a canonical `A`-algebra isomorphism `A_f ≃ₐ[A] A_g`,
namely the two restriction homomorphisms; thus the ring `A(U) = A_f` depends only on the basic
open set `U` and not on the chosen `f`. -/
noncomputable def sectionRingEquiv {f g : A} (h : basicOpen f = basicOpen g) :
    Localization.Away f ≃ₐ[A] Localization.Away g :=
  AlgEquiv.ofAlgHom (restriction h.ge) (restriction h.le)
    (restriction_comp_restriction_of_basicOpen_eq h).1
    (restriction_comp_restriction_of_basicOpen_eq h).2

/-- **(i)**: the identification of `A_f` with `A_g` for `X_f = X_g` is unique: any two
`A`-algebra isomorphisms between them are equal, so the identification involves no choice. -/
theorem subsingleton_sectionRingEquiv {f g : A} :
    Subsingleton (Localization.Away f ≃ₐ[A] Localization.Away g) :=
  ⟨fun e e' => AlgEquiv.coe_toAlgHom_injective
    (away_algHom_ext (e : Localization.Away f →ₐ[A] Localization.Away g)
      (e' : Localization.Away f →ₐ[A] Localization.Away g))⟩

/-- **(i)**: consequently, the identification does not depend on any choice. -/
theorem sectionRingEquiv_unique {f g : A} (h : basicOpen f = basicOpen g)
    (e : Localization.Away f ≃ₐ[A] Localization.Away g) : e = sectionRingEquiv h :=
  @Subsingleton.elim _ (subsingleton_sectionRingEquiv (f := f) (g := g)) e _

/-- **(i)**: the identification is the identity when the two generators agree. -/
theorem sectionRingEquiv_rfl (f : A) :
    sectionRingEquiv (rfl : basicOpen f = basicOpen f) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective (away_algHom_ext _ _)

/-- **(i)+(ii)**: the restriction homomorphism is well defined on the open sets themselves: it
does not depend on the chosen generators `f` of `U = X_f` and `g` of `U' = X_g`. -/
theorem restriction_congr {f f' g g' : A} (hf : basicOpen f = basicOpen f')
    (hg : basicOpen g = basicOpen g') (h : basicOpen g ≤ basicOpen f)
    (h' : basicOpen g' ≤ basicOpen f') :
    (restriction h').comp (sectionRingEquiv hf).toAlgHom =
      (sectionRingEquiv hg).toAlgHom.comp (restriction h) :=
  away_algHom_ext _ _

/-! ## The presheaf of rings on the basis of basic open sets

Parts (i) and (ii) give, for every generator `f ∈ A`, the ring `A(X_f) = A_f`, and for every
inclusion `X_g ⊆ X_f` the restriction homomorphism `A_f → A_g`; parts (iii) and (iv) say exactly
that this data is a presheaf of rings on the basis `(X_f)_{f ∈ A}` of `Spec A`. -/

section Presheaf

open CategoryTheory

/-- The poset of basic open sets of `Spec A`, presented by generators: the elements are the
elements of `A` and `f ≤ g` means `X_f ⊆ X_g`.  Different generators of the same basic open set
give different elements of this poset, but part (i) — see `sectionRingEquiv` and
`subsingleton_sectionRingEquiv` — shows that the associated section rings are canonically and
uniquely identified. -/
abbrev BasicOpenIndex (A : Type u) [CommRing A] : Type u := A

instance BasicOpenIndex.instPreorder (A : Type u) [CommRing A] : Preorder (BasicOpenIndex A) where
  le f g := basicOpen f ≤ basicOpen g
  le_refl f := le_rfl
  le_trans _ _ _ := le_trans

/-- **(i)–(iv)**, packaged: the assignment `X_f ↦ A(X_f) = A_f` together with the restriction
homomorphisms is a presheaf of rings on the basis `(X_f)_{f ∈ A}` of `X = Spec A`, that is, a
contravariant functor from the poset of basic open sets to the category of commutative rings.
The functor laws are parts (iii) and (iv). -/
noncomputable def presheafOnBasis (A : Type u) [CommRing A] :
    (BasicOpenIndex A)ᵒᵖ ⥤ CommRingCat.{u} where
  obj f := CommRingCat.of (Localization.Away (f.unop : A))
  map {f g} φ := CommRingCat.ofHom
    (restriction (f := (f.unop : A)) (g := (g.unop : A))
      (CategoryTheory.leOfHom φ.unop)).toRingHom
  map_id f := by
    apply CommRingCat.hom_ext
    show (restriction (f := (f.unop : A)) (g := (f.unop : A))
      (CategoryTheory.leOfHom (𝟙 f.unop))).toRingHom = RingHom.id _
    rw [restriction_self]
    rfl
  map_comp {X Y Z} f g := by
    apply CommRingCat.hom_ext
    show (restriction (f := (X.unop : A)) (g := (Z.unop : A))
        (CategoryTheory.leOfHom ((f ≫ g).unop))).toRingHom =
      ((restriction (f := (Y.unop : A)) (g := (Z.unop : A))
          (CategoryTheory.leOfHom g.unop)).comp
        (restriction (f := (X.unop : A)) (g := (Y.unop : A))
          (CategoryTheory.leOfHom f.unop))).toRingHom
    rw [restriction_comp_restriction]

end Presheaf

/-! ## (v) The stalk of the presheaf at a prime is the local ring -/

section Stalk

variable (p : Ideal A) [hp : p.IsPrime]

/-- The powers of `f` are units in `A_𝔭`, for `f ∉ 𝔭`. -/
theorem isUnit_algebraMap_powers_atPrime {f : A} (hf : f ∉ p) :
    ∀ y : Submonoid.powers f, IsUnit (algebraMap A (Localization.AtPrime p) (y : A)) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y f).mp hy
  rw [map_pow]
  exact (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨f, hf⟩).pow n

/-- For `𝔭 ∈ X_f`, i.e. `f ∉ 𝔭`, the canonical map `A_f → A_𝔭` given by the universal property of
localization: `1 / f ↦ (algebraMap f)⁻¹`. -/
noncomputable def toAtPrime (f : A) (hf : f ∉ p) :
    Localization.Away f →ₐ[A] Localization.AtPrime p :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (S := Localization.Away f)
    (P := Localization.AtPrime p) (f := Algebra.ofId A (Localization.AtPrime p))
    (isUnit_algebraMap_powers_atPrime p hf)

theorem toAtPrime_algebraMap (f : A) (hf : f ∉ p) (a : A) :
    toAtPrime p f hf (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.AtPrime p) a :=
  IsLocalization.lift_eq (isUnit_algebraMap_powers_atPrime p hf) a

/-- The canonical maps `A_f → A_𝔭` are compatible with the restriction homomorphisms: they form a
cocone over the basic open neighbourhoods of `𝔭`. -/
theorem toAtPrime_restriction {f g : A} (h : basicOpen g ≤ basicOpen f) (hf : f ∉ p)
    (hg : g ∉ p) :
    (toAtPrime p g hg).toRingHom.comp (restriction h).toRingHom =
      (toAtPrime p f hf).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    restriction_algebraMap, toAtPrime_algebraMap]

/-- **(v)**, universal property of the direct limit: `A_𝔭` is the direct limit of the rings
`A(U) = A_f` over the basic open neighbourhoods `U = X_f` of `𝔭`.

A direct limit is characterized by its universal property (Atiyah–Macdonald, Ch. 2, Exercise 16,
applied to the directed set of basic neighbourhoods of `𝔭`): given any ring `T` and any compatible
family of homomorphisms `A_f → T` (`f ∉ 𝔭`) out of the diagram, there is a unique homomorphism
`A_𝔭 → T` through which they all factor. -/
theorem existsUnique_stalk_lift (T : Type*) [CommRing T]
    (φ : ∀ (f : A), f ∉ p → Localization.Away f →+* T)
    (hφ : ∀ (f g : A) (hf : f ∉ p) (hg : g ∉ p) (h : basicOpen g ≤ basicOpen f),
      (φ g hg).comp (restriction h).toRingHom = φ f hf) :
    ∃! Φ : Localization.AtPrime p →+* T, ∀ (f : A) (hf : f ∉ p),
      Φ.comp (toAtPrime p f hf).toRingHom = φ f hf := by
  classical
  have h1 : (1 : A) ∉ p := fun hmem => hp.ne_top (Ideal.eq_top_iff_one p |>.mpr hmem)
  -- the underlying map `A →+* T`, induced by the ring `A = A_1`
  set g₀ : A →+* T := (φ 1 h1).comp (algebraMap A (Localization.Away 1)) with hg₀
  have hunit : ∀ y : p.primeCompl, IsUnit (g₀ (y : A)) := by
    intro y
    have hle : basicOpen (y : A) ≤ basicOpen (1 : A) := by
      rw [basicOpen_one]
      exact le_top
    have hcompat : g₀ (y : A) =
        φ (y : A) y.2 ((restriction hle) (algebraMap A (Localization.Away 1) (y : A))) := by
      rw [hg₀]
      exact (congrFun (congrArg DFunLike.coe (hφ 1 (y : A) h1 y.2 hle))
        (algebraMap A (Localization.Away 1) (y : A))).symm
    rw [hcompat, restriction_algebraMap]
    exact IsUnit.map (φ (y : A) y.2) (IsLocalization.Away.algebraMap_isUnit (y : A))
  refine ⟨IsLocalization.lift hunit, ?_, ?_⟩
  · -- existence: the candidate factors the given family
    intro f hf
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      toAtPrime_algebraMap, IsLocalization.lift_eq, hg₀]
    have hle : basicOpen f ≤ basicOpen (1 : A) := by
      rw [basicOpen_one]
      exact le_top
    have hcompat := congrFun (congrArg DFunLike.coe (hφ 1 f h1 hf hle))
      (algebraMap A (Localization.Away 1) a)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      restriction_algebraMap] at hcompat
    exact hcompat.symm
  · -- uniqueness
    intro Φ' hΦ'
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp only [RingHom.comp_apply]
    have hfac := congrFun (congrArg DFunLike.coe (hΦ' 1 h1))
      (algebraMap A (Localization.Away 1) a)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hfac
    rw [toAtPrime_algebraMap] at hfac
    rw [hfac, IsLocalization.lift_eq, hg₀]
    rfl

/-- **(v)**: two ring homomorphisms out of `A_𝔭` which agree on every `A_f` (`f ∉ 𝔭`) are equal;
the `A_f` detect the local ring. -/
theorem ringHom_ext_of_toAtPrime {T : Type*} [CommRing T]
    {Φ Ψ : Localization.AtPrime p →+* T}
    (h : ∀ (f : A) (hf : f ∉ p),
      Φ.comp (toAtPrime p f hf).toRingHom = Ψ.comp (toAtPrime p f hf).toRingHom) : Φ = Ψ := by
  obtain ⟨Θ, hΘ, huniq⟩ := existsUnique_stalk_lift p T
    (fun f hf => Φ.comp (toAtPrime p f hf).toRingHom)
    (fun f g hf hg hle => by
      rw [RingHom.comp_assoc,
        toAtPrime_restriction (p := p) (f := f) (g := g) hle hf hg])
  have hΦ : Φ = Θ := huniq Φ (fun f hf => rfl)
  have hΨ : Ψ = Θ := huniq Ψ (fun f hf => (h f hf).symm)
  rw [hΦ, hΨ]

/-- **(v)**, concretely: every element of the local ring `A_𝔭` is the image of an element of some
`A_f` with `f ∉ 𝔭`. -/
theorem exists_toAtPrime_eq (x : Localization.AtPrime p) :
    ∃ (f : A) (hf : f ∉ p), ∃ y : Localization.Away f, toAtPrime p f hf y = x := by
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq (M := p.primeCompl)
    (S := Localization.AtPrime p) x
  refine ⟨(s : A), s.2, IsLocalization.mk' (Localization.Away (s : A)) a
    ⟨(s : A), Submonoid.mem_powers (s : A)⟩, ?_⟩
  rw [← hs]
  have hg := isUnit_algebraMap_powers_atPrime p s.2 (f := (s : A))
  refine (IsLocalization.lift_mk'_spec (M := Submonoid.powers (s : A))
    (S := Localization.Away (s : A)) (P := Localization.AtPrime p)
    (g := algebraMap A (Localization.AtPrime p)) hg a _
    ⟨(s : A), Submonoid.mem_powers (s : A)⟩).mpr ?_
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) a s
  rw [mul_comm]
  exact hspec.symm

/-- **(v)**, injectivity half of the description of the direct limit: an element of `A_f`
(`f ∉ 𝔭`) which becomes zero in the local ring `A_𝔭` already becomes zero in the smaller ring
`A_{f g}` for some `g ∉ 𝔭`.  (This is the statement that the kernel of `A_f → A_𝔭` is the union of
the kernels of the restrictions `A_f → A_{f g}`, `g ∉ 𝔭`.) -/
theorem exists_restriction_eq_zero_of_toAtPrime_eq_zero {f : A} (hf : f ∉ p)
    {y : Localization.Away f} (hy : toAtPrime p f hf y = 0) :
    ∃ (g : A) (_ : g ∉ p), restriction (basicOpen_mul_le_left f g) y = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (x := f) y
  have ha' : y * algebraMap A (Localization.Away f) (f ^ m) =
      algebraMap A (Localization.Away f) a := by
    rw [map_pow]
    exact ha
  -- the numerator already dies in `A_𝔭`
  have hzero : algebraMap A (Localization.AtPrime p) a = 0 := by
    have h2 : toAtPrime p f hf (algebraMap A (Localization.Away f) a) = 0 := by
      rw [← ha', map_mul, toAtPrime_algebraMap, hy, zero_mul]
    rwa [toAtPrime_algebraMap] at h2
  -- hence it is killed by some `c ∉ 𝔭`
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl (Localization.AtPrime p)
    (x := a) (y := 0)).mp (by rw [hzero, map_zero])
  have hc' : (c : A) * a = 0 := by
    rw [mul_zero] at hc
    exact hc
  refine ⟨(c : A), c.2, ?_⟩
  -- in `A_{f c}` the numerator itself is zero
  have hca : algebraMap A (Localization.Away (f * (c : A))) a = 0 := by
    have hunit : IsUnit (algebraMap A (Localization.Away (f * (c : A))) (c : A)) :=
      isUnit_algebraMap_of_basicOpen_le (basicOpen_mul_le_right f (c : A))
    have h1 : algebraMap A (Localization.Away (f * (c : A))) (c : A) *
          algebraMap A (Localization.Away (f * (c : A))) a =
        algebraMap A (Localization.Away (f * (c : A))) (c : A) * 0 := by
      rw [← map_mul, hc', map_zero, mul_zero]
    exact (IsUnit.mul_right_inj hunit).mp h1
  have hle : basicOpen (f * (c : A)) ≤ basicOpen f := basicOpen_mul_le_left f (c : A)
  have hunit2 : IsUnit (algebraMap A (Localization.Away (f * (c : A))) (f ^ m)) := by
    rw [map_pow]
    exact (isUnit_algebraMap_of_basicOpen_le hle).pow m
  have h3 : restriction hle y *
      algebraMap A (Localization.Away (f * (c : A))) (f ^ m) = 0 := by
    calc restriction hle y * algebraMap A (Localization.Away (f * (c : A))) (f ^ m)
        = restriction hle y *
            restriction hle (algebraMap A (Localization.Away f) (f ^ m)) := by
          rw [restriction_algebraMap]
      _ = restriction hle (y * algebraMap A (Localization.Away f) (f ^ m)) := by rw [map_mul]
      _ = restriction hle (algebraMap A (Localization.Away f) a) := by rw [ha']
      _ = algebraMap A (Localization.Away (f * (c : A))) a := restriction_algebraMap hle a
      _ = 0 := hca
  have h4 : restriction hle y * algebraMap A (Localization.Away (f * (c : A))) (f ^ m) =
      0 * algebraMap A (Localization.Away (f * (c : A))) (f ^ m) := by
    rw [h3, zero_mul]
  exact (IsUnit.mul_left_inj hunit2).mp h4

/-- **(v)**: two elements of `A_f` (`f ∉ 𝔭`) with the same image in `A_𝔭` become equal in some
`A_{f g}` with `g ∉ 𝔭`. -/
theorem exists_restriction_eq_of_toAtPrime_eq {f : A} (hf : f ∉ p)
    {y y' : Localization.Away f} (h : toAtPrime p f hf y = toAtPrime p f hf y') :
    ∃ (g : A) (_ : g ∉ p),
      restriction (basicOpen_mul_le_left f g) y = restriction (basicOpen_mul_le_left f g) y' := by
  have hsub : toAtPrime p f hf (y - y') = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨g, hg, hgz⟩ := exists_restriction_eq_zero_of_toAtPrime_eq_zero p hf hsub
  exact ⟨g, hg, sub_eq_zero.mp (by rw [← map_sub]; exact hgz)⟩

end Stalk


end AtiyahMcdonald69.Ex_3_23

/-! ## Axiom checks -/

#print axioms AtiyahMcdonald69.Ex_3_23.exists_pow_eq_mul_of_basicOpen_le
#print axioms AtiyahMcdonald69.Ex_3_23.restriction
#print axioms AtiyahMcdonald69.Ex_3_23.restriction_mk'
#print axioms AtiyahMcdonald69.Ex_3_23.restriction_mk'_indep
#print axioms AtiyahMcdonald69.Ex_3_23.restriction_comp_restriction_of_basicOpen_eq
#print axioms AtiyahMcdonald69.Ex_3_23.restriction_comp_restriction
#print axioms AtiyahMcdonald69.Ex_3_23.sectionRingEquiv
#print axioms AtiyahMcdonald69.Ex_3_23.subsingleton_sectionRingEquiv
#print axioms AtiyahMcdonald69.Ex_3_23.toAtPrime
#print axioms AtiyahMcdonald69.Ex_3_23.existsUnique_stalk_lift
#print axioms AtiyahMcdonald69.Ex_3_23.ringHom_ext_of_toAtPrime
#print axioms AtiyahMcdonald69.Ex_3_23.exists_toAtPrime_eq
#print axioms AtiyahMcdonald69.Ex_3_23.exists_restriction_eq_zero_of_toAtPrime_eq_zero
#print axioms AtiyahMcdonald69.Ex_3_23.exists_restriction_eq_of_toAtPrime_eq
#print axioms AtiyahMcdonald69.Ex_3_23.presheafOnBasis
