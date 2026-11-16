/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 3, Exercise 25.

**Book statement** (verbatim, §3 Exercise 25):
"Let `f : A → B`, `g : A → C` be ring homomorphisms and let `h : A → B ⊗_A C` be defined by
`h(x) = f(x) ⊗ g(x)`. Let `X, Y, Z, T` be the prime spectra of `A, B, C, B ⊗_A C`
respectively. Then `h*(T) = f*(Y) ∩ g*(Z)`."

**Audit of the statement.**  The formula printed in the book, `h(x) = f(x) ⊗ g(x)`, does *not*
define a ring homomorphism in general: it fails to be additive (see `bookH_not_additive` below,
with the explicit counterexample `A = B = C = ℤ`, where `h(1+1) = 4` but `h(1) + h(1) = 2`).
The official solutions manual resolves the ambiguity by defining
`h(x) = f(x) ⊗ 1 = 1 ⊗ g(x)`, i.e. `h` is the `A`-algebra structure map of `B ⊗_A C`, and this is
the reading under which the hint of the book ("the fibre `h*⁻¹(𝔭)` is the spectrum of
`(B ⊗_A C) ⊗_A k(𝔭)`") is true.  We therefore prove the theorem for the algebra structure map
(`mem_range_comap_tensorProduct`, `range_comap_tensorProduct`).  This loses nothing: the two
candidate maps have *exactly the same* fibres over prime ideals (`bookH_mem_iff`), because
`f(x) ⊗ g(x) = (algebraMap x) * (algebraMap x)` and for a prime ideal `Q`, `y * y ∈ Q ↔ y ∈ Q`.
Hence the induced maps on prime spectra coincide, and the printed equality of `h*(T)` with
`f*(Y) ∩ g*(Z)` holds for the printed formula as well, read through its fibres
(`bookH_mem_iff`, `range_bookH`).

No hypothesis (noetherian, flat, finitely generated, …) is needed; in particular the zero ring is
allowed.
-/
import Mathlib

open TensorProduct

namespace AtiyahMcdonald69.Ex_3_25

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-! ### The map `h` of the exercise -/

/-- The map of the exercise, `h(x) = f(x) ⊗ g(x)`, written in terms of the `A`-algebra structure
maps `f = algebraMap A B`, `g = algebraMap A C`.  (This map is not additive in general; see
`bookH_not_additive`.) -/
noncomputable def bookH (x : A) : B ⊗[A] C := algebraMap A B x ⊗ₜ[A] algebraMap A C x

/-- The map `h` of the exercise agrees with the `A`-algebra structure map of `B ⊗[A] C` up to
squaring: `h x = (algebraMap x) ^ 2`. -/
theorem bookH_eq_algebraMap_mul (x : A) :
    bookH (B := B) (C := C) x
      = algebraMap A (B ⊗[A] C) x * algebraMap A (B ⊗[A] C) x := by
  have h1 : algebraMap A (B ⊗[A] C) x = algebraMap A B x ⊗ₜ[A] (1 : C) :=
    Algebra.TensorProduct.algebraMap_apply (r := x)
  have h2 : algebraMap A (B ⊗[A] C) x = (1 : B) ⊗ₜ[A] algebraMap A C x :=
    h1.trans (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := B) (B := C) x)
  calc bookH (B := B) (C := C) x
      = algebraMap A B x ⊗ₜ[A] algebraMap A C x := rfl
    _ = (algebraMap A B x ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] algebraMap A C x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = algebraMap A (B ⊗[A] C) x * algebraMap A (B ⊗[A] C) x :=
        congrArg₂ (· * ·) h1.symm h2.symm

/-- For a *prime* ideal, an element and its square are in it simultaneously.  Hence `h` and the
`A`-algebra structure map of `B ⊗[A] C` have the same fibres over points of `Spec (B ⊗[A] C)`. -/
theorem bookH_mem_iff (Q : PrimeSpectrum (B ⊗[A] C)) (x : A) :
    bookH (B := B) (C := C) x ∈ Q.asIdeal
      ↔ algebraMap A (B ⊗[A] C) x ∈ Q.asIdeal := by
  rw [bookH_eq_algebraMap_mul]
  exact (Ideal.IsPrime.mul_mem_iff_mem_or_mem Q.isPrime).trans or_self_iff

/-! ### Tensor products over a field -/

section Field

variable (K : Type*) [Field K]

/-- A tensor product of two nontrivial vector spaces over a field is nontrivial. -/
theorem nontrivial_left_of_tensor {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (h : Nontrivial (V ⊗[K] W)) : Nontrivial V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Subsingleton V := hV
    exact absurd (inferInstance : Subsingleton (V ⊗[K] W))
      (not_subsingleton_iff_nontrivial.mpr h)
  · exact hV

/-- A tensor product of vector spaces over a field is nontrivial exactly when both factors are
nonzero.  This is the "vector space" ingredient of the book's argument. -/
theorem nontrivial_tensorProduct_iff_field (V W : Type*) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : Nontrivial (V ⊗[K] W) ↔ Nontrivial V ∧ Nontrivial W := by
  constructor
  · intro h
    refine ⟨nontrivial_left_of_tensor K h, ?_⟩
    exact nontrivial_left_of_tensor K ((Equiv.nontrivial_congr (TensorProduct.comm K V W).toEquiv).mp h)
  · rintro ⟨hV, hW⟩
    have := hV
    have := hW
    have : Module.FaithfullyFlat K V := inferInstance
    exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right K V).mpr hW

end Field

/-! ### The fibre criterion

Mathlib's `PrimeSpectrum.nontrivial_iff_mem_rangeComap` says: for an `A`-algebra `S` and a prime
`𝔭` of `A`, the fibre of `Spec S → Spec A` over `𝔭` is nonempty iff
`k(𝔭) ⊗[A] S` is nontrivial, where `k(𝔭) = 𝔭.ResidueField` is the residue field at `𝔭`.
This is exactly the first step of the book's hint. -/

/-- The base change `k(𝔭) ⊗[A] (B ⊗[A] C)` of a tensor product of algebras is (via
`TensorProduct.AlgebraTensorModule.distribBaseChange`) the tensor product over the residue field of
the base changes `k(𝔭) ⊗[A] B` and `k(𝔭) ⊗[A] C`, whence, over a field, the "both factors
nonzero" step. -/
theorem nontrivial_tensorProduct_residueField_iff (p : PrimeSpectrum A) :
    Nontrivial (p.asIdeal.ResidueField ⊗[A] (B ⊗[A] C)) ↔
      Nontrivial (p.asIdeal.ResidueField ⊗[A] B) ∧
        Nontrivial (p.asIdeal.ResidueField ⊗[A] C) := by
  set k := p.asIdeal.ResidueField
  exact (Equiv.nontrivial_congr
      (TensorProduct.AlgebraTensorModule.distribBaseChange (R := A) (A := k) (N := B)
        (Q := C)).toEquiv).trans
    (nontrivial_tensorProduct_iff_field k (k ⊗[A] B) (k ⊗[A] C))

/-! ### The main theorem -/

/-- **Exercise 3.25.**  For a prime `𝔭` of `A`:
`𝔭 ∈ h*(T) ↔ 𝔭 ∈ f*(Y) ∧ 𝔭 ∈ g*(Z)`, where `h : A → B ⊗[A] C` is the `A`-algebra structure
map (`h(x) = f(x) ⊗ 1 = 1 ⊗ g(x)`). -/
theorem mem_range_comap_tensorProduct (p : PrimeSpectrum A) :
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C))) ↔
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) ∧
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
  constructor
  · rintro ⟨Q, rfl⟩
    refine ⟨⟨PrimeSpectrum.comap Algebra.TensorProduct.includeLeftRingHom Q, ?_⟩,
      ⟨PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom Q, ?_⟩⟩
    · rw [Algebra.TensorProduct.algebraMap_def (R := A) (S := A) (A := B) (B := C),
        PrimeSpectrum.comap_comp_apply]
    · rw [Algebra.TensorProduct.algebraMap_def (R := A) (S := A) (A := B) (B := C),
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, PrimeSpectrum.comap_comp_apply]
  · rintro ⟨hB, hC⟩
    have hB' : Nontrivial (p.asIdeal.ResidueField ⊗[A] B) :=
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := B) p).mpr hB
    have hC' : Nontrivial (p.asIdeal.ResidueField ⊗[A] C) :=
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := C) p).mpr hC
    exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := B ⊗[A] C) p).mp
      ((nontrivial_tensorProduct_residueField_iff p).mpr ⟨hB', hC'⟩)

/-- **Exercise 3.25**, in the form of an equality of subsets of `Spec A`:
`h*(T) = f*(Y) ∩ g*(Z)`. -/
theorem range_comap_tensorProduct :
    Set.range (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C))) =
      Set.range (PrimeSpectrum.comap (algebraMap A B)) ∩
        Set.range (PrimeSpectrum.comap (algebraMap A C)) :=
  Set.ext mem_range_comap_tensorProduct

/-- **Exercise 3.25**, for the map `h` literally printed in the book: for every prime `Q` of
`B ⊗[A] C` the fibre of the printed map `h(x) = f(x) ⊗ g(x)` over `Q` is the same as the fibre of
the algebra structure map considered above.  Consequently the printed formula induces the same map
`Spec (B ⊗[A] C) → Spec A`. -/
theorem range_bookH :
    {p : PrimeSpectrum A |
        ∃ Q : PrimeSpectrum (B ⊗[A] C), ∀ x : A, (x ∈ p.asIdeal ↔ bookH (B := B) (C := C) x ∈ Q.asIdeal)}
      = Set.range (PrimeSpectrum.comap (algebraMap A B)) ∩
        Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
  ext p
  constructor
  · rintro ⟨Q, hQ⟩
    have hQ' : PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) Q = p := by
      refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← bookH_mem_iff Q x, ← hQ x]
    exact mem_range_comap_tensorProduct p |>.mp ⟨Q, hQ'⟩
  · intro hp
    obtain ⟨Q, hQ⟩ := mem_range_comap_tensorProduct p |>.mpr hp
    refine ⟨Q, fun x => ?_⟩
    rw [← hQ, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, bookH_mem_iff]

/-- The book's hint, made precise: the fibre of `h*` over `𝔭` is nonempty exactly when both
residue-field base changes `B ⊗_A k(𝔭)` and `C ⊗_A k(𝔭)` are nonzero rings. -/
theorem fiber_nonempty_iff (p : PrimeSpectrum A) :
    (∃ Q : PrimeSpectrum (B ⊗[A] C), PrimeSpectrum.comap (algebraMap A (B ⊗[A] C)) Q = p) ↔
      Nontrivial (p.asIdeal.ResidueField ⊗[A] B) ∧
        Nontrivial (p.asIdeal.ResidueField ⊗[A] C) :=
  (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := B ⊗[A] C) p).symm.trans
    (nontrivial_tensorProduct_residueField_iff p)

/-- **Exercise 3.25**, packaged as the single statement of the exercise. -/
theorem solution :
    Set.range (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C))) =
      Set.range (PrimeSpectrum.comap (algebraMap A B)) ∩
        Set.range (PrimeSpectrum.comap (algebraMap A C)) :=
  range_comap_tensorProduct

/-! ### Audit: the printed formula is not a ring homomorphism

The book's `h(x) = f(x) ⊗ g(x)` fails to be additive already for `A = B = C = ℤ` with `f = g = id`.
-/

/-- The map `x ↦ x ⊗ x` is **not** additive: in `ℤ ⊗[ℤ] ℤ` one has `2 ⊗ 2 ≠ 1 ⊗ 1 + 1 ⊗ 1`.
This shows that the formula `h(x) = f(x) ⊗ g(x)` printed in the book does not define a ring
homomorphism, and explains why the exercise is formalised for `h(x) = f(x) ⊗ 1 = 1 ⊗ g(x)`. -/
theorem bookH_not_additive :
    ¬ ∀ x y : ℤ, bookH (A := ℤ) (B := ℤ) (C := ℤ) (x + y)
      = bookH (A := ℤ) (B := ℤ) (C := ℤ) x + bookH (A := ℤ) (B := ℤ) (C := ℤ) y := by
  intro h
  have h2 := congrArg (TensorProduct.lid ℤ ℤ) (h 1 1)
  simp [bookH] at h2

/-! ### The exercise in the book's own hypothesis form -/

set_option linter.style.haveILetI false in
omit [Algebra A B] [Algebra A C] in
/-- **Exercise 3.25** for a pair of ring homomorphisms `f : A →+* B`, `g : A →+* C`, exactly in the
hypothesis form of the book: `B` and `C` are regarded as `A`-algebras via `f` and `g`
(`RingHom.toAlgebra`), and then `h*(T) = f*(Y) ∩ g*(Z)`. -/
theorem solution_ringHom (f : A →+* B) (g : A →+* C) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    Set.range (PrimeSpectrum.comap (algebraMap A (B ⊗[A] C))) =
      Set.range (PrimeSpectrum.comap (algebraMap A B)) ∩
        Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  exact range_comap_tensorProduct

end AtiyahMcdonald69.Ex_3_25
