import Mathlib

/-!
# Hartshorne, *Algebraic Geometry* (1977), Chapter I, Exercise 1.3

Source statement (Hartshorne 1977, I.1, Exercise 1.3):

> Let `Y` be the algebraic set in `A³` defined by the two polynomials `x ^ 2 - y * z` and
> `x * z - x`.  Show that `Y` is a union of three irreducible components.  Describe them, and
> find their prime ideals.

This file formalizes that statement for an algebraically closed field `k` (the standing
hypothesis of Chapter I), with `A³ = Fin 3 → k` the point set `{x, y, z} → k`, `x = X 0`,
`y = X 1`, `z = X 2`, Zariski closed sets the zero loci of ideals of polynomials (Hartshorne's
`Z(T)` for a set `T` of polynomials, since `zeroLocus (Ideal.span T) = {p | ∀ f ∈ T, f(p) = 0}`),
and the ideal of a closed set `Z` the ideal of all polynomials vanishing on `Z`
(`MvPolynomial.vanishingIdeal`).  The main results are:

* `Y_eq_union` : `Y = V(x, y) ∪ V(x, z) ∪ V(x ^ 2 - y, z - 1)` (the three components described);
* `isIrreducible_Vxy`, `isIrreducible_Vxz`, `isIrreducible_Vpar` : each of the three sets is
  irreducible (via the Nullstellensatz and primacy of `(x, y)`, `(x, z)`, `(x ^ 2 - y, z - 1)`);
* `not_subset_*` : no one of the three contains another;
* `irreducible_components` / `irreducible_components'` : the maximal (closed) irreducible subsets
  of `Y` are exactly these three sets, i.e. `Y` is the union of exactly three irreducible
  components;
* `vanishingIdeal_Vxy`, `vanishingIdeal_Vxz`, `vanishingIdeal_Vpar` : the prime ideals of the
  components are `(x, y)`, `(x, z)` and `(x ^ 2 - y, z - 1)`; and `vanishingIdeal_Y` : the ideal
  of `Y` itself is the intersection `(x, y) ⊓ (x, z) ⊓ (x ^ 2 - y, z - 1)`;
* `hartshorne_I_1_3` : all of the above assembled in one statement.

The primacy of the three ideals is proved exactly as in the source, through the quotient
identifications `k[x,y,z]/(x,y) ≅ k[z]`, `k[x,y,z]/(x,z) ≅ k[y]`,
`k[x,y,z]/(x ^ 2 - y, z - 1) ≅ k[x]` (Mathlib's `Polynomial.quotientSpanCXSubCAlgEquiv` and
`Polynomial.quotientSpanXSubCAlgEquiv`, transported through `MvPolynomial.finSuccEquiv`), which
exhibit the quotients as polynomial rings over `k` (in particular as domains).
-/

open MvPolynomial

namespace Hartshorne77.Ex_I_1_3

noncomputable section

section Points

variable {α : Type*}

/-- The point `(a, b, c)` of `α³`. -/
def pt (a b c : α) : Fin 3 → α := fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem pt_zero (a b c : α) : pt a b c 0 = a := rfl

@[simp] theorem pt_one (a b c : α) : pt a b c 1 = b := by
  simp [pt]

@[simp] theorem pt_two (a b c : α) : pt a b c 2 = c := by
  simp [pt]

end Points

/-! ## Generic lemmas on quotients of polynomial rings -/

theorem isDomain_of_ringEquiv {A B : Type*} [Semiring A] [Semiring B] (e : A ≃+* B)
    (h : IsDomain B) : IsDomain A :=
  @MulEquiv.isDomain A B _ _ h e.toMulEquiv

theorem isPrime_span_C_X_sub_C {R : Type*} [CommRing R] (a b : R) :
    (Ideal.span {Polynomial.C a, Polynomial.X - Polynomial.C b} : Ideal (Polynomial R)).IsPrime ↔
      (Ideal.span {a} : Ideal R).IsPrime := by
  have h1 : IsDomain (Polynomial R ⧸ Ideal.span {Polynomial.C a, Polynomial.X - Polynomial.C b}) ↔
      (Ideal.span {Polynomial.C a, Polynomial.X - Polynomial.C b} : Ideal (Polynomial R)).IsPrime :=
    Ideal.Quotient.isDomain_iff_prime _
  have h2 : IsDomain (R ⧸ Ideal.span {a}) ↔ (Ideal.span {a} : Ideal R).IsPrime :=
    Ideal.Quotient.isDomain_iff_prime _
  rw [← h1, ← h2]
  have e := Polynomial.quotientSpanCXSubCAlgEquiv a b
  exact ⟨fun h => isDomain_of_ringEquiv e.symm.toRingEquiv h,
    fun h => isDomain_of_ringEquiv e.toRingEquiv h⟩

theorem isPrime_span_X_sub_C {R : Type*} [CommRing R] [IsDomain R] (r : R) :
    (Ideal.span {Polynomial.X - Polynomial.C r} : Ideal (Polynomial R)).IsPrime := by
  have e := Polynomial.quotientSpanXSubCAlgEquiv r
  have h : IsDomain (Polynomial R ⧸ Ideal.span {Polynomial.X - Polynomial.C r}) :=
    isDomain_of_ringEquiv e.toRingEquiv inferInstance
  exact (Ideal.Quotient.isDomain_iff_prime _).mp h

/-! ## The Zariski topology on affine space -/
variable {k : Type*} [Field k]

/-- A subset of `k^n` is Zariski closed if it is the zero locus of an ideal of polynomials. -/
def IsZarClosed (n : ℕ) (s : Set (Fin n → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) k), s = MvPolynomial.zeroLocus k I

theorem zeroLocus_inf {n : ℕ} (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k (I ⊓ J) =
      MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J := by
  refine Set.Subset.antisymm (fun x hx => ?_)
    (Set.union_subset (MvPolynomial.zeroLocus_anti_mono inf_le_left)
      (MvPolynomial.zeroLocus_anti_mono inf_le_right))
  by_contra h
  rw [Set.mem_union, not_or] at h
  obtain ⟨h1, h2⟩ := h
  rw [MvPolynomial.mem_zeroLocus_iff] at hx
  simp only [MvPolynomial.mem_zeroLocus_iff, not_forall] at h1 h2
  obtain ⟨p, hpI, hpx⟩ := h1
  obtain ⟨q, hqJ, hqx⟩ := h2
  have h0 : MvPolynomial.aeval x (p * q) = 0 :=
    hx (p * q) (Ideal.mul_le_inf (Ideal.mul_mem_mul hpI hqJ))
  rw [map_mul] at h0
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact hpx h'
  · exact hqx h'

/-- the ideal of polynomials that vanish at `x` -/
def vanishingAt {n : ℕ} (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  MvPolynomial.vanishingIdeal k ({x} : Set (Fin n → k))

theorem mem_vanishingAt {n : ℕ} (x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    p ∈ vanishingAt x ↔ MvPolynomial.aeval x p = 0 := by
  simp [vanishingAt, MvPolynomial.mem_vanishingIdeal_iff]

theorem isZarClosed_sInter {n : ℕ} {A : Set (Set (Fin n → k))}
    (hA : ∀ s ∈ A, IsZarClosed n s) : IsZarClosed n (⋂₀ A) := by
  classical
  choose I hI using hA
  refine ⟨Ideal.span {p : MvPolynomial (Fin n) k |
    ∃ (s : Set (Fin n → k)) (hsA : s ∈ A), p ∈ I s hsA}, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rw [MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, Ideal.span_le]
    rintro p ⟨s, hsA, hps⟩
    change ∀ x ∈ (⋂₀ A), MvPolynomial.aeval x p = 0
    intro x hx
    have hxs : x ∈ s := by
      simpa only [Set.mem_sInter] using hx s hsA
    rw [hI s hsA] at hxs
    exact hxs p hps
  · intro x hx
    simp only [Set.mem_sInter] at hx ⊢
    intro s hsA
    rw [hI s hsA]
    simp only [MvPolynomial.mem_zeroLocus_iff] at hx ⊢
    intro p hp
    exact hx p (Ideal.subset_span ⟨s, hsA, hp⟩)

theorem isZarClosed_union {n : ℕ} {A B : Set (Fin n → k)}
    (hA : IsZarClosed n A) (hB : IsZarClosed n B) : IsZarClosed n (A ∪ B) := by
  obtain ⟨I, rfl⟩ := hA
  obtain ⟨J, rfl⟩ := hB
  exact ⟨I ⊓ J, (zeroLocus_inf I J).symm⟩

/-- The Zariski topology on affine `n`-space over `k`. -/
instance instZar (n : ℕ) : TopologicalSpace (Fin n → k) :=
  TopologicalSpace.ofClosed {s | IsZarClosed n s}
    ⟨⊤, by
      show (∅ : Set (Fin n → k)) = MvPolynomial.zeroLocus k ⊤
      rw [MvPolynomial.zeroLocus_top]
      rfl⟩
    (fun _ hA => isZarClosed_sInter hA)
    (fun _ hA _ hB => isZarClosed_union hA hB)

theorem isOpen_iff_isZarClosed {n : ℕ} {s : Set (Fin n → k)} :
    IsOpen s ↔ IsZarClosed n sᶜ := Iff.rfl

theorem isClosed_iff_isZarClosed {n : ℕ} {s : Set (Fin n → k)} :
    IsClosed s ↔ IsZarClosed n s := by
  rw [show IsClosed s ↔ IsOpen sᶜ from ⟨fun h => h.isOpen_compl, fun h => IsClosed.mk h⟩]
  rw [isOpen_iff_isZarClosed]
  simp

theorem isZarClosed_zeroLocus {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) :
    IsClosed (MvPolynomial.zeroLocus k I) :=
  (isClosed_iff_isZarClosed).mpr ⟨I, rfl⟩

/-! ## Primality of the three ideals -/
variable {k : Type*} [Field k]

theorem isPrime_map_iff_algEquiv {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) (I : Ideal A) :
    (I.map (e : A →+* B)).IsPrime ↔ I.IsPrime := by
  constructor
  · intro h
    have h' : ((I.map (e : A →+* B)).map ((e.symm : B ≃ₐ[k] A) : B →+* A)).IsPrime :=
      Ideal.map_isPrime_of_equiv (e.symm : B ≃ₐ[k] A)
    have hcomp : ((e.symm : B ≃ₐ[k] A) : B →+* A).comp ((e : A ≃ₐ[k] B) : A →+* B) =
        RingHom.id A := by
      ext x
      simp
    rwa [Ideal.map_map, hcomp, Ideal.map_id] at h'
  · intro h
    exact Ideal.map_isPrime_of_equiv (e : A ≃ₐ[k] B)

theorem isPrime_span_X {R : Type*} [CommRing R] [IsDomain R] :
    (Ideal.span {Polynomial.X} : Ideal (Polynomial R)).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `Ideal.span {X 0}` is prime in a multivariate polynomial ring. -/
theorem isPrime_span_X_zero (n : ℕ) :
    (Ideal.span {MvPolynomial.X (0 : Fin (n + 1))} :
      Ideal (MvPolynomial (Fin (n + 1)) k)).IsPrime := by
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.finSuccEquiv k n)]
  have himg : Ideal.map (MvPolynomial.finSuccEquiv k n :
      MvPolynomial (Fin (n + 1)) k →+* Polynomial (MvPolynomial (Fin n) k))
      (Ideal.span {MvPolynomial.X (0 : Fin (n + 1))}) = Ideal.span {Polynomial.X} := by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {(MvPolynomial.finSuccEquiv k n) (MvPolynomial.X (0 : Fin (n + 1)))} =
      Ideal.span {Polynomial.X}
    rw [MvPolynomial.finSuccEquiv_X_zero]
  rw [himg]
  exact isPrime_span_X

/-- `Ideal.span {x, y}` is prime in `k[x,y,z]`. -/
theorem isPrime_span_X0_X1 :
    (Ideal.span {MvPolynomial.X (0 : Fin 3), MvPolynomial.X 1} :
      Ideal (MvPolynomial (Fin 3) k)).IsPrime := by
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.finSuccEquiv k 2)]
  have himg : Ideal.map (MvPolynomial.finSuccEquiv k 2 :
      MvPolynomial (Fin 3) k →+* Polynomial (MvPolynomial (Fin 2) k))
      (Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}) =
      Ideal.span {Polynomial.C (MvPolynomial.X 0), Polynomial.X - Polynomial.C 0} := by
    rw [Ideal.map_span, Set.image_pair]
    show Ideal.span {(MvPolynomial.finSuccEquiv k 2) (MvPolynomial.X (0 : Fin 3)),
      (MvPolynomial.finSuccEquiv k 2) (MvPolynomial.X (Fin.succ (0 : Fin 2)))} =
      Ideal.span {Polynomial.C (MvPolynomial.X 0), Polynomial.X - Polynomial.C 0}
    rw [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    simp only [Polynomial.C_0, sub_zero]
    exact Ideal.span_pair_comm
  rw [himg, isPrime_span_C_X_sub_C]
  exact isPrime_span_X_zero 1

/-- `Ideal.span {x, z}` is prime in `k[x,y,z]`. -/
theorem isPrime_span_X0_X2 :
    (Ideal.span {MvPolynomial.X (0 : Fin 3), MvPolynomial.X 2} :
      Ideal (MvPolynomial (Fin 3) k)).IsPrime := by
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.renameEquiv k (Equiv.swap (1 : Fin 3) 2))]
  have himg : Ideal.map (MvPolynomial.renameEquiv k (Equiv.swap (1 : Fin 3) 2) :
      MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)
      (Ideal.span {MvPolynomial.X 0, MvPolynomial.X 2}) =
      Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1} := by
    rw [Ideal.map_span, Set.image_pair]
    show Ideal.span {(MvPolynomial.renameEquiv k (Equiv.swap (1 : Fin 3) 2)) (MvPolynomial.X 0),
      (MvPolynomial.renameEquiv k (Equiv.swap (1 : Fin 3) 2)) (MvPolynomial.X 2)} =
      Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}
    simp [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]
  rw [himg]
  exact isPrime_span_X0_X1

/-- `Ideal.span {x^2 - y, z - 1}` is prime in `k[x,y,z]`. -/
theorem isPrime_span_par :
    (Ideal.span {MvPolynomial.X (0 : Fin 3) ^ 2 - MvPolynomial.X 1,
      MvPolynomial.X 2 - 1} : Ideal (MvPolynomial (Fin 3) k)).IsPrime := by
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2))]
  have himg1 : Ideal.map (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2) :
      MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)
      (Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1, MvPolynomial.X 2 - 1}) =
      Ideal.span {MvPolynomial.X 2 ^ 2 - MvPolynomial.X 1, MvPolynomial.X 0 - 1} := by
    rw [Ideal.map_span, Set.image_pair]
    show Ideal.span {(MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2))
        (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1),
      (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2)) (MvPolynomial.X 2 - 1)} =
      Ideal.span {MvPolynomial.X 2 ^ 2 - MvPolynomial.X 1, MvPolynomial.X 0 - 1}
    simp [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      show (Equiv.swap (0 : Fin 3) 2) 1 = 1 from by decide]
  rw [himg1]
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.finSuccEquiv k 2)]
  have himg2 : Ideal.map (MvPolynomial.finSuccEquiv k 2 :
      MvPolynomial (Fin 3) k →+* Polynomial (MvPolynomial (Fin 2) k))
      (Ideal.span {MvPolynomial.X 2 ^ 2 - MvPolynomial.X 1, MvPolynomial.X 0 - 1}) =
      Ideal.span {Polynomial.C (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0),
        Polynomial.X - Polynomial.C 1} := by
    rw [Ideal.map_span, Set.image_pair]
    show Ideal.span {(MvPolynomial.finSuccEquiv k 2)
        (MvPolynomial.X (Fin.succ (1 : Fin 2)) ^ 2 - MvPolynomial.X (Fin.succ (0 : Fin 2))),
      (MvPolynomial.finSuccEquiv k 2) (MvPolynomial.X 0 - 1)} =
      Ideal.span {Polynomial.C (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0),
        Polynomial.X - Polynomial.C 1}
    simp only [map_sub, map_pow, map_one, MvPolynomial.finSuccEquiv_X_zero,
      MvPolynomial.finSuccEquiv_X_succ]
  rw [himg2, isPrime_span_C_X_sub_C]
  rw [← isPrime_map_iff_algEquiv (MvPolynomial.finSuccEquiv k 1)]
  have himg3 : Ideal.map (MvPolynomial.finSuccEquiv k 1 :
      MvPolynomial (Fin 2) k →+* Polynomial (MvPolynomial (Fin 1) k))
      (Ideal.span {MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0}) =
      Ideal.span {Polynomial.X - Polynomial.C (MvPolynomial.X 0 ^ 2)} := by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {(MvPolynomial.finSuccEquiv k 1)
        (MvPolynomial.X (Fin.succ (0 : Fin 1)) ^ 2 - MvPolynomial.X 0)} =
      Ideal.span {Polynomial.X - Polynomial.C (MvPolynomial.X 0 ^ 2)}
    simp only [map_sub, map_pow, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    rw [← Polynomial.C_pow]
    rw [← Ideal.span_singleton_neg (x := Polynomial.X - Polynomial.C (MvPolynomial.X 0 ^ 2))]
    congr 1
    ring_nf
  rw [himg3]
  exact isPrime_span_X_sub_C _

/-! ## The algebraic set `Y` and its three subsets -/

/-- The prime ideal `(x, y)`. -/
def pXY : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

/-- The prime ideal `(x, z)`. -/
def pXZ : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {MvPolynomial.X 0, MvPolynomial.X 2}

/-- The prime ideal `(x ^ 2 - y, z - 1)`. -/
def pPar : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1, MvPolynomial.X 2 - 1}

/-- The ideal `(x ^ 2 - y * z, x * z - x)` defining `Y`. -/
def IY : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 * MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0}

instance instPrimeXY : (pXY : Ideal (MvPolynomial (Fin 3) k)).IsPrime := isPrime_span_X0_X1
instance instPrimeXZ : (pXZ : Ideal (MvPolynomial (Fin 3) k)).IsPrime := isPrime_span_X0_X2
instance instPrimePar : (pPar : Ideal (MvPolynomial (Fin 3) k)).IsPrime := isPrime_span_par

/-- The algebraic set `Y = V(x ^ 2 - y * z, x * z - x) ⊆ k³` of Hartshorne I.1.3. -/
def Y : Set (Fin 3 → k) := MvPolynomial.zeroLocus (k := k) (K := k) IY

/-- The `z`-axis `V(x, y)`. -/
def Vxy : Set (Fin 3 → k) := MvPolynomial.zeroLocus (k := k) (K := k) pXY

/-- The `y`-axis `V(x, z)`. -/
def Vxz : Set (Fin 3 → k) := MvPolynomial.zeroLocus (k := k) (K := k) pXZ

/-- The parabola `V(x ^ 2 - y, z - 1)` in the plane `z = 1`. -/
def Vpar : Set (Fin 3 → k) := MvPolynomial.zeroLocus (k := k) (K := k) pPar

theorem mem_Y {p : Fin 3 → k} : p ∈ Y ↔ p 0 ^ 2 = p 1 * p 2 ∧ p 0 * p 2 = p 0 := by
  simp [Y, IY, MvPolynomial.zeroLocus_span, sub_eq_zero]

theorem mem_Vxy {p : Fin 3 → k} : p ∈ Vxy ↔ p 0 = 0 ∧ p 1 = 0 := by
  simp [Vxy, pXY, MvPolynomial.zeroLocus_span]

theorem mem_Vxz {p : Fin 3 → k} : p ∈ Vxz ↔ p 0 = 0 ∧ p 2 = 0 := by
  simp [Vxz, pXZ, MvPolynomial.zeroLocus_span]

theorem mem_Vpar {p : Fin 3 → k} : p ∈ Vpar ↔ p 0 ^ 2 = p 1 ∧ p 2 = 1 := by
  simp only [Vpar, pPar, MvPolynomial.zeroLocus_span, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, aeval_X, map_sub, map_pow, map_one,
    sub_eq_zero]

@[simp] theorem isClosed_Y : IsClosed (Y : Set (Fin 3 → k)) := isZarClosed_zeroLocus (k := k) (IY : Ideal (MvPolynomial (Fin 3) k))
@[simp] theorem isClosed_Vxy : IsClosed (Vxy : Set (Fin 3 → k)) := isZarClosed_zeroLocus (k := k) (pXY : Ideal (MvPolynomial (Fin 3) k))
@[simp] theorem isClosed_Vxz : IsClosed (Vxz : Set (Fin 3 → k)) := isZarClosed_zeroLocus (k := k) (pXZ : Ideal (MvPolynomial (Fin 3) k))
@[simp] theorem isClosed_Vpar : IsClosed (Vpar : Set (Fin 3 → k)) := isZarClosed_zeroLocus (k := k) (pPar : Ideal (MvPolynomial (Fin 3) k))

/-- **The decomposition**: `Y = V(x, y) ∪ V(x, z) ∪ V(x ^ 2 - y, z - 1)`. -/
theorem Y_eq_union : (Y : Set (Fin 3 → k)) = Vxy ∪ Vxz ∪ Vpar := by
  ext p
  simp only [Set.mem_union, mem_Y, mem_Vxy, mem_Vxz, mem_Vpar]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : p 0 * (p 2 - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h2'
    · have h12 : p 1 * p 2 = 0 := by rw [← h1, h0]; ring
      rcases mul_eq_zero.mp h12 with h1' | h2''
      · exact Or.inl (Or.inl ⟨h0, h1'⟩)
      · exact Or.inl (Or.inr ⟨h0, h2''⟩)
    · refine Or.inr ⟨?_, sub_eq_zero.mp h2'⟩
      rw [sub_eq_zero.mp h2'] at h1
      simpa using h1
  · rintro ((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h1, h2⟩)
    · rw [h0, h1]
      constructor <;> ring
    · rw [h0, h2]
      constructor <;> ring
    · rw [h1, h2]
      constructor <;> ring

/-- The three components are pairwise incomparable. -/
theorem not_subset_Vxy_Vxz : ¬ (Vxy : Set (Fin 3 → k)) ⊆ Vxz := by
  intro h
  have h1 : (pt 0 0 1 : Fin 3 → k) ∈ Vxy := by simp [mem_Vxy]
  have h2 : (pt 0 0 1 : Fin 3 → k) ∈ Vxz := h h1
  simp [mem_Vxz] at h2

theorem not_subset_Vxy_Vpar : ¬ (Vxy : Set (Fin 3 → k)) ⊆ Vpar := by
  intro h
  have h1 : (pt 0 0 0 : Fin 3 → k) ∈ Vxy := by simp [mem_Vxy]
  have h2 : (pt 0 0 0 : Fin 3 → k) ∈ Vpar := h h1
  simp [mem_Vpar] at h2

theorem not_subset_Vxz_Vxy : ¬ (Vxz : Set (Fin 3 → k)) ⊆ Vxy := by
  intro h
  have h1 : (pt 0 1 0 : Fin 3 → k) ∈ Vxz := by simp [mem_Vxz]
  have h2 : (pt 0 1 0 : Fin 3 → k) ∈ Vxy := h h1
  simp [mem_Vxy] at h2

theorem not_subset_Vxz_Vpar : ¬ (Vxz : Set (Fin 3 → k)) ⊆ Vpar := by
  intro h
  have h1 : (pt 0 0 0 : Fin 3 → k) ∈ Vxz := by simp [mem_Vxz]
  have h2 : (pt 0 0 0 : Fin 3 → k) ∈ Vpar := h h1
  simp [mem_Vpar] at h2

theorem not_subset_Vpar_Vxy : ¬ (Vpar : Set (Fin 3 → k)) ⊆ Vxy := by
  intro h
  have h1 : (pt 1 1 1 : Fin 3 → k) ∈ Vpar := by simp [mem_Vpar]
  have h2 : (pt 1 1 1 : Fin 3 → k) ∈ Vxy := h h1
  simp [mem_Vxy] at h2

theorem not_subset_Vpar_Vxz : ¬ (Vpar : Set (Fin 3 → k)) ⊆ Vxz := by
  intro h
  have h1 : (pt 1 1 1 : Fin 3 → k) ∈ Vpar := by simp [mem_Vpar]
  have h2 : (pt 1 1 1 : Fin 3 → k) ∈ Vxz := h h1
  simp [mem_Vxz] at h2

/-! ## Zero loci of prime ideals -/

variable [IsAlgClosed k]

/-- A prime ideal has nonempty zero locus (weak Nullstellensatz). -/
theorem zeroLocus_nonempty_of_isPrime {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    (MvPolynomial.zeroLocus k P).Nonempty := by
  obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal P (show P.IsPrime from inferInstance).ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hMmax
  refine ⟨x, ?_⟩
  rw [MvPolynomial.mem_zeroLocus_iff]
  intro p hp
  have hpM : p ∈ M := hPM hp
  rw [hx] at hpM
  exact (mem_vanishingAt x p).mp hpM

theorem inf_le_of_isPrime {R : Type*} [CommSemiring R] {P I J : Ideal R} (hP : P.IsPrime)
    (h : I ⊓ J ≤ P) : I ≤ P ∨ J ≤ P := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hI, hJ⟩ := hc
  obtain ⟨a, haI, haP⟩ := Set.not_subset.mp hI
  obtain ⟨b, hbJ, hbP⟩ := Set.not_subset.mp hJ
  have hab : a * b ∈ I ⊓ J := Ideal.mul_le_inf (Ideal.mul_mem_mul haI hbJ)
  exact hbP ((hP.mem_or_mem (h hab)).resolve_left haP)

/-- The zero locus of a prime ideal is irreducible. -/
theorem isIrreducible_zeroLocus_of_isPrime {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k))
    [P.IsPrime] : IsIrreducible (MvPolynomial.zeroLocus k P) := by
  refine ⟨zeroLocus_nonempty_of_isPrime P, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro Z₁ Z₂ hZ₁ hZ₂ hsub
  obtain ⟨I₁, rfl⟩ := (isClosed_iff_isZarClosed).mp hZ₁
  obtain ⟨I₂, rfl⟩ := (isClosed_iff_isZarClosed).mp hZ₂
  have hsub' : MvPolynomial.zeroLocus k P ⊆ MvPolynomial.zeroLocus k (I₁ ⊓ I₂) := by
    rw [zeroLocus_inf]
    exact hsub
  have hle : I₁ ⊓ I₂ ≤ P := by
    have h1 : I₁ ⊓ I₂ ≤ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k (I₁ ⊓ I₂)) :=
      MvPolynomial.le_vanishingIdeal_zeroLocus (K := k) (I₁ ⊓ I₂)
    have h2 : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k (I₁ ⊓ I₂)) ≤
        MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) :=
      MvPolynomial.vanishingIdeal_anti_mono hsub'
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (k := k) (K := k) (P := P)] at h2
    exact h1.trans h2
  rcases inf_le_of_isPrime (P := P) (show P.IsPrime from inferInstance) hle with h | h
  · exact Or.inl (MvPolynomial.zeroLocus_anti_mono h)
  · exact Or.inr (MvPolynomial.zeroLocus_anti_mono h)

/-! ## Irreducibility of the three subsets -/

theorem isIrreducible_Vxy : IsIrreducible (Vxy : Set (Fin 3 → k)) := isIrreducible_zeroLocus_of_isPrime (k := k) (pXY : Ideal (MvPolynomial (Fin 3) k))
theorem isIrreducible_Vxz : IsIrreducible (Vxz : Set (Fin 3 → k)) := isIrreducible_zeroLocus_of_isPrime (k := k) (pXZ : Ideal (MvPolynomial (Fin 3) k))
theorem isIrreducible_Vpar : IsIrreducible (Vpar : Set (Fin 3 → k)) := isIrreducible_zeroLocus_of_isPrime (k := k) (pPar : Ideal (MvPolynomial (Fin 3) k))

/-! ## The components -/
/-- The ideals of the three components. -/
theorem vanishingIdeal_Vxy : MvPolynomial.vanishingIdeal k (Vxy : Set (Fin 3 → k)) = pXY :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (k := k) (K := k) (P := pXY)

theorem vanishingIdeal_Vxz : MvPolynomial.vanishingIdeal k (Vxz : Set (Fin 3 → k)) = pXZ :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (k := k) (K := k) (P := pXZ)

theorem vanishingIdeal_Vpar : MvPolynomial.vanishingIdeal k (Vpar : Set (Fin 3 → k)) = pPar :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (k := k) (K := k) (P := pPar)

omit [IsAlgClosed k] in
theorem vanishingIdeal_union {A B : Set (Fin 3 → k)} :
    MvPolynomial.vanishingIdeal k (A ∪ B) =
      MvPolynomial.vanishingIdeal k A ⊓ MvPolynomial.vanishingIdeal k B := by
  ext f
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Ideal.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

/-- The ideal of `Y` is the intersection of the three prime ideals (not their sum). -/
theorem vanishingIdeal_Y : MvPolynomial.vanishingIdeal k (Y : Set (Fin 3 → k)) = pXY ⊓ pXZ ⊓ pPar := by
  rw [Y_eq_union, vanishingIdeal_union, vanishingIdeal_union, vanishingIdeal_Vxy,
    vanishingIdeal_Vxz, vanishingIdeal_Vpar]

omit [IsAlgClosed k] in
/-- Every irreducible subset of `Y` is contained in one of the three components. -/
theorem subset_of_irreducible {C : Set (Fin 3 → k)} (hC : IsIrreducible C)
    (hCY : C ⊆ (Y : Set (Fin 3 → k))) :
    C ⊆ Vxy ∨ C ⊆ Vxz ∨ C ⊆ Vpar := by
  have hsub : C ⊆ Vxy ∪ (Vxz ∪ Vpar) := by
    rw [← Set.union_assoc, ← Y_eq_union]
    exact hCY
  have split := isPreirreducible_iff_isClosed_union_isClosed.mp hC.2
  rcases split Vxy (Vxz ∪ Vpar) isClosed_Vxy (isClosed_Vxz.union isClosed_Vpar) hsub with h | h
  · exact Or.inl h
  · rcases split Vxz Vpar isClosed_Vxz isClosed_Vpar h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-- **`Y` is a union of exactly three irreducible components**: the irreducible closed subsets of
`Y` that are maximal with respect to inclusion are precisely `V(x, y)`, `V(x, z)` and
`V(x ^ 2 - y, z - 1)`. -/
theorem irreducible_components {C : Set (Fin 3 → k)} :
    Maximal (fun x => IsClosed x ∧ IsIrreducible x ∧ x ⊆ (Y : Set (Fin 3 → k))) C ↔
      C = Vxy ∨ C = Vxz ∨ C = Vpar := by
  have hYxy : (Vxy : Set (Fin 3 → k)) ⊆ Y := by
    rw [Y_eq_union]; exact Set.subset_union_left.trans Set.subset_union_left
  have hYxz : (Vxz : Set (Fin 3 → k)) ⊆ Y := by
    rw [Y_eq_union]; exact Set.subset_union_right.trans Set.subset_union_left
  have hYpar : (Vpar : Set (Fin 3 → k)) ⊆ Y := by
    rw [Y_eq_union]; exact Set.subset_union_right
  constructor
  · rintro ⟨⟨hcl, hC, hCY'⟩, hmax⟩
    rcases subset_of_irreducible hC hCY' with h | h | h
    · left
      exact le_antisymm h (hmax (y := Vxy) ⟨isClosed_Vxy, isIrreducible_Vxy, hYxy⟩ h)
    · right; left
      exact le_antisymm h (hmax (y := Vxz) ⟨isClosed_Vxz, isIrreducible_Vxz, hYxz⟩ h)
    · right; right
      exact le_antisymm h (hmax (y := Vpar) ⟨isClosed_Vpar, isIrreducible_Vpar, hYpar⟩ h)
  · rintro (rfl | rfl | rfl)
    · refine ⟨⟨isClosed_Vxy, isIrreducible_Vxy, hYxy⟩, ?_⟩
      intro b hb hsub
      rcases subset_of_irreducible hb.2.1 hb.2.2 with h | h | h
      · exact h
      · exact absurd (hsub.trans h) not_subset_Vxy_Vxz
      · exact absurd (hsub.trans h) not_subset_Vxy_Vpar
    · refine ⟨⟨isClosed_Vxz, isIrreducible_Vxz, hYxz⟩, ?_⟩
      intro b hb hsub
      rcases subset_of_irreducible hb.2.1 hb.2.2 with h | h | h
      · exact absurd (hsub.trans h) not_subset_Vxz_Vxy
      · exact h
      · exact absurd (hsub.trans h) not_subset_Vxz_Vpar
    · refine ⟨⟨isClosed_Vpar, isIrreducible_Vpar, hYpar⟩, ?_⟩
      intro b hb hsub
      rcases subset_of_irreducible hb.2.1 hb.2.2 with h | h | h
      · exact absurd (hsub.trans h) not_subset_Vpar_Vxy
      · exact absurd (hsub.trans h) not_subset_Vpar_Vxz
      · exact h

omit [IsAlgClosed k] in
/-- Hartshorne (I.1) defines an irreducible component of `Y` to be a maximal irreducible subset of
`Y`; since `Y` is closed, this is the same as a maximal closed irreducible subset of `Y`. -/
theorem maximal_irreducible_iff {C : Set (Fin 3 → k)} :
    Maximal (fun x => IsIrreducible x ∧ x ⊆ (Y : Set (Fin 3 → k))) C ↔
      Maximal (fun x => IsClosed x ∧ IsIrreducible x ∧ x ⊆ (Y : Set (Fin 3 → k))) C := by
  constructor
  · rintro ⟨⟨hC, hCY'⟩, hmax⟩
    have hcl : IsClosed C := by
      have h1 : IsIrreducible (closure C) := hC.closure
      have h2 : closure C ⊆ (Y : Set (Fin 3 → k)) := closure_minimal hCY' isClosed_Y
      exact isClosed_of_closure_subset (hmax ⟨h1, h2⟩ subset_closure)
    refine ⟨⟨hcl, hC, hCY'⟩, ?_⟩
    intro b hb hsub
    exact hmax ⟨hb.2.1, hb.2.2⟩ hsub
  · rintro ⟨⟨hcl, hC, hCY'⟩, hmax⟩
    refine ⟨⟨hC, hCY'⟩, ?_⟩
    intro b hb hsub
    have h1 : IsIrreducible (closure b) := hb.1.closure
    have h2 : closure b ⊆ (Y : Set (Fin 3 → k)) := closure_minimal hb.2 isClosed_Y
    exact subset_closure.trans (hmax ⟨isClosed_closure, h1, h2⟩ (hsub.trans subset_closure))

/-- **`Y` has exactly three irreducible components** in Hartshorne's sense: the maximal
irreducible subsets of `Y` are `V(x, y)`, `V(x, z)` and `V(x ^ 2 - y, z - 1)`. -/
theorem irreducible_components' {C : Set (Fin 3 → k)} :
    Maximal (fun x => IsIrreducible x ∧ x ⊆ (Y : Set (Fin 3 → k))) C ↔
      C = Vxy ∨ C = Vxz ∨ C = Vpar :=
  maximal_irreducible_iff.trans irreducible_components

/-! ### Sanity checks on the definitions -/

/-- A point of the `y`-axis lies on `Y`. -/
example : (pt 0 1 0 : Fin 3 → k) ∈ Y := by
  simp [mem_Y]

/-- A point of the parabola `z = 1`, `y = x ^ 2` lies on `Y`. -/
example : (pt 1 1 1 : Fin 3 → k) ∈ Y := by
  simp [mem_Y]

/-- The point `(1, 0, 0)` does not lie on `Y`. -/
example : (pt 1 0 0 : Fin 3 → k) ∉ Y := by
  simp [mem_Y]

/-- The three components really are distinct closed sets. -/
example : (Vxy : Set (Fin 3 → k)) ≠ Vxz := by
  intro h
  exact not_subset_Vxy_Vxz (le_of_eq h)

/-- **Hartshorne I.1.3**, assembled: `Y` is the union of the three irreducible components
`V(x, y)`, `V(x, z)` and `V(x ^ 2 - y, z - 1)`, no one of which contains another, and their
prime ideals are `(x, y)`, `(x, z)` and `(x ^ 2 - y, z - 1)`. -/
theorem hartshorne_I_1_3 :
    (Y : Set (Fin 3 → k)) = Vxy ∪ Vxz ∪ Vpar ∧
    IsIrreducible (Vxy : Set (Fin 3 → k)) ∧
    IsIrreducible (Vxz : Set (Fin 3 → k)) ∧
    IsIrreducible (Vpar : Set (Fin 3 → k)) ∧
    ¬ (Vxy : Set (Fin 3 → k)) ⊆ Vxz ∧ ¬ (Vxy : Set (Fin 3 → k)) ⊆ Vpar ∧
    ¬ (Vxz : Set (Fin 3 → k)) ⊆ Vxy ∧ ¬ (Vxz : Set (Fin 3 → k)) ⊆ Vpar ∧
    ¬ (Vpar : Set (Fin 3 → k)) ⊆ Vxy ∧ ¬ (Vpar : Set (Fin 3 → k)) ⊆ Vxz ∧
    MvPolynomial.vanishingIdeal k (Vxy : Set (Fin 3 → k)) = pXY ∧
    MvPolynomial.vanishingIdeal k (Vxz : Set (Fin 3 → k)) = pXZ ∧
    MvPolynomial.vanishingIdeal k (Vpar : Set (Fin 3 → k)) = pPar :=
  ⟨Y_eq_union, isIrreducible_Vxy, isIrreducible_Vxz, isIrreducible_Vpar,
    not_subset_Vxy_Vxz, not_subset_Vxy_Vpar, not_subset_Vxz_Vxy, not_subset_Vxz_Vpar,
    not_subset_Vpar_Vxy, not_subset_Vpar_Vxz, vanishingIdeal_Vxy, vanishingIdeal_Vxz,
    vanishingIdeal_Vpar⟩

end

end Hartshorne77.Ex_I_1_3

#print axioms Hartshorne77.Ex_I_1_3.hartshorne_I_1_3
#print axioms Hartshorne77.Ex_I_1_3.Y_eq_union
#print axioms Hartshorne77.Ex_I_1_3.vanishingIdeal_Vxy
#print axioms Hartshorne77.Ex_I_1_3.vanishingIdeal_Vxz
#print axioms Hartshorne77.Ex_I_1_3.vanishingIdeal_Vpar
#print axioms Hartshorne77.Ex_I_1_3.vanishingIdeal_Y
#print axioms Hartshorne77.Ex_I_1_3.isIrreducible_Vxy
#print axioms Hartshorne77.Ex_I_1_3.isIrreducible_Vxz
#print axioms Hartshorne77.Ex_I_1_3.isIrreducible_Vpar
#print axioms Hartshorne77.Ex_I_1_3.irreducible_components
#print axioms Hartshorne77.Ex_I_1_3.irreducible_components'
#print axioms Hartshorne77.Ex_I_1_3.maximal_irreducible_iff
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vxy_Vxz
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vxy_Vpar
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vxz_Vxy
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vxz_Vpar
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vpar_Vxy
#print axioms Hartshorne77.Ex_I_1_3.not_subset_Vpar_Vxz
#print axioms Hartshorne77.Ex_I_1_3.isPrime_span_X0_X1
#print axioms Hartshorne77.Ex_I_1_3.isPrime_span_X0_X2
#print axioms Hartshorne77.Ex_I_1_3.isPrime_span_par
#print axioms Hartshorne77.Ex_I_1_3.zeroLocus_nonempty_of_isPrime
#print axioms Hartshorne77.Ex_I_1_3.isIrreducible_zeroLocus_of_isPrime
#print axioms Hartshorne77.Ex_I_1_3.mem_Y
#print axioms Hartshorne77.Ex_I_1_3.instPrimeXY
