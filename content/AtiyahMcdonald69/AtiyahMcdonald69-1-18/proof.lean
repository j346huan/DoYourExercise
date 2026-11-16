/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Chapter 1, Exercise 1.18.

Statement (AM 1969, Ch. 1, Exercise 18). Let `A` be a ring and let `X = Spec(A)`, the set of prime
ideals of `A` equipped with the Zariski topology; a point `x ∈ X` is a prime ideal `𝔭_x` of `A`.
Show the following.

  (a) The set `{x}` is closed if and only if `𝔭_x` is a maximal ideal.
  (b) `Cl({x}) = V(𝔭_x)`.
  (c) `y ∈ Cl({x})` if and only if `𝔭_x ⊆ 𝔭_y`.
  (d) `X` is a `T₀`-space: for distinct `x ≠ y` there is an open set containing exactly one of them.

Formalisation notes.
* `PrimeSpectrum A` is Mathlib's `Spec A` (Zariski topology `PrimeSpectrum.zariskiTopology`),
  `x.asIdeal : Ideal A` is the prime ideal `𝔭_x`, and `V(E)` is `PrimeSpectrum.zeroLocus E`:
  `PrimeSpectrum.mem_zeroLocus` says `x ∈ V(E) ↔ E ⊆ 𝔭_x`.
* The Zariski closed sets are exactly the zero loci (`PrimeSpectrum.isClosed_iff_zeroLocus_ideal`);
  this is the definition of the topology, not an exercise result.
* Part (a) is `part_a`, part (b) is `part_b`, part (c) is `part_c`, part (d) is `part_d`, stated in
  the elementary textbook form of `T₀` (two distinct points are separated by an open set); the
  equivalent Mathlib form is recorded as `part_d'`.  `solution` bundles the four parts.
* Book's argument for (a): if `𝔭` is maximal then `V(𝔭) = {𝔭}`; conversely if `{𝔭} = V(E)` and
  `𝔪 ⊇ 𝔭` is maximal, then `𝔪 ∈ V(E) = {𝔭}`, so `𝔪 = 𝔭`.  For (b): `V(𝔭)` is closed and contains
  `x`, and for a closed `C = V(I)` containing `x` we have `I ⊆ 𝔭`, hence `V(𝔭) ⊆ V(I) = C`, so
  `V(𝔭)` is the smallest closed set containing `x`.  For (d): if `𝔭_x ⊄ 𝔭_y` pick
  `f ∈ 𝔭_x \ 𝔭_y`; then the basic open `X_f` contains `y` and not `x`.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_1_18

open PrimeSpectrum

variable {A : Type*} [CommRing A]

/-- Exercise 1.18 (a): for a point `x` of `X = Spec A`, the singleton `{x}` is closed in the
Zariski topology if and only if the prime ideal `𝔭_x` is maximal. -/
theorem part_a (x : PrimeSpectrum A) :
    IsClosed ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal.IsMaximal := by
  constructor
  · -- `{x}` closed, say `{x} = V(I)`.  A maximal ideal `𝔪 ⊇ 𝔭_x` lies in `V(I)`, hence equals `𝔭_x`.
    intro hcl
    obtain ⟨I, hI⟩ :=
      (PrimeSpectrum.isClosed_iff_zeroLocus_ideal ({x} : Set (PrimeSpectrum A))).mp hcl
    have hx : x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [← hI]
      exact Set.mem_singleton x
    have hIx : (I : Set A) ⊆ (x.asIdeal : Set A) := (PrimeSpectrum.mem_zeroLocus x (I : Set A)).mp hx
    obtain ⟨m, hmmax, hxle⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
    have hmprime : m.IsPrime := hmmax.isPrime
    have hm_mem : (⟨m, hmprime⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact fun r hr => hxle (hIx hr)
    rw [← hI] at hm_mem
    have hm_eq : (⟨m, hmprime⟩ : PrimeSpectrum A) = x := by
      simpa only [Set.mem_singleton_iff] using hm_mem
    have hm : m = x.asIdeal := congrArg PrimeSpectrum.asIdeal hm_eq
    exact hm ▸ hmmax
  · -- `𝔭_x` maximal: any prime above `𝔭_x` equals `𝔭_x`, so `{x} = V(𝔭_x)` is closed.
    intro hmax
    refine (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
      ({x} : Set (PrimeSpectrum A))).mpr ⟨x.asIdeal, ?_⟩
    ext y
    rw [Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    constructor
    · rintro rfl
      exact le_rfl
    · intro hle
      exact PrimeSpectrum.ext (hmax.eq_of_le y.isPrime.ne_top hle).symm

/-- Exercise 1.18 (b): for a point `x` of `X = Spec A`, the closure of `{x}` is the zero locus
(the "variety") `V(𝔭_x)` of the prime ideal `𝔭_x`. -/
theorem part_b (x : PrimeSpectrum A) :
    closure ({x} : Set (PrimeSpectrum A)) = PrimeSpectrum.zeroLocus (x.asIdeal : Set A) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- `V(𝔭_x)` is closed and contains `x`, hence contains `Cl {x}`.
    exact (PrimeSpectrum.isClosed_zeroLocus (x.asIdeal : Set A)).closure_subset_iff.mpr
      (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact (PrimeSpectrum.mem_zeroLocus x (x.asIdeal : Set A)).mpr le_rfl)
  · -- `V(𝔭_x)` is contained in every closed set containing `x`, in particular in `Cl {x}`.
    obtain ⟨I, hI⟩ :=
      (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
        (closure ({x} : Set (PrimeSpectrum A)))).mp isClosed_closure
    have hx : x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [← hI]
      exact subset_closure (Set.mem_singleton x)
    have hIx : (I : Set A) ⊆ (x.asIdeal : Set A) := (PrimeSpectrum.mem_zeroLocus x (I : Set A)).mp hx
    calc PrimeSpectrum.zeroLocus (x.asIdeal : Set A)
        ⊆ PrimeSpectrum.zeroLocus (I : Set A) := PrimeSpectrum.zeroLocus_anti_mono hIx
      _ = closure ({x} : Set (PrimeSpectrum A)) := hI.symm

/-- Exercise 1.18 (c): `y` lies in the closure of `{x}` if and only if `𝔭_x ⊆ 𝔭_y`. -/
theorem part_c (x y : PrimeSpectrum A) :
    y ∈ closure ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal ≤ y.asIdeal := by
  rw [part_b, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]

/-- Exercise 1.18 (d), in the elementary textbook form of the `T₀` separation property: distinct
points `x ≠ y` of `X = Spec A` are separated by an open set, i.e. some open set contains exactly
one of them. -/
theorem part_d (x y : PrimeSpectrum A) (hxy : x ≠ y) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U)) := by
  have hne : x.asIdeal ≠ y.asIdeal := fun h => hxy (PrimeSpectrum.ext h)
  by_cases hle : x.asIdeal ≤ y.asIdeal
  · -- Then `𝔭_y ⊄ 𝔭_x`, so pick `f ∈ 𝔭_y \ 𝔭_x`; the basic open `X_f` contains `x`, not `y`.
    have hnot : ¬ y.asIdeal ≤ x.asIdeal := fun h => hne (le_antisymm hle h)
    obtain ⟨f, hfy, hfx⟩ :=
      Set.not_subset.mp (fun hsub : (y.asIdeal : Set A) ⊆ (x.asIdeal : Set A) =>
        hnot (SetLike.coe_subset_coe.mp hsub))
    refine ⟨(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)),
      PrimeSpectrum.isOpen_basicOpen, Or.inl ⟨?_, ?_⟩⟩
    · exact (PrimeSpectrum.mem_basicOpen f x).mpr hfx
    · intro hy
      exact ((PrimeSpectrum.mem_basicOpen f y).mp hy) hfy
  · -- Then `𝔭_x ⊄ 𝔭_y`; pick `f ∈ 𝔭_x \ 𝔭_y`; the basic open `X_f` contains `y`, not `x`.
    obtain ⟨f, hfx, hfy⟩ :=
      Set.not_subset.mp (fun hsub : (x.asIdeal : Set A) ⊆ (y.asIdeal : Set A) =>
        hle (SetLike.coe_subset_coe.mp hsub))
    refine ⟨(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)),
      PrimeSpectrum.isOpen_basicOpen, Or.inr ⟨?_, ?_⟩⟩
    · exact (PrimeSpectrum.mem_basicOpen f y).mpr hfy
    · intro hx
      exact ((PrimeSpectrum.mem_basicOpen f x).mp hx) hfx

/-- Exercise 1.18 (d), in the form of the topological `T₀` property of `Spec A`. -/
theorem part_d' : T0Space (PrimeSpectrum A) := by
  rw [t0Space_iff_exists_isOpen_xor_mem]
  intro x y hxy
  obtain ⟨U, hU, hxor⟩ := part_d x y hxy
  refine ⟨U, hU, ?_⟩
  rcases hxor with ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩
  · exact Or.inl ⟨hxU, hyU⟩
  · exact Or.inr ⟨hyU, hxU⟩

/-- Exercise 1.18, all four parts together. -/
theorem solution :
    (∀ x : PrimeSpectrum A, IsClosed ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal.IsMaximal) ∧
    (∀ x : PrimeSpectrum A,
      closure ({x} : Set (PrimeSpectrum A)) = PrimeSpectrum.zeroLocus (x.asIdeal : Set A)) ∧
    (∀ x y : PrimeSpectrum A,
      y ∈ closure ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal ≤ y.asIdeal) ∧
    (∀ x y : PrimeSpectrum A, x ≠ y →
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U))) :=
  ⟨part_a, part_b, part_c, part_d⟩

end AtiyahMcdonald69.Ex_1_18
