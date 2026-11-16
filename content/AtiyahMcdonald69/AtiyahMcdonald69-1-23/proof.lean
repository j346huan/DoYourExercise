/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter 1, Exercise 23 (the exercise on p. 14 stated in terms of the Boolean ring
of Exercise 11 and the basic open sets `X_f` of Exercise 17).

Statement (Atiyah–Macdonald, Chapter 1, Exercise 23).
Let `A` be a Boolean ring (`x * x = x` for all `x ∈ A`) and let `X = Spec(A)`,
with `X_f = {p ∈ X : f ∉ p}` for `f ∈ A`.

  (i)   For each `f ∈ A`, the set `X_f` is both open and closed in `X`.
  (ii)  Let `f₁, …, fₙ ∈ A`. Then `X_{f₁} ∪ ⋯ ∪ X_{fₙ} = X_f` for some `f ∈ A`.
  (iii) The sets `X_f` are the only subsets of `X` which are both open and closed.
  (iv)  `X` is a compact Hausdorff space.

Below `X_f` is `PrimeSpectrum.basicOpen f` and `X` is `PrimeSpectrum A`.

The book's standing convention is that all rings have `1 ≠ 0`; consistently the
statements are made for an arbitrary Boolean ring (they in fact also hold for the zero
ring, whose spectrum is empty, so no `Nontrivial` hypothesis is mathematically required
and none is added).

The proofs follow the book's solution, with its two dependencies verified here rather
than assumed:
* from Exercise 1.11 only the identity `f * (1 - f) = 0` is used (with `1 - f` the
  "complement" of `f` in a Boolean ring);
* from Exercise 17 only the definition `X_f = {p : f ∉ p}` and the fact that the `X_f`
  form a basis of the topology of `Spec A` are used
  (`PrimeSpectrum.isTopologicalBasis_basic_opens`).

Part (ii) is proved with the *explicit* element `f = 1 - (1 - f₁) ⋯ (1 - fₙ)`
(for `n = 0` the empty product is `1`, giving `f = 0` and the empty union), and part
(iii) uses (ii) together with quasi-compactness of the closed set `Y`, as in the book.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_1_23

open PrimeSpectrum

variable {A : Type*} [BooleanRing A]
variable {ι : Type*}

/-! ### Elementary identities in a Boolean ring -/

/-- In a Boolean ring, `x * (1 - x) = 0`. -/
theorem mul_one_sub (x : A) : x * (1 - x) = 0 := by
  rw [mul_sub, mul_one, BooleanRing.mul_self, sub_self]

/-- In a Boolean ring, `(1 - x) * x = 0`. -/
theorem one_sub_mul (x : A) : (1 - x) * x = 0 := by
  rw [sub_mul, one_mul, BooleanRing.mul_self, sub_self]

/-- In a Boolean ring, `x + (1 - x) = 1`. -/
theorem add_one_sub (x : A) : x + (1 - x) = 1 := by
  rw [add_comm, sub_add_cancel]

/-- In a Boolean ring, `(1 - x) + x = 1`. -/
theorem one_sub_add (x : A) : (1 - x) + x = 1 := sub_add_cancel 1 x

/-- In a Boolean ring, `1 - x` is idempotent whenever `x` is. -/
theorem isIdempotentElem_one_sub {x : A} (hx : IsIdempotentElem x) :
    IsIdempotentElem (1 - x) := by
  have hx' : x * x = x := hx
  show (1 - x) * (1 - x) = 1 - x
  calc (1 - x) * (1 - x) = 1 - x - x + x * x := by ring
    _ = 1 - x - x + x := by rw [hx']
    _ = 1 - x := by ring

/-- A product of elements of the form `1 - f i` is idempotent in a Boolean ring. -/
theorem isIdempotentElem_prod_one_sub (s : Finset ι) (f : ι → A) :
    IsIdempotentElem (s.prod fun i => 1 - f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [IsIdempotentElem]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, mul_comm (1 - f a)]
      exact ih.mul (isIdempotentElem_one_sub (BooleanRing.isIdempotentElem (f a)))

/-! ### The sets `X_f` as zero sets

In a Boolean ring `X_f = V(1 - f)`: a prime contains `1 - f` exactly when it does not
contain `f`.  This is what makes `X_f` closed. -/

/-- `X_f = V(1 - f)`: a prime ideal omits `f` iff it contains `1 - f`. -/
theorem basicOpen_eq_zeroLocus_one_sub (f : A) :
    (basicOpen f : Set (PrimeSpectrum A)) = zeroLocus ({1 - f} : Set A) :=
  basicOpen_eq_zeroLocus_of_mul_add f (1 - f) (mul_one_sub f) (add_one_sub f)

/-- `X_{1 - x} = V(x)`. -/
theorem basicOpen_one_sub_eq_zeroLocus (x : A) :
    (basicOpen (1 - x) : Set (PrimeSpectrum A)) = zeroLocus ({x} : Set A) :=
  basicOpen_eq_zeroLocus_of_mul_add (1 - x) x (one_sub_mul x) (one_sub_add x)

/-- A prime ideal contains a finite product iff it contains one of the factors, so the
union of the zero sets `V(g i)` is the zero set of the product. -/
theorem iUnion_zeroLocus_singleton_prod (s : Finset ι) (g : ι → A) :
    (⋃ i ∈ s, zeroLocus ({g i} : Set A)) = zeroLocus ({s.prod g} : Set A) := by
  ext p
  simp only [Set.mem_iUnion, mem_zeroLocus, Set.singleton_subset_iff]
  constructor
  · rintro ⟨i, hi, hmem⟩
    exact (Ideal.IsPrime.prod_mem_iff (s := s) (x := g) (p := p.asIdeal)).mpr ⟨i, hi, hmem⟩
  · intro hmem
    obtain ⟨i, hi, hmem'⟩ :=
      (Ideal.IsPrime.prod_mem_iff (s := s) (x := g) (p := p.asIdeal)).mp hmem
    exact ⟨i, hi, hmem'⟩

/-! ### Part (i) -/

/-- **Exercise 1.23 (i)**: for each `f ∈ A` the set `X_f` is both open and closed. -/
theorem part_i (f : A) : IsClopen (basicOpen f : Set (PrimeSpectrum A)) :=
  isClopen_basicOpen_of_mul_add f (1 - f) (mul_one_sub f) (add_one_sub f)

/-- **Exercise 1.23 (i)**, unfolded: `X_f` is closed and open (`X_f = V(1 - f)`). -/
theorem part_i' (f : A) :
    IsClosed (basicOpen f : Set (PrimeSpectrum A)) ∧
      IsOpen (basicOpen f : Set (PrimeSpectrum A)) := part_i f

/-! ### Part (ii) -/

/-- **Exercise 1.23 (ii)**, for a family indexed by a finset and with the explicit
element `1 - ∏ i ∈ s, (1 - f i)`: a finite union of `X_f`'s is a single `X_f`. -/
theorem biUnion_basicOpen (s : Finset ι) (f : ι → A) :
    (⋃ i ∈ s, (basicOpen (f i) : Set (PrimeSpectrum A))) =
      basicOpen (1 - s.prod fun i => 1 - f i) := by
  classical
  have hP : (⋃ i ∈ s, (basicOpen (f i) : Set (PrimeSpectrum A))) =
      zeroLocus ({s.prod fun i => 1 - f i} : Set A) := by
    simp_rw [basicOpen_eq_zeroLocus_one_sub]
    exact iUnion_zeroLocus_singleton_prod s fun i => 1 - f i
  rw [hP, basicOpen_one_sub_eq_zeroLocus]

/-- **Exercise 1.23 (ii)**, with the explicit element `f = 1 - ∏ i, (1 - f i)`. -/
theorem part_ii_explicit {n : ℕ} (f : Fin n → A) :
    (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum A))) = basicOpen (1 - ∏ i, (1 - f i)) := by
  simpa using biUnion_basicOpen (Finset.univ : Finset (Fin n)) f

/-- **Exercise 1.23 (ii)**: for `f₁, …, fₙ ∈ A` there is `f ∈ A` with
`X_{f₁} ∪ ⋯ ∪ X_{fₙ} = X_f`; one may take `f = 1 - (1 - f₁) ⋯ (1 - fₙ)`. -/
theorem part_ii {n : ℕ} (f : Fin n → A) :
    ∃ g : A, (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum A))) = basicOpen g :=
  ⟨_, part_ii_explicit f⟩

/-! ### Part (iii) -/

/-- **Exercise 1.23 (iii)**: the only subsets of `X = Spec(A)` which are both open and
closed are the sets `X_f`. -/
theorem part_iii (Y : Set (PrimeSpectrum A)) (hY : IsClopen Y) :
    ∃ f : A, Y = basicOpen f := by
  classical
  -- Step 1: the basic open sets contained in `Y` cover `Y`, because `Y` is open.
  have hcover : Y ⊆ ⋃ r : {x : A // (basicOpen x : Set (PrimeSpectrum A)) ⊆ Y},
      (basicOpen r.1 : Set (PrimeSpectrum A)) := by
    intro p hp
    -- `Y` is open, so some basic open set `X_r` with `p ∈ X_r` lies in `Y`.
    obtain ⟨v, ⟨r, rfl⟩, hpr, hrY⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hY.2
    exact Set.mem_iUnion.mpr ⟨⟨r, hrY⟩, hpr⟩
  -- Step 2: `Y` is closed in the quasi-compact space `X`, hence quasi-compact, so a
  -- finite subfamily of these basic open sets already covers `Y`.
  obtain ⟨t, ht⟩ := hY.1.isCompact.elim_finite_subcover
    (fun r : {x : A // (basicOpen x : Set (PrimeSpectrum A)) ⊆ Y} =>
      (basicOpen r.1 : Set (PrimeSpectrum A)))
    (fun _ => isOpen_basicOpen) hcover
  have hsub : (⋃ r ∈ t, (basicOpen r.1 : Set (PrimeSpectrum A))) ⊆ Y := by
    intro p hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨r, hp⟩ := hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨-, hpr⟩ := hp
    exact r.2 hpr
  -- Step 3: this finite union of basic open sets is a single `X_f` by part (ii).
  have hYeq : Y = ⋃ r ∈ t, (basicOpen r.1 : Set (PrimeSpectrum A)) :=
    le_antisymm ht hsub
  exact ⟨1 - t.prod fun r => 1 - r.1, hYeq.trans (biUnion_basicOpen t fun r => r.1)⟩

/-! ### Part (iv) -/

/-- In a Boolean ring, if `x` lies in a prime `p` then `1 - x` does not. -/
theorem one_sub_notMem {p : PrimeSpectrum A} {x : A} (h : x ∈ p.asIdeal) :
    1 - x ∉ p.asIdeal := by
  intro hc
  refine p.asIdeal.notMem_of_isUnit isUnit_one ?_
  have h1 := p.asIdeal.add_mem hc h
  rwa [one_sub_add] at h1

/-- In a Boolean ring, `X_x` and `X_{1-x}` are disjoint. -/
theorem disjoint_basicOpen_one_sub (x : A) :
    Disjoint (basicOpen x : Set (PrimeSpectrum A)) (basicOpen (1 - x)) := by
  refine Set.disjoint_left.mpr fun r hr hr' => ?_
  rcases r.isPrime.mem_or_mem_of_mul_eq_zero (mul_one_sub x) with h | h
  · exact hr h
  · exact hr' h

/-- **Exercise 1.23 (iv)**, Hausdorff part: distinct primes are separated by the
disjoint basic open sets `X_x` and `X_{1-x}`. -/
theorem t2Space_primeSpectrum : T2Space (PrimeSpectrum A) := by
  refine ⟨fun p q hpq => ?_⟩
  have hne : p.asIdeal ≠ q.asIdeal := fun h => hpq (PrimeSpectrum.ext h)
  have key : ∃ x : A, (x ∈ p.asIdeal ∧ x ∉ q.asIdeal) ∨ (x ∈ q.asIdeal ∧ x ∉ p.asIdeal) := by
    by_contra h
    rw [not_exists] at h
    refine hne (SetLike.ext fun x => ⟨?_, ?_⟩)
    · intro hx
      by_contra hx'
      exact h x (Or.inl ⟨hx, hx'⟩)
    · intro hx
      by_contra hx'
      exact h x (Or.inr ⟨hx, hx'⟩)
  obtain ⟨x, ⟨hxp, hxq⟩ | ⟨hxq, hxp⟩⟩ := key
  · exact ⟨_, _, isOpen_basicOpen, isOpen_basicOpen, one_sub_notMem hxp, hxq,
      (disjoint_basicOpen_one_sub x).symm⟩
  · exact ⟨_, _, isOpen_basicOpen, isOpen_basicOpen, hxp, one_sub_notMem hxq,
      disjoint_basicOpen_one_sub x⟩

/-- **Exercise 1.23 (iv)**: `Spec(A)` is a compact Hausdorff space. -/
theorem part_iv : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) :=
  ⟨inferInstance, t2Space_primeSpectrum⟩

/-- **Exercise 1.23** of Atiyah–Macdonald, all four parts at once. -/
theorem solution :
    (∀ f : A, IsClopen (basicOpen f : Set (PrimeSpectrum A))) ∧
    (∀ {n : ℕ} (f : Fin n → A),
      ∃ g : A, (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum A))) = basicOpen g) ∧
    (∀ Y : Set (PrimeSpectrum A), IsClopen Y → ∃ f : A, Y = basicOpen f) ∧
    (CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A)) :=
  ⟨part_i, fun f => part_ii f, part_iii, part_iv⟩

end AtiyahMcdonald69.Ex_1_23
