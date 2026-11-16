import Mathlib

/-!
# Atiyah–Macdonald, Exercise 3.24

Let `A` be a ring, `X = Spec A`, and for a basic open set `U = X_f` let `A(U) = A_f`
(Exercise 3.23), with the restriction homomorphisms `ρ : A(U) → A(U')` for `U' ⊆ U`.

The exercise asks: if `(U_i)_{i ∈ I}` is a covering of `X` by basic open sets and
`s_i ∈ A(U_i)` are compatible on the intersections `U_i ∩ U_j = X_{f_i f_j}`, then there is a
unique `s ∈ A = A(X)` whose image in `A(U_i)` is `s_i` for all `i`.

We formalize this with the basic open sets presented by generators `f : ι → A`:
`U _ i = X_{f i}`, and `U_i ∩ U_j = X_{f i * f j}`.  The hypothesis "the `U_i` cover `X`"
is equivalent to `Ideal.span (Set.range f) = ⊤` (`cover_iff` below).  `A(U)` is the actual
localization `A_f = Localization.Away f`, and the restriction maps are the canonical maps
`A_f →+* A_{fg}`; the intersection is modelled by `A_{f i * f j}`, which is legitimate by
Exercise 3.23 (i) (the ring `A(U)` depends only on the open set `U`).

## Main results

* `Asec` : `A(U)` for `U = X_f`, namely `A_f`; `AsecOneEquiv` : `A(X_1) ≃+* A`.
* `resLeft`, `resRight` : the two restriction maps `A(X_f) →+* A(X_{fg})`, `A(X_g) →+* A(X_{fg})`
  of Exercise 3.23 (ii).
* `Compat` : the compatibility condition on a family of sections.
* `existsUnique_of_fintype` : the gluing property for a finite cover.
* `existsUnique_glue` / `solution` : **Exercise 3.24**, existence and uniqueness of `s ∈ A`.
* `eq_zero_of_forall_algebraMap_eq_zero`, `algebraMap_injective_pi` : the uniqueness principle
  ("an element vanishing on a basic open cover is zero").
* `bijective_to_compatible` : the sheaf condition, as a bijection between `A` and compatible
  families of sections.
* `cover_iff` : covering by the `X_{f i}` ↔ the `f i` generate the unit ideal.
* `uniqueness_fails_without_cover`, `existence_fails_without_cover` : the cover hypothesis is
  not redundant.
-/

namespace AtiyahMcdonald69.Ex_3_24

universe u

open scoped BigOperators

section Basic

variable {A : Type u} [CommRing A]

/-- `A(U)` for the basic open set `U = X_f`: the localization `A_f` (Exercise 3.23). -/
abbrev Asec (f : A) : Type u := Localization.Away f

/-- The restriction homomorphism `A(X_f) →+* A(X_{f * g})` ("`X_{fg} ⊆ X_f`"):
the canonical map `A_f → A_{fg}`, i.e. `ρ` of Exercise 3.23(ii). -/
noncomputable def resRight (f g : A) : Asec f →+* Asec (f * g) :=
  IsLocalization.Away.awayToAwayRight (x := f) (y := g) (S := Asec f) (P := Asec (f * g))

/-- The restriction homomorphism `A(X_g) →+* A(X_{f * g})` ("`X_{fg} ⊆ X_g`"):
the other leg of the restriction to the intersection `X_f ∩ X_g = X_{fg}`. -/
noncomputable def resLeft (f g : A) : Asec g →+* Asec (f * g) :=
  IsLocalization.Away.awayToAwayLeft (x := g) (y := f) (S := Asec g) (P := Asec (f * g))

@[simp]
lemma resRight_algebraMap (f g : A) (a : A) :
    resRight f g (algebraMap A (Asec f) a) = algebraMap A (Asec (f * g)) a :=
  IsLocalization.Away.awayToAwayRight_eq (x := f) (y := g) (S := Asec f) (P := Asec (f * g)) a

@[simp]
lemma resLeft_algebraMap (f g : A) (a : A) :
    resLeft f g (algebraMap A (Asec g) a) = algebraMap A (Asec (f * g)) a :=
  IsLocalization.Away.awayToAwayLeft_eq (x := g) (y := f) (S := Asec g) (P := Asec (f * g)) a

/-- `A(X) = A(X_1) ≅ A`: the ring attached to the whole space `X = X_1` is `A` itself
(Exercise 3.23), which is why the conclusion of Exercise 3.24 asks for `s ∈ A`. -/
noncomputable def AsecOneEquiv : A ≃+* Asec (1 : A) :=
  (IsLocalization.atOne A (Asec (1 : A))).toRingEquiv

/-- Compatibility of a family of sections `s i ∈ A(U i)` on the intersections: for every pair
`i j`, the images of `s i` and `s j` in `A(U i ∩ U j) = A(X_{f i * f j})` agree. -/
def Compat {ι : Type*} (f : ι → A) (s : ∀ i, Asec (f i)) : Prop :=
  ∀ i j, resLeft (f i) (f j) (s j) = resRight (f i) (f j) (s i)

end Basic

section Finite

variable {A : Type u} [CommRing A] {ι : Type*}

/-- Vanishing at all members of a *finite* basic open cover implies vanishing.
(First paragraph of the natural solution of Exercise 3.24: uniqueness.) -/
theorem eq_zero_of_fintype [Fintype ι] (f : ι → A)
    (hspan : Ideal.span (Set.range f) = ⊤) (d : A)
    (hd : ∀ i, algebraMap A (Asec (f i)) d = 0) : d = 0 := by
  classical
  have hex : ∀ i, ∃ n : ℕ, (f i) ^ n * d = 0 := by
    intro i
    obtain ⟨n, hn⟩ :=
      IsLocalization.Away.exists_of_eq (x := f i) (S := Asec (f i)) (a := d) (b := 0)
        (by rw [hd i, map_zero])
    exact ⟨n, by simpa using hn⟩
  choose n hn using hex
  let M := ∑ i, n i
  have hspanM : Ideal.span (Set.range fun i => (f i) ^ M) = ⊤ := by
    have hrange : Set.range (fun i => (f i) ^ M) = (fun x : A => x ^ M) '' Set.range f := by
      ext x
      simp [Set.mem_range]
    rw [hrange, Ideal.span_pow_eq_top (Set.range f) hspan M]
  obtain ⟨c, hc⟩ : ∃ c : ι → A, ∑ i, c i * (f i) ^ M = 1 :=
    Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hspanM)
  have hMd : ∀ i, (f i) ^ M * d = 0 := by
    intro i
    have h1 : n i ≤ M := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    calc (f i) ^ M * d = ((f i) ^ (M - n i) * (f i) ^ (n i)) * d := by
          rw [pow_sub_mul_pow (f i) h1]
      _ = (f i) ^ (M - n i) * ((f i) ^ (n i) * d) := by ring
      _ = 0 := by rw [hn i, mul_zero]
  calc d = 1 * d := (one_mul d).symm
    _ = (∑ i, c i * (f i) ^ M) * d := by rw [hc]
    _ = ∑ i, c i * ((f i) ^ M * d) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by simp [hMd]

/-- If `x ^ m * u = x ^ m * v` then `x ^ n * u = x ^ n * v` for `n ≥ m`. -/
lemma pow_mul_congr {R : Type*} [CommRing R] (x u v : R) {m n : ℕ} (hmn : m ≤ n)
    (hE : x ^ m * u = x ^ m * v) : x ^ n * u = x ^ n * v := by
  calc x ^ n * u = (x ^ (n - m) * x ^ m) * u := by rw [pow_sub_mul_pow x hmn]
    _ = x ^ (n - m) * (x ^ m * u) := by ring
    _ = x ^ (n - m) * (x ^ m * v) := by rw [hE]
    _ = (x ^ (n - m) * x ^ m) * v := by ring
    _ = x ^ n * v := by rw [pow_sub_mul_pow x hmn]

/-- **Exercise 3.24, finite cover case**: sections over a finite basic open cover that agree on
the pairwise intersections glue uniquely to an element of `A = A(X)`. -/
theorem existsUnique_of_fintype [Fintype ι] (f : ι → A)
    (hspan : Ideal.span (Set.range f) = ⊤) (s : ∀ i, Asec (f i)) (h : Compat f s) :
    ∃! r : A, ∀ i, algebraMap A (Asec (f i)) r = s i := by
  classical
  -- Step 1: write every section as a fraction with denominator a power of `f i`, of the shape
  -- `s i * (f i) ^ n i = r i`.
  obtain ⟨r, n, hr⟩ : ∃ (r : ι → A) (n : ι → ℕ),
      ∀ i, s i * algebraMap A (Asec (f i)) ((f i) ^ (n i)) = algebraMap A (Asec (f i)) (r i) :=
    ⟨fun i => (IsLocalization.Away.sec (f i) (s i)).1,
     fun i => (IsLocalization.Away.sec (f i) (s i)).2,
     fun i => IsLocalization.Away.sec_spec (x := f i) (s i)⟩
  -- Step 2: pass to a common exponent `N` (the maximum of the `n i`).
  set N : ℕ := Finset.univ.sup n with hN
  have hnN : ∀ i, n i ≤ N := fun i => Finset.le_sup (f := n) (Finset.mem_univ i)
  set r' : ι → A := fun i => (f i) ^ (N - n i) * r i with hr'def
  have hr' : ∀ i, s i * algebraMap A (Asec (f i)) ((f i) ^ N) = algebraMap A (Asec (f i)) (r' i) := by
    intro i
    have hsplit : (f i) ^ N = (f i) ^ (N - n i) * (f i) ^ (n i) :=
      (pow_sub_mul_pow (f i) (hnN i)).symm
    calc s i * algebraMap A (Asec (f i)) ((f i) ^ N)
        = s i * (algebraMap A (Asec (f i)) ((f i) ^ (N - n i)) *
            algebraMap A (Asec (f i)) ((f i) ^ (n i))) := by rw [← map_mul, hsplit]
      _ = (s i * algebraMap A (Asec (f i)) ((f i) ^ (n i))) *
            algebraMap A (Asec (f i)) ((f i) ^ (N - n i)) := by ring
      _ = algebraMap A (Asec (f i)) (r i) * algebraMap A (Asec (f i)) ((f i) ^ (N - n i)) := by
            rw [hr i]
      _ = algebraMap A (Asec (f i)) (r' i) := by
            rw [← map_mul]
            congr 1
            rw [hr'def]
            ring
  -- Step 3: compatibility, cleared of denominators.
  have key : ∀ i j : ι, ∃ m : ℕ,
      (f i * f j) ^ m * (r' i * (f j) ^ N) = (f i * f j) ^ m * (r' j * (f i) ^ N) := by
    intro i j
    refine IsLocalization.Away.exists_of_eq (x := f i * f j) (S := Asec (f i * f j))
      (a := r' i * (f j) ^ N) (b := r' j * (f i) ^ N) ?_
    have h1 : resRight (f i) (f j) (s i) * algebraMap A (Asec (f i * f j)) ((f i) ^ N)
        = algebraMap A (Asec (f i * f j)) (r' i) := by
      have := congrArg (resRight (f i) (f j)) (hr' i)
      simpa using this
    have h2 : resLeft (f i) (f j) (s j) * algebraMap A (Asec (f i * f j)) ((f j) ^ N)
        = algebraMap A (Asec (f i * f j)) (r' j) := by
      have := congrArg (resLeft (f i) (f j)) (hr' j)
      simpa using this
    calc algebraMap A (Asec (f i * f j)) (r' i * (f j) ^ N)
        = algebraMap A (Asec (f i * f j)) (r' i) * algebraMap A (Asec (f i * f j)) ((f j) ^ N) := by
            rw [map_mul, map_pow]
      _ = (resRight (f i) (f j) (s i) * algebraMap A (Asec (f i * f j)) ((f i) ^ N)) *
            algebraMap A (Asec (f i * f j)) ((f j) ^ N) := by rw [h1]
      _ = (resLeft (f i) (f j) (s j) * algebraMap A (Asec (f i * f j)) ((f j) ^ N)) *
            algebraMap A (Asec (f i * f j)) ((f i) ^ N) := by
            rw [← h i j]
            ring
      _ = algebraMap A (Asec (f i * f j)) (r' j) * algebraMap A (Asec (f i * f j)) ((f i) ^ N) := by
            rw [h2]
      _ = algebraMap A (Asec (f i * f j)) (r' j * (f i) ^ N) := by simp only [map_mul, map_pow]
  -- Step 4: a common exponent `N'` for the compatibility.
  choose m hm using key
  set N' : ℕ := (Finset.univ : Finset (ι × ι)).sup (fun p => m p.1 p.2) with hN'
  have hmN' : ∀ i j, m i j ≤ N' := fun i j =>
    Finset.le_sup (f := fun p : ι × ι => m p.1 p.2) (Finset.mem_univ (i, j))
  have key' : ∀ i j, (f i * f j) ^ N' * (r' i * (f j) ^ N)
      = (f i * f j) ^ N' * (r' j * (f i) ^ N) :=
    fun i j => pow_mul_congr _ _ _ (hmN' i j) (hm i j)
  -- Step 5: clear the remaining `(f j) ^ N` factors.
  set N'' : ℕ := N' + N with hN''
  set r'' : ι → A := fun i => (f i) ^ N' * r' i with hr''def
  have hr'' : ∀ i, s i * algebraMap A (Asec (f i)) ((f i) ^ N'') = algebraMap A (Asec (f i)) (r'' i) := by
    intro i
    have hsplit : (f i) ^ N'' = (f i) ^ N' * (f i) ^ N := by rw [hN'', pow_add]
    calc s i * algebraMap A (Asec (f i)) ((f i) ^ N'')
        = s i * (algebraMap A (Asec (f i)) ((f i) ^ N') *
            algebraMap A (Asec (f i)) ((f i) ^ N)) := by rw [← map_mul, hsplit]
      _ = (s i * algebraMap A (Asec (f i)) ((f i) ^ N)) *
            algebraMap A (Asec (f i)) ((f i) ^ N') := by ring
      _ = algebraMap A (Asec (f i)) (r' i) * algebraMap A (Asec (f i)) ((f i) ^ N') := by
            rw [hr' i]
      _ = algebraMap A (Asec (f i)) (r'' i) := by
            rw [← map_mul]
            congr 1
            rw [hr''def]
            ring
  have hcompat'' : ∀ i j, r'' i * (f j) ^ N'' = r'' j * (f i) ^ N'' := by
    intro i j
    calc r'' i * (f j) ^ N''
        = (f i * f j) ^ N' * (r' i * (f j) ^ N) := by rw [hr''def, hN'', pow_add, mul_pow]; ring
      _ = (f i * f j) ^ N' * (r' j * (f i) ^ N) := key' i j
      _ = r'' j * (f i) ^ N'' := by rw [hr''def, hN'', pow_add, mul_pow]; ring
  -- Step 6: the `(f i) ^ N''` generate the unit ideal, so a Bézout-type sum is available.
  have hspan'' : Ideal.span (Set.range fun i => (f i) ^ N'') = ⊤ := by
    have hrange : Set.range (fun i => (f i) ^ N'') = (fun x : A => x ^ N'') '' Set.range f := by
      ext x
      simp [Set.mem_range]
    rw [hrange, Ideal.span_pow_eq_top (Set.range f) hspan N'']
  obtain ⟨c, hc⟩ : ∃ c : ι → A, ∑ i, c i * (f i) ^ N'' = 1 :=
    Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hspan'')
  -- Step 7: the glued element.
  have hglue : ∀ i, algebraMap A (Asec (f i)) (∑ j, c j * r'' j) = s i := by
    intro i
    have hkey : (∑ j, c j * r'' j) * (f i) ^ N'' = r'' i := by
      calc (∑ j, c j * r'' j) * (f i) ^ N''
          = ∑ j, c j * (r'' j * (f i) ^ N'') := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, c j * (r'' i * (f j) ^ N'') :=
              Finset.sum_congr rfl fun j _ => by rw [hcompat'' j i]
        _ = (∑ j, c j * (f j) ^ N'') * r'' i := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
        _ = r'' i := by rw [hc, one_mul]
    refine (IsLocalization.Away.algebraMap_pow_isUnit (x := f i) (S := Asec (f i)) N'').mul_left_inj.mp ?_
    rw [← map_pow, ← map_mul, hkey, hr'' i]
  refine ⟨∑ j, c j * r'' j, hglue, fun r2 hr2 => ?_⟩
  refine sub_eq_zero.mp (eq_zero_of_fintype f hspan (r2 - ∑ j, c j * r'' j) fun i => ?_)
  rw [map_sub, hr2 i, hglue i, sub_self]

end Finite

section General

variable {A : Type u} [CommRing A] {ι : Type*}

/-- A covering family of basic open sets `X_{f i}` contains a finite subcover. -/
theorem exists_finset_cover (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤) :
    ∃ u : Finset ι, Ideal.span (Set.range fun i : {i // i ∈ u} => f i.1) = ⊤ := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ι →₀ A, c.sum (fun i a => a * f i) = 1 :=
    Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp ((Ideal.eq_top_iff_one _).mp hspan)
  refine ⟨c.support, (Ideal.eq_top_iff_one _).mpr ?_⟩
  have hmem : ∀ i ∈ c.support, f i ∈ Ideal.span (Set.range fun i : {i // i ∈ c.support} => f i.1) :=
    fun i hi => Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩
  rw [← hc, Finsupp.sum]
  exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hmem i hi)

/-- Enlarging a finite cover keeps it a cover. -/
theorem span_insert_eq_top [DecidableEq ι] (f : ι → A) {u : Finset ι}
    (hu : Ideal.span (Set.range fun i : {i // i ∈ u} => f i.1) = ⊤) (j : ι) :
    Ideal.span (Set.range fun i : {i // i ∈ insert j u} => f i.1) = ⊤ := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range fun i : {i // i ∈ u} => f i.1) :=
    (Ideal.eq_top_iff_one _).mp hu
  refine (Ideal.eq_top_iff_one _).mpr ?_
  have hle : Ideal.span (Set.range fun i : {i // i ∈ u} => f i.1) ≤
      Ideal.span (Set.range fun i : {i // i ∈ insert j u} => f i.1) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, rfl⟩
  exact hle h1

/-- An element of `A` that vanishes in every member of a basic open cover is zero.
This is the uniqueness half of Exercise 3.24 (stated for an arbitrary index set). -/
theorem eq_zero_of_forall_algebraMap_eq_zero (f : ι → A)
    (hspan : Ideal.span (Set.range f) = ⊤) (d : A)
    (hd : ∀ i, algebraMap A (Asec (f i)) d = 0) : d = 0 := by
  obtain ⟨u, hu⟩ := exists_finset_cover f hspan
  exact eq_zero_of_fintype (fun i : {i // i ∈ u} => f i.1) hu d fun i => hd i.1

/-- **Atiyah–Macdonald, Exercise 3.24.**  Let `X = Spec A` and let `(X_{f i})_{i ∈ I}` be a
covering of `X` by basic open sets.  For each `i`, let `s i ∈ A(X_{f i})` be such that for every
pair `i, j` the images of `s i` and `s j` in `A(X_{f i} ∩ X_{f j}) = A(X_{f i * f j})` agree.
Then there is a unique `s ∈ A = A(X)` whose image in `A(X_{f i})` is `s i` for all `i`. -/
theorem existsUnique_glue (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (s : ∀ i, Asec (f i)) (h : Compat f s) :
    ∃! r : A, ∀ i, algebraMap A (Asec (f i)) r = s i := by
  classical
  obtain ⟨u, hu⟩ := exists_finset_cover f hspan
  -- glue over a finite subcover
  obtain ⟨r, hr, huniq⟩ :=
    existsUnique_of_fintype (fun i : {i // i ∈ u} => f i.1) hu (fun i => s i.1) (fun i j => h i.1 j.1)
  -- check the remaining members of the cover by enlarging the finite subcover
  have hall : ∀ j, algebraMap A (Asec (f j)) r = s j := by
    intro j
    obtain ⟨rj, hrj, -⟩ :=
      existsUnique_of_fintype (fun i : {i // i ∈ insert j u} => f i.1) (span_insert_eq_top f hu j)
        (fun i => s i.1) (fun i j' => h i.1 j'.1)
    have hru : ∀ i : {i // i ∈ u}, algebraMap A (Asec (f i.1)) rj = s i.1 :=
      fun i => hrj ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    have hrj_eq : rj = r := huniq rj hru
    rw [← hrj_eq]
    exact hrj ⟨j, Finset.mem_insert_self j u⟩
  exact ⟨r, hall, fun r2 hr2 => huniq r2 fun i => hr2 i.1⟩

/-- The finite form of the covering hypothesis used in practice: if `∑ i, w i * f i = 1` then
the basic open sets `X_{f i}` cover `X`. -/
theorem existsUnique_of_sum_eq_one [Fintype ι] (f w : ι → A) (hw : ∑ i, w i * f i = 1)
    (s : ∀ i, Asec (f i)) (h : Compat f s) :
    ∃! r : A, ∀ i, algebraMap A (Asec (f i)) r = s i :=
  existsUnique_glue f
    ((Ideal.eq_top_iff_one _).mpr ((Ideal.mem_span_range_iff_exists_fun (v := f)).mpr ⟨w, hw⟩)) s h

/-- The hypothesis "the basic open sets `X_{f i}` cover `Spec A`", in ideal-theoretic form:
every prime ideal omits some `f i`.  It is equivalent to `Ideal.span (Set.range f) = ⊤`. -/
theorem cover_iff (f : ι → A) :
    (∀ p : Ideal A, p.IsPrime → ∃ i, f i ∉ p) ↔ Ideal.span (Set.range f) = ⊤ := by
  constructor
  · intro hcov
    by_contra hne
    obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range f)) hne
    obtain ⟨i, hi⟩ := hcov m hmax.isPrime
    exact hi (hle (Ideal.subset_span ⟨i, rfl⟩))
  · intro hspan p hp
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hle : Ideal.span (Set.range f) ≤ p :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
    rw [hspan] at hle
    exact hp.ne_top (top_le_iff.mp hle)

/-- **Atiyah–Macdonald, Exercise 3.24** with the covering hypothesis in the geometric form of
Exercise 3.23: every prime ideal of `A` omits at least one of the `f i`. -/
theorem solution (f : ι → A) (hcover : ∀ p : Ideal A, p.IsPrime → ∃ i, f i ∉ p)
    (s : ∀ i, Asec (f i)) (h : Compat f s) :
    ∃! r : A, ∀ i, algebraMap A (Asec (f i)) r = s i :=
  existsUnique_glue f ((cover_iff f).mp hcover) s h

end General

section More

variable {A : Type u} [CommRing A] {ι : Type*}

/-- The two restrictions of a single section to `X_f ∩ X_f` agree (this is what compatibility
says for `i = j`). -/
lemma resLeft_self (f : A) : resLeft f f = resRight f f :=
  IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => by
    rw [RingHom.comp_apply, RingHom.comp_apply, resLeft_algebraMap, resRight_algebraMap])

/-- The canonical sections `x ↦ x/1` form a compatible family. -/
theorem compat_algebraMap (f : ι → A) (a : A) :
    Compat f fun i => algebraMap A (Asec (f i)) a := fun i j => by
  rw [resLeft_algebraMap, resRight_algebraMap]

/-- The uniqueness half of Exercise 3.24, in the form of injectivity of the map to the product
of the localizations. -/
theorem algebraMap_injective_pi (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Injective fun a : A => (fun i => algebraMap A (Asec (f i)) a) :=
  fun a b hab => by
    refine sub_eq_zero.mp (eq_zero_of_forall_algebraMap_eq_zero f hspan (a - b) fun i => ?_)
    have hi : algebraMap A (Asec (f i)) a = algebraMap A (Asec (f i)) b := congrFun hab i
    rw [map_sub, hi, sub_self]

/-- Exercise 3.24 indexed by the ring elements generating the basic open sets (`X_a` for `a ∈ s`),
which is the shape used in Mathlib's `Localization.existsUnique_algebraMap_eq_of_span_eq_top`. -/
theorem existsUnique_of_span_eq_top (s : Set A) (hspan : Ideal.span s = ⊤)
    (f : ∀ a : s, Asec a.1)
    (h : ∀ a b : s, resLeft a.1 b.1 (f b) = resRight a.1 b.1 (f a)) :
    ∃! r : A, ∀ a : s, algebraMap A (Asec a.1) r = f a := by
  have hspan' : Ideal.span (Set.range fun a : s => a.1) = ⊤ := by rwa [Subtype.range_coe]
  exact existsUnique_glue (fun a : s => a.1) hspan' f h

/-- Cross-check: the same statement is `Localization.existsUnique_algebraMap_eq_of_span_eq_top`
in Mathlib, which is proved there by a different route.  Both proofs elaborate, so the
statement formalized here is the Mathlib statement of the sheaf condition. -/
theorem existsUnique_of_span_eq_top_mathlib (s : Set A) (hspan : Ideal.span s = ⊤)
    (f : ∀ a : s, Asec a.1)
    (h : ∀ a b : s, resLeft a.1 b.1 (f b) = resRight a.1 b.1 (f a)) :
    ∃! r : A, ∀ a : s, algebraMap A (Asec a.1) r = f a :=
  Localization.existsUnique_algebraMap_eq_of_span_eq_top s hspan f fun a b => (h a b).symm

/-- The sheaf condition in bijection form: over a covering by basic open sets, `A = A(X)` is in
bijection with the set of compatible families of sections. -/
theorem bijective_to_compatible (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Bijective fun a : A =>
      (⟨fun i => algebraMap A (Asec (f i)) a, compat_algebraMap f a⟩ :
        {s : ∀ i, Asec (f i) // Compat f s}) := by
  constructor
  · intro a b hab
    apply algebraMap_injective_pi f hspan
    funext i
    exact congrFun (congrArg Subtype.val hab) i
  · rintro ⟨s, hs⟩
    obtain ⟨r, hr, -⟩ := existsUnique_glue f hspan s hs
    exact ⟨r, Subtype.ext (funext hr)⟩

end More

section Counterexamples

/-- **Counterexample**: without the hypothesis that the basic open sets cover `X`, gluing can
fail to be *unique*.  In `A = ZMod 4` the element `2` is nilpotent, hence vanishes in `A_2`,
although `X_2 ≠ Spec A` because `2` is not a unit.  So the zero section over `X_2` has two
distinct preimages, `0` and `2`. -/
theorem uniqueness_fails_without_cover :
    Ideal.span (Set.range fun _ : PUnit => (2 : ZMod 4)) ≠ ⊤ ∧
    ∃ s : ∀ _ : PUnit, Asec (2 : ZMod 4),
      Compat (fun _ : PUnit => (2 : ZMod 4)) s ∧
      ¬ ∃! r : ZMod 4,
        ∀ i, algebraMap (ZMod 4) (Asec ((fun _ : PUnit => (2 : ZMod 4)) i)) r = s i := by
  have h2sq : (algebraMap (ZMod 4) (Asec (2 : ZMod 4)) 2) *
      (algebraMap (ZMod 4) (Asec (2 : ZMod 4)) 2) = 0 := by
    rw [← map_mul]
    have : (2 : ZMod 4) * 2 = 0 := by decide
    rw [this, map_zero]
  have hvan : algebraMap (ZMod 4) (Asec (2 : ZMod 4)) 2 = 0 := by
    obtain ⟨u, hu⟩ :=
      IsLocalization.Away.algebraMap_isUnit (x := (2 : ZMod 4)) (S := Asec (2 : ZMod 4))
    have h2sq' : (u : Asec (2 : ZMod 4)) * (u : Asec (2 : ZMod 4)) = 0 := by
      rw [hu]; exact h2sq
    have hzero : (u : Asec (2 : ZMod 4)) = 0 := by
      calc (u : Asec (2 : ZMod 4)) = (u : Asec (2 : ZMod 4)) * 1 := (mul_one _).symm
        _ = (u : Asec (2 : ZMod 4)) * ((u : Asec (2 : ZMod 4)) * ↑u⁻¹) := by
              rw [Units.mul_inv, mul_one]
        _ = ((u : Asec (2 : ZMod 4)) * (u : Asec (2 : ZMod 4))) * ↑u⁻¹ := by ring
        _ = 0 := by rw [h2sq']; ring
    rw [← hu, hzero]
  refine ⟨?_, 0, fun _ _ => by rw [resLeft_self], ?_⟩
  · intro htop
    rw [show Set.range (fun _ : PUnit => (2 : ZMod 4)) = {(2 : ZMod 4)} by
      ext x; simp] at htop
    rw [Ideal.span_singleton_eq_top] at htop
    exact absurd htop (by decide)
  · rintro ⟨r, hr, huniq⟩
    have hz : (0 : ZMod 4) = r := huniq 0 fun _ => by simp
    have ht : (2 : ZMod 4) = r := huniq 2 fun _ => hvan
    exact absurd (ht.trans hz.symm) (by decide)

/-- **Counterexample**: without the hypothesis that the basic open sets cover `X`, gluing can
fail to *exist*.  In `A = ℤ` the section `1/2 ∈ A_2` does not come from an integer, and
`X_2 ≠ Spec ℤ` since `2` is not a unit. -/
theorem existence_fails_without_cover :
    Ideal.span (Set.range fun _ : PUnit => (2 : ℤ)) ≠ ⊤ ∧
    ∃ s : ∀ _ : PUnit, Asec (2 : ℤ),
      Compat (fun _ : PUnit => (2 : ℤ)) s ∧
      ¬ ∃ r : ℤ,
        ∀ i, algebraMap ℤ (Asec ((fun _ : PUnit => (2 : ℤ)) i)) r = s i := by
  refine ⟨?_, fun _ => IsLocalization.Away.invSelf (2 : ℤ), fun _ _ => by rw [resLeft_self], ?_⟩
  · intro htop
    rw [show Set.range (fun _ : PUnit => (2 : ℤ)) = {(2 : ℤ)} by ext x; simp] at htop
    rw [Ideal.span_singleton_eq_top] at htop
    exact Int.prime_two.not_isUnit htop
  · rintro ⟨r, hr⟩
    have hr' : algebraMap ℤ (Asec (2 : ℤ)) r = IsLocalization.Away.invSelf (2 : ℤ) :=
      hr PUnit.unit
    have hmul : algebraMap ℤ (Asec (2 : ℤ)) (r * 2) = algebraMap ℤ (Asec (2 : ℤ)) 1 := by
      rw [map_mul, map_one, hr', mul_comm (IsLocalization.Away.invSelf (2 : ℤ)),
        IsLocalization.Away.mul_invSelf]
    obtain ⟨n, hn⟩ :=
      IsLocalization.Away.exists_of_eq (x := (2 : ℤ)) (S := Asec (2 : ℤ)) (a := r * 2) (b := 1) hmul
    have h2 : (2 : ℤ) ^ n * (2 * r - 1) = 0 := by
      calc (2 : ℤ) ^ n * (2 * r - 1) = (2 : ℤ) ^ n * (r * 2) - (2 : ℤ) ^ n * 1 := by ring
        _ = (2 : ℤ) ^ n - (2 : ℤ) ^ n := by rw [hn]; ring
        _ = 0 := by ring
    have h3 : ((2 : ℤ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    have h4 : 2 * r - 1 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h h3
      · exact h
    omega

/-- A concrete non-vacuous instance: `X_2 ∪ X_3 = Spec ℤ`, i.e. the two basic open sets really
cover `X`, so the hypotheses of Exercise 3.24 are satisfiable. -/
theorem example_cover_int :
    Ideal.span (Set.range fun b : Bool => cond b (3 : ℤ) 2) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem : ∀ x : ℤ, x ∈ ({2, 3} : Set ℤ) →
      x ∈ Ideal.span (Set.range fun b : Bool => cond b (3 : ℤ) 2) := by
    intro x hx
    refine Ideal.subset_span ?_
    rcases hx with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  have h1 : (1 : ℤ) = (-1) * 2 + 1 * 3 := by norm_num
  rw [h1]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (hmem 2 (by simp)))
    (Ideal.mul_mem_left _ _ (hmem 3 (by simp)))

/-- Over the cover `X_2 ∪ X_3` of `Spec ℤ`, an integer is determined by its two images in
`ℤ[1/2]` and `ℤ[1/3]`: the unique gluing of the family of images of `r` is `r` itself. -/
theorem example_glue_int (r : ℤ) :
    ∃! s : ℤ, ∀ b : Bool,
      algebraMap ℤ (Asec (cond b (3 : ℤ) 2)) s = algebraMap ℤ (Asec (cond b (3 : ℤ) 2)) r :=
  existsUnique_glue _ example_cover_int _ (compat_algebraMap _ r)

end Counterexamples

#print axioms AtiyahMcdonald69.Ex_3_24.existsUnique_glue
#print axioms AtiyahMcdonald69.Ex_3_24.existsUnique_of_fintype
#print axioms AtiyahMcdonald69.Ex_3_24.eq_zero_of_forall_algebraMap_eq_zero
#print axioms AtiyahMcdonald69.Ex_3_24.cover_iff
#print axioms AtiyahMcdonald69.Ex_3_24.existsUnique_of_span_eq_top
#print axioms AtiyahMcdonald69.Ex_3_24.solution
#print axioms AtiyahMcdonald69.Ex_3_24.existsUnique_of_sum_eq_one
#print axioms AtiyahMcdonald69.Ex_3_24.bijective_to_compatible
#print axioms AtiyahMcdonald69.Ex_3_24.uniqueness_fails_without_cover
#print axioms AtiyahMcdonald69.Ex_3_24.existence_fails_without_cover
#print axioms AtiyahMcdonald69.Ex_3_24.example_glue_int

end AtiyahMcdonald69.Ex_3_24
