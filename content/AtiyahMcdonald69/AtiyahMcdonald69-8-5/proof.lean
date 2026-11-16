/-
# Atiyah–Macdonald (1969), Chapter 8 ("Artin Rings"), Exercise 5

**Exercise, verbatim.**
*"5. In Chapter 5, Exercise 16, show that `X` is a finite covering of `L` (i.e. the number of
points of `X` lying over a given point of `L` is finite and bounded)."*

**Setting of the reference (Chapter 5, Exercise 16, the geometric form of Noether
normalisation).**  `k` is a field, `X ⊆ k^n` an affine algebraic variety with coordinate ring
`A = P(X) ≠ 0`; there are `r ≤ n`, a linear subspace `L ⊆ k^n` of dimension `r` and a linear
surjection `π : k^n → L` with `π|_X : X → L` surjective.  Writing `A₀ = P(L) = k[y₁,…,y_r]`, the
`y_i` are algebraically independent over `k` (so `A₀ ↪ A`) and `A` is integral and of finite type
over `A₀`; by Chapter 5, §1, (5.1) and (5.2), an integral algebra of finite type is a finite
module, so `A` is a finite `A₀`-module.  The
exercise asks that `π|_X` be a *finite covering*: every fibre is finite, with a bound independent
of the point.

**Content proved here** (for a general field `k`, and for an arbitrary number `N` of `A₀`-module
generators of `A`):

* `span_fiber_eq_top`, `moduleFinite_fiber`, `finrank_fiber_le` — the fibre `A ⧸ 𝔪A` of
  `Spec A → Spec A₀` over a maximal ideal `𝔪` is a finite-dimensional `(A₀ ⧸ 𝔪)`-algebra spanned
  by the images of the `N` generators (the source's *"every fibre algebra `B ⊗_A k(𝔭)` has
  dimension at most `N`"*).
* `card_maximal_le_finrank` — a finite-dimensional algebra over a field has at most `finrank` many
  maximal ideals (CRT: distinct maximal ideals are pairwise coprime, so the map to the product of
  the residue fields is onto and the dimensions add up; each residue field is nonzero).  This is
  the source's *"a finite-dimensional algebra over a field has at most its dimension many maximal
  ideals"*.
* `fiber_card_le` — **bounded fibres**: for every maximal ideal `𝔪` of `A₀` there is a `Finset` of
  ideals of `A` consisting exactly of the maximal ideals `𝔫` with `𝔫 ∩ A₀ = 𝔪`, and it has at most
  `N` elements.  (`fiber_card_le_primes`: the same for prime ideals, which over a closed point are
  all maximal by integrality — so these are all the points of the scheme-theoretic fibre.)
* `exists_prime_over` — **lying over**: every prime of `A₀` lies under a prime of `A`, i.e.
  `Spec A → Spec A₀` is onto (the source's *"surjectivity follows from lying over"*), using that
  `A₀ ↪ A` (algebraic independence of the `y_i`).
* `fiber_finite` — the same count for sets: the set of points of `X` over a closed point is finite
  with cardinality at most `N` (`Set.ncard`).
* `solution` — the exercise: with `A₀ = MvPolynomial (Fin r) k = k[y₁,…,y_r]` the two assertions
  above hold, i.e. `X` is a finite covering of `L`, with the explicit uniform bound `N` (the number
  of `A₀`-module generators of `A`).
* `solution_finite` — the literal "finite and bounded" quantifier form, from the hypothesis that
  `A` is a finite `A₀`-module (the datum supplied by Chapter 5): there is a uniform `N` bounding
  every fibre, and `X → L` is onto.

**Reading of "points".**  By Chapter 1, Exercise 27 the points of the affine variety
`X = Max(A)` are the maximal ideals of `A` (for `k` algebraically closed); correspondingly the
points of `L` are the maximal ideals of `A₀ = k[y₁,…,y_r]`.  Hence "the number of points of `X`
lying over a point `𝔪` of `L`" is the number of maximal ideals `𝔫` of `A` with
`𝔫 ∩ A₀ = 𝔪`, which is what the statements below count.

**Scope / dependencies.**  The Noether normalisation datum of Chapter 5, Exercise 16 — the
polynomial subalgebra `A₀ = k[y₁,…,y_r]`, the algebraic independence of the `y_i`, and the number
`N` of `A₀`-module generators of `A` — is taken as a hypothesis, exactly as the exercise inherits
it; the content proper to Exercise 8.5 is proved from it.  Nothing else is assumed.  There are no
`sorry`s, no `admit`s and no extra axioms; the only axioms used are Lean's standard
`propext`, `Classical.choice`, `Quot.sound` (verified with `#print axioms`).

Natural-language source of the proof formalised here:
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-8.5
-/
import Mathlib

open Function

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace AtiyahMcdonald69.Ex_8_5

section Fiber

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The fibres of `Spec A → Spec A₀` are generated over the residue field by the images of a
generating family of `A` over `A₀`. -/
theorem span_fiber_eq_top {ι : Type*} (b : ι → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) :
    Submodule.span (A₀ ⧸ 𝔪)
      (Set.range fun i => Ideal.Quotient.mk (𝔪.map (algebraMap A₀ A)) (b i)) = ⊤ := by
  have key : ∀ y ∈ Submodule.span A₀ (Set.range b),
      Ideal.Quotient.mk (𝔪.map (algebraMap A₀ A)) y ∈
        Submodule.span (A₀ ⧸ 𝔪)
          (Set.range fun i => Ideal.Quotient.mk (𝔪.map (algebraMap A₀ A)) (b i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => exact Submodule.add_mem _ ihu ihv
    | smul a u _ ih =>
        have h1 : Ideal.Quotient.mk (𝔪.map (algebraMap A₀ A)) (a • u)
            = (Ideal.Quotient.mk 𝔪 a) •
              (Ideal.Quotient.mk (𝔪.map (algebraMap A₀ A)) u) := by
          rw [Algebra.smul_def, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, map_mul]
        rw [h1]
        exact Submodule.smul_mem _ _ ih
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact key y (by rw [hb]; exact Submodule.mem_top)

/-- A finite generating family of `A` over `A₀` makes `A` a finite `A₀`-module. -/
theorem moduleFinite_of_span {ι : Type*} [Finite ι] (b : ι → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) : Module.Finite A₀ A := by
  have h : Module.Finite A₀ ↥(Submodule.span A₀ (Set.range b)) :=
    Module.Finite.span_of_finite A₀ (Set.finite_range b)
  rw [hb] at h
  exact Module.Finite.equiv Submodule.topEquiv

/-- The fibre algebra is a finite module over the residue field. -/
theorem moduleFinite_fiber {ι : Type*} [Finite ι] (b : ι → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) :
    Module.Finite (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) :=
  moduleFinite_of_span (A₀ := A₀ ⧸ 𝔪) _ (span_fiber_eq_top b hb 𝔪)

/-- **Fibre dimension bound** (source: *"every fibre algebra … has dimension at most N"*). -/
theorem finrank_fiber_le {N : ℕ} (b : Fin N → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) (h𝔪 : 𝔪.IsMaximal) :
    Module.finrank (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) ≤ N := by
  have hsp := span_fiber_eq_top b hb 𝔪
  calc Module.finrank (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A))
      ≤ Fintype.card (Fin N) := finrank_le_of_span_eq_top hsp
    _ = N := Fintype.card_fin N

end Fiber

/-- A finite-dimensional algebra over a field has at most `finrank` many maximal ideals. -/
theorem card_maximal_le_finrank
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B]
    (s : Finset (Ideal B)) (hs : ∀ 𝔭 ∈ s, 𝔭.IsMaximal) :
    s.card ≤ Module.finrank K B := by
  classical
  have key : s.card ≤
      Module.finrank K ((𝔭 : {𝔭 // 𝔭 ∈ s}) → B ⧸ ((𝔭 : {𝔭 // 𝔭 ∈ s}) : Ideal B)) := by
    rw [Module.finrank_pi_fintype]
    have h1 : s.card = ∑ _ : {𝔭 // 𝔭 ∈ s}, 1 := by simp
    rw [h1]
    refine Finset.sum_le_sum fun 𝔭 _ => ?_
    have hmax : (𝔭.1 : Ideal B).IsMaximal := hs 𝔭.1 𝔭.2
    have hpos : 0 < Module.finrank K (B ⧸ 𝔭.1) := Module.finrank_pos
    omega
  refine key.trans ?_
  have hcop : Pairwise
      (IsCoprime on fun 𝔭 : {𝔭 // 𝔭 ∈ s} => ((𝔭 : {𝔭 // 𝔭 ∈ s}) : Ideal B)) := by
    intro 𝔭 𝔭' hne
    have hmax : (𝔭.1 : Ideal B).IsMaximal := hs 𝔭.1 𝔭.2
    have hmax' : (𝔭'.1 : Ideal B).IsMaximal := hs 𝔭'.1 𝔭'.2
    refine Ideal.isCoprime_of_isMaximal ?_
    intro h
    exact hne (Subtype.ext h)
  have hsurj : Function.Surjective (LinearMap.pi fun 𝔭 : {𝔭 // 𝔭 ∈ s} =>
      (Ideal.Quotient.mkₐ K (𝔭.1 : Ideal B)).toLinearMap) := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨b, funext hb⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

section FiniteFibers

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The fibre `A ⧸ 𝔪A` over a maximal ideal `𝔪` has at most `N` maximal ideals, provided `A` is
generated by `N` elements as an `A₀`-module. -/
theorem fiber_card_le {N : ℕ} (b : Fin N → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) (h𝔪 : 𝔪.IsMaximal) :
    ∃ s : Finset (Ideal A),
      (∀ 𝔫 : Ideal A, 𝔫 ∈ s ↔ 𝔫.IsMaximal ∧ 𝔫.under A₀ = 𝔪) ∧ s.card ≤ N := by
  classical
  letI : Field (A₀ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  letI : Algebra (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have hfin : Module.Finite (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) := moduleFinite_fiber b hb 𝔪
  have hdim : Module.finrank (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) ≤ N :=
    finrank_fiber_le b hb 𝔪 h𝔪
  -- the maximal ideals of the fibre are finite in number, by the uniform bound
  have hfinite : {𝔭 : Ideal (A ⧸ 𝔪.map (algebraMap A₀ A)) | 𝔭.IsMaximal}.Finite := by
    by_contra hinf
    obtain ⟨u, hu, hucard⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (N + 1)
    have hle : u.card ≤ N := by
      refine (card_maximal_le_finrank (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) u ?_).trans hdim
      intro 𝔭 h𝔭
      exact hu h𝔭
    omega
  set t : Finset (Ideal (A ⧸ 𝔪.map (algebraMap A₀ A))) := hfinite.toFinset
  have htmem : ∀ 𝔭 : Ideal (A ⧸ 𝔪.map (algebraMap A₀ A)), 𝔭 ∈ t ↔ 𝔭.IsMaximal := by
    intro 𝔭
    rw [Set.Finite.mem_toFinset]
    rfl
  have hcard : t.card ≤ N := by
    refine (card_maximal_le_finrank (A₀ ⧸ 𝔪) (A ⧸ 𝔪.map (algebraMap A₀ A)) t ?_).trans hdim
    intro 𝔭 h𝔭
    exact (htmem 𝔭).mp h𝔭
  set q : A →+* (A ⧸ 𝔪.map (algebraMap A₀ A)) := Ideal.Quotient.mk _
  refine ⟨t.image fun 𝔭 => 𝔭.comap q, ?_, ?_⟩
  · intro 𝔫
    constructor
    · intro h
      obtain ⟨𝔭, h𝔭t, rfl⟩ := Finset.mem_image.mp h
      have hmax : 𝔭.IsMaximal := (htmem 𝔭).mp h𝔭t
      refine ⟨Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective, ?_⟩
      rw [Ideal.under_def, Ideal.comap_comap]
      refine (h𝔪.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) ?_).symm
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply]
      have hzero : q (algebraMap A₀ A x) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem (algebraMap A₀ A) hx
      rw [hzero]
      exact 𝔭.zero_mem
    · rintro ⟨hmax, hunder⟩
      have hIle : 𝔪.map (algebraMap A₀ A) ≤ 𝔫 := by
        rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def]
        rw [hunder]
      have hmaxmap : (𝔫.map q).IsMaximal :=
        Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
          (by rw [show RingHom.ker q = 𝔪.map (algebraMap A₀ A) from Ideal.mk_ker]; exact hIle)
      have hcomap : (𝔫.map q).comap q = 𝔫 :=
        Ideal.comap_map_eq_self_of_isMaximal q hmaxmap.ne_top
      exact Finset.mem_image.mpr ⟨𝔫.map q, (htmem _).mpr hmaxmap, hcomap⟩
  · calc (t.image fun 𝔭 => 𝔭.comap q).card ≤ t.card := Finset.card_image_le
      _ ≤ N := hcard

/-- The same bound for prime ideals of `A` over a maximal ideal `𝔪`. -/
theorem fiber_card_le_primes {N : ℕ} (b : Fin N → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) (h𝔪 : 𝔪.IsMaximal) :
    ∃ s : Finset (Ideal A),
      (∀ 𝔫 : Ideal A, 𝔫 ∈ s ↔ 𝔫.IsPrime ∧ 𝔫.under A₀ = 𝔪) ∧ s.card ≤ N := by
  have hfin : Module.Finite A₀ A := moduleFinite_of_span b hb
  have hint : Algebra.IsIntegral A₀ A := Algebra.IsIntegral.of_finite A₀ A
  obtain ⟨s, hs, hcard⟩ := fiber_card_le b hb 𝔪 h𝔪
  refine ⟨s, fun 𝔫 => ?_, hcard⟩
  rw [hs 𝔫]
  constructor
  · rintro ⟨hmax, hunder⟩
    exact ⟨hmax.isPrime, hunder⟩
  · rintro ⟨hprime, hunder⟩
    have hmaxc : (Ideal.comap (algebraMap A₀ A) 𝔫).IsMaximal := by
      rw [← Ideal.under_def, hunder]
      exact h𝔪
    exact ⟨Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hmaxc, hunder⟩

/-- The "finite" half of "finite covering", spelled out for sets: the set of points of `X` over a
closed point `𝔪` of `L` is finite, and its cardinality is at most `N`. -/
theorem fiber_finite {N : ℕ} (b : Fin N → A)
    (hb : Submodule.span A₀ (Set.range b) = ⊤) (𝔪 : Ideal A₀) (h𝔪 : 𝔪.IsMaximal) :
    {𝔫 : Ideal A | 𝔫.IsPrime ∧ 𝔫.under A₀ = 𝔪}.Finite ∧
      {𝔫 : Ideal A | 𝔫.IsPrime ∧ 𝔫.under A₀ = 𝔪}.ncard ≤ N := by
  obtain ⟨s, hs, hcard⟩ := fiber_card_le_primes b hb 𝔪 h𝔪
  have hset : {𝔫 : Ideal A | 𝔫.IsPrime ∧ 𝔫.under A₀ = 𝔪} = ↑s := by
    ext 𝔫
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hs 𝔫]
  have hfin : {𝔫 : Ideal A | 𝔫.IsPrime ∧ 𝔫.under A₀ = 𝔪}.Finite := hset ▸ s.finite_toSet
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have htofinset : hfin.toFinset = s := by
    ext 𝔫
    rw [Set.Finite.mem_toFinset, hset, Finset.mem_coe]
  rw [htofinset]
  exact hcard

/-- **Surjectivity** (lying over). -/
theorem exists_prime_over (hint : Algebra.IsIntegral A₀ A)
    (hinj : Function.Injective (algebraMap A₀ A)) (𝔭 : Ideal A₀) (h𝔭 : 𝔭.IsPrime) :
    ∃ 𝔮 : Ideal A, 𝔮.IsPrime ∧ 𝔮.under A₀ = 𝔭 := by
  have hkerle : Ideal.comap (algebraMap A₀ A) (⊥ : Ideal A) ≤ 𝔭 := by
    rw [Ideal.comap_bot_of_injective (f := algebraMap A₀ A) hinj]
    exact bot_le
  obtain ⟨Q, -, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal A) hkerle
  exact ⟨Q, hQprime, hQ⟩

end FiniteFibers

variable (k : Type*) [Field k] (r N : ℕ)

/-- **Atiyah–Macdonald, Chapter 8, Exercise 5.** -/
theorem solution (A : Type*) [CommRing A] [Algebra k A]
    [Algebra (MvPolynomial (Fin r) k) A] [IsScalarTower k (MvPolynomial (Fin r) k) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin r) k) A))
    (b : Fin N → A)
    (hb : Submodule.span (MvPolynomial (Fin r) k) (Set.range b) = ⊤) :
    (∀ 𝔪 : Ideal (MvPolynomial (Fin r) k), 𝔪.IsMaximal →
        ∃ s : Finset (Ideal A),
          (∀ 𝔫 : Ideal A, 𝔫 ∈ s ↔
            𝔫.IsMaximal ∧ 𝔫.under (MvPolynomial (Fin r) k) = 𝔪) ∧ s.card ≤ N) ∧
      (∀ 𝔭 : Ideal (MvPolynomial (Fin r) k), 𝔭.IsPrime →
        ∃ 𝔮 : Ideal A, 𝔮.IsPrime ∧ 𝔮.under (MvPolynomial (Fin r) k) = 𝔭) := by
  have hfin : Module.Finite (MvPolynomial (Fin r) k) A := moduleFinite_of_span b hb
  have hint : Algebra.IsIntegral (MvPolynomial (Fin r) k) A := Algebra.IsIntegral.of_finite _ _
  exact ⟨fun _ h𝔪 => fiber_card_le b hb _ h𝔪, fun _ h𝔭 => exists_prime_over hint hinj _ h𝔭⟩

/-- The literal quantifier form of the exercise (*"finite and bounded"*): if `A` is a finite
`A₀`-module — the datum furnished by Chapter 5, Exercise 16 together with Chapter 5 (5.1)–(5.2) —
then there is a single integer `N` bounding the number of
points of `X` over every point of `L`, and `X → L` is surjective. -/
theorem solution_finite (A : Type*) [CommRing A] [Algebra k A]
    [Algebra (MvPolynomial (Fin r) k) A] [IsScalarTower k (MvPolynomial (Fin r) k) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin r) k) A))
    [Module.Finite (MvPolynomial (Fin r) k) A] :
    (∃ N : ℕ, ∀ 𝔪 : Ideal (MvPolynomial (Fin r) k), 𝔪.IsMaximal →
        ∃ s : Finset (Ideal A),
          (∀ 𝔫 : Ideal A, 𝔫 ∈ s ↔
            𝔫.IsMaximal ∧ 𝔫.under (MvPolynomial (Fin r) k) = 𝔪) ∧ s.card ≤ N) ∧
      (∀ 𝔭 : Ideal (MvPolynomial (Fin r) k), 𝔭.IsPrime →
        ∃ 𝔮 : Ideal A, 𝔮.IsPrime ∧ 𝔮.under (MvPolynomial (Fin r) k) = 𝔭) := by
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin r) k) (M := A)
  exact ⟨⟨N, fun 𝔪 h𝔪 => (solution k r N A hinj b hb).1 𝔪 h𝔪⟩,
    fun 𝔭 h𝔭 => (solution k r N A hinj b hb).2 𝔭 h𝔭⟩

end AtiyahMcdonald69.Ex_8_5
