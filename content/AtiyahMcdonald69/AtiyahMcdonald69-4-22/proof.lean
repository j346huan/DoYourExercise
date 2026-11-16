import Mathlib

/-!
# Atiyah–Macdonald, Exercise 4.22

**Statement** (M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*,
Chapter 4, Exercise 22):

> A primary decomposition of `N` in `M` is a representation of `N` as an intersection
> `N = Q₁ ∩ ⋯ ∩ Qₙ` of primary submodules of `M`; it is a *minimal* primary decomposition if the
> ideals `pᵢ = r_M(Qᵢ)` are all distinct and if none of the components `Qᵢ` can be omitted from
> the intersection, that is if `Qᵢ ⊉ ⋂_{j ≠ i} Qⱼ` (`1 ≤ i ≤ n`).
>
> Prove the analogue of (4.5), that the prime ideals `pᵢ` depend only on `N` (and `M`). They are
> called the prime ideals *belonging to* `N` in `M`. Show that they are also the prime ideals
> belonging to `0` in `M/N`.

The notions occurring in the statement are recovered from the earlier exercises of the same
chapter:

* `r_M(N)` (Exercise 4.20) is `{x ∈ A | ∃ q > 0, x^q M ⊆ N}`; we take it to be the radical of the
  colon ideal `(N : M)`, and `mem_rInM_iff` records the defining property.
* "primary in `M`" (Exercise 4.21) means `Q ≠ M` and every zero-divisor on `M ⧸ Q` is nilpotent;
  `isPrimary_iff_book` shows this is Mathlib's `Submodule.IsPrimary`, `isPrimary_iff_colon` gives
  the equivalent "colon" form used in the proof, and `IsPrimary.isPrime_rInM` is the (4.21)
  conclusion that `r_M(Q)` is a prime ideal.
* "(minimal) primary decomposition of `N` in `M`" is `Submodule.IsMinimalPrimaryDecomposition`;
  `isMinimalPrimaryDecomposition_iff` spells out that this is literally the book's definition.
* The prime ideals belonging to `N` are `N.associatedPrimes`, i.e. the prime ideals of the form
  `(N : x).radical` (`x : M`), see `Submodule.isAssociatedPrime_def`.

Natural proof: <https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-22>
-/

namespace AtiyahMcdonald69.Ex_4_22

open Submodule
open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-! ## The radical of a submodule in `M` (Exercise 4.20) -/

/-- (4.20) The radical of a submodule `N` in `M`:
`r_M(N) = (N : M).radical = {x : A | ∃ q > 0, x ^ q • M ≤ N}`. -/
def rInM (N : Submodule A M) : Ideal A :=
  (N.colon Set.univ).radical

/-- (4.20) Membership in the radical of `N` in `M`, in the form used in the book:
`x ^ q • M ≤ N` for some `q > 0`. -/
theorem mem_rInM_iff {N : Submodule A M} {x : A} :
    x ∈ rInM N ↔ ∃ q : ℕ, 0 < q ∧ ∀ m : M, x ^ q • m ∈ N := by
  rw [rInM, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨q, hq⟩
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      have h1 : (1 : A) ∈ N.colon (Set.univ : Set M) := by simpa using hq
      have htop : N = ⊤ := by
        rw [eq_top_iff]
        intro m _
        simpa using (Submodule.mem_colon.mp h1) m (Set.mem_univ m)
      refine ⟨1, Nat.one_pos, fun m => ?_⟩
      rw [htop]
      simp
    · exact ⟨q, hqpos, fun m => (Submodule.mem_colon.mp hq) m (Set.mem_univ m)⟩
  · rintro ⟨q, -, h⟩
    exact ⟨q, Submodule.mem_colon.mpr fun m _ => h m⟩

/-- (4.20) Membership in `r_M(N)` written with submodule scalar multiples. -/
theorem mem_rInM_iff' {N : Submodule A M} {x : A} :
    x ∈ rInM N ↔ ∃ q : ℕ, 0 < q ∧ x ^ q • (⊤ : Submodule A M) ≤ N := by
  rw [mem_rInM_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    refine ⟨q, hq, fun m hm => ?_⟩
    obtain ⟨m', -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists m (x ^ q : A) (⊤ : Submodule A M)).mp hm
    exact h m'
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun m =>
      h (Submodule.smul_mem_pointwise_smul m (x ^ q : A) (⊤ : Submodule A M) Submodule.mem_top)⟩

/-- (4.20) As a set, `r_M(N)` is exactly `{x : A | ∃ q > 0, x ^ q • M ≤ N}`; in particular it
is an ideal. -/
theorem coe_rInM (N : Submodule A M) :
    (rInM N : Set A) = {x : A | ∃ q : ℕ, 0 < q ∧ x ^ q • (⊤ : Submodule A M) ≤ N} := by
  ext x
  exact mem_rInM_iff' (N := N)

/-! ## Primary submodules (Exercise 4.21) -/

/-- (4.21) A submodule `Q` of `M` is primary in `M` iff `Q ≠ M` and every zero-divisor on
`M ⧸ Q` is nilpotent (Atiyah–Macdonald's definition), i.e. iff `Submodule.IsPrimary Q`. -/
theorem isPrimary_iff_book (Q : Submodule A M) :
    Q.IsPrimary ↔ Q ≠ ⊤ ∧ ∀ (x : A) (m : M ⧸ Q), m ≠ 0 → x • m = 0 →
      ∃ n : ℕ, x ^ n • (⊤ : Submodule A (M ⧸ Q)) = ⊥ :=
  Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul

/-- (4.21) The working form of primariness: if `x • m ∈ Q` and `m ∉ Q`, then `x ∈ r_M(Q)`. -/
theorem isPrimary_iff_colon (Q : Submodule A M) :
    Q.IsPrimary ↔ Q ≠ ⊤ ∧ ∀ (x : A) (m : M), x • m ∈ Q → m ∈ Q ∨ x ∈ rInM Q := by
  simp only [Submodule.IsPrimary]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x m hxm => ?_⟩
    rcases h2 hxm with hm | ⟨n, hn⟩
    · exact Or.inl hm
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact absurd (top_le_iff.mp (by simpa using hn)) h1
      · exact Or.inr ((mem_rInM_iff' (N := Q)).mpr ⟨n, hpos, hn⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun {x m} hxm => ?_⟩
    rcases h2 x m hxm with hm | hin
    · exact Or.inl hm
    · obtain ⟨n, -, hle⟩ := (mem_rInM_iff' (N := Q)).mp hin
      exact Or.inr ⟨n, hle⟩

/-- (4.21) If `Q` is primary in `M`, then `r_M(Q)` is a prime ideal. -/
theorem IsPrimary.isPrime_rInM {Q : Submodule A M} (hQ : Q.IsPrimary) :
    (rInM Q).IsPrime :=
  hQ.isPrime_radical_colon

/-! ## Minimal primary decompositions (Exercise 4.22, definition) -/

/-- (4.22) The definition of a minimal primary decomposition, spelled out: `N = ⋂ t`, every
`Q ∈ t` is primary in `M`, the ideals `r_M(Q)` (`Q ∈ t`) are pairwise distinct, and no component
can be omitted. This is exactly the content of `Submodule.IsMinimalPrimaryDecomposition`. -/
theorem isMinimalPrimaryDecomposition_iff (N : Submodule A M) (t : Finset (Submodule A M)) :
    N.IsMinimalPrimaryDecomposition t ↔
      t.inf id = N ∧ (∀ Q ∈ t, Q.IsPrimary) ∧
        (∀ Q ∈ t, ∀ Q' ∈ t, rInM Q = rInM Q' → Q = Q') ∧
          (∀ Q ∈ t, ∃ m ∈ (t.erase Q).inf id, m ∉ Q) := by
  constructor
  · intro h
    refine ⟨h.inf_eq, h.primary, ?_, ?_⟩
    · intro Q hQ Q' hQ' heq
      by_contra hne
      exact absurd heq (h.distinct hQ hQ' hne)
    · intro Q hQ
      exact SetLike.not_le_iff_exists.mp (h.minimal hQ)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · intro Q hQ Q' hQ' hne heq
      exact hne (h3 Q hQ Q' hQ' heq)
    · intro Q hQ
      obtain ⟨m, hm, hmQ⟩ := h4 Q hQ
      exact fun hle => hmQ (hle hm)

/-! ## The analogue of (4.5) -/

/-- The radical of a finite intersection of ideals is the intersection of the radicals
(the case of `Ideal.radical_inf` needed below). -/
theorem radical_finset_inf_apply {ι : Type*} (s : Finset ι) (f : ι → Ideal A) :
    (s.inf f).radical = s.inf fun i => (f i).radical := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Ideal.radical_inf, ih]

/-- The key computation of the natural proof: for `x : M`,
`r(N : x) = ⋂_{Q ∈ t, x ∉ Q} r(Q : x) = ⋂_{Q ∈ t, x ∉ Q} r_M(Q)`; the terms with `x ∈ Q` are
`r(Q : x) = A` and drop out. -/
theorem radical_colon_eq_inf {N : Submodule A M} {t : Finset (Submodule A M)}
    (hN : t.inf id = N) (x : M) :
    (N.colon {x}).radical = t.inf (fun Q => (Q.colon {x}).radical) := by
  rw [← hN, colon_finsetInf]
  simp only [id_eq]
  rw [radical_finset_inf_apply]

/-- In a finite intersection of ideals, if all but one of the ideals are `⊤`, the intersection is
the remaining ideal. -/
theorem finset_inf_eq_of_forall_eq_top {ι : Type*} {s : Finset ι} {f : ι → Ideal A} {i : ι}
    (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = ⊤) : s.inf f = f i := by
  refine le_antisymm (Finset.inf_le hi) (Finset.le_inf fun j hj => ?_)
  by_cases hji : j = i
  · subst hji
    exact le_rfl
  · rw [h j hj hji]
    exact le_top

/-- The analogue of Theorem 4.5 (Atiyah–Macdonald) for modules: in a minimal primary
decomposition `N = ⋂ t`, the prime ideals `r_M(Q) = (Q : M).radical` (`Q ∈ t`) are precisely the
associated primes of `N`, i.e. the prime ideals of the form `r(N : x)` (`x ∈ M`). -/
theorem image_rInM_eq_associatedPrimes {N : Submodule A M} {t : Finset (Submodule A M)}
    (ht : N.IsMinimalPrimaryDecomposition t) :
    rInM '' (t : Set (Submodule A M)) = N.associatedPrimes := by
  classical
  have h : ∀ x : M, (N.colon {x}).radical = t.inf (fun Q => (Q.colon {x}).radical) :=
    fun x => radical_colon_eq_inf ht.inf_eq x
  ext p
  constructor
  · rintro ⟨Q, hQt, rfl⟩
    obtain ⟨x, hxt, hxQ⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hQt)
    have hxt' : ∀ Q' ∈ t.erase Q, x ∈ Q' := fun Q' hQ' =>
      (Submodule.mem_finsetInf.mp hxt) Q' hQ'
    have hinf : t.inf (fun Q' => (Q'.colon {x}).radical) = (Q.colon {x}).radical := by
      refine finset_inf_eq_of_forall_eq_top (f := fun Q' => (Q'.colon {x}).radical) hQt ?_
      intro Q' hQ't hQ'ne
      have hxQ' : x ∈ Q' := hxt' Q' (Finset.mem_erase.mpr ⟨hQ'ne, hQ't⟩)
      rw [show Q'.colon {x} = ⊤ by
        rw [Submodule.colon_eq_top_iff_subset]
        exact Set.singleton_subset_iff.mpr hxQ', Ideal.radical_top]
    refine ⟨(ht.primary hQt).isPrime_radical_colon, x, ?_⟩
    rw [h x, hinf]
    exact ((ht.primary hQt).radical_colon_singleton_of_notMem hxQ).symm
  · rintro ⟨hp, x, rfl⟩
    rw [h x] at hp
    obtain ⟨Q, hQ, hQp⟩ := Ideal.eq_inf_of_isPrime_inf hp
    refine ⟨Q, hQ, ?_⟩
    by_cases hxQ : x ∈ Q
    · exfalso
      have htop : (Q.colon {x}).radical = ⊤ := by
        rw [show Q.colon {x} = ⊤ by
          rw [Submodule.colon_eq_top_iff_subset]
          exact Set.singleton_subset_iff.mpr hxQ, Ideal.radical_top]
      rw [← hQp, htop] at hp
      exact hp.ne_top rfl
    · rw [h x, ← hQp, (ht.primary hQ).radical_colon_singleton_of_notMem hxQ]
      rfl

/-- (4.22, first part) The prime ideals belonging to `N` — the radicals `r_M(Q) = (Q : M).radical`
of the components of a minimal primary decomposition of `N` — do not depend on the chosen
decomposition. -/
theorem primeIdealsBelonging_independent {N : Submodule A M}
    {t t' : Finset (Submodule A M)}
    (ht : N.IsMinimalPrimaryDecomposition t) (ht' : N.IsMinimalPrimaryDecomposition t') :
    rInM '' (t : Set (Submodule A M)) = rInM '' (t' : Set (Submodule A M)) := by
  rw [image_rInM_eq_associatedPrimes ht, image_rInM_eq_associatedPrimes ht']

/-- The annihilator of the image of `x` in `M ⧸ N` is `(N : x)`. -/
theorem colon_bot_quotient_mk (N : Submodule A M) (x : M) :
    ((⊥ : Submodule A (M ⧸ N)).colon {N.mkQ x}) = N.colon {x} := by
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Submodule.mkQ_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/-- (4.22, second part) The prime ideals belonging to `N` in `M` are the prime ideals belonging
to `0` in `M ⧸ N`. -/
theorem associatedPrimes_eq_quotient (N : Submodule A M) :
    N.associatedPrimes = _root_.associatedPrimes A (M ⧸ N) := by
  ext p
  rw [Submodule.AssociatePrimes.mem_iff, Submodule.isAssociatedPrime_def,
    AssociatedPrimes.mem_iff, IsAssociatedPrime, Submodule.isAssociatedPrime_def]
  constructor
  · rintro ⟨hp, x, hpx⟩
    exact ⟨hp, N.mkQ x, by rw [hpx, colon_bot_quotient_mk]⟩
  · rintro ⟨hp, y, hy⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact ⟨hp, x, by rw [hy, colon_bot_quotient_mk]⟩

/-- **Atiyah–Macdonald, Exercise 4.22**, in full. Let `N ≤ M` and let `t`, `t'` be minimal primary
decompositions of `N` in `M`. Then:

1. the prime ideals belonging to `N`, i.e. the ideals `r_M(Q) = (Q : M).radical` for `Q ∈ t`, are
   exactly the prime ideals of the form `r(N : x)` (`x : M`);
2. consequently they are independent of the chosen minimal primary decomposition;
3. and they are exactly the prime ideals belonging to `0` in `M ⧸ N`. -/
theorem solution {N : Submodule A M} {t t' : Finset (Submodule A M)}
    (ht : N.IsMinimalPrimaryDecomposition t) (ht' : N.IsMinimalPrimaryDecomposition t') :
    (∀ p : Ideal A, p ∈ rInM '' (t : Set (Submodule A M)) ↔
        p.IsPrime ∧ ∃ x : M, p = (N.colon {x}).radical) ∧
      rInM '' (t : Set (Submodule A M)) = rInM '' (t' : Set (Submodule A M)) ∧
        rInM '' (t : Set (Submodule A M)) = _root_.associatedPrimes A (M ⧸ N) := by
  refine ⟨fun p => ?_, primeIdealsBelonging_independent ht ht', ?_⟩
  · rw [image_rInM_eq_associatedPrimes ht, Submodule.AssociatePrimes.mem_iff,
      Submodule.isAssociatedPrime_def]
  · rw [image_rInM_eq_associatedPrimes ht, associatedPrimes_eq_quotient]

/-- Non-vacuity of Exercise 4.22: in a Noetherian module every submodule admits a minimal
primary decomposition (Lasker–Noether), so the hypothesis of `solution` is satisfiable. -/
theorem exists_isMinimalPrimaryDecomposition [IsNoetherian A M] (N : Submodule A M) :
    ∃ t : Finset (Submodule A M), N.IsMinimalPrimaryDecomposition t :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker A M) N

end AtiyahMcdonald69.Ex_4_22

#print axioms AtiyahMcdonald69.Ex_4_22.coe_rInM
#print axioms AtiyahMcdonald69.Ex_4_22.mem_rInM_iff
#print axioms AtiyahMcdonald69.Ex_4_22.mem_rInM_iff'
#print axioms AtiyahMcdonald69.Ex_4_22.isPrimary_iff_book
#print axioms AtiyahMcdonald69.Ex_4_22.isPrimary_iff_colon
#print axioms AtiyahMcdonald69.Ex_4_22.IsPrimary.isPrime_rInM
#print axioms AtiyahMcdonald69.Ex_4_22.isMinimalPrimaryDecomposition_iff
#print axioms AtiyahMcdonald69.Ex_4_22.radical_finset_inf_apply
#print axioms AtiyahMcdonald69.Ex_4_22.radical_colon_eq_inf
#print axioms AtiyahMcdonald69.Ex_4_22.finset_inf_eq_of_forall_eq_top
#print axioms AtiyahMcdonald69.Ex_4_22.image_rInM_eq_associatedPrimes
#print axioms AtiyahMcdonald69.Ex_4_22.primeIdealsBelonging_independent
#print axioms AtiyahMcdonald69.Ex_4_22.colon_bot_quotient_mk
#print axioms AtiyahMcdonald69.Ex_4_22.associatedPrimes_eq_quotient
#print axioms AtiyahMcdonald69.Ex_4_22.solution
#print axioms AtiyahMcdonald69.Ex_4_22.exists_isMinimalPrimaryDecomposition
