/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969),
Chapter 4, Exercise 19.

Natural proof: https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-4-19

**Statement** (A a commutative ring, p a prime ideal of A):

(i) Every p-primary ideal contains `S_p(0)`, the kernel of the canonical homomorphism
    `A → A_p`.

Suppose that `A` satisfies the condition
(L) for every prime ideal `p`, `⋂ {q | q is p-primary} = S_p(0)`
(Noetherian rings satisfy this, see Chapter 10). Then:

(ii) for distinct prime ideals `p₁, …, pₙ`, none of which is a minimal prime ideal of `A`,
     there exists an ideal `a` of `A` whose associated prime ideals are `p₁, …, pₙ`.

The formalization below proves both parts. `associatedPrimes` of an ideal `a` is
`Submodule.associatedPrimes a` (with `A` as a module over itself), i.e. the set of prime
ideals `p` with `p = radical (a : x)` for some `x : A`; by Mathlib's Theorem 4.5
(`Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`) these are
exactly the radicals of the components in a minimal primary decomposition, which is
Atiyah–Macdonald's definition of "prime ideals belonging to `a`".
-/
import Mathlib

open Ideal

namespace AtiyahMcdonald69.Ex_4_19

variable {A : Type*} [CommRing A]

/-! ### `S_p(0)`, the kernel of `A → A_p` -/

/-- `S_p(0)` is the kernel of the canonical homomorphism `A → A_p`, i.e. of the
localization map `A → Localization p.primeCompl`. -/
noncomputable def spZero (p : Ideal A) [p.IsPrime] : Ideal A :=
  RingHom.ker (algebraMap A (Localization p.primeCompl))

theorem mem_spZero {p : Ideal A} [p.IsPrime] {a : A} :
    a ∈ spZero p ↔ ∃ s : A, s ∉ p ∧ s * a = 0 := by
  rw [spZero, RingHom.mem_ker,
    IsLocalization.map_eq_zero_iff p.primeCompl (Localization p.primeCompl) a]
  constructor
  · rintro ⟨⟨s, hs⟩, hsa⟩
    exact ⟨s, hs, hsa⟩
  · rintro ⟨s, hs, hsa⟩
    exact ⟨⟨s, hs⟩, hsa⟩

/-- Exercise 4.10 (i): `S_p(0) ⊆ p`. -/
theorem spZero_le (p : Ideal A) [p.IsPrime] : spZero p ≤ p := by
  intro a ha
  obtain ⟨s, hs, hsa⟩ := mem_spZero.mp ha
  have hmem : s * a ∈ p := by
    rw [hsa]
    exact p.zero_mem
  exact ((inferInstance : p.IsPrime).mem_or_mem hmem).resolve_left hs

/-- If `p ⊆ q` then `S_q(0) ⊆ S_p(0)`. -/
theorem spZero_antitone {p q : Ideal A} [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    spZero q ≤ spZero p := by
  intro a ha
  obtain ⟨s, hs, hsa⟩ := mem_spZero.mp ha
  exact mem_spZero.mpr ⟨s, fun hsp => hs (hpq hsp), hsa⟩

/-- `radical S_p(0) ⊆ p`, the easy half of Exercise 4.10 (ii). -/
theorem radical_spZero_le (p : Ideal A) [p.IsPrime] : (spZero p).radical ≤ p :=
  (Ideal.IsPrime.radical_le_iff (inferInstance : p.IsPrime)).mpr (spZero_le p)

/-- **Exercise 4.19 (i)**: every `p`-primary ideal contains `S_p(0)`. -/
theorem spZero_le_of_isPrimary {p q : Ideal A} [p.IsPrime] (hq : q.IsPrimary)
    (hqr : q.radical = p) : spZero p ≤ q := by
  intro a ha
  obtain ⟨s, hs, hsa⟩ := mem_spZero.mp ha
  have hsq : a * s ∈ q := by
    rw [mul_comm]
    rw [hsa]
    exact q.zero_mem
  have hs' : s ∉ q.radical := by
    rw [hqr]
    exact hs
  rcases (Ideal.isPrimary_iff.mp hq).2 hsq with h | h
  · exact h
  · exact absurd h hs'

/-! ### Condition (L) -/

/-- Atiyah–Macdonald's condition (L), in elementwise form: an element lying in every
`p`-primary ideal lies in `S_p(0)`.  Together with part (i) this is equivalent to
`⋂ {q | q is p-primary} = S_p(0)`; see `conditionL_iff`. -/
def ConditionL : Prop :=
  ∀ (p : Ideal A) [p.IsPrime] (x : A), x ∉ spZero p → ∃ q : Ideal A, q.IsPrimary ∧ q.radical = p ∧ x ∉ q

/-- Condition (L) is equivalent to the statement that the intersection of all `p`-primary
ideals is `S_p(0)`. -/
theorem conditionL_iff (p : Ideal A) [p.IsPrime] :
    sInf {q : Ideal A | q.IsPrimary ∧ q.radical = p} = spZero p ↔
      ∀ x : A, x ∉ spZero p → ∃ q : Ideal A, q.IsPrimary ∧ q.radical = p ∧ x ∉ q := by
  constructor
  · intro h x hx
    by_contra hcon
    apply hx
    rw [← h, Ideal.mem_sInf]
    intro q hq
    by_contra hxq
    exact hcon ⟨q, hq.1, hq.2, hxq⟩
  · intro h
    refine le_antisymm ?_ ?_
    · intro x hx
      by_contra hx'
      obtain ⟨q, hq, hqr, hqx⟩ := h x hx'
      exact hqx (Ideal.mem_sInf.mp hx ⟨hq, hqr⟩)
    · intro x hx
      exact Ideal.mem_sInf.mpr (fun q hq => spZero_le_of_isPrimary hq.1 hq.2 hx)

/-- If `b ⊄ S_p(0)` and (L) holds, then `b` is not contained in some `p`-primary ideal. -/
theorem exists_isPrimary_not_le (hL : ConditionL (A := A)) {p b : Ideal A} [p.IsPrime]
    (hb : ¬ b ≤ spZero p) : ∃ q : Ideal A, q.IsPrimary ∧ q.radical = p ∧ ¬ b ≤ q := by
  obtain ⟨x, hxb, hx⟩ := SetLike.not_le_iff_exists.mp hb
  obtain ⟨q, hq, hqr, hxq⟩ := hL p x hx
  exact ⟨q, hq, hqr, fun h => hxq (h hxb)⟩

/-! ### The main induction -/

/-- **Auxiliary induction.** Let `A` satisfy (L) and let `s` be a finite set of distinct
prime ideals, none of them minimal.  Then there is a minimal primary decomposition whose
associated primes are exactly `s`.

The induction removes a maximal element `p₀` of `s` (maximality is used to find elements of
`p₀` outside the other primes, and in the contradiction with the minimality hypothesis), and
adjoins a `p₀`-primary ideal `q₀` which does not contain the ideal produced by the induction
hypothesis; the trick `x * y ^ m` (with `x` witnessing that a component is needed and
`y ∈ p₀` outside the other primes) shows that the new decomposition is still irredundant. -/
theorem exists_minimalPrimaryDecomposition (hL : ConditionL (A := A)) :
    ∀ (n : ℕ) (s : Finset (Ideal A)), s.card = n →
      (∀ p ∈ s, p.IsPrime) → (∀ p ∈ s, p ∉ minimalPrimes A) →
      ∃ t : Finset (Ideal A),
        Submodule.IsMinimalPrimaryDecomposition (t.inf id) t ∧
          (fun q => q.radical) '' (t : Set (Ideal A)) = (s : Set (Ideal A)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hcard hprime hmin
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
    · obtain ⟨p₀, hp₀mem, hp₀max⟩ := s.exists_maximal hne
      have hp₀prime : p₀.IsPrime := hprime p₀ hp₀mem
      have hcard' : (s.erase p₀).card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hp₀mem
      obtain ⟨t₀, ht₀, ht₀s⟩ :=
        ih _ hcard' (s.erase p₀) rfl (fun p hp => hprime p (Finset.mem_of_mem_erase hp))
          (fun p hp => hmin p (Finset.mem_of_mem_erase hp))
      -- `t₀.inf id` is not contained in `S_{p₀}(0)`
      have hbnotle : ¬ t₀.inf id ≤ @spZero A _ p₀ hp₀prime := by
        intro hle
        obtain ⟨p', hp'min, hp'le⟩ :=
          @Ideal.exists_minimalPrimes_le A _ ⊥ p₀ hp₀prime bot_le
        have hp'min' : Minimal (fun q : Ideal A => q.IsPrime ∧ ⊥ ≤ q) p' := hp'min
        have hp'prime : p'.IsPrime := hp'min'.1.1
        have hle' : t₀.inf id ≤ @spZero A _ p' hp'prime :=
          le_trans hle (@spZero_antitone A _ p' p₀ hp'prime hp₀prime hp'le)
        have hrad : (t₀.inf id).radical = t₀.inf (fun q => q.radical) := by
          rw [← Ideal.radicalInfTopHom_apply, map_finset_inf]
          rfl
        have hle'' : t₀.inf (fun q => q.radical) ≤ p' := by
          rw [← hrad]
          exact le_trans (Ideal.radical_mono hle') (@radical_spZero_le A _ p' hp'prime)
        obtain ⟨q, hqt, hqle⟩ := hp'prime.inf_le'.mp hle''
        have hqmem : q.radical ∈ (s.erase p₀ : Set (Ideal A)) := by
          rw [← ht₀s]
          exact Set.mem_image_of_mem _ hqt
        have hqprime : q.radical.IsPrime := Ideal.isPrime_radical (ht₀.primary hqt)
        have heq : q.radical = p' :=
          le_antisymm hqle (hp'min'.le_of_le ⟨hqprime, bot_le⟩ hqle)
        exact hmin q.radical (Finset.mem_of_mem_erase hqmem) (heq ▸ hp'min)
      obtain ⟨q₀, hq₀prim, hq₀rad, hbq₀⟩ :=
        @exists_isPrimary_not_le A _ hL p₀ (t₀.inf id) hp₀prime hbnotle
      have hq₀notin : q₀ ∉ t₀ := by
        intro hmem
        have hrad : q₀.radical ∈ (s.erase p₀ : Set (Ideal A)) := by
          rw [← ht₀s]
          exact Set.mem_image_of_mem _ hmem
        rw [hq₀rad] at hrad
        exact Finset.notMem_erase p₀ s hrad
      have hinj₀ : Set.InjOn (fun q => q.radical) (↑t₀ : Set (Ideal A)) := by
        have := Submodule.IsMinimalPrimaryDecomposition.injOn (t₀.inf id) t₀ ht₀
        simpa [Function.onFun, Submodule.colon_univ] using this
      refine ⟨insert q₀ t₀, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      · -- primary
        intro J hJ
        rcases Finset.mem_insert.mp hJ with rfl | hJ
        · exact hq₀prim
        · exact ht₀.primary hJ
      · -- distinct radicals
        have hq₀notin_image : p₀ ∉ (fun q => q.radical) '' (↑t₀ : Set (Ideal A)) := by
          rw [ht₀s]
          exact Finset.notMem_erase p₀ s
        intro J hJ K hK hJK
        simp only [Function.onFun, ne_eq, Submodule.colon_univ]
        rintro hEq
        refine hJK ?_
        rcases Finset.mem_insert.mp hJ with hJq | hJt
        · rcases Finset.mem_insert.mp hK with hKq | hKt
          · rw [hJq, hKq]
          · exfalso
            apply hq₀notin_image
            rw [← hq₀rad, ← hJq, hEq]
            exact Set.mem_image_of_mem _ hKt
        · rcases Finset.mem_insert.mp hK with hKq | hKt
          · exfalso
            apply hq₀notin_image
            rw [← hq₀rad, ← hKq, ← hEq]
            exact Set.mem_image_of_mem _ hJt
          · exact hinj₀ hJt hKt hEq
      · -- irredundancy
        intro J hJ
        rcases Finset.mem_insert.mp hJ with hJq | hJt
        · rw [hJq, Finset.erase_insert hq₀notin]
          exact hbq₀
        · have hJne : q₀ ≠ J := fun h => hq₀notin (h ▸ hJt)
          have herase : (insert q₀ t₀).erase J = insert q₀ (t₀.erase J) := by
            ext z
            simp only [Finset.mem_erase, Finset.mem_insert]
            constructor
            · rintro ⟨hzJ, hzq | hzt⟩
              · exact Or.inl hzq
              · exact Or.inr ⟨hzJ, hzt⟩
            · rintro (hzq | ⟨hzJ, hzt⟩)
              · rw [hzq]
                exact ⟨hJne, Or.inl rfl⟩
              · exact ⟨hzJ, Or.inr hzt⟩
          rw [herase, Finset.inf_insert]
          intro hle
          obtain ⟨x, hxmem, hxJ⟩ := SetLike.not_le_iff_exists.mp (ht₀.minimal hJt)
          have hJradmem : Ideal.radical J ∈ (s.erase p₀ : Set (Ideal A)) := by
            rw [← ht₀s]
            exact Set.mem_image_of_mem _ hJt
          have hJrads : Ideal.radical J ∈ s := Finset.mem_of_mem_erase hJradmem
          have hJradne : Ideal.radical J ≠ p₀ := Finset.ne_of_mem_erase hJradmem
          have hp₀notle : ¬ p₀ ≤ Ideal.radical J := by
            intro hle'
            exact hJradne (le_antisymm hle' (hp₀max hJrads hle')).symm
          obtain ⟨y, hyp₀, hyJ⟩ := SetLike.not_le_iff_exists.mp hp₀notle
          obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp (hq₀rad ▸ hyp₀)
          have hmem : x * y ^ m ∈ q₀ ⊓ (t₀.erase J).inf id :=
            ⟨Ideal.mul_mem_left q₀ x hm, Ideal.mul_mem_right (y ^ m) _ hxmem⟩
          have hxym : x * y ^ m ∈ J := hle hmem
          have hyrad : y ^ m ∈ Ideal.radical J := by
            rcases (Ideal.isPrimary_iff.mp (ht₀.primary hJt)).2 hxym with h | h
            · exact absurd h hxJ
            · exact h
          exact hyJ ((Ideal.isPrime_radical (ht₀.primary hJt)).mem_of_pow_mem m hyrad)
      · -- the image of the radicals is `s`
        rw [Finset.coe_insert, Set.image_insert_eq, hq₀rad, ht₀s, ← Finset.coe_insert,
          Finset.insert_erase hp₀mem]

/-- **Exercise 4.19 (ii)**.  If `A` satisfies (L), and `s` is a finite set of distinct prime
ideals none of which is a minimal prime ideal of `A`, then there is an ideal whose associated
prime ideals are exactly `s`. -/
theorem exists_ideal_associatedPrimes_eq (hL : ConditionL (A := A)) {s : Finset (Ideal A)}
    (hprime : ∀ p ∈ s, p.IsPrime) (hmin : ∀ p ∈ s, p ∉ minimalPrimes A) :
    ∃ a : Ideal A, a.associatedPrimes = (s : Set (Ideal A)) := by
  obtain ⟨t, ht, hts⟩ := exists_minimalPrimaryDecomposition hL s.card s rfl hprime hmin
  refine ⟨t.inf id, ?_⟩
  have h1 : (fun J : Ideal A => (J.colon Set.univ).radical) = fun q => q.radical :=
    funext fun J => by simp
  rw [← Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes ht, h1, hts]

/-- **Exercise 4.19 (ii)**, stated with the indexing of the book: for distinct prime ideals
`p 0, …, p (n-1)`, none of which is a minimal prime ideal of `A`, there is an ideal of `A`
whose associated prime ideals are precisely these. -/
theorem exists_ideal_associatedPrimes_eq_range (hL : ConditionL (A := A)) {n : ℕ}
    (p : Fin n → Ideal A) (hprime : ∀ i, (p i).IsPrime) (hinj : Function.Injective p)
    (hmin : ∀ i, p i ∉ minimalPrimes A) :
    ∃ a : Ideal A, a.associatedPrimes = Set.range p := by
  have hcard : (Finset.univ.image p).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hprime' : ∀ q ∈ Finset.univ.image p, q.IsPrime := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact hprime i
  have hmin' : ∀ q ∈ Finset.univ.image p, q ∉ minimalPrimes A := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact hmin i
  obtain ⟨a, ha⟩ := exists_ideal_associatedPrimes_eq hL hprime' hmin'
  refine ⟨a, ?_⟩
  rw [show ((Finset.univ.image p : Finset (Ideal A)) : Set (Ideal A)) = Set.range p from ?_]
    at ha
  · exact ha
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Condition (L) stated in the form used in the book, i.e. with an actual intersection:
`⋂ {q | q is p-primary} = S_p(0)` for every prime `p`. -/
theorem ConditionL.of_sInf
    (h : ∀ (p : Ideal A) [p.IsPrime],
      sInf {q : Ideal A | q.IsPrimary ∧ q.radical = p} = spZero p) :
    ConditionL (A := A) := by
  intro p hp x hx
  exact (@conditionL_iff A _ p hp).mp (@h p hp) x hx

/-- **Exercise 4.19 (ii)**, with the hypothesis written as the book writes it: the
intersection of all `p`-primary ideals is `S_p(0)` for every prime `p`. -/
theorem part_ii
    (h : ∀ (p : Ideal A) [p.IsPrime],
      sInf {q : Ideal A | q.IsPrimary ∧ q.radical = p} = spZero p)
    {s : Finset (Ideal A)} (hprime : ∀ p ∈ s, p.IsPrime)
    (hmin : ∀ p ∈ s, p ∉ minimalPrimes A) :
    ∃ a : Ideal A, a.associatedPrimes = (s : Set (Ideal A)) :=
  exists_ideal_associatedPrimes_eq (ConditionL.of_sInf h) hprime hmin

/-! ### Remarks on the natural proof (audit)

The natural proof (the hint printed in the book) argues, in the contradiction step, with a
*minimal* prime ideal `p ⊆ pₙ` and invokes Exercise 4.10 (ii), `radical S_p(0) = p` for
minimal `p`.  Auditing the argument shows that only the easy half `radical S_p(0) ⊆ p`
(Exercise 4.10 (i), here `radical_spZero_le`) is required, together with the minimality of
`p`, which is used to conclude `pᵢ ⊆ p → pᵢ = p`.  This is the route taken above (`hbnotle`).

The hypothesis that no `pᵢ` is a minimal prime ideal of `A` is essential, and the formal
proof uses it exactly once, in the step `heq`.  It cannot be dropped: for `A = k[X]` with
`k` a field, no ideal has associated prime ideals `{(0), (X)}`.  Indeed, if `(0)` is an
associated prime of `a`, then `(0) = radical (a : x)` for some `x ≠ 0`, so `a : x = 0`;
if moreover `a ≠ 0`, say `a = (f)` with `f ≠ 0`, then `f * x ∈ (f) = a`, i.e. `f ∈ a : x`,
a contradiction.  Hence `a = 0`, whose only associated prime is `(0)`.  So `(X)` — a
non-minimal prime — cannot be added, while `(0)` is minimal.

Finally, condition (L) is used only in part (ii), and only through
`exists_isPrimary_not_le`; part (i) (`spZero_le_of_isPrimary`) holds in any commutative ring.
The statement "(Noetherian rings satisfy this condition)" is a forward reference to
Chapter 10 and is therefore taken as a hypothesis here, exactly as in the exercise.
-/

/-! ### Axiom checks (only `propext`, `Classical.choice`, `Quot.sound` are permitted) -/

#print axioms AtiyahMcdonald69.Ex_4_19.spZero_le_of_isPrimary
#print axioms AtiyahMcdonald69.Ex_4_19.conditionL_iff
#print axioms AtiyahMcdonald69.Ex_4_19.exists_minimalPrimaryDecomposition
#print axioms AtiyahMcdonald69.Ex_4_19.exists_ideal_associatedPrimes_eq
#print axioms AtiyahMcdonald69.Ex_4_19.exists_ideal_associatedPrimes_eq_range
#print axioms AtiyahMcdonald69.Ex_4_19.part_ii
