/-
# Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), Exercise 11.6 (p. 126)

**Original exercise.** Let `A` be a ring (commutative, with `1`; in the book rings are nonzero) and let
`A[x]` be the polynomial ring in one indeterminate over `A`. Prove that
`1 + dim A ≤ dim A[x] ≤ 1 + 2 * dim A`,
where `dim` is the Krull dimension (the book allows the value `∞`, i.e. the convention that a ring of
infinite Krull dimension has `dim = ∞`).

**Coverage.** Both inequalities, for an arbitrary ring — no Noetherian hypothesis is used anywhere.
Krull dimension is Mathlib's `ringKrullDim : CommRing → WithBot ℕ∞`: the top element `⊤` is `∞`, and
`⊥` is the value on the zero ring. Since `⊥ + 1 = ⊥` and `1 + 2 * ⊥ = ⊥` in `WithBot ℕ∞`, the
statement below holds for *all* commutative rings, so no `Nontrivial` hypothesis is needed. For
`dim A = ⊤` the two inequalities read `⊤ ≤ dim A[x] ≤ ⊤`, so they say `dim A[x] = ⊤`; the direction
`dim A = ⊤ → dim A[x] = ⊤` is also recorded separately as
`ringKrullDim_polynomial_eq_top_of_eq_top` (the converse follows from the second inequality).

**Source of the natural-language proof.**
https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-11-6
(public repository `j346huan/DoYourExercise`, commit `80e1ebef…`, file
`.scratch/DoYourExercise/content/AtiyahMcdonald69/AtiyahMcdonald69-11-6/proof.tex`).

**Mathematical approach (and where each step is formalised).**
*Lower bound* (`part_a`). A strict chain `𝔭₀ ⊊ … ⊊ 𝔭ᵣ` of primes of `A` gives the strict chain
`𝔭₀[x] ⊊ … ⊊ 𝔭ᵣ[x] ⊊ 𝔭ᵣ[x] + (x)` of primes of `A[x]`; the last ideal is prime because
`A[x]/(𝔭ᵣ[x] + (x)) ≅ A/𝔭ᵣ`. This construction is formalised from scratch here:
`extIdeal p = 𝔭[x]` (`under_extIdeal`, `isPrime_extIdeal`, `extIdeal_lt_extIdeal`), the ideal
`upperIdeal p = 𝔭[x] + (x)` realised as the contraction of `(x)` along `A[x] → (A/𝔭)[x]`
(`isPrime_upperIdeal`, `extIdeal_lt_upperIdeal`, both with contraction `𝔭`), then the monotone maps
`mapC`, `upperC` on `Spec A → Spec A[x]`, the strict inequality `mapC P < upperC P`
(`mapC_lt_upperC`) and the height computation `height_step` give the bound by taking suprema
(`part_a`). The chain-level form of the same construction is `exists_prime_chain_succ`
(every strict chain of `r + 1` primes of `A` extends to one of `r + 2` primes of `A[x]`), and the
height form is `prime_height_add_one_le`.
*Upper bound* (`part_b`). For a prime `𝔭` of `A`, primes of `A[x]` above `𝔭` correspond to primes of
the polynomial ring `κ(𝔭)[x]` over the residue field, which has Krull dimension `1`; hence at most two
members of a strict chain of primes of `A[x]` have the same contraction, and a chain whose
contractions have length `d` has length at most `2 * d + 1`. The local step is `not_three_same_under`
(no three primes `q₀ < q₁ < q₂` of `A[x]` share a contraction, proved with Mathlib's order
isomorphism `PrimeSpectrum.preimageOrderIsoFiber` between the fibre of `Spec A[x] → Spec A` at `𝔭`
and `Spec κ(𝔭)[x]`); it gives `krullDim_fiber_le_one`, i.e. that every fibre of the contraction map
`Spec A[x] → Spec A` has Krull dimension at most `1`. The counting step is Mathlib's general lemma
`Order.krullDim_le_of_krullDim_preimage_le'`, which turns a fibre bound `m` into
`dim ≤ (m+1) * dim A + m`; `part_b` is its specialisation `m = 1`. (The same inequality is available
in Mathlib as `Polynomial.ringKrullDim_le`, recorded here as `part_b_via_mathlib`.)

**Sanity checks.** `ringKrullDim_polynomial_field` shows the bounds are sharp: over a field the two
inequalities give `dim K[x] = 1`, so the statement of the exercise is not vacuous.
`ringKrullDim_polynomial_eq_top_of_eq_top` covers the infinite-dimensional convention.

**Adaptations.** `dim A[x]` is `ringKrullDim R[X]`, `A[x]` being `Polynomial R`. The book's
`1 + dim A` is written `1 + ringKrullDim R` and the book's `1 + 2 dim A` as `1 + 2 * ringKrullDim R`;
addition and multiplication in `WithBot ℕ∞` are commutative, so these agree with
`ringKrullDim R + 1` and `2 * ringKrullDim R + 1`. Nothing else is adapted: no extra hypotheses and no
weakened conclusion. All results are proved with the usual Lean/Mathlib axioms only
(`propext`, `Classical.choice`, `Quot.sound`); see the `#print axioms` output at the end of the file.
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_11_6

open Polynomial

variable {R : Type*} [CommRing R]

/-! ### The two prime ideals `𝔭[x]` and `𝔭[x] + (x)` of `R[x]` -/

/-- The textbook ideal `𝔭[x]` of `R[x]`: the extension of `𝔭` along `R → R[x]`. As a set it consists
of the polynomials all of whose coefficients lie in `𝔭`. -/
noncomputable def extIdeal (p : Ideal R) : Ideal R[X] := p.map (C : R →+* R[X])

/-- The textbook ideal `𝔭[x] + (x)`: the polynomials whose constant coefficient lies in `𝔭`. It is
realised as the contraction of `(x)` along the ring homomorphism `R[x] → (R/𝔭)[x]`. -/
noncomputable def upperIdeal (p : Ideal R) : Ideal R[X] :=
  Ideal.comap (mapRingHom (Ideal.Quotient.mk p)) (Ideal.span {X} : Ideal (R ⧸ p)[X])

lemma mapRingHom_C_mk (p : Ideal R) (b : R) :
    mapRingHom (Ideal.Quotient.mk p) (C b) = C (Ideal.Quotient.mk p b) :=
  Polynomial.map_C _

lemma mapRingHom_X_mk (p : Ideal R) : mapRingHom (Ideal.Quotient.mk p) (X : R[X]) = X :=
  Polynomial.map_X _

lemma isPrime_extIdeal (p : Ideal R) (hp : p.IsPrime) : (extIdeal p).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime p).mpr hp

/-- The contraction of `𝔭[x]` is `𝔭`; in particular `𝔭 ↦ 𝔭[x]` is injective and order reflecting. -/
lemma under_extIdeal (p : Ideal R) : (extIdeal p).under R = p := by
  refine le_antisymm ?_ ?_
  · intro a ha
    rw [Ideal.under_def, Ideal.mem_comap] at ha
    have h' : (C a : R[X]) ∈ Ideal.map (C : R →+* R[X]) p := ha
    simpa using (Ideal.mem_map_C_iff.mp h' 0)
  · intro a ha
    rw [Ideal.under_def, Ideal.mem_comap]
    exact Ideal.mem_map_of_mem (f := (C : R →+* R[X])) ha

/-- `𝔭 ↦ 𝔭[x]` is strictly increasing, so it maps a strict chain of primes to a strict chain. -/
lemma extIdeal_lt_extIdeal {p q : Ideal R} (h : p < q) : extIdeal p < extIdeal q := by
  refine lt_of_le_of_ne (Ideal.map_mono h.le) ?_
  intro heq
  have h2 : (extIdeal p).under R = (extIdeal q).under R := congrArg (Ideal.under R) heq
  rw [under_extIdeal, under_extIdeal] at h2
  exact h.ne h2

/-- `𝔭[x] + (x)` is prime: modulo it, `R[x]` becomes the domain `R/𝔭`. -/
lemma isPrime_upperIdeal (p : Ideal R) (hp : p.IsPrime) : (upperIdeal p).IsPrime := by
  have hD : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have hX : (Ideal.span {X} : Ideal (R ⧸ p)[X]).IsPrime := by
    rw [← ker_constantCoeff]
    exact RingHom.ker_isPrime _
  exact Ideal.IsPrime.comap (mapRingHom (Ideal.Quotient.mk p))

lemma extIdeal_le_upperIdeal (p : Ideal R) : extIdeal p ≤ upperIdeal p := by
  refine Ideal.map_le_iff_le_comap.mpr fun b hb => ?_
  show C b ∈ Ideal.comap (mapRingHom (Ideal.Quotient.mk p)) (Ideal.span {X})
  refine Ideal.mem_comap.mpr ?_
  rw [mapRingHom_C_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  exact Ideal.zero_mem _

lemma X_mem_upperIdeal (p : Ideal R) : (X : R[X]) ∈ upperIdeal p := by
  show X ∈ Ideal.comap (mapRingHom (Ideal.Quotient.mk p)) (Ideal.span {X})
  refine Ideal.mem_comap.mpr ?_
  rw [mapRingHom_X_mk]
  exact Ideal.subset_span rfl

lemma X_notMem_extIdeal (p : Ideal R) [hp : p.IsPrime] : (X : R[X]) ∉ extIdeal p := by
  intro h
  have h1 : (1 : R) ∈ p := by
    simpa using (Ideal.mem_map_C_iff.mp h 1)
  exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

/-- `𝔭[x] ⊊ 𝔭[x] + (x)`: the polynomial `x` lies in the second ideal but not in the first. -/
lemma extIdeal_lt_upperIdeal (p : Ideal R) [hp : p.IsPrime] : extIdeal p < upperIdeal p :=
  lt_of_le_of_ne (extIdeal_le_upperIdeal p) fun h =>
    X_notMem_extIdeal p (h ▸ X_mem_upperIdeal p)

/-- The prime `𝔭[x] + (x)` has the same contraction as `𝔭[x]`, namely `𝔭`. -/
lemma under_upperIdeal (p : Ideal R) [p.IsPrime] : (upperIdeal p).under R = p := by
  refine le_antisymm ?_ ?_
  · intro a ha
    rw [Ideal.under_def, Ideal.mem_comap] at ha
    have h2 : mapRingHom (Ideal.Quotient.mk p) (C a) ∈ Ideal.span {X} := ha
    rw [mapRingHom_C_mk, ← ker_constantCoeff, RingHom.mem_ker] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h2)
  · intro a ha
    rw [Ideal.under_def, Ideal.mem_comap]
    exact extIdeal_le_upperIdeal p (Ideal.mem_map_of_mem (f := (C : R →+* R[X])) ha)

/-! ### The two maps `Spec R → Spec R[x]` used in the lower bound -/

/-- The map `𝔭 ↦ 𝔭[x]` on prime spectra. -/
noncomputable def mapC (P : PrimeSpectrum R) : PrimeSpectrum R[X] :=
  ⟨extIdeal P.asIdeal, isPrime_extIdeal P.asIdeal P.isPrime⟩

/-- The map `𝔭 ↦ 𝔭[x] + (x)` on prime spectra. -/
noncomputable def upperC (P : PrimeSpectrum R) : PrimeSpectrum R[X] :=
  ⟨upperIdeal P.asIdeal, isPrime_upperIdeal P.asIdeal P.isPrime⟩

lemma mapC_strictMono : StrictMono (mapC (R := R)) := by
  intro P Q hPQ
  exact extIdeal_lt_extIdeal hPQ

lemma mapC_lt_upperC (P : PrimeSpectrum R) : mapC P < upperC P :=
  extIdeal_lt_upperIdeal P.asIdeal

/-- The height computation behind the lower bound: `ht 𝔭 + 1 ≤ ht (𝔭[x] + (x))`. -/
lemma height_step (P : PrimeSpectrum R) :
    Order.height P + 1 ≤ Order.height (upperC P) := by
  have h1 : Order.height P ≤ Order.height (mapC P) :=
    Order.height_le_height_apply_of_strictMono (mapC (R := R)) mapC_strictMono P
  have h2 : Order.height (mapC P) + 1 ≤ Order.height (upperC P) :=
    Order.height_add_one_le (mapC_lt_upperC P)
  calc Order.height P + 1 = 1 + Order.height P := add_comm _ _
    _ ≤ 1 + Order.height (mapC P) := by gcongr
    _ = Order.height (mapC P) + 1 := add_comm _ _
    _ ≤ Order.height (upperC P) := h2

/-- Height form of the textbook construction: for a prime `𝔭`, the two primes `𝔭[x] < 𝔭[x] + (x)` of
`R[x]` give `ht 𝔭 + 1 ≤ ht (𝔭[x] + (x))`. -/
lemma height_step_ideal (p : Ideal R) (hp : p.IsPrime) :
    p.height + 1 ≤ (upperIdeal p).height := by
  have h := height_step ⟨p, hp⟩
  show (⟨p, hp⟩ : PrimeSpectrum R).asIdeal.height + 1 ≤ (upperC ⟨p, hp⟩).asIdeal.height
  rwa [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]

/-- Chain lifting in height form: `ht 𝔭 + 1 ≤ dim R[x]` for every prime `𝔭` of `R`. -/
theorem prime_height_add_one_le (p : Ideal R) (hp : p.IsPrime) :
    ((p.height + 1 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R[X] := by
  have hp' : (upperIdeal p).IsPrime := isPrime_upperIdeal p hp
  exact (WithBot.coe_le_coe.mpr (height_step_ideal p hp)).trans
    (Ideal.height_le_ringKrullDim_of_isPrime (I := upperIdeal p))

/-- **Chain lifting.** Every strict chain of primes of `R` can be extended, by appending
`𝔭[x] + (x)` above the image of its top element, to a strict chain of primes of `R[x]` one step
longer. This is precisely the construction used for the lower bound in the solution. -/
theorem exists_prime_chain_succ (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum R[X]), l'.length = l.length + 1 := by
  refine ⟨(l.map (mapC (R := R)) mapC_strictMono).snoc (upperC l.last) ?_, ?_⟩
  · rw [LTSeries.last_map]
    exact mapC_lt_upperC l.last
  · simp

/-- **Exercise 11.6, first inequality**: `1 + dim A ≤ dim A[x]`. Proved here by the book's chain
construction (`mapC`, `upperC`, `height_step`) and the formula
`dim = ⨆ (ht 𝔭)` for the Krull dimension. -/
theorem part_a (R : Type*) [CommRing R] : 1 + ringKrullDim R ≤ ringKrullDim R[X] := by
  have key : ringKrullDim R + 1 ≤ ringKrullDim R[X] := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · have hsub : Subsingleton R := hR
      have hsub' : Subsingleton R[X] :=
        ⟨fun f g => Polynomial.ext fun n => Subsingleton.elim _ _⟩
      rw [ringKrullDim_eq_bot_of_subsingleton (R := R),
        ringKrullDim_eq_bot_of_subsingleton (R := R[X])]
      simp
    · have hnt : Nontrivial R := hR
      simp only [ringKrullDim, Order.krullDim_eq_iSup_height_of_nonempty (α := PrimeSpectrum R),
        Order.krullDim_eq_iSup_height_of_nonempty (α := PrimeSpectrum R[X])]
      rw [show (1 : WithBot ℕ∞) = ↑(1 : ℕ∞) from WithBot.coe_one.symm, ← WithBot.coe_add,
        ENat.iSup_add, WithBot.coe_le_coe]
      refine iSup_le fun P => (height_step P).trans ?_
      exact le_iSup (fun Q : PrimeSpectrum R[X] => Order.height Q) (upperC P)
  simpa only [add_comm] using key

/-! ### The book's upper-bound step -/

/-- A preorder of Krull dimension at most one has no strictly increasing chain of three elements
(the middle one would be neither minimal nor maximal). -/
theorem no_three_of_krullDim_le_one {α : Type*} [Preorder α]
    (h : Order.krullDim α ≤ ((1 : ℕ) : WithBot ℕ∞)) {A B C : α}
    (hAB : A < B) (hBC : B < C) : False := by
  have h' : Order.krullDim α ≤ 1 := h
  rcases (Order.krullDim_le_one_iff.mp h') B with hmin | hmax
  · exact (lt_irrefl A) (lt_of_lt_of_le hAB (hmin hAB.le))
  · exact (lt_irrefl B) (lt_of_lt_of_le hBC (hmax hBC.le))

/-- **The book's upper-bound step.** Primes of `R[x]` above a fixed prime `𝔭` of `R` correspond to
primes of `κ(𝔭)[x]`, which has Krull dimension at most one; hence a strictly increasing chain of
primes of `R[x]` contains at most two primes with a given contraction. -/
theorem not_three_same_under {q₀ q₁ q₂ : PrimeSpectrum R[X]}
    (h₀₁ : q₀ < q₁) (h₁₂ : q₁ < q₂) (h : q₀.asIdeal.under R = q₂.asIdeal.under R) : False := by
  have h₀₁' : q₀.asIdeal.under R ≤ q₁.asIdeal.under R := Ideal.comap_mono h₀₁.le
  have h₁₂' : q₁.asIdeal.under R ≤ q₂.asIdeal.under R := Ideal.comap_mono h₁₂.le
  have hp₁ : q₁.asIdeal.under R = q₀.asIdeal.under R := le_antisymm (h ▸ h₁₂') h₀₁'
  have hpp : (q₀.asIdeal.under R).IsPrime := Ideal.IsPrime.under R q₀.asIdeal
  let F : PrimeSpectrum R := ⟨q₀.asIdeal.under R, hpp⟩
  have hF₀ : PrimeSpectrum.comap (algebraMap R R[X]) q₀ = F :=
    PrimeSpectrum.ext_iff.mpr rfl
  have hF₁ : PrimeSpectrum.comap (algebraMap R R[X]) q₁ = F :=
    PrimeSpectrum.ext_iff.mpr hp₁
  have hF₂ : PrimeSpectrum.comap (algebraMap R R[X]) q₂ = F :=
    PrimeSpectrum.ext_iff.mpr h.symm
  let Q₀ : ↑(PrimeSpectrum.comap (algebraMap R R[X]) ⁻¹' ({F} : Set (PrimeSpectrum R))) :=
    ⟨q₀, by simpa using hF₀⟩
  let Q₁ : ↑(PrimeSpectrum.comap (algebraMap R R[X]) ⁻¹' ({F} : Set (PrimeSpectrum R))) :=
    ⟨q₁, by simpa using hF₁⟩
  let Q₂ : ↑(PrimeSpectrum.comap (algebraMap R R[X]) ⁻¹' ({F} : Set (PrimeSpectrum R))) :=
    ⟨q₂, by simpa using hF₂⟩
  have hQ₀₁ : Q₀ < Q₁ := h₀₁
  have hQ₁₂ : Q₁ < Q₂ := h₁₂
  have hdim : Order.krullDim (PrimeSpectrum (F.asIdeal.Fiber R[X])) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    show Order.krullDim (PrimeSpectrum ((q₀.asIdeal.under R).Fiber R[X])) ≤ ((1 : ℕ) : WithBot ℕ∞)
    rw [← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv
        (polyEquivTensor R (q₀.asIdeal.under R).ResidueField).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance
  exact no_three_of_krullDim_le_one hdim
    ((PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) F).strictMono hQ₀₁)
    ((PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) F).strictMono hQ₁₂)

/-- The contraction map `Spec R[x] → Spec R`, `q ↦ q ∩ R`, is monotone. -/
theorem underMonotone : Monotone (fun q : PrimeSpectrum R[X] =>
    (⟨q.asIdeal.under R, Ideal.IsPrime.under R q.asIdeal⟩ : PrimeSpectrum R)) := by
  intro a b hab
  exact Ideal.comap_mono hab

/-- Every fibre of the contraction map `Spec R[x] → Spec R` has Krull dimension at most one: this is
the counting statement that at most two primes of `R[x]` in a strict chain have the same
contraction (a preorder of Krull dimension `≤ 1` has no strictly increasing chain of three elements,
because its middle element would be neither minimal nor maximal). -/
theorem krullDim_fiber_le_one (p : PrimeSpectrum R) :
    Order.krullDim ↥((fun q : PrimeSpectrum R[X] =>
      (⟨q.asIdeal.under R, Ideal.IsPrime.under R q.asIdeal⟩ : PrimeSpectrum R)) ⁻¹' {p}) ≤ 1 := by
  set f : PrimeSpectrum R[X] → PrimeSpectrum R :=
    fun q => ⟨q.asIdeal.under R, Ideal.IsPrime.under R q.asIdeal⟩
  rw [Order.krullDim_le_one_iff]
  intro q
  by_cases hmin : IsMin q
  · exact Or.inl hmin
  · refine Or.inr ?_
    intro q' hqq'
    by_contra hcon
    have hlt : q < q' := lt_of_le_of_ne hqq' fun h => hcon (le_of_eq h.symm)
    have hmin' : ¬ ∀ b, b ≤ q → q ≤ b := hmin
    obtain ⟨b, hbq, hqb⟩ : ∃ b, ∃ (_ : b ≤ q), ¬ q ≤ b := by
      simpa only [not_forall, Classical.not_imp] using hmin'
    have hblt : b < q := lt_of_le_of_ne hbq fun h => hqb (le_of_eq h.symm)
    have e1 : f b.1 = p := b.2
    have e2 : f q'.1 = p := q'.2
    have hb' : b.1.asIdeal.under R = q'.1.asIdeal.under R := by
      have h := congrArg (fun x : PrimeSpectrum R => x.asIdeal) (e1.trans e2.symm)
      simpa [f] using h
    exact not_three_same_under hblt hlt hb'

/-- **Exercise 11.6, second inequality**, by the book's counting argument: the fibres of
`Spec R[x] → Spec R` have dimension at most one (`krullDim_fiber_le_one`), so Mathlib's general fibre
lemma `Order.krullDim_le_of_krullDim_preimage_le'` bounds `dim R[x]` by `(1+1) * dim R + 1`. -/
theorem part_b (R : Type*) [CommRing R] :
    ringKrullDim R[X] ≤ 1 + 2 * ringKrullDim R := by
  have h := Order.krullDim_le_of_krullDim_preimage_le' (m := 1)
    (f := fun q : PrimeSpectrum R[X] =>
      (⟨q.asIdeal.under R, Ideal.IsPrime.under R q.asIdeal⟩ : PrimeSpectrum R))
    underMonotone krullDim_fiber_le_one
  calc Order.krullDim (PrimeSpectrum R[X])
      ≤ (↑1 + 1) * Order.krullDim (PrimeSpectrum R) + ↑1 := h
    _ = 2 * Order.krullDim (PrimeSpectrum R) + 1 := by
        rw [show ((↑1 : WithBot ℕ∞) + 1) = 2 from by norm_num]
    _ = 1 + 2 * Order.krullDim (PrimeSpectrum R) := by rw [add_comm]

/-- The same inequality obtained from Mathlib's pre-existing theorem `Polynomial.ringKrullDim_le`
(whose proof performs the same fibre decomposition); recorded as a cross-check. -/
theorem part_b_via_mathlib (R : Type*) [CommRing R] :
    ringKrullDim R[X] ≤ 1 + 2 * ringKrullDim R := by
  simpa only [add_comm] using Polynomial.ringKrullDim_le (R := R)

/-- **Atiyah–Macdonald, Exercise 11.6.** For every commutative ring `A`,
`1 + dim A ≤ dim A[x] ≤ 1 + 2 * dim A`. -/
theorem solution (R : Type*) [CommRing R] :
    1 + ringKrullDim R ≤ ringKrullDim R[X] ∧
      ringKrullDim R[X] ≤ 1 + 2 * ringKrullDim R :=
  ⟨part_a R, part_b R⟩

/-- The infinite-dimensional case, which the solution treats separately: if `dim A = ∞` then
`dim A[x] = ∞`. Proved through the chain lifting `exists_prime_chain_succ`: arbitrary long strict
chains in `Spec A` give arbitrary long strict chains in `Spec A[x]`. Together with the second
inequality this gives `dim A[x] = ∞ ↔ dim A = ∞`, the convention used in the book. -/
theorem ringKrullDim_polynomial_eq_top_of_eq_top (h : ringKrullDim R = ⊤) :
    ringKrullDim R[X] = ⊤ := by
  rw [ENat.WithBot.eq_top_iff_forall_ge]
  intro n
  show ((n : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R[X])
  rw [Order.le_krullDim_iff]
  cases n with
  | zero =>
    have h0 : ((0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by rw [h]; exact le_top
    have h0' : ((0 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) := h0
    rw [Order.le_krullDim_iff] at h0'
    obtain ⟨l, hl⟩ := h0'
    exact ⟨l.map (mapC (R := R)) mapC_strictMono, by simpa using hl⟩
  | succ k =>
    have hk : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by rw [h]; exact le_top
    have hk' : ((k : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) := hk
    rw [Order.le_krullDim_iff] at hk'
    obtain ⟨l, hl⟩ := hk'
    obtain ⟨l', hl'⟩ := exists_prime_chain_succ l
    exact ⟨l', by rw [hl', hl]⟩

/-- The bounds are sharp: over a field both inequalities force `dim K[x] = 1`. This also witnesses
that the statement of the exercise is not vacuous. -/
theorem ringKrullDim_polynomial_field (K : Type*) [Field K] : ringKrullDim K[X] = 1 := by
  have h1 : 1 + ringKrullDim K ≤ ringKrullDim K[X] := part_a K
  have h2 : ringKrullDim K[X] ≤ 1 + 2 * ringKrullDim K := part_b K
  rw [ringKrullDim_eq_zero_of_field K] at h1 h2
  simp only [mul_zero, add_zero] at h1 h2
  exact le_antisymm h2 h1

end AtiyahMcdonald69.Ex_11_6

#print axioms AtiyahMcdonald69.Ex_11_6.part_a
#print axioms AtiyahMcdonald69.Ex_11_6.part_b
#print axioms AtiyahMcdonald69.Ex_11_6.part_b_via_mathlib
#print axioms AtiyahMcdonald69.Ex_11_6.krullDim_fiber_le_one
#print axioms AtiyahMcdonald69.Ex_11_6.solution
#print axioms AtiyahMcdonald69.Ex_11_6.not_three_same_under
#print axioms AtiyahMcdonald69.Ex_11_6.exists_prime_chain_succ
#print axioms AtiyahMcdonald69.Ex_11_6.ringKrullDim_polynomial_eq_top_of_eq_top
#print axioms AtiyahMcdonald69.Ex_11_6.ringKrullDim_polynomial_field
