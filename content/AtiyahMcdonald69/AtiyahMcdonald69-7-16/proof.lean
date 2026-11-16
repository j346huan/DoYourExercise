/-
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 7, Exercise 16 (p. 86).

Statement (verbatim): Let `A` be a Noetherian ring, `M` a finitely generated `A`-module.
Then the following are equivalent:

(i)   `M` is a flat `A`-module;
(ii)  `M_𝔭` is a free `A_𝔭`-module, for all prime ideals `𝔭`;
(iii) `M_𝔪` is a free `A_𝔪`-module, for all maximal ideals `𝔪`.

In other words, flat = locally free.

Formalization choices (the exercise's own objects are kept, no existential abstraction):
* `A` Noetherian:                `[IsNoetherianRing A]`
* `M` finitely generated:        `[Module.Finite A M]`
* `M` flat:                      `Module.Flat A M`
* `M_𝔭` over `A_𝔭`:               `LocalizedModule 𝔭.primeCompl M` over `Localization.AtPrime 𝔭`
* `M_𝔭` free:                    `Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M)`

The single hard input is A&M Exercise 7.15 (finitely generated flat modules over a
Noetherian local ring are free), which Mathlib provides in the stronger form
`Module.free_of_flat_of_isLocalRing` (no Noetherian hypothesis needed).
-/
import Mathlib

namespace AtiyahMcdonald69.Ex_7_16

open Module

variable (A : Type*) [CommRing A] [IsNoetherianRing A]
variable (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Atiyah–Macdonald Exercise 7.16: for a Noetherian ring `A` and a finitely generated
`A`-module `M`, flatness of `M`, freeness of every `M_𝔭` over `A_𝔭` at prime ideals, and
freeness of every `M_𝔪` over `A_𝔪` at maximal ideals are equivalent. -/
theorem solution :
    List.TFAE
      [ Module.Flat A M,
        ∀ (p : Ideal A) [p.IsPrime],
          Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M),
        ∀ (m : Ideal A) [m.IsMaximal],
          Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) ] := by
  tfae_have 1 → 2 := by
    intro hflat p hp
    -- (i) ⇒ (ii): a localization of a flat module is flat (A&M Prop. 3.3), and a finitely
    -- generated flat module over the Noetherian local ring `A_𝔭` is free (A&M Ex. 7.15).
    -- The Noetherian hypothesis on `A` is used here: `A_𝔭` is a Noetherian local ring.
    have : Module.Flat A M := hflat
    have hnoeth : IsNoetherianRing (Localization.AtPrime p) := inferInstance
    have hloc : Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
      Module.Flat.localizedModule p.primeCompl
    have hfin : Module.Finite (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
      inferInstance
    exact Module.free_of_flat_of_isLocalRing
  tfae_have 2 → 3 := by
    intro h m _hm
    exact h m
  tfae_have 3 → 1 := by
    -- (iii) ⇒ (i): freeness gives flatness over `A_𝔪`, which is flatness over `A` by
    -- `Module.flat_iff_of_isLocalization`; flatness is then local at maximal ideals
    -- (A&M Prop. 3.10), i.e. `Module.flat_of_localized_maximal`.
    intro h
    apply Module.flat_of_localized_maximal
    intro m hm
    have hfree : Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) := h m
    have hflatloc : Module.Flat (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
      Module.Flat.of_free
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime m) m.primeCompl
      (M := LocalizedModule m.primeCompl M)).mp hflatloc
  tfae_finish

/-- Atiyah–Macdonald Exercise 7.16, "flat = locally free" form: `M` is flat iff `M_𝔭` is a
free `A_𝔭`-module for every prime ideal `𝔭`. -/
theorem flat_iff_forall_free_atPrime :
    Module.Flat A M ↔
      ∀ (p : Ideal A) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
  (solution A M).out 0 1

/-- Atiyah–Macdonald Exercise 7.16, maximal-ideal form: `M` is flat iff `M_𝔪` is a free
`A_𝔪`-module for every maximal ideal `𝔪`. -/
theorem flat_iff_forall_free_atMaximal :
    Module.Flat A M ↔
      ∀ (m : Ideal A) [m.IsMaximal],
        Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
  (solution A M).out 0 2

/-- Atiyah–Macdonald Exercise 7.16: every `M_𝔭` is free over `A_𝔭` iff every `M_𝔪` is free
over `A_𝔪`. -/
theorem forall_free_atPrime_iff_forall_free_atMaximal :
    (∀ (p : Ideal A) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ↔
      ∀ (m : Ideal A) [m.IsMaximal],
        Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
  (solution A M).out 1 2

end AtiyahMcdonald69.Ex_7_16

#print axioms AtiyahMcdonald69.Ex_7_16.solution
#print axioms AtiyahMcdonald69.Ex_7_16.flat_iff_forall_free_atPrime
#print axioms AtiyahMcdonald69.Ex_7_16.flat_iff_forall_free_atMaximal
#print axioms AtiyahMcdonald69.Ex_7_16.forall_free_atPrime_iff_forall_free_atMaximal
