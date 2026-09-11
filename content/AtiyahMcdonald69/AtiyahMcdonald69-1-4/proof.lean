import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Coeff

theorem AtiyahMcdonald69.Ex_1_4.solution (A : Type*) [CommRing A] :
  Ideal.jacobson (⊥ : Ideal (Polynomial A)) = Ideal.radical (⊥ : Ideal (Polynomial A)) := by
  have nilradical_le_jacobson_polynomial :
    Ideal.radical (⊥ : Ideal (Polynomial A)) ≤ Ideal.jacobson (⊥ : Ideal (Polynomial A)) := by
    exact Ideal.radical_le_jacobson
  have unit_mul_X_add_one_of_mem_jacobson :
    ∀ f : Polynomial A, f ∈ Ideal.jacobson (⊥ : Ideal (Polynomial A)) → IsUnit (f * Polynomial.X + 1) := by
    intro f hf
    exact Ideal.mem_jacobson_bot.mp hf Polynomial.X
  have nilpotent_of_mem_jacobson_polynomial :
    ∀ f : Polynomial A, f ∈ Ideal.jacobson (⊥ : Ideal (Polynomial A)) → IsNilpotent f := by
    intro f hf
    apply Polynomial.isNilpotent_iff.mpr
    intro i
    have h := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit
      (unit_mul_X_add_one_of_mem_jacobson f hf)).2 (i + 1) (Nat.succ_ne_zero i)
    simpa [Polynomial.coeff_add, Polynomial.coeff_one] using h
  apply le_antisymm
  · intro f hf
    obtain ⟨n, hn⟩ := nilpotent_of_mem_jacobson_polynomial f hf
    change ∃ n : ℕ, f ^ n ∈ (⊥ : Ideal (Polynomial A))
    exact ⟨n, by simpa only [Ideal.mem_bot] using hn⟩
  · exact nilradical_le_jacobson_polynomial
