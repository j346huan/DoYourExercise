/-
Atiyah–Macdonald, *Introduction to Commutative Algebra* (Addison–Wesley, 1969),
Chapter 1, Exercise 24:

  "Show that every Boolean lattice becomes a Boolean ring, and that every Boolean ring becomes a
   Boolean lattice. Deduce that Boolean lattices and Boolean rings are equivalent."

Formalization conventions.

* A **Boolean lattice** in the sense of the exercise is a lattice with a smallest element `0`, a
  greatest element `1`, distributive laws, and a complement `a'` of every element `a`, unique with
  `a ⊓ a' = 0` and `a ⊔ a' = 1`.  We use Mathlib's class `BooleanAlgebra`: a bounded distributive
  lattice with a complement satisfying the complement laws.  The uniqueness of the complement,
  which is what the book's definition asks for, is proved as
  `compl_eq_of_inf_eq_bot_sup_eq_top` below.

* A **Boolean ring** is a ring in which every element is idempotent (`a * a = a`); this is Mathlib's
  class `BooleanRing`, and commutativity of the ring is *not* assumed.  (Atiyah–Macdonald use the
  convention that all rings are commutative, so nothing is lost; for completeness, commutativity
  and `a + a = 0` are nevertheless *derived* from idempotency in the section
  `BooleanRingArithmetic`, so that the two conventions are proved to agree.)

Reference for the exercise: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapter 1,
Exercise 24; see also https://j346huan.github.io/DoYourExercise/#/problem/AtiyahMcdonald69-1-24

The main declarations are
* `booleanRingOfBooleanAlgebra` : the Boolean ring attached to a Boolean lattice,
  with `a + b = (a ⊓ bᶜ) ⊔ (aᶜ ⊓ b)`, `a * b = a ⊓ b`, `0 = ⊥`, `1 = ⊤`, `-a = a`;
* `booleanAlgebraOfBooleanRing` : the Boolean lattice attached to a Boolean ring, with order
  `a ≤ b ↔ a * b = a`, `a ⊓ b = a * b`, `a ⊔ b = a + b + a * b`, `0 = 0`, `1 = 1`,
  complement `aᶜ = 1 + a`;
* `recovered_le`, `recovered_sup`, `recovered_compl`, `recovered_add`, `recovered_mul`, ... : the
  two constructions are mutually inverse on the nose (identity maps), which is the book's
  "Boolean lattices and Boolean rings are equivalent";
* `roundTripOrderIso`, `roundTripRingEquiv` : the identity maps are isomorphisms of the recovered
  lattice/ring with the original one;
* `ringHom_iff_boundedLatticeHom` : they also have the same morphisms;
* `solution` : the statement of the exercise, assembled from the above.
-/
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Order.SymmDiff
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

-- Only style linters are switched off (some `simp` sets and `haveI` uses are intentionally
-- uniform across goals); the file produces no warnings, and is checked with `-DwarningAsError`.
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped symmDiff

namespace AtiyahMcdonald69.Ex_1_24

universe u

/-! ## Boolean ring arithmetic derived from idempotency -/

section BooleanRingArithmetic

variable {A : Type u} [BooleanRing A]

/-- In a Boolean ring every element is its own additive inverse (Atiyah–Macdonald, Exercise 1.11
(a)).  Only idempotency of multiplication is used. -/
theorem add_self_eq_zero (a : A) : a + a = 0 := by
  have h : a + a = a + a + (a + a) := by
    calc a + a = (a + a) * (a + a) := (BooleanRing.mul_self (a + a)).symm
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by simp only [BooleanRing.mul_self]
  have h3 : (a + a) + (a + a) = (a + a) + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h3

/-- In a Boolean ring, `a * b + b * a = 0`.  This is the key step in proving that multiplication
is commutative. -/
theorem mul_add_mul_eq_zero (a b : A) : a * b + b * a = 0 := by
  have h : a + b = a + b + (a * b + b * a) := by
    calc a + b = (a + b) * (a + b) := (BooleanRing.mul_self (a + b)).symm
      _ = (a * a + a * b) + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + b + (a * b + b * a) := by
            simp only [BooleanRing.mul_self]
            abel
  have h3 : a + b + (a * b + b * a) = a + b + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h3

/-- In a Boolean ring every element is its own negative. -/
theorem neg_eq_self (a : A) : -a = a := by
  calc -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self_eq_zero, zero_add]

/-- Multiplication in a Boolean ring is commutative. -/
theorem mul_comm_eq (a b : A) : a * b = b * a := by
  have h := mul_add_mul_eq_zero a b
  calc a * b = -(b * a) := eq_neg_of_add_eq_zero_left h
    _ = b * a := neg_eq_self (b * a)

end BooleanRingArithmetic

/-! ## (1) A Boolean lattice becomes a Boolean ring -/

section LatticeToRing

variable {L : Type u} [BooleanAlgebra L]

/-- **A Boolean lattice becomes a Boolean ring.**  On a Boolean lattice `L` take addition to be
the symmetric difference `a + b = a ∆ b = (a ⊓ bᶜ) ⊔ (aᶜ ⊓ b)`, multiplication to be the meet
`a * b = a ⊓ b`, `0 = ⊥`, `1 = ⊤` and `-a = a`.  Commutativity, associativity and distributivity
of these operations (the book's first paragraph) are the corresponding lattice identities for
`∆` and `⊓`. -/
@[instance_reducible]
def booleanRingOfBooleanAlgebra (L : Type u) [BooleanAlgebra L] : BooleanRing L where
  add := (· ∆ ·)
  add_assoc := symmDiff_assoc
  zero := ⊥
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  neg := id
  neg_add_cancel := symmDiff_self
  add_comm := symmDiff_comm
  mul := (· ⊓ ·)
  mul_assoc := inf_assoc
  left_distrib := inf_symmDiff_distrib_left
  right_distrib := inf_symmDiff_distrib_right
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq
  nsmul := letI : Zero L := ⟨⊥⟩; letI : Add L := ⟨(· ∆ ·)⟩; nsmulRec
  zsmul := letI : Zero L := ⟨⊥⟩; letI : Add L := ⟨(· ∆ ·)⟩; letI : Neg L := ⟨id⟩; zsmulRec
  isIdempotentElem := fun a => inf_idem a

theorem booleanRingOfBooleanAlgebra_add (a b : L) :
    (booleanRingOfBooleanAlgebra L).add a b = a ∆ b := rfl

theorem booleanRingOfBooleanAlgebra_mul (a b : L) :
    (booleanRingOfBooleanAlgebra L).mul a b = a ⊓ b := rfl

theorem booleanRingOfBooleanAlgebra_zero : (booleanRingOfBooleanAlgebra L).zero = ⊥ := rfl

theorem booleanRingOfBooleanAlgebra_one : (booleanRingOfBooleanAlgebra L).one = ⊤ := rfl

theorem booleanRingOfBooleanAlgebra_neg (a : L) :
    (booleanRingOfBooleanAlgebra L).neg a = a := rfl

/-- In the ring attached to a Boolean lattice, every element is its own additive inverse. -/
theorem booleanRingOfBooleanAlgebra_add_self (a : L) :
    (booleanRingOfBooleanAlgebra L).add a a = (booleanRingOfBooleanAlgebra L).zero :=
  symmDiff_self a

/-- In the ring attached to a Boolean lattice, multiplication is idempotent. -/
theorem booleanRingOfBooleanAlgebra_mul_self (a : L) :
    (booleanRingOfBooleanAlgebra L).mul a a = a :=
  inf_idem a

/-- In the ring attached to a Boolean lattice, multiplication is commutative. -/
theorem booleanRingOfBooleanAlgebra_mul_comm (a b : L) :
    (booleanRingOfBooleanAlgebra L).mul a b = (booleanRingOfBooleanAlgebra L).mul b a :=
  inf_comm a b

/-- In a Boolean lattice, a complement is unique: two elements with the same meet and join with `a`
coincide.  This is the uniqueness part of the book's definition of a Boolean lattice. -/
theorem compl_eq_of_inf_eq_bot_sup_eq_top {a b : L} (h₁ : a ⊓ b = ⊥) (h₂ : a ⊔ b = ⊤) :
    b = aᶜ := by
  have hb : b = b ⊓ aᶜ := by
    calc b = b ⊓ ⊤ := (inf_top_eq b).symm
      _ = b ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top]
      _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := by rw [inf_sup_left]
      _ = ⊥ ⊔ (b ⊓ aᶜ) := by rw [inf_comm b a, h₁]
      _ = b ⊓ aᶜ := bot_sup_eq _
  have ha : aᶜ = aᶜ ⊓ b := by
    calc aᶜ = aᶜ ⊓ ⊤ := (inf_top_eq aᶜ).symm
      _ = aᶜ ⊓ (a ⊔ b) := by rw [h₂]
      _ = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ b) := by rw [inf_sup_left]
      _ = ⊥ ⊔ (aᶜ ⊓ b) := by rw [inf_comm aᶜ a, inf_compl_eq_bot]
      _ = aᶜ ⊓ b := bot_sup_eq _
  rw [hb, inf_comm, ← ha]

end LatticeToRing

/-! ## (2) A Boolean ring becomes a Boolean lattice -/

section RingToLattice

variable {A : Type u} [BooleanRing A]

/-! ### Auxiliary calculations in a Boolean ring

The identities below are of the form `p = q` for polynomials `p`, `q` in the ring operations;
they are proved by normalising both sides (`ring_nf`) and then using `2x = 0` and `x * x = x`. -/

theorem add_self_add (a b : A) : a + (a + b) = b := by
  rw [← add_assoc, add_self_eq_zero, zero_add]

theorem add_self_right (a b : A) : a + (b + b) = a := by
  rw [add_self_eq_zero, add_zero]

macro "boolean_ring_close" : tactic => `(tactic|
  simp only [pow_two, BooleanRing.mul_self, mul_two, add_self_eq_zero, add_self_add,
    add_self_right, add_comm, add_left_comm, add_assoc, zero_add, add_zero])

/-- The distributivity identity for the join `a ⊔ b = a + b + a * b` and the meet `a ⊓ b = a * b`
of the recovered lattice: `(a ⊔ b) ⊓ (a ⊔ c) = a ⊔ b ⊓ c`. -/
theorem sup_mul_sup (a b c : A) :
    (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) := by
  ring_nf
  boolean_ring_close

/-- **A Boolean ring becomes a Boolean lattice.**  On a Boolean ring `A` take the partial order
`a ≤ b ↔ a * b = a`, meet `a ⊓ b = a * b`, join `a ⊔ b = a + b + a * b`, bottom `0`, top `1` and
complement `aᶜ = 1 + a`.  The verifications, in the form in which the book carries them out, are
the lemmas `divisibility_refl`, `divisibility_trans`, `divisibility_antisymm` (the order),
`mul_le_left`, `mul_le_right`, `le_mul` (meet), `add_add_mul_le_left`, `add_add_mul_le_right`,
`add_add_mul_le` (join), `sup_inf_distrib`, `inf_sup_distrib` (distributivity), `bot_le`, `le_top`
(bounds) and `inf_compl`, `sup_compl`, `compl_unique` (complements) below. -/
@[instance_reducible]
def booleanAlgebraOfBooleanRing (A : Type u) [BooleanRing A] : BooleanAlgebra A where
  sup := fun a b => a + b + a * b
  inf := fun a b => a * b
  le := fun a b => a * b = a
  top := 1
  bot := 0
  compl := fun a => 1 + a
  sdiff := fun a b => a * (1 + b)
  himp := fun a b => b + (1 + a) + b * (1 + a)
  le_refl := fun a => BooleanRing.mul_self a
  le_trans := fun a b c hab hbc => by rw [← hab, mul_assoc, hbc, hab]
  le_antisymm := fun a b hab hba => by rw [← hab, mul_comm_eq, hba]
  le_sup_left := fun a b => by
    show a * (a + b + a * b) = a
    ring_nf
    boolean_ring_close
  le_sup_right := fun a b => by
    show b * (a + b + a * b) = b
    ring_nf
    boolean_ring_close
  sup_le := fun a b c hac hbc => by
    show (a + b + a * b) * c = a + b + a * b
    rw [add_mul, add_mul, hac, hbc, mul_assoc, hbc]
  inf_le_left := fun a b => by
    show a * b * a = a * b
    rw [mul_assoc, mul_comm_eq b a, ← mul_assoc, BooleanRing.mul_self]
  inf_le_right := fun a b => by
    show a * b * b = a * b
    rw [mul_assoc, BooleanRing.mul_self]
  le_inf := fun a b c hab hac => by
    show a * (b * c) = a
    rw [← mul_assoc, hab, hac]
  le_sup_inf := fun x y z => by
    show (x + y + x * y) * (x + z + x * z) * (x + y * z + x * (y * z)) =
      (x + y + x * y) * (x + z + x * z)
    rw [sup_mul_sup, sup_mul_sup, BooleanRing.mul_self]
  inf_compl_le_bot := fun a => by
    show a * (1 + a) * 0 = a * (1 + a)
    rw [mul_zero, mul_add, mul_one, BooleanRing.mul_self, add_self_eq_zero]
  top_le_sup_compl := fun a => by
    show 1 * (a + (1 + a) + a * (1 + a)) = 1
    rw [one_mul, mul_add, mul_one, BooleanRing.mul_self, add_self_right, add_comm 1 a, add_self_add]
  le_top := fun a => by
    show a * 1 = a
    rw [mul_one]
  bot_le := fun a => by
    show 0 * a = 0
    rw [zero_mul]
  sdiff_eq := fun a b => rfl
  himp_eq := fun a b => rfl

theorem booleanAlgebraOfBooleanRing_le (a b : A) :
    (booleanAlgebraOfBooleanRing A).le a b ↔ a * b = a := Iff.rfl

theorem booleanAlgebraOfBooleanRing_sup (a b : A) :
    (booleanAlgebraOfBooleanRing A).sup a b = a + b + a * b := rfl

theorem booleanAlgebraOfBooleanRing_inf (a b : A) :
    (booleanAlgebraOfBooleanRing A).inf a b = a * b := rfl

theorem booleanAlgebraOfBooleanRing_compl (a : A) :
    (booleanAlgebraOfBooleanRing A).compl a = 1 + a := rfl

theorem booleanAlgebraOfBooleanRing_bot : (booleanAlgebraOfBooleanRing A).bot = 0 := rfl

theorem booleanAlgebraOfBooleanRing_top : (booleanAlgebraOfBooleanRing A).top = 1 := rfl

/-! ### The verification of the Boolean lattice axioms, in the form used by the book -/

/-- The relation `a ≤ b ↔ a * b = a` is reflexive. -/
theorem divisibility_refl (a : A) : a * a = a := BooleanRing.mul_self a

/-- The relation `a ≤ b ↔ a * b = a` is transitive. -/
theorem divisibility_trans {a b c : A} (hab : a * b = a) (hbc : b * c = b) : a * c = a := by
  rw [← hab, mul_assoc, hbc, hab]

/-- The relation `a ≤ b ↔ a * b = a` is antisymmetric. -/
theorem divisibility_antisymm {a b : A} (hab : a * b = a) (hba : b * a = b) : a = b := by
  rw [← hab, mul_comm_eq a b, hba]

/-- `a * b` is a lower bound of `a` and `b`. -/
theorem mul_le_left (a b : A) : (a * b) * a = a * b := by
  rw [mul_assoc, mul_comm_eq b a, ← mul_assoc, BooleanRing.mul_self]

theorem mul_le_right (a b : A) : (a * b) * b = a * b := by
  rw [mul_assoc, BooleanRing.mul_self]

/-- `a * b` is the *greatest* lower bound of `a` and `b`. -/
theorem le_mul {a b c : A} (hca : c * a = c) (hcb : c * b = c) : c * (a * b) = c := by
  calc c * (a * b) = c * a * b := (mul_assoc c a b).symm
    _ = c * b := by rw [hca]
    _ = c := hcb

/-- `a + b + a * b` is an upper bound of `a` and `b`. -/
theorem add_add_mul_le_left (a b : A) : a * (a + b + a * b) = a := by
  ring_nf
  boolean_ring_close

theorem add_add_mul_le_right (a b : A) : b * (a + b + a * b) = b := by
  ring_nf
  boolean_ring_close

/-- `a + b + a * b` is the *least* upper bound of `a` and `b`. -/
theorem add_add_mul_le {a b c : A} (hac : a * c = a) (hbc : b * c = b) :
    (a + b + a * b) * c = a + b + a * b := by
  rw [add_mul, add_mul, hac, hbc, mul_assoc, hbc]

/-- The join `a ⊔ b = a + b + a * b` distributes over the meet `a ⊓ b = a * b`. -/
theorem sup_inf_distrib (a b c : A) :
    a + b * c + a * (b * c) = (a + b + a * b) * (a + c + a * c) := (sup_mul_sup a b c).symm

/-- The meet `a ⊓ b = a * b` distributes over the join `a ⊔ b = a + b + a * b`. -/
theorem inf_sup_distrib (a b c : A) : a * (b + c + b * c) = a * b + a * c + (a * b) * (a * c) := by
  ring_nf
  boolean_ring_close

/-- `0` is the least element of the recovered order. -/
theorem bot_le (a : A) : 0 * a = 0 := zero_mul a

/-- `1` is the greatest element of the recovered order. -/
theorem le_top (a : A) : a * 1 = a := mul_one a

/-- `1 + a` is a complement of `a`: the meet is `0`. -/
theorem inf_compl (a : A) : a * (1 + a) = 0 := by
  rw [mul_add, mul_one, BooleanRing.mul_self, add_self_eq_zero]

/-- `1 + a` is a complement of `a`: the join is `1`. -/
theorem sup_compl (a : A) : a + (1 + a) + a * (1 + a) = 1 := by
  rw [inf_compl, add_zero, add_comm 1 a, add_self_add]

/-- In the recovered lattice the complement of `a` is unique: an element whose meet with `a` is
`0` and whose join with `a` is `1` must be `1 + a`.  (This is the book's "if `c` is another
complement, then `ac = 0` and `a + c + ac = 1`, so `c = 1 - a`".) -/
theorem compl_unique {a b : A} (h₁ : a * b = 0) (h₂ : a + b + a * b = 1) : b = 1 + a := by
  have h : a + b = 1 := by
    calc a + b = a + b + 0 := (add_zero _).symm
      _ = a + b + a * b := by rw [h₁]
      _ = 1 := h₂
  have h3 : a + (a + b) = a + 1 := by rw [h]
  rw [← add_assoc, add_self_eq_zero, zero_add] at h3
  rw [h3, add_comm a 1]

end RingToLattice

/-! ## (3) The two constructions are mutually inverse -/

section RoundTripLattice

variable {L : Type u} [BooleanAlgebra L]

/-- Starting from the Boolean lattice `L`, making it a Boolean ring and then a Boolean lattice
again returns the original order: a meet-and-order recovery, as in the book. -/
theorem recovered_le (a b : L) :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).le a b ↔ a ≤ b :=
  inf_eq_left

/-- Starting from the Boolean lattice `L`, the join of the recovered lattice is the original join. -/
theorem recovered_sup (a b : L) :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).sup a b = a ⊔ b := by
  show (booleanRingOfBooleanAlgebra L).add ((booleanRingOfBooleanAlgebra L).add a b)
    ((booleanRingOfBooleanAlgebra L).mul a b) = a ⊔ b
  exact symmDiff_symmDiff_inf a b

/-- Starting from the Boolean lattice `L`, the meet of the recovered lattice is the original meet. -/
theorem recovered_inf (a b : L) :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).inf a b = a ⊓ b := rfl

/-- Starting from the Boolean lattice `L`, the complement of the recovered lattice is the original
complement. -/
theorem recovered_compl (a : L) :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).compl a = aᶜ := by
  show (booleanRingOfBooleanAlgebra L).add (booleanRingOfBooleanAlgebra L).one a = aᶜ
  exact top_symmDiff a

theorem recovered_bot :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).bot = ⊥ := rfl

theorem recovered_top :
    (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).top = ⊤ := rfl

end RoundTripLattice

section RoundTripRing

variable {A : Type u} [BooleanRing A]

/-- Starting from the Boolean ring `A`, making it a Boolean lattice and then a Boolean ring again
returns the original addition: the recovered addition is `a(1-b) + (1-a)b = a + b` (and `1 - b = 1 + b`
in a Boolean ring), the extra meet term of the recovered join being `a * b * (a * b) = 0`. -/
theorem recovered_add (a b : A) :
    (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).add a b
      = a + b := by
  haveI : BooleanAlgebra A := @booleanAlgebraOfBooleanRing A ‹BooleanRing A›
  have hb : b * (1 + b) = 0 := by
    rw [mul_add, mul_one, BooleanRing.mul_self, add_self_eq_zero]
  have h1 : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]
  have h2 : b * (1 + a) = b + a * b := by rw [mul_add, mul_one, mul_comm_eq b a]
  have h3 : a * (1 + b) * (b * (1 + a)) = 0 := by
    calc a * (1 + b) * (b * (1 + a)) = a * (b * (1 + b)) * (1 + a) := by ring
      _ = 0 := by rw [hb, mul_zero, zero_mul]
  show a * (1 + b) + b * (1 + a) + a * (1 + b) * (b * (1 + a)) = a + b
  rw [h3, h1, h2, add_zero, add_assoc, add_comm b (a * b), add_self_add]

/-- Starting from the Boolean ring `A`, the recovered multiplication is unchanged. -/
theorem recovered_mul (a b : A) :
    (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).mul a b
      = a * b := rfl

theorem recovered_zero :
    (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).zero = 0 := rfl

theorem recovered_one :
    (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).one = 1 := rfl

/-- Starting from the Boolean ring `A`, the recovered negation is the original negation. -/
theorem recovered_neg (a : A) :
    (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).neg a
      = -a := by
  show a = -a
  rw [neg_eq_self]

end RoundTripRing

/-! ## (4) Morphisms: Boolean ring homs are Boolean lattice homs

Since both constructions keep the underlying type and the underlying function of a morphism, the
correspondence below says that the two constructions are functorial and mutually inverse on
morphisms as well, i.e. that Boolean rings and Boolean lattices are equivalent as categories. -/

section Morphisms

variable {L L' : Type u} [BooleanAlgebra L] [BooleanAlgebra L']

/-- A map between Boolean lattices is a homomorphism of the attached Boolean rings (preserves
symmetric difference, meet, `⊥` and `⊤`) if and only if it is a homomorphism of Boolean lattices. -/
theorem ringHom_iff_boundedLatticeHom (g : L → L') :
    ((∀ a b : L, g (a ∆ b) = g a ∆ g b) ∧ (∀ a b : L, g (a ⊓ b) = g a ⊓ g b) ∧
        g ⊥ = ⊥ ∧ g ⊤ = ⊤) ↔
      ∃ f : BoundedLatticeHom L L', ⇑f = g := by
  constructor
  · rintro ⟨hadd, hinf, hbot, htop⟩
    refine ⟨{ toFun := g
              map_sup' := fun a b => ?_
              map_inf' := hinf
              map_top' := htop
              map_bot' := hbot }, rfl⟩
    rw [← symmDiff_symmDiff_inf a b, hadd, hadd, hinf]
    exact symmDiff_symmDiff_inf (g a) (g b)
  · rintro ⟨f, rfl⟩
    exact ⟨map_symmDiff' f, fun a b => f.map_inf' a b, f.map_bot', f.map_top'⟩

end Morphisms

/-! ## (4') Packaging the round trips as isomorphisms

`BoolRingOf L` is the carrier of `L` viewed as a Boolean ring and `BoolAlgOf A` is the carrier of
`A` viewed as a Boolean lattice.  These type synonyms let us say that the identity maps are
isomorphisms without ambiguity between the several structures carried by the same type. -/

/-- The carrier of a Boolean lattice, viewed as a Boolean ring. -/
def BoolRingOf (L : Type u) : Type u := L

/-- The carrier of a Boolean ring, viewed as a Boolean lattice. -/
def BoolAlgOf (A : Type u) : Type u := A

instance instBooleanRingBoolRingOf (L : Type u) [BooleanAlgebra L] : BooleanRing (BoolRingOf L) :=
  booleanRingOfBooleanAlgebra L

instance instBooleanAlgebraBoolAlgOf (A : Type u) [BooleanRing A] : BooleanAlgebra (BoolAlgOf A) :=
  booleanAlgebraOfBooleanRing A

/-- The identity equivalence of the carriers, used in `roundTripOrderIso`. -/
def idOrderEquiv (L : Type u) [BooleanAlgebra L] : BoolAlgOf (BoolRingOf L) ≃ L :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- The identity equivalence of the carriers, used in `roundTripRingEquiv`. -/
def idRingEquiv (A : Type u) [BooleanRing A] : BoolRingOf (BoolAlgOf A) ≃ A :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- The identity map is an isomorphism from the Boolean lattice recovered from the Boolean ring
attached to `L` back to the original Boolean lattice `L`. -/
def roundTripOrderIso (L : Type u) [BooleanAlgebra L] : BoolAlgOf (BoolRingOf L) ≃o L where
  toEquiv := idOrderEquiv L
  map_rel_iff' := by
    intro a b
    exact (recovered_le (L := L) a b).symm

/-- The identity map is an isomorphism from the Boolean ring recovered from the Boolean lattice
attached to `A` back to the original Boolean ring `A`. -/
def roundTripRingEquiv (A : Type u) [BooleanRing A] : BoolRingOf (BoolAlgOf A) ≃+* A where
  toEquiv := idRingEquiv A
  map_mul' := by
    intro a b
    exact recovered_mul (A := A) a b
  map_add' := by
    intro a b
    exact recovered_add (A := A) a b

/-! ## (5) The exercise -/

/-- **Atiyah–Macdonald, Chapter 1, Exercise 24.**  Every Boolean lattice becomes a Boolean ring
(addition = symmetric difference, multiplication = meet, `0 = ⊥`, `1 = ⊤`, `-a = a`), every Boolean
ring becomes a Boolean lattice (order `a ≤ b ↔ a * b = a`, meet = multiplication, join
`a ⊔ b = a + b + a * b`, `0` and `1` the ring's, complement `1 + a`, with a unique complement), the
two constructions are mutually inverse on the nose (identity maps on carriers), and the two notions
have the same morphisms; hence Boolean lattices and Boolean rings are equivalent. -/
theorem solution :
    (∀ (L : Type u) [BooleanAlgebra L] (a b : L),
      (booleanRingOfBooleanAlgebra L).add a b = a ∆ b ∧
      (booleanRingOfBooleanAlgebra L).mul a b = a ⊓ b ∧
      (booleanRingOfBooleanAlgebra L).zero = ⊥ ∧
      (booleanRingOfBooleanAlgebra L).one = ⊤ ∧
      (booleanRingOfBooleanAlgebra L).neg a = a ∧
      (booleanRingOfBooleanAlgebra L).add a a = (booleanRingOfBooleanAlgebra L).zero ∧
      (booleanRingOfBooleanAlgebra L).mul a a = a) ∧
    (∀ (A : Type u) [BooleanRing A] (a b : A),
      ((booleanAlgebraOfBooleanRing A).le a b ↔ a * b = a) ∧
      (booleanAlgebraOfBooleanRing A).sup a b = a + b + a * b ∧
      (booleanAlgebraOfBooleanRing A).inf a b = a * b ∧
      (booleanAlgebraOfBooleanRing A).compl a = 1 + a ∧
      (booleanAlgebraOfBooleanRing A).bot = 0 ∧
      (booleanAlgebraOfBooleanRing A).top = 1 ∧
      (a * b = 0 → a + b + a * b = 1 → b = 1 + a)) ∧
    (∀ (L : Type u) [BooleanAlgebra L] (a b : L),
      ((@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).le a b ↔ a ≤ b) ∧
      (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).sup a b = a ⊔ b ∧
      (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).inf a b = a ⊓ b ∧
      (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).compl a = aᶜ ∧
      (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).bot = ⊥ ∧
      (@booleanAlgebraOfBooleanRing L (booleanRingOfBooleanAlgebra L)).top = ⊤) ∧
    (∀ (A : Type u) [BooleanRing A] (a b : A),
      (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).add a b
        = a + b ∧
      (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).mul a b
        = a * b ∧
      (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).zero = 0 ∧
      (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).one = 1 ∧
      (@booleanRingOfBooleanAlgebra A (@booleanAlgebraOfBooleanRing A ‹BooleanRing A›)).neg a
        = -a) ∧
    (∀ (L : Type u) [BooleanAlgebra L], ⇑(roundTripOrderIso L) = (id : L → L)) ∧
    (∀ (A : Type u) [BooleanRing A], ⇑(roundTripRingEquiv A) = (id : A → A)) ∧
    (∀ (L L' : Type u) [BooleanAlgebra L] [BooleanAlgebra L'] (g : L → L'),
      (((∀ a b : L, g (a ∆ b) = g a ∆ g b) ∧ (∀ a b : L, g (a ⊓ b) = g a ⊓ g b) ∧
          g ⊥ = ⊥ ∧ g ⊤ = ⊤) ↔
        ∃ f : BoundedLatticeHom L L', ⇑f = g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L _ a b
    exact ⟨booleanRingOfBooleanAlgebra_add a b, booleanRingOfBooleanAlgebra_mul a b,
      booleanRingOfBooleanAlgebra_zero, booleanRingOfBooleanAlgebra_one,
      booleanRingOfBooleanAlgebra_neg a, booleanRingOfBooleanAlgebra_add_self a,
      booleanRingOfBooleanAlgebra_mul_self a⟩
  · intro A _ a b
    exact ⟨booleanAlgebraOfBooleanRing_le a b, booleanAlgebraOfBooleanRing_sup a b,
      booleanAlgebraOfBooleanRing_inf a b, booleanAlgebraOfBooleanRing_compl a,
      booleanAlgebraOfBooleanRing_bot, booleanAlgebraOfBooleanRing_top,
      fun h₁ h₂ => compl_unique h₁ h₂⟩
  · intro L _ a b
    exact ⟨recovered_le a b, recovered_sup a b, recovered_inf a b, recovered_compl a,
      recovered_bot, recovered_top⟩
  · intro A _ a b
    exact ⟨recovered_add a b, recovered_mul a b, recovered_zero, recovered_one, recovered_neg a⟩
  · intro L _
    rfl
  · intro A _
    rfl
  · intro L L' _ _ g
    exact ringHom_iff_boundedLatticeHom g

end AtiyahMcdonald69.Ex_1_24
