import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
--------------------------------------------------------------------------------
open CommGroup
--------------------------------------------------------------------------------

theorem prod_npow [CommGroup G] (a b : G) (n : ℕ): (a*b)^n = a^n * b^n := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    repeat rw [pow_succ]
    rw [ih]
    conv =>
      rhs
      rw [mul_left_comm, <- mul_assoc, <- mul_assoc, mul_comm b a]
    rw [<- mul_assoc]

