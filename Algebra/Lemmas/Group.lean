import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Contrapose
--------------------------------------------------------------------------------
open CommGroup
namespace MaddyGroupLemmas
--------------------------------------------------------------------------------

theorem prod_npow [CommGroup G] (a b : G) (n : ℕ) : (a*b)^n = a^n * b^n := by
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

theorem mul_left_cancel [Group G] (t a b : G) : t*a = t*b -> a = b := by
  intro h
  rw [<- one_mul a, <- one_mul b]
  rw [<- mul_left_inv t, mul_assoc, h]
  simp

theorem mul_right_cancel [Group G] (t a b : G) : a*t = b*t -> a = b := by
  intro h
  rw [<- mul_one a, <- mul_one b]
  rw [<- mul_right_inv t, <- mul_assoc, h, mul_assoc]

def PowDistributes [Monoid G] (a b : G) (n : ℕ) := (a*b)^n = a^n * b^n

theorem pow_distrib_three_conseq_is_comm
        [Group G]
        : (∀ (a b : G) (n : ({100, 101, 102} : Finset ℕ)),
          (a*b)^↑↑n = a^↑↑n * b^↑↑n)
        -> ∀ x y : G, x*y = y*x
        := by
  intro h x y
  apply mul_right_cancel (x^100)
  have known : 100 + 1 = 101 := by rfl
  conv => rhs; rw [mul_assoc, <- pow_succ, known]
  apply mul_right_cancel (y^100)
  conv => rhs; lhs; rw [pow_succ]
  conv => rhs; rw [mul_assoc]; rhs; rw [mul_assoc, <- h x y ⟨100, by simp⟩]
  simp
  conv => lhs; rw [mul_assoc, <- h x y ⟨100, by simp⟩]
  simp
  sorry

