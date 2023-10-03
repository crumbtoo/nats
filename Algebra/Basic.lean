import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Use
import Std.Tactic.Basic
namespace Basic
--------------------------------------------------------------------------------
class MyMonoid (M : Type u) extends Mul M where
  mul_assoc : ∀ (a b c : M), (a * b) * c = a * (b * c)
  one : M
  mul_one : ∀ (a : M), a * one = a
  one_mul : ∀ (a : M), one * a = a

open MyMonoid

class MyGroup (G : Type u) extends MyMonoid G, Inv G, Div G where
  mul_inv : ∀ (a : G), a * a⁻¹ = one
  div_eq_mul_inv : ∀ (a b : G), a / b = a * b⁻¹

open MyGroup

theorem inv_one [MyGroup G] : (one : G)⁻¹ = one := by
  /- rw [inv_eq_recip, div_eq_mul_inv] -/
  conv =>
    rhs
    rw [<- mul_inv one]
  rw [one_mul]

theorem mul_left_cancel [MyGroup G] (t a b : G) : t*a = t*b -> a = b := by
  intro h
  rw [<- one_mul a, <- one_mul b]
  rw [<- mul_inv t]
  sorry

theorem mul_right_cancel [MyGroup G] (t a b : G) : a*t = b*t -> a = b := by
  intro h
  rw [<- mul_one a, <- mul_one b]
  rw [<- mul_inv t]
  rw [<- mul_assoc, <- mul_assoc]
  rw [h]

theorem inv_mul [MyGroup G] (a : G) : a⁻¹ * a = one := by
  sorry

theorem inv_inv [MyGroup G] : ∀ (a : G), a⁻¹⁻¹ = a := by
  intro a
  apply mul_left_cancel a⁻¹
  rw [inv_mul, mul_inv]

example [MyGroup G] : ∀ (a : G), ∃ (b : G), a * b = one := by
  intro a
  use a⁻¹
  exact mul_inv a

theorem inv_eq_recip [MyGroup G] (a : G) : a⁻¹ = one / a := by
  rw [<- one_mul a⁻¹]
  apply Eq.symm
  exact MyGroup.div_eq_mul_inv one a

theorem mul_div_assoc [MyGroup G] (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, <- mul_assoc, <- div_eq_mul_inv]

theorem div_self [MyGroup G] (a : G) : a/a = one := by
  rw [div_eq_mul_inv]
  exact mul_inv _

theorem mul_both [MyGroup G] (t : G) {a b : G} (h : a = b) : t*a = t*b := by
  rw [h]

theorem inv_div [MyGroup G] (a b : G) : (a / b)⁻¹ = b / a := by
  rw [inv_eq_recip]
  sorry

theorem div_div [MyGroup G] (a b c : G) : a / (b / c) = a*c / b := by
  sorry

example [MyGroup G] [Nonempty G]
        : (∀ (a : G), ∃ (b : G), a * b = one)
        -> ∃ (f : G -> G), ∀ n, n * f n = one
        := by
  intro h
  /- have f := Classical.arbitrary (G -> G) -/
  /- use f -/
  have a := Classical.arbitrary G
  cases h a with
  | intro w eh =>
    have f : G -> G := by
      intro _
      exact w
    have i (x : G) : f x = w := sorry
    use f
    intro n
    rw [i]
    sorry

