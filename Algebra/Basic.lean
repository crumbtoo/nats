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

theorem div_one [MyGroup G] (a : G) : a / one = a := by
  rw [div_eq_mul_inv, inv_one, mul_one]

theorem inv_inv [MyGroup G] : ∀ (a : G), a⁻¹⁻¹ = a := by
  intro a
  rw [<- one_mul a⁻¹⁻¹, <- mul_inv a, mul_assoc, mul_inv, mul_one]

-- redo this later lol
theorem inv_mul [MyGroup G] (a : G) : a⁻¹ * a = one := by
  rw [<- mul_one a⁻¹]
  conv =>
    lhs
    rw [<- mul_inv a⁻¹⁻¹]
    rhs
    rw [<- mul_one a, <- mul_inv a⁻¹, <- mul_assoc, mul_inv, one_mul]
  rw [mul_inv, mul_one, mul_inv]

theorem inv_comm [MyGroup G] (a : G) : a * a⁻¹ = a⁻¹ * a := by
  rw [mul_inv, inv_mul]

theorem mul_left_cancel [MyGroup G] (t a b : G) : t*a = t*b -> a = b := by
  intro h
  rw [<- one_mul a, <- one_mul b]
  rw [<- mul_inv t]
  rw [inv_comm, mul_assoc, mul_assoc, h]

theorem mul_right_cancel [MyGroup G] (t a b : G) : a*t = b*t -> a = b := by
  intro h
  rw [<- mul_one a, <- mul_one b]
  rw [<- mul_inv t]
  rw [<- mul_assoc, <- mul_assoc]
  rw [h]

theorem inv_eq_recip [MyGroup G] (a : G) : a⁻¹ = one / a := by
  rw [<- one_mul a⁻¹]
  apply Eq.symm
  exact MyGroup.div_eq_mul_inv one a

theorem mul_div_assoc [MyGroup G] (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, <- mul_assoc, <- div_eq_mul_inv]

theorem div_self [MyGroup G] (a : G) : a/a = one := by
  rw [div_eq_mul_inv]
  exact mul_inv _

theorem mul_div [MyGroup G] (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

theorem div_cancel [MyGroup G] (a b c : G) : (a*b)/c = (a/c)*(b/c) := by
  repeat rw [div_eq_mul_inv]
  sorry

theorem inv_product [MyGroup G] (a b : G) : (a*b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply mul_left_cancel (a*b)
  rw [mul_inv]
  sorry

theorem div_mul_div [MyGroup G] (a b c d : G)
                    : (a/b) * (c/d) = (a*c)/(b*d)
                    := by
  apply mul_right_cancel ((a*c)/(b*d))⁻¹
  rw [mul_inv]
  conv =>
    lhs




/- theorem inv_div [MyGroup G] (a b : G) : (a / b)⁻¹ = b / a := by -/
/-   rw [<- one_mul (a/b)⁻¹, ] -/

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

