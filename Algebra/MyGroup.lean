import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Use
import Std.Tactic.Basic
--------------------------------------------------------------------------------
namespace MyGroup
--------------------------------------------------------------------------------
class MyMonoid (M : Type u) extends Semigroup M, MulOneClass M where
  /- mul_assoc : ∀ (a b c : M), (a * b) * c = a * (b * c) -/
  npow : ℕ -> M -> M
  npow_zero' : ∀ (m : M), npow 0 m = 1
  npow_succ' : ∀ (m : M) (n : ℕ), npow (n+1) m = m * npow n m

open MyMonoid

instance [MyMonoid M] : OfNat M 1 where
  ofNat := One.one

@[default_instance]
instance [MyMonoid M] : Pow M ℕ where
  pow m n := npow n m

variable {M : Type*} [MyMonoid M]

theorem npow_eq_pow (n : ℕ) (m : M) : npow n m = m^n := by rfl

theorem npow_zero (m : M) : m^0 = 1 := by
  rw [<- npow_eq_pow, npow_zero']

theorem npow_succ (m : M) (n : ℕ) : m^(n+1) = m * m^n := by
  rw [<- npow_eq_pow, <- npow_eq_pow, npow_succ']

theorem npow_one (m : M) : m^1 = m := by
  rw [npow_succ, npow_zero, mul_one]

theorem npow_mul (m : M) (n : ℕ) : m^n * m = m^(n+1) := by
  induction n with
  | zero =>
    rw [npow_zero, one_mul, Nat.zero_add, npow_one]
  | succ k ih =>
    rw [npow_succ, npow_succ, mul_assoc, ih]

theorem npow_comm (m : M) (n k : ℕ) : m^n * m^k = m^k * m^n := by
  induction n with
  | zero =>
    rw [npow_zero, one_mul, mul_one]
  | succ d ih =>
    conv => lhs; rw [npow_succ]
    conv => rhs; rw [<- npow_mul]
    rw [<- mul_assoc, mul_assoc, ih, <- mul_assoc]
    rw [<- npow_succ, <- npow_mul, mul_assoc, <- npow_succ, <- npow_mul]
    rw [<- mul_assoc]

theorem mul_npow_comm (m : M) (n : ℕ) : m * m^k = m^k * m := by
  conv =>
    pattern m^k*m
    rhs
    rw [<- npow_one m]
  conv =>
    pattern m*m^k
    lhs
    rw [<- npow_one m]
  exact npow_comm m 1 k

theorem npow_add (m : M) (n k : ℕ) : m^n * m^k = m^(n+k) := by
  induction k with
  | zero =>
    rw [npow_zero, Nat.add_zero, mul_one]
  | succ d ih =>
    rw [Nat.add_succ, npow_succ m (n+d), npow_succ, <- mul_assoc]
    rw [<- mul_npow_comm m n, mul_assoc, ih]

--------------------------------------------------------------------------------

class MyGroup (G : Type u) extends MyMonoid G, Inv G, Div G where
  mul_inv : ∀ (a : G), a * a⁻¹ = 1
  div_eq_mul_inv : ∀ (a b : G), a / b = a * b⁻¹

open MyGroup

@[default_instance]
instance [MyGroup G] : Pow G ℕ where
  pow m n := npow n m

instance [MyGroup G] : Pow G (Finset ℕ) where
  pow m n := npow n m

variable {G : Type*} [MyGroup G]

theorem inv_one : (1 : G)⁻¹ = 1 := by
  /- rw [inv_eq_recip, div_eq_mul_inv] -/
  conv =>
    rhs
    rw [<- mul_inv 1]
  rw [one_mul]

theorem div_one (a : G) : a / 1 = a := by
  rw [div_eq_mul_inv, inv_one, mul_one]

theorem inv_inv : ∀ (a : G), a⁻¹⁻¹ = a := by
  intro a
  rw [<- one_mul a⁻¹⁻¹, <- mul_inv a, mul_assoc, mul_inv, mul_one]

-- redo this later lol
theorem inv_mul (a : G) : a⁻¹ * a = 1 := by
  rw [<- mul_one a⁻¹]
  conv =>
    lhs
    rw [<- mul_inv a⁻¹⁻¹]
    rhs
    rw [<- mul_one a, <- mul_inv a⁻¹, <- mul_assoc, mul_inv, one_mul]
  rw [mul_inv, mul_one, mul_inv]

theorem inv_comm (a : G) : a * a⁻¹ = a⁻¹ * a := by
  rw [mul_inv, inv_mul]

theorem mul_left_cancel (t a b : G) : t*a = t*b -> a = b := by
  intro h
  rw [<- one_mul a, <- one_mul b]
  rw [<- mul_inv t]
  rw [inv_comm, mul_assoc, mul_assoc, h]

theorem mul_right_cancel (t a b : G) : a*t = b*t -> a = b := by
  intro h
  rw [<- mul_one a, <- mul_one b]
  rw [<- mul_inv t]
  rw [<- mul_assoc, <- mul_assoc]
  rw [h]

theorem inv_eq_recip (a : G) : a⁻¹ = 1 / a := by
  rw [<- one_mul a⁻¹]
  apply Eq.symm
  exact MyGroup.div_eq_mul_inv 1 a

theorem mul_div_assoc (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, <- mul_assoc, <- div_eq_mul_inv]

theorem div_self (a : G) : a/a = 1 := by
  rw [div_eq_mul_inv]
  exact mul_inv _

theorem mul_div (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

theorem inv_product (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ := by
  have i := by
    have j : a*b*b⁻¹*a⁻¹ = a*a⁻¹ := by
      conv => lhs; lhs; rw [mul_assoc, mul_inv, mul_one]
    calc
      a*b*(b⁻¹*a⁻¹) = a*b*b⁻¹*a⁻¹     := by rw [<- mul_assoc]
      _             = a*a⁻¹           := j
      _             = 1               := by rw [mul_inv]

  apply mul_left_cancel (a*b)
  rw [i, <- mul_inv (a*b)]

theorem inv_div (a b : G) : (a / b)⁻¹ = b / a := by
  repeat rw [div_eq_mul_inv]
  rw [inv_product, inv_inv]

theorem div_mul_div (a b c d : G)
                    : (a/b) * (c/d) = (a*c)/(b*d)
                    := by
  apply mul_right_cancel ((a*c)/(b*d))⁻¹
  rw [mul_inv]
  sorry

theorem div_div (a b c : G) : a / (b / c) = a*c / b := by
  sorry

example : ¬ ∀ (a : G), a * a = 1 -> a = 1 := by
  intro h
  have a := Classical.arbitrary G
  specialize h a
  sorry

theorem own_inv (a : G) : a*a = 1 -> a⁻¹ = a := by
  intro h
  apply mul_left_cancel a
  rw [h]
  exact mul_inv _

example (a : G) : a*a = 1 -> ∀ b, a*b = b*a := by
  intro h b
  rw [<- one_mul (a*b), <- mul_one (b*a)]
  sorry

