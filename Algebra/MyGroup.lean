import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Use
import Std.Tactic.Basic
--------------------------------------------------------------------------------
namespace MyGroup
--------------------------------------------------------------------------------
class MyMonoid (M : Type u) extends MulOneClass M where
  mul_assoc : ∀ (a b c : M), (a * b) * c = a * (b * c)
  npow : ℕ -> M -> M
  npow_zero' : ∀ (m : M), npow 0 m = 1
  npow_succ' : ∀ (m : M) (n : ℕ), npow (n+1) m = m * npow n m

open MyMonoid

instance [MyMonoid M] : OfNat M 1 where
  ofNat := One.one

@[default_instance]
instance [MyMonoid M] : Pow M ℕ where
  pow m n := npow n m

/- variable {M : Type*} [Monoid M] -/

theorem npow_eq_pow [MyMonoid M] (n : ℕ) (m : M) : npow n m = m^n := by rfl

theorem npow_zero [MyMonoid M] (m : M) : m^0 = 1 := by
  rw [<- npow_eq_pow, npow_zero']

theorem npow_succ [MyMonoid M] (m : M) (n : ℕ) : m^(n+1) = m * m^n := by
  rw [<- npow_eq_pow, <- npow_eq_pow, npow_succ']

theorem npow_one [MyMonoid M] (m : M) : m^1 = m := by
  rw [npow_succ, npow_zero, mul_one]

theorem npow_mul [MyMonoid M] (m : M) (n : ℕ) : m^n * m = m^(n+1) := by
  induction n with
  | zero =>
    rw [npow_zero, one_mul, Nat.zero_add, npow_one]
  | succ k ih =>
    rw [npow_succ, npow_succ, mul_assoc, ih]

theorem npow_add [MyMonoid M] (m : M) (n k : ℕ) : m^n * m^k = m^(n+k) := by
  sorry

theorem npow_comm [MyMonoid M] (m : M) (n k : ℕ) : m^n * m^k = m^k * m^n := by
  induction n generalizing k with
  | zero =>
    rw [npow_zero, one_mul, mul_one]
  | succ d ih =>
    conv => lhs; rw [npow_succ]
    conv => rhs; rw [<- npow_mul]
    rw [<- mul_assoc, mul_assoc, ih, <- mul_assoc]
    rw [<- npow_succ, <- npow_mul, mul_assoc, <- npow_succ, <- npow_mul]
    rw [<- mul_assoc]

theorem mul_npow_comm [MyMonoid M] (m : M) (n : ℕ) : m * m^k = m^k * m := by
  conv =>
    pattern m^k*m
    rhs
    rw [<- npow_one m]
  conv =>
    pattern m*m^k
    lhs
    rw [<- npow_one m]
  exact npow_comm m 1 k

--------------------------------------------------------------------------------

class MyGroup (G : Type u) extends MyMonoid G, Inv G, Div G where
  mul_inv : ∀ (a : G), a * a⁻¹ = 1
  div_eq_mul_inv : ∀ (a b : G), a / b = a * b⁻¹

open MyGroup

theorem inv_one [MyGroup G] : (1 : G)⁻¹ = 1 := by
  /- rw [inv_eq_recip, div_eq_mul_inv] -/
  conv =>
    rhs
    rw [<- mul_inv 1]
  rw [one_mul]

theorem div_one [MyGroup G] (a : G) : a / 1 = a := by
  rw [div_eq_mul_inv, inv_one, mul_one]

theorem inv_inv [MyGroup G] : ∀ (a : G), a⁻¹⁻¹ = a := by
  intro a
  rw [<- one_mul a⁻¹⁻¹, <- mul_inv a, mul_assoc, mul_inv, mul_one]

-- redo this later lol
theorem inv_mul [MyGroup G] (a : G) : a⁻¹ * a = 1 := by
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

theorem inv_eq_recip [MyGroup G] (a : G) : a⁻¹ = 1 / a := by
  rw [<- one_mul a⁻¹]
  apply Eq.symm
  exact MyGroup.div_eq_mul_inv 1 a

theorem mul_div_assoc [MyGroup G] (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, <- mul_assoc, <- div_eq_mul_inv]

theorem div_self [MyGroup G] (a : G) : a/a = 1 := by
  rw [div_eq_mul_inv]
  exact mul_inv _

theorem mul_div [MyGroup G] (a b c : G) : a*(b/c) = (a*b)/c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

theorem inv_product [MyGroup G] (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ := by
  have i := by
    have j : a*b*b⁻¹*a⁻¹ = a*a⁻¹ := by
      conv => lhs; lhs; rw [mul_assoc, mul_inv, mul_one]
    calc
      a*b*(b⁻¹*a⁻¹) = a*b*b⁻¹*a⁻¹     := by rw [<- mul_assoc]
      _             = a*a⁻¹           := j
      _             = 1               := by rw [mul_inv]

  apply mul_left_cancel (a*b)
  rw [i, <- mul_inv (a*b)]

theorem div_mul_div [MyGroup G] (a b c d : G)
                    : (a/b) * (c/d) = (a*c)/(b*d)
                    := by
  apply mul_right_cancel ((a*c)/(b*d))⁻¹
  rw [mul_inv]
  sorry

/- theorem inv_div [MyGroup G] (a b : G) : (a / b)⁻¹ = b / a := by -/
/-   rw [<- one_mul (a/b)⁻¹, ] -/

theorem div_div [MyGroup G] (a b c : G) : a / (b / c) = a*c / b := by
  sorry

example [MyGroup G] : ¬ ∀ (a : G), a * a = 1 -> a = 1 := by
  intro h
  have a := Classical.arbitrary G
  specialize h a
  sorry

theorem own_inv [MyGroup G] {a : G} : a*a = 1 -> a⁻¹ = a := by
  intro h
  apply mul_left_cancel a
  rw [h]
  exact mul_inv _

example [MyGroup G] (a : G) : a*a = 1 -> ∀ b, a*b = b*a := by
  intro h b
  rw [<- one_mul (a*b), <- mul_one (b*a)]
  sorry

example [MyGroup G] : ∀ a : G, a*a = 1 -> a = 1 := by
  intro a h
  have inv_a : a = a⁻¹ := calc
    a = a             := by rfl
    _ = a * (a * a⁻¹) := by rw [mul_inv, mul_one]
    _ = a * a * a⁻¹   := by rw [mul_assoc]
    _ = a⁻¹           := by rw [h, one_mul]
  calc
    a = 1 * a           := by rw [one_mul]
    _ = a⁻¹ * a * a     := by rw [<- inv_mul a]
    _ = a⁻¹ * a         := sorry
    _ = 1               := sorry

example [MyGroup G] [Nonempty G]
        : (∀ (a : G), ∃ (b : G), a * b = 1)
        -> ∃ (f : G -> G), ∀ n, n * f n = 1
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

