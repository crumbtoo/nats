import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.PresentedGroup
--------------------------------------------------------------------------------
namespace HoldenP8
--------------------------------------------------------------------------------

def f : ℝ -> ℝ := λ x => x+1
def g : ℝ -> ℝ := λ x => 2*x

def f' : ℝ -> ℝ := λ x => x-1
noncomputable def g' : ℝ -> ℝ := λ x => x/2

theorem f_def : f x = x+1 := by rfl
theorem f'_def : f' x = x-1 := by rfl
theorem g_def : g x = 2*x := by rfl
theorem g'_def : g' x = x/2 := by rfl

theorem iter_f : f^[n] = (λ (x : ℝ) => x+n) := by
  induction n with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [Function.iterate_succ', Nat.cast_succ, ih]
    conv =>
      rhs
      intro x
      rw [<- add_assoc]

theorem iter_f' : f'^[n] = (λ (x : ℝ) => x-n) := by
  induction n with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [Function.iterate_succ, Nat.cast_succ, ih]
    conv => rhs; intro x; rw [sub_add_eq_sub_sub_swap]

theorem iter_g : g^[n] = (λ (x : ℝ) => 2^n*x) := by
  induction n with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [Function.iterate_succ', pow_succ, ih]
    have i : g = λx => 2*x := by rfl
    rw [i, Function.comp_def]
    conv =>
      lhs
      intro
      rw [<- mul_assoc]

theorem iter_g' : g'^[n] = (λ (x : ℝ) => x/2^n) := by
  induction n with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [Function.iterate_succ, pow_succ, ih]
    conv =>
      rhs; intro x; rw [div_mul_eq_div_div]

theorem comp_fg (n m : ℕ) : f^[n] ∘ g^[m] = λ (x : ℝ) => 2^m*x+n := by
  rw [iter_f, iter_g, Function.comp_def]

theorem comp_gf (n m : ℕ) : g^[m] ∘ f^[n] = λ (x : ℝ) => 2^m*(x+n) := by
  rw [iter_f, iter_g, Function.comp_def]

--------------------------------------------------------------------------------

example : g' ∘ f^[3] ∘ g = (λ (x : ℝ) => x + 3/2) := by
  rw [<- Function.iterate_one g', <- Function.iterate_one g]
  rw [comp_fg]
  simp
  rw [Function.comp_def]
  conv =>
    lhs
    intro x
    rw [g'_def, add_div, mul_comm, div_eq_mul_inv]
    simp

--------------------------------------------------------------------------------

def S : Type := ({ f, f', g, g', id } : Set (ℝ -> ℝ))

def BS : Type := @PresentedGroup S ∅

/- inductive BS where -/
/- | atom    : S -> BS -/
/- | comp    : BS -> BS -> BS -/

/- def npow : BS -> ℕ -> BS -/
/- | _, Nat.zero      => BS.atom ⟨id, by simp⟩ -/ 
/- | a, Nat.succ n    => BS.comp a (pow a n) -/

/- instance : Pow BS ℕ where -/
/-   pow := npow -/

/- def inv : BS -> BS := by -/
/-   intro a -/
/-   cases a with -/
/-   | atom af => -/
/-     cases af with -/
/-     | mk v p => -/
/-       sorry -/
/-   | comp g h => -/
/-     sorry -/

/- def zpow : BS -> ℤ -> BS -/
/- | a, Int.ofNat n    => a^n -/
/- | a, Int.negSucc n  => zpow a⁻¹ (-n) -/

/- instance : Pow BS ℤ where -/
/-   pow := zpow -/

