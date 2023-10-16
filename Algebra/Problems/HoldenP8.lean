import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
--------------------------------------------------------------------------------

def f : ℝ -> ℝ := λ x => x+1
def g : ℝ -> ℝ := λ x => 2*x

def f' : ℝ -> ℝ := λ x => x-1
noncomputable def g' : ℝ -> ℝ := λ x => x/2

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

def S : Type := ({ f, f', g, g' } : Set (ℝ -> ℝ))

inductive BS where
| atom    : S -> BS
| comp    : BS -> BS -> BS

