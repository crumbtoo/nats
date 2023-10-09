import Mathlib.Data.Nat.Fib
--------------------------------------------------------------------------------
namespace Fib
--------------------------------------------------------------------------------

section

open Nat

example (n : ℕ) {h : n >= 2} : fib n = fib (n-2) + fib (n-1) := by
  induction n with
  | zero =>
    contradiction
  | succ k ih =>
    cases k with
    | zero =>
      contradiction
    | succ d =>
      rw [succ_eq_add_one, fib_add_one]
      simp
      rw [<- succ_eq_add_one d]
      exact succ_ne_zero _
end
