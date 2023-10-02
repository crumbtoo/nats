import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
--------------------------------------------------------------------------------
open Nat
namespace TriangleNumbers
--------------------------------------------------------------------------------

def T : Nat -> Nat
| 0      => 0
| succ n => succ n + T n

--------------------------------------------------------------------------------

lemma t_zero : T 0 = 0 := by
  rfl

lemma t_succ (n : Nat) : T (succ n) = succ n + T n := by
  rfl

theorem t_eq_polynomial (n : Nat) : T n = (n^2 + n) / 2 := by
  induction n with
  | zero =>
    simp
  | succ d ih =>
    rw [t_succ, ih]
    sorry

