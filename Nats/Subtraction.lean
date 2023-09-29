import Nats.Basic
import Nats.Addition
import Nats.Order
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Std.Tactic.Basic
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Addition
namespace Subtraction
--------------------------------------------------------------------------------

def pred (n : nat) {h : n ≠ 0} : nat := by
  cases n with
  | zero =>
    rw [zero_is_0] at h
    contradiction
  | succ d =>
    exact d

theorem nz_has_pred {n : nat} : n ≠ 0 ↔ ∃ p, succ p = n := by
  sorry

