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
open Order
namespace Subtraction
--------------------------------------------------------------------------------

def pred (n : nat) {h : n = succ k} : nat := by
  cases n with
  | zero =>
    contradiction
  | succ d =>
    exact d

theorem nz_has_pred {n : nat} : n ≠ 0 ↔ ∃ p, succ p = n := by
  have p : (∃ p, succ p = n) -> n ≠ 0 := by
    intro ha
    cases ha with
    | intro w eh =>
      cases w with
      | zero =>
        rw [<- eh]
        simp
      | succ d =>
        rw [<- eh]
        exact succ_ne_zero _
  exact ⟨nz_is_succ n, p⟩ 

theorem pred_inv_succ (n : nat) : pred (succ n) (n) = n := by
  sorry

def sub (a b : nat) {h : b ≤ a} : nat := by
  cases b with
  -- a - 0
  | zero =>
    exact a
  -- a - succ k
  | succ k =>
    have p : k ≤ pred a := by
      sorry
    exact @sub (pred a) k p

