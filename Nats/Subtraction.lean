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

-- i really don't that zero has a defined predecessor :(
def pred : nat -> nat
| 0      => 0
| succ k => k

axiom pred_inj (a b : nat) : pred a = pred b -> a = b

def pred' (n : nat) {h : n ≠ 0} : nat := by
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

theorem pred_zero : pred 0 = 0 := by
  rfl

theorem pred_succ {n : nat} : pred (succ n) = n := by
  rfl

theorem add_pred (a b : nat) {h : b ≠ 0} : a + pred b = pred (a + b) := by
  cases b with
  | zero =>
    contradiction
  | succ d =>
    rw [pred_succ, add_succ, pred_succ]

theorem pred_inj_iff (a b : nat) : pred a = pred b ↔ a = b := by
  have p : a = b -> pred a = pred b := by
    intro ha
    rw [ha]
  exact ⟨pred_inj a b, p⟩

-- ∀ a b, a < b -> a - b = 0 :(
def sub (a b : nat) : nat := by
  cases b with
  | zero =>
    exact a
  | succ k =>
    exact sub (pred a) k

instance : Sub nat where
  sub := Subtraction.sub

