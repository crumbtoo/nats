import Nats.Basic
import Nats.Multiplication
import Nats.Parity
import Nats.Order
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Parity
open Order
open Multiplication
namespace Division
--------------------------------------------------------------------------------

def dvd (n a : nat) := ∃ b, a*b = n

instance : Dvd nat where
  dvd := Division.dvd

theorem even_dvd_two {a : nat} : is_even a -> a ∣ 2 := by
  intro ha
  cases ha with
  | intro w eh =>
    use w
    rw [two_mul]
    exact eh

theorem le_not_dvd (a b : nat) : a < b -> ¬ a ∣ b := by
  intro ha
  induction b with
  | zero =>
    exfalso
    exact lt_zero ha
  | succ d ih =>
    intro hb
    cases hb with
    | intro w eh =>
      rw [succ_mul] at eh
      sorry

