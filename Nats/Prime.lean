import Nats.Basic
import Nats.Division
import Mathlib.Tactic.Contrapose
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Division
namespace Prime
--------------------------------------------------------------------------------

def is_prime (n : nat) := ¬ ∃ k, k ≠ 1 ∧ k ≠ n ∧ n ∣ k

example : is_prime 2 := by
  intro h
  sorry

