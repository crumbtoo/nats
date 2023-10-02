import Nats.Basic
import Nats.Addition
import Nats.Multiplication
import Nats.Subtraction
import Nats.Parity
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Addition
open Subtraction
open Parity
open Multiplication
namespace Division
--------------------------------------------------------------------------------

def dvd (a n : nat) := ∃ b, a*b = n

