import Nats.Basic
import Nats.Multiplication
namespace TriangleNumbers
open nat
open nat.nat
--------------------------------------------------------------------------------

def T : nat -> nat
| 0      => 0
| succ n => succ n + T n

--------------------------------------------------------------------------------

theorem t_eq_polynomial (n : nat) : T n = (n^2 + n) / 2 := by
  sorry

