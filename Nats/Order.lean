import Nats.Basic
import Nats.Addition
import Nats.Logic
import Mathlib.Tactic.Contrapose
import Std.Tactic.Basic
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Addition
namespace Order
--------------------------------------------------------------------------------

def le (a b : nat) := ∃ n, a + n = b
def lt (a b : nat) := ∃ n, a + succ n = b
def ge (a b : nat) := ¬ ∃ n, a + succ n = b
def gt (a b : nat) := ¬ ∃ n, a + n = b

instance : LE nat where
  le := Order.le
instance : LT nat where
  lt := Order.lt

--------------------------------------------------------------------------------

theorem le_expand (a b : nat) : a ≤ b ↔ (∃ n, a + n = b) := by
  have p : a ≤ b -> (∃ n, a + n = b) := by
    intro ha
    rw [<- le]
    exact ha
  have q : (∃ n, a + n = b) -> a ≤ b := by
    intro ha
    rw [LE.le]
    rw [<- le] at ha
    exact ha
  exact ⟨p, q⟩ 

theorem lt_expand (a b : nat) : a < b ↔ (∃ n, a + succ n = b) := by
  have p : a < b -> (∃ n, a + succ n = b) := by
    intro ha
    rw [<- lt]
    exact ha
  have q : (∃ n, a + succ n = b) -> a < b := by
    intro ha
    rw [LT.lt]
    rw [<- lt] at ha
    exact ha
  exact ⟨p, q⟩ 

theorem ge_iff_not_lt (a b : nat) : a ≥ b ↔ ¬ a < b := by
  have p : a ≥ b -> ¬ a < b := by
    intro ha hb
    rw [GE.ge, le_expand] at ha
    rw [lt_expand] at hb
    apply Exists.elim ha $ λ w => by
      intro ha'
      apply Exists.elim hb $ λ x => by
        intro hb'
        rw [<- ha', add_assoc, add_succ] at hb'
        exact n_add_succ_ne_n _ hb'

  have q : ¬ a < b -> a ≥ b := by
    intro ha
    sorry
  exact ⟨p, q⟩ 

theorem gt_expand (a b : nat) : a > b ↔ ¬ (∃ n, a + n = b) := by
  rw [GT.gt]
  sorry

theorem gt_ne (a b : nat) : a > b -> a ≠ b := by
  intro h
  sorry

theorem sum_gt (a b n : nat) : a > n -> a+b > n := by
  intro h
  cases b with
  | zero =>
    rw [zero_is_0, add_zero]
    exact h
  | succ d =>
    sorry


