import Nats.Basic
import Nats.Addition
import Nats.Logic
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Std.Tactic.Basic
--------------------------------------------------------------------------------
open Basic
open Basic.nat
open Addition
namespace Order
--------------------------------------------------------------------------------

def le (a b : nat) := ∃ n, a + n = b
def lt (a b : nat) := le a b ∧ a ≠ b
def ge (a b : nat) := le b a
def gt (a b : nat) := lt b a

instance : LE nat where
  le := Order.le
instance : LT nat where
  lt := Order.lt

--------------------------------------------------------------------------------

theorem le_is_le (a b : nat) : a ≤ b ↔ le a b := by rfl
theorem lt_is_lt (a b : nat) : a < b ↔ lt a b := by rfl
theorem ge_is_ge (a b : nat) : a ≥ b ↔ ge a b := by rfl
theorem gt_is_gt (a b : nat) : a > b ↔ gt a b := by rfl

theorem le_expand (a b : nat) : a ≤ b ↔ ∃ n, a + n = b := by rfl
theorem lt_expand (a b : nat) : a < b ↔ a ≤ b ∧ a ≠ b := by rfl
theorem ge_expand (a b : nat) : a ≥ b ↔ b ≤ a := by rfl
theorem gt_expand (a b : nat) : a > b ↔ b < a := by rfl

theorem lt_as_le (a b : nat) : a < b ↔ (a ≤ b ∧ a ≠ b) := by
  have p : a < b -> (a ≤ b ∧ a ≠ b) := by
    intro ha
    rw [lt_is_lt, lt] at ha
    cases ha with
    | intro r s =>
      rw [<- le_is_le] at r
      exact ⟨r, s⟩ 
  have q : (a ≤ b ∧ a ≠ b) -> a < b := by
    intro ha
    rw [lt_expand]
    exact ha
  exact ⟨p, q⟩ 

theorem lt_zero {k : nat} : ¬ k < 0 := by
  intro ha
  rw [lt_expand, le_expand] at ha
  cases ha with
  | intro p q =>
    apply Exists.elim p $ λ w => by
      intro hb
      rw [zero_sum] at hb
      cases hb with
      | intro i o =>
        contradiction

theorem zero_le {k : nat} : 0 ≤ k := by
  cases k with
  | zero =>
    rw [zero_is_0, le_expand]
    use 0
    rfl
  | succ d =>
    rw [le_expand]
    use succ d
    simp

theorem le_zero {k : nat} : k ≤ 0 ↔ k = 0 := by
  have p : k ≤ 0 -> k = 0 := by
    intro ha
    rw [le_expand] at ha
    cases ha with
    | intro w eh =>
      rw [zero_sum] at eh
      have ⟨i, _⟩ := eh
      exact i
  have q : k = 0 -> k ≤ 0 := by
    intro ha
    rw [le_expand]
    use 0
    simp
    exact ha
  exact ⟨p, q⟩ 

theorem le_self {k : nat} : k ≤ k := by
  use 0
  simp

theorem zero_lt_succ {k : nat} : 0 < succ k := by
  rw [lt_expand]
  have p : 0 ≠ succ k := by
    apply Ne.symm
    exact succ_ne_zero _
  exact ⟨zero_le, p⟩ 

theorem le_succ {n a : nat} : n ≤ a -> n ≤ succ a := by
  cases n with
  | zero =>
    rw [zero_is_0]
    intro _
    exact zero_le
  | succ d =>
    intro ha
    rw [le_expand]
    rw [le_expand] at ha
    cases ha with
    | intro w eh =>
      use succ w
      rw [add_succ, succ_inj_iff]
      exact eh

theorem succ_is_gt (n : nat) : n < succ n := by
  induction n with
  | zero =>
    exact zero_lt_succ
  | succ d ih =>
    rw [lt_expand, le_expand]
    have p : ∃ n, succ d + n = succ (succ d) := by
      rw [lt_expand] at ih
      cases ih with
      | intro i o =>
        cases i with
        | intro w eh =>
          use w
          rw [succ_add, succ_inj_iff]
          exact eh
    have q : succ d ≠ succ (succ d) := by
      exact n_ne_succ_n _
    exact ⟨p, q⟩ 

theorem succ_inj_le {a b : nat} : succ a ≤ succ b ↔ a ≤ b := by
  cases a with
  | zero =>
    have p : succ 0 ≤ succ b -> 0 ≤ b := by
      intro _
      exact zero_le
    have q : 0 ≤ b -> succ 0 ≤ succ b := by
      intro ha
      have hb : 0 ≤ succ b := by
        exact le_succ ha
      cases b with
      | zero =>
        rw [zero_is_0]
        exact le_self
      | succ d =>
        rw [le_expand]
        use succ d
        rw [succ_add, zero_add]
    exact ⟨p, q⟩ 
  | succ d =>
    have p : succ (succ d) ≤ succ b -> succ d ≤ b := by
      intro ha
      rw [le_expand]
      rw [le_expand] at ha
      cases ha with
      | intro w eh =>
        rw [succ_add, succ_inj_iff] at eh
        use w
    have q : succ d ≤ b -> succ (succ d) ≤ succ b := by
      intro ha
      rw [le_expand]
      rw [le_expand] at ha
      cases ha with
      | intro w eh =>
        rw [<- succ_inj_iff, <- succ_add] at eh
        use w
    exact ⟨p, q⟩ 

theorem le_transitive (a b c : nat) : a ≤ b ∧ b ≤ c -> a ≤ c := by
  intro ⟨ha, hb⟩ 
  sorry

theorem le_add (n a b : nat) : n ≤ a -> n ≤ a + b := by
  induction b with
  | zero =>
    rw [zero_is_0, add_zero]
    intro h
    exact h
  | succ d ih =>
    sorry

