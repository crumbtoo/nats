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

theorem zero_lt_succ (n : nat) : 0 < succ n := by
  induction n with
  | zero =>
    rw [lt_expand]
    use zero
    simp
  | succ d _ =>
    rw [lt_expand]
    use (succ d)
    simp

theorem succ_inj_lt (a b : nat) : succ a < succ b ↔ a < b := by
  have p : succ a < succ b -> a < b := by
    intro ha
    induction b with
    | zero =>
      apply Exists.elim ha $ λ w => by
        intro hb
        exfalso
        rw [add_succ, succ_inj_iff, succ_add] at hb
        exact succ_ne_zero _ hb
    | succ d _ =>
      apply Exists.elim ha $ λ w => by
        intro ha'
        rw [add_succ, succ_inj_iff, succ_add, succ_inj_iff] at ha'
        use w
        rw [add_succ, succ_inj_iff]
        exact ha'
  have q : a < b -> succ a < succ b := by
    intro ha
    induction b with
    | zero =>
      apply Exists.elim ha $ λ w => by
        intro ha'
        exfalso
        rw [add_succ] at ha'
        exact succ_ne_zero _ ha'
    | succ d _ =>
      apply Exists.elim ha $ λ w => by
        intro ha'
        rw [add_succ, succ_inj_iff] at ha'
        use w
        rw [add_succ, succ_inj_iff, succ_add, succ_inj_iff]
        exact ha'
  exact ⟨p, q⟩ 

theorem ne_is_lt_or_gt (a b : nat) : a ≠ b ↔ (a < b ∨ a > b) := by
  have p : a ≠ b -> (a < b ∨ a > b) := by
    intro ha
    /- rw [GT.gt, lt_expand, lt_expand] -/
    induction a generalizing b with
    | zero =>
      cases b with
      | zero =>
        contradiction
      | succ d =>
        left
        exact zero_lt_succ _
    | succ d ih =>
      cases b with
      | zero =>
        right
        rw [GT.gt]
        exact zero_lt_succ _
      | succ e =>
        have hb : d ≠ e := by
          intro hb
          rw [<- succ_inj_iff] at hb
          contradiction
        have hc : d < e := by
          ih e hb
        left
  have q : (a < b ∨ a > b) -> a ≠ b := by
    sorry
  exact ⟨p, q⟩ 

theorem lt_add (a b n : nat) : a < b -> a < b + n := by
  intro h
  induction a with
  | zero =>
    cases n with
    | zero =>
      rw [zero_is_0, add_zero]
      exact h
    | succ d =>
      rw [add_succ]
      exact zero_lt_succ _
  | succ d ih =>
    cases n with
    | zero =>
      rw [zero_is_0, add_zero]
      exact h
    | succ e =>
      rw [add_succ]

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
    contrapose
    rw [not_not]
    intro ha
    induction a with
    | zero =>
      sorry
    | succ d ih =>
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


