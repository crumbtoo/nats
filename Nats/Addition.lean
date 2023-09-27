import Nats.Basic
--------------------------------------------------------------------------------
open nat
open nat.nat
namespace Addition
--------------------------------------------------------------------------------

theorem add_zero (a : nat) : a + 0 = a := by rfl

theorem add_succ (a b : nat) : a + succ b = succ (a + b) := by rfl

theorem zero_add (a : nat) : 0 + a = a := by
  induction a with
  | zero      => rfl
  | succ d ih => rw [add_succ, ih]

theorem succ_add (a b : nat) : succ a + b = succ (a + b) := by
  induction b with
  | zero      => rw [zero_is_0, add_zero, add_zero]
  | succ d ih => rw [add_succ, ih, <- add_succ]

@[simp]
theorem add_comm (a b : nat) : a + b = b + a := by
  induction b with
  | zero      => rw [zero_is_0, add_zero, zero_add]
  | succ d ih => rw [add_succ, succ_add, ih]

@[simp]
theorem add_assoc (a b c : nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero      => rw [zero_is_0, add_zero, add_zero]
  | succ d ih => rw [add_succ, add_succ, add_succ, ih]

theorem succ_eq_add_one (a : nat) : succ a = a + 1 := by
  have h : 1 = succ 0 := by rfl
  rw [h, add_succ, add_zero]

@[simp]
theorem add_right_comm (a b c : nat) : a + (b + c) = b + (a + c) := by
  rw [<- add_assoc, <- add_assoc, add_comm b a]

theorem add_left_cancel {n a b : nat} : n + a = n + b -> a = b := by
  intro h
  induction n with
  | zero =>
    rw [zero_is_0] at h
    repeat rw [zero_add] at h
    exact h
  | succ d ih =>
    apply ih
    repeat rw [succ_add] at h
    exact succ_inj h

theorem add_right_cancel {n a b : nat} (h : a + n = b + n) : a = b := by
  rw [add_comm a n, add_comm b n] at h
  exact add_left_cancel h

theorem add_succ_ne_zero (a : nat) : succ a + n ≠ 0 := by
  rw [succ_add]
  exact succ_ne_zero _

theorem n_ne_succ_n (n : nat) : n ≠ succ n := by
  induction n with
  | zero =>
    apply Ne.symm
    exact succ_ne_zero _
  | succ d ih =>
    intro ha
    rw [succ_inj_iff] at ha
    contradiction

theorem n_add_succ_ne_n (n : nat) : n + succ k ≠ n := by
  induction n generalizing k with
  | zero =>
    rw [zero_is_0, add_succ]
    exact succ_ne_zero _
  | succ d ih =>
    intro ha
    rw [succ_add, add_succ, succ_inj_iff] at ha
    cases k with
    | zero =>
      rw [zero_is_0, add_zero] at ha
      apply n_ne_succ_n d
      exact Eq.symm ha
    | succ e =>
      rw [<- add_succ] at ha
      have i : d + succ (succ e) ≠ d := by
        exact ih
      contradiction

