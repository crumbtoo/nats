import Nats.Addition
import Nats.Basic
import Mathlib.Tactic.LeftRight
--------------------------------------------------------------------------------
open nat
open nat.nat
open Addition
namespace Multiplication
--------------------------------------------------------------------------------

theorem mul_zero (a : nat) : a * 0 = 0 := by rfl

theorem mul_succ (a b : nat) : a * succ b = a + (a * b) := by rfl

theorem zero_mul (a : nat) : 0 * a = 0 := by
  induction a with
  | zero      => rw [zero_is_0, mul_zero]
  | succ d ih => rw [mul_succ, ih, add_zero]

theorem succ_mul (a b : nat) : succ a * b = (a * b) + b := by
  induction b with
  | zero      => rw [zero_is_0, mul_zero, mul_zero, add_zero]
  | succ d ih => rw [mul_succ, ih, succ_add, mul_succ, add_succ, add_assoc]

theorem mul_one (a : nat) : a * 1 = a := by
  induction a with
  | zero      => rw [zero_is_0, zero_mul]
  | succ d ih => rw [succ_mul, ih, succ_eq_add_one]

theorem one_mul (a : nat) : 1 * a = a := by
  induction a with
  | zero      => rw [zero_is_0, mul_zero]
  | succ d ih => rw [mul_succ, ih, succ_eq_add_one, add_comm]

theorem mul_comm (a b : nat) : a * b = b * a := by
  induction b with
  | zero =>
    rw [zero_is_0, mul_zero, zero_mul]
  | succ d ih =>
    rw [mul_succ, succ_mul, ih]
    simp

theorem mul_left_distrib (a b c : nat) : a * (b + c) = (a*b + a*c) := by
  induction c with
  | zero      => rw [zero_is_0, add_zero, mul_zero, add_zero]
  | succ d ih => rw [add_succ, mul_succ, ih, mul_succ, add_right_comm (a*b) _]

theorem succ_mul_succ_ne_zero : succ a * succ b ≠ 0 := by
  rw [mul_succ, succ_add]
  exact succ_ne_zero _

theorem mul_zero_factor {a b : nat} : a*b = 0 -> a=0 ∨ b=0 := by
  intro h
  cases a with
  | zero =>
    left
    rfl
  | succ d =>
    cases b with
    | zero =>
      right
      rfl
    | succ e =>
      constructor
      apply False.elim
      exact succ_mul_succ_ne_zero h

theorem mul_zero_product {a b : nat} : a=0 ∨ b=0 -> a*b = 0 := by
  intro h
  cases h with
  | inl hl =>
    rw [hl, zero_mul]
  | inr hr =>
    rw [hr, mul_zero]

theorem mul_zero_factor_iff (a b : nat) : a*b = 0 ↔ a=0 ∨ b=0 := by
  exact ⟨mul_zero_factor, mul_zero_product⟩ 
  
theorem mul_left_uncancel {a b : nat} (n : nat) : a = b -> n*a = n*b := by
  intro h
  induction n with
  | zero =>
    rw [zero_is_0, zero_mul, zero_mul]
  | succ d ih =>
    rw [succ_mul, succ_mul, ih, h]

theorem mul_left_cancel {n a b : nat} : n ≠ 0 -> n*a = n*b -> a = b := by
  intro ha hb
  induction b generalizing a with
  | zero =>
    rw [zero_is_0]
    rw [zero_is_0, mul_zero] at hb
    cases mul_zero_factor hb with
    | inl hl =>
      apply False.elim
      exact ha hl
    | inr hr =>
      exact hr
  | succ d ih =>
    cases a with
    | zero =>
      rw [zero_is_0, mul_zero] at hb
      have hb := Eq.symm hb
      cases mul_zero_factor hb with
      | inl hl =>
        apply False.elim
        exact ha hl
      | inr hr =>
        apply False.elim
        exact succ_ne_zero d hr
    | succ k =>
      rw [mul_succ, mul_succ] at hb
      have hb := add_left_cancel hb
      rw [succ_inj_iff]
      exact ih hb

--------------------------------------------------------------------------------

