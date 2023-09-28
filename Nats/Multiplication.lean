import Nats.Addition
import Nats.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
--------------------------------------------------------------------------------
open Basic
open Basic.nat
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

theorem mul_assoc (a b c : nat) : a * (b * c) = a * b * c := by
  induction c with
  | zero =>
    rw [zero_is_0, mul_zero, mul_zero, mul_zero]
  | succ d ih =>
    rw [mul_succ, mul_succ, mul_left_distrib, ih]

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

theorem mul_left_cancel {n a b : nat} {ha : n ≠ 0}: n*a = n*b -> a = b := by
  intro hb
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

theorem nz_mul_nz (a b : nat) : a ≠ 0 ∧ b ≠ 0 -> a*b ≠ 0 := by
  intro ⟨p, q⟩ ha
  rw [mul_zero_factor_iff] at ha
  cases ha with
  | inl hl =>
    apply p
    exact hl
  | inr hr =>
    apply q
    exact hr

--------------------------------------------------------------------------------

def pow : nat -> nat -> nat
| _, 0      => 1
| n, succ k => n * (pow n k)

instance : Pow nat nat where
  pow := Multiplication.pow

theorem pow_zero (n : nat) : n ^ 0 = 1 := by rfl

theorem pow_succ (n k : nat) : n ^ (succ k) = n * (n^k) := by rfl

theorem zero_pow_succ (n : nat) : 0 ^ (succ n) = 0 := by
  rw [pow_succ, zero_mul]

theorem pow_one (n : nat) : n ^ 1 = n := by rfl

theorem one_pow (n : nat) : 1 ^ n = 1 := by
  induction n with
  | zero =>
    rw [zero_is_0, pow_zero]
  | succ d ih =>
    rw [pow_succ, one_mul]
    exact ih

theorem pow_add (a r s : nat) : a^(r+s) = a^r * a^s := by
  induction s with
  | zero =>
    rw [zero_is_0, add_zero, pow_zero, mul_one]
  | succ d ih =>
    rw [add_succ, pow_succ, pow_succ, mul_assoc, mul_comm (a^r), ih, mul_assoc]

theorem pow_mul (a m n : nat) : a^(m*n) = (a^m)^n := by
  induction n with
  | zero =>
    rw [zero_is_0, mul_zero, pow_zero, pow_zero]
  | succ d ih =>
    rw [pow_succ, <- ih, mul_succ, <- pow_add]

--------------------------------------------------------------------------------

def dvd (n a : nat) := ∃ b, a*b = n

instance : Dvd nat where
  dvd := Multiplication.dvd

/- def div (x y : nat) : nat := -/
/-   if 0 < y ∧ y ≤ x then -/
/-     div (x - y) y + 1 -/
/-   else -/
/-     0 -/

