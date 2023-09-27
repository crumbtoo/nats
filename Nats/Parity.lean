import Nats.Basic
import Nats.Addition
import Nats.Multiplication
import Nats.Logic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Use
import Mathlib.Tactic.ExistsI
import Mathlib.Tactic.Contrapose
import Std.Tactic.Basic
--------------------------------------------------------------------------------
open nat
open nat.nat
open Addition
open Multiplication
namespace Parity
--------------------------------------------------------------------------------

def is_even (n : nat) := ∃ k, k+k = n
def is_odd (n : nat) := ∃ k, succ (k+k) = n

example : is_even 0 := by
  rw [is_even]
  have h : ((0 : nat) = 2 * 0) := by rfl
  exact ⟨0, h⟩ 

example : is_odd 1 := by
  rw [is_odd]
  have h : ((1 : nat) = succ (2 * 0)) := by rfl
  exact ⟨0, h⟩

theorem zero_is_even : is_even 0 := by
  rw [is_even]
  have h : ((0 : nat) = 2*0) := by rfl
  exact ⟨0, h⟩ 

theorem zero_is_not_odd : ¬ is_odd (0 : nat) := by
  intro h
  rw [is_odd] at h
  exact Exists.elim h $ λ w => by
    exact succ_ne_zero _

theorem one_is_odd : is_odd 1 := by
  rw [is_odd]
  have h : ((1 : nat) = 2*0+1) := by rfl
  exact ⟨0, h⟩ 

theorem one_is_not_even : ¬ is_even 1 := by
  rw [is_even, Logic.existential_negation]
  intro n
  rw [<- Ne]

  have i : (1 : nat) = succ 0 := by rfl

  induction n with
  | zero =>
    rw [zero_is_0, add_zero]
    apply Ne.symm
    rw [i]
    exact succ_ne_zero _
  | succ d _ =>
    intro h
    rw [add_succ, succ_add, i, succ_inj_iff] at h
    apply succ_ne_zero (d+d)
    exact h

theorem succ_even_is_odd (n : nat) : is_even n -> is_odd (succ n) := by
  rw [is_even, is_odd]
  intro ha
  apply Exists.elim ha $ λ w => by
    intro hb
    rw [<- succ_inj_iff] at hb
    exact ⟨w, hb⟩ 

theorem succ_odd_is_even (n : nat) : is_odd n -> is_even (succ n) := by
  rw [is_odd, is_even]
  intro ha
  apply Exists.elim ha $ λ w => by
    intro hb
    use (succ w)
    rw [add_succ, succ_inj_iff, succ_add]
    exact hb

theorem odd_is_succ_even (n : nat) : is_odd (succ n) -> is_even n := by
  rw [is_even, is_odd]
  intro ha
  apply Exists.elim ha $ λ w => by
    intro hb
    rw [succ_inj_iff] at hb
    exact ⟨w, hb⟩ 

theorem even_or_odd : ∀ n : nat, is_even n ∨ is_odd n := by
  intro n
  induction n with
  | zero =>
    left
    exact zero_is_even
  | succ d ih =>
    cases ih with
    | inl hl =>
      right
      exact succ_even_is_odd d hl
    | inr hr =>
      left
      apply Exists.elim hr $ λ w => by
        intro _
        exact succ_odd_is_even d hr

theorem succ_n_add_n_is_odd (k : nat) (ha : n = succ (k + k)) : is_odd n := by
  use k
  apply Eq.symm
  exact ha

theorem n_add_n_is_not_odd (n : nat) : n + n = k -> ¬ is_odd k := by
  intro ha
  induction k generalizing n with
  | zero =>
    exact zero_is_not_odd
  | succ d ih =>
    intro hb
    apply Exists.elim hb $ λ w => by
      intro hc
      rw [succ_inj_iff] at hc
      apply ih w hc
      cases n with
      | zero =>
        rw [zero_is_0, add_zero] at ha
        exfalso
        exact succ_ne_zero _ (Eq.symm ha)
      | succ e =>
        rw [add_succ, succ_add, succ_inj_iff] at ha
        exact ⟨e, ha⟩ 

theorem even_and_odd (n : nat) : ¬ (is_even n ∧ is_odd n) := by
  intro ⟨ha, hb⟩ 
  induction n with
  | zero =>
    exact zero_is_not_odd hb
  | succ d ih =>
    have i := odd_is_succ_even _ hb
    have j : is_odd d := by
      apply Exists.elim ha $ λ w => by
        intro hc
        cases w with
        | zero =>
          exfalso
          exact succ_ne_zero _ (Eq.symm hc)
        | succ e =>
          rw [add_succ, succ_add, succ_inj_iff] at hc
          exact succ_n_add_n_is_odd _ (Eq.symm hc)
    exact ih i j

theorem even_is_not_odd (n : nat) : is_even n -> ¬ is_odd n := by
  intro p q
  apply even_and_odd n
  exact ⟨p, q⟩ 

theorem odd_is_not_even (n : nat) : is_odd n -> ¬ is_even n := by
  intro p q
  apply even_and_odd n
  exact ⟨q, p⟩ 

theorem even_iff_not_odd (n : nat) : is_even n ↔ ¬ is_odd n := by
  have p : is_even n -> ¬ is_odd n := by
    exact even_is_not_odd _
  have q : ¬ is_odd n -> is_even n := by
    contrapose
    intro ha hb
    cases even_or_odd n with
    | inl hl =>
      contradiction
    | inr hr =>
      contradiction
  exact ⟨p, q⟩ 

theorem odd_iff_not_even (n : nat) : is_odd n ↔ ¬ is_even n := by
  exact Iff.not_right (Iff.symm $ even_iff_not_odd n)

theorem even_is_succ_odd (n : nat) : is_even (succ n) -> is_odd n := by
  cases even_or_odd n with
  | inl hl =>
    contrapose
    intro ha
    rw [<- even_iff_not_odd] at ha
    rw [<- odd_iff_not_even]
    exact succ_even_is_odd n hl
  | inr hr =>
    intro _
    exact hr
    
theorem even_ne_odd (a b : nat) : is_even a ∧ is_odd b -> a ≠ b := by
  intro ⟨p, q⟩ 
  intro h
  induction b generalizing a with
  | zero =>
    exact zero_is_not_odd q
  | succ d ih =>
    rw [h] at p
    have p' : is_odd d := even_is_succ_odd d p
    have q' : is_even d := odd_is_succ_even d q
    apply ih d q' p'
    rfl

theorem two_n_is_even (n : nat) : is_even (n+n) := by
  exact ⟨n, rfl⟩ 

example : ∃ k, k+k = (4 : nat) := by
  use 2
  rfl

theorem succ_two_n_is_odd (n : nat) : is_odd (succ (n+n)) := by
  exact ⟨n, rfl⟩ 

theorem eq_is_same_parity (a b : nat)
    : a = b -> (is_even a ∧ is_even b) ∨ (is_odd a ∧ is_odd b) := by
  intro ha
  rw [ha]
  cases even_or_odd b with
  | inl hl =>
    left
    exact ⟨hl, hl⟩ 
  | inr hr =>
    right
    exact ⟨hr, hr⟩ 

theorem pred_even_is_odd (n : nat) : is_even (succ n) ↔ is_odd n := by
  exact ⟨even_is_succ_odd n, succ_odd_is_even n⟩ 

theorem pred_odd_is_even (n : nat) : is_odd (succ n) ↔ is_even n := by
  exact ⟨odd_is_succ_even n, succ_even_is_odd n⟩ 

--------------------------------------------------------------------------------

theorem even_add_even_is_even (a b : nat)
    : is_even a ∧ is_even b -> is_even (a+b) := by
  intro ⟨ha, hb⟩ 
  induction a generalizing b with
  | zero =>
    rw [zero_is_0, zero_add]
    exact hb
  | succ d _ =>
    cases even_or_odd d with
    | inl hl =>
      have i : is_odd d := even_is_succ_odd d ha
      exfalso
      exact even_and_odd d ⟨hl, i⟩ 
    | inr hr =>
      apply Exists.elim ha $ λ r => by
        intro hc
        apply Exists.elim hb $ λ s => by
          intro hd
          use (r+s)
          rw [<- hc, <- hd]
          simp

theorem even_add_odd_is_odd (a b : nat)
    : is_even a ∧ is_odd b -> is_odd (a+b) := by
  intro ⟨ha, hb⟩ 
  cases b with
  | zero =>
    exfalso
    exact zero_is_not_odd hb
  | succ d =>
    rw [add_succ]
    apply even_is_succ_odd
    have i : is_even d := odd_is_succ_even _ hb
    rw [pred_even_is_odd, pred_odd_is_even]
    exact even_add_even_is_even _ _ ⟨ha, i⟩ 

