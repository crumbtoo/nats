import Nats.Basic
import Nats.Addition
import Nats.Multiplication
import Nats.Logic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Use
import Mathlib.Tactic.ExistsI
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

theorem even_sub_2_is_even (n : nat)
    : is_even (succ (succ n)) -> is_even n := by
  intro ha
  cases even_or_odd n with
  | inl hl =>
    exact hl
  | inr hr =>
    induction n with
    | zero =>
      exact zero_is_even
    | succ d ih =>
      have i : is_even (succ (succ d)) :=
        succ_odd_is_even (succ d) hr
      sorry
    
  
/- theorem even_sub_2_is_even (n : nat) -/
/-     : is_even (succ (succ n)) -> is_even n := by -/
/-   intro ha -/
/-   have i : is_odd (succ n) := by -/
/-     cases even_or_odd n with -/
/-     | inl hl => -/
/-       exact succ_even_is_odd n hl -/
/-     | inr hr => -/
/-       cases even_or_odd n with -/
/-       | inl hl₂ => -/
/-         exact succ_even_is_odd n hl₂ -/
/-       | inr hr₂ => -/
        
/-   sorry -/

theorem even_is_succ_odd (n : nat) : is_even (succ n) -> is_odd n := by
  intro ha
  induction n with
  | zero =>
    exfalso
    apply one_is_not_even
    exact ha
  | succ d ih =>
    apply succ_even_is_odd
    sorry

theorem succ_even_is_not_even (n : nat) : is_even n -> ¬ is_even (succ n) := by
  intro ha
  induction n with
  | zero =>
    intro hb
    apply Exists.elim hb $ λ w => by
      intro hc
      induction w with
      | zero =>
        rw [zero_is_0, add_zero] at hc
        have hc := Eq.symm hc
        apply succ_ne_zero 0
        exact hc
      | succ d ih =>
        rw [add_succ, succ_add, succ_inj_iff] at hc
        apply succ_ne_zero (d + d)
        exact hc
  | succ d ih =>
    intro hb
    have i : is_even d := by
      sorry
    sorry

theorem two_n_is_even (n : nat) : is_even (n+n) := by
  exact ⟨n, rfl⟩ 

example : ∃ k, k+k = (4 : nat) := by
  use 2
  rfl

theorem two_n_is_not_odd (n : nat) : ¬ is_odd (n+n) := by
  have i : is_even (n+n) := two_n_is_even n
  induction n with
  | zero =>
    intro ha
    apply Exists.elim ha $ λ w => by
      intro hb
      apply succ_ne_zero (w+w)
      exact hb
  | succ d ih =>
    rw [add_succ, succ_add]
    intro ha
    apply Exists.elim ha $ λ w => by
      intro hb
      rw [succ_inj_iff] at hb
      sorry

theorem succ_two_n_is_odd (n : nat) : is_odd (succ (n+n)) := by
  exact ⟨n, rfl⟩ 

theorem eq_is_same_parity (a b : nat)
    : a = b -> (is_even a ∧ is_even b) ∨ (is_odd a ∧ is_odd b) := by
  intro ha
  sorry

theorem zero_is_not_odd : ¬ is_odd (0 : nat) := by
  intro h
  rw [is_odd] at h
  exact Exists.elim h $ λ w => by
    exact succ_ne_zero _

theorem even_and_odd (n : nat) : ¬ (is_even n ∧ is_odd n) := by
  intro ⟨p, q⟩ 
  induction n with
  | zero =>
    apply zero_is_not_odd
    exact q
  | succ d ih =>
    have q' : is_even d := odd_is_succ_even d q
    have p' : is_odd d := sorry
    sorry

theorem two_mul (n : nat) : 2*n = n+n := by
  have two_eq_succ_succ : 2 = succ (succ zero) := by
    rfl
  rw [two_eq_succ_succ, succ_mul, succ_mul, zero_is_0, zero_mul, zero_add]
      
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

theorem even_is_not_odd (n : nat) : is_even n -> ¬ is_odd n := by
  intro ha hb
  apply even_ne_odd n n ⟨ha, hb⟩ 
  rfl

/- theorem even_is_not_odd (n : nat) : is_even n -> ¬ is_odd n := by -/
/-   intro ha hb -/
/-   induction n with -/
/-   | zero => -/
/-     apply zero_is_not_odd -/
/-     rw [zero_is_0] at hb -/
/-     exact hb -/
/-   | succ d ih => -/
/-     have p : is_even d := odd_is_succ_even d hb -/
/-     have q : is_odd d := even_is_succ_odd d ha -/
/-     exact ih p q -/

example : ∀ k, succ (2*k) ≠ 0 := by
  intro k
  exact succ_ne_zero _

theorem parity_boolean (n : nat) : ¬ is_even n ↔ is_odd n := by
  have p : ¬ is_even n -> is_odd n := by
    sorry
  have q : is_odd n -> ¬ is_even n := by
    sorry
  exact ⟨p, q⟩ 

theorem parity_alternation (n : nat) : is_even n ↔ is_odd (succ n) := by
  exact ⟨succ_even_is_odd n, odd_is_succ_even n⟩ 

/- theorem succ_parity (n : nat) : is_even n ↔ ¬ is_even (succ n) := by -/
/-   constructor -/
/-   induction n with -/
/-   | zero => -/
/-     intro h -/
/-     rw [zero_is_0, succ_eq_add_one, zero_add] -/
/-     rw [Not] -/
/-     intro i -/
/-     have j : ¬ is_even 1 := by -/


variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (λ w =>
     λ hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

/- theorem even_mul_even_is_even (a b : nat) : is_even a ∧ is_even b -> is_even (a*b) := by -/
/-   intro h -/
/-   induction b with -/
/-   | zero      => -/
/-     rw [zero_is_0, mul_zero] -/
/-     have hz : (zero = 2 * zero) := by rfl -/
/-     exact ⟨zero, hz⟩ -/ 
/-   | succ d ih => -/
/-     rw [is_even, mul_succ] -/


/- instance : Decidable (is_even n) where -/


/- example (n : nat) : 4 = 2*n := by -/
  

