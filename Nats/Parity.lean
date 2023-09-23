import Nats.Basic
import Nats.Addition
import Nats.Multiplication
import Mathlib.Tactic.LeftRight
--------------------------------------------------------------------------------
open nat
open nat.nat
open Addition
open Multiplication
namespace Parity
--------------------------------------------------------------------------------

def is_even (n : nat) := ∃ k, 2*k = n
def is_odd (n : nat) := ∃ k, succ (2*k) = n

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

theorem succ_even_is_odd (n : nat) : is_even n -> is_odd (succ n) := by
  rw [is_even, is_odd]
  intro ha
  apply Exists.elim ha $ λ w => by
    intro hb
    rw [<- succ_inj_iff] at hb
    exact ⟨w, hb⟩ 

theorem odd_is_succ_even (n : nat) : is_odd (succ n) -> is_even n := by
  rw [is_even, is_odd]
  intro ha
  apply Exists.elim ha $ λ w => by
    intro hb
    rw [succ_inj_iff] at hb
    rw [<- hb]
    sorry

theorem succ_odd_is_even (n : nat) : is_odd n -> is_even (succ n) := by
  sorry

theorem two_n_is_even (n : nat) : is_even (2*n) := by
  exact ⟨n, rfl⟩ 

theorem existential_negation {p : x -> Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  have pa : (¬ ∃ x, p x) -> (∀ x, ¬ p x) := by
    intro ha w hb
    apply ha
    exact ⟨w, hb⟩

  have pb : (∀ x, ¬ p x) -> (¬ ∃ x, p x) := by
    intro ha hb
    apply Exists.elim hb $ λ w => by
      exact ha w

  exact ⟨pa, pb⟩ 

theorem even_is_not_odd (n : nat) : is_even n -> ¬ is_odd n := by
  intro ha
  induction n with
  | zero =>
    rw [is_odd, existential_negation]
    intro x
    rw [<- Ne]
    exact succ_ne_zero _
  | succ d ih =>
    rw [is_odd, existential_negation]
    intro x
    intro h
    rw [succ_inj_iff] at h
    apply ih
    rw [<- h]
    have d_is_even : is_even d := by
      rw [<- h]
      exact two_n_is_even _
    exact two_n_is_even _
    sorry
      
    


theorem even_ne_odd (a b : nat) : is_even a ∧ is_odd b -> a ≠ b := by
  intro ⟨p, q⟩ 
  rw [is_even] at p
  rw [is_odd] at q
  sorry

example : ∀ k, succ (2*k) ≠ 0 := by
  intro k
  exact succ_ne_zero _

-- ¬∃ k, P(n)
-- ∀ k, ¬P(n)


theorem even_or_odd : ∀ n, is_even n ∨ is_odd n := by
  intro n
  induction n with
  | zero =>
    left
    exact zero_is_even
  | succ d ih =>
    sorry


theorem parity_boolean (n : nat) : ¬ is_even n ↔ is_odd n := by
  have p : ¬ is_even n -> is_odd n := by
    rw [Not]
    intro h
    induction n with
    | zero =>
      apply False.elim
      exact h zero_is_even
    | succ d ih =>
      apply False.elim
      apply h
      rw [is_even]
      sorry
        
        
      
  have q : is_odd n -> ¬ is_even n := by
    sorry
  exact ⟨p, q⟩ 

theorem succ_odd_is_even (n : nat) : is_odd n -> is_even (succ n) := by
  sorry

theorem parity_alternation (n : nat) : is_even n ↔ is_odd (succ n) := by
  sorry

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
    (fun w =>
     fun hw : p w ∧ q w =>
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
  

