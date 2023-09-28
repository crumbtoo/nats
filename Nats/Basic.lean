namespace Basic
--------------------------------------------------------------------------------

inductive nat : Type
-- PA.1: 0 is a natural number
| zero : nat
-- PA.6 for every natural number n, succ n is a natural number
| succ : nat -> nat
deriving Repr, BEq, DecidableEq, Inhabited

open nat

def natToMyNat : Nat -> nat
| 0           => zero
| Nat.succ n  => succ (natToMyNat n)

instance : OfNat nat n where
  ofNat := natToMyNat n

def myNatToNat : nat -> Nat
| zero      => 0
| succ n    => Nat.succ (myNatToNat n)

instance : ToString nat where
  toString n := toString (myNatToNat n)

--------------------------------------------------------------------------------

def add : nat -> nat -> nat
| a, 0      => a
| a, succ b => succ (add a b)

instance : Add nat where
  add := Basic.add

def mul : nat -> nat -> nat
| _, 0      => 0
| a, succ b => a + (mul a b)

instance : Mul nat where
  mul := Basic.mul

--------------------------------------------------------------------------------

-- PA.7 for all natural numbers a and b, succ a = succ b => a = b
axiom succ_inj {a b : nat} : succ a = succ b -> a = b

-- PA.8 for every natural number n, succ n = 0 is false
axiom succ_ne_zero (n : nat) : succ n ≠ 0

--------------------------------------------------------------------------------

theorem zero_is_0 : zero = 0 := by rfl

--------------------------------------------------------------------------------

theorem succ_inj_iff (a b : nat) : succ a = succ b ↔ a = b := by
  have ha : succ a = succ b -> a = b := by
    apply succ_inj
  have hb : a = b -> succ a = succ b := by
    intro h
    rw [h]
  exact ⟨ha, hb⟩

theorem nz_is_succ : ∀ n : nat, n ≠ 0 -> ∃ m, succ m = n := by
  intro n h
  rw [Ne, Not] at h
  induction n with
  | zero =>
    apply False.elim
    rw [zero_is_0] at h
    apply h
    rfl
  | succ d _ =>
    exact ⟨d, rfl⟩

