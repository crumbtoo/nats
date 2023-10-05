import Algebra.MyGroup
import Mathlib.Data.Finset.Basic
--------------------------------------------------------------------------------
open MyGroup
namespace Examples
--------------------------------------------------------------------------------

namespace ZUnit

/- def ZUnit := { x : ℤ | x == -1 || x == 1 } -/
/- def ZUnit := ({-1, 1} : Finset ℤ) -/
/- def ZUnit := CoeSort.coe ({-1, 1} : Finset ℤ) -/
/- def ZUnitSet := ({-1, 1} : Finset ℤ) -/
def isUnit n := n = -1 ∨ n = 1
def ZUnit := {n : ℤ // isUnit n}

theorem zunit_one : (1 : ℤ) = -1 ∨ (1 : ℤ) = 1 := by right; rfl

theorem zunit_neg_one : (-1 : ℤ) = -1 ∨ (-1 : ℤ) = 1 := by left; rfl

#eval (⟨1, zunit_one⟩ : ZUnit)
#eval (⟨-1, zunit_neg_one⟩ : ZUnit)

instance : OfNat ZUnit 1 where
  ofNat := ⟨1, zunit_one⟩ 

theorem fin_proof {p : ℤ -> Prop} : p (-1 : ℤ) ∧ p (1 : ℤ) -> ∀ (x : ZUnit), p (x.1) := by
  intro ⟨p, q⟩ ⟨z, zp⟩ 
  cases z with
  | ofNat n => sorry
  | negSucc n => sorry
  
def neg : ZUnit -> ZUnit := by
  intro ⟨n, p⟩
  have i : isUnit n -> isUnit (-n) := by
    intro h
    cases h with
    | inl hl => rw [hl, neg_neg]; right; rfl
    | inr hr => rw [hr]; left; rfl
  exact ⟨-n, i p⟩ 

instance : Neg ZUnit where
  neg := ZUnit.neg

end ZUnit

instance : MyGroup ZUnit where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  div := sorry
  mul_inv := sorry
  div_eq_mul_inv := sorry
