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

theorem one_is_unit : isUnit 1 := by
  right
  rfl

theorem neg_one_is_unit : isUnit (-1) := by
  left
  rfl

-- todo: iff
theorem neg_unit : isUnit n -> isUnit (-n) := by
  intro h
  cases h with
  | inl hl => rw [hl, neg_neg]; exact one_is_unit
  | inr hr => rw [hr];          exact neg_one_is_unit

theorem unit_product : isUnit x ∧ isUnit y -> isUnit (x*y) := by
  intro ⟨p, q⟩
  cases p with
  | inl hl₁ =>
    cases q with
    | inl hl₂ =>
      rw [hl₁, hl₂]
      simp
      exact one_is_unit
    | inr hr₂ =>
      rw [hl₁, hr₂]
      simp
      exact neg_one_is_unit
  | inr hr₁ =>
    cases q with
    | inl hl₂ =>
      rw [hr₁, hl₂]
      simp
      exact neg_one_is_unit
    | inr hr₂ =>
      rw [hr₁, hr₂]
      simp
      exact one_is_unit

instance : OfNat ZUnit 1 where
  ofNat := ⟨1, zunit_one⟩ 
  
def neg : ZUnit -> ZUnit := by
  intro ⟨n, p⟩
  exact ⟨-n, neg_unit p⟩ 

instance : Neg ZUnit where
  neg := ZUnit.neg

def mul : ZUnit -> ZUnit -> ZUnit := by
  intro ⟨a, p⟩ ⟨b, q⟩ 
  exact ⟨a*b, unit_product ⟨p, q⟩⟩ 

instance : Mul ZUnit where
  mul := ZUnit.mul

end ZUnit

instance : MyGroup ZUnit.ZUnit where
  mul := Examples.ZUnit.mul
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  div := sorry
  mul_inv := sorry
  div_eq_mul_inv := sorry

