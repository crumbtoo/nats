import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Algebra.Lemmas.Group
--------------------------------------------------------------------------------
namespace Problems
open Group
open Monoid
--------------------------------------------------------------------------------

section HoldenGroupProblem

def MulPow (G : Type) [Group G] (n : ℕ) := ∀ (a b : G), (a*b)^n = a^n * b^n

theorem mul_pow_implies_comm
        [Group G] (j : ℕ)
        : MulPow G j ∧ MulPow G (j+1) ∧ MulPow G (j+2)
        -> ∀ (a b : G), Commute a b
        := by
  intro ⟨powj, powk, powl⟩ a b
  let k := j + 1
  let l := j + 2

  have p : b*(a*b)^j = (a*b)^j*b := by
    have lem₁ : (a*b)^l = a*a^k*b^k*b := sorry
    conv => rhs; rw [powj]
    apply MaddyGroupLemmas.mul_left_cancel a
    sorry

  sorry

-- Suppose G is a group where (ab)ⁿ = aⁿbⁿ for all a, b ∈ G and n ∈ {100, 101,
-- 102}. Prove that G is abelian.
example [Group G]
        : (∀ (a b : G) (n : ({100, 101, 102} : Finset ℕ)),
            (a*b)^↑↑n = a^↑↑n * b^↑↑n )
        -> (∀ (x y : G), x*y = y*x)
        := by
  intro h
  intro x y
  -- actual proof
  sorry

--------------------------------------------------------------------------------


end HoldenGroupProblem

section

variable {G : Type*} [Group G]

example (a : G) : a⁻¹⁻¹ = a := by
  calc
    a⁻¹⁻¹ = a⁻¹⁻¹               := by rfl
    _     = a⁻¹⁻¹ * 1           := by rw [mul_one a⁻¹⁻¹]
    _     = a⁻¹⁻¹ * (a⁻¹ * a)   := by rw [mul_left_inv]
    _     = a⁻¹⁻¹ * a⁻¹ * a     := by rw [mul_assoc]
    _     = 1 * a               := by rw [mul_left_inv]
    _     = a                   := by rw [one_mul]

end

--------------------------------------------------------------------------------

lemma zmod_is_of_nat (n : ℕ) (a : ZMod n) : ∃ (k : ℕ), ↑k = a := by
  use ↑a
  

example (n : ℕ) (a b c : ZMod n) : a + b + c = a + (b + c) := by
  sorry


