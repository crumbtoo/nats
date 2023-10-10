import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Data.Finset.Basic
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

/- example [Group G] -/
/-         : (∀ (a b : G) (n : ({100, 101, 102} : Finset ℕ)), -/
/-             (a*b)^↑↑n = a^↑↑n * b^↑↑n ) -/
/-         -> CommGroup G -/
/-         := by -/
/-   intro a b n h -/
/-   have i : n.val = 100 ∨ n.val = 101 ∨ n.val = 102 := by -/
/-     have j := n.property -/
/-     rw [elem_or_eq] at j -/
/-     exact j -/
/-   apply CommGroup_of_comm_group -/
/-   intro x y -/
/-   -- start of actual proof -/

end HoldenGroupProblem

