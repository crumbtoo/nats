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

lemma elem_or_eq {n : ℕ}
        : n ∈ ({100, 101, 102} : Finset ℕ) ↔ n = 100 ∨ n = 101 ∨ n = 102
        := by
  sorry

lemma CommGroup_of_comm_group
      [Group G]
      : (∀ (a b : G), a*b = b*a) -> CommGroup G := by
  intro h
  exact { mul_comm := h }

lemma both (f : α -> β) : a = b -> f a = f b := by
  intro h
  rw [h]

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
  have p : y*(x*y)^100 = (x*y)^100 * y := by
    apply MaddyGroupLemmas.mul_left_cancel x
    rw [<- mul_assoc, <- mul_assoc]
    conv =>
      rhs; lhs; rhs
      rw [h x y ⟨100, by simp⟩]
      simp
    have j : 100 + 1 = 101 := by rfl
    conv =>
      rhs
      rw [<- mul_assoc, <- pow_succ]
      rw [mul_assoc, pow_mul_comm', <- pow_succ]
      rw [j]
    conv =>
      lhs
      rw [<- pow_succ]
      rw [j]
    exact h x y ⟨101, by simp⟩
  apply MaddyGroupLemmas.mul_left_cancel x
  apply MaddyGroupLemmas.mul_right_cancel y
  apply MaddyGroupLemmas.mul_right_cancel ((x*y)^100)
  conv => rhs; rw [mul_assoc, p]

    /- x^101 * y^101 = (x*y)^101         := Eq.symm $ h x y ⟨101, sorry⟩ -/
    /- _             = x*y*(x*y)^100     := by rw [pow_succ] -/
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


