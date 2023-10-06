import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Data.Finset.Basic
import Algebra.Lemmas.Group
--------------------------------------------------------------------------------
namespace Problems
--------------------------------------------------------------------------------

lemma elem_or_eq {n : ℕ}
        : n ∈ ({100, 101, 102} : Finset ℕ) ↔ n = 100 ∨ n = 101 ∨ n = 102
        := by
  sorry

def Commutative (G : Type) [Group G] := ∀ (a b : G), a*b = b*a

lemma commutative_group_is_CommGroup [Group G]
      (h : Commutative G)
      : CommGroup G
      :=
  { mul_comm := h }

-- Suppose G is a group where (ab)ⁿ = aⁿbⁿ for all a, b ∈ G and n ∈ {100, 101,
-- 102}. Prove that G is abelian.
example [Group G]
        : ∀ (a b : G) (n : ({100, 101, 102} : Finset ℕ)),
          (a*b)^↑↑n = a^↑↑n * b^↑↑n
          -> Commutative G
        := by
  intro a b n
  have i : n.val = 100 ∨ n.val = 101 ∨ n.val = 102 := by
    have j := n.property
    rw [elem_or_eq] at j
    exact j
  contrapose
  intro h
  sorry

