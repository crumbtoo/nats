import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Data.Finset.Basic
import Algebra.Lemmas.Group
--------------------------------------------------------------------------------
namespace Problems
--------------------------------------------------------------------------------

def Abelian (T : Type*) [Group T] := ∀ (a b : T), a*b = b*a
def AbelianAdd (T : Type*) [AddGroup T] := ∀ (a b : T), a+b = b+a

lemma elem_or_eq {n : ℕ}
        : n ∈ ({100, 101, 102} : Finset ℕ) ↔ n = 100 ∨ n = 101 ∨ n = 102
        := by
  sorry

-- Suppose G is a group where (ab)ⁿ = aⁿbⁿ for all a, b ∈ G and n ∈ {100, 101,
-- 102}. Prove that G is abelian.
example [Group G]
        : ∀ (a b : G) (n : ({100, 101, 102} : Finset ℕ)),
        (a*b)^↑↑n = a^↑↑n * b^↑↑n
        -> CommGroup G
        := by
  intro a b n h
  have i : n.val = 100 ∨ n.val = 101 ∨ n.val = 102 := by
    have j := n.property
    rw [elem_or_eq] at j
    exact j

  rw [elem_or_eq] at n


