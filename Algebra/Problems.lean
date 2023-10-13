import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Logic.Nonempty
import Algebra.Lemmas.Group
--------------------------------------------------------------------------------
namespace Problems
open Group
open Monoid
--------------------------------------------------------------------------------

section HoldenGroupProblem

def MulPow (G : Type) [Group G] (n : ℕ) (a b : G) := (a*b)^n = a^n * b^n

theorem mul_pow_implies_comm
        [Group G] (i : ℕ)
        : ∀ (a b : G), MulPow G i a b ∧ MulPow G (i+1) a b ∧ MulPow G (i+2) a b
          -> Commute a b
        := by
  intro a b ⟨powi, powj, powk⟩
  let j := i + 1
  conv at powj in (i+1) => change j

  have lem₁ : (a*b)^j*a = a*(a*b)^j := by
    rw [powj]
    apply MaddyGroupLemmas.mul_right_cancel b
    conv =>
      congr
      · rw [mul_assoc _ a b]
        rw [<- powj]
        rw [<- pow_succ']
      · rw [<- mul_assoc, mul_assoc _]
        congr
        · rw [<- pow_succ]
        · rw [<- pow_succ']
    exact powk

  apply Eq.symm
  apply MaddyGroupLemmas.mul_left_cancel (a^i*b^i)
  conv => rhs; rw [<- powi, <- pow_succ']
  conv in (i+1) => change j
  rw [powj]
  have hi : b^i*b*a = a*b^j -> a^i*b^i*(b*a) = a^j*b^j := by
    intro ha
    apply MaddyGroupLemmas.mul_left_cancel (a^i)⁻¹
    conv =>
      lhs
      rw [mul_assoc, <- mul_assoc, mul_left_inv, one_mul]
      rw [<- mul_assoc, <- pow_succ']
      pattern (i+1); change j
    conv =>
      rhs
      rw [pow_succ', <- mul_assoc, <- mul_assoc, mul_left_inv, one_mul]
    rw [<- pow_succ'] at ha
    conv at ha in (i+1) => change j
    exact ha
  apply hi
  rw [<- pow_succ']
  conv in (i+1) => change j
  apply MaddyGroupLemmas.mul_left_cancel (a^j)
  apply MaddyGroupLemmas.mul_right_cancel b
  rw [<- mul_assoc, <- powj]
  rw [mul_assoc, <- pow_succ']
  conv =>
    rhs; rw [<- mul_assoc, Commute.pow_left]
    lhs; rw [mul_assoc, <- powj, <- lem₁]
  rw [mul_assoc, <- pow_succ']

-- Suppose G is a group where (ab)ⁿ = aⁿbⁿ for all a, b ∈ G and n ∈ {100, 101,
-- 102}. Prove that G is abelian.
example [Group G]
        : ∀ (a b : G), 
            (∀ (n : ({100, 101, 102} : Finset ℕ)),
              (a*b)^↑↑n = a^↑↑n * b^↑↑n)
        -> a*b = b*a
        := by
  intro a b h
  have hi : (a*b)^100 = a^100*b^100 := h ⟨100, by simp⟩
  have hj : (a*b)^101 = a^101*b^101 := h ⟨101, by simp⟩
  have hk : (a*b)^102 = a^102*b^102 := h ⟨102, by simp⟩
  exact mul_pow_implies_comm 100 a b ⟨hi, hj, hk⟩ 

end HoldenGroupProblem
--------------------------------------------------------------------------------

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

namespace DFAA117

-- Let G = { z ∈ ℂ | ∃ (n ∈ ℕ) : zⁿ = 1 }
--  (a) Prove that G is a group under multiplication
--  (b) Prove that G is not a group under addition

def G := { z : ℂ // ∃ (n : ℕ), z^n = 1 }

noncomputable def zangle : G -> ℝ := by
  intro ⟨z, _⟩
  exact Real.arctan (z.im / z.re)

theorem z_is_rational : ∀ (a : G), ∃ (q : ℚ), zangle a = q * π := by
  intro a
  let w := Classical.arbitrary ℚ
  sorry

/- def mul : G -> G -> G := by -/
/-   intro ⟨a, pa⟩ ⟨b, pb⟩ -/

/- theorem mul_one (a : G) : a * 1 := by -/
/-   sorry -/

end DFAA117

