import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
--------------------------------------------------------------------------------

namespace DFAA117

open Complex

-- Let G = { z ∈ ℂ | ∃ (n ∈ ℕ) : zⁿ = 1 }
--  (a) Prove that G is a group under multiplication
--  (b) Prove that G is not a group under addition

def GP (z : ℂ) := ∃ (n : ℕ+), z^n = 1

def G := { z : ℂ // GP z }

theorem g_euler {z : ℂ} : GP z -> ∃ (x : ℝ), exp (I * x) = z := by
  sorry

theorem mul_closed (a b : ℂ) (ha : GP a) (hb : GP b) : GP (a*b) := by
  let a' := Exists.choose $ g_euler ha
  sorry

def mul : G -> G -> G := by
  intro ⟨a, pa⟩ ⟨b, pb⟩
  sorry

/- theorem mul_one (a : G) : a * 1 := by -/
/-   sorry -/

end DFAA117

