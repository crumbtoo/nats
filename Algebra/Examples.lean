import Mathlib.Data.Finset.Basic
--------------------------------------------------------------------------------
open MyGroup
namespace Examples
--------------------------------------------------------------------------------

namespace ProductGroup
section

variable {G H : Type*} [Group G] [Group H]

def pg_mul : G × H -> G × H -> G × H := by
  intro ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
  exact ⟨g₁ * g₂, h₁ * h₂⟩ 

instance : Mul (G × H) where
  mul := pg_mul

theorem pg_mul_assoc (a b c : G × H) : a * b * c = a * (b * c) := by
  sorry

instance : Group (G × H) where
  mul := pg_mul
  mul_assoc := pg_mul_assoc
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry

end
end ProductGroup

