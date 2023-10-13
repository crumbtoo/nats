import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.OrderOfElement
--------------------------------------------------------------------------------

example [Group G] (a : G) : a^2 = 1 ↔ orderOf a = 1 ∨ orderOf a = 2 := by
  have p : a^2 = 1 -> orderOf a = 1 ∨ orderOf a = 2 := by
    intro ha
    let n : ℕ := orderOf a
    conv =>
      congr
      · lhs; change n
      · lhs; change n
    sorry

  have q : orderOf a = 1 ∨ orderOf a = 2 -> a^2 = 1 := by
    sorry
  exact ⟨p, q⟩

