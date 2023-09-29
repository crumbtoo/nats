import Mathlib.Logic.Basic
--------------------------------------------------------------------------------
namespace Logic
--------------------------------------------------------------------------------

theorem existential_negation {p : x -> Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  have pa : (¬ ∃ x, p x) -> (∀ x, ¬ p x) := by
    intro ha w hb
    apply ha
    exact ⟨w, hb⟩
  have pb : (∀ x, ¬ p x) -> (¬ ∃ x, p x) := by
    intro ha hb
    apply Exists.elim hb $ λ w => by
      exact ha w
  exact ⟨pa, pb⟩ 

theorem not_not {a : Prop} : ¬ ¬ a ↔ a := by
  have p : ¬ ¬ a -> a := of_not_not
  have q : a -> ¬ ¬ a := by
    rw [Not, Not]
    intro x h
    apply h
    exact x
  exact ⟨p, q⟩ 

