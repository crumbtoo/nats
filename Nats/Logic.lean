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

