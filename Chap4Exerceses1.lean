open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h : ∃ x : α, r =>
    match h with
      | ⟨_, hw⟩ => hw

example (a : α) : r → (∃ x : α, r) :=
  fun h2 : r =>
    Exists.intro a h2

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  have h1 :=
    fun h2 : (∃ x, p x ∧ r) =>
      match h2 with |
        ⟨w, h2w⟩ => ⟨⟨w, h2w.left⟩, h2w.right⟩
  have h2 :=
    fun h3 : (∃ x, p x) ∧ r =>
      ⟨h3.left, ⟨,h3.right⟩⟩
  Iff.intro h1 h2

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
