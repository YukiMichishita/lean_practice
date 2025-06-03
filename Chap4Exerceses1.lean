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
      match h3 with |
        ⟨⟨h4, h5⟩, h6⟩ => ⟨h4, ⟨h5, h6⟩⟩
  Iff.intro h1 h2

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  have h1 :=
    fun h2 : (∃ x, p x ∨ q x) =>
      match h2 with
        | ⟨h3, h4⟩ =>
          Or.elim h4
            (fun h5 : p h3 => Or.inl (Exists.intro h3 h5))
            (fun h6 : q h3 => Or.inr (Exists.intro h3 h6))
  have h2 :=
    fun h3 : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h3
        (fun h4 =>
          match h4 with
           | ⟨h5, h6⟩ => ⟨h5, Or.inl h6⟩)
        (fun h4 =>
          match h4 with
           | ⟨h5, h6⟩ => ⟨h5, Or.inr h6⟩)
  Iff.intro h1 h2

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  have h1 :=
    fun h2 => fun h3 =>
      sorry
  have h2 := sorry
  Iff.intro h1 h2

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

theorem t1 (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
theorem t2 : α → ((∃ x, r → p x) ↔ (r → ∃ x, p x)) := t1
