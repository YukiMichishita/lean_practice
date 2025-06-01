open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : (p → q ∨ r) =>
      byCases
        (fun h₁ : p =>
          Or.elim (show (q ∨ r) from h h₁)
            (fun h₂ : q => show  (p → q) ∨ (p → r) from Or.inl (fun _ => h₂))
            (fun h₂ : r => show  (p → q) ∨ (p → r) from Or.inr (fun _ => h₂))
        )
        (fun h₁ : ¬p =>
          Or.inl (show (p → q) from fun h₂ : p => absurd h₂ h₁)
        )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
    byCases
      (fun h₁ : p =>
        Or.inr (fun h₂ : q => show False from h ⟨h₁, h₂⟩)
      )
      Or.inl

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example : ¬(p → q) → p ∧ ¬q :=
  fun h₁ : ¬(p → q) =>
    byCases
      (fun h₂ : p =>
        have h₄ : ¬q :=
        byContradiction (fun h₃ : ¬¬q => absurd (fun _ => dne h₃) h₁)
        ⟨h₂, h₄⟩
      )
      (fun h₂ : ¬p =>
        have h₃ : ¬p → (p → q) :=
          fun h₄ : ¬p => fun h₅ : p => show q from absurd h₅ h₄
        absurd (h₃ h₂) h₁
      )

example : (p → q) → (¬p ∨ q) :=
  fun h₁ : p → q =>
    byCases
      (fun h₂ : p => Or.inr (h₁ h₂))
      Or.inl

example : (¬q → ¬p) → (p → q) :=
  fun h₁ : ¬q → ¬p =>
    byCases
      (fun h₂ : q => fun _ => h₂)
      (fun h₂ : ¬q =>
        fun h₃ : p => show q from absurd h₃ (h₁ h₂))

example : p ∨ ¬p :=
  have h₁ : ¬¬(p ∨ ¬p) :=
    fun h₂ : ¬(p ∨ ¬p) =>
      have h₃ : ¬p := fun h₄ : p => show False from h₂ (Or.inl h₄)
      h₂ (Or.inr h₃)
  dne h₁

example : (((p → q) → p) → p) :=
  fun h₁ : (p → q) → p =>
    byCases
      id
      (fun h₂ : ¬p =>
        have h₃ : ¬p → p → q := fun h₄ : ¬p => fun h₅ : p => absurd h₅ h₄
        h₁ (h₃ h₂)
      )
