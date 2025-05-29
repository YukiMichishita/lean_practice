variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
    have hp : (h: p ∧ q) → (q ∧ p) := fun (h : p ∧ q) => ⟨ h.right, h.left ⟩
    have hq := fun (h : q ∧ p) => ⟨ h.right, h.left ⟩
    Iff.intro
        hp
        hq

example : p ∨ q ↔ q ∨ p :=
    have h₅ : p → p ∨ q := fun (hp : p) => Or.inl hp
    have h₆ : q → p ∨ q := fun (hp :  q) => Or.inr hp
    have h₁ : p → q ∨ p := fun (hp : p) => Or.inr hp
    have h₂ : q → q ∨ p := fun (hq : q) => Or.inl hq
    have h₃ : p ∨ q → q ∨ p :=
        fun (hp : p ∨ q) => show q ∨ p from hp.elim h₁ h₂
    have h₄ : q ∨ p → p ∨ q :=
        fun (hp : q ∨ p) => show p ∨ q from  hp.elim h₆ h₅
    Iff.intro h₃ h₄

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    have h₁ := fun (hp : (p ∧ q) ∧ r) => ⟨ hp.left.left, ⟨ hp.left.right, hp.right ⟩ ⟩
    have h₂ := fun (hp : p ∧ (q ∧ r)) => ⟨ ⟨hp.left,  hp.right.left⟩, hp.right.right  ⟩
    Iff.intro h₁ h₂


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    have h₁ : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
        fun (hp : (p ∨ q) ∨ r) =>
        hp.elim
            (fun (hp₁ : (p ∨ q)) =>
                hp₁.elim
                    (fun(hp₂ : p) => show p ∨ (q ∨ r) from Or.inl hp₂)
                    (fun(hp₂ : q) => show p ∨ (q ∨ r) from Or.inr (Or.inl hp₂)))
            (fun (hp₁ : r) => show p ∨ (q ∨ r) from  Or.inr (Or.inr hp₁))
    have h₂ : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
        fun (hp : p ∨ (q ∨ r)) =>
        hp.elim
            (fun (h₁ : p) => show (p ∨ q) ∨ r from Or.inl (Or.inl h₁))
            (fun (h₂ : (q ∨ r)) =>
                h₂.elim
                (fun(h₃ : q) => show (p ∨ q) ∨ r from Or.inl (Or.inr h₃))
                (fun(h₃ : r) => show (p ∨ q) ∨ r from Or.inr h₃))
    Iff.intro h₁ h₂

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    have h₁ : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
        fun (h : p ∧ (q ∨ r)) =>
            h.right.elim
                (fun(hq : q) => show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨h.left, hq⟩)
                (fun(hr : r) => show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨h.left, hr⟩)
    have h₂ : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := sorry
    Iff.intro h₁ h₂

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
