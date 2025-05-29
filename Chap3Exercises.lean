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
    have h₂ : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
        fun (h : (p ∧ q) ∨ (p ∧ r)) =>
            h.elim
                (fun(h₁: (p ∧ q)) => ⟨h₁.left, Or.inl h₁.right⟩)
                (fun(h₂: (p ∧ r)) => ⟨h₂.left, Or.inr h₂.right⟩)
    Iff.intro h₁ h₂

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    have h₁ : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
        fun(h:p ∨ (q ∧ r)) =>
            h.elim
                (fun(h₂:p) => ⟨Or.inl h₂, Or.inl h₂⟩)
                (fun(h₃:q ∧ r) => ⟨Or.inr h₃.left, Or.inr h₃.right⟩)
    have h₂ : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
        have hl: (hl₁:p) → (p ∨ (q ∧ r)) := fun(hl₁:p) => Or.inl hl₁
        fun(h:(p ∨ q) ∧ (p ∨ r)) =>
            h.left.elim
                (hl)
                (fun(h₄:q) =>
                    h.right.elim
                        (hl)
                        (fun(h₆:r) => Or.inr ⟨h₄, h₆⟩)
                )
    Iff.intro h₁ h₂

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) :=
    have h₁ : (p → (q → r)) → (p ∧ q → r) :=
        fun(h₁:p → (q → r)) => (fun (h₂:p ∧ q) => h₁ h₂.left h₂.right)
    have h₂ : (p ∧ q → r) → (p → (q → r)) :=
        fun (h₁:p ∧ q → r) => (fun (h₂:p) => (fun(h₃:q) => h₁ ⟨h₂, h₃⟩))
    Iff.intro h₁ h₂

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    have h₁ : ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
        fun h₁:(p ∨ q → r) =>
            have h₂ := fun h:p => h₁ (Or.inl h)
            have h₃ := fun h:q => h₁ (Or.inr h)
            ⟨h₂,h₃⟩
    have h₂ : (p → r) ∧ (q → r) →  ((p ∨ q) → r) :=
        fun h₁: (p → r) ∧ (q → r) =>
            fun h₂: p ∨ q =>
                h₂.elim
                    (fun h₃:p => h₁.left h₃)
                    (fun h₃:q => h₁.right h₃)
    Iff.intro h₁ h₂

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    have h₁ :=
        fun h₂ : ¬(p ∨ q) =>
            have np := fun h₃ : p => show False from h₂ (Or.inl h₃)
            have nq := fun h₃ : q => show False from  h₂ (Or.inr h₃)
            ⟨np,nq⟩
    have h₂ :=
        fun h₂ : ¬p ∧ ¬q =>
            fun h₃ : p ∨ q =>
                h₃.elim
                    (fun h₄: p => show False from h₂.left h₄)
                    (fun h₄: q => show False from h₂.right h₄)
    Iff.intro h₁ h₂

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h: ¬p ∨ ¬q =>
        fun h₂: p ∧ q =>
            h.elim
                (fun h₃:¬p => show False from h₃ h₂.left)
                (fun h₃:¬q => show False from h₃ h₂.right)

example : ¬(p ∧ ¬p) :=
    fun h: p ∧ ¬p =>
        show False from h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
    fun h: p ∧ ¬q =>
        fun h₂: p → q =>
            show False from h.right (h₂ h.left)

example : ¬p → (p → q) :=
    fun h₁: ¬p =>
        fun h₂: p =>
            absurd h₂ h₁

example : (¬p ∨ q) → (p → q) :=
    fun h₁: ¬p ∨ q =>
        fun h₂: p =>
            h₁.elim
                (fun h₃:¬p => absurd h₂ h₃)
                id

example : p ∨ False ↔ p :=
    have r := fun h₁: p ∨ False =>
        h₁.elim
            (show p → p from id)
            (show False → p from (fun f:False => f.elim))
    have l := fun h₁: p => Or.inl h₁
    Iff.intro r l

example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
