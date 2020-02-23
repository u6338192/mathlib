import tactic
import hotkeys

open tactic

example (P : bool → bool → Prop) : (∃ x : bool, ∀ y : bool, P x y)
  → ∀ y : bool, ∃ x : bool, P x y :=
begin
  intros h y,
  cases h with x h,
  use x,
  revert y,
  exact h,
end

example (P : bool → bool → bool → Prop) : (∃ x₁ : bool, ∀ y : bool, ∃ x₂ : bool, P x₁ y x₂)
  → ∀ y : bool, ∃ x₁ : bool, ∃ x₂ : bool, P x₁ y x₂ :=
begin
  intros h y,
  cases h with x h,
  use x,
  revert y,
  exact h,
end

example (P : bool → bool → bool → Prop) : (∃ x₁ : bool, ∃ x₂ : bool, ∀ y : bool, P x₁ x₂ y)
  → ∀ y : bool, ∃ x₁ : bool, ∃ x₂ : bool, P x₁ x₂ y :=
begin
  intros h y,
  cases h with x₁ h,
  cases h with x₂ h,
  use x₁,
  use x₂,
  revert y,
  exact h,
end

example (P : bool → bool → bool → bool → Prop) :
  (∃ x₁ : bool, ∀ y₁ : bool, ∃ x₂ : bool, ∀ y₂ : bool, P x₁ y₁ x₂ y₂)
  → ∀ y₁ : bool, ∀ y₂ : bool, ∃ x₁ : bool, ∃ x₂ : bool, P x₁ y₁ x₂ y₂ :=
begin
  intros h y₁ y₂,
  cases h with x₁ h,
  have o₁ : ∃ (x₂ : bool), ∀ (y₂ : bool), P x₁ y₁ x₂ y₂, from
  begin
    exact h y₁,
  end,
  cases o₁ with x₂ o₁,
  use x₁,
  use x₂,
  revert y₂,
  exact o₁,
end

example (P : bool → bool → bool → Prop) : (∃ x₁ : bool, ∃ x₂ : bool, ∀ y : bool, P x₁ y x₂)
  → ∀ y : bool, ∃ x₁ : bool, ∃ x₂ : bool, P x₁ y x₂ :=
begin
  intros h y,
  cases h with x₁ h,
  cases h with x₂ h,
  use x₁,
  use x₂,
  revert y,
  exact h,
end

example (P : bool → bool → bool → Prop) : (∃ x₁ : bool, ∃ x₂ : bool, ∀ y : bool, P x₁ y x₂)
  → ∃ x₁ : bool, ∀ y : bool, ∃ x₂ : bool, P x₁ y x₂ :=
begin
  intro h,
  cases h with x₁ h,
  cases h with x₂ h,
  use x₁,
  intro y,
  use x₂,
  revert y,
  exact h,
end

--This lemma not required
lemma push_in_foralls :
  (∀ (x₁ : bool), ∃ (y₁ : bool), ∀ (x₂ : bool), ∃ (y₂ : bool),
  x₁ ≠ tt ∧ ↥x₂ ∧ y₂ ≠ tt ∨ ↥y₁ ∧ x₂ ≠ tt ∧ ↥y₂) →
  (∀ (x₁ : bool), ∀ (x₂ : bool), ∃ (y₁ : bool), ∃ (y₂ : bool),
  x₁ ≠ tt ∧ ↥x₂ ∧ y₂ ≠ tt ∨ ↥y₁ ∧ x₂ ≠ tt ∧ ↥y₂) :=
begin
  intros h x₁ x₂,
  have o₁ : ∃ (y₁ : bool), ∀ (x₂ : bool), ∃ (y₂ : bool),
    x₁ ≠ tt ∧ ↥x₂ ∧ y₂ ≠ tt ∨ ↥y₁ ∧ x₂ ≠ tt ∧ ↥y₂, from h x₁,
  cases o₁ with y₁ o₁,
  have o₂ : ∃ (y₂ : bool),
    x₁ ≠ tt ∧ ↥x₂ ∧ y₂ ≠ tt ∨ ↥y₁ ∧ x₂ ≠ tt ∧ ↥y₂, from o₁ x₂,
  cases o₂ with y₂ o₂,
  use y₁,
  use y₂,
  exact o₂,
end

example :
  (∃ x₁ : bool, ∃ x₂ : bool, (x₁ ∨ ¬x₂) ∧ x₂) →
  (∃ x₁ : bool, ∀ y₁ : bool, ∃ x₂ : bool, ∀ y₂ : bool,
  (x₁ ∨ ¬x₂ ∨ y₂) ∧ (¬y₁ ∨ x₂ ∨ ¬y₂)) :=
begin
  intro h,
  cases h with x₁ h,
  cases h with x₂ h,
  use x₁,
  intro y₁,
  use x₂,
  intro y₂,
  split,
  {
    refine or.assoc.mp _,
    left,
    exact h.left,
  },
  {
    right,
    left,
    exact h.right,
  },
end

--note to go backwards the problem must be in DNF not CNF.
example :
  (∀ x₁ : bool, ∃ y₁ : bool, ∀ x₂ : bool, ∃ y₂ : bool,
  (¬x₁ ∧ x₂ ∧ ¬ y₂) ∨ (y₁ ∧ ¬x₂ ∧ y₂)) →
  (∀ x₁ : bool, ∀ x₂ : bool, (¬x₁ ∧ x₂) ∨ ¬x₂) :=
begin
  contrapose,
  intro h,
  push_neg at *,
  cases h with x₁ h,
  cases h with x₂ h,
  use x₁,
  intro y₁,
  use x₂,
  intro y₂,
  split,
  {
    refine or.assoc.mp _,
    left,
    exact h.left,
  },
  {
    right,
    left,
    exact h.right,
  },
end

example : (∀ x₁ : bool, ∀ x₂ : bool, (¬x₁ ∧ x₂) ∨ ¬x₂) →
  ∀ x₁ : bool, ∃ y₁ : bool, ∀ x₂ : bool, ∃ y₂ : bool,
  (¬x₁ ∧ x₂ ∧ ¬y₂) ∨ (y₁ ∧ ¬x₂ ∧ y₂) :=
begin
  intro h,
  intro x₁,
  use tt,
  intro x₂,
  cases h x₁ x₂ with h,
  {
    use ff,
    left,
    tauto,
  },
  {
    use tt,
    right,
    tauto,
  },
end

example (U V : Type) (P : U → Prop) (Q : V → Prop) :
(∀ x : U, P x) ∨ (∀ y : V, Q y) ↔ ∀ (x : U) (y : V), P x ∨ Q y :=
begin
  split,
  {
    intro h,
    intros x y,
    cases h,
    { left, exact h x, },
    { right, exact h y, },
  },
  {
    intro  h,
    classical,
    by_cases h₁ : (∀ (x : U), P x),
    { left, exact h₁, },
    {
      right,
      push_neg at h₁,
      cases h₁ with x h₁,
      intro y,
      have o : P x ∨ Q y, from h x y,
      cases o,
      { exfalso, exact h₁ o, },
      { exact o, },
    },
  },
end
