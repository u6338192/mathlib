import hotkeys

open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
begin
  intro,
  cases a,
  exact a_h,
end

example : r → (∃ x : α, r) :=
λ b, exists.intro a b --tactic mode can't see the variable a : α?

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
begin
  split,
  {
    intro,
    split,
    {
      cases a,
      exact exists.intro a_w a_h.left,
    },
    {
      cases a,
      exact a_h.right,
    },
  },
  {
    intro,
    cases a,
    cases a_left,
    split,
    swap,
    exact a_left_w,
    exact ⟨a_left_h, a_right⟩,
    --exact exists.intro a_left_w ⟨a_left_h, a_right⟩,
  },
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin
  split,
  {
    intro,
    cases a,
    cases a_h,
    {
      left,
      split,
      swap,
      exact a_w,
      exact a_h,
    },
    {
      right,
      split,
      swap,
      exact a_w,
      exact a_h,
    },
  },
  {
    intro,
    cases a,
    {
      cases a,
      split,
      swap,
      exact a_w,
      left,
      exact a_h,
    },
    {
      cases a,
      split,
      swap,
      exact a_w,
      right,
      exact a_h,
    },
  },
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
  split,
  {
    intro,
    intro,
    cases a_1,
    have s₁ : p a_1_w, from a a_1_w,
    exact a_1_h (a a_1_w),
  },
  {
    intros,
    push_neg at a,
    exact a x,
  },
end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
begin
  split,
  {
    intro,
    intro,
    cases a,
    have o₁ : ¬p a_w, from by exact a_1 a_w,
    exact a_1 a_w a_h,
  },
  {
    intro,
    push_neg at a,
    exact a,
  },
end

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
  split,
  {
    intro,
    push_neg at a,
    exact a,
  },
  {
    intro,
    push_neg,
    exact a,
  },
end

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
begin
  split,
  {
    intro,
    push_neg at a,
    exact a,
  },
  {
    intro,
    push_neg,
    exact a,
  },
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
begin
  split,
  {
    intros,
    cases a_1,
    exact a a_1_w a_1_h,
  },
  {
    intros,
    have s₁ : ∃ (x : α), p x, from begin
      split,
      swap,
      exact x,
      exact a_1,
    end,
    exact a s₁,
  },
end

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
begin
  split,
  {
    intros b c,
    cases b,
    exact b_h (c b_w),
  },
  {
    have s₁ : (∀ (x : α), p x) ∨ ¬(∀ (x : α), p x), from em (Π (x : α), p x),
    intro,
    cases s₁,
    { exact ⟨a, λ _, a_1 s₁⟩, },
    {
      push_neg at s₁,
      cases s₁,
      split,
      swap,
      { exact s₁_w, },
      {
        intros,
        exact absurd a_2 s₁_h,
      },
    },
  },
end

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
begin
  split,
  {
    intros b c,
    cases b,
    exact b_h (c b_w),
  },
  {
    intro,
    have o₂ : ¬¬(∃ (x : α), p x → r) → (∃ (x : α), p x → r), from
    begin
      intro,
      push_neg at a_2,
      exact a_2,
    end,
    apply o₂,
    intro,
    push_neg at a_2,
    have o₃ : ∀ (x : α), p x, from λ x, (a_2 x).left,
    have o₄ : r, from a_1 o₃,
    have o₅ : ¬ r, from (a_2 a).right,
    exact o₅ (a_1 o₃),
  },
end

example (b : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
begin
  split,
  {
    intros,
    cases a,
    have o₁ : p a_w, from a_h a_1,
    split,
    swap,
    exact a_w,
    exact o₁,
  },
  {
    intro,
    have o₂ : ¬¬(∃ (x : α), r → p x) → (∃ (x : α), r → p x), from
    begin
      intro,
      push_neg at a_1,
      exact a_1,
    end,
    apply o₂,
    intro,
    push_neg at a_1,
    have o₃ : r ∧ ¬ p b, from a_1 b,
    have o₄ : ∃ (x : α), p x, from
    begin
      apply a,
      exact o₃.left,
    end,
    have o₅ : ∀ (c : α), ¬p c, from
    begin
      intro,
      exact set.not_mem_of_mem_diff (a_1 c),
    end,
    cases o₄,
    have o₆ : ¬ (p o₄_w), from o₅ o₄_w,
    exact o₅ o₄_w o₄_h,
  },
end
