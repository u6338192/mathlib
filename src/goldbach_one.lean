import data.nat.basic
import data.nat.prime
import hotkeys

open nat

example (n : ℕ) (h₁ : n ≤ 6) : ∃ p₁ p₂ : ℕ, prime p₁ ∧ prime p₂ ∧ p₁ + p₂ = 2 * n :=
begin
  sorry
end

lemma wtf_contra (A B : Prop) (H : A → B) : ¬ B → ¬ A  := mt H

lemma wtf_rfl (a b : ℕ) (h₁ : ¬(a = b)) : a ≠ b := h₁

lemma twins_if_special_function (n : ℕ) (h₁ : 6 ≤ n) (f : ℕ → ℕ) (h₂ : 1 ≤ f n)
  (h₃ : ∀ m c : ℕ, c ≠ 1 → m ≠ 1 → n + f n + 1 ≠ m * c)
  (h₄ : ∀ m c : ℕ, c ≠ 1 → m ≠ 1 → n + f n - 1 ≠ m * c)
  : ∃ m : ℕ, n < m ∧ prime (m-1) ∧ prime (m+1) :=
begin
  split, split, swap, split, fsplit, swap, intros, right,
  work_on_goal 2 { fsplit, swap, intros, right, },
  work_on_goal 5 { use n + (f n), },
  work_on_goal 4 { exact lt_add_of_pos_right n h₂ },
  work_on_goal 1 {
    have o₁ : 2 ≤ 6, from by norm_num,
    have o₂ : 2 ≤ n, from le_trans o₁ h₁,
    have o₃ : 2 ≤ n + (f n - 1), from le_add_right o₂,
    have o₄ : 2 < n + (f n), from lt_add_of_le_of_pos o₂ h₂,
    exact le_pred_of_lt o₄,
  },
  work_on_goal 2 {
    have o₁ : 2 ≤ 6, from by norm_num,
    have o₂ : 2 ≤ n, from le_trans o₁ h₁,
    show 2 ≤ n + (f n + 1), from le_add_right o₂,
  },

  --This should probably be factored out into it's own lemma
  dsimp [(∣)] at H, revert H, contrapose, push_neg, intros, apply wtf_rfl, intro,
  have w₁ : m ≠ m * c, from ne_of_ne_of_eq a a_1,
  have w₂ : c ≠ 1, from
  begin
    intro,
    rw a_2 at w₁,
    rw mul_one at w₁,
    exact a (false.rec (m = n + f n - 1) (w₁ rfl)),
  end,
  have w₃ : m = 1, from
  begin
    have o₁ : m ≠ 1 → n + f n - 1 ≠ m * c, from h₄ m c w₂,
    have o₂ : ¬n + f n - 1 ≠ m * c → ¬m ≠ 1, from mt (h₄ m c w₂),
    have o₃ : n + f n - 1 = m * c → m = 1, from begin push_neg at o₂, exact o₂ end,
    exact o₃ a_1,
  end,
  rw w₃ at a_1,
  rw w₃ at h₄,


  swap,

  --This should probably be factored out into it's own lemma
  dsimp [(∣)] at H, revert H, contrapose, push_neg, intros, apply wtf_rfl, intro,
  have w₁ : m ≠ m * c, from ne_of_ne_of_eq a a_1,
  have w₂ : c ≠ 1, from
  begin
    intro,
    rw a_2 at w₁,
    rw mul_one at w₁,
    exact a (false.rec (m = n + f n + 1) (w₁ rfl)),
  end,
  have w₃ : m = 1, from
  begin
    have o₁ : m ≠ 1 → n + f n + 1 ≠ m * c, from h₃ m c w₂,
    have o₂ : ¬n + f n + 1 ≠ m * c → ¬m ≠ 1, from mt (h₃ m c w₂),
    have o₃ : n + f n + 1 = m * c → m = 1, from begin push_neg at o₂, exact o₂ end,
    exact o₃ a_1,
  end,


end

lemma exists_fn (n : ℕ) : ∃ f : ℕ → ℕ,
  (∀ m c : ℕ, c ≠ 1 → m ≠ 1 → n + f n + 1 ≠ m * c) ∧
  (∀ m c : ℕ, c ≠ 1 → m ≠ 1 → n + f n - 1 ≠ m * c) :=
begin
  split, split,

  intro,

  swap,

  intro,
end

theorem twin_primes (n : ℕ) (h₁ : 6 ≤ n) : ∃ m : ℕ, n < m ∧ prime (m-1) ∧ prime (m+1) :=
begin
  refine twins_if_special_function n h₁ _ _ _ _,


end
