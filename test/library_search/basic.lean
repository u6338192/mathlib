/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.nat.basic

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true
/- For debugging purposes, we can display the list of lemmas: -/
-- set_option trace.suggest true

namespace test.library_search

-- Check that `library_search` fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { library_search },
end

-- Verify that `library_search` solves goals via `solve_by_elim` when the library isn't
-- even needed.
example (P : Prop) (p : P) : P :=
by library_search
example (P : Prop) (p : P) (np : ¬P) : false :=
by library_search
example (X : Type) (P : Prop) (x : X) (h : Π x : X, x = x → P) : P :=
by library_search

def lt_one (n : ℕ) := n < 1
lemma zero_lt_one (n : ℕ) (h : n = 0) : lt_one n := by subst h; dsimp [lt_one]; simp
-- Verify that calls to solve_by_elim to discharge subgoals use `rfl`
example : lt_one 0 :=
by library_search

example (α : Prop) : α → α :=
by library_search -- says: `exact id`

example (p : Prop) [decidable p] : (¬¬p) → p :=
by library_search -- says: `exact not_not.mp`

example (a b : Prop) (h : a ∧ b) : a :=
by library_search -- says: `exact h.left`

example (P Q : Prop) [decidable P] [decidable Q]: (¬ Q → ¬ P) → (P → Q) :=
by library_search -- says: `exact not_imp_not.mp`

example (a b : ℕ) : a + b = b + a :=
by library_search -- says: `exact add_comm a b`

example {a b : ℕ} : a ≤ a + b :=
by library_search -- says: `exact nat.le.intro rfl`

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- says: `exact nat.mul_sub_left_distrib n m k`

example (n m k : ℕ) : n * m - n * k = n * (m - k) :=
by library_search -- says: `exact eq.symm (nat.mul_sub_left_distrib n m k)`

example {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
by library_search -- says: `exact nat.le_pred_of_lt h`

example {α : Type} (x y : α) : x = y ↔ y = x :=
by library_search -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
by library_search -- says: `exact add_pos ha hb`

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
by library_search -- says: `exact add_pos`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by library_search -- says: `exact nat.le_of_dvd w h`


-- We even find `iff` results:

example : ∀ P : Prop, ¬(P ↔ ¬P) :=
by library_search -- says: `λ (a : Prop), (iff_not_self a).mp`

example {a b c : ℕ} (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c :=
by library_search -- exact mul_dvd_mul_left a w

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
by library_search -- says `exact (nat.dvd_add_left h₁).mp h₂`

-- We have control of how `library_search` uses `solve_by_elim`.

-- In particular, we can add extra lemmas to the `solve_by_elim` step
-- (i.e. for `library_search` to use to attempt to discharge subgoals
-- after successfully applying a lemma from the library.)
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search [add_lt_add], -- Says: `exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end

-- We can also use attributes:
meta def ex_attr : user_attribute := {
  name := `ex,
  descr := "A lemma that should be applied by `library_search` when discharging subgoals."
}

run_cmd attribute.register ``ex_attr

attribute [ex] add_lt_add

example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  suggest with ex,
  library_search with ex, -- Says: `exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end

example (a b : ℕ) (h : 0 < b) : (a * b) / b = a :=
by library_search -- Says: `exact nat.mul_div_left a h`

example (a b : ℕ) (h : b ≠ 0) : (a * b) / b = a :=
begin
  success_if_fail { library_search },
  library_search [nat.pos_iff_ne_zero.mpr],
end

-- Checking examples from issue #2220
example {α : Sort*} (h : empty) : α :=
by library_search

example {α : Type*} (h : empty) : α :=
by library_search

def map_from_sum {A B C : Type} (f : A → C) (g : B → C) : (A ⊕ B) → C := by library_search

end test.library_search
