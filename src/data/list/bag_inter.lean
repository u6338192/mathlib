import data.list.basic
import tactic.chain
import tactic.auto_cases
import tactic.tidy
import tactic.squeeze

open list
open nat

variables {α : Type*} [decidable_eq α]

local attribute [simp] min_succ_succ count_cons erase_cons count_erase

lemma foo {a : α} {L : list α} (h : a ∈ L) (n : ℕ) : succ (min n (pred (count a L))) = min (succ n) (count a L) :=
begin
  rw ←nat.min_succ_succ,
  rw nat.succ_pred_eq_of_pos,
  exact count_pos.2 h
end

open tactic

@[simp] theorem count_bag_inter' {a : α} :
  ∀ {l₁ l₂ : list α}, count a (l₁.bag_inter l₂) = min (count a l₁) (count a l₂)
| []         l₂ := by simp
| l₁         [] := by simp
| (h₁ :: l₁) (h₂ :: l₂) :=
begin
  simp only [list.bag_inter],
  dsimp at *,
  tactic.tidy.simp_non_aux,
  split_ifs,
  tactic.tidy.simp_non_aux,
  split_ifs,
  refl,
  simp,
  split_ifs,
  { tidy? },
  { tidy? },
  -- tidy?,

  rw foo h,

  rw decidable.not_or_iff_and_not at h,
  have w : a ∉ l₂ := h.right,
  rw count_eq_zero_of_not_mem w,
  simp,
  -- sorry,
  -- sorry,
end
-- using_well_founded
-- { rel_tac := λ _ _, tactic.apply_instance,
--   dec_tac := tactic.target >>= tactic.trace >> tactic.assumption, }
