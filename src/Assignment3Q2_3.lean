import data.multiset
import algebra.group
import tactic.basic data.num.lemmas data.list.basic
import hotkeys

variable α : Type

@[derive has_reflect]
inductive comm_semi_group_expr (α : Type)
| const : α → comm_semi_group_expr
| comp : comm_semi_group_expr → comm_semi_group_expr → comm_semi_group_expr

open comm_semi_group_expr

def to_list : comm_semi_group_expr α → list α
| (const a)        := [a]
| (comp exp1 exp2) := (to_list exp1) ++ (to_list exp2)

def to_multiset : comm_semi_group_expr α → multiset α
| (const a)        := {a}
| (comp exp1 exp2) := (to_multiset exp1) + (to_multiset exp2)

def eval [comm_semigroup α] : comm_semi_group_expr α → α
| (const a) := a
| (comp exp1 exp2) := (eval exp1) * (eval exp2)

def len [comm_semigroup α] (e : comm_semi_group_expr α) := (to_multiset α e).card

lemma length_split [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  : len α (comp e₁ e₂) = len α e₁ + len α e₂ :=
begin
  unfold len,
  unfold to_multiset,
  exact multiset.card_add (to_multiset α e₁) (to_multiset α e₂),
end

@[simp] lemma length_set [comm_semigroup α] (e : comm_semi_group_expr α) (h : len α e = 1)
  : ∃ a : α, to_multiset α e = {a} :=
begin
  induction e with e ha hb hc hd,
  { use e, refl, },
  { exact multiset.card_eq_one.mp h, },
end

lemma eval_singleton [comm_semigroup α] (a : α) (e : comm_semi_group_expr α)
  (h : to_multiset α e = {a}) : eval α e = a :=
begin
  have o₁ : e = const a, from
  begin
    cases e,
    {
      have o₂ : to_multiset α (const e) = {e}, from rfl,
       have o₃ : {a} = {e}, from
      begin
        rw ←o₂,
        rw ←h,
      end,
      have o₄ : a = e, from multiset.singleton_inj.mp (eq.symm h),
      rw o₄,
    },
    {
      sorry,
    },
  end,
  rw o₁,
  refl,
end

lemma main_thm_aux [comm_semigroup α] (n : ℕ) (h₀ : 1 ≤ n) (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  (h₁ : n = len α e₁)
  : x₁ = x₂ :=
begin
  have o₁ : len α e₁ = len α e₂, from
  begin
    unfold len,
    rw h,
  end,
  induction h₀,
  {

    have s₁ : ∃ a : α, to_multiset α e₁ = {a}, from length_set α e₁ (eq.symm h₁),
    have s₂ : ∃ b : α, to_multiset α e₂ = {b}, from
    begin
      apply length_set,
      rw ←o₁,
      exact eq.symm h₁,
    end,
    cases s₁,
    cases s₂,
    have s₃ : {s₂_w} = {s₁_w}, from
    begin
      rw h at s₁_h,
      rw s₁_h at s₂_h,
      exact s₂_h.symm,
    end,
    have s₄ : s₁_w = x₁, from
    begin
      cases w1,
      rw eval_singleton,
      exact s₁_h,
    end,
    have s₅ : s₂_w = x₂, from
    begin
      cases w2,
      rw eval_singleton,
      exact s₂_h,
    end,
    rw s₄ at s₁_h,
    rw s₅ at s₂_h,
    have s₆ : {x₁} = {x₂}, from
    begin
      rw h at s₁_h,
      rw s₁_h at s₂_h,
      exact s₂_h,
    end,
    exact multiset.singleton_inj.mp s₆,
  },
  {

  },

end

theorem main_thm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  : x₁ = x₂ :=
begin
  apply main_thm_aux (len α e₁) _ e₁ e₂ x₁ x₂ h w1 w2 rfl,
end
