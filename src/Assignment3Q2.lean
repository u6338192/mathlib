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

def to_multiset : comm_semi_group_expr α → multiset α
| (const a)        := {a}
| (comp exp1 exp2) := (to_multiset exp1) + (to_multiset exp2)

def eval [comm_semigroup α] : comm_semi_group_expr α → α
| (const a) := a
| (comp exp1 exp2) := (eval exp1) * (eval exp2)

def len [comm_semigroup α] (e : comm_semi_group_expr α) := (to_multiset α e).card

@[simp] lemma length_set [comm_semigroup α] (e : comm_semi_group_expr α) (h : len α e = 1)
  : ∃ a : α, to_multiset α e = {a} :=
begin
  induction e with e ha hb hc hd,
  { use e, refl, },
  { exact multiset.card_eq_one.mp h, },
end

lemma const_set_length [comm_semigroup α] (e : comm_semi_group_expr α) (a : α)
  (h₁ : to_multiset α e = {a}) : len α e = 1 :=
begin
  induction e,
  { refl, },
  {
    unfold len,
    rw h₁,
    refl,
  },
end

lemma length_split [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  : len α (comp e₁ e₂) = len α e₁ + len α e₂ :=
begin
  unfold len,
  unfold to_multiset,
  exact multiset.card_add (to_multiset α e₁) (to_multiset α e₂),
end

lemma set_length_eq [comm_semigroup α] (e₁ : comm_semi_group_expr α) (a : α)
  : len α e₁ ≤ len α (comp e₁ (const a)) :=
begin
  rw length_split,
  exact nat.le_succ (len α e₁),
end

lemma comp_set_length [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  : len α e₁ ≤ len α (comp e₁ e₂) :=
begin
  rw length_split,
  exact nat.le.intro rfl,
end

@[simp] lemma expr_singleton [comm_semigroup α] (e : comm_semi_group_expr α) (a : α)
  (h : to_multiset α e = {a}) : const a = e :=
begin
  induction e with e ha hb hc hd,
  {
    dsimp [to_multiset] at h,
    have o₁ : a = e, from multiset.singleton_inj.mp (eq.symm h),
    exact congr_arg const o₁,
  },
  {
    dsimp [to_multiset] at h,
    dsimp at *,
    sorry,
  },
end

lemma not_q_eq_p_and_q_lt_p (p q : ℕ) (h₁ : q = p) (h₂ : q < p): false :=
begin
  rw h₁ at h₂,
  revert h₂,
  contrapose,
  intro,
  exact irrefl p,
end

@[simp] lemma set_split [comm_semigroup α] (e : comm_semi_group_expr α) (h : len α e > 1)
  : ∃ x : (comm_semi_group_expr α), ∃ a : α, to_multiset α e = to_multiset α x + {a} :=
begin
  induction e with e ha hb hc hd,
  {
    have o₁ : len α (const e) = 1, from rfl,
    have o₂ : false, from not_q_eq_p_and_q_lt_p 1 1 rfl h,
    exact false.rec (∃ (x : comm_semi_group_expr α) (a : α), to_multiset α (const e)
      = to_multiset α x + {a}) o₂,
  },
  {
    sorry,
  },
end

@[simp] lemma csge_rep_e [comm_semigroup α] (e : comm_semi_group_expr α)
  : ∃ x : comm_semi_group_expr α, ∃ a : α, eval α e = eval α (comp x (const a)) :=
begin
  induction e with e ha hb hc hd,
  sorry,
  sorry,
end

@[simp] lemma csge_rep_m [comm_semigroup α] (e : comm_semi_group_expr α)
  : ∃ x : comm_semi_group_expr α, ∃ a : α, to_multiset α e = to_multiset α x + {a} :=
begin
  induction e with e ha hb hc hd,
  sorry,
  sorry,
end

lemma one_lt_len  [comm_semigroup α] (e : comm_semi_group_expr α) : 1 ≤ len α e :=
begin
  sorry
end

lemma sets_eq_len_eq [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  (h : to_multiset α e₁ = to_multiset α e₂) : len α e₁ = len α e₂ :=
begin
  induction e₁,
  {
    induction e₂,
    {
      refl,
    },
    {
      rw length_split,
      have o₁ : len α (const e₁) = 1, from rfl,
      rw o₁,
      have o₂ : 1 ≤ len α e₂_a, from one_lt_len α e₂_a,
      have o₃ : 1 ≤ len α e₂_a_1, from one_lt_len α e₂_a_1,
      sorry, -- I can do this
    },
  },
  {
    induction e₂,
    {
      rw length_split,
      have o₁ : len α (const e₂) = 1, from rfl,
      rw o₁,
      sorry,
    },
    {
      rw length_split,
      rw length_split,
      sorry,
    },
  }
end

theorem main_thm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  : x₁ = x₂ :=
begin
  sorry,

end
