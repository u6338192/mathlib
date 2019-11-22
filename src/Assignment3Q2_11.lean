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

lemma not_q_eq_p_and_q_lt_p (p q : ℕ) (h₁ : q = p) (h₂ : q < p): false :=
begin
  rw h₁ at h₂,
  revert h₂,
  contrapose,
  intro,
  exact irrefl p,
end

lemma comp_neq_const [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) :
  2 ≤ len α (comp e₁ e₂) :=
begin
  induction e₂,
  {
    induction e₁,
    { refl, },
    {
      rw length_split,
      rw length_split,
      rw length_split at e₁_ih_a_1,
      rw add_assoc,
      exact le_add_left e₁_ih_a_1,
    },
  },
  {
    induction e₁,
    {
      rw length_split,
      rw length_split,
      rw length_split at e₂_ih_a,
      rw ←add_assoc,
      exact le_add_right e₂_ih_a,
    },
    {
      rw length_split,
      rw length_split,
      rw length_split,
      rw length_split at e₂_ih_a_1,
      rw length_split at e₂_ih_a_1,
      rw add_comm (len α e₂_a) (len α e₂_a_1),
      rw ←add_assoc,
      exact le_add_right e₂_ih_a_1,
    },
  },
end

lemma length_gt_one  [comm_semigroup α] (e : comm_semi_group_expr α) : 1 ≤ len α e :=
begin
  cases e with a e₁ e₂,
  { refl, },
  {
    have o₁ : 2 ≤ len α (comp e₁ e₂), from comp_neq_const α e₁ e₂,
    exact le_of_lt o₁,
  },
end

lemma eval_const [comm_semigroup α] (b : α) (e : comm_semi_group_expr α)
  (h : to_multiset α e = {b}) : eval α e = b :=
begin
  have o₁ : e = const b, from
  begin
    cases e,
    {
      have o₂ : {e} = {b}, from h,
      have o₃ : e = b, from multiset.singleton_inj.mp h,
      rw o₃,
    },
    {
      have o₄ : 1 < len α (comp e_a e_a_1), from comp_neq_const α e_a e_a_1,
      have o₅ : len α (comp e_a e_a_1) = 1, from
      begin
        unfold len,
        rw h,
        refl,
      end,
      have o₆ : false, from by
      begin
        apply not_q_eq_p_and_q_lt_p (len α (comp e_a e_a_1)) 1,
        { exact eq.symm o₅ },
        { exact o₄ },
      end,
      exact congr_fun (congr_fun (false.rec (comp =
        λ (e_a e_a_1 : comm_semi_group_expr α), const b) o₆) e_a) e_a_1,
    },
  end,
  rw o₁,
  refl,
end

lemma comp_assoc [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) :
to_multiset α (comp e₁ (comp e₂ e₃)) = to_multiset α (comp e₂ (comp e₁ e₃)) :=
begin
  dsimp [to_multiset],
  rw add_comm,
  rw add_comm (to_multiset α e₁) (to_multiset α e₃),
  rw add_assoc,
end

lemma comp_assoc_eval [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) :
eval α (comp e₁ (comp e₂ e₃)) = eval α (comp e₂ (comp e₁ e₃)) :=
begin
  dsimp [eval],
  rw mul_comm,
  rw mul_comm (eval α e₁) (eval α e₃),
  rw mul_assoc,
end

lemma comp_comm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) :
  to_multiset α (comp e₁ e₂) = to_multiset α (comp e₂ e₁) :=
begin
  dsimp [to_multiset],
  rw add_comm,
end

lemma comp_comm_eval [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) :
  eval α (comp e₁ e₂) = eval α (comp e₂ e₁) :=
begin
  dsimp [eval],
  rw mul_comm,
end

lemma len_expr_ne_zero [comm_semigroup α] (e : comm_semi_group_expr α) :
  len α e ≠ 0 :=
begin
  cases e,
  {
    have o₁ : len α (const e) = 1, from rfl,
    exact one_ne_zero,
  },
  {
    have o₂ : 2 ≤ len α (comp e_a e_a_1), from comp_neq_const α e_a e_a_1,
    exact lattice.ne_bot_of_gt o₂,
  },
end

lemma expr_const [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  (a : α) (h : a ∈ to_multiset α e₂) : ∃ e₃ : comm_semi_group_expr α,
  to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const a)) :=
begin
  induction e₂ with e₂ b c hb hc,
  {
    use e₁,
    have o₁ : a = e₂, from
    begin
      dsimp [to_multiset] at h,
      cases h,
      exact h,
      exact false.rec (a = e₂) h,
    end,
    rw o₁,
  },
  {
    dsimp [to_multiset] at h,
    have o₁ : a ∈ to_multiset α b ∨ a ∈ to_multiset α c, from multiset.mem_add.mp h,
    cases o₁,
    {
      have o₂ : ∃ (e₃ : comm_semi_group_expr α),
        to_multiset α (comp e₁ b) = to_multiset α (comp e₃ (const a)), from hb o₁,
      cases o₂,
      use (comp c o₂_w),
      dsimp [to_multiset],
      dsimp [to_multiset] at o₂_h,
      rw ←add_assoc,
      rw o₂_h,
      rw add_comm,
      rw add_assoc,
    },
    {
      have o₂ : ∃ (e₃ : comm_semi_group_expr α),
        to_multiset α (comp e₁ c) = to_multiset α (comp e₃ (const a)), from hc o₁,
      cases o₂,
      use (comp b o₂_w),
      dsimp [to_multiset],
      dsimp [to_multiset] at o₂_h,
      rw ←add_assoc,
      rw add_comm (to_multiset α e₁) (to_multiset α b),
      rw add_assoc,
      rw o₂_h,
      rw add_assoc,
    },
  },
end

lemma expr_const_strong [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  (a : α) (h : a ∈ to_multiset α (comp e₁ e₂)) : ∃ e₃ : comm_semi_group_expr α,
  to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const a)) :=
begin
  have o₁ : a ∈ to_multiset α e₁ ∨ a ∈ to_multiset α e₂, from
  begin
    dsimp [to_multiset] at h,
    exact multiset.mem_add.mp h,
  end,
  cases o₁,
  {
    rw comp_comm,
    exact expr_const α e₂ e₁ a o₁,
  },
  {
    exact expr_const α e₁ e₂ a o₁,
  },
end

lemma expr_const_eval [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) :
  ∃ e₃ : comm_semi_group_expr α, ∃ a : α,
  eval α (comp e₁ e₂) = eval α (comp e₃ (const a)) :=
begin
  induction e₂,
  { use e₁,
    use e₂, },
  {
    cases e₂_ih_a_1 with w h,
    cases e₂_ih_a with x y,
    cases h,
    cases y,
    rw comp_assoc_eval,
    split,
    use h_w,
    swap,
    exact (comp e₂_a w),
    dsimp [eval] at h_h,
    dsimp [eval],
    rw h_h,
    rw mul_assoc,
  },
end

lemma expr_const_eval_with_multiset [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  (a : α) (h : a ∈ to_multiset α e₂):
  ∃ e₃ : comm_semi_group_expr α, eval α (comp e₁ e₂) = eval α (comp e₃ (const a)) :=
begin
  induction e₂ with e₂ b c hb hc,
  {
    use e₁,
    have o₁ : a = e₂, from
    begin
      dsimp [to_multiset] at h,
      cases h,
      exact h,
      exact false.rec (a = e₂) h,
    end,
    rw o₁,
  },
  {
    dsimp [to_multiset] at h,
    have o₁ : a ∈ to_multiset α b ∨ a ∈ to_multiset α c, from multiset.mem_add.mp h,
    cases o₁,
    {
      have o₂ : ∃ (e₃ : comm_semi_group_expr α),
        eval α (comp e₁ b) = eval α (comp e₃ (const a)), from hb o₁,
      cases o₂,
      use (comp c o₂_w),
      dsimp [eval],
      dsimp [eval] at o₂_h,
      rw ←mul_assoc,
      rw o₂_h,
      rw mul_comm,
      rw mul_assoc,
    },
    {
      have o₂ : ∃ (e₃ : comm_semi_group_expr α),
        eval α (comp e₁ c) = eval α (comp e₃ (const a)), from hc o₁,
      cases o₂,
      use (comp b o₂_w),
      dsimp [eval],
      dsimp [eval] at o₂_h,
      rw ←mul_assoc,
      rw mul_comm (eval α e₁) (eval α b),
      rw mul_assoc,
      rw o₂_h,
      rw mul_assoc,
    },
  },
end

lemma expr_const_eval_with_multiset_strong [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α)
  (a : α) (h : a ∈ to_multiset α (comp e₁ e₂)) :
  ∃ e₃ : comm_semi_group_expr α, eval α (comp e₁ e₂) = eval α (comp e₃ (const a)) :=
begin
  have o₁ : a ∈ to_multiset α e₁ ∨ a ∈ to_multiset α e₂, from
  begin
    dsimp [to_multiset] at h,
    exact multiset.mem_add.mp h,
  end,
  cases o₁,
  {
    rw comp_comm_eval,
    exact expr_const_eval_with_multiset α e₂ e₁ a o₁,
  },
  {
    exact expr_const_eval_with_multiset α e₁ e₂ a o₁,
  },
end

lemma multiset_non_empty [comm_semigroup α] (e : comm_semi_group_expr α) :
  ∃ a : α, a ∈ to_multiset α e :=
begin
  induction e with e b c ih ihe,
  {
    use e,
    exact set.mem_insert e (λ (e : α), false),
  },
  {
    cases ih,
    cases ihe,
    dsimp [to_multiset],
    use ihe_w,
    simp,
    right,
    exact ihe_h,
  },
end

lemma const_along [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α e₁ = to_multiset α e₂ → eval α e₁ = eval α e₂) :
  to_multiset α (comp e₁ (const x)) = to_multiset α (comp e₂ (const x)) →
  eval α (comp e₁ (const x)) = eval α (comp e₂ (const x)) :=
begin
  intro H,
  dsimp [to_multiset] at H,
  rw add_right_cancel_iff at H,
  have o₁ : eval α e₁ = eval α e₂, from h H,
  dsimp [eval],
  rw o₁,
end

--I really think this might work
lemma this_is_it_baby [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) (x : α)
  (n : ℕ) (h : len α e₁ = n) (h₁ : to_multiset α e₁ = to_multiset α (comp e₂ (const x)))
  (h₂ : eval α e₁ = eval α (comp e₃ (const x))) :
  to_multiset α e₂ = to_multiset α e₃ :=
begin
  revert e₁ e₂ x,
  induction n,
  {
    intros,
    sorry,
  },
  {
    intros,
    sorry,
  },
end

lemma thought_it_out_a_little_induc [comm_semigroup α] (e₁ e₂ e₃ e₄ : comm_semi_group_expr α) (x : α)
  (n : ℕ) (h : len α e₃ = n) (h₁ : to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const x)))
  (h₂ : eval α (comp e₁ e₂) = eval α (comp e₄ (const x))) :
  to_multiset α (comp e₃ (const x)) = to_multiset α (comp e₄ (const x)) :=
begin
  revert e₁ e₂ e₃ e₄ x,
  induction n,
  {
    intros,
    sorry,
  },
  {
    intros,
    sorry,
  },
end

lemma thought_it_out_a_little [comm_semigroup α] (e₁ e₂ e₃ e₄ : comm_semi_group_expr α) (x : α)
  (h₁ : to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const x)))
  (h₂ : eval α (comp e₁ e₂) = eval α (comp e₄ (const x))) :
  to_multiset α (comp e₃ (const x)) = to_multiset α (comp e₄ (const x)) :=
begin
  sorry,
end

lemma the_problem_induc [comm_semigroup α] (n : ℕ) (e₁ e₂ e₃ e₄ : comm_semi_group_expr α) (x : α)
  (h₂ : len α (comp e₁ e₂) = n)
  (h : to_multiset α (comp (comp e₁ e₂) (const x)) = to_multiset α (comp (comp e₃ e₄) (const x))) :
  eval α (comp (comp e₁ e₂) (const x)) = eval α (comp (comp e₃ e₄) (const x)) :=
begin
  revert e₁ e₂ e₃ e₄ x,
  induction n,
  {
    intros,
    have o₁ : len α (comp e₁ e₂) ≠ 0, from len_expr_ne_zero α (comp e₁ e₂),
    exfalso,
    exact o₁ h₂,
  },
  {
    intros,

  },
end

lemma the_problem [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const x))) :
  eval α (comp e₁ e₂) = eval α (comp e₃ (const x)) :=
begin
  sorry,
end



theorem main_thm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  : x₁ = x₂ :=
begin
  sorry,
end
