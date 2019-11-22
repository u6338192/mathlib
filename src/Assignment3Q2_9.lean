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

lemma the_key [comm_semigroup α] (n : ℕ) (e₁ e₂ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (comp e₁ (const x)) = to_multiset α (comp e₂ (const x)))
  (h₂ : len α e₁ = n) :
  eval α (comp e₁ (const x)) = eval α (comp e₂ (const x)) :=
begin
  revert e₁ e₂ x,
  induction n,
  {
    intros,
    cases e₁,
    {
      have o₁ : len α (const e₁) = 1, from rfl,
      have o₂ : 0 = 1, from begin rw h₂ at o₁, exact o₁, end,
      have o₃ : 0 < 1, from lt_add_one 0,
      exfalso,
      exact not_q_eq_p_and_q_lt_p 1 0 o₂ o₃,
    },
    {
      have o₁ : 2 ≤ len α (comp e₁_a e₁_a_1), from comp_neq_const α e₁_a e₁_a_1,
      have o₂ : 2 ≤ 0, from begin rw h₂ at o₁, exact o₁, end,
      exfalso,
      exact nat.not_succ_le_zero 1 o₂,
    },
  },
  {
    intros,
    have o₁ : to_multiset α e₁ = to_multiset α e₂, from
    begin
      dsimp [to_multiset] at h,
      rw add_right_cancel_iff at h,
      exact h,
    end,
    have o₂ : ∃ a : α, a ∈ to_multiset α e₁, from multiset_non_empty α e₁,
    cases o₂ with b hb,
    have o₃ : b ∈ to_multiset α e₂, from begin rw o₁ at hb, exact hb, end,
    cases e₁,
    {
      cases e₂,
      {
        sorry,
      },
      {
        sorry,
      },
    },
    {
      cases e₂,
      {
        sorry,
      },
      {
        have o₄ : ∃ e₃ : comm_semi_group_expr α, to_multiset α (comp e₁_a e₁_a_1)
          = to_multiset α (comp e₃ (const b)), from expr_const_strong α e₁_a e₁_a_1 b hb,
        have o₅ : ∃ e₄ : comm_semi_group_expr α, to_multiset α (comp e₂_a e₂_a_1)
          = to_multiset α (comp e₄ (const b)), from expr_const_strong α e₂_a e₂_a_1 b o₃,
        cases o₄ with c hc,
        cases o₅ with d hd,
        have o₆ : ∃ e₅ : comm_semi_group_expr α, eval α (comp e₁_a e₁_a_1)
          = eval α (comp e₅ (const b)), from expr_const_eval_with_multiset_strong α e₁_a e₁_a_1 b hb,
        have o₇ : ∃ e₆ : comm_semi_group_expr α, eval α (comp e₂_a e₂_a_1)
          = eval α (comp e₆ (const b)), from expr_const_eval_with_multiset_strong α e₂_a e₂_a_1 b o₃,
        cases o₆ with x hx,
        cases o₇ with y hy,
        have s₁ : eval α (comp e₁_a e₁_a_1) = eval α (comp e₂_a e₂_a_1), from
        begin
          rw [hx, hy],
          apply n_ih,
          sorry,
          sorry, --same problem-- I don't know how to solve this.
        end,
        sorry,
      },
    },
  },
end

lemma the_key' [comm_semigroup α] (n : ℕ) (e₁ e₂ e₃ e₄ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (comp (comp e₁ e₂) (const x)) = to_multiset α (comp (comp e₃ e₄) (const x)))
  (h₂ : len α e₁ = n) :
  eval α (comp (comp e₁ e₂) (const x)) = eval α (comp (comp e₃ e₄) (const x)) :=
begin
  revert e₁ e₂ e₃ e₄,
  induction n,
  {
    intros,
    cases e₁,
    {
      have o₁ : len α (const e₁) = 1, from rfl,
      have o₂ : 0 = 1, from begin rw h₂ at o₁, exact o₁, end,
      have o₃ : 0 < 1, from lt_add_one 0,
      exfalso,
      exact not_q_eq_p_and_q_lt_p 1 0 o₂ o₃,
    },
    {
      have o₁ : 2 ≤ len α (comp e₁_a e₁_a_1), from comp_neq_const α e₁_a e₁_a_1,
      have o₂ : 2 ≤ 0, from begin rw h₂ at o₁, exact o₁, end,
      exfalso,
      exact nat.not_succ_le_zero 1 o₂,
    },
  },
  {
    intros,
    sorry,
  },
end

lemma easy_induction [comm_semigroup α] (n : ℕ) (e₁ e₂ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (h₂ : len α e₁ = n) :
  eval α (comp e₁ (const x)) = eval α (comp e₂ (const x)) :=
begin
  revert e₁,
  revert e₂,
  induction n,
  {
    intros,
    sorry,
  },
  {
    intros b c hb hc,
    dsimp [eval],
    cases b,
    {
      cases c,
      {
        sorry,
      },
      {
        sorry,
      }
    },
    {
      cases c,
      {
        sorry,
      },
      {
        have o₁ : ∃ a : α, a ∈ to_multiset α e, from by lib
        have s₁ : ∃ e₃ : comm_semi_group_expr α,
          eval α (comp c_a c_a_1) = eval α (comp e₃ (const a)), from by lib,
      },
    },
  },
end

lemma expr_const_eval_lock [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α)
  (a : α) (h : a ∈ to_multiset α e₂) (h₂ : to_multiset α (comp e₁ e₂)
  = to_multiset α (comp e₃ (const a))) :
  eval α (comp e₁ e₂) = eval α (comp e₃ (const a)) :=
begin
  have s₁ : ∃ e₄ : comm_semi_group_expr α, eval α (comp e₁ e₂) = eval α (comp e₄ (const a)),
    from expr_const_eval_with_multiset α e₁ e₂ a h,
  cases s₁ with b hb,
  rw hb,
  dsimp [eval],
  have s₂ : to_multiset α b = to_multiset α e₃, from
  begin
    sorry,
  end,
  sorry,
end

--This is what I need to prove
lemma last_bit' [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const x))) :
  eval α (comp e₁ e₂) = eval α (comp e₃ (const x)) :=
begin
  sorry,
end

theorem main_thm_aux [comm_semigroup α] (n : ℕ) (e₁ e₂ : comm_semi_group_expr α)
  (h : to_multiset α e₁ = to_multiset α e₂) (h₂ : len α e₁ = n)
  : eval α e₁ = eval α e₂ :=
begin
  revert e₁,
  revert e₂,
  induction n,
  {
    sorry,
  },
  {
    intros,
    have s₁ : ∃ a : α, a ∈ to_multiset α e₁, from multiset_non_empty α e₁,
    cases s₁ with b c,
    have o₁ : b ∈ to_multiset α e₂, from set.mem_of_eq_of_mem (eq.symm h) c,
    have s₂ : ∃ e₃ : comm_semi_group_expr α,
      to_multiset α e₁ = to_multiset α (comp e₃ (const b)), from sorry,
    have s₃ : ∃ e₄ : comm_semi_group_expr α,
      to_multiset α e₂ = to_multiset α (comp e₄ (const b)), from sorry,
    cases s₂ with e₃ he₃,
    cases s₃ with e₄ he₄,
    have s₄ : len α e₃ = n_n, from by sorry,
    have s₅ : eval α e₃ = eval α e₄, from
    begin
      apply n_ih,
      rw [he₃, he₄] at h,
      dsimp [to_multiset] at h,
      rw add_right_cancel_iff at h,
      exact h,
      exact s₄,
    end,
    have s₆ : eval α (comp e₃ (const b)) = eval α (comp e₄ (const b)), from
    begin
      refine const_along α e₃ e₄ b _ _,
      intro h₅,
      exact n_ih e₄ e₃ h₅ s₄,
      rw [he₃, he₄] at h,
      exact h,
    end,
    sorry,
  },
end

theorem main_thm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  : x₁ = x₂ :=
begin
  rw [←w1, ←w2],
  exact main_thm_aux α (len α e₁) e₁ e₂ x₁ x₁ h rfl,
end
