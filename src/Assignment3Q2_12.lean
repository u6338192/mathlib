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

lemma const_ne_comp [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (const x) = to_multiset α (comp e₁ e₂)) :
  eval α (const x) = eval α (comp e₁ e₂) :=
begin
  have o₁ : len α (const x) = 1, from rfl,
  have o₂ : 2 ≤ len α (comp e₁ e₂), from comp_neq_const α e₁ e₂,
  have o₃ : len α (comp e₁ e₂) = len α (const x), from
  begin
    dsimp [len],
    rw h,
  end,
  have o₄ : 2 ≤ 1, from begin rw [o₃, o₁] at o₂, exact o₂ end,
  exfalso,
  exact not_q_eq_p_and_q_lt_p 1 1 rfl o₄,
end

lemma const_ne_comp_false [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x : α)
  (h : to_multiset α (const x) = to_multiset α (comp e₁ e₂)) :
  false :=
begin
  have o₁ : len α (const x) = 1, from rfl,
  have o₂ : 2 ≤ len α (comp e₁ e₂), from comp_neq_const α e₁ e₂,
  have o₃ : len α (comp e₁ e₂) = len α (const x), from
  begin
    dsimp [len],
    rw h,
  end,
  have o₄ : 2 ≤ 1, from begin rw [o₃, o₁] at o₂, exact o₂ end,
  exact not_q_eq_p_and_q_lt_p 1 1 rfl o₄,
end

--think about this
lemma fkn_hell [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α)
  (a : α) (h : to_multiset α (comp e₁ e₂) = to_multiset α (comp e₃ (const a))) :
  eval α (comp e₁ e₂) = eval α (comp e₃ (const a)) :=
begin
  sorry,
end

--This is the last sorry
lemma eval_eq [comm_semigroup α] (e₁ e₂ e₃ : comm_semi_group_expr α) (x : α)
  (n : ℕ) (h : len α e₁ = n)
  (h₁ : to_multiset α e₁ = to_multiset α (comp e₂ (const x)))
  (h₂ : eval α e₁ = eval α (comp e₃ (const x))) :
  eval α e₂ = eval α e₃ :=
begin
  sorry,
end

theorem main_thm_induc [comm_semigroup α] (n : ℕ) (e₁ e₂ : comm_semi_group_expr α)
  (h₂ : len α e₁ = n) (h : to_multiset α e₁ = to_multiset α e₂)
  : eval α e₁ = eval α e₂ :=
begin
  revert e₁ e₂,
  induction n,
  {
    intros,
    have o₁ : len α e₁ ≠ 0, from len_expr_ne_zero α e₁,
    exfalso,
    exact o₁ h₂,
  },
  {
    intros,
    have s₁ : ∃ a : α, a ∈ to_multiset α e₁, from multiset_non_empty α e₁,
    cases s₁ with a ha,
    have s₂ : a ∈ to_multiset α e₂, from begin rw h at ha, exact ha, end,
    cases e₁,
    {
      cases e₂,
      {
        dsimp [to_multiset] at h,
        have o₁ : e₁ = e₂, from (multiset.cons_inj_left 0).mp h,
        rw o₁,
      },
      {
        exact const_ne_comp α e₂_a e₂_a_1 e₁ h,
      },
    },
    {
      cases e₂,
      {
        symmetry,
        exact const_ne_comp α e₁_a e₁_a_1 e₂ (eq.symm h),
      },
      {
        have s₃ : ∃ e₃ : comm_semi_group_expr α, to_multiset α (comp e₁_a e₁_a_1)
          = to_multiset α (comp e₃ (const a)), from expr_const_strong α e₁_a e₁_a_1 a ha,
        have s₄ : ∃ e₄ : comm_semi_group_expr α, to_multiset α (comp e₂_a e₂_a_1)
          = to_multiset α (comp e₄ (const a)), from expr_const_strong α e₂_a e₂_a_1 a s₂,
        cases s₃ with e₃ he₃,
        cases s₄ with e₄ he₄,
        have s₅ : ∃ e₅ : comm_semi_group_expr α, eval α (comp e₁_a e₁_a_1)
          = eval α (comp e₅ (const a)),
          from expr_const_eval_with_multiset_strong α e₁_a e₁_a_1 a ha,
        have s₆ : ∃ e₆ : comm_semi_group_expr α, eval α (comp e₂_a e₂_a_1)
          = eval α (comp e₆ (const a)),
          from expr_const_eval_with_multiset_strong α e₂_a e₂_a_1 a s₂,
        cases s₅ with e₅ he₅,
        cases s₆ with e₆ he₆,
        rw [he₅, he₆],
        have s₇ : eval α e₃ = eval α e₅,
          from eval_eq α (comp e₁_a e₁_a_1) e₃ e₅ a (len α (comp e₁_a e₁_a_1)) rfl he₃ he₅,
        have s₈ : eval α e₄ = eval α e₆,
          from eval_eq α (comp e₂_a e₂_a_1) e₄ e₆ a (len α (comp e₂_a e₂_a_1)) rfl he₄ he₆,
        dsimp [eval],
        rw [←s₇, ←s₈],
        have s₉ : eval α e₃ = eval α e₄, from
        begin
          apply n_ih,
          {
            have o₁ : len α (comp e₁_a e₁_a_1) = len α (comp e₃ (const a)), from
            begin
              dsimp [len],
              rw he₃,
            end,
            have o₂ : len α (comp e₃ (const a)) = nat.succ n_n, from
            begin
              rw o₁ at h₂,
              exact h₂,
            end,
            dsimp [len] at *,
            dsimp [to_multiset] at o₂,
            have o₃ : multiset.card (to_multiset α e₃ + {a})
              = multiset.card (to_multiset α e₃) + 1,
              from multiset.card_add (to_multiset α e₃) {a},
            have shouldnt_need_to_do_this : ({a} : multiset α) = a :: 0, from rfl,
            rw shouldnt_need_to_do_this at o₃,
            rw o₂ at o₃,
            have RSNTDT : nat.succ n_n = n_n + 1, from rfl,
            rw RSNTDT at o₃,
            rw add_right_cancel_iff at o₃,
            exact o₃.symm,
          },
          {
            rw [he₃, he₄] at h,
            dsimp [to_multiset] at h,
            rw add_right_cancel_iff at h,
            exact h,
          },
        end,
        rw s₉,
      },
    },
  },
end

theorem main_thm [comm_semigroup α] (e₁ e₂ : comm_semi_group_expr α) (x₁ x₂ : α)
  (h : to_multiset α e₁ = to_multiset α e₂) (w1 : eval α e₁ = x₁) (w2 : eval α e₂ = x₂)
  : x₁ = x₂ :=
begin
  rw [←w1, ←w2],
  exact main_thm_induc α (len α e₁) e₁ e₂ rfl h,
end
