import operand
import data.finsupp
import tactic.interactive
import hotkeys

open tactic

-- lemma eq_big_sum_Z (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)
--   : finset.sum S (λ s, f s) = finset.sum S (λ s, g s) :=
-- begin
--   exact finset.sum_congr rfl h,
-- end

-- lemma eq_big_prod_Z (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)
--   : finset.prod S (λ s, f s) = finset.prod S (λ s, g s) :=
-- begin
--   exact finset.fold_congr h,
-- end

-- lemma eq_big_fold_Z (f g : ℤ → ℤ) (S : finset ℤ)
--   (h : ∀ m ∈ S, f m = g m)
--   : finset.fold (+) 0 (λ s, f s) S = finset.fold (+) 0 (λ s, g s) S :=
-- begin
--   exact finset.sum_congr rfl h,
-- end

-- lemma sum_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
--   : finset.sum S (λ s, f s) = finset.sum S (λ s, - f (- s)) :=
-- begin
--   exact finset.sum_congr rfl h,
-- end

-- lemma prod_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
--   : finset.prod S (λ s, f s) = finset.prod S (λ s, - f (- s)) :=
-- begin
--   exact finset.fold_congr h
-- end

-- lemma fold_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
--   : finset.fold (+) 0 (λ s, f s) S = finset.fold (+) 0 (λ s, - f (- s)) S :=
-- begin
--   exact finset.sum_congr rfl h,
-- end

-- lemma sum_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)
--   : finset.sum S (λ s, f s) = 0 :=
-- begin
--   exact finset.sum_eq_zero h,
-- end

-- lemma prod_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 1)
--   : finset.prod S (λ s, f s) = 1 :=
-- begin
--   exact finset.prod_eq_one h,
-- end

-- lemma fold_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)
--   : finset.fold (+) 0 (λ s, f s) S = 0 :=
-- begin
--   exact finset.sum_eq_zero h,
-- end

-- lemma eq_big_sum_Z_no_lambda (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)
--   : finset.sum S f = finset.sum S (λ s, g s) :=
-- begin
--   exact finset.sum_congr rfl h,
-- end

lemma eq_big_prod_Z_no_lamda (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)
  : finset.prod S f = finset.prod S (λ s, g s) :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
end

lemma eq_big_fold_Z_no_lamda (f g : ℤ → ℤ) (S : finset ℤ)
  (h : ∀ m ∈ S, f m = g m)
  : finset.fold (+) 0 f S = finset.fold (+) 0 (λ s, g s) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
end

lemma sum_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
  : finset.sum S f = finset.sum S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},
    },
end

lemma prod_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
  : finset.prod S f = finset.prod S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},
    },
end

lemma fold_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))
  : finset.fold (+) 0 f S = finset.fold (+) 0 (λ s, - f (- s)) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
end

lemma sum_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)
  : finset.sum S f = 0 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
  exact multiset.sum_map_zero, --library_search
end

lemma prod_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 1)
  : finset.prod S f = 1 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
  exact multiset.prod_map_one, --library_search
end

lemma fold_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)
  : finset.fold (+) 0 f S = 0 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},
  },
  exact multiset.sum_map_zero, --library_search
end

lemma eq_big_sum_Z'' (f g : ℤ → ℤ) (S₁ S₂ : finset ℤ) (h : S₁ = S₂) (w : ∀ m ∈ S₂, f m = g m)
  : finset.sum S₁ (λ s, f s) = finset.sum S₂ (λ s, g s) :=
begin
  exact finset.sum_congr h w,
end

lemma eq_big_sum_Z' (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)
  : finset.sum S (λ s, f s) = finset.sum S (λ s, g s) :=
begin
  conv {
    to_lhs,
    applyc `finset.sum_congr,
    skip,
    intro `s,
    intro `s_mem,
    rw [h s s_mem],
  },
end

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
[comm_monoid γ] [decidable_eq α] [decidable_eq β] [has_zero β]
variables {s₁ s₂ : finset α} {a a' : α} {b : β} {f g : α →₀ β} {op : α → β → γ}

-- @[to_additive finsupp.sum]
-- def prod` [has_zero β] [comm_monoid γ] (f : α →₀ β) (g : α → β → γ) : γ :=
-- f.support.prod (λa, g a (f a))
-- attribute [to_additive finsupp.sum.equations._eqn_1] finsupp.prod.equations._eqn_1

@[to_additive finsupp.sum_congr]
lemma prod_congr (h : f.support = g.support) :
 (∀a∈g.support, f a = g a) → finsupp.prod f op = finsupp.prod g op :=
  λ w, finset.prod_congr h (λ a mem, by rw [w a mem])

-- lemma eq_big_finsupp_prod_Z [has_zero β] [comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
--   (h : f₁.support = f₂.support) (w : ∀a∈f₁.support, f₁ a = f₂ a) :
-- finsupp.prod f₁ g = finsupp.prod f₂ g :=
-- begin
--   apply prod_congr,
--   exact h,
--   rw h at w, -- library_search fails here because of the rw.
--   exact w,
-- end

--This lemma is false.
lemma finsupp_sum_test_Z [has_zero β] [add_comm_monoid γ] (f : α →₀ β) (g : α → β → γ)
  (h : f.support = f.support) (w : ∀a∈f.support, f a = 0) :
finsupp.sum f g = 0 :=
begin
  unfold finsupp.sum,
  apply finset.sum_eq_zero,
  intros s s_mem,
  have o₁ : f s = 0, from w s s_mem,
  rw o₁,
  sorry,
end

--This lemma is false.
lemma finsupp_prod_test_Z [has_one β] [comm_monoid γ] (f : α →₀ β) (g : α → β → γ)
  (h : f.support = f.support) (w : ∀a∈f.support, f a = 1) :
finsupp.prod f g = 1 :=
begin
  unfold finsupp.prod,
  apply finset.prod_eq_one,
  intros s s_mem,
  have o₁ : f s = 1, from w s s_mem,
  rw o₁,
  sorry,
end

--false lemma I think
lemma eq_big_finsupp_sum [has_zero β] [add_comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (w : ∀a∈f₁.support, f₁ a = f₂ a) :
finsupp.sum f₁ g = finsupp.sum f₂ g :=
begin
  --lib,
  sorry,
end

lemma eq_big_finsupp_sum' [has_zero β] [add_comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (h : f₁.support = f₂.support)
  (w : ∀a∈f₂.support, f₁ a = f₂ a) :
finsupp.sum f₁ g = finsupp.sum f₂ g :=
begin
  exact finsupp.sum_congr h w,
end

lemma eq_big_finsupp_prod_Z' [has_zero β] [comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (h : f₁.support = f₂.support) (w : ∀a∈f₁.support, f₁ a = f₂ a) :
finsupp.prod f₁ g = finsupp.prod f₂ g :=
begin
  have w' : ∀ (a : α), a ∈ f₂.support → f₁ a = f₂ a, from begin rw h at w, exact w, end,
  exact prod_congr h w',
end
