import operand
import data.finsupp
import tactic.interactive

open tactic

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

lemma eq_big_finsupp_prod_Z [has_zero β] [comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (h : f₁.support = f₂.support) (w : ∀a∈f₁.support, f₁ a = f₂ a) :
finsupp.prod f₁ g = finsupp.prod f₂ g :=
begin
  --apply prod_congr,
  conv
  {
    to_lhs,
    applyc `prod_congr,
    --rw h, -- Need to figure out how to deal with this
    skip,
    intro `s,
    intro `s_mem,
    skip, -- WTF!!!
    --rw [w s s_mem],

  },
  sorry,
end


lemma finsupp_sum_test_Z [has_zero β] [add_comm_monoid γ] (f : α →₀ β) (g : α → β → γ)
  (h : f.support = f.support) (w : ∀a∈f.support, f a = 0) :
finsupp.sum f g = 0 :=
begin
  conv {
    to_lhs,
    operand {rw [w s s_mem],},
  },
  exact multiset.sum_map_zero, --library_search
end

lemma finsupp_sum_test_Z' [has_zero β] [add_comm_monoid γ] (f : α →₀ β) (g : α → β → γ)
  (h : f.support = f.support) (w : ∀a∈f.support, f a = 0) :
finsupp.sum f g = 0 :=
begin
  conv {
    to_lhs,
    applyc `finsupp.sum_congr,
    rotate 1,
    intro `s,
    intro `s_mem,
    rw [w s s_mem],
    swap,
    skip,

  },
  exact multiset.sum_map_zero, --library_search
end

lemma finsupp_prod_test_Z [has_one β] [comm_monoid γ] (f : α →₀ β) (g : α → β → γ)
  (h : f.support = f.support) (w : ∀a∈f.support, f a = 1) :
finsupp.prod f g = 1 :=
begin
  conv {
    to_lhs,
    operand {rw [w s s_mem]},
  },
  exact multiset.prod_map_one, --library_search
end

example : true :=
begin
  success_if_fail { conv { operand { skip }, }, },
  trivial
end

lemma eq_big_finsupp_sum [has_zero β] [add_comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (w : ∀a∈f₁.support, f₁ a = f₂ a) :
finsupp.sum f₁ g = finsupp.sum f₂ g :=
begin
  conv
  {
    to_lhs,
    operand {rw [w s s_mem],},
  },
end

lemma eq_big_finsupp_sum' [has_zero β] [add_comm_monoid γ] (f₁ f₂ : α →₀ β) (g : α → β → γ)
  (h : f₁.support = f₂.support)
  (w : ∀a∈f₂.support, f₁ a = f₂ a) :
finsupp.sum f₁ g = finsupp.sum f₂ g :=
begin
  conv
  {
    to_lhs,
    applyc `finsupp.sum_congr,
    rw h,
    skip,
    intro `s,
    intro `s_mem,
    rw [w s s_mem],
  },
end
