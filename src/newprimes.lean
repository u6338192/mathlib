import data.nat.prime
import tactic
import tactic.find
import hotkeys

open nat

def divisors_aux (n : ℕ) : ℕ → list ℕ
| 0     := []
| (h+1) := if n % h = 0
           then [h] ++ divisors_aux h
           else divisors_aux h

def divisors (n :ℕ) := divisors_aux n (n+1)

def is_in_list (n : ℕ) : list ℕ → bool
| []     := false
| (h::t) := if h = n then true else is_in_list t

#eval divisors 5
#eval divisors 4
#eval divisors_aux 12 13
#eval divisors_aux 0 10
#eval divisors 0
#eval divisors_aux 12 1
#eval divisors_aux 12 0

def myprime (p : ℕ) : Prop := (p ≥ 2) ∧ divisors p = [p,1]

example (n : ℕ) : divisors_aux n 0 = [] := rfl

lemma def_aux (h n : ℕ) : divisors_aux n (h+1) = if n % h = 0
                                            then [h] ++ divisors_aux n h
                                            else divisors_aux n h := rfl

lemma ite_zero_eq_zero (p : ℕ) : ite (0 = 0) ([p] ++ divisors_aux p p) (divisors_aux p p) =
  ([p] ++ (divisors_aux p p)) := rfl

lemma mod_one (n : ℕ) (h : n ≠ 0) : divisors_aux n 1 = [] :=
begin
  rw def_aux,
  have o₀ : n % 0 = n, from mod_def n 0,
  have o₁ : n % 0 ≠ 0, from ne_of_eq_of_ne o₀ h,
  have o₂ : ite (n % 0 = 0) ([0] ++ divisors_aux n 0) (divisors_aux n 0)
    = divisors_aux n 0, from if_neg o₁,
  rw o₂,
  refl,
end

lemma not_q_eq_p_and_q_lt_p (p q : ℕ) (h₁ : q = p) (h₂ : q < p): false :=
begin
  rw h₁ at h₂,
  revert h₂,
  contrapose,
  intro,
  exact irrefl p,
end

lemma q_eq_p_to_not_q_lt_p (p q : ℕ) (h₁ : q = p) : ¬(q < p) := λ a, not_q_eq_p_and_q_lt_p p q h₁ a

lemma q_lt_p_to_not_q_eq_p (p q : ℕ) (h₁ : q < p) : ¬(q = p) := λ a, not_q_eq_p_and_q_lt_p p q a h₁

lemma prime_mod (p b : ℕ) (h₁ : prime p) (h₂ : 2 ≤ b) (h₃ : b < p) : p % b ≠ 0 :=
begin
  have o₁ : p % b = 0 → b ∣ p, from dvd_of_mod_eq_zero,
  have o₂ : ¬(b ∣ p) → ¬(p % b = 0), from mt o₁,
  apply o₂,
  have o₃ : 2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p, from h₁,
  have o₄ : ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p, from o₃.right,
  have o₅ : b ∣ p → b = 1 ∨ b = p, from o₄ b,
  have o₆ : ¬(b = 1 ∨ b = p) → ¬(b ∣ p), from mt (o₄ b),
  have o₇ : ¬(b = 1) ∧ ¬(b = p) → ¬(b = 1 ∨ b = p), from not_or_distrib.mpr,
  have o₈ : ¬(b = 1) ∧ ¬(b = p) → ¬(b ∣ p), from λ a, o₆ (o₇ a),
  have o₉ : ¬(b = 1), from λ a, not_q_eq_p_and_q_lt_p b 1 a.symm h₂,
  have s₁ : ¬(b = p), from q_lt_p_to_not_q_eq_p p b h₃,
  exact o₈ ⟨o₉,s₁⟩,
end

lemma Reid_B (a p : ℕ) (h₁ : 2 <= a) (h₂ : a <= p) (h₃ : prime p)
  : divisors_aux p a = [1] :=
begin
  induction h₁,
  {
    rw def_aux,
    have o₀ : p % 1 = 0, from mod_one p,
    have o₁ : ite (p % 1 = 0) ([1] ++ divisors_aux p 1) (divisors_aux p 1)
      = [1] ++ divisors_aux p 1, from if_pos o₀,
    rw o₁,
    have o₂ : p ≠ 0, from prime.ne_zero h₃,
    have o₃ : divisors_aux p 1 = [], from mod_one p o₂,
    rw o₃,
    refl,
  },
  {
    rw def_aux,
    have o₃ : h₁_b < p, from h₂,
    have o₄ : h₁_b ≤ p, from le_of_lt h₂,
    rw h₁_ih o₄,
    have o₅ : p % h₁_b ≠ 0, from prime_mod p h₁_b h₃ h₁_a h₂,
    exact if_neg o₅,
  }
end

lemma my_prime_good (p n : ℕ) : prime p → myprime p :=
have s₁ : prime p → (p ≥ 2), from prime.two_le,
have s₆ : prime p → p ≠ 1, from prime.ne_one,
have s₄ : prime p → (n ∣ p → n = 1 ∨ n = p), from λ (pp : prime p), (dvd_prime pp).mp,
have s₅ : prime p → divisors_aux p p = [1], from
begin
  intro,
  refine Reid_B p p _ _ a,
  {exact s₁ a},
  {refl},
end,
have s₂ : prime p → divisors p = [p,1], from
begin
  intro,
  unfold divisors,
  rw [def_aux, mod_self p, ite_zero_eq_zero, s₅],
  refl,
  exact a
end,
have s₃ : (p ≥ 2) ∧ (divisors p = [p,1]) → myprime p, from
  begin intros, unfold myprime, assumption, end,
show prime p → myprime p, from
begin intro, apply s₃, split,
  exact s₁ a,
  exact s₂ a
end

lemma p_mod_p_ite (p : ℕ) : ite (p % p = 0) ([p] ++ divisors_aux p p) (divisors_aux p p)
  = [p] ++ divisors_aux p p :=
begin
  have o₁ : p % p = 0, from mod_self p,
  exact if_pos o₁,
end

lemma p_mod_a_ite (p a : ℕ) (h₁ : p % a = 0) :
  ite (p % a = 0) ([a] ++ divisors_aux p a) (divisors_aux p a)
  = [a] ++ divisors_aux p a := if_pos h₁

lemma prime_list_mem (p k : ℕ) (h₁ : divisors p = [p, 1]) (h₂ : k ∈ divisors p) : k = p ∨ k = 1 :=
begin
  rw h₁ at h₂,
  cases h₂,
  {
    exact or.inl h₂
  },
  {
    cases h₂,
    exact or.inr h₂,
    {
      have o₁ : false, from h₂,
      exact false.rec (k = p ∨ k = 1) o₁,
    },
  },
end

lemma a_in_div_aux (p a : ℕ) (h₁ : p % a = 0) : a ∈ divisors_aux p (a+1) :=
begin
  unfold divisors_aux,
  rw [p_mod_a_ite p a h₁],
  exact set.mem_insert a (λ (a : ℕ), list.mem a (list.append list.nil (divisors_aux p a))),
end

lemma div_aux_subset (p a b k : ℕ) (h₁ : a ≤ b) (h₂ : k ∈ divisors_aux p a) :
  k ∈ divisors_aux p b :=
begin
  --auto_cases, bug in auto_cases?
  check, --did not find induction here
         --auto_cases does not find this induction hyptoheis probably because h₁ : a ≤ b.
  induction h₁,
  {
    exact h₂,
  },
  {
    unfold divisors_aux,
    split_ifs,
    {
      exact set.mem_union_right (eq k) h₁_ih
    },
    {
      exact h₁_ih,
    }
  },
end

lemma k_mod_p_k_div_p (p k : ℕ) (h₁ : p % k = 0) (h₂ : 0 < p) : k ∈ divisors p :=
begin
  have o₁ : k ∈ divisors_aux p (k+1), from a_in_div_aux p k h₁,
  unfold divisors,
  have o₃ : k ∣ p, from dvd_of_mod_eq_zero h₁,
  have o₄ : k ≤ p, from le_of_dvd h₂ o₃,
  have o₂ : k < p + 1, from lt_succ_iff.mpr o₄,
  exact div_aux_subset p (succ k) (p + 1) k o₂ o₁,
end

lemma good_prime_my (p : ℕ) : myprime p → prime p :=
λ b,
begin
  have s₁ : (p ≥ 2), from b.left,
  have o₀ : divisors p = [p,1], from b.right,
  have s₂ : divisors p = [p,1] → (∀ k : ℕ, p % k = 0 → k = 1 ∨ k = p), from
  begin
    intros,
    rw or.comm,
    refine prime_list_mem p k o₀ _,
    have j₁ : 0 < p, from lt_of_succ_lt s₁,
    exact k_mod_p_k_div_p p k a_1 j₁
  end,
  have s₃ : ∀ k : ℕ, k ∣ p → p % k = 0, from λ a, mod_eq_zero_of_dvd,
  have s₄ : ∀ k : ℕ, k ∣ p → k = 1 ∨ k = p, from
  begin
    intros,
    exact s₂ o₀ k (s₃ k a),
  end,
  show prime p, from
  begin
    unfold prime,
    split,
    {
      exact s₁,
    },
    {
      exact s₄,
    }
  end
end
