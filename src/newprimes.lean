import data.nat.prime

open nat

def divisors_aux (n : ℕ) : ℕ → list ℕ
| 0     := []
| 1     := [1]
| (h+1) := if n % h = 0
           then [h] ++ divisors_aux h
           else divisors_aux h

def divisors (n :ℕ) := divisors_aux n (n+1)

def is_in_list (n : ℕ) : list ℕ → bool
| []     := false
| (h::t) := if h = n then true else is_in_list t

#eval divisors 5
#eval divisors 4

def myprime (p : ℕ) : Prop := (p ≥ 2) ∧ divisors p = [1,p]

lemma h_div_in_list (h n : ℕ) (t : list ℕ) : h ∣ n → is_in_list h (divisors n) :=
sorry

lemma my_prime_good (p n : ℕ) : prime p → myprime p :=
have s₁ : prime p → (p ≥ 2), from prime.two_le,
have s₄ : prime p → (n ∣ p → n = 1 ∨ n = p), from λ (pp : prime p), (dvd_prime pp).mp,
have s₂ : (n ∣ p → n = 1 ∨ n = p) → divisors p = [1,p], from
begin
  intro,
  sorry
end,
have s₃ : (p ≥ 2) ∧ (divisors p = [1,p]) → myprime p, from
  begin intros, unfold myprime, assumption, end,
show prime p → myprime p, from
begin intro, apply s₃, split,
  exact s₁ a,
  exact s₂ (s₄ a)
end
