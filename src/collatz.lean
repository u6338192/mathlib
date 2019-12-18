import tactic
import hotkeys

open tactic

def collatz (n : ℕ) : ℕ :=
if n % 2 = 0
  then n / 2
  else 3 * n + 1

#eval collatz 23

def collatz_comp : ℕ → ℕ → ℕ
| 0     m := m
| (n+1) m := collatz_comp n (collatz m)

#eval collatz_comp 15 23

--I'm not sure how to make this a non-meta definition
meta def collatz_list : ℕ → list ℕ
| 0     := []
| 1     := [1]
| (n+1) := [n+1] ++ collatz_list (collatz (n+1))

#eval collatz_list 63

def collatz_list_count : ℕ → ℕ → list ℕ
| 0     n := [n]
| (m+1) n := [n] ++ collatz_list_count m (collatz n)

#eval collatz_list_count 15 23

theorem strong_induction (P : ℕ → Prop) (h : ∀ n : ℕ, (∀ k : ℕ, k < n → P k) → P n) :
  ∀ n : ℕ, P n :=
begin
  intro n,
  have bc : P 0, from
    begin
      apply h,
      intros k j,
      exfalso,
      exact nat.not_succ_le_zero k j,
    end,
  have j : ∀ k : ℕ, k < n → P k, from
    begin
      induction n with n hnn,
      {
        intros,
        exfalso,
        exact nat.not_succ_le_zero k a,
      },
      {
        intros,
        have o₁ : P n, from h n hnn,
        --want to split into cases
        --1) k = n
        --2) K < n
        sorry,
      },
    end,
    exact h n j,
end

theorem collatz_conjecture (n : ℕ) : ∃ k : ℕ, collatz_comp k n = 1 :=
begin
  sorry,
end
