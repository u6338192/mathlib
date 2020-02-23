import tactic
import hotkeys
import data.nat.parity

open tactic
open nat

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
        rw nat.lt_succ_iff_lt_or_eq at a,
        cases a,
        { exact hnn k a, },
        { rw a, exact h n hnn, },
      },
    end,
  exact h n j,
end

lemma collatz_on_odd (n a b k : ℕ) (h₀ : 1 ≤ k) (h₁ : n = 2^k * a + b) (h₂ : b % 2 = 1) :
  collatz n = 3 * 2^k * a + collatz b :=
begin
  unfold collatz,
  have o₁ : ¬b % 2 = 0, from
  begin
    rw h₂,
    exact of_to_bool_ff rfl,
  end,
  have o₂ : ¬n % 2 = 0, from
  begin
    rw h₁,
    rw ← even_iff at o₁,
    rw ← even_iff at *,
    simp [h₂] with parity_simps,
    intro,
    cases a_1,
    apply o₁,
    apply a_1_mpr,
    left,
    intro,
    rw a_1 at h₀,
    exact not_succ_le_zero 0 h₀,
  end,
  split_ifs,
  rw h₁,
  ring,
end

lemma collatz_add (k l n : ℕ) : collatz_comp k (collatz_comp l n) = collatz_comp (k + l) n :=
begin
  revert n,
  induction l with l hl,
  {
    intro n,
    have o₁ : collatz_comp 0 n = n, from rfl,
    rw [o₁, add_zero],
  },
  {
    have o₂ : nat.succ l = l + 1, from rfl,
    rw o₂ at *,
    intro n,
    rw ←add_assoc,
    have o₃ : collatz_comp (l + 1) n = collatz_comp l (collatz n), from rfl,
    have o₄ : collatz_comp (k + l + 1) n = collatz_comp (k + l) (collatz n), from rfl,
    rw [o₃, o₄],
    exact hl (collatz n),
  },
end

lemma collatz_chain (n m : ℕ) (h₁ : ∃ k : ℕ, collatz_comp k m = 1)
  (h₂ : ∃ l : ℕ, collatz_comp l n = m) : ∃ j : ℕ, collatz_comp j n = 1 :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  rw ←hl at hk,
  rw collatz_add at hk,
  use (k + l),
  exact hk,
end

def collatz_prop (n : ℕ) : Prop := ∃ l : ℕ, collatz_comp l n = 1

theorem collatz_conjecture (n : ℕ) : ∃ k : ℕ, collatz_comp k n = 1 :=
begin
  apply strong_induction collatz_prop,
  intros m kpop,
  dsimp [collatz_prop] at *,
  sorry,
  --Experimenting
  --apply collatz_chain,
end
