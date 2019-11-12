import algebra.group
import algebra.big_operators
import data.nat.prime
import data.nat.modeq
import data.zmod.basic
import hotkeys

open nat

theorem wilson (n : ℕ) (h₁ : 1 < n) : prime n ↔ n ∣ (1 + fact (n-1)) :=
begin
  sorry,
end

lemma bezouts (n m : ℕ) (h₁ : coprime n m) : ∃ a b : ℤ, a * n + b * m = 1 := sorry

lemma zero (a b c : ℕ) : modeq b b 0 :=
begin
  unfold modeq,
  have o₁ : b % b = 0, from mod_self b,
  have o₂ : 0 % b = 0, from zero_mod b,
  rw [o₁,o₂],
end

lemma one (a b c : ℕ) : modeq b (a*b) 0 :=
begin
  unfold modeq,
  have o₁ : (a * b) % b = 0, from mul_mod_left a b,
  have o₂ : 0 % b = 0, from zero_mod b,
  rw [o₁,o₂],
end

lemma two (a b c : ℕ) : modeq b (a + b) a :=
begin
  unfold modeq,
  exact add_mod_right a b,
end

example (a b c : ℕ) : modeq b (c + a*b) c :=
begin
  unfold modeq,
  exact add_mul_mod_self_right c a b,
end

example (a b c : ℕ) : c + a*b ≡ c [MOD b] :=
begin
  --unfold modeq,
  exact add_mul_mod_self_right c a b,
end

lemma inverse (n m : ℕ) (h₁ : prime n) (h₂ : ¬ n ∣ m) : ∃ b : ℤ, m * b ≡ 1 [ZMOD n] :=
begin
  have s₁ : coprime n m, from (prime.coprime_iff_not_dvd h₁).mpr h₂,
  have s₂ : ∃ a b : ℤ, a * n + b * m = 1, from bezouts n m s₁,
  cases s₂,
  cases s₂_h,
  split,
  swap,
  exact s₂_h_w,
  have s₃ : s₂_w * ↑n + s₂_h_w * ↑m ≡ s₂_h_w * ↑m [ZMOD ↑n], from
  begin
    unfold modeq,
    apply add_mul_mod_self_right,
  end,
  rw s₂_h_h at s₃,
  rw mul_comm at s₃,
  exact int.modeq.symm s₃
end


theorem wilson' (n : ℕ) (h₁ : 1 < n) : prime n ↔ (fact (n-1)) ≡ n-1 [MOD n] :=
begin
  split,
  {

  },
end

theorem wilson'' (n : ℕ) (h₁ : 1 < n) : prime n ↔ (fact (n-1)) ≡ n-1 [ZMOD n] :=
begin
  split,
  {

  },
end
