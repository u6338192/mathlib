import init.meta.well_founded_tactics
import tactic.basic

open well_founded

lemma lt (a b : ℕ) (h₂ : a < b) (h₃ : 0 < a) : (b - (b/a)*a) < b :=
begin
  have h : 0 < b, from sorry,
  refine nat.sub_lt h _,
  refine (nat.div_lt_iff_lt_mul 0 (b / a) h₃).mp _,
  rw nat.div_def,
  rw nat.div_def,
  rw nat.div_def,
  rw nat.div_def,
  squeeze_simp,
  suggest,
end

def gcd_luc : ℕ → ℕ → ℕ
| a 0 := a
| 0 b := b
| (a + 1) (b + 1) := have (b - (b/a)*a) < b, from lt a b,
         have (a - (a/b)*b) < a, from lt b a,
         if a < b then gcd_luc a (b - (b/a)*a)
                  else gcd_luc (a - (a/b)*b) b
