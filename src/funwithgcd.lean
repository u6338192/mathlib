import init.meta.well_founded_tactics
import tactic.basic

open well_founded

lemma lt (a b : ℕ) (h : b > 0) : (b - (b/a)*a) < b :=
begin
  library_search
end

def gcd_luc : ℕ → ℕ → ℕ
| a 0 := a
| 0 b := b
| a b := have (b - (b/a)*a) < b, from lt a b,
         have (a - (a/b)*b) < a, from lt b a,
         if a < b then gcd_luc a (b - (b/a)*a)
                  else gcd_luc (a - (a/b)*b) b
