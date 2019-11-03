import tactic.suggest
import tactic.solve_by_elim
import data.nat.basic
import data.nat.prime

open tactic
open nat

namespace tactic

meta def cram : ℕ → tactic unit
| 0     := done <|> all_goals tactic.interactive.library_search
| (n+1) := done <|> all_goals (tactic.interactive.library_search >> cram n)

namespace interactive

meta def cram : tactic unit :=
tactic.cram 10000

end interactive

end tactic

open nat

example (n : ℕ) : ∃ a : ℕ, a > n ∧ prime (a-1) ∧ prime (a+1) :=
begin
  sorry
end
