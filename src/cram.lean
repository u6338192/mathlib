import tactic.suggest
import data.nat.basic

open tactic
open nat

namespace tactic

meta def cram_old (discharger : tactic unit := done) : tactic string :=
(suggest_core discharger).mfirst
  (λ a : suggest.application,
    do guard (a.num_goals = 0 ∨ a.num_goals = 1),
       write a.state,
       return a.script)

meta def cram' (discharger : tactic unit := done) : tactic string :=
(suggest_core discharger).mfirst
  (λ a : suggest.application,
    do guard (a.num_goals = 0 ∨ a.num_goals = 1),
       if a.num_goals = 0 then do write a.state, return a.script
       else if a.num_goals = 1 then do write a.state, script ← library_search, return script
       else fail "")

meta def cram (discharger : tactic unit := done) : tactic string :=
(suggest_core discharger).mfirst
  (λ a : suggest.application,
    do guard (a.num_goals = 1), write a.state, script ← library_search, return script)

-- want to filter this mllist so that we only have the results with num_goals = 1.
-- want recurse on cram so that to some depth, and if the goal is solved return the message
-- just like library_search.

namespace interactive

meta def cram (discharger : tactic unit := done) : tactic unit :=
tactic.cram >>= trace

end interactive

end tactic

example (a b c :ℕ) (h : a = b) (j : b < c) : a < c :=
begin
  rw h,
  exact j,
end
