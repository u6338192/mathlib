import tactic.suggest
import tactic.solve_by_elim
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

open interactive lean.parser interactive.types
open suggest
local postfix `?`:9001 := optional

namespace interactive

meta def cram (discharger : tactic unit := done) : tactic unit :=
tactic.cram >>= trace

--This tactic is suppose to be a mix between suggest and solve_by_elim.
--Solve_by_elim already works, just need it too print
meta def baby_back (all_goals : parse $ (tk "*")?)
 (no_dflt : parse only_flag)
 (hs : parse simp_arg_list)
 (attr_names : parse with_ident_list)
 (opt : by_elim_opt := { }) : tactic unit :=

--duplicate code
do [g] ← get_goals <|> fail "FAIL!",

   asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_elim { all_goals := all_goals.is_some, assumptions := return asms, ..opt },

   s ← read,
   m ← tactic_statement g,
   g ← instantiate_mvars g,

   trace m

end interactive

end tactic

example (a b c :ℕ) (h : a = b) (j : b < c) : a < c :=
begin
  rw h,
  exact j,
end

variables {m n k : ℕ}

theorem lt_of_sub_lt_sub_left : m - n < m - k → k < n :=
lt_imp_lt_of_le_imp_le (nat.sub_le_sub_left _)

example : m - n < m - k → k < n :=
begin solve_by_elim [lt_imp_lt_of_le_imp_le, nat.sub_le_sub_left], end

example : m - n < m - k → k < n :=
begin baby_back [lt_imp_lt_of_le_imp_le, nat.sub_le_sub_left], end
