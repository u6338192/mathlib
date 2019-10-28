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

open suggest

meta def solve_by_suggest_aux (discharger : tactic unit)
  (asms : tactic (list expr))
  (g : expr) : ℕ → tactic unit
| 0 := do trace (tactic_statement g)
| (n+1) := do (do done, [g] ← get_goals <|> fail "FAIL!!!", trace (tactic_statement g))
              <|>
              (apply_assumption asms $ solve_by_suggest_aux n) <|>
              (discharger >> solve_by_suggest_aux n)

meta structure by_suggest_opt :=
  (all_goals : bool := ff)
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := mk_assumption_set false [] [])
  (max_rep : ℕ := 3)

meta def solve_by_suggest (opt : by_elim_opt := { }) : tactic unit :=
do
  [g] ← get_goals <|> fail "FAIL!!!",
  tactic.fail_if_no_goals,
  (if opt.all_goals then id else focus1) $
    solve_by_suggest_aux opt.discharger opt.assumptions g opt.max_rep

open interactive lean.parser interactive.types
local postfix `?`:9001 := optional

namespace interactive

meta def cram (discharger : tactic unit := done) : tactic unit :=
tactic.cram >>= trace

--TODO
--*get baby_back to print all possible refine statements
--*Some major refactoring including suggest and solve_by_elim

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
   tactic.solve_by_elim { all_goals := all_goals.is_some, discharger := skip, assumptions := return asms, ..opt },

   --s ← read,
   trace (tactic_statement g)


meta def solve_by_suggest (all_goals : parse $ (tk "*")?)
 (no_dflt : parse only_flag)
 (hs : parse simp_arg_list)
 (attr_names : parse with_ident_list)
 (opt : by_elim_opt := { }) : tactic unit :=
 do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.solve_by_suggest { all_goals := all_goals.is_some, discharger := skip, assumptions := return asms, ..opt }

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

example {m : nat} : max 0 m = m :=
begin baby_back end
--max_eq_right (zero_le _)

example {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
begin baby_back [nat.lt_succ_iff, lt_imp_lt_of_le_imp_le, nat.sub_le_sub_left] end

example {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
begin baby_back [eq_zero_of_le_div, le_refl] end
--eq_zero_of_le_div (le_refl _) h

example {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
begin suggest, solve_by_suggest [le_refl] end
