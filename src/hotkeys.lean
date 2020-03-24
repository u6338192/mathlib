import tactic
import tactic.tidy
import init.meta.lean.parser
import baby_back_new

open tactic
open tactic.tidy
open parser

meta def lib : tactic unit :=
tactic.interactive.library_search

meta def ac : tactic unit :=
do str ← auto_cases,
   trace str

meta def sbe_string (num : ℕ := 5) : tactic string :=
do (g::s) ← get_goals,
   solve_by_elim {max_rep := num},
   tactic.suggest.tactic_statement g

meta def sbe (num : ℕ := 5) : tactic unit :=
trace (sbe_string num)

/-- calls `cases` on every local hypothesis, succeeding if
    it succeeds on at least one hypothesis. -/
--modify this so it reports all successful application of cases and induction
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed

--This is stuff for learning about exprs.
meta def trace_expr (e : expr) : tactic unit :=
do t ← infer_type e,
   trace (to_string t)

meta def trace_type : tactic unit :=
do (g::gs) ← get_goals,
   trace_expr g

meta def trace_list_type : list expr → tactic unit
| [] := skip
| (e::es) := trace_expr e >> trace_list_type es

meta def trace_assumption_type : tactic unit :=
do ctx ← local_context,
   trace_list_type ctx

--This function takes a proof expr and gives the type that's proven
meta def trace_infered_type (e : expr) : tactic unit :=
do t ← infer_type e,
   trace t
--End learning expr stuff

open interactive lean.parser interactive.types
open tactic tactic.suggest
local postfix `?`:9001 := optional

-- namespace tactic.interactive

-- meta def bb (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)  (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) : tactic unit :=
-- do asms ← mk_assumption_set no_dflt hs attr_names,
--    tactic.baby_back { all_goals := all_goals.is_some, discharger := skip, assumptions := return asms, ..opt }

-- end tactic.interactive

-- example (n m : ℕ) : n * m = m * n :=
-- begin
--   check_list,
--   sorry,
-- end
