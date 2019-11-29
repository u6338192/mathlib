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

meta def tactics_list : list (tactic string) :=
[ reflexivity                                 >> pure "refl",
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  ext1_wrapper,
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  --propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  propositional_goal >> sbe_string,
  `[unfold_coes]                              >> pure "unfold_coes",
  `[unfold_aux]                               >> pure "unfold_aux",
  --Following tactics added by lucas
  split                                       >> pure "split",
  `[split_ifs]                                >> pure "split_ifs",
  swap                                        >> pure "swap",
  `[ring]                                     >> pure "ring",
  `[push_neg]                                 >> pure "push_neg",
  `[contrapose]                               >> pure "contrapose",
  `[finish]                                   >> pure "finish",
  `[tauto]                                    >> pure "tauto",
  `[cc]                                       >> pure "cc",
  --End additions
  tidy.run_tactics ]

meta def check (discharger : tactic unit := skip) : tactic unit :=
do tactics_list.mmap (λ t, (do state ← read, str ← t, trace str, discharger, write state) <|> skip),
   skip

-- meta def check_list_aux : ℕ → list string → tactic(list (list string))
-- | 0     [] := none
-- | 0     L  := some [L]
-- | (n+1) L  := lock_tactic_state (do
--                  tactics_list.mmap (λ t, (do str ← t,
--                                              CL ← check_list_aux n (L ++ [str]),
--                                              return (list.intercalate ["],["] CL))
--                                              <|>
--                                              (return [])))

-- meta def check_list (n : ℕ := 3) : tactic unit :=
-- do L ← check_list_aux n [],
--    L.mmap(λ l, trace l),
--    skip

--ideally this would produce a list (list string), where each list of strings
--is a successful chain of tactics. Note I think this is done in the chain tactic.
meta def check_list_aux : ℕ → list string → tactic (list string)
| 0     [] := none
| 0     L  := do return L
| (n+1) L  := do A ← tactics_list.mmap (λ t, lock_tactic_state
                                        (do str ← t,
                                            let L' := L ++ [str],
                                            C ← check_list_aux n L',
                                            return C)
                                        <|> return [""]),
                 return (flatten_list A)

meta def check_list (n : ℕ := 3) : tactic unit :=
do L ← tactics_list.mmap (λ t, lock_tactic_state ((do str ← t, return str) <|> return "")),
   T ← check_list_aux n L,
   T.mmap (λ str, trace str),
   skip

open interactive lean.parser interactive.types
open tactic tactic.suggest
local postfix `?`:9001 := optional

namespace tactic.interactive

meta def bb (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)  (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) : tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.baby_back { all_goals := all_goals.is_some, discharger := skip, assumptions := return asms, ..opt }

end tactic.interactive

example (n m : ℕ) : n * m = m * n :=
begin
  check_list,
  sorry,
end
