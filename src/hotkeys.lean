import tactic
import tactic.tidy
import init.meta.lean.parser

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
  --End additions
  tidy.run_tactics ]

meta def check (discharger : tactic unit := skip) : tactic unit :=
do tactics_list.mmap (λ t, (do state ← read, str ← t, trace str, discharger, write state) <|> skip),
   skip

meta def check_list_aux : ℕ → list string → tactic(list (list string))
| 0     [] := none
| 0     L  := some [L]
| (n+1) L  := lock_tactic_state (do
                 tactics_list.mmap (λ t, (do str ← t,
                                             CL ← check_list_aux n (L ++ [str]),
                                             return (list.intercalate ["],["] CL))
                                             <|>
                                             (return [])))


meta def check_list (n : ℕ := 3) : tactic unit :=
do L ← check_list_aux n [],
   L.mmap(λ l, trace l),
   skip
