import algebra.big_operators
import data.finsupp
import tactic.interactive
import tactic.converter.interactive

open tactic
open finset

namespace conv.interactive

meta def operand_core (t : conv.interactive.itactic) : conv unit :=
do (r, lhs, _) ← target_lhs_rhs,
   guard (r = `eq),
   lam ← match lhs with
     | `(finset.sum  %%S %%lam) := tactic.applyc `finset.sum_congr >> skip >> return lam
     | `(finset.prod %%S %%lam) := tactic.applyc `finset.prod_congr >> skip >> return lam
     | `(finsupp.sum  %%S %%lam) := tactic.applyc `finsupp.sum_congr >> `[rotate 2] >> `[exact f₂] >> skip >> return lam
     | `(finsupp.prod %%S %%lam) := tactic.applyc `finsupp.prod_congr >> skip >> return lam
     | `(fold %%op %%b %%lam %%S)   := tactic.applyc `finset.fold_congr >> return lam
     | _                        := tactic.fail "The goal expression is not in the correct form."
   end,
   (a::gs) ← get_goals,
   set_goals [a],
   intro `s,
   intro `s_mem,   
   t

--Note: for mathlib this will be in tactic.converter.interactive
meta def zoom (t : conv.interactive.itactic) : conv unit :=
do transitivity,
   a :: rest ← get_goals,
   set_goals [a],
   t,
   all_goals reflexivity,
   set_goals rest
   
meta def operand (t : conv.interactive.itactic) : conv unit :=
zoom (operand_core t)

end conv.interactive
