import tactic.suggest
import tactic.solve_by_elim
import data.nat.basic

open interactive lean.parser interactive.types
open tactic tactic.suggest
local postfix `?`:9001 := optional

namespace tactic

-- meta def baby_back_aux (discharger : tactic unit) (asms : tactic (list expr)) (g : expr) : ℕ → tactic unit
-- | 0 := skip--trace (tactic_statement g) --done
-- | (n+1) := --done <|>
--               (apply_assumption asms $ trace (tactic_statement g) >> baby_back_aux n) <|>
--               (discharger >> baby_back_aux n)
--               --(trace (tactic_statement g))

-- meta def baby_back (opt : by_elim_opt := { }) : tactic unit :=
-- do
--   tactic.fail_if_no_goals,
--   (if opt.all_goals then id else focus1) $ do
--     [g] ← get_goals,
--     baby_back_aux opt.discharger opt.assumptions g opt.max_rep
--     --trace (tactic_statement g)

meta def baby_back_aux (discharger : tactic unit) (asms : tactic (list expr)) (g : expr) : ℕ → tactic unit
| 0 := trace (tactic_statement g)
| (n+1) := (done >> trace (tactic_statement g)) <|>
           lock_tactic_state
             (do L ← asms,
                 L.mmap (λ e, apply e >> baby_back_aux n <|> trace (tactic_statement g)),
                 skip)


meta def baby_back (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  (if opt.all_goals then id else focus1) $ do
    [g] ← get_goals,
    baby_back_aux opt.discharger opt.assumptions g opt.max_rep

namespace interactive

meta def baby_back (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)  (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) : tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.baby_back { all_goals := all_goals.is_some, discharger := skip, assumptions := return asms, ..opt }

end interactive

end tactic

open nat

example {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
begin baby_back [nat.lt_succ_iff, lt_imp_lt_of_le_imp_le, nat.sub_le_sub_left] end

example {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
begin baby_back [eq_zero_of_le_div, le_refl] end

example {m n k : ℕ} : m - n < m - k → k < n :=
begin baby_back [lt_imp_lt_of_le_imp_le, nat.sub_le_sub_left], end

example {m : nat} : max 0 m = m :=
begin baby_back end

example {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
begin
  baby_back [eq_zero_of_le_div],
  baby_back [le_refl],
  baby_back,
end

--* `solve_by_elim` is doing more than what is being printed out.
--* cntrl clicking on .force in suggest takes you to `not`vfor some reason.
--* should solve by elim use absurd?
example {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
begin
  --suggest,
  --baby_back [eq_zero_of_le_div],
  refine eq_zero_of_le_div _ _,
  --baby_back [le_refl],
  exact 2,
  exact le_refl 2,
  --baby_back,
  exact h
end

example (a : Prop) (h₁ : a) (h₂ : ¬a) : false := by library_search
