/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison, Lucas Allen
-/

/-
Changes:
* added `dflt_list` and `mk_const_list`, and modified `mk_assumption_set` to use these.
* removed (discharger : tactic unit := done) from `library_search`, `suggest`, `suggest_scripts`
  `suggest_core`, `suggest_core'`, `apply_declaration` and `apply_and_solve`.
* Replaced by (opt : by_elim_opt := { }) from solve_by_elim.
* Replaced all occurences of `discharger` by `opt`, `opt.discharger`, or `..opt`
* Added (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  as inputs to `suggest` and `library_search`.
* inserted a `do` block into the interactive `library_search` function.
* Added `asms ← mk_assumption_set no_dflt hs attr_names,` to the interactive `suggest` and
  `library_search` functions.
* Added `g :: _ ← get_goals, AND
     if ¬(all_goals.is_some ∨ opt.backtrack_all_goals) then
     do { state ← read,
        let m := message g state,
        skip }
     else skip`
  to the interactive `solve_by_elim` function.
-/

/-
To do:
* Rewrite `suggest_core'` to make better use of `solve_by_elim.` DONE
  -> `suggest` and `library_search` don't remake the assumption set each time a lemma is applied.
* Get `solve_by_elim` to return a "try this" statement. DONE
* Namespaces. DONE
-/
import tactic.core
import data.mllist

namespace tactic

namespace output

/--
Replace any metavariables in the expression with underscores, in preparation for printing
`refine ...` statements.
-/
meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_mvar then some (unchecked_cast pexpr.mk_placeholder) else none)

/--
Construct a `refine ...` or `exact ...` string which would construct `g`.
-/
meta def tactic_statement (g : expr) : tactic string :=
do g ← instantiate_mvars g,
   g ← head_beta g,
   r ← pp (replace_mvars g),
   if g.has_meta_var
   then return (sformat!"Try this: refine {r}")
   else return (sformat!"Try this: exact {r}")

/--
Assuming that a goal `g` has been (partially) solved in the tactic_state `l`,
this function prepares a string of the form `exact ...` or `refine ...` (possibly with underscores)
that will reproduce that result.
-/
meta def message (g : expr) (l : tactic_state) : tactic string :=
do s ← read,
   write l,
   r ← tactic_statement g,
   write s,
   return r

end output

namespace solve_by_elim

/-- A list of names of lemmas for use in `solve_by_elim`. This list is only used in `mk_assumption_set`-/
meta def dflt_list : list name := [`rfl, `trivial, `congr_fun, `congr_arg]

meta def funcs : list name := [`rfl, `trivial, `congr_fun, `congr_arg,
                              `eq.refl, `eq.symm, `eq.trans, `eq.subst,
                              `and.intro, `and.elim_left, `and.elim_right,
                              `or.elim, `or.inl, `or.inr,
                              `iff.intro, `iff.elim_left, `iff.elim_right,
                              `propext,
                              `exists.intro, `exists.elim,
                              `false.elim]

/--
Builds a collection of lemmas for use in the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congr_fun` and `congr_arg`.
* The flag `no_dflt` removes these.
* The argument `hs` is a list of `simp_arg_type`s,
  and can be used to add, or remove, lemmas or expressions from the set.
* The argument `attr : list name` adds all lemmas tagged with one of a specified list of attributes.
-/
meta def mk_assumption_set (no_dflt : bool) (hs : list simp_arg_type) (attr : list name) : tactic (list expr) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   hs ← hs.mmap i_to_expr_for_apply,
   l ← attr.mmap $ λ a, attribute.get_instances a,
   let l := l.join,
   m ← list.mmap mk_const l,
   let hs := (hs ++ m).filter $ λ h, expr.const_name h ∉ gex,
   hs ← if no_dflt then
          return hs
        else
          do { dflt_exprs ← list.mmap mk_const dflt_list,
               return (dflt_exprs ++ hs) },
   if ¬ no_dflt ∨ all_hyps then do
    ctx ← local_context,
    return $ hs.append (ctx.filter (λ h, h.local_uniq_name ∉ hex)) -- remove local exceptions
   else return hs

/--
The internal implementation of `solve_by_elim`, with a limiting counter.
-/
meta def solve_by_elim_aux (discharger : tactic unit) (asms : tactic (list expr))  : ℕ → tactic unit
| 0 := done
| (n+1) := done <|>
              (apply_assumption asms $ solve_by_elim_aux n) <|>
              (discharger >> solve_by_elim_aux n)

/--
Configuration options for `solve_by_elim`.

* By default `solve_by_elim` operates only on the first goal,
  but with `backtrack_all_goals := true`, it operates on all goals at once,
  backtracking across goals as needed,
  and only succeeds if it dischargers all goals.
* `discharger` specifies a tactic to try discharge subgoals
  (this is only attempted on subgoals for which no lemma applies successfully).
* `assumptions` generates the list of lemmas to use in the backtracking search.
* `max_rep` bounds the depth of the search.
-/
meta structure by_elim_opt :=
  (backtrack_all_goals : bool := ff)
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := mk_assumption_set false [] [])
  (max_rep : ℕ := 3)

/--
`solve_by_elim` repeatedly tries `apply`ing a lemma
from the list of assumptions (passed via the `by_elim_opt` argument),
recursively operating on any generated subgoals.
It succeeds only if it discharges the first goal
(or with `backtrack_all_goals := tt`, if it discharges all goals.)
-/
meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
    (if opt.backtrack_all_goals then id else focus1) $
    solve_by_elim_aux opt.discharger opt.assumptions opt.max_rep

end solve_by_elim

open native

namespace suggest

open output
open solve_by_elim

/-- compute the head symbol of an expression, but normalise `>` to `<` and `≥` to `≤` -/
-- We may want to tweak this further?
meta def head_symbol : expr → name
| (expr.pi _ _ _ t) := head_symbol t
| (expr.app f _) := head_symbol f
| (expr.const n _) :=
  -- TODO this is a hack; if you suspect more cases here would help, please report them
  match n with
  | `gt := `has_lt.lt
  | `ge := `has_le.le
  | _   := n
  end
| _ := `_

/--
A declaration can match the head symbol of the current goal in four possible ways:
* `ex`  : an exact match
* `mp`  : the declaration returns an `iff`, and the right hand side matches the goal
* `mpr` : the declaration returns an `iff`, and the left hand side matches the goal
* `both`: the declaration returns an `iff`, and the both sides match the goal
-/
@[derive decidable_eq, derive inhabited]
inductive head_symbol_match
| ex | mp | mpr | both

open head_symbol_match

/-- a textual representation of a `head_symbol_match`, for trace debugging. -/
def head_symbol_match.to_string : head_symbol_match → string
| ex   := "exact"
| mp   := "iff.mp"
| mpr  := "iff.mpr"
| both := "iff.mp and iff.mpr"

/--
When we are determining if a given declaration is potentially relevant for the current goal,
we compute `unfold_head_symbol` on the head symbol of the declaration, producing a list of names.
We consider the declaration potentially relevant if the head symbol of the goal appears in this list.
-/
-- This is a hack.
meta def unfold_head_symbol : name → list name
| `false := [`not, `false]
| n      := [n]

/-- Determine if, and in which way, a given expression matches the specified head symbol. -/
meta def match_head_symbol (hs : name) : expr → option head_symbol_match
| (expr.pi _ _ _ t) := match_head_symbol t
| `(%%a ↔ %%b)      := if `iff = hs then some ex else
                       match (match_head_symbol a, match_head_symbol b) with
                       | (some ex, some ex) :=
                           some both
                       | (some ex, _) := some mpr
                       | (_, some ex) := some mp
                       | _ := none
                       end
| (expr.app f _)    := match_head_symbol f
| (expr.const n _)  := if list.mem hs (unfold_head_symbol n) then some ex else none
| _ := none

meta structure decl_data :=
(d : declaration)
(n : name)
(m : head_symbol_match)
(l : ℕ) -- cached length of name

/--
Generate a `decl_data` from the given declaration if
it matches the head symbol `hs` for the current goal.
-/
-- We used to check here for private declarations, or declarations with certain suffixes.
-- It turns out `apply` is so fast, it's better to just try them all.
meta def process_declaration (hs : name) (d : declaration) : option decl_data :=
let n := d.to_name in
if ¬ d.is_trusted ∨ n.is_internal then
  none
else
  (λ m, ⟨d, n, m, n.length⟩) <$> match_head_symbol hs d.type

/-- Retrieve all library definitions with a given head symbol. -/
meta def library_defs (hs : name) : tactic (list decl_data) :=
do env ← get_env,
   return $ env.decl_filter_map (process_declaration hs)

/--
Apply the lemma `e`, then attempt to close all goals using `solve_by_elim { discharger := discharger }`,
failing if `close_goals = tt` and there are any goals remaining.
-/
-- Implementation note: as this is used by both `library_search` and `suggest`,
-- we first run `solve_by_elim` separately on a subset of the goals, whether or not `close_goals` is set,
-- and then if `close_goals = tt`, require that `solve_by_elim { all_goals := tt }` succeeds
-- on the remaining goals.
meta def apply_and_solve (close_goals : bool) (opt : by_elim_opt := { }) (e : expr) : tactic unit :=
apply e >>
-- Phase 1
-- Run `solve_by_elim` on each "safe" goal separately, not worrying about failures.
-- (We only attempt the "safe" goals in this way in Phase 1. In Phase 2 we will do
-- backtracking search across all goals, allowing us to guess solutions that involve data, or
-- unify metavariables, but only as long as we can finish all goals.)
try (any_goals (independent_goal >> solve_by_elim { ..opt })) >>
-- Phase 2
(done <|>
  -- If there were any goals that we did not attempt solving in the first phase
  -- (because they weren't propositional, or contained a metavariable)
  -- as a second phase we attempt to solve all remaining goals at once (with backtracking across goals).
  any_goals (success_if_fail independent_goal) >>
  solve_by_elim { backtrack_all_goals := tt, ..opt } <|>
  -- and fail unless `close_goals = ff`
  guard ¬ close_goals)

/--
Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the goal using `apply_and_solve`.
-/
meta def apply_declaration (close_goals : bool) (opt : by_elim_opt := { }) (d : decl_data) : tactic unit :=
let tac := apply_and_solve close_goals opt in
do (e, t) ← decl_mk_const d.d,
   match d.m with
   | ex   := tac e
   | mp   := do l ← iff_mp_core e t, tac l
   | mpr  := do l ← iff_mpr_core e t, tac l
   | both :=
      (do l ← iff_mp_core e t, tac l) <|>
      (do l ← iff_mpr_core e t, tac l)
   end

/-- An `application` records the result of a successful application of a library lemma. -/
meta structure application :=
(state     : tactic_state)
(script    : string)
(decl      : option declaration)
(num_goals : ℕ)
(hyps_used : ℕ)

end suggest

open output
open solve_by_elim
open suggest

declare_trace suggest         -- Trace a list of all relevant lemmas

-- implementation note: we produce a `tactic (mllist tactic application)` first,
-- because it's easier to work in the tactic monad, but in a moment we squash this
-- down to an `mllist tactic application`.
private meta def suggest_core' (opt : by_elim_opt := { }) :
  tactic (mllist tactic application) :=
do g :: _ ← get_goals,
   hyps ← local_context,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (lock_tactic_state (do
     focus1 $ solve_by_elim { ..opt },
     s ← read,
     m ← tactic_statement g,
     g ← instantiate_mvars g,
     return $ mllist.of_list [⟨s, m, none, 0, hyps.countp(λ h, h.occurs g)⟩])) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
   t ← infer_type g,
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `suggest) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),

   -- Try applying each lemma against the goal,
   -- then record the number of remaining goals, and number of local hypotheses used.
   return $ (mllist.of_list defs).mfilter_map
   -- (This tactic block is only executed when we evaluate the mllist,
   -- so we need to do the `focus1` here.)
   (λ d, lock_tactic_state $ focus1 $ do
     apply_declaration ff opt d,
     ng ← num_goals,
     g ← instantiate_mvars g,
     state ← read,
     m ← message g state,
     return
     { application .
       state := state,
       decl := d.d,
       script := m,
       num_goals := ng,
       hyps_used := hyps.countp(λ h, h.occurs g) }))

/--
The core `suggest` tactic.
It attempts to apply a declaration from the library,
then solve new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from the library,
* `script`, a string of the form `refine ...` or `exact ...` which will reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
meta def suggest_core (opt : by_elim_opt := { }) : mllist tactic application :=
(mllist.monad_lift (suggest_core' opt)).join

/--
See `suggest_core`.

Returns a list of at most `limit` `application`s,
sorted by number of goals, and then (reverse) number of hypotheses used.
-/
meta def suggest (limit : option ℕ := none) (opt : by_elim_opt := { }) : tactic (list application) :=
do let results := suggest_core opt,
   -- Get the first n elements of the successful lemmas
   L ← if h : limit.is_some then results.take (option.get h) else results.force,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   return $ L.qsort(λ d₁ d₂, d₁.num_goals < d₂.num_goals ∨ (d₁.num_goals = d₂.num_goals ∧ d₁.hyps_used ≥ d₂.hyps_used))

/--
Returns a list of at most `limit` strings, of the form `exact ...` or `refine ...`, which make
progress on the current goal using a declaration from the library.
-/
meta def suggest_scripts (limit : option ℕ := none) (opt : by_elim_opt := { }) : tactic (list string) :=
do L ← suggest limit opt,
   return $ L.map application.script

/--
Returns a string of the form `exact ...`, which closes the current goal.
-/
meta def library_search (opt : by_elim_opt := { }) : tactic string :=
(suggest_core opt).mfirst (λ a, do guard (a.num_goals = 0), write a.state, return a.script)

open interactive lean.parser interactive.types
local postfix `?`:9001 := optional

namespace interactive
/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

alternatively, when encountering an assumption of the form `sg₀ → ¬ sg₁`,
after the main approach failed, the goal is dismissed and `sg₀` and `sg₁`
are made into the new goal.

optional arguments:
- asms: list of rules to consider instead of the local constants
- tac:  a tactic to run on each subgoals after applying an assumption; if
        this tactic fails, the corresponding assumption will be rejected and
        the next one will be attempted.
-/
meta def apply_assumption
  (asms : tactic (list expr) := local_context)
  (tac : tactic unit := return ()) : tactic unit :=
tactic.apply_assumption asms tac

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_rep` recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if `apply_assumption` chooses an unproductive assumption.

By default, the assumptions passed to apply_assumption are the local context, `rfl`, `trivial`, `congr_fun` and
`congr_arg`.

`solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas.

`solve_by_elim with attr₁ ... attrᵣ also applied all lemmas tagged with the specified attributes.

`solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `rfl`, `trivial`, `congr_fun`, or `congr_arg`
unless they are explicitly included.

`solve_by_elim [-id]` removes a specified assumption.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments:
- discharger: a subsidiary tactic to try at each step (e.g. `cc` may be helpful)
- max_rep: number of attempts at discharging generated sub-goals
-/
meta def solve_by_elim (all_goals : parse $ (tk "*")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) :
  tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   g :: _ ← get_goals,
   tactic.solve_by_elim.solve_by_elim
   { backtrack_all_goals := all_goals.is_some ∨ opt.backtrack_all_goals,
     assumptions := return asms,
     ..opt },
     if ¬(all_goals.is_some ∨ opt.backtrack_all_goals) then
     do { state ← read,
        m ← message g state,
        trace m }
     else skip

declare_trace silence_suggest -- Turn off `exact/refine ...` trace messages for `suggest`

/--
`suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.
-/
meta def suggest (n : parse (with_desc "n" small_nat)?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) :
  tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   L ← tactic.suggest_scripts (n.get_or_else 50) { assumptions := return asms, ..opt },
  if is_trace_enabled_for `silence_suggest then
    skip
  else
    if L.length = 0 then
      fail "There are no applicable declarations"
    else
      L.mmap trace >> skip

declare_trace silence_library_search -- Turn off `exact ...` trace message for `library_search

/--
`library_search` attempts to apply every definition in the library whose head symbol
matches the goal, and then discharge any new goals using `solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.
-/
meta def library_search (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (opt : by_elim_opt := { }) :
  tactic unit :=
do asms ← mk_assumption_set no_dflt hs attr_names,
   tactic.library_search { assumptions := return asms, ..opt } >>=
if is_trace_enabled_for `silence_library_search then
  (λ _, skip)
else
  trace
end interactive

end tactic

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {X : Type} (x : X) : x = x :=
by solve_by_elim

example : true :=
by solve_by_elim

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : ∀ x : α, b x = a x) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
  success_if_fail { solve_by_elim only [] },
  success_if_fail { solve_by_elim only [h₀] },
  solve_by_elim only [h₀, congr_fun]
end

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim [h₀]

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
 success_if_fail { solve_by_elim [*, -h₀] },
 solve_by_elim [*]
end

example {α β : Type} (a b : α) (f : α → β) (i : function.injective f) (h : f a = f b) : a = b :=
begin
  success_if_fail { solve_by_elim only [i] },
  success_if_fail { solve_by_elim only [h] },
  solve_by_elim only [i,h]
end

@[user_attribute]
meta def ex : user_attribute := {
  name := `ex,
  descr := "An example attribute for testing solve_by_elim."
}

@[ex] def f : ℕ := 0

example : ℕ := by solve_by_elim [f]

example : ℕ :=
begin
  success_if_fail { solve_by_elim },
  success_if_fail { solve_by_elim [-f] with ex },
  solve_by_elim with ex,
end

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end

open tactic

example : true :=
begin
  (do gs ← get_goals,
     set_goals [],
     success_if_fail `[solve_by_elim],
     set_goals gs),
  trivial
end

example {α : Type} (r : α → α → Prop) (f : α → α → α)
  (l : ∀ a b c : α, r a b → r a (f b c) → r a c)
  (a b c : α) (h₁ : r a b) (h₂ : r a (f b c)) : r a c :=
begin
  solve_by_elim,
end

-- Verifying that `solve_by_elim*` acts on all remaining goals.
example (n : ℕ) : ℕ × ℕ :=
begin
  split,
  solve_by_elim*,
end

-- Verifying that `solve_by_elim*` backtracks when given multiple goals.
example (n m : ℕ) (f : ℕ → ℕ → Prop) (h : f n m) : ∃ p : ℕ × ℕ, f p.1 p.2 :=
begin
  repeat { split },
  solve_by_elim*,
end

example {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
begin
  apply le_trans,
  solve_by_elim { backtrack_all_goals := true },
end
