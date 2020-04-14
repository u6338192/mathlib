--Assignment 3 Question 1, u6338192
--import tactic.interactive
import tactic.interactive
import tactic

--A function that takes a list of ℕ and a list of α and filters the list
--of α with the list of ℕ. Scott gave me this on Zulip.
def filter_list {α : Type} (l₁ : list ℕ) (l₂ : list α) : list α :=
  l₁.filter_map(λ x, l₂.nth x)

--Testing filter_list
#eval filter_list [0,1,3] [1,2,3,4,5,6,7,8]
#eval filter_list [1,2,4] [0,1,2,3,4,5]

--A function that checks if a number is in a list of ℕ.
def is_in_nat_list (m : ℕ) : list ℕ → bool
| []     := ff
| (h::t) := if h = m then tt else is_in_nat_list t

--Testing is_in_nat_list
#eval is_in_nat_list 4 [1,2,3,4]
#eval is_in_nat_list 5 [1,2,3,4]

--A function that takes a list of ℕ and returns a list of numbers which are
--not in the first list less than some number.
def nat_list_complement : ℕ → list ℕ → list ℕ
| 0 []     := [0]
| 0 l      := if is_in_nat_list 0 l then [] else [0]
| (n+1) [] := (n+1)::(nat_list_complement n [])
| (n+1) l  := if is_in_nat_list (n+1) l
                then nat_list_complement n l
                else (n+1)::(nat_list_complement n l)

--Testing nat_list_complement
#eval nat_list_complement 5 [5,3,2,1,4]
#eval nat_list_complement 5 [1,2,4]
def test_list := [4,7,4,7,9,0,8,4,3]
#eval nat_list_complement test_list.length test_list

--open the tactic and tactic.interactive namespaces.
open tactic
open tactic.interactive

--The actual tactic.interactive namespace, need this for itactic to work.
namespace tactic.interactive

--Focus_goals and Work_on_goals had a large amount of similar code, this has been
--factored out into this function.
meta def factored_stuff (p : interactive.parse lean.parser.pexpr) (tac : itactic)
  : tactic (list expr) :=
do gs ← get_goals,
   e ← to_expr p,
   l ← eval_expr (list ℕ) e,
   let lcomp := nat_list_complement gs.length l,
   let la := filter_list l gs,
   let lb := filter_list lcomp gs,
   if la = [] then
     fail "No goals were selected, check to make sure your list is non emtpy."
     else skip,
   set_goals la,
   all_goals tac,
   return lb

--The focus_goals tactic, allows the user to select the goals they wish
--to apply a list of tactics to, fails if the goals don't all succeed.
meta def focus_goals (p : interactive.parse lean.parser.pexpr) (tac : itactic)
  : tactic unit :=
do lb ← factored_stuff p tac,
   gs ← get_goals,
   if gs = [] then set_goals lb else fail "goals not discharged"

--The work_on_goals tactic, allows the user to select the goals they wish
--to apply a list of tactics to.
meta def work_on_goals' (p : interactive.parse lean.parser.pexpr) (tac : itactic) : tactic unit :=
do lb ← factored_stuff p tac,
   gs ← get_goals,
   set_goals (gs ++ lb)

meta def work_on_goals (p : interactive.parse lean.parser.pexpr) (tac : itactic) : tactic unit :=
do gs ← get_goals,
   e ← to_expr p,
   l ← eval_expr (list ℕ) e,
   let gl := l.filter_map (λ x, gs.nth x),
   let glc := gs.remove_all gl,
   set_goals gl,
   all_goals tac,
   gs ← get_goals,
   set_goals (gs ++ glc)

--The end of tactic.interactive
end tactic.interactive

--Toy Examples:

example : true ∧ 1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 = 4 ∧ 5 = 5 :=
begin
  split, swap,
  split, swap,
  split, swap,
  split, swap,
  split, swap,
  focus_goals [1,4,3] { trivial },
  focus_goals [1,2,0] { trivial },
end

example {a b c : ℕ} (h : a = b) (g : b = c) : a = c ∧ c = a :=
begin
  split,
  focus_goals [0] { rw h }, --This shows that focus_goals fails if the goals are not discharged
  focus_goals [0] { rw h },
end

example {a b c : ℕ} (h : a = b) (g : b = c) : a = c ∧ c = a :=
begin
  split,
  work_on_goals [0] { rw h, rw g },
  work_on_goals [0] { rw h },
  work_on_goals [0] { rw g },
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∨ q) ∧ r :=
begin
  split,
  focus_goals [1] { assumption },
  focus_goals [0] { right, use hq },
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∨ q) ∧ r :=
begin
  split,
  work_on_goals [1] { assumption },
  work_on_goals [0] { right, use hq },
end

example (a b : ℕ) : (a+b) = (b+a)  :=
begin
  focus_goals [0] { simp }
end

example (a b c : ℕ) : (a+b) = (b+a) ∧ (b+c) = (c+b) ∧ (a+c) = (c+a) :=
begin
  work_on_goals [0] { split, swap, split, },
  work_on_goals [0,2] { simp, },
  work_on_goals [0] { simp },
end

example (a b c : ℕ) : (a+b) = (b+a) ∧ (b+c) = (c+b) → (a+c) = (c+a) :=
begin
  focus_goals [0] { intro, simp },
end

example : ∀ (x : ℕ), ∃ (p₁ p₂ : ℕ), p₁ + p₂ = 2 * x :=
begin
  work_on_goals [0] { intro, split, split },
  work_on_goals [1,2] { assumption, },
  work_on_goals [0] { library_search },
end

example : ∀ (x : ℕ), ∃ (p₁ p₂ : ℕ), p₁ = x - 1 ∨ p₂ = x + 1 :=
begin
  work_on_goals [0] { intro, split, split, right },
  work_on_goals [1,2] { exact (x+1) },
  work_on_goals [0] { refl },
end
