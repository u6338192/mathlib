import hotkeys
import meta.expr
import tactic.core

open expr
open tactic
open binder_info

def n : ℕ := 3
def F : ℕ → ℕ := λ n, n + 1

#eval trace_infered_type `(λ (n : ℕ), F n)
#eval trace_infered_type `(F n)

meta def ccc : tactic unit :=
do m ← mk_const `F,
   b ← mk_const `n,
   let ee := expr.app m b,
   let eee := expr.lam `b implicit b m,

   trace_infered_type m,
   trace_infered_type b,
   trace_infered_type ee,
   trace_infered_type eee,
   trace_infered_type `(λ n, F n),
   trace `(λ n, F n)

#eval ccc

/-
A quick overview:

    intro x replaces the goal with \lam x, _
    apply f replaces the goal with f _ _ _
    refine e1 (e2 _) (e3 _) replaces the goal with e1 (e2 _) (e3 _) (which should make it clear why I say sometimes that refine is the "universal" tactic, capable of playing the role of all others)
    exact e replaces the goal with e
    change foo replaces the goal with (_ : foo)
    rw foo replaces the goal with eq.rec_on foo _
    induction foo replaces the goal with T.rec_on foo _ _ where T is the type of foo
    cases foo replaces the goal with T.cases_on foo _ _ where T is the type of foo
    split replaces the goal with and.intro _ _
    have x := t replaces the goal with (\lam x, _) t
    let x := t replaces the goal with let x := t in _
    revert x replaces the goal with _ x
-/

meta def funcs : list name := [`rfl, `trivial, `congr_fun, `congr_arg,
                              `eq.refl, `eq.symm, `eq.trans, `eq.subst,
                              `and.intro, `and.elim_left, `and.elim_right,
                              `or.elim, `or.inl, `or.inr,
                              `iff.intro, `iff.elim_left, `iff.elim_right,
                              `propext,
                              `exists.intro, `exists.elim,
                              `false.elim,
                              `classical.em, `classical.by_contradiction] --classical stuff
                              -- , `nat.cases_on, `nat.rec_on]
                              --want to be able to do: intro, revert, induction, cases, rw.

variables a b c d : ℕ

#eval trace_infered_type `(trivial)
#eval trace_infered_type `(@rfl.{1} nat (@bit1.{0} nat nat.has_one nat.has_add
                          (@has_one.one.{0} nat nat.has_one)))
#eval trace_infered_type `(@bit1.{0} nat nat.has_one nat.has_add
                          (@has_one.one.{0} nat nat.has_one))
#eval trace_infered_type `(ℕ)
#eval trace_infered_type `(λ (p q : Prop) (h : p) (j : q), @and.intro p q h j)
#eval trace_infered_type `(λ (p q : Prop), @and.intro p q)
#eval trace_infered_type `(λ (p q : Prop) (h : p) (j : q), and.intro h j)

set_option pp.all true
lemma rfl_check : 3 = 3 := rfl
#print rfl_check

meta def vars : list name := [`a, `b, `c, `d]

meta def mk_const_list (L : list name) : tactic (list expr) := L.mmap mk_const

meta def print_func_types (L : list name) : tactic unit :=
do le ← mk_const_list L,
   le.mmap' trace_infered_type

#eval print_func_types funcs
-- #eval print_func_types vars -- ERROR: unknown declaration 'a'

meta def print_simp_lemma : list name → tactic unit
| []     := skip
| (h::t) := do v ← is_simp_lemma h,
            if v then do trace "Y" else trace "N",
            print_simp_lemma t

#eval print_simp_lemma vars
#eval print_simp_lemma funcs

--Need to figure out what to do here
meta def recurse_build : list expr → list expr
| []     := []
| (h::t) := []

meta def expr_tac : expr → tactic unit
| (expr.lam _ _ t u) := trace "lambda!" >> expr_tac t >> expr_tac u
| (expr.pi _ _ t u) := trace "PI!" >> expr_tac t >> expr_tac u
| (expr.app f n) := trace "Function application!" >> expr_tac f >> expr_tac n
| (expr.const n _) := trace "const!"
| _ := trace "no one fucking knows"

#eval expr_tac `(ℕ)
#eval expr_tac `(λ (p q : Prop), @and.intro p q)
#eval expr_tac `(@and.intro)
#eval expr_tac `(F n)
#eval expr_tac `(@rfl.{1} nat (@bit1.{0} nat nat.has_one nat.has_add
                          (@has_one.one.{0} nat nat.has_one)))
#eval expr_tac `(trivial)

#eval trace_infered_type `(λ α : Type, λ p q : α → Prop, assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from (h y).left)

#check revert

def F : ℕ → ℕ :=
begin
  --   refine λ x, _,
  apply λ _, _, --both refine and apply work
  apply 3,
end

def F' : ℕ → ℕ → ℕ :=
begin
  --   refine λ x, _,
  apply λ x y, _, --both refine and apply work
  apply 3,
end

#eval expr_tac `(λ x : ℕ, x)

#check cc

set_option pp.all false

example (p : nat → Prop) (h : ∃ (x : ℕ), p x) : ∃ x, p x :=
begin
  apply exists.intro,
  apply exists.elim h,
  -- apply exists.elim h,
  -- cases h,

end

example {α : Type} (a a' b b' : α) (f : α → α → α) (ha : a = a') (hb : b = b') : f a b = f a' b':=
begin
  apply eq.subst ha,
  apply eq.subst hb,
  refl,
end

lemma iff_congr' (a a' b b' : Prop) (f : Prop → Prop → Prop) (ha : a ↔ a') (hb : b ↔ b') :
  f a b ↔ f a' b':=
begin
  have ga : a = a', from begin apply propext, exact ha, end,
  have gb : b = b', from begin apply propext, exact hb, end,
  rw ha,
  rw hb,
  -- can solve_by_elim solve this?
end

#check iff_congr
#check propext

set_option pp.all true

#print iff_congr'
