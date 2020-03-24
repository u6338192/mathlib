import hotkeys
import tactic.rewrite_all

open tactic

lemma test (a b c : ℕ) (h : a = b) : a = b :=
begin
  rw h,
end

#print test

#print eq

#print tactic.tidy
#print tactic.hint
#print tactic.dunfold

constants α β γ : Type
constants (a : α) (b : β)
#reduce (λ x : α, x) a

lemma testtwo (a b c : ℕ) (h : a = b) : a = b :=
begin
  induction h,
  refl,
end

lemma testthree (a b c d : ℕ) (h : a = b) (j : c = d) : a + c = b + d :=
begin
  have o : b = a, from by exact eq.symm h,
  induction o,
  induction j,
  refl,
end

lemma testfour (h : ∃ x : ℕ, x = 5) : 4 + 1 = 5 :=
begin
  induction h,
  norm_num,
end

lemma testfive : ∃ x : ℕ, x = 5 :=
begin
  have o : ¬ ¬ (∃ (x : ℕ), x = 5) → ∃ (x : ℕ), x = 5, from
  begin
    intro h,
    push_neg at h,
    exact h,
  end,
  apply o,
  intro h,
  push_neg at h,
  apply h 5,
  refl,
end

example : true := by exact trivial

lemma testhint (a b c : ℕ) (h : a = b) : a + c = b + c :=
begin
  induction h,
  refl,
end

lemma testrwall (a b c : ℕ) (h : a = b) : a + b = a + a :=
begin
  perform_nth_rewrite 2 h,
end

#print testrwall

lemma testrwall (a b c d : ℕ) (h : a = b) : a + b = c + d :=
begin
  change h,
end

open nat

example (p : ℕ) : prime p :=
begin
  change 2 ≤ p ∧ ∀ m ∣ p, m = 1 ∨ m = p,
  sorry
end

example (p : ℕ) : 2 ≤ p ∧ ∀ m ∣ p, m = 1 ∨ m = p :=
begin
  change prime p,
  dsimp,
end

meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."

meta def broken_trace_goal : tactic unit :=
tactic.trace tactic.target

meta def trace_goal : tactic unit :=
 tactic.target >>= tactic.trace

meta def let_example : tactic unit :=
do
 let message := "Hello, World.",
 tactic.trace message

meta def is_done : tactic bool :=
(tactic.target >> return ff) <|> return tt

meta def trace_is_done : tactic unit :=
is_done >>= tactic.trace

meta def trace_goal_is_eq : tactic unit :=
(do  `(%%l = %%r) ← tactic.target,
     tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r) )
   <|> tactic.trace "Goal is not an equality"

meta def trace_expr' (e : expr) : tactic unit :=
do t ← infer_type e,
   trace (to_string t)

meta def trace_type' : tactic unit :=
do (g::gs) ← get_goals,
   trace_expr g

meta def trace_list_type' : list expr → tactic unit
| [] := skip
| (e::es) := trace_expr e >> trace_list_type es

meta def trace_assumption_type' : tactic unit :=
do ctx ← local_context,
   trace_list_type ctx

example : true :=
begin
  my_first_tactic,
  trace_type,
  trace_goal_is_eq,
  trace_is_done,
  trivial,
  let_example,
  trace_is_done,

end

example : ∀ x : ℕ, 0 ≤ x :=
begin
  broken_trace_goal,
  trace_type,
  trace_goal_is_eq,
  trivial
end

open tactic.interactive («have»)
open tactic (get_local infer_type)

meta def tactic.interactive.add_eq_h₁_h₂ : tactic unit :=
do e1 ← get_local `h₁,
   e2 ← get_local `h₂,
   «have» none none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

meta def trace_local : tactic unit :=
do e1 ← get_local `h₁,
   trace `h₁,
   trace e1

example (a b j k : ℤ) (h₁ : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  trace_local,
  add_eq_h₁_h₂,
  exact this
end

open interactive (parse)
open lean.parser (ident)

meta def tactic.interactive.add_eq (h1 : parse ident) (h2 : parse ident) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» none none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (a b j k : ℤ) (u₁ : a = b) (u₂ : j = k) :
  a + j = b + k :=
begin
  add_eq u₁ u₂,
  exact this
end

open lean.parser (tk)
meta def tactic.interactive.add_eq' (h1 : parse ident) (h2 : parse ident)
  (h : parse (optional (tk "with" *> ident))) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» h none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (m a b c j k : ℤ) (Hj : a = b) (Hk : j = k) :
  a + j = b + k :=
begin
  add_eq' Hj Hk with new,
  exact new
end

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  replace hyp := congr_arg (λ x, c*x) hyp,
  exact hyp
end

open interactive (loc.ns)
open interactive.types (texpr location)
meta def tactic.interactive.mul_left (q : parse texpr) : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  mul_left c at hyp,
  exact hyp
end

#print succ_add

--Lean need to know the type...

#reduce λ (n m : ℕ),
  nat.brec_on m
    (λ (m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m) (n : ℕ),
       (λ (n m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m),
          nat.cases_on m
            (λ (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) 0),
               id_rhs (succ n + 0 = succ n + 0) rfl)
            (λ (m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) (succ m)),
               id_rhs (succ (succ n + m) = succ (succ (n + m))) (congr_arg succ (_F.fst.fst n)))
            _F) n m _F) n

#reduce nat.succ_add

-- set_option pp.implicit true
#print succ_add

#reduce λ (n m : ℕ),
  @pprod.fst (∀ (n : ℕ), nat.add (succ n) m = succ (nat.add n m))
    (@nat.rec (λ (n : ℕ), Type) punit
       (λ (n : ℕ) (ih : Type), pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
       m)
    (@nat.rec
       (λ (n : ℕ),
          pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n))
            (@nat.rec (λ (n : ℕ), Type) punit
               (λ (n : ℕ) (ih : Type),
                  pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
               n))
       (@pprod.mk (∀ (n : ℕ), succ n = succ n) punit (λ (n : ℕ), @eq.refl ℕ (succ n)) punit.star)
       (λ (n : ℕ)
        (ih :
          pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n))
            (@nat.rec (λ (n : ℕ), Type) punit
               (λ (n : ℕ) (ih : Type),
                  pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
               n)),
          @pprod.mk (∀ (n_1 : ℕ), succ (nat.add (succ n_1) n) = succ (succ (nat.add n_1 n)))
            (pprod
               (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n))
                  (@nat.rec (λ (n : ℕ), Type) punit
                     (λ (n : ℕ) (ih : Type),
                        pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
                     n))
               punit)
            (λ (n_1 : ℕ),
               @eq.rec ℕ (nat.add (succ n_1) n) (λ (_x : ℕ), succ (nat.add (succ n_1) n) = succ _x)
                 (@eq.refl ℕ (succ (nat.add (succ n_1) n)))
                 (succ (nat.add n_1 n))
                 (@pprod.fst (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n))
                    (@nat.rec (λ (n : ℕ), Type) punit
                       (λ (n : ℕ) (ih : Type),
                          pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
                       n)
                    ih
                    n_1))
            (@pprod.mk
               (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n))
                  (@nat.rec (λ (n : ℕ), Type) punit
                     (λ (n : ℕ) (ih : Type),
                        pprod (pprod (∀ (n_1 : ℕ), nat.add (succ n_1) n = succ (nat.add n_1 n)) ih) punit)
                     n))
               punit
               ih
               punit.star))
       m)
    n
#check succ_add
#reduce λ (n m : ℕ),
  @nat.brec_on (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m
    (λ (m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m) (n : ℕ),
       (λ (n m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m),
          @nat.cases_on
            (λ (m : ℕ),
               nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) m → succ n + m = succ (n + m))
            m
            (λ (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) 0),
               id_rhs (succ n + 0 = succ n + 0) (@rfl ℕ (succ n + 0)))
            (λ (m : ℕ) (_F : nat.below (λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) (succ m)),
               id_rhs (succ (succ n + m) = succ (succ (n + m)))
                 (@congr_arg ℕ ℕ (succ n + m) (succ (n + m)) succ
                    (@pprod.fst ((λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) (nat.add m 0))
                       (@nat.rec (λ (n : ℕ), Type) punit
                          (λ (n : ℕ) (ih : Type),
                             pprod (pprod ((λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) n) ih) punit)
                          (nat.add m 0))
                       (@pprod.fst
                          (pprod ((λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) (nat.add m 0))
                             (@nat.rec (λ (n : ℕ), Type) punit
                                (λ (n : ℕ) (ih : Type),
                                   pprod (pprod ((λ (m : ℕ), ∀ (n : ℕ), succ n + m = succ (n + m)) n) ih) punit)
                                (nat.add m 0)))
                          punit _F) n))) _F) n m _F) n

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

def t (x : ℕ) : ℕ :=
let y := x + x in y * y

#check t
#print t
#reduce t 2   -- 16


#check id
#check @id

#check or


constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
#reduce λ hp : p, λ hq : q, hp

#print t1
#check t1
#reduce t1

#reduce succ_add

theorem t1' : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp

#print t1
#check t1
#reduce t1

-- set_option pp.implicit true
-- #reduce succ_add

#eval trace_infered_type `(λ hp : p, λ hq : q, hp)

variables r s : Prop

#eval trace_infered_type `(λ hp : p, λ hq : q, hp)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  λ p, h₁ (h₂ p)

#check assume (hp : p) (hq : q), and.intro hp hq

--For some reason it wants p and q to be constants not variables
#eval trace_infered_type `(λ (hp : p) (hq : q), and.intro hp hq)
#eval trace_infered_type `(λ hp : p, λ hq : q, and.intro hp hq)

--It wants to know that p q are props
#eval trace_infered_type `(λ p q : Prop, λ hp : p, λ hq : q, and.intro hp hq)

#eval trace_infered_type `(λ p q : Prop, λ h : p ∧ q, and.intro (and.right h) (and.left h))

#eval trace_infered_type `(λ p q : Prop, λ hp : p, or.intro_left q hp)

example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

#eval trace_infered_type `(λ p q : Prop, λ h : p ∨ q, or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq))

#eval trace_infered_type `(λ p q : Prop, λ  hpq : p → q, λ hnq : q → false, assume hp : p,
show false, from hnq (hpq hp))

#eval trace_infered_type `(λ p q : Prop, λ  hp : p, λ hnp : p → false, show q, from absurd hp hnp)

example (h : p ∧ q) : q ∧ p :=
begin
  have hp : p, from h.left,
  suffices hq : q, from begin exact and.intro hq hp, end,
  show q, from begin exact h.right, end,
end

open classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, show p, from absurd hnp h)

theorem emtodne {p : Prop} (h : p ∨ ¬p) : ¬¬p → p :=
begin
  intro j,
  cases h,
  {
    exact h,
  },
  {
    exfalso,
    exact j h,
  },
end

#eval trace_infered_type `(λ p : Prop, λ  h : ¬¬p, by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)
)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
begin
  apply or.elim (em p),
  intro hp,
  right,
  intro hq,
  apply h,
  split,
  exact hp,
  exact hq,
  intro hnp,
  left,
  exact hnp,
end

#eval trace_infered_type `(λ α : Type, λ p q : α → Prop, assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from (h y).left)

lemma testiffrw {p q r : Prop} (h : p ↔ q) (j : q ↔ r) : p ↔ r :=
begin
  rw h,
  rw j
end

#print testiffrw

universe u

lemma ex1 (α : Type u) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
eq.subst h1 h2

lemma ex1' (α : Type u) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
begin
  rw ←h1,
  exact h2,
end

lemma ex2 (α : Type u) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
h1 ▸ h2

#print ex1
#print ex1'

variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

include h1 h2 h3 h4
theorem T : a = e :=
calc
  a     = b      : by rw h1
    ... = c + 1  : by rw h2
    ... = d + 1  : by rw h3
    ... = 1 + d  : by rw add_comm
    ... =  e     : by rw h4

#eval trace_infered_type `(
λ a b c d e : ℕ,
λ h1 : a = b,
λ h2 : b = c + 1,
λ h3 : c = d,
λ h4 : e = 1 + d,

calc
  a     = b      : by rw h1
    ... = c + 1  : by rw h2
    ... = d + 1  : by rw h3
    ... = 1 + d  : by rw add_comm
    ... =  e     : by rw h4)

variable g : ℕ → ℕ → ℕ
variable hg : g 0 0 = 0

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.implicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

def is_even (a' : ℕ) := ∃ b', a' = 2 * b'

theorem even_plus_even {a' b' : ℕ}
  (h1 : is_even a') (h2 : is_even b') : is_even (a' + b') :=
begin

end
