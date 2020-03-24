import tactic.hint
import tactic.suggest
import tactic hotkeys

example {p : Prop} : ¬(p ↔ ¬p) :=
begin
  intro,
  cases a with h j,
  have t : p → false, from begin intro hp, apply h hp, exact hp, end,
  apply h,
  all_goals {apply j},
  all_goals {apply t},
  -- exact h (j t) (j t),
end

--Perhaps add these to solve_by_elim
#check congr_arg
#check eq.rec_on
#check iff.rec_on

/- Three things for solve by elim
1) add eq/iff/nat.rec_on to assumptions list
2) get it to give a 'try this' statement if it succeeds
3) give shorter names 'sbe' and 'lib' for library_search

!) test these before asking to PR
-/

#eval trace_infered_type `(λ α : Type, λ p q : α → Prop, assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from (h y).left)

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end

#print test
#check test
#reduce test
#eval trace_infered_type `(λ (p q : Prop) (hp : p) (hq : q), (⟨hp, ⟨hq, hp⟩⟩ : p ∧ q ∧ p))

lemma AX1 {p q : Prop} : (((p → q) → p) → p) :=
begin
  classical,

  intro j,
  by_cases p,
  { exact h, },
  { apply j,
    intro p,
    exfalso,
    exact h p,
  },
end

#print AX1
#eval trace_infered_type `(λ {p q : Prop} (d : decidable p) (j : (p → q) → p),
  dite p (λ (h : p), h) (λ (h : ¬p), j (λ (p : p), false.rec q (h p))))

#print notation
#print notation + * -
#print axioms
#print options
#print prefix nat
#print prefix nat.le
#print classes
#print instances ring
#print fields ring

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

def number_of_day (d : weekday) : ℕ :=
begin
  induction d,
  exact 1,
  exact 2,
  exact 3,
  exact 4,
  exact 5,
  exact 6,
  exact 7,
end
--weekday.rec_on d 1 2 3 4 5 6 7

#reduce number_of_day weekday.sunday
#reduce number_of_day weekday.monday
#reduce number_of_day weekday.tuesday

def band' (b1 b2 : bool) : bool :=
begin
  cases b1,
  exact ff,
  exact b2,
end
--bool.cases_on b1 ff b2

universes u v

def fst {α : Type u} {β : Type v} (p : α × β) : α :=
prod.rec_on p (λ a b, a)

def prod_example (p : bool × ℕ) : ℕ :=
-- begin
--   induction p,
--   exact (λ b n, cond b (2 * n) (2 * n + 1)) p_fst p_snd,
-- end
prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

#print prod_example

-- #eval trace_infered_type `(λ (p : bool × ℕ), prod.rec_on p
--   (λ (b : bool) (n : ℕ), cond b (2 * n) (2 * n + 1)))

#reduce prod_example (tt, 3)
#reduce prod_example (ff, 3)

lemma inhabnat : inhabited ℕ :=
begin
  use 0,
end

set_option pp.all true
#print inhabnat

#eval trace_infered_type `(@inhabited.mk.{1} nat (@has_zero.zero.{0} nat nat.has_zero))
set_option pp.all false

example {α β : Type} (h₁ : inhabited α) (h₂ : inhabited β) : inhabited (α × β) :=
begin
  tactic.unfreeze_local_instances,
  induction h₁,
  induction h₂,
  have h : (α × β), from prod.mk h₁ h₂,
  use h,
end

example {α β : Type} (h₁ : inhabited β) : inhabited (α → β) :=
begin
  tactic.unfreeze_local_instances,
  induction h₁,
  use (λ a, h₁),
end

namespace nat

inductive nat' : Type
| zero : nat'
| succ : nat' → nat'

def add' (m n : nat) : nat :=
begin
  induction n,
  exact m,
  exact (succ n_ih),
end
-- nat.rec_on n m (λ n add_m_n, succ add_m_n)

-- try it out
#reduce add' (succ zero) (succ (succ zero))
#reduce add' 4 99

theorem zero_add' (n : ℕ) : 0 + n = n :=
nat.rec_on n
  (show 0 + 0 = 0, from rfl)
  (assume n,
    assume ih : 0 + n = n,
    show 0 + succ n = succ n, from
      calc
        0 + succ n = succ (0 + n) : rfl
          ... = succ n : by rw ih)

set_option pp.all true
#print zero_add'
set_option pp.all false

#eval trace_infered_type `(
λ (n : nat),
  @nat.rec_on.{0}
    (λ (_x : nat), @eq.{1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) _x) _x)
    n
    (show @eq.{1} nat
            (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero)
               (@has_zero.zero.{0} nat nat.has_zero))
            (@has_zero.zero.{0} nat nat.has_zero), from
       @rfl.{1} nat
         (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) (@has_zero.zero.{0} nat nat.has_zero)))
    (λ (n : nat) (ih : @eq.{1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n) n),
       show @eq.{1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) (nat.succ n))
              (nat.succ n), from
         @eq.trans.{1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) (nat.succ n))
           (nat.succ (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n))
           (nat.succ n)
           (@rfl.{1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) (nat.succ n)))
           (@eq.mpr.{0}
              (@eq.{1} nat (nat.succ (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n))
                 (nat.succ n))
              (@eq.{1} nat (nat.succ n) (nat.succ n))
              (@id.{0}
                 (@eq.{1} Prop
                    (@eq.{1} nat (nat.succ (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n))
                       (nat.succ n))
                    (@eq.{1} nat (nat.succ n) (nat.succ n)))
                 (@eq.rec.{0 1} nat (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n)
                    (λ (_a : nat),
                       @eq.{1} Prop
                         (@eq.{1} nat
                            (nat.succ (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n))
                            (nat.succ n))
                         (@eq.{1} nat (nat.succ _a) (nat.succ n)))
                    (@eq.refl.{1} Prop
                       (@eq.{1} nat
                          (nat.succ (@has_add.add.{0} nat nat.has_add (@has_zero.zero.{0} nat nat.has_zero) n))
                          (nat.succ n)))
                    n
                    ih))
              (@eq.refl.{1} nat (nat.succ n))))
)

--nat.rec_on needs to know what's being proved.
#check @nat.rec_on

end nat

--ask about this on zulip?
def append' {α : Type} (s t : list α) : list α :=
begin
  -- induction t,
  -- exact s,
  -- exact ((λ x u, list.cons x u) t_hd s),
  apply @list.rec.{1 0} α (λ (_x : list.{0} α), list.{0} α),
  exact t,
  exact (λ x l u, x::u),
  exact s,
end
-- list.rec t (λ x l u, x::u) s

#reduce append' [1,2,3] [4, 5, 6]

set_option pp.all true
#print append'
set_option pp.all false

#eval trace_infered_type `(λ {α : Type} (s t : list.{0} α),
  @list.rec.{1 0} α (λ (_x : list.{0} α), list.{0} α) t
  (λ (x : α) (l u : list.{0} α), @list.cons.{0} α x u) s)

variable α : Type

theorem cons_append (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

theorem append_nil (t : list α) : t ++ [] = t :=
begin
  induction t,
  refl,
  conv
  {
    to_rhs,
    rw ←t_ih,
  },
  refl,
end

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) :=
begin
  induction r,
  refl,

  repeat {rw cons_append},
  rw r_ih,
end

def list_length {α : Type} (t : list α) : ℕ :=
-- begin
  -- -- induction t,
  -- -- exact 0,
  -- -- exact 1 + t_ih,
  -- apply @list.rec.{1 0} α (λ (_x : list.{0} α), ℕ),
  -- exact 0,
  -- -- intros,
  -- -- exact 1 + ih,
  -- exact (λ a b n, 1 + n),
  -- exact t,
-- end
list.rec 0 (λ a b n, n + 1) t

#print list_length

#eval list_length [1,3,4,6,7,8,9]

theorem append_length {α : Type} (t s : list α) :
  list_length (s ++ t) = list_length s + list_length t :=
begin
  induction s,
  have h : list.nil ++ t = t := rfl,
  have j : list_length list.nil = 0 :=
  begin
    refl,
    recover,
    exact α,
  end,
  rw [h, j],
  rw zero_add,

  have k : list_length (s_hd :: s_tl) = list_length (s_tl) + 1 := rfl,
  rw [k, cons_append],
  have e : list_length (s_hd :: (s_tl ++ t)) = list_length(s_tl ++ t) + 1 := rfl,
  rw [e, s_ih],
  simp,
end

open nat
variable p : ℕ → Prop

example (hz : p 0) (hs : ∀ n, p (succ n)) (m k : ℕ) :
  p (m + 3 * k) :=
begin
  cases (m + 3 * k),
  { exact hz },  -- goal is p 0
  apply hs       -- goal is a : ℕ ⊢ p (succ a)
end

open nat

example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
  n + k = m + k :=
begin
  injection h with h',
  injection h' with h'',
  rw h''
end

#check (@eq.rec_on :
  Π {α : Sort u} {a : α} {C : α → Sort v} {b : α},
    a = b → C a → C b)

theorem symm' {α : Type u} {a b : α} (h : eq a b) : eq b a :=
begin
  apply eq.subst h,
  refl,
end
-- eq.subst h (eq.refl a)

theorem trans' {α : Type u} {a b c : α}
  (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
begin
  exact eq.subst h₂ h₁,
end

theorem congr' {α β : Type u} {a b : α} (f : α → β)
  (h : eq a b) : eq (f a) (f b) :=
begin
  apply eq.subst h,
  refl,
end

def len {α : Type} : list α → ℕ
| []     := 0
| (h::t) := 1 + len t

def rev {α : Type} : list α → list α
| []     := []
| (h::t) := rev t ++ [h]

#reduce len [2,3,4,5,6]
#reduce rev [5,6,7,8,1]

lemma len_add {α : Type} (s t : list α) : len (s ++ t) = len s + len t :=
begin
  have o₁ : ∀ t : list α, [] ++ t = t, from λ t, rfl,
  have o₂ : @len α [] = 0, from rfl,
  have o₃ : ∀ (h : α) (t : list α), (len (h::t)) = 1 + len t, from λ h t, rfl,
  induction s,

  rw [o₁, o₂],
  apply eq.symm,
  apply zero_add,

  rw cons_append,
  rw [o₃, s_ih, o₃ s_hd s_tl, add_assoc],
end

example {α : Type} (t : list α) : len (rev t) = len t :=
begin
  induction t,
  refl,

  have o₃ : ∀ (h : α) (t : list α), (len (h::t)) = 1 + len t, from λ h t, rfl,
  unfold rev,
  rw len_add,
  rw t_ih,
  rw o₃ t_hd t_tl,
  rw add_comm,
  refl,
end

example {α : Type} (t : list α) : rev (rev t) = t :=
begin
  induction t,
  refl,

  have o₂ : ∀ (h : α) (t : list α), [h] ++ rev t = rev (t ++ [h]), from
  begin
    intros h t,
    induction t with m n ih,
    refl,

    conv {
      to_rhs,
      rw cons_append,
    },
    unfold rev,
    rw ←ih,
    rw append_assoc,
  end,

  unfold rev,
  rw ←o₂,
  rw t_ih,
  refl,
end

inductive nat_expr : Type
| const : ℕ → nat_expr
| var   : char → nat_expr
| plus  : nat_expr → nat_expr → nat_expr
| times : nat_expr → nat_expr → nat_expr

set_option trace.eqn_compiler.elim_match true

open nat_expr

def nat_expr_eval' (f : char → ℕ) : nat_expr → ℕ
| (const n)   := n
| (var c)     := f c
| (plus s t)  := nat_expr_eval' s + nat_expr_eval' t
| (times s t) := nat_expr_eval' s * nat_expr_eval' t

def nat_expr_eval (f : char → ℕ) : nat_expr → ℕ :=
begin
  intro e,
  induction e,

  exact e,

  exact f e,

  exact e_ih_a + e_ih_a_1,

  exact e_ih_a * e_ih_a_1,
end

def ft (c : char) : ℕ := c.val

#eval nat_expr_eval ft (nat_expr.plus (nat_expr.const 3) (nat_expr.const 4))

#eval nat_expr_eval ft (plus (times (var 'v') (var 't')) (const 67))

def f1 : ℕ → ℕ → ℕ
| 0  _  := 1
| _  0  := 2
| _  _  := arbitrary ℕ   -- the "incomplete" case

variables (a b : ℕ)

example : f1 0     0     = 1 := rfl
example : f1 0     (a+1) = 1 := rfl
example : f1 (a+1) 0     = 2 := rfl
example : f1 (a+1) (b+1) = arbitrary nat := rfl

def f2 : ℕ → ℕ → option ℕ
| 0  _  := some 1
| _  0  := some 2
| _  _  := none          -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl

def bar : ℕ → list ℕ → bool → ℕ
| 0     _        ff := 0
| 0     (b :: _) _  := b
| 0     []       tt := 7
| (a+1) []       ff := a
| (a+1) []       tt := a + 1
| (a+1) (b :: _) _  := a + b

def foo : char → ℕ
| 'A' := 1
| 'B' := 2
| _   := 3

#print foo._main

variable (C : ℕ → Type)

#check (@nat.below C : ℕ → Type)

#reduce @nat.below C (3 : nat)

#check (@nat.brec_on C :
  Π (n : ℕ), (Π (n : ℕ), nat.below C n → C n) → C n)

variable σ : Sort u
variable r : α → α → Prop

#check (acc r : α → Prop)

#check (well_founded r : Prop)

def nat_to_bin : ℕ → list ℕ
| 0       := [0]
| 1       := [1]
| (n + 2) :=
  have (n + 2) / 2 < n + 2, from sorry,
  nat_to_bin ((n + 2) / 2) ++ [n % 2]

#eval nat_to_bin 1234567

def ack : nat → nat → nat
| 0     y     := y+1
| (x+1) 0     := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)

#eval ack 3 5

#print lean.version
