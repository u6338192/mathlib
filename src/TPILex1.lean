
def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
begin
  cases h1 with a' h1,
  cases h2 with b' h2,
  unfold is_even,
  sorry,
end

variables (α : Type) (p q : α → Prop)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
  split,
  {
    intro h,
    intro j,
    cases j with o j,
    apply j,
    exact h o,
  },
  {
    intro h,
    intro x,
    sorry, --needs classical I think
  },
end

variable r : Prop

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
  split,
  {
    intros a b x,
    apply a x b,
  },
  {
    intros h x r,
    apply h r x,
  }
end

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
begin
  have j : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  cases j with a b,
  have k : shaves barber barber → false, from
  begin
    intro s,
    apply a s s,
  end,
  have l : shaves barber barber, from b k,
  exact k l,
end

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
begin
  conv {
    to_lhs,
    rw ←sub_self x,
  },
  rw mul_sub,
  rw sub_self,
end

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
begin
  have k : exp (log x + log y) = x * y, from
  begin
    rw exp_add,
    rw exp_log_eq hx,
    rw exp_log_eq hy,
  end,
  rw ←k,
  rw log_exp_eq,
end

#print log_mul
