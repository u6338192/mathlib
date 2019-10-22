--Assignment 2 Question 1, Lucas Allen u6338192

--Importing required mathlib files.
--Scott said I could use finsets for defining primes.
import algebra.big_operators
import data.nat.prime

--Opening required inductive types.
open finset
open set

--Function that returns a list of all numbers less than n, not including 0.
--This is from assignment 1 question 2.
def le_num_list : ℕ → list ℕ
| 0 := []
| (n+1) := [n+1] ++ le_num_list (n)

--Function that return a finset of all divisors of a natural number.
--This is from assignment 1 question 2.
def divisors_aux (n : ℕ) : list ℕ → finset ℕ
| [] := {1}
| (h::t) := if n % h = 0 then {h} ∪ divisors_aux (t) else divisors_aux (t)

--Function that returns diviors but only takes one argument.
--This is from assignment 1 question 2.
def divisors (n : ℕ) : finset ℕ := divisors_aux n (le_num_list n)

--Function that returns true if n is prime, and false otherwise.
--This works by finding the set of divisors and checking if it's {1,n}.
--Note that this is not a prop.
def isprime (n : ℕ) : bool := (n ≥ 2) ∧ (divisors n = {1,n})

--Testing isprime function.
#eval isprime 4
#eval isprime 5

--First definition of prime.
def myprime (n : ℕ) : Prop := (n ≥ 2) ∧ (divisors n = {1,n})

#eval (divisors 4).1

--Keeley's example from Zulip, in the 'sets not equal' topic.
example : ({1, 2, 3} : finset ℕ) ≠ {1, 2} := dec_trivial

--Proof that 4 is not prime.
theorem four_not_prime : ¬ myprime 4 :=
have h : divisors 4 = {1,2,4}, from rfl,
have g : ({1, 2, 4} : finset ℕ) ≠ {1,4}, from dec_trivial,
begin
  unfold myprime,
  rw [h],
  cases h,
  intro h,
  cases h with a b,
  contradiction,
end

--Proof that 5 is prime.
theorem five_is_prime : myprime 5 :=
have h : divisors 5 = {1,5}, from rfl,
begin
unfold myprime,
rw [h],
split,
exact dec_trivial,
assumption,
end

--A better Prop definition for primes maybe:
def my_second_prime (n : ℕ) : Prop := isprime n = tt

--Lemma showing that the first definition of prime implies the second
lemma first_prime_implies_second (p : ℕ) : myprime p → my_second_prime p :=
begin
  dsimp [myprime, my_second_prime, isprime],
  intro h,
  exact dif_pos h, --knew to use this from library search
end

--Lemma showing that the second definition of prime implies the first
lemma second_prime_implies_first (p : ℕ) : my_second_prime p → myprime p :=
begin
  dsimp [myprime, my_second_prime, isprime],
  intro h,
  simp at h,
  assumption,
end

open nat

lemma my_prime_good (p n : ℕ) : prime p → myprime p :=
have s₁ : prime p → (p ≥ 2), from prime.two_le,
have s₄ : prime p → (n ∣ p → n = 1 ∨ n = p), from λ (pp : prime p), (dvd_prime pp).mp
have s₂ : (n ∣ p → n = 1 ∨ n = p) → divisors p = {1,p}, from
begin
  intro,
  unfold divisors,
  sorry --this is too hard for me at the moment.
end,
have s₃ : (p ≥ 2) ∧ (divisors p = {1,p}) → myprime p, from
  begin intros, unfold myprime, assumption, end,
show prime p → myprime p, from
begin intro, apply s₃, split,
  exact s₁ a,
  exact s₂ (s₄ a)
end

--Lemma showing that the definition of primes are equivalent.
lemma equiv_defs (p : ℕ) : myprime p ↔ my_second_prime p :=
iff.intro
(first_prime_implies_second p)
(second_prime_implies_first p)

--Setting trace.class_instances to true to see how Lean constructs
--the decidability instances.
set_option trace.class_instances true

--Instance for decidable (myprime n).
--Lean first searches a whole bunch of instances and then gives the message:
--"(message too long, truncated at 262144 characters)" before even getting
--past the (0) node.
--However, if we replace the {1,n} with [1,n].to_finset in the definition of
--myprime, then we can answer the question (the reason I didn't make the change
--was because it broke some of my proofs.)
--Lean first finds an instance of and.decidable, and moves to the (1) node.
--It then finds an instance of finset.has_decidable_eq and moves to the (2) node
--Next it finds an instance of nat.decidable_eq and completes.
instance my_prime_decidable (n : ℕ) : decidable (myprime n) :=
begin
  dsimp [myprime],
  apply_instance,
end

--Instance for decidable (my_second_prime n).
--Lean checks a whole bunch of instances until it finally finds an
--instance of bool.decidable_eq, then it finishes. It never goes past
--the (0) node in the class instance trace.
--This shows that my_second_prime_decidable is the strictly (in the
--mathematical sense) better instance of decidability. This is because:
--1) It actually prints out the entire class trace.
--2) I don't need to change the definition of my_second_prime to answer
--the question.
instance my_second_prime_decidable (n : ℕ) : decidable (my_second_prime n) :=
begin
  dsimp [my_second_prime],
  apply_instance,
end

--Instance of decidable_pred myprime.
--Lean first checks my_second_prime_decidable, but it's not right.
--It then checks my_prime_decidable and it works.
instance my_prime_decidable_insatance : decidable_pred myprime :=
begin
  apply_instance,
end

--Instance of decidable_pred my_second_prime.
--Lean first checks my_prime_decidable, but it's not right.
--It then checks my_second_prime_decidable and it works.
instance my_second_prime_decidable_insatance : decidable_pred my_second_prime :=
begin
  apply_instance,
end

--Setting trace.class_instances to false because leaving it on is too scary.
set_option trace.class_instances true

--Tried to show that 65537, 7919, and 541 were prime, but got "deep
--recursion was detected" errors for 65537 and 7919, and a "deterministic
--timeout" error for 541.
--proof that 71 is prime, Compiled
-- theorem twentieth_prime : myprime 71 :=
-- have h : divisors 71 = {1,71}, from rfl,
-- begin
-- unfold myprime,
-- rw [h],
-- split,
-- exact dec_trivial,
-- assumption,
-- end

--Testing isprime function with larger numbers, they all work.
#eval isprime 71
#eval isprime 541
#eval isprime 7919
#eval isprime 65537
#eval isprime 600011

--More random testing.
#eval timeit "myprime" to_bool (myprime 600011)
#eval timeit "my_second_prime" to_bool (my_second_prime 600011)
#eval isprime 1
