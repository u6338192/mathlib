import tactic
import hotkeys

open tactic
open nat

--This could be replaced by foldl in mathlib
def fold (f : ℕ → ℕ) : ℕ → ℕ → ℕ
| 0     n := n
| (m+1) n := fold m (f n)

def fold_list (f : ℕ → ℕ) : ℕ → ℕ → list ℕ
| 0     n := [n]
| (m+1) n := [n] ++ fold_list m (f n)

def Binfun (n : ℕ) (g₀ g₁ : ℕ → ℕ) : ℕ :=
if n % 2 = 0
  then g₀ n
  else g₁ n

def collatz (n : ℕ) : ℕ := Binfun n (λ n, n / 2) (λ n, 3*n + 1)

#eval fold_list collatz 107 63

def colfiv (n : ℕ) : ℕ := Binfun n (λ n, n / 2) (λ n, 5*n + 1)

def colsev (n : ℕ) : ℕ := Binfun n (λ n, n / 2) (λ n, 7*n + 1)

#eval fold_list colfiv 100 13

#eval fold_list colsev 100 21

def colnum (m : ℕ) : ℕ → ℕ := λ n, Binfun n (λ n, n / 2) (λ n, m*n + 1)

#eval fold_list (colnum 61) 1000 1

--want to get the sequence
def bin_list (f : ℕ → ℕ) : ℕ → ℕ → list ℕ
| 0     n := if n % 2 = 0 then [0] else [1]
| (m+1) n := if n % 2 = 0 then [0] ++ bin_list m (f n) else [1] ++ bin_list m (f n)

#eval bin_list collatz 100 7
#eval fold_list collatz 100 7

#eval bin_list (colnum 5) 1000 13
#eval fold_list (colnum 5) 1000 13

--TO DO
--*function which takes a binary sequence as input and returns an arithmetic
-- sequence as output. The arithmetic sequence is the set of input which
-- produce the input sequence under bin_list
--*function which takes a binary sequence as input and returns an arithmetic
-- sequence as output. The arithmetic sequence is the set of outputs which is
-- produced sequence under bin_list
--*Determine a lower bound for the inputs which generate sequences

#eval fold_list (colnum 5) 100 33
#eval bin_list (colnum 5) 100 33

#eval fold_list (colnum 3) 100 33
#eval bin_list (colnum 3) 100 33

#eval fold_list (colnum 3) 100 7
#eval bin_list (colnum 3) 100 7

#eval fold_list (colnum 3) 100 19
#eval bin_list (colnum 3) 100 19

#eval fold_list (colnum 3) 100 135
#eval bin_list (colnum 3) 100 135

def arithmetic_sequence (a b : ℕ) : ℕ → ℕ := λ m, a * m + b

#eval arithmetic_sequence 5 3 1

def scalar_mul {a b : ℕ} (z : ℕ) (s : ℕ → ℕ) (h : s = arithmetic_sequence a b) : ℕ → ℕ :=
arithmetic_sequence (z*a) (z*b)

def scalar_add {a b : ℕ} (z : ℕ) (s : ℕ → ℕ) (h : s = arithmetic_sequence a b) : ℕ → ℕ :=
arithmetic_sequence (a) (b + z)

notation `*` := scalar_mul
notation `+` := scalar_add
notation `as` := arithmetic_sequence

#eval (scalar_mul 4 (arithmetic_sequence 5 3) rfl) 1
#eval (* 4 (arithmetic_sequence 5 3) rfl) 1

lemma arith_sub {a b c d m : ℕ} : as a b (as c d m) = as (a*c) (a*d + b) m :=
begin
  dsimp [arithmetic_sequence] at *,
  ring,
end

lemma arith_sub_fun {a b c d : ℕ} : (λ m : ℕ, as a b (as c d m))
  = (λ m : ℕ, as (a*c) (a*d + b) m) :=
begin
  dsimp [arithmetic_sequence] at *,
  ring,
end

lemma test : (λ m : ℕ, as 2 1 (as 2 1 m)) = (λ m : ℕ, as 4 3 m) :=
begin
  apply arith_sub_fun,
end

-- Perhaps arithmetic_sequence should be a type
def input_as : list bool → (ℕ → ℕ) → (ℕ → ℕ)
| []     g := as 2 1
| (h::t) g := if h = ff
                       then as 2 1
                       else as 2 1

-- I don't like this
inductive arith_seq (a b : ℕ)
| expression : arith_seq
