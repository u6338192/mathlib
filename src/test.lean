def divisors_aux (n : ℕ) : ℕ → list ℕ
| 0     := []
| (h+1) := if n % h = 0
           then [h] ++ divisors_aux h
           else divisors_aux h

example (n : ℕ) : divisors_aux n 0 = [] := rfl
example (m n : ℕ) : divisors_aux m (n+1) = if m % n = 0 then [n] ++ divisors_aux m n else divisors_aux m n := rfl
