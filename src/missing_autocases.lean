import hotkeys

inductive mynat
| zero : mynat
| succ : mynat → mynat

lemma test_one (n a : ℕ) (h : 1 ≤ n) : n * a = a * n :=
begin
  auto_cases,
  induction h,
  sorry,
  sorry,
end

lemma test_two (n : mynat) : n = n :=
begin
  --auto_cases,
  induction n,
  sorry,
  sorry,
end

lemma test_three (n : ℕ) : n = n :=
begin
  auto_cases,
  -- induction n,
  -- sorry,
  -- sorry,
end
