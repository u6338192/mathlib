import tactic.tidy

open tactic

meta def check : tactic unit :=
do let L := tactic.tidy.default_tactics,
   L.mmap (λ t, (do str ← t, trace str) <|> do skip),
   skip
