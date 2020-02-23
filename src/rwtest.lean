import init.meta.interactive
import hotkeys

import init.meta.tactic init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.smt.congruence_closure init.category.combinators
import init.meta.interactive_base init.meta.derive init.meta.match_tactic
import init.meta.congr_tactic

open tactic

lemma test (a b c : ℕ) (h : a = b) : a = b :=
begin
  rw h,
end

#print test

#print eq

lemma testtwo (a b c : ℕ) (h : a = b) : a = b :=
begin
  induction h,
  refl,
end

variables a b : ℕ
constant h : a = b
#check eq.symm (h a b)




namespace tactic

namespace interactive

open interactive
open lean
open lean.parser
open interactive_base

meta def rw_hint (l : parse location) : tactic unit :=
do hs ← local_context,
   hs.mmap (λ h, rw h  )

end interactive

end tactic

lemma testthree (a b c d : ℕ) (h : a = b) (j : c = d) : a + c = b + d :=
begin
  have o : b = a, from by exact eq.symm h,
  induction o,
  rw o,
end
