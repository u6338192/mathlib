/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
@[user_attribute]
meta def crash_attribute : user_attribute unit unit := {
  name := `sigbus,
  descr := "An attribute to help generate server crashes, for debugging IDE interactions.",
  cache_cfg :=
   { mk_cache := λ ls, crash_attribute.get_cache,
     dependencies := [] }
}

/-- This tactic crashes the server, exploiting a stack overflow in
    attribute caching. -/
meta def induce_crash : tactic unit := crash_attribute.get_cache

-- run_cmd induce_crash
