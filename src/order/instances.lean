def bool_preorder : preorder bool :=
{ le := λ a b, bor a (bnot b) = tt,
  le_refl := λ a, begin cases a; simp end,
  le_trans := λ a b c h₁ h₂, begin cases a; cases b; cases c; simp at *; assumption end }

local attribute [instance] bool_preorder
@[simp] lemma tt_le_tt     : tt ≤ tt = true  := begin dsimp [(≤), preorder.le], simp end
@[simp] lemma not_tt_lt_tt : tt < tt = false := begin dsimp [(<), preorder.lt], simp end
@[simp] lemma tt_le_ff     : tt ≤ ff = true  := begin dsimp [(≤), preorder.le], simp end
@[simp] lemma tt_lt_ff     : tt < ff = true  := begin dsimp [(<), preorder.lt], simp end
@[simp] lemma not_ff_le_tt : ff ≤ tt = false := begin dsimp [(≤), preorder.le], simp end
@[simp] lemma not_ff_lt_tt : ff < tt = false := begin dsimp [(<), preorder.lt], simp end
@[simp] lemma ff_le_ff     : ff ≤ ff = true  := begin dsimp [(≤), preorder.le], simp end
@[simp] lemma not_ff_lt_ff : ff < ff = false := begin dsimp [(<), preorder.lt], simp end

def bool_partial_order : partial_order bool :=
{ le_antisymm := λ a b, begin cases a; cases b; intros; simp at *; assumption end
  .. bool_preorder }

def bool_linear_order : linear_order bool :=
{ le_total := λ a b, begin cases a; cases b; intros; simp at *; assumption end
  .. bool_partial_order }

def bool_decidable_linear_order : decidable_linear_order bool :=
{ decidable_le := λ a b, begin cases a; cases b; simp; apply_instance end,
  .. bool_linear_order }
local attribute [instance] bool_decidable_linear_order

example : tt ≤ ff := by exact dec_trivial

def empty_preorder : preorder empty :=
{ le := λ _ _, true,
  le_refl := empty.rec _,
  le_trans := empty.rec _ }

def empty_partial_order : partial_order empty :=
{ le_antisymm := empty.rec _,
  .. empty_preorder }

def empty_linear_order : linear_order empty :=
{ le_total := empty.rec _,
  .. empty_partial_order }

def empty_decidable_linear_order : decidable_linear_order empty :=
{ decidable_le := empty.rec _,
  .. empty_linear_order }

attribute [instance] empty_preorder empty_partial_order empty_linear_order
                     empty_decidable_linear_order
