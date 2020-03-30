-- import tactic.hint
-- import tactic.suggest
import tactic

def ack : ℕ → ℕ → ℕ
| 0     y     := y+1
| (x+1) 0     := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)

#eval ack 3 5

mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

open even odd

theorem not_odd_zero : ¬ odd 0.

mutual theorem even_of_odd_succ, odd_of_even_succ
with even_of_odd_succ : ∀ n, odd (n + 1) → even n
| _ (odd_succ n h) := begin exact h end
with odd_of_even_succ : ∀ n, even (n + 1) → odd n
| _ (even_succ n h) := h

open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open function

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) :=
begin
  unfold surjective at *,
  intro b,
  cases (hg b),
  cases (hf w) with j k,
  use j,
  rw ←h,
  rw ←k,
end

inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0) (const 7)) (times (const 2) (var 1))

def aeval (v : ℕ → ℕ) : aexpr → ℕ
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := aeval e₁ + aeval e₂
| (times e₁ e₂) := aeval e₁ * aeval e₂

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

-- Try it out. You should get 47 here.
-- #eval aeval sample_val sample_aexpr

#eval aeval sample_val sample_aexpr

def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def fuse : aexpr → aexpr
| (plus e₁ e₂)  := simp_const (plus (fuse e₁) (fuse e₂))
| (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))
| e := e

#eval aeval sample_val (fuse sample_aexpr)
#eval fuse sample_aexpr

theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
begin
  intro e,
  induction e with a b c d j k c d n o,
  refl,
  refl,

  repeat {
    cases c,
    cases d,
    repeat {
      dsimp [simp_const, aeval],
    refl, },
  },
end

#print simp_const_eq

theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
begin
  intro e,
  induction e with a b c d l m n o l m,

  repeat {
    dsimp [fuse, aeval],
    refl,
  },

  repeat {
    dsimp [fuse],
    rw simp_const_eq,
    dsimp [aeval],
    rw [l, m],
  },
end

instance inhabited_list {α : Type _} : inhabited (list α) := ⟨[]⟩

#check default (list ℕ)
#reduce default (list ℕ)

-- #check default empty
#check default (list empty)
#reduce default (list empty)

def list_add {α : Type} [has_add α] : list α → list α → list α
| [] L := []
| L [] := []
| (h₁::t₁) (h₂::t₂) := (h₁ + h₂)::(list_add t₁ t₂)

#reduce list_add [1,2,3] [6,7]

instance list_has_add {α : Type} [has_add α] : has_add (list α) :=
  -- ⟨λ L₁ L₂ : list α, list_add L₁ L₂⟩
  ⟨list_add⟩

def ite' (c : Prop) [d : decidable c] {α : Type}
  (t e : α) : α :=
begin
  apply decidable.rec_on d,
  exact λ hnc, e,
  exact λ hc, t,
end
-- decidable.rec_on d (λ hnc, e) (λ hc, t)

example : 1 ≠ 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

#print classes
#print instances inhabited

def inhabited.set (α : Type*) : inhabited (set α) :=
begin
  unfold set,
  apply_instance,
end
-- by unfold set; apply_instance

section
  variables a b c d e : Prop
  variable p : Prop → Prop

  theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ iff.refl _

  theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
  begin
    apply eq.subst,
    apply propext h,
    apply h₁,
  end
  -- propext h ▸ h₁
end

-- universe u

-- def set (α : Type u) := α → Prop

namespace set

-- variable {α : Type u}

-- definition mem (x : α) (a : set α) := a x
-- notation e ∈ a := mem e a

theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
begin
  apply funext,
  intro x,
  apply propext,
  apply h,
end
-- funext (assume x, propext (h x))

end set

def f₁ (x : ℕ) := x
def f₂ (x : ℕ) := 0 + x

theorem feq : f₁ = f₂ :=
begin
  apply funext,
  intro x,
  dsimp [f₁, f₂],
  symmetry,
  apply zero_add,
end
-- funext (assume x, (zero_add x).symm)

def val : ℕ :=
begin
  exact eq.rec_on feq (0 : ℕ),
end
-- eq.rec_on feq (0 : ℕ)

-- complicated!
#reduce val

-- evaluates to 0
#eval val

example (α : Type u) : nonempty α ↔ ∃ x : α, true :=
begin
  apply iff.intro,
  intro a,
  induction a,
  use a,

  intro a,
  cases a with a h,
  use a,
end
-- iff.intro (λ ⟨a⟩, ⟨a, trivial⟩) (λ ⟨a, h⟩, ⟨a⟩)

open classical

noncomputable theorem indefinite_description
    {α : Sort u} (p : α → Prop) :
  (∃ x, p x) → {x // p x} :=
λ h, choice (let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩)
