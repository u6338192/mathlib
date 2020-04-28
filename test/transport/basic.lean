import tactic.transport
import order.bounded_lattice
import algebra.lie_algebra

-- We verify that `transport` can move a `semiring` across an equivalence.
-- Note that we've never even mentioned the idea of addition or multiplication to `transport`.
def semiring.map {α : Type} [semiring α] {β : Type} (e : α ≃ β) : semiring β :=
by transport using e

-- Indeed, it can equally well move a `semilattice_sup_top`.
def sup_top.map {α : Type} [semilattice_sup_top α] {β : Type} (e : α ≃ β) : semilattice_sup_top β :=
by transport using e

-- Verify definitional equality of the new structure data.
example {α : Type} [semilattice_sup_top α] {β : Type} (e : α ≃ β) (x y : β) :
begin
  haveI := sup_top.map e,
  exact (x ≤ y) = (e.symm x ≤ e.symm y),
end :=
rfl

-- And why not Lie rings while we're at it?
def lie_ring.map {α : Type} [lie_ring α] {β : Type} (e : α ≃ β) : lie_ring β :=
by transport using e

-- Verify definitional equality of the new structure data.
example {α : Type} [lie_ring α] {β : Type} (e : α ≃ β) (x y : β) :
begin
  haveI := lie_ring.map e,
  exact ⁅x, y⁆ = e ⁅e.symm x, e.symm y⁆
end :=
rfl

-- Below we verify in more detail that the transported structure for `semiring`
-- is definitionally what you would hope for.

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

def mynat_equiv : ℕ ≃ mynat :=
{ to_fun := λ n, nat.rec_on n mynat.zero (λ n, mynat.succ),
  inv_fun := λ n, mynat.rec_on n nat.zero (λ n, nat.succ),
  left_inv := λ n, begin induction n, refl, exact congr_arg nat.succ n_ih, end,
  right_inv := λ n, begin induction n, refl, exact congr_arg mynat.succ n_ih, end }

@[simp] lemma mynat_equiv_apply_zero : mynat_equiv 0 = mynat.zero := rfl
@[simp] lemma mynat_equiv_apply_succ (n : ℕ) :
  mynat_equiv (n + 1) = mynat.succ (mynat_equiv n) := rfl
@[simp] lemma mynat_equiv_symm_apply_zero : mynat_equiv.symm mynat.zero = 0:= rfl
@[simp] lemma mynat_equiv_symm_apply_succ (n : mynat) :
  mynat_equiv.symm (mynat.succ n) = (mynat_equiv.symm n) + 1 := rfl

instance semiring_mynat : semiring mynat :=
by transport (by apply_instance : semiring ℕ) using mynat_equiv

lemma mynat_add_def (a b : mynat) : a + b = mynat_equiv (mynat_equiv.symm a + mynat_equiv.symm b) :=
rfl

-- Verify that we can do computations with the transported structure.
example :
  (mynat.succ (mynat.succ mynat.zero)) + (mynat.succ mynat.zero) =
    (mynat.succ (mynat.succ (mynat.succ mynat.zero))) :=
rfl

lemma mynat_zero_def : (0 : mynat) = mynat_equiv 0 :=
rfl

lemma mynat_one_def : (1 : mynat) = mynat_equiv 1 :=
rfl

lemma mynat_mul_def (a b : mynat) : a * b = mynat_equiv (mynat_equiv.symm a * mynat_equiv.symm b) :=
rfl

example : (3 : mynat) + (7 : mynat) = (10 : mynat) :=
rfl

example : (2 : mynat) * (2 : mynat) = (4 : mynat) :=
rfl

example : (3 : mynat) + (7 : mynat) * (2 : mynat) = (17 : mynat) :=
rfl
