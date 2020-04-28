/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import group_theory.group_action

/-!
# Modules over a ring

In this file we define

* `semimodule R M` : an additive commutative monoid `M` is a `semimodule` over a
  `semiring` `R` if for `r : R` and `x : M` their "scalar multiplication `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

* `module R M` : same as `semimodule R M` but assumes that `R` is a `ring` and `M` is an
  additive commutative group.

* `vector_space k M` : same as `semimodule k M` and `module k M` but assumes that `k` is a `field`
  and `M` is an additive commutative group.

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`module`s.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map.

* `submodule R M` : a subset of `M` that contains zero and is closed with respect to addition and
  scalar multiplication.

* `subspace k M` : an abbreviation for `submodule` assuming that `k` is a `field`.

## Implementation notes

* `vector_space` is an abbreviation for `module R M` while the latter `extends semimodule R M`.
  There were several attempts to make `module` an abbreviation of `semimodule` but this makes
  class instance search too hard for Lean 3.

## TODO

* `submodule R M` was written before bundled `submonoid`s, so it does not extend it.

## Tags

semimodule, module, vector space, submodule, subspace, linear map
-/

open function

universes u u' v w x y z
variables {R : Type u} {k : Type u'} {S : Type v} {M : Type w} {M₂ : Type x} {M₃ : Type y}
  {ι : Type z}

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
end prio

section semimodule
variables [semiring R] [add_comm_monoid M] [semimodule R M] (r s : R) (x y : M)

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
variables (R)
@[simp] theorem zero_smul : (0 : R) • x = 0 := semimodule.zero_smul x

variable (M)

/-- `(•)` as an `add_monoid_hom`. -/
def smul_add_hom : R →+ M →+ M :=
{ to_fun := const_smul_hom M,
  map_zero' := add_monoid_hom.ext $ λ r, by simp,
  map_add' := λ x y, add_monoid_hom.ext $ λ r, by simp [add_smul] }

variables {R M}

@[simp] lemma smul_add_hom_apply (r : R) (x : M) :
  smul_add_hom R M r x = r • x := rfl

lemma semimodule.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 :=
by rw [←one_smul R x, ←zero_eq_one, zero_smul]

lemma list.sum_smul {l : list R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_list_sum l

lemma multiset.sum_smul {l : multiset R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_multiset_sum l

lemma finset.sum_smul {f : ι → R} {s : finset ι} {x : M} :
  s.sum f • x = s.sum (λ r, (f r) • x) :=
((smul_add_hom R M).flip x).map_sum f s

end semimodule

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `R` and an additive group of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (R : Type u) (M : Type v) [ring R] [add_comm_group M] extends semimodule R M
end prio

/--
To prove two module structures on a fixed `add_comm_group` agree,
it suffices to check the scalar multiplications agree.
-/
-- We'll later use this to show `module ℤ M` is a subsingleton.
@[ext]
lemma module_ext {R : Type*} [ring R] {M : Type*} [add_comm_group M] (P Q : module R M)
  (w : ∀ (r : R) (m : M), by { haveI := P, exact r • m } = by { haveI := Q, exact r • m }) :
  P = Q :=
begin
  resetI,
  rcases P with ⟨⟨⟨⟨⟨P⟩⟩⟩⟩⟩, rcases Q with ⟨⟨⟨⟨⟨Q⟩⟩⟩⟩⟩, congr,
  funext r m,
  exact w r m,
  all_goals { apply proof_irrel_heq },
end

/-- An auxiliary `structure` that is used to define `module`s without verifying
`zero_smul` and `smul_zero`. -/
structure module.core (R M) [ring R] [add_comm_group M] extends has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀x : M, (1 : R) • x = x)

/-- Define `module` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `module.core`. -/
def module.of_core [ring R] [add_comm_group M] (Mc : module.core R M) : module R M :=
by letI := Mc.to_has_scalar; exact
{ zero_smul := λ x, (add_monoid_hom.mk' (λ r : R, r • x) (λ r s, Mc.add_smul r s x)).map_zero,
  smul_zero := λ r, (add_monoid_hom.mk' ((•) r) (Mc.smul_add r)).map_zero,
  ..Mc }

section module
variables [ring R] [add_comm_group M] [module R M] (r s : R) (x y : M)

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

variables (R)
theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp
variables {R}

@[simp] theorem smul_neg : r • (-x) = -(r • x) :=
by rw [← neg_one_smul R, ← mul_smul, mul_neg_one, neg_smul]

theorem smul_sub (r : R) (x y : M) : r • (x - y) = r • x - r • y :=
by simp [smul_add, sub_eq_add_neg]; rw smul_neg

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y :=
by simp [add_smul, sub_eq_add_neg]

theorem smul_eq_zero {R E : Type*} [division_ring R] [add_comm_group E] [module R E]
  {c : R} {x : E} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
⟨λ h, classical.by_cases or.inl
  (λ hc, or.inr $ by rw [← one_smul R x, ← inv_mul_cancel hc, mul_smul, h, smul_zero]),
  λ h, h.elim (λ hc, hc.symm ▸ zero_smul R x) (λ hx, hx.symm ▸ smul_zero c)⟩

end module

instance semiring.to_semimodule [semiring R] : semimodule R R :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul,
  zero_smul := zero_mul,
  smul_zero := mul_zero }

@[simp] lemma smul_eq_mul [semiring R] {a a' : R} : a • a' = a * a' := rfl

instance ring.to_module [ring R] : module R R :=
{ to_semimodule := semiring.to_semimodule }

/-- A ring homomorphism `f : R →+* S` defines a semimodule structure by `r • x = f r * x`. -/
def ring_hom.to_semimodule [semiring R] [semiring S] (f : R →+* S) : semimodule R S :=
{ smul := λ r x, f r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw [mul_add],
  add_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_add, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_mul, mul_assoc],
  one_smul := λ x, show f 1 * x = _, by rw [f.map_one, one_mul],
  zero_smul := λ x, show f 0 * x = 0, by rw [f.map_zero, zero_mul],
  smul_zero := λ r, mul_zero (f r) }

/-- A ring homomorphism `f : R →+* S` defines a module structure by `r • x = f r * x`. -/
def ring_hom.to_module [ring R] [ring S] (f : R →+* S) : module R S :=
{ to_semimodule := f.to_semimodule }

/-- A class saying that `f` is an `R` linear map. Though it is a class,
it is used as an explicit argument in most lemmas. -/
class is_linear_map (R : Type u) {M : Type v} {M₂ : Type w}
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M → M₂) : Prop :=
(add [] : ∀ x y, f (x + y) = f x + f y)
(smul [] : ∀ (c : R) x, f (c • x) = c • f x)

/-- A bundled `R`-linear map from `M` to `M₂`. -/
structure linear_map (R : Type u) (M : Type v) (M₂ : Type w)
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂] :=
(to_fun : M → M₂)
(add  : ∀x y, to_fun (x + y) = to_fun x + to_fun y)
(smul : ∀(c : R) x, to_fun (c • x) = c • to_fun x)

infixr ` →ₗ `:25 := linear_map _
notation β ` →ₗ[`:25 α:25 `] `:0 γ:0 := linear_map α β γ

namespace linear_map

variables [ring R] [add_comm_group M] [add_comm_group M₂]

section
variables [module R M] [module R M₂]
variables (f g : M →ₗ[R] M₂)

instance : has_coe_to_fun (M →ₗ[R] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : M → M₂) (h₁ h₂) :
  ((linear_map.mk f h₁ h₂ : M →ₗ[R] M₂) : M → M₂) = f := rfl
end

-- We can infer the module structure implicitly from the linear maps,
-- rather than via typeclass resolution.
variables {module_M : module R M} {module_M₂ : module R M₂}
variables (f g : M →ₗ[R] M₂)

@[simp] lemma to_fun_eq_coe : f.to_fun = ⇑f := rfl

theorem is_linear : is_linear_map R f := {..f}

variables {f g}
@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma coe_fn_congr : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl } , ext⟩

variables (f g)

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := f.add x y

@[simp] lemma map_smul (c : R) (x : M) : f (c • x) = c • f x := f.smul c x

@[simp] lemma map_zero : f 0 = 0 :=
by rw [← zero_smul R, map_smul f 0 0, zero_smul]

instance : is_add_group_hom f := { map_add := map_add f }

/-- convert a linear map to an additive map -/
def to_add_monoid_hom : M →+ M₂ :=
{ to_fun := f,
  map_zero' := f.map_zero,
  map_add' := f.map_add }

@[simp] lemma to_add_monoid_hom_coe :
  ((f.to_add_monoid_hom) : M → M₂) = f := rfl

@[simp] lemma map_neg (x : M) : f (- x) = - f x :=
f.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (x y : M) : f (x - y) = f x - f y :=
f.to_add_monoid_hom.map_sub x y

@[simp] lemma map_sum {t : finset ι} {g : ι → M} :
  f (t.sum g) = t.sum (λi, f (g i)) :=
f.to_add_monoid_hom.map_sum _ _

end linear_map

namespace linear_map
variables [ring R] [add_comm_group M] [add_comm_group M₂]
variables [add_comm_group M₃]
variables {module_M : module R M} {module_M₂ : module R M₂} {module_M₃ : module R M₃}
variables (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂)

/-- Composition of two linear maps is a linear map -/
def comp : M →ₗ[R] M₃ := ⟨f ∘ g, by simp, by simp⟩

@[simp] lemma comp_apply (x : M) : f.comp g x = f (g x) := rfl

/-- Identity map as a `linear_map` -/
def id {R} {M} [ring R] [add_comm_group M] [module R M] : M →ₗ[R] M := ⟨id, λ _ _, rfl, λ _ _, rfl⟩

@[simp] lemma id_apply {R} {M} [ring R] [add_comm_group M] [module R M] (x : M) :
  @id R M _ _ _ x = x := rfl

end linear_map

namespace is_linear_map
variables [ring R] [add_comm_group M] [add_comm_group M₂]
variables [module R M] [module R M₂]

/-- Convert an `is_linear_map` predicate to a `linear_map` -/
def mk' (f : M → M₂) (H : is_linear_map R f) : M →ₗ M₂ := {to_fun := f, ..H}

@[simp] theorem mk'_apply {f : M → M₂} (H : is_linear_map R f) (x : M) :
  mk' f H x = f x := rfl

lemma is_linear_map_neg : is_linear_map R (λ (z : M), -z) :=
is_linear_map.mk neg_add (λ x y, (smul_neg x y).symm)

lemma is_linear_map_smul {R M : Type*} [comm_ring R] [add_comm_group M] [module R M] (c : R) :
  is_linear_map R (λ (z : M), c • z) :=
begin
  refine is_linear_map.mk (smul_add c) _,
  intros _ _,
  simp only [smul_smul, mul_comm]
end

--TODO: move
lemma is_linear_map_smul' (a : M) :
  is_linear_map R (λ (c : R), c • a) :=
is_linear_map.mk (λ x y, add_smul x y a) (λ x y, mul_smul x y a)

variables {f : M → M₂} (lin : is_linear_map R f)
include M M₂ lin

lemma map_zero : f (0 : M) = (0 : M₂) := (lin.mk' f).map_zero

lemma map_add : ∀ x y, f (x + y) = f x + f y := lin.add

lemma map_neg (x) : f (- x) = - f x := (lin.mk' f).map_neg x

lemma map_sub (x y) : f (x - y) = f x - f y := (lin.mk' f).map_sub x y

lemma map_smul (c : R) (x : M) : f (c • x) = c • f x := (lin.mk' f).map_smul c x

end is_linear_map

/-- Ring of linear endomorphismsms of a module. -/
abbreviation module.End (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] := M →ₗ[R] M

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure submodule (R : Type u) (M : Type v) [ring R]
  [add_comm_group M] [module R M] : Type v :=
(carrier : set M)
(zero : (0:M) ∈ carrier)
(add : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
(smul : ∀ (c:R) {x}, x ∈ carrier → c • x ∈ carrier)

namespace submodule
variables [ring R] [add_comm_group M] [add_comm_group M₂]

section
variables [module R M]

instance : has_coe (submodule R M) (set M) := ⟨submodule.carrier⟩
instance : has_mem M (submodule R M) := ⟨λ x p, x ∈ (p : set M)⟩
end

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variables {module_M : module R M}
variables {p q : submodule R M}
variables {r : R} {x y : M}

theorem ext' (h : (p : set M) = q) : p = q :=
by cases p; cases q; congr'

protected theorem ext'_iff : (p : set M) = q ↔ p = q :=
⟨ext', λ h, h ▸ rfl⟩

@[ext] theorem ext
  (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := ext' $ set.ext h

variables (p)
@[simp] theorem mem_coe : x ∈ (p : set M) ↔ x ∈ p := iff.rfl

@[simp] lemma zero_mem : (0 : M) ∈ p := p.zero

lemma add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p := p.add h₁ h₂

lemma smul_mem (r : R) (h : x ∈ p) : r • x ∈ p := p.smul r h

lemma neg_mem (hx : x ∈ p) : -x ∈ p := by rw ← neg_one_smul R; exact p.smul_mem _ hx

lemma sub_mem (hx : x ∈ p) (hy : y ∈ p) : x - y ∈ p := p.add_mem hx (p.neg_mem hy)

lemma neg_mem_iff : -x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa using neg_mem p h, neg_mem p⟩

lemma add_mem_iff_left (h₁ : y ∈ p) : x + y ∈ p ↔ x ∈ p :=
⟨λ h₂, by simpa using sub_mem _ h₂ h₁, λ h₂, add_mem _ h₂ h₁⟩

lemma add_mem_iff_right (h₁ : x ∈ p) : x + y ∈ p ↔ y ∈ p :=
⟨λ h₂, by simpa using sub_mem _ h₂ h₁, add_mem _ h₁⟩

lemma sum_mem {t : finset ι} {f : ι → M} :
  (∀c∈t, f c ∈ p) → t.sum f ∈ p :=
begin
  classical,
  exact finset.induction_on t (by simp [p.zero_mem]) (by simp [p.add_mem] {contextual := tt})
end

lemma smul_mem_iff' (u : units R) : (u:R) • x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa only [smul_smul, u.inv_mul, one_smul] using p.smul_mem ↑u⁻¹ h, p.smul_mem u⟩

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance : has_neg p := ⟨λx, ⟨-x.1, neg_mem _ x.2⟩⟩
instance : has_scalar R p := ⟨λ c x, ⟨c • x.1, smul_mem _ c x.2⟩⟩

variables {p}
@[simp, norm_cast] lemma coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : p) : M) = 0 := rfl
@[simp, norm_cast] lemma coe_neg (x : p) : ((-x : p) : M) = -x := rfl
@[simp, norm_cast] lemma coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x := rfl

@[simp] protected lemma eta (x : p) (hx : (x : M) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

instance : add_comm_group p :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..};
  { intros, apply set_coe.ext, simp [add_comm, add_left_comm] }

instance submodule_is_add_subgroup : is_add_subgroup (p : set M) :=
{ zero_mem := p.zero,
  add_mem  := p.add,
  neg_mem  := λ _, p.neg_mem }

@[simp, norm_cast] lemma coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y := rfl

variables (p)

instance : module R p :=
by refine {smul := (•), ..};
   { intros, apply set_coe.ext, simp [smul_add, add_smul, mul_smul] }

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val : ((submodule.subtype p) : p → M) = subtype.val := rfl

end submodule

-- TODO: Do we want one-sided ideals?

/-- Ideal in a commutative ring is an additive subgroup `s` such that
`a * b ∈ s` whenever `b ∈ s`. We define `ideal R` as `submodule R R`. -/
@[reducible] def ideal (R : Type u) [comm_ring R] := submodule R R

namespace ideal
variables [comm_ring R] (I : ideal R) {a b : R}

protected lemma zero_mem : (0 : R) ∈ I := I.zero_mem

protected lemma add_mem : a ∈ I → b ∈ I → a + b ∈ I := I.add_mem

lemma neg_mem_iff : -a ∈ I ↔ a ∈ I := I.neg_mem_iff

lemma add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) := I.add_mem_iff_left

lemma add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) := I.add_mem_iff_right

protected lemma sub_mem : a ∈ I → b ∈ I → a - b ∈ I := I.sub_mem

lemma mul_mem_left : b ∈ I → a * b ∈ I := I.smul_mem _

lemma mul_mem_right (h : a ∈ I) : a * b ∈ I := mul_comm b a ▸ I.mul_mem_left h

end ideal

/--
Vector spaces are defined as an `abbreviation` for modules,
if the base ring is a field.
(A previous definition made `vector_space` a structure
defined to be `module`.)
This has as advantage that vector spaces are completely transparent
for type class inference, which means that all instances for modules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend vector spaces an sich,
in definitions such as `normed_space`.
The solution is to extend `module` instead.
-/
library_note "vector space definition"

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
abbreviation vector_space (k : Type u) (M : Type v) [field k] [add_comm_group M] :=
module k M

instance field.to_vector_space {k : Type*} [field k] : vector_space k k := ring.to_module

/-- Subspace of a vector space. Defined to equal `submodule`. -/
@[reducible] def subspace (k : Type u) (M : Type v)
  [field k] [add_comm_group M] [vector_space k M] : Type v :=
submodule k M

instance subspace.vector_space {k M}
  {f : field k} [add_comm_group M] [vector_space k M]
  (p : subspace k M) : vector_space k p := p.module

namespace submodule

variables [division_ring R] [add_comm_group M] [module R M]
variables (p : submodule R M) {r : R} {x y : M}

theorem smul_mem_iff (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
p.smul_mem_iff' (units.mk0 r r0)

end submodule

namespace add_comm_monoid
open add_monoid

variables [add_comm_monoid M]

/-- The natural ℕ-semimodule structure on any `add_comm_monoid`. -/
-- We don't make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℕ`.
def nat_semimodule : semimodule ℕ M :=
{ smul := smul,
  smul_add := λ _ _ _, smul_add _ _ _,
  add_smul := λ _ _ _, add_smul _ _ _,
  mul_smul := λ _ _ _, mul_smul _ _ _,
  one_smul := one_smul,
  zero_smul := zero_smul,
  smul_zero := smul_zero }

end add_comm_monoid

namespace add_comm_group

variables [add_comm_group M]

/-- The natural ℤ-module structure on any `add_comm_group`. -/
-- We don't immediately make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℤ`.
-- We do turn it into a global instance, but only at the end of this file,
-- and I remain dubious whether this is a good idea.
def int_module : module ℤ M :=
{ smul := gsmul,
  smul_add := λ _ _ _, gsmul_add _ _ _,
  add_smul := λ _ _ _, add_gsmul _ _ _,
  mul_smul := λ _ _ _, gsmul_mul _ _ _,
  one_smul := one_gsmul,
  zero_smul := zero_gsmul,
  smul_zero := gsmul_zero }

instance : subsingleton (module ℤ M) :=
begin
  split,
  intros P Q,
  ext,
  -- isn't that lovely: `r • m = r • m`
  have one_smul : by { haveI := P, exact (1 : ℤ) • m } = by { haveI := Q, exact (1 : ℤ) • m },
    begin
      rw [@one_smul ℤ _ _ (by { haveI := P, apply_instance, }) m],
      rw [@one_smul ℤ _ _ (by { haveI := Q, apply_instance, }) m],
    end,
  have nat_smul : ∀ n : ℕ, by { haveI := P, exact (n : ℤ) • m } = by { haveI := Q, exact (n : ℤ) • m },
    begin
      intro n,
      induction n with n ih,
      { erw [zero_smul, zero_smul], },
      { rw [int.coe_nat_succ, add_smul, add_smul],
        erw ih,
        rw [one_smul], }
    end,
  cases r,
  { rw [int.of_nat_eq_coe, nat_smul], },
  { rw [int.neg_succ_of_nat_coe, neg_smul, neg_smul, nat_smul], }
end

end add_comm_group

section
local attribute [instance] add_comm_monoid.nat_semimodule

lemma semimodule.smul_eq_smul (R : Type*) [semiring R]
  {M : Type*} [add_comm_monoid M] [semimodule R M]
  (n : ℕ) (b : M) : n • b = (n : R) • b :=
begin
  induction n with n ih,
  { rw [nat.cast_zero, zero_smul, zero_smul] },
  { change (n + 1) • b = (n + 1 : R) • b,
    rw [add_smul, add_smul, one_smul, ih, one_smul] }
end

lemma semimodule.add_monoid_smul_eq_smul (R : Type*) [semiring R]
  {M : Type*} [add_comm_monoid M] [semimodule R M] (n : ℕ) (b : M) :
  add_monoid.smul n b = (n : R) • b :=
semimodule.smul_eq_smul R n b

lemma nat.smul_def {M : Type*} [add_comm_monoid M] (n : ℕ) (x : M) :
  n • x = add_monoid.smul n x :=
rfl

end

section
local attribute [instance] add_comm_group.int_module

lemma gsmul_eq_smul {M : Type*} [add_comm_group M] (n : ℤ) (x : M) : gsmul n x = n • x := rfl

lemma module.gsmul_eq_smul_cast (R : Type*) [ring R] {β : Type*} [add_comm_group β] [module R β]
  (n : ℤ) (b : β) : gsmul n b = (n : R) • b :=
begin
  cases n,
  { apply semimodule.add_monoid_smul_eq_smul, },
  { dsimp,
    rw semimodule.add_monoid_smul_eq_smul R,
    push_cast,
    rw neg_smul, }
end

lemma module.gsmul_eq_smul {M : Type*} [add_comm_group M] [module ℤ M]
  (n : ℤ) (b : M) : gsmul n b = n • b :=
by rw [module.gsmul_eq_smul_cast ℤ, int.cast_id]

end

-- We prove this without using the `add_comm_group.int_module` instance, so the `•`s here
-- come from whatever the local `module ℤ` structure actually is.
lemma add_monoid_hom.map_int_module_smul
  [add_comm_group M] [add_comm_group M₂]
  [module ℤ M] [module ℤ M₂] (f : M →+ M₂) (x : ℤ) (a : M) : f (x • a) = x • f a :=
by simp only [← module.gsmul_eq_smul, f.map_gsmul]

lemma add_monoid_hom.map_int_cast_smul
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →+ M₂) (x : ℤ) (a : M) : f ((x : R) • a) = (x : R) • f a :=
by simp only [← module.gsmul_eq_smul_cast, f.map_gsmul]

lemma add_monoid_hom.map_nat_cast_smul
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂] (f : M →+ M₂) (x : ℕ) (a : M) :
  f ((x : R) • a) = (x : R) • f a :=
by simp only [← semimodule.add_monoid_smul_eq_smul, f.map_smul]

lemma add_monoid_hom.map_rat_cast_smul {R : Type*} [division_ring R] [char_zero R]
  {E : Type*} [add_comm_group E] [module R E] {F : Type*} [add_comm_group F] [module R F]
  (f : E →+ F) (c : ℚ) (x : E) :
  f ((c : R) • x) = (c : R) • f x :=
begin
  have : ∀ (x : E) (n : ℕ), 0 < n → f (((n⁻¹ : ℚ) : R) • x) = ((n⁻¹ : ℚ) : R) • f x,
  { intros x n hn,
    replace hn : (n : R) ≠ 0 := nat.cast_ne_zero.2 (ne_of_gt hn),
    conv_rhs { congr, skip, rw [← one_smul R x, ← mul_inv_cancel hn, mul_smul] },
    rw [f.map_nat_cast_smul, smul_smul, rat.cast_inv, rat.cast_coe_nat,
      inv_mul_cancel hn, one_smul] },
  refine c.num_denom_cases_on (λ m n hn hmn, _),
  rw [rat.mk_eq_div, div_eq_mul_inv, rat.cast_mul, int.cast_coe_nat, mul_smul, mul_smul,
    rat.cast_coe_int, f.map_int_cast_smul, this _ n hn]
end

lemma add_monoid_hom.map_rat_module_smul {E : Type*} [add_comm_group E] [vector_space ℚ E]
  {F : Type*} [add_comm_group F] [module ℚ F] (f : E →+ F) (c : ℚ) (x : E) :
  f (c • x) = c • f x :=
rat.cast_id c ▸ f.map_rat_cast_smul c x

-- We finally turn on these instances globally:
attribute [instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def add_monoid_hom.to_int_linear_map [add_comm_group M] [add_comm_group M₂] (f : M →+ M₂) :
  M →ₗ[ℤ] M₂ :=
⟨f, f.map_add, f.map_int_module_smul⟩

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def add_monoid_hom.to_rat_linear_map [add_comm_group M] [vector_space ℚ M]
  [add_comm_group M₂] [vector_space ℚ M₂] (f : M →+ M₂) :
  M →ₗ[ℚ] M₂ :=
⟨f, f.map_add, f.map_rat_module_smul⟩

namespace finset

variable (R)

lemma sum_const' [semiring R] [add_comm_monoid M] [semimodule R M] {s : finset ι} (b : M) :
  finset.sum s (λ (i : ι), b) = (finset.card s : R) • b :=
by rw [finset.sum_const, ← semimodule.smul_eq_smul]; refl

variables {R} [decidable_linear_ordered_cancel_add_comm_monoid M]
  {s : finset ι} (f : ι → M)

theorem exists_card_smul_le_sum (hs : s.nonempty) :
  ∃ i ∈ s, s.card • f i ≤ s.sum f :=
exists_le_of_sum_le hs $ by rw [sum_const, ← nat.smul_def, smul_sum]

theorem exists_card_smul_ge_sum (hs : s.nonempty) :
  ∃ i ∈ s, s.sum f ≤ s.card • f i :=
exists_le_of_sum_le hs $ by rw [sum_const, ← nat.smul_def, smul_sum]

end finset
