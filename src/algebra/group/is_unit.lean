/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Contents of this file was cherry-picked from `algebra/associated` by Yury Kudryashov.
I copied the original copyright header from there.
-/
import algebra.group.units_hom

/-!
# `is_unit` predicate

In this file we define the `is_unit` predicate on a `monoid`, and
prove a few basic properties. For the bundled version see `units`. See
also `prime`, `associated`, and `irreducible` in `algebra/associated`.

-/

variables {M : Type*} {N : Type*}

/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : units M`, where
`units M` is a bundled version of `is_unit`. -/
def is_unit [monoid M] (a : M) : Prop := ∃ u : units M, a = u

@[simp] lemma is_unit_unit [monoid M] (u : units M) : is_unit (u : M) := ⟨u, rfl⟩

lemma is_unit.map [monoid M] [monoid N] (f : M →* N) {x : M} (h : is_unit x) : is_unit (f x) :=
by rcases h with ⟨y, rfl⟩; exact is_unit_unit (units.map f y)

lemma is_unit.map' [monoid M] [monoid N] (f : M → N) {x : M} (h : is_unit x) [is_monoid_hom f] :
  is_unit (f x) :=
h.map (monoid_hom.of f)

@[simp] theorem is_unit_one [monoid M] : is_unit (1:M) := ⟨1, rfl⟩

theorem is_unit_of_mul_one [comm_monoid M] (a b : M) (h : a * b = 1) : is_unit a :=
⟨units.mk_of_mul_eq_one a b h, rfl⟩

theorem is_unit_iff_exists_inv [comm_monoid M] {a : M} : is_unit a ↔ ∃ b, a * b = 1 :=
⟨by rintro ⟨⟨a, b, hab, _⟩, rfl⟩; exact ⟨b, hab⟩,
 λ ⟨b, hab⟩, is_unit_of_mul_one _ b hab⟩

theorem is_unit_iff_exists_inv' [comm_monoid M] {a : M} : is_unit a ↔ ∃ b, b * a = 1 :=
by simp [is_unit_iff_exists_inv, mul_comm]

/-- Multiplication by a `u : units M` doesn't affect `is_unit`. -/
@[simp] theorem units.is_unit_mul_units [monoid M] (a : M) (u : units M) :
  is_unit (a * u) ↔ is_unit a :=
iff.intro
  (assume ⟨v, hv⟩,
    have is_unit (a * ↑u * ↑u⁻¹), by existsi v * u⁻¹; rw [hv, units.coe_mul],
    by rwa [mul_assoc, units.mul_inv, mul_one] at this)
  (assume ⟨v, hv⟩, hv.symm ▸ ⟨v * u, (units.coe_mul v u).symm⟩)

theorem is_unit_of_mul_is_unit_left [comm_monoid M] {x y : M}
  (hu : is_unit (x * y)) : is_unit x :=
let ⟨z, hz⟩ := is_unit_iff_exists_inv.1 hu in
is_unit_iff_exists_inv.2 ⟨y * z, by rwa ← mul_assoc⟩

theorem is_unit_of_mul_is_unit_right [comm_monoid M] {x y : M}
  (hu : is_unit (x * y)) : is_unit y :=
@is_unit_of_mul_is_unit_left _ _ y x $ by rwa mul_comm

@[simp] theorem is_unit_nat {n : ℕ} : is_unit n ↔ n = 1 :=
iff.intro
  (assume ⟨u, hu⟩, match n, u, hu, nat.units_eq_one u with _, _, rfl, rfl := rfl end)
  (assume h, h.symm ▸ ⟨1, rfl⟩)

/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* units N`. See also `units.lift_right` for a computable version. -/
noncomputable def is_unit.lift_right [monoid M] [monoid N] (f : M →* N)
  (hf : ∀ x, is_unit (f x)) : M →* units N :=
units.lift_right f (λ x, classical.some (hf x)) (λ x, (classical.some_spec (hf x)).symm)

@[simp] lemma is_unit.coe_lift_right [monoid M] [monoid N] (f : M →* N)
  (hf : ∀ x, is_unit (f x)) (x) :
  (is_unit.lift_right f hf x : N) = f x :=
units.coe_lift_right _ x
