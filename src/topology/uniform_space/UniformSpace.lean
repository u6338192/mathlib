/- Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison

Introduce UniformSpace -- the category of uniform spaces.
-/
import category_theory.concrete_category
import category_theory.full_subcategory
import topology.uniform_space.complete_separated
import topology.Top.basic

universes u v

open category_theory

/-- The category of uniform spaces. -/
@[reducible] def UniformSpace : Type (u+1) := bundled uniform_space

namespace UniformSpace

instance (x : UniformSpace) : uniform_space x := x.str

-- TODO fix the order of the implicit arguments f and g in uniform_continuous.comp,
-- then replace the second half of this with `@uniform_continuous.comp`.
instance concrete_category_uniform_continuous : concrete_category @uniform_continuous :=
⟨@uniform_continuous_id, by { introsI, apply uniform_continuous.comp; assumption }⟩

def of (α : Type u) [uniform_space α] : UniformSpace := ⟨α⟩

abbreviation forget : UniformSpace.{u} ⥤ Type u := forget

instance forget.faithful : faithful (forget) := {}

def forget_to_Top : UniformSpace.{u} ⥤ Top.{u} :=
{ obj := λ X, { α := X.1 },
  map := λ X Y f, ⟨ f, uniform_continuous.continuous f.property ⟩ }

def forget_to_Type_via_Top : forget_to_Top ⋙ Top.forget ≅ forget := iso.refl _

end UniformSpace

structure CpltSepUniformSpace :=
(α : Type u)
[is_uniform_space : uniform_space α]
[is_complete_space : complete_space α]
[is_separated : separated α]

namespace CpltSepUniformSpace

instance : has_coe_to_sort CpltSepUniformSpace :=
{ S := Type u, coe := CpltSepUniformSpace.α }

attribute [instance] is_uniform_space is_complete_space is_separated

def to_UniformSpace (X : CpltSepUniformSpace) : UniformSpace :=
⟨X.α⟩

instance CpltSepUniformSpace_category : category CpltSepUniformSpace :=
induced_category.category to_UniformSpace

def of (X : Type u) [uniform_space X] [complete_space X] [separated X] : CpltSepUniformSpace := ⟨X⟩

def forget_to_UniformSpace : CpltSepUniformSpace ⥤ UniformSpace := induced_functor to_UniformSpace

def forget : CpltSepUniformSpace ⥤ Type u :=
{ obj := λ R, R,
  map := λ R S f, f.1 }

instance forget_faithful : faithful forget := {}

def forget_to_Type_via_UniformSpace : forget_to_UniformSpace ⋙ UniformSpace.forget ≅ forget := iso.refl _



end CpltSepUniformSpace
