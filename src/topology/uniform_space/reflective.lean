import category_theory.adjunction.basic
import category_theory.fully_faithful
import category_theory.isomorphism
import category_theory.limits.limits

open category_theory
open category_theory.limits

universes v₁ v₂ u₁ u₂

variables {C : Sort u₁} {D : Sort u₁} [𝒞 : category.{v₁+1} C] [𝒟 : category.{v₁+1} D]
include 𝒞 𝒟
variables {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

-- Lemma 4.5.13 from Riehl
def unit_is_iso_of_L_fully_faithful [fully_faithful L] : is_iso (adjunction.unit h) := sorry
def counit_is_iso_of_R_fully_faithful [fully_faithful R] : is_iso (adjunction.counit h) := sorry

def L_fully_faithful_of_unit_is_iso [is_iso (adjunction.unit h)] : fully_faithful L := sorry
def R_fully_faithful_of_counit_is_iso [is_iso (adjunction.counit h)] : fully_faithful R := sorry

-- TODO also do the statements for full and faithful separately.

-- TODO Show that a reflective subcategory is closed under limits.
variables [fully_faithful R]
variables {J : Type v₁} [𝒥 : small_category J]
include 𝒥
include h

@[simp] def reflected_cone (F : J ⥤ D) [has_limit (F ⋙ R)] : cone F :=
{ X := L.obj (limit (F ⋙ R)),
  π :=
  { app := λ j, (h.hom_equiv (limit (F ⋙ R)) (F.obj j)).symm (limit.π (F ⋙ R) j),
    naturality' := begin intros, have w := limit.w (F ⋙ R) f, dsimp, simp only [category.id_comp], rw ←(h.hom_equiv_naturality_right_symm _ _), rw ←w, refl, end } }

def reflected_cone_is_limit (F : J ⥤ D) [has_limit (F ⋙ R)] : is_limit (reflected_cone h F) :=
{ lift := λ s, begin dsimp [reflected_cone], apply R.preimage, apply (h.hom_equiv _ _).to_fun, apply L.map, exact limit.lift _ (R.map_cone s), end }
