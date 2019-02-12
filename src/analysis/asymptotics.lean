/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Big O and little o.
-/
import algebra.pi_instances order.filter analysis.normed_space.basic
open filter

-- move this to normed_space.basic

namespace normed_space

variables {α : Type*} {β : Type*}

protected theorem tendsto_nhds_zero [normed_group β] {f : α → β} {l : filter α} :
  tendsto f l (nhds 0) ↔ ∀ ε > 0, { x | ∥ f x ∥ < ε } ∈ l.sets :=
begin
  rw [metric.tendsto_nhds], simp only [normed_group.dist_eq, sub_zero],
  split,
  { intros h ε εgt0,
    rcases h ε εgt0 with ⟨s, ssets, hs⟩,
    exact mem_sets_of_superset ssets hs },
  intros h ε εgt0,
  exact ⟨_, h ε εgt0, set.subset.refl _⟩ 
end

end normed_space

namespace set
variables {α : Type*} {β : Type*}

def sadd [has_add α] (x : α) (s : set α) := (+) x <$> s

local infixr ` <+> `:65 := sadd

theorem sadd_sadd [add_semigroup α] (x y : α) (s : set α) : x <+> (y <+> s) = (x + y) <+> s :=
by { unfold sadd, rw [←comp_map], congr' 1, ext z, rw add_assoc }

end set

-- asymptotics proper

open filter

namespace asymptotics

variables {α : Type*} {β : Type*} 

section
variable  [normed_ring β]

def is_bigo (g f : α → β) (l : filter α) : Prop :=
∃ c, { x | ∥ g x ∥ ≤ c * ∥ f x ∥ } ∈ l.sets

def bigo (f : α → β) (l : filter α) : set (α → β) :=
{ g : α → β | is_bigo g f l }

def is_littleo (g f : α → β) (l : filter α) : Prop :=
∀ c, { x | c * ∥ g x ∥ ≤ ∥ f x ∥ } ∈ l.sets

def littleo (f : α → β) (l : filter α) : set (α → β) :=
{ g : α → β | is_bigo g f l }

end

theorem tendsto_nhds_zero_of_is_littleo [normed_field β] {f g : α → β} {l : filter α} 
    (h : is_littleo f g l) :  
  tendsto (λ x, f x * (g x)⁻¹) l (nhds 0) :=
begin
  rw normed_space.tendsto_nhds_zero,
  intros ε hε,
  show {x : α | ∥f x * (g x)⁻¹∥ < ε} ∈ l.sets,
  apply mem_sets_of_superset (h (ε⁻¹ + 1)), 
  intro x, dsimp, intro hx,
  rw [normed_field.norm_mul, norm_inv],
  show ∥f x∥ * ∥g x∥⁻¹ < ε,
  cases classical.em (∥g x∥ = 0) with h gne0,
  { rw [h, inv_zero, mul_zero], exact hε },
  cases classical.em (∥f x∥ = 0) with h fne0,
  { rw [h, zero_mul], exact hε },
  have fnpos : ∥f x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm fne0),
  have gnpos : ∥g x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm gne0),
  have enlt : ε⁻¹ < ε⁻¹ + 1, from lt_add_of_pos_right _ zero_lt_one,
  rw [←division_def, div_lt_iff gnpos, mul_comm, ←div_lt_iff hε, division_def, mul_comm],
  show ε⁻¹ * ∥f x∥ < ∥g x∥, from calc
    ε⁻¹ * ∥f x∥ < (ε⁻¹ + 1) * ∥f x∥ : by rw (mul_lt_mul_right fnpos); exact enlt
            ... ≤ ∥g x∥             : hx
end

theorem is_littleo_of_tendsto [normed_field β] {f g : α → β} {l : filter α} 
    (hgf : ∀ x, g x = 0 → f x = 0) (h : tendsto (λ x, f x * (g x)⁻¹) l (nhds 0)) :
  is_littleo f g l :=
begin
  rw normed_space.tendsto_nhds_zero at h,
  intro c, 
  show {x : α | c * ∥f x∥ ≤ ∥g x∥} ∈ l.sets,   
  cases (le_or_gt c 0) with h cgt0,
  { apply mem_sets_of_superset univ_mem_sets,
    intros x _,
    refine le_trans _ (norm_nonneg _),
    exact mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)},
  apply mem_sets_of_superset (h c⁻¹ (inv_pos cgt0)),
  intro x,
  intro hx, 
  change ∥f x * (g x)⁻¹∥ < c⁻¹ at hx,
  show c * ∥f x∥ ≤ ∥g x∥,
  cases classical.em (∥g x∥ = 0) with h gne0,
  { have : g x = 0, from (norm_eq_zero (g x)).mp h,
    rw [hgf _ this, norm_zero, mul_zero], exact norm_nonneg _ },
  have gnpos : ∥g x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm gne0),
  show c * ∥f x∥ ≤ ∥g x∥,  
  rw [mul_comm, ←le_div_iff cgt0, division_def, mul_comm],
  rw [normed_field.norm_mul, norm_inv, ←division_def, div_lt_iff gnpos] at hx,
  exact le_of_lt hx
end

theorem is_littleo_iff [normed_field β] {f g : α → β} {l : filter α} 
    (hgf : ∀ x, g x = 0 → f x = 0) : 
  is_littleo f g l ↔ tendsto (λ x, f x * (g x)⁻¹) l (nhds 0) :=
iff.intro tendsto_nhds_zero_of_is_littleo (is_littleo_of_tendsto hgf)

end asymptotics

