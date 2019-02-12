/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The Frechet derivative. We use `fderiv` for the Frechet derivative, and `deriv`
for the univariate one.
-/
import tactic.interactive order.filter topology.basic analysis.normed_space.bounded_linear_maps
import .asymptotics
universe u

/- move this stuff -/

-- note: in module.lean, there should also be unbundled theorems for linear maps. Here
-- is an example.

namespace is_linear_map
variables {α : Type*} {β : Type*} {γ : Type*}
variables [ring α] [add_comm_group β] [add_comm_group γ]
variables [module α β] [module α γ]
include α

@[simp] theorem map_zero {f : β → γ} (h : is_linear_map α f) : f 0 = 0 :=
(mk' _ h).map_zero

end is_linear_map

-- move to order.filter.basic

namespace filter

variables {α : Type*} {β : Type*} {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}

theorem tendsto.congr (h : tendsto f₁ l₁ l₂) (h' : ∀ x, f₁ x = f₂ x) : 
  tendsto f₂ l₁ l₂ :=
have f₁ = f₂, from funext h',
by rw ←this; exact h

-- change implicit arguments in tendsto_const_nhds

end filter

open filter

-- move to topology.basic

-- rename tendsto_at_within_iff_subtype to tendsto_nhds_within

section

variables {α : Type*} {β : Type*} 

theorem tendsto_nhds_within_mono_left [topological_space α] {f : α → β} {a : α} 
    {s t : set α} {l : filter β} (h : tendsto f (nhds_within a t) l) (hst : s ⊆ t) : 
  tendsto f (nhds_within a s) l :=
tendsto_le_left (nhds_within_mono a hst) h

theorem tendsto_nhds_within_mono_right [topological_space β] {f : α → β} {l : filter α}
    {a : β} {s t : set β}(h : tendsto f l (nhds_within a s)) (hst : s ⊆ t) : 
  tendsto f l (nhds_within a t) :=
tendsto_le_right (nhds_within_mono a hst) h

theorem tendsto_nhds_within_of_tendsto_nhds [topological_space α] {f : α → β} {a : α} 
    {s : set α} {l : filter β} (h : tendsto f (nhds a) l) : 
  tendsto f (nhds_within a s) l :=
by rw [←nhds_within_univ] at h; exact tendsto_nhds_within_mono_left h (set.subset_univ _)

end

-- move to normed_space

section
variables {α : Type*} [normed_field α] {β : Type*} {γ : Type*}
variables {E : Type*} {F : Type*} [normed_space α E] [normed_space α F]

lemma tendsto_smul_const {g : γ → F} {e : filter γ} (s : α) {b : F} :
  (tendsto g e (nhds b)) → tendsto (λ x, s • (g x)) e (nhds (s • b)) :=
tendsto_smul tendsto_const_nhds 

end 

-- deriv begins here

open asymptotics

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]

def has_fderiv_at_within (f : E → F) (f' : E → F) (x : E) (s : set E) :=
is_bounded_linear_map f' ∧ 
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0)

def has_fderiv_at (f : E → F) (f' : E → F) (x : E) :=
has_fderiv_at_within f f' x set.univ

theorem has_fderiv_equiv_aux (f : E → F) (f' : E → F) (x : E) (s : set E) 
    (bf' : is_bounded_linear_map f') :
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) (nhds_within x s) (nhds 0) = 
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
begin
  have f'0 : f' 0 = 0 := bf'.to_is_linear_map.map_zero,
  rw [tendsto_iff_norm_tendsto_zero], congr,
  ext x',
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

theorem has_fderiv_iff_littleo {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within f f' x s ↔
    is_bounded_linear_map f' ∧ 
      is_littleo (λ x', ∥f x' - f x - f' (x' - x)∥) (λ x', ∥x' - x∥) (nhds_within x s) :=
and.congr_right_iff.mpr $
  assume bf' : is_bounded_linear_map f',
  have f'0 : f' 0 = 0 := bf'.to_is_linear_map.map_zero,
  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from
    assume x' hx',
    have x' = x, 
      from eq_of_sub_eq_zero ((norm_eq_zero _).mp hx'),
    by rw this; simp [f'0],
  begin
    rw has_fderiv_equiv_aux _ _ _ _ bf',
    rw is_littleo_iff h,
    apply iff_of_eq, congr, ext x', 
    apply mul_comm
  end

def has_fderiv_at_within_mono {f : E → F} {f' : E → F} {x : E} {s t : set E} 
    (h : has_fderiv_at_within f f' x t) (hst : s ⊆ t) :
  has_fderiv_at_within f f' x s :=
and.intro h.left (tendsto_nhds_within_mono_left h.right hst)

theorem has_fderiv_at_within.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} 
    {x : E} {s : set E} (h : has_fderiv_at_within f₀ f₀' x s) 
    (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within f₁ f₁' x s :=
by rw [←(funext h₀ : f₀ = f₁), ←(funext h₁ : f₀' = f₁')]; exact h

theorem has_fderiv_id (x : E) (s : set E) : has_fderiv_at_within id id x s :=
and.intro is_bounded_linear_map.id $ 
  (@tendsto_const_nhds _ _ _ 0 _).congr (by simp)

theorem has_fderiv_const (c : F) (x : E) (s : set E) : 
  has_fderiv_at_within (λ x, c) (λ y, 0) x s :=
and.intro is_bounded_linear_map.zero $
  (@tendsto_const_nhds _ _ _ 0 _).congr (by simp)

theorem has_fderiv_smul {f : E → F} {f' : E → F} {x : E} {s : set E} 
    (c : ℝ) (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, c • f x) (λ x, c • f' x) x s :=
and.intro (is_bounded_linear_map.smul c h.left) $
begin
  have h' := tendsto_smul_const c h.right,
  rw smul_zero at h',
  apply h'.congr, intro x, simp,
  rw [smul_smul, mul_comm c, ←smul_smul, smul_add, smul_add c, smul_neg, smul_neg]
end

theorem has_fderiv_add {f g : E → F} {f' g' : E → F} {x : E} {s : set E} 
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x + g x) (λ x, f' x + g' x) x s :=
and.intro (is_bounded_linear_map.add hf.left hg.left) $
begin
  have h' := tendsto_add hf.right hg.right,
  rw add_zero at h',
  apply h'.congr, intro x, simp [smul_add]
end

theorem has_fderiv_neg {f : E → F} {f' : E → F} {x : E} {s : set E} 
    (h : has_fderiv_at_within f f' x s) :
  has_fderiv_at_within (λ x, - f x) (λ x, - f' x) x s :=
(has_fderiv_smul (-1 : ℝ) h).congr (by simp) (by simp)

theorem has_fderiv_sub {f g : E → F} {f' g' : E → F} {x : E} {s : set E} 
    (hf : has_fderiv_at_within f f' x s) (hg : has_fderiv_at_within g g' x s) :
  has_fderiv_at_within (λ x, f x - g x) (λ x, f' x - g' x) x s :=
has_fderiv_add hf (has_fderiv_neg hg)

theorem continuous_of_has_fderiv {f : E → F} {f' : E → F} {x : E} {s : set E} 
    (h : has_fderiv_at_within f f' x s) :
  continuous_at_within f x s :=
have bf : is_bounded_linear_map f' := h.left,
have f'0 : f' 0 = 0 := bf.to_is_linear_map.map_zero,
have h₁ : tendsto (λ x', ∥x' - x∥) (nhds_within x s) (nhds 0),
  from tendsto_iff_norm_tendsto_zero.mp (tendsto_nhds_within_of_tendsto_nhds tendsto_id),
have h₂ : tendsto (λ x', f x' - f x - f' (x' - x)) (nhds_within x s) (nhds 0),
  begin
    have := tendsto_smul h₁ h.right, rw [zero_smul] at this,
    apply this.congr, intro x', dsimp,
    cases classical.em (x = x') with h' h', { simp [h', f'0] },
    have : ∥x' + -x∥ ≠ 0, by rw [ne, norm_eq_zero, add_neg_eq_zero]; apply ne.symm h',
    rw [smul_smul, mul_inv_cancel this, one_smul]  
  end,
have h₃ : tendsto (λ x', f' (x' - x)) (nhds_within x s) (nhds 0),
  begin
    have : tendsto (λ x', x' - x) (nhds x) (nhds 0),
      by rw ←sub_self x; exact tendsto_sub tendsto_id tendsto_const_nhds,
    apply tendsto.comp (tendsto_nhds_within_of_tendsto_nhds this),
    suffices : tendsto f' (nhds 0) (nhds (f' 0)), by rwa f'0 at this,
    exact continuous_iff_continuous_at.mp bf.continuous 0
  end,
have h₄ : tendsto (λ x', f x' - f x) (nhds_within x s) (nhds 0),
  begin 
    have :=  tendsto_add h₂ h₃, rw add_zero at this,
    apply this.congr, intro x', simp
  end,
begin
  have := tendsto_add h₄ (tendsto_const_nhds), rw zero_add at this,
  apply this.congr, intro x', simp
end
