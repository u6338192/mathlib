import data.complex.basic
import data.complex.exponential
import hotkeys

open complex

example (a : ℂ) : 1 * a = a :=
begin
  exact one_mul a,
end

example : I * I = -1 :=
begin
  apply I_mul_I, --why didn't library_search get this. Gives deterministic timeout
  --solve_by_elim [neg_inj', complex.I_mul_I],
end

lemma auto_not_good_yet (x₁ y₁ : ℝ) : (⟨x₁,y₁⟩ : ℂ).im = y₁ := rfl

example (x₁ y₁ x₂ y₂ : ℝ) (a b : ℂ) (h₁ : a = ⟨x₁,y₁⟩) (h₂ : b = ⟨x₂,y₂⟩) :
  a * b = ⟨x₁*x₂ - y₁*y₂,x₁*y₂ + x₂*y₁⟩ :=
begin
  apply ext,
  {
    rw [h₁,h₂],
    dsimp [(*)],
    refl,
  },
  {
    conv {
      to_rhs,
      rw auto_not_good_yet,
      rw add_comm,
      rw mul_comm,
      rw add_comm,
    },
    rw [h₁,h₂],
    dsimp [(*)],
    refl,
  },
end

open complex

example (x : ℂ) : exp x ≠ 0 :=
begin
  exact exp_ne_zero x
end

example (x : ℂ) : sin x ^ 2 = 1 - cos x ^ 2 :=
begin
  exact sin_square x,
end

example (a b c : ℂ) (h₁ : a = b) : a + c = b + c := congr_fun (congr_arg has_add.add h₁) c

example (a b c : ℂ) (h₁ : a + c = b - c + c) : a + c = b :=
begin
  simp at h₁,
  exact h₁,
end

example (x : ℂ) : sin x ^ 2 + cos x ^ 2 = 1 :=
begin
  have s₁ : sin x ^ 2 = 1 - cos x ^ 2, from sin_square x,
  have s₂ : sin x ^ 2 + cos x ^ 2 = 1 - cos x ^ 2 + cos x ^ 2, from
    congr_fun (congr_arg has_add.add s₁) (cos x ^ 2),
  simp at s₂,
  rw add_comm,
  exact s₂,
end

--try some of the exersices.
