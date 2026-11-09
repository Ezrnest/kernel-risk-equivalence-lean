import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparison of quadratic forms under conjugated operator perturbations

Conjugation gives the relative quadratic-form comparison.
It uses actual bounded linear maps and their Hilbert adjoints. It does not yet
construct square roots/inverse square roots or identify the manuscript's
regularized covariance perturbation with this factorization.
-/

namespace KernelSeq

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Conjugating a norm-bounded operator controls its quadratic form.
Self-adjointness of `D` is not needed for this real scalar estimate. -/
theorem conjugated_perturbation_quadratic_le (R : E →L[ℝ] F) (D : F →L[ℝ] F)
    {δ : ℝ} (hD : ‖D‖ ≤ δ) (x : E) :
    |inner ℝ x ((R.adjoint.comp (D.comp R)) x)| ≤ δ * ‖R x‖ ^ 2 := by
  change |inner ℝ x (R.adjoint (D (R x)))| ≤ _
  rw [R.adjoint_inner_right]
  calc
    |inner ℝ (R x) (D (R x))| ≤ ‖R x‖ * ‖D (R x)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖R x‖ * (‖D‖ * ‖R x‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm (R x)) (norm_nonneg _)
    _ ≤ ‖R x‖ * (δ * ‖R x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) (norm_nonneg _)
    _ = δ * ‖R x‖ ^ 2 := by ring

/-- Quadratic-form version of relative Loewner comparison.
The factorization and population quadratic form are explicit hypotheses. -/
theorem relative_quadratic_form_comparison (A B : E →L[ℝ] E)
    (R : E →L[ℝ] F) (D : F →L[ℝ] F) {δ : ℝ}
    (hD : ‖D‖ ≤ δ) (hgap : B - A = R.adjoint.comp (D.comp R))
    (hpop : ∀ x, inner ℝ x (A x) = ‖R x‖ ^ 2) (x : E) :
    (1 - δ) * inner ℝ x (A x) ≤ inner ℝ x (B x) ∧
      inner ℝ x (B x) ≤ (1 + δ) * inner ℝ x (A x) := by
  have h := conjugated_perturbation_quadratic_le R D hD x
  rw [← hgap, sub_apply, inner_sub_right, ← hpop x] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> nlinarith

/-- The `δ ≤ 1/2` consequence used for regularized covariance operators. -/
theorem relative_quadratic_form_half_comparison (A B : E →L[ℝ] E)
    (R : E →L[ℝ] F) (D : F →L[ℝ] F) {δ : ℝ}
    (hD : ‖D‖ ≤ δ) (hδ : δ ≤ 1 / 2)
    (hgap : B - A = R.adjoint.comp (D.comp R))
    (hpop : ∀ x, inner ℝ x (A x) = ‖R x‖ ^ 2) (x : E) :
    (1 / 2 : ℝ) * inner ℝ x (A x) ≤ inner ℝ x (B x) ∧
      inner ℝ x (B x) ≤ (3 / 2 : ℝ) * inner ℝ x (A x) := by
  have h := relative_quadratic_form_comparison A B R D hD hgap hpop x
  have hnonneg : 0 ≤ inner ℝ x (A x) := by rw [hpop]; exact sq_nonneg _
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hnonneg]

end KernelSeq
