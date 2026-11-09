import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The actual diagonal multivariate Gaussian is a product-coordinate law

Equality is proved by characteristic functions, not by an assumption that
matching second moments determine arbitrary distributions.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped ENNReal NNReal RealInnerProductSpace BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem multivariateGaussian_diagonal_eq_map_pi (v : ι → ℝ) (hv : ∀ j, 0 ≤ v j) :
    multivariateGaussian 0 (Matrix.diagonal v) =
      (Measure.pi (fun j => gaussianReal 0 (⟨v j, hv j⟩ : ℝ≥0))).map (toLp 2) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ ι)
  ext t
  rw [charFun_multivariateGaussian (PosSemidef.diagonal hv)]
  simp_rw [charFun_pi, charFun_gaussianReal, ← Complex.exp_sum]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    Matrix.mulVec_diagonal, dotProduct, Complex.ofReal_sum]
  congr 1
  push_cast
  simp only [mul_zero, zero_mul, zero_sub]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change -((t j : ℂ)*((v j : ℂ)*(t j : ℂ))/2) = -((v j : ℂ)*(t j : ℂ)^2/2)
  ring

theorem multivariateGaussian_noise_eq_map_pi (σ : ℝ) :
    multivariateGaussian 0 (σ^2 • (1 : Matrix ι ι ℝ)) =
      (Measure.pi (fun _ : ι => gaussianReal 0 (⟨σ^2, sq_nonneg σ⟩ : ℝ≥0))).map (toLp 2) := by
  have he : σ^2 • (1 : Matrix ι ι ℝ) = diagonal (fun _ : ι => σ^2) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [he]
  exact multivariateGaussian_diagonal_eq_map_pi _ (fun _ => sq_nonneg σ)

end
end KernelSeq
