import KernelSeq.FilterDimension

/-!
# Polynomial envelope scales from the actual filter dimension

The global loss envelope is polynomial in the expectation scale
`n / (lambda * Nq)`. The extra covariance bound needed for this reduction is
derived from the actual filter series and the finite covariance trace.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq

variable {H X : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- The original scalar profile bound and covariance trace give a uniform
bound for `lambda^2 Nq`, including arbitrarily large lambda. -/
theorem lambda_sq_mul_featureFilterDimension_le (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    lam ^ 2 * featureFilterDimension k hk φ ≤
      A ^ 2 * M * featureCovarianceTrace k hk := by
  have hA : 0 ≤ A := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have hpoint (i : FeatureCovarianceIndex k hk) :
      lam ^ 2 * ResidualFilter.shrinkage φ i.1 ^ 2 ≤ A ^ 2 * M * i.1 := by
    have ht := featureCovarianceEigenvalue_mem k hk hM i
    have hφ := (le_div_iff₀ hlam).mp (h.profile_bound hlam ht)
    have hφsq := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hlam.le) hφ 2
    simp only [mul_pow, sq_abs] at hφsq
    have ht2 : i.1 ^ 2 ≤ M * i.1 := by nlinarith [ht.1, ht.2]
    calc
      _ = i.1 ^ 2 * (|φ i.1| ^ 2 * lam ^ 2) := by
        simp only [ResidualFilter.shrinkage, sq_abs]; ring
      _ ≤ i.1 ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left
        (by simpa only [sq_abs] using hφsq) (sq_nonneg _)
      _ ≤ (M * i.1) * A ^ 2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      _ = _ := by ring
  rw [featureFilterDimension, featureCovarianceTrace, ← tsum_mul_left, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hpoint
    ((summable_featureFilterDimension k hk φ hlam hM hf h).mul_left _)
    ((summable_featureCovarianceEigenvalues k hk).mul_left _)

/-- Bounded features make the preceding constant a fixed deterministic one. -/
theorem lambda_sq_mul_featureFilterDimension_le_sq_bound
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) (κ : ℝ)
    (hκ : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ κ ^ 2) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    lam ^ 2 * featureFilterDimension k hk φ ≤ A ^ 2 * κ ^ 4 := by
  calc
    _ ≤ A ^ 2 * κ ^ 2 * featureCovarianceTrace k hk :=
      lambda_sq_mul_featureFilterDimension_le k hk φ hlam hM hf h
    _ ≤ A ^ 2 * κ ^ 2 * κ ^ 2 := mul_le_mul_of_nonneg_left
      (featureCovarianceTrace_le_sq_bound k hk κ hκ) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end KernelSeq
