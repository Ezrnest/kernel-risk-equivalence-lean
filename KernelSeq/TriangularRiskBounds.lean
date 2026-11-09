import KernelSeq.TriangularRiskFacts
import KernelSeq.UniformGoodBias
import KernelSeq.UniformGoodVariance
import KernelSeq.UniformBadRisk

/-!
# Actual finite-row risk bounds for triangular arrays

Every integral uses its row's own probability space and actual RKHS
conditional risk. The common constants depend only on the common primitive
filter/kernel constants and the positive noise lower bound. All covariance,
source, bias and variance estimates are supplied by the actual model.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq.TriangularRiskModel
noncomputable section

universe uH uX uΩ
variable {κ ρ A : ℝ} (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A)

def goodRiskIntegral : ℝ :=
  ∫ ω in m.goodEvent, |m.conditionalRisk ω - m.benchmark| / m.benchmark ∂m.P

def badRiskIntegral : ℝ :=
  (∫ ω in m.goodEventᶜ, m.conditionalRisk ω ∂m.P) / m.benchmark

def normalizedL1 : ℝ :=
  (∫ ω, |m.conditionalRisk ω - m.benchmark| ∂m.P) / m.benchmark

def goodBiasIntegral : ℝ :=
  ∫ ω in m.goodEvent, |m.bias ω - m.populationBias| / m.benchmark ∂m.P

def goodVarianceIntegral : ℝ :=
  ∫ ω in m.goodEvent, |m.varianceEnergy ω - m.Q| / m.Q ∂m.P

def biasErrorScale : ℝ :=
  uniformBiasErrorRate (m.L / (m.n : ℝ) + m.cutoff ^ 2 + m.v / m.cutoff ^ 2)
    (m.sourceBalance / m.cutoff ^ 2)

theorem goodRiskIntegral_nonneg (hQ : 0 < m.Q) : 0 ≤ m.goodRiskIntegral :=
  integral_nonneg fun _ => div_nonneg (abs_nonneg _) (m.benchmark_pos hQ).le

theorem badRiskIntegral_nonneg (hQ : 0 < m.Q) : 0 ≤ m.badRiskIntegral :=
  div_nonneg (integral_nonneg_of_ae (ae_restrict_of_ae m.conditionalRisk_nonneg))
    (m.benchmark_pos hQ).le

theorem normalizedL1_nonneg (hQ : 0 < m.Q) : 0 ≤ m.normalizedL1 :=
  div_nonneg (integral_nonneg fun _ => abs_nonneg _) (m.benchmark_pos hQ).le

/-- The row's bias estimate uses the exact source exponent and actual
fourth-root cutoff. No cutoff, moment or interaction certificate is assumed. -/
theorem goodBiasIntegral_bound {s0 : ℝ} (hs0 : 0 < s0) (hσlower : s0 ≤ m.σ)
    (hQ : 0 < m.Q)
    (hlin : Real.sqrt m.v * intrinsicDimensionLog m.N m.r / dimensionLog m.N ≤ 1) :
    m.goodBiasIntegral ≤
      uniformBiasRiskConstant (residualComparisonOrder ρ) ρ A s0 * m.biasErrorScale := by
  have hb := setIntegral_actual_good_bias_uniform_row
    (featureCovarianceBasis m.feature m.feature_memLp) m.sample_pos m.design
    m.design_law m.design_independent m.feature m.feature_memLp m.feature_stronglyMeasurable
    κ m.kappa_nonneg m.feature_bound m.population_bound m.empirical_bound m.φ m.lambda_pos
    m.spectral_filter m.filter_contract m.f m.target_support m.σ s0 hs0 hσlower hQ m.leverage_ae hlin
  rw [goodBiasIntegral, m.benchmark_eq]
  simpa only [biasErrorScale, bias, populationBias,
    goodEvent, deviation, L, N, Q, r, v, sourceBalance, S, gamma, cutoff, alpha,
    actualOriginalBiasCutoff, uniformBiasSourceExponent, residualComparisonOrder] using hb

/-- Actual variance comparison with common constants, under the finite
smallness tests that follow eventually from original compatibility. -/
theorem goodVarianceIntegral_bound (hQ : 0 < m.Q)
    (hlin : Real.sqrt m.v * intrinsicDimensionLog m.N m.r / dimensionLog m.N ≤ 1)
    (hcompatSmall : A ^ 4 * m.compatibility ^ 2 ≤ 1) :
    m.goodVarianceIntegral ≤ uniformVarianceRiskConstant ρ A *
      (m.compatibility + m.compatibility ^ 2) := by
  have hv := setIntegral_actual_good_variance_uniform_row
    (featureCovarianceBasis m.feature m.feature_memLp) m.sample_pos m.design
    m.design_law m.design_independent m.feature m.feature_memLp m.feature_stronglyMeasurable
    m.φ m.lambda_pos m.population_bound m.empirical_bound m.spectral_filter m.filter_contract
    hQ m.leverage_ae hlin hcompatSmall
  exact hv

/-- Genuine risk assembly uses the row's a.e. conditional-energy identity;
the conditional variance integrability is derived internally. -/
theorem goodRiskIntegral_le_bias_variance (hQ : 0 < m.Q) :
    m.goodRiskIntegral ≤ m.goodBiasIntegral + m.goodVarianceIntegral := by
  have hb := setIntegral_good_risk_relative_le_bias_variance
    m.conditionalRisk m.bias m.varianceEnergy m.populationBias (m.σ ^ 2 / (m.n : ℝ))
    m.Q m.goodEvent (sq_nonneg _)
    (div_pos (sq_pos_of_pos m.noise_pos) (Nat.cast_pos.mpr m.sample_pos)) hQ
    m.conditionalRisk_integrable m.bias_integrable m.conditionalRisk_energy
  simpa only [goodRiskIntegral, goodBiasIntegral, goodVarianceIntegral, m.benchmark_eq] using hb

/-- A common finite-row good-risk bound with the true sequence benchmark. -/
theorem goodRiskIntegral_bound {s0 : ℝ} (hs0 : 0 < s0) (hσlower : s0 ≤ m.σ)
    (hQ : 0 < m.Q)
    (hlin : Real.sqrt m.v * intrinsicDimensionLog m.N m.r / dimensionLog m.N ≤ 1)
    (hcompatSmall : A ^ 4 * m.compatibility ^ 2 ≤ 1) :
    m.goodRiskIntegral ≤
      uniformBiasRiskConstant (residualComparisonOrder ρ) ρ A s0 * m.biasErrorScale +
      uniformVarianceRiskConstant ρ A * (m.compatibility + m.compatibility ^ 2) :=
  (m.goodRiskIntegral_le_bias_variance hQ).trans (add_le_add
    (m.goodBiasIntegral_bound hs0 hσlower hQ hlin)
    (m.goodVarianceIntegral_bound hQ hlin hcompatSmall))

/-- The original source balance controls the target norm internally. The
noise level may grow, and both model spaces and laws may vary with the row. -/
theorem badRiskIntegral_bound {s0 : ℝ} (hs0 : 0 < s0) (hσlower : s0 ≤ m.σ)
    (hQ : 0 < m.Q) (hQn : m.Q ≤ (m.n : ℝ))
    (hdelete : (m.L + 1) / (m.n : ℝ) ≤ 1 / 8)
    (hintrinsic : m.L * intrinsicDimensionLog m.N m.r / (m.n : ℝ) ≤ 1 / 65536) :
    m.badRiskIntegral ≤ uniformBadRiskConstant A κ s0 * (1 + m.expectationH) ^ 3 *
      (1 + m.sourceBalance) * Real.exp (-(1 / 65536 : ℝ) * (m.n : ℝ) / m.L) := by
  have hb := rkhs_uniform_bad_risk_quantitative m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.observation_measurable m.design_law m.independent_pairs
    m.f m.σ s0 hs0 hσlower m.noise_mean m.noise_second m.φ m.lambda_pos
    m.spectral_filter m.filter_contract m.alpha_pos.le m.alpha_le_one
    m.target_support hQ hQn hdelete hintrinsic
  have he : -(m.n : ℝ) / (65536 * m.L) = -(1 / 65536 : ℝ) * (m.n : ℝ) / m.L := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hb' : m.badRiskIntegral ≤ uniformBadRiskConstant A κ s0 * (1 + m.expectationH) ^ 3 *
      (1 + m.sourceBalance) * Real.exp (-(m.n : ℝ) / (65536 * m.L)) := by
    simpa only [badRiskIntegral, goodEvent, deviation, Set.compl_setOf, not_le, conditionalRisk,
      benchmark, expectationH, sourceBalance, S, gamma, L, N, Q, r, feature, feature_memLp,
      design] using hb
  rwa [he] at hb'

end
end KernelSeq.TriangularRiskModel
