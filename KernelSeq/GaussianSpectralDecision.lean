import KernelSeq.GaussianRegressionExperiment
import KernelSeq.SpectralScaleModel
import KernelSeq.EmpiricalMeasurability

/-!
# The actual spectral estimator is a measurable regression decision

This constructs a rule on observed design/response data. Its extended-real
regression risk is identified with the genuine integrable expected risk in
the main equivalence theorem. No finite-risk or measurability certificate is
assumed for this estimator.
-/

namespace KernelSeq
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

universe uH uX
variable {κ ρ A : ℝ} (b : SpectralScaleModel.{uH,uX} κ ρ A)

local instance spectralDecisionLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 b.μ) := borel _
local instance spectralDecisionLpBorelSpace : BorelSpace (Lp ℝ 2 b.μ) := ⟨rfl⟩

def gaussianSpectralDecision : (Fin b.n → b.X) × EuclideanSpace ℝ (Fin b.n) → Lp ℝ 2 b.μ :=
  fun z => rkhsEmpiricalPrediction b.kernel_measurable κ b.kappa_nonneg b.diagonal_bound
    b.sample_pos z.1 (fun j => z.2 j) b.φ b.lambda_pos b.filter_contract

theorem measurable_gaussianSpectralDecision : Measurable (gaussianSpectralDecision b) := by
  let Z : Fin b.n → ((Fin b.n → b.X) × EuclideanSpace ℝ (Fin b.n)) → b.X × ℝ :=
    fun j z => (z.1 j, z.2 j)
  have hZ (j : Fin b.n) : Measurable (Z j) := by dsimp [Z]; fun_prop
  have hs := observation_empiricalSpectralEstimator_stronglyMeasurable b.sample_pos Z hZ
    b.feature (rkhsFeature_stronglyMeasurable b.kernel_measurable) κ
    (fun x => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ b.kappa_nonneg b.diagonal_bound x) 2)
    b.φ b.lambda_pos b.spectral_filter b.filter_contract
  exact ((rkhsEmbedding b.μ b.kernel_measurable κ b.kappa_nonneg b.diagonal_bound).continuous.comp_stronglyMeasurable hs).measurable

/-- Equality uses the actual observed-response integrability theorem,
including Gaussian noise and arbitrary supported L2 targets. -/
theorem gaussianSpectralDecision_risk_eq_expectationRisk
    {σ : ℝ} (hσ : 0 < σ)
    (hsupport : b.f ∈ (predictionCovariance (featureEmbedding b.μ b.feature b.feature_memLp)).range.topologicalClosure) :
    gaussianRegressionRisk b.μ σ (gaussianSpectralDecision b) b.f =
      ENNReal.ofReal (CanonicalGaussianRegression.riskModel b.μ b.kernel_measurable b.kappa_nonneg
        b.diagonal_bound b.n b.sample_pos b.f hsupport σ hσ b.lam b.lambda_pos b.φ
        b.spectral_filter b.filter_contract).expectationRisk := by
  let m := CanonicalGaussianRegression.riskModel b.μ b.kernel_measurable b.kappa_nonneg
    b.diagonal_bound b.n b.sample_pos b.f hsupport σ hσ b.lam b.lambda_pos b.φ
    b.spectral_filter b.filter_contract
  have hi := (rkhs_conditional_prediction_risk m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.observation_measurable m.design_law m.f m.σ
    m.noise_pos m.independent_pairs m.noise_mean m.noise_second m.φ m.lambda_pos
    m.spectral_filter m.filter_contract).1
  rw [gaussianRegressionRisk_eq_raw_sample b.μ _ (measurable_gaussianSpectralDecision b)]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)).symm

end
end KernelSeq
