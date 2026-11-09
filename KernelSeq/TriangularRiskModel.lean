import KernelSeq.ExpectationRiskEquivalenceComplete

/-!
# Genuine row-dependent RKHS regression models

Each row carries its own design space, observation probability space, RKHS,
design distribution, kernel, target, noise variance and filter. The structure
contains only the original model and filter assumptions. All spectral,
leverage, risk and scale quantities below are constructed from those data.
In particular, no concentration or risk-comparison estimate is a field.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq
noncomputable section

universe uH uX uΩ

/-- One actual model in a triangular array, with common primitive constants
κ, ρ and A but fully row-dependent spaces, laws, kernel, target and noise. -/
structure TriangularRiskModel (κ ρ A : ℝ) where
  H : Type uH
  X : Type uX
  Ω : Type uΩ
  [measurableX : MeasurableSpace X]
  [measurableΩ : MeasurableSpace Ω]
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℝ H]
  [completeH : CompleteSpace H]
  [secondCountableH : SecondCountableTopology H]
  [rkhs : RKHS ℝ H X ℝ]
  μ : Measure X
  P : Measure Ω
  [probabilityμ : IsProbabilityMeasure μ]
  [probabilityP : IsProbabilityMeasure P]
  kernel_measurable : Measurable (fun p : X × X => rkhsKernel (H := H) p.1 p.2)
  kappa_nonneg : 0 ≤ κ
  diagonal_bound : ∀ x, rkhsKernel (H := H) x x ≤ κ ^ 2
  n : ℕ
  sample_pos : 0 < n
  Z : Fin n → Ω → X × ℝ
  observation_measurable : ∀ j, Measurable (Z j)
  design_law : ∀ j, MeasurePreserving (fun ω => (Z j ω).1) P μ
  independent_pairs : iIndepFun Z P
  f : Lp ℝ 2 μ
  target_support : f ∈ (predictionCovariance (featureEmbedding μ (rkhsFeature (H := H))
    (rkhsFeature_memLp μ kernel_measurable κ kappa_nonneg diagonal_bound))).range.topologicalClosure
  σ : ℝ
  noise_pos : 0 < σ
  noise_mean : ∀ j, P[observationNoise (Z j) (lpRepresentative f) |
    observationDesignSigma (Z j)] =ᵐ[P] (fun _ => 0)
  noise_second : ∀ j, P[(fun ω => observationNoise (Z j) (lpRepresentative f) ω ^ 2) |
    observationDesignSigma (Z j)] =ᵐ[P] (fun _ => σ ^ 2)
  lam : ℝ
  lambda_pos : 0 < lam
  φ : ℝ → ℝ
  spectral_filter : ResidualFilter.SpectralFilter (κ ^ 2) φ
  filter_contract : ResidualFilter.Contract lam (κ ^ 2) ρ A φ

attribute [instance] TriangularRiskModel.measurableX TriangularRiskModel.measurableΩ
  TriangularRiskModel.normedH TriangularRiskModel.innerH TriangularRiskModel.completeH
  TriangularRiskModel.secondCountableH TriangularRiskModel.rkhs
  TriangularRiskModel.probabilityμ TriangularRiskModel.probabilityP

namespace TriangularRiskModel

variable {κ ρ A : ℝ} (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A)

def feature : m.X → m.H := rkhsFeature (H := m.H)

theorem feature_memLp : MemLp m.feature 2 m.μ :=
  rkhsFeature_memLp m.μ m.kernel_measurable κ m.kappa_nonneg m.diagonal_bound

def predictionEmbedding : m.H →L[ℝ] Lp ℝ 2 m.μ :=
  featureEmbedding m.μ m.feature m.feature_memLp

theorem population_bound : ‖populationCovariance m.predictionEmbedding‖ ≤ κ ^ 2 :=
  rkhs_population_covariance_bound m.kernel_measurable κ m.kappa_nonneg m.diagonal_bound

def design (j : Fin m.n) (ω : m.Ω) : m.X := (m.Z j ω).1

theorem empirical_bound (ω : m.Ω) :
    ‖empiricalCovariance (fun j => m.feature (m.design j ω))‖ ≤ κ ^ 2 :=
  rkhs_empirical_covariance_bound κ m.kappa_nonneg m.diagonal_bound m.sample_pos _

def L : ℝ := featureLeverageEssentialSup m.feature m.feature_memLp m.lam
def N : ℝ := featureEffectiveDimension m.feature m.feature_memLp m.lam
def Q : ℝ := featureFilterDimension m.feature m.feature_memLp m.φ
def r : ℝ := featureCovarianceRetention m.feature m.feature_memLp m.lam
def alpha (_m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) : ℝ := residualComparisonOrder ρ
def S : ℝ := featureSequenceSourceEnergy m.feature m.feature_memLp m.lam m.alpha m.f
def v : ℝ := m.L * dimensionLog m.N / (m.n : ℝ)
def gamma : ℝ := originalBiasGamma m.L (m.n : ℝ) m.N
def compatibility : ℝ := m.N / m.Q * Real.sqrt m.v
def sourceBalance : ℝ := (m.n : ℝ) * m.S * m.gamma ^ 2 / m.Q
def expectationH : ℝ := (m.n : ℝ) / (m.lam * m.Q)
def expectationScale : ℝ := m.L / (m.n : ℝ) * Real.log (Real.exp 1 + m.expectationH)
def cutoff : ℝ := actualOriginalBiasCutoff m.feature m.feature_memLp m.lam m.φ
  m.alpha m.f m.L m.n A

def deviation (ω : m.Ω) : ℝ :=
  actualCovarianceDeviation m.feature m.feature_memLp m.lam (fun j => m.design j ω)

def goodEvent : Set m.Ω := {ω | m.deviation ω ≤ 1 / 4}

def conditionalRisk : m.Ω → ℝ :=
  rkhsConditionalPredictionRisk (P := m.P) m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.f m.φ m.lambda_pos m.filter_contract

def expectationRisk : ℝ :=
  rkhsExpectationPredictionRisk (P := m.P) m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.f m.φ m.lambda_pos m.filter_contract

def benchmark : ℝ :=
  sequenceBenchmark m.feature m.feature_memLp m.φ m.f m.σ m.n

def bias : m.Ω → ℝ := fun ω =>
  actualEmpiricalBiasEnergy m.feature m.feature_memLp m.φ m.lambda_pos
    (fun j => m.design j ω) (m.empirical_bound ω) m.filter_contract m.f

def populationBias : ℝ :=
  ‖populationSpectralResidual m.feature m.feature_memLp m.φ m.population_bound m.spectral_filter m.f‖ ^ 2

def varianceEnergy : m.Ω → ℝ := fun ω =>
  actualVarianceEnergy m.feature m.feature_memLp m.φ m.lambda_pos
    (fun j => m.design j ω) (m.empirical_bound ω) m.filter_contract

theorem benchmark_eq : m.benchmark = m.populationBias + m.σ ^ 2 / (m.n : ℝ) * m.Q :=
  sequenceBenchmark_eq_population m.feature m.feature_memLp m.φ m.population_bound
    m.spectral_filter m.target_support m.σ m.n

theorem benchmark_pos (hQ : 0 < m.Q) : 0 < m.benchmark := by
  rw [m.benchmark_eq]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    (mul_pos (div_pos (sq_pos_of_pos m.noise_pos) (Nat.cast_pos.mpr m.sample_pos)) hQ)

theorem conditionalRisk_nonneg : 0 ≤ᵐ[m.P] m.conditionalRisk :=
  rkhsConditionalPredictionRisk_nonneg_ae m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.f m.φ m.lambda_pos m.filter_contract

theorem conditionalRisk_integrable : Integrable m.conditionalRisk m.P :=
  integrable_rkhsConditionalPredictionRisk m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.f m.φ m.lambda_pos m.filter_contract

theorem conditionalRisk_energy : m.conditionalRisk =ᵐ[m.P]
    (fun ω => m.bias ω + m.σ ^ 2 / (m.n : ℝ) * m.varianceEnergy ω) := by
  simpa only [conditionalRisk, bias, varianceEnergy, rkhsConditionalPredictionRisk,
    rkhsVarianceEnergy, feature, feature_memLp, design] using
    (rkhs_conditional_prediction_risk_energy m.kernel_measurable κ m.kappa_nonneg
      m.diagonal_bound m.sample_pos m.Z m.observation_measurable m.design_law m.f m.σ
      m.noise_pos m.independent_pairs m.noise_mean m.noise_second m.φ m.lambda_pos
      m.spectral_filter m.filter_contract).2

/-- This tower step explicitly uses genuine integrability of the original
observed-response loss, derived from the model's actual noise assumptions. -/
theorem expectationRisk_eq_integral : m.expectationRisk = ∫ ω, m.conditionalRisk ω ∂m.P := by
  have hi := (rkhs_conditional_prediction_risk m.kernel_measurable κ m.kappa_nonneg
    m.diagonal_bound m.sample_pos m.Z m.observation_measurable m.design_law m.f m.σ
    m.noise_pos m.independent_pairs m.noise_mean m.noise_second m.φ m.lambda_pos
    m.spectral_filter m.filter_contract).1
  exact rkhsExpectationPredictionRisk_eq_integral_conditional_of_integrable
    m.kernel_measurable κ m.kappa_nonneg m.diagonal_bound m.sample_pos m.Z
    m.observation_measurable m.f m.φ m.lambda_pos m.filter_contract hi

end TriangularRiskModel
end
end KernelSeq
