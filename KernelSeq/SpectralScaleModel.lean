import KernelSeq.PolynomialSpectrum
import KernelSeq.SourceBall
import KernelSeq.TriangularRiskModel

/-!
# Primitive deterministic data for the scale-verification propositions

Scale verification does not require observation pairs or a noise law. Each
row here therefore contains only its actual kernel, design law, target,
filter, sample size and regularization, with the original primitive bounds.
The full regression model forgets to these data by a definitional projection.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

universe uH uX uΩ

structure SpectralScaleModel (κ ρ A : ℝ) where
  H : Type uH
  X : Type uX
  [measurableX : MeasurableSpace X]
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℝ H]
  [completeH : CompleteSpace H]
  [secondCountableH : SecondCountableTopology H]
  [rkhs : RKHS ℝ H X ℝ]
  μ : Measure X
  [probabilityμ : IsProbabilityMeasure μ]
  kernel_measurable : Measurable (fun p : X × X => rkhsKernel (H := H) p.1 p.2)
  kappa_nonneg : 0 ≤ κ
  diagonal_bound : ∀ x, rkhsKernel (H := H) x x ≤ κ ^ 2
  n : ℕ
  sample_pos : 0 < n
  f : Lp ℝ 2 μ
  lam : ℝ
  lambda_pos : 0 < lam
  φ : ℝ → ℝ
  spectral_filter : ResidualFilter.SpectralFilter (κ ^ 2) φ
  filter_contract : ResidualFilter.Contract lam (κ ^ 2) ρ A φ

attribute [instance] SpectralScaleModel.measurableX SpectralScaleModel.normedH
  SpectralScaleModel.innerH SpectralScaleModel.completeH SpectralScaleModel.secondCountableH
  SpectralScaleModel.rkhs SpectralScaleModel.probabilityμ

namespace SpectralScaleModel

variable {κ ρ A : ℝ} (m : SpectralScaleModel.{uH, uX} κ ρ A)

def feature : m.X → m.H := rkhsFeature (H := m.H)

theorem feature_memLp : MemLp m.feature 2 m.μ :=
  rkhsFeature_memLp m.μ m.kernel_measurable κ m.kappa_nonneg m.diagonal_bound

theorem population_bound :
    ‖populationCovariance (featureEmbedding m.μ m.feature m.feature_memLp)‖ ≤ κ ^ 2 :=
  rkhs_population_covariance_bound m.kernel_measurable κ m.kappa_nonneg m.diagonal_bound

def L : ℝ := featureLeverageEssentialSup m.feature m.feature_memLp m.lam
def N : ℝ := featureEffectiveDimension m.feature m.feature_memLp m.lam
def Q : ℝ := featureFilterDimension m.feature m.feature_memLp m.φ
def alpha (_m : SpectralScaleModel.{uH, uX} κ ρ A) : ℝ := residualComparisonOrder ρ
def S : ℝ := featureSequenceSourceEnergy m.feature m.feature_memLp m.lam m.alpha m.f
def compatibility : ℝ := m.N / m.Q * Real.sqrt (m.L * dimensionLog m.N / (m.n : ℝ))
def sourceBalance : ℝ := (m.n : ℝ) * m.S * originalBiasGamma m.L (m.n : ℝ) m.N ^ 2 / m.Q
def expectationScale : ℝ := m.L / (m.n : ℝ) * Real.log (Real.exp 1 + (m.n : ℝ) / (m.lam * m.Q))

abbrev SpectrumEnumeration := FeatureSpectrumEnumeration m.feature m.feature_memLp
def eigenvalue (e : m.SpectrumEnumeration) (j : ℕ) : ℝ :=
  enumeratedEigenvalue m.feature m.feature_memLp e j

def SourceBall (s : ℝ) (hs : 0 ≤ s) (R : ℝ) : Set (Lp ℝ 2 m.μ) :=
  featureSourceBall m.feature m.feature_memLp s hs R

theorem L_nonneg : 0 ≤ m.L :=
  featureLeverageEssentialSup_nonneg m.feature m.feature_memLp m.lambda_pos
    (Eventually.of_forall fun y =>
      pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ m.kappa_nonneg m.diagonal_bound y) 2)

theorem N_nonneg : 0 ≤ m.N :=
  featureEffectiveDimension_nonneg m.feature m.feature_memLp m.lam m.lambda_pos

theorem Q_nonneg : 0 ≤ m.Q := featureFilterDimension_nonneg m.feature m.feature_memLp m.φ

theorem S_nonneg : 0 ≤ m.S :=
  featureSequenceSourceEnergy_nonneg m.feature m.feature_memLp m.lambda_pos m.f

theorem L_le_universal : m.L ≤ κ ^ 2 / m.lam :=
  featureLeverageEssentialSup_le_sq_bound_div m.feature m.feature_memLp m.lambda_pos
    (Eventually.of_forall fun y =>
      pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ m.kappa_nonneg m.diagonal_bound y) 2)

theorem sourceEnergy_le {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hsource : m.f ∈ m.SourceBall s hs R) :
    m.S ≤ (1 + κ ^ 2) ^ (s - min s m.alpha) * R ^ 2 * m.lam ^ (min s m.alpha) :=
  featureSequenceSourceEnergy_le_sourceBall m.feature m.feature_memLp hs
    (residualComparisonOrder_pos m.filter_contract.rho_pos).le hR m.lambda_pos m.population_bound hsource

end SpectralScaleModel

namespace TriangularRiskModel

variable {κ ρ A : ℝ}

/-- Forget observations and noise without changing any actual spectral or
source quantity. No scale estimate is a field of either primitive model. -/
def scaleModel (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) :
    SpectralScaleModel.{uH, uX} κ ρ A where
  H := m.H
  X := m.X
  measurableX := m.measurableX
  normedH := m.normedH
  innerH := m.innerH
  completeH := m.completeH
  secondCountableH := m.secondCountableH
  rkhs := m.rkhs
  μ := m.μ
  probabilityμ := m.probabilityμ
  kernel_measurable := m.kernel_measurable
  kappa_nonneg := m.kappa_nonneg
  diagonal_bound := m.diagonal_bound
  n := m.n
  sample_pos := m.sample_pos
  f := m.f
  lam := m.lam
  lambda_pos := m.lambda_pos
  φ := m.φ
  spectral_filter := m.spectral_filter
  filter_contract := m.filter_contract

@[simp] theorem scaleModel_compatibility (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) :
    m.scaleModel.compatibility = m.compatibility := rfl

@[simp] theorem scaleModel_sourceBalance (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) :
    m.scaleModel.sourceBalance = m.sourceBalance := rfl

@[simp] theorem scaleModel_expectationScale (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) :
    m.scaleModel.expectationScale = m.expectationScale := rfl

end TriangularRiskModel
end
end KernelSeq
