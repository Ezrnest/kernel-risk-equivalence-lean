import KernelSeq.RealRHSFluctuation
import KernelSeq.CompactCalculus
import KernelSeq.CompactEmbedding

/-!
# The spectral estimator's actual right-hand-side fluctuation

Connects the constructed real inverse square root, the actual sampled RHS,
and the population spectral residual. The finite second-moment and tail bounds
and the `o_P` fluctuation bound are proved for the general
filter assumptions. The leverage rate is an explicit a.e. bound; obtaining it
from the main theorem's effective-dimension scale remains a different step.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Both actual covariance operators have the same spectral upper bound. -/
theorem predictionCovariance_norm_eq_population (S : H →L[ℝ] Lp ℝ 2 μ) :
    ‖predictionCovariance S‖ = ‖populationCovariance S‖ := by
  rw [populationCovariance_norm]
  simpa only [predictionCovariance, ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map,
    pow_two] using S.adjoint.norm_adjoint_comp_self

/-- The actual population solution `φ(T) S* f`, constructed under the existing
filter contract on a spectral interval containing the covariance spectrum. -/
noncomputable def populationSpectralSolution (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ) : H :=
  compactFilterOperator (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) φ hlam hM h
      ((featureEmbedding μ k hk).adjoint f)

/-- The actual spectral residual `ψ(L) f`, with a nontrivial kernel permitted. -/
noncomputable def populationSpectralResidual (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  compactResidualOperator (predictionCovariance (featureEmbedding μ k hk))
    (predictionCovariance_feature_isCompact μ k hk)
    (predictionCovariance_isPositive (featureEmbedding μ k hk)) φ
    ((predictionCovariance_norm_eq_population _).trans_le hM) hf f

/-- The RHS residual identity now has neither spectral-calculus nor
intertwining premises: both are theorems of the actual embedding. -/
theorem populationSpectralSolution_residual (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ) :
    f - featureEmbedding μ k hk (populationSpectralSolution k hk φ hlam hM h f) =
      populationSpectralResidual k hk φ hM hf f :=
  population_residual_filter_identity (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk)
    (predictionCovariance_feature_isCompact μ k hk) hlam hM
    ((predictionCovariance_norm_eq_population _).trans_le hM) φ hf h f

variable [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H]

/-- The finite-sample second-moment bound for the right-hand-side fluctuation
with the real constructed inverse square root and spectral population solution. -/
theorem integral_spectral_normalizedRHS_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, ‖normalizedRHS k hk lam f (populationSpectralSolution k hk φ hlam hM h f)
      (fun i => x i ω)‖ ^ 2 ∂P) ≤ L / (n : ℝ) * ‖populationSpectralResidual k hk φ hM hf f‖ ^ 2 := by
  have hb := integral_normalizedRHS_sq_le hn x hlaw hindep k hk lam f
    (populationSpectralSolution k hk φ hlam hM h f) hL
  rwa [populationSpectralSolution_residual k hk φ hlam hM hf h f] at hb

/-- Explicit Markov bound, stronger than merely naming a stochastic order. -/
theorem measure_spectral_normalizedRHS_ge_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ ‖normalizedRHS k hk lam f (populationSpectralSolution k hk φ hlam hM h f)
      (fun i => x i ω)‖} ≤
        ENNReal.ofReal (L / (n : ℝ) * ‖populationSpectralResidual k hk φ hM hf f‖ ^ 2 / t ^ 2) := by
  have hb := measure_normalizedRHS_ge_le hn x hlaw hindep k hk lam f
    (populationSpectralSolution k hk φ hlam hM h f) hL ht
  rwa [populationSpectralSolution_residual k hk φ hlam hM hf h f] at hb

/-- The spectral `o_P` conclusion at the manuscript's leverage rate. The common
filter constants `M,ρ,A` are outside the index, preserving family uniformity. -/
theorem spectral_normalizedRHS_div_residual_tendstoInMeasure {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hindep : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (f : ι → Lp ℝ 2 μ) (L : ι → ℝ) (hLnonneg : ∀ i, 0 ≤ L i)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖⁻¹ •
      normalizedRHS k hk (lam i) (f i)
        (populationSpectralSolution k hk (φ i) (hlam i) hM (h i) (f i))
        (fun j => x i j ω)) l (fun _ => 0) := by
  have hb := normalizedRHS_div_residual_tendstoInMeasure n hn x hlaw hindep k hk lam f
    (fun i => populationSpectralSolution k hk (φ i) (hlam i) hM (h i) (f i))
    L hLnonneg hL hrate
  have hres (i : ι) : f i - featureEmbedding μ k hk
      (populationSpectralSolution k hk (φ i) (hlam i) hM (h i) (f i)) =
      populationSpectralResidual k hk (φ i) hM (hf i) (f i) :=
    populationSpectralSolution_residual k hk (φ i) (hlam i) hM (hf i) (h i) (f i)
  simpa only [hres] using hb

end KernelSeq
