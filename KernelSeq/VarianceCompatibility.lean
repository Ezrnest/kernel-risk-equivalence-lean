import KernelSeq.ActualVarianceAsymptotics
import KernelSeq.NormalizedBernstein
import KernelSeq.ConcentrationAsymptotics

/-!
# Actual variance convergence at the original compatible scale

This connects the original variance-compatibility assumption to all stochastic
inputs of the actual variance transfer. The sole extra mathematical premise is
the explicitly displayed external finite-dimensional Bernstein leaf. No
covariance convergence rate, HS scale, trace bound, or variance conclusion is
an assumption of the final theorem below.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace KernelSeq

variable {ι Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {P : Measure Ω} {μ : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
  {l : Filter ι}

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
/-- The variance energy in the comparison is exactly the finite-sample
prediction-column energy of the actual empirical filter. -/
theorem actualVarianceEnergy_eq_prediction_column_energy
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    {n : ℕ} (x : Fin n → X) (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    actualVarianceEnergy k hk φ hlam x hMX h = (n : ℝ)⁻¹ *
      ∑ i, ‖featureEmbedding μ k hk
        (compactFilterOperator (empiricalCovariance (fun j => k (x j)))
          (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
            (k (x i)))‖ ^ 2 := by
  have heq : hsLeftComposition (featureEmbedding μ k hk)
      (empiricalFilteredRootColumns (fun i => k (x i)) φ hlam hMX h) =
      empiricalVarianceColumns (fun i => k (x i))
        ((featureEmbedding μ k hk).comp
          (compactFilterOperator (empiricalCovariance (fun j => k (x j)))
            (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h))
        (empiricalCovarianceBasis (fun i => k (x i))) := by
    ext j
    rfl
  change ‖hsLeftComposition (featureEmbedding μ k hk)
    (empiricalFilteredRootColumns (fun i => k (x i)) φ hlam hMX h)‖ ^ 2 = _
  rw [heq, empiricalVarianceColumns_norm_sq]
  rfl

/-- Multiplying both variance energies by their genuine common positive noise
scale leaves the relative error exactly unchanged, including zero `Q`. -/
theorem positive_scaled_variance_relative_error (a Q c : ℝ) (hc : 0 < c) :
    |c * a - c * Q| / (c * Q) = |a - Q| / Q := by
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact mul_div_mul_left _ _ hc.ne'

/-- Lipschitz variance comparison for the feature and sample model,
conditional only on the named external finite-dimensional Bernstein theorem.
The original compatibility condition supplies every error scale. -/
theorem actual_variance_relative_of_compatibility
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : ι → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) *
        Real.sqrt (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hTropp : ∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i))
        (bernsteinFeature_memLp k hk (lam i))) P) :
    TendstoInMeasure P (fun i ω =>
      |actualVarianceEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) -
        featureFilterDimension k hk (φ i)| / featureFilterDimension k hk (φ i)) l (fun _ => 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let r := fun i => featureCovarianceRetention k hk (lam i)
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  have hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < (n i : ℝ) ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hQ] with i hQi
    refine ⟨feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i),
      Nat.cast_pos.mpr (hn i), featureEffectiveDimension_nonneg k hk (lam i) (hlam i), hQi,
      featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
      featureCovarianceRetention_le_one k hk (lam i) (hlam i),
      featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩
  have hδ := variance_compatibility_covariance_limits_of_threshold_tails P δ L
    (fun i => (n i : ℝ)) N Q r A hgood hcompat (by
      intro z hz
      filter_upwards [hQ] with i hQi
      have hr := featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i)
        (hlam i) hM (hf i) (h i) hQi
      have ht := normalized_covariance_bernstein_tail k hk (lam i) (hlam i) (hTropp i)
        (hn i) (x i) (hlaw i) (hind i) (hL i) hr z hz
      simpa only [normalizedIntrinsicThreshold, intrinsicDimensionLog, dimensionLog,
        δ, N, r, actualCovarianceDeviation, covarianceRelativeDeviation, abs_norm] using ht)
  exact actual_variance_relative_tendstoInMeasure n hn x hlaw (fun i _ _ hij => (hind i).indepFun hij)
    k hk lam hlam hM hMX φ hf h L hL hQ hδ.1 hδ.2
    (variance_compatibility_hs_moment_scale_limit L (fun i => (n i : ℝ)) N Q r A hgood hcompat)

end KernelSeq
