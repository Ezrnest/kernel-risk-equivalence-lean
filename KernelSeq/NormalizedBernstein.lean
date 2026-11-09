import KernelSeq.InfiniteBernstein
import KernelSeq.BernsteinTailScale
import KernelSeq.ActualVarianceTransfer

/-!
# Intrinsic Bernstein tails for the actual normalized covariance

The actual population inverse square root whitens the feature. Its covariance,
norm, trace and centered empirical average are identified with the manuscript's
`R T R`, retention, effective dimension and normalized deviation. The only
external probability premise remains the visible finite Bernstein leaf on the
finite spectral subspaces of this actual whitened covariance.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace KernelSeq

variable {H X Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace X] [MeasurableSpace Ω] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The actual population-whitened feature, not a normalized covariance certificate. -/
noncomputable def bernsteinFeature (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) : X → H :=
  fun y => featureRegularizedInvSqrt μ k hk lam (k y)

theorem bernsteinFeature_memLp (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    MemLp (bernsteinFeature k hk lam) 2 μ := memLp_normalized_feature k hk lam

/-- The whitened feature covariance is precisely the actual `R T R`. -/
theorem bernsteinFeature_covariance (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    populationCovariance (featureEmbedding μ (bernsteinFeature k hk lam)
      (bernsteinFeature_memLp k hk lam)) =
      featureRegularizedInvSqrt μ k hk lam * populationCovariance (featureEmbedding μ k hk) *
        featureRegularizedInvSqrt μ k hk lam := by
  change populationCovariance (featureEmbedding μ
    (fun y => featureRegularizedInvSqrt μ k hk lam (k y))
    ((featureRegularizedInvSqrt μ k hk lam).comp_memLp' hk)) = _
  rw [← populationCovariance_conjugation,
    (featureRegularizedInvSqrt_isSelfAdjoint k hk lam).adjoint_eq]

theorem bernsteinFeature_covariance_norm (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    ‖populationCovariance (featureEmbedding μ (bernsteinFeature k hk lam)
      (bernsteinFeature_memLp k hk lam))‖ = featureCovarianceRetention k hk lam := by
  rw [bernsteinFeature_covariance, featureCovarianceRetention_eq_norm]

omit [IsProbabilityMeasure μ] in
/-- Exact centered rank-one averaging, with positive sample size explicit. -/
theorem centeredRankOne_average_eq {n : ℕ} (hn : 0 < n)
    (u : X → H) (hu : MemLp u 2 μ) (x : Fin n → X) :
    (n : ℝ)⁻¹ • ∑ i, centeredRankOne u hu (x i) =
      empiricalCovariance (fun i => u (x i)) - populationCovariance (featureEmbedding μ u hu) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [centeredRankOne, Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, empiricalCovariance]
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn0]

/-- The centered whitened average is the actual operator inside `δ_λ`. -/
theorem bernsteinFeature_centered_average {n : ℕ} (hn : 0 < n)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (x : Fin n → X) :
    (n : ℝ)⁻¹ • ∑ i, centeredRankOne (bernsteinFeature k hk lam)
      (bernsteinFeature_memLp k hk lam) (x i) =
      featureRegularizedInvSqrt μ k hk lam *
        (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
          featureRegularizedInvSqrt μ k hk lam := by
  rw [centeredRankOne_average_eq hn, bernsteinFeature_covariance]
  change empiricalCovariance (fun i => featureRegularizedInvSqrt μ k hk lam (k (x i))) - _ = _
  rw [← empiricalCovariance_conjugation,
    (featureRegularizedInvSqrt_isSelfAdjoint k hk lam).adjoint_eq]
  noncomm_ring

/-- Exact normalization of the true deviation by the true centered sum. -/
theorem actualCovarianceDeviation_eq_centeredSum_div {n : ℕ} (hn : 0 < n)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (x : Fin n → X) :
    actualCovarianceDeviation k hk lam x =
      ‖∑ i, centeredRankOne (bernsteinFeature k hk lam)
        (bernsteinFeature_memLp k hk lam) (x i)‖ / (n : ℝ) := by
  change ‖featureRegularizedInvSqrt μ k hk lam *
    (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
      featureRegularizedInvSqrt μ k hk lam‖ = _
  rw [← bernsteinFeature_centered_average hn k hk lam x]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_mul_inv]
  ring

variable [TopologicalSpace.SeparableSpace H]

/-- The actual whitened feature energy is exactly `N₁(λ)`. -/
theorem integral_bernsteinFeature_norm_sq (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    (∫ y, ‖bernsteinFeature k hk lam y‖ ^ 2 ∂μ) = featureEffectiveDimension k hk lam :=
  integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam

/-- The actual covariance trace, in its constructed complete spectral basis,
is `N₁(λ)`; its diagonal summability is an upstream Parseval conclusion. -/
theorem bernsteinFeature_covariance_basisTrace (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    basisTrace (featureCovarianceBasis (bernsteinFeature k hk lam) (bernsteinFeature_memLp k hk lam))
      (populationCovariance (featureEmbedding μ (bernsteinFeature k hk lam)
        (bernsteinFeature_memLp k hk lam))) = featureEffectiveDimension k hk lam := by
  letI := featureCovarianceIndex_countable (bernsteinFeature k hk lam) (bernsteinFeature_memLp k hk lam)
  rw [(populationCovariance_basisTrace _ _ (bernsteinFeature_memLp k hk lam)).2]
  exact integral_bernsteinFeature_norm_sq k hk lam hlam

variable [IsProbabilityMeasure P]

/-- The actual intrinsic normalized-covariance tail, with explicit threshold
and the external finite-dimensional Bernstein premise visible in the statement.
Retention need only be positive at this instance; no uniform lower bound is imposed. -/
theorem normalized_covariance_bernstein_tail
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    (hTropp : FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk lam) (bernsteinFeature_memLp k hk lam)) P)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (hind : iIndepFun x P)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hr : 0 < featureCovarianceRetention k hk lam) (z : ℝ) (hz : 0 ≤ z) :
    P {ω | bernsteinThreshold ((n : ℝ) * L * featureCovarianceRetention k hk lam) (2 * L)
        (dimensionLog (featureEffectiveDimension k hk lam / featureCovarianceRetention k hk lam) + z) /
          (n : ℝ) < actualCovarianceDeviation k hk lam (fun i => x i ω)} ≤
      ENNReal.ofReal (8 * Real.exp (-z)) := by
  let u := bernsteinFeature k hk lam
  let hu := bernsteinFeature_memLp k hk lam
  let r := featureCovarianceRetention k hk lam
  let N := featureEffectiveDimension k hk lam
  let t := bernsteinThreshold ((n : ℝ) * L * r) (2 * L) (dimensionLog (N / r) + z)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcn : ‖populationCovariance (featureEmbedding μ u hu)‖ = r :=
    bernsteinFeature_covariance_norm k hk lam
  have hbound : ∀ᵐ y ∂μ, ‖u y‖ ^ 2 ≤ L := hL
  have hLpos : 0 < L := hr.trans_le (by
    change r ≤ L
    rw [← hcn]
    exact populationCovariance_norm_le_feature_bound u hu hbound)
  have hv : 0 < (n : ℝ) * L * r := mul_pos (mul_pos hnpos hLpos) hr
  have hR : 0 ≤ 2 * L := mul_nonneg (by norm_num) hLpos.le
  have hd : 0 ≤ N / r := div_nonneg (featureEffectiveDimension_nonneg k hk lam hlam) hr.le
  have hs : 1 ≤ dimensionLog (N / r) + z := by linarith [one_le_dimensionLog hd]
  have ht : Real.sqrt (((n : ℝ) * L) * ‖populationCovariance (featureEmbedding μ u hu)‖) +
      (2 * L) / 3 ≤ t := by
    rw [hcn]
    exact bernsteinThreshold_admissible hv.le hR hs
  have htail := infinite_covariance_sum_tail u hu hTropp hn x hlaw hind hbound
    (by rwa [hcn]) t ht
  rw [integral_bernsteinFeature_norm_sq k hk lam hlam, hcn] at htail
  have hsub : {ω | t / (n : ℝ) < actualCovarianceDeviation k hk lam (fun i => x i ω)} ⊆
      {ω | t < ‖∑ i, centeredRankOne u hu (x i ω)‖} := by
    intro ω hω
    change t / (n : ℝ) < actualCovarianceDeviation k hk lam (fun i => x i ω) at hω
    rw [actualCovarianceDeviation_eq_centeredSum_div hn k hk lam] at hω
    exact (div_lt_div_iff_of_pos_right hnpos).mp hω
  exact ((measure_mono hsub).trans htail).trans (ENNReal.ofReal_le_ofReal
    (intrinsicBernstein_expression_le hd hv hR hz))

end KernelSeq
