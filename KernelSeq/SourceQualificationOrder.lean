import KernelSeq.SourceQualification

/-!
# Full scalar qualification transfers to actual source-ball risk

The scalar qualification order may exceed the residual order chosen for the
Lipschitz contract. This distinction is needed for Pinsker, gradient flow,
gradient descent and smooth cutoffs. The premise here is precisely the usual
scalar filter qualification, not a source-ball bias or risk certificate.
-/

open MeasureTheory Submodule

namespace KernelSeq
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- Qualification at the source order bounds every actual source-weighted
spectral coordinate, without assuming a DOI or residual Lipschitz estimate. -/
theorem featureSourceBiasWeight_le_of_qualification (k : X→H) (hk : MemLp k 2 μ)
    (φ : ℝ→ℝ) {lam M s F : ℝ} (hlam : 0<lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hqual : ∀ t ∈ Set.Ioc (0:ℝ) M, t^(s/2)*|ResidualFilter.residual φ t|≤F*lam^(s/2))
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    featureSourceBiasWeight k hk s φ i ≤ F^2*lam^s := by
  have ht := featureCovarianceEigenvalue_mem k hk hM i.1
  have hh := hqual i.1.1 ⟨i.2, ht.2⟩
  have hs := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg ht.1 _) (abs_nonneg _)) hh 2
  have hpow (t : ℝ) (ht : 0≤t) : (t^(s/2))^2=t^s := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht]
    congr 1
    ring
  simpa only [featureSourceBiasWeight, mul_pow, sq_abs, hpow _ ht.1, hpow _ hlam.le] using hs

theorem featureSourceBiasSpectralSup_le_of_qualification (k : X→H) (hk : MemLp k 2 μ)
    (φ : ℝ→ℝ) {lam M s F : ℝ} (hlam : 0<lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hqual : ∀ t ∈ Set.Ioc (0:ℝ) M, t^(s/2)*|ResidualFilter.residual φ t|≤F*lam^(s/2)) :
    featureSourceBiasSpectralSup k hk s φ ≤ F^2*lam^s := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro y (rfl | ⟨i, rfl⟩)
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hlam.le _)
  · exact featureSourceBiasWeight_le_of_qualification k hk φ hlam hM hqual i

/-- The actual source-ball bias upper bound using the full qualification
order, even when the filter contract uses a smaller order. -/
theorem featureSourceWorstBias_le_of_qualification (k : X→H) (hk : MemLp k 2 μ)
    (φ : ℝ→ℝ) {lam M s R F : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (hqual : ∀ t ∈ Set.Ioc (0:ℝ) M, t^(s/2)*|ResidualFilter.residual φ t|≤F*lam^(s/2)) :
    featureSourceWorstBias k hk s hs R φ ≤ F^2*R^2*lam^s := by
  rw [featureSourceWorstBias_eq k hk hs hR hM φ hf]
  exact (mul_le_mul_of_nonneg_left
    (featureSourceBiasSpectralSup_le_of_qualification k hk φ hlam hM hqual) (sq_nonneg R)).trans_eq (by ring)

theorem featureSequenceBias_le_sourceBall_of_qualification (k : X→H) (hk : MemLp k 2 μ)
    (φ : ℝ→ℝ) {lam M s R F : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (hqual : ∀ t ∈ Set.Ioc (0:ℝ) M, t^(s/2)*|ResidualFilter.residual φ t|≤F*lam^(s/2))
    {f : Lp ℝ 2 μ} (hsource : f∈featureSourceBall k hk s hs R) :
    featureSequenceBias k hk φ f ≤ F^2*R^2*lam^s := by
  exact (featureSequenceBias_le_sourceBall_spectralSup k hk hs hR hM φ hf hsource).trans
    ((mul_le_mul_of_nonneg_left
      (featureSourceBiasSpectralSup_le_of_qualification k hk φ hlam hM hqual) (sq_nonneg R)).trans_eq (by ring))

theorem sequenceBenchmark_le_sourceBall_of_qualification (k : X→H) (hk : MemLp k 2 μ)
    (φ : ℝ→ℝ) {lam M s R F : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ)
    (hqual : ∀ t ∈ Set.Ioc (0:ℝ) M, t^(s/2)*|ResidualFilter.residual φ t|≤F*lam^(s/2))
    {f : Lp ℝ 2 μ} (hsource : f∈featureSourceBall k hk s hs R) (σ : ℝ) (n : ℕ) :
    sequenceBenchmark k hk φ f σ n ≤ F^2*R^2*lam^s + σ^2/(n:ℝ)*featureFilterDimension k hk φ := by
  have hsupport := featureSourceBall_supported k hk s hs R hsource
  rw [sequenceBenchmark_eq_population k hk φ hM hf hsupport σ n,
    populationSpectralResidual_norm_sq_eq_sequenceBias k hk φ hM hf hsupport]
  exact add_le_add (featureSequenceBias_le_sourceBall_of_qualification k hk φ hlam hs hR hM hf hqual hsource) le_rfl

end
end KernelSeq
