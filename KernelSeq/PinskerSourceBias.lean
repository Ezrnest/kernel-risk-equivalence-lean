import KernelSeq.SourceQualificationOrder
import KernelSeq.PinskerFilter

/-!
# Pinsker's exact worst bias on actual source balls

When one positive population eigenvalue lies above the regularization scale,
the worst bias is exactly `R² lam^s`, attained by the actual source direction
`L^(s/2) (R e_i)`. This is the finite-regularization identity used before the
spectral-sum and minimax arguments; no such asymptotic or minimax conclusion
is asserted here.
-/

open MeasureTheory Submodule

namespace KernelSeq
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

def featureSourceDirection (k : X→H) (hk : MemLp k 2 μ) (s : ℝ) (hs : 0≤s) (R : ℝ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) : Lp ℝ 2 μ :=
  predictionSourcePower (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs
    (R • (predictionSingularBasis (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ))

theorem featureSourceDirection_mem_sourceBall (k : X→H) (hk : MemLp k 2 μ)
    (s : ℝ) (hs : 0≤s) {R : ℝ} (hR : 0≤R)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    featureSourceDirection k hk s hs R i ∈ featureSourceBall k hk s hs R := by
  refine ⟨R • (predictionSingularBasis (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ), ?_, ?_, rfl⟩
  · exact (PredictionRange (featureEmbedding μ k hk)).smul_mem R (Subtype.prop _)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
    have hn : ‖(predictionSingularBasis (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ)‖ = 1 :=
      (predictionSingularBasis _ _).orthonormal.norm_eq_one i
    rw [hn, mul_one]

omit [IsProbabilityMeasure μ] in
theorem featureSourceBiasWeight_pinsker_eq (k : X→H) (hk : MemLp k 2 μ)
    {lam s : ℝ} (hlam : 0<lam)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hresolved : lam ≤ i.1.1) :
    featureSourceBiasWeight k hk s (ResidualFilter.pinsker lam s) i = lam^s := by
  unfold featureSourceBiasWeight
  rw [ResidualFilter.pinsker_residual hlam, max_eq_left hresolved,
    ← Real.rpow_two, ← Real.rpow_mul (div_pos hlam i.2).le]
  have he : (s/2)*2=s := by ring
  rw [he, ← Real.mul_rpow i.2.le (div_pos hlam i.2).le]
  congr 1
  field_simp [i.2.ne']

theorem featureSourceWorstBias_pinsker_le (k : X→H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M) :
    featureSourceWorstBias k hk s hs R (ResidualFilter.pinsker lam s) ≤ R^2*lam^s := by
  have hq : ∀ t ∈ Set.Ioc (0:ℝ) M,
      t^(s/2)*|ResidualFilter.residual (ResidualFilter.pinsker lam s) t|≤(1:ℝ)*lam^(s/2) := by
    intro t ht
    simpa only [one_mul] using ResidualFilter.pinsker_qualification hlam ht.1.le
      (by positivity : 0≤s/2) le_rfl
  simpa only [one_pow, one_mul] using featureSourceWorstBias_le_of_qualification k hk
    (ResidualFilter.pinsker lam s) hlam hs hR hM (ResidualFilter.pinsker_spectralFilter hlam hs) hq

/-- Exact worst bias, with the actual positive direction exhibited rather
than an assumed attained supremum. The radius may also be zero. -/
theorem featureSourceWorstBias_pinsker_eq (k : X→H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hresolved : lam ≤ i.1.1) :
    featureSourceWorstBias k hk s hs R (ResidualFilter.pinsker lam s) = R^2*lam^s := by
  apply le_antisymm (featureSourceWorstBias_pinsker_le k hk hlam hs hR hM)
  rw [featureSourceWorstBias_eq k hk hs hR hM _ (ResidualFilter.pinsker_spectralFilter hlam hs)]
  have hi := featureSourceBiasWeight_le_spectralSup k hk hs hM
    (ResidualFilter.pinsker lam s) (ResidualFilter.pinsker_spectralFilter hlam hs) i
  rw [featureSourceBiasWeight_pinsker_eq k hk hlam i hresolved] at hi
  exact mul_le_mul_of_nonneg_left hi (sq_nonneg R)

theorem featureSequenceBias_pinsker_attained (k : X→H) (hk : MemLp k 2 μ)
    {lam s : ℝ} (hlam : 0<lam) (hs : 0≤s) (R : ℝ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hresolved : lam ≤ i.1.1) :
    featureSequenceBias k hk (ResidualFilter.pinsker lam s) (featureSourceDirection k hk s hs R i) = R^2*lam^s := by
  rw [featureSourceDirection, featureSequenceBias_source_direction,
    featureSourceBiasWeight_pinsker_eq k hk hlam i hresolved]

theorem populationSpectralResidual_pinsker_attained (k : X→H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (hlam : 0<lam) (hs : 0≤s) (hR : 0≤R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hresolved : lam ≤ i.1.1) :
    ‖populationSpectralResidual k hk (ResidualFilter.pinsker lam s) hM
      (ResidualFilter.pinsker_spectralFilter hlam hs) (featureSourceDirection k hk s hs R i)‖^2 = R^2*lam^s := by
  rw [populationSpectralResidual_norm_sq_eq_sequenceBias k hk _ hM
    (ResidualFilter.pinsker_spectralFilter hlam hs)
    (featureSourceBall_supported k hk s hs R (featureSourceDirection_mem_sourceBall k hk s hs hR i))]
  exact featureSequenceBias_pinsker_attained k hk hlam hs R i hresolved

end
end KernelSeq
