import KernelFoundations.SourceBall
import KernelSeq.UniformSource

/-!
# Source-energy bound for the sequence benchmark
-/

open MeasureTheory Submodule

namespace KernelSeq

export KernelFoundations (
  predictionSourcePower predictionSourceBall zero_mem_predictionSourceBall
  predictionSourceBall_zero predictionSourcePower_mem_predictionRange
  predictionSourceBall_mem_predictionRange predictionSourcePower_coefficient
  predictionSourcePower_coefficient_sq source_regularized_weight_bound
  featureSourceBall featureSourceBall_supported
)
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The original source-energy bound on the genuine source ball. The
constant is uniform over targets, dimensions, spaces and regularization. -/
theorem featureSequenceSourceEnergy_le_sourceBall (k : X → H) (hk : MemLp k 2 μ)
    {s α R lam M : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    {f : Lp ℝ 2 μ} (hf : f ∈ featureSourceBall k hk s hs R) :
    featureSequenceSourceEnergy k hk lam α f ≤
      (1+M)^(s-min s α) * R^2 * lam^(min s α) := by
  obtain ⟨g, hg, hgR, rfl⟩ := hf
  have hfSupport := predictionSourcePower_mem_predictionRange (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) s hs hg
  have hsum := summable_featureSequenceSourceEnergy k hk hlam hα hfSupport
  have hcoeff := featureSequenceCoefficient_sq_summable k hk hg
  have hpoint (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
      (lam/(i.1.1+lam))^α * featureSequenceCoefficient k hk
          (predictionSourcePower (featureEmbedding μ k hk)
            (populationCovariance_feature_isCompact μ k hk) s hs g) i^2 ≤
        ((1+M)^(s-min s α) * lam^(min s α)) * featureSequenceCoefficient k hk g i^2 := by
    have he : featureSequenceCoefficient k hk
        (predictionSourcePower (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) s hs g) i^2 =
        i.1.1^s * featureSequenceCoefficient k hk g i^2 :=
      predictionSourcePower_coefficient_sq (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) s hs g i
    rw [he]
    have hb := source_regularized_weight_bound hlam ((norm_nonneg _).trans hM)
      (featureCovarianceEigenvalue_mem k hk hM i.1) hs hα
    calc
      _ = (i.1.1^s * (lam/(i.1.1+lam))^α) * featureSequenceCoefficient k hk g i^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg (featureSequenceCoefficient k hk g i))
  have hb := Summable.tsum_le_tsum hpoint hsum (hcoeff.mul_left _)
  have hparseval : (∑' i, featureSequenceCoefficient k hk g i^2) = ‖g‖^2 :=
    (predictionSingularBasis_parseval (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) hg).symm
  rw [tsum_mul_left, hparseval] at hb
  refine hb.trans ?_
  have hsquare : ‖g‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hgR
  have hconstant : 0 ≤ (1+M)^(s-min s α) * lam^(min s α) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [(norm_nonneg _).trans hM]) _)
      (Real.rpow_nonneg hlam.le _)
  have hm := mul_le_mul_of_nonneg_left hsquare hconstant
  convert hm using 1; ring

end
end KernelSeq
