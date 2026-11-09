import KernelSeq.FiniteSourceEllipsoid

/-!
# Norm bounds from the actual source operator

These bounds derive the containing prediction ball and the outside-prior
target envelope from the original operator power. No target norm bound is
added to the source assumption.
-/

namespace KernelSeq
open MeasureTheory
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem predictionSourcePower_norm_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) :
    ‖predictionSourcePower S hc s hs‖ ≤ ‖S.comp S.adjoint‖^(s/2) :=
  compactSpectralMultiplier_norm_le _ _ _ _ _ _ _

theorem predictionSourcePower_apply_norm_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {M : ℝ} (hM : ‖S.comp S.adjoint‖ ≤ M) (g : E) :
    ‖predictionSourcePower S hc s hs g‖ ≤ (1+M)^(s/2)*‖g‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  apply ((predictionSourcePower S hc s hs).le_opNorm g).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (predictionSourcePower_norm_le S hc s hs).trans
    (Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by positivity))

theorem predictionSourceBall_norm_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {M R : ℝ} (hM : ‖S.comp S.adjoint‖ ≤ M) {f : E}
    (hf : f ∈ predictionSourceBall S hc s hs R) : ‖f‖ ≤ (1+M)^(s/2)*R := by
  obtain ⟨g, _, hgn, rfl⟩ := hf
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  exact (predictionSourcePower_apply_norm_le S hc s hs hM g).trans
    (mul_le_mul_of_nonneg_left hgn (Real.rpow_nonneg (by linarith) _))

section Feature
variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [Fintype ι]

theorem feature_prediction_covariance_norm_le (k : X → H) (hk : MemLp k 2 μ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) :
    ‖predictionCovariance (featureEmbedding μ k hk)‖ ≤ κ^2 := by
  change ‖(featureEmbedding μ k hk).comp (featureEmbedding μ k hk).adjoint‖ ≤ _
  rw [show ‖(featureEmbedding μ k hk).comp (featureEmbedding μ k hk).adjoint‖ =
      ‖featureEmbedding μ k hk‖^2 by
    simpa only [pow_two, ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] using
      (featureEmbedding μ k hk).adjoint.norm_adjoint_comp_self]
  exact pow_le_pow_left₀ (norm_nonneg _) (featureEmbedding_norm_le μ k hk κ hκ hbound) 2

theorem featureSourceBall_norm_le (k : X → H) (hk : MemLp k 2 μ)
    {κ s R : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) (hs : 0 ≤ s)
    {f : Lp ℝ 2 μ} (hf : f ∈ featureSourceBall k hk s hs R) :
    ‖f‖ ≤ (1+κ^2)^(s/2)*R :=
  predictionSourceBall_norm_le _ _ _ _ (feature_prediction_covariance_norm_le k hk hκ hbound) hf

theorem finitePrediction_norm_sq_le_sourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {κ s : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) (hs : 0 ≤ s)
    (θ : EuclideanSpace ℝ ι) :
    ‖FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ‖^2 ≤
      (1+κ^2)^s * finiteSourceEnergy k hk jmap s θ := by
  have hn := predictionSourcePower_apply_norm_le (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) s hs
    (feature_prediction_covariance_norm_le k hk hκ hbound)
    (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap)
      (finiteSourceCoordinates k hk jmap s θ))
  rw [finiteSourceCoordinates_power] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, FinitePredictionBayes.synthesis_norm_sq
    (finitePredictionFunction_orthonormal k hk jmap hj) (finiteSourceCoordinates k hk jmap s θ),
      finiteSourceCoordinates_norm_sq] at hsq
  have hp : ((1+κ^2)^(s/2))^2 = (1+κ^2)^s := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 1+κ^2)]
    congr 1
    ring
  rwa [hp] at hsq

end Feature
end
end KernelSeq
