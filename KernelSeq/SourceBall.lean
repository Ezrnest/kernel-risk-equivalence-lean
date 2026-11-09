import KernelSeq.UniformSource

/-!
# Actual source balls and their regularized source energy

The source ball is the image of the radius-R ball in the closed prediction
range under the genuine bounded operator `(S S*)^(s/2)`. Its coordinates
belong to the actual positive singular system, including multiplicities.
Neither the prediction space nor `L²(μ)` is assumed separable.
-/

open MeasureTheory Submodule

namespace KernelSeq
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual positive fractional power of the prediction covariance. -/
def predictionSourcePower (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (s : ℝ) (hs : 0 ≤ s) : E →L[ℝ] E :=
  compactSpectralMultiplier (S.comp S.adjoint)
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) (fun t => t ^ (s / 2))
    (‖S.comp S.adjoint‖ ^ (s / 2)) (Real.rpow_nonneg (norm_nonneg _) _)
    (fun t ht => by
      rw [abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
      exact Real.rpow_le_rpow ht.1 ht.2 (by positivity))

/-- The prediction source ball uses source vectors supported in the closed
prediction range. -/
def predictionSourceBall (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (s : ℝ) (hs : 0 ≤ s) (R : ℝ) : Set E :=
  {f | ∃ h ∈ PredictionRange S, ‖h‖ ≤ R ∧ predictionSourcePower S hc s hs h = f}

theorem zero_mem_predictionSourceBall (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) {R : ℝ} (hR : 0 ≤ R) :
    (0 : E) ∈ predictionSourceBall S hc s hs R :=
  ⟨0, (PredictionRange S).zero_mem, by simpa only [norm_zero] using hR, map_zero _⟩

theorem predictionSourceBall_zero (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) :
    predictionSourceBall S hc s hs 0 = {0} := by
  ext f
  constructor
  · rintro ⟨g, _, hg, rfl⟩
    have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm hg (norm_nonneg g))
    simp only [hg0, map_zero, Set.mem_singleton_iff]
  · rintro rfl
    exact zero_mem_predictionSourceBall S hc s hs le_rfl

theorem predictionSourcePower_mem_predictionRange (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {h : E} (hh : h ∈ PredictionRange S) :
    predictionSourcePower S hc s hs h ∈ PredictionRange S :=
  compactSpectralMultiplier_mem_predictionRange S
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc) _ _ _ _ hh

theorem predictionSourceBall_mem_predictionRange (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) (R : ℝ)
    {f : E} (hf : f ∈ predictionSourceBall S hc s hs R) : f ∈ PredictionRange S := by
  obtain ⟨h, hh, _, rfl⟩ := hf
  exact predictionSourcePower_mem_predictionRange S hc s hs hh

theorem predictionSourcePower_coefficient (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    (h : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hc i : E) (predictionSourcePower S hc s hs h) =
      i.1.1 ^ (s / 2) * inner ℝ (predictionSingularBasis S hc i : E) h :=
  predictionSingularBasis_multiplier_coefficient S hc
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc) _ _ _ _ h i

theorem predictionSourcePower_coefficient_sq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    (h : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hc i : E) (predictionSourcePower S hc s hs h) ^ 2 =
      i.1.1 ^ s * inner ℝ (predictionSingularBasis S hc i : E) h ^ 2 := by
  rw [predictionSourcePower_coefficient, mul_pow]
  congr 1
  rw [← Real.rpow_two, ← Real.rpow_mul i.2.le]
  congr 1
  ring

/-- The scalar source estimate, with a constant depending only on the
spectral upper bound and source exponents, valid also at zero. -/
theorem source_regularized_weight_bound {lam M t s α : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hs : 0 ≤ s) (hα : 0 ≤ α) :
    t ^ s * (lam / (t + lam)) ^ α ≤
      (1 + M) ^ (s - min s α) * lam ^ (min s α) := by
  let r := min s α
  have hr : 0 ≤ r := le_min hs hα
  have hsr : 0 ≤ s-r := sub_nonneg.mpr (min_le_left _ _)
  have hαr : 0 ≤ α-r := sub_nonneg.mpr (min_le_right _ _)
  have hden : 0 < t+lam := add_pos_of_nonneg_of_pos ht.1 hlam
  have hw : 0 ≤ lam/(t+lam) := (div_pos hlam hden).le
  have hw1 : lam/(t+lam) ≤ 1 := (div_le_one hden).mpr (by linarith [ht.1])
  have hmix : t*(lam/(t+lam)) ≤ lam := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have htPow : t^s = t^(s-r)*t^r := by
    simpa only [sub_add_cancel] using Real.rpow_add_of_nonneg ht.1 hsr hr
  have hwPow : (lam/(t+lam))^α = (lam/(t+lam))^r*(lam/(t+lam))^(α-r) := by
    simpa only [add_sub_cancel] using Real.rpow_add_of_nonneg hw hr hαr
  have h₁ : t^(s-r) ≤ (1+M)^(s-r) :=
    Real.rpow_le_rpow ht.1 (by linarith [ht.2]) hsr
  have h₂ := Real.rpow_le_rpow (mul_nonneg ht.1 hw) hmix hr
  have h₃ := Real.rpow_le_one hw hw1 hαr
  calc
    _ = t^(s-r) * (t*(lam/(t+lam)))^r * (lam/(t+lam))^(α-r) := by
      rw [htPow, hwPow, Real.mul_rpow ht.1 hw]
      ring
    _ ≤ ((1+M)^(s-r) * lam^r) * 1 := by
      exact mul_le_mul (mul_le_mul h₁ h₂ (Real.rpow_nonneg (mul_nonneg ht.1 hw) _)
        (Real.rpow_nonneg (by positivity) _)) h₃
        (Real.rpow_nonneg hw _) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hlam.le _))
    _ = _ := by simp only [mul_one, r]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual `L²(μ)` source ball, attached to the same embedding and
positive eigenbasis as the manuscript sequence benchmark. -/
def featureSourceBall (k : X → H) (hk : MemLp k 2 μ) (s : ℝ) (hs : 0 ≤ s) (R : ℝ) :
    Set (Lp ℝ 2 μ) :=
  predictionSourceBall (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs R

theorem featureSourceBall_supported (k : X → H) (hk : MemLp k 2 μ)
    (s : ℝ) (hs : 0 ≤ s) (R : ℝ) {f : Lp ℝ 2 μ} (hf : f ∈ featureSourceBall k hk s hs R) :
    f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure := by
  simpa only [predictionCovariance, closure_range_self_comp_adjoint] using
    predictionSourceBall_mem_predictionRange (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) s hs R hf

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
