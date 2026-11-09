import KernelSeq.SourceEllipsoid

/-!
# Exact worst population bias on the actual source ball

The supremum is over actual supported `L²(μ)` targets, not formal sequences.
Each lower-bound direction is attained by an actual source vector `R e_i`.
The positive spectral supremum includes zero, giving value zero when the
positive spectrum is empty. A zero radius is allowed as well.
-/

open MeasureTheory Submodule
open scoped Classical

namespace KernelSeq
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem predictionSourcePower_single_coefficient_sq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) (R : ℝ)
    (i j : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hc j : E)
        (predictionSourcePower S hc s hs (R • (predictionSingularBasis S hc i : E))) ^ 2 =
      if j = i then i.1.1^s * R^2 else 0 := by
  classical
  have hij : inner ℝ (predictionSingularBasis S hc j : E)
      (predictionSingularBasis S hc i : E) = if j = i then 1 else 0 :=
    (orthonormal_iff_ite.mp (predictionSingularBasis S hc).orthonormal) j i
  rw [predictionSourcePower_coefficient_sq, inner_smul_right, hij]
  split_ifs with hji
  · subst j
    simp only [mul_one]
  · simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def featureSourceBiasWeight (k : X → H) (hk : MemLp k 2 μ) (s : ℝ) (φ : ℝ → ℝ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) : ℝ :=
  i.1.1^s * ResidualFilter.residual φ i.1.1^2

def featureSourceBiasSpectralSup (k : X → H) (hk : MemLp k 2 μ) (s : ℝ) (φ : ℝ → ℝ) : ℝ :=
  sSup (insert 0 (Set.range (featureSourceBiasWeight k hk s φ)))

def featureSourceWorstBias (k : X → H) (hk : MemLp k 2 μ)
    (s : ℝ) (hs : 0 ≤ s) (R : ℝ) (φ : ℝ → ℝ) : ℝ :=
  sSup ((fun f => featureSequenceBias k hk φ f) '' featureSourceBall k hk s hs R)

omit [IsProbabilityMeasure μ] in
theorem featureSourceBiasWeight_nonneg (k : X → H) (hk : MemLp k 2 μ)
    (s : ℝ) (φ : ℝ → ℝ) (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    0 ≤ featureSourceBiasWeight k hk s φ i :=
  mul_nonneg (Real.rpow_nonneg i.2.le _) (sq_nonneg _)

theorem featureSourceBiasWeight_le (k : X → H) (hk : MemLp k 2 μ)
    {s M : ℝ} (hs : 0 ≤ s) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    featureSourceBiasWeight k hk s φ i ≤ M^s := by
  have ht := featureCovarianceEigenvalue_mem k hk hM i.1
  have hr := hf.residual_mem ht
  have hr2 : ResidualFilter.residual φ i.1.1^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hr.1 hr.2 2
  calc
    _ ≤ i.1.1^s * 1 := mul_le_mul_of_nonneg_left hr2 (Real.rpow_nonneg ht.1 _)
    _ ≤ _ := by simpa only [mul_one] using Real.rpow_le_rpow ht.1 ht.2 hs

theorem featureSourceBiasSpectral_bddAbove (k : X → H) (hk : MemLp k 2 μ)
    {s M : ℝ} (hs : 0 ≤ s) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    BddAbove (insert 0 (Set.range (featureSourceBiasWeight k hk s φ))) := by
  refine ⟨M^s, ?_⟩
  rintro y (rfl | ⟨i, rfl⟩)
  · exact Real.rpow_nonneg ((norm_nonneg _).trans hM) _
  · exact featureSourceBiasWeight_le k hk hs hM φ hf i

theorem featureSourceBiasSpectralSup_nonneg (k : X → H) (hk : MemLp k 2 μ)
    {s M : ℝ} (hs : 0 ≤ s) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    0 ≤ featureSourceBiasSpectralSup k hk s φ :=
  le_csSup (featureSourceBiasSpectral_bddAbove k hk hs hM φ hf) (Set.mem_insert 0 _)

theorem featureSourceBiasWeight_le_spectralSup (k : X → H) (hk : MemLp k 2 μ)
    {s M : ℝ} (hs : 0 ≤ s) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    featureSourceBiasWeight k hk s φ i ≤ featureSourceBiasSpectralSup k hk s φ :=
  le_csSup (featureSourceBiasSpectral_bddAbove k hk hs hM φ hf) (Set.mem_insert_of_mem _ (Set.mem_range_self i))

theorem featureSequenceBias_le_sourceBall_spectralSup (k : X → H) (hk : MemLp k 2 μ)
    {s R M : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    {f : Lp ℝ 2 μ} (hsource : f ∈ featureSourceBall k hk s hs R) :
    featureSequenceBias k hk φ f ≤ R^2 * featureSourceBiasSpectralSup k hk s φ := by
  obtain ⟨g, hg, hgR, rfl⟩ := hsource
  have hsupport := predictionSourcePower_mem_predictionRange (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) s hs hg
  have hsum := summable_featureSequenceBias k hk φ hM hf hsupport
  have hcoeff := featureSequenceCoefficient_sq_summable k hk hg
  have hpoint (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
      ResidualFilter.residual φ i.1.1^2 * featureSequenceCoefficient k hk
        (predictionSourcePower (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) s hs g) i^2 ≤
      featureSourceBiasSpectralSup k hk s φ * featureSequenceCoefficient k hk g i^2 := by
    have he : featureSequenceCoefficient k hk
        (predictionSourcePower (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) s hs g) i^2 =
        i.1.1^s * featureSequenceCoefficient k hk g i^2 :=
      predictionSourcePower_coefficient_sq (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) s hs g i
    rw [he]
    calc
      _ = featureSourceBiasWeight k hk s φ i * featureSequenceCoefficient k hk g i^2 := by
        unfold featureSourceBiasWeight
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (featureSourceBiasWeight_le_spectralSup k hk hs hM φ hf i) (sq_nonneg _)
  have hb := Summable.tsum_le_tsum hpoint hsum (hcoeff.mul_left _)
  have hp : (∑' i, featureSequenceCoefficient k hk g i^2) = ‖g‖^2 :=
    (predictionSingularBasis_parseval _ (populationCovariance_feature_isCompact μ k hk) hg).symm
  rw [tsum_mul_left, hp] at hb
  refine hb.trans ?_
  have hsq := (sq_le_sq₀ (norm_nonneg _) hR).mpr hgR
  exact (mul_le_mul_of_nonneg_left hsq (featureSourceBiasSpectralSup_nonneg k hk hs hM φ hf)).trans_eq (mul_comm _ _)

theorem featureSequenceBias_source_direction (k : X → H) (hk : MemLp k 2 μ)
    {s : ℝ} (hs : 0 ≤ s) (R : ℝ) (φ : ℝ → ℝ)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    featureSequenceBias k hk φ
      (predictionSourcePower (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs
        (R • (predictionSingularBasis (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ))) =
      R^2 * featureSourceBiasWeight k hk s φ i := by
  classical
  have hcoeff (j : PredictionSingularIndex (featureEmbedding μ k hk)) :
      featureSequenceCoefficient k hk
        (predictionSourcePower (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs
          (R • (predictionSingularBasis (featureEmbedding μ k hk)
            (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ))) j^2 =
      if j = i then i.1.1^s * R^2 else 0 :=
    predictionSourcePower_single_coefficient_sq _ _ s hs R i j
  unfold featureSequenceBias
  simp_rw [hcoeff]
  rw [tsum_eq_single i]
  · simp only [ite_true, featureSourceBiasWeight]
    ring
  · intro j hji
    simp only [if_neg hji, mul_zero]

/-- Exact worst bias on the actual source ball. The inserted zero is the
explicit empty-positive-spectrum convention; no positive eigenvalue is assumed. -/
theorem featureSourceWorstBias_eq (k : X → H) (hk : MemLp k 2 μ)
    {s R M : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    featureSourceWorstBias k hk s hs R φ = R^2 * featureSourceBiasSpectralSup k hk s φ := by
  let B := (fun f => featureSequenceBias k hk φ f) '' featureSourceBall k hk s hs R
  have hB0 : 0 ∈ B := by
    refine ⟨0, zero_mem_predictionSourceBall _ _ s hs hR, ?_⟩
    simp only [featureSequenceBias, featureSequenceCoefficient, inner_zero_right, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, tsum_zero]
  have hBbd : BddAbove B := by
    refine ⟨R^2 * featureSourceBiasSpectralSup k hk s φ, ?_⟩
    rintro _ ⟨f, hsource, rfl⟩
    exact featureSequenceBias_le_sourceBall_spectralSup k hk hs hR hM φ hf hsource
  have hupper : featureSourceWorstBias k hk s hs R φ ≤ R^2 * featureSourceBiasSpectralSup k hk s φ := by
    apply csSup_le ⟨0, hB0⟩
    rintro _ ⟨f, hsource, rfl⟩
    exact featureSequenceBias_le_sourceBall_spectralSup k hk hs hR hM φ hf hsource
  have hnonneg : 0 ≤ featureSourceWorstBias k hk s hs R φ := le_csSup hBbd hB0
  apply le_antisymm hupper
  by_cases hR0 : R = 0
  · simpa only [hR0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using hnonneg
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  have hR2 : 0 < R^2 := sq_pos_of_pos hRpos
  have hsup : featureSourceBiasSpectralSup k hk s φ ≤ featureSourceWorstBias k hk s hs R φ / R^2 := by
    apply csSup_le (Set.insert_nonempty 0 _)
    rintro y (rfl | ⟨i, rfl⟩)
    · exact div_nonneg hnonneg hR2.le
    · apply (le_div_iff₀ hR2).mpr
      have hdir : R^2 * featureSourceBiasWeight k hk s φ i ∈ B := by
        refine ⟨_, ⟨R • (predictionSingularBasis (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ), ?_, ?_, rfl⟩,
          featureSequenceBias_source_direction k hk hs R φ i⟩
        · exact (PredictionRange (featureEmbedding μ k hk)).smul_mem R (Subtype.prop _)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
          have hn : ‖(predictionSingularBasis (featureEmbedding μ k hk)
              (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ)‖ = 1 :=
            (predictionSingularBasis _ _).orthonormal.norm_eq_one i
          rw [hn, mul_one]
      exact (mul_comm _ _).trans_le (le_csSup hBbd hdir)
  have hh := (le_div_iff₀ hR2).mp hsup
  simpa only [mul_comm] using hh

end
end KernelSeq
