import KernelSeq.SourceBias

/-!
# Qualification, source-ball risk and kernel-ridge saturation

All targets and bias energies below are actual supported prediction-space
objects. Qualification is derived from the original residual contract.
-/

open MeasureTheory Submodule
open scoped Classical

namespace KernelSeq
noncomputable section

namespace ResidualFilter

theorem Contract.residual_sq_le_regularized {lam M ρ A t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hf : SpectralFilter M φ) (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    residual φ t ^ 2 ≤ A^2 * (lam/(t+lam))^(2*ρ) := by
  have hA := h.constant_nonneg hlam (ht.1.trans ht.2)
  have hr := h.residual_size hlam ht
  rw [abs_of_nonneg (hf.residual_nonneg ht)] at hr
  have hs := pow_le_pow_left₀ (hf.residual_nonneg ht) hr 2
  have he : ((lam/(t+lam))^ρ)^2 = (lam/(t+lam))^(2*ρ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (regularization_weight_mem hlam ht).1.le]
    congr 1
    ring
  simpa only [mul_pow, he] using hs

end ResidualFilter

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureSequenceBias_le_qualified_sourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    {f : Lp ℝ 2 μ} (hsupport : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    featureSequenceBias k hk φ f ≤ A^2 * featureSequenceSourceEnergy k hk lam (2*ρ) f := by
  rw [featureSequenceBias, featureSequenceSourceEnergy, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_featureSequenceBias k hk φ hM hf hsupport)
    ((summable_featureSequenceSourceEnergy k hk hlam (by linarith [h.rho_pos]) hsupport).mul_left _)
  intro i
  exact (mul_le_mul_of_nonneg_right
    (h.residual_sq_le_regularized hf hlam (featureCovarianceEigenvalue_mem k hk hM i.1))
    (sq_nonneg (featureSequenceCoefficient k hk f i))).trans_eq (by ring)

/-- The qualification/source upper bound includes saturation at `2ρ` and
has a constant independent of the target and regularization. -/
theorem featureSequenceBias_le_sourceBall_qualification (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A s R : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    {f : Lp ℝ 2 μ} (hsource : f ∈ featureSourceBall k hk s hs R) :
    featureSequenceBias k hk φ f ≤ A^2 * (1+M)^(s-min s (2*ρ)) * R^2 * lam^(min s (2*ρ)) := by
  have hsupport : f ∈ PredictionRange (featureEmbedding μ k hk) :=
    predictionSourceBall_mem_predictionRange _ _ s hs R hsource
  have hfirst := featureSequenceBias_le_qualified_sourceEnergy k hk φ hlam hM hf h hsupport
  have hsecond := featureSequenceSourceEnergy_le_sourceBall k hk (α := 2*ρ) hs
    (by linarith [h.rho_pos]) hR hlam hM hsource
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hsecond (sq_nonneg A)).trans_eq (by ring))

theorem featureSourceWorstBias_le_qualification (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A s R : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    featureSourceWorstBias k hk s hs R φ ≤ A^2 * (1+M)^(s-min s (2*ρ)) * R^2 * lam^(min s (2*ρ)) := by
  rw [featureSourceWorstBias]
  have hn : ((fun f => featureSequenceBias k hk φ f) '' featureSourceBall k hk s hs R).Nonempty :=
    ⟨featureSequenceBias k hk φ 0, ⟨0, zero_mem_predictionSourceBall _ _ s hs hR, rfl⟩⟩
  apply csSup_le hn
  rintro _ ⟨f, hsource, rfl⟩
  exact featureSequenceBias_le_sourceBall_qualification k hk φ hlam hs hR hM hf h hsource

/-- The genuine population sequence risk bound on the source ball; the
kernel-risk comparison can then be applied using its original scale hypotheses. -/
theorem sequenceBenchmark_le_sourceBall_qualification (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A s R : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    {f : Lp ℝ 2 μ} (hsource : f ∈ featureSourceBall k hk s hs R) (σ : ℝ) (n : ℕ) :
    sequenceBenchmark k hk φ f σ n ≤
      A^2 * (1+M)^(s-min s (2*ρ)) * R^2 * lam^(min s (2*ρ)) +
      σ^2/(n:ℝ) * featureFilterDimension k hk φ := by
  have hsupport := featureSourceBall_supported k hk s hs R hsource
  rw [sequenceBenchmark_eq_population k hk φ hM hf hsupport σ n,
    populationSpectralResidual_norm_sq_eq_sequenceBias k hk φ hM hf hsupport]
  exact add_le_add (featureSequenceBias_le_sourceBall_qualification k hk φ hlam hs hR hM hf h hsource) le_rfl

/-- The nonnegative spectral supremum agrees with the ordinary supremum
whenever there is a positive spectral coordinate. -/
theorem featureSourceBiasSpectralSup_eq_sSup (k : X → H) (hk : MemLp k 2 μ)
    [Nonempty (PredictionSingularIndex (featureEmbedding μ k hk))]
    {s M : ℝ} (hs : 0 ≤ s) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    featureSourceBiasSpectralSup k hk s φ = sSup (Set.range (featureSourceBiasWeight k hk s φ)) := by
  have hbd : BddAbove (Set.range (featureSourceBiasWeight k hk s φ)) :=
    (featureSourceBiasSpectral_bddAbove k hk hs hM φ hf).mono (Set.subset_insert _ _)
  have hn : 0 ≤ sSup (Set.range (featureSourceBiasWeight k hk s φ)) := by
    let i := Classical.choice (inferInstance : Nonempty (PredictionSingularIndex (featureEmbedding μ k hk)))
    exact (featureSourceBiasWeight_nonneg k hk s φ i).trans (le_csSup hbd (Set.mem_range_self i))
  apply le_antisymm
  · apply csSup_le (Set.insert_nonempty 0 _)
    rintro y (rfl | hy)
    · exact hn
    · exact le_csSup hbd hy
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    exact featureSourceBiasWeight_le_spectralSup k hk hs hM φ hf i

omit [IsProbabilityMeasure μ] in
theorem featureSourceBiasSpectralSup_empty (k : X → H) (hk : MemLp k 2 μ)
    [IsEmpty (PredictionSingularIndex (featureEmbedding μ k hk))] (s : ℝ) (φ : ℝ → ℝ) :
    featureSourceBiasSpectralSup k hk s φ = 0 := by
  have he : Set.range (featureSourceBiasWeight k hk s φ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨i, _⟩
    exact isEmptyElim i
  simp only [featureSourceBiasSpectralSup, he, insert_empty_eq, csSup_singleton]

theorem featureSourceWorstBias_eq_sSup (k : X → H) (hk : MemLp k 2 μ)
    [Nonempty (PredictionSingularIndex (featureEmbedding μ k hk))]
    {s R M : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    featureSourceWorstBias k hk s hs R φ =
      R^2 * sSup (Set.range (featureSourceBiasWeight k hk s φ)) := by
  rw [featureSourceWorstBias_eq k hk hs hR hM φ hf,
    featureSourceBiasSpectralSup_eq_sSup k hk hs hM φ hf]

/-- The source-ball supremum is also the supremum of actual population
prediction-residual norms, not merely a coordinate-series definition. -/
theorem featureSourceWorstBias_eq_populationBiasSup (k : X → H) (hk : MemLp k 2 μ)
    {s R M : ℝ} (hs : 0 ≤ s)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) :
    featureSourceWorstBias k hk s hs R φ =
      sSup ((fun f => ‖populationSpectralResidual k hk φ hM hf f‖^2) '' featureSourceBall k hk s hs R) := by
  apply congrArg sSup
  apply Set.ext
  intro y
  constructor
  · rintro ⟨f, hsource, rfl⟩
    exact ⟨f, hsource, populationSpectralResidual_norm_sq_eq_sequenceBias k hk φ hM hf
      (featureSourceBall_supported k hk s hs R hsource)⟩
  · rintro ⟨f, hsource, rfl⟩
    exact ⟨f, hsource, (populationSpectralResidual_norm_sq_eq_sequenceBias k hk φ hM hf
      (featureSourceBall_supported k hk s hs R hsource)).symm⟩

/-- KRR's upper saturation exponent is exactly `min(s,2)`. -/
theorem featureSourceWorstBias_ridge_le (k : X → H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) :
    featureSourceWorstBias k hk s hs R (ResidualFilter.ridge lam) ≤
      4 * (1+M)^(s-min s 2) * R^2 * lam^(min s 2) := by
  simpa only [show (2:ℝ)*1=2 by norm_num, show (2:ℝ)^2=4 by norm_num] using
    featureSourceWorstBias_le_qualification k hk (ResidualFilter.ridge lam) hlam hs hR hM
      (ResidualFilter.ridge_spectralFilter hlam) (ResidualFilter.ridge_contract hlam)

/-- A single fixed positive population direction proves the lower KRR
saturation rate. It requires neither an eigenvalue-decay model nor a
lower bound on every target coordinate. -/
theorem featureSourceWorstBias_ridge_ge_direction (k : X → H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hsmall : lam ≤ i.1.1) :
    R^2 * i.1.1^s / (4*i.1.1^2) * lam^2 ≤
      featureSourceWorstBias k hk s hs R (ResidualFilter.ridge lam) := by
  have ht := i.2
  have hr : lam/(2*i.1.1) ≤ ResidualFilter.residual (ResidualFilter.ridge lam) i.1.1 := by
    rw [ResidualFilter.ridge_residual (by linarith : i.1.1+lam ≠ 0)]
    exact div_le_div_of_nonneg_left hlam.le (by linarith) (by linarith)
  have hrsq := pow_le_pow_left₀ (div_nonneg hlam.le (by positivity : 0≤2*i.1.1)) hr 2
  have hweight : i.1.1^s / (4*i.1.1^2) * lam^2 ≤
      featureSourceBiasWeight k hk s (ResidualFilter.ridge lam) i := by
    have hm := mul_le_mul_of_nonneg_left hrsq (Real.rpow_nonneg ht.le s)
    calc
      _ = i.1.1^s * (lam/(2*i.1.1))^2 := by
        simp only [div_pow, mul_pow, show (2:ℝ)^2=4 by norm_num]
        ring
      _ ≤ _ := hm
  rw [featureSourceWorstBias_eq k hk hs hR hM _ (ResidualFilter.ridge_spectralFilter hlam)]
  have hi := featureSourceBiasWeight_le_spectralSup k hk hs hM
    (ResidualFilter.ridge lam) (ResidualFilter.ridge_spectralFilter hlam) i
  calc
    _ = R^2 * (i.1.1^s / (4*i.1.1^2) * lam^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hweight.trans hi) (sq_nonneg R)

/-- Above smoothness two, a fixed positive population direction makes the
KRR saturation bounds comparable to `lam²`, with positive constants uniform
over all `0 < lam ≤ t_i`. -/
theorem featureSourceWorstBias_ridge_saturation (k : X → H) (hk : MemLp k 2 μ)
    {M s R : ℝ} (hs : 2 ≤ s) (hR : 0 < R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ i.1.1 →
      c*lam^2 ≤ featureSourceWorstBias k hk s (by linarith) R (ResidualFilter.ridge lam) ∧
      featureSourceWorstBias k hk s (by linarith) R (ResidualFilter.ridge lam) ≤ C*lam^2 := by
  let c := R^2 * i.1.1^s / (4*i.1.1^2)
  let C := 4 * (1+M)^(s-2) * R^2
  have hMn : 0 ≤ M := (norm_nonneg _).trans hM
  have hs0 : 0 ≤ s := by linarith
  have hc : 0 < c := div_pos (mul_pos (sq_pos_of_pos hR) (Real.rpow_pos_of_pos i.2 s))
    (mul_pos (by norm_num) (sq_pos_of_pos i.2))
  have hC : 0 < C := mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)) (sq_pos_of_pos hR)
  refine ⟨c, C, hc, hC, ?_⟩
  intro lam hlam hsmall
  constructor
  · exact featureSourceWorstBias_ridge_ge_direction k hk (s := s) hlam hs0 hR.le hM i hsmall
  · simpa only [min_eq_right hs, C, Real.rpow_two] using
      featureSourceWorstBias_ridge_le k hk (s := s) hlam hs0 hR.le hM

end
end KernelSeq
