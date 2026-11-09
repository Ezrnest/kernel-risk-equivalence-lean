import KernelSeq.SingularSystem
import KernelSeq.SpectralRHS
import KernelSeq.FilterDimension

/-!
# The sequence benchmark in the actual supported singular system

The prediction coordinates are those of the actual basis `S v_i / sqrt(t_i)`
of the closed prediction range. Parseval is therefore applied in the supported
space, without requiring the ambient `L²(μ)` to be separable. The benchmark is
the deterministic bias/variance expression; no infinite Gaussian noise law is
constructed in this module.
-/

open MeasureTheory Submodule

namespace KernelSeq

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem compactSpectralMultiplier_isSymmetric (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    (compactSpectralMultiplier T hc hp φ K hK hφ).IsSymmetric :=
  hilbertDiagonal_isSymmetric _ _ _ _ _

/-- Actual multiplier action on the coefficients of the singular prediction basis. -/
theorem predictionSingularBasis_multiplier_coefficient (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    (f : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hcT i : E)
      (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f) =
      φ i.1.1 * inner ℝ (predictionSingularBasis S hcT i : E) f := by
  calc
    _ = inner ℝ (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (predictionSingularBasis S hcT i : E)) f :=
      (compactSpectralMultiplier_isSymmetric _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ _ _).symm
    _ = _ := by
      rw [compactSpectralMultiplier_eigen _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (predictionSingularBasis_eigen S hcT i), inner_smul_left, conj_trivial]

/-- The actual multiplier preserves the source-supported prediction space. -/
theorem compactSpectralMultiplier_mem_predictionRange (S : H →L[ℝ] E)
    (hcL : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    compactSpectralMultiplier (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f ∈ PredictionRange S := by
  have hRange : S.adjoint.kerᗮ = PredictionRange S := by
    simpa only [ContinuousLinearMap.adjoint_adjoint, PredictionRange] using S.adjoint.orthogonal_ker
  rw [← hRange]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  have hzL : (S.comp S.adjoint) z = 0 := by
    change S (S.adjoint z) = 0
    rw [show S.adjoint z = 0 from hz, map_zero]
  have hfz := inner_zero_of_mem_closure_range_of_self_comp_adjoint_eq_zero S hf hzL
  calc
    _ = inner ℝ (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ z) f :=
      (compactSpectralMultiplier_isSymmetric _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ _ _).symm
    _ = 0 := by
      rw [compactSpectralMultiplier_eigen _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (show (S.comp S.adjoint) z = (0 : ℝ) • z by
            simpa only [zero_smul] using hzL), inner_smul_left, conj_trivial, hfz, mul_zero]

/-- Parseval in the actual supported singular basis gives the true multiplier
energy, with the positive eigenvalues and multiplicities of `T = S* S`. -/
theorem predictionSingularBasis_multiplier_norm_sq (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    ‖compactSpectralMultiplier (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f‖ ^ 2 =
      ∑' i : PredictionSingularIndex S,
        φ i.1.1 ^ 2 * inner ℝ (predictionSingularBasis S hcT i : E) f ^ 2 := by
  rw [predictionSingularBasis_parseval S hcT
    (compactSpectralMultiplier_mem_predictionRange S hcL φ K hK hφ hf)]
  apply tsum_congr
  intro i
  rw [predictionSingularBasis_multiplier_coefficient, mul_pow]

/-- Convergence of the displayed coefficient energy is a theorem about actual
coordinates, rather than a convention for possibly divergent `tsum`. -/
theorem predictionSingularBasis_multiplier_energy_summable (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    Summable (fun i : PredictionSingularIndex S =>
      φ i.1.1 ^ 2 * inner ℝ (predictionSingularBasis S hcT i : E) f ^ 2) := by
  have hs := predictionSingularBasis_coefficients_summable S hcT
    (compactSpectralMultiplier_mem_predictionRange S hcL φ K hK hφ hf)
  simpa only [predictionSingularBasis_multiplier_coefficient, mul_pow] using hs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual sequence coordinate of a target in prediction space. -/
noncomputable def featureSequenceCoefficient (k : X → H) (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) (i : PredictionSingularIndex (featureEmbedding μ k hk)) : ℝ :=
  inner ℝ (predictionSingularBasis (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ) f

noncomputable def featureSequenceBias (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
    ResidualFilter.residual φ i.1.1 ^ 2 * featureSequenceCoefficient k hk f i ^ 2

noncomputable def featureSequenceSourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (lam α : ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
    (lam / (i.1.1 + lam)) ^ α * featureSequenceCoefficient k hk f i ^ 2

theorem featureSequenceCoefficient_sq_summable (k : X → H) (hk : MemLp k 2 μ)
    {f : Lp ℝ 2 μ} (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    Summable (fun i => featureSequenceCoefficient k hk f i ^ 2) :=
  predictionSingularBasis_coefficients_summable _ (populationCovariance_feature_isCompact μ k hk) hf

/-- The real population residual bias is exactly the supported sequence bias. -/
theorem populationSpectralResidual_norm_sq_eq_sequenceBias (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : Lp ℝ 2 μ}
    (hf : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖populationSpectralResidual k hk φ hM hfilter f‖ ^ 2 = featureSequenceBias k hk φ f := by
  have hs : f ∈ PredictionRange (featureEmbedding μ k hk) := by
    simpa only [predictionCovariance, closure_range_self_comp_adjoint] using hf
  exact predictionSingularBasis_multiplier_norm_sq (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (predictionCovariance_feature_isCompact μ k hk)
    (ResidualFilter.residual φ) 1 zero_le_one _ hs

theorem summable_featureSequenceBias (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : Lp ℝ 2 μ}
    (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    Summable (fun i => ResidualFilter.residual φ i.1.1 ^ 2 * featureSequenceCoefficient k hk f i ^ 2) := by
  apply predictionSingularBasis_multiplier_energy_summable (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (predictionCovariance_feature_isCompact μ k hk)
    (ResidualFilter.residual φ) 1 zero_le_one _ hf
  intro t ht
  exact hfilter.residual_abs_le_one ⟨ht.1,
    ht.2.trans ((predictionCovariance_norm_eq_population _).trans_le hM)⟩

theorem summable_featureSequenceSourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    {lam α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) {f : Lp ℝ 2 μ}
    (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      (lam / (i.1.1 + lam)) ^ α * featureSequenceCoefficient k hk f i ^ 2) := by
  apply summable_regularized_coefficients (M := ‖populationCovariance (featureEmbedding μ k hk)‖)
    (fun i => i.1.1) _ hlam hα _ (featureSequenceCoefficient_sq_summable k hk hf)
  intro i
  exact ⟨i.2.le, (le_abs_self i.1.1).trans (compactEigenvalue_norm_le _
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric i.1)⟩

/-- The actual weighted population target norm uses the same positive singular
coordinates as the sequence model. -/
theorem populationResidualWeight_norm_sq_eq_sequence (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : Lp ℝ 2 μ}
    (hf : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖compactResidualWeightOperator (predictionCovariance (featureEmbedding μ k hk))
      (predictionCovariance_feature_isCompact μ k hk)
      (predictionCovariance_isPositive (featureEmbedding μ k hk)) φ hlam hα
      ((predictionCovariance_norm_eq_population _).trans_le hM) hfilter f‖ ^ 2 =
      ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
        residualWeight lam α φ i.1.1 ^ 2 * featureSequenceCoefficient k hk f i ^ 2 := by
  have hs : f ∈ PredictionRange (featureEmbedding μ k hk) := by
    simpa only [predictionCovariance, closure_range_self_comp_adjoint] using hf
  exact predictionSingularBasis_multiplier_norm_sq (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (predictionCovariance_feature_isCompact μ k hk)
    (residualWeight lam α φ) 2 (by norm_num) _ hs

/-- Qualification yields the manuscript's weighted source estimate in the
same actual supported singular system, with the exact constant `(A+1)²`. -/
theorem populationResidualWeight_norm_sq_le_sequenceSource (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    {f : Lp ℝ 2 μ}
    (hf : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖compactResidualWeightOperator (predictionCovariance (featureEmbedding μ k hk))
      (predictionCovariance_feature_isCompact μ k hk)
      (predictionCovariance_isPositive (featureEmbedding μ k hk)) φ hlam hα
      ((predictionCovariance_norm_eq_population _).trans_le hM) hfilter f‖ ^ 2 ≤
        (A + 1) ^ 2 * featureSequenceSourceEnergy k hk lam α f := by
  rw [populationResidualWeight_norm_sq_eq_sequence k hk φ hlam hα hM hfilter hf,
    featureSequenceSourceEnergy]
  apply tsum_residualWeight_coefficients_le _ _ hfilter h hlam hα hαρ
  · intro i
    exact featureCovarianceEigenvalue_mem k hk hM i.1
  · apply featureSequenceCoefficient_sq_summable k hk
    simpa only [predictionCovariance, closure_range_self_comp_adjoint] using hf

/-- Removing the zero covariance spectrum changes no filter variance term:
`q(0)=0`, regardless of the value of the inverse profile at zero. -/
theorem featureFilterDimension_eq_positive_sequence (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) :
    featureFilterDimension k hk φ =
      ∑' i : PredictionSingularIndex (featureEmbedding μ k hk), ResidualFilter.shrinkage φ i.1.1 ^ 2 := by
  unfold featureFilterDimension
  symm
  apply tsum_subtype_eq_of_support_subset
    (s := {i : FeatureCovarianceIndex k hk | 0 < i.1})
    (f := fun i : FeatureCovarianceIndex k hk => ResidualFilter.shrinkage φ i.1 ^ 2)
  intro i hi
  have ht := compactEigenvalue_nonneg _ (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) i
  by_contra hnot
  have hz : i.1 = 0 := le_antisymm (le_of_not_gt hnot) ht
  exact hi (by simp only [hz, ResidualFilter.shrinkage, zero_mul, zero_pow (by decide : 2 ≠ 0)])

/-- Finiteness of the positive `Nq` series follows from the actual covariance
trace and filter contract. Only the feature Hilbert space is assumed separable. -/
theorem summable_positive_sequence_filterDimension [TopologicalSpace.SeparableSpace H]
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      ResidualFilter.shrinkage φ i.1.1 ^ 2) :=
  (summable_featureFilterDimension k hk φ hlam hM hfilter h).subtype _

/-- Both components of the deterministic sequence benchmark are genuinely
convergent series under the source assumptions. -/
theorem sequenceBenchmark_series_summable [TopologicalSpace.SeparableSpace H]
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    {f : Lp ℝ 2 μ} (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      ResidualFilter.residual φ i.1.1 ^ 2 * featureSequenceCoefficient k hk f i ^ 2) ∧
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      ResidualFilter.shrinkage φ i.1.1 ^ 2) :=
  ⟨summable_featureSequenceBias k hk φ hM hfilter hf,
    summable_positive_sequence_filterDimension k hk φ hlam hM hfilter h⟩

/-- The deterministic sequence-model bias/variance expression on the actual
positive singular system. No Gaussian-law existence is asserted here. -/
noncomputable def sequenceBenchmark (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) (f : Lp ℝ 2 μ) (σ : ℝ) (n : ℕ) : ℝ :=
  featureSequenceBias k hk φ f + σ ^ 2 / (n : ℝ) *
    ∑' i : PredictionSingularIndex (featureEmbedding μ k hk), ResidualFilter.shrinkage φ i.1.1 ^ 2

/-- Exact equality with the actual population bias and actual variance
dimension, derived without assuming a bias identity. -/
theorem sequenceBenchmark_eq_population (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {M : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : Lp ℝ 2 μ}
    (hf : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ : ℝ) (n : ℕ) :
    sequenceBenchmark k hk φ f σ n = ‖populationSpectralResidual k hk φ hM hfilter f‖ ^ 2 +
      σ ^ 2 / (n : ℝ) * featureFilterDimension k hk φ := by
  rw [populationSpectralResidual_norm_sq_eq_sequenceBias k hk φ hM hfilter hf,
    featureFilterDimension_eq_positive_sequence]
  rfl

end KernelSeq
