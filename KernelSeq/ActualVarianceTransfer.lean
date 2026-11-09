import KernelSeq.VarianceTraceComparison
import KernelSeq.VarianceTransfer
import KernelSeq.LipschitzHS
import KernelSeq.MixedPerturbation

/-!
# Actual pointwise common variance transfer

The population operator is the actual covariance `T=S* S` of the feature
embedding, and the empirical operator is the actual sample covariance. Both
shrinkage operators are represented by constructed Hilbert--Schmidt columns.
Their difference is checked through reconstruction and injectivity, so neither
HS existence, a trace perturbation bound, nor the square-root comparison is an
input certificate. The remaining probabilistic rates are separate from these
pointwise statements.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace KernelSeq

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Actual HS columns of the population shrinkage, with summability derived
from the actual filter dimension. -/
noncomputable def populationShrinkageHSColumns (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    HilbertSchmidtColumns (FeatureCovarianceIndex k hk) H :=
  ⟨fun i => compactShrinkageOperator (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk) (populationCovariance_isPositive _) φ hM hf
      (featureCovarianceBasis k hk i),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hasSum_compactShrinkageOperator_columns k hk φ hlam hM hf h).summable)⟩

theorem hilbertSchmidtOperator_populationShrinkageHSColumns
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    hilbertSchmidtOperator (featureCovarianceBasis k hk)
      (populationShrinkageHSColumns k hk φ hlam hM hf h) =
      compactShrinkageOperator (populationCovariance (featureEmbedding μ k hk))
        (populationCovariance_feature_isCompact μ k hk) (populationCovariance_isPositive _) φ hM hf := by
  apply continuousLinearMap_eq_of_hilbertBasis (featureCovarianceBasis k hk)
  intro i
  rw [hilbertSchmidtOperator_basis]
  rfl

theorem populationShrinkageHSColumns_norm_sq (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    ‖populationShrinkageHSColumns k hk φ hlam hM hf h‖ ^ 2 = featureFilterDimension k hk φ := by
  rw [hsColumns_norm_sq]
  exact (hasSum_compactShrinkageOperator_columns k hk φ hlam hM hf h).tsum_eq

/-- The actual empirical shrinkage columns in the empirical covariance basis. -/
noncomputable def empiricalShrinkageHSColumns {n : ℕ} (z : Fin n → H) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) : HilbertSchmidtColumns (EmpiricalCovarianceIndex z) H :=
  hsLeftComposition (empiricalCovarianceSqrt z) (empiricalFilteredRootColumns z φ hlam hM h)

omit [TopologicalSpace.SeparableSpace H] in
theorem hilbertSchmidtOperator_empiricalShrinkageHSColumns {n : ℕ} (z : Fin n → H)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖empiricalCovariance z‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    hilbertSchmidtOperator (empiricalCovarianceBasis z) (empiricalShrinkageHSColumns z φ hlam hM h) =
      compactShrinkageOperator (empiricalCovariance z) (empiricalCovariance_isCompact z)
        (empiricalCovariance_isPositive z) φ hM hf :=
  hilbertSchmidtOperator_empiricalShrinkageColumns z φ hlam hM hf h

/-- Empirical shrinkage rebased to the actual population covariance basis. -/
noncomputable def actualEmpiricalShrinkageColumns (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) : HilbertSchmidtColumns (FeatureCovarianceIndex k hk) H :=
  hsRebase (empiricalCovarianceBasis (fun i => k (x i))) (featureCovarianceBasis k hk)
    (empiricalShrinkageHSColumns (fun i => k (x i)) φ hlam hMX h)

/-- The actual HS difference, in one common population basis. -/
noncomputable def actualShrinkageDifferenceColumns (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    HilbertSchmidtColumns (FeatureCovarianceIndex k hk) H :=
  actualEmpiricalShrinkageColumns k hk φ hlam x hMX h - populationShrinkageHSColumns k hk φ hlam hM hf h

/-- The empirical and population columns represent the actual shrinkage difference. -/
theorem hilbertSchmidtOperator_actualShrinkageDifferenceColumns
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    hilbertSchmidtOperator (featureCovarianceBasis k hk)
      (actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h) =
      compactShrinkageOperator (empiricalCovariance (fun i => k (x i))) (empiricalCovariance_isCompact _)
        (empiricalCovariance_isPositive _) φ hMX hf -
      compactShrinkageOperator (populationCovariance (featureEmbedding μ k hk))
        (populationCovariance_feature_isCompact μ k hk) (populationCovariance_isPositive _) φ hM hf := by
  rw [actualShrinkageDifferenceColumns, map_sub, actualEmpiricalShrinkageColumns,
    hilbertSchmidtOperator_rebase, hilbertSchmidtOperator_empiricalShrinkageHSColumns,
    hilbertSchmidtOperator_populationShrinkageHSColumns]

omit [TopologicalSpace.SeparableSpace H] in
theorem actualEmpiricalShrinkageColumns_norm_sq (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    ‖actualEmpiricalShrinkageColumns k hk φ hlam x hMX h‖ ^ 2 =
      empiricalFilterDimension (fun i => k (x i)) φ := by
  rw [actualEmpiricalShrinkageColumns, hsRebase_norm]
  exact empiricalFilteredRootColumns_shrinkage_norm_sq _ φ hlam hMX hf h

/-- The source square-root comparison is derived from the actual HS triangle
inequality, with `d` the norm of the actual shrinkage difference. -/
theorem actual_variance_sqrt_comparison (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    |Real.sqrt (empiricalFilterDimension (fun i => k (x i)) φ) - Real.sqrt (featureFilterDimension k hk φ)| ≤
      ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖ := by
  rw [← actualEmpiricalShrinkageColumns_norm_sq k hk φ hlam x hMX hf h,
    ← populationShrinkageHSColumns_norm_sq k hk φ hlam hM hf h,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact abs_norm_sub_norm_le _ _

/-- The actual unscaled empirical prediction variance energy `a`. -/
noncomputable def actualVarianceEnergy (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) : ℝ :=
  ‖hsLeftComposition (featureEmbedding μ k hk)
    (empiricalFilteredRootColumns (fun i => k (x i)) φ hlam hMX h)‖ ^ 2

/-- The actual operator deviation used in the pointwise good event. -/
noncomputable def actualCovarianceDeviation (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → X) : ℝ :=
  covarianceRelativeDeviation (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance (fun i => k (x i))) lam

/-- The full pointwise general variance comparison for actual feature/sample
operators. The trace and square-root estimates are proved upstream theorems,
not extra premises in this statement. -/
theorem actual_quantitative_variance_comparison (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    |actualVarianceEnergy k hk φ hlam x hMX h - featureFilterDimension k hk φ| ≤
      ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖ *
        (2 * Real.sqrt (featureFilterDimension k hk φ) +
          ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖) +
      (2 * (1 + A ^ 2)) * actualCovarianceDeviation k hk lam x *
        ((Real.sqrt (featureFilterDimension k hk φ) +
          ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖) ^ 2 +
          empiricalEffectiveDimension (fun i => k (x i)) lam) := by
  apply quantitative_variance_comparison (W := empiricalFilterDimension (fun i => k (x i)) φ)
  · exact tsum_nonneg (fun _ => sq_nonneg _)
  · exact featureFilterDimension_nonneg k hk φ
  · apply tsum_nonneg
    intro i
    have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact (fun i => k (x i)))
      (empiricalCovariance_isPositive _) i
    exact div_nonneg ht (add_nonneg ht hlam.le)
  · exact norm_nonneg _
  · exact norm_nonneg _
  · exact hδ
  · exact empirical_variance_trace_abs_sub_le (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) _ φ hlam hMX hf h
  · exact actual_variance_sqrt_comparison k hk φ hlam hM x hMX hf h

/-- The actual HS shrinkage difference is bounded on the source quarter good
event. Equality of the independently constructed difference columns is proved
by injectivity of the actual bounded-operator reconstruction. -/
theorem actualShrinkageDifferenceColumns_norm_le_eta (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖ ≤
      (2 * A * (1 + ρ)) *
        ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam x‖ := by
  let T := populationCovariance (featureEmbedding μ k hk)
  let TX := empiricalCovariance (fun i => k (x i))
  let c := manuscriptMixedColumns (featureCovarianceBasis k hk) k hk lam x
  have hK : hilbertSchmidtOperator
      (compactEigenbasis T (populationCovariance_feature_isCompact μ k hk)
        (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric) c =
      compactMixedDifference TX T (empiricalCovariance_isCompact _) (populationCovariance_feature_isCompact μ k hk)
        (empiricalCovariance_isPositive _) (populationCovariance_isPositive _) lam :=
    hilbertSchmidtOperator_manuscriptMixedColumns (featureCovarianceBasis k hk) k hk lam hlam x
  let d := compactShrinkageDifferenceColumns TX T
    (empiricalCovariance_isCompact _) (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance_isPositive _) (populationCovariance_isPositive _)
    φ hlam hMX hM hf h c hK
  have hrepr := hilbertSchmidtOperator_compactShrinkageDifferenceColumns TX T
    (empiricalCovariance_isCompact _) (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance_isPositive _) (populationCovariance_isPositive _)
    φ hlam hMX hM hf h c hK
  have heq : actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h = d := by
    apply hilbertSchmidtOperator_injective (featureCovarianceBasis k hk)
    rw [hilbertSchmidtOperator_actualShrinkageDifferenceColumns]
    exact hrepr.symm
  have hC : 0 ≤ A * (1 + ρ) :=
    mul_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hM)) (by linarith [h.rho_pos])
  rw [heq]
  calc
    ‖d‖ ≤ (A * (1 + ρ)) * ‖c‖ :=
      compactShrinkageDifferenceColumns_norm_le TX T
        (empiricalCovariance_isCompact _) (populationCovariance_feature_isCompact μ k hk)
        (empiricalCovariance_isPositive _) (populationCovariance_isPositive _)
        φ hlam hMX hM hf h c hK
    _ ≤ (A * (1 + ρ)) * (2 *
        ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam x‖) :=
      mul_le_mul_of_nonneg_left
        (manuscriptMixedColumns_norm_le (featureCovarianceBasis k hk) k hk lam hlam x hδ) hC
    _ = _ := by ring

/-- A convenient polynomial version of the exact source RHS, with explicit
constant `4(1+A²)`. This algebra does not introduce any operator hypothesis. -/
theorem variance_source_rhs_le_polynomial {Q N d δ A : ℝ}
    (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hd : 0 ≤ d) (hδ : 0 ≤ δ) :
    d * (2 * Real.sqrt Q + d) + (2 * (1 + A ^ 2)) * δ * ((Real.sqrt Q + d) ^ 2 + N) ≤
      (4 * (1 + A ^ 2)) * ((1 + δ) * d ^ 2 + Real.sqrt Q * d + δ * (Q + N)) := by
  have hp : (Real.sqrt Q + d) ^ 2 = Q + 2 * Real.sqrt Q * d + d ^ 2 := by
    nlinarith [Real.sq_sqrt hQ]
  have hm : (Real.sqrt Q - d) ^ 2 = Q - 2 * Real.sqrt Q * d + d ^ 2 := by
    nlinarith [Real.sq_sqrt hQ]
  have hid :
      (4 * (1 + A ^ 2)) * ((1 + δ) * d ^ 2 + Real.sqrt Q * d + δ * (Q + N)) -
        (d * (2 * Real.sqrt Q + d) + (2 * (1 + A ^ 2)) * δ * ((Real.sqrt Q + d) ^ 2 + N)) =
      (4 * (1 + A ^ 2) - 1) * d ^ 2 + (4 * (1 + A ^ 2) - 2) * Real.sqrt Q * d +
        (2 * (1 + A ^ 2)) * δ * ((Real.sqrt Q - d) ^ 2 + N) := by
    rw [hp, hm]
    ring
  have hc₁ : 0 ≤ 4 * (1 + A ^ 2) - 1 := by nlinarith [sq_nonneg A]
  have hc₂ : 0 ≤ 4 * (1 + A ^ 2) - 2 := by nlinarith [sq_nonneg A]
  apply sub_nonneg.mp
  rw [hid]
  exact add_nonneg
    (add_nonneg (mul_nonneg hc₁ (sq_nonneg d))
      (mul_nonneg (mul_nonneg hc₂ (Real.sqrt_nonneg Q)) hd))
    (mul_nonneg (mul_nonneg (by positivity) hδ) (add_nonneg (sq_nonneg _) hN))

/-- Actual common variance transfer in polynomial form. `d` is the norm of the
constructed actual shrinkage difference, not an assumed comparison variable. -/
theorem actual_variance_comparison_polynomial (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    |actualVarianceEnergy k hk φ hlam x hMX h - featureFilterDimension k hk φ| ≤
      (4 * (1 + A ^ 2)) *
        ((1 + actualCovarianceDeviation k hk lam x) *
            ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖ ^ 2 +
          Real.sqrt (featureFilterDimension k hk φ) *
            ‖actualShrinkageDifferenceColumns k hk φ hlam hM x hMX hf h‖ +
          actualCovarianceDeviation k hk lam x *
            (featureFilterDimension k hk φ + empiricalEffectiveDimension (fun i => k (x i)) lam)) := by
  apply (actual_quantitative_variance_comparison k hk φ hlam hM x hMX hf h hδ).trans
  apply variance_source_rhs_le_polynomial (featureFilterDimension_nonneg k hk φ) _ (norm_nonneg _) (norm_nonneg _)
  apply tsum_nonneg
  intro i
  have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact (fun i => k (x i)))
    (empiricalCovariance_isPositive _) i
  exact div_nonneg ht (add_nonneg ht hlam.le)

end KernelSeq
