import KernelFoundations.RegularizedFeatures
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual covariance trace and effective dimension

Integrating Parseval for the actual feature map identifies the covariance
spectral trace and regularized effective dimension with feature norm integrals.
The eigenbasis, its eigenvalues, and the real inverse square root are constructed
from `T = S* S`; neither summability nor a trace identity is a premise. Only the
feature Hilbert space is assumed separable, never the prediction space `L²(μ)`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelFoundations

variable {X H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X}

omit [CompleteSpace H] in
/-- Parseval may be integrated for an actual L² feature. The series theorem
proves summability of the coordinate integrals from the integrable total norm;
no summability of those integrals is assumed. -/
theorem hasSum_integral_sq_hilbertBasis [Countable J] (b : HilbertBasis J ℝ H)
    (u : X → H) (hu : MemLp u 2 μ) :
    HasSum (fun i => ∫ x, inner ℝ (b i) (u x) ^ 2 ∂μ)
      (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  have hparseval (x : X) : HasSum (fun i => inner ℝ (b i) (u x) ^ 2) (‖u x‖ ^ 2) := by
    simpa only [real_inner_comm (u x), ← pow_two, real_inner_self_eq_norm_sq] using
      b.hasSum_inner_mul_inner (u x) (u x)
  apply hasSum_integral_of_dominated_convergence
    (fun i x => inner ℝ (b i) (u x) ^ 2)
  · intro i
    exact (hu.1.const_inner (𝕜 := ℝ) (c := b i)).pow 2
  · intro i
    exact Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)])
  · exact Eventually.of_forall (fun x => (hparseval x).summable)
  · have heq : (fun x => ∑' i, inner ℝ (b i) (u x) ^ 2) = (fun x => ‖u x‖ ^ 2) := by
      funext x
      exact (hparseval x).tsum_eq
    rw [heq]
    exact (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  · exact Eventually.of_forall hparseval

variable [IsProbabilityMeasure μ]

/-- The actual complete covariance eigenbasis index, including its zero eigenspace. -/
abbrev FeatureCovarianceIndex (k : X → H) (hk : MemLp k 2 μ) :=
  CompactSpectralIndex (populationCovariance (featureEmbedding μ k hk))

noncomputable def featureCovarianceBasis (k : X → H) (hk : MemLp k 2 μ) :
    HilbertBasis (FeatureCovarianceIndex k hk) ℝ H :=
  compactEigenbasis (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric

/-- Each coordinate second moment is its actual covariance eigenvalue. -/
theorem integral_sq_feature_coordinate (k : X → H) (hk : MemLp k 2 μ)
    (i : FeatureCovarianceIndex k hk) :
    (∫ x, inner ℝ (featureCovarianceBasis k hk i) (k x) ^ 2 ∂μ) = i.1 := by
  let S := featureEmbedding μ k hk
  let b := featureCovarianceBasis k hk
  have hcoord : (∫ x, inner ℝ (b i) (k x) ^ 2 ∂μ) = ‖S (b i)‖ ^ 2 := by
    rw [← integral_sq_L2]
    apply integral_congr_ae
    filter_upwards [featureEmbedding_ae μ k hk (b i)] with x hx
    rw [hx, real_inner_comm]
  rw [hcoord, S.apply_norm_sq_eq_inner_adjoint_right]
  change inner ℝ (b i) (populationCovariance S (b i)) = _
  have he := compactEigenbasis_eigen (populationCovariance S)
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive S).isSymmetric i
  change populationCovariance S (b i) = i.1 • b i at he
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    b.orthonormal.norm_eq_one, one_pow, mul_one]

/-- The real inverse-root coordinate second moment is `t/(t+λ)`. -/
theorem integral_sq_normalized_feature_coordinate (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) (i : FeatureCovarianceIndex k hk) :
    (∫ x, inner ℝ (featureCovarianceBasis k hk i)
      (featureRegularizedInvSqrt μ k hk lam (k x)) ^ 2 ∂μ) = i.1 / (i.1 + lam) := by
  have hcoord (x : X) : inner ℝ (featureCovarianceBasis k hk i)
      (featureRegularizedInvSqrt μ k hk lam (k x)) =
      (Real.sqrt (i.1 + lam))⁻¹ * inner ℝ (featureCovarianceBasis k hk i) (k x) := by
    simpa only [featureCovarianceBasis, featureRegularizedInvSqrt,
      HilbertBasis.repr_apply_apply] using
      compactRegularizedInvSqrt_repr (populationCovariance (featureEmbedding μ k hk))
        (populationCovariance_feature_isCompact μ k hk)
        (populationCovariance_isPositive (featureEmbedding μ k hk)) lam hlam (k x) i
  simp_rw [hcoord, mul_pow]
  rw [integral_const_mul, integral_sq_feature_coordinate, inv_pow,
    Real.sq_sqrt (add_nonneg (compactEigenvalue_nonneg _
      (populationCovariance_feature_isCompact μ k hk)
      (populationCovariance_isPositive (featureEmbedding μ k hk)) i) hlam.le)]
  ring

/-- The constructed normalizer preserves square integrability of the actual
feature map. This integrability statement itself needs no sign of `lam`. -/
theorem memLp_normalized_feature (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    MemLp (fun x => featureRegularizedInvSqrt μ k hk lam (k x)) 2 μ :=
  (featureRegularizedInvSqrt μ k hk lam).comp_memLp' hk

theorem integrable_normalizedLeverage (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    Integrable (normalizedLeverage k hk lam) μ :=
  (memLp_two_iff_integrable_sq_norm (memLp_normalized_feature k hk lam).1).mp
    (memLp_normalized_feature k hk lam)

variable [TopologicalSpace.SeparableSpace H]

/-- Countability is derived from separability of the feature space, independently
of any separability of `L²(μ)` or regularity of the design measurable space. -/
theorem featureCovarianceIndex_countable (k : X → H) (hk : MemLp k 2 μ) :
    Countable (FeatureCovarianceIndex k hk) :=
  compactSpectralIndex_countable _ (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric

/-- Actual covariance eigenvalues have the finite feature second moment as their
sum. Summability is a conclusion of integrated Parseval. -/
theorem hasSum_featureCovarianceEigenvalues (k : X → H) (hk : MemLp k 2 μ) :
    HasSum (fun i : FeatureCovarianceIndex k hk => i.1) (∫ x, ‖k x‖ ^ 2 ∂μ) := by
  letI := featureCovarianceIndex_countable k hk
  have hs := hasSum_integral_sq_hilbertBasis (featureCovarianceBasis k hk) k hk
  have ht : (fun i => ∫ x, inner ℝ (featureCovarianceBasis k hk i) (k x) ^ 2 ∂μ) =
      (fun i : FeatureCovarianceIndex k hk => i.1) := by
    funext i
    exact integral_sq_feature_coordinate k hk i
  rw [ht] at hs
  exact hs

theorem summable_featureCovarianceEigenvalues (k : X → H) (hk : MemLp k 2 μ) :
    Summable (fun i : FeatureCovarianceIndex k hk => i.1) :=
  (hasSum_featureCovarianceEigenvalues k hk).summable

/-- The spectral trace of the actual positive covariance; finiteness is proved
by `hasSum_featureCovarianceEigenvalues`, not incorporated as input data. -/
noncomputable def featureCovarianceTrace (k : X → H) (hk : MemLp k 2 μ) : ℝ :=
  ∑' i : FeatureCovarianceIndex k hk, i.1

theorem featureCovarianceTrace_eq_integral (k : X → H) (hk : MemLp k 2 μ) :
    featureCovarianceTrace k hk = ∫ x, ‖k x‖ ^ 2 ∂μ :=
  (hasSum_featureCovarianceEigenvalues k hk).tsum_eq

/-- The first effective dimension of the actual covariance. -/
noncomputable def featureEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) : ℝ :=
  ∑' i : FeatureCovarianceIndex k hk, i.1 / (i.1 + lam)

/-- The effective-dimension series genuinely sums to the actual integrated
leverage. Its finiteness follows from the normalized feature's L² property. -/
theorem hasSum_featureEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    HasSum (fun i : FeatureCovarianceIndex k hk => i.1 / (i.1 + lam))
      (∫ x, normalizedLeverage k hk lam x ∂μ) := by
  letI := featureCovarianceIndex_countable k hk
  have hs := hasSum_integral_sq_hilbertBasis (featureCovarianceBasis k hk)
    (fun x => featureRegularizedInvSqrt μ k hk lam (k x))
    (memLp_normalized_feature k hk lam)
  have ht : (fun i => ∫ x, inner ℝ (featureCovarianceBasis k hk i)
      (featureRegularizedInvSqrt μ k hk lam (k x)) ^ 2 ∂μ) =
      (fun i : FeatureCovarianceIndex k hk => i.1 / (i.1 + lam)) := by
    funext i
    exact integral_sq_normalized_feature_coordinate k hk lam hlam i
  rw [ht] at hs
  exact hs

theorem summable_featureEffectiveDimension (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    Summable (fun i : FeatureCovarianceIndex k hk => i.1 / (i.1 + lam)) :=
  (hasSum_featureEffectiveDimension k hk lam hlam).summable

theorem integral_normalizedLeverage_eq_featureEffectiveDimension
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) :
    (∫ x, normalizedLeverage k hk lam x ∂μ) = featureEffectiveDimension k hk lam :=
  (hasSum_featureEffectiveDimension k hk lam hlam).tsum_eq.symm

/-- The explicit spectral-series identity for the actual real inverse root. -/
theorem integral_featureRegularizedInvSqrt_sq_eq_tsum (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    (∫ x, ‖featureRegularizedInvSqrt μ k hk lam (k x)‖ ^ 2 ∂μ) =
      ∑' i : FeatureCovarianceIndex k hk, i.1 / (i.1 + lam) :=
  integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam

theorem featureCovarianceTrace_nonneg (k : X → H) (hk : MemLp k 2 μ) :
    0 ≤ featureCovarianceTrace k hk := by
  rw [featureCovarianceTrace_eq_integral]
  exact integral_nonneg (fun x => sq_nonneg _)

theorem featureEffectiveDimension_nonneg (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) : 0 ≤ featureEffectiveDimension k hk lam := by
  rw [← integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- The basic trace bound follows from the actual feature norm bound. -/
theorem featureCovarianceTrace_le_sq_bound (k : X → H) (hk : MemLp k 2 μ)
    (κ : ℝ) (hκ : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ κ ^ 2) :
    featureCovarianceTrace k hk ≤ κ ^ 2 := by
  rw [featureCovarianceTrace_eq_integral]
  calc
    _ ≤ ∫ _ : X, κ ^ 2 ∂μ := integral_mono_ae
      ((memLp_two_iff_integrable_sq_norm hk.1).mp hk) (integrable_const _) hκ
    _ = κ ^ 2 := by simp

/-- The effective dimension is bounded by the actual covariance trace divided
by regularization, via the proved real inverse-root estimate. -/
theorem featureEffectiveDimension_le_trace_div (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    featureEffectiveDimension k hk lam ≤ featureCovarianceTrace k hk / lam := by
  rw [← integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam,
    featureCovarianceTrace_eq_integral]
  calc
    _ ≤ ∫ x, ‖k x‖ ^ 2 / lam ∂μ := integral_mono_ae
      (integrable_normalizedLeverage k hk lam)
      (((memLp_two_iff_integrable_sq_norm hk.1).mp hk).div_const lam)
      (Eventually.of_forall (normalizedLeverage_le_norm_sq_div k hk lam hlam))
    _ = _ := integral_div lam (fun x => ‖k x‖ ^ 2)

theorem featureEffectiveDimension_le_sq_bound_div (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) (κ : ℝ)
    (hκ : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ κ ^ 2) :
    featureEffectiveDimension k hk lam ≤ κ ^ 2 / lam :=
  (featureEffectiveDimension_le_trace_div k hk lam hlam).trans
    (div_le_div_of_nonneg_right (featureCovarianceTrace_le_sq_bound k hk κ hκ) hlam.le)

end KernelFoundations
