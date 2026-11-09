import KernelFoundations.CompactSpectral
import KernelFoundations.CompactCovariance
import KernelFoundations.RKHSFeature

/-!
# Regularized feature maps and leverage
-/

open MeasureTheory

namespace KernelFoundations

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- The inverse square root of the actual feature covariance plus `lam I`.
It is used at positive `lam`, where the whitening identity below holds. -/
noncomputable def featureRegularizedInvSqrt (μ : Measure X) [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) lam

theorem featureRegularizedInvSqrt_isSelfAdjoint (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) : IsSelfAdjoint (featureRegularizedInvSqrt μ k hk lam) :=
  compactRegularizedInvSqrt_isSelfAdjoint _ _ _ _

theorem featureRegularizedInvSqrt_normalizes (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    featureRegularizedInvSqrt μ k hk lam *
      (populationCovariance (featureEmbedding μ k hk) + lam • (1 : H →L[ℝ] H)) *
        featureRegularizedInvSqrt μ k hk lam = 1 :=
  compactRegularizedInvSqrt_normalizes _ _ _ _ hlam

theorem featureRegularizedInvSqrt_norm_le (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖featureRegularizedInvSqrt μ k hk lam‖ ≤ 1 / Real.sqrt lam :=
  compactRegularizedInvSqrt_norm_le _ _ _ _ hlam

/-- The leverage is the squared norm of the actually whitened feature. -/
noncomputable def normalizedLeverage (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (y : X) : ℝ :=
  ‖featureRegularizedInvSqrt μ k hk lam (k y)‖ ^ 2

theorem normalizedLeverage_le_norm_sq_div (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) (y : X) :
    normalizedLeverage k hk lam y ≤ ‖k y‖ ^ 2 / lam := by
  have hb := (featureRegularizedInvSqrt μ k hk lam).le_of_opNorm_le
    (featureRegularizedInvSqrt_norm_le k hk lam hlam) (k y)
  change ‖featureRegularizedInvSqrt μ k hk lam (k y)‖ ^ 2 ≤ _
  calc
    _ ≤ (1 / Real.sqrt lam * ‖k y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hlam.le]; ring

/-- An a.e. diagonal/norm-square kernel bound gives the crude leverage bound. -/
theorem normalizedLeverage_ae_le_of_sq_bound (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) (κ : ℝ)
    (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ κ ^ 2 / lam := by
  filter_upwards [hκ] with y hy
  exact (normalizedLeverage_le_norm_sq_div k hk lam hlam y).trans
    (div_le_div_of_nonneg_right hy hlam.le)

theorem normalizedLeverage_ae_le_of_norm_bound (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) (κ : ℝ)
    (hκ : ∀ᵐ y ∂μ, ‖k y‖ ≤ κ) :
    ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ κ ^ 2 / lam := by
  apply normalizedLeverage_ae_le_of_sq_bound k hk lam hlam κ
  filter_upwards [hκ] with y hy
  exact pow_le_pow_left₀ (norm_nonneg _) hy 2

/-- For the canonical RKHS feature, the kernel diagonal itself bounds leverage.
Measurability and square integrability come from the actual measurable kernel. -/
theorem normalizedLeverage_rkhs_le [SecondCountableTopology H]
    [RKHS ℝ H X ℝ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ y, rkhsKernel (X := X) (H := H) y y ≤ κ ^ 2)
    (lam : ℝ) (hlam : 0 < lam) (y : X) :
    normalizedLeverage (rkhsFeature (X := X) (H := H))
      (rkhsFeature_memLp μ hK κ hκ hdiag) lam y ≤ κ ^ 2 / lam := by
  refine (normalizedLeverage_le_norm_sq_div _ _ lam hlam y).trans
    (div_le_div_of_nonneg_right ?_ hlam.le)
  simpa only [rkhsFeature_norm_sq] using hdiag y


end KernelFoundations
