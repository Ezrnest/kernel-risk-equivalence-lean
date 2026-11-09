import KernelFoundations.EffectiveDimension
import Mathlib.MeasureTheory.Function.EssSup

/-!
# Essential supremum of regularized leverage
-/

open MeasureTheory Filter

namespace KernelFoundations
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual maximal normalized leverage, defined by the real essential
supremum. Its a.e. bound is proved below from the bounded kernel assumption. -/
def featureLeverageEssentialSup (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) : ℝ :=
  essSup (normalizedLeverage k hk lam) μ

theorem normalizedLeverage_isBoundedUnder (k : X → H) (hk : MemLp k 2 μ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    IsBoundedUnder (· ≤ ·) (ae μ) (normalizedLeverage k hk lam) :=
  ⟨κ ^ 2 / lam, normalizedLeverage_ae_le_of_sq_bound k hk lam hlam κ hκ⟩

theorem normalizedLeverage_ae_le_essentialSup (k : X → H) (hk : MemLp k 2 μ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ featureLeverageEssentialSup k hk lam :=
  ae_le_essSup (normalizedLeverage_isBoundedUnder k hk hlam hκ)

theorem featureLeverageEssentialSup_nonneg (k : X → H) (hk : MemLp k 2 μ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    0 ≤ featureLeverageEssentialSup k hk lam := by
  obtain ⟨y, hy⟩ := (normalizedLeverage_ae_le_essentialSup k hk hlam hκ).exists
  exact (sq_nonneg _).trans hy

theorem featureLeverageEssentialSup_le_sq_bound_div (k : X → H) (hk : MemLp k 2 μ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    featureLeverageEssentialSup k hk lam ≤ κ ^ 2 / lam := by
  exact essSup_le_of_ae_le _ (normalizedLeverage_ae_le_of_sq_bound k hk lam hlam κ hκ)
    (isCoboundedUnder_le_of_le (ae μ)
      (fun y => sq_nonneg ‖featureRegularizedInvSqrt μ k hk lam (k y)‖))

theorem featureLeverageEssentialSup_le_of_ae_le (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    featureLeverageEssentialSup k hk lam ≤ L :=
  essSup_le_of_ae_le _ hL (isCoboundedUnder_le_of_le (ae μ)
    (fun y => sq_nonneg ‖featureRegularizedInvSqrt μ k hk lam (k y)‖))

theorem featureEffectiveDimension_le_essentialSup [TopologicalSpace.SeparableSpace H]
    (k : X → H) (hk : MemLp k 2 μ)
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2) :
    featureEffectiveDimension k hk lam ≤ featureLeverageEssentialSup k hk lam := by
  rw [← integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam]
  have hi : Integrable (normalizedLeverage k hk lam) μ := integrable_normalizedLeverage k hk lam
  calc
    _ ≤ ∫ _ : X, featureLeverageEssentialSup k hk lam ∂μ :=
      integral_mono_ae hi (integrable_const _) (normalizedLeverage_ae_le_essentialSup k hk hlam hκ)
    _ = _ := by simp

end

end KernelFoundations
