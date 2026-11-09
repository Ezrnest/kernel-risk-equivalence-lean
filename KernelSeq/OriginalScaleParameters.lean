import KernelFoundations.Leverage
import KernelSeq.EffectiveDimension

/-!
# Residual comparison order
-/

open MeasureTheory Filter

namespace KernelSeq

export KernelFoundations (
  featureLeverageEssentialSup normalizedLeverage_isBoundedUnder
  normalizedLeverage_ae_le_essentialSup featureLeverageEssentialSup_nonneg
  featureLeverageEssentialSup_le_sq_bound_div
  featureLeverageEssentialSup_le_of_ae_le
  featureEffectiveDimension_le_essentialSup
)
noncomputable section

/-- The exact order αψ used in the manuscript's source-energy condition. -/
def residualComparisonOrder (ρ : ℝ) : ℝ := min (2 * ρ) 1

theorem residualComparisonOrder_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < residualComparisonOrder ρ := by
  exact lt_min (by linarith) (by norm_num)

theorem residualComparisonOrder_le_one (ρ : ℝ) : residualComparisonOrder ρ ≤ 1 :=
  min_le_right _ _

theorem residualComparisonOrder_half_le (ρ : ℝ) : residualComparisonOrder ρ / 2 ≤ ρ := by
  have h := min_le_left (2 * ρ) (1 : ℝ)
  dsimp only [residualComparisonOrder]
  linarith

end
end KernelSeq
