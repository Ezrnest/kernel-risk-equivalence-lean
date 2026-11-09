import KernelSeq.FourierSchur
import KernelSeq.UniversalThetaRegularity

/-!
# The actual universal theta Schur multiplier

The Fourier density is constructed from the manuscript's actual theta profile.
The multiplier estimate applies to arbitrary real Hilbert bases and every `p ≥ 2`,
with one constant depending only on `α`. No Fourier or multiplier certificate is an input.
-/

open MeasureTheory

namespace KernelSeq

noncomputable section

/-- The actual finite Fourier `L¹` norm of the universal profile. -/
def interactionThetaFourierL1 (α : ℝ) : ℝ := ∫ ξ : ℝ, ‖interactionThetaFourierDensity α ξ‖

/-- A named constant independent of the Schatten exponent and all spectral grids. -/
def interactionThetaSchurConstant (α : ℝ) : ℝ := 4 * interactionThetaFourierL1 α

theorem interactionThetaFourierL1_nonneg (α : ℝ) : 0 ≤ interactionThetaFourierL1 α :=
  integral_nonneg fun _ => norm_nonneg _

theorem interactionThetaSchurConstant_nonneg (α : ℝ) : 0 ≤ interactionThetaSchurConstant α :=
  mul_nonneg (by norm_num) (interactionThetaFourierL1_nonneg α)

/-- The genuine scalar bound follows from the derived Fourier representation. -/
theorem interactionTheta_norm_le_fourierL1 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    ‖interactionTheta α z‖ ≤ interactionThetaFourierL1 α := by
  rw [interactionTheta_real_density_integral hα0 hα1 z]
  exact realFourierProfile_norm_le _ (interactionThetaFourierDensity_integrable hα0 hα1) z

theorem one_le_interactionThetaFourierL1 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    1 ≤ interactionThetaFourierL1 α := by
  simpa [interactionTheta] using
    interactionTheta_norm_le_fourierL1 hα0 hα1 0

/-- The named constant is positive: the true profile has value one at zero. -/
theorem interactionThetaSchurConstant_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    0 < interactionThetaSchurConstant α := by
  have h := one_le_interactionThetaFourierL1 hα0 hα1
  unfold interactionThetaSchurConstant
  linarith

variable {ι κ H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual bounded map on the complete Hilbert space of HS columns. -/
def interactionThetaGridMultiplier (a : HilbertBasis κ ℝ E) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ) :
    HilbertSchmidtColumns ι E →L[ℝ] HilbertSchmidtColumns ι E :=
  hsSchurMultiplier a (fun i j => interactionTheta α (x i - y j))
    (interactionThetaFourierL1 α) (interactionThetaFourierL1_nonneg α)
    (fun i j => interactionTheta_norm_le_fourierL1 hα0 hα1 (x i - y j))

omit [CompleteSpace H] in
/-- Exact cross-basis entries include all repeated spectral values and the nonzero diagonal. -/
theorem interactionThetaGridMultiplier_coefficient
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) (i : κ) (j : ι) :
    inner ℝ (a i) (hilbertSchmidtOperator b
      (interactionThetaGridMultiplier a hα0 hα1 x y c) (b j)) =
        interactionTheta α (x i - y j) * inner ℝ (a i) (hilbertSchmidtOperator b c (b j)) :=
  hsSchurMultiplier_coefficient a b _ _ _ _ c i j

/-- The original universal theta multiplier bound, uniform for every `p ≥ 2`. -/
theorem interactionTheta_grid_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (interactionThetaGridMultiplier a hα0 hα1 x y c) p ≤
      interactionThetaSchurConstant α * hsSchattenNorm b c p :=
  fourierRepresentedGrid_schatten_le b a (interactionTheta α) (interactionThetaFourierDensity α)
    (interactionThetaFourierDensity_integrable hα0 hα1)
    (interactionTheta_real_density_integral hα0 hα1) x y c hp

end
end KernelSeq
