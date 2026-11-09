import KernelSeq.InteractionSchur
import KernelSeq.ThetaSchur
import KernelSeq.ChiMikhlin

/-!
# The filter-specific logarithmic interaction multiplier

The manuscript's scalar contract now supplies every profile bound used in
the three-term Schur estimate. The special θ Fourier theorem and χ Mikhlin
theorem are proved locally. Only the two general finite analytic leaves are
inputs to the resulting actual infinite-dimensional multiplier estimate.
-/

open MeasureTheory

namespace KernelSeq
noncomputable section

universe uι uκ uH uE
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def actualLogInteractionGrid (α : ℝ) (φ : ℝ → ℝ) (u : κ → ℝ) (v : ι → ℝ) : κ → ι → ℝ :=
  fun i j => logarithmicInteractionKernel α φ (u i) (v j)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem actualLogInteractionGrid_factorization {M : ℝ} (hM : 0 ≤ M)
    (α : ℝ) (φ : ℝ → ℝ) (u : κ → ℝ) (v : ι → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) M) (hv : ∀ j, v j ∈ Set.Icc (0 : ℝ) M) :
    actualLogInteractionGrid α φ u v =
      factorizedInteractionGrid
        (extendedLogProfile M hM (logInteractionInverseProfile φ))
        (extendedLogProfile M hM (logInteractionResidualProfile α φ))
        (interactionTheta α) (fun t s => interactionChi α (t - s))
        (fun i => Real.log (1 + u i)) (fun j => Real.log (1 + v j)) := by
  funext i j
  have hx : Real.log (1 + u i) ∈ ResidualFilter.logDomain 1 M := by
    simpa only [div_one] using ResidualFilter.log_coordinate_mem (by norm_num : (0 : ℝ) < 1) (hu i)
  have hy : Real.log (1 + v j) ∈ ResidualFilter.logDomain 1 M := by
    simpa only [div_one] using ResidualFilter.log_coordinate_mem (by norm_num : (0 : ℝ) < 1) (hv j)
  have hxu : Real.exp (Real.log (1 + u i)) - 1 = u i := by
    rw [Real.exp_log (by linarith [(hu i).1])]
    ring
  have hyv : Real.exp (Real.log (1 + v j)) - 1 = v j := by
    rw [Real.exp_log (by linarith [(hv j).1])]
    ring
  change logarithmicInteractionKernel α φ (u i) (v j) = _
  conv_lhs => rw [← hxu, ← hyv]
  rw [logarithmicInteractionKernel_factorization]
  simp only [factorizedInteractionGrid, dividedDifference, offDiagonalGridKernel,
    interactionChiOffDiagonal,
    extendedLogProfile_eq hM (logInteractionInverseProfile φ) hx,
    extendedLogProfile_eq hM (logInteractionInverseProfile φ) hy,
    extendedLogProfile_eq hM (logInteractionResidualProfile α φ) hx,
    extendedLogProfile_eq hM (logInteractionResidualProfile α φ) hy]

/-- A scalar bound for the actual kernel, uniform over the spectral interval. -/
def actualLogInteractionGridBound (α ρ A BF : ℝ) : ℝ :=
  A * interactionThetaFourierL1 α * (A * (1 + ρ - α / 2)) +
    A * interactionThetaFourierL1 α * BF + A ^ 2 * chiMikhlinBound α

/-- This constant is independent of the inverse-profile Lipschitz constant,
the spectral upper bound and the auxiliary cutoff. -/
def actualLogInteractionConstant (CL CH α ρ A : ℝ) : ℝ :=
  interactionProfileConstant CL CH A (A * (1 + ρ - α / 2))
    (interactionThetaFourierL1 α) (chiMikhlinBound α)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem actualLogInteractionGrid_norm_le {M α ρ A BF : ℝ} {φ : ℝ → ℝ}
    (hM : 0 ≤ M) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hφ : ResidualFilter.SpectralFilter M φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain 1 M, ∀ t ∈ ResidualFilter.logDomain 1 M,
      |ResidualFilter.inverseProfile 1 φ s - ResidualFilter.inverseProfile 1 φ t| ≤ BF * |s - t|)
    (u : κ → ℝ) (v : ι → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) M) (hv : ∀ j, v j ∈ Set.Icc (0 : ℝ) M) (i : κ) (j : ι) :
    ‖actualLogInteractionGrid α φ u v i j‖ ≤ actualLogInteractionGridBound α ρ A BF := by
  rw [actualLogInteractionGrid_factorization hM α φ u v hu hv]
  have hA := h.constant_nonneg (by norm_num : (0 : ℝ) < 1) hM
  have hLP : 0 ≤ A * (1 + ρ - α / 2) := mul_nonneg hA (by linarith)
  have hχ := interactionChi_hms hα0.le (by linarith : α ≤ 2)
  apply factorizedInteractionGrid_norm_le _ _ _ _ hA hLP hBF
    (interactionThetaFourierL1_nonneg α) hχ.bound_nonneg
  · exact extendedLogProfile_abs_le hM _ (fun t ht => logInteractionInverseProfile_abs_le h ht)
  · exact extendedLogProfile_abs_le hM _ (fun t ht => logInteractionResidualProfile_abs_le h hαρ ht)
  · exact extendedLogProfile_nonneg hM _ (fun t ht => logInteractionResidualProfile_nonneg hφ hM ht)
  · intro t
    simpa only [Real.norm_eq_abs] using interactionTheta_norm_le_fourierL1 hα0 hα1 t
  · exact hχ.size_bound
  · exact extendedLogProfile_lipschitz hM _ hLP
      (fun s hs t ht => logInteractionResidualProfile_lipschitz h hαρ hs ht)
  · exact extendedLogProfile_lipschitz hM _ hBF (by
      intro s hs t ht
      simpa only [logInteractionInverseProfile_eq] using hFlip s hs t ht)

theorem actualLogInteractionGrid_schatten_le {CL CH M α ρ A BF p K : ℝ} {φ : ℝ → ℝ}
    (hLip : FiniteLipschitzSchur.{uι, uκ, uH, uE} CL)
    (hHMS : FiniteHMS.{uι, uκ, uH, uE} CH)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (hM : 0 ≤ M) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hφ : ResidualFilter.SpectralFilter M φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain 1 M, ∀ t ∈ ResidualFilter.logDomain 1 M,
      |ResidualFilter.inverseProfile 1 φ s - ResidualFilter.inverseProfile 1 φ t| ≤ BF * |s - t|)
    (u : κ → ℝ) (v : ι → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) M) (hv : ∀ j, v j ∈ Set.Icc (0 : ℝ) M)
    (hK : 0 ≤ K) (hgrid : ∀ i j, ‖actualLogInteractionGrid α φ u v i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) (hp : 2 ≤ p) :
    hsSchattenNorm b (hsSchurMultiplier a (actualLogInteractionGrid α φ u v) K hK hgrid c) p ≤
      actualLogInteractionConstant CL CH α ρ A * (1 + BF) * p * hsSchattenNorm b c p := by
  have heq := actualLogInteractionGrid_factorization hM α φ u v hu hv
  have hgrid' := hgrid
  simp only [heq] at hgrid'
  have hA := h.constant_nonneg (by norm_num : (0 : ℝ) < 1) hM
  have hLP : 0 ≤ A * (1 + ρ - α / 2) := mul_nonneg hA (by linarith)
  have hχ := interactionChi_hms hα0.le (by linarith : α ≤ 2)
  have ht := factorizedInteraction_schatten_le hLip hHMS b a
    (extendedLogProfile M hM (logInteractionInverseProfile φ))
    (extendedLogProfile M hM (logInteractionResidualProfile α φ))
    (interactionTheta α) (fun t s => interactionChi α (t - s))
    (interactionThetaFourierDensity α) (interactionThetaFourierDensity_integrable hα0 hα1)
    (interactionTheta_real_density_integral hα0 hα1)
    hA (extendedLogProfile_abs_le hM _ (fun t ht => logInteractionInverseProfile_abs_le h ht))
    (extendedLogProfile_abs_le hM _ (fun t ht => logInteractionResidualProfile_abs_le h hαρ ht))
    (extendedLogProfile_nonneg hM _ (fun t ht => logInteractionResidualProfile_nonneg hφ hM ht))
    hLP hBF
    (extendedLogProfile_lipschitz hM _ hLP
      (fun s hs t ht => logInteractionResidualProfile_lipschitz h hαρ hs ht))
    (extendedLogProfile_lipschitz hM _ hBF (by
      intro s hs t ht
      simpa only [logInteractionInverseProfile_eq] using hFlip s hs t ht))
    hχ (fun i => Real.log (1 + u i)) (fun j => Real.log (1 + v j)) hK hgrid' c hp
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right
    (interactionSchurConstant_le_profile hLip.constant_nonneg hHMS.constant_nonneg
      hp hA hLP hBF (interactionThetaFourierL1_nonneg α) hχ.bound_nonneg)
        (hsSchattenNorm_nonneg b c p))
  simpa only [heq, actualLogInteractionConstant, interactionThetaFourierL1] using hfinal

end
end KernelSeq
