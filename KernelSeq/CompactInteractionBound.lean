import KernelSeq.LogInteractionBound
import KernelSeq.EmbeddedInteraction

/-!
# The compact embedded-interaction bound from general finite analytic leaves

Specializes the proved scalar Fourier/Mikhlin/profile estimates to the actual
two compact covariance spectra, then invokes the proved DOI reconstruction.
No project-specific interaction, multiplier or coefficient identity is an input.
-/

namespace KernelSeq
noncomputable section

universe uH uI
variable {H : Type uH} {I : Type uI}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem compactScaledEigenvalue_mem (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) {lam M : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (i : CompactSpectralIndex T) : i.1 / lam ∈ Set.Icc (0 : ℝ) (M / lam) := by
  refine ⟨div_nonneg (compactEigenvalue_nonneg T hc hp i) hlam.le, ?_⟩
  apply div_le_div_of_nonneg_right _ hlam.le
  exact ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)).trans hM

theorem compactLogInteractionKernel_norm_le (TX T : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α BF : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hMT : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain lam M, ∀ t ∈ ResidualFilter.logDomain lam M,
      |ResidualFilter.inverseProfile lam φ s - ResidualFilter.inverseProfile lam φ t| ≤ BF * |s - t|)
    (i : CompactSpectralIndex TX) (j : CompactSpectralIndex T) :
    ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ actualLogInteractionGridBound α ρ A BF := by
  apply actualLogInteractionGrid_norm_le
    (div_nonneg ((norm_nonneg T).trans hMT) hlam.le)
    (localizedDimensionless_contract hlam h) (localizedDimensionless_spectralFilter hlam hf)
    hα0 hα1 hαρ hBF ?_ (fun i : CompactSpectralIndex TX => i.1 / lam)
    (fun j : CompactSpectralIndex T => j.1 / lam)
    (compactScaledEigenvalue_mem TX hcX hpX hlam hMX) (compactScaledEigenvalue_mem T hc hp hlam hMT)
  intro s hs t ht
  rw [localizedDimensionless_inverseProfile, localizedDimensionless_inverseProfile]
  exact hFlip s (by simpa only [ResidualFilter.logDomain, div_one] using hs)
    t (by simpa only [ResidualFilter.logDomain, div_one] using ht)

theorem compactInteractionKernelSchur_from_finite {CL CH lam M ρ A α BF p B : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hMT : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain lam M, ∀ t ∈ ResidualFilter.logDomain lam M,
      |ResidualFilter.inverseProfile lam φ s - ResidualFilter.inverseProfile lam φ t| ≤ BF * |s - t|)
    (hp2 : 2 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B) :
    InteractionKernelSchurBound TX T hcX hc hpX hp lam α φ B hB hkernel p
      (actualLogInteractionConstant CL CH α ρ A * (1 + BF) * p) := by
  intro d
  apply actualLogInteractionGrid_schatten_le hLip hHMS
    (compactEigenbasis T hc hp.isSymmetric) (compactEigenbasis TX hcX hpX.isSymmetric)
    (div_nonneg ((norm_nonneg T).trans hMT) hlam.le)
    (localizedDimensionless_contract hlam h) (localizedDimensionless_spectralFilter hlam hf)
    hα0 hα1 hαρ hBF ?_ (fun i : CompactSpectralIndex TX => i.1 / lam)
    (fun j : CompactSpectralIndex T => j.1 / lam)
    (compactScaledEigenvalue_mem TX hcX hpX hlam hMX) (compactScaledEigenvalue_mem T hc hp hlam hMT)
    hB hkernel d hp2
  intro s hs t ht
  rw [localizedDimensionless_inverseProfile, localizedDimensionless_inverseProfile]
  exact hFlip s (by simpa only [ResidualFilter.logDomain, div_one] using hs)
    t (by simpa only [ResidualFilter.logDomain, div_one] using ht)

theorem compact_embedded_interaction_bound {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α BF p : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hMT : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain lam M, ∀ t ∈ ResidualFilter.logDomain lam M,
      |ResidualFilter.inverseProfile lam φ s - ResidualFilter.inverseProfile lam φ t| ≤ BF * |s - t|)
    (hp2 : 2 ≤ p) (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) (z : H) :
    ‖(compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hMT hf h *
        compactRegularizedSqrt T hc hp 0) z‖ ≤
      Real.sqrt 2 * actualLogInteractionConstant CL CH α ρ A * (1 + BF) * p *
        hsSchattenNorm b c p * ‖compactResidualWeightOperator T hc hp φ hlam hα0.le hMT hf z‖ := by
  have hA := h.constant_nonneg hlam ((norm_nonneg T).trans hMT)
  have hB : 0 ≤ actualLogInteractionGridBound α ρ A BF := by
    unfold actualLogInteractionGridBound
    have hLP : 0 ≤ A * (1 + ρ - α / 2) := mul_nonneg hA (by linarith)
    have hW := interactionThetaFourierL1_nonneg α
    have hχ := chiMikhlinBound_nonneg α
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hA hW) hLP)
      (mul_nonneg (mul_nonneg hA hW) hBF)) (mul_nonneg (sq_nonneg _) hχ)
  have hk := compactLogInteractionKernel_norm_le TX T hcX hc hpX hp φ hlam hMX hMT
    hf h hα0 hα1 hαρ hBF hFlip
  have hSchur := compactInteractionKernelSchur_from_finite hLip hHMS TX T hcX hc hpX hp φ
    hlam hMX hMT hf h hα0 hα1 hαρ hBF hFlip hp2 hB hk
  have ht := embedded_interaction_of_schur_bound b TX T hcX hc hpX hp φ hlam hMX hMT hf h
    hα0.le hp2 hB hk hSchur hδ c hcK z
  simpa only [mul_assoc] using ht

end
end KernelSeq
