import KernelSeq.CompactInteractionBound
import KernelSeq.InteractionSchurLipschitz

/-!
# Actual compact interaction without the general HMS theorem

The actual chi bound and finite-to-infinite extension supply the multiplier.
The compact DOI, eigenvalues, outside factors and mixed columns remain the
original constructions. Only dyadic finite Lipschitz bounds are external.
-/

namespace KernelSeq
noncomputable section

universe uH uI
variable {H : Type uH} {I : Type uI}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem compactInteractionKernelSchur_from_lipschitz {CL lam M ρ A α BF B : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hMT : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain lam M, ∀ t ∈ ResidualFilter.logDomain lam M,
      |ResidualFilter.inverseProfile lam φ s - ResidualFilter.inverseProfile lam φ t| ≤ BF * |s - t|)
    (m : ℕ) (hB : 0 ≤ B)
    (hkernel : ∀ i j, ‖compactLogInteractionKernel TX T lam α φ i j‖ ≤ B) :
    InteractionKernelSchurBound TX T hcX hc hpX hp lam α φ B hB hkernel
      (dyadicSchattenExponent m)
      (lipschitzInteractionConstant CL α ρ A * (1 + BF) * dyadicSchattenExponent m) := by
  intro d
  apply actualLogInteractionGrid_dyadic_from_lipschitz hLip
    (compactEigenbasis T hc hp.isSymmetric) (compactEigenbasis TX hcX hpX.isSymmetric)
    (div_nonneg ((norm_nonneg T).trans hMT) hlam.le)
    (localizedDimensionless_contract hlam h) (localizedDimensionless_spectralFilter hlam hf)
    hα0 hα1 hαρ hBF ?_ (fun i : CompactSpectralIndex TX => i.1 / lam)
    (fun j : CompactSpectralIndex T => j.1 / lam)
    (compactScaledEigenvalue_mem TX hcX hpX hlam hMX) (compactScaledEigenvalue_mem T hc hp hlam hMT)
    m hB hkernel d
  intro s hs t ht
  rw [localizedDimensionless_inverseProfile, localizedDimensionless_inverseProfile]
  exact hFlip s (by simpa only [ResidualFilter.logDomain, div_one] using hs)
    t (by simpa only [ResidualFilter.logDomain, div_one] using ht)

theorem compact_embedded_interaction_bound_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL) (b : HilbertBasis I ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α BF : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hMT : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ) (hBF : 0 ≤ BF)
    (hFlip : ∀ s ∈ ResidualFilter.logDomain lam M, ∀ t ∈ ResidualFilter.logDomain lam M,
      |ResidualFilter.inverseProfile lam φ s - ResidualFilter.inverseProfile lam φ t| ≤ BF * |s - t|)
    (m : ℕ) (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) (z : H) :
    ‖(compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hMT hf h *
        compactRegularizedSqrt T hc hp 0) z‖ ≤
      Real.sqrt 2 * lipschitzInteractionConstant CL α ρ A * (1 + BF) * dyadicSchattenExponent m *
        hsSchattenNorm b c (dyadicSchattenExponent m) *
        ‖compactResidualWeightOperator T hc hp φ hlam hα0.le hMT hf z‖ := by
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
  have hSchur := compactInteractionKernelSchur_from_lipschitz hLip TX T hcX hc hpX hp φ
    hlam hMX hMT hf h hα0 hα1 hαρ hBF hFlip m hB hk
  have ht := embedded_interaction_of_schur_bound b TX T hcX hc hpX hp φ hlam hMX hMT hf h
    hα0.le (dyadicSchattenExponent_ge_two m) hB hk hSchur hδ c hcK z
  simpa only [mul_assoc] using ht

end
end KernelSeq
