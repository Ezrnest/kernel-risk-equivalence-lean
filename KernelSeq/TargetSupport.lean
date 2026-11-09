import KernelFoundations.TargetSupport
import KernelSeq.SpectralEnergy

/-!
# Positive-spectrum energies for residual filters
-/

namespace KernelSeq

export KernelFoundations (
  regularized_target_positive_summable
  PositiveSpectralIndex closure_range_self_comp_adjoint
  inner_zero_of_mem_closure_range_of_self_comp_adjoint_eq_zero
  compactEigenbasis_zero_coefficient tsum_spectral_coefficients_eq_positive
  norm_sq_eq_positive_spectral_coefficients
  summable_positive_spectral_coefficients
  compactSpectralMultiplier_positive_energy_summable
  compactSpectralMultiplier_norm_sq_eq_positive
  regularized_target_series_eq_positive
  compactEigenbasis_mem_range_of_positive positiveSpectralIndex_countable
)

open Submodule TopologicalSpace

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The manuscript's residual bias is exactly a positive-spectrum energy. -/
theorem compactResidualOperator_norm_sq_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {M : ℝ} (hM : ‖S.comp S.adjoint‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hM hfilter f‖ ^ 2 =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        ResidualFilter.residual φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  exact compactSpectralMultiplier_norm_sq_eq_positive S hc _ _ _ _ hf

/-- The auxiliary weighted residual energy also reduces to the positive spectrum. -/
theorem compactResidualWeightOperator_norm_sq_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hM : ‖S.comp S.adjoint‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualWeightOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hM hfilter f‖ ^ 2 =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        residualWeight lam α φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  exact compactSpectralMultiplier_norm_sq_eq_positive S hc _ _ _ _ hf

/-- The actual weighted target estimate now has exactly the positive-spectrum
source energy used in the paper, with summability inherited from Parseval. -/
theorem compactResidualWeightOperator_norm_sq_le_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {lam M ρ A α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖S.comp S.adjoint‖ ≤ M) (hfilter : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualWeightOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hM hfilter f‖ ^ 2 ≤
      (A + 1) ^ 2 * ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        (lam / (i.1.1 + lam)) ^ α * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  rw [← regularized_target_series_eq_positive S hc hf]
  exact compactResidualWeightOperator_norm_sq_le (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hαρ hM hfilter h f

end KernelSeq
