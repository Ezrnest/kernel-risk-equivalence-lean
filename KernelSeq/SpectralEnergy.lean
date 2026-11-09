import KernelFoundations.SpectralEnergy
import KernelSeq.CompactCalculus
import KernelSeq.SpectralWeights

/-!
# Spectral target energies as actual Hilbert norms

Connects the coefficient estimates in `SpectralWeights` to the actual compact
real-operator calculus by Parseval. This gives the weighted target norm
estimate for Lipschitz bias comparison. The full eigenspace index includes the
kernel; `TargetSupport` proves reduction to the positive spectrum under the
target support condition. `SequenceBenchmark` connects the actual singular
prediction basis with the manuscript's source-energy formula.
-/

namespace KernelSeq

export KernelFoundations (
  hilbertBasis_coefficients_sq_summable hilbertBasis_norm_sq_eq_tsum
  compactSpectralMultiplier_norm_sq_eq_tsum
)

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

namespace ResidualFilter

/-- The actual source weight is uniformly bounded on the population spectrum. -/
theorem residualWeight_abs_le_two {lam M α t : ℝ} {φ : ℝ → ℝ}
    (hf : SpectralFilter M φ) (hlam : 0 < lam) (hα : 0 ≤ α)
    (ht : t ∈ Set.Icc (0 : ℝ) M) : |residualWeight lam α φ t| ≤ 2 := by
  rw [abs_of_nonneg (residualWeight_nonneg hf hlam ht)]
  have hb := regularization_weight_mem hlam ht
  have hp := Real.rpow_le_one hb.1.le hb.2 (div_nonneg hα (by norm_num : (0 : ℝ) ≤ 2))
  have hres := hf.residual_abs_le_one ht
  have hr := le_abs_self (residual φ t)
  dsimp only [residualWeight]
  linarith

end ResidualFilter

/-- The actual `a_{lam,α}(T)` operator, with boundedness proved from filter
admissibility. This construction does not assume its weighted-target estimate. -/
noncomputable def compactResidualWeightOperator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) : H →L[ℝ] H :=
  compactSpectralMultiplier T hc hp (residualWeight lam α φ) 2 (by norm_num)
    (fun _ ht => ResidualFilter.residualWeight_abs_le_two hf hlam hα ⟨ht.1, ht.2.trans hM⟩)

/-- The weighted norm bound for the population operator and target in the
Lipschitz bias comparison.
Square summability and all weighted-series convergence are derived. -/
theorem compactResidualWeightOperator_norm_sq_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖T‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : H) :
    ‖compactResidualWeightOperator T hc hp φ hlam hα hM hf f‖ ^ 2 ≤
      (A + 1) ^ 2 * ∑' i : CompactSpectralIndex T,
        (lam / (i.1 + lam)) ^ α *
          (compactEigenbasis T hc hp.isSymmetric).repr f i ^ 2 := by
  rw [compactResidualWeightOperator, compactSpectralMultiplier_norm_sq_eq_tsum]
  apply tsum_residualWeight_coefficients_le _ _ hf h hlam hα hαρ
  · intro i
    exact ⟨compactEigenvalue_nonneg T hc hp i,
      ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)).trans hM⟩
  · exact hilbertBasis_coefficients_sq_summable _ f

end KernelSeq
