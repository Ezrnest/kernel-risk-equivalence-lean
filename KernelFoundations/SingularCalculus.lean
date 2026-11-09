import KernelFoundations.SingularSystem

/-!
# Spectral multiplier calculus in the singular basis
-/

open MeasureTheory Submodule

namespace KernelFoundations

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem compactSpectralMultiplier_isSymmetric (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    (compactSpectralMultiplier T hc hp φ K hK hφ).IsSymmetric :=
  hilbertDiagonal_isSymmetric _ _ _ _ _

/-- Actual multiplier action on the coefficients of the singular prediction basis. -/
theorem predictionSingularBasis_multiplier_coefficient (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    (f : E) (i : PredictionSingularIndex S) :
    inner ℝ (predictionSingularBasis S hcT i : E)
      (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f) =
      φ i.1.1 * inner ℝ (predictionSingularBasis S hcT i : E) f := by
  calc
    _ = inner ℝ (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (predictionSingularBasis S hcT i : E)) f :=
      (compactSpectralMultiplier_isSymmetric _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ _ _).symm
    _ = _ := by
      rw [compactSpectralMultiplier_eigen _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (predictionSingularBasis_eigen S hcT i), inner_smul_left, conj_trivial]

/-- The actual multiplier preserves the source-supported prediction space. -/
theorem compactSpectralMultiplier_mem_predictionRange (S : H →L[ℝ] E)
    (hcL : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    compactSpectralMultiplier (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f ∈ PredictionRange S := by
  have hRange : S.adjoint.kerᗮ = PredictionRange S := by
    simpa only [ContinuousLinearMap.adjoint_adjoint, PredictionRange] using S.adjoint.orthogonal_ker
  rw [← hRange]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  have hzL : (S.comp S.adjoint) z = 0 := by
    change S (S.adjoint z) = 0
    rw [show S.adjoint z = 0 from hz, map_zero]
  have hfz := inner_zero_of_mem_closure_range_of_self_comp_adjoint_eq_zero S hf hzL
  calc
    _ = inner ℝ (compactSpectralMultiplier (S.comp S.adjoint) hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ z) f :=
      (compactSpectralMultiplier_isSymmetric _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ _ _).symm
    _ = 0 := by
      rw [compactSpectralMultiplier_eigen _ hcL
        (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ
          (show (S.comp S.adjoint) z = (0 : ℝ) • z by
            simpa only [zero_smul] using hzL), inner_smul_left, conj_trivial, hfz, mul_zero]

/-- Parseval in the actual supported singular basis gives the true multiplier
energy, with the positive eigenvalues and multiplicities of `T = S* S`. -/
theorem predictionSingularBasis_multiplier_norm_sq (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    ‖compactSpectralMultiplier (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f‖ ^ 2 =
      ∑' i : PredictionSingularIndex S,
        φ i.1.1 ^ 2 * inner ℝ (predictionSingularBasis S hcT i : E) f ^ 2 := by
  rw [predictionSingularBasis_parseval S hcT
    (compactSpectralMultiplier_mem_predictionRange S hcL φ K hK hφ hf)]
  apply tsum_congr
  intro i
  rw [predictionSingularBasis_multiplier_coefficient, mul_pow]

/-- Convergence of the displayed coefficient energy is a theorem about actual
coordinates, rather than a convention for possibly divergent `tsum`. -/
theorem predictionSingularBasis_multiplier_energy_summable (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S)) (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ PredictionRange S) :
    Summable (fun i : PredictionSingularIndex S =>
      φ i.1.1 ^ 2 * inner ℝ (predictionSingularBasis S hcT i : E) f ^ 2) := by
  have hs := predictionSingularBasis_coefficients_summable S hcT
    (compactSpectralMultiplier_mem_predictionRange S hcL φ K hK hφ hf)
  simpa only [predictionSingularBasis_multiplier_coefficient, mul_pow] using hs


end KernelFoundations
