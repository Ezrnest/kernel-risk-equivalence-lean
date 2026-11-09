import KernelSeq.FixedSymbolRieszRepresentation
import KernelSeq.AngularPlanarRiesz

/-!
# Actual planar Riesz representation and dominated partial symbols

The rotation coefficients use the actual rotated anisotropic planar Riesz
kernel. Nonzero frequencies use the proved angular identification; at zero
each genuine planar kernel is zero, so every coefficient is zero directly.
No pointwise angular identification at zero is asserted. Absolute rotation
weights give true uniform bounds on all finite partial symbols.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
namespace KernelSeq
noncomputable section

/-- The actual sine-weighted average of the nth rotated planar Riesz kernel. -/
def fixedPlanarRieszAverage (n : ℕ) (ξ : ℝ × ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
    rotatedAnisotropicRieszSymbol (angularRieszAnisotropy n) φ ξ *
      Real.sin (((n + 1 : ℕ) : ℝ) * φ)

@[simp] theorem fixedPlanarRieszAverage_zero (n : ℕ) : fixedPlanarRieszAverage n 0 = 0 := by
  simp only [fixedPlanarRieszAverage, rotatedAnisotropicRieszSymbol_zero, zero_mul,
    intervalIntegral.integral_zero, mul_zero]

/-- Actual angular conversion, used only at nonzero frequencies. -/
theorem fixedPlanarRieszAverage_eq_angular (n : ℕ) (ξ : ℝ × ℝ) (hξ : ξ ≠ 0) :
    fixedPlanarRieszAverage n ξ = (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
      angularRieszProfile (angularRieszAnisotropy n)
        (2 * Complex.arg (⟨ξ.1, ξ.2⟩ : ℂ) - φ) * Real.sin (((n + 1 : ℕ) : ℝ) * φ) := by
  simp only [fixedPlanarRieszAverage, rotatedAnisotropicRieszSymbol_eq_angular _ _ _ hξ]

/-- The actual planar integrand is continuous in the rotation angle,
including at zero frequency where it is genuinely zero. -/
theorem fixedPlanarRieszAverage_integrand_continuous (n : ℕ) (ξ : ℝ × ℝ) :
    Continuous (fun φ : ℝ => rotatedAnisotropicRieszSymbol (angularRieszAnisotropy n) φ ξ *
      Real.sin (((n + 1 : ℕ) : ℝ) * φ)) :=
  (rotatedAnisotropicRieszSymbol_continuous (angularRieszAnisotropy_mem n).1
    (angularRieszAnisotropy_mem n).2 ξ).mul (by fun_prop)

/-- The genuine average is bounded by one, from the actual kernel and
sine bounds and the exact normalization by one period. -/
theorem fixedPlanarRieszAverage_abs_le_one (n : ℕ) (ξ : ℝ × ℝ) :
    |fixedPlanarRieszAverage n ξ| ≤ 1 := by
  have hb (φ : ℝ) : ‖rotatedAnisotropicRieszSymbol (angularRieszAnisotropy n) φ ξ *
      Real.sin (((n + 1 : ℕ) : ℝ) * φ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (rotatedAnisotropicRieszSymbol_abs_le _ _ ξ) (Real.abs_sin_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun φ _ => hb φ)
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos hp, one_mul] at hi
  rw [fixedPlanarRieszAverage, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * Real.pi) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 1 := by field_simp [Real.pi_ne_zero]

/-- The actual fixed planar symbol is the genuine sum of its actual
rotated anisotropic Riesz averages. The zero-frequency branch is separate. -/
theorem hasSum_fixedPlanarRiesz (ξ : ℝ × ℝ) :
    HasSum (fun n : ℕ => fixedSymbolRieszWeight n * fixedPlanarRieszAverage n ξ)
      (lipschitzEvenSymbol ξ.1 ξ.2) := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : lipschitzEvenSymbol (0 : ℝ) 0 = 0 := by simp [lipschitzEvenSymbol]
    simp only [Prod.fst_zero, Prod.snd_zero, fixedPlanarRieszAverage_zero, mul_zero, hz]
    exact hasSum_zero
  · simpa only [fixedPlanarRieszAverage_eq_angular _ _ hξ] using
      hasSum_lipschitzEvenSymbol_rotation_Riesz ξ.1 ξ.2

theorem lipschitzEvenSymbol_eq_tsum_fixedPlanarRiesz (ξ : ℝ × ℝ) :
    lipschitzEvenSymbol ξ.1 ξ.2 = ∑' n : ℕ, fixedSymbolRieszWeight n * fixedPlanarRieszAverage n ξ :=
  (hasSum_fixedPlanarRiesz ξ).tsum_eq.symm

/-- Absolute summability of the actual planar expansion follows from the
already proved summable weights and actual average bound. -/
theorem fixedPlanarRiesz_terms_abs_summable (ξ : ℝ × ℝ) :
    Summable (fun n : ℕ => |fixedSymbolRieszWeight n * fixedPlanarRieszAverage n ξ|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ fixedSymbolRieszWeight_abs_summable
  intro n
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (fixedPlanarRieszAverage_abs_le_one n ξ) (abs_nonneg _)).trans_eq (mul_one _)

/-- The actual finite partial planar symbol. -/
def fixedPlanarRieszPartialSymbol (N : ℕ) (ξ : ℝ × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, fixedSymbolRieszWeight n * fixedPlanarRieszAverage n ξ

@[simp] theorem fixedPlanarRieszPartialSymbol_zero (N : ℕ) : fixedPlanarRieszPartialSymbol N 0 = 0 := by
  simp only [fixedPlanarRieszPartialSymbol, fixedPlanarRieszAverage_zero, mul_zero, Finset.sum_const_zero]

/-- Genuine pointwise convergence of the actual finite planar symbols. -/
theorem fixedPlanarRieszPartialSymbol_tendsto (ξ : ℝ × ℝ) :
    Tendsto (fun N : ℕ => fixedPlanarRieszPartialSymbol N ξ) atTop
      (𝓝 (lipschitzEvenSymbol ξ.1 ξ.2)) :=
  (hasSum_fixedPlanarRiesz ξ).tendsto_sum_nat

/-- One actual bound dominates every finite partial symbol uniformly in
the number of harmonics and in all planar frequencies, including zero. -/
theorem fixedPlanarRieszPartialSymbol_abs_le (N : ℕ) (ξ : ℝ × ℝ) :
    |fixedPlanarRieszPartialSymbol N ξ| ≤ ∑' n : ℕ, |fixedSymbolRieszWeight n| := by
  unfold fixedPlanarRieszPartialSymbol
  calc
    _ ≤ ∑ n ∈ Finset.range N, |fixedSymbolRieszWeight n * fixedPlanarRieszAverage n ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, |fixedSymbolRieszWeight n| := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (fixedPlanarRieszAverage_abs_le_one n ξ) (abs_nonneg _)).trans_eq (mul_one _)
    _ ≤ _ := fixedSymbolRieszWeight_abs_summable.sum_le_tsum _ (fun _ _ => abs_nonneg _)

end
end KernelSeq
