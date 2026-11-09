import KernelSeq.MatrixLaplacePotential
import KernelSeq.BernsteinMgfFactor

/-!
# Scalar optimization of the actual matrix trace Laplace method

The proved potential tail inequality gives the exact intrinsic Bernstein
prefactor and exponent from an explicit trace-moment bound. This is only the
Laplace conversion: the trace moment of an independent matrix sum is not
proved or assumed to be available automatically here.
-/

open MeasureTheory Filter

namespace KernelSeq
noncomputable section

theorem exp_symmetric_remainder_ge_quarter_exp {z : ℝ} (hz : 1 ≤ z) :
    Real.exp z / 4 ≤ Real.exp z + Real.exp (-z) - 2 := by
  have he : 2 ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  have hq : Real.exp (-z) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
  have hq0 := (Real.exp_pos (-z)).le
  have hs : 1 / 4 ≤ (1 - Real.exp (-z)) ^ 2 := by nlinarith
  have hid : Real.exp z * (1 - Real.exp (-z)) ^ 2 =
      Real.exp z + Real.exp (-z) - 2 := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  calc
    _ = Real.exp z * (1 / 4) := by ring
    _ ≤ Real.exp z * (1 - Real.exp (-z)) ^ 2 := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = _ := hid

theorem bernstein_mgf_optimizer_product_ge_one {v R t : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (ht : Real.sqrt v + R / 3 ≤ t) :
    1 ≤ t / (v + R * t / 3) * t := by
  have hs := Real.sqrt_nonneg v
  have ht0 : 0 ≤ t := by linarith
  have hden : 0 < v + R * t / 3 := by positivity
  have hts : Real.sqrt v ≤ t := by linarith
  have hp1 := mul_le_mul_of_nonneg_left (show Real.sqrt v ≤ t - R / 3 by linarith) ht0
  have hp2 := mul_le_mul_of_nonneg_right hts hs
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [Real.sq_sqrt hv.le]

variable {Ω ι H : Type*} [MeasurableSpace Ω] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem matrixLaplace_norm_tail_exp (b : HilbertBasis ι ℝ H) (Y : Ω → H →L[ℝ] H)
    (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω)) {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hθt : 1 ≤ θ * t)
    (hplus : Integrable (fun ω => NormedSpace.exp (θ • Y ω)) P)
    (hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • Y ω)) P) :
    P {ω | t ≤ ‖Y ω‖} ≤ ENNReal.ofReal
      (4 * Real.exp (-(θ * t)) * (∫ ω, matrixLaplacePotential b θ (Y ω) ∂P)) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  have hI : 0 ≤ ∫ ω, matrixLaplacePotential b θ (Y ω) ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hY] with ω hω
    exact matrixLaplacePotential_nonneg b (Y ω)
      (isCompactOperator_of_locallyCompactSpace_dom _) hω.isSymmetric θ
  have hC := exp_symmetric_remainder_ge_quarter_exp hθt
  have hsmall : 0 < Real.exp (θ * t) / 4 := by positivity
  refine (matrixLaplace_norm_tail b Y hY hθ ht hplus hminus).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (∫ ω, matrixLaplacePotential b θ (Y ω) ∂P) / (Real.exp (θ * t) / 4) :=
      div_le_div_of_nonneg_left hI hsmall hC
    _ = _ := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- The full scalar Laplace conversion with the actual trace potential.
`hmoment` is a displayed upstream trace-moment estimate, not a proved
independent-sum theorem and not a project-specific risk certificate. -/
theorem matrixLaplace_bernstein_of_trace_moment (b : HilbertBasis ι ℝ H)
    (Y : Ω → H →L[ℝ] H) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {v R t d : ℝ} (hv : 0 < v) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (ht : Real.sqrt v + R / 3 ≤ t)
    (hplus : Integrable (fun ω => NormedSpace.exp ((t / (v + R * t / 3)) • Y ω)) P)
    (hminus : Integrable (fun ω => NormedSpace.exp ((-(t / (v + R * t / 3))) • Y ω)) P)
    (hmoment : (∫ ω, matrixLaplacePotential b (t / (v + R * t / 3)) (Y ω) ∂P) ≤
      2 * d * (Real.exp (matrixExpRemainderCoefficient (t / (v + R * t / 3)) R * v) - 1)) :
    P {ω | t ≤ ‖Y ω‖} ≤
      ENNReal.ofReal (8 * d * Real.exp (-(t ^ 2) / (2 * (v + R * t / 3)))) := by
  have ht0 : 0 < t := by
    have hs := Real.sqrt_pos.mpr hv
    linarith
  have hden : 0 < v + R * t / 3 := by positivity
  have hθ : 0 < t / (v + R * t / 3) := div_pos ht0 hden
  have hθt := bernstein_mgf_optimizer_product_ge_one hv hR ht
  refine (matrixLaplace_norm_tail_exp b Y hY hθ ht0 hθt hplus hminus).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hI : (∫ ω, matrixLaplacePotential b (t / (v + R * t / 3)) (Y ω) ∂P) ≤
      2 * d * Real.exp (matrixExpRemainderCoefficient (t / (v + R * t / 3)) R * v) :=
    hmoment.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc
    _ ≤ 4 * Real.exp (-(t / (v + R * t / 3) * t)) *
        (2 * d * Real.exp (matrixExpRemainderCoefficient (t / (v + R * t / 3)) R * v)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 8 * d * Real.exp (-(t / (v + R * t / 3)) * t +
        matrixExpRemainderCoefficient (t / (v + R * t / 3)) R * v) := by
      rw [Real.exp_add]
      simp only [neg_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (bernstein_mgf_optimized_exponent hv hR ht0.le)) (by positivity)

end
end KernelSeq
