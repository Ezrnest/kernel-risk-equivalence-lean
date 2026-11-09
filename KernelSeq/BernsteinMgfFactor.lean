import KernelSeq.MatrixBernsteinExp
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The proved scalar Bernstein bound for the actual exponential remainder

The geometric bound follows from the genuine exponential series and an
elementary factorial inequality. The usual optimized exponent is derived from
that bound, including radius zero. No matrix concentration statement is an
input or a conclusion of this scalar step.
-/

namespace KernelSeq
noncomputable section

theorem bernstein_factorial_lower (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hmul := Nat.mul_le_mul_left 3 ih
    have hscale := Nat.mul_le_mul_right (k + 2).factorial (show 3 ≤ k + 3 by omega)
    calc
      2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ 3 * (k + 2).factorial := hmul
      _ ≤ (k + 3) * (k + 2).factorial := hscale
      _ = (k + 1 + 2).factorial := by
        simpa only [Nat.add_assoc] using (Nat.factorial_succ (k + 2)).symm

theorem exp_quadratic_remainder_le_bernstein {z : ℝ} (hz : 0 ≤ z) (hz3 : z < 3) :
    Real.exp z - 1 - z ≤ z ^ 2 / (2 * (1 - z / 3)) := by
  have hr0 : 0 ≤ z / 3 := by positivity
  have hr1 : z / 3 < 1 := by linarith
  have hnorm : ‖z / 3‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hterm (k : ℕ) : z ^ (k + 2) / ((k + 2).factorial : ℝ) ≤
      (z ^ 2 / 2) * (z / 3) ^ k := by
    have hfac : (2 : ℝ) * 3 ^ k ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast bernstein_factorial_lower k
    have ht := div_le_div_of_nonneg_left (pow_nonneg hz (k + 2))
      (by positivity : (0 : ℝ) < 2 * 3 ^ k) hfac
    refine ht.trans_eq ?_
    rw [pow_add, div_pow]
    field_simp
  have hs := hasSum_le hterm (exp_remainder_hasSum z)
    ((hasSum_geometric_of_norm_lt_one hnorm).mul_left (z ^ 2 / 2))
  exact hs.trans_eq (by field_simp)

theorem matrixExpRemainderCoefficient_le_bernstein {θ R : ℝ}
    (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hθR : θ * R < 3) :
    matrixExpRemainderCoefficient θ R ≤ θ ^ 2 / (2 * (1 - θ * R / 3)) := by
  by_cases hR0 : R = 0
  · subst R
    simp only [matrixExpRemainderCoefficient_zero, mul_zero, zero_div, sub_zero, mul_one]
    exact le_rfl
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos (lt_of_le_of_ne hR (Ne.symm hR0))
  rw [matrixExpRemainderCoefficient_of_ne_zero θ hR0]
  calc
    _ ≤ ((θ * R) ^ 2 / (2 * (1 - θ * R / 3))) / R ^ 2 :=
      div_le_div_of_nonneg_right (exp_quadratic_remainder_le_bernstein (mul_nonneg hθ hR) hθR) hR2.le
    _ = _ := by field_simp [hR0]

theorem bernstein_mgf_optimizer_nonneg {v R t : ℝ} (hv : 0 < v) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    0 ≤ t / (v + R * t / 3) := by positivity

theorem bernstein_mgf_optimizer_admissible {v R t : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    t / (v + R * t / 3) * R < 3 := by
  have hden : 0 < v + R * t / 3 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith

theorem bernstein_mgf_optimized_exponent {v R t : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    -(t / (v + R * t / 3)) * t +
        matrixExpRemainderCoefficient (t / (v + R * t / 3)) R * v ≤
      -(t ^ 2) / (2 * (v + R * t / 3)) := by
  have hθ := bernstein_mgf_optimizer_nonneg hv hR ht
  have hθR := bernstein_mgf_optimizer_admissible hv hR ht
  have hg := matrixExpRemainderCoefficient_le_bernstein hθ hR hθR
  calc
    _ ≤ -(t / (v + R * t / 3)) * t +
        ((t / (v + R * t / 3)) ^ 2 / (2 * (1 - t / (v + R * t / 3) * R / 3))) * v :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hg hv.le)
    _ = _ := by
      have hden : v + R * t / 3 ≠ 0 := ne_of_gt (by positivity)
      have hsmall : 1 - t / (v + R * t / 3) * R / 3 ≠ 0 := by linarith
      field_simp [hden, hsmall, hv.ne']
      ring

open MeasureTheory

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The actual matrix moment-generating bound in the standard Bernstein
quadratic form. It follows from the proved exponential series bound; no
operator-monotonicity claim for the exponential is used. -/
theorem integral_operator_exp_le_bernstein_majorant (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R : ℝ} (hθ : 0 ≤ θ) (hθR : θ * R < 3) (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R)
    (hmean : (∫ ω, Y ω ∂P) = 0) (W : H →L[ℝ] H)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    (∫ ω, NormedSpace.exp (θ • Y ω) ∂P : H →L[ℝ] H) ≤
      NormedSpace.exp ((θ ^ 2 / (2 * (1 - θ * R / 3))) • W) := by
  obtain ⟨ω, hω⟩ := hR.exists
  have hR0 : 0 ≤ R := (norm_nonneg (Y ω)).trans hω
  have hYi := integrable_operator_of_ae_norm_bound Y hYm hR
  have hY2 := integrable_operator_square_of_bound Y hYi hR
  have hvar : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H).IsPositive :=
    integral_operator_isPositive _ hY2 (hY.mono fun ω hω =>
      operator_square_isPositive_of_isSelfAdjoint (Y ω) hω)
  have hWpos : W.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive W).mp
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hvar).trans hW)
  have hg := matrixExpRemainderCoefficient_le_bernstein hθ hR0 hθR
  have hc : 0 ≤ θ ^ 2 / (2 * (1 - θ * R / 3)) := by
    apply div_nonneg (sq_nonneg _)
    linarith
  have hmid : 1 + matrixExpRemainderCoefficient θ R • W ≤
      1 + (θ ^ 2 / (2 * (1 - θ * R / 3))) • W := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    have heq : (1 + (θ ^ 2 / (2 * (1 - θ * R / 3))) • W) -
        (1 + matrixExpRemainderCoefficient θ R • W) =
        ((θ ^ 2 / (2 * (1 - θ * R / 3))) - matrixExpRemainderCoefficient θ R) • W := by module
    rw [heq]
    exact hWpos.smul_of_nonneg (sub_nonneg.mpr hg)
  exact ((integral_operator_exp_le_one_add_majorant Y hYm hY hθ hR hmean W hW).trans hmid).trans
    (finite_one_add_operator_le_exp _ (hWpos.smul_of_nonneg hc).isSymmetric)

end
end KernelSeq
