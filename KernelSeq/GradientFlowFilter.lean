import KernelSeq.SmoothResidualFilter

/-!
# Gradient-flow spectral filters

The time `1/lam` gradient-flow inverse includes its actual removable value at
zero. Its original admissibility and residual contract are proved with fixed
constants, without any auxiliary filter certificate.
-/

namespace KernelSeq.ResidualFilter

open MeasureTheory Set
noncomputable section

def gradientFlow (lam t : ℝ) : ℝ :=
  if t = 0 then lam⁻¹ else (1 - Real.exp (-t / lam)) / t

theorem gradientFlow_zero (lam : ℝ) : gradientFlow lam 0 = lam⁻¹ := by simp [gradientFlow]

theorem gradientFlow_shrinkage (lam t : ℝ) :
    shrinkage (gradientFlow lam) t = 1 - Real.exp (-t / lam) := by
  by_cases ht : t = 0
  · subst t
    simp [shrinkage]
  · simp only [shrinkage, gradientFlow, if_neg ht]
    field_simp

theorem gradientFlow_residual (lam t : ℝ) :
    residual (gradientFlow lam) t = Real.exp (-t / lam) := by
  rw [residual, gradientFlow_shrinkage]
  ring

theorem gradientFlow_spectralFilter {lam M : ℝ} (hlam : 0 < lam) :
    SpectralFilter M (gradientFlow lam) := by
  have hmeas : Measurable (gradientFlow lam) := by
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      ((continuous_const.sub ((continuous_id.neg.div_const lam).rexp)).measurable.div measurable_id)
  constructor
  · exact hmeas.comp measurable_subtype_coe
  · intro t ht
    by_cases ht0 : t = 0
    · simp [gradientFlow, ht0, hlam.le]
    · rw [gradientFlow, if_neg ht0]
      apply div_nonneg _ ht.1
      apply sub_nonneg.mpr
      exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hlam.le)
  · intro t ht
    rw [gradientFlow_shrinkage]
    have he1 : Real.exp (-t / lam) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hlam.le)
    constructor <;> linarith [Real.exp_pos (-t / lam)]

theorem gradientFlow_inverse_size {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    (t + lam) * gradientFlow lam t ≤ 2 := by
  by_cases ht0 : t = 0
  · subst t
    simp [gradientFlow, hlam.ne']
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    rw [gradientFlow, if_neg ht0]
    by_cases htl : t ≤ lam
    · have hlin : 1 - Real.exp (-t / lam) ≤ t / lam := by
        have h := Real.add_one_le_exp (-t / lam)
        rw [neg_div] at h
        rw [neg_div]
        linarith
      have hg : (1 - Real.exp (-t / lam)) / t ≤ 1 / lam := by
        apply (div_le_iff₀ htp).2
        simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hlin
      calc
        _ ≤ (t + lam) * (1 / lam) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ hlam).2; linarith
    · have hg : (1 - Real.exp (-t / lam)) / t ≤ 1 / t :=
        div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-t / lam)]) ht
      calc
        _ ≤ (t + lam) * (1 / t) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ htp).2; linarith

theorem gradientFlow_residual_contDiff (lam : ℝ) : ContDiff ℝ 1 (residual (gradientFlow lam)) := by
  have heq : residual (gradientFlow lam) = fun t => Real.exp (-t / lam) :=
    funext (gradientFlow_residual lam)
  rw [heq]
  exact (contDiff_id.neg.div_const lam).exp

theorem gradientFlow_residual_deriv (lam t : ℝ) :
    deriv (residual (gradientFlow lam)) t = -Real.exp (-t / lam) / lam := by
  have heq : residual (gradientFlow lam) = fun t => Real.exp (-t / lam) :=
    funext (gradientFlow_residual lam)
  rw [heq]
  simpa only [id_eq, Pi.neg_apply, neg_div, one_div, neg_mul, mul_neg, div_eq_mul_inv, mul_one, mul_comm] using
    (((hasDerivAt_id t).neg.div_const lam).exp).deriv

/-- The elementary exponential estimate used for the combined smooth bound. -/
theorem gradientFlow_polynomial_bound {z : ℝ} (hz : 0 ≤ z) :
    (2 + z) * (1 + z) ≤ 4 * Real.exp z := by
  have hlin := Real.add_one_le_exp (z / 2)
  have hnonneg : 0 ≤ z / 2 + 1 := by positivity
  have hs := mul_self_le_mul_self hnonneg hlin
  have heq : Real.exp (z / 2) * Real.exp (z / 2) = Real.exp z := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hs
  nlinarith

theorem gradientFlow_combined_bound {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    |residual (gradientFlow lam) t| +
      (t + lam) * |deriv (residual (gradientFlow lam)) t| ≤
        4 * (lam / (t + lam)) ^ (1 : ℝ) := by
  rw [gradientFlow_residual, gradientFlow_residual_deriv, Real.rpow_one,
    abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hlam]
  have hz : 0 ≤ t / lam := div_nonneg ht hlam.le
  have he : 0 < Real.exp (t / lam) := Real.exp_pos _
  have hp := gradientFlow_polynomial_bound hz
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
  rw [neg_div, Real.exp_neg]
  have hcoord : t + lam = lam * (1 + t / lam) := by field_simp; ring
  calc
    _ = (2 + t / lam) / Real.exp (t / lam) := by field_simp; ring
    _ ≤ (4 * lam) / (t + lam) := by
      apply (div_le_div_iff₀ he hden).2
      rw [hcoord]
      nlinarith [mul_le_mul_of_nonneg_left hp hlam.le]
    _ = _ := by ring

/-- Gradient flow satisfies the original contract with `ρ=1`, `A=8`. -/
theorem gradientFlow_contract {lam M : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M) :
    Contract lam M 1 8 (gradientFlow lam) := by
  have h := contract_of_smooth_condition_nonnegative_interval (B := 4) hlam hM
    (by norm_num : (0 : ℝ) < 1) (gradientFlow_spectralFilter hlam)
    (gradientFlow_residual_contDiff lam).contDiffOn.absolutelyContinuousOnInterval
    (fun t ht => (gradientFlow_inverse_size hlam ht.1).trans (by norm_num))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact gradientFlow_combined_bound hlam ht.1)
  norm_num at h ⊢
  exact h

end
end KernelSeq.ResidualFilter
