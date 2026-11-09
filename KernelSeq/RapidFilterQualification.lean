import KernelSeq.StableGradientDescentFilter
import KernelSeq.SmoothedCutoffFilter
import KernelSeq.SpectralClippingFilter

/-!
# Arbitrary qualification of rapidly decaying filters

The gradient-flow, real-time stable-gradient-descent, and smoothed-cutoff
filters have arbitrary qualification. The scalar constants depend only on
the qualification order.
Clipping also has arbitrary qualification, by its compact residual support.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- A uniform polynomial/exponential bound, including exponent and base zero. -/
theorem rpow_mul_exp_neg_le_order_rpow {z τ : ℝ} (hz : 0 ≤ z) (hτ : 0 ≤ τ) :
    z ^ τ * Real.exp (-z) ≤ τ ^ τ := by
  by_cases hτ0 : τ = 0
  · subst τ
    simp only [Real.rpow_zero, one_mul]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  · have hτp : 0 < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
    have hx0 : 0 ≤ z / τ * Real.exp (-(z / τ)) := by positivity
    have hx1 : z / τ * Real.exp (-(z / τ)) ≤ 1 :=
      (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
    have hp := Real.rpow_le_one hx0 hx1 hτ
    have heq : (Real.exp (-(z / τ))) ^ τ = Real.exp (-z) := by
      rw [← Real.exp_mul]
      congr 1
      field_simp
    have hzq : τ ^ τ * (z / τ) ^ τ = z ^ τ := by
      rw [← Real.mul_rpow hτ (div_nonneg hz hτ)]
      congr 1
      field_simp
    calc
      z ^ τ * Real.exp (-z) = τ ^ τ * (z / τ * Real.exp (-(z / τ))) ^ τ := by
        rw [Real.mul_rpow (div_nonneg hz hτ) (Real.exp_pos _).le, heq, ← mul_assoc, hzq]
      _ ≤ τ ^ τ * 1 := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hτ _)
      _ = _ := by ring

theorem scaled_rpow_mul_exp_neg_le {lam t τ : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    t ^ τ * Real.exp (-t / lam) ≤ τ ^ τ * lam ^ τ := by
  have hp := rpow_mul_exp_neg_le_order_rpow (div_nonneg ht hlam.le) hτ
  have heq : lam ^ τ * (t / lam) ^ τ = t ^ τ := by
    rw [← Real.mul_rpow hlam.le (div_nonneg ht hlam.le)]
    congr 1
    field_simp
  calc
    _ = lam ^ τ * ((t / lam) ^ τ * Real.exp (-(t / lam))) := by rw [← mul_assoc, heq, neg_div]
    _ ≤ lam ^ τ * τ ^ τ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hlam.le _)
    _ = _ := by ring

/-- Gradient flow has arbitrary qualification, with a constant independent of
the regularization and of the spectral upper bound. -/
theorem gradientFlow_qualification {lam t τ : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    t ^ τ * |residual (gradientFlow lam) t| ≤ τ ^ τ * lam ^ τ := by
  rw [gradientFlow_residual, abs_of_pos (Real.exp_pos _)]
  exact scaled_rpow_mul_exp_neg_le hlam ht hτ

/-- The real-iteration stable gradient-descent filter has arbitrary
qualification. Unlike its contract, this bound does not require `m ≥ 1`. -/
theorem stableGradientDescent_qualification {eta lam M margin t τ : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Set.Icc (0 : ℝ) M) (hτ : 0 ≤ τ) :
    t ^ τ * |residual (stableGradientDescent eta lam) t| ≤ τ ^ τ * lam ^ τ := by
  have hr0 : 0 ≤ residual (stableGradientDescent eta lam) t :=
    (stableGradientDescent_spectralFilter heta hlam hmargin hstable).residual_nonneg ht
  rw [abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left
    (stableGradientDescent_residual_le_exp heta hlam hmargin hstable ht)
    (Real.rpow_nonneg ht.1 _)).trans (scaled_rpow_mul_exp_neg_le hlam ht.1 hτ)

theorem smoothedCutoff_qualification {lam t τ : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    t ^ τ * |residual (smoothedCutoff lam χ) t| ≤ (2 : ℝ) ^ τ * lam ^ τ := by
  have hr := (smoothedCutoff_spectralFilter (M := t) hlam hχ).residual_mem ⟨ht, le_rfl⟩
  rw [abs_of_nonneg hr.1]
  by_cases htt : t ≤ 2 * lam
  · calc
      _ ≤ t ^ τ * 1 := mul_le_mul_of_nonneg_left hr.2 (Real.rpow_nonneg ht _)
      _ ≤ (2 * lam) ^ τ := by simpa only [mul_one] using Real.rpow_le_rpow ht htt hτ
      _ = _ := Real.mul_rpow (by norm_num) hlam.le
  · have hz : 2 ≤ t / lam := (le_div_iff₀ hlam).2 (by linarith)
    rw [smoothedCutoff_residual hlam hχ, hχ.above _ hz]
    simp only [sub_self, mul_zero]
    positivity

/-- Compact residual support also gives clipping arbitrary qualification,
with the exact constant one. -/
theorem clipping_qualification {lam t τ : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    t ^ τ * |residual (clipping lam) t| ≤ lam ^ τ := by
  have hr := (clipping_spectralFilter (M := t) hlam).residual_mem ⟨ht, le_rfl⟩
  rw [abs_of_nonneg hr.1]
  by_cases htl : t ≤ lam
  · exact (mul_le_mul_of_nonneg_left hr.2 (Real.rpow_nonneg ht _)).trans
      (by simpa only [mul_one] using Real.rpow_le_rpow ht htl hτ)
  · rw [clipping_residual hlam, max_eq_right (by
      have h : 1 ≤ t / lam := (le_div_iff₀ hlam).2 (by simpa using le_of_not_ge htl)
      linarith : 1 - t / lam ≤ 0), mul_zero]
    exact Real.rpow_nonneg hlam.le _

end
end KernelSeq.ResidualFilter
