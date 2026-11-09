import KernelSeq.StableGradientDescentFilter
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Stable real-iteration gradient descent for every positive regularization

The fixed-margin derivative estimate gives a global inverse bound by the mean
value theorem. Thus the actual stable filter satisfies the same residual
contract for all `lam > 0`, including real iteration times below one.
-/

namespace KernelSeq.ResidualFilter

open MeasureTheory Set
noncomputable section

theorem stableGradientDescent_shrinkage_le_linear {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    shrinkage (stableGradientDescent eta lam) t ≤ (1 - margin)⁻¹ * (t / lam) := by
  have hd : 0 < 1 - margin := by linarith
  have hc : 0 ≤ (1 - margin)⁻¹ := inv_nonneg.mpr hd.le
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) M := by
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hdiff : ∀ x ∈ Icc (0 : ℝ) t,
      DifferentiableAt ℝ (residual (stableGradientDescent eta lam)) x := by
    intro x hx
    have hxm := hsub hx
    have hbase : 0 < 1 - eta * x := by
      have h := mul_le_mul_of_nonneg_left hxm.2 heta.le
      linarith
    have heq : residual (stableGradientDescent eta lam) =
        fun x => (1 - eta * x) ^ gradientDescentIterations eta lam :=
      funext (stableGradientDescent_residual eta lam)
    rw [heq]
    exact ((((hasDerivAt_id x).const_mul eta).const_sub 1).rpow_const
      (p := gradientDescentIterations eta lam) (Or.inl hbase.ne')).differentiableAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖deriv (residual (stableGradientDescent eta lam)) x‖ ≤ (1 - margin)⁻¹ / lam := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hder := stableGradientDescent_abs_deriv_le_exp heta hlam hmargin hstable (hsub hx)
    have he : Real.exp (-x / lam) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.1) hlam.le)
    exact hder.trans (div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hc) hlam.le)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc (0 : ℝ) t) (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht.1⟩)
    (show t ∈ Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)
  have hz : residual (stableGradientDescent eta lam) 0 = 1 := by simp [residual, shrinkage]
  rw [hz, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hh
  calc
    _ = 1 - residual (stableGradientDescent eta lam) t := by unfold residual; ring
    _ ≤ |residual (stableGradientDescent eta lam) t - 1| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ ≤ ((1 - margin)⁻¹ / lam) * t := hh
    _ = _ := by ring

/-- Unlike the initial Bernoulli proof, this inverse bound is uniform over all
positive regularizations and therefore all positive real iteration times. -/
theorem stableGradientDescent_inverse_size_global {eta lam M margin t : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hmargin : margin < 1)
    (hstable : eta * M ≤ margin) (ht : t ∈ Icc (0 : ℝ) M) :
    (t + lam) * stableGradientDescent eta lam t ≤ 2 / (1 - margin) := by
  have hmargin0 : 0 ≤ margin := (mul_nonneg heta.le (ht.1.trans ht.2)).trans hstable
  have hd : 0 < 1 - margin := by linarith
  have hc : 1 ≤ (1 - margin)⁻¹ := (one_le_inv₀ hd).2 (by linarith)
  have hc0 : 0 ≤ (1 - margin)⁻¹ := inv_nonneg.mpr hd.le
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_add, stableGradientDescent_zero, mul_inv_cancel₀ hlam.ne']
    rw [div_eq_mul_inv]
    linarith
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hq := stableGradientDescent_shrinkage_le_linear heta hlam hmargin hstable ht
    rw [stableGradientDescent_shrinkage] at hq
    rw [stableGradientDescent, if_neg ht0]
    by_cases htl : t ≤ lam
    · have hg : (1 - (1 - eta * t) ^ gradientDescentIterations eta lam) / t ≤
          (1 - margin)⁻¹ / lam := by
        apply (div_le_iff₀ htp).2
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hq
      calc
        _ ≤ (t + lam) * ((1 - margin)⁻¹ / lam) :=
          mul_le_mul_of_nonneg_left hg (by linarith [ht.1])
        _ ≤ 2 * (1 - margin)⁻¹ := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hlam).2
          nlinarith
        _ = _ := by ring
    · have hr := (stableGradientDescent_spectralFilter heta hlam hmargin hstable).residual_nonneg ht
      rw [stableGradientDescent_residual] at hr
      have hg : (1 - (1 - eta * t) ^ gradientDescentIterations eta lam) / t ≤ 1 / t :=
        div_le_div_of_nonneg_right (by linarith) ht.1
      calc
        _ ≤ (t + lam) * (1 / t) := mul_le_mul_of_nonneg_left hg (by linarith [ht.1])
        _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ htp).2; linarith
        _ ≤ 2 * (1 - margin)⁻¹ := by linarith
        _ = _ := by ring

/-- All positive regularizations satisfy the actual original contract with
the same margin-only constant. There is no small-regularization premise. -/
theorem stableGradientDescent_contract_global {eta lam M margin : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hmargin : margin < 1) (hstable : eta * M ≤ margin) :
    Contract lam M 1 (8 / (1 - margin)) (stableGradientDescent eta lam) := by
  have hmargin0 : 0 ≤ margin := (mul_nonneg heta.le hM).trans hstable
  have hd : 0 < 1 - margin := by linarith
  have hB : 4 ≤ stableGradientDescentSmoothConstant margin := by
    unfold stableGradientDescentSmoothConstant
    exact (le_div_iff₀ hd).2 (by linarith)
  have hh := contract_of_smooth_condition_nonnegative_interval
    (B := stableGradientDescentSmoothConstant margin) hlam hM (by norm_num : (0 : ℝ) < 1)
    (stableGradientDescent_spectralFilter heta hlam hmargin hstable)
    (stableGradientDescent_residual_contDiffOn heta hM hmargin hstable).absolutelyContinuousOnInterval
    (fun t ht => (stableGradientDescent_inverse_size_global heta hlam hmargin hstable ht).trans
      (by
        unfold stableGradientDescentSmoothConstant
        exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hd.le))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact stableGradientDescent_combined_bound heta hlam hmargin hstable ht)
  have heq : max (stableGradientDescentSmoothConstant margin) 1 * max 2 (1 : ℝ) =
      8 / (1 - margin) := by
    rw [max_eq_left (by linarith : 1 ≤ stableGradientDescentSmoothConstant margin)]
    norm_num [stableGradientDescentSmoothConstant]
    ring
  rwa [heq] at hh

end
end KernelSeq.ResidualFilter
