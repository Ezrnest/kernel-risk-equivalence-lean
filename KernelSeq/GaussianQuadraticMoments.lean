import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Actual exponential moments of a Gaussian square

The formulas are derived from the Gaussian density and Gaussian integral.
Integrability is proved, rather than assumed as an MGF certificate.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Filter
open scoped Real ENNReal NNReal
noncomputable section

theorem integral_exp_mul_sq_standardGaussian {a : ℝ} (ha : a < 1/2) :
    (∫ x : ℝ, Real.exp (a*x^2) ∂gaussianReal 0 1) = (Real.sqrt (1-2*a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  have he : (fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2) * Real.exp (a*x^2)) =
      (fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*x^2)) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian]
  have hb : 0 < 1/2-a := by linarith
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    show 1-2*a = 2*(1/2-a) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', (Real.sqrt_pos.mpr hb).ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']

theorem integrable_exp_mul_sq_standardGaussian {a : ℝ} (ha : a < 1/2) :
    Integrable (fun x : ℝ => Real.exp (a*x^2)) (gaussianReal 0 1) := by
  by_contra hn
  have hi := integral_exp_mul_sq_standardGaussian ha
  rw [integral_undef hn] at hi
  exact (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith : 0 < 1-2*a))).ne' hi.symm

theorem integrable_exp_centered_sq_standardGaussian {a : ℝ} (ha : a < 1/2) :
    Integrable (fun x : ℝ => Real.exp (a*(x^2-1))) (gaussianReal 0 1) := by
  have he (x : ℝ) : Real.exp (a*(x^2-1)) = Real.exp (-a) * Real.exp (a*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (integrable_exp_mul_sq_standardGaussian ha).const_mul _

theorem integral_exp_centered_sq_standardGaussian {a : ℝ} (ha : a < 1/2) :
    (∫ x : ℝ, Real.exp (a*(x^2-1)) ∂gaussianReal 0 1) =
      Real.exp (-a) / Real.sqrt (1-2*a) := by
  have he (x : ℝ) : Real.exp (a*(x^2-1)) = Real.exp (-a) * Real.exp (a*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_sq_standardGaussian ha, div_eq_mul_inv]

/-- A uniform genuine quadratic-exponential bound on the interval needed
for exponential prior shaving. The constant is deliberately nonoptimal. -/
theorem integral_exp_centered_sq_standardGaussian_le {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1/4) :
    (∫ x : ℝ, Real.exp (a*(x^2-1)) ∂gaussianReal 0 1) ≤ Real.exp (4*a^2) := by
  have hd : 0 < 1-2*a := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hl
  have hid : (1-2*a)⁻¹ - 1 = 2*a/(1-2*a) := by field_simp; ring
  rw [hid] at hl
  have hf : 2*a^2/(1-2*a) ≤ 4*a^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 1/4-a by linarith)]
  have he : -a + (2*a/(1-2*a))/2 = 2*a^2/(1-2*a) := by
    calc
      _ = a*((1-2*a)⁻¹-1) := by ring
      _ = a*(2*a/(1-2*a)) := by rw [hid]
      _ = _ := by ring
  have hlog : -a - Real.log (1-2*a)/2 ≤ 4*a^2 := by linarith
  have hm : Real.log (Real.exp (-a) / Real.sqrt (1-2*a)) =
      -a - Real.log (1-2*a)/2 := by
    rw [Real.log_div (Real.exp_ne_zero _) (Real.sqrt_pos.mpr hd).ne',
      Real.log_exp, Real.log_sqrt hd.le]
  have hb := Real.exp_le_exp.mpr (hm.trans_le hlog)
  rw [Real.exp_log (div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr hd))] at hb
  rw [integral_exp_centered_sq_standardGaussian (by linarith : a < 1/2)]
  exact hb

end
end KernelSeq
