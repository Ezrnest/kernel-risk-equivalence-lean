import KernelSeq.AngularFourierDecay
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Actual circle Fourier coefficients of the fixed angular symbol

The genuine periodic angular function is lifted to the actual quotient circle.
Its Fourier coefficients are identified with its real cosine and sine moments;
the real moment estimates therefore apply to the established Fourier library.
-/

open MeasureTheory
open scoped ComplexConjugate ContDiff

namespace KernelSeq
noncomputable section

local instance angularCirclePositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def angularCircleMap (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) : C(AddCircle (2 * Real.pi), ℂ) where
  toFun := (show Function.Periodic (fun x : ℝ => (f x : ℂ)) (2 * Real.pi) from
    fun x => congrArg Complex.ofReal (hper x)).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (Complex.continuous_ofReal.comp hf).quotient_liftOn' _

@[simp]
theorem angularCircleMap_coe (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) (x : ℝ) :
    angularCircleMap f hf hper (x : AddCircle (2 * Real.pi)) = (f x : ℂ) := rfl

theorem angular_fourier_nat_phase (n : ℕ) (x : ℝ) :
    fourier (T := 2 * Real.pi) (-(n : ℤ)) (x : AddCircle (2 * Real.pi)) =
      (Real.cos ((n : ℝ) * x) : ℂ) - (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  have he : (2 * (Real.pi : ℂ) * Complex.I * (Int.cast (-(n : ℤ)) : ℂ) * (x : ℂ)) /
      ((2 * Real.pi : ℝ) : ℂ) = ((-(n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [he]
  apply Complex.ext
  · simp only [Complex.exp_ofReal_mul_I_re, neg_mul, Real.cos_neg, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero]
  · simp only [Complex.exp_ofReal_mul_I_im, neg_mul, Real.sin_neg, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, zero_mul, add_zero, zero_sub]

/-- Actual natural Fourier coefficients of the lifted periodic function.
The normalization is exactly the normalized Haar measure on the circle. -/
theorem fourierCoeff_angularCircleMap_nat (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    fourierCoeff (angularCircleMap f hf hper) (n : ℤ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((angularCosMoment f n : ℂ) - (angularSinMoment f n : ℂ) * Complex.I) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, angularCircleMap_coe, angular_fourier_nat_phase, smul_eq_mul]
  have hcos : Continuous (fun x : ℝ => ((f x * Real.cos ((n : ℝ) * x) : ℝ) : ℂ)) := by fun_prop
  have hsin : Continuous (fun x : ℝ => ((f x * Real.sin ((n : ℝ) * x) : ℝ) : ℂ)) := by fun_prop
  have hfun : (fun x : ℝ =>
      ((Real.cos ((n : ℝ) * x) : ℂ) - (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I) * (f x : ℂ)) =
      (fun x : ℝ => ((f x * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) -
        ((f x * Real.sin ((n : ℝ) * x) : ℝ) : ℂ) * Complex.I) := by
    funext x
    push_cast
    ring
  rw [hfun, intervalIntegral.integral_sub (hcos.intervalIntegrable _ _)
    ((hsin.mul_const Complex.I).intervalIntegrable _ _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  rfl

theorem fourierCoeff_angularCircleMap_neg (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℤ) :
    fourierCoeff (angularCircleMap f hf hper) (-n) =
      conj (fourierCoeff (angularCircleMap f hf hper) n) := by
  have hreal (x : AddCircle (2 * Real.pi)) :
      conj (angularCircleMap f hf hper x) = angularCircleMap f hf hper x := by
    induction x using QuotientAddGroup.induction_on
    simp only [angularCircleMap_coe, Complex.conj_ofReal]
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul, map_mul, hreal, ← fourier_neg, neg_neg]

theorem norm_fourierCoeff_angularCircleMap_nat_le (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    ‖fourierCoeff (angularCircleMap f hf hper) (n : ℤ)‖ ≤
      (1 / (2 * Real.pi)) * (|angularCosMoment f n| + |angularSinMoment f n|) := by
  rw [fourierCoeff_angularCircleMap_nat, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using
    (norm_sub_le (angularCosMoment f n : ℂ) ((angularSinMoment f n : ℂ) * Complex.I))

/-- Genuine coefficient summability of the actual smooth angular lift.
The proof uses the proved real coefficient decay, not a Fourier summability
or inversion certificate. -/
theorem summable_fourierCoeff_angularCircleMap {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    Summable (fourierCoeff (angularCircleMap f hf.continuous hper)) := by
  have hw := (angularMoments_weighted_summable hf hper).mul_left (1 / (2 * Real.pi))
  have hnorm : Summable (fun n : ℕ =>
      ‖fourierCoeff (angularCircleMap f hf.continuous hper) ((n + 1 : ℕ) : ℤ)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hw
    intro n
    have ht := norm_fourierCoeff_angularCircleMap_nat_le f hf.continuous hper (n + 1)
    have ha : 0 ≤ |angularCosMoment f (n + 1)| + |angularSinMoment f (n + 1)| := by positivity
    have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ht.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_right hN ha]) (by positivity))
  have hnat : Summable (fun n : ℕ =>
      fourierCoeff (angularCircleMap f hf.continuous hper) (n : ℤ)) :=
    (summable_nat_add_iff 1).mp hnorm.of_norm
  have hneg : Summable (fun n : ℕ =>
      fourierCoeff (angularCircleMap f hf.continuous hper) (-(n : ℤ))) := by
    simpa only [fourierCoeff_angularCircleMap_neg] using (Complex.summable_conj.mpr hnat)
  exact Summable.of_nat_of_neg hnat hneg

/-- Actual uniform Fourier reconstruction of the genuine angular function,
using Mathlib's established circle Fourier basis and the proved coefficients. -/
theorem angularCircleMap_hasSum_fourier {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    HasSum (fun n : ℤ =>
      fourierCoeff (angularCircleMap f hf.continuous hper) n • fourier n)
        (angularCircleMap f hf.continuous hper) :=
  hasSum_fourier_series_of_summable (summable_fourierCoeff_angularCircleMap hf hper)

theorem lipschitzAngularProfile_hasSum_fourier (x : ℝ) :
    HasSum (fun n : ℤ =>
      fourierCoeff (angularCircleMap lipschitzAngularProfile
        lipschitzAngularProfile_contDiff.continuous lipschitzAngularProfile_periodic) n •
          fourier n (x : AddCircle (2 * Real.pi))) (lipschitzAngularProfile x : ℂ) := by
  simpa only [angularCircleMap_coe] using
    has_pointwise_sum_fourier_series_of_summable
      (summable_fourierCoeff_angularCircleMap lipschitzAngularProfile_contDiff
        lipschitzAngularProfile_periodic) (x : AddCircle (2 * Real.pi))

end
end KernelSeq
