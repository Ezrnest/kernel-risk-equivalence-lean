import KernelSeq.AngularFourierSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Actual odd symmetry of the fixed angular symbol

The constructed fixed symbol is odd in its second coordinate. Its angular
profile therefore has no constant or cosine modes. These actual moment
identities avoid introducing an unrelated constant-mode multiplier.
-/

namespace KernelSeq
noncomputable section
local instance angularSinePositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem lipschitzEvenSymbol_neg_right (s t : ℝ) :
    lipschitzEvenSymbol s (-t) = -lipschitzEvenSymbol s t := by
  unfold lipschitzEvenSymbol
  rw [neg_div, lipschitzEvenCutoff_neg]
  ring

theorem lipschitzAngularProfile_neg (ψ : ℝ) :
    lipschitzAngularProfile (-ψ) = -lipschitzAngularProfile ψ := by
  simp only [lipschitzAngularProfile, neg_div, Real.cos_neg, Real.sin_neg,
    lipschitzEvenSymbol_neg_right]

/-- The actual angular profile recovers the actual planar symbol on every
real vector. The zero vector is handled by the genuine value at angle zero. -/
theorem lipschitzEvenSymbol_eq_angular (s t : ℝ) :
    lipschitzEvenSymbol s t = lipschitzAngularProfile (2 * Complex.arg (⟨s, t⟩ : ℂ)) := by
  by_cases hz : (⟨s, t⟩ : ℂ) = 0
  · have hs : s = 0 := congrArg Complex.re hz
    have ht : t = 0 := congrArg Complex.im hz
    subst s
    subst t
    change lipschitzEvenSymbol 0 0 = lipschitzAngularProfile (2 * Complex.arg 0)
    simp [lipschitzAngularProfile, lipschitzEvenSymbol, Complex.arg_zero]
  · have hr : ‖(⟨s, t⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have h := lipschitzEvenSymbol_homogeneous
      (Real.cos (Complex.arg (⟨s, t⟩ : ℂ))) (Real.sin (Complex.arg (⟨s, t⟩ : ℂ))) hr
    have he : 2 * Complex.arg (⟨s, t⟩ : ℂ) / 2 = Complex.arg (⟨s, t⟩ : ℂ) := by ring
    unfold lipschitzAngularProfile
    rw [he]
    simpa only [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg] using h

/-- Genuine periodic odd real functions have zero cosine moments on a full
period, including their constant mode. Reflection is an actual change of
variables in the interval integral. -/
theorem angularCosMoment_eq_zero_of_odd (f : ℝ → ℝ)
    (hper : Function.Periodic f (2 * Real.pi)) (hodd : ∀ x, f (-x) = -f x) (n : ℕ) :
    angularCosMoment f n = 0 := by
  have href (x : ℝ) : f (2 * Real.pi - x) = -f x := by
    have he : 2 * Real.pi - x = -x + 2 * Real.pi := by ring
    rw [he, hper (-x), hodd]
  have hfun : (fun x : ℝ => f (2 * Real.pi - x) * Real.cos ((n : ℝ) * (2 * Real.pi - x))) =
      (fun x : ℝ => -(f x * Real.cos ((n : ℝ) * x))) := by
    funext x
    rw [href, mul_sub, Real.cos_nat_mul_two_pi_sub]
    ring
  have hi := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => f x * Real.cos ((n : ℝ) * x)) (2 * Real.pi)
    (a := 0) (b := 2 * Real.pi)
  change (∫ x in 0..(2 * Real.pi), f (2 * Real.pi - x) *
    Real.cos ((n : ℝ) * (2 * Real.pi - x))) = _ at hi
  rw [hfun, intervalIntegral.integral_neg] at hi
  simp only [sub_self, sub_zero] at hi
  change -angularCosMoment f n = angularCosMoment f n at hi
  linarith

theorem lipschitzAngularCosMoment_eq_zero (n : ℕ) :
    angularCosMoment lipschitzAngularProfile n = 0 :=
  angularCosMoment_eq_zero_of_odd lipschitzAngularProfile lipschitzAngularProfile_periodic
    lipschitzAngularProfile_neg n

theorem lipschitzAngularFourierCoeff_zero :
    fourierCoeff (angularCircleMap lipschitzAngularProfile
      lipschitzAngularProfile_contDiff.continuous lipschitzAngularProfile_periodic) 0 = 0 := by
  have he := fourierCoeff_angularCircleMap_nat lipschitzAngularProfile
    lipschitzAngularProfile_contDiff.continuous lipschitzAngularProfile_periodic 0
  simpa only [Nat.cast_zero, lipschitzAngularCosMoment_eq_zero, angularSinMoment,
    Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, intervalIntegral.integral_zero,
    Complex.ofReal_zero, zero_mul, sub_zero] using he

end
end KernelSeq
