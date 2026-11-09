import KernelSeq.HeatRieszPolynomial
import KernelSeq.LipschitzEvenSymbol
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual angular expansion of anisotropic reflection multipliers

This is a scalar construction for the fixed-even-symbol reduction. A real
anisotropic reflection Riesz multiplier has an explicit angular profile and
geometric cosine expansion. A concrete anisotropy gives a polynomial lower
bound on its chosen harmonic coefficient. No Fourier operator norm or UMD
estimate is an input or a conclusion here.
-/

namespace KernelSeq
noncomputable section
open scoped ContDiff

/-- The actual fixed symbol on the circle, parametrized so that the
simultaneous evenness gives period 2 pi rather than an extra odd mode. -/
def lipschitzAngularProfile (ψ : ℝ) : ℝ :=
  lipschitzEvenSymbol (Real.cos (ψ / 2)) (Real.sin (ψ / 2))

theorem lipschitzAngularProfile_contDiff : ContDiff ℝ ∞ lipschitzAngularProfile := by
  rw [contDiff_iff_contDiffAt]
  intro ψ
  have hz : (Real.cos (ψ / 2), Real.sin (ψ / 2)) ≠ (0 : ℝ × ℝ) := by
    intro h
    have hc := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero] at hc hs
    nlinarith [Real.sin_sq_add_cos_sq (ψ / 2)]
  have hcurve : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.cos (t / 2), Real.sin (t / 2))) ψ := by
    fun_prop
  exact (lipschitzEvenSymbol_contDiffAt hz).comp ψ hcurve

theorem lipschitzAngularProfile_periodic : Function.Periodic lipschitzAngularProfile (2 * Real.pi) := by
  intro ψ
  unfold lipschitzAngularProfile
  have he : (ψ + 2 * Real.pi) / 2 = ψ / 2 + Real.pi := by ring
  rw [he, Real.cos_add_pi, Real.sin_add_pi, lipschitzEvenSymbol_even]

theorem lipschitzAngularProfile_abs_le (ψ : ℝ) : |lipschitzAngularProfile ψ| ≤ 3 :=
  lipschitzEvenSymbol_abs_le _ _

def angularRieszDenominator (r ψ : ℝ) : ℝ := 1 - 2 * r * Real.cos ψ + r ^ 2

def angularRieszProfile (r ψ : ℝ) : ℝ :=
  ((1 + r ^ 2) * Real.cos ψ - 2 * r) / angularRieszDenominator r ψ

theorem angularRieszDenominator_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ψ : ℝ) :
    0 < angularRieszDenominator r ψ := by
  unfold angularRieszDenominator
  have hcos : 0 ≤ r * (1 - Real.cos ψ) := mul_nonneg hr0 (sub_nonneg.mpr (Real.cos_le_one ψ))
  nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]

theorem angularRieszProfile_eq_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ψ : ℝ) :
    angularRieszProfile r ψ =
      -r + (1 - r ^ 2) * ((Real.cos ψ - r) / angularRieszDenominator r ψ) := by
  have hd := ne_of_gt (angularRieszDenominator_pos hr0 hr1 ψ)
  unfold angularRieszProfile
  field_simp [hd]
  unfold angularRieszDenominator
  ring

/-- The profile is the actual reflected Riesz symbol at an anisotropically
scaled unit direction; the argument of the angular profile is twice the angle. -/
theorem angularRieszProfile_eq_reflection (r θ : ℝ) :
    planarRieszSymbol planarReflectionMatrix
      ((1 - r) * Real.cos θ, (1 + r) * Real.sin θ) = angularRieszProfile r (2 * θ) := by
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hd : ((1 - r) * Real.cos θ) ^ 2 + ((1 + r) * Real.sin θ) ^ 2 =
      angularRieszDenominator r (2 * θ) := by
    unfold angularRieszDenominator
    rw [mul_pow, mul_pow, hs, Real.cos_two_mul]
    ring
  have hn : ((1 - r) * Real.cos θ) ^ 2 - ((1 + r) * Real.sin θ) ^ 2 =
      (1 + r ^ 2) * Real.cos (2 * θ) - 2 * r := by
    rw [mul_pow, mul_pow, hs, Real.cos_two_mul]
    ring
  simpa [planarRieszSymbol, planarQuadraticForm, planarFrequencySq,
    planarReflectionMatrix, angularRieszProfile, sub_eq_add_neg] using
      congrArg₂ (fun x y : ℝ => x / y) hn hd

private theorem angularGeometric_re {r ψ : ℝ} :
    (Complex.exp ((ψ : ℂ) * Complex.I) /
      (1 - (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))).re =
        (Real.cos ψ - r) / angularRieszDenominator r ψ := by
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, Complex.sub_im, Complex.one_im, Complex.mul_im]
  have hnorm : Complex.normSq (1 - (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) =
      angularRieszDenominator r ψ := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, Complex.sub_im,
      Complex.one_im, Complex.mul_im, angularRieszDenominator]
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  rw [hnorm, ← add_div]
  congr 1
  linear_combination -r * (Real.sin_sq_add_cos_sq ψ)

/-- A genuine summable cosine series, derived from the complex geometric
series and its real continuous linear map. -/
theorem hasSum_angularGeometric {r : ℝ} (hr : |r| < 1) (ψ : ℝ) :
    HasSum (fun n : ℕ => r ^ n * Real.cos (((n : ℝ) + 1) * ψ))
      ((Real.cos ψ - r) / angularRieszDenominator r ψ) := by
  let w := Complex.exp ((ψ : ℂ) * Complex.I)
  have hw : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I ψ
  have hn : ‖(r : ℂ) * w‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one] using hr
  have h := Complex.hasSum_re ((hasSum_geometric_of_norm_lt_one hn).mul_left w)
  have hfun : (fun n : ℕ => (w * ((r : ℂ) * w) ^ n).re) =
      (fun n : ℕ => r ^ n * Real.cos (((n : ℝ) + 1) * ψ)) := by
    funext n
    have he : w * ((r : ℂ) * w) ^ n =
        (r : ℂ) ^ n * Complex.exp (((((n : ℝ) + 1) * ψ : ℝ) : ℂ) * Complex.I) := by
      dsimp only [w]
      rw [mul_pow, mul_left_comm, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    rw [he]
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  rw [hfun] at h
  convert h using 1
  rw [← div_eq_mul_inv, angularGeometric_re]

/-- The anisotropic reflection profile has its actual summable harmonic
expansion after adding back the displayed constant mode. -/
theorem hasSum_angularRieszProfile {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ψ : ℝ) :
    HasSum (fun n : ℕ => (1 - r ^ 2) * r ^ n * Real.cos (((n : ℝ) + 1) * ψ))
      (angularRieszProfile r ψ + r) := by
  have hr : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hs := (hasSum_angularGeometric hr ψ).mul_left (1 - r ^ 2)
  have he := angularRieszProfile_eq_geometric hr0 hr1 ψ
  convert! hs using 1
  · funext n
    ring
  · linarith

def angularRieszAnisotropy (n : ℕ) : ℝ := 1 - 1 / (2 * ((n : ℝ) + 1))

def angularRieszCoefficient (n : ℕ) : ℝ :=
  (1 - angularRieszAnisotropy n ^ 2) * angularRieszAnisotropy n ^ n

/-- One concrete anisotropy per positive harmonic gives an actual lower
coefficient bound of order 1/n by Bernoulli's inequality. -/
theorem angularRieszCoefficient_lower (n : ℕ) :
    1 / (4 * ((n : ℝ) + 1)) ≤ angularRieszCoefficient n := by
  let r := angularRieszAnisotropy n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hle : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hr0 : 0 ≤ r := by dsimp only [r, angularRieszAnisotropy]; linarith
  have hr1 : r ≤ 1 := by dsimp only [r, angularRieszAnisotropy]; linarith
  have hpow := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ r by linarith) n
  have hhalf : (1 / 2 : ℝ) ≤ r ^ n := by
    have he : (n : ℝ) / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
      nlinarith
    have heq : (n : ℝ) * (r - 1) = -(n : ℝ) / (2 * ((n : ℝ) + 1)) := by
      dsimp only [r, angularRieszAnisotropy]
      ring
    rw [heq] at hpow
    have he' : -(1 / 2 : ℝ) ≤ -(n : ℝ) / (2 * ((n : ℝ) + 1)) := by
      simpa only [neg_div] using neg_le_neg he
    linarith
  have hsize : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 - r ^ 2 := by
    have he : 1 - r = 1 / (2 * ((n : ℝ) + 1)) := by dsimp only [r, angularRieszAnisotropy]; ring
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have ht := mul_le_mul hsize hhalf (by norm_num : (0 : ℝ) ≤ 1 / 2) (by nlinarith : 0 ≤ 1 - r ^ 2)
  unfold angularRieszCoefficient
  change _ ≤ (1 - r ^ 2) * r ^ n
  calc
    _ = (1 / (2 * ((n : ℝ) + 1))) * (1 / 2) := by
      field_simp
      ring
    _ ≤ _ := ht

end
end KernelSeq
