import KernelSeq.AngularSineExpansion
import KernelSeq.AngularRieszAveraging
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Actual sine and rotation-Riesz representation of the fixed symbol

The genuine complex circle Fourier series is paired at opposite integer
frequencies. Oddness removes every cosine and constant mode, yielding an
actual positive-frequency real sine series. Each sine is then replaced by
the proved rotation average of actual anisotropic reflection profiles.
No Fourier-reconstruction, harmonic, or multiplier-norm premise is assumed.
-/

open MeasureTheory
open scoped ComplexConjugate
namespace KernelSeq
noncomputable section
local instance fixedRieszPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem angular_fourier_positive_phase (n : ℕ) (ψ : ℝ) :
    fourier (T := 2 * Real.pi) (n : ℤ) (ψ : AddCircle (2 * Real.pi)) =
      (Real.cos ((n : ℝ) * ψ) : ℂ) + (Real.sin ((n : ℝ) * ψ) : ℂ) * Complex.I := by
  have h := congrArg conj (angular_fourier_nat_phase n ψ)
  simpa only [← fourier_neg, neg_neg, map_sub, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, sub_neg_eq_add] using h

/-- Actual scalar sine coefficient in the chosen angular parametrization. -/
def fixedSymbolSineCoefficient (n : ℕ) : ℝ :=
  angularSinMoment lipschitzAngularProfile (n + 1) / Real.pi

/-- Genuine positive-frequency sine reconstruction of the actual fixed
angular profile, derived from Mathlib's actual circle Fourier series. -/
theorem hasSum_fixedSymbol_sine (ψ : ℝ) :
    HasSum (fun n : ℕ => fixedSymbolSineCoefficient n * Real.sin (((n + 1 : ℕ) : ℝ) * ψ))
      (lipschitzAngularProfile ψ) := by
  let f := angularCircleMap lipschitzAngularProfile lipschitzAngularProfile_contDiff.continuous
    lipschitzAngularProfile_periodic
  let term : ℤ → ℂ := fun k => fourierCoeff f k • fourier k (ψ : AddCircle (2 * Real.pi))
  have hzero : term 0 = 0 := by simp only [term, f, lipschitzAngularFourierCoeff_zero, zero_smul]
  have hfull : HasSum term (lipschitzAngularProfile ψ : ℂ) := lipschitzAngularProfile_hasSum_fourier ψ
  have hpair := Complex.hasSum_re hfull.nat_add_neg
  simp only [hzero, add_zero, Complex.ofReal_re] at hpair
  have hshift := (hasSum_nat_add_iff' 1).mpr hpair
  simp only [Finset.sum_range_one, Nat.cast_zero, neg_zero, hzero, add_zero, Complex.zero_re,
    sub_zero] at hshift
  have hp (n : ℕ) : (term ((n + 1 : ℕ) : ℤ) + term (-((n + 1 : ℕ) : ℤ))).re =
      fixedSymbolSineCoefficient n * Real.sin (((n + 1 : ℕ) : ℝ) * ψ) := by
    have hc : fourierCoeff f ((n + 1 : ℕ) : ℤ) =
        -((angularSinMoment lipschitzAngularProfile (n + 1) / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [fourierCoeff_angularCircleMap_nat, lipschitzAngularCosMoment_eq_zero]
      push_cast
      ring
    have hn := fourierCoeff_angularCircleMap_neg lipschitzAngularProfile
      lipschitzAngularProfile_contDiff.continuous lipschitzAngularProfile_periodic ((n + 1 : ℕ) : ℤ)
    change fourierCoeff f (-((n + 1 : ℕ) : ℤ)) = conj (fourierCoeff f ((n + 1 : ℕ) : ℤ)) at hn
    dsimp only [term]
    rw [hn, hc, angular_fourier_positive_phase, angular_fourier_nat_phase]
    simp only [smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      Complex.add_re, Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_zero,
      mul_zero, zero_mul, sub_zero, mul_one, zero_sub]
    unfold fixedSymbolSineCoefficient
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [hp] using hshift

/-- The real sine coefficient's actual Riesz rotation weight. -/
def fixedSymbolRieszWeight (n : ℕ) : ℝ :=
  2 * fixedSymbolSineCoefficient n / angularRieszCoefficient n

/-- Genuine pointwise infinite representation by actual rotated
anisotropic reflection profiles. The normalizing coefficient is derived
from the actual rotation integral, including its factor one half. -/
theorem hasSum_fixedSymbol_rotation_Riesz (ψ : ℝ) :
    HasSum (fun n : ℕ => fixedSymbolRieszWeight n * ((1 / (2 * Real.pi)) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) *
        Real.sin (((n + 1 : ℕ) : ℝ) * φ))) (lipschitzAngularProfile ψ) := by
  convert hasSum_fixedSymbol_sine ψ using 1
  funext n
  rw [angularRieszProfile_selected_sin_average]
  unfold fixedSymbolRieszWeight
  field_simp [(angularRieszCoefficient_pos n).ne']

/-- The actual rotation weights are absolutely summable, by the already
proved cubic Fourier decay and concrete harmonic coefficient lower bound. -/
theorem fixedSymbolRieszWeight_abs_summable : Summable (fun n : ℕ => |fixedSymbolRieszWeight n|) := by
  have hs := angularRieszMomentWeights_summable lipschitzAngularProfile_contDiff lipschitzAngularProfile_periodic
  simp only [lipschitzAngularCosMoment_eq_zero, abs_zero, zero_add] at hs
  refine (hs.mul_left (2 / Real.pi)).congr fun n => ?_
  unfold fixedSymbolRieszWeight fixedSymbolSineCoefficient
  rw [abs_div, abs_mul, abs_div, abs_of_pos (angularRieszCoefficient_pos n),
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

theorem lipschitzAngularProfile_eq_tsum_sine (ψ : ℝ) :
    lipschitzAngularProfile ψ = ∑' n : ℕ,
      fixedSymbolSineCoefficient n * Real.sin (((n + 1 : ℕ) : ℝ) * ψ) :=
  (hasSum_fixedSymbol_sine ψ).tsum_eq.symm

theorem lipschitzAngularProfile_eq_tsum_rotation_Riesz (ψ : ℝ) :
    lipschitzAngularProfile ψ = ∑' n : ℕ,
      fixedSymbolRieszWeight n * ((1 / (2 * Real.pi)) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) *
          Real.sin (((n + 1 : ℕ) : ℝ) * φ)) :=
  (hasSum_fixedSymbol_rotation_Riesz ψ).tsum_eq.symm

/-- The actual fixed planar symbol has the same proved scalar rotation
representation. The existing angular identification includes the zero
vector, where the genuine angular profile value is zero. -/
theorem hasSum_lipschitzEvenSymbol_rotation_Riesz (s t : ℝ) :
    HasSum (fun n : ℕ => fixedSymbolRieszWeight n * ((1 / (2 * Real.pi)) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), angularRieszProfile (angularRieszAnisotropy n)
        (2 * Complex.arg (⟨s, t⟩ : ℂ) - φ) * Real.sin (((n + 1 : ℕ) : ℝ) * φ)))
      (lipschitzEvenSymbol s t) := by
  rw [lipschitzEvenSymbol_eq_angular s t]
  exact hasSum_fixedSymbol_rotation_Riesz _

end
end KernelSeq
