import KernelSeq.AngularPolynomialAverage
import KernelSeq.FixedPlanarRieszRepresentation
import KernelSeq.RotatedRieszLp

/-!
# Actual sine-averaged planar Riesz operator bounds

The coefficient is the genuine probability-angle integral, with exactly
the normalization in `fixedPlanarRieszAverage`. The rotated-family estimate
is the proved matching-exponent Walsh/Riesz theorem, rather than a norm
certificate supplied to this result.
-/

open MeasureTheory

namespace KernelSeq
noncomputable section

/-- The actual probability-angle coefficient equals the existing actual
normalized interval average. No frequency-zero exception is needed here. -/
theorem angularRotationIntegral_rotatedRiesz_sin_eq (n : ℕ) (ξ : ℝ × ℝ) :
    (∫ φ, Real.sin (((n + 1 : ℕ) : ℝ) * φ) *
      rotatedAnisotropicRieszSymbol (angularRieszAnisotropy n) φ ξ ∂angularRotationMeasure) =
        fixedPlanarRieszAverage n ξ := by
  rw [integral_angularRotationMeasure]
  simp only [smul_eq_mul, fixedPlanarRieszAverage]
  congr 1
  apply intervalIntegral.integral_congr
  intro φ _
  ring

variable {J ι H : Type*} [Fintype J] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every actual modal average has the same linear-in-q matching-Lq
bound as its actual rotated Riesz family. The statement has no analytic
multiplier, martingale or family norm certificate as a hypothesis. -/
theorem fixedPlanarRieszAverage_schattenLpNorm_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (n m : ℕ) :
    hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y
      (fun j => fixedPlanarRieszAverage n (((k j).1 : ℝ), ((k j).2 : ℝ))))
        (dyadicSchattenExponent m) ≤
      (133 * dyadicSchattenExponent m) *
        hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y (fun _ => 1))
          (dyadicSchattenExponent m) := by
  have hq := dyadicSchattenExponent_ge_two m
  have hB : 0 ≤ (133 * dyadicSchattenExponent m) *
      hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y (fun _ => 1))
        (dyadicSchattenExponent m) :=
    mul_nonneg (by linarith) (hsSchattenLpNorm_nonneg b _ _)
  have h := weightedTrigColumns_angular_norm_le b k X Y
    (fun φ => Real.sin (((n + 1 : ℕ) : ℝ) * φ))
    (fun φ j => rotatedAnisotropicRieszSymbol (angularRieszAnisotropy n) φ
      (((k j).1 : ℝ), ((k j).2 : ℝ)))
    (by fun_prop)
    (fun j => rotatedAnisotropicRieszSymbol_continuous (angularRieszAnisotropy_mem n).1
      (angularRieszAnisotropy_mem n).2 _)
    (fun φ => Real.abs_sin_le_one _)
    (fun φ j => rotatedAnisotropicRieszSymbol_abs_le _ φ _) hq hB
    (fun φ => rotatedRiesz_schattenLpNorm_le b k X Y (angularRieszAnisotropy n) φ m)
  simpa only [angularRotationIntegral_rotatedRiesz_sin_eq] using h

end
end KernelSeq
