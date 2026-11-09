import KernelSeq.WalshRieszLp
import KernelSeq.WalshZeroStart
import KernelSeq.AngularPlanarRiesz
import KernelSeq.FinitePolynomialLpContinuity
import KernelSeq.SchattenLpAveraging

/-!
# Actual rotated anisotropic Riesz matching-exponent bounds

The two genuine planar directions identify the rotated reflection symbol
with the proved anisotropic Riesz multiplier. The true finite Walsh theorem
supplies constant 133; no Walsh, multiplier-moment or norm certificate is
an input. Explicit finite HS bounds supply genuine moment integrability.
The scalar anisotropy r and rotation angle are unrestricted.
-/

open MeasureTheory
open scoped BigOperators
namespace KernelSeq
noncomputable section

variable {J ι H : Type*} [Fintype J] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem rotatedRiesz_direction_symbol_eq (r φ : ℝ) (ξ : ℝ × ℝ) :
    planarRieszSymbol planarReflectionMatrix
      (ξ.1 * ((1 - r) * Real.cos (φ / 2)) + ξ.2 * ((1 - r) * Real.sin (φ / 2)),
        ξ.1 * (-(1 + r) * Real.sin (φ / 2)) + ξ.2 * ((1 + r) * Real.cos (φ / 2))) =
      rotatedAnisotropicRieszSymbol r φ ξ := by
  unfold rotatedAnisotropicRieszSymbol
  congr 1
  apply Prod.ext <;> dsimp only <;> ring

/-- Genuine matching-exponent moment bound for every actual rotated
anisotropic Riesz multiplier on the finite real matrix polynomial. -/
theorem rotatedRiesz_schattenMoment_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (r φ : ℝ) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ)) • X j)
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ)) • Y j) θ))
        (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (133 * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ))
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  let u : ℝ × ℝ := ((1 - r) * Real.cos (φ / 2), (1 - r) * Real.sin (φ / 2))
  let v : ℝ × ℝ := (-(1 + r) * Real.sin (φ / 2), (1 + r) * Real.cos (φ / 2))
  have hs (j : J) : planarRieszSymbol planarReflectionMatrix
      (((k j).1 : ℝ) * u.1 + ((k j).2 : ℝ) * u.2,
        ((k j).1 : ℝ) * v.1 + ((k j).2 : ℝ) * v.2) =
      rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ)) := by
    simpa only [u, v] using rotatedRiesz_direction_symbol_eq r φ (((k j).1 : ℝ), ((k j).2 : ℝ))
  simpa only [hs] using
    anisotropicRiesz_schattenMoment_le_of_walsh finiteWalshLpTransformBound_proved b k X Y u v m

omit [CompleteSpace H] in
/-- The actual rotated polynomial columns have an explicit uniform HS
bound independent of r, angle and torus location. -/
theorem rotatedRiesz_weightedTrigColumns_norm_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (r φ : ℝ) (θ : ℝ × ℝ) :
    ‖weightedTrigColumns b k X Y
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ))) θ‖ ≤
      ∑ j, (‖finiteOperatorColumns b (X j)‖ + ‖finiteOperatorColumns b (Y j)‖) := by
  simpa only [one_mul] using weightedTrigColumns_norm_le b k X Y
    (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ))) (fun _ => 1)
    (fun j => rotatedAnisotropicRieszSymbol_abs_le r φ _) θ

/-- Genuine integrability follows from actual continuous finite columns
and their explicit uniform HS bound, with no moment premise. -/
theorem rotatedRiesz_schattenMoment_integrable (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (r φ : ℝ) (m : ℕ) :
    Integrable (fun θ => hsSchattenNorm b (weightedTrigColumns b k X Y
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ))) θ)
        (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m)) fourierSquareMeasure := by
  let M := ∑ j, (‖finiteOperatorColumns b (X j)‖ + ‖finiteOperatorColumns b (Y j)‖)
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => by positivity
  exact integrable_hsSchattenNorm_rpow_of_bound b (dyadicSchattenExponent_ge_two m) hM _
    (weightedTrigColumns_continuous b k X Y _).stronglyMeasurable
    (fun θ => rotatedRiesz_weightedTrigColumns_norm_le b k X Y r φ θ)

/-- The moment bound in terms of the actual weighted polynomial columns,
with the input represented by the genuine constant weight one. -/
theorem rotatedRiesz_weightedTrigColumns_moment_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (r φ : ℝ) (m : ℕ) :
    (∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ))) θ)
        (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure) ≤
      (133 * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        ∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y (fun _ => 1) θ)
          (dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) ∂fourierSquareMeasure := by
  simpa only [weightedTrigColumns_eq, one_smul] using rotatedRiesz_schattenMoment_le b k X Y r φ m

/-- The actual matching-Lq norm bound, obtained by taking the genuine
positive qth root. Zero input and zero output require no division. -/
theorem rotatedRiesz_schattenLpNorm_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (r φ : ℝ) (m : ℕ) :
    hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y
      (fun j => rotatedAnisotropicRieszSymbol r φ (((k j).1 : ℝ), ((k j).2 : ℝ))))
        (dyadicSchattenExponent m) ≤
      (133 * dyadicSchattenExponent m) *
        hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y (fun _ => 1))
          (dyadicSchattenExponent m) := by
  let q := dyadicSchattenExponent m
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (dyadicSchattenExponent_ge_two m)
  have h := Real.rpow_le_rpow
    (integral_nonneg fun θ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q)
    (rotatedRiesz_weightedTrigColumns_moment_le b k X Y r φ m) (inv_nonneg.mpr hq.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 133 * q) q)
    (integral_nonneg fun θ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q),
    Real.rpow_rpow_inv (by positivity : (0 : ℝ) ≤ 133 * q) hq.ne'] at h
  exact h

end
end KernelSeq
