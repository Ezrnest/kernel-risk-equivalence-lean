import KernelSeq.FinitePolynomialLpContinuity
import KernelSeq.SchattenLpAveraging
import KernelSeq.AngularPlanarRiesz

/-!
# Actual angular probability averages of finite matrix polynomials

The normalized angular measure is constructed from Lebesgue measure. Finite
HS-valued integration commutes with the true scalar coefficient average;
joint continuity and the explicit finite coefficient bound then supply all
analytic conditions for the proved Schatten averaging theorem.
-/

open MeasureTheory Set
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- The genuine uniform probability measure on one angular period. -/
def angularRotationMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Ioc 0 (2 * Real.pi))

instance angularRotationMeasure_isProbability : IsProbabilityMeasure angularRotationMeasure where
  measure_univ := by
    simp only [angularRotationMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * Real.pi))]
    have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
    rw [one_div, inv_mul_cancel₀ hp, ENNReal.ofReal_one]

/-- The genuine Bochner integral is the normalized interval integral. -/
theorem integral_angularRotationMeasure {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ → V) :
    (∫ φ, F φ ∂angularRotationMeasure) = (1 / (2 * Real.pi)) • ∫ φ in 0..2 * Real.pi, F φ := by
  rw [angularRotationMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 * Real.pi)),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

variable {J ι H : Type*} [Fintype J] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A true uniform HS bound, depending only on the actual finite matrix
coefficients, for all unit-bounded scalar multipliers and phases. -/
def weightedTrigColumnsHSBound (b : HilbertBasis ι ℝ H) (X Y : J → H →L[ℝ] H) : ℝ :=
  ∑ j, (‖finiteOperatorColumns b (X j)‖ + ‖finiteOperatorColumns b (Y j)‖)

omit [CompleteSpace H] in
theorem weightedTrigColumnsHSBound_nonneg (b : HilbertBasis ι ℝ H) (X Y : J → H →L[ℝ] H) :
    0 ≤ weightedTrigColumnsHSBound b X Y := Finset.sum_nonneg fun j _ => by positivity

omit [CompleteSpace H] in
theorem weightedTrigColumns_norm_le_unit (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (a : J → ℝ) (ha : ∀ j, |a j| ≤ 1) (θ : ℝ × ℝ) :
    ‖weightedTrigColumns b k X Y a θ‖ ≤ weightedTrigColumnsHSBound b X Y := by
  simpa only [one_mul, weightedTrigColumnsHSBound] using
    weightedTrigColumns_norm_le b k X Y a (fun _ => 1) ha θ

omit [CompleteSpace H] in
/-- The actual matrix-polynomial columns are jointly continuous in angle
and torus location when every true multiplier coefficient is continuous. -/
theorem weightedTrigColumns_joint_continuous (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (a : ℝ → J → ℝ) (ha : ∀ j, Continuous (fun φ => a φ j)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => weightedTrigColumns b k X Y (a z.1) z.2) := by
  unfold weightedTrigColumns
  apply continuous_finsetSum
  intro j _
  have hcos : Continuous (fun z : ℝ × (ℝ × ℝ) => Real.cos (integerPlanePhase (k j) z.2)) := by
    unfold integerPlanePhase
    fun_prop
  have hsin : Continuous (fun z : ℝ × (ℝ × ℝ) => Real.sin (integerPlanePhase (k j) z.2)) := by
    unfold integerPlanePhase
    fun_prop
  exact ((((ha j).comp continuous_fst).mul hcos).smul continuous_const).add
    ((((ha j).comp continuous_fst).mul hsin).smul continuous_const)

omit [Fintype J] in
private theorem integrable_angular_weight_coefficient (w : ℝ → ℝ) (a : ℝ → J → ℝ)
    (hw : Continuous w) (ha : ∀ j, Continuous (fun φ => a φ j))
    (hw1 : ∀ φ, |w φ| ≤ 1) (ha1 : ∀ φ j, |a φ j| ≤ 1) (j : J) :
    Integrable (fun φ => w φ * a φ j) angularRotationMeasure := by
  apply Integrable.of_bound (hw.mul (ha j)).stronglyMeasurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun φ => by
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hw1 φ) (ha1 φ j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)

/-- Genuine finite-dimensional coefficient/Bochner interchange in the
original HS space, with every summand's integrability derived explicitly. -/
theorem weightedTrigColumns_angular_integral (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (w : ℝ → ℝ) (a : ℝ → J → ℝ)
    (hw : Continuous w) (ha : ∀ j, Continuous (fun φ => a φ j))
    (hw1 : ∀ φ, |w φ| ≤ 1) (ha1 : ∀ φ j, |a φ j| ≤ 1) (θ : ℝ × ℝ) :
    (∫ φ, w φ • weightedTrigColumns b k X Y (a φ) θ ∂angularRotationMeasure) =
      weightedTrigColumns b k X Y (fun j => ∫ φ, w φ * a φ j ∂angularRotationMeasure) θ := by
  have hi (j : J) := integrable_angular_weight_coefficient w a hw ha hw1 ha1 j
  have hX (j : J) := ((hi j).mul_const (Real.cos (integerPlanePhase (k j) θ))).smul_const
    (finiteOperatorColumns b (X j))
  have hY (j : J) := ((hi j).mul_const (Real.sin (integerPlanePhase (k j) θ))).smul_const
    (finiteOperatorColumns b (Y j))
  have hfun : (fun φ => w φ • weightedTrigColumns b k X Y (a φ) θ) = fun φ => ∑ j, (
      ((w φ * a φ j) * Real.cos (integerPlanePhase (k j) θ)) • finiteOperatorColumns b (X j) +
      ((w φ * a φ j) * Real.sin (integerPlanePhase (k j) θ)) • finiteOperatorColumns b (Y j)) := by
    funext φ
    simp only [weightedTrigColumns, Finset.smul_sum, smul_add, smul_smul, mul_assoc]
  rw [hfun, integral_finsetSum (f := fun j φ =>
    ((w φ * a φ j) * Real.cos (integerPlanePhase (k j) θ)) • finiteOperatorColumns b (X j) +
    ((w φ * a φ j) * Real.sin (integerPlanePhase (k j) θ)) • finiteOperatorColumns b (Y j))
    Finset.univ (fun j _ => (hX j).add (hY j))]
  unfold weightedTrigColumns
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_add (hX j) (hY j), integral_smul_const, integral_smul_const,
    integral_mul_const, integral_mul_const]

/-- Actual scalar-coefficient angular averaging contracts the matrix
polynomial's matching Schatten moment, from the displayed true family bound. -/
theorem weightedTrigColumns_angular_moment_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (w : ℝ → ℝ) (a : ℝ → J → ℝ)
    (hw : Continuous w) (ha : ∀ j, Continuous (fun φ => a φ j))
    (hw1 : ∀ φ, |w φ| ≤ 1) (ha1 : ∀ φ j, |a φ j| ≤ 1)
    {q B : ℝ} (hq : 2 ≤ q) (hB : 0 ≤ B)
    (hmoment : ∀ φ, ∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y (a φ) θ) q ^ q
      ∂fourierSquareMeasure ≤ B ^ q) :
    (∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y
      (fun j => ∫ φ, w φ * a φ j ∂angularRotationMeasure) θ) q ^ q ∂fourierSquareMeasure) ≤ B ^ q := by
  have h := hsSchattenNorm_angular_average_rpow_le_bound
    (ν := angularRotationMeasure) (μ := fourierSquareMeasure) b hq
    (weightedTrigColumnsHSBound_nonneg b X Y) hB
    (fun z : ℝ × (ℝ × ℝ) => weightedTrigColumns b k X Y (a z.1) z.2)
    (weightedTrigColumns_joint_continuous b k X Y a ha).stronglyMeasurable
    (fun φ θ => weightedTrigColumns_norm_le_unit b k X Y (a φ) (ha1 φ) θ)
    w hw.stronglyMeasurable hw1 hmoment
  simpa only [weightedTrigColumns_angular_integral b k X Y w a hw ha hw1 ha1] using h

/-- Concrete rotated anisotropic Riesz family and genuine sine weighting;
the actual zero-frequency symbol is retained, with no angular identity at zero. -/
theorem rotatedRieszPolynomial_sine_average_moment_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    {q B : ℝ} (hq : 2 ≤ q) (hB : 0 ≤ B)
    (hmoment : ∀ φ, ∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y
      (fun j => rotatedAnisotropicRieszSymbol r φ ((k j).1, (k j).2)) θ) q ^ q
        ∂fourierSquareMeasure ≤ B ^ q) :
    (∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y
      (fun j => ∫ φ, Real.sin ((N : ℝ) * φ) *
        rotatedAnisotropicRieszSymbol r φ ((k j).1, (k j).2) ∂angularRotationMeasure) θ) q ^ q
      ∂fourierSquareMeasure) ≤ B ^ q := by
  exact weightedTrigColumns_angular_moment_le b k X Y (fun φ => Real.sin ((N : ℝ) * φ))
    (fun φ j => rotatedAnisotropicRieszSymbol r φ ((k j).1, (k j).2))
    (by fun_prop) (fun j => rotatedAnisotropicRieszSymbol_continuous hr0 hr1 _)
    (fun φ => Real.abs_sin_le_one _) (fun φ j => rotatedAnisotropicRieszSymbol_abs_le r φ _) hq hB hmoment

/-- The actual averaged-coefficient polynomial contracts matching-Lq
norm under a genuine family norm bound; the Bochner/coefficient identity
and every analytic integrability condition are derived above. -/
theorem weightedTrigColumns_angular_norm_le (b : HilbertBasis ι ℝ H) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (w : ℝ → ℝ) (a : ℝ → J → ℝ)
    (hw : Continuous w) (ha : ∀ j, Continuous (fun φ => a φ j))
    (hw1 : ∀ φ, |w φ| ≤ 1) (ha1 : ∀ φ j, |a φ j| ≤ 1)
    {q B : ℝ} (hq : 2 ≤ q) (hB : 0 ≤ B)
    (hfamily : ∀ φ, hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y (a φ)) q ≤ B) :
    hsSchattenLpNorm b fourierSquareMeasure (weightedTrigColumns b k X Y
      (fun j => ∫ φ, w φ * a φ j ∂angularRotationMeasure)) q ≤ B := by
  have hq0 : 0 < q := by linarith
  have hmoment (φ : ℝ) :
      (∫ θ, hsSchattenNorm b (weightedTrigColumns b k X Y (a φ) θ) q ^ q ∂fourierSquareMeasure) ≤ B ^ q := by
    have h := Real.rpow_le_rpow (hsSchattenLpNorm_nonneg b (weightedTrigColumns b k X Y (a φ)) q)
      (hfamily φ) hq0.le
    unfold hsSchattenLpNorm at h
    rwa [Real.rpow_inv_rpow (integral_nonneg fun θ =>
      Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q) hq0.ne'] at h
  have h := hsSchattenLpNorm_angular_average_le_bound
    (ν := angularRotationMeasure) (μ := fourierSquareMeasure) b hq
    (weightedTrigColumnsHSBound_nonneg b X Y) hB
    (fun z : ℝ × (ℝ × ℝ) => weightedTrigColumns b k X Y (a z.1) z.2)
    (weightedTrigColumns_joint_continuous b k X Y a ha).stronglyMeasurable
    (fun φ θ => weightedTrigColumns_norm_le_unit b k X Y (a φ) (ha1 φ) θ)
    w hw.stronglyMeasurable hw1 hmoment
  have heq : (fun θ => ∫ φ, w φ • weightedTrigColumns b k X Y (a φ) θ ∂angularRotationMeasure) =
      weightedTrigColumns b k X Y (fun j => ∫ φ, w φ * a φ j ∂angularRotationMeasure) :=
    funext fun θ => weightedTrigColumns_angular_integral b k X Y w a hw ha hw1 ha1 θ
  rwa [heq] at h

end
end KernelSeq
