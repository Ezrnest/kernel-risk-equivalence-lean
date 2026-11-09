import KernelSeq.GaussianDiagonalLaw
import KernelSeq.GaussianWeightedChiSquare
import KernelSeq.GaussianLinearBayes

/-!
# Actual finite Gaussian-prior source energy and its exponential tail

The diagonal multivariate Gaussian is identified with scaled independent
standard coordinates by an actual measure equality. Thus both the exact
energy expectation and the tail concern the original prior law.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix WithLp Filter
open scoped ENNReal NNReal BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scaledGaussianVector (v : ι → ℝ) (z : ι → ℝ) : EuclideanSpace ℝ ι :=
  toLp 2 (fun j => Real.sqrt (v j) * z j)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_scaledGaussianVector (v : ι → ℝ) : Measurable (scaledGaussianVector v) := by
  unfold scaledGaussianVector
  fun_prop

theorem multivariateGaussian_diagonal_eq_scaled_standard (v : ι → ℝ) (hv : ∀ j, 0 ≤ v j) :
    multivariateGaussian 0 (diagonal v) =
      (standardGaussianCoordinates ι).map (scaledGaussianVector v) := by
  let f (j : ι) (x : ℝ) := Real.sqrt (v j) * x
  have hf (j : ι) : Measurable (f j) := by fun_prop [f]
  letI : ∀ j, IsProbabilityMeasure ((gaussianReal 0 1).map (f j)) :=
    fun j => Measure.isProbabilityMeasure_map (hf j).aemeasurable
  have hmap : (standardGaussianCoordinates ι).map (fun z j => f j (z j)) =
      Measure.pi (fun j => gaussianReal 0 (⟨v j, hv j⟩ : ℝ≥0)) := by
    rw [standardGaussianCoordinates, Measure.pi_map_pi (fun j => (hf j).aemeasurable)]
    congr 1
    funext j
    dsimp only [f]
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    exact Subtype.ext (Real.sq_sqrt (hv j))
  rw [multivariateGaussian_diagonal_eq_map_pi v hv, ← hmap,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

def gaussianPriorEnergy (w : ι → ℝ) (θ : EuclideanSpace ℝ ι) : ℝ :=
  ∑ j, w j * θ j ^ 2

omit [DecidableEq ι] in
theorem gaussianPriorEnergy_scaled (v w : ι → ℝ) (hv : ∀ j, 0 ≤ v j) (z : ι → ℝ) :
    gaussianPriorEnergy w (scaledGaussianVector v z) = gaussianQuadraticForm (fun j => w j * v j) z := by
  unfold gaussianPriorEnergy gaussianQuadraticForm
  apply Finset.sum_congr rfl
  intro j _
  change w j * (Real.sqrt (v j) * z j)^2 = (w j*v j)*z j^2
  rw [mul_pow, Real.sq_sqrt (hv j)]
  ring

theorem gaussianPriorEnergy_integrable (v w : ι → ℝ) :
    Integrable (gaussianPriorEnergy w) (multivariateGaussian 0 (diagonal v)) := by
  apply integrable_finsetSum
  intro j _
  have hg : HasGaussianLaw (id : EuclideanSpace ℝ ι → _) (multivariateGaussian 0 (diagonal v)) :=
    IsGaussian.hasGaussianLaw_id
  exact ((hg.map_fun (GaussianLinearBayes.coordinateCLM j)).memLp_two.integrable_sq).const_mul (w j)

/-- The source-energy mean is the actual weighted prior variance sum. -/
theorem integral_gaussianPriorEnergy (v w : ι → ℝ) (hv : ∀ j, 0 ≤ v j) :
    (∫ θ, gaussianPriorEnergy w θ ∂multivariateGaussian 0 (diagonal v)) = ∑ j, w j * v j := by
  have hLp (j : ι) : MemLp (fun θ : EuclideanSpace ℝ ι => θ j) 2
      (multivariateGaussian 0 (diagonal v)) :=
    (IsGaussian.hasGaussianLaw_id.map_fun (GaussianLinearBayes.coordinateCLM j)).memLp_two
  have hm (j : ι) : (∫ θ : EuclideanSpace ℝ ι, θ j ∂multivariateGaussian 0 (diagonal v)) = 0 := by
    change (∫ θ, GaussianLinearBayes.coordinateCLM j θ ∂multivariateGaussian 0 (diagonal v)) = 0
    rw [(GaussianLinearBayes.coordinateCLM j).integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  have hs (j : ι) : (∫ θ : EuclideanSpace ℝ ι, θ j^2 ∂multivariateGaussian 0 (diagonal v)) = v j := by
    have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) (PosSemidef.diagonal hv) j j
    simp only [covariance, hm, sub_zero] at hc
    simpa only [pow_two, diagonal_apply_eq] using hc
  unfold gaussianPriorEnergy
  rw [integral_finsetSum _ (fun j _ => (hLp j).integrable_sq.const_mul (w j))]
  simp_rw [integral_const_mul, hs]

/-- The exponential source-energy tail for the genuine finite Gaussian
prior. Zero variances and zero source weights are allowed. -/
theorem gaussianPriorEnergy_relative_tail (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    {B δ : ℝ} (hB : 0 < B) (hbound : ∀ j, w j * v j ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (multivariateGaussian 0 (diagonal v))
      {θ | (1+δ)*(∑ j, w j*v j) ≤ gaussianPriorEnergy w θ} ≤
      ENNReal.ofReal (Real.exp (-(δ^2*(∑ j, w j*v j))/(32*B))) := by
  have hm : Measurable (gaussianPriorEnergy w) := by unfold gaussianPriorEnergy; fun_prop
  rw [multivariateGaussian_diagonal_eq_scaled_standard v hv,
    Measure.map_apply (measurable_scaledGaussianVector v) (measurableSet_le measurable_const hm)]
  have he : (scaledGaussianVector v) ⁻¹'
      {θ | (1+δ)*(∑ j, w j*v j) ≤ gaussianPriorEnergy w θ} =
      {z | (1+δ)*gaussianQuadraticMean (fun j => w j*v j) ≤ gaussianQuadraticForm (fun j => w j*v j) z} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, gaussianPriorEnergy_scaled v w hv, gaussianQuadraticMean]
  rw [he]
  exact gaussianQuadratic_relative_tail_ennreal (fun j => w j*v j)
    (fun j => mul_nonneg (hw j) (hv j)) hB hbound hδ hδ1

end
end KernelSeq
