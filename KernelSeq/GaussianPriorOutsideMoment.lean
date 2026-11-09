import KernelSeq.GaussianPriorQuadratic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exponential and outside-ball moments of the actual Gaussian prior

The genuine diagonal Gaussian law supplies exponential integrability and
the square moment used by Cauchy--Schwarz. No tail or moment certificate is
assumed. These estimates allow the finite coordinate type to vary later.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped ENNReal BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem gaussianPriorEnergy_nonneg (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (θ : EuclideanSpace ℝ ι) : 0 ≤ gaussianPriorEnergy w θ :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))

theorem gaussianPriorEnergy_exp_integrable (v w : ι → ℝ) (hv : ∀ j, 0 ≤ v j)
    (hsmall : ∀ j, w j*v j < 1/2) :
    Integrable (fun θ => Real.exp (gaussianPriorEnergy w θ))
      (multivariateGaussian 0 (diagonal v)) := by
  rw [multivariateGaussian_diagonal_eq_scaled_standard v hv]
  apply (integrable_map_measure (by unfold gaussianPriorEnergy; fun_prop : AEStronglyMeasurable
    (fun θ => Real.exp (gaussianPriorEnergy w θ))
      ((standardGaussianCoordinates ι).map (scaledGaussianVector v)))
    (measurable_scaledGaussianVector v).aemeasurable).mpr
  have hi := (gaussianQuadratic_exp_integrable (fun j => w j*v j)
    (t := 1) (by simpa using hsmall)).const_mul
      (Real.exp (gaussianQuadraticMean (fun j => w j*v j)))
  have he : (fun z => Real.exp (gaussianPriorEnergy w (scaledGaussianVector v z))) =
      (fun z => Real.exp (gaussianQuadraticMean (fun j => w j*v j))*
        Real.exp (1*(gaussianQuadraticForm (fun j => w j*v j) z-
          gaussianQuadraticMean (fun j => w j*v j)))) := by
    funext z
    rw [gaussianPriorEnergy_scaled v w hv, ← Real.exp_add]
    congr 1
    ring
  simpa only [Function.comp_def, he] using hi

theorem integral_gaussianPriorEnergy_exp_le (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    {B : ℝ} (hB : B ≤ 1/4) (hbound : ∀ j, w j*v j ≤ B) :
    (∫ θ, Real.exp (gaussianPriorEnergy w θ) ∂multivariateGaussian 0 (diagonal v)) ≤
      Real.exp (2*∑ j, w j*v j) := by
  let b := fun j => w j*v j
  have hb (j : ι) : 0 ≤ b j := mul_nonneg (hw j) (hv j)
  have h1 (j : ι) : 1*b j ≤ 1/4 := by simpa only [one_mul] using (hbound j).trans hB
  have hm : Measurable (fun θ => Real.exp (gaussianPriorEnergy w θ)) := by
    unfold gaussianPriorEnergy
    fun_prop
  rw [multivariateGaussian_diagonal_eq_scaled_standard v hv,
    integral_map (measurable_scaledGaussianVector v).aemeasurable hm.aestronglyMeasurable]
  have he : (fun z => Real.exp (gaussianPriorEnergy w (scaledGaussianVector v z))) =
      (fun z => Real.exp (gaussianQuadraticMean b)*
        Real.exp (1*(gaussianQuadraticForm b z-gaussianQuadraticMean b))) := by
    funext z
    rw [gaussianPriorEnergy_scaled v w hv, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul]
  have hsq : (∑ j, b j^2) ≤ B*∑ j, b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (hb j) (sub_nonneg.mpr (hbound j))]
  have hS : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
  have hh := mul_le_mul_of_nonneg_left (gaussianQuadratic_exp_integral_le b
    (fun j => by simpa only [one_mul] using hb j) h1) (Real.exp_pos (gaussianQuadraticMean b)).le
  refine hh.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [gaussianQuadraticMean, b]
  nlinarith [mul_nonneg hS (show 0 ≤ 1-4*B by linarith)]

theorem gaussianPriorEnergy_memLp_two (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hsmall : ∀ j, w j*v j < 1/2) :
    MemLp (gaussianPriorEnergy w) 2 (multivariateGaussian 0 (diagonal v)) := by
  apply (memLp_two_iff_integrable_sq (by unfold gaussianPriorEnergy; fun_prop)).mpr
  apply ((gaussianPriorEnergy_exp_integrable v w hv hsmall).const_mul 2).mono'
    (by unfold gaussianPriorEnergy; fun_prop)
  filter_upwards [] with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := Real.pow_div_factorial_le_exp (gaussianPriorEnergy w θ)
    (gaussianPriorEnergy_nonneg w hw θ) 2
  norm_num at hh
  linarith

theorem integral_gaussianPriorEnergy_sq_le (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    {B : ℝ} (hB : B ≤ 1/4) (hbound : ∀ j, w j*v j ≤ B) :
    (∫ θ, (gaussianPriorEnergy w θ)^2 ∂multivariateGaussian 0 (diagonal v)) ≤
      2*Real.exp (2*∑ j, w j*v j) := by
  have hsmall (j : ι) : w j*v j < 1/2 := (hbound j).trans_lt (by linarith)
  have hmono := integral_mono (gaussianPriorEnergy_memLp_two v w hv hw hsmall).integrable_sq
    ((gaussianPriorEnergy_exp_integrable v w hv hsmall).const_mul 2) (fun θ => by
      have hh := Real.pow_div_factorial_le_exp (gaussianPriorEnergy w θ)
        (gaussianPriorEnergy_nonneg w hw θ) 2
      norm_num at hh
      linarith)
  rw [integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (integral_gaussianPriorEnergy_exp_le v w hv hw hB hbound) (by norm_num))

theorem gaussianPriorEnergy_setIntegral_le (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hsmall : ∀ j, w j*v j < 1/2) (E : Set (EuclideanSpace ℝ ι)) (hE : MeasurableSet E) :
    (∫ θ in E, gaussianPriorEnergy w θ ∂multivariateGaussian 0 (diagonal v)) ≤
      Real.sqrt (∫ θ, (gaussianPriorEnergy w θ)^2 ∂multivariateGaussian 0 (diagonal v))*
        Real.sqrt ((multivariateGaussian 0 (diagonal v)).real E) := by
  let P := multivariateGaussian (0 : EuclideanSpace ℝ ι) (diagonal v)
  have hg : MemLp (E.indicator (fun _ => (1 : ℝ))) 2 P := (memLp_const 1).indicator hE
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) (f := gaussianPriorEnergy w) (g := E.indicator (fun _ => (1 : ℝ)))
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall (gaussianPriorEnergy_nonneg w hw))
    (Eventually.of_forall (fun θ => by by_cases h : θ ∈ E <;> simp [h]))
    (by simpa using gaussianPriorEnergy_memLp_two v w hv hw hsmall) (by simpa using hg)
  have he : (fun θ => gaussianPriorEnergy w θ*(E.indicator (fun _ => (1 : ℝ))) θ) =
      E.indicator (gaussianPriorEnergy w) := by
    funext θ
    by_cases h : θ ∈ E <;> simp [h]
  have he2 : (fun θ => ((E.indicator (fun _ => (1 : ℝ))) θ)^2) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext θ
    by_cases h : θ ∈ E <;> simp [h]
  simp only [Real.rpow_two, he, he2, integral_indicator hE, integral_const, smul_eq_mul,
    mul_one, ← Real.sqrt_eq_rpow] at hh
  simpa only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter] using hh

def priorShavingExponent (δ R : ℝ) : ℝ := δ^2*(1-δ)*R^2/1024

theorem priorShavingExponent_pos {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R) :
    0 < priorShavingExponent δ R := by unfold priorShavingExponent; positivity

theorem gaussianPriorEnergy_outside_tail (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    {δ R B : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (_hR : 0 < R) (hB : 0 < B)
    (hbound : ∀ j, w j*v j ≤ B)
    (hSlo : (1-δ)*R^2/2 ≤ ∑ j, w j*v j)
    (hShi : (∑ j, w j*v j) ≤ (1-δ/2)*R^2) :
    (multivariateGaussian 0 (diagonal v)) {θ | R^2 < gaussianPriorEnergy w θ} ≤
      ENNReal.ofReal (Real.exp (-priorShavingExponent δ R/B)) := by
  have hsubset : {θ | R^2 < gaussianPriorEnergy w θ} ⊆
      {θ | (1+δ/4)*(∑ j, w j*v j) ≤ gaussianPriorEnergy w θ} := by
    intro θ hθ
    have hmul := mul_le_mul_of_nonneg_left hShi (by positivity : 0 ≤ 1+δ/4)
    have hs : (1+δ/4)*((1-δ/2)*R^2) ≤ R^2 := by nlinarith [sq_nonneg R, sq_nonneg δ]
    exact le_trans (hmul.trans hs) hθ.le
  refine (measure_mono hsubset).trans ((gaussianPriorEnergy_relative_tail v w hv hw
    hB hbound (by positivity : 0 < δ/4) (by linarith : δ/4 ≤ 1)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < 32*B) hB).mpr
  unfold priorShavingExponent
  have hm := mul_le_mul_of_nonneg_left hSlo (sq_nonneg δ)
  nlinarith

/-- A true outside first moment, obtained from the internally proved
exponential square moment and the actual Gaussian probability tail. -/
theorem gaussianPriorEnergy_outside_moment_le (v w : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    {δ R B : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R) (hB : 0 < B)
    (hBsmall : B ≤ 1/4) (hbound : ∀ j, w j*v j ≤ B)
    (hSlo : (1-δ)*R^2/2 ≤ ∑ j, w j*v j)
    (hShi : (∑ j, w j*v j) ≤ (1-δ/2)*R^2) :
    (∫ θ in {θ | R^2 < gaussianPriorEnergy w θ}, gaussianPriorEnergy w θ
      ∂multivariateGaussian 0 (diagonal v)) ≤
      Real.sqrt (2*Real.exp (2*R^2))*Real.exp (-priorShavingExponent δ R/(2*B)) := by
  have hsmall (j : ι) : w j*v j < 1/2 := (hbound j).trans_lt (by linarith)
  have ht := gaussianPriorEnergy_outside_tail v w hv hw hδ hδ1 hR hB hbound hSlo hShi
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at htr
  have hSr : (∑ j, w j*v j) ≤ R^2 := by nlinarith [sq_nonneg R]
  have hsq : (∫ θ, (gaussianPriorEnergy w θ)^2 ∂multivariateGaussian 0 (diagonal v)) ≤
      2*Real.exp (2*R^2) :=
    (integral_gaussianPriorEnergy_sq_le v w hv hw hBsmall hbound).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have hE : MeasurableSet {θ | R^2 < gaussianPriorEnergy w θ} := by
    exact measurableSet_lt measurable_const (by unfold gaussianPriorEnergy; fun_prop)
  refine (gaussianPriorEnergy_setIntegral_le v w hv hw hsmall _ hE).trans ?_
  calc
    _ ≤ Real.sqrt (2*Real.exp (2*R^2))*Real.sqrt (Real.exp (-priorShavingExponent δ R/B)) :=
      mul_le_mul (Real.sqrt_le_sqrt hsq) (Real.sqrt_le_sqrt htr)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.exp_half]
      congr 2
      ring

end
end KernelSeq
