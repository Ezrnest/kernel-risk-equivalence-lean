import KernelSeq.GaussianLinearBayes
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian linear Bayes risk against every measurable decision

Losses are nonnegative extended-real integrals, so nonintegrable decisions
are included without the default-zero convention of a Bochner integral.
The posterior residual's independence, centering and covariance are genuine
conclusions of the actual Gaussian model.
-/

namespace KernelSeq.GaussianLinearBayes

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section

private theorem centered_integral_sq_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ]
    (hLp : MemLp id 2 μ) (hmean : (∫ x, x ∂μ) = 0) (z : E) :
    (∫ x, ‖x-z‖^2 ∂μ) = (∫ x, ‖x‖^2 ∂μ) + ‖z‖^2 := by
  have hnorm : Integrable (fun x : E => ‖x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hLp.1).mp hLp
  have hid := hLp.integrable (by norm_num)
  have hinner : Integrable (fun x : E => inner ℝ z x) μ := hid.const_inner z
  have he (x : E) : ‖x-z‖^2 = ‖x‖^2 + ‖z‖^2 - 2*inner ℝ z x := by
    rw [norm_sub_sq_real, real_inner_comm]
    ring
  simp_rw [he]
  have hsub := integral_sub (hnorm.add (integrable_const (‖z‖^2))) (hinner.const_mul 2)
  simp only [Pi.add_apply] at hsub
  have hinner0 : (∫ x : E, inner ℝ z x ∂μ) = 0 := by
    simpa only [id_eq, hmean, inner_zero_right] using (integral_inner (𝕜 := ℝ) hid z)
  rw [hsub,
    integral_add hnorm (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_const_mul, hinner0, mul_zero, sub_zero]

private theorem centered_lintegral_sq_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ]
    (hLp : MemLp id 2 μ) (hmean : (∫ x, x ∂μ) = 0) (z : E) :
    (∫⁻ x, ENNReal.ofReal (‖x-z‖^2) ∂μ) =
      ENNReal.ofReal ((∫ x, ‖x‖^2 ∂μ) + ‖z‖^2) := by
  have hshift : MemLp (fun x : E => x-z) 2 μ := hLp.sub (memLp_const z)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hshift.1).mp hshift)
    (Eventually.of_forall fun _ => sq_nonneg _), centered_integral_sq_sub hLp hmean]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem posteriorResidual_coordinate_integral (v : ι → ℝ) (σ : ℝ)
    (Φ : Matrix κ ι ℝ) (i : ι) :
    (∫ ω, posteriorResidual v σ Φ ω i ∂modelMeasure v σ) = 0 := by
  change (∫ ω, coordinateCLM i (posteriorResidual v σ Φ ω) ∂modelMeasure v σ) = 0
  rw [(coordinateCLM i).integral_comp_comm (posteriorResidual_hasGaussianLaw v σ Φ).integrable,
    posteriorResidual_integral, map_zero]

/-- The true expected squared residual is the trace of inverse precision. -/
theorem posteriorResidual_integral_norm_sq {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    (∫ ω, ‖posteriorResidual v σ Φ ω‖^2 ∂modelMeasure v σ) =
      (posteriorCovariance v σ Φ).trace := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  have hi (i : ι) : Integrable (fun ω => (posteriorResidual v σ Φ ω i)^2) (modelMeasure v σ) :=
    (statistic_coordinate_memLp v σ (residualFactor v σ Φ) (-gain v σ Φ) i).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hc := covariance_posteriorResidual hv hσ Φ i i
  simp only [covariance, posteriorResidual_coordinate_integral, sub_zero] at hc
  simpa only [pow_two, Matrix.diag_apply] using hc

def residualLaw (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (modelMeasure v σ).map (posteriorResidual v σ Φ)

instance residualLaw_probability (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    IsProbabilityMeasure (residualLaw v σ Φ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem residualLaw_memLp (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    MemLp id 2 (residualLaw v σ Φ) :=
  (posteriorResidual_hasGaussianLaw v σ Φ).isGaussian_map.memLp_two_id

theorem residualLaw_integral (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    (∫ x, x ∂residualLaw v σ Φ) = 0 := by
  rw [residualLaw, integral_map (by fun_prop) (by fun_prop), posteriorResidual_integral]

theorem residualLaw_integral_norm_sq {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    (∫ x, ‖x‖^2 ∂residualLaw v σ Φ) = (posteriorCovariance v σ Φ).trace := by
  rw [residualLaw, integral_map (by fun_prop) (by fun_prop), posteriorResidual_integral_norm_sq hv hσ]

/-- The extended-real coefficient risk includes all measurable rules,
including those with infinite risk. -/
def decisionRisk (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ)
    (d : EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (‖ω.1 - d (observation Φ ω)‖^2) ∂modelMeasure v σ

/-- Every measurable decision has Bayes risk at least inverse-precision
trace. Neither linearity nor finite risk is assumed for the decision. -/
theorem trace_le_decisionRisk {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ)
    (d : EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) (hd : Measurable d) :
    ENNReal.ofReal (posteriorCovariance v σ Φ).trace ≤ decisionRisk v σ Φ d := by
  let R := posteriorResidual v σ Φ
  let Y := observation Φ
  let K := matrixCLM (gain v σ Φ)
  let P := modelMeasure (κ := κ) v σ
  let L : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (‖z.1 - (d z.2 - K z.2)‖^2)
  have hL : Measurable L := by fun_prop
  have hmap : P.map (fun ω => (R ω, Y ω)) = (residualLaw v σ Φ).prod (P.map Y) :=
    (posteriorResidual_independent_observation hv hσ Φ).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop)
  have hrisk : decisionRisk v σ Φ d = ∫⁻ z, L z ∂((residualLaw v σ Φ).prod (P.map Y)) := by
    rw [← hmap, lintegral_map hL (by fun_prop)]
    apply lintegral_congr
    intro ω
    dsimp only [decisionRisk, L, R, Y, K, P]
    rw [posteriorResidual_eq]
    congr 2
    abel_nf
  rw [hrisk, lintegral_prod_symm _ hL.aemeasurable]
  have hpY : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    _ = ∫⁻ _y, ENNReal.ofReal (posteriorCovariance v σ Φ).trace ∂P.map Y := by
      rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [L]
      rw [centered_lintegral_sq_sub (residualLaw_memLp v σ Φ)
        (residualLaw_integral v σ Φ), residualLaw_integral_norm_sq hv hσ]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))

/-- The genuine linear posterior mean attains the bound over the entire
measurable decision class. -/
theorem decisionRisk_posteriorMean {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    decisionRisk v σ Φ (matrixCLM (gain v σ Φ)) =
      ENNReal.ofReal (posteriorCovariance v σ Φ).trace := by
  unfold decisionRisk
  simp_rw [← posteriorResidual_eq]
  have hLp := (posteriorResidual_hasGaussianLaw v σ Φ).memLp_two
  rw [← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hLp.1).mp hLp)
    (Eventually.of_forall fun _ => sq_nonneg _), posteriorResidual_integral_norm_sq hv hσ]

/-- The infimum is over the entire measurable finite-coordinate decision
class, without a finite-risk or linearity restriction. -/
def coefficientBayesRisk (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : ℝ≥0∞ :=
  ⨅ (d : EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) (_hd : Measurable d), decisionRisk v σ Φ d

theorem coefficientBayesRisk_eq_trace {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    coefficientBayesRisk v σ Φ = ENNReal.ofReal (posteriorCovariance v σ Φ).trace := by
  unfold coefficientBayesRisk
  apply le_antisymm
  · have hd : Measurable (matrixCLM (gain v σ Φ)) := by fun_prop
    exact iInf_le_of_le (matrixCLM (gain v σ Φ))
      (iInf_le_of_le hd (decisionRisk_posteriorMean hv hσ Φ).le)
  · exact le_iInf fun d => le_iInf fun hd => trace_le_decisionRisk hv hσ Φ d hd

end
end KernelSeq.GaussianLinearBayes
