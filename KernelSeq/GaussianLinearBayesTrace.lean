import KernelSeq.GaussianLinearBayesDesign

/-!
# The genuine finite expected posterior trace

The posterior trace is bounded by the actual prior trace, so its design
expectation is a genuine integrable Bochner integral. Extended-real Bayes
risk therefore equals that expectation, without assigning zero to a
nonintegrable loss or imposing a finite-risk condition on decision rules.
-/

namespace KernelSeq.GaussianLinearBayes

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ENNReal BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance gaussianTraceMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) :=
  borel _
local instance gaussianTraceMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

theorem prior_coordinate_integral (v : ι → ℝ) (σ : ℝ) (i : ι) :
    (∫ ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ, ω.1 i ∂modelMeasure v σ) = 0 := by
  change (∫ ω, coordinateCLM i ω.1 ∂modelMeasure (κ := κ) v σ) = 0
  rw [(coordinateCLM i).integral_comp_comm (prior_hasGaussianLaw v σ).integrable,
    integral_prior, map_zero]

theorem prior_integral_norm_sq {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) :
    (∫ ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ, ‖ω.1‖^2 ∂modelMeasure v σ) =
      (priorCovariance v).trace := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => (prior_coordinate_memLp (κ := κ) v σ i).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  have hc := covariance_prior (κ := κ) hv σ i i
  simp only [covariance, prior_coordinate_integral, sub_zero] at hc
  simpa only [pow_two, Matrix.diag_apply] using hc

theorem decisionRisk_zero {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    decisionRisk v σ Φ (fun _ => 0) = ENNReal.ofReal (priorCovariance v).trace := by
  unfold decisionRisk
  simp only [sub_zero]
  have hLp := (prior_hasGaussianLaw (κ := κ) v σ).memLp_two
  rw [← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hLp.1).mp hLp)
    (Eventually.of_forall fun _ => sq_nonneg _), prior_integral_norm_sq hv σ]

theorem posterior_trace_le_prior_trace {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    (posteriorCovariance v σ Φ).trace ≤ (priorCovariance v).trace := by
  have ht := trace_le_decisionRisk hv hσ Φ (fun _ => 0) measurable_const
  rw [decisionRisk_zero hv σ Φ] at ht
  exact (ENNReal.ofReal_le_ofReal_iff (priorCovariance_posDef hv).posSemidef.trace_nonneg).mp ht

variable {X : Type*} [MeasurableSpace X]

omit [DecidableEq κ] in
theorem measurable_posterior_trace {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    Measurable (fun x => (posteriorCovariance v σ (Φ x)).trace) :=
  (posteriorCovariance_continuous hv σ).matrix_trace.measurable.comp hΦ

theorem integrable_posterior_trace {ν : Measure X} [IsFiniteMeasure ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    Integrable (fun x => (posteriorCovariance v σ (Φ x)).trace) ν := by
  apply (integrable_const ((priorCovariance v).trace)).mono'
    (measurable_posterior_trace hv σ Φ hΦ).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (posteriorCovariance_posDef hv σ (Φ x)).posSemidef.trace_nonneg]
    exact posterior_trace_le_prior_trace hv hσ (Φ x)

/-- This is the manuscript's `E_X Tr C_X`, with integrability derived from
the actual Gaussian model and all measurable decisions retained. -/
theorem designCoefficientBayesRisk_eq_expected_trace {ν : Measure X} [IsFiniteMeasure ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    designCoefficientBayesRisk ν v σ Φ =
      ENNReal.ofReal (∫ x, (posteriorCovariance v σ (Φ x)).trace ∂ν) := by
  rw [designCoefficientBayesRisk_eq_integral_trace hv hσ Φ hΦ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_posterior_trace hv hσ Φ hΦ)
      (Eventually.of_forall fun x => (posteriorCovariance_posDef hv σ (Φ x)).posSemidef.trace_nonneg)]

end
end KernelSeq.GaussianLinearBayes
