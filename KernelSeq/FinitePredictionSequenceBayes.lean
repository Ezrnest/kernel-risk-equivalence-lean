import KernelSeq.FinitePredictionBayes
import KernelSeq.GaussianBayesSequenceBound

/-!
# Actual population prediction coordinates supply the sequence Bayes lower bound

The normalized design second moments are proved by the actual population
singular functions. They are not additional statistical assumptions. Bessel's
inequality then gives the bound for all measurable ambient `L²(μ)` predictions.
-/

namespace KernelSeq

open MeasureTheory Matrix
open scoped ENNReal BigOperators
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance finiteSequenceLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance finiteSequenceLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

theorem actual_expected_posterior_trace_ge_sequence (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    {v : ι → ℝ} (hv : ∀ j, 0 < v j) {σ : ℝ} (hσ : 0 < σ) :
    (∑ j, ((v j)⁻¹ + (Fintype.card κ : ℝ) * (σ^2)⁻¹)⁻¹) ≤
      ∫ xs, (GaussianLinearBayes.posteriorCovariance v σ
        (finitePredictionDesignMatrix (κ := κ) k hk jmap xs)).trace
        ∂Measure.pi (fun _ : κ => μ) :=
  GaussianLinearBayes.expected_posterior_trace_ge_sequence hv hσ _
    (measurable_finitePredictionDesignMatrix k hk jmap)
    (finitePredictionDesignMatrix_entry_memLp k hk jmap)
    (integral_finitePredictionDesignMatrix_column_sq k hk jmap)

/-- The Gaussian-sequence Bayes lower bound for every measurable actual
prediction rule. Neither Gram moments nor a posterior-risk comparison is a premise. -/
theorem actual_prediction_gaussian_sequence_bayes_lower (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {v : ι → ℝ} (hv : ∀ j, 0 < v j) {σ : ℝ} (hσ : 0 < σ)
    (d : (κ → X) × EuclideanSpace ℝ κ → Lp ℝ 2 μ) (hd : Measurable d) :
    ENNReal.ofReal (∑ j, ((v j)⁻¹ + (Fintype.card κ : ℝ) * (σ^2)⁻¹)⁻¹) ≤
      FinitePredictionBayes.predictionDecisionRisk (Measure.pi (fun _ : κ => μ)) v σ
        (finitePredictionDesignMatrix k hk jmap) (finitePredictionFunction k hk jmap) d := by
  have ht := GaussianLinearBayes.integrable_posterior_trace hv hσ _
    (measurable_finitePredictionDesignMatrix (κ := κ) k hk jmap)
      (ν := Measure.pi (fun _ : κ => μ))
  have hn : ∀ᵐ xs ∂Measure.pi (fun _ : κ => μ), 0 ≤
      (GaussianLinearBayes.posteriorCovariance v σ (finitePredictionDesignMatrix k hk jmap xs)).trace :=
    Filter.Eventually.of_forall fun xs => (GaussianLinearBayes.posteriorCovariance_posDef hv σ _).posSemidef.trace_nonneg
  calc
    _ ≤ ENNReal.ofReal (∫ xs, (GaussianLinearBayes.posteriorCovariance v σ
        (finitePredictionDesignMatrix k hk jmap xs)).trace ∂Measure.pi (fun _ : κ => μ)) :=
      ENNReal.ofReal_le_ofReal (actual_expected_posterior_trace_ge_sequence (κ := κ) k hk jmap hv hσ)
    _ = _ := ofReal_integral_eq_lintegral_ofReal ht hn
    _ ≤ _ := actual_prediction_gaussian_bayes_lower k hk jmap hj hv hσ d hd

end
end KernelSeq
