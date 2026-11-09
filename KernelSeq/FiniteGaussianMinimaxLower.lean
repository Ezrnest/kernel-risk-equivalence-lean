import KernelSeq.FiniteGaussianRegressionBayes
import KernelSeq.GaussianRangeMinimax
import KernelSeq.SourceNormBounds

/-!
# A genuine finite Gaussian prior gives an original-class minimax lower bound

Actual source membership, the containing prediction ball, and the outside
loss envelope are all derived. The only event condition is positive mass of
the source ball, as needed to define the supported prior. The Pinsker prior
concentration theorem supplies it eventually from the original assumptions.
-/

namespace KernelSeq
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
noncomputable section

variable {X H ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]

local instance finiteMinimaxLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance finiteMinimaxLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

theorem finiteGaussian_minimax_sourceBall_lower
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {κ s R σ : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ)
    (hs : 0 ≤ s) (hR : 0 < R) (hσ : 0 < σ) (n : ℕ)
    (v : ι → ℝ) (hv : ∀ j, 0 < v j)
    (hpos : 0 < (multivariateGaussian 0 (Matrix.diagonal v))
      {θ | finiteSourceEnergy k hk jmap s θ ≤ R^2}) :
    ENNReal.ofReal (∑ j, ((v j)⁻¹+(n : ℝ)*(σ^2)⁻¹)⁻¹) ≤
      gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R) +
      ∫⁻ θ in {θ | finiteSourceEnergy k hk jmap s θ ≤ R^2}ᶜ,
        ENNReal.ofReal (2*((1+κ^2)^(s/2)*R)^2 +
          2*(1+κ^2)^s*finiteSourceEnergy k hk jmap s θ)
        ∂multivariateGaussian 0 (Matrix.diagonal v) := by
  let π := multivariateGaussian 0 (Matrix.diagonal v)
  let C := {θ | finiteSourceEnergy k hk jmap s θ ≤ R^2}
  let g := FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap)
  let B := (1+κ^2)^(s/2)*R
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : MeasurableSet C := by
    apply measurableSet_le _ measurable_const
    unfold finiteSourceEnergy
    fun_prop
  have hclass (θ : EuclideanSpace ℝ ι) (hθ : θ ∈ C) : g θ ∈ featureSourceBall k hk s hs R :=
    finiteSynthesis_mem_sourceBall_of_energy k hk jmap hj hs hR.le θ hθ
  have hnorm (f : Lp ℝ 2 μ) (hf : f ∈ featureSourceBall k hk s hs R) : ‖f‖ ≤ B :=
    featureSourceBall_norm_le k hk hκ hbound hs hf
  have htrunc := predictionBayesRisk_le_minimax_add_tail π
    (gaussianRegressionSampleMeasure μ σ n) g (gaussianRegressionData μ)
    (featureSourceBall k hk s hs R) hB hC hpos hclass hnorm
  have hbayes := finiteGaussianRegression_bayes_ge_sequence (n := n) k hk jmap hj hv hσ
  have hfirst := hbayes.trans htrunc
  apply hfirst.trans
  apply add_le_add (gaussianRegressionMinimaxRisk_le_rangeMinimaxRisk k hk σ n _)
  apply lintegral_mono
  intro θ
  apply ENNReal.ofReal_le_ofReal
  have hnormsq := finitePrediction_norm_sq_le_sourceEnergy k hk jmap hj hκ hbound hs θ
  dsimp only [g, B]
  nlinarith only [hnormsq]

end
end KernelSeq
