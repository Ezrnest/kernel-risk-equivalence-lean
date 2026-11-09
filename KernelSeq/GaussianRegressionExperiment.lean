import KernelSeq.CanonicalGaussianRegression
import KernelSeq.GaussianDiagonalLaw
import KernelSeq.BayesMinimax

/-!
# The full measurable Gaussian regression experiment

The design/noise presentation is measure-equivalent to the actual finite
product of original observation pairs. Risks are nonnegative integrals and
the decision class includes every measurable rule, including infinite-risk
rules. No joint evaluation map on an arbitrary L2 space is assumed.
-/

namespace KernelSeq
open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def gaussianRegressionSampleMeasure (σ : ℝ) (n : ℕ) :
    Measure ((Fin n → X) × EuclideanSpace ℝ (Fin n)) :=
  (Measure.pi (fun _ : Fin n => μ)).prod
    (multivariateGaussian 0 (σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)))

instance gaussianRegressionSampleMeasure_probability (σ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (gaussianRegressionSampleMeasure μ σ n) := by
  unfold gaussianRegressionSampleMeasure
  infer_instance

def gaussianRegressionSampleEquiv (n : ℕ) :
    (Fin n → X × ℝ) ≃ᵐ ((Fin n → X) × EuclideanSpace ℝ (Fin n)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow X ℝ (Fin n)).trans
    ((MeasurableEquiv.refl (Fin n → X)).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ)))

theorem gaussianRegressionSampleEquiv_measurePreserving (σ : ℝ) (n : ℕ) :
    MeasurePreserving (gaussianRegressionSampleEquiv (X := X) n)
      (CanonicalGaussianRegression.sampleMeasure μ σ n) (gaussianRegressionSampleMeasure μ σ n) := by
  have hn : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => CanonicalGaussianRegression.noiseMeasure σ))
      (multivariateGaussian 0 (σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    refine ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, ?_⟩
    exact (multivariateGaussian_noise_eq_map_pi σ).symm
  exact ((MeasurePreserving.id _).prod hn).comp
    (measurePreserving_arrowProdEquivProdArrow X ℝ (Fin n)
      (fun _ => μ) (fun _ => CanonicalGaussianRegression.noiseMeasure σ))

def gaussianRegressionData {n : ℕ} (f : Lp ℝ 2 μ)
    (z : (Fin n → X) × EuclideanSpace ℝ (Fin n)) :
    (Fin n → X) × EuclideanSpace ℝ (Fin n) :=
  (z.1, toLp 2 (fun i => lpRepresentative f (z.1 i) + z.2 i))

omit [IsProbabilityMeasure μ] in
theorem measurable_gaussianRegressionData {n : ℕ} (f : Lp ℝ 2 μ) :
    Measurable (gaussianRegressionData μ (n := n) f) := by
  unfold gaussianRegressionData
  have hm := lpRepresentative_measurable f
  fun_prop

local instance regressionLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance regressionLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

def gaussianRegressionRisk (σ : ℝ) {n : ℕ}
    (d : (Fin n → X) × EuclideanSpace ℝ (Fin n) → Lp ℝ 2 μ) (f : Lp ℝ 2 μ) : ℝ≥0∞ :=
  predictionDecisionRisk (gaussianRegressionSampleMeasure μ σ n) (gaussianRegressionData μ) d f

def gaussianRegressionMinimaxRisk (σ : ℝ) (n : ℕ) (F : Set (Lp ℝ 2 μ)) : ℝ≥0∞ :=
  predictionMinimaxRisk (gaussianRegressionSampleMeasure μ σ n) (gaussianRegressionData μ) F

/-- The full measurable-rule risk is exactly the risk under the original
i.i.d. design/Gaussian-noise observation-pair sample. -/
theorem gaussianRegressionRisk_eq_raw_sample {σ : ℝ} {n : ℕ}
    (d : (Fin n → X) × EuclideanSpace ℝ (Fin n) → Lp ℝ 2 μ) (hd : Measurable d)
    (f : Lp ℝ 2 μ) :
    gaussianRegressionRisk μ σ d f =
      ∫⁻ ω : Fin n → X × ℝ, ENNReal.ofReal
        (‖d ((fun i => (ω i).1), toLp 2 (fun i => lpRepresentative f (ω i).1 + (ω i).2))-f‖^2)
        ∂CanonicalGaussianRegression.sampleMeasure μ σ n := by
  unfold gaussianRegressionRisk predictionDecisionRisk
  rw [← (gaussianRegressionSampleEquiv_measurePreserving μ σ n).map_eq]
  have hm : Measurable (fun z => ENNReal.ofReal (‖d (gaussianRegressionData μ f z)-f‖^2)) := by
    have hdata := measurable_gaussianRegressionData μ (n := n) f
    fun_prop
  rw [lintegral_map hm (gaussianRegressionSampleEquiv (X := X) n).measurable]
  rfl

end
end KernelSeq
