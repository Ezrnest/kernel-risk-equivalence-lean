import KernelSeq.FinitePredictionSequenceBayes
import KernelSeq.GaussianRegressionExperiment
import KernelSeq.BayesPriorTruncation

/-!
# The finite Gaussian Bayes lower bound in the full regression decision class

For each fixed target, the actual measurable `L²` representative is replaced
only almost everywhere under the design law. Bessel's inequality first
reduces arbitrary ambient predictions to finite Euclidean coefficients.
Only this finite coefficient loss is interchanged by Tonelli. No joint
measurability of evaluation or norm differences on a nonseparable `L²` space
is assumed.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix WithLp Filter
open scoped ENNReal BigOperators
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

local instance finiteRegressionLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance finiteRegressionLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
local instance finiteRegressionMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) := borel _
local instance finiteRegressionMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

def finiteGaussianRegressionData (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (θ : EuclideanSpace ℝ ι)
    (z : (Fin n → X) × EuclideanSpace ℝ (Fin n)) :
    (Fin n → X) × EuclideanSpace ℝ (Fin n) :=
  (z.1, toLp 2 (fun i => finitePredictionRepresentative k hk jmap θ (z.1 i) + z.2 i))

omit [DecidableEq ι] in
theorem measurable_finiteGaussianRegressionData (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) :
    Measurable (fun p : EuclideanSpace ℝ ι × ((Fin n → X) × EuclideanSpace ℝ (Fin n)) =>
      finiteGaussianRegressionData k hk jmap p.1 p.2) := by
  unfold finiteGaussianRegressionData
  have hm := measurable_finitePredictionRepresentative k hk jmap
  fun_prop

theorem finiteGaussianRegressionData_eq_linear (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (θ : EuclideanSpace ℝ ι)
    (z : (Fin n → X) × EuclideanSpace ℝ (Fin n)) :
    finiteGaussianRegressionData k hk jmap θ z =
      (z.1, GaussianLinearBayes.observation (finitePredictionDesignMatrix k hk jmap z.1) (θ,z.2)) := by
  unfold finiteGaussianRegressionData
  apply Prod.ext
  · rfl
  · rw [GaussianLinearBayes.observation_apply]
    ext i
    change (∑ j, θ j * lpRepresentative (finitePredictionFunction k hk jmap j) (z.1 i)) + z.2 i =
      (∑ j, finitePredictionDesignMatrix k hk jmap z.1 i j * θ j) + z.2 i
    simp only [finitePredictionDesignMatrix_apply, mul_comm]

omit [DecidableEq ι] in
/-- This replacement is done for each fixed coefficient target, so no
joint choice of representatives on the ambient `L²` space is needed. -/
theorem gaussianRegressionData_finiteSignal_ae (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    (θ : EuclideanSpace ℝ ι) (σ : ℝ) :
    gaussianRegressionData μ (n := n)
      (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ) =ᵐ[gaussianRegressionSampleMeasure μ σ n]
        finiteGaussianRegressionData k hk jmap θ := by
  have he := finitePredictionRepresentative_ae_eq k hk jmap θ
  have hall : ∀ᵐ z ∂gaussianRegressionSampleMeasure μ σ n, ∀ i : Fin n,
      lpRepresentative (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ) (z.1 i) =
        finitePredictionRepresentative k hk jmap θ (z.1 i) := by
    apply ae_all_iff.mpr
    intro i
    have hlaw : MeasurePreserving (fun z : (Fin n → X) × EuclideanSpace ℝ (Fin n) => z.1 i)
        (gaussianRegressionSampleMeasure μ σ n) μ :=
      (measurePreserving_eval (fun _ : Fin n => μ) i).comp measurePreserving_fst
    exact hlaw.quasiMeasurePreserving.ae he
  filter_upwards [hall] with z hz
  unfold gaussianRegressionData finiteGaussianRegressionData
  apply Prod.ext
  · rfl
  · ext i
    exact congrArg (fun a : ℝ => a + z.2 i) (hz i)

private theorem finiteCoefficientLoss_integral_swap
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    (v : ι → ℝ) (σ : ℝ)
    (d : (Fin n → X) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ ι) (hd : Measurable d) :
    (∫⁻ θ, ∫⁻ z, ENNReal.ofReal (‖θ-d (finiteGaussianRegressionData k hk jmap θ z)‖^2)
      ∂gaussianRegressionSampleMeasure μ σ n ∂multivariateGaussian 0 (diagonal v)) =
      GaussianLinearBayes.designDecisionRisk (Measure.pi (fun _ : Fin n => μ)) v σ
        (finitePredictionDesignMatrix k hk jmap) d := by
  let F := fun (θ : EuclideanSpace ℝ ι) (xs : Fin n → X) (ε : EuclideanSpace ℝ (Fin n)) =>
    ENNReal.ofReal (‖θ-d (finiteGaussianRegressionData k hk jmap θ (xs,ε))‖^2)
  have hF : Measurable (fun p : (EuclideanSpace ℝ ι × (Fin n → X)) × EuclideanSpace ℝ (Fin n) =>
      F p.1.1 p.1.2 p.2) := by
    have hdata := measurable_finiteGaussianRegressionData (n := n) k hk jmap
    fun_prop
  have hinner : Measurable (fun p : EuclideanSpace ℝ ι × (Fin n → X) =>
      ∫⁻ ε, F p.1 p.2 ε ∂multivariateGaussian 0 (σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    hF.lintegral_prod_right
  calc
    _ = ∫⁻ θ, ∫⁻ xs, ∫⁻ ε, F θ xs ε
        ∂multivariateGaussian 0 (σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        ∂Measure.pi (fun _ : Fin n => μ) ∂multivariateGaussian 0 (diagonal v) := by
      apply lintegral_congr
      intro θ
      apply lintegral_prod
      have hdata : Measurable (fun z : (Fin n → X) × EuclideanSpace ℝ (Fin n) =>
          finiteGaussianRegressionData k hk jmap θ z) :=
        (measurable_finiteGaussianRegressionData (n := n) k hk jmap).comp
          (measurable_const.prodMk measurable_id)
      fun_prop
    _ = ∫⁻ xs, ∫⁻ θ, ∫⁻ ε, F θ xs ε
        ∂multivariateGaussian 0 (σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        ∂multivariateGaussian 0 (diagonal v) ∂Measure.pi (fun _ : Fin n => μ) :=
      lintegral_lintegral_swap hinner.aemeasurable
    _ = ∫⁻ xs, ∫⁻ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin n), F p.1 xs p.2
        ∂GaussianLinearBayes.modelMeasure v σ ∂Measure.pi (fun _ : Fin n => μ) := by
      apply lintegral_congr
      intro xs
      symm
      apply lintegral_prod
      have hfix : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin n) => F p.1 xs p.2) := by
        have hdata : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin n) =>
            finiteGaussianRegressionData k hk jmap p.1 (xs,p.2)) :=
          (measurable_finiteGaussianRegressionData (n := n) k hk jmap).comp
            (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
        fun_prop
      exact hfix.aemeasurable
    _ = _ := by
      rw [GaussianLinearBayes.designDecisionRisk_eq_integral v σ _
        (measurable_finitePredictionDesignMatrix k hk jmap) d hd]
      apply lintegral_congr
      intro xs
      unfold GaussianLinearBayes.decisionRisk
      apply lintegral_congr
      intro p
      dsimp only [F]
      rw [finiteGaussianRegressionData_eq_linear]

/-- Full measurable `L²` prediction rules dominate the actual finite
Gaussian coefficient Bayes risk. Ambient losses are never interchanged. -/
theorem finiteGaussianRegression_coefficientBayes_le_ruleRisk
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    (v : ι → ℝ) (σ : ℝ)
    (d : (Fin n → X) × EuclideanSpace ℝ (Fin n) → Lp ℝ 2 μ) (hd : Measurable d) :
    GaussianLinearBayes.designCoefficientBayesRisk (Measure.pi (fun _ : Fin n => μ)) v σ
      (finitePredictionDesignMatrix k hk jmap) ≤
      predictionRuleBayesRisk (multivariateGaussian 0 (diagonal v)) (gaussianRegressionSampleMeasure μ σ n)
        (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap))
        (fun θ => gaussianRegressionData μ
          (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ)) d := by
  let e := finitePredictionFunction k hk jmap
  let dc := fun z => FinitePredictionBayes.coefficients e (d z)
  have he : Orthonormal ℝ e := finitePredictionFunction_orthonormal k hk jmap hj
  have hdc : Measurable dc := (FinitePredictionBayes.coefficients e).measurable.comp hd
  have hreplace :
      (∫⁻ θ, ∫⁻ z, ENNReal.ofReal (‖θ-dc (finiteGaussianRegressionData k hk jmap θ z)‖^2)
        ∂gaussianRegressionSampleMeasure μ σ n ∂multivariateGaussian 0 (diagonal v)) =
      ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (‖θ-dc (gaussianRegressionData μ
        (FinitePredictionBayes.synthesis e θ) z)‖^2)
        ∂gaussianRegressionSampleMeasure μ σ n ∂multivariateGaussian 0 (diagonal v) := by
    apply lintegral_congr
    intro θ
    apply lintegral_congr_ae
    filter_upwards [gaussianRegressionData_finiteSignal_ae (n := n) k hk jmap θ σ] with z hz
    rw [hz]
  calc
    _ ≤ GaussianLinearBayes.designDecisionRisk (Measure.pi (fun _ : Fin n => μ)) v σ
        (finitePredictionDesignMatrix k hk jmap) dc :=
      iInf_le_of_le dc (iInf_le_of_le hdc le_rfl)
    _ = _ := (finiteCoefficientLoss_integral_swap k hk jmap v σ dc hdc).symm.trans hreplace
    _ ≤ _ := by
      apply lintegral_mono
      intro θ
      apply lintegral_mono
      intro z
      have hb := FinitePredictionBayes.coefficient_loss_le_prediction_loss he θ
        (d (gaussianRegressionData μ (FinitePredictionBayes.synthesis e θ) z))
      refine (ENNReal.ofReal_le_ofReal hb).trans_eq ?_
      congr 2
      exact norm_sub_rev _ _

/-- The full original regression Bayes decision class has the Gaussian
sequence lower bound. All actual finite-design moments are supplied inside
the proof, and no separability of ambient `L²(μ)` is required. -/
theorem finiteGaussianRegression_bayes_ge_sequence
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {v : ι → ℝ} (hv : ∀ j, 0 < v j) {σ : ℝ} (hσ : 0 < σ) :
    ENNReal.ofReal (∑ j, ((v j)⁻¹ + (n : ℝ)*(σ^2)⁻¹)⁻¹) ≤
      predictionBayesRisk (multivariateGaussian 0 (diagonal v)) (gaussianRegressionSampleMeasure μ σ n)
        (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap))
        (fun θ => gaussianRegressionData μ (n := n)
          (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ)) := by
  have hs := GaussianLinearBayes.sequence_bound_le_designCoefficientBayesRisk (κ := Fin n)
    hv hσ (finitePredictionDesignMatrix k hk jmap)
    (measurable_finitePredictionDesignMatrix k hk jmap)
    (finitePredictionDesignMatrix_entry_memLp k hk jmap)
    (integral_finitePredictionDesignMatrix_column_sq k hk jmap)
  simp only [Fintype.card_fin] at hs
  apply hs.trans
  exact le_iInf fun d => le_iInf fun hd =>
    finiteGaussianRegression_coefficientBayes_le_ruleRisk k hk jmap hj v σ d hd

end
end KernelSeq
