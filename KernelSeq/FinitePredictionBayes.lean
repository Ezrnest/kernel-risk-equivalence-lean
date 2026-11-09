import KernelSeq.GaussianLinearBayesTrace
import KernelSeq.CanonicalGaussianRegression
import KernelSeq.SingularSystem

/-!
# From arbitrary prediction rules to actual finite Gaussian coefficients

Bessel's inequality applies to all predictions in the ambient Hilbert space,
without separability of that space. The actual population singular functions
also produce a measurable finite regression design with its exact second
moments; neither orthogonality nor the design moments are certificate inputs.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix Filter WithLp
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section

namespace FinitePredictionBayes

variable {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coefficients (e : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (e i)))

omit [Fintype ι] in
theorem coefficients_apply (e : ι → E) (f : E) (i : ι) :
    coefficients e f i = inner ℝ (e i) f := rfl

def synthesis (e : ι → E) : EuclideanSpace ℝ ι →L[ℝ] E :=
  ∑ i, (GaussianLinearBayes.coordinateCLM i).smulRight (e i)

theorem synthesis_apply (e : ι → E) (θ : EuclideanSpace ℝ ι) :
    synthesis e θ = ∑ i, θ i • e i := by
  simp only [synthesis, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

theorem coefficients_synthesis {e : ι → E} (he : Orthonormal ℝ e) (θ : EuclideanSpace ℝ ι) :
    coefficients e (synthesis e θ) = θ := by
  classical
  ext i
  rw [coefficients_apply, synthesis_apply, inner_sum]
  simp [inner_smul_right, orthonormal_iff_ite.mp he]

theorem coefficients_norm_sq_le {e : ι → E} (he : Orthonormal ℝ e) (f : E) :
    ‖coefficients e f‖^2 ≤ ‖f‖^2 := by
  simpa only [EuclideanSpace.norm_sq_eq, coefficients_apply] using
    (he.sum_inner_products_le (s := Finset.univ) f)

theorem coefficient_loss_le_prediction_loss {e : ι → E} (he : Orthonormal ℝ e)
    (θ : EuclideanSpace ℝ ι) (f : E) :
    ‖θ - coefficients e f‖^2 ≤ ‖synthesis e θ - f‖^2 := by
  have hb := coefficients_norm_sq_le he (synthesis e θ - f)
  rw [map_sub, coefficients_synthesis he] at hb
  exact hb

theorem synthesis_norm_sq {e : ι → E} (he : Orthonormal ℝ e) (θ : EuclideanSpace ℝ ι) :
    ‖synthesis e θ‖^2 = ‖θ‖^2 := by
  rw [← real_inner_self_eq_norm_sq, synthesis_apply, he.inner_sum θ θ Finset.univ,
    EuclideanSpace.real_norm_sq_eq]
  simp only [conj_trivial, pow_two]

variable [MeasurableSpace E] [BorelSpace E]
  {κ X : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ] [MeasurableSpace X]

local instance finitePredictionMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) := borel _
local instance finitePredictionMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

def predictionDecisionRisk (ν : Measure X) (v : ι → ℝ) (σ : ℝ)
    (Φ : X → Matrix κ ι ℝ) (e : ι → E) (d : X × EuclideanSpace ℝ κ → E) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖synthesis e z.2.1 - d (z.1, GaussianLinearBayes.observation (Φ z.1) z.2)‖^2)
    ∂ν.prod (GaussianLinearBayes.modelMeasure v σ)

/-- Every measurable ambient prediction has at least the finite-coordinate
Gaussian Bayes loss. The prediction is not assumed to lie in the active span. -/
theorem integral_trace_le_predictionDecisionRisk {ν : Measure X} [SFinite ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    {e : ι → E} (he : Orthonormal ℝ e)
    (d : X × EuclideanSpace ℝ κ → E) (hd : Measurable d) :
    (∫⁻ x, ENNReal.ofReal (GaussianLinearBayes.posteriorCovariance v σ (Φ x)).trace ∂ν) ≤
      predictionDecisionRisk ν v σ Φ e d := by
  have hb := GaussianLinearBayes.integral_trace_le_designDecisionRisk (ν := ν) hv hσ Φ hΦ
    (fun z => coefficients e (d z)) ((coefficients e).measurable.comp hd)
  refine hb.trans (lintegral_mono fun z => ?_)
  exact ENNReal.ofReal_le_ofReal (coefficient_loss_le_prediction_loss he z.2.1 _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The finite posterior mean synthesized in the actual prediction space
attains that lower bound. -/
theorem predictionDecisionRisk_posteriorMean {ν : Measure X} [SFinite ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    {e : ι → E} (he : Orthonormal ℝ e) :
    predictionDecisionRisk ν v σ Φ e
      (fun z => synthesis e (GaussianLinearBayes.designPosteriorMean v σ Φ z)) =
      ∫⁻ x, ENNReal.ofReal (GaussianLinearBayes.posteriorCovariance v σ (Φ x)).trace ∂ν := by
  rw [← GaussianLinearBayes.designDecisionRisk_posteriorMean hv hσ Φ hΦ]
  apply lintegral_congr
  intro z
  rw [← map_sub, synthesis_norm_sq he]

end FinitePredictionBayes

section ActualDesign

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePredictionFunction (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (j : ι) : Lp ℝ 2 μ :=
  predictionSingularBasis (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (jmap j)

omit [Fintype ι] in
theorem finitePredictionFunction_orthonormal (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap) :
    Orthonormal ℝ (finitePredictionFunction k hk jmap) := by
  exact ((predictionSingularBasis (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk)).orthonormal.comp jmap hj).comp_linearIsometry
      (Submodule.subtypeₗᵢ _)

def finitePredictionDesignMatrix (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (xs : κ → X) : Matrix κ ι ℝ :=
  Matrix.of (fun i j => lpRepresentative (finitePredictionFunction k hk jmap j) (xs i))

omit [Fintype ι] [Fintype κ] in
theorem finitePredictionDesignMatrix_apply (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (xs : κ → X) (i : κ) (j : ι) :
    finitePredictionDesignMatrix k hk jmap xs i j =
      lpRepresentative (finitePredictionFunction k hk jmap j) (xs i) := rfl

local instance finiteBasisMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) := borel _
local instance finiteBasisMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

theorem measurable_finitePredictionDesignMatrix (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) :
    Measurable (finitePredictionDesignMatrix (κ := κ) k hk jmap) :=
  GaussianLinearBayes.measurable_matrix_of_entries _ (fun i _j =>
    (lpRepresentative_measurable _).comp (measurable_pi_apply i))

omit [Fintype ι] in
theorem finitePredictionDesignMatrix_entry_memLp (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (i : κ) (j : ι) :
    MemLp (fun xs => finitePredictionDesignMatrix k hk jmap xs i j) 2
      (Measure.pi (fun _ : κ => μ)) :=
  (lpRepresentative_memLp _).comp_measurePreserving (measurePreserving_eval _ i)

omit [Fintype ι] in
theorem integral_finitePredictionDesignMatrix_entry_sq (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (i : κ) (j : ι) :
    (∫ xs, finitePredictionDesignMatrix k hk jmap xs i j ^ 2 ∂Measure.pi (fun _ : κ => μ)) = 1 := by
  have hlaw := measurePreserving_eval (fun _ : κ => μ) i
  have he := integral_map hlaw.aemeasurable
    (show AEStronglyMeasurable (fun x => lpRepresentative (finitePredictionFunction k hk jmap j) x ^ 2)
      ((Measure.pi (fun _ : κ => μ)).map (Function.eval i)) from by
        rw [hlaw.map_eq]
        exact ((lpRepresentative_stronglyMeasurable _).pow 2).aestronglyMeasurable)
  rw [hlaw.map_eq] at he
  calc
    _ = ∫ x, lpRepresentative (finitePredictionFunction k hk jmap j) x ^ 2 ∂μ := he.symm
    _ = ∫ x, (finitePredictionFunction k hk jmap j) x ^ 2 ∂μ :=
      integral_congr_ae ((lpRepresentative_ae_eq _).fun_comp (· ^ 2))
    _ = ‖finitePredictionFunction k hk jmap j‖^2 := integral_sq_L2 _
    _ = 1 := by
      have hn := (predictionSingularBasis (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk)).orthonormal.norm_eq_one (jmap j)
      change ‖predictionSingularBasis (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) (jmap j)‖^2 = 1
      rw [hn, one_pow]

omit [Fintype ι] in
/-- The original diagonal Gram moment is a conclusion for the actual
population eigenfunctions sampled under the actual product design law. -/
theorem integral_finitePredictionDesignMatrix_column_sq (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (j : ι) :
    (∫ xs, ∑ i, finitePredictionDesignMatrix k hk jmap xs i j ^ 2
      ∂Measure.pi (fun _ : κ => μ)) = (Fintype.card κ : ℝ) := by
  rw [integral_finsetSum _ (fun i _ => (finitePredictionDesignMatrix_entry_memLp k hk jmap i j).integrable_sq)]
  simp only [integral_finitePredictionDesignMatrix_entry_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- A version of the finite signal which is jointly measurable in its
Gaussian coefficients and its prediction argument. -/
def finitePredictionRepresentative (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    (θ : EuclideanSpace ℝ ι) (x : X) : ℝ :=
  ∑ j, θ j * lpRepresentative (finitePredictionFunction k hk jmap j) x

theorem measurable_finitePredictionRepresentative (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) :
    Measurable (fun z : EuclideanSpace ℝ ι × X => finitePredictionRepresentative k hk jmap z.1 z.2) := by
  unfold finitePredictionRepresentative
  have hm (j : ι) := lpRepresentative_measurable (finitePredictionFunction k hk jmap j)
  fun_prop

theorem finitePredictionRepresentative_ae_eq (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (θ : EuclideanSpace ℝ ι) :
    lpRepresentative (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ) =ᵐ[μ]
      finitePredictionRepresentative k hk jmap θ := by
  have he (j : ι) : ((θ j • finitePredictionFunction k hk jmap j : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      (fun x => θ j * lpRepresentative (finitePredictionFunction k hk jmap j) x) := by
    filter_upwards [Lp.coeFn_smul (θ j) (finitePredictionFunction k hk jmap j),
      lpRepresentative_ae_eq (finitePredictionFunction k hk jmap j)] with x hx hr
    simpa only [Pi.smul_apply, smul_eq_mul, hr] using hx
  refine (lpRepresentative_ae_eq _).trans ?_
  rw [FinitePredictionBayes.synthesis_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => θ j • finitePredictionFunction k hk jmap j),
    ae_all_iff.mpr he] with x hx hxj
  exact hx.trans (Finset.sum_congr rfl (fun j _ => hxj j))

local instance finitePredictionLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance finitePredictionLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

/-- The full prediction-class Bayes lower bound on actual `L²(μ)` targets.
Orthogonality and the finite design are derived from the population singular
system. The ambient `L²(μ)` is not required to be separable. -/
theorem actual_prediction_gaussian_bayes_lower [DecidableEq ι] [DecidableEq κ]
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {v : ι → ℝ} (hv : ∀ j, 0 < v j) {σ : ℝ} (hσ : 0 < σ)
    (d : (κ → X) × EuclideanSpace ℝ κ → Lp ℝ 2 μ) (hd : Measurable d) :
    (∫⁻ xs, ENNReal.ofReal (GaussianLinearBayes.posteriorCovariance v σ
      (finitePredictionDesignMatrix k hk jmap xs)).trace ∂Measure.pi (fun _ : κ => μ)) ≤
      FinitePredictionBayes.predictionDecisionRisk (Measure.pi (fun _ : κ => μ)) v σ
        (finitePredictionDesignMatrix k hk jmap) (finitePredictionFunction k hk jmap) d :=
  FinitePredictionBayes.integral_trace_le_predictionDecisionRisk hv hσ _
    (measurable_finitePredictionDesignMatrix k hk jmap)
    (finitePredictionFunction_orthonormal k hk jmap hj) d hd

end ActualDesign
end
end KernelSeq
