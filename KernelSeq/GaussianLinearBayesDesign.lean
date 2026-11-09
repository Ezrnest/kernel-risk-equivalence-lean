import KernelSeq.GaussianLinearBayesRisk
import Mathlib.Topology.Instances.Matrix

/-!
# Measurable random-design Gaussian linear Bayes experiments

The design space is an arbitrary measurable space. Its law is independent
of the actual Gaussian prior/noise product law. The precision inverse and
posterior mean are genuinely jointly measurable. The risk identity is over
all jointly measurable decisions, with nonnegative extended-real loss.
-/

namespace KernelSeq.GaussianLinearBayes

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance gaussianDesignMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) :=
  borel _
local instance gaussianDesignMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

omit [DecidableEq κ] in
theorem precision_continuous (v : ι → ℝ) (σ : ℝ) :
    Continuous (fun Φ : Matrix κ ι ℝ => precision v σ Φ) := by
  unfold precision
  fun_prop

omit [DecidableEq κ] in
theorem posteriorCovariance_continuous {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) :
    Continuous (fun Φ : Matrix κ ι ℝ => posteriorCovariance v σ Φ) := by
  apply continuous_iff_continuousAt.mpr
  intro Φ
  have hdet : (precision v σ Φ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (precision_posDef hv σ Φ).isUnit).ne_zero
  have hi : ContinuousAt Inv.inv (precision v σ Φ) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact hi.comp (precision_continuous v σ).continuousAt

omit [DecidableEq κ] in
theorem gain_continuous {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) :
    Continuous (fun Φ : Matrix κ ι ℝ => gain v σ Φ) := by
  have hc := posteriorCovariance_continuous (κ := κ) hv σ
  unfold gain
  fun_prop

theorem measurable_matrixCLM_apply {Z a b : Type*} [MeasurableSpace Z]
    [Fintype a] [Fintype b] [DecidableEq b]
    (M : Z → Matrix a b ℝ) (hM : Measurable M)
    (x : Z → EuclideanSpace ℝ b) (hx : Measurable x) :
    Measurable (fun z => matrixCLM (M z) (x z)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : a => ℝ)
  have hcoeff (i : a) (j : b) : Measurable (fun z => M z i j) :=
    ((continuous_id : Continuous (fun N : Matrix a b ℝ => N)).matrix_elem i j).measurable.comp hM
  have hcoords : Measurable (fun z => fun i => ∑ j, M z i j * x z j) := by fun_prop
  exact e.symm.continuous.measurable.comp hcoords

theorem measurable_matrix_of_entries {Z a b : Type*} [MeasurableSpace Z]
    [Fintype a] [Fintype b] (M : Z → Matrix a b ℝ)
    (hM : ∀ i j, Measurable (fun z => M z i j)) : Measurable M := by
  change @Measurable Z (a → b → ℝ) _ (borel (a → b → ℝ)) M
  rw [← @BorelSpace.measurable_eq (a → b → ℝ) _ MeasurableSpace.pi inferInstance]
  exact measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (hM i))

variable {X : Type*} [MeasurableSpace X]

def designPosteriorMean (v : ι → ℝ) (σ : ℝ) (Φ : X → Matrix κ ι ℝ)
    (z : X × EuclideanSpace ℝ κ) : EuclideanSpace ℝ ι :=
  matrixCLM (gain v σ (Φ z.1)) z.2

theorem measurable_designPosteriorMean {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    Measurable (designPosteriorMean v σ Φ) :=
  measurable_matrixCLM_apply _ (((gain_continuous hv σ).measurable.comp hΦ).comp measurable_fst)
    _ measurable_snd

theorem measurable_designObservation (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    Measurable (fun z : X × (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) =>
      observation (Φ z.1) z.2) := by
  simp_rw [observation_apply]
  exact (measurable_matrixCLM_apply _ (hΦ.comp measurable_fst) _
    (measurable_fst.comp measurable_snd)).add (measurable_snd.comp measurable_snd)

def designDecisionRisk (ν : Measure X) (v : ι → ℝ) (σ : ℝ) (Φ : X → Matrix κ ι ℝ)
    (d : X × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.2.1 - d (z.1, observation (Φ z.1) z.2)‖^2)
    ∂ν.prod (modelMeasure v σ)

theorem designDecisionRisk_eq_integral {ν : Measure X} [SFinite ν]
    (v : ι → ℝ) (σ : ℝ) (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    (d : X × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) (hd : Measurable d) :
    designDecisionRisk ν v σ Φ d = ∫⁻ x, decisionRisk v σ (Φ x) (fun y => d (x,y)) ∂ν := by
  have hm : Measurable (fun z : X × (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) =>
      ENNReal.ofReal (‖z.2.1 - d (z.1, observation (Φ z.1) z.2)‖^2)) := by
    have ho := measurable_designObservation Φ hΦ
    fun_prop
  exact lintegral_prod _ hm.aemeasurable

/-- Conditional Gaussian Bayes lower bounds integrate over an entirely
arbitrary design law; no standard-Borel assumption on the design is used. -/
theorem integral_trace_le_designDecisionRisk {ν : Measure X} [SFinite ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    (d : X × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) (hd : Measurable d) :
    (∫⁻ x, ENNReal.ofReal (posteriorCovariance v σ (Φ x)).trace ∂ν) ≤
      designDecisionRisk ν v σ Φ d := by
  rw [designDecisionRisk_eq_integral v σ Φ hΦ d hd]
  apply lintegral_mono
  intro x
  exact trace_le_decisionRisk hv hσ (Φ x) _ (hd.comp (measurable_const.prodMk measurable_id))

theorem designDecisionRisk_posteriorMean {ν : Measure X} [SFinite ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    designDecisionRisk ν v σ Φ (designPosteriorMean v σ Φ) =
      ∫⁻ x, ENNReal.ofReal (posteriorCovariance v σ (Φ x)).trace ∂ν := by
  rw [designDecisionRisk_eq_integral v σ Φ hΦ _ (measurable_designPosteriorMean hv σ Φ hΦ)]
  exact lintegral_congr (fun x => decisionRisk_posteriorMean hv hσ (Φ x))

def designCoefficientBayesRisk (ν : Measure X) (v : ι → ℝ) (σ : ℝ) (Φ : X → Matrix κ ι ℝ) : ℝ≥0∞ :=
  ⨅ (d : X × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) (_hd : Measurable d),
    designDecisionRisk ν v σ Φ d

theorem designCoefficientBayesRisk_eq_integral_trace {ν : Measure X} [SFinite ν]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ℝ} (hσ : 0 < σ)
    (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ) :
    designCoefficientBayesRisk ν v σ Φ =
      ∫⁻ x, ENNReal.ofReal (posteriorCovariance v σ (Φ x)).trace ∂ν := by
  unfold designCoefficientBayesRisk
  apply le_antisymm
  · exact iInf_le_of_le (designPosteriorMean v σ Φ)
      (iInf_le_of_le (measurable_designPosteriorMean hv σ Φ hΦ)
        (designDecisionRisk_posteriorMean hv hσ Φ hΦ).le)
  · exact le_iInf fun d => le_iInf fun hd => integral_trace_le_designDecisionRisk hv hσ Φ hΦ d hd

end
end KernelSeq.GaussianLinearBayes
