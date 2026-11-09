import KernelSeq.HilbertBallClipping
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Actual prior truncation over every measurable prediction rule

Continuous ball clipping is constructed explicitly. It decreases loss on
the supported class and bounds the loss outside it. Splitting the genuine
nonnegative Bayes integral proves the shaving inequality without a moment
condition on the decision rule or a supplied comparison of Bayes risks.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped ENNReal
noncomputable section

variable {Θ U Z E : Type*} [MeasurableSpace Θ] [MeasurableSpace U] [MeasurableSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

def predictionRuleBayesRisk (π : Measure Θ) (ν : Measure U) (g : Θ → E)
    (Y : Θ → U → Z) (d : Z → E) : ℝ≥0∞ :=
  ∫⁻ θ, ∫⁻ u, ENNReal.ofReal (‖d (Y θ u) - g θ‖^2) ∂ν ∂π

def predictionBayesRisk (π : Measure Θ) (ν : Measure U) (g : Θ → E)
    (Y : Θ → U → Z) : ℝ≥0∞ :=
  ⨅ (d : Z → E) (_hd : Measurable d), predictionRuleBayesRisk π ν g Y d

def supportedPrior (π : Measure Θ) (C : Set Θ) : Measure Θ := (π C)⁻¹ • π.restrict C

/-- A fully explicit prior-shaving inequality. The remainder is the actual
outside-class target second-moment integral. Later Gaussian concentration
and moment estimates bound this quantity; no such rate is assumed here. -/
theorem predictionBayesRisk_prior_shaving
    (π : Measure Θ) [IsProbabilityMeasure π] (ν : Measure U) [IsProbabilityMeasure ν]
    (g : Θ → E) (Y : Θ → U → Z)
    {B : ℝ} (hB : 0 < B) {C : Set Θ} (hC : MeasurableSet C) (hpos : 0 < π C)
    (hclass : ∀ θ ∈ C, ‖g θ‖ ≤ B) :
    predictionBayesRisk π ν g Y ≤ predictionBayesRisk (supportedPrior π C) ν g Y +
      ∫⁻ θ in Cᶜ, ENNReal.ofReal (2*B^2 + 2*‖g θ‖^2) ∂π := by
  let T : ℝ≥0∞ := ∫⁻ θ in Cᶜ, ENNReal.ofReal (2*B^2+2*‖g θ‖^2) ∂π
  have hweight : π C * (π C)⁻¹ = 1 := ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _)
  have hineq (d : Z → E) (hd : Measurable d) :
      predictionBayesRisk π ν g Y ≤ predictionRuleBayesRisk (supportedPrior π C) ν g Y d + T := by
    let dc : Z → E := clipHilbertBall B ∘ d
    have hdc : Measurable dc := (clipHilbertBall_continuous hB).measurable.comp hd
    have hstart : predictionBayesRisk π ν g Y ≤ predictionRuleBayesRisk π ν g Y dc :=
      iInf_le_of_le dc (iInf_le_of_le hdc le_rfl)
    have hins : (∫⁻ θ in C, ∫⁻ u, ENNReal.ofReal (‖dc (Y θ u)-g θ‖^2) ∂ν ∂π) ≤
        ∫⁻ θ in C, ∫⁻ u, ENNReal.ofReal (‖d (Y θ u)-g θ‖^2) ∂ν ∂π := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC] with θ hθ
      exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal
        (clipHilbertBall_sq_loss_le hB (d (Y θ u)) (g θ) (hclass θ hθ))
    have hout : (∫⁻ θ in Cᶜ, ∫⁻ u, ENNReal.ofReal (‖dc (Y θ u)-g θ‖^2) ∂ν ∂π) ≤ T := by
      apply lintegral_mono
      intro θ
      calc
        _ ≤ ∫⁻ _u : U, ENNReal.ofReal (2*B^2+2*‖g θ‖^2) ∂ν :=
          lintegral_mono fun u => ENNReal.ofReal_le_ofReal
            (clipHilbertBall_sq_loss_bound hB (d (Y θ u)) (g θ))
        _ = _ := by simp
    have hcondition : (∫⁻ θ in C, ∫⁻ u, ENNReal.ofReal (‖d (Y θ u)-g θ‖^2) ∂ν ∂π) ≤
        predictionRuleBayesRisk (supportedPrior π C) ν g Y d := by
      calc
        _ = π C * predictionRuleBayesRisk (supportedPrior π C) ν g Y d := by
          rw [predictionRuleBayesRisk, supportedPrior, lintegral_smul_measure,
            smul_eq_mul, ← mul_assoc, hweight, one_mul]
        _ ≤ _ := by
          have hle : π C ≤ 1 := by simpa using (measure_mono (Set.subset_univ C) : π C ≤ π univ)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hle
            (show 0 ≤ predictionRuleBayesRisk (supportedPrior π C) ν g Y d from bot_le)
    apply hstart.trans
    change (∫⁻ θ, ∫⁻ u, ENNReal.ofReal (‖dc (Y θ u)-g θ‖^2) ∂ν ∂π) ≤ _
    rw [← lintegral_add_compl _ hC]
    exact add_le_add (hins.trans hcondition) hout
  calc
    _ ≤ ⨅ (d : Z → E) (hd : Measurable d),
        predictionRuleBayesRisk (supportedPrior π C) ν g Y d + T :=
      le_iInf fun d => le_iInf fun hd => hineq d hd
    _ = _ := by simp only [predictionBayesRisk, ENNReal.iInf_add, T]

end
end KernelSeq
