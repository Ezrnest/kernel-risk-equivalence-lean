import KernelSeq.BayesPriorTruncation

/-!
# Bayes-to-minimax transfer with an actual supported prior

The minimax infimum is over the full measurable decision class, with genuine
nonnegative risks. Supported-prior normalization and averaging are proved;
the full-prior comparison uses the constructed Hilbert-ball clipping.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped ENNReal
noncomputable section

variable {Θ U Z E : Type*} [MeasurableSpace Θ] [MeasurableSpace U] [MeasurableSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

def predictionDecisionRisk (ν : Measure U) (Y : E → U → Z) (d : Z → E) (f : E) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (‖d (Y f u)-f‖^2) ∂ν

def predictionMinimaxRisk (ν : Measure U) (Y : E → U → Z) (F : Set E) : ℝ≥0∞ :=
  ⨅ (d : Z → E) (_hd : Measurable d), ⨆ f : F, predictionDecisionRisk ν Y d f.val

theorem supportedPrior_isProbabilityMeasure (π : Measure Θ) [IsProbabilityMeasure π]
    {C : Set Θ} (hpos : 0 < π C) : IsProbabilityMeasure (supportedPrior π C) := by
  constructor
  simp only [supportedPrior, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top _ _)

theorem supportedPrior_mem_ae (π : Measure Θ) {C : Set Θ} (hC : MeasurableSet C) :
    ∀ᵐ θ ∂supportedPrior π C, θ ∈ C :=
  Measure.ae_smul_measure (ae_restrict_mem hC) _

omit [InnerProductSpace ℝ E] [BorelSpace E] in
/-- A probability prior genuinely supported by the parameter class gives a
lower bound for the minimax risk over every measurable prediction rule. -/
theorem predictionBayesRisk_le_minimax_of_supported
    (π : Measure Θ) [IsProbabilityMeasure π] (ν : Measure U)
    (g : Θ → E) (Y : E → U → Z) (F : Set E)
    (hsupport : ∀ᵐ θ ∂π, g θ ∈ F) :
    predictionBayesRisk π ν g (fun θ => Y (g θ)) ≤ predictionMinimaxRisk ν Y F := by
  unfold predictionBayesRisk predictionMinimaxRisk
  apply iInf_mono
  intro d
  apply iInf_mono
  intro _hd
  calc
    _ ≤ ∫⁻ _θ, (⨆ f : F, predictionDecisionRisk ν Y d f.val) ∂π := by
      apply lintegral_mono_ae
      filter_upwards [hsupport] with θ hθ
      exact le_iSup_of_le ⟨g θ,hθ⟩ le_rfl
    _ = _ := by simp

/-- The full-prior Bayes risk is bounded by the actual minimax risk plus
the proved clipping remainder. This statement has no prior-shaving risk
certificate among its assumptions. -/
theorem predictionBayesRisk_le_minimax_add_tail
    (π : Measure Θ) [IsProbabilityMeasure π] (ν : Measure U) [IsProbabilityMeasure ν]
    (g : Θ → E) (Y : E → U → Z) (F : Set E)
    {B : ℝ} (hB : 0 < B) {C : Set Θ} (hC : MeasurableSet C) (hpos : 0 < π C)
    (hclass : ∀ θ ∈ C, g θ ∈ F) (hnorm : ∀ f ∈ F, ‖f‖ ≤ B) :
    predictionBayesRisk π ν g (fun θ => Y (g θ)) ≤ predictionMinimaxRisk ν Y F +
      ∫⁻ θ in Cᶜ, ENNReal.ofReal (2*B^2+2*‖g θ‖^2) ∂π := by
  letI := supportedPrior_isProbabilityMeasure π hpos
  have hsup : ∀ᵐ θ ∂supportedPrior π C, g θ ∈ F :=
    (supportedPrior_mem_ae π hC).mono fun θ hθ => hclass θ hθ
  have hb := predictionBayesRisk_le_minimax_of_supported (supportedPrior π C) ν g Y F hsup
  exact (predictionBayesRisk_prior_shaving π ν g (fun θ => Y (g θ)) hB hC hpos
    (fun θ hθ => hnorm _ (hclass θ hθ))).trans (add_le_add hb le_rfl)

end
end KernelSeq
