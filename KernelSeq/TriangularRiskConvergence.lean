import KernelSeq.TriangularRiskBounds
import KernelSeq.TriangularRiskRates
import KernelSeq.UniformRiskConvergence

/-!
# Complete risk equivalence for genuinely changing regression rows

Each row may have a different RKHS, design space, observation space, kernel,
law and target. The only common bounds are the original model/filter
constants and a positive noise lower bound. All finite analytic and
probabilistic estimates are supplied by actual local theorems.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A s0 : ℝ}

theorem triangular_good_risk_L1
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0)) :
    Tendsto (fun i => (m i).goodRiskIntegral) l (𝓝 0) := by
  have hsmall := triangular_eventually_small m hQ hc
  apply squeeze_zero' (hQ.mono fun i hi => (m i).goodRiskIntegral_nonneg hi) _
    (triangular_good_envelope_tendsto_zero m s0 hQ hc hz)
  filter_upwards [hnoise, hQ, hsmall] with i hni hQi hsi
  exact (m i).goodRiskIntegral_bound hs0 hni hQi hsi.2.2.2.1 hsi.2.2.2.2

omit [NeBot l] in
theorem triangular_bad_risk_L1
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0))
    (he : Tendsto (fun i => (m i).expectationScale) l (𝓝 0)) :
    Tendsto (fun i => (m i).badRiskIntegral) l (𝓝 0) := by
  have hsmall := triangular_eventually_small m hQ hc
  apply squeeze_zero' (hQ.mono fun i hi => (m i).badRiskIntegral_nonneg hi) _
    (triangular_bad_envelope_tendsto_zero m s0 hQ hz he)
  filter_upwards [hnoise, hQ, hsmall] with i hni hQi hsi
  exact (m i).badRiskIntegral_bound hs0 hni hQi hsi.1 hsi.2.1 hsi.2.2.1

/-- The original conditional-in-probability conclusion for arbitrary actual
rows. There is no additional expectation/logarithmic scale assumption. -/
theorem triangular_conditional_risk_equivalence
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun i => (m i).P
      {ω | ε < |(m i).conditionalRisk ω / (m i).benchmark - 1|}) l (𝓝 0) :=
  risk_ratio_probability_of_good_bad_L1 (fun i => (m i).P)
    (fun i => (m i).conditionalRisk) (fun i => (m i).benchmark)
    (fun i => (m i).conditionalRisk_integrable) (hQ.mono fun i hi => (m i).benchmark_pos hi)
    (fun i => (m i).goodEvent) (fun i => (m i).goodEvent_measurable)
    (triangular_good_risk_L1 m hs0 hnoise hQ hc hz)
    (triangular_bad_probability_tendsto_zero m hQ hc)

/-- The original expectation-risk conclusion for changing rows, under
exactly the additional logarithmic expectation scale. The second conclusion
is normalized conditional-risk L1 convergence, not raw-loss concentration. -/
theorem triangular_expectation_risk_equivalence
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0))
    (he : Tendsto (fun i => (m i).expectationScale) l (𝓝 0)) :
    Tendsto (fun i => (m i).expectationRisk / (m i).benchmark) l (𝓝 1) ∧
      Tendsto (fun i => (m i).normalizedL1) l (𝓝 0) := by
  have hgood := triangular_good_risk_L1 m hs0 hnoise hQ hc hz
  have hbad := triangular_bad_risk_L1 m hs0 hnoise hQ hc hz he
  have hprob := triangular_bad_probability_tendsto_zero m hQ hc
  have h := risk_expectation_from_good_bad_rows (fun i => (m i).P)
    (fun i => (m i).conditionalRisk) (fun i => (m i).benchmark)
    (fun i => (m i).conditionalRisk_integrable) (fun i => (m i).conditionalRisk_nonneg)
    (hQ.mono fun i hi => (m i).benchmark_pos hi)
    (fun i => (m i).goodEvent) (fun i => (m i).goodEvent_measurable)
    hgood (by simpa only [TriangularRiskModel.badRiskIntegral, integral_div] using hbad) hprob
  refine ⟨?_, ?_⟩
  · apply h.1.congr'
    exact Eventually.of_forall fun i => by
      change ((∫ ω, (m i).conditionalRisk ω ∂(m i).P) / (m i).benchmark) =
        (m i).expectationRisk / (m i).benchmark
      rw [(m i).expectationRisk_eq_integral]
  · simpa only [TriangularRiskModel.normalizedL1, integral_div] using h.2

end
end KernelSeq
