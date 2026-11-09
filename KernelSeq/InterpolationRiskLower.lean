import KernelSeq.TriangularRiskBounds
import KernelSeq.TriangularRiskTails
import KernelSeq.UniformRiskConvergence
import KernelSeq.SpectralCounting

/-!
# Resolved population coordinates give an actual conditional-risk lower bound

The interpolation-regime lower bound uses only variance compatibility.
The count retains the actual positive population spectrum's multiplicities.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

universe uH uX uΩ

namespace TriangularRiskModel
variable {κ ρ A : ℝ} (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A)

/-- The number of population coordinates substantially retained by the
filter. The common resolution threshold is derived from its residual contract. -/
def resolvedCount : ℕ :=
  featureSpectralCount m.feature m.feature_memLp
    (m.lam * ResidualFilter.resolvedScaleFactor ρ A)

theorem quarter_resolvedCount_le : (1 / 4 : ℝ) * m.resolvedCount ≤ m.Q :=
  quarter_mul_featureSpectralCount_le_filterDimension m.feature m.feature_memLp m.φ
    m.lambda_pos m.population_bound m.spectral_filter m.filter_contract

theorem varianceEnergy_integrable : Integrable m.varianceEnergy m.P :=
  integrable_variance_of_risk_bias_identity m.conditionalRisk m.bias m.varianceEnergy
    (div_pos (sq_pos_of_pos m.noise_pos) (Nat.cast_pos.mpr m.sample_pos)).ne'
    m.conditionalRisk_integrable m.bias_integrable m.conditionalRisk_energy

/-- Nonnegative squared bias in the genuine conditional-energy identity
gives the first lower bound without any bias comparison theorem. -/
theorem variance_le_conditionalRisk :
    ∀ᵐ ω ∂m.P, m.σ ^ 2 / (m.n : ℝ) * m.varianceEnergy ω ≤ m.conditionalRisk ω := by
  filter_upwards [m.conditionalRisk_energy] with ω hω
  rw [hω]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- A finite-row lower-tail estimate by the actual good-event variance
integral and the bad-design probability. -/
theorem conditionalRisk_resolved_lower_tail_le (hQ : 0 < m.Q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    m.P {ω | m.conditionalRisk ω <
      (1-ε) * m.σ^2 / (4*(m.n : ℝ)) * m.resolvedCount} ≤
      m.P m.goodEventᶜ + ENNReal.ofReal (m.goodVarianceIntegral / ε) := by
  have ha : 0 < m.σ^2 / (m.n : ℝ) :=
    div_pos (sq_pos_of_pos m.noise_pos) (Nat.cast_pos.mpr m.sample_pos)
  have hm := measure_relative_risk_exceedance_le_good_bad m.varianceEnergy m.Q
    m.varianceEnergy_integrable hQ m.goodEvent m.goodEvent_measurable hε
  refine (measure_mono_ae ?_).trans hm
  filter_upwards [m.variance_le_conditionalRisk] with ω hω
  intro ht
  have hthreshold : (1-ε) * m.σ^2 / (4*(m.n : ℝ)) * m.resolvedCount =
      ((1-ε) * (m.σ^2 / (m.n : ℝ))) * ((1/4 : ℝ) * m.resolvedCount) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlow : m.σ^2 / (m.n : ℝ) * m.varianceEnergy ω <
      ((1-ε) * (m.σ^2 / (m.n : ℝ))) * m.Q := by
    apply (hω.trans_lt ht).trans_le
    rw [hthreshold]
    exact mul_le_mul_of_nonneg_left m.quarter_resolvedCount_le
      (mul_nonneg (sub_nonneg.mpr hε1) ha.le)
  have hv : m.varianceEnergy ω < (1-ε) * m.Q := by
    apply (mul_lt_mul_iff_right₀ ha).mp
    nlinarith only [hlow]
  change ε < |m.varianceEnergy ω - m.Q| / m.Q
  apply (lt_div_iff₀ hQ).mpr
  have hd : ε * m.Q < -(m.varianceEnergy ω - m.Q) := by nlinarith only [hv]
  exact hd.trans_le (neg_le_abs _)

end TriangularRiskModel

variable {J : Type*} {l : Filter J} {κ ρ A : ℝ}

/-- Actual good-event variance comparison follows from variance
compatibility alone, even for changing regression spaces, laws and targets. -/
theorem triangular_good_variance_L1_of_compatibility
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0)) :
    Tendsto (fun i => (m i).goodVarianceIntegral) l (𝓝 0) := by
  have hsmall := triangular_eventually_small m hQ hc
  have hb : Tendsto (fun i => uniformVarianceRiskConstant ρ A *
      ((m i).compatibility + (m i).compatibility^2)) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_zero] using
      (hc.add (hc.pow 2)).const_mul (uniformVarianceRiskConstant ρ A)
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    integral_nonneg fun _ => div_nonneg (abs_nonneg _) (by exact (m _).Q_nonneg)) _ hb
  filter_upwards [hQ, hsmall] with i hi hsi
  exact (m i).goodVarianceIntegral_bound hi hsi.2.2.2.1 hsi.2.2.2.2

/-- The interpolation-regime risk lower bound in exact tail form. The
noise level may vary arbitrarily among the positive levels in the model.
No target source balance or expectation-scale hypothesis is needed. -/
theorem triangular_conditionalRisk_resolved_lower_tail
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun i => (m i).P {ω | (m i).conditionalRisk ω <
      (1-ε) * (m i).σ^2 / (4*((m i).n : ℝ)) * (m i).resolvedCount}) l (𝓝 0) := by
  have hv := triangular_good_variance_L1_of_compatibility m hQ hc
  have hp := triangular_bad_probability_tendsto_zero m hQ hc
  have ht := (ENNReal.tendsto_ofReal hp).add (ENNReal.tendsto_ofReal (hv.div_const ε))
  simp only [ENNReal.ofReal_zero, zero_div, add_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [hQ, ENNReal.tendsto_nhds_zero.mp ht δ hδ] with i hi hit
  have he : ENNReal.ofReal ((m i).P.real (m i).goodEventᶜ) = (m i).P (m i).goodEventᶜ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  exact ((m i).conditionalRisk_resolved_lower_tail_le hi hε hε1.le).trans
    (by rwa [he] at hit)

end
end KernelSeq
